#include "structurer.hpp"
#include "identifier_utils.hpp"
#include "codegen.hpp"
#include <algorithm>
#include <atomic>
#include <cctype>
#include <cstdio>
#include <functional>
#include <future>
#include <limits>
#include <optional>
#include <sstream>
#include <thread>
#include <unordered_map>
#include <unordered_set>

template <typename Formatter>
static std::vector<std::string> formatFunctionsParallel(const std::vector<Function>& functions, Formatter&& formatter) {
    const size_t functionCount = functions.size();
    std::vector<std::string> chunks(functionCount);
    if (functionCount == 0) {
        return chunks;
    }

    unsigned int workerCount = std::thread::hardware_concurrency();
    if (workerCount == 0) {
        workerCount = 4;
    }
    workerCount = (unsigned int)std::min<size_t>(workerCount, functionCount);
    if (workerCount <= 1 || functionCount < 4) {
        for (size_t i = 0; i < functionCount; ++i) {
            chunks[i] = formatter(functions[i]);
        }
        return chunks;
    }

    std::atomic<size_t> nextIndex{0};
    std::vector<std::future<void>> workers;
    workers.reserve(workerCount);
    for (unsigned int worker = 0; worker < workerCount; ++worker) {
        workers.push_back(std::async(std::launch::async, [&]() {
            while (true) {
                size_t index = nextIndex.fetch_add(1);
                if (index >= functionCount) {
                    break;
                }
                chunks[index] = formatter(functions[index]);
            }
        }));
    }
    for (auto& worker : workers) {
        worker.get();
    }
    return chunks;
}

namespace {
static std::atomic<bool> g_inlineClosureBodies{true};

static AstFunction structureFunctionWithAliases(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                                const std::vector<std::string>& upvalueAliases,
                                                const std::unordered_map<int, std::vector<std::string>>& aliasesByFunction,
                                                const std::vector<std::string>* functionDisplayNames = nullptr);

struct TableEntry {
    std::optional<std::string> namedKey;
    std::optional<int> numericKey;
    std::optional<int> keyValueId;
    std::optional<std::string> keyExpression;
    int valueId = -1;
    std::optional<std::string> valueExpression;
};

struct TableConstruction {
    int resultValueId = -1;
    bool selfReferential = false;
    bool inlineable = true;
    std::vector<TableEntry> entries;
};

struct ExpressionContext {
    const Chunk& chunk;
    const Function& sourceFunction;
    const OpcodeMap& opmap;
    const SSAFunction& analyzed;
    std::vector<std::string> upvalueAliases;
    const std::unordered_map<int, std::vector<std::string>>* aliasesByFunction = nullptr;
    const std::vector<std::string>* functionDisplayNames = nullptr;
    std::unordered_map<int, TableConstruction> tables;
    std::unordered_map<int, const PhiNode*> phiByResult;
    std::unordered_set<int> symbolicPhiValues;
    std::unordered_set<int> symbolicMutableValues;
    std::unordered_set<int> capturedMutableValues;
    std::unordered_set<int> closureCapturedValues;
    std::unordered_set<int> foldedInstructions;
    std::unordered_set<int> foldedCallExpressions;
    std::unordered_map<int, std::string> slotAliases;
    std::unordered_map<int, std::string> expressionCache;
    std::unordered_set<int> expressionStack;
};

static std::string localNameForSlot(const Function& function, int slot) {
    auto isSyntheticParamLocal = [&](const std::string& name) {
        if (slot >= 0 && slot < function.numParams) {
            return false;
        }
        if (name.size() < 2 || name[0] != 'p') {
            return false;
        }
        return std::all_of(name.begin() + 1, name.end(), [](unsigned char ch) {
            return std::isdigit(ch) != 0;
        });
    };

    for (const auto& local : function.locals) {
        if (local.slot == slot && local.startPc == 0 && !local.name.empty() && local.name[0] != '(' &&
            !isSyntheticParamLocal(local.name)) {
            return sanitizeLuaIdentifier(local.name, slot < function.numParams ? "p" : "v");
        }
    }
    if (slot >= 0 && slot < function.numParams) {
        return "p" + std::to_string(slot);
    }
    return "v" + std::to_string(slot);
}

static bool isUsableFunctionName(const std::string& name) {
    return isLuaIdentifier(name);
}

static std::string canonicalProtoName(const Function& function) {
    return "proto_" + std::to_string(function.id);
}

static std::string fallbackDisplayFunctionName(const Function& function) {
    return "fn_" + std::to_string(function.id);
}

static std::vector<std::string> buildFunctionDisplayNames(const Chunk& chunk) {
    std::vector<std::string> names(chunk.functions.size());
    std::vector<std::string> bases(chunk.functions.size());
    std::unordered_map<std::string, int> baseCounts;

    for (const auto& function : chunk.functions) {
        if (function.id < 0 || function.id >= (int)chunk.functions.size()) {
            continue;
        }
        if (isUsableFunctionName(function.debugName)) {
            std::string base = sanitizeLuaIdentifier(function.debugName, "fn");
            bases[function.id] = base;
            baseCounts[base]++;
        }
    }

    for (const auto& function : chunk.functions) {
        if (function.id < 0 || function.id >= (int)chunk.functions.size()) {
            continue;
        }
        const std::string& base = bases[function.id];
        if (base.empty()) {
            names[function.id] = fallbackDisplayFunctionName(function);
        } else if (baseCounts[base] > 1) {
            names[function.id] = base + "_" + std::to_string(function.id);
        } else {
            names[function.id] = base;
        }
    }

    return names;
}

static std::string displayNameForFunction(const std::vector<std::string>& names, const Function& function) {
    if (function.id >= 0 && function.id < (int)names.size() && !names[function.id].empty()) {
        return names[function.id];
    }
    return fallbackDisplayFunctionName(function);
}

static std::string normalizeLiteral(const std::string& value) {
    if (value == "inf") {
        return "math.huge";
    }
    if (value == "-inf") {
        return "-math.huge";
    }
    if (value == "nan") {
        return "0/0";
    }
    return value;
}

static std::string trimSpace(std::string value) {
    while (!value.empty() && std::isspace((unsigned char)value.front())) {
        value.erase(value.begin());
    }
    while (!value.empty() && std::isspace((unsigned char)value.back())) {
        value.pop_back();
    }
    return value;
}

static bool needsMethodReceiverParens(const std::string& expression) {
    std::string trimmed = trimSpace(expression);
    if (trimmed.empty()) {
        return false;
    }
    if (trimmed.front() == '(') {
        return false;
    }
    char first = trimmed.front();
    if (first == '"' || first == '\'' || first == '{' || first == '[' || std::isdigit((unsigned char)first) || first == '-') {
        return true;
    }
    return false;
}

static bool needsCallCalleeParens(const std::string& expression) {
    std::string trimmed = trimSpace(expression);
    if (trimmed.empty() || trimmed.front() == '(') {
        return false;
    }
    if (trimmed.rfind("function", 0) == 0 ||
        trimmed.find('\n') != std::string::npos ||
        trimmed.find('\r') != std::string::npos) {
        return true;
    }
    char first = trimmed.front();
    if (std::isalpha(static_cast<unsigned char>(first)) || first == '_') {
        return false;
    }
    return true;
}

static bool isIdentifierKey(const std::string& value) {
    return isLuaIdentifier(value);
}

static bool isQualifiedIdentifierPath(const std::string& value) {
    if (value.empty()) {
        return false;
    }
    size_t start = 0;
    while (start < value.size()) {
        size_t dot = value.find('.', start);
        std::string segment = dot == std::string::npos
            ? value.substr(start)
            : value.substr(start, dot - start);
        if (!isLuaIdentifier(segment)) {
            return false;
        }
        if (dot == std::string::npos) {
            return true;
        }
        start = dot + 1;
    }
    return false;
}

static std::string escapeLuaStringLiteral(const std::string& value) {
    std::string escaped;
    escaped.reserve(value.size() + 8);
    for (unsigned char ch : value) {
        switch (ch) {
            case '\\':
                escaped += "\\\\";
                break;
            case '\"':
                escaped += "\\\"";
                break;
            case '\n':
                escaped += "\\n";
                break;
            case '\r':
                escaped += "\\r";
                break;
            case '\t':
                escaped += "\\t";
                break;
            default:
                if (ch < 32 || ch == 127) {
                    char buf[8];
                    std::snprintf(buf, sizeof(buf), "\\x%02X", static_cast<unsigned int>(ch));
                    escaped += buf;
                } else {
                    escaped.push_back(static_cast<char>(ch));
                }
                break;
        }
    }
    return "\"" + escaped + "\"";
}

static bool needsIndexBaseParens(const std::string& expression) {
    std::string trimmed = trimSpace(expression);
    if (trimmed.empty() || trimmed.front() == '(') {
        return false;
    }

    int parenDepth = 0;
    int bracketDepth = 0;
    int braceDepth = 0;
    bool inString = false;
    char stringQuote = '\0';
    bool escaped = false;

    for (char ch : trimmed) {
        if (inString) {
            if (escaped) {
                escaped = false;
                continue;
            }
            if (ch == '\\') {
                escaped = true;
                continue;
            }
            if (ch == stringQuote) {
                inString = false;
            }
            continue;
        }

        if (ch == '"' || ch == '\'') {
            inString = true;
            stringQuote = ch;
            continue;
        }

        if (ch == '(') {
            ++parenDepth;
            continue;
        }
        if (ch == ')') {
            --parenDepth;
            continue;
        }
        if (ch == '[') {
            ++bracketDepth;
            continue;
        }
        if (ch == ']') {
            --bracketDepth;
            continue;
        }
        if (ch == '{') {
            ++braceDepth;
            continue;
        }
        if (ch == '}') {
            --braceDepth;
            continue;
        }

        if (parenDepth == 0 && bracketDepth == 0 && braceDepth == 0) {
            if (std::isspace(static_cast<unsigned char>(ch)) ||
                ch == '+' || ch == '-' || ch == '*' || ch == '/' || ch == '%' ||
                ch == '^' || ch == '#' || ch == '<' || ch == '>' || ch == '=') {
                return true;
            }
        }
    }

    if (trimmed == "nil" || trimmed == "true" || trimmed == "false") {
        return true;
    }

    char first = trimmed.front();
    return !(std::isalpha(static_cast<unsigned char>(first)) || first == '_');
}

static std::string indexBase(const std::string& expression) {
    return needsIndexBaseParens(expression) ? ("(" + expression + ")") : expression;
}

static std::string formatIndexAccess(std::string objectExpr, std::string keyExpr) {
    return indexBase(objectExpr) + "[" + keyExpr + "]";
}

static std::string formatNamedFieldAccess(std::string objectExpr, const std::string& key) {
    if (isIdentifierKey(key)) {
        return indexBase(objectExpr) + "." + key;
    }
    return formatIndexAccess(std::move(objectExpr), escapeLuaStringLiteral(key));
}

static const SSAInstruction* definingInstruction(const SSAFunction& function, int valueId) {
    if (valueId < 0 || valueId >= (int)function.values.size()) {
        return nullptr;
    }
    int defInst = function.values[valueId].definingInstruction;
    if (defInst < 0 || defInst >= (int)function.instructions.size()) {
        return nullptr;
    }
    return &function.instructions[defInst];
}

static bool isSideEffectingValue(const SSAFunction& analyzed, int valueId) {
    const SSAInstruction* def = definingInstruction(analyzed, valueId);
    if (!def) {
        return false;
    }
    return def->hasSideEffects && def->inst.stdOp != OP_GETIMPORT && def->inst.stdOp != OP_GETUPVAL;
}

static int findValueForSlotInBlock(const SSAFunction& analyzed, int blockId, int beforeInstructionIndex, int slot) {
    if (blockId < 0 || blockId >= (int)analyzed.blocks.size()) {
        return -1;
    }

    const auto& block = analyzed.blocks[blockId];
    int currentValue = -1;

    for (const auto& phi : block.phis) {
        if (!phi.dead && phi.slot == slot && phi.resultValueId >= 0) {
            currentValue = phi.resultValueId;
        }
    }

    for (int instIndex : block.instructionRefs) {
        if (beforeInstructionIndex >= 0 && instIndex >= beforeInstructionIndex) {
            break;
        }
        const auto& instruction = analyzed.instructions[instIndex];
        for (int defValueId : instruction.defs) {
            if (defValueId >= 0 && defValueId < (int)analyzed.values.size() && analyzed.values[defValueId].slot == slot) {
                currentValue = defValueId;
            }
        }
        for (int defValueId : instruction.clobberDefs) {
            if (defValueId >= 0 && defValueId < (int)analyzed.values.size() && analyzed.values[defValueId].slot == slot) {
                currentValue = defValueId;
            }
        }
    }

    return currentValue;
}

static int currentValueForSlotAtInstruction(const SSAFunction& analyzed, int instructionIndex, int slot) {
    if (instructionIndex >= 0 && instructionIndex < (int)analyzed.instructions.size()) {
        int blockId = analyzed.instructions[instructionIndex].blockId;
        while (blockId >= 0) {
            int valueId = findValueForSlotInBlock(analyzed, blockId, instructionIndex, slot);
            if (valueId >= 0) {
                return valueId;
            }
            if (blockId >= (int)analyzed.cfg.immediateDominator.size()) {
                break;
            }
            blockId = analyzed.cfg.immediateDominator[blockId];
            instructionIndex = -1;
        }
    }

    for (const auto& value : analyzed.values) {
        if (value.slot == slot && value.isParameter) {
            return value.id;
        }
    }
    return -1;
}

static int valueIdForSlot(ExpressionContext& context, const SSAInstruction& instruction, int slot) {
    return currentValueForSlotAtInstruction(context.analyzed, instruction.index, slot);
}

static std::string buildExpression(ExpressionContext& context, int valueId, int depth = 0);
static std::string buildCallExpression(ExpressionContext& context, const SSAInstruction& instruction, int depth);
static std::string buildArgumentExpression(ExpressionContext& context, int valueId, int depth, bool isLastArgument);
static std::string assignmentTargetForValue(ExpressionContext& context, int valueId);
static bool isConditionalOpcode(int stdOp);
static bool canInlineConditionValue(ExpressionContext& context, const SSAInstruction& terminator, size_t useIndex);
static bool isInlineableConditionProducer(ExpressionContext& context, const SSAInstruction& instruction,
                                          const SSAInstruction& terminator);
static std::string buildConditionOperand(ExpressionContext& context, const SSAInstruction& terminator, size_t useIndex);
static bool isRegisterLikeAlias(const std::string& alias);
static bool isSyntheticParameterAlias(const std::string& alias);
static bool hasNumericSuffix(const std::string& alias);
static std::string stripNumericSuffix(std::string alias);
static bool isGenericSemanticAlias(const std::string& alias);
static int aliasQuality(const std::string& alias, float confidence = 0.0f);
static bool shouldPreferAlias(const std::string& candidate, const std::string& current);
static void initializeSlotAliases(ExpressionContext& context);
static std::string slotAliasFor(ExpressionContext& context, int slot);
static std::string normalizeStructuredAlias(ExpressionContext& context, int slot, std::string alias);
static std::string normalizeInheritedAlias(std::string alias);
static ExpressionContext forkContextWithAliases(ExpressionContext& context, const std::unordered_map<int, std::string>& aliases);
static std::unordered_map<int, std::string> inferLoopAliases(ExpressionContext& context, const SSAInstruction& instruction,
                                                             int bodyBlock, int latchBlock, int postLoopBlock);
static std::optional<const Function*> resolveChildFunction(ExpressionContext& context, const SSAInstruction& instruction);

static std::string buildSlotExpression(ExpressionContext& context, const SSAInstruction& instruction, int slot, int depth = 0) {
    int valueId = valueIdForSlot(context, instruction, slot);
    if (valueId < 0) {
        return "_";
    }
    return buildExpression(context, valueId, depth);
}

static std::string trimTrailingNewline(std::string value) {
    while (!value.empty() && (value.back() == '\n' || value.back() == '\r')) {
        value.pop_back();
    }
    return value;
}

static std::string stripLeadingIndentOnFirstLine(std::string value, int indentWidth) {
    size_t firstLineEnd = value.find('\n');
    size_t firstLineLength = firstLineEnd == std::string::npos ? value.size() : firstLineEnd;
    size_t removable = 0;
    while (removable < (size_t)indentWidth && removable < firstLineLength && value[removable] == ' ') {
        ++removable;
    }
    if (removable > 0) {
        value.erase(0, removable);
    }
    return value;
}

static const PhiNode* phiForValue(ExpressionContext& context, int valueId) {
    auto it = context.phiByResult.find(valueId);
    return it != context.phiByResult.end() ? it->second : nullptr;
}

static bool isConditionalOpcode(int stdOp) {
    switch (stdOp) {
        case OP_JUMPIF:
        case OP_JUMPIFNOT:
        case OP_JUMPIFEQ:
        case OP_JUMPIFNOTEQ:
        case OP_JUMPIFLE:
        case OP_JUMPIFLT:
        case OP_JUMPIFNOTLE:
        case OP_JUMPIFNOTLT:
        case OP_JUMPXEQKNIL:
        case OP_JUMPXEQKB:
        case OP_JUMPXEQKN:
        case OP_JUMPXEQKS:
            return true;
        default:
            return false;
    }
}

static bool canInlineConditionValue(ExpressionContext& context, const SSAInstruction& terminator, size_t useIndex) {
    if (!isConditionalOpcode(terminator.inst.stdOp) || useIndex >= terminator.uses.size()) {
        return false;
    }

    int valueId = terminator.uses[useIndex];
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return false;
    }

    const auto& value = context.analyzed.values[valueId];
    if (value.isPhi || value.isParameter || value.isUpvalue ||
        context.symbolicMutableValues.count(valueId) || context.capturedMutableValues.count(valueId)) {
        return false;
    }

    const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
    if (!def || def->defs.size() != 1 || def->defs.front() != valueId) {
        return false;
    }

    if (def->inst.stdOp != OP_CALL && def->inst.stdOp != OP_NATIVECALL) {
        return false;
    }

    int instructionUseCount = 0;
    for (const auto& instruction : context.analyzed.instructions) {
        for (int usedValueId : instruction.uses) {
            if (usedValueId == valueId) {
                ++instructionUseCount;
                if (&instruction != &terminator || instructionUseCount > 1) {
                    return false;
                }
            }
        }
    }

    return instructionUseCount == 1;
}

static bool isInlineableConditionProducer(ExpressionContext& context, const SSAInstruction& instruction,
                                          const SSAInstruction& terminator) {
    if (instruction.index == terminator.index || instruction.defs.size() != 1 || !isConditionalOpcode(terminator.inst.stdOp)) {
        return false;
    }

    int valueId = instruction.defs.front();
    for (size_t useIndex = 0; useIndex < terminator.uses.size(); ++useIndex) {
        if (terminator.uses[useIndex] == valueId && canInlineConditionValue(context, terminator, useIndex)) {
            return true;
        }
    }
    return false;
}

static std::string buildConditionOperand(ExpressionContext& context, const SSAInstruction& terminator, size_t useIndex) {
    if (canInlineConditionValue(context, terminator, useIndex)) {
        int valueId = terminator.uses[useIndex];
        if (const SSAInstruction* def = definingInstruction(context.analyzed, valueId)) {
            return buildCallExpression(context, *def, 0);
        }
    }
    if (useIndex < terminator.uses.size()) {
        int valueId = terminator.uses[useIndex];
        if (valueId >= 0 && valueId < (int)context.analyzed.values.size()) {
            const auto& value = context.analyzed.values[valueId];
            int logicalSlot = value.slot;
            if (auto it = context.analyzed.cellSlotToEscapedSlot.find(logicalSlot);
                it != context.analyzed.cellSlotToEscapedSlot.end()) {
                logicalSlot = it->second;
            }
            if (logicalSlot >= 0 && context.analyzed.escapedMutableSlots.count(logicalSlot) != 0) {
                std::string slotAlias = sanitizeLuaIdentifier(slotAliasFor(context, logicalSlot), "v");
                if (!slotAlias.empty() && slotAlias != "_") {
                    return slotAlias;
                }
                return normalizeStructuredAlias(context, logicalSlot, value.name);
            }
        }
    }
    return useIndex < terminator.uses.size() ? buildExpression(context, terminator.uses[useIndex]) : "_";
}

static std::optional<int> choosePhiRepresentative(ExpressionContext& context, const PhiNode& phi) {
    if (context.symbolicPhiValues.count(phi.resultValueId)) {
        return std::nullopt;
    }

    if (phi.inputs.empty()) {
        return std::nullopt;
    }

    // Merged-state cleanup: collapse phi when all incoming values are semantically the same.
    // This reduces join-state temp junk like boards_1 / v41.key in non-loop merges.
    int canonicalInput = -1;
    bool sameInput = true;
    for (const auto& [pred, inputValueId] : phi.inputs) {
        (void)pred;
        if (inputValueId == phi.resultValueId || inputValueId < 0 ||
            inputValueId >= (int)context.analyzed.values.size()) {
            continue;
        }
        if (canonicalInput < 0) {
            canonicalInput = inputValueId;
            continue;
        }
        if (canonicalInput != inputValueId) {
            sameInput = false;
            break;
        }
    }
    if (sameInput && canonicalInput >= 0) {
        return canonicalInput;
    }

    std::optional<std::string> canonicalConstant;
    bool sameConstant = true;
    int constantRepresentative = -1;
    for (const auto& [pred, inputValueId] : phi.inputs) {
        (void)pred;
        if (inputValueId == phi.resultValueId || inputValueId < 0 ||
            inputValueId >= (int)context.analyzed.values.size()) {
            continue;
        }
        const auto& inputValue = context.analyzed.values[inputValueId];
        if (!inputValue.constantValue.has_value()) {
            sameConstant = false;
            break;
        }
        if (!canonicalConstant.has_value()) {
            canonicalConstant = *inputValue.constantValue;
            constantRepresentative = inputValueId;
            continue;
        }
        if (*canonicalConstant != *inputValue.constantValue) {
            sameConstant = false;
            break;
        }
    }
    if (sameConstant && constantRepresentative >= 0) {
        return constantRepresentative;
    }

    int aliasRepresentative = -1;
    std::string canonicalAlias;
    int canonicalSlot = std::numeric_limits<int>::min();
    bool sameAlias = true;
    for (const auto& [pred, inputValueId] : phi.inputs) {
        (void)pred;
        if (inputValueId == phi.resultValueId || inputValueId < 0 ||
            inputValueId >= (int)context.analyzed.values.size()) {
            continue;
        }

        const auto& inputValue = context.analyzed.values[inputValueId];
        std::string alias = assignmentTargetForValue(context, inputValueId);
        if (aliasRepresentative < 0) {
            aliasRepresentative = inputValueId;
            canonicalAlias = alias;
            canonicalSlot = inputValue.slot;
            continue;
        }

        if (alias != canonicalAlias &&
            (inputValue.slot < 0 || canonicalSlot < 0 || inputValue.slot != canonicalSlot)) {
            sameAlias = false;
            break;
        }
    }
    if (sameAlias && aliasRepresentative >= 0) {
        return aliasRepresentative;
    }

    std::vector<int> loopBackPreds;
    for (const auto& edge : context.analyzed.cfg.edges) {
        if (edge.toBlock == phi.blockId && edge.kind == CFGEdgeKind::LoopBack) {
            loopBackPreds.push_back(edge.fromBlock);
        }
    }

    auto pickInput = [&](bool preferNonLoopBack) -> std::optional<int> {
        for (int pred : context.analyzed.cfg.blocks[phi.blockId].predecessors) {
            auto it = phi.inputs.find(pred);
            if (it == phi.inputs.end()) {
                continue;
            }
            bool isLoopBack = std::find(loopBackPreds.begin(), loopBackPreds.end(), pred) != loopBackPreds.end();
            if (preferNonLoopBack && isLoopBack) {
                continue;
            }
            if (!preferNonLoopBack && !isLoopBack) {
                continue;
            }
            if (it->second != phi.resultValueId) {
                return it->second;
            }
        }
        return std::nullopt;
    };

    if (auto chosen = pickInput(true); chosen.has_value()) {
        return chosen;
    }
    if (auto chosen = pickInput(false); chosen.has_value()) {
        return chosen;
    }

    for (const auto& [pred, inputValueId] : phi.inputs) {
        (void)pred;
        if (inputValueId != phi.resultValueId) {
            return inputValueId;
        }
    }
    return std::nullopt;
}

static void populatePhiMap(ExpressionContext& context) {
    context.phiByResult.clear();
    for (const auto& block : context.analyzed.blocks) {
        for (const auto& phi : block.phis) {
            if (phi.resultValueId >= 0) {
                context.phiByResult[phi.resultValueId] = &phi;
            }
        }
    }
}

static std::string renderTableLiteral(ExpressionContext& context, const TableConstruction& table, int depth) {
    if (table.selfReferential) {
        return assignmentTargetForValue(context, table.resultValueId);
    }

    std::ostringstream out;
    std::string ind(depth * 4, ' ');
    std::string inner((depth + 1) * 4, ' ');

    out << "{";
    if (!table.entries.empty()) {
        out << "\n";
        for (size_t i = 0; i < table.entries.size(); ++i) {
            const auto& entry = table.entries[i];
            out << inner;
            if (entry.namedKey.has_value()) {
                if (isIdentifierKey(*entry.namedKey)) {
                    out << *entry.namedKey << " = ";
                } else {
                    out << "[" << escapeLuaStringLiteral(*entry.namedKey) << "] = ";
                }
            } else if (entry.numericKey.has_value()) {
                out << "[" << *entry.numericKey << "] = ";
            } else if (entry.keyValueId.has_value()) {
                out << "[" << buildExpression(context, *entry.keyValueId, depth + 1) << "] = ";
            } else if (entry.keyExpression.has_value()) {
                out << "[" << *entry.keyExpression << "] = ";
            }
            out << (entry.valueExpression.has_value()
                ? *entry.valueExpression
                : buildExpression(context, entry.valueId, depth + 1));
            if (i + 1 < table.entries.size()) {
                out << ",";
            }
            out << "\n";
        }
        out << ind;
    }
    out << "}";
    return out.str();
}

static bool isCallInstruction(const SSAInstruction& instruction) {
    return instruction.inst.stdOp == OP_CALL || instruction.inst.stdOp == OP_NATIVECALL;
}

static std::string buildArgumentExpression(ExpressionContext& context, int valueId, int depth, bool isLastArgument) {
    std::string expression = buildExpression(context, valueId, depth);
    if (!isLastArgument || expression == "...") {
        return expression;
    }

    const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
    if (def && isCallInstruction(*def)) {
        return "(" + expression + ")";
    }
    return expression;
}

static std::string buildCallExpression(ExpressionContext& context, const SSAInstruction& instruction, int depth) {
    if (!instruction.uses.empty()) {
        const SSAInstruction* calleeDef = definingInstruction(context.analyzed, instruction.uses.front());
        if (calleeDef && calleeDef->inst.stdOp == OP_NAMECALL && calleeDef->inst.keyName.has_value()) {
            std::ostringstream out;
            std::string objectExpr = !calleeDef->uses.empty() ? buildExpression(context, calleeDef->uses.front(), depth) : "_";
            std::string receiver = needsMethodReceiverParens(objectExpr) ? ("(" + objectExpr + ")") : objectExpr;
            out << receiver << ":" << *calleeDef->inst.keyName << "(";
            for (size_t i = 2; i < instruction.uses.size(); ++i) {
                if (i > 2) {
                    out << ", ";
                }
                out << buildArgumentExpression(context, instruction.uses[i], depth, i + 1 == instruction.uses.size());
            }
            out << ")";
            return out.str();
        }
    }

    if (instruction.renderedText.has_value()) {
        return *instruction.renderedText;
    }

    std::ostringstream out;
    std::string calleeExpr = instruction.uses.empty() ? "_" : buildExpression(context, instruction.uses[0], depth);
    if (needsCallCalleeParens(calleeExpr)) {
        calleeExpr = "(" + calleeExpr + ")";
    }
    out << calleeExpr << "(";
    for (size_t i = 1; i < instruction.uses.size(); ++i) {
        if (i > 1) {
            out << ", ";
        }
        out << buildArgumentExpression(context, instruction.uses[i], depth, i + 1 == instruction.uses.size());
    }
    out << ")";
    return out.str();
}

static bool isInlineableValueConstructorImport(const std::string& importName) {
    static const std::unordered_set<std::string> kConstructors = {
        "Color3.new",
        "Color3.fromRGB",
        "Color3.fromHSV",
        "NumberRange.new",
    };
    return kConstructors.count(importName) != 0;
}

static const SSAInstruction* inlineableValueConstructorCall(ExpressionContext& context, int valueId) {
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return nullptr;
    }

    const auto& value = context.analyzed.values[valueId];
    if (value.isPhi || value.isParameter || value.isUpvalue || value.useCount != 1 ||
        context.symbolicMutableValues.count(valueId) ||
        context.capturedMutableValues.count(valueId) ||
        context.closureCapturedValues.count(valueId)) {
        return nullptr;
    }

    const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
    if (!def || def->defs.size() != 1 || def->defs.front() != valueId ||
        (def->inst.stdOp != OP_CALL && def->inst.stdOp != OP_NATIVECALL) ||
        def->uses.empty()) {
        return nullptr;
    }

    const SSAInstruction* calleeDef = definingInstruction(context.analyzed, def->uses.front());
    if (!calleeDef || calleeDef->inst.stdOp != OP_GETIMPORT ||
        !calleeDef->inst.importName.has_value() ||
        !isInlineableValueConstructorImport(*calleeDef->inst.importName)) {
        return nullptr;
    }

    for (size_t i = 1; i < def->uses.size(); ++i) {
        int argValueId = def->uses[i];
        if (argValueId < 0 || argValueId >= (int)context.analyzed.values.size()) {
            return nullptr;
        }
        if (context.symbolicMutableValues.count(argValueId) ||
            context.capturedMutableValues.count(argValueId) ||
            context.closureCapturedValues.count(argValueId) ||
            isSideEffectingValue(context.analyzed, argValueId)) {
            return nullptr;
        }
    }

    return def;
}

static void inlineValueConstructorEntry(ExpressionContext& context, TableEntry& entry, int sourceValueId) {
    if (const SSAInstruction* call = inlineableValueConstructorCall(context, sourceValueId)) {
        entry.valueExpression = buildCallExpression(context, *call, 0);
        context.foldedInstructions.insert(call->index);
    }
}

static bool isBlockedInlineCalleeName(const std::string& name) {
    static const std::unordered_set<std::string> kBlocked = {
        "require",
        "error",
        "assert",
        "pcall",
        "xpcall",
    };
    return kBlocked.count(name) != 0;
}

static bool hasBlockedInlineCallee(ExpressionContext& context, const SSAInstruction& instruction) {
    if (instruction.uses.empty()) {
        return true;
    }

    const SSAInstruction* calleeDef = definingInstruction(context.analyzed, instruction.uses.front());
    if (!calleeDef) {
        return false;
    }
    if (calleeDef->inst.stdOp == OP_GETIMPORT && calleeDef->inst.importName.has_value()) {
        return isBlockedInlineCalleeName(*calleeDef->inst.importName);
    }
    if (calleeDef->inst.stdOp == OP_GETGLOBAL && calleeDef->inst.keyName.has_value()) {
        return isBlockedInlineCalleeName(*calleeDef->inst.keyName);
    }
    return false;
}

static bool findSingleUseInstruction(ExpressionContext& context, int valueId, const SSAInstruction** useInstruction,
                                     size_t* useIndex) {
    int useCount = 0;
    const SSAInstruction* foundInstruction = nullptr;
    size_t foundIndex = 0;

    for (const auto& instruction : context.analyzed.instructions) {
        for (size_t i = 0; i < instruction.uses.size(); ++i) {
            if (instruction.uses[i] != valueId) {
                continue;
            }
            ++useCount;
            foundInstruction = &instruction;
            foundIndex = i;
            if (useCount > 1) {
                return false;
            }
        }
    }

    if (useCount != 1 || !foundInstruction) {
        return false;
    }
    if (useInstruction) {
        *useInstruction = foundInstruction;
    }
    if (useIndex) {
        *useIndex = foundIndex;
    }
    return true;
}

static bool hasInterveningSideEffects(ExpressionContext& context, const SSAInstruction& defInstruction,
                                      const SSAInstruction& useInstruction) {
    if (defInstruction.blockId != useInstruction.blockId || defInstruction.index >= useInstruction.index) {
        return true;
    }

    for (int index = defInstruction.index + 1; index < useInstruction.index; ++index) {
        if (index < 0 || index >= (int)context.analyzed.instructions.size()) {
            return true;
        }
        const SSAInstruction& instruction = context.analyzed.instructions[index];
        if (instruction.dead) {
            continue;
        }
        if (instruction.hasSideEffects && instruction.inst.stdOp != OP_NAMECALL) {
            return true;
        }
    }
    return false;
}

static bool canInlineSingleUseCallValue(ExpressionContext& context, int valueId) {
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return false;
    }

    const auto& value = context.analyzed.values[valueId];
    if (value.isPhi || value.isParameter || value.isUpvalue || value.useCount != 1 ||
        context.symbolicMutableValues.count(valueId) ||
        context.capturedMutableValues.count(valueId) ||
        context.closureCapturedValues.count(valueId)) {
        return false;
    }

    const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
    if (!def || !isCallInstruction(*def) || def->defs.size() != 1 || def->defs.front() != valueId ||
        def->uses.empty()) {
        return false;
    }
    if (def->inst.stdOp == OP_CALL && def->inst.c != 2) {
        return false;
    }
    if (hasBlockedInlineCallee(context, *def)) {
        return false;
    }

    const SSAInstruction* useInstruction = nullptr;
    size_t useIndex = 0;
    if (!findSingleUseInstruction(context, valueId, &useInstruction, &useIndex) || !useInstruction) {
        return false;
    }
    (void)useIndex;

    if (hasInterveningSideEffects(context, *def, *useInstruction)) {
        return false;
    }
    return true;
}

static std::vector<std::string> collectClosureCaptureAliases(ExpressionContext& context, const SSAInstruction& closureInstruction, const Function& childFunction) {
    std::vector<std::string> aliases;
    aliases.reserve(childFunction.numUpvalues);

    auto aliasNeedsUpgrade = [](const std::string& value) {
        if (value.empty() || value == "_") {
            return true;
        }
        if (value.rfind("upval", 0) == 0 || value.rfind("capture", 0) == 0) {
            return true;
        }
        if (isGenericSemanticAlias(value)) {
            return true;
        }
        if (value.size() > 1 && value[0] == 'v' && std::isdigit((unsigned char)value[1])) {
            for (size_t i = 2; i < value.size(); ++i) {
                if (!std::isdigit((unsigned char)value[i]) && value[i] != '_') {
                    return false;
                }
            }
            return true;
        }
        return false;
    };

    int capturePc = closureInstruction.inst.pc + closureInstruction.inst.width;
    int closureInstIndex = closureInstruction.index;

    for (int i = 0; i < childFunction.numUpvalues && capturePc < (int)context.sourceFunction.instructions.size(); ++i, ++capturePc) {
        int captureOp = context.opmap.lookup(context.sourceFunction.instructions[capturePc].opcode());
        if (captureOp != OP_CAPTURE) {
            break;
        }

        const auto& captureInst = context.sourceFunction.instructions[capturePc];
        int captureType = captureInst.a();
        int source = captureInst.b();
        std::string alias;

        switch (captureType) {
            case 0:
            case 1: {
                bool preserveExactSlotAlias =
                    (captureType == 1 && context.analyzed.escapedMutableSlots.count(source) != 0);
                int currentValueId = currentValueForSlotAtInstruction(context.analyzed, closureInstIndex, source);
                if (preserveExactSlotAlias) {
                    (void)currentValueId;
                    alias = sanitizeLuaIdentifier(slotAliasFor(context, source), "v");
                } else if (currentValueId >= 0 && currentValueId < (int)context.analyzed.values.size()) {
                    std::string candidate =
                        normalizeStructuredAlias(context, source, context.analyzed.values[currentValueId].name);
                    alias = normalizeInheritedAlias(candidate);
                } else {
                    std::string candidate = slotAliasFor(context, source);
                    alias = normalizeInheritedAlias(candidate);
                }
                break;
            }
            case 2:
                if (source >= 0 && source < (int)context.upvalueAliases.size() && !context.upvalueAliases[source].empty()) {
                    alias = normalizeInheritedAlias(context.upvalueAliases[source]);
                } else if (source >= 0 && source < (int)context.sourceFunction.upvalueNames.size() && !context.sourceFunction.upvalueNames[source].empty()) {
                    alias = context.sourceFunction.upvalueNames[source];
                } else {
                    alias = "upval" + std::to_string(source);
                }
                break;
            default:
                alias = "capture" + std::to_string(source);
                break;
        }

        if (i >= 0 && i < (int)childFunction.upvalueNames.size() &&
            !childFunction.upvalueNames[i].empty() &&
            aliasNeedsUpgrade(alias)) {
            alias = sanitizeLuaIdentifier(childFunction.upvalueNames[i], "upval");
        }

        aliases.push_back(normalizeInheritedAlias(alias));
    }

    return aliases;
}

static std::vector<std::string> resolveClosureCaptureAliases(ExpressionContext& context, const SSAInstruction& closureInstruction,
                                                             const Function& childFunction) {
    std::vector<std::string> aliases = collectClosureCaptureAliases(context, closureInstruction, childFunction);
    if (!context.aliasesByFunction) {
        return aliases;
    }

    auto it = context.aliasesByFunction->find(childFunction.id);
    if (it == context.aliasesByFunction->end()) {
        return aliases;
    }

    if (aliases.size() < it->second.size()) {
        aliases.resize(it->second.size());
    }

    for (size_t i = 0; i < it->second.size(); ++i) {
        const std::string& candidate = it->second[i];
        if (candidate.empty()) {
            continue;
        }
        if (shouldPreferAlias(candidate, aliases[i])) {
            aliases[i] = candidate;
        }
    }

    int capturePc = closureInstruction.inst.pc + closureInstruction.inst.width;
    int closureInstIndex = closureInstruction.index;
    int captureInstIndex = closureInstruction.index + 1;
    for (size_t i = 0; i < aliases.size() && capturePc < (int)context.sourceFunction.instructions.size(); ++i, ++capturePc) {
        int captureOp = context.opmap.lookup(context.sourceFunction.instructions[capturePc].opcode());
        if (captureOp != OP_CAPTURE) {
            break;
        }

        const auto& captureInst = context.sourceFunction.instructions[capturePc];
        int captureType = captureInst.a();
        int source = captureInst.b();
        if (captureType != 1 || context.analyzed.escapedMutableSlots.count(source) == 0) {
            if (captureInstIndex < (int)context.analyzed.instructions.size()) {
                ++captureInstIndex;
            }
            continue;
        }

        if (captureInstIndex >= 0 && captureInstIndex < (int)context.analyzed.instructions.size()) {
            const auto& ssaCapture = context.analyzed.instructions[captureInstIndex];
            if (ssaCapture.inst.stdOp == OP_CAPTURE && !ssaCapture.uses.empty()) {
                aliases[i] = sanitizeLuaIdentifier(slotAliasFor(context, source), "v");
                ++captureInstIndex;
                continue;
            }
        }

        int currentValueId = currentValueForSlotAtInstruction(context.analyzed, closureInstIndex, source);
        if (currentValueId >= 0 && currentValueId < (int)context.analyzed.values.size()) {
            aliases[i] = sanitizeLuaIdentifier(slotAliasFor(context, source), "v");
        } else {
            std::string candidate = slotAliasFor(context, source);
            aliases[i] = sanitizeLuaIdentifier(candidate, "v");
        }
        if (captureInstIndex < (int)context.analyzed.instructions.size()) {
            ++captureInstIndex;
        }
    }

    return aliases;
}

static void markCapturedMutableSlots(ExpressionContext& context) {
    std::function<void(int, bool)> markValueFamily = [&](int valueId, bool reintroduceAsLocal) {
        if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
            return;
        }
        bool inserted = context.symbolicMutableValues.insert(valueId).second;
        if (reintroduceAsLocal) {
            context.capturedMutableValues.insert(valueId);
        }
        if (!inserted) {
            return;
        }

        const auto& value = context.analyzed.values[valueId];
        if (value.isPhi) {
            if (const PhiNode* phi = phiForValue(context, valueId)) {
                for (const auto& [pred, inputValueId] : phi->inputs) {
                    (void)pred;
                    if (inputValueId >= 0 && inputValueId < (int)context.analyzed.values.size() &&
                        context.analyzed.values[inputValueId].slot == value.slot) {
                        markValueFamily(inputValueId, reintroduceAsLocal);
                    }
                }
            }
            return;
        }

        const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
        if (!def) {
            return;
        }
        for (int useValueId : def->uses) {
            if (useValueId >= 0 && useValueId < (int)context.analyzed.values.size() &&
                context.analyzed.values[useValueId].slot == value.slot) {
                markValueFamily(useValueId, reintroduceAsLocal);
            }
        }
    };

    for (const auto& value : context.analyzed.values) {
        if (value.isUpvalue && context.analyzed.escapedMutableSlots.count(value.slot)) {
            markValueFamily(value.id, false);
        }
    }

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp != OP_CAPTURE || instruction.uses.empty()) {
            continue;
        }
        if (instruction.inst.a == 0 || instruction.inst.a == 1) {
            markValueFamily(instruction.uses.front(), true);
        }
    }

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp == OP_GETUPVAL && !instruction.defs.empty()) {
            int upvalueSlot = context.sourceFunction.maxStackSize + instruction.inst.b;
            if (context.analyzed.escapedMutableSlots.count(upvalueSlot)) {
                markValueFamily(instruction.defs.front(), false);
            }
        } else if (instruction.inst.stdOp == OP_SETUPVAL) {
            for (int defValueId : instruction.defs) {
                markValueFamily(defValueId, false);
            }
        }
    }
}

static void markClosureCapturedValues(ExpressionContext& context) {
    context.closureCapturedValues.clear();
    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp != OP_CAPTURE || instruction.uses.empty()) {
            continue;
        }
        if (instruction.inst.a == 0 || instruction.inst.a == 1) {
            context.closureCapturedValues.insert(instruction.uses.front());
        }
    }
}

static bool isDirectClosureCaptureValue(const ExpressionContext& context, int valueId) {
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return false;
    }
    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp != OP_CAPTURE || instruction.uses.empty()) {
            continue;
        }
        if (instruction.inst.a != 0 && instruction.inst.a != 1) {
            continue;
        }
        if (instruction.uses.front() == valueId) {
            return true;
        }
    }
    return false;
}

static bool hasEarlierDirectClosureCaptureInSameSlot(const ExpressionContext& context, int valueId) {
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return false;
    }

    const auto& value = context.analyzed.values[valueId];
    if (value.slot < 0 || value.definingInstruction < 0) {
        return false;
    }

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp != OP_CAPTURE || instruction.uses.empty()) {
            continue;
        }
        if (instruction.inst.a != 0 && instruction.inst.a != 1) {
            continue;
        }

        int capturedValueId = instruction.uses.front();
        if (capturedValueId < 0 || capturedValueId >= (int)context.analyzed.values.size() ||
            capturedValueId == valueId) {
            continue;
        }

        const auto& capturedValue = context.analyzed.values[capturedValueId];
        if (capturedValue.slot != value.slot || capturedValue.definingInstruction < 0) {
            continue;
        }

        if (capturedValue.definingInstruction < value.definingInstruction) {
            return true;
        }
    }
    return false;
}

static void markSymbolicLoopPhiValues(ExpressionContext& context) {
    for (const auto& edge : context.analyzed.cfg.edges) {
        if (edge.kind != CFGEdgeKind::LoopBack) {
            continue;
        }

        int latchBlock = edge.fromBlock;
        if (latchBlock < 0 || latchBlock >= (int)context.analyzed.blocks.size()) {
            continue;
        }

        const auto& latch = context.analyzed.blocks[latchBlock];
        if (latch.instructionRefs.empty()) {
            continue;
        }

        const auto& terminator = context.analyzed.instructions[latch.instructionRefs.back()];
        if (terminator.inst.stdOp != OP_FORGLOOP && terminator.inst.stdOp != OP_FORNLOOP) {
            continue;
        }

        std::unordered_set<int> loopDefSlots;
        for (int valueId : terminator.defs) {
            if (valueId >= 0 && valueId < (int)context.analyzed.values.size()) {
                loopDefSlots.insert(context.analyzed.values[valueId].slot);
            }
        }

        int headerBlock = edge.toBlock;
        if (headerBlock < 0 || headerBlock >= (int)context.analyzed.blocks.size()) {
            continue;
        }

        for (const auto& phi : context.analyzed.blocks[headerBlock].phis) {
            if (phi.resultValueId >= 0 && loopDefSlots.count(phi.slot)) {
                context.symbolicPhiValues.insert(phi.resultValueId);
            }
        }
    }
}

static void markSymbolicConditionalPhiValues(ExpressionContext& context) {
    std::function<void(int)> markPhiFamily = [&](int valueId) {
        if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
            return;
        }
        if (!context.analyzed.values[valueId].isPhi) {
            return;
        }
        if (!context.symbolicPhiValues.insert(valueId).second) {
            return;
        }

        if (const PhiNode* phi = phiForValue(context, valueId)) {
            for (const auto& [pred, inputValueId] : phi->inputs) {
                (void)pred;
                if (inputValueId >= 0 && inputValueId < (int)context.analyzed.values.size() &&
                    context.analyzed.values[inputValueId].isPhi) {
                    markPhiFamily(inputValueId);
                }
            }
        }
    };

    for (const auto& instruction : context.analyzed.instructions) {
        if (!isConditionalOpcode(instruction.inst.stdOp)) {
            continue;
        }
        for (int valueId : instruction.uses) {
            markPhiFamily(valueId);
        }
    }
}

static std::optional<const Function*> resolveChildFunction(ExpressionContext& context, const SSAInstruction& instruction) {
    int protoIndex = -1;

    if (instruction.inst.stdOp == OP_NEWCLOSURE) {
        if (instruction.inst.d >= 0 && instruction.inst.d < (int)context.sourceFunction.childProtos.size()) {
            protoIndex = context.sourceFunction.childProtos[instruction.inst.d];
        }
    } else if (instruction.inst.stdOp == OP_DUPCLOSURE) {
        if (instruction.inst.d >= 0 && instruction.inst.d < (int)context.sourceFunction.constants.size() &&
            context.sourceFunction.constants[instruction.inst.d].type == ConstantType::Closure) {
            protoIndex = context.sourceFunction.constants[instruction.inst.d].closureIdx;
        }
    }

    if (protoIndex < 0 || protoIndex >= (int)context.chunk.functions.size()) {
        return std::nullopt;
    }
    return &context.chunk.functions[protoIndex];
}

static std::string renderClosureExpression(ExpressionContext& context, const SSAInstruction& instruction, int depth) {
    auto childFunction = resolveChildFunction(context, instruction);
    if (!childFunction.has_value()) {
        return context.analyzed.values[instruction.defs.front()].name;
    }
    if (!g_inlineClosureBodies.load(std::memory_order_relaxed)) {
        return context.functionDisplayNames
            ? displayNameForFunction(*context.functionDisplayNames, **childFunction)
            : canonicalProtoName(**childFunction);
    }

    std::vector<std::string> captureAliases = resolveClosureCaptureAliases(context, instruction, **childFunction);
    AstFunction childAst = context.aliasesByFunction
        ? structureFunctionWithAliases(context.chunk, **childFunction, context.opmap, captureAliases,
                                       *context.aliasesByFunction, context.functionDisplayNames)
        : structureFunction(context.chunk, **childFunction, context.opmap, captureAliases);
    std::string anonymous = formatAnonymousAstFunction(childAst, depth + 1);
    anonymous = trimTrailingNewline(anonymous);
    anonymous = stripLeadingIndentOnFirstLine(anonymous, (depth + 1) * 4);
    return anonymous;
}

static std::optional<AstFunction> buildClosureAst(ExpressionContext& context, const SSAInstruction& instruction) {
    auto childFunction = resolveChildFunction(context, instruction);
    if (!childFunction.has_value()) {
        return std::nullopt;
    }

    std::vector<std::string> captureAliases = resolveClosureCaptureAliases(context, instruction, **childFunction);
    if (context.aliasesByFunction) {
        return structureFunctionWithAliases(context.chunk, **childFunction, context.opmap, captureAliases,
                                           *context.aliasesByFunction, context.functionDisplayNames);
    }
    return structureFunction(context.chunk, **childFunction, context.opmap, captureAliases);
}

static bool isClosureValue(ExpressionContext& context, int valueId, const SSAInstruction** closureInstruction = nullptr) {
    const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
    if (!def) {
        return false;
    }
    if (def->inst.stdOp != OP_NEWCLOSURE && def->inst.stdOp != OP_DUPCLOSURE) {
        return false;
    }
    if (closureInstruction) {
        *closureInstruction = def;
    }
    return true;
}

static bool isWeakAlias(const std::string& alias) {
    return alias.empty() || alias.rfind("upval", 0) == 0 || alias.rfind("capture", 0) == 0 || alias == "_";
}

static bool isGenericSemanticAlias(const std::string& alias) {
    static const std::unordered_set<std::string> genericAliases = {
        "result", "closure", "value", "item", "entry", "condition",
        "count", "flag", "index", "table", "merge", "text", "formatted"
    };

    if (genericAliases.count(alias) != 0) {
        return true;
    }

    if (alias.rfind("result_", 0) == 0 || alias.rfind("value_", 0) == 0 ||
        alias.rfind("count_", 0) == 0) {
        return true;
    }
    return false;
}

static bool isRegisterLikeAlias(const std::string& alias) {
    if (alias.size() < 2 || alias[0] != 'v' || !std::isdigit((unsigned char)alias[1])) {
        return false;
    }
    for (size_t i = 2; i < alias.size(); ++i) {
        if (!std::isdigit((unsigned char)alias[i]) && alias[i] != '_') {
            return false;
        }
    }
    return true;
}

static bool isSyntheticParameterAlias(const std::string& alias) {
    if (alias.size() < 2 || alias[0] != 'p') {
        return false;
    }
    return std::all_of(alias.begin() + 1, alias.end(), [](unsigned char ch) {
        return std::isdigit(ch) != 0;
    });
}

static bool hasNumericSuffix(const std::string& alias) {
    size_t pos = alias.rfind('_');
    if (pos == std::string::npos || pos + 1 >= alias.size()) {
        return false;
    }
    for (size_t i = pos + 1; i < alias.size(); ++i) {
        if (!std::isdigit((unsigned char)alias[i])) {
            return false;
        }
    }
    return true;
}

static std::string stripNumericSuffix(std::string alias) {
    if (hasNumericSuffix(alias)) {
        alias.erase(alias.rfind('_'));
    }
    return alias;
}

static bool isRiskyBareAlias(const std::string& alias) {
    static const std::unordered_set<std::string> riskyAliases = {
        "table", "string", "math", "task", "os", "debug", "utf8", "coroutine",
        "bit32", "buffer", "game", "workspace", "script", "require", "pairs",
        "ipairs", "next", "select", "type", "warn", "error", "print", "pcall",
        "xpcall", "assert", "setmetatable", "getmetatable", "rawget", "rawset",
        "rawequal", "tonumber", "tostring"
    };
    return riskyAliases.count(alias) != 0;
}

static std::string normalizeUpvalueAliasName(std::string alias) {
    if (alias.empty() || isWeakAlias(alias)) {
        return alias;
    }
    if (hasNumericSuffix(alias)) {
        std::string stripped = stripNumericSuffix(alias);
        if (!isRiskyBareAlias(stripped)) {
            alias = stripped;
        }
    }
    return sanitizeLuaIdentifier(alias, "upval");
}

static int aliasQuality(const std::string& alias, float confidence) {
    if (alias.empty()) {
        return -1000;
    }
    if (isWeakAlias(alias)) {
        return -500;
    }

    int score = 100;
    if (isRegisterLikeAlias(alias)) {
        score -= 60;
    }
    if (isSyntheticParameterAlias(alias)) {
        score -= 55;
    }
    if (hasNumericSuffix(alias)) {
        score -= 25;
    }
    score -= (int)alias.size() / 8;
    score += (int)(std::clamp(confidence, 0.0f, 1.0f) * 45.0f);
    return score;
}

static bool shouldPreferAlias(const std::string& candidate, const std::string& current) {
    if (candidate.empty()) {
        return false;
    }
    if (current.empty()) {
        return true;
    }

    const bool candidateGeneric = isWeakAlias(candidate) || isGenericSemanticAlias(candidate);
    const bool currentGeneric = isWeakAlias(current) || isGenericSemanticAlias(current);
    if (!candidateGeneric && currentGeneric) {
        return true;
    }
    if (candidateGeneric && !currentGeneric) {
        return false;
    }
    return aliasQuality(candidate) > aliasQuality(current);
}

static void initializeSlotAliases(ExpressionContext& context) {
    struct SlotAliasChoice {
        int bestAnyScore = -10000;
        std::string bestAnyAlias;
        int bestSpecificScore = -10000;
        std::string bestSpecificAlias;
        std::unordered_set<std::string> specificCandidates;
    };
    std::unordered_map<int, SlotAliasChoice> bestBySlot;

    for (const auto& value : context.analyzed.values) {
        if (value.slot < 0) {
            continue;
        }

        if (const SSAInstruction* def = definingInstruction(context.analyzed, value.id)) {
            if (def->inst.stdOp == OP_GETGLOBAL || def->inst.stdOp == OP_GETIMPORT) {
                continue;
            }
        }

        std::string candidate = sanitizeLuaIdentifier(value.name, value.isParameter ? "p" : "v");
        if (candidate.empty() || isWeakAlias(candidate) || isRegisterLikeAlias(candidate) || isSyntheticParameterAlias(candidate)) {
            continue;
        }

        int score = aliasQuality(candidate, value.nameConfidence);
        auto& choice = bestBySlot[value.slot];
        if (score > choice.bestAnyScore) {
            choice.bestAnyScore = score;
            choice.bestAnyAlias = candidate;
        }
        if (!isGenericSemanticAlias(candidate) && score > choice.bestSpecificScore) {
            choice.bestSpecificScore = score;
            choice.bestSpecificAlias = candidate;
        }
        if (!isGenericSemanticAlias(candidate)) {
            choice.specificCandidates.insert(stripNumericSuffix(candidate));
        }
    }

    for (const auto& [slot, choice] : bestBySlot) {
        if (choice.specificCandidates.size() > 1) {
            continue;
        }
        std::string selected = choice.bestSpecificAlias;
        if (!selected.empty()) {
            context.slotAliases[slot] = selected;
        }
    }

    auto hasStateUpdateForSlot = [&](int slot) {
        for (const auto& instruction : context.analyzed.instructions) {
            if (instruction.defs.size() != 1 || instruction.uses.empty()) {
                continue;
            }
            int defValueId = instruction.defs.front();
            if (defValueId < 0 || defValueId >= (int)context.analyzed.values.size() ||
                context.analyzed.values[defValueId].slot != slot) {
                continue;
            }
            for (int useValueId : instruction.uses) {
                if (useValueId >= 0 && useValueId < (int)context.analyzed.values.size() &&
                    context.analyzed.values[useValueId].slot == slot) {
                    return true;
                }
            }
        }
        return false;
    };

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp != OP_MOVE || instruction.defs.size() != 1 || instruction.uses.size() != 1) {
            continue;
        }

        int defValueId = instruction.defs.front();
        int sourceValueId = instruction.uses.front();
        if (defValueId < 0 || defValueId >= (int)context.analyzed.values.size() ||
            sourceValueId < 0 || sourceValueId >= (int)context.analyzed.values.size()) {
            continue;
        }

        const auto& defValue = context.analyzed.values[defValueId];
        const auto& sourceValue = context.analyzed.values[sourceValueId];
        if (!sourceValue.isParameter || defValue.slot < context.sourceFunction.numParams ||
            context.slotAliases.count(defValue.slot) != 0 || !hasStateUpdateForSlot(defValue.slot)) {
            continue;
        }

        std::string targetDefault = localNameForSlot(context.sourceFunction, defValue.slot);
        if (!isRegisterLikeAlias(targetDefault)) {
            continue;
        }

        std::string sourceAlias = localNameForSlot(context.sourceFunction, sourceValue.slot);
        if (isLuaIdentifier(sourceAlias)) {
            context.slotAliases[defValue.slot] = sourceAlias;
        }
    }
}

static std::string slotAliasFor(ExpressionContext& context, int slot) {
    auto it = context.slotAliases.find(slot);
    if (it != context.slotAliases.end() && !it->second.empty()) {
        return it->second;
    }
    return localNameForSlot(context.sourceFunction, slot);
}

static std::string assignmentTargetForValue(ExpressionContext& context, int valueId) {
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return "_";
    }
    const auto& value = context.analyzed.values[valueId];
    const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
    if (def && isCallInstruction(*def)) {
        return sanitizeLuaIdentifier(value.name, value.slot >= 0 ? slotAliasFor(context, value.slot) : "result");
    }
    if (value.slot >= 0) {
        std::string alias = normalizeStructuredAlias(context, value.slot, value.name);
        if (!isLuaIdentifier(alias)) {
            alias = sanitizeLuaIdentifier(alias, slotAliasFor(context, value.slot));
        }
        return alias;
    }
    return sanitizeLuaIdentifier(value.name, "v");
}

static std::string upvalueAliasFor(ExpressionContext& context, int upvalueIndex) {
    std::string inherited;
    if (upvalueIndex >= 0 && upvalueIndex < (int)context.upvalueAliases.size()) {
        inherited = normalizeInheritedAlias(context.upvalueAliases[upvalueIndex]);
    }

    std::string declared;
    if (upvalueIndex >= 0 && upvalueIndex < (int)context.sourceFunction.upvalueNames.size() &&
        !context.sourceFunction.upvalueNames[upvalueIndex].empty()) {
        declared = normalizeUpvalueAliasName(context.sourceFunction.upvalueNames[upvalueIndex]);
    }

    if (!declared.empty() && shouldPreferAlias(declared, inherited)) {
        return declared;
    }
    if (declared.empty() && !inherited.empty() && isGenericSemanticAlias(inherited) &&
        context.sourceFunction.debugName.rfind("__", 0) == 0) {
        return "handler";
    }
    if (!inherited.empty()) {
        return sanitizeLuaIdentifier(inherited, "upval");
    }
    return "upval" + std::to_string(upvalueIndex);
}

static std::string constantOperandForIndex(ExpressionContext& context, int constantIndex) {
    if (constantIndex >= 0 && constantIndex < (int)context.sourceFunction.constants.size()) {
        return normalizeLiteral(context.sourceFunction.constants[constantIndex].toString({}));
    }
    return "nil";
}

static std::string normalizeStructuredAlias(ExpressionContext& context, int slot, std::string alias) {
    std::string slotAlias = slotAliasFor(context, slot);

    if (alias.empty() || isWeakAlias(alias) || isRegisterLikeAlias(alias) || isSyntheticParameterAlias(alias)) {
        return slotAlias;
    }

    if (alias.empty() || isRegisterLikeAlias(alias) || isSyntheticParameterAlias(alias)) {
        return slotAlias;
    }

    if (!slotAlias.empty() && aliasQuality(slotAlias) > aliasQuality(alias)) {
        return slotAlias;
    }

    return alias;
}

static std::string normalizeInheritedAlias(std::string alias) {
    if (alias.empty() || isWeakAlias(alias)) {
        return alias;
    }
    if (hasNumericSuffix(alias) && !isRegisterLikeAlias(alias)) {
        std::string stripped = stripNumericSuffix(alias);
        if (!isRiskyBareAlias(stripped)) {
            alias = stripped;
        }
    }
    return sanitizeLuaIdentifier(alias, "v");
}

static ExpressionContext forkContextWithAliases(ExpressionContext& context, const std::unordered_map<int, std::string>& aliases) {
    ExpressionContext derived = context;
    for (const auto& [slot, alias] : aliases) {
        if (!alias.empty()) {
            derived.slotAliases[slot] = alias;
        }
    }
    derived.expressionCache.clear();
    derived.expressionStack.clear();
    return derived;
}

static bool isInitialCapturedDefinition(ExpressionContext& context, int valueId,
                                        const std::unordered_set<int>& capturedValues) {
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return false;
    }

    const auto& value = context.analyzed.values[valueId];
    if (value.isParameter || value.slot < 0) {
        return false;
    }

    for (int candidateValueId : capturedValues) {
        if (candidateValueId < 0 || candidateValueId >= (int)context.analyzed.values.size() ||
            candidateValueId == valueId) {
            continue;
        }
        const auto& candidate = context.analyzed.values[candidateValueId];
        if (candidate.slot != value.slot) {
            continue;
        }
        if (candidate.definingInstruction >= 0 &&
            candidate.definingInstruction < value.definingInstruction) {
            return false;
        }
    }

    return true;
}

static bool isInitialCapturedMutableDefinition(ExpressionContext& context, int valueId) {
    return isInitialCapturedDefinition(context, valueId, context.capturedMutableValues);
}

static bool isInitialClosureCapturedDefinition(ExpressionContext& context, int valueId) {
    return isInitialCapturedDefinition(context, valueId, context.closureCapturedValues);
}

static bool tableHasNamedKeys(ExpressionContext& context, int valueId, std::initializer_list<const char*> keys) {
    auto tableIt = context.tables.find(valueId);
    if (tableIt == context.tables.end()) {
        return false;
    }

    for (const char* key : keys) {
        bool found = false;
        for (const auto& entry : tableIt->second.entries) {
            if (entry.namedKey.has_value() && *entry.namedKey == key) {
                found = true;
                break;
            }
        }
        if (!found) {
            return false;
        }
    }
    return true;
}

static std::unordered_set<int> collectLoopBlocks(ExpressionContext& context, int bodyBlock, int latchBlock, int postLoopBlock) {
    std::unordered_set<int> blocks;
    if (bodyBlock < 0) {
        return blocks;
    }

    std::vector<int> worklist{bodyBlock};
    while (!worklist.empty()) {
        int blockId = worklist.back();
        worklist.pop_back();

        if (blockId < 0 || blockId >= (int)context.analyzed.cfg.blocks.size() || !blocks.insert(blockId).second) {
            continue;
        }

        if (blockId == latchBlock) {
            continue;
        }

        for (const auto& edge : context.analyzed.cfg.edges) {
            if (edge.fromBlock != blockId) {
                continue;
            }
            if (edge.toBlock == postLoopBlock || edge.kind == CFGEdgeKind::LoopExit) {
                continue;
            }
            worklist.push_back(edge.toBlock);
        }
    }

    if (latchBlock >= 0) {
        blocks.insert(latchBlock);
    }
    return blocks;
}

static std::string inferLoopAliasForValue(ExpressionContext& context, int valueId, size_t position,
                                          const std::unordered_set<int>& loopBlocks, int iteratorSourceValueId) {
    auto hasMeaningfulLoopUse = [&]() {
        for (int blockId : loopBlocks) {
            if (blockId < 0 || blockId >= (int)context.analyzed.blocks.size()) {
                continue;
            }

            for (int instIndex : context.analyzed.blocks[blockId].instructionRefs) {
                const auto& instruction = context.analyzed.instructions[instIndex];
                if (instruction.inst.stdOp == OP_FORGPREP || instruction.inst.stdOp == OP_FORGPREP_NEXT ||
                    instruction.inst.stdOp == OP_FORGPREP_INEXT || instruction.inst.stdOp == OP_FORNPREP ||
                    instruction.inst.stdOp == OP_FORGLOOP || instruction.inst.stdOp == OP_FORNLOOP) {
                    continue;
                }
                if (std::find(instruction.uses.begin(), instruction.uses.end(), valueId) != instruction.uses.end()) {
                    return true;
                }
            }
        }
        return false;
    };

    if (valueId >= 0 && valueId < (int)context.analyzed.values.size() && !hasMeaningfulLoopUse()) {
        return "_";
    }

    if (position == 0 && tableHasNamedKeys(context, iteratorSourceValueId, {"Crews", "Stomps", "Airshots"})) {
        return "boardName";
    }
    if (position == 1 && tableHasNamedKeys(context, iteratorSourceValueId, {"Crews", "Stomps", "Airshots"})) {
        return "container";
    }

    bool looksLikeEntry = false;
    bool looksLikeRank = false;
    bool looksLikeChild = false;
    bool looksLikeContainer = false;

    for (int blockId : loopBlocks) {
        if (blockId < 0 || blockId >= (int)context.analyzed.blocks.size()) {
            continue;
        }

        for (int instIndex : context.analyzed.blocks[blockId].instructionRefs) {
            const auto& instruction = context.analyzed.instructions[instIndex];

            if (instruction.inst.stdOp == OP_GETTABLEKS && !instruction.uses.empty() && instruction.uses[0] == valueId &&
                instruction.inst.keyName.has_value()) {
                const std::string& key = *instruction.inst.keyName;
                if (key == "key" || key == "value") {
                    looksLikeEntry = true;
                }
            }

            if (instruction.inst.stdOp == OP_SETTABLEKS && !instruction.uses.empty() && instruction.uses[0] == valueId &&
                instruction.inst.keyName.has_value()) {
                const std::string& key = *instruction.inst.keyName;
                if (key == "LayoutOrder") {
                    looksLikeRank = true;
                }
            }

            if (instruction.inst.stdOp == OP_NAMECALL && !instruction.uses.empty() && instruction.uses[0] == valueId &&
                instruction.inst.keyName.has_value()) {
                const std::string& method = *instruction.inst.keyName;
                if (method == "Destroy" || method == "IsA") {
                    looksLikeChild = true;
                } else if (method == "GetChildren") {
                    looksLikeContainer = true;
                }
            }

            if ((instruction.inst.stdOp == OP_CALL || instruction.inst.stdOp == OP_NATIVECALL) &&
                instruction.uses.size() >= 2 && instruction.uses[1] == valueId) {
                const SSAInstruction* calleeDef = definingInstruction(context.analyzed, instruction.uses[0]);
                if (calleeDef && calleeDef->inst.stdOp == OP_GETIMPORT && calleeDef->inst.importName.has_value() &&
                    *calleeDef->inst.importName == "tostring") {
                    looksLikeRank = true;
                }
            }
        }
    }

    if (looksLikeEntry) {
        return "entry";
    }
    if (looksLikeChild) {
        return position == 0 ? "index" : "child";
    }
    if (looksLikeContainer) {
        return position == 0 ? "boardName" : "container";
    }
    if (looksLikeRank) {
        return "rank";
    }

    return position == 0 ? "key" : "value";
}

static std::unordered_map<int, std::string> inferLoopAliases(ExpressionContext& context, const SSAInstruction& instruction,
                                                             int bodyBlock, int latchBlock, int postLoopBlock) {
    std::unordered_map<int, std::string> aliases;
    std::unordered_set<int> loopBlocks = collectLoopBlocks(context, bodyBlock, latchBlock, postLoopBlock);
    int iteratorSourceValueId = !instruction.uses.empty() ? instruction.uses[0] : -1;

    std::vector<int> slots;
    if (instruction.inst.stdOp == OP_FORGPREP || instruction.inst.stdOp == OP_FORGPREP_NEXT || instruction.inst.stdOp == OP_FORGPREP_INEXT) {
        slots.push_back(instruction.inst.a + 3);
        slots.push_back(instruction.inst.a + 4);
    } else if (instruction.inst.stdOp == OP_FORNPREP) {
        slots.push_back(instruction.inst.a + 2);
    }

    for (size_t i = 0; i < slots.size(); ++i) {
        int slot = slots[i];
        int valueId = -1;
        std::vector<int> orderedLoopBlocks(loopBlocks.begin(), loopBlocks.end());
        std::sort(orderedLoopBlocks.begin(), orderedLoopBlocks.end());
        for (int blockId : orderedLoopBlocks) {
            valueId = findValueForSlotInBlock(context.analyzed, blockId, -1, slot);
            if (valueId >= 0) {
                break;
            }
        }
        if (valueId < 0) {
            valueId = valueIdForSlot(context, instruction, slot);
        }
        if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
            continue;
        }

        std::string alias = inferLoopAliasForValue(context, valueId, i, loopBlocks, iteratorSourceValueId);
        if (!alias.empty()) {
            aliases[slot] = alias;
        }
    }

    return aliases;
}

static void mergeAliases(std::vector<std::string>& target, const std::vector<std::string>& source) {
    if (target.size() < source.size()) {
        target.resize(source.size());
    }
    for (size_t i = 0; i < source.size(); ++i) {
        if (!source[i].empty() && (target[i].empty() || aliasQuality(source[i]) > aliasQuality(target[i]))) {
            target[i] = source[i];
        }
    }
}

static std::optional<std::string> renderNamedClosureDefinition(ExpressionContext& context, const std::string& qualifiedName,
                                                               int valueId, int depth) {
    const SSAInstruction* closureInstruction = nullptr;
    if (!isClosureValue(context, valueId, &closureInstruction) || !closureInstruction || qualifiedName.empty()) {
        return std::nullopt;
    }

    auto childFunction = resolveChildFunction(context, *closureInstruction);
    if (!childFunction.has_value()) {
        return std::nullopt;
    }
    if (!g_inlineClosureBodies.load(std::memory_order_relaxed)) {
        std::string functionName = context.functionDisplayNames
            ? displayNameForFunction(*context.functionDisplayNames, **childFunction)
            : canonicalProtoName(**childFunction);
        return qualifiedName + " = " + functionName;
    }

    auto childAst = buildClosureAst(context, *closureInstruction);
    if (!childAst.has_value()) {
        return std::nullopt;
    }

    return trimTrailingNewline(formatNamedAstFunction(*childAst, qualifiedName, depth));
}

static void collectStructuredAliasesRecursiveImpl(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                                  const std::vector<std::string>& upvalueAliases,
                                                  std::unordered_map<int, std::vector<std::string>>& aliasesByFunction,
                                                  std::unordered_set<int>& activeFunctions) {
    if (!activeFunctions.insert(sourceFunction.id).second) {
        return;
    }

    mergeAliases(aliasesByFunction[sourceFunction.id], upvalueAliases);

    SSAFunction analyzed = analyzeFunction(chunk, sourceFunction, opmap, upvalueAliases);
    ExpressionContext context{chunk, sourceFunction, opmap, analyzed, upvalueAliases};
    context.aliasesByFunction = &aliasesByFunction;
    initializeSlotAliases(context);

    for (const auto& instruction : context.analyzed.instructions) {
        auto childFunction = resolveChildFunction(context, instruction);
        if (!childFunction.has_value()) {
            continue;
        }

        std::vector<std::string> captureAliases = resolveClosureCaptureAliases(context, instruction, **childFunction);
        auto& childAliases = aliasesByFunction[(*childFunction)->id];
        std::vector<std::string> previousAliases = childAliases;

        std::unordered_set<size_t> preserveExactCaptureAliases;
        int capturePc = instruction.inst.pc + instruction.inst.width;
        for (size_t upvalueIndex = 0;
             upvalueIndex < captureAliases.size() && capturePc < (int)context.sourceFunction.instructions.size();
             ++upvalueIndex, ++capturePc) {
            int captureOp = context.opmap.lookup(context.sourceFunction.instructions[capturePc].opcode());
            if (captureOp != OP_CAPTURE) {
                break;
            }
            const auto& captureInst = context.sourceFunction.instructions[capturePc];
            int captureType = captureInst.a();
            int source = captureInst.b();
            if (captureType == 1 && context.analyzed.escapedMutableSlots.count(source) != 0) {
                preserveExactCaptureAliases.insert(upvalueIndex);
            }
        }

        if (childAliases.size() < captureAliases.size()) {
            childAliases.resize(captureAliases.size());
        }
        for (size_t i = 0; i < captureAliases.size(); ++i) {
            const std::string& candidate = captureAliases[i];
            if (candidate.empty()) {
                continue;
            }
            if (preserveExactCaptureAliases.count(i) != 0 ||
                childAliases[i].empty() || aliasQuality(candidate) > aliasQuality(childAliases[i])) {
                childAliases[i] = candidate;
            }
        }

        if (childAliases != previousAliases) {
            collectStructuredAliasesRecursiveImpl(chunk, **childFunction, opmap, childAliases, aliasesByFunction, activeFunctions);
        }
    }

    activeFunctions.erase(sourceFunction.id);
}

static void collectStructuredAliasesRecursive(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                              const std::vector<std::string>& upvalueAliases,
                                              std::unordered_map<int, std::vector<std::string>>& aliasesByFunction) {
    std::unordered_set<int> activeFunctions;
    collectStructuredAliasesRecursiveImpl(chunk, sourceFunction, opmap, upvalueAliases, aliasesByFunction, activeFunctions);
}

static std::string buildExpression(ExpressionContext& context, int valueId, int depth) {
    if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
        return "_";
    }

    if (auto cacheIt = context.expressionCache.find(valueId); cacheIt != context.expressionCache.end()) {
        return cacheIt->second;
    }

    if (context.expressionStack.count(valueId)) {
        const auto& stackedValue = context.analyzed.values[valueId];
        return stackedValue.isPhi
            ? normalizeStructuredAlias(context, stackedValue.slot, stackedValue.name)
            : stackedValue.name;
    }
    context.expressionStack.insert(valueId);

    const auto& value = context.analyzed.values[valueId];
    std::string result;

    const SSAInstruction* def = definingInstruction(context.analyzed, valueId);
    if (value.constantValue.has_value() && context.symbolicMutableValues.count(valueId)) {
        result = normalizeStructuredAlias(context, value.slot, value.name);
    } else if (value.constantValue.has_value()) {
        result = normalizeLiteral(*value.constantValue);
    } else if (value.isPhi) {
        if (const PhiNode* phi = phiForValue(context, valueId)) {
            if (context.symbolicMutableValues.count(valueId)) {
                result = normalizeStructuredAlias(context, value.slot, value.name);
            } else if (context.symbolicPhiValues.count(valueId)) {
                std::optional<int> parameterInput;
                for (const auto& [pred, inputValueId] : phi->inputs) {
                    (void)pred;
                    if (inputValueId >= 0 && inputValueId < (int)context.analyzed.values.size() &&
                        context.analyzed.values[inputValueId].isParameter) {
                        parameterInput = inputValueId;
                        break;
                    }
                }
                if (parameterInput.has_value()) {
                    result = buildExpression(context, *parameterInput, depth);
                } else if (value.slot >= 0 && value.slot < context.sourceFunction.numParams) {
                    result = slotAliasFor(context, value.slot);
                } else {
                    result = normalizeStructuredAlias(context, value.slot, value.name);
                }
            } else if (auto representative = choosePhiRepresentative(context, *phi); representative.has_value()) {
                result = buildExpression(context, *representative, depth);
            } else {
                result = normalizeStructuredAlias(context, value.slot, value.name);
            }
        } else {
            result = normalizeStructuredAlias(context, value.slot, value.name);
        }
    } else if (auto tableIt = context.tables.find(valueId); tableIt != context.tables.end()) {
        if (tableIt->second.inlineable) {
            result = renderTableLiteral(context, tableIt->second, depth);
        } else {
            result = value.name;
        }
    } else {
        if (!def) {
            if (value.slot >= 0 && value.slot < context.sourceFunction.numParams) {
                result = slotAliasFor(context, value.slot);
            } else {
                result = value.slot >= 0
                ? normalizeStructuredAlias(context, value.slot, value.name)
                : value.name;
            }
        } else if (context.foldedCallExpressions.count(def->index) != 0 && isCallInstruction(*def)) {
            result = buildCallExpression(context, *def, depth);
        } else if (isSideEffectingValue(context.analyzed, valueId) &&
                   def->inst.stdOp != OP_NEWTABLE &&
                   def->inst.stdOp != OP_DUPTABLE &&
                   def->inst.stdOp != OP_NEWCLOSURE &&
                   def->inst.stdOp != OP_DUPCLOSURE) {
            result = value.slot >= 0
                ? sanitizeLuaIdentifier(value.name, slotAliasFor(context, value.slot))
                : value.name;
        } else {
            auto useExpr = [&](size_t idx) -> std::string {
                return idx < def->uses.size() ? buildExpression(context, def->uses[idx], depth) : "_";
            };

            switch (def->inst.stdOp) {
                case OP_LOADNIL:
                case OP_LOADB:
                case OP_LOADN:
                case OP_LOADK:
                case OP_LOADKX:
                case OP_GETIMPORT:
                    result = value.constantValue.has_value() ? normalizeLiteral(*value.constantValue) : value.name;
                    break;
                case OP_GETGLOBAL: {
                    if (def->inst.keyName.has_value()) {
                        const std::string& key = *def->inst.keyName;
                        if (isIdentifierKey(key)) {
                            result = key;
                        } else {
                            result = "_G[" + escapeLuaStringLiteral(key) + "]";
                        }
                    } else {
                        result = "_G[" + escapeLuaStringLiteral("__global_" + std::to_string(def->inst.pc)) + "]";
                    }
                    break;
                }
                case OP_GETUPVAL: {
                    int upvalueIndex = def->inst.b;
                    result = upvalueAliasFor(context, upvalueIndex);
                    break;
                }
                case OP_MOVE:
                    result = useExpr(0);
                    break;
                case OP_GETTABLEKS:
                    result = formatNamedFieldAccess(useExpr(0), def->inst.keyName.value_or("key"));
                    break;
                case OP_GETTABLE:
                    result = formatIndexAccess(useExpr(0), useExpr(1));
                    break;
                case OP_GETTABLEN:
                    result = formatIndexAccess(useExpr(0), std::to_string((int)def->inst.c + 1));
                    break;
                case OP_GETVARARGS:
                    result = "...";
                    break;
                case OP_CONCAT: {
                    std::ostringstream out;
                    for (size_t i = 0; i < def->uses.size(); ++i) {
                        if (i) {
                            out << " .. ";
                        }
                        out << buildExpression(context, def->uses[i], depth);
                    }
                    result = out.str();
                    break;
                }
                case OP_ADD:
                case OP_SUB:
                case OP_MUL:
                case OP_DIV:
                case OP_MOD:
                case OP_POW:
                case OP_IDIV:
                case OP_AND:
                case OP_OR: {
                    static const std::unordered_map<int, std::string> ops = {
                        {OP_ADD, "+"}, {OP_SUB, "-"}, {OP_MUL, "*"}, {OP_DIV, "/"},
                        {OP_MOD, "%"}, {OP_POW, "^"}, {OP_IDIV, "//"},
                        {OP_AND, "and"}, {OP_OR, "or"},
                    };
                    auto it = ops.find(def->inst.stdOp);
                    result = useExpr(0) + " " + (it == ops.end() ? "?" : it->second) + " " + useExpr(1);
                    break;
                }
                case OP_ADDK:
                case OP_SUBK:
                case OP_MULK:
                case OP_DIVK:
                case OP_MODK:
                case OP_POWK:
                case OP_ANDK:
                case OP_ORK:
                case OP_IDIVK: {
                    static const std::unordered_map<int, std::string> ops = {
                        {OP_ADDK, "+"}, {OP_SUBK, "-"}, {OP_MULK, "*"}, {OP_DIVK, "/"},
                        {OP_MODK, "%"}, {OP_POWK, "^"}, {OP_ANDK, "and"}, {OP_ORK, "or"},
                        {OP_IDIVK, "//"},
                    };
                    auto it = ops.find(def->inst.stdOp);
                    result = useExpr(0) + " " + (it == ops.end() ? "?" : it->second) + " " +
                        constantOperandForIndex(context, def->inst.c);
                    break;
                }
                case OP_SUBRK:
                    result = constantOperandForIndex(context, def->inst.b) + " - " + useExpr(0);
                    break;
                case OP_DIVRK:
                    result = constantOperandForIndex(context, def->inst.b) + " / " + useExpr(0);
                    break;
                case OP_NOT:
                    result = "not " + useExpr(0);
                    break;
                case OP_MINUS:
                    result = "-" + useExpr(0);
                    break;
                case OP_LENGTH:
                    result = "#" + useExpr(0);
                    break;
                case OP_CALL:
                case OP_NATIVECALL:
                    result = buildCallExpression(context, *def, depth);
                    break;
                case OP_NEWCLOSURE:
                case OP_DUPCLOSURE:
                    result = renderClosureExpression(context, *def, depth);
                    break;
                default:
                    result = value.slot >= 0
                        ? normalizeStructuredAlias(context, value.slot, value.name)
                        : value.name;
                    break;
            }
        }
    }

    context.expressionStack.erase(valueId);
    context.expressionCache[valueId] = result;
    return result;
}

static void prepareTableConstructions(ExpressionContext& context) {
    populatePhiMap(context);

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp == OP_NEWTABLE || instruction.inst.stdOp == OP_DUPTABLE) {
            if (instruction.defs.size() == 1) {
                TableConstruction table;
                table.resultValueId = instruction.defs.front();
                if (instruction.inst.stdOp == OP_DUPTABLE &&
                    instruction.inst.d >= 0 &&
                    instruction.inst.d < (int)context.sourceFunction.constants.size()) {
                    const Constant& templateConstant = context.sourceFunction.constants[instruction.inst.d];
                    if (templateConstant.type == ConstantType::TableWithConstants) {
                        for (size_t i = 0; i < templateConstant.tableKeys.size() && i < templateConstant.tableConstantValues.size(); ++i) {
                            int valueIndex = templateConstant.tableConstantValues[i];
                            if (valueIndex < 0 || valueIndex >= (int)context.sourceFunction.constants.size()) {
                                continue;
                            }

                            int keyIndex = templateConstant.tableKeys[i];
                            if (keyIndex < 0 || keyIndex >= (int)context.sourceFunction.constants.size()) {
                                continue;
                            }

                            const Constant& keyConstant = context.sourceFunction.constants[keyIndex];
                            TableEntry entry;
                            if (keyConstant.type == ConstantType::String) {
                                if (isIdentifierKey(keyConstant.strVal)) {
                                    entry.namedKey = keyConstant.strVal;
                                } else {
                                    entry.keyExpression = keyConstant.toString(context.chunk.strings);
                                }
                            } else {
                                entry.keyExpression = normalizeLiteral(keyConstant.toString(context.chunk.strings));
                            }
                            entry.valueExpression = normalizeLiteral(context.sourceFunction.constants[valueIndex].toString(context.chunk.strings));
                            table.entries.push_back(std::move(entry));
                        }
                    }
                }
                context.tables[table.resultValueId] = std::move(table);
            }
            continue;
        }
    }

    auto isConstructionUse = [&](const SSAInstruction& instruction, int tableValueId) {
        if (instruction.inst.stdOp == OP_SETTABLEKS) {
            if (instruction.uses.size() >= 2 && instruction.uses[1] == tableValueId) {
                return true;
            }
            if (instruction.inst.keyName.has_value() && *instruction.inst.keyName == "__index" &&
                !instruction.uses.empty() && instruction.uses[0] == tableValueId) {
                return true;
            }
            return false;
        }
        if (instruction.inst.stdOp == OP_SETTABLE) {
            return instruction.uses.size() >= 2 && instruction.uses[1] == tableValueId;
        }
        if (instruction.inst.stdOp == OP_SETTABLEN) {
            return instruction.uses.size() >= 2 && instruction.uses[1] == tableValueId;
        }
        if (instruction.inst.stdOp == OP_SETLIST && !instruction.uses.empty()) {
            return instruction.uses[0] == tableValueId;
        }
        return false;
    };

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp == OP_SETTABLEKS) {
            int tableValueId = valueIdForSlot(context, instruction, instruction.inst.b);
            int sourceValueId = valueIdForSlot(context, instruction, instruction.inst.a);
            if (tableValueId < 0 && instruction.inst.keyName.has_value() &&
                *instruction.inst.keyName == "__index" && context.tables.count(sourceValueId)) {
                tableValueId = sourceValueId;
            }
            auto it = context.tables.find(tableValueId);
            if (it != context.tables.end() && instruction.inst.keyName.has_value() &&
                *instruction.inst.keyName == "__index" && sourceValueId == it->second.resultValueId) {
                it->second.selfReferential = true;
            }
        }
    }

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp == OP_SETTABLEKS) {
            int tableValueId = valueIdForSlot(context, instruction, instruction.inst.b);
            int sourceValueId = valueIdForSlot(context, instruction, instruction.inst.a);
            if (tableValueId < 0 && instruction.inst.keyName.has_value() &&
                *instruction.inst.keyName == "__index" && context.tables.count(sourceValueId)) {
                tableValueId = sourceValueId;
            }
            auto it = context.tables.find(tableValueId);
            if (it != context.tables.end()) {
                if (it->second.selfReferential) {
                    continue;
                }
                TableEntry entry;
                entry.namedKey = instruction.inst.keyName.value_or("key");
                entry.valueId = sourceValueId;
                inlineValueConstructorEntry(context, entry, sourceValueId);
                it->second.entries.push_back(std::move(entry));
                context.foldedInstructions.insert(instruction.index);
            }
            continue;
        }

        if (instruction.inst.stdOp == OP_SETTABLE) {
            int tableValueId = valueIdForSlot(context, instruction, instruction.inst.b);
            int sourceValueId = valueIdForSlot(context, instruction, instruction.inst.a);
            int keyValueId = valueIdForSlot(context, instruction, instruction.inst.c);
            auto it = context.tables.find(tableValueId);
            if (it != context.tables.end()) {
                if (it->second.selfReferential) {
                    continue;
                }
                TableEntry entry;
                entry.keyValueId = keyValueId;
                entry.valueId = sourceValueId;
                inlineValueConstructorEntry(context, entry, sourceValueId);
                it->second.entries.push_back(std::move(entry));
                context.foldedInstructions.insert(instruction.index);
            }
            continue;
        }

        if (instruction.inst.stdOp == OP_SETTABLEN) {
            int tableValueId = valueIdForSlot(context, instruction, instruction.inst.b);
            int sourceValueId = valueIdForSlot(context, instruction, instruction.inst.a);
            auto it = context.tables.find(tableValueId);
            if (it != context.tables.end()) {
                if (it->second.selfReferential) {
                    continue;
                }
                TableEntry entry;
                entry.numericKey = (int)instruction.inst.c + 1;
                entry.valueId = sourceValueId;
                inlineValueConstructorEntry(context, entry, sourceValueId);
                it->second.entries.push_back(std::move(entry));
                context.foldedInstructions.insert(instruction.index);
            }
            continue;
        }

        if (instruction.inst.stdOp == OP_SETLIST && instruction.uses.size() >= 2) {
            auto it = context.tables.find(instruction.uses[0]);
            if (it != context.tables.end()) {
                if (it->second.selfReferential) {
                    continue;
                }
                for (size_t i = 1; i < instruction.uses.size(); ++i) {
                    TableEntry entry;
                    entry.valueId = instruction.uses[i];
                    inlineValueConstructorEntry(context, entry, instruction.uses[i]);
                    it->second.entries.push_back(std::move(entry));
                }
                context.foldedInstructions.insert(instruction.index);
            }
        }
    }

    for (auto& [valueId, table] : context.tables) {
        int externalUseCount = 0;
        for (const auto& instruction : context.analyzed.instructions) {
            if (isConstructionUse(instruction, valueId)) {
                continue;
            }
            if (std::find(instruction.uses.begin(), instruction.uses.end(), valueId) != instruction.uses.end()) {
                ++externalUseCount;
            }
        }
        table.inlineable = externalUseCount <= 1 &&
            !(externalUseCount > 0 && tableHasNamedKeys(context, valueId, {"Crews", "Stomps", "Airshots"}));
    }

    for (const auto& [valueId, table] : context.tables) {
        bool preserveDefinition =
            context.capturedMutableValues.count(valueId) != 0 ||
            context.closureCapturedValues.count(valueId) != 0 ||
            isDirectClosureCaptureValue(context, valueId);
        if (!table.selfReferential && table.inlineable && !preserveDefinition) {
            if (const SSAInstruction* def = definingInstruction(context.analyzed, valueId)) {
                context.foldedInstructions.insert(def->index);
            }
        }
    }
}

static void prepareInlineableCallExpressions(ExpressionContext& context) {
    for (const auto& value : context.analyzed.values) {
        if (!canInlineSingleUseCallValue(context, value.id)) {
            continue;
        }

        const SSAInstruction* def = definingInstruction(context.analyzed, value.id);
        if (!def) {
            continue;
        }
        context.foldedCallExpressions.insert(def->index);
        context.foldedInstructions.insert(def->index);
    }
    context.expressionCache.clear();
}

static std::string renderCondition(ExpressionContext& context, const SSAInstruction& instruction) {
    auto useExpr = [&](size_t idx) -> std::string {
        return buildConditionOperand(context, instruction, idx);
    };
    auto renderBooleanCondition = [](std::string lhs, bool expectTruthy) -> std::string {
        if (lhs.rfind("not ", 0) == 0) {
            return expectTruthy ? lhs.substr(4) : lhs;
        }
        if (expectTruthy) {
            return lhs;
        }
        return lhs.find_first_of(" \t\n") == std::string::npos ? ("not " + lhs) : ("not (" + lhs + ")");
    };
    auto renderJumpXEqCondition = [&]() -> std::string {
        std::string lhs = useExpr(0);
        std::string rhs = instruction.inst.constantValue.value_or("nil");
        if (rhs == "true") {
            return renderBooleanCondition(lhs, instruction.inst.fallthroughOnMatch);
        }
        if (rhs == "false") {
            return renderBooleanCondition(lhs, !instruction.inst.fallthroughOnMatch);
        }
        const char* op = instruction.inst.fallthroughOnMatch ? " == " : " ~= ";
        return lhs + op + rhs;
    };

    switch (instruction.inst.stdOp) {
        case OP_JUMPIF:
            return "not " + useExpr(0);
        case OP_JUMPIFNOT:
            return useExpr(0);
        case OP_JUMPIFEQ:
            return useExpr(0) + " ~= " + useExpr(1);
        case OP_JUMPIFNOTEQ:
            return useExpr(0) + " == " + useExpr(1);
        case OP_JUMPIFLE:
            return useExpr(0) + " > " + useExpr(1);
        case OP_JUMPIFLT:
            return useExpr(0) + " >= " + useExpr(1);
        case OP_JUMPIFNOTLE:
            return useExpr(0) + " <= " + useExpr(1);
        case OP_JUMPIFNOTLT:
            return useExpr(0) + " < " + useExpr(1);
        case OP_JUMPXEQKNIL:
        case OP_JUMPXEQKB:
        case OP_JUMPXEQKN:
        case OP_JUMPXEQKS:
            return renderJumpXEqCondition();
        default:
            return "cond_" + std::to_string(instruction.inst.pc);
    }
}

static std::string invertCondition(std::string condition) {
    if (condition.empty()) {
        return "false";
    }
    if (condition.rfind("not ", 0) == 0) {
        return condition.substr(4);
    }
    return "not (" + condition + ")";
}

static CFGEdgeKind edgeKindBetween(const ExpressionContext& context, int fromBlock, int toBlock) {
    for (const auto& edge : context.analyzed.cfg.edges) {
        if (edge.fromBlock == fromBlock && edge.toBlock == toBlock) {
            return edge.kind;
        }
    }
    return CFGEdgeKind::Jump;
}

static bool canReachBlock(const ExpressionContext& context, int startBlock, int targetBlock, int stopBlock,
                          std::unordered_set<int>& seen) {
    if (startBlock < 0) {
        return false;
    }
    if (startBlock == targetBlock) {
        return true;
    }
    if (startBlock == stopBlock || !seen.insert(startBlock).second) {
        return false;
    }

    for (int succ : context.analyzed.cfg.blocks[startBlock].successors) {
        if (succ == stopBlock) {
            continue;
        }
        if (canReachBlock(context, succ, targetBlock, stopBlock, seen)) {
            return true;
        }
    }
    return false;
}

static bool canReachBlock(const ExpressionContext& context, int startBlock, int targetBlock, int stopBlock) {
    std::unordered_set<int> seen;
    return canReachBlock(context, startBlock, targetBlock, stopBlock, seen);
}

static int shortestDistanceToBlock(const ExpressionContext& context, int startBlock, int targetBlock, int stopBlock) {
    if (startBlock < 0 || targetBlock < 0 || startBlock >= (int)context.analyzed.cfg.blocks.size() ||
        targetBlock >= (int)context.analyzed.cfg.blocks.size()) {
        return -1;
    }
    if (startBlock == targetBlock) {
        return 0;
    }

    std::vector<int> distance(context.analyzed.cfg.blocks.size(), -1);
    std::vector<int> queue;
    queue.reserve(context.analyzed.cfg.blocks.size());

    distance[startBlock] = 0;
    queue.push_back(startBlock);

    for (size_t idx = 0; idx < queue.size(); ++idx) {
        int blockId = queue[idx];
        if (blockId == stopBlock) {
            continue;
        }
        if (blockId < 0 || blockId >= (int)context.analyzed.cfg.blocks.size()) {
            continue;
        }

        const auto& block = context.analyzed.cfg.blocks[blockId];
        for (int succ : block.successors) {
            if (succ < 0 || succ >= (int)context.analyzed.cfg.blocks.size()) {
                continue;
            }
            if (succ == stopBlock) {
                continue;
            }
            if (distance[succ] != -1) {
                continue;
            }
            distance[succ] = distance[blockId] + 1;
            if (succ == targetBlock) {
                return distance[succ];
            }
            queue.push_back(succ);
        }
    }

    return -1;
}

static bool isValidBlockId(const ExpressionContext& context, int blockId) {
    return blockId >= 0 && blockId < (int)context.analyzed.blocks.size();
}

static int nearestCommonPostDominator(const ExpressionContext& context, int firstBlock, int secondBlock) {
    if (!isValidBlockId(context, firstBlock) || !isValidBlockId(context, secondBlock)) {
        return -1;
    }

    std::unordered_set<int> firstChain;
    int current = firstBlock;
    while (isValidBlockId(context, current)) {
        firstChain.insert(current);
        if (current >= (int)context.analyzed.cfg.immediatePostDominator.size()) {
            break;
        }
        current = context.analyzed.cfg.immediatePostDominator[current];
    }

    current = secondBlock;
    while (isValidBlockId(context, current)) {
        if (firstChain.count(current)) {
            return current;
        }
        if (current >= (int)context.analyzed.cfg.immediatePostDominator.size()) {
            break;
        }
        current = context.analyzed.cfg.immediatePostDominator[current];
    }

    return -1;
}

static bool branchCanReachJoin(const ExpressionContext& context, int branchBlock, int joinBlock) {
    if (!isValidBlockId(context, branchBlock) || !isValidBlockId(context, joinBlock)) {
        return false;
    }
    if (branchBlock == joinBlock) {
        return true;
    }
    return canReachBlock(context, branchBlock, joinBlock, -1);
}

static int chooseConditionalJoinBlock(const ExpressionContext& context, int currentBlock, int branchTrue,
                                      int branchFalse, int stopBlock) {
    auto reachableFromBoth = [&](int candidate) {
        if (!isValidBlockId(context, candidate) || candidate == currentBlock) {
            return false;
        }

        bool trueReach = branchTrue < 0 || branchCanReachJoin(context, branchTrue, candidate);
        bool falseReach = branchFalse < 0 || branchCanReachJoin(context, branchFalse, candidate);
        return trueReach && falseReach;
    };

    int ipdomJoin = (currentBlock >= 0 && currentBlock < (int)context.analyzed.cfg.immediatePostDominator.size())
        ? context.analyzed.cfg.immediatePostDominator[currentBlock]
        : -1;
    if (reachableFromBoth(ipdomJoin)) {
        return ipdomJoin;
    }

    int mergedJoin = nearestCommonPostDominator(context, branchTrue, branchFalse);
    if (reachableFromBoth(mergedJoin)) {
        return mergedJoin;
    }

    if (reachableFromBoth(stopBlock)) {
        return stopBlock;
    }

    // Structurer v2 fallback: search for nearest reachable merge block.
    // This improves elseif/while/repeat recovery when immediate post-dominator is under-constrained.
    int bestJoin = -1;
    int bestScore = std::numeric_limits<int>::max();
    const int blockCount = (int)context.analyzed.cfg.blocks.size();
    for (int candidate = 0; candidate < blockCount; ++candidate) {
        if (!reachableFromBoth(candidate)) {
            continue;
        }
        if ((candidate == branchTrue || candidate == branchFalse) && candidate != stopBlock) {
            continue;
        }

        int dTrue = branchTrue < 0 ? 0 : shortestDistanceToBlock(context, branchTrue, candidate, stopBlock);
        int dFalse = branchFalse < 0 ? 0 : shortestDistanceToBlock(context, branchFalse, candidate, stopBlock);
        int dCurrent = shortestDistanceToBlock(context, currentBlock, candidate, stopBlock);
        if ((branchTrue >= 0 && dTrue < 0) || (branchFalse >= 0 && dFalse < 0)) {
            continue;
        }
        if (dCurrent < 0) {
            continue;
        }

        int score = dTrue + dFalse + (2 * dCurrent);
        if (candidate == ipdomJoin) {
            score -= 1;
        }
        if (score < bestScore || (score == bestScore && (bestJoin < 0 || candidate < bestJoin))) {
            bestScore = score;
            bestJoin = candidate;
        }
    }
    if (bestJoin >= 0) {
        return bestJoin;
    }

    return ipdomJoin;
}

static std::vector<int> loopBackPredecessors(const ExpressionContext& context, int headerBlock) {
    std::vector<int> preds;
    for (const auto& edge : context.analyzed.cfg.edges) {
        if (edge.toBlock == headerBlock && edge.kind == CFGEdgeKind::LoopBack) {
            preds.push_back(edge.fromBlock);
        }
    }
    return preds;
}

static bool isStructuredLoopLatch(const ExpressionContext& context, int blockId) {
    if (blockId < 0 || blockId >= (int)context.analyzed.blocks.size()) {
        return false;
    }
    const auto& block = context.analyzed.blocks[blockId];
    if (block.instructionRefs.empty()) {
        return false;
    }
    const auto& terminator = context.analyzed.instructions[block.instructionRefs.back()];
    return terminator.inst.stdOp != OP_FORGLOOP && terminator.inst.stdOp != OP_FORNLOOP;
}

static std::vector<int> structuredLoopBackPredecessors(const ExpressionContext& context, int headerBlock) {
    std::vector<int> preds;
    for (int pred : loopBackPredecessors(context, headerBlock)) {
        if (isStructuredLoopLatch(context, pred)) {
            preds.push_back(pred);
        }
    }
    return preds;
}

static std::string conditionForSuccessor(ExpressionContext& context, const SSAInstruction& terminator, int successor,
                                         int branchTrue, int branchFalse) {
    std::string base = renderCondition(context, terminator);
    if (successor == branchFalse) {
        return base;
    }
    if (successor == branchTrue) {
        return invertCondition(base);
    }
    return base;
}

static std::string repeatConditionForExit(ExpressionContext& context, const SSAInstruction& terminator, int exitBlock,
                                          int branchTrue, int branchFalse) {
    return conditionForSuccessor(context, terminator, exitBlock, branchTrue, branchFalse);
}

static void mergeVisitedBlocks(std::unordered_set<int>& destination, const std::unordered_set<int>& source) {
    destination.insert(source.begin(), source.end());
}

static std::string renderLoopHeader(ExpressionContext& context, const SSAInstruction& instruction) {
    auto useExpr = [&](size_t idx) -> std::string {
        return idx < instruction.uses.size() ? buildExpression(context, instruction.uses[idx]) : "_";
    };
    auto useIsNil = [&](size_t idx) -> bool {
        if (idx >= instruction.uses.size()) {
            return false;
        }
        int valueId = instruction.uses[idx];
        if (valueId < 0 || valueId >= (int)context.analyzed.values.size()) {
            return false;
        }
        const auto& value = context.analyzed.values[valueId];
        return value.constantValue.has_value() && *value.constantValue == "nil";
    };
    auto defName = [&](size_t idx, int fallbackSlot) -> std::string {
        std::string preferredSlotAlias = slotAliasFor(context, fallbackSlot);
        if (preferredSlotAlias == "_") {
            return preferredSlotAlias;
        }
        if (idx < instruction.defs.size()) {
            const auto& defValue = context.analyzed.values[instruction.defs[idx]];
            if (defValue.useCount == 0) {
                return std::string("_");
            }
            return normalizeStructuredAlias(context, defValue.slot, defValue.name);
        }
        return preferredSlotAlias;
    };
    auto inferredOpenCallArgument = [&](const SSAInstruction& callInstruction, int argumentOffset) -> int {
        if (callInstruction.inst.stdOp != OP_CALL && callInstruction.inst.stdOp != OP_NATIVECALL) {
            return -1;
        }
        if (callInstruction.inst.b != 0) {
            size_t useIndex = (size_t)argumentOffset;
            return useIndex < callInstruction.uses.size() ? callInstruction.uses[useIndex] : -1;
        }
        return currentValueForSlotAtInstruction(context.analyzed, callInstruction.index, callInstruction.inst.a + argumentOffset);
    };

    if (instruction.inst.stdOp == OP_FORGPREP || instruction.inst.stdOp == OP_FORGPREP_NEXT || instruction.inst.stdOp == OP_FORGPREP_INEXT) {
        std::string iteratorExpr;
        bool directIteratorExpr = false;
        if (!instruction.uses.empty()) {
            const SSAInstruction* iteratorDef = definingInstruction(context.analyzed, instruction.uses[0]);
            if (iteratorDef &&
                (iteratorDef->inst.stdOp == OP_CALL || iteratorDef->inst.stdOp == OP_NATIVECALL) &&
                iteratorDef->defs.size() == instruction.uses.size()) {
                bool directIterator = true;
                for (size_t i = 0; i < iteratorDef->defs.size(); ++i) {
                    if (iteratorDef->defs[i] != instruction.uses[i]) {
                        directIterator = false;
                        break;
                    }
                }
                if (directIterator) {
                    if (!iteratorDef->uses.empty()) {
                        const SSAInstruction* calleeDef = definingInstruction(context.analyzed, iteratorDef->uses[0]);
                        if (calleeDef && calleeDef->inst.stdOp == OP_NAMECALL && calleeDef->inst.keyName.has_value()) {
                            std::string objectExpr = "_";
                            if (!calleeDef->uses.empty()) {
                                int objectValueId = calleeDef->uses.front();
                                if (objectValueId >= 0 && objectValueId < (int)context.analyzed.values.size()) {
                                    const auto& objectValue = context.analyzed.values[objectValueId];
                                    if (objectValue.slot >= 0) {
                                        objectExpr = normalizeStructuredAlias(context, objectValue.slot, objectValue.name);
                                    } else {
                                        objectExpr = buildExpression(context, objectValueId, 0);
                                    }
                                }
                            }

                            std::ostringstream out;
                            out << objectExpr << ":" << *calleeDef->inst.keyName << "(";
                            for (size_t i = 2; i < iteratorDef->uses.size(); ++i) {
                                if (i > 2) {
                                    out << ", ";
                                }
                                out << buildExpression(context, iteratorDef->uses[i], 0);
                            }
                            out << ")";
                            iteratorExpr = out.str();
                        } else if (calleeDef && calleeDef->inst.stdOp == OP_GETIMPORT && calleeDef->inst.importName.has_value()) {
                            const std::string& importName = *calleeDef->inst.importName;
                            if (importName == "pairs" || importName == "ipairs") {
                                int stateValueId = inferredOpenCallArgument(*iteratorDef, 1);
                                if (stateValueId >= 0) {
                                    iteratorExpr = importName + "(" + buildExpression(context, stateValueId, 0) + ")";
                                } else {
                                    iteratorExpr = importName + "()";
                                }
                            } else {
                                iteratorExpr = buildCallExpression(context, *iteratorDef, 0);
                            }
                        } else {
                            iteratorExpr = buildCallExpression(context, *iteratorDef, 0);
                        }
                    } else {
                        iteratorExpr = buildCallExpression(context, *iteratorDef, 0);
                    }
                    directIteratorExpr = true;
                }
            }
        }

        if (iteratorExpr.empty()) {
            iteratorExpr = instruction.renderedText.value_or(useExpr(0));
        }
        if (!directIteratorExpr && !instruction.renderedText.has_value() &&
            instruction.uses.size() >= 3 && useIsNil(1) && useIsNil(2)) {
            iteratorExpr = "pairs(" + useExpr(0) + ")";
        }
        if (iteratorExpr.empty()) {
            iteratorExpr = useExpr(0);
        }
        return "for " + defName(0, instruction.inst.a + 3) + ", " + defName(1, instruction.inst.a + 4) + " in " + iteratorExpr + " do";
    }
    if (instruction.inst.stdOp == OP_FORNPREP) {
        return "for " + defName(0, instruction.inst.a + 2) + " = " + useExpr(2) + ", " + useExpr(0) + ", " + useExpr(1) + " do";
    }
    return "while true do";
}

static std::string renderInstruction(ExpressionContext& context, const SSAInstruction& instruction) {
    auto assignTarget = [&](size_t idx = 0) -> std::string {
        return idx < instruction.defs.size() ? assignmentTargetForValue(context, instruction.defs[idx]) : "_";
    };
    auto useExpr = [&](size_t idx) -> std::string {
        return idx < instruction.uses.size() ? buildExpression(context, instruction.uses[idx]) : "_";
    };
    auto definesCapturedMutableSlot = [&]() -> bool {
        if (instruction.defs.size() != 1) {
            return false;
        }
        int valueId = instruction.defs.front();
        return context.capturedMutableValues.count(valueId) != 0;
    };
    auto definesClosureCapturedSlot = [&]() -> bool {
        if (instruction.defs.size() != 1) {
            return false;
        }
        int valueId = instruction.defs.front();
        return context.closureCapturedValues.count(valueId) != 0 ||
            isDirectClosureCaptureValue(context, valueId);
    };
    auto renderCapturedMutableInit = [&]() -> std::string {
        if (instruction.defs.empty()) {
            return "_";
        }

        const auto& value = context.analyzed.values[instruction.defs.front()];
        std::string target = assignmentTargetForValue(context, instruction.defs.front());
        std::string rhs = "_";
        switch (instruction.inst.stdOp) {
            case OP_LOADNIL:
            case OP_LOADB:
            case OP_LOADN:
            case OP_LOADK:
            case OP_LOADKX:
            case OP_GETIMPORT:
            case OP_GETGLOBAL:
                rhs = value.constantValue.has_value()
                    ? normalizeLiteral(*value.constantValue)
                    : (instruction.inst.constantValue.has_value()
                        ? normalizeLiteral(*instruction.inst.constantValue)
                        : value.name);
                break;
            case OP_MOVE:
                rhs = useExpr(0);
                break;
            case OP_GETUPVAL:
                rhs = upvalueAliasFor(context, instruction.inst.b);
                break;
            default:
                rhs = buildExpression(context, instruction.defs.front(), 0);
                break;
        }

        bool isInitialDefinition = !value.isParameter;
        isInitialDefinition = isInitialDefinition && isInitialCapturedMutableDefinition(context, instruction.defs.front());
        if (rhs == target) {
            return "";
        }
        return (isInitialDefinition ? "local " : "") + target + " = " + rhs;
    };
    auto renderClosureCaptureInit = [&]() -> std::string {
        if (instruction.defs.empty()) {
            return "_";
        }
        int valueId = instruction.defs.front();
        const auto& value = context.analyzed.values[valueId];
        std::string target = assignmentTargetForValue(context, valueId);
        std::string rhs = "_";
        switch (instruction.inst.stdOp) {
            case OP_LOADNIL:
            case OP_LOADB:
            case OP_LOADN:
            case OP_LOADK:
            case OP_LOADKX:
            case OP_GETIMPORT:
            case OP_GETGLOBAL:
                rhs = value.constantValue.has_value()
                    ? normalizeLiteral(*value.constantValue)
                    : (instruction.inst.constantValue.has_value()
                        ? normalizeLiteral(*instruction.inst.constantValue)
                        : value.name);
                break;
            case OP_MOVE:
                rhs = useExpr(0);
                break;
            case OP_GETUPVAL:
                rhs = upvalueAliasFor(context, instruction.inst.b);
                break;
            case OP_GETTABLE:
            case OP_GETTABLEKS:
            case OP_GETTABLEN:
            case OP_NEWCLOSURE:
            case OP_DUPCLOSURE:
                rhs = buildExpression(context, valueId, 0);
                break;
            default:
                rhs = buildExpression(context, valueId, 0);
                break;
        }
        if (rhs == target) {
            return "";
        }
        bool isInitialDefinition = isInitialClosureCapturedDefinition(context, valueId);
        if (!isInitialDefinition && isDirectClosureCaptureValue(context, valueId) &&
            !hasEarlierDirectClosureCaptureInSameSlot(context, valueId)) {
            isInitialDefinition = true;
        }
        return (isInitialDefinition ? "local " : "") + target + " = " + rhs;
    };

    switch (instruction.inst.stdOp) {
        case OP_LOADNIL:
        case OP_LOADB:
        case OP_LOADN:
        case OP_LOADK:
        case OP_LOADKX:
        case OP_GETIMPORT:
        case OP_GETGLOBAL:
        case OP_MOVE:
        case OP_GETUPVAL:
        case OP_GETTABLE:
        case OP_GETTABLEKS:
        case OP_GETTABLEN:
        case OP_NEWCLOSURE:
        case OP_DUPCLOSURE:
            if (definesCapturedMutableSlot()) {
                return renderCapturedMutableInit();
            }
            if (definesClosureCapturedSlot()) {
                return renderClosureCaptureInit();
            }
            if (!instruction.defs.empty()) {
                return assignTarget() + " = " + buildExpression(context, instruction.defs.front(), 0);
            }
            return "-- " + instruction.inst.opName + " @pc " + std::to_string(instruction.inst.pc);
        case OP_NEWTABLE:
        case OP_DUPTABLE: {
            if (!instruction.defs.empty()) {
                auto tableIt = context.tables.find(instruction.defs.front());
                if (tableIt != context.tables.end() && !tableIt->second.selfReferential) {
                    return "local " + assignTarget() + " = " + renderTableLiteral(context, tableIt->second, 0);
                }
                return "local " + assignTarget() + " = {}";
            }
            return "{}";
        }
        case OP_CALL:
        case OP_NATIVECALL: {
            std::string callExpr = buildCallExpression(context, instruction, 0);
            if (instruction.defs.empty()) {
                return callExpr;
            }
            std::ostringstream out;
            out << "local ";
            for (size_t i = 0; i < instruction.defs.size(); ++i) {
                if (i) {
                    out << ", ";
                }
                out << assignTarget(i);
            }
            out << " = " << callExpr;
            return out.str();
        }
        case OP_SETTABLEKS: {
            int tableValueId = valueIdForSlot(context, instruction, instruction.inst.b);
            int sourceValueId = valueIdForSlot(context, instruction, instruction.inst.a);
            if (tableValueId < 0 && instruction.inst.keyName.has_value() &&
                *instruction.inst.keyName == "__index" && context.tables.count(sourceValueId)) {
                tableValueId = sourceValueId;
            }
            std::string tableExpr = tableValueId >= 0 ? buildExpression(context, tableValueId, 0) : "_";
            std::string key = instruction.inst.keyName.value_or("key");

            auto tableIt = context.tables.find(tableValueId);
            if (tableIt != context.tables.end() && tableIt->second.selfReferential &&
                key != "__index" && isIdentifierKey(key) && isQualifiedIdentifierPath(tableExpr)) {
                if (auto named = renderNamedClosureDefinition(context, tableExpr + "." + key, sourceValueId, 0);
                    named.has_value()) {
                    return *named;
                }
            }

            std::string valueExpr = sourceValueId >= 0 ? buildExpression(context, sourceValueId, 0) : "_";
            return formatNamedFieldAccess(tableExpr, key) + " = " + valueExpr;
        }
        case OP_SETTABLE: {
            std::string tableExpr = buildSlotExpression(context, instruction, instruction.inst.b);
            std::string keyExpr = buildSlotExpression(context, instruction, instruction.inst.c);
            std::string valueExpr = buildSlotExpression(context, instruction, instruction.inst.a);
            return formatIndexAccess(tableExpr, keyExpr) + " = " + valueExpr;
        }
        case OP_SETTABLEN: {
            std::string tableExpr = buildSlotExpression(context, instruction, instruction.inst.b);
            std::string valueExpr = buildSlotExpression(context, instruction, instruction.inst.a);
            return formatIndexAccess(tableExpr, std::to_string((int)instruction.inst.c + 1)) + " = " + valueExpr;
        }
        case OP_SETLIST: {
            std::string tableExpr = buildSlotExpression(context, instruction, instruction.inst.a);
            if (!instruction.uses.empty()) {
                tableExpr = useExpr(0);
            }

            std::vector<std::string> values;
            if (instruction.uses.size() >= 2) {
                for (size_t i = 1; i < instruction.uses.size(); ++i) {
                    values.push_back(useExpr(i));
                }
            } else {
                int valueCount = instruction.inst.c > 0 ? (int)instruction.inst.c - 1 : 1;
                for (int offset = 0; offset < valueCount; ++offset) {
                    values.push_back(buildSlotExpression(context, instruction, instruction.inst.b + offset));
                }
            }

            std::ostringstream out;
            int startIndex = (int)instruction.inst.aux;
            for (size_t i = 0; i < values.size(); ++i) {
                if (i) {
                    out << "\n";
                }
                out << tableExpr << "[" << (startIndex + (int)i) << "] = " << values[i];
            }
            return out.str();
        }
        case OP_SETUPVAL:
            return upvalueAliasFor(context, instruction.inst.b) + " = " + useExpr(0);
        case OP_SETGLOBAL:
            if (instruction.inst.keyName.has_value()) {
                const std::string& key = *instruction.inst.keyName;
                if (isIdentifierKey(key)) {
                    return key + " = " + useExpr(0);
                }
                return "_G[" + escapeLuaStringLiteral(key) + "] = " + useExpr(0);
            }
            return "_G[" + escapeLuaStringLiteral("__global_" + std::to_string(instruction.inst.pc)) + "] = " + useExpr(0);
        case OP_ADD:
        case OP_SUB:
        case OP_MUL:
        case OP_DIV:
        case OP_MOD:
        case OP_POW:
        case OP_IDIV:
        case OP_ADDK:
        case OP_SUBK:
        case OP_MULK:
        case OP_DIVK:
        case OP_MODK:
        case OP_POWK:
        case OP_AND:
        case OP_OR:
        case OP_ANDK:
        case OP_ORK:
        case OP_SUBRK:
        case OP_DIVRK:
        case OP_IDIVK:
        case OP_NOT:
        case OP_MINUS:
        case OP_LENGTH:
            return assignTarget() + " = " + (!instruction.defs.empty() ? buildExpression(context, instruction.defs.front(), 0) : "_");
        case OP_RETURN: {
            std::ostringstream out;
            out << "return";
            if (!instruction.uses.empty()) {
                out << " ";
                for (size_t i = 0; i < instruction.uses.size(); ++i) {
                    if (i) {
                        out << ", ";
                    }
                    const SSAInstruction* def = definingInstruction(context.analyzed, instruction.uses[i]);
                    if (def && (def->inst.stdOp == OP_CALL || def->inst.stdOp == OP_NATIVECALL) &&
                        context.analyzed.values[instruction.uses[i]].useCount == 1) {
                        out << buildCallExpression(context, *def, 0);
                    } else {
                        out << useExpr(i);
                    }
                }
            }
            return out.str();
        }
        default:
            return "-- " + instruction.inst.opName + " @pc " + std::to_string(instruction.inst.pc);
    }
}

static bool shouldEmitNonTerminator(const SSAInstruction& instruction, const ExpressionContext& context) {
    if (instruction.dead || context.foldedInstructions.count(instruction.index)) {
        return false;
    }

    auto definesCapturedMutableSlot = [&]() {
        if (instruction.defs.size() != 1) {
            return false;
        }
        int valueId = instruction.defs.front();
        return context.capturedMutableValues.count(valueId) != 0;
    };
    auto definesClosureCapturedSlot = [&]() {
        if (instruction.defs.size() != 1) {
            return false;
        }
        int valueId = instruction.defs.front();
        return context.closureCapturedValues.count(valueId) != 0 ||
            isDirectClosureCaptureValue(context, valueId);
    };

    if ((instruction.inst.stdOp == OP_NEWTABLE || instruction.inst.stdOp == OP_DUPTABLE) && !instruction.defs.empty()) {
        auto tableIt = context.tables.find(instruction.defs.front());
        if (tableIt != context.tables.end() && !tableIt->second.selfReferential && tableIt->second.inlineable) {
            if (definesCapturedMutableSlot() || definesClosureCapturedSlot()) {
                return true;
            }
            return false;
        }
    }

    auto isStateUpdate = [&]() {
        if (instruction.defs.size() != 1 || instruction.uses.empty()) {
            return false;
        }
        int defValueId = instruction.defs.front();
        int useValueId = instruction.uses.front();
        if (defValueId < 0 || defValueId >= (int)context.analyzed.values.size() ||
            useValueId < 0 || useValueId >= (int)context.analyzed.values.size()) {
            return false;
        }
        const auto& defValue = context.analyzed.values[defValueId];
        const auto& useValue = context.analyzed.values[useValueId];
        return defValue.slot >= 0 && defValue.slot == useValue.slot;
    };

    if (definesClosureCapturedSlot()) {
        return true;
    }

    switch (instruction.inst.stdOp) {
        case OP_LOADNIL:
        case OP_LOADB:
        case OP_LOADN:
        case OP_LOADK:
        case OP_LOADKX:
        case OP_GETGLOBAL:
        case OP_GETIMPORT:
        case OP_MOVE:
        case OP_GETUPVAL:
        case OP_GETTABLE:
        case OP_GETTABLEKS:
        case OP_GETTABLEN:
        case OP_NEWCLOSURE:
        case OP_DUPCLOSURE:
            return definesCapturedMutableSlot();
        case OP_NEWTABLE:
        case OP_DUPTABLE:
        case OP_CALL:
        case OP_NATIVECALL:
        case OP_SETTABLEKS:
        case OP_SETTABLE:
        case OP_SETTABLEN:
        case OP_SETLIST:
        case OP_SETUPVAL:
        case OP_SETGLOBAL:
            return true;
        case OP_ADD:
        case OP_SUB:
        case OP_MUL:
        case OP_DIV:
        case OP_MOD:
        case OP_POW:
        case OP_IDIV:
        case OP_ADDK:
        case OP_SUBK:
        case OP_MULK:
        case OP_DIVK:
        case OP_MODK:
        case OP_POWK:
        case OP_AND:
        case OP_OR:
        case OP_ANDK:
        case OP_ORK:
        case OP_SUBRK:
        case OP_DIVRK:
        case OP_IDIVK:
        case OP_NOT:
        case OP_MINUS:
        case OP_LENGTH:
            return isStateUpdate();
        default:
            return instruction.hasSideEffects && instruction.inst.stdOp != OP_NAMECALL;
    }
}

static bool isDirectLoopFeederCall(const SSAInstruction& instruction, const SSAInstruction& terminator,
                                   const ExpressionContext& context) {
    if ((instruction.inst.stdOp != OP_CALL && instruction.inst.stdOp != OP_NATIVECALL) ||
        (terminator.inst.stdOp != OP_FORGPREP && terminator.inst.stdOp != OP_FORGPREP_NEXT &&
         terminator.inst.stdOp != OP_FORGPREP_INEXT) ||
        instruction.defs.empty() ||
        instruction.defs.size() != terminator.uses.size()) {
        return false;
    }

    for (size_t i = 0; i < instruction.defs.size(); ++i) {
        if (instruction.defs[i] != terminator.uses[i]) {
            return false;
        }
        if (instruction.defs[i] < 0 || instruction.defs[i] >= (int)context.analyzed.values.size()) {
            return false;
        }
    }

    return true;
}

static std::unordered_set<int> collectNaturalLoopBlocks(const ExpressionContext& context, int headerBlock,
                                                        const std::vector<int>& latchBlocks) {
    std::unordered_set<int> blocks;
    if (headerBlock < 0 || headerBlock >= (int)context.analyzed.blocks.size() || latchBlocks.empty()) {
        return blocks;
    }

    blocks.insert(headerBlock);
    std::vector<int> worklist;
    for (int latchBlock : latchBlocks) {
        if (latchBlock < 0 || latchBlock >= (int)context.analyzed.blocks.size()) {
            continue;
        }
        if (blocks.insert(latchBlock).second) {
            worklist.push_back(latchBlock);
        }
    }

    while (!worklist.empty()) {
        int blockId = worklist.back();
        worklist.pop_back();
        for (int pred : context.analyzed.cfg.blocks[blockId].predecessors) {
            if (pred >= 0 && pred < (int)context.analyzed.blocks.size() && blocks.insert(pred).second && pred != headerBlock) {
                worklist.push_back(pred);
            }
        }
    }

    return blocks;
}

static int uniqueLoopExitBlock(const ExpressionContext& context, const std::unordered_set<int>& loopBlocks) {
    int exitBlock = -1;
    for (int blockId : loopBlocks) {
        if (blockId < 0 || blockId >= (int)context.analyzed.cfg.blocks.size()) {
            continue;
        }
        for (int succ : context.analyzed.cfg.blocks[blockId].successors) {
            if (loopBlocks.count(succ)) {
                continue;
            }
            if (exitBlock < 0) {
                exitBlock = succ;
            } else if (exitBlock != succ) {
                return -1;
            }
        }
    }
    return exitBlock;
}

static bool isRepeatLatchBlock(const ExpressionContext& context, int currentBlock, int candidateBlock) {
    if (candidateBlock < 0 || candidateBlock >= (int)context.analyzed.blocks.size() || candidateBlock == currentBlock) {
        return false;
    }

    const auto& cfgBlock = context.analyzed.cfg.blocks[candidateBlock];
    if (cfgBlock.successors.size() != 1 || cfgBlock.successors.front() != currentBlock) {
        return false;
    }

    const auto& ssaBlock = context.analyzed.blocks[candidateBlock];
    if (ssaBlock.instructionRefs.empty()) {
        return false;
    }

    int terminatorInstIndex = ssaBlock.instructionRefs.back();
    const auto& terminator = context.analyzed.instructions[terminatorInstIndex];
    if (terminator.inst.stdOp != OP_JUMPBACK) {
        return false;
    }

    for (int instIndex : ssaBlock.instructionRefs) {
        if (instIndex == terminatorInstIndex) {
            continue;
        }
        if (shouldEmitNonTerminator(context.analyzed.instructions[instIndex], context)) {
            return false;
        }
    }

    return true;
}

static std::vector<AstStatement> collectCapturedLoopPreheaderInitializers(ExpressionContext& context, int preheaderBlock,
                                                                          int headerBlock) {
    std::vector<AstStatement> statements;
    if (preheaderBlock < 0 || preheaderBlock >= (int)context.analyzed.blocks.size() ||
        headerBlock < 0 || headerBlock >= (int)context.analyzed.blocks.size()) {
        return statements;
    }

    std::unordered_set<int> emittedSlots;
    for (const auto& phi : context.analyzed.blocks[headerBlock].phis) {
        if (phi.resultValueId < 0 || !context.capturedMutableValues.count(phi.resultValueId)) {
            continue;
        }
        auto inputIt = phi.inputs.find(preheaderBlock);
        if (inputIt == phi.inputs.end()) {
            continue;
        }

        int inputValueId = inputIt->second;
        if (inputValueId < 0 || inputValueId >= (int)context.analyzed.values.size()) {
            continue;
        }

        const auto& phiValue = context.analyzed.values[phi.resultValueId];
        if (phiValue.slot < 0 || !emittedSlots.insert(phiValue.slot).second) {
            continue;
        }

        AstStatement raw;
        raw.kind = AstStatementKind::Raw;
        std::string target = assignmentTargetForValue(context, phi.resultValueId);
        std::string rhs;
        const auto& inputValue = context.analyzed.values[inputValueId];
        if (inputValue.constantValue.has_value()) {
            rhs = normalizeLiteral(*inputValue.constantValue);
        } else {
            rhs = buildExpression(context, inputValueId, 0);
        }
        bool isLocal = isInitialCapturedMutableDefinition(context, inputValueId);
        raw.text = (isLocal ? "local " : "") + target + " = " + rhs;
        statements.push_back(std::move(raw));
    }

    return statements;
}

static std::vector<AstStatement> buildRegionList(ExpressionContext& context, int entryBlock, int stopBlock,
                                                 std::unordered_set<int>& visited, int suppressedLoopHeader = -1,
                                                 bool breakOnStopEdge = false) {
    AstStatement block;
    block.kind = AstStatementKind::Block;

    int current = entryBlock;
    while (current >= 0 && current != stopBlock && !visited.count(current)) {
        visited.insert(current);
        const auto& cfgBlock = context.analyzed.cfg.blocks[current];
        const auto& ssaBlock = context.analyzed.blocks[current];

        int terminatorInstIndex = -1;
        if (!ssaBlock.instructionRefs.empty()) {
            terminatorInstIndex = ssaBlock.instructionRefs.back();
        }

        int loopExit = -1;
        int loopBody = -1;
        int branchTrue = -1;
        int branchFalse = -1;

        for (int succ : cfgBlock.successors) {
            for (const auto& edge : context.analyzed.cfg.edges) {
                if (edge.fromBlock == current && edge.toBlock == succ) {
                    if (edge.kind == CFGEdgeKind::LoopExit) {
                        loopExit = succ;
                    } else if (edge.kind == CFGEdgeKind::Fallthrough && loopBody == -1) {
                        loopBody = succ;
                    } else if (edge.kind == CFGEdgeKind::BranchTrue) {
                        branchTrue = succ;
                    } else if (edge.kind == CFGEdgeKind::BranchFalse) {
                        branchFalse = succ;
                    }
                }
            }
        }

        auto buildNestedRegion = [&](int nestedEntry, int nestedStop, bool commitVisited = true) {
            std::unordered_set<int> nestedVisited = visited;
            if (nestedEntry == current) {
                nestedVisited.erase(current);
            }
            std::vector<AstStatement> nestedBody = buildRegionList(
                context, nestedEntry, nestedStop, nestedVisited, suppressedLoopHeader, breakOnStopEdge
            );
            if (commitVisited) {
                mergeVisitedBlocks(visited, nestedVisited);
            }
            return nestedBody;
        };

        std::vector<AstStatement> currentStatements;
        for (int instIndex : ssaBlock.instructionRefs) {
            if (instIndex == terminatorInstIndex) {
                continue;
            }
            const auto& instruction = context.analyzed.instructions[instIndex];
            if (terminatorInstIndex >= 0) {
                const auto& terminator = context.analyzed.instructions[terminatorInstIndex];
                if (isInlineableConditionProducer(context, instruction, terminator)) {
                    continue;
                }
            }
            if ((instruction.inst.stdOp == OP_CALL || instruction.inst.stdOp == OP_NATIVECALL) &&
                terminatorInstIndex >= 0) {
                const auto& terminator = context.analyzed.instructions[terminatorInstIndex];
                if (isDirectLoopFeederCall(instruction, terminator, context)) {
                    continue;
                }
                if (terminator.inst.stdOp == OP_RETURN &&
                    instruction.defs.size() == terminator.uses.size() &&
                    !instruction.defs.empty()) {
                    bool directReturn = true;
                    for (size_t i = 0; i < instruction.defs.size(); ++i) {
                        if (instruction.defs[i] != terminator.uses[i] ||
                            context.analyzed.values[instruction.defs[i]].useCount != 1) {
                            directReturn = false;
                            break;
                        }
                    }
                    if (directReturn) {
                        continue;
                    }
                }
            }
            if (!shouldEmitNonTerminator(instruction, context)) {
                continue;
            }
            AstStatement raw;
            raw.kind = AstStatementKind::Raw;
            raw.text = renderInstruction(context, instruction);
            if (raw.text.empty()) {
                continue;
            }
            currentStatements.push_back(std::move(raw));
        }

        auto appendCurrentStatements = [&]() {
            for (auto& stmt : currentStatements) {
                block.body.push_back(std::move(stmt));
            }
            currentStatements.clear();
        };

        if (terminatorInstIndex >= 0) {
            const auto& terminator = context.analyzed.instructions[terminatorInstIndex];
            if (terminator.inst.stdOp == OP_FORGPREP || terminator.inst.stdOp == OP_FORGPREP_NEXT ||
                terminator.inst.stdOp == OP_FORGPREP_INEXT || terminator.inst.stdOp == OP_FORNPREP) {
                if (ssaBlock.instructionRefs.size() >= 2) {
                    const auto& iteratorSetup =
                        context.analyzed.instructions[ssaBlock.instructionRefs[ssaBlock.instructionRefs.size() - 2]];
                    if (isDirectLoopFeederCall(iteratorSetup, terminator, context) && !currentStatements.empty()) {
                        std::string setupText = renderInstruction(context, iteratorSetup);
                        if (currentStatements.back().kind == AstStatementKind::Raw &&
                            currentStatements.back().text == setupText) {
                            currentStatements.pop_back();
                        }
                    }
                }

                int loopLatch = loopExit;
                int postLoop = -1;
                if (loopLatch >= 0) {
                    for (const auto& edge : context.analyzed.cfg.edges) {
                        if (edge.fromBlock == loopLatch && edge.kind == CFGEdgeKind::LoopExit) {
                            postLoop = edge.toBlock;
                            break;
                        }
                    }
                }
                ExpressionContext loopContext = forkContextWithAliases(
                    context,
                    inferLoopAliases(context, terminator, loopBody, loopLatch, postLoop)
                );

                std::vector<AstStatement> preheaderInit =
                    collectCapturedLoopPreheaderInitializers(loopContext, current, loopBody);
                for (auto& stmt : preheaderInit) {
                    bool duplicate = false;
                    for (const auto& existing : block.body) {
                        if (existing.kind == AstStatementKind::Raw && existing.text == stmt.text) {
                            duplicate = true;
                            break;
                        }
                    }
                    if (!duplicate) {
                        for (const auto& existing : currentStatements) {
                            if (existing.kind == AstStatementKind::Raw && existing.text == stmt.text) {
                                duplicate = true;
                                break;
                            }
                        }
                    }
                    if (!duplicate) {
                        currentStatements.push_back(std::move(stmt));
                    }
                }

                appendCurrentStatements();
                AstStatement loop;
                loop.kind = AstStatementKind::Loop;
                loop.header = renderLoopHeader(loopContext, terminator);
                if (loopBody >= 0) {
                    loop.body = buildRegionList(loopContext, loopBody, loopLatch, visited);
                }
                block.body.push_back(loop);
                if (loopLatch >= 0) {
                    visited.insert(loopLatch);
                }
                current = postLoop;
                continue;
            }

            if (terminator.inst.stdOp == OP_JUMPIF || terminator.inst.stdOp == OP_JUMPIFNOT ||
                terminator.inst.stdOp == OP_JUMPIFEQ || terminator.inst.stdOp == OP_JUMPIFNOTEQ ||
                terminator.inst.stdOp == OP_JUMPIFLE || terminator.inst.stdOp == OP_JUMPIFLT ||
                terminator.inst.stdOp == OP_JUMPIFNOTLE || terminator.inst.stdOp == OP_JUMPIFNOTLT ||
                terminator.inst.stdOp == OP_JUMPXEQKNIL || terminator.inst.stdOp == OP_JUMPXEQKB ||
                terminator.inst.stdOp == OP_JUMPXEQKN || terminator.inst.stdOp == OP_JUMPXEQKS) {
                auto canFormWhile = [&](int bodyBlock, int exitBlock) -> bool {
                    if (bodyBlock < 0 || exitBlock < 0 || bodyBlock == exitBlock) {
                        return false;
                    }

                    std::vector<int> latchBlocks = structuredLoopBackPredecessors(context, current);
                    if (latchBlocks.empty()) {
                        return false;
                    }

                    if (current < 0 || current >= (int)context.analyzed.cfg.immediatePostDominator.size()) {
                        return false;
                    }
                    if (context.analyzed.cfg.immediatePostDominator[current] != exitBlock) {
                        return false;
                    }

                    auto hasDirectLoopBackToHeader = [&](int fromBlock) -> bool {
                        for (const auto& edge : context.analyzed.cfg.edges) {
                            if (edge.fromBlock == fromBlock && edge.toBlock == current &&
                                edge.kind == CFGEdgeKind::LoopBack) {
                                return true;
                            }
                        }
                        return false;
                    };

                    for (int latchBlock : latchBlocks) {
                        if (latchBlock == bodyBlock) {
                            if (hasDirectLoopBackToHeader(bodyBlock)) {
                                return true;
                            }
                            continue;
                        }
                        if (canReachBlock(context, bodyBlock, latchBlock, exitBlock)) {
                            return true;
                        }
                    }
                    return false;
                };

                int repeatLatch = -1;
                int repeatExit = -1;
                if (current >= 0 &&
                    current < (int)context.analyzed.cfg.immediatePostDominator.size()) {
                    if (branchTrue >= 0 && isRepeatLatchBlock(context, current, branchTrue) &&
                        context.analyzed.cfg.immediatePostDominator[current] == branchFalse) {
                        repeatLatch = branchTrue;
                        repeatExit = branchFalse;
                    } else if (branchFalse >= 0 && isRepeatLatchBlock(context, current, branchFalse) &&
                               context.analyzed.cfg.immediatePostDominator[current] == branchTrue) {
                        repeatLatch = branchFalse;
                        repeatExit = branchTrue;
                    }
                }

                if (repeatLatch >= 0 && repeatExit >= 0) {
                    AstStatement loop;
                    loop.kind = AstStatementKind::Loop;
                    loop.header = "repeat";
                    loop.footer = "until " + repeatConditionForExit(context, terminator, repeatExit, branchTrue, branchFalse);
                    loop.body = std::move(currentStatements);
                    block.body.push_back(std::move(loop));
                    visited.insert(repeatLatch);
                    current = repeatExit;
                    continue;
                }

                if (canFormWhile(branchFalse, branchTrue) || canFormWhile(branchTrue, branchFalse)) {
                    int bodyBlock = canFormWhile(branchFalse, branchTrue) ? branchFalse : branchTrue;
                    int exitBlock = bodyBlock == branchFalse ? branchTrue : branchFalse;

                    appendCurrentStatements();
                    AstStatement loop;
                    loop.kind = AstStatementKind::Loop;
                    loop.header = "while " + conditionForSuccessor(context, terminator, bodyBlock, branchTrue, branchFalse) + " do";
                    loop.body = buildNestedRegion(bodyBlock, exitBlock, true);
                    block.body.push_back(loop);
                    current = exitBlock;
                    continue;
                }

                if (current != suppressedLoopHeader) {
                    std::vector<int> latchBlocks = structuredLoopBackPredecessors(context, current);
                    std::unordered_set<int> naturalLoopBlocks = collectNaturalLoopBlocks(context, current, latchBlocks);
                    int naturalExit = uniqueLoopExitBlock(context, naturalLoopBlocks);
                    if (naturalLoopBlocks.size() > 2 && naturalExit >= 0) {
                        std::unordered_set<int> nestedVisited = visited;
                        nestedVisited.erase(current);
                        std::vector<AstStatement> nestedBody = buildRegionList(
                            context, current, naturalExit, nestedVisited, current, true
                        );
                        mergeVisitedBlocks(visited, nestedVisited);

                        AstStatement loop;
                        loop.kind = AstStatementKind::Loop;
                        loop.header = "while true do";
                        loop.body = std::move(nestedBody);
                        block.body.push_back(std::move(loop));
                        current = naturalExit;
                        continue;
                    }
                }

                if (breakOnStopEdge && stopBlock >= 0 &&
                    ((branchTrue == stopBlock && branchFalse >= 0 && branchFalse != stopBlock) ||
                     (branchFalse == stopBlock && branchTrue >= 0 && branchTrue != stopBlock))) {
                    appendCurrentStatements();

                    AstStatement ifStmt;
                    ifStmt.kind = AstStatementKind::If;
                    ifStmt.header = repeatConditionForExit(context, terminator, stopBlock, branchTrue, branchFalse);

                    AstStatement breakStmt;
                    breakStmt.kind = AstStatementKind::Raw;
                    breakStmt.text = "break";
                    ifStmt.body.push_back(std::move(breakStmt));
                    block.body.push_back(std::move(ifStmt));

                    current = branchTrue == stopBlock ? branchFalse : branchTrue;
                    continue;
                }

                appendCurrentStatements();
                AstStatement ifStmt;
                ifStmt.kind = AstStatementKind::If;
                std::string condition = renderCondition(context, terminator);

                int join = chooseConditionalJoinBlock(context, current, branchTrue, branchFalse, stopBlock);
                if (!isValidBlockId(context, join) && isValidBlockId(context, stopBlock)) {
                    join = stopBlock;
                }

                int thenBlock = branchFalse;
                int elseBlock = branchTrue;

                if (thenBlock == join && elseBlock >= 0 && elseBlock != join) {
                    condition = invertCondition(condition);
                    thenBlock = elseBlock;
                    elseBlock = -1;
                } else if (elseBlock == join) {
                    elseBlock = -1;
                }

                ifStmt.header = condition;

                if (thenBlock >= 0 && thenBlock != join) {
                    ifStmt.body = buildRegionList(context, thenBlock, join, visited);
                }

                if (elseBlock >= 0 && elseBlock != join) {
                    ifStmt.elseBody = buildRegionList(context, elseBlock, join, visited);
                }

                if (ifStmt.body.empty() && ifStmt.elseBody.empty()) {
                    current = isValidBlockId(context, join) ? join : stopBlock;
                    continue;
                }

                block.body.push_back(ifStmt);
                current = isValidBlockId(context, join) ? join : stopBlock;
                continue;
            }

            if (!terminator.dead &&
                terminator.inst.stdOp != OP_UNKNOWN &&
                terminator.inst.opName != "???" &&
                terminator.inst.stdOp != OP_FORGLOOP &&
                terminator.inst.stdOp != OP_FORNLOOP &&
                terminator.inst.stdOp != OP_JUMP &&
                terminator.inst.stdOp != OP_JUMPBACK &&
                terminator.inst.stdOp != OP_PREPVARARGS &&
                terminator.inst.stdOp != OP_NOP &&
                shouldEmitNonTerminator(terminator, context) &&
                !context.foldedInstructions.count(terminator.index)) {
                appendCurrentStatements();
                AstStatement raw;
                raw.kind = AstStatementKind::Raw;
                raw.text = renderInstruction(context, terminator);
                if (!raw.text.empty()) {
                    block.body.push_back(raw);
                }
            }
        }

        appendCurrentStatements();

        if (!cfgBlock.successors.empty()) {
            current = cfgBlock.successors.front();
        } else {
            break;
        }
    }

    return block.body;
}
} // namespace

namespace {
struct StructuringQuality {
    float confidence = 1.0f;
    int placeholderCount = 0;
    int emptyIfCount = 0;
    int whileTrueCount = 0;
    bool recommendFallback = false;
};

static std::atomic<int> g_structuredFunctionsProcessed{0};
static std::atomic<int> g_structuredFunctionsFallback{0};

static bool isIdentifierChar(unsigned char ch) {
    return std::isalnum(ch) != 0 || ch == '_';
}

static int countExactToken(const std::string& text, const std::string& token) {
    if (token.empty() || text.empty()) {
        return 0;
    }
    int count = 0;
    size_t pos = 0;
    while ((pos = text.find(token, pos)) != std::string::npos) {
        bool leftBoundary = pos == 0 || !isIdentifierChar((unsigned char)text[pos - 1]);
        bool rightBoundary = (pos + token.size() >= text.size()) ||
            !isIdentifierChar((unsigned char)text[pos + token.size()]);
        if (leftBoundary && rightBoundary) {
            ++count;
        }
        pos += token.size();
    }
    return count;
}

static int countSubstring(const std::string& text, const std::string& needle) {
    if (needle.empty() || text.empty()) {
        return 0;
    }
    int count = 0;
    size_t pos = 0;
    while ((pos = text.find(needle, pos)) != std::string::npos) {
        ++count;
        pos += needle.size();
    }
    return count;
}

static AstFunction makeFunctionShell(const Function& sourceFunction) {
    AstFunction function;
    function.name = isUsableFunctionName(sourceFunction.debugName)
        ? sourceFunction.debugName
        : canonicalProtoName(sourceFunction);
    for (int slot = 0; slot < sourceFunction.numParams; ++slot) {
        function.params.push_back(localNameForSlot(sourceFunction, slot));
    }
    if (sourceFunction.isVararg) {
        function.params.push_back("...");
    }
    function.body.kind = AstStatementKind::Block;
    return function;
}

static std::vector<AstStatement> collectMissingDirectCaptureInitializers(
    ExpressionContext& context, const std::vector<AstStatement>& existingStatements
) {
    (void)existingStatements;

    std::unordered_set<int> emittedSlots;
    std::vector<AstStatement> initializers;

    for (const auto& instruction : context.analyzed.instructions) {
        if (instruction.inst.stdOp != OP_CAPTURE || instruction.inst.a != 1 || instruction.uses.empty()) {
            continue;
        }

        int capturedValueId = instruction.uses.front();
        if (capturedValueId < 0 || capturedValueId >= (int)context.analyzed.values.size()) {
            continue;
        }

        const auto& capturedValue = context.analyzed.values[capturedValueId];
        if (capturedValue.slot < 0 || !emittedSlots.insert(capturedValue.slot).second) {
            continue;
        }
        if (!capturedValue.constantValue.has_value()) {
            continue;
        }

        std::string target = sanitizeLuaIdentifier(slotAliasFor(context, capturedValue.slot), "v");
        if (!isLuaIdentifier(target)) {
            continue;
        }

        std::string rhs = normalizeLiteral(*capturedValue.constantValue);
        if (rhs.empty() || rhs == target) {
            continue;
        }

        AstStatement raw;
        raw.kind = AstStatementKind::Raw;
        raw.text = "local " + target + " = " + rhs;
        initializers.push_back(std::move(raw));
    }

    return initializers;
}

static StructuringQuality evaluateStructuredQuality(const AstFunction& function, const SSAFunction& analyzed) {
    StructuringQuality quality;
    std::string rendered = formatAstFunction(function);

    quality.placeholderCount =
        countExactToken(rendered, "condition") +
        countExactToken(rendered, "_");
    quality.emptyIfCount = countSubstring(rendered, "then\nend") + countSubstring(rendered, "then\r\nend");
    quality.whileTrueCount = countExactToken(rendered, "while true do");

    if (rendered.empty()) {
        quality.confidence -= 0.7f;
    }
    if (!analyzed.instructions.empty() && function.body.body.empty()) {
        quality.confidence -= 0.55f;
    }
    quality.confidence -= std::min(0.45f, quality.placeholderCount * 0.03f);
    quality.confidence -= std::min(0.25f, quality.emptyIfCount * 0.08f);
    quality.confidence -= std::min(0.15f, quality.whileTrueCount * 0.03f);
    if (quality.confidence < 0.0f) {
        quality.confidence = 0.0f;
    }

    const bool sufficientlyComplex = analyzed.instructions.size() >= 12;
    quality.recommendFallback =
        ((!analyzed.instructions.empty() && function.body.body.empty()) ||
         (sufficientlyComplex &&
          (quality.confidence < 0.56f ||
           quality.placeholderCount >= 10 ||
           (quality.placeholderCount >= 6 && quality.emptyIfCount > 0))));
    return quality;
}

static AstFunction buildStructuredFunctionFromContext(ExpressionContext& context) {
    AstFunction function = makeFunctionShell(context.sourceFunction);
    if (!context.analyzed.blocks.empty() && !context.analyzed.cfg.blocks.empty()) {
        std::unordered_set<int> visited;
        function.body.body = buildRegionList(context, 0, -1, visited);
        std::vector<AstStatement> captureInitializers =
            collectMissingDirectCaptureInitializers(context, function.body.body);
        if (!captureInitializers.empty()) {
            std::vector<AstStatement> merged;
            merged.reserve(captureInitializers.size() + function.body.body.size());
            for (auto& initializer : captureInitializers) {
                merged.push_back(std::move(initializer));
            }
            for (auto& statement : function.body.body) {
                merged.push_back(std::move(statement));
            }
            function.body.body = std::move(merged);
        }
    }
    return function;
}

static AstFunction fallbackFunctionToLegacyBody(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                                const StructuringQuality& quality,
                                                const std::string* reason = nullptr) {
    AstFunction fallback = makeFunctionShell(sourceFunction);

    AstStatement note;
    note.kind = AstStatementKind::Raw;
    note.text =
        "-- Structured fallback: legacy body emitter\n"
        "-- confidence=" + std::to_string(quality.confidence) +
        " placeholders=" + std::to_string(quality.placeholderCount);
    if (reason && !reason->empty()) {
        note.text += "\n-- reason=" + *reason;
    }
    fallback.body.body.push_back(std::move(note));

    AstStatement body;
    body.kind = AstStatementKind::Raw;
    std::string legacyBody = trimSpace(generateFunctionBodyCode(chunk, opmap, sourceFunction));
    if (legacyBody.empty()) {
        legacyBody = "-- legacy fallback body unavailable";
    }
    body.text = "-- legacy fallback body emitted\n" + legacyBody;
    fallback.body.body.push_back(std::move(body));
    return fallback;
}

static AstFunction structureFunctionWithPolicy(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                               const std::vector<std::string>& upvalueAliases,
                                               const std::unordered_map<int, std::vector<std::string>>* aliasesByFunction,
                                               const std::vector<std::string>* functionDisplayNames = nullptr) {
    try {
        SSAFunction analyzed = analyzeFunction(chunk, sourceFunction, opmap, upvalueAliases);
        ExpressionContext context{chunk, sourceFunction, opmap, analyzed, upvalueAliases};
        context.aliasesByFunction = aliasesByFunction;
        context.functionDisplayNames = functionDisplayNames;
        initializeSlotAliases(context);
        populatePhiMap(context);
        markSymbolicLoopPhiValues(context);
        markSymbolicConditionalPhiValues(context);
        markCapturedMutableSlots(context);
        markClosureCapturedValues(context);
        prepareTableConstructions(context);
        prepareInlineableCallExpressions(context);

        AstFunction function = buildStructuredFunctionFromContext(context);
        StructuringQuality quality = evaluateStructuredQuality(function, analyzed);
        g_structuredFunctionsProcessed.fetch_add(1, std::memory_order_relaxed);
        if (quality.recommendFallback) {
            g_structuredFunctionsFallback.fetch_add(1, std::memory_order_relaxed);
            fprintf(stderr,
                    "[*] Structured fallback for proto#%d (confidence=%.2f placeholders=%d)\n",
                    sourceFunction.id, quality.confidence, quality.placeholderCount);
            return fallbackFunctionToLegacyBody(chunk, sourceFunction, opmap, quality);
        }
        return function;
    } catch (const std::exception& ex) {
        g_structuredFunctionsProcessed.fetch_add(1, std::memory_order_relaxed);
        g_structuredFunctionsFallback.fetch_add(1, std::memory_order_relaxed);
        fprintf(stderr, "[*] Structured fallback for proto#%d due to exception: %s\n",
                sourceFunction.id, ex.what());

        StructuringQuality degraded;
        degraded.confidence = 0.0f;
        degraded.placeholderCount = 9999;
        degraded.recommendFallback = true;
        std::string reason = std::string("exception: ") + ex.what();
        return fallbackFunctionToLegacyBody(chunk, sourceFunction, opmap, degraded, &reason);
    }
}

static AstFunction structureFunctionWithAliases(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                                const std::vector<std::string>& upvalueAliases,
                                                const std::unordered_map<int, std::vector<std::string>>& aliasesByFunction,
                                                const std::vector<std::string>* functionDisplayNames) {
    return structureFunctionWithPolicy(chunk, sourceFunction, opmap, upvalueAliases, &aliasesByFunction,
                                       functionDisplayNames);
}
} // namespace

AstFunction structureFunction(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                              const std::vector<std::string>& upvalueAliases) {
    return structureFunctionWithPolicy(chunk, sourceFunction, opmap, upvalueAliases, nullptr, nullptr);
}

AstFunction structureMainFunction(const Chunk& chunk, const OpcodeMap& opmap) {
    if (chunk.mainIndex < 0 || chunk.mainIndex >= (int)chunk.functions.size()) {
        return {};
    }

    std::unordered_map<int, std::vector<std::string>> aliasesByFunction;
    collectStructuredAliasesRecursive(chunk, chunk.functions[chunk.mainIndex], opmap, {}, aliasesByFunction);
    return structureFunctionWithAliases(chunk, chunk.functions[chunk.mainIndex], opmap, {}, aliasesByFunction, nullptr);
}

std::string formatStructuredSource(const Chunk& chunk, const OpcodeMap& opmap) {
    g_structuredFunctionsProcessed.store(0, std::memory_order_relaxed);
    g_structuredFunctionsFallback.store(0, std::memory_order_relaxed);

    std::ostringstream out;
    out << "-- ============================================\n";
    out << "-- Luau Decompiled Output\n";
    out << "-- Bytecode v" << (int)chunk.version << " | Types v" << (int)chunk.typesVersion << "\n";
    out << "-- " << chunk.strings.size() << " strings, " << chunk.functions.size() << " functions\n";
    int typedFunctions = 0;
    int typeBlobBytes = 0;
    for (const auto& function : chunk.functions) {
        if (function.hasTypeInfo) {
            typedFunctions++;
            typeBlobBytes += function.typeInfoSize;
        }
    }
    out << "-- Type info: " << typedFunctions << " typed functions, " << typeBlobBytes << " bytes\n";
    out << "-- Main entry: proto#" << chunk.mainIndex << "\n";
    out << "-- Opcodes mapped: " << opmap.totalMapped << "/" << OP_COUNT << "\n";
    out << "-- Structurer fallback policy: per-function confidence gate\n";
    out << "-- ============================================\n\n";
    out << "-- Backend: structured-ast\n\n";

    g_inlineClosureBodies.store(false, std::memory_order_relaxed);

    std::unordered_map<int, std::vector<std::string>> aliasesByFunction;
    if (chunk.mainIndex >= 0 && chunk.mainIndex < (int)chunk.functions.size()) {
        collectStructuredAliasesRecursive(chunk, chunk.functions[chunk.mainIndex], opmap, {}, aliasesByFunction);
    }
    std::vector<std::string> displayNames = buildFunctionDisplayNames(chunk);

    auto functionChunks = formatFunctionsParallel(chunk.functions, [&](const Function& function) {
        if (function.id == chunk.mainIndex) {
            return std::string{};
        }

        auto aliasIt = aliasesByFunction.find(function.id);
        AstFunction ast = structureFunctionWithAliases(
            chunk,
            function,
            opmap,
            aliasIt != aliasesByFunction.end() ? aliasIt->second : std::vector<std::string>{},
            aliasesByFunction,
            &displayNames
        );
        ast.name = displayNameForFunction(displayNames, function);

        std::ostringstream chunkOut;
        chunkOut << formatAstFunction(ast) << "\n";
        return chunkOut.str();
    });

    bool emittedFunction = false;
    for (const auto& chunkText : functionChunks) {
        if (!chunkText.empty()) {
            out << chunkText;
            emittedFunction = true;
        }
    }
    if (emittedFunction) {
        out << "-- Main entry body: "
            << displayNameForFunction(displayNames, chunk.functions[chunk.mainIndex]) << "\n";
    }

    std::string body;
    if (chunk.mainIndex >= 0 && chunk.mainIndex < (int)chunk.functions.size()) {
        AstFunction mainAst = structureFunctionWithAliases(chunk, chunk.functions[chunk.mainIndex], opmap, {},
                                                           aliasesByFunction, &displayNames);
        mainAst.name = displayNameForFunction(displayNames, chunk.functions[chunk.mainIndex]);
        body = formatAstChunk(mainAst);
        out << body;
        if (!body.empty() && body.back() != '\n') {
            out << "\n";
        }
    } else {
        out << "-- Missing main entry\n";
    }
    out << "\n-- Structured functions processed: "
        << g_structuredFunctionsProcessed.load(std::memory_order_relaxed) << "\n";
    out << "-- Structured fallbacks used: "
        << g_structuredFunctionsFallback.load(std::memory_order_relaxed) << "\n";

    g_inlineClosureBodies.store(true, std::memory_order_relaxed);
    return out.str();
}

std::string formatStructuredAst(const Chunk& chunk, const OpcodeMap& opmap) {
    g_structuredFunctionsProcessed.store(0, std::memory_order_relaxed);
    g_structuredFunctionsFallback.store(0, std::memory_order_relaxed);

    std::ostringstream out;
    out << "-- Structured AST Dump\n";
    out << "-- Functions: " << chunk.functions.size() << "\n\n";

    std::unordered_map<int, std::vector<std::string>> aliasesByFunction;
    if (chunk.mainIndex >= 0 && chunk.mainIndex < (int)chunk.functions.size()) {
        collectStructuredAliasesRecursive(chunk, chunk.functions[chunk.mainIndex], opmap, {}, aliasesByFunction);
    }
    std::vector<std::string> displayNames = buildFunctionDisplayNames(chunk);

    auto chunks = formatFunctionsParallel(chunk.functions, [&](const Function& function) {
        auto aliasIt = aliasesByFunction.find(function.id);
        AstFunction ast = structureFunctionWithAliases(
            chunk,
            function,
            opmap,
            aliasIt != aliasesByFunction.end() ? aliasIt->second : std::vector<std::string>{},
            aliasesByFunction,
            &displayNames
        );
        ast.name = displayNameForFunction(displayNames, function);
        return formatAstFunction(ast) + "\n";
    });

    for (const auto& chunkText : chunks) {
        out << chunkText;
    }

    out << "-- Structured functions processed: "
        << g_structuredFunctionsProcessed.load(std::memory_order_relaxed) << "\n";
    out << "-- Structured fallbacks used: "
        << g_structuredFunctionsFallback.load(std::memory_order_relaxed) << "\n";

    return out.str();
}
