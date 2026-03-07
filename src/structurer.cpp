#include "structurer.hpp"
#include "identifier_utils.hpp"
#include <algorithm>
#include <cctype>
#include <functional>
#include <optional>
#include <sstream>
#include <unordered_map>
#include <unordered_set>

static AstFunction structureFunctionWithAliases(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                                const std::vector<std::string>& upvalueAliases,
                                                const std::unordered_map<int, std::vector<std::string>>& aliasesByFunction);

namespace {
struct TableEntry {
    std::optional<std::string> namedKey;
    std::optional<int> numericKey;
    std::optional<int> keyValueId;
    int valueId = -1;
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
    std::unordered_map<int, TableConstruction> tables;
    std::unordered_map<int, const PhiNode*> phiByResult;
    std::unordered_set<int> symbolicPhiValues;
    std::unordered_set<int> symbolicMutableValues;
    std::unordered_set<int> capturedMutableValues;
    std::unordered_set<int> closureCapturedValues;
    std::unordered_set<int> foldedInstructions;
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

static bool isIdentifierKey(const std::string& value) {
    return isLuaIdentifier(value);
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
static int aliasQuality(const std::string& alias);
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
    return useIndex < terminator.uses.size() ? buildExpression(context, terminator.uses[useIndex]) : "_";
}

static std::optional<int> choosePhiRepresentative(ExpressionContext& context, const PhiNode& phi) {
    if (context.symbolicPhiValues.count(phi.resultValueId)) {
        return std::nullopt;
    }

    if (phi.inputs.empty()) {
        return std::nullopt;
    }

    std::vector<int> loopBackPreds;
    for (const auto& edge : context.analyzed.cfg.edges) {
        if (edge.toBlock == phi.blockId && edge.kind == CFGEdgeKind::LoopBack) {
            loopBackPreds.push_back(edge.fromBlock);
        }
    }

    if (!loopBackPreds.empty()) {
        return std::nullopt;
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
                    out << "[\"" << *entry.namedKey << "\"] = ";
                }
            } else if (entry.numericKey.has_value()) {
                out << "[" << *entry.numericKey << "] = ";
            } else if (entry.keyValueId.has_value()) {
                out << "[" << buildExpression(context, *entry.keyValueId, depth + 1) << "] = ";
            }
            out << buildExpression(context, entry.valueId, depth + 1);
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
                out << buildExpression(context, instruction.uses[i], depth);
            }
            out << ")";
            return out.str();
        }
    }

    if (instruction.renderedText.has_value()) {
        return *instruction.renderedText;
    }

    std::ostringstream out;
    out << (instruction.uses.empty() ? "_" : buildExpression(context, instruction.uses[0], depth)) << "(";
    for (size_t i = 1; i < instruction.uses.size(); ++i) {
        if (i > 1) {
            out << ", ";
        }
        out << buildExpression(context, instruction.uses[i], depth);
    }
    out << ")";
    return out.str();
}

static std::vector<std::string> collectClosureCaptureAliases(ExpressionContext& context, const SSAInstruction& closureInstruction, const Function& childFunction) {
    std::vector<std::string> aliases;
    aliases.reserve(childFunction.numUpvalues);

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
                int currentValueId = currentValueForSlotAtInstruction(context.analyzed, closureInstIndex, source);
                if (currentValueId >= 0 && currentValueId < (int)context.analyzed.values.size()) {
                    alias = normalizeInheritedAlias(
                        normalizeStructuredAlias(context, source, context.analyzed.values[currentValueId].name)
                    );
                } else {
                    alias = normalizeInheritedAlias(slotAliasFor(context, source));
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

        aliases.push_back(alias);
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
        if (aliases[i].empty() || aliasQuality(candidate) > aliasQuality(aliases[i])) {
            aliases[i] = candidate;
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

    std::vector<std::string> captureAliases = resolveClosureCaptureAliases(context, instruction, **childFunction);
    AstFunction childAst = context.aliasesByFunction
        ? structureFunctionWithAliases(context.chunk, **childFunction, context.opmap, captureAliases, *context.aliasesByFunction)
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
        return structureFunctionWithAliases(context.chunk, **childFunction, context.opmap, captureAliases, *context.aliasesByFunction);
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
        "count", "index", "table", "merge", "text", "formatted"
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

static int aliasQuality(const std::string& alias) {
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
    return score;
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

        int score = aliasQuality(candidate);
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
        std::string selected = !choice.bestSpecificAlias.empty() ? choice.bestSpecificAlias : choice.bestAnyAlias;
        if (!selected.empty()) {
            context.slotAliases[slot] = selected;
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
    if (value.slot >= 0) {
        return normalizeStructuredAlias(context, value.slot, value.name);
    }
    return value.name;
}

static std::string upvalueAliasFor(ExpressionContext& context, int upvalueIndex) {
    if (upvalueIndex >= 0 && upvalueIndex < (int)context.upvalueAliases.size() &&
        !context.upvalueAliases[upvalueIndex].empty()) {
        return normalizeUpvalueAliasName(context.upvalueAliases[upvalueIndex]);
    }
    if (upvalueIndex >= 0 && upvalueIndex < (int)context.sourceFunction.upvalueNames.size() &&
        !context.sourceFunction.upvalueNames[upvalueIndex].empty()) {
        return normalizeUpvalueAliasName(context.sourceFunction.upvalueNames[upvalueIndex]);
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
    initializeSlotAliases(context);

    for (const auto& instruction : context.analyzed.instructions) {
        auto childFunction = resolveChildFunction(context, instruction);
        if (!childFunction.has_value()) {
            continue;
        }

        std::vector<std::string> captureAliases = collectClosureCaptureAliases(context, instruction, **childFunction);
        auto& childAliases = aliasesByFunction[(*childFunction)->id];
        std::vector<std::string> previousAliases = childAliases;
        mergeAliases(childAliases, captureAliases);
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
            result = value.slot >= 0
                ? normalizeStructuredAlias(context, value.slot, value.name)
                : value.name;
        } else if (isSideEffectingValue(context.analyzed, valueId) &&
                   def->inst.stdOp != OP_NEWTABLE &&
                   def->inst.stdOp != OP_DUPTABLE &&
                   def->inst.stdOp != OP_NEWCLOSURE &&
                   def->inst.stdOp != OP_DUPCLOSURE) {
            result = value.slot >= 0
                ? normalizeStructuredAlias(context, value.slot, value.name)
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
                            result = "_G[\"" + key + "\"]";
                        }
                    } else {
                        result = "_G[\"__global_" + std::to_string(def->inst.pc) + "\"]";
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
                    result = useExpr(0) + "." + def->inst.keyName.value_or("key");
                    break;
                case OP_GETTABLE:
                    result = useExpr(0) + "[" + useExpr(1) + "]";
                    break;
                case OP_GETTABLEN:
                    result = useExpr(0) + "[" + std::to_string((int)def->inst.c + 1) + "]";
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
            context.closureCapturedValues.count(valueId) != 0;
        if (!table.selfReferential && table.inlineable && !preserveDefinition) {
            if (const SSAInstruction* def = definingInstruction(context.analyzed, valueId)) {
                context.foldedInstructions.insert(def->index);
            }
        }
    }
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
        return context.closureCapturedValues.count(valueId) != 0;
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
                key != "__index" && isIdentifierKey(key)) {
                if (auto named = renderNamedClosureDefinition(context, tableExpr + "." + key, sourceValueId, 0);
                    named.has_value()) {
                    return *named;
                }
            }

            std::string valueExpr = sourceValueId >= 0 ? buildExpression(context, sourceValueId, 0) : "_";
            return tableExpr + "." + key + " = " + valueExpr;
        }
        case OP_SETTABLE: {
            std::string tableExpr = buildSlotExpression(context, instruction, instruction.inst.b);
            std::string keyExpr = buildSlotExpression(context, instruction, instruction.inst.c);
            std::string valueExpr = buildSlotExpression(context, instruction, instruction.inst.a);
            return tableExpr + "[" + keyExpr + "] = " + valueExpr;
        }
        case OP_SETTABLEN: {
            std::string tableExpr = buildSlotExpression(context, instruction, instruction.inst.b);
            std::string valueExpr = buildSlotExpression(context, instruction, instruction.inst.a);
            return tableExpr + "[" + std::to_string((int)instruction.inst.c + 1) + "] = " + valueExpr;
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
                return "_G[\"" + key + "\"] = " + useExpr(0);
            }
            return "_G[\"__global_" + std::to_string(instruction.inst.pc) + "\"] = " + useExpr(0);
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
        return context.closureCapturedValues.count(valueId) != 0;
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

                int join = (current >= 0 && current < (int)context.analyzed.cfg.immediatePostDominator.size())
                    ? context.analyzed.cfg.immediatePostDominator[current]
                    : -1;

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
                    current = join;
                    continue;
                }

                block.body.push_back(ifStmt);
                current = join;
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

AstFunction structureFunction(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                              const std::vector<std::string>& upvalueAliases) {
    SSAFunction analyzed = analyzeFunction(chunk, sourceFunction, opmap, upvalueAliases);
    ExpressionContext context{chunk, sourceFunction, opmap, analyzed, upvalueAliases};
    initializeSlotAliases(context);
    populatePhiMap(context);
    markSymbolicLoopPhiValues(context);
    markSymbolicConditionalPhiValues(context);
    markCapturedMutableSlots(context);
    markClosureCapturedValues(context);
    prepareTableConstructions(context);

    AstFunction function;
    function.name = isUsableFunctionName(sourceFunction.debugName)
        ? sourceFunction.debugName
        : ("proto_" + std::to_string(sourceFunction.id));
    for (int slot = 0; slot < sourceFunction.numParams; ++slot) {
        function.params.push_back(localNameForSlot(sourceFunction, slot));
    }
        function.body.kind = AstStatementKind::Block;
    if (!context.analyzed.blocks.empty() && !context.analyzed.cfg.blocks.empty()) {
        std::unordered_set<int> visited;
        function.body.body = buildRegionList(context, 0, -1, visited);
    }
    return function;
}

static AstFunction structureFunctionWithAliases(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                                                const std::vector<std::string>& upvalueAliases,
                                                const std::unordered_map<int, std::vector<std::string>>& aliasesByFunction) {
    SSAFunction analyzed = analyzeFunction(chunk, sourceFunction, opmap, upvalueAliases);
    ExpressionContext context{chunk, sourceFunction, opmap, analyzed, upvalueAliases};
    context.aliasesByFunction = &aliasesByFunction;
    initializeSlotAliases(context);
    populatePhiMap(context);
    markSymbolicLoopPhiValues(context);
    markSymbolicConditionalPhiValues(context);
    markCapturedMutableSlots(context);
    markClosureCapturedValues(context);
    prepareTableConstructions(context);

    AstFunction function;
    function.name = isUsableFunctionName(sourceFunction.debugName)
        ? sourceFunction.debugName
        : ("proto_" + std::to_string(sourceFunction.id));
    for (int slot = 0; slot < sourceFunction.numParams; ++slot) {
        function.params.push_back(localNameForSlot(sourceFunction, slot));
    }
    function.body.kind = AstStatementKind::Block;
    if (!context.analyzed.blocks.empty() && !context.analyzed.cfg.blocks.empty()) {
        std::unordered_set<int> visited;
        function.body.body = buildRegionList(context, 0, -1, visited);
    }
    return function;
}

AstFunction structureMainFunction(const Chunk& chunk, const OpcodeMap& opmap) {
    if (chunk.mainIndex < 0 || chunk.mainIndex >= (int)chunk.functions.size()) {
        return {};
    }

    std::unordered_map<int, std::vector<std::string>> aliasesByFunction;
    collectStructuredAliasesRecursive(chunk, chunk.functions[chunk.mainIndex], opmap, {}, aliasesByFunction);
    return structureFunctionWithAliases(chunk, chunk.functions[chunk.mainIndex], opmap, {}, aliasesByFunction);
}

std::string formatStructuredSource(const Chunk& chunk, const OpcodeMap& opmap) {
    std::ostringstream out;
    out << "-- ============================================\n";
    out << "-- Luau Decompiled Output\n";
    out << "-- Bytecode v" << (int)chunk.version << " | Types v" << (int)chunk.typesVersion << "\n";
    out << "-- " << chunk.strings.size() << " strings, " << chunk.functions.size() << " functions\n";
    out << "-- Main entry: proto#" << chunk.mainIndex << "\n";
    out << "-- Opcodes mapped: " << opmap.totalMapped << "/" << OP_COUNT << "\n";
    out << "-- ============================================\n\n";
    out << "-- Backend: structured-ast\n\n";

    std::string body = formatAstChunk(structureMainFunction(chunk, opmap));
    out << body;
    if (!body.empty() && body.back() != '\n') {
        out << "\n";
    }
    return out.str();
}

std::string formatStructuredAst(const Chunk& chunk, const OpcodeMap& opmap) {
    std::ostringstream out;
    out << "-- Structured AST Dump\n";
    out << "-- Functions: " << chunk.functions.size() << "\n\n";

    std::unordered_map<int, std::vector<std::string>> aliasesByFunction;
    if (chunk.mainIndex >= 0 && chunk.mainIndex < (int)chunk.functions.size()) {
        collectStructuredAliasesRecursive(chunk, chunk.functions[chunk.mainIndex], opmap, {}, aliasesByFunction);
    }

    for (const auto& function : chunk.functions) {
        auto aliasIt = aliasesByFunction.find(function.id);
        AstFunction ast = structureFunctionWithAliases(
            chunk,
            function,
            opmap,
            aliasIt != aliasesByFunction.end() ? aliasIt->second : std::vector<std::string>{},
            aliasesByFunction
        );
        out << formatAstFunction(ast) << "\n";
    }

    return out.str();
}
