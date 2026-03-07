#include "analysis.hpp"
#include "identifier_utils.hpp"
#include <algorithm>
#include <cctype>
#include <cmath>
#include <sstream>
#include <unordered_map>

namespace {
static std::string toIdentifier(std::string value) {
    std::string out;
    bool upperNext = false;
    for (char ch : value) {
        if (std::isalnum((unsigned char)ch)) {
            if (out.empty()) {
                out.push_back((char)std::tolower((unsigned char)ch));
            } else if (upperNext) {
                out.push_back((char)std::toupper((unsigned char)ch));
                upperNext = false;
            } else {
                out.push_back(ch);
            }
        } else {
            upperNext = true;
        }
    }
    return sanitizeLuaIdentifier(out, "v");
}

static std::optional<double> parseNumericLiteral(const std::string& value) {
    try {
        size_t parsed = 0;
        double result = std::stod(value, &parsed);
        if (parsed == value.size()) {
            return result;
        }
    } catch (...) {
    }
    return std::nullopt;
}

static std::optional<std::string> asQuotedString(const std::string& value) {
    if (value.size() >= 2 && value.front() == '"' && value.back() == '"') {
        return value.substr(1, value.size() - 2);
    }
    return std::nullopt;
}

static std::string formatNumber(double value) {
    if (std::fabs(value - std::round(value)) < 1e-9) {
        return std::to_string((long long)std::llround(value));
    }
    std::ostringstream out;
    out << value;
    return out.str();
}

static bool isVersionedTempName(const std::string& name, char prefix) {
    if (name.size() < 4 || name[0] != prefix) {
        return false;
    }
    size_t i = 1;
    while (i < name.size() && std::isdigit((unsigned char)name[i])) {
        ++i;
    }
    if (i <= 1 || i >= name.size() || name[i] != '_') {
        return false;
    }
    ++i;
    if (i >= name.size()) {
        return false;
    }
    for (; i < name.size(); ++i) {
        if (!std::isdigit((unsigned char)name[i])) {
            return false;
        }
    }
    return true;
}

static std::string canonicalizeTempName(std::string name) {
    if (isVersionedTempName(name, 'v') || isVersionedTempName(name, 'p')) {
        name.erase(name.rfind('_'));
    }
    return name;
}

static std::string valueText(const SSAFunction& function, int valueId) {
    const auto& value = function.values[valueId];
    if (value.constantValue.has_value()) {
        return *value.constantValue;
    }
    return canonicalizeTempName(value.name);
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

static int logicalSlotForSSA(const SSAFunction& function, int slot) {
    if (auto it = function.cellSlotToEscapedSlot.find(slot); it != function.cellSlotToEscapedSlot.end()) {
        return it->second;
    }
    return slot;
}

static bool isEscapedMutableValue(const SSAFunction& function, int valueId) {
    if (valueId < 0 || valueId >= (int)function.values.size()) {
        return false;
    }
    int slot = logicalSlotForSSA(function, function.values[valueId].slot);
    return slot >= 0 && function.escapedMutableSlots.count(slot) != 0;
}

static int resolveAliasValue(const std::vector<int>& replacements, int valueId) {
    if (valueId < 0 || valueId >= (int)replacements.size()) {
        return valueId;
    }

    int current = valueId;
    std::unordered_set<int> visited;
    while (current >= 0 && current < (int)replacements.size() && replacements[current] >= 0) {
        if (!visited.insert(current).second) {
            break;
        }
        current = replacements[current];
    }
    return current;
}

static void recomputeUseCounts(SSAFunction& function) {
    for (auto& value : function.values) {
        value.useCount = 0;
    }

    for (const auto& block : function.blocks) {
        for (const auto& phi : block.phis) {
            if (phi.dead) {
                continue;
            }
            for (const auto& [pred, valueId] : phi.inputs) {
                (void)pred;
                if (valueId >= 0 && valueId < (int)function.values.size()) {
                    function.values[valueId].useCount++;
                }
            }
        }
    }

    for (const auto& instruction : function.instructions) {
        if (instruction.dead) {
            continue;
        }
        for (int valueId : instruction.uses) {
            if (valueId >= 0 && valueId < (int)function.values.size()) {
                function.values[valueId].useCount++;
            }
        }
    }
}

static bool simplifyValueAliases(SSAFunction& function) {
    if (function.values.empty()) {
        return false;
    }

    std::vector<int> replacements(function.values.size(), -1);
    bool changed = false;

    for (auto& block : function.blocks) {
        for (auto& phi : block.phis) {
            if (phi.dead || phi.resultValueId < 0) {
                continue;
            }
            if (isEscapedMutableValue(function, phi.resultValueId)) {
                continue;
            }

            int commonValueId = -1;
            bool hasComparableInput = false;
            bool allEqual = true;
            for (const auto& [pred, inputValueId] : phi.inputs) {
                (void)pred;
                int resolvedInput = resolveAliasValue(replacements, inputValueId);
                if (resolvedInput == phi.resultValueId) {
                    continue;
                }
                if (!hasComparableInput) {
                    hasComparableInput = true;
                    commonValueId = resolvedInput;
                } else if (commonValueId != resolvedInput) {
                    allEqual = false;
                    break;
                }
            }

            if (allEqual && hasComparableInput && commonValueId >= 0 && commonValueId != phi.resultValueId) {
                replacements[phi.resultValueId] = commonValueId;
                phi.dead = true;
                changed = true;
            }
        }
    }

    for (const auto& instruction : function.instructions) {
        if (instruction.dead) {
            continue;
        }
        if (instruction.inst.stdOp != OP_MOVE || instruction.defs.size() != 1 || instruction.uses.size() != 1) {
            continue;
        }

        int defValueId = instruction.defs.front();
        int sourceValueId = resolveAliasValue(replacements, instruction.uses.front());
        if (defValueId < 0 || defValueId >= (int)function.values.size()) {
            continue;
        }
        if (sourceValueId < 0 || sourceValueId >= (int)function.values.size()) {
            continue;
        }
        if (defValueId == sourceValueId || isEscapedMutableValue(function, defValueId)) {
            continue;
        }

        replacements[defValueId] = sourceValueId;
        changed = true;
    }

    if (!changed) {
        return false;
    }

    for (int valueId = 0; valueId < (int)replacements.size(); ++valueId) {
        if (replacements[valueId] >= 0) {
            replacements[valueId] = resolveAliasValue(replacements, replacements[valueId]);
        }
    }

    for (auto& block : function.blocks) {
        for (auto& phi : block.phis) {
            if (phi.dead) {
                continue;
            }
            for (auto& [pred, inputValueId] : phi.inputs) {
                (void)pred;
                int resolved = resolveAliasValue(replacements, inputValueId);
                if (resolved >= 0) {
                    inputValueId = resolved;
                }
            }
        }
    }

    for (auto& instruction : function.instructions) {
        for (int& useValueId : instruction.uses) {
            int resolved = resolveAliasValue(replacements, useValueId);
            if (resolved >= 0) {
                useValueId = resolved;
            }
        }
    }

    for (int valueId = 0; valueId < (int)replacements.size(); ++valueId) {
        int replacementValueId = replacements[valueId];
        if (replacementValueId < 0 || replacementValueId >= (int)function.values.size()) {
            continue;
        }
        auto& value = function.values[valueId];
        const auto& replacement = function.values[replacementValueId];
        if (!value.constantValue.has_value() && replacement.constantValue.has_value()) {
            value.constantValue = replacement.constantValue;
        }
    }

    recomputeUseCounts(function);
    return true;
}

static void applyUniqueName(std::unordered_map<std::string, int>& seen, SSAVariable& value, const std::string& base) {
    std::string sanitized = toIdentifier(base);
    int count = seen[sanitized]++;
    value.name = count == 0 ? sanitized : sanitized + "_" + std::to_string(count);
}

static std::string stripQuotedString(const std::string& value) {
    if (value.size() >= 2 && value.front() == '"' && value.back() == '"') {
        return value.substr(1, value.size() - 2);
    }
    return value;
}

static std::string upperFirst(std::string value) {
    if (!value.empty()) {
        value[0] = (char)std::toupper((unsigned char)value[0]);
    }
    return value;
}

static std::string canonicalServiceVariableName(const std::string& serviceName) {
    static const std::unordered_map<std::string, std::string> kServiceNames = {
        {"Players", "players"},
        {"RunService", "runService"},
        {"ReplicatedStorage", "replicatedStorage"},
        {"ReplicatedFirst", "replicatedFirst"},
        {"TweenService", "tweenService"},
        {"HttpService", "httpService"},
        {"UserInputService", "userInputService"},
        {"Lighting", "lighting"},
        {"Workspace", "workspace"},
        {"CollectionService", "collectionService"},
        {"MarketplaceService", "marketplaceService"},
        {"TeleportService", "teleportService"},
        {"StarterGui", "starterGui"},
        {"GuiService", "guiService"},
        {"ContextActionService", "contextActionService"},
        {"GroupService", "groupService"},
        {"PathfindingService", "pathfindingService"},
    };
    auto it = kServiceNames.find(serviceName);
    if (it != kServiceNames.end()) {
        return it->second;
    }
    return toIdentifier(serviceName);
}

static std::string inferTableBaseName(const SSAFunction& function, int tableValueId) {
    std::unordered_map<std::string, int> keys;
    bool selfIndex = false;
    int tableSlot = (tableValueId >= 0 && tableValueId < (int)function.values.size()) ? function.values[tableValueId].slot : -1;

    for (const auto& instruction : function.instructions) {
        if (instruction.inst.stdOp != OP_SETTABLEKS || !instruction.inst.keyName.has_value()) {
            continue;
        }

        bool targetsTable = false;
        if (instruction.inst.b == tableSlot) {
            targetsTable = true;
        } else if (instruction.uses.size() >= 2 && instruction.uses[1] == tableValueId) {
            targetsTable = true;
        }

        if (!targetsTable) {
            continue;
        }

        const std::string& key = *instruction.inst.keyName;
        keys[key]++;
        if (key == "__index" && instruction.inst.a == tableSlot) {
            selfIndex = true;
        }
    }

    auto hasKey = [&](const char* key) {
        return keys.find(key) != keys.end();
    };

    if (selfIndex && (hasKey("New") || hasKey("new"))) {
        return "module";
    }
    if (hasKey("Crews") && hasKey("Stomps") && hasKey("Airshots")) {
        return "boards";
    }
    if (hasKey("Name") && hasKey("Price") && hasKey("Stock")) {
        return "vehicle";
    }
    if (hasKey("Rank") && hasKey("Username") && hasKey("Value")) {
        return "entry";
    }
    if (hasKey("Examples") && hasKey("Example")) {
        return "templates";
    }
    return "";
}

static std::string inferAssignedFieldName(const SSAFunction& function, int valueId) {
    int valueSlot = (valueId >= 0 && valueId < (int)function.values.size()) ? function.values[valueId].slot : -1;
    for (const auto& instruction : function.instructions) {
        if (instruction.inst.stdOp == OP_SETTABLEKS && !instruction.dead && instruction.inst.keyName.has_value()) {
            bool matchesSource = instruction.inst.a == valueSlot ||
                (!instruction.uses.empty() && instruction.uses[0] == valueId);
            if (!matchesSource) {
                continue;
            }
            return *instruction.inst.keyName;
        }
    }
    return "";
}

static std::string inferPhiBaseName(const SSAFunction& function, int valueId);

static std::string findDebugLocalName(const Function& sourceFunction, int slot, int pc) {
    for (const auto& local : sourceFunction.locals) {
        if (local.slot == slot && local.startPc <= pc && pc < local.endPc &&
            !local.name.empty() && local.name[0] != '(') {
            return local.name;
        }
    }
    return "";
}

static bool valueHasFieldUse(const SSAFunction& function, int valueId, const std::string& key) {
    for (const auto& instruction : function.instructions) {
        if (instruction.inst.stdOp == OP_GETTABLEKS && instruction.inst.keyName.has_value() &&
            *instruction.inst.keyName == key && !instruction.uses.empty() && instruction.uses[0] == valueId) {
            return true;
        }
    }
    return false;
}

static std::string inferPcallResultBase(const SSAFunction& function, int valueId) {
    if (valueHasFieldUse(function, valueId, "EmblemUrl") || valueHasFieldUse(function, valueId, "Name")) {
        return "groupInfo";
    }
    if (valueHasFieldUse(function, valueId, "key") || valueHasFieldUse(function, valueId, "value")) {
        return "entry";
    }
    return "result";
}

static std::string inferTostringBase(const SSAFunction& function, int operandValueId) {
    const SSAInstruction* operandDef = definingInstruction(function, operandValueId);
    if (operandDef && operandDef->inst.stdOp == OP_MOVE && !operandDef->uses.empty()) {
        return inferTostringBase(function, operandDef->uses.front());
    }
    if (operandDef && operandDef->inst.stdOp == OP_GETTABLEKS && operandDef->inst.keyName.has_value()) {
        return toIdentifier(*operandDef->inst.keyName) + "Text";
    }

    const std::string operandName = valueText(function, operandValueId);
    if (operandName == "rank") {
        return "rankText";
    }
    if (operandValueId >= 0 && operandValueId < (int)function.values.size() && function.values[operandValueId].isPhi) {
        std::string phiBase = inferPhiBaseName(function, operandValueId);
        if (!phiBase.empty()) {
            return phiBase + "Text";
        }
    }
    if (operandName.size() > 1 && operandName[0] == 'v') {
        bool registerLike = true;
        for (size_t i = 1; i < operandName.size(); ++i) {
            if (!std::isdigit((unsigned char)operandName[i]) && operandName[i] != '_') {
                registerLike = false;
                break;
            }
        }
        if (registerLike) {
            return "text";
        }
    }
    if (operandName.size() > 1 && operandName[0] == 'p' &&
        std::all_of(operandName.begin() + 1, operandName.end(), [](unsigned char ch) {
            return std::isdigit(ch) != 0;
        })) {
        return "text";
    }
    if (!operandName.empty() && operandName != "_") {
        return operandName + "Text";
    }
    return "text";
}

static std::string inferPhiBaseName(const SSAFunction& function, int valueId) {
    bool usedAsEntry = false;
    bool usedAsRank = false;
    bool usedAsChild = false;

    for (const auto& instruction : function.instructions) {
        bool usesValue = std::find(instruction.uses.begin(), instruction.uses.end(), valueId) != instruction.uses.end();
        if (!usesValue) {
            continue;
        }

        if (instruction.inst.stdOp == OP_GETTABLEKS && instruction.inst.keyName.has_value()) {
            const std::string& key = *instruction.inst.keyName;
            if (key == "key" || key == "value") {
                usedAsEntry = true;
            }
        }

        if (instruction.inst.stdOp == OP_SETTABLEKS && instruction.inst.keyName.has_value()) {
            const std::string& key = *instruction.inst.keyName;
            if (key == "LayoutOrder") {
                usedAsRank = true;
            }
        }

        if ((instruction.inst.stdOp == OP_CALL || instruction.inst.stdOp == OP_NATIVECALL) && !instruction.uses.empty()) {
            const SSAInstruction* calleeDef = definingInstruction(function, instruction.uses.front());
            if (calleeDef && calleeDef->inst.stdOp == OP_NAMECALL && calleeDef->inst.keyName.has_value() &&
                !calleeDef->uses.empty() && calleeDef->uses.front() == valueId) {
                const std::string& methodName = *calleeDef->inst.keyName;
                if (methodName == "Destroy" || methodName == "IsA") {
                    usedAsChild = true;
                }
            }

            const SSAInstruction* globalDef = definingInstruction(function, instruction.uses.front());
            if (globalDef && globalDef->inst.stdOp == OP_GETIMPORT && globalDef->inst.importName.has_value() &&
                *globalDef->inst.importName == "tostring" && instruction.uses.size() >= 2 && instruction.uses[1] == valueId) {
                usedAsRank = true;
            }
        }
    }

    if (usedAsEntry) {
        return "entry";
    }
    if (usedAsChild) {
        return "child";
    }
    if (usedAsRank) {
        return "rank";
    }
    return "";
}

static bool isArithmeticOp(int op) {
    switch (op) {
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
        case OP_IDIVK:
        case OP_SUBRK:
        case OP_DIVRK:
            return true;
        default:
            return false;
    }
}

static bool isConditionalJumpOp(int op) {
    switch (op) {
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

static std::string inferUsageDrivenBaseName(const SSAFunction& function, int valueId) {
    std::unordered_map<std::string, int> score;
    auto bump = [&](const std::string& name, int amount) {
        score[name] += amount;
    };

    for (const auto& instruction : function.instructions) {
        bool usesValue = std::find(instruction.uses.begin(), instruction.uses.end(), valueId) != instruction.uses.end();
        if (!usesValue) {
            continue;
        }

        switch (instruction.inst.stdOp) {
            case OP_GETTABLE:
                if (instruction.uses.size() >= 2 && instruction.uses[1] == valueId) {
                    bump("key", 4);
                } else {
                    bump("tableValue", 1);
                }
                break;
            case OP_SETTABLE:
                if (instruction.uses.size() >= 3) {
                    if (instruction.uses[2] == valueId) {
                        bump("key", 4);
                    }
                    if (instruction.uses[0] == valueId) {
                        bump("value", 2);
                    }
                }
                break;
            case OP_SETTABLEKS:
                if (!instruction.inst.keyName.has_value()) {
                    break;
                }
                if (*instruction.inst.keyName == "key") {
                    bump("key", 3);
                } else if (*instruction.inst.keyName == "value") {
                    bump("value", 3);
                } else if (*instruction.inst.keyName == "Name") {
                    bump("name", 3);
                } else if (*instruction.inst.keyName == "Id") {
                    bump("id", 3);
                }
                break;
            case OP_FORGLOOP:
            case OP_FORGPREP:
            case OP_FORGPREP_NEXT:
            case OP_FORGPREP_INEXT:
                bump("item", 2);
                bump("entry", 1);
                break;
            case OP_FORNLOOP:
            case OP_FORNPREP:
                bump("i", 4);
                bump("index", 2);
                break;
            default:
                if (isArithmeticOp(instruction.inst.stdOp)) {
                    bump("count", 2);
                    bump("value", 1);
                }
                if (isConditionalJumpOp(instruction.inst.stdOp)) {
                    bump("condition", 2);
                }
                break;
        }
    }

    std::string best;
    int bestScore = 0;
    for (const auto& [name, value] : score) {
        if (value > bestScore) {
            bestScore = value;
            best = name;
        }
    }
    return bestScore >= 3 ? best : "";
}
} 

void inferNames(SSAFunction& function, const Function& sourceFunction, const std::vector<std::string>& upvalueAliases) {
    std::unordered_map<std::string, int> usedNames;

    for (auto& value : function.values) {
        int logicalSlot = logicalSlotForSSA(function, value.slot);

        if (value.isParameter) {
            std::string localName;
            for (const auto& local : sourceFunction.locals) {
                if (local.slot == logicalSlot && local.startPc == 0 && !local.name.empty() && local.name[0] != '(') {
                    localName = local.name;
                    break;
                }
            }
            if (!localName.empty()) {
                applyUniqueName(usedNames, value, localName);
                continue;
            }
            applyUniqueName(usedNames, value, "p" + std::to_string(logicalSlot));
            continue;
        }
        if (value.isUpvalue) {
            std::string base;
            int upvalueIndex = value.upvalueIndex;
            if (upvalueIndex >= 0 && upvalueIndex < (int)upvalueAliases.size() && !upvalueAliases[upvalueIndex].empty()) {
                base = upvalueAliases[upvalueIndex];
            } else if (upvalueIndex >= 0 && upvalueIndex < (int)sourceFunction.upvalueNames.size() && !sourceFunction.upvalueNames[upvalueIndex].empty()) {
                base = sourceFunction.upvalueNames[upvalueIndex];
            } else {
                base = "upval" + std::to_string(upvalueIndex);
            }
            if (base.rfind("upval", 0) == 0) {
                std::string usageBase = inferUsageDrivenBaseName(function, value.id);
                if (!usageBase.empty()) {
                    base = usageBase;
                }
            }
            applyUniqueName(usedNames, value, base);
            continue;
        }

        std::string base = "v" + std::to_string(logicalSlot);
        if (value.isPhi) {
            std::string phiBase = inferPhiBaseName(function, value.id);
            if (!phiBase.empty()) {
                base = phiBase;
            }
        }
        const SSAInstruction* def = definingInstruction(function, value.id);
        if (def) {
            std::string debugLocalName = findDebugLocalName(sourceFunction, logicalSlot, def->inst.pc);
            if (!debugLocalName.empty()) {
                base = debugLocalName;
            }
        }
        if (def) {
            if (def->inst.stdOp == OP_GETUPVAL) {
                int upvalueIndex = def->inst.b;
                if (upvalueIndex >= 0 && upvalueIndex < (int)upvalueAliases.size() && !upvalueAliases[upvalueIndex].empty()) {
                    base = upvalueAliases[upvalueIndex];
                } else if (upvalueIndex >= 0 && upvalueIndex < (int)sourceFunction.upvalueNames.size() && !sourceFunction.upvalueNames[upvalueIndex].empty()) {
                    base = sourceFunction.upvalueNames[upvalueIndex];
                } else {
                    base = "upval" + std::to_string(upvalueIndex);
                }
            } else if (def->inst.stdOp == OP_NAMECALL && def->inst.keyName.has_value()) {
                std::string methodBase = toIdentifier(*def->inst.keyName);
                if (!def->defs.empty() && value.id == def->defs.front()) {
                    base = methodBase + "Method";
                } else {
                    base = methodBase + "Self";
                }
            } else if (def->inst.importName.has_value()) {
                const std::string& importName = *def->inst.importName;
                size_t dot = importName.find_last_of('.');
                base = dot == std::string::npos ? importName : importName.substr(dot + 1);
            } else if (def->inst.keyName.has_value()) {
                base = *def->inst.keyName;
            } else if (def->inst.stdOp == OP_NEWTABLE || def->inst.stdOp == OP_DUPTABLE) {
                base = inferTableBaseName(function, value.id);
                if (base.empty()) {
                    base = "table";
                }
            } else if (def->inst.stdOp == OP_NEWCLOSURE || def->inst.stdOp == OP_DUPCLOSURE) {
                base = inferAssignedFieldName(function, value.id);
                if (base.empty()) {
                    base = "closure";
                }
            } else if (def->inst.stdOp == OP_CALL || def->inst.stdOp == OP_NATIVECALL) {
                base = "result";
                if (!def->uses.empty()) {
                    const SSAInstruction* calleeDef = definingInstruction(function, def->uses.front());
                    if (calleeDef && calleeDef->inst.stdOp == OP_NAMECALL && calleeDef->inst.keyName.has_value()) {
                        const std::string& methodName = *calleeDef->inst.keyName;
                        if (methodName == "GetService" && def->uses.size() >= 3) {
                            base = canonicalServiceVariableName(stripQuotedString(valueText(function, def->uses[2])));
                        } else if (methodName == "WaitForChild" && def->uses.size() >= 3) {
                            std::string childName = stripQuotedString(valueText(function, def->uses[2]));
                            base = childName.empty() ? "child" : toIdentifier(childName);
                        } else if (methodName == "FindFirstChild") {
                            if (def->uses.size() >= 3) {
                                std::string childName = stripQuotedString(valueText(function, def->uses[2]));
                                base = childName.empty() ? "existing" : toIdentifier(childName);
                            } else {
                                base = "existing";
                            }
                        } else if (methodName == "Clone") {
                            base = "clone";
                        } else if (methodName == "GetChildren") {
                            if (!def->defs.empty() && value.id == def->defs.front()) {
                                base = "children";
                            } else if (def->defs.size() > 1 && value.id == def->defs[1]) {
                                base = "state";
                            } else {
                                base = "index";
                            }
                        } else if (methodName == "IsA") {
                            if (def->uses.size() >= 3) {
                                base = "is" + upperFirst(stripQuotedString(valueText(function, def->uses[2])));
                            } else {
                                base = "matchesType";
                            }
                        } else if (methodName == "Format" || methodName == "format") {
                            base = "formatted";
                        } else {
                            base = methodName;
                        }
                    } else if (calleeDef && calleeDef->inst.stdOp == OP_GETIMPORT && calleeDef->inst.importName.has_value()) {
                        const std::string& importName = *calleeDef->inst.importName;
                        if (importName == "pcall") {
                            if (!def->defs.empty() && value.id == def->defs.front()) {
                                base = "ok";
                            } else {
                                base = inferPcallResultBase(function, value.id);
                            }
                        } else if (importName == "tostring" && def->uses.size() >= 2) {
                            base = inferTostringBase(function, def->uses[1]);
                        }
                    }
                }
            } else if (def->inst.stdOp == OP_CONCAT) {
                base = "text";
            } else if (value.isPhi) {
                base = "merge";
            }
        }

        if (base == "merge" || (base.size() > 1 && base[0] == 'v' &&
            std::all_of(base.begin() + 1, base.end(), [](unsigned char ch) { return std::isdigit(ch) != 0; }))) {
            std::string usageBase = inferUsageDrivenBaseName(function, value.id);
            if (!usageBase.empty()) {
                base = usageBase;
            }
        }

        applyUniqueName(usedNames, value, base);
    }
}

void detectSemanticPatterns(SSAFunction& function) {
    for (auto& instruction : function.instructions) {
        if (instruction.inst.stdOp == OP_CALL && !instruction.uses.empty()) {
            const SSAInstruction* calleeDef = definingInstruction(function, instruction.uses.front());
            if (calleeDef && calleeDef->inst.stdOp == OP_NAMECALL && calleeDef->inst.keyName.has_value() &&
                !calleeDef->uses.empty()) {
                std::string objectExpr = valueText(function, calleeDef->uses.front());
                std::string text = objectExpr + ":" + *calleeDef->inst.keyName + "(";
                for (size_t i = 2; i < instruction.uses.size(); ++i) {
                    if (i > 2) {
                        text += ", ";
                    }
                    text += valueText(function, instruction.uses[i]);
                }
                text += ")";
                instruction.semanticHint = "method_call";
                instruction.renderedText = text;
                continue;
            }
        }

        if ((instruction.inst.stdOp == OP_FORGPREP || instruction.inst.stdOp == OP_FORGPREP_NEXT || instruction.inst.stdOp == OP_FORGPREP_INEXT) &&
            !instruction.uses.empty()) {
            const SSAInstruction* iteratorDef = definingInstruction(function, instruction.uses.front());
            if (iteratorDef &&
                (iteratorDef->inst.stdOp == OP_CALL || iteratorDef->inst.stdOp == OP_NATIVECALL) &&
                iteratorDef->defs.size() == instruction.uses.size() &&
                iteratorDef->renderedText.has_value()) {
                bool directIterator = !iteratorDef->defs.empty();
                for (size_t i = 0; i < iteratorDef->defs.size(); ++i) {
                    if (iteratorDef->defs[i] != instruction.uses[i]) {
                        directIterator = false;
                        break;
                    }
                }

                if (directIterator) {
                    std::string iteratorExpr = *iteratorDef->renderedText;
                    const SSAInstruction* calleeDef = !iteratorDef->uses.empty()
                        ? definingInstruction(function, iteratorDef->uses.front())
                        : nullptr;
                    if (calleeDef && calleeDef->inst.stdOp == OP_NAMECALL && calleeDef->inst.keyName.has_value()) {
                        const std::string& methodName = *calleeDef->inst.keyName;
                        if (methodName == "GetChildren" || methodName == "GetDescendants") {
                            instruction.semanticHint = "array_loop";
                            instruction.renderedText = iteratorExpr;
                            continue;
                        }
                    }

                    instruction.semanticHint = "direct_iterator";
                    instruction.renderedText = iteratorExpr;
                    continue;
                }
            }
        }

        if ((instruction.inst.stdOp == OP_FORGPREP || instruction.inst.stdOp == OP_FORGPREP_NEXT || instruction.inst.stdOp == OP_FORGPREP_INEXT) &&
            instruction.uses.size() >= 2) {
            std::string iterator = valueText(function, instruction.uses[0]);
            std::string state = valueText(function, instruction.uses[1]);
            if (iterator == "next") {
                instruction.semanticHint = "pairs_loop";
                instruction.renderedText = "pairs(" + state + ")";
            } else if (iterator == "inext" || iterator == "ipairs") {
                instruction.semanticHint = "ipairs_loop";
                instruction.renderedText = "ipairs(" + state + ")";
            }
        }
    }
}

void propagateConstants(SSAFunction& function, const Function& sourceFunction) {
    (void)sourceFunction;

    for (auto& instruction : function.instructions) {
        if (instruction.defs.empty()) {
            continue;
        }

        auto setAllDefs = [&](const std::string& value) {
            for (int valueId : instruction.defs) {
                function.values[valueId].constantValue = value;
            }
        };

        switch (instruction.inst.stdOp) {
            case OP_LOADNIL:
                setAllDefs("nil");
                break;
            case OP_LOADB:
                setAllDefs(instruction.inst.b ? "true" : "false");
                break;
            case OP_LOADN:
                setAllDefs(std::to_string(instruction.inst.d));
                break;
            case OP_LOADK:
            case OP_LOADKX:
                if (instruction.inst.constantValue.has_value()) {
                    setAllDefs(*instruction.inst.constantValue);
                }
                break;
            case OP_GETIMPORT:
                if (instruction.inst.importName.has_value()) {
                    setAllDefs(*instruction.inst.importName);
                }
                break;
            case OP_GETUPVAL:
                if (!instruction.uses.empty()) {
                    const auto& src = function.values[instruction.uses[0]];
                    if (!isEscapedMutableValue(function, instruction.uses[0]) && src.constantValue.has_value()) {
                        setAllDefs(*src.constantValue);
                    }
                }
                break;
            case OP_SETUPVAL:
                if (!instruction.uses.empty() && !isEscapedMutableValue(function, instruction.defs.front())) {
                    const auto& src = function.values[instruction.uses[0]];
                    if (!isEscapedMutableValue(function, instruction.uses[0]) && src.constantValue.has_value()) {
                        setAllDefs(*src.constantValue);
                    }
                }
                break;
            case OP_MOVE:
                if (!instruction.uses.empty()) {
                    const auto& src = function.values[instruction.uses[0]];
                    if (!isEscapedMutableValue(function, instruction.uses[0]) && src.constantValue.has_value()) {
                        setAllDefs(*src.constantValue);
                    }
                }
                break;
            case OP_CONCAT:
                if (!instruction.uses.empty()) {
                    std::string result;
                    bool allStrings = true;
                    for (int valueId : instruction.uses) {
                        if (isEscapedMutableValue(function, valueId)) {
                            allStrings = false;
                            break;
                        }
                        const auto& value = function.values[valueId];
                        if (!value.constantValue.has_value()) {
                            allStrings = false;
                            break;
                        }
                        auto inner = asQuotedString(*value.constantValue);
                        if (!inner.has_value()) {
                            allStrings = false;
                            break;
                        }
                        result += *inner;
                    }
                    if (allStrings) {
                        setAllDefs("\"" + result + "\"");
                    }
                }
                break;
            case OP_ADD:
            case OP_SUB:
            case OP_MUL:
            case OP_DIV:
            case OP_MOD:
            case OP_POW:
                if (instruction.uses.size() >= 2) {
                    if (isEscapedMutableValue(function, instruction.uses[0]) ||
                        isEscapedMutableValue(function, instruction.uses[1])) {
                        break;
                    }
                    auto lhs = parseNumericLiteral(valueText(function, instruction.uses[0]));
                    auto rhs = parseNumericLiteral(valueText(function, instruction.uses[1]));
                    if (lhs.has_value() && rhs.has_value()) {
                        double result = 0.0;
                        switch (instruction.inst.stdOp) {
                            case OP_ADD: result = *lhs + *rhs; break;
                            case OP_SUB: result = *lhs - *rhs; break;
                            case OP_MUL: result = *lhs * *rhs; break;
                            case OP_DIV: result = *lhs / *rhs; break;
                            case OP_MOD: result = std::fmod(*lhs, *rhs); break;
                            case OP_POW: result = std::pow(*lhs, *rhs); break;
                            default: break;
                        }
                        setAllDefs(formatNumber(result));
                    }
                }
                break;
            default:
                break;
        }
    }

    for (auto& block : function.blocks) {
        for (auto& phi : block.phis) {
            std::string common;
            bool first = true;
            bool consistent = true;
            for (const auto& [pred, valueId] : phi.inputs) {
                (void)pred;
                const auto& input = function.values[valueId];
                if (!input.constantValue.has_value()) {
                    consistent = false;
                    break;
                }
                if (first) {
                    common = *input.constantValue;
                    first = false;
                } else if (common != *input.constantValue) {
                    consistent = false;
                    break;
                }
            }
            if (consistent && !first && phi.resultValueId >= 0 &&
                !isEscapedMutableValue(function, phi.resultValueId)) {
                function.values[phi.resultValueId].constantValue = common;
            }
        }
    }
}

void eliminateDeadCode(SSAFunction& function) {
    for (auto& instruction : function.instructions) {
        if (instruction.hasSideEffects || instruction.defs.empty()) {
            continue;
        }

        bool allUnused = true;
        for (int valueId : instruction.defs) {
            if (valueId >= 0 && valueId < (int)function.values.size() && function.values[valueId].useCount > 0) {
                allUnused = false;
                break;
            }
        }
        instruction.dead = allUnused;
    }

    for (auto& block : function.blocks) {
        for (auto& phi : block.phis) {
            if (phi.resultValueId >= 0 && phi.resultValueId < (int)function.values.size() && function.values[phi.resultValueId].useCount == 0) {
                phi.dead = true;
            }
        }
    }
}

SSAFunction analyzeFunction(const Chunk& chunk, const Function& function, const OpcodeMap& opmap,
                           const std::vector<std::string>& upvalueAliases) {
    SSAFunction analyzed = buildSSAFunction(chunk, function, opmap);
    propagateConstants(analyzed, function);
    for (int i = 0; i < 4; ++i) {
        if (!simplifyValueAliases(analyzed)) {
            break;
        }
        propagateConstants(analyzed, function);
    }
    inferNames(analyzed, function, upvalueAliases);
    detectSemanticPatterns(analyzed);
    eliminateDeadCode(analyzed);
    recomputeUseCounts(analyzed);
    return analyzed;
}

std::string formatAnalyzedSSA(const Chunk& chunk, const OpcodeMap& opmap) {
    std::ostringstream out;
    out << "-- Analyzed SSA Dump\n";
    out << "-- Functions: " << chunk.functions.size() << "\n\n";

    for (const auto& function : chunk.functions) {
        SSAFunction analyzed = analyzeFunction(chunk, function, opmap);
        out << "Function proto#" << function.id;
        if (!function.debugName.empty()) {
            out << " \"" << function.debugName << "\"";
        }
        if (function.lineDefined > 0) {
            out << " line " << function.lineDefined;
        }
        out << "\n";

        for (const auto& block : analyzed.blocks) {
            out << "  block b" << block.blockId << "\n";
            for (const auto& phi : block.phis) {
                if (phi.dead) {
                    continue;
                }
                const auto& result = analyzed.values[phi.resultValueId];
                out << "    phi " << result.name;
                if (result.constantValue.has_value()) {
                    out << " = " << *result.constantValue;
                }
                out << " <- ";
                bool first = true;
                for (const auto& [pred, valueId] : phi.inputs) {
                    if (!first) out << ", ";
                    first = false;
                    out << "b" << pred << ":" << analyzed.values[valueId].name;
                }
                out << "\n";
            }
            for (int instIndex : block.instructionRefs) {
                const auto& instruction = analyzed.instructions[instIndex];
                if (instruction.dead) {
                    continue;
                }
                out << "    [" << instruction.inst.pc << "] " << instruction.inst.opName;
                if (!instruction.defs.empty()) {
                    out << " defs=";
                    for (size_t i = 0; i < instruction.defs.size(); ++i) {
                        if (i) out << ", ";
                        const auto& value = analyzed.values[instruction.defs[i]];
                        out << value.name;
                        if (value.constantValue.has_value()) {
                            out << "=" << *value.constantValue;
                        }
                    }
                }
                if (!instruction.uses.empty()) {
                    out << " uses=";
                    for (size_t i = 0; i < instruction.uses.size(); ++i) {
                        if (i) out << ", ";
                        out << analyzed.values[instruction.uses[i]].name;
                    }
                }
                if (!instruction.clobberDefs.empty()) {
                    out << " clobber=";
                    for (size_t i = 0; i < instruction.clobberDefs.size(); ++i) {
                        if (i) out << ", ";
                        out << analyzed.values[instruction.clobberDefs[i]].name;
                    }
                }
                if (!instruction.semanticHint.empty()) {
                    out << " hint=" << instruction.semanticHint;
                }
                if (instruction.renderedText.has_value()) {
                    out << " render=" << *instruction.renderedText;
                }
                out << "\n";
            }
        }
        out << "\n";
    }

    return out.str();
}
