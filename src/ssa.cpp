#include "ssa.hpp"
#include "identifier_utils.hpp"
#include <algorithm>
#include <cctype>
#include <sstream>
#include <unordered_map>
#include <unordered_set>

namespace {
struct SlotAccess {
    std::vector<int> uses;
    std::vector<int> defs;
    std::vector<int> clobberDefs;
    bool hasSideEffects = false;
};

static SlotAccess analyzeSlotAccess(const Function& function, const DecodedInstruction& inst,
                                    const std::vector<int>& callClobberSlots, int openResultBase);

static int upvalueCellSlot(const Function& function, int upvalueIndex) {
    if (upvalueIndex < 0) {
        return -1;
    }
    return function.maxStackSize + upvalueIndex;
}

static void addUnique(std::vector<int>& values, int value) {
    if (value < 0) {
        return;
    }
    if (std::find(values.begin(), values.end(), value) == values.end()) {
        values.push_back(value);
    }
}

static void addRange(std::vector<int>& values, int start, int count) {
    if (count <= 0) {
        return;
    }
    for (int i = 0; i < count; ++i) {
        addUnique(values, start + i);
    }
}

struct ClosureCapture {
    int type = 0;
    int source = -1;
};

struct ClosureInfo {
    int instIndex = -1;
    int targetSlot = -1;
    int childProto = -1;
    std::vector<ClosureCapture> captures;
};

static int resolveChildProtoIndex(const Chunk& chunk, const Function& function, const DecodedInstruction& inst) {
    if (inst.stdOp == OP_NEWCLOSURE) {
        if (inst.d >= 0 && inst.d < (int)function.childProtos.size()) {
            int proto = function.childProtos[inst.d];
            if (proto >= 0 && proto < (int)chunk.functions.size()) {
                return proto;
            }
        }
    } else if (inst.stdOp == OP_DUPCLOSURE) {
        if (inst.d >= 0 && inst.d < (int)function.constants.size() &&
            function.constants[inst.d].type == ConstantType::Closure) {
            int proto = function.constants[inst.d].closureIdx;
            if (proto >= 0 && proto < (int)chunk.functions.size()) {
                return proto;
            }
        }
    }
    return -1;
}

static std::unordered_map<int, ClosureInfo> collectClosureInfoByInstruction(const Chunk& chunk, const Function& function,
                                                                            const FunctionIR& ir) {
    std::unordered_map<int, ClosureInfo> byInst;

    for (int instIndex = 0; instIndex < (int)ir.size(); ++instIndex) {
        const auto& inst = ir[instIndex];
        if (inst.stdOp != OP_NEWCLOSURE && inst.stdOp != OP_DUPCLOSURE) {
            continue;
        }

        int childProto = resolveChildProtoIndex(chunk, function, inst);
        if (childProto < 0) {
            continue;
        }

        ClosureInfo info;
        info.instIndex = instIndex;
        info.targetSlot = inst.a;
        info.childProto = childProto;

        int expectedCaptures = chunk.functions[childProto].numUpvalues;
        for (int lookahead = instIndex + 1;
             lookahead < (int)ir.size() && (int)info.captures.size() < expectedCaptures;
             ++lookahead) {
            const auto& captureInst = ir[lookahead];
            if (captureInst.stdOp != OP_CAPTURE) {
                break;
            }
            info.captures.push_back({captureInst.a, captureInst.b});
        }

        byInst[instIndex] = std::move(info);
    }

    return byInst;
}

static std::vector<int> sortedSlotsFromSet(const std::unordered_set<int>& slots) {
    std::vector<int> out(slots.begin(), slots.end());
    std::sort(out.begin(), out.end());
    return out;
}

static std::unordered_map<int, std::unordered_set<int>> computeTransitiveUpvalueWriteSummaries(const Chunk& chunk,
                                                                                                const OpcodeMap& opmap) {
    std::unordered_map<int, FunctionIR> irByProto;
    std::unordered_map<int, std::unordered_map<int, ClosureInfo>> closuresByProto;
    std::unordered_map<int, std::unordered_set<int>> directWritesByProto;
    std::unordered_map<int, std::unordered_set<int>> summaryByProto;
    static const std::vector<int> kNoCallClobbers;

    for (const auto& function : chunk.functions) {
        FunctionIR ir = decodeFunctionIR(function, opmap);
        irByProto[function.id] = ir;
        closuresByProto[function.id] = collectClosureInfoByInstruction(chunk, function, irByProto[function.id]);

        std::unordered_set<int> directWrites;
        for (const auto& inst : irByProto[function.id]) {
            if (inst.stdOp == OP_SETUPVAL) {
                directWrites.insert(inst.b);
            }
        }

        directWritesByProto[function.id] = directWrites;
        summaryByProto[function.id] = directWrites;
    }

    bool changed = true;
    int maxIters = std::max(8, (int)chunk.functions.size() * 4);
    for (int iter = 0; iter < maxIters && changed; ++iter) {
        changed = false;

        for (const auto& function : chunk.functions) {
            const FunctionIR& ir = irByProto[function.id];
            const auto& closureByInst = closuresByProto[function.id];

            std::unordered_set<int> newWrites = directWritesByProto[function.id];
            std::unordered_map<int, int> slotClosureInst;

            for (int instIndex = 0; instIndex < (int)ir.size(); ++instIndex) {
                const auto& inst = ir[instIndex];

                if ((inst.stdOp == OP_CALL || inst.stdOp == OP_NATIVECALL)) {
                    auto closureIt = slotClosureInst.find(inst.a);
                    if (closureIt != slotClosureInst.end()) {
                        auto infoIt = closureByInst.find(closureIt->second);
                        if (infoIt != closureByInst.end()) {
                            int childProto = infoIt->second.childProto;
                            auto childSummaryIt = summaryByProto.find(childProto);
                            if (childSummaryIt != summaryByProto.end()) {
                                for (int childUpvalueIndex : childSummaryIt->second) {
                                    if (childUpvalueIndex < 0 ||
                                        childUpvalueIndex >= (int)infoIt->second.captures.size()) {
                                        continue;
                                    }
                                    const auto& capture = infoIt->second.captures[childUpvalueIndex];
                                    if (capture.type == 2 && capture.source >= 0 && capture.source < function.numUpvalues) {
                                        newWrites.insert(capture.source);
                                    }
                                }
                            }
                        }
                    }
                }

                if ((inst.stdOp == OP_NEWCLOSURE || inst.stdOp == OP_DUPCLOSURE) && closureByInst.count(instIndex)) {
                    slotClosureInst[inst.a] = instIndex;
                    continue;
                }

                if (inst.stdOp == OP_MOVE) {
                    auto srcIt = slotClosureInst.find(inst.b);
                    if (srcIt != slotClosureInst.end()) {
                        slotClosureInst[inst.a] = srcIt->second;
                    } else {
                        slotClosureInst.erase(inst.a);
                    }
                    continue;
                }

                SlotAccess access = analyzeSlotAccess(function, inst, kNoCallClobbers, -1);
                for (int defSlot : access.defs) {
                    slotClosureInst.erase(defSlot);
                }
            }

            if (newWrites != summaryByProto[function.id]) {
                summaryByProto[function.id] = std::move(newWrites);
                changed = true;
            }
        }
    }

    return summaryByProto;
}

static std::unordered_map<int, std::vector<int>> computePreciseCallClobbers(
    const Chunk& chunk,
    const Function& function,
    const FunctionIR& ir,
    const std::unordered_set<int>& escapedMutableSlots,
    const std::vector<int>& fallbackCallClobberSlots,
    const std::unordered_map<int, std::unordered_set<int>>& transitiveUpvalueWrites
) {
    std::unordered_map<int, std::vector<int>> clobbersByInst;
    if (ir.empty()) {
        return clobbersByInst;
    }

    const int slotCount = function.maxStackSize;
    if (slotCount <= 0) {
        return clobbersByInst;
    }

    const int kUnknownClosure = -1;
    const int kTooManyClosures = 8;

    auto closureByInst = collectClosureInfoByInstruction(chunk, function, ir);

    std::unordered_map<int, std::vector<int>> closureEffectsByInst;
    for (const auto& [instIndex, info] : closureByInst) {
        std::unordered_set<int> effectSlots;
        auto summaryIt = transitiveUpvalueWrites.find(info.childProto);
        if (summaryIt != transitiveUpvalueWrites.end()) {
            for (int upvalueIndex : summaryIt->second) {
                if (upvalueIndex < 0 || upvalueIndex >= (int)info.captures.size()) {
                    continue;
                }
                const auto& capture = info.captures[upvalueIndex];
                if (capture.type == 2) {
                    int parentUpvalueSlot = upvalueCellSlot(function, capture.source);
                    if (escapedMutableSlots.count(parentUpvalueSlot)) {
                        effectSlots.insert(parentUpvalueSlot);
                    }
                } else if (capture.type == 1) {
                    int parentSlot = capture.source;
                    if (parentSlot >= 0 && escapedMutableSlots.count(parentSlot)) {
                        effectSlots.insert(parentSlot);
                    }
                }
            }
        }
        closureEffectsByInst[instIndex] = sortedSlotsFromSet(effectSlots);
    }

    std::vector<std::unordered_set<int>> inState(ir.size());
    std::vector<std::unordered_set<int>> outState(ir.size());
    std::vector<int> pcToInst(function.instructions.size(), -1);
    for (int i = 0; i < (int)ir.size(); ++i) {
        if (ir[i].pc >= 0 && ir[i].pc < (int)pcToInst.size()) {
            pcToInst[ir[i].pc] = i;
        }
    }

    std::vector<std::vector<int>> preds(ir.size());
    std::vector<std::vector<int>> succs(ir.size());
    auto addEdge = [&](int from, int to) {
        if (from < 0 || to < 0 || from >= (int)ir.size() || to >= (int)ir.size()) {
            return;
        }
        if (std::find(succs[from].begin(), succs[from].end(), to) == succs[from].end()) {
            succs[from].push_back(to);
            preds[to].push_back(from);
        }
    };

    for (int i = 0; i < (int)ir.size(); ++i) {
        const auto& inst = ir[i];
        int next = i + 1;
        bool isTerminator = false;
        if (inst.stdOp == OP_JUMP || inst.stdOp == OP_JUMPBACK || inst.stdOp == OP_JUMPX || inst.stdOp == OP_RETURN) {
            isTerminator = true;
        }
        if (!isTerminator && next < (int)ir.size()) {
            addEdge(i, next);
        }
        if (inst.jumpTargetPc.has_value()) {
            int targetInst = (*inst.jumpTargetPc >= 0 && *inst.jumpTargetPc < (int)pcToInst.size()) ? pcToInst[*inst.jumpTargetPc] : -1;
            addEdge(i, targetInst);
        }
    }

    auto transfer = [&](const std::unordered_set<int>& inSet, int instIndex) -> std::unordered_set<int> {
        std::unordered_set<int> out = inSet;
        const auto& inst = ir[instIndex];
        static constexpr int kSlotClosureEncodingBase = 1000000;
        static const std::vector<int> kNoCallClobbers;

        auto assignUnknown = [&](int slot) {
            if (slot >= 0 && slot < slotCount) {
                out.insert(kUnknownClosure * (slotCount + 1) - slot - 1); 
            }
        };
        auto clearUnknown = [&](int slot) {
            out.erase(kUnknownClosure * (slotCount + 1) - slot - 1);
        };
        auto hasUnknown = [&](int slot) {
            return out.count(kUnknownClosure * (slotCount + 1) - slot - 1) != 0;
        };
        auto getClosureIds = [&](int slot) {
            std::unordered_set<int> ids;
            for (int value : out) {
                int encodedPrefix = slot * kSlotClosureEncodingBase;
                if (value >= encodedPrefix && value < encodedPrefix + kSlotClosureEncodingBase) {
                    ids.insert(value - encodedPrefix);
                }
            }
            return ids;
        };
        auto clearSlotClosures = [&](int slot) {
            int encodedPrefix = slot * kSlotClosureEncodingBase;
            std::vector<int> toErase;
            for (int value : out) {
                if (value >= encodedPrefix && value < encodedPrefix + kSlotClosureEncodingBase) {
                    toErase.push_back(value);
                }
            }
            for (int value : toErase) {
                out.erase(value);
            }
        };
        auto setSlotClosure = [&](int slot, int closureInstIndex) {
            if (slot < 0 || slot >= slotCount) {
                return;
            }
            clearSlotClosures(slot);
            clearUnknown(slot);
            out.insert(slot * kSlotClosureEncodingBase + closureInstIndex);
        };
        auto copySlot = [&](int dst, int src) {
            if (dst < 0 || dst >= slotCount || src < 0 || src >= slotCount) {
                return;
            }
            clearSlotClosures(dst);
            clearUnknown(dst);
            int encodedPrefix = src * kSlotClosureEncodingBase;
            std::vector<int> toInsert;
            for (int value : out) {
                if (value >= encodedPrefix && value < encodedPrefix + kSlotClosureEncodingBase) {
                    toInsert.push_back((dst * kSlotClosureEncodingBase) + (value - encodedPrefix));
                }
            }
            for (int value : toInsert) {
                out.insert(value);
            }
            if (hasUnknown(src)) {
                out.insert(kUnknownClosure * (slotCount + 1) - dst - 1);
            }
            auto ids = getClosureIds(dst);
            if (ids.size() > kTooManyClosures) {
                clearSlotClosures(dst);
                assignUnknown(dst);
            }
        };

        switch (inst.stdOp) {
            case OP_NEWCLOSURE:
            case OP_DUPCLOSURE:
                if (closureByInst.count(instIndex)) {
                    setSlotClosure(inst.a, instIndex);
                } else {
                    clearSlotClosures(inst.a);
                    assignUnknown(inst.a);
                }
                break;
            case OP_MOVE:
                copySlot(inst.a, inst.b);
                break;
            case OP_CALL:
            case OP_NATIVECALL:
            case OP_NAMECALL:
            case OP_LOADNIL:
            case OP_LOADB:
            case OP_LOADN:
            case OP_LOADK:
            case OP_LOADKX:
            case OP_GETGLOBAL:
            case OP_GETIMPORT:
            case OP_GETUPVAL:
            case OP_GETTABLE:
            case OP_GETTABLEKS:
            case OP_GETTABLEN:
            case OP_GETVARARGS:
            case OP_NOT:
            case OP_MINUS:
            case OP_LENGTH:
            case OP_ADD:
            case OP_SUB:
            case OP_MUL:
            case OP_DIV:
            case OP_MOD:
            case OP_POW:
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
            case OP_IDIV:
            case OP_IDIVK:
            case OP_CONCAT:
            case OP_NEWTABLE:
            case OP_DUPTABLE:
                break;
            default:
                break;
        }

        SlotAccess raw = analyzeSlotAccess(function, inst, kNoCallClobbers, -1);
        std::vector<int> defs = raw.defs;

        for (int slot : defs) {
            if (slot < 0 || slot >= slotCount) {
                continue;
            }
            if (inst.stdOp != OP_NEWCLOSURE && inst.stdOp != OP_DUPCLOSURE && inst.stdOp != OP_MOVE) {
                clearSlotClosures(slot);
                assignUnknown(slot);
            }
        }

        return out;
    };

    bool changed = true;
    while (changed) {
        changed = false;
        for (int instIndex = 0; instIndex < (int)ir.size(); ++instIndex) {
            std::unordered_set<int> newIn;
            if (!preds[instIndex].empty()) {
                for (int pred : preds[instIndex]) {
                    newIn.insert(outState[pred].begin(), outState[pred].end());
                }
            }
            if (newIn != inState[instIndex]) {
                inState[instIndex] = newIn;
                changed = true;
            }

            std::unordered_set<int> newOut = transfer(inState[instIndex], instIndex);
            if (newOut != outState[instIndex]) {
                outState[instIndex] = std::move(newOut);
                changed = true;
            }
        }
    }

    auto slotUnknownMarker = [&](int slot) {
        return kUnknownClosure * (slotCount + 1) - slot - 1;
    };

    for (int instIndex = 0; instIndex < (int)ir.size(); ++instIndex) {
        const auto& inst = ir[instIndex];
        if (inst.stdOp != OP_CALL && inst.stdOp != OP_NATIVECALL) {
            continue;
        }

        int calleeSlot = inst.a;
        bool unknown = calleeSlot < 0 || calleeSlot >= slotCount || inState[instIndex].count(slotUnknownMarker(calleeSlot)) != 0;
        std::unordered_set<int> closureInsts;
        if (!unknown && calleeSlot >= 0 && calleeSlot < slotCount) {
            int encodedPrefix = calleeSlot * 1000000;
            for (int value : inState[instIndex]) {
                if (value >= encodedPrefix && value < encodedPrefix + 1000000) {
                    closureInsts.insert(value - encodedPrefix);
                }
            }
            if (closureInsts.empty()) {
                unknown = true;
            }
        }

        if (unknown) {
            clobbersByInst[instIndex] = fallbackCallClobberSlots;
            continue;
        }

        std::unordered_set<int> preciseSlots;
        bool precise = true;
        for (int closureInst : closureInsts) {
            auto it = closureEffectsByInst.find(closureInst);
            if (it == closureEffectsByInst.end()) {
                precise = false;
                break;
            }
            for (int slot : it->second) {
                preciseSlots.insert(slot);
            }
        }

        if (precise) {
            clobbersByInst[instIndex] = sortedSlotsFromSet(preciseSlots);
        } else {
            clobbersByInst[instIndex] = fallbackCallClobberSlots;
        }
    }

    return clobbersByInst;
}

static SlotAccess analyzeSlotAccess(const Function& function, const DecodedInstruction& inst,
                                    const std::vector<int>& callClobberSlots, int openResultBase) {
    SlotAccess access;
    switch (inst.stdOp) {
        case OP_MOVE:
            addUnique(access.uses, inst.b);
            addUnique(access.defs, inst.a);
            break;
        case OP_LOADNIL:
        case OP_LOADB:
        case OP_LOADN:
        case OP_LOADK:
        case OP_LOADKX:
        case OP_GETGLOBAL:
        case OP_GETIMPORT:
        case OP_NEWTABLE:
        case OP_DUPTABLE:
        case OP_NEWCLOSURE:
        case OP_DUPCLOSURE:
            addUnique(access.defs, inst.a);
            break;
        case OP_GETUPVAL:
            addUnique(access.uses, upvalueCellSlot(function, inst.b));
            addUnique(access.defs, inst.a);
            break;
        case OP_GETTABLE:
            addUnique(access.uses, inst.b);
            addUnique(access.uses, inst.c);
            addUnique(access.defs, inst.a);
            break;
        case OP_GETTABLEKS:
        case OP_GETTABLEN:
            addUnique(access.uses, inst.b);
            addUnique(access.defs, inst.a);
            break;
        case OP_SETTABLE:
            addUnique(access.uses, inst.a);
            addUnique(access.uses, inst.b);
            addUnique(access.uses, inst.c);
            access.hasSideEffects = true;
            break;
        case OP_SETTABLEKS:
        case OP_SETTABLEN:
            addUnique(access.uses, inst.a);
            addUnique(access.uses, inst.b);
            access.hasSideEffects = true;
            break;
        case OP_SETUPVAL:
            addUnique(access.uses, inst.a);
            addUnique(access.defs, upvalueCellSlot(function, inst.b));
            access.hasSideEffects = true;
            break;
        case OP_SETGLOBAL:
            addUnique(access.uses, inst.a);
            access.hasSideEffects = true;
            break;
        case OP_NAMECALL:
            addUnique(access.uses, inst.b);
            addUnique(access.defs, inst.a);
            addUnique(access.defs, inst.a + 1);
            break;
        case OP_CALL: {
            if (inst.b == 0) {
                addUnique(access.uses, inst.a);
                if (openResultBase >= inst.a + 1) {
                    addRange(access.uses, inst.a + 1, openResultBase - inst.a);
                }
            } else {
                addRange(access.uses, inst.a, inst.b);
            }
            if (inst.c == 0) {
                addUnique(access.defs, inst.a);
            } else if (inst.c > 1) {
                addRange(access.defs, inst.a, inst.c - 1);
            }
            for (int slot : callClobberSlots) {
                
                
                
                if (inst.c == 0 && slot >= inst.a && slot < function.maxStackSize) {
                    continue;
                }
                if (std::find(access.defs.begin(), access.defs.end(), slot) == access.defs.end()) {
                    addUnique(access.clobberDefs, slot);
                }
            }
            access.hasSideEffects = true;
            break;
        }
        case OP_NATIVECALL:
            addUnique(access.uses, inst.a);
            addUnique(access.defs, inst.a);
            for (int slot : callClobberSlots) {
                if (std::find(access.defs.begin(), access.defs.end(), slot) == access.defs.end()) {
                    addUnique(access.clobberDefs, slot);
                }
            }
            access.hasSideEffects = true;
            break;
        case OP_RETURN:
            if (inst.b > 1) {
                addRange(access.uses, inst.a, inst.b - 1);
            } else if (inst.b == 0) {
                addUnique(access.uses, inst.a);
                if (openResultBase >= inst.a + 1) {
                    addRange(access.uses, inst.a + 1, openResultBase - inst.a);
                }
            }
            access.hasSideEffects = true;
            break;
        case OP_JUMPIF:
        case OP_JUMPIFNOT:
        case OP_JUMPXEQKNIL:
        case OP_JUMPXEQKB:
        case OP_JUMPXEQKN:
        case OP_JUMPXEQKS:
            addUnique(access.uses, inst.a);
            break;
        case OP_JUMPIFEQ:
        case OP_JUMPIFNOTEQ:
        case OP_JUMPIFLE:
        case OP_JUMPIFLT:
        case OP_JUMPIFNOTLE:
        case OP_JUMPIFNOTLT:
            addUnique(access.uses, inst.a);
            addUnique(access.uses, (int)inst.aux);
            break;
        case OP_ADD:
        case OP_SUB:
        case OP_MUL:
        case OP_DIV:
        case OP_MOD:
        case OP_POW:
        case OP_AND:
        case OP_OR:
            addUnique(access.uses, inst.b);
            addUnique(access.uses, inst.c);
            addUnique(access.defs, inst.a);
            break;
        case OP_ADDK:
        case OP_SUBK:
        case OP_MULK:
        case OP_DIVK:
        case OP_MODK:
        case OP_POWK:
        case OP_ANDK:
        case OP_ORK:
        case OP_NOT:
        case OP_MINUS:
        case OP_LENGTH:
            addUnique(access.uses, inst.b);
            addUnique(access.defs, inst.a);
            break;
        case OP_SUBRK:
        case OP_DIVRK:
            addUnique(access.uses, inst.c);
            addUnique(access.defs, inst.a);
            break;
        case OP_CONCAT:
            addRange(access.uses, inst.b, (int)inst.c - (int)inst.b + 1);
            addUnique(access.defs, inst.a);
            break;
        case OP_GETVARARGS:
            if (inst.b == 0) addUnique(access.defs, inst.a);
            else addRange(access.defs, inst.a, inst.b - 1);
            break;
        case OP_FORNPREP:
            addUnique(access.uses, inst.a);
            addUnique(access.uses, inst.a + 1);
            addUnique(access.uses, inst.a + 2);
            break;
        case OP_FORNLOOP:
            addUnique(access.uses, inst.a);
            addUnique(access.uses, inst.a + 1);
            addUnique(access.uses, inst.a + 2);
            addUnique(access.defs, inst.a + 2);
            break;
        case OP_FORGPREP:
        case OP_FORGPREP_NEXT:
        case OP_FORGPREP_INEXT:
            addUnique(access.uses, inst.a);
            addUnique(access.uses, inst.a + 1);
            addUnique(access.uses, inst.a + 2);
            break;
        case OP_FORGLOOP:
            addUnique(access.uses, inst.a);
            addUnique(access.uses, inst.a + 1);
            addUnique(access.uses, inst.a + 2);
            addUnique(access.defs, inst.a + 3);
            addUnique(access.defs, inst.a + 4);
            break;
        case OP_CAPTURE:
            if (inst.a == 2) {
                addUnique(access.uses, upvalueCellSlot(function, inst.b));
            } else {
                addUnique(access.uses, inst.b);
            }
            break;
        case OP_SETLIST:
            addUnique(access.uses, inst.a);
            if (inst.c > 0) {
                addRange(access.uses, inst.b, inst.c - 1);
            } else {
                addUnique(access.uses, inst.b);
                if (openResultBase >= inst.b + 1) {
                    addRange(access.uses, inst.b + 1, openResultBase - inst.b);
                }
            }
            access.hasSideEffects = true;
            break;
        default:
            break;
    }
    return access;
}

static std::unordered_set<int> collectEscapedMutableSlots(const Function& function, const FunctionIR& ir) {
    std::unordered_set<int> slots;

    for (const auto& instruction : ir) {
        if (instruction.stdOp == OP_CAPTURE) {
            if (instruction.a == 1) {
                slots.insert(instruction.b);
            } else if (instruction.a == 2) {
                int slot = upvalueCellSlot(function, instruction.b);
                if (slot >= 0) {
                    slots.insert(slot);
                }
            }
        } else if (instruction.stdOp == OP_SETUPVAL) {
            int slot = upvalueCellSlot(function, instruction.b);
            if (slot >= 0) {
                slots.insert(slot);
            }
        }
    }

    return slots;
}

static std::vector<std::vector<int>> buildDominatorTree(const std::vector<int>& idom) {
    std::vector<std::vector<int>> tree(idom.size());
    for (int blockId = 0; blockId < (int)idom.size(); ++blockId) {
        if (idom[blockId] >= 0) {
            tree[idom[blockId]].push_back(blockId);
        }
    }
    return tree;
}

static std::vector<std::vector<int>> buildDominanceFrontier(const ControlFlowGraph& cfg) {
    std::vector<std::vector<int>> frontier(cfg.blocks.size());
    for (const auto& block : cfg.blocks) {
        if (block.predecessors.size() < 2) {
            continue;
        }
        for (int pred : block.predecessors) {
            int runner = pred;
            while (runner >= 0 && runner != cfg.immediateDominator[block.id]) {
                addUnique(frontier[runner], block.id);
                runner = cfg.immediateDominator[runner];
            }
        }
    }
    return frontier;
}

static int makeValue(const Function& function, SSAFunction& ssa, int slot, int version, int blockId, int instIndex, bool isPhi, bool isParameter) {
    SSAVariable value;
    value.id = (int)ssa.values.size();
    value.slot = slot;
    value.version = version;
    value.definingBlock = blockId;
    value.definingInstruction = instIndex;
    value.isPhi = isPhi;
    value.isParameter = isParameter;
    const int firstUpvalueSlot = function.maxStackSize;
    const int pastLastUpvalueSlot = function.maxStackSize + function.numUpvalues;
    if (slot >= firstUpvalueSlot && slot < pastLastUpvalueSlot) {
        value.isUpvalue = true;
        value.upvalueIndex = slot - function.maxStackSize;
    }
    ssa.values.push_back(value);
    return value.id;
}

static int ensureCurrentValue(const Function& function, SSAFunction& ssa, std::vector<std::vector<int>>& stacks, std::vector<int>& nextVersion, int slot) {
    if (slot < 0 || slot >= (int)stacks.size()) {
        return -1;
    }
    if (stacks[slot].empty()) {
        int valueId = makeValue(function, ssa, slot, nextVersion[slot]++, 0, -1, false, false);
        stacks[slot].push_back(valueId);
    }
    return stacks[slot].back();
}

static std::string localNameForSlot(const Function& function, int slot) {
    if (slot >= function.maxStackSize) {
        int upvalueIndex = slot - function.maxStackSize;
        if (upvalueIndex >= 0 && upvalueIndex < (int)function.upvalueNames.size() && !function.upvalueNames[upvalueIndex].empty()) {
            return sanitizeLuaIdentifier(function.upvalueNames[upvalueIndex], "upval");
        }
        return "upval" + std::to_string(upvalueIndex);
    }
    for (const auto& local : function.locals) {
        if (local.slot == slot && local.startPc == 0 && !local.name.empty() && local.name[0] != '(') {
            return sanitizeLuaIdentifier(local.name, slot < function.numParams ? "p" : "v");
        }
    }
    return "";
}

static void renameBlock(SSAFunction& ssa, const Function& function, int blockId, std::vector<std::vector<int>>& stacks, std::vector<int>& nextVersion) {
    std::vector<int> pushedSlots;

    for (auto& phi : ssa.blocks[blockId].phis) {
        int valueId = makeValue(function, ssa, phi.slot, nextVersion[phi.slot]++, blockId, -1, true, false);
        phi.resultValueId = valueId;
        stacks[phi.slot].push_back(valueId);
        pushedSlots.push_back(phi.slot);
    }

    for (int instIndex : ssa.blocks[blockId].instructionRefs) {
        auto& instruction = ssa.instructions[instIndex];
        instruction.blockId = blockId;
        for (int slot : instruction.rawUses) {
            instruction.uses.push_back(ensureCurrentValue(function, ssa, stacks, nextVersion, slot));
        }
        for (int slot : instruction.rawDefs) {
            int valueId = makeValue(function, ssa, slot, nextVersion[slot]++, blockId, instIndex, false, false);
            instruction.defs.push_back(valueId);
            stacks[slot].push_back(valueId);
            pushedSlots.push_back(slot);
        }
        for (int slot : instruction.rawClobberDefs) {
            int valueId = makeValue(function, ssa, slot, nextVersion[slot]++, blockId, instIndex, false, false);
            instruction.clobberDefs.push_back(valueId);
            stacks[slot].push_back(valueId);
            pushedSlots.push_back(slot);
        }
    }

    for (int succ : ssa.cfg.blocks[blockId].successors) {
        auto& succBlock = ssa.blocks[succ];
        for (auto& phi : succBlock.phis) {
            phi.inputs[blockId] = ensureCurrentValue(function, ssa, stacks, nextVersion, phi.slot);
        }
    }

    for (int child : ssa.dominatorTree[blockId]) {
        renameBlock(ssa, function, child, stacks, nextVersion);
    }

    for (auto it = pushedSlots.rbegin(); it != pushedSlots.rend(); ++it) {
        int slot = *it;
        if (!stacks[slot].empty()) {
            stacks[slot].pop_back();
        }
    }
}
} 

SSAFunction buildSSAFunction(const Chunk& chunk, const Function& function, const OpcodeMap& opmap) {
    SSAFunction ssa;
    ssa.functionId = function.id;
    ssa.name = function.debugName;
    ssa.ir = decodeFunctionIR(function, opmap);
    ssa.cfg = buildControlFlowGraph(function, opmap);
    ssa.escapedMutableSlots = collectEscapedMutableSlots(function, ssa.ir);
    const int rawSlotCount = function.maxStackSize + function.numUpvalues;

    auto isStableEscapedLocalSlot = [&](int slot) -> bool {
        if (slot >= 0 && slot < function.numParams) {
            return true;
        }
        for (const auto& local : function.locals) {
            if (local.slot == slot && local.startPc == 0 &&
                local.endPc >= (int)function.instructions.size() &&
                !local.name.empty() && local.name[0] != '(') {
                return true;
            }
        }
        return false;
    };

    std::vector<int> escapedLocalSlots;
    escapedLocalSlots.reserve(ssa.escapedMutableSlots.size());
    for (int slot : ssa.escapedMutableSlots) {
        if (slot >= 0 && slot < function.maxStackSize && isStableEscapedLocalSlot(slot)) {
            escapedLocalSlots.push_back(slot);
        }
    }
    std::sort(escapedLocalSlots.begin(), escapedLocalSlots.end());
    escapedLocalSlots.erase(std::unique(escapedLocalSlots.begin(), escapedLocalSlots.end()), escapedLocalSlots.end());

    int nextCellSlot = rawSlotCount;
    for (int slot : escapedLocalSlots) {
        ssa.escapedSlotToCellSlot[slot] = nextCellSlot;
        ssa.cellSlotToEscapedSlot[nextCellSlot] = slot;
        ++nextCellSlot;
    }

    ssa.blocks.resize(ssa.cfg.blocks.size());
    const int totalSlots = nextCellSlot;

    std::vector<int> callClobberSlots;
    callClobberSlots.reserve(ssa.escapedMutableSlots.size() + ssa.escapedSlotToCellSlot.size());
    for (int slot : ssa.escapedMutableSlots) {
        int effectiveSlot = -1;
        if (slot >= function.maxStackSize && slot < rawSlotCount) {
            effectiveSlot = slot;
        } else if (auto it = ssa.escapedSlotToCellSlot.find(slot); it != ssa.escapedSlotToCellSlot.end()) {
            effectiveSlot = it->second;
        }
        if (effectiveSlot >= 0 && effectiveSlot < totalSlots) {
            callClobberSlots.push_back(effectiveSlot);
        }
    }
    std::sort(callClobberSlots.begin(), callClobberSlots.end());
    callClobberSlots.erase(std::unique(callClobberSlots.begin(), callClobberSlots.end()), callClobberSlots.end());

    static std::unordered_map<const Chunk*, std::unordered_map<int, std::unordered_set<int>>> summaryCache;
    auto cacheIt = summaryCache.find(&chunk);
    if (cacheIt == summaryCache.end()) {
        cacheIt = summaryCache.emplace(&chunk, computeTransitiveUpvalueWriteSummaries(chunk, opmap)).first;
    }
    const auto& transitiveUpvalueWrites = cacheIt->second;

    auto preciseCallClobbers = computePreciseCallClobbers(
        chunk, function, ssa.ir, ssa.escapedMutableSlots, callClobberSlots, transitiveUpvalueWrites
    );

    for (const auto& block : ssa.cfg.blocks) {
        ssa.blocks[block.id].blockId = block.id;
    }

    constexpr int kNoOpenResult = -1;
    int openResultBase = kNoOpenResult;
    auto remapEscapedSlot = [&](int slot) -> int {
        auto it = ssa.escapedSlotToCellSlot.find(slot);
        return it != ssa.escapedSlotToCellSlot.end() ? it->second : slot;
    };
    auto normalizeCallClobberCandidates = [&](const std::vector<int>& slots) {
        std::vector<int> normalized;
        normalized.reserve(slots.size());
        for (int slot : slots) {
            if (slot < 0) {
                continue;
            }
            if (slot >= function.maxStackSize || ssa.escapedSlotToCellSlot.count(slot) != 0) {
                addUnique(normalized, slot);
            }
        }
        return normalized;
    };
    auto remapSlots = [&](std::vector<int>& slots) {
        std::vector<int> remapped;
        remapped.reserve(slots.size());
        for (int slot : slots) {
            int mapped = remapEscapedSlot(slot);
            addUnique(remapped, mapped);
        }
        slots.swap(remapped);
    };

    for (int instIndex = 0; instIndex < (int)ssa.ir.size(); ++instIndex) {
        SSAInstruction instruction;
        instruction.index = instIndex;
        instruction.inst = ssa.ir[instIndex];
        const std::vector<int>* callClobbers = &callClobberSlots;
        static const std::vector<int> kEmptyCallClobbers;
        std::vector<int> normalizedCallClobbers;
        if (instruction.inst.stdOp != OP_CALL && instruction.inst.stdOp != OP_NATIVECALL) {
            callClobbers = &kEmptyCallClobbers;
        } else if (auto it = preciseCallClobbers.find(instIndex); it != preciseCallClobbers.end()) {
            normalizedCallClobbers = normalizeCallClobberCandidates(it->second);
            callClobbers = &normalizedCallClobbers;
        } else {
            normalizedCallClobbers = normalizeCallClobberCandidates(callClobberSlots);
            callClobbers = &normalizedCallClobbers;
        }

        SlotAccess access = analyzeSlotAccess(function, instruction.inst, *callClobbers, openResultBase);
        const std::vector<int> openWindowDefs = access.defs;
        const std::vector<int> openWindowClobberDefs = access.clobberDefs;
        remapSlots(access.uses);
        remapSlots(access.defs);
        remapSlots(access.clobberDefs);
        instruction.rawUses = std::move(access.uses);
        instruction.rawDefs = std::move(access.defs);
        instruction.rawClobberDefs = std::move(access.clobberDefs);
        instruction.hasSideEffects = access.hasSideEffects;

        ssa.instructions.push_back(std::move(instruction));

        int blockId = (instruction.inst.pc >= 0 && instruction.inst.pc < (int)ssa.cfg.pcToBlock.size())
            ? ssa.cfg.pcToBlock[instruction.inst.pc]
            : -1;
        if (blockId >= 0) {
            ssa.blocks[blockId].instructionRefs.push_back(instIndex);
        }

        const auto& irInst = ssa.ir[instIndex];
        const bool producesOpenResults =
            (irInst.stdOp == OP_CALL && irInst.c == 0) ||
            (irInst.stdOp == OP_GETVARARGS && irInst.b == 0);
        const bool consumesOpenResults =
            (irInst.stdOp == OP_CALL && irInst.b == 0) ||
            (irInst.stdOp == OP_RETURN && irInst.b == 0) ||
            (irInst.stdOp == OP_SETLIST && irInst.c == 0);
        const bool fixedCallClosesResults = (irInst.stdOp == OP_CALL && irInst.c != 0);

        bool clobbersOpenWindow = false;
        if (openResultBase != kNoOpenResult) {
            for (int slot : openWindowDefs) {
                if (slot >= openResultBase) {
                    clobbersOpenWindow = true;
                    break;
                }
            }
            if (!clobbersOpenWindow) {
                for (int slot : openWindowClobberDefs) {
                    if (slot >= openResultBase) {
                        clobbersOpenWindow = true;
                        break;
                    }
                }
            }
        }

        if (producesOpenResults) {
            openResultBase = irInst.a;
        } else if (consumesOpenResults || fixedCallClosesResults || clobbersOpenWindow) {
            openResultBase = kNoOpenResult;
        }
    }

    ssa.dominatorTree = buildDominatorTree(ssa.cfg.immediateDominator);
    ssa.dominanceFrontier = buildDominanceFrontier(ssa.cfg);

    std::vector<std::unordered_set<int>> definedSlots(ssa.blocks.size());
    std::vector<std::vector<int>> definitionBlocks(totalSlots);
    for (const auto& block : ssa.blocks) {
        for (int instIndex : block.instructionRefs) {
            for (int slot : ssa.instructions[instIndex].rawDefs) {
                if (slot >= 0 && slot < totalSlots && !definedSlots[block.blockId].count(slot)) {
                    definedSlots[block.blockId].insert(slot);
                    definitionBlocks[slot].push_back(block.blockId);
                }
            }
            for (int slot : ssa.instructions[instIndex].rawClobberDefs) {
                if (slot >= 0 && slot < totalSlots && !definedSlots[block.blockId].count(slot)) {
                    definedSlots[block.blockId].insert(slot);
                    definitionBlocks[slot].push_back(block.blockId);
                }
            }
        }
    }

    for (int slot = 0; slot < totalSlots; ++slot) {
        std::vector<int> worklist = definitionBlocks[slot];
        std::unordered_set<int> visited(worklist.begin(), worklist.end());
        std::unordered_set<int> hasPhi;

        while (!worklist.empty()) {
            int blockId = worklist.back();
            worklist.pop_back();
            for (int frontierBlock : ssa.dominanceFrontier[blockId]) {
                if (hasPhi.insert(frontierBlock).second) {
                    PhiNode phi;
                    phi.blockId = frontierBlock;
                    phi.slot = slot;
                    ssa.blocks[frontierBlock].phiIndexBySlot[slot] = (int)ssa.blocks[frontierBlock].phis.size();
                    ssa.blocks[frontierBlock].phis.push_back(phi);

                    if (!definedSlots[frontierBlock].count(slot) && !visited.count(frontierBlock)) {
                        visited.insert(frontierBlock);
                        worklist.push_back(frontierBlock);
                    }
                }
            }
        }
    }

    std::vector<std::vector<int>> stacks(totalSlots);
    std::vector<int> nextVersion(totalSlots, 0);
    for (int slot = 0; slot < function.numParams && slot < function.maxStackSize; ++slot) {
        int logicalSlot = slot;
        int targetSlot = remapEscapedSlot(slot);
        int valueId = makeValue(function, ssa, targetSlot, nextVersion[targetSlot]++, 0, -1, false, true);
        stacks[targetSlot].push_back(valueId);
        if (targetSlot != logicalSlot) {
            int fallbackValueId = makeValue(function, ssa, logicalSlot, nextVersion[logicalSlot]++, 0, -1, false, true);
            stacks[logicalSlot].push_back(fallbackValueId);
        }
    }
    for (int upvalueIndex = 0; upvalueIndex < function.numUpvalues; ++upvalueIndex) {
        int slot = upvalueCellSlot(function, upvalueIndex);
        int targetSlot = remapEscapedSlot(slot);
        int valueId = makeValue(function, ssa, targetSlot, nextVersion[targetSlot]++, 0, -1, false, false);
        stacks[targetSlot].push_back(valueId);
        if (targetSlot != slot) {
            int fallbackValueId = makeValue(function, ssa, slot, nextVersion[slot]++, 0, -1, false, false);
            stacks[slot].push_back(fallbackValueId);
        }
    }

    if (!ssa.blocks.empty()) {
        renameBlock(ssa, function, 0, stacks, nextVersion);
    }

    for (auto& block : ssa.blocks) {
        for (auto& phi : block.phis) {
            for (const auto& [pred, valueId] : phi.inputs) {
                (void)pred;
                if (valueId >= 0 && valueId < (int)ssa.values.size()) {
                    ssa.values[valueId].useCount++;
                }
            }
        }
    }

    for (const auto& instruction : ssa.instructions) {
        for (int valueId : instruction.uses) {
            if (valueId >= 0 && valueId < (int)ssa.values.size()) {
                ssa.values[valueId].useCount++;
            }
        }
    }

    std::unordered_map<std::string, int> usedNames;
    for (auto& value : ssa.values) {
        int logicalSlot = value.slot;
        bool isEscapedCellValue = false;
        if (auto it = ssa.cellSlotToEscapedSlot.find(value.slot); it != ssa.cellSlotToEscapedSlot.end()) {
            logicalSlot = it->second;
            isEscapedCellValue = true;
        }

        std::string baseName;
        if (value.isParameter) {
            baseName = localNameForSlot(function, logicalSlot);
            if (baseName.empty()) {
                baseName = "p" + std::to_string(logicalSlot);
            }
        } else if (value.isUpvalue) {
            baseName = localNameForSlot(function, logicalSlot);
            if (baseName.empty()) {
                baseName = "upval" + std::to_string(value.upvalueIndex);
            }
        } else {
            baseName = "v" + std::to_string(logicalSlot);
        }

        if (isEscapedCellValue && !value.isParameter && !value.isUpvalue) {
            baseName = sanitizeLuaIdentifier(baseName + "Cell", "cell");
        }

        int count = usedNames[baseName]++;
        value.name = count == 0 ? baseName : baseName + "_" + std::to_string(count);
    }

    return ssa;
}

std::string formatSSA(const Chunk& chunk, const OpcodeMap& opmap) {
    std::ostringstream out;
    out << "-- SSA Dump\n";
    out << "-- Functions: " << chunk.functions.size() << "\n\n";

    for (const auto& function : chunk.functions) {
        SSAFunction ssa = buildSSAFunction(chunk, function, opmap);
        out << "Function proto#" << function.id;
        if (!function.debugName.empty()) {
            out << " \"" << function.debugName << "\"";
        }
        if (function.lineDefined > 0) {
            out << " line " << function.lineDefined;
        }
        out << "\n";

        for (const auto& block : ssa.blocks) {
            out << "  block b" << block.blockId << "\n";
            for (const auto& phi : block.phis) {
                const auto& result = ssa.values[phi.resultValueId];
                out << "    phi " << result.name << " <- ";
                bool first = true;
                for (const auto& [pred, valueId] : phi.inputs) {
                    if (!first) out << ", ";
                    first = false;
                    out << "b" << pred << ":" << ssa.values[valueId].name;
                }
                out << "\n";
            }
            for (int instIndex : block.instructionRefs) {
                const auto& instruction = ssa.instructions[instIndex];
                out << "    [" << instruction.inst.pc << "] " << instruction.inst.opName;
                if (!instruction.defs.empty()) {
                    out << " defs=";
                    for (size_t i = 0; i < instruction.defs.size(); ++i) {
                        if (i) out << ", ";
                        out << ssa.values[instruction.defs[i]].name;
                    }
                }
                if (!instruction.uses.empty()) {
                    out << " uses=";
                    for (size_t i = 0; i < instruction.uses.size(); ++i) {
                        if (i) out << ", ";
                        out << ssa.values[instruction.uses[i]].name;
                    }
                }
                if (!instruction.clobberDefs.empty()) {
                    out << " clobber=";
                    for (size_t i = 0; i < instruction.clobberDefs.size(); ++i) {
                        if (i) out << ", ";
                        out << ssa.values[instruction.clobberDefs[i]].name;
                    }
                }
                out << "\n";
            }
        }
        out << "\n";
    }

    return out.str();
}
