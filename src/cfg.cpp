#include "cfg.hpp"
#include <algorithm>
#include <sstream>
#include <unordered_set>

static bool isConditionalJump(int op) {
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

static bool isTerminal(int op) {
    return op == OP_RETURN;
}

static const char* edgeKindName(CFGEdgeKind kind) {
    switch (kind) {
        case CFGEdgeKind::Fallthrough: return "fallthrough";
        case CFGEdgeKind::Jump: return "jump";
        case CFGEdgeKind::BranchTrue: return "branch_true";
        case CFGEdgeKind::BranchFalse: return "branch_false";
        case CFGEdgeKind::LoopBack: return "loop_back";
        case CFGEdgeKind::LoopExit: return "loop_exit";
        default: return "unknown";
    }
}

static void appendUnique(std::vector<int>& values, int value) {
    if (std::find(values.begin(), values.end(), value) == values.end()) {
        values.push_back(value);
    }
}

static void addEdge(ControlFlowGraph& cfg, int fromBlock, int toBlock, int sourcePc, CFGEdgeKind kind) {
    if (fromBlock < 0 || toBlock < 0 || fromBlock >= (int)cfg.blocks.size() || toBlock >= (int)cfg.blocks.size()) {
        return;
    }

    cfg.edges.push_back({fromBlock, toBlock, sourcePc, kind});
    appendUnique(cfg.blocks[fromBlock].successors, toBlock);
    appendUnique(cfg.blocks[toBlock].predecessors, fromBlock);
}

static std::vector<std::unordered_set<int>> computeDominanceSets(const ControlFlowGraph& cfg, bool postDominators) {
    const int blockCount = (int)cfg.blocks.size();
    std::vector<std::unordered_set<int>> dom(blockCount);
    if (blockCount == 0) {
        return dom;
    }

    std::vector<int> seeds;
    if (!postDominators) {
        seeds.push_back(0);
    } else {
        for (const auto& block : cfg.blocks) {
            if (block.successors.empty()) {
                seeds.push_back(block.id);
            }
        }
        if (seeds.empty()) {
            seeds.push_back(blockCount - 1);
        }
    }

    for (const auto& block : cfg.blocks) {
        bool isSeed = std::find(seeds.begin(), seeds.end(), block.id) != seeds.end();
        if (isSeed) {
            dom[block.id].insert(block.id);
        } else {
            for (const auto& candidate : cfg.blocks) {
                dom[block.id].insert(candidate.id);
            }
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (const auto& block : cfg.blocks) {
            bool isSeed = std::find(seeds.begin(), seeds.end(), block.id) != seeds.end();
            if (isSeed) {
                continue;
            }

            const std::vector<int>& incoming = postDominators ? block.successors : block.predecessors;
            std::unordered_set<int> nextSet;
            bool first = true;

            if (incoming.empty()) {
                nextSet.insert(block.id);
            } else {
                for (int other : incoming) {
                    if (first) {
                        nextSet = dom[other];
                        first = false;
                    } else {
                        std::unordered_set<int> intersection;
                        for (int value : nextSet) {
                            if (dom[other].count(value)) {
                                intersection.insert(value);
                            }
                        }
                        nextSet = std::move(intersection);
                    }
                }
                nextSet.insert(block.id);
            }

            if (nextSet != dom[block.id]) {
                dom[block.id] = std::move(nextSet);
                changed = true;
            }
        }
    }

    return dom;
}

static std::vector<int> computeImmediateDominators(const ControlFlowGraph& cfg, const std::vector<std::unordered_set<int>>& domSets, bool postDominators) {
    const int blockCount = (int)cfg.blocks.size();
    std::vector<int> idom(blockCount, -1);
    if (blockCount == 0) {
        return idom;
    }

    for (const auto& block : cfg.blocks) {
        bool isSeed = (!postDominators && block.id == 0) || (postDominators && block.successors.empty());
        if (isSeed) {
            idom[block.id] = -1;
            continue;
        }

        std::vector<int> strictDominators;
        for (int candidate : domSets[block.id]) {
            if (candidate != block.id) {
                strictDominators.push_back(candidate);
            }
        }

        for (int candidate : strictDominators) {
            bool isImmediate = true;
            for (int other : strictDominators) {
                if (other == candidate) {
                    continue;
                }
                if (domSets[other].count(candidate)) {
                    isImmediate = false;
                    break;
                }
            }
            if (isImmediate) {
                idom[block.id] = candidate;
                break;
            }
        }
    }

    return idom;
}

ControlFlowGraph buildControlFlowGraph(const Function& function, const OpcodeMap& opmap) {
    ControlFlowGraph cfg;
    const int numInst = (int)function.instructions.size();
    cfg.pcToBlock.assign(numInst, -1);
    cfg.rawPcToInstruction.assign(numInst, -1);
    if (numInst == 0) {
        return cfg;
    }

    FunctionIR instructions = decodeFunctionIR(function, opmap);
    std::unordered_set<int> leaders;
    leaders.insert(0);

    for (const auto& inst : instructions) {
        if (inst.jumpTargetPc.has_value()) {
            int targetPc = *inst.jumpTargetPc;
            if (targetPc >= 0 && targetPc < numInst) {
                leaders.insert(targetPc);
            }
        }

        int nextPc = inst.pc + inst.width;
        if (!isTerminal(inst.stdOp) && nextPc < numInst &&
            (inst.stdOp == OP_JUMP || inst.stdOp == OP_JUMPX || isConditionalJump(inst.stdOp) || inst.stdOp == OP_FORNPREP || inst.stdOp == OP_FORNLOOP ||
             inst.stdOp == OP_FORGPREP || inst.stdOp == OP_FORGPREP_NEXT || inst.stdOp == OP_FORGPREP_INEXT || inst.stdOp == OP_FORGLOOP ||
             inst.stdOp == OP_JUMPBACK)) {
            leaders.insert(nextPc);
        }
    }

    std::vector<int> sortedLeaders(leaders.begin(), leaders.end());
    std::sort(sortedLeaders.begin(), sortedLeaders.end());

    for (int i = 0; i < (int)sortedLeaders.size(); ++i) {
        const int startPc = sortedLeaders[i];
        const int endPc = (i + 1 < (int)sortedLeaders.size()) ? sortedLeaders[i + 1] - 1 : numInst - 1;
        BasicBlock block;
        block.id = i;
        block.startPc = startPc;
        block.endPc = endPc;
        cfg.blocks.push_back(block);

        for (int pc = startPc; pc <= endPc && pc < numInst; ++pc) {
            cfg.pcToBlock[pc] = i;
        }
    }

    for (int index = 0; index < (int)instructions.size(); ++index) {
        const auto& inst = instructions[index];
        for (int pc = inst.pc; pc < inst.pc + inst.width && pc < numInst; ++pc) {
            cfg.rawPcToInstruction[pc] = index;
        }
    }

    for (auto& block : cfg.blocks) {
        const int instructionIndex = (block.endPc >= 0 && block.endPc < numInst) ? cfg.rawPcToInstruction[block.endPc] : -1;
        if (instructionIndex < 0) {
            continue;
        }

        const auto& inst = instructions[instructionIndex];
        const int targetPc = inst.jumpTargetPc.value_or(-1);
        const int targetBlock = (targetPc >= 0 && targetPc < numInst) ? cfg.pcToBlock[targetPc] : -1;
        const int nextPc = inst.pc + inst.width;
        const int fallthroughBlock = (nextPc < numInst) ? cfg.pcToBlock[nextPc] : -1;

        if (isTerminal(inst.stdOp)) {
            continue;
        }

        if (inst.stdOp == OP_JUMP || inst.stdOp == OP_JUMPBACK || inst.stdOp == OP_JUMPX) {
            bool isBackEdge = (inst.stdOp == OP_JUMPX) ? (inst.e < 0) : (inst.d < 0);
            addEdge(cfg, block.id, targetBlock, inst.pc, isBackEdge ? CFGEdgeKind::LoopBack : CFGEdgeKind::Jump);
            continue;
        }

        if (isConditionalJump(inst.stdOp)) {
            addEdge(cfg, block.id, targetBlock, inst.pc, CFGEdgeKind::BranchTrue);
            addEdge(cfg, block.id, fallthroughBlock, inst.pc, CFGEdgeKind::BranchFalse);
            continue;
        }

        if (inst.stdOp == OP_FORNPREP || inst.stdOp == OP_FORGPREP || inst.stdOp == OP_FORGPREP_NEXT || inst.stdOp == OP_FORGPREP_INEXT) {
            addEdge(cfg, block.id, targetBlock, inst.pc, CFGEdgeKind::LoopExit);
            addEdge(cfg, block.id, fallthroughBlock, inst.pc, CFGEdgeKind::Fallthrough);
            continue;
        }

        if (inst.stdOp == OP_FORNLOOP || inst.stdOp == OP_FORGLOOP) {
            addEdge(cfg, block.id, targetBlock, inst.pc, CFGEdgeKind::LoopBack);
            addEdge(cfg, block.id, fallthroughBlock, inst.pc, CFGEdgeKind::LoopExit);
            continue;
        }

        addEdge(cfg, block.id, fallthroughBlock, inst.pc, CFGEdgeKind::Fallthrough);
    }

    for (const auto& edge : cfg.edges) {
        if (edge.kind != CFGEdgeKind::BranchTrue) {
            continue;
        }

        const int conditionPc = edge.sourcePc;
        const int ifExitPc = cfg.blocks[edge.toBlock].startPc;
        if (ifExitPc <= 0) {
            continue;
        }

        const int thenEndPc = ifExitPc - 1;
        const int thenEndBlock = (thenEndPc >= 0 && thenEndPc < numInst) ? cfg.pcToBlock[thenEndPc] : -1;
        if (thenEndBlock < 0) {
            continue;
        }

        const int jumpPc = cfg.blocks[thenEndBlock].endPc;
        const auto& jumpInst = function.instructions[jumpPc];
        const int jumpOp = opmap.lookup(jumpInst.opcode());
        if (jumpOp != OP_JUMP || jumpInst.d() <= 0) {
            continue;
        }

        const int elseEndPc = jumpPc + jumpInst.d() + 1;
        if (elseEndPc <= ifExitPc || elseEndPc > numInst) {
            continue;
        }

        cfg.elseByJumpPc[jumpPc] = {conditionPc, jumpPc, ifExitPc, elseEndPc};
    }

    auto dominators = computeDominanceSets(cfg, false);
    auto postDominators = computeDominanceSets(cfg, true);
    cfg.immediateDominator = computeImmediateDominators(cfg, dominators, false);
    cfg.immediatePostDominator = computeImmediateDominators(cfg, postDominators, true);

    return cfg;
}

std::string formatControlFlowGraph(const Chunk& chunk, const OpcodeMap& opmap) {
    std::ostringstream out;
    out << "-- Control Flow Graph Dump\n";
    out << "-- Functions: " << chunk.functions.size() << "\n\n";

    for (const auto& function : chunk.functions) {
        ControlFlowGraph cfg = buildControlFlowGraph(function, opmap);
        FunctionIR ir = decodeFunctionIR(function, opmap);

        out << "Function proto#" << function.id;
        if (!function.debugName.empty()) {
            out << " \"" << function.debugName << "\"";
        }
        if (function.lineDefined > 0) {
            out << " line " << function.lineDefined;
        }
        out << "\n";

        for (const auto& block : cfg.blocks) {
            const int lastIndex = (block.endPc >= 0 && block.endPc < (int)cfg.rawPcToInstruction.size())
                ? cfg.rawPcToInstruction[block.endPc]
                : -1;
            const char* lastOp = (lastIndex >= 0 && lastIndex < (int)ir.size())
                ? ir[lastIndex].opName.c_str()
                : "OTHER";

            out << "  block b" << block.id
                << " [" << block.startPc << ", " << block.endPc << "]"
                << " last=" << lastOp;

            if (cfg.immediateDominator.size() == cfg.blocks.size()) {
                out << " idom=";
                if (cfg.immediateDominator[block.id] >= 0) out << "b" << cfg.immediateDominator[block.id];
                else out << "entry";
            }
            if (cfg.immediatePostDominator.size() == cfg.blocks.size()) {
                out << " ipdom=";
                if (cfg.immediatePostDominator[block.id] >= 0) out << "b" << cfg.immediatePostDominator[block.id];
                else out << "exit";
            }
            out << "\n";

            if (!block.predecessors.empty()) {
                out << "    preds:";
                for (int pred : block.predecessors) {
                    out << " b" << pred;
                }
                out << "\n";
            }

            if (!block.successors.empty()) {
                out << "    succs:";
                for (int succ : block.successors) {
                    out << " b" << succ;
                }
                out << "\n";
            }
        }

        if (!cfg.edges.empty()) {
            out << "  edges:\n";
            for (const auto& edge : cfg.edges) {
                out << "    b" << edge.fromBlock << " -> b" << edge.toBlock
                    << " @pc " << edge.sourcePc
                    << " (" << edgeKindName(edge.kind) << ")\n";
            }
        }

        if (!cfg.elseByJumpPc.empty()) {
            out << "  else_transitions:\n";
            for (const auto& [jumpPc, transition] : cfg.elseByJumpPc) {
                out << "    cond_pc=" << transition.conditionPc
                    << " jump_pc=" << jumpPc
                    << " else_start=" << transition.elseStartPc
                    << " else_end=" << transition.elseEndPc << "\n";
            }
        }

        out << "\n";
    }

    return out.str();
}
