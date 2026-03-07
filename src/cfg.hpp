#pragma once

#include "deserializer.hpp"
#include "automapper.hpp"
#include "ir.hpp"
#include <string>
#include <unordered_map>
#include <vector>

enum class CFGEdgeKind {
    Fallthrough,
    Jump,
    BranchTrue,
    BranchFalse,
    LoopBack,
    LoopExit
};

struct CFGEdge {
    int fromBlock = -1;
    int toBlock = -1;
    int sourcePc = -1;
    CFGEdgeKind kind = CFGEdgeKind::Fallthrough;
};

struct BasicBlock {
    int id = -1;
    int startPc = -1;
    int endPc = -1;
    std::vector<int> predecessors;
    std::vector<int> successors;
};

struct ElseTransition {
    int conditionPc = -1;
    int jumpPc = -1;
    int elseStartPc = -1;
    int elseEndPc = -1;
};

struct ControlFlowGraph {
    std::vector<BasicBlock> blocks;
    std::vector<int> pcToBlock;
    std::vector<int> rawPcToInstruction;
    std::vector<int> immediateDominator;
    std::vector<int> immediatePostDominator;
    std::vector<CFGEdge> edges;
    std::unordered_map<int, ElseTransition> elseByJumpPc;
};

ControlFlowGraph buildControlFlowGraph(const Function& function, const OpcodeMap& opmap);
std::string formatControlFlowGraph(const Chunk& chunk, const OpcodeMap& opmap);
