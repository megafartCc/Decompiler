#pragma once

#include "deserializer.hpp"
#include "automapper.hpp"
#include "cfg.hpp"
#include "ir.hpp"
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct SSAVariable {
    int id = -1;
    int slot = -1;
    int version = -1;
    int definingBlock = -1;
    int definingInstruction = -1;
    bool isPhi = false;
    bool isParameter = false;
    bool isUpvalue = false;
    int upvalueIndex = -1;
    int useCount = 0;
    std::string name;
    float nameConfidence = 0.0f;
    std::optional<std::string> constantValue;
};

struct PhiNode {
    int blockId = -1;
    int slot = -1;
    int resultValueId = -1;
    std::unordered_map<int, int> inputs;
    bool dead = false;
};

struct SSAInstruction {
    int index = -1;
    int blockId = -1;
    DecodedInstruction inst;
    std::vector<int> rawUses;
    std::vector<int> rawDefs;
    std::vector<int> rawClobberDefs;
    std::vector<int> uses;
    std::vector<int> defs;
    std::vector<int> clobberDefs;
    bool hasSideEffects = false;
    bool dead = false;
    std::string semanticHint;
    std::optional<std::string> renderedText;
};

struct SSABlock {
    int blockId = -1;
    std::vector<int> instructionRefs;
    std::vector<PhiNode> phis;
    std::unordered_map<int, int> phiIndexBySlot;
};

struct SSAFunction {
    int functionId = -1;
    std::string name;
    FunctionIR ir;
    ControlFlowGraph cfg;
    std::vector<SSABlock> blocks;
    std::vector<SSAInstruction> instructions;
    std::vector<SSAVariable> values;
    std::vector<std::vector<int>> dominatorTree;
    std::vector<std::vector<int>> dominanceFrontier;
    std::unordered_set<int> escapedMutableSlots;
    std::unordered_map<int, int> escapedSlotToCellSlot;
    std::unordered_map<int, int> cellSlotToEscapedSlot;
};

SSAFunction buildSSAFunction(const Chunk& chunk, const Function& function, const OpcodeMap& opmap);
std::string formatSSA(const Chunk& chunk, const OpcodeMap& opmap);
