#pragma once
#include <cstdint>
#include <string>
#include <vector>
#include <optional>

// ==========================================
// Luau Bytecode Data Structures
// ==========================================

enum class ConstantType : uint8_t {
    Nil     = 0,
    Bool    = 1,
    Number  = 2,
    String  = 3,
    Import  = 4,
    Table   = 5,
    Closure = 6,
    Vector  = 7,
};

struct Constant {
    ConstantType type;
    bool   boolVal  = false;
    double numVal   = 0.0;
    std::string strVal;
    // Import: packed id
    uint32_t importId = 0;
    std::vector<std::string> importNames;
    // Table: key indices
    std::vector<int> tableKeys;
    // Closure: proto index
    int closureIdx   = 0;
    // Vector
    float vecX = 0, vecY = 0, vecZ = 0, vecW = 0;

    std::string toString(const std::vector<std::string>& strings) const;
};

struct RawInstruction {
    uint32_t value;
    uint8_t  opcode()  const { return value & 0xFF; }
    uint8_t  a()       const { return (value >> 8) & 0xFF; }
    uint8_t  b()       const { return (value >> 16) & 0xFF; }
    uint8_t  c()       const { return (value >> 24) & 0xFF; }
    int16_t  d()       const { return (int16_t)(value >> 16); }
    int32_t  e()       const { return (int32_t)value >> 8; }
};

struct LocalVarInfo {
    std::string name;
    int startPc;
    int endPc;
    uint8_t slot;
};

struct Function {
    int id;
    uint8_t maxStackSize;
    uint8_t numParams;
    uint8_t numUpvalues;
    bool    isVararg;
    uint8_t flags;
    int     lineDefined;
    std::string debugName;

    std::vector<RawInstruction> instructions;
    std::vector<Constant> constants;
    std::vector<int> childProtos;
    
    // Debug info
    std::vector<LocalVarInfo> locals;
    std::vector<std::string> upvalueNames;
    
    // Line info
    bool hasLineInfo = false;
    uint8_t lineGapLog = 0;
    std::vector<uint8_t> lineOffsets;
    std::vector<int32_t> absLineInfo;
};

struct Chunk {
    uint8_t version;
    uint8_t typesVersion;
    std::vector<std::string> strings;
    std::vector<Function> functions;
    int mainIndex;
};

// Deserialize raw bytes into a Chunk
Chunk deserialize(const uint8_t* data, size_t size);
