#pragma once

#include "deserializer.hpp"
#include "automapper.hpp"
#include <optional>
#include <string>
#include <vector>

struct DecodedInstruction {
    int pc = 0;
    int width = 1;
    int stdOp = OP_UNKNOWN;
    std::string opName;
    uint8_t a = 0;
    uint8_t b = 0;
    uint8_t c = 0;
    int16_t d = 0;
    int32_t e = 0;
    bool hasAux = false;
    uint32_t aux = 0;
    std::optional<int> jumpTargetPc;
    std::optional<std::string> keyName;
    std::optional<std::string> importName;
    std::optional<std::string> constantValue;
    bool fallthroughOnMatch = false;
};

using FunctionIR = std::vector<DecodedInstruction>;

FunctionIR decodeFunctionIR(const Function& function, const OpcodeMap& opmap);
std::string formatInstructionIR(const Chunk& chunk, const OpcodeMap& opmap);
