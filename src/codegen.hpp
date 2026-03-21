#pragma once
#include "deserializer.hpp"
#include "automapper.hpp"
#include <string>

// Generate readable Lua pseudo-code from a chunk with mapped opcodes
std::string generateCode(const Chunk& chunk, const OpcodeMap& opmap);

// Generate legacy pseudo-code for a single function.
std::string generateFunctionCode(const Chunk& chunk, const OpcodeMap& opmap, const Function& function);

// Generate only the legacy pseudo-code body (without surrounding function ... end).
std::string generateFunctionBodyCode(const Chunk& chunk, const OpcodeMap& opmap, const Function& function);
