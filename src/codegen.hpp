#pragma once
#include "deserializer.hpp"
#include "automapper.hpp"
#include <string>

// Generate readable Lua pseudo-code from a chunk with mapped opcodes
std::string generateCode(const Chunk& chunk, const OpcodeMap& opmap);
