#pragma once
#include "deserializer.hpp"
#include "automapper.hpp"
#include <string>

// Disassemble a Chunk into human-readable output
std::string disassemble(const Chunk& chunk, const OpcodeMap* opmap = nullptr);
