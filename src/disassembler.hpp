#pragma once
#include "deserializer.hpp"
#include "automapper.hpp"
#include <string>


std::string disassemble(const Chunk& chunk, const OpcodeMap* opmap = nullptr);
