#pragma once
#include "deserializer.hpp"
#include "automapper.hpp"
#include <string>


std::string generateCode(const Chunk& chunk, const OpcodeMap& opmap);
