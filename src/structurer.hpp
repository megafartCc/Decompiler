#pragma once

#include "analysis.hpp"
#include "ast.hpp"

AstFunction structureFunction(const Chunk& chunk, const Function& sourceFunction, const OpcodeMap& opmap,
                             const std::vector<std::string>& upvalueAliases = {});
AstFunction structureMainFunction(const Chunk& chunk, const OpcodeMap& opmap);
std::string formatStructuredSource(const Chunk& chunk, const OpcodeMap& opmap);
std::string formatStructuredAst(const Chunk& chunk, const OpcodeMap& opmap);
