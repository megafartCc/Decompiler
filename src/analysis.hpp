#pragma once

#include "ssa.hpp"
#include <string>
#include <vector>

void inferNames(SSAFunction& function, const Function& sourceFunction, const std::vector<std::string>& upvalueAliases = {});
void detectSemanticPatterns(SSAFunction& function);
void propagateConstants(SSAFunction& function, const Function& sourceFunction);
void eliminateDeadCode(SSAFunction& function);
SSAFunction analyzeFunction(const Chunk& chunk, const Function& function, const OpcodeMap& opmap,
                           const std::vector<std::string>& upvalueAliases = {});
std::string formatAnalyzedSSA(const Chunk& chunk, const OpcodeMap& opmap);
