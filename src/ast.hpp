#pragma once

#include <string>
#include <vector>

enum class AstStatementKind {
    Block,
    Raw,
    If,
    Loop
};

struct AstStatement {
    AstStatementKind kind = AstStatementKind::Raw;
    std::string text;
    std::string header;
    std::string footer;
    std::vector<AstStatement> body;
    std::vector<AstStatement> elseBody;
};

struct AstFunction {
    std::string name;
    std::vector<std::string> params;
    AstStatement body;
};

std::string formatAstFunction(const AstFunction& function);
std::string formatAstChunk(const AstFunction& function);
std::string formatAnonymousAstFunction(const AstFunction& function, int baseIndentLevel = 0);
std::string formatNamedAstFunction(const AstFunction& function, const std::string& qualifiedName,
                                   int baseIndentLevel = 0);
