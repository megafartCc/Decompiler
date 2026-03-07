#include "ast.hpp"
#include <cctype>
#include <cstring>
#include <optional>
#include <set>
#include <sstream>

namespace {
static std::string indent(int level) {
    return std::string(level * 4, ' ');
}

static bool isRenderableFunctionName(const std::string& name, bool allowQualified) {
    if (name.empty()) {
        return false;
    }

    auto isNameChar = [&](char ch, bool first) {
        if (std::isalnum((unsigned char)ch) || ch == '_') {
            return !first || !std::isdigit((unsigned char)ch);
        }
        if (allowQualified && (ch == '.' || ch == ':')) {
            return !first;
        }
        return false;
    };

    bool segmentStart = true;
    for (char ch : name) {
        if (!isNameChar(ch, segmentStart)) {
            return false;
        }
        segmentStart = (allowQualified && (ch == '.' || ch == ':'));
    }

    return !segmentStart;
}

static std::string trimWhitespace(std::string value) {
    const size_t start = value.find_first_not_of(" \t\r\n");
    if (start == std::string::npos) {
        return "";
    }
    const size_t end = value.find_last_not_of(" \t\r\n");
    return value.substr(start, end - start + 1);
}

static std::string stripOuterParens(std::string value) {
    value = trimWhitespace(std::move(value));
    while (value.size() >= 2 && value.front() == '(' && value.back() == ')') {
        int depth = 0;
        bool wrapsWhole = true;
        for (size_t i = 0; i < value.size(); ++i) {
            char ch = value[i];
            if (ch == '(') {
                ++depth;
            } else if (ch == ')') {
                --depth;
                if (depth == 0 && i + 1 < value.size()) {
                    wrapsWhole = false;
                    break;
                }
            }
        }
        if (!wrapsWhole || depth != 0) {
            break;
        }
        value = trimWhitespace(value.substr(1, value.size() - 2));
    }
    return value;
}

static std::optional<std::string> invertComparisonText(const std::string& value) {
    const std::string inner = stripOuterParens(value);
    struct Comparator {
        const char* op;
        const char* inverted;
    };
    static constexpr Comparator comparators[] = {
        {"<=", ">"},
        {">=", "<"},
        {"==", "~="},
        {"~=", "=="},
        {"<", ">="},
        {">", "<="},
    };

    int depth = 0;
    for (size_t i = 0; i < inner.size(); ++i) {
        char ch = inner[i];
        if (ch == '(') {
            ++depth;
            continue;
        }
        if (ch == ')') {
            --depth;
            continue;
        }
        if (depth != 0) {
            continue;
        }
        for (const auto& comparator : comparators) {
            const size_t opLen = std::strlen(comparator.op);
            if (i + opLen <= inner.size() && inner.compare(i, opLen, comparator.op) == 0) {
                std::string lhs = trimWhitespace(inner.substr(0, i));
                std::string rhs = trimWhitespace(inner.substr(i + opLen));
                if (!lhs.empty() && !rhs.empty()) {
                    return lhs + " " + comparator.inverted + " " + rhs;
                }
            }
        }
    }
    return std::nullopt;
}

static std::string normalizeConditionText(std::string value) {
    std::string trimmed = trimWhitespace(std::move(value));
    if (trimmed.rfind("not ", 0) == 0) {
        std::string inner = trimWhitespace(trimmed.substr(4));
        if (auto inverted = invertComparisonText(inner); inverted.has_value()) {
            return *inverted;
        }
        inner = stripOuterParens(std::move(inner));
        if (inner.rfind("not ", 0) == 0) {
            return normalizeConditionText(inner.substr(4));
        }
    }
    return trimmed;
}

static std::string parenthesizeCondition(const std::string& value) {
    std::string trimmed = normalizeConditionText(value);
    if (trimmed.empty()) {
        return "true";
    }
    if (trimmed.front() == '(' && trimmed.back() == ')') {
        return trimmed;
    }
    return "(" + trimmed + ")";
}

static std::optional<bool> evaluateConstantCondition(const std::string& value) {
    std::string trimmed = trimWhitespace(value);
    while (trimmed.size() >= 2 && trimmed.front() == '(' && trimmed.back() == ')') {
        trimmed = trimWhitespace(trimmed.substr(1, trimmed.size() - 2));
    }

    struct SimpleLiteral {
        enum class Kind { Invalid, Nil, Boolean, Number, String };
        Kind kind = Kind::Invalid;
        bool booleanValue = false;
        double numberValue = 0.0;
        std::string stringValue;
    };

    auto parseLiteral = [&](const std::string& text) -> SimpleLiteral {
        const std::string token = trimWhitespace(text);
        if (token == "nil") {
            return {SimpleLiteral::Kind::Nil, false, 0.0, {}};
        }
        if (token == "true") {
            return {SimpleLiteral::Kind::Boolean, true, 0.0, {}};
        }
        if (token == "false") {
            return {SimpleLiteral::Kind::Boolean, false, 0.0, {}};
        }
        if (token.size() >= 2 && token.front() == '"' && token.back() == '"') {
            return {SimpleLiteral::Kind::String, false, 0.0, token.substr(1, token.size() - 2)};
        }
        try {
            size_t parsed = 0;
            double number = std::stod(token, &parsed);
            if (parsed == token.size()) {
                return {SimpleLiteral::Kind::Number, false, number, {}};
            }
        } catch (...) {
        }
        return {};
    };

    auto evaluateLiteralComparison = [&](const std::string& text) -> std::optional<bool> {
        std::string expr = trimWhitespace(text);
        int depth = 0;
        struct Comparator {
            const char* op;
            int len;
        };
        static constexpr Comparator comparators[] = {
            {"==", 2}, {"~=", 2}, {"<=", 2}, {">=", 2}, {"<", 1}, {">", 1},
        };

        for (size_t i = 0; i < expr.size(); ++i) {
            char ch = expr[i];
            if (ch == '(') {
                ++depth;
                continue;
            }
            if (ch == ')') {
                --depth;
                continue;
            }
            if (depth != 0) {
                continue;
            }

            for (const auto& comparator : comparators) {
                if (i + (size_t)comparator.len > expr.size() ||
                    expr.compare(i, comparator.len, comparator.op) != 0) {
                    continue;
                }

                SimpleLiteral lhs = parseLiteral(expr.substr(0, i));
                SimpleLiteral rhs = parseLiteral(expr.substr(i + comparator.len));
                if (lhs.kind == SimpleLiteral::Kind::Invalid || rhs.kind == SimpleLiteral::Kind::Invalid) {
                    return std::nullopt;
                }

                auto equals = [&]() {
                    if (lhs.kind != rhs.kind) {
                        return false;
                    }
                    switch (lhs.kind) {
                        case SimpleLiteral::Kind::Nil:
                            return true;
                        case SimpleLiteral::Kind::Boolean:
                            return lhs.booleanValue == rhs.booleanValue;
                        case SimpleLiteral::Kind::Number:
                            return lhs.numberValue == rhs.numberValue;
                        case SimpleLiteral::Kind::String:
                            return lhs.stringValue == rhs.stringValue;
                        default:
                            return false;
                    }
                };

                if (std::strcmp(comparator.op, "==") == 0) {
                    return equals();
                }
                if (std::strcmp(comparator.op, "~=") == 0) {
                    return !equals();
                }

                if (lhs.kind != SimpleLiteral::Kind::Number || rhs.kind != SimpleLiteral::Kind::Number) {
                    return std::nullopt;
                }

                if (std::strcmp(comparator.op, "<=") == 0) {
                    return lhs.numberValue <= rhs.numberValue;
                }
                if (std::strcmp(comparator.op, ">=") == 0) {
                    return lhs.numberValue >= rhs.numberValue;
                }
                if (std::strcmp(comparator.op, "<") == 0) {
                    return lhs.numberValue < rhs.numberValue;
                }
                if (std::strcmp(comparator.op, ">") == 0) {
                    return lhs.numberValue > rhs.numberValue;
                }
            }
        }
        return std::nullopt;
    };

    if (auto literalComparison = evaluateLiteralComparison(trimmed); literalComparison.has_value()) {
        return literalComparison;
    }

    if (trimmed == "true") {
        return true;
    }
    if (trimmed == "false") {
        return false;
    }
    if (trimmed.rfind("not ", 0) == 0) {
        if (auto inner = evaluateConstantCondition(trimmed.substr(4)); inner.has_value()) {
            return !*inner;
        }
    }
    return std::nullopt;
}

static bool isBareReturn(const AstStatement& statement) {
    return statement.kind == AstStatementKind::Raw && trimWhitespace(statement.text) == "return";
}

static bool isBareBreak(const AstStatement& statement) {
    return statement.kind == AstStatementKind::Raw && trimWhitespace(statement.text) == "break";
}

static bool isSimpleBreakIf(const AstStatement& statement, std::string& condition) {
    if (statement.kind != AstStatementKind::If || !statement.elseBody.empty() || statement.body.size() != 1 ||
        !isBareBreak(statement.body.front())) {
        return false;
    }
    condition = trimWhitespace(statement.header);
    return !condition.empty();
}

static std::string negateConditionText(const std::string& value) {
    std::string trimmed = trimWhitespace(value);
    if (trimmed.empty()) {
        return "false";
    }
    if (trimmed.rfind("not ", 0) == 0) {
        return trimWhitespace(trimmed.substr(4));
    }
    if (trimmed.front() == '(' && trimmed.back() == ')') {
        return "not " + trimmed;
    }
    if (trimmed.find_first_of(" \t\n") == std::string::npos) {
        return "not " + trimmed;
    }
    return "not (" + trimmed + ")";
}

static bool collapseReturnFromLocal(const AstStatement& current, const AstStatement& next, std::string& replacement) {
    if (current.kind != AstStatementKind::Raw || next.kind != AstStatementKind::Raw) {
        return false;
    }

    const std::string prefix = "local ";
    const std::string assign = " = ";
    if (current.text.rfind(prefix, 0) != 0 || current.text.find('\n') != std::string::npos ||
        next.text.find('\n') != std::string::npos) {
        return false;
    }

    size_t assignPos = current.text.find(assign, prefix.size());
    if (assignPos == std::string::npos) {
        return false;
    }

    std::string varName = current.text.substr(prefix.size(), assignPos - prefix.size());
    if (varName.find(',') != std::string::npos || varName.empty()) {
        return false;
    }

    std::string returnText = "return " + varName;
    if (next.text != returnText) {
        return false;
    }

    replacement = "return " + current.text.substr(assignPos + assign.size());
    return true;
}

static bool isLuaIdentifierText(const std::string& value) {
    if (value.empty()) {
        return false;
    }
    if (!(std::isalpha((unsigned char)value[0]) || value[0] == '_')) {
        return false;
    }
    for (size_t i = 1; i < value.size(); ++i) {
        char ch = value[i];
        if (!(std::isalnum((unsigned char)ch) || ch == '_')) {
            return false;
        }
    }
    return true;
}

static bool parseSimpleLocalAssignment(const AstStatement& statement, std::string& varName, std::string& expr) {
    if (statement.kind != AstStatementKind::Raw) {
        return false;
    }

    const std::string text = trimWhitespace(statement.text);
    const std::string prefix = "local ";
    const std::string assign = " = ";
    if (text.rfind(prefix, 0) != 0 || text.find('\n') != std::string::npos) {
        return false;
    }

    size_t assignPos = text.find(assign, prefix.size());
    if (assignPos == std::string::npos) {
        return false;
    }

    varName = trimWhitespace(text.substr(prefix.size(), assignPos - prefix.size()));
    expr = trimWhitespace(text.substr(assignPos + assign.size()));
    if (!isLuaIdentifierText(varName) || varName.find(',') != std::string::npos || expr.empty()) {
        return false;
    }

    return true;
}

static bool isIdentifierBoundary(char ch) {
    return !(std::isalnum((unsigned char)ch) || ch == '_');
}

static bool isNumericLiteralText(const std::string& value) {
    std::string trimmed = trimWhitespace(value);
    if (trimmed.empty()) {
        return false;
    }
    try {
        size_t parsed = 0;
        const double parsedValue = std::stod(trimmed, &parsed);
        (void)parsedValue;
        return parsed == trimmed.size();
    } catch (...) {
        return false;
    }
}

static std::string inlineReplacementExpr(const std::string& expr) {
    std::string trimmed = trimWhitespace(expr);
    if (trimmed.empty()) {
        return trimmed;
    }
    if (isLuaIdentifierText(trimmed) || trimmed == "nil" || trimmed == "true" || trimmed == "false" ||
        isNumericLiteralText(trimmed)) {
        return trimmed;
    }
    return "(" + trimmed + ")";
}

static int countIdentifierOccurrences(const std::string& text, const std::string& identifier) {
    if (identifier.empty() || text.empty()) {
        return 0;
    }

    int count = 0;
    size_t pos = 0;
    while ((pos = text.find(identifier, pos)) != std::string::npos) {
        bool leftBoundary = pos == 0 || isIdentifierBoundary(text[pos - 1]);
        bool rightBoundary = (pos + identifier.size() >= text.size()) || isIdentifierBoundary(text[pos + identifier.size()]);
        if (leftBoundary && rightBoundary) {
            ++count;
        }
        pos += identifier.size();
    }
    return count;
}

static bool replaceIdentifierOnce(std::string& text, const std::string& identifier, const std::string& replacement) {
    if (text.empty() || identifier.empty()) {
        return false;
    }

    size_t pos = 0;
    while ((pos = text.find(identifier, pos)) != std::string::npos) {
        bool leftBoundary = pos == 0 || isIdentifierBoundary(text[pos - 1]);
        bool rightBoundary = (pos + identifier.size() >= text.size()) || isIdentifierBoundary(text[pos + identifier.size()]);
        if (leftBoundary && rightBoundary) {
            text.replace(pos, identifier.size(), replacement);
            return true;
        }
        pos += identifier.size();
    }
    return false;
}

static bool replaceSingleUseIdentifierInStatement(AstStatement& statement, const std::string& identifier,
                                                  const std::string& replacement) {
    if (replaceIdentifierOnce(statement.text, identifier, replacement)) {
        return true;
    }
    if (replaceIdentifierOnce(statement.header, identifier, replacement)) {
        return true;
    }
    if (replaceIdentifierOnce(statement.footer, identifier, replacement)) {
        return true;
    }
    for (auto& child : statement.body) {
        if (replaceSingleUseIdentifierInStatement(child, identifier, replacement)) {
            return true;
        }
    }
    for (auto& child : statement.elseBody) {
        if (replaceSingleUseIdentifierInStatement(child, identifier, replacement)) {
            return true;
        }
    }
    return false;
}

static bool isNoOpSelfAssignmentText(const std::string& text) {
    std::string trimmed = trimWhitespace(text);
    if (trimmed.empty() || trimmed.find('\n') != std::string::npos) {
        return false;
    }

    bool isLocal = false;
    if (trimmed.rfind("local ", 0) == 0) {
        isLocal = true;
        trimmed = trimWhitespace(trimmed.substr(6));
    }

    size_t assignPos = trimmed.find('=');
    if (assignPos == std::string::npos || trimmed.find('=', assignPos + 1) != std::string::npos) {
        return false;
    }

    std::string lhs = trimWhitespace(trimmed.substr(0, assignPos));
    std::string rhs = trimWhitespace(trimmed.substr(assignPos + 1));
    if (!isLuaIdentifierText(lhs) || !isLuaIdentifierText(rhs)) {
        return false;
    }
    if (lhs != rhs) {
        return false;
    }

    // Keep global-script aliasing in function prologs if it was explicit source shape.
    if (isLocal && lhs == "script") {
        return true;
    }

    return true;
}

static int countIdentifierUsesInStatement(const AstStatement& statement, const std::string& identifier) {
    int uses = countIdentifierOccurrences(statement.text, identifier);
    uses += countIdentifierOccurrences(statement.header, identifier);
    uses += countIdentifierOccurrences(statement.footer, identifier);
    for (const auto& child : statement.body) {
        uses += countIdentifierUsesInStatement(child, identifier);
    }
    for (const auto& child : statement.elseBody) {
        uses += countIdentifierUsesInStatement(child, identifier);
    }
    return uses;
}

static int countIdentifierUsesInTail(const std::vector<AstStatement>& statements, size_t fromIndex, const std::string& identifier) {
    int uses = 0;
    for (size_t i = fromIndex; i < statements.size(); ++i) {
        uses += countIdentifierUsesInStatement(statements[i], identifier);
    }
    return uses;
}

static bool isSideEffectFreeInlineExpression(const std::string& expr) {
    std::string trimmed = trimWhitespace(expr);
    if (trimmed.empty()) {
        return false;
    }

    trimmed = stripOuterParens(trimmed);

    if (trimmed.find("function") != std::string::npos ||
        trimmed.find(':') != std::string::npos ||
        trimmed.find('=') != std::string::npos ||
        trimmed.find("...") != std::string::npos ||
        trimmed.find('\n') != std::string::npos ||
        trimmed.find('\r') != std::string::npos) {
        return false;
    }

    // Keep this conservative: call-like expressions need deeper parsing.
    if (trimmed.find('(') != std::string::npos || trimmed.find(')') != std::string::npos) {
        return false;
    }

    return true;
}

static std::vector<std::string> splitCommaSeparated(const std::string& value) {
    std::vector<std::string> parts;
    std::string current;
    int depth = 0;
    for (char ch : value) {
        if (ch == '(' || ch == '[' || ch == '{') {
            ++depth;
        } else if (ch == ')' || ch == ']' || ch == '}') {
            --depth;
        }

        if (ch == ',' && depth == 0) {
            parts.push_back(trimWhitespace(current));
            current.clear();
            continue;
        }
        current.push_back(ch);
    }
    parts.push_back(trimWhitespace(current));
    return parts;
}

static bool isDottedIdentifierPath(const std::string& value) {
    if (value.empty()) {
        return false;
    }

    size_t start = 0;
    while (start < value.size()) {
        size_t dot = value.find('.', start);
        std::string segment = dot == std::string::npos
            ? value.substr(start)
            : value.substr(start, dot - start);
        segment = trimWhitespace(segment);
        if (!isLuaIdentifierText(segment)) {
            return false;
        }
        if (dot == std::string::npos) {
            break;
        }
        start = dot + 1;
    }

    return true;
}

static std::optional<std::string> normalizeMethodCallExpression(const std::string& expression) {
    std::string expr = trimWhitespace(expression);
    if (expr.empty() || expr.find(':') != std::string::npos) {
        return std::nullopt;
    }

    int depth = 0;
    size_t openPos = std::string::npos;
    for (size_t i = 0; i < expr.size(); ++i) {
        char ch = expr[i];
        if (ch == '(') {
            if (depth == 0 && openPos == std::string::npos) {
                openPos = i;
            }
            ++depth;
        } else if (ch == ')') {
            --depth;
            if (depth < 0) {
                return std::nullopt;
            }
            if (depth == 0 && i + 1 != expr.size()) {
                return std::nullopt;
            }
        }
    }

    if (openPos == std::string::npos || depth != 0 || expr.back() != ')') {
        return std::nullopt;
    }

    std::string callee = trimWhitespace(expr.substr(0, openPos));
    std::string args = trimWhitespace(expr.substr(openPos + 1, expr.size() - openPos - 2));
    size_t dot = callee.rfind('.');
    if (dot == std::string::npos) {
        return std::nullopt;
    }

    std::string objectExpr = trimWhitespace(callee.substr(0, dot));
    std::string methodName = trimWhitespace(callee.substr(dot + 1));
    if (!isDottedIdentifierPath(objectExpr) || !isLuaIdentifierText(methodName)) {
        return std::nullopt;
    }

    std::string normalizedArgs;
    if (args == objectExpr) {
        normalizedArgs.clear();
    } else {
        std::string prefix = objectExpr + ",";
        if (args.rfind(prefix, 0) != 0) {
            return std::nullopt;
        }
        normalizedArgs = trimWhitespace(args.substr(prefix.size()));
    }

    return objectExpr + ":" + methodName + "(" + normalizedArgs + ")";
}

static std::string normalizeMethodCallsInRawText(const std::string& text) {
    std::string trimmed = trimWhitespace(text);
    if (trimmed.empty() || trimmed.find('\n') != std::string::npos || trimmed.find('\r') != std::string::npos) {
        return text;
    }

    auto rewriteExpr = [&](const std::string& prefix, const std::string& expr) -> std::string {
        if (auto normalized = normalizeMethodCallExpression(expr); normalized.has_value()) {
            return prefix + *normalized;
        }
        return text;
    };

    if (trimmed.rfind("return ", 0) == 0) {
        return rewriteExpr("return ", trimmed.substr(7));
    }

    if (trimmed.rfind("local ", 0) == 0) {
        size_t assignPos = trimmed.find(" = ");
        if (assignPos != std::string::npos) {
            std::string lhs = trimWhitespace(trimmed.substr(0, assignPos + 3));
            std::string rhs = trimWhitespace(trimmed.substr(assignPos + 3));
            return rewriteExpr(lhs, rhs);
        }
    }

    size_t assignPos = trimmed.find(" = ");
    if (assignPos != std::string::npos && trimmed.find("==") == std::string::npos && trimmed.find("~=") == std::string::npos &&
        trimmed.find("<=") == std::string::npos && trimmed.find(">=") == std::string::npos) {
        std::string lhs = trimWhitespace(trimmed.substr(0, assignPos + 3));
        std::string rhs = trimWhitespace(trimmed.substr(assignPos + 3));
        return rewriteExpr(lhs, rhs);
    }

    if (auto normalized = normalizeMethodCallExpression(trimmed); normalized.has_value()) {
        return *normalized;
    }

    return text;
}

static bool parseEmptyTableDeclaration(const AstStatement& statement, std::string& tableName) {
    if (statement.kind != AstStatementKind::Raw) {
        return false;
    }
    std::string text = trimWhitespace(statement.text);
    if (text.find('\n') != std::string::npos || text.find('\r') != std::string::npos) {
        return false;
    }
    if (text.rfind("local ", 0) != 0 || text.size() < 11) {
        return false;
    }
    size_t assignPos = text.find(" = ");
    if (assignPos == std::string::npos) {
        return false;
    }
    std::string lhs = trimWhitespace(text.substr(6, assignPos - 6));
    std::string rhs = trimWhitespace(text.substr(assignPos + 3));
    if (rhs != "{}" || !isLuaIdentifierText(lhs)) {
        return false;
    }
    tableName = lhs;
    return true;
}

static bool parseNamedTableFieldAssignment(const AstStatement& statement, const std::string& tableName,
                                           std::string& key, std::string& expr) {
    if (statement.kind != AstStatementKind::Raw) {
        return false;
    }
    std::string text = trimWhitespace(statement.text);
    if (text.find('\n') != std::string::npos || text.find('\r') != std::string::npos) {
        return false;
    }
    std::string prefix = tableName + ".";
    if (text.rfind(prefix, 0) != 0) {
        return false;
    }
    size_t assignPos = text.find(" = ");
    if (assignPos == std::string::npos || assignPos <= prefix.size()) {
        return false;
    }
    key = trimWhitespace(text.substr(prefix.size(), assignPos - prefix.size()));
    expr = trimWhitespace(text.substr(assignPos + 3));
    if (!isLuaIdentifierText(key) || expr.empty()) {
        return false;
    }
    return true;
}

static void normalizeInlineTableLiterals(std::vector<AstStatement>& statements) {
    for (size_t i = 0; i < statements.size(); ++i) {
        std::string tableName;
        if (!parseEmptyTableDeclaration(statements[i], tableName)) {
            continue;
        }

        std::vector<std::pair<std::string, std::string>> entries;
        std::set<std::string> seenKeys;
        size_t j = i + 1;
        for (; j < statements.size(); ++j) {
            std::string key;
            std::string expr;
            if (!parseNamedTableFieldAssignment(statements[j], tableName, key, expr)) {
                break;
            }
            if (countIdentifierOccurrences(expr, tableName) > 0) {
                entries.clear();
                break;
            }
            if (!seenKeys.insert(key).second) {
                break;
            }
            entries.push_back({key, expr});
        }

        if (entries.empty()) {
            continue;
        }

        std::ostringstream folded;
        folded << "local " << tableName << " = {\n";
        for (size_t idx = 0; idx < entries.size(); ++idx) {
            folded << "    " << entries[idx].first << " = " << entries[idx].second;
            if (idx + 1 < entries.size()) {
                folded << ",";
            }
            folded << "\n";
        }
        folded << "}";

        statements[i].text = folded.str();
        statements.erase(statements.begin() + (long long)i + 1, statements.begin() + (long long)j);
    }
}

static void normalizeRawStatementText(AstStatement& statement) {
    if (statement.kind == AstStatementKind::Raw) {
        statement.text = normalizeMethodCallsInRawText(statement.text);
    }
    for (auto& child : statement.body) {
        normalizeRawStatementText(child);
    }
    for (auto& child : statement.elseBody) {
        normalizeRawStatementText(child);
    }
}

static void normalizeStatementLists(AstStatement& statement) {
    auto normalizeList = [&](std::vector<AstStatement>& list) {
        for (auto& child : list) {
            normalizeStatementLists(child);
        }
        normalizeInlineTableLiterals(list);
        for (auto& child : list) {
            normalizeRawStatementText(child);
        }
    };

    normalizeList(statement.body);
    normalizeList(statement.elseBody);
}

static void rewriteLoopHeaderUnusedVars(AstStatement& statement) {
    if (statement.kind != AstStatementKind::Loop || statement.header.empty()) {
        return;
    }

    std::string header = trimWhitespace(statement.header);
    if (header.rfind("for ", 0) != 0 || header.size() < 8 || header.substr(header.size() - 3) != " do") {
        return;
    }

    const size_t bodyStart = 4;
    const size_t bodyEnd = header.size() - 3;
    std::string body = trimWhitespace(header.substr(bodyStart, bodyEnd - bodyStart));
    size_t inPos = body.find(" in ");
    if (inPos == std::string::npos) {
        return;
    }

    std::string varList = trimWhitespace(body.substr(0, inPos));
    std::string iteratorExpr = trimWhitespace(body.substr(inPos + 4));
    if (varList.empty() || iteratorExpr.empty() || varList.find('=') != std::string::npos) {
        // Numeric loops are kept as-is.
        return;
    }

    std::vector<std::string> vars = splitCommaSeparated(varList);
    if (vars.empty()) {
        return;
    }

    bool changed = false;
    for (auto& var : vars) {
        if (var.empty() || var == "_" || !isLuaIdentifierText(var)) {
            continue;
        }
        int uses = 0;
        for (const auto& child : statement.body) {
            uses += countIdentifierUsesInStatement(child, var);
        }
        if (uses == 0) {
            var = "_";
            changed = true;
        }
    }

    if (!changed) {
        return;
    }

    while (vars.size() > 1 && vars.back() == "_") {
        vars.pop_back();
    }

    std::ostringstream rebuiltVars;
    for (size_t i = 0; i < vars.size(); ++i) {
        if (i) {
            rebuiltVars << ", ";
        }
        rebuiltVars << vars[i];
    }

    statement.header = "for " + rebuiltVars.str() + " in " + iteratorExpr + " do";
}

static bool inlineIfConditionFromLocal(AstStatement& ifStatement, const std::string& varName, const std::string& expr) {
    if (ifStatement.kind != AstStatementKind::If) {
        return false;
    }

    std::string header = trimWhitespace(ifStatement.header);
    if (header == varName || stripOuterParens(header) == varName) {
        ifStatement.header = expr;
        return true;
    }
    if (header == "not " + varName || stripOuterParens(header) == "not " + varName) {
        ifStatement.header = "not (" + expr + ")";
        return true;
    }

    return false;
}

static void inlineSingleUseTemps(std::vector<AstStatement>& statements) {
    if (statements.size() < 2) {
        return;
    }

    size_t i = 0;
    while (i + 1 < statements.size()) {
        std::string varName;
        std::string expr;
        if (!parseSimpleLocalAssignment(statements[i], varName, expr) || !isSideEffectFreeInlineExpression(expr)) {
            ++i;
            continue;
        }

        if (countIdentifierUsesInTail(statements, i + 1, varName) != 1) {
            ++i;
            continue;
        }

        bool inlined = inlineIfConditionFromLocal(statements[i + 1], varName, expr);
        if (!inlined) {
            const std::string replacement = inlineReplacementExpr(expr);
            for (size_t j = i + 1; j < statements.size() && !inlined; ++j) {
                inlined = replaceSingleUseIdentifierInStatement(statements[j], varName, replacement);
            }
        }

        if (!inlined) {
            ++i;
            continue;
        }

        statements.erase(statements.begin() + i);
    }
}

static AstStatement simplifyStatement(AstStatement statement);

static std::vector<AstStatement> simplifyStatements(std::vector<AstStatement> statements, bool trimTrailingBareReturn) {
    std::vector<AstStatement> simplified;
    simplified.reserve(statements.size());

    for (auto& statement : statements) {
        AstStatement current = simplifyStatement(std::move(statement));
        if (current.kind == AstStatementKind::Raw && trimWhitespace(current.text).empty()) {
            continue;
        }
        if (current.kind == AstStatementKind::Block) {
            for (auto& child : current.body) {
                simplified.push_back(std::move(child));
            }
            continue;
        }
        simplified.push_back(std::move(current));
    }

    inlineSingleUseTemps(simplified);

    if (trimTrailingBareReturn) {
        while (!simplified.empty() && isBareReturn(simplified.back())) {
            simplified.pop_back();
        }
    }

    return simplified;
}

static AstStatement simplifyStatement(AstStatement statement) {
    switch (statement.kind) {
        case AstStatementKind::Block:
            statement.body = simplifyStatements(std::move(statement.body), false);
            break;
        case AstStatementKind::If:
            statement.header = normalizeConditionText(std::move(statement.header));
            statement.body = simplifyStatements(std::move(statement.body), false);
            statement.elseBody = simplifyStatements(std::move(statement.elseBody), false);

            if (statement.body.empty() && statement.elseBody.empty()) {
                AstStatement empty;
                empty.kind = AstStatementKind::Raw;
                empty.text.clear();
                return empty;
            }

            if (statement.body.empty() && !statement.elseBody.empty()) {
                statement.header = normalizeConditionText(negateConditionText(statement.header));
                statement.body = std::move(statement.elseBody);
                statement.elseBody.clear();
            }

            if (!statement.elseBody.empty()) {
                std::string header = trimWhitespace(statement.header);
                if (header.rfind("not ", 0) == 0) {
                    statement.header = normalizeConditionText(header.substr(4));
                    std::swap(statement.body, statement.elseBody);
                }
            }

            while (statement.elseBody.empty() &&
                   statement.body.size() == 1 &&
                   statement.body.front().kind == AstStatementKind::If &&
                   statement.body.front().elseBody.empty()) {
                AstStatement child = std::move(statement.body.front());
                statement.header = parenthesizeCondition(statement.header) + " and " + parenthesizeCondition(child.header);
                statement.body = std::move(child.body);
            }

            if (auto constant = evaluateConstantCondition(statement.header); constant.has_value()) {
                AstStatement collapsed;
                collapsed.kind = AstStatementKind::Block;
                collapsed.body = *constant ? std::move(statement.body) : std::move(statement.elseBody);
                return collapsed;
            }
            break;
        case AstStatementKind::Loop:
            if (statement.header.rfind("while ", 0) == 0 && statement.header.size() > 9 &&
                statement.header.substr(statement.header.size() - 3) == " do") {
                std::string condition = statement.header.substr(6, statement.header.size() - 9);
                statement.header = "while " + normalizeConditionText(std::move(condition)) + " do";
            }
            if (statement.footer.rfind("until ", 0) == 0) {
                statement.footer = "until " + normalizeConditionText(statement.footer.substr(6));
            }
            statement.body = simplifyStatements(std::move(statement.body), false);
            if (statement.header == "while true do" && statement.footer.empty() && !statement.body.empty()) {
                std::string condition;
                if (isSimpleBreakIf(statement.body.front(), condition)) {
                    statement.header = "while " + negateConditionText(condition) + " do";
                    statement.body.erase(statement.body.begin());
                } else if (isSimpleBreakIf(statement.body.back(), condition)) {
                    statement.header = "repeat";
                    statement.footer = "until " + condition;
                    statement.body.pop_back();
                }
            }
            rewriteLoopHeaderUnusedVars(statement);
            break;
        case AstStatementKind::Raw:
            statement.text = trimWhitespace(statement.text);
            if (isNoOpSelfAssignmentText(statement.text)) {
                statement.text.clear();
            }
            break;
    }

    return statement;
}

static AstFunction beautifyFunction(AstFunction function) {
    function.body = simplifyStatement(std::move(function.body));
    if (function.body.kind == AstStatementKind::Block) {
        function.body.body = simplifyStatements(std::move(function.body.body), true);
    }
    normalizeStatementLists(function.body);
    normalizeRawStatementText(function.body);
    return function;
}

static void renderIfStatement(std::ostringstream& out, const AstStatement& statement, int level);

static void renderStatement(std::ostringstream& out, const AstStatement& statement, int level) {
    const std::string ind = indent(level);
    auto renderRaw = [&](const std::string& text) {
        if (text.empty()) {
            return;
        }

        size_t start = 0;
        while (start <= text.size()) {
            size_t end = text.find('\n', start);
            std::string line = end == std::string::npos ? text.substr(start) : text.substr(start, end - start);
            if (!line.empty()) {
                out << ind << line << "\n";
            } else {
                out << "\n";
            }
            if (end == std::string::npos) {
                break;
            }
            start = end + 1;
        }
    };

    switch (statement.kind) {
        case AstStatementKind::Block:
            for (size_t i = 0; i < statement.body.size(); ++i) {
                std::string replacement;
                if (i + 1 < statement.body.size() && collapseReturnFromLocal(statement.body[i], statement.body[i + 1], replacement)) {
                    AstStatement folded;
                    folded.kind = AstStatementKind::Raw;
                    folded.text = replacement;
                    renderStatement(out, folded, level);
                    ++i;
                    continue;
                }
                renderStatement(out, statement.body[i], level);
            }
            break;
        case AstStatementKind::Raw:
            renderRaw(statement.text);
            break;
        case AstStatementKind::If:
            renderIfStatement(out, statement, level);
            break;
        case AstStatementKind::Loop:
            out << ind << statement.header << "\n";
            for (const auto& child : statement.body) {
                renderStatement(out, child, level + 1);
            }
            if (!statement.footer.empty()) {
                out << ind << statement.footer << "\n";
            } else {
                out << ind << "end\n";
            }
            break;
    }
}

static void renderIfStatement(std::ostringstream& out, const AstStatement& statement, int level) {
    const std::string ind = indent(level);
    out << ind << "if " << statement.header << " then\n";
    for (const auto& child : statement.body) {
        renderStatement(out, child, level + 1);
    }

    const AstStatement* currentElseIf = nullptr;
    const std::vector<AstStatement>* elseTail = &statement.elseBody;
    while (elseTail->size() == 1 && elseTail->front().kind == AstStatementKind::If) {
        currentElseIf = &elseTail->front();
        out << ind << "elseif " << currentElseIf->header << " then\n";
        for (const auto& child : currentElseIf->body) {
            renderStatement(out, child, level + 1);
        }
        elseTail = &currentElseIf->elseBody;
    }

    if (!elseTail->empty()) {
        out << ind << "else\n";
        for (const auto& child : *elseTail) {
            renderStatement(out, child, level + 1);
        }
    }

    out << ind << "end\n";
}
} // namespace

static void renderFunction(std::ostringstream& out, const AstFunction& function, bool anonymous,
                           const std::string& explicitName, int baseIndentLevel) {
    const std::string ind = indent(baseIndentLevel);
    out << ind << "function";
    if (!anonymous) {
        const std::string& candidateName = explicitName.empty() ? function.name : explicitName;
        out << " " << (isRenderableFunctionName(candidateName, !explicitName.empty()) ? candidateName : "proto_unknown");
    }
    out << "(";
    for (size_t i = 0; i < function.params.size(); ++i) {
        if (i) out << ", ";
        out << function.params[i];
    }
    out << ")\n";
    renderStatement(out, function.body, baseIndentLevel + 1);
    out << ind << "end\n";
}

std::string formatAstFunction(const AstFunction& function) {
    std::ostringstream out;
    AstFunction beautified = beautifyFunction(function);
    renderFunction(out, beautified, false, "", 0);
    return out.str();
}

std::string formatAstChunk(const AstFunction& function) {
    std::ostringstream out;
    AstFunction beautified = beautifyFunction(function);
    renderStatement(out, beautified.body, 0);
    return out.str();
}

std::string formatAnonymousAstFunction(const AstFunction& function, int baseIndentLevel) {
    std::ostringstream out;
    AstFunction beautified = beautifyFunction(function);
    renderFunction(out, beautified, true, "", baseIndentLevel);
    return out.str();
}

std::string formatNamedAstFunction(const AstFunction& function, const std::string& qualifiedName, int baseIndentLevel) {
    std::ostringstream out;
    AstFunction beautified = beautifyFunction(function);
    renderFunction(out, beautified, false, qualifiedName, baseIndentLevel);
    return out.str();
}
