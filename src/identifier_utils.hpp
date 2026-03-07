#pragma once

#include <algorithm>
#include <cctype>
#include <string>
#include <string_view>

inline bool isLuaKeyword(std::string_view value) {
    static constexpr std::string_view kKeywords[] = {
        "and", "break", "do", "else", "elseif", "end", "false", "for",
        "function", "if", "in", "local", "nil", "not", "or", "repeat",
        "return", "then", "true", "until", "while",
    };

    return std::find(std::begin(kKeywords), std::end(kKeywords), value) != std::end(kKeywords);
}

inline bool isLuaIdentifier(std::string_view value) {
    if (value.empty()) {
        return false;
    }
    unsigned char first = static_cast<unsigned char>(value.front());
    if (!std::isalpha(first) && first != '_') {
        return false;
    }
    for (char ch : value) {
        unsigned char uch = static_cast<unsigned char>(ch);
        if (!std::isalnum(uch) && ch != '_') {
            return false;
        }
    }
    return !isLuaKeyword(value);
}

inline std::string sanitizeLuaIdentifier(std::string value, const std::string& fallbackPrefix = "v") {
    if (value.empty()) {
        value = fallbackPrefix;
    }
    if (value.empty() || std::isdigit(static_cast<unsigned char>(value.front()))) {
        value = fallbackPrefix + value;
    }
    if (isLuaKeyword(value)) {
        value.push_back('_');
    }
    return value;
}
