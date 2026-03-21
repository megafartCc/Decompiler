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
    std::string fallback = fallbackPrefix.empty() ? "v" : fallbackPrefix;
    std::string cleanedFallback;
    cleanedFallback.reserve(fallback.size() + 1);
    for (char ch : fallback) {
        unsigned char uch = static_cast<unsigned char>(ch);
        cleanedFallback.push_back((std::isalnum(uch) || ch == '_') ? ch : '_');
    }
    if (cleanedFallback.empty()) {
        cleanedFallback = "v";
    }
    if (std::isdigit(static_cast<unsigned char>(cleanedFallback.front()))) {
        cleanedFallback.insert(cleanedFallback.begin(), 'v');
    }

    if (value.empty()) {
        value = cleanedFallback;
    }

    std::string sanitized;
    sanitized.reserve(value.size() + 4);
    for (char ch : value) {
        unsigned char uch = static_cast<unsigned char>(ch);
        if (std::isalnum(uch) || ch == '_') {
            sanitized.push_back(ch);
        } else if (sanitized.empty() || sanitized.back() != '_') {
            sanitized.push_back('_');
        }
    }

    if (sanitized.empty()) {
        sanitized = cleanedFallback;
    }
    if (std::isdigit(static_cast<unsigned char>(sanitized.front()))) {
        sanitized = cleanedFallback + "_" + sanitized;
    }
    if (isLuaKeyword(sanitized)) {
        sanitized.push_back('_');
    }
    return sanitized;
}
