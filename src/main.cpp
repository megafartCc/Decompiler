#include "deserializer.hpp"
#include "disassembler.hpp"
#include "automapper.hpp"
#include "cfg.hpp"
#include "ir.hpp"
#include "analysis.hpp"
#include "structurer.hpp"
#include "codegen.hpp"
#include <fstream>
#include <iostream>
#include <optional>
#include <regex>
#include <vector>
#include <cstring>

static std::vector<uint8_t> readFile(const char* path) {
    std::ifstream f(path, std::ios::binary | std::ios::ate);
    if (!f) throw std::runtime_error(std::string("Cannot open file: ") + path);
    auto size = f.tellg();
    f.seekg(0, std::ios::beg);
    std::vector<uint8_t> buf(size);
    f.read((char*)buf.data(), size);
    return buf;
}

static void stripHeader(std::vector<uint8_t>& data) {
    // FINALDUMPer prepends "-- Script: ..." text to bytecode files
    // Detect and strip: look for first byte after a newline that could be a version
    if (data.size() > 4 && data[0] == '-' && data[1] == '-') {
        for (size_t i = 0; i < data.size() - 1; i++) {
            if (data[i] == '\n') {
                fprintf(stderr, "[*] Stripping %zu-byte text header from bytecode\n", i + 1);
                data.erase(data.begin(), data.begin() + i + 1);
                return;
            }
        }
    }
}

static bool hasStructuredLowLevelArtifacts(const std::string& text) {
    static const std::vector<std::regex> kPatterns = {
        std::regex(R"(-- [A-Z][A-Z0-9_]* @pc [0-9]+)"),
        std::regex(R"(-- \?\?\? @pc [0-9]+)"),
        std::regex(R"(\bSETUPVAL\b)"),
    };

    for (const auto& pattern : kPatterns) {
        if (std::regex_search(text, pattern)) {
            return true;
        }
    }
    return false;
}

static std::optional<std::string> findStructuredSemanticDefect(const std::string& text) {
    struct SemanticPattern {
        std::regex pattern;
        const char* reason;
    };

    static const std::vector<SemanticPattern> kPatterns = {
        {std::regex(R"(\bif\s+[^\n]+\s+then\s*\n\s*end\b)"), "empty if branch (if ... then end)"},
        {std::regex(R"(\btable\.insert\s*\(\s*\))"), "empty table.insert() call"},
        {std::regex(R"((^|\n)[ \t]*local[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*=[ \t]*\2[ \t]*(\n|$))"), "no-op local self-assignment"},
    };

    for (const auto& entry : kPatterns) {
        if (std::regex_search(text, entry.pattern)) {
            return std::string(entry.reason);
        }
    }
    return std::nullopt;
}

static bool hasUnresolvedRegisterLikeReturn(const std::string& text) {
    static const std::regex kPattern(R"((^|\n)[ \t]*return[ \t]+v[0-9]+(?:_[0-9]+)?[ \t]*(\n|$))");
    return std::regex_search(text, kPattern);
}

static bool canProceedStrictStructuredWithLowConfidence(const OpcodeMap& opmap) {
    // Conservative acceptance for small scripts where confidence can be under-calibrated:
    // require complete map coverage and zero hard decode anomalies.
    return opmap.totalMapped >= OP_COUNT &&
           opmap.unknownOps == 0 &&
           opmap.invalidAux == 0 &&
           opmap.invalidJumpTargets == 0 &&
           opmap.sampledFunctions > 0;
}

int main(int argc, char* argv[]) {
    bool rawMode = false;
    bool cfgMode = false;
    bool irMode = false;
    bool ssaMode = false;
    bool astMode = false;
    bool legacyMode = false;
    bool strictStructuredMode = false;
    const char* inputPath = nullptr;
    const char* outputPath = nullptr;

    auto printUsage = []() {
        fprintf(stderr, "Luau Decompiler v2.3.0\n");
        fprintf(stderr, "Usage: luau_decompiler [--raw|--cfg|--ir|--ssa|--ast|--legacy|--strict-structured] <file.luac> [output.lua]\n");
        fprintf(stderr, "  --raw       Output raw disassembly instead of pseudo-code\n");
        fprintf(stderr, "  --cfg       Output control-flow graph dump\n");
        fprintf(stderr, "  --ir        Output normalized instruction IR dump\n");
        fprintf(stderr, "  --ssa       Output analyzed SSA dump\n");
        fprintf(stderr, "  --ast       Output structured AST dump\n");
        fprintf(stderr, "  --legacy    Output legacy full pseudo-code emitter output\n");
        fprintf(stderr, "  --strict-structured  Fail if structured output still contains low-level placeholders\n");
        fprintf(stderr, "  Default mode: auto-detect opcodes and generate readable Lua\n");
    };

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            printUsage();
            return 0;
        }
        else if (strcmp(argv[i], "--raw") == 0 || strcmp(argv[i], "-r") == 0)
            rawMode = true;
        else if (strcmp(argv[i], "--cfg") == 0 || strcmp(argv[i], "-g") == 0)
            cfgMode = true;
        else if (strcmp(argv[i], "--ir") == 0)
            irMode = true;
        else if (strcmp(argv[i], "--ssa") == 0)
            ssaMode = true;
        else if (strcmp(argv[i], "--ast") == 0)
            astMode = true;
        else if (strcmp(argv[i], "--legacy") == 0)
            legacyMode = true;
        else if (strcmp(argv[i], "--strict-structured") == 0)
            strictStructuredMode = true;
        else if (!inputPath)
            inputPath = argv[i];
        else if (!outputPath)
            outputPath = argv[i];
    }

    if (!inputPath) {
        printUsage();
        return 1;
    }

    try {
        fprintf(stderr, "[*] Loading: %s\n", inputPath);
        auto data = readFile(inputPath);
        fprintf(stderr, "[*] File size: %zu bytes\n", data.size());
        
        // Version explicit whitelist check
        // uint8_t version = data.size() > 0 ? data[0] : 0;
        // if (version != 6 && version != 255) {
        //      fprintf(stderr, "[!] Error: Unsupported bytecode version\n");
        //      return 1;
        // }

        stripHeader(data);

        fprintf(stderr, "[*] Deserializing bytecode...\n");
        Chunk chunk = deserialize(data.data(), data.size());

        std::string output;

        if (rawMode) {
            fprintf(stderr, "[*] Auto-detecting opcode mapping for disassembly...\n");
            OpcodeMap opmap = autoDetectOpcodes(chunk);

            fprintf(stderr, "[*] Generating mapped raw disassembly...\n");
            output = disassemble(chunk, &opmap);
        } else if (irMode) {
            fprintf(stderr, "[*] Auto-detecting opcode mapping for IR...\n");
            OpcodeMap opmap = autoDetectOpcodes(chunk);

            fprintf(stderr, "[*] Lifting instructions into normalized IR...\n");
            output = formatInstructionIR(chunk, opmap);
        } else if (ssaMode) {
            fprintf(stderr, "[*] Auto-detecting opcode mapping for SSA...\n");
            OpcodeMap opmap = autoDetectOpcodes(chunk);
            if (opmap.mappingConfidence < 0.45f &&
                !canProceedStrictStructuredWithLowConfidence(opmap)) {
                throw std::runtime_error("opcode mapping confidence too low for SSA analysis");
            }

            fprintf(stderr, "[*] Building SSA and analysis passes...\n");
            output = formatAnalyzedSSA(chunk, opmap);
        } else if (astMode) {
            fprintf(stderr, "[*] Auto-detecting opcode mapping for AST...\n");
            OpcodeMap opmap = autoDetectOpcodes(chunk);
            if (opmap.mappingConfidence < 0.45f &&
                !canProceedStrictStructuredWithLowConfidence(opmap)) {
                throw std::runtime_error("opcode mapping confidence too low for AST output");
            }

            fprintf(stderr, "[*] Structuring CFG into AST...\n");
            output = formatStructuredAst(chunk, opmap);
        } else if (cfgMode) {
            fprintf(stderr, "[*] Auto-detecting opcode mapping for CFG...\n");
            OpcodeMap opmap = autoDetectOpcodes(chunk);

            fprintf(stderr, "[*] Building control-flow graph...\n");
            output = formatControlFlowGraph(chunk, opmap);
        } else if (legacyMode) {
            fprintf(stderr, "[*] Auto-detecting opcode mapping for legacy pseudo-code...\n");
            OpcodeMap opmap = autoDetectOpcodes(chunk);

            fprintf(stderr, "[*] Generating legacy pseudo-code (%d opcodes mapped)...\n", opmap.totalMapped);
            output = generateCode(chunk, opmap);
        } else {
            fprintf(stderr, "[*] Auto-detecting opcode mapping...\n");
            OpcodeMap opmap = autoDetectOpcodes(chunk);
            if (strictStructuredMode && opmap.mappingConfidence < 0.45f &&
                !canProceedStrictStructuredWithLowConfidence(opmap)) {
                throw std::runtime_error("opcode mapping confidence too low for strict structured output");
            }

            fprintf(stderr, "[*] Generating pseudo-code (%d opcodes mapped)...\n", opmap.totalMapped);
            output = formatStructuredSource(chunk, opmap);
        }

        if (strictStructuredMode && !rawMode && !cfgMode && !irMode && !ssaMode) {
            if (hasStructuredLowLevelArtifacts(output)) {
                throw std::runtime_error("structured output still contains low-level artifacts");
            }
            if (auto semanticDefect = findStructuredSemanticDefect(output); semanticDefect.has_value()) {
                throw std::runtime_error("structured output failed semantic quality gate: " + *semanticDefect);
            }
            if (hasUnresolvedRegisterLikeReturn(output)) {
                fprintf(stderr,
                        "[*] Structured semantic warning: unresolved register-like return value\n");
            }
        }

        if (outputPath) {
            std::ofstream outFile(outputPath);
            if (!outFile) throw std::runtime_error(std::string("Cannot write to: ") + outputPath);
            outFile << output;
            fprintf(stderr, "[+] Output written to: %s\n", outputPath);
        } else {
            std::cout << output;
        }

        fprintf(stderr, "[+] Done! %zu functions, %zu strings.\n",
                chunk.functions.size(), chunk.strings.size());

    } catch (const std::exception& e) {
        fprintf(stderr, "[!] Error: %s\n", e.what());
        return 1;
    }

    return 0;
}
