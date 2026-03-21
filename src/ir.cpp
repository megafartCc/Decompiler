#include "ir.hpp"
#include <atomic>
#include <future>
#include <sstream>
#include <thread>

static constexpr uint32_t kJumpXEqConstantMask = 0x00ffffffu;
static constexpr uint32_t kJumpXEqFallthroughOnMatchFlag = 0x80000000u;

static bool opcodeHasAuxWord(int stdOp) {
    switch (stdOp) {
        case OP_GETIMPORT:
        case OP_GETGLOBAL:
        case OP_SETGLOBAL:
        case OP_GETTABLEKS:
        case OP_SETTABLEKS:
        case OP_NAMECALL:
        case OP_JUMPIFEQ:
        case OP_JUMPIFNOTEQ:
        case OP_JUMPIFLE:
        case OP_JUMPIFLT:
        case OP_JUMPIFNOTLE:
        case OP_JUMPIFNOTLT:
        case OP_LOADKX:
        case OP_NEWTABLE:
        case OP_SETLIST:
        case OP_FORGLOOP:
        case OP_FASTCALL3:
        case OP_FASTCALL2:
        case OP_FASTCALL2K:
        case OP_COVERAGE:
        case OP_JUMPXEQKNIL:
        case OP_JUMPXEQKB:
        case OP_JUMPXEQKN:
        case OP_JUMPXEQKS:
            return true;
        default:
            return false;
    }
}

static std::optional<std::string> decodeStringConstant(const Function& function, uint32_t aux) {
    if (aux < function.constants.size() && function.constants[aux].type == ConstantType::String) {
        return function.constants[aux].strVal;
    }
    return std::nullopt;
}

static std::optional<std::string> decodeImportName(const Function& function, uint32_t aux) {
    for (const auto& constant : function.constants) {
        if (constant.type == ConstantType::Import && constant.importId == aux && !constant.importNames.empty()) {
            std::string joined;
            for (size_t i = 0; i < constant.importNames.size(); ++i) {
                if (i > 0) {
                    joined += ".";
                }
                joined += constant.importNames[i];
            }
            return joined;
        }
    }
    return std::nullopt;
}

static uint32_t jumpXEqConstantIndex(uint32_t aux) {
    return aux & kJumpXEqConstantMask;
}

static bool jumpXEqFallthroughOnMatch(uint32_t aux) {
    return (aux & kJumpXEqFallthroughOnMatchFlag) != 0;
}

template <typename Formatter>
static std::vector<std::string> formatFunctionsParallel(const std::vector<Function>& functions, Formatter&& formatter) {
    const size_t functionCount = functions.size();
    std::vector<std::string> chunks(functionCount);
    if (functionCount == 0) {
        return chunks;
    }

    unsigned int workerCount = std::thread::hardware_concurrency();
    if (workerCount == 0) {
        workerCount = 4;
    }
    workerCount = (unsigned int)std::min<size_t>(workerCount, functionCount);
    if (workerCount <= 1 || functionCount < 4) {
        for (size_t i = 0; i < functionCount; ++i) {
            chunks[i] = formatter(functions[i]);
        }
        return chunks;
    }

    std::atomic<size_t> nextIndex{0};
    std::vector<std::future<void>> workers;
    workers.reserve(workerCount);
    for (unsigned int worker = 0; worker < workerCount; ++worker) {
        workers.push_back(std::async(std::launch::async, [&]() {
            while (true) {
                size_t index = nextIndex.fetch_add(1);
                if (index >= functionCount) {
                    break;
                }
                chunks[index] = formatter(functions[index]);
            }
        }));
    }
    for (auto& worker : workers) {
        worker.get();
    }
    return chunks;
}

FunctionIR decodeFunctionIR(const Function& function, const OpcodeMap& opmap) {
    FunctionIR ir;
    const int numInst = (int)function.instructions.size();

    for (int pc = 0; pc < numInst; ) {
        const auto& raw = function.instructions[pc];
        DecodedInstruction decoded;
        decoded.pc = pc;
        decoded.stdOp = opmap.lookup(raw.opcode());
        decoded.opName = stdOpName(decoded.stdOp);
        decoded.a = raw.a();
        decoded.b = raw.b();
        decoded.c = raw.c();
        decoded.d = raw.d();
        decoded.e = raw.e();

        if (opcodeHasAuxWord(decoded.stdOp) && pc + 1 < numInst) {
            decoded.hasAux = true;
            decoded.aux = function.instructions[pc + 1].value;
            decoded.width = 2;
        }

        switch (decoded.stdOp) {
            case OP_LOADNIL:
                decoded.constantValue = "nil";
                break;
            case OP_LOADB:
                decoded.constantValue = decoded.b ? "true" : "false";
                break;
            case OP_LOADN:
                decoded.constantValue = std::to_string(decoded.d);
                break;
            case OP_LOADK:
                if (decoded.d >= 0 && decoded.d < (int)function.constants.size()) {
                    decoded.constantValue = function.constants[decoded.d].toString({});
                }
                break;
            case OP_GETIMPORT:
                decoded.importName = decodeImportName(function, decoded.aux);
                break;
            case OP_GETGLOBAL:
            case OP_SETGLOBAL:
                decoded.keyName = decodeStringConstant(function, decoded.aux);
                break;
            case OP_GETTABLEKS:
            case OP_SETTABLEKS:
            case OP_NAMECALL:
                decoded.keyName = decodeStringConstant(function, decoded.aux);
                break;
            case OP_LOADKX:
                if (decoded.aux < function.constants.size()) {
                    decoded.constantValue = function.constants[decoded.aux].toString({});
                }
                break;
            case OP_ADDK:
            case OP_SUBK:
            case OP_MULK:
            case OP_DIVK:
            case OP_MODK:
            case OP_POWK:
            case OP_IDIVK:
            case OP_ANDK:
            case OP_ORK:
                if (decoded.c < function.constants.size()) {
                    decoded.constantValue = function.constants[decoded.c].toString({});
                }
                break;
            case OP_SUBRK:
            case OP_DIVRK:
                if (decoded.b < function.constants.size()) {
                    decoded.constantValue = function.constants[decoded.b].toString({});
                }
                break;
            case OP_JUMPXEQKNIL:
                decoded.constantValue = "nil";
                decoded.fallthroughOnMatch = jumpXEqFallthroughOnMatch(decoded.aux);
                break;
            case OP_JUMPXEQKB:
                decoded.constantValue = (decoded.aux & 1u) ? "true" : "false";
                decoded.fallthroughOnMatch = jumpXEqFallthroughOnMatch(decoded.aux);
                break;
            case OP_JUMPXEQKN: {
                uint32_t constantIndex = jumpXEqConstantIndex(decoded.aux);
                if (constantIndex < function.constants.size()) {
                    decoded.constantValue = function.constants[constantIndex].toString({});
                }
                decoded.fallthroughOnMatch = jumpXEqFallthroughOnMatch(decoded.aux);
                break;
            }
            case OP_JUMPXEQKS: {
                uint32_t constantIndex = jumpXEqConstantIndex(decoded.aux);
                if (constantIndex < function.constants.size()) {
                    decoded.constantValue = function.constants[constantIndex].toString({});
                    if (function.constants[constantIndex].type == ConstantType::String) {
                        decoded.keyName = function.constants[constantIndex].strVal;
                    }
                }
                decoded.fallthroughOnMatch = jumpXEqFallthroughOnMatch(decoded.aux);
                break;
            }
            default:
                break;
        }

        switch (decoded.stdOp) {
            case OP_JUMPX:
                decoded.jumpTargetPc = pc + decoded.e + 1;
                break;
            case OP_JUMP:
            case OP_JUMPBACK:
            case OP_JUMPIF:
            case OP_JUMPIFNOT:
            case OP_JUMPIFEQ:
            case OP_JUMPIFNOTEQ:
            case OP_JUMPIFLE:
            case OP_JUMPIFLT:
            case OP_JUMPIFNOTLE:
            case OP_JUMPIFNOTLT:
            case OP_FORNPREP:
            case OP_FORNLOOP:
            case OP_FORGPREP:
            case OP_FORGPREP_NEXT:
            case OP_FORGPREP_INEXT:
            case OP_FORGLOOP:
            case OP_JUMPXEQKNIL:
            case OP_JUMPXEQKB:
            case OP_JUMPXEQKN:
            case OP_JUMPXEQKS:
                decoded.jumpTargetPc = pc + decoded.d + 1;
                break;
            default:
                break;
        }

        ir.push_back(decoded);
        pc += decoded.width;
    }

    return ir;
}

std::string formatInstructionIR(const Chunk& chunk, const OpcodeMap& opmap) {
    std::ostringstream out;
    out << "-- Instruction IR Dump\n";
    out << "-- Functions: " << chunk.functions.size() << "\n\n";

    auto chunks = formatFunctionsParallel(chunk.functions, [&](const Function& function) {
        std::ostringstream fnOut;
        fnOut << "Function proto#" << function.id;
        if (!function.debugName.empty()) {
            fnOut << " \"" << function.debugName << "\"";
        }
        if (function.lineDefined > 0) {
            fnOut << " line " << function.lineDefined;
        }
        fnOut << "\n";

        FunctionIR ir = decodeFunctionIR(function, opmap);
        for (const auto& inst : ir) {
            fnOut << "  pc=" << inst.pc
                  << " width=" << inst.width
                  << " op=" << inst.opName
                  << " A=" << (int)inst.a
                  << " B=" << (int)inst.b
                  << " C=" << (int)inst.c
                  << " D=" << inst.d;

            if (inst.jumpTargetPc.has_value()) {
                fnOut << " target=" << *inst.jumpTargetPc;
            }
            if (inst.importName.has_value()) {
                fnOut << " import=" << *inst.importName;
            }
            if (inst.keyName.has_value()) {
                fnOut << " key=" << *inst.keyName;
            }
            if (inst.constantValue.has_value()) {
                fnOut << " const=" << *inst.constantValue;
            }
            if (inst.stdOp == OP_JUMPXEQKNIL || inst.stdOp == OP_JUMPXEQKB ||
                inst.stdOp == OP_JUMPXEQKN || inst.stdOp == OP_JUMPXEQKS) {
                fnOut << " fallthrough=" << (inst.fallthroughOnMatch ? "match" : "mismatch");
            }
            fnOut << "\n";
        }
        fnOut << "\n";
        return fnOut.str();
    });

    for (const auto& chunkText : chunks) {
        out << chunkText;
    }

    return out.str();
}
