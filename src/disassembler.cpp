#include "disassembler.hpp"
#include <sstream>
#include <iomanip>
#include <cstdio>

// ==========================================
// Standard Luau OpCode names (open-source Luau order)
// Roblox shuffles these, but we print both the raw value
// AND the standard name if it matches
// ==========================================
static const char* STANDARD_OPNAMES[] = {
    "NOP", "BREAK", "LOADNIL", "LOADB", "LOADN", "LOADK", "MOVE",
    "GETGLOBAL", "SETGLOBAL", "GETUPVAL", "SETUPVAL", "CLOSEUPVALS",
    "GETIMPORT", "GETTABLE", "SETTABLE", "GETTABLEKS", "SETTABLEKS",
    "GETTABLEN", "SETTABLEN", "NEWCLOSURE", "NAMECALL", "CALL", "RETURN",
    "JUMP", "JUMPBACK", "JUMPIF", "JUMPIFNOT",
    "JUMPIFEQ", "JUMPIFLE", "JUMPIFLT",
    "JUMPIFNOTEQ", "JUMPIFNOTLE", "JUMPIFNOTLT",
    "ADD", "SUB", "MUL", "DIV", "MOD", "POW",
    "ADDK", "SUBK", "MULK", "DIVK", "MODK", "POWK",
    "AND", "OR", "ANDK", "ORK",
    "CONCAT", "NOT", "MINUS", "LENGTH",
    "NEWTABLE", "DUPTABLE", "SETLIST",
    "FORNPREP", "FORNLOOP", "FORGLOOP", "FORGPREP_INEXT",
    "FASTCALL3", "FORGPREP_NEXT", "NATIVECALL",
    "GETVARARGS", "DUPCLOSURE", "PREPVARARGS", "LOADKX",
    "JUMPX", "FASTCALL", "COVERAGE", "CAPTURE",
    "SUBRK", "DIVRK",
    "FASTCALL1", "FASTCALL2", "FASTCALL2K",
    "FORGPREP",
    "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS",
    "IDIV", "IDIVK",
};
static constexpr int NUM_STANDARD_OPS = sizeof(STANDARD_OPNAMES) / sizeof(STANDARD_OPNAMES[0]);

static int getLineForPc(const Function& f, int pc) {
    if (!f.hasLineInfo || pc < 0 || pc >= (int)f.lineOffsets.size()) return -1;
    int interval = pc >> f.lineGapLog;
    int baseLine = (interval < (int)f.absLineInfo.size()) ? f.absLineInfo[interval] : 0;
    return baseLine + f.lineOffsets[pc] + f.lineDefined;
}

static std::string getLocalName(const Function& f, int slot, int pc) {
    for (auto& lv : f.locals) {
        if (lv.slot == slot && pc >= lv.startPc && pc < lv.endPc)
            return lv.name;
    }
    return "r" + std::to_string(slot);
}

std::string disassemble(const Chunk& chunk, const OpcodeMap* opmap) {
    std::ostringstream out;

    out << "-- ============================================\n";
    out << "-- Luau Bytecode Disassembly\n";
    out << "-- Version: " << (int)chunk.version << "\n";
    out << "-- Types version: " << (int)chunk.typesVersion << "\n";
    out << "-- Strings: " << chunk.strings.size() << "\n";
    out << "-- Functions: " << chunk.functions.size() << "\n";
    out << "-- Main: proto#" << chunk.mainIndex << "\n";
    out << "-- ============================================\n\n";

    // Dump string table
    out << "-- ============ STRING TABLE ============\n";
    for (size_t i = 0; i < chunk.strings.size(); i++) {
        auto& s = chunk.strings[i];
        // Escape non-printable chars
        std::string escaped;
        for (char ch : s) {
            if (ch >= 32 && ch < 127) escaped += ch;
            else {
                char buf[8];
                snprintf(buf, sizeof(buf), "\\x%02X", (uint8_t)ch);
                escaped += buf;
            }
        }
        if (escaped.size() > 120) escaped = escaped.substr(0, 120) + "...";
        out << "-- [" << std::setw(4) << i+1 << "] \"" << escaped << "\"\n";
    }
    out << "\n";

    // Dump each function
    for (auto& f : chunk.functions) {
        out << "-- ============ FUNCTION proto#" << f.id << " ============\n";
        out << "-- Name: " << (f.debugName.empty() ? "(anonymous)" : f.debugName) << "\n";
        out << "-- Line defined: " << f.lineDefined << "\n";
        out << "-- Params: " << (int)f.numParams
            << "  Stack: " << (int)f.maxStackSize
            << "  Upvals: " << (int)f.numUpvalues
            << "  Vararg: " << (f.isVararg ? "yes" : "no") << "\n";
        out << "-- Instructions: " << f.instructions.size()
            << "  Constants: " << f.constants.size()
            << "  Children: " << f.childProtos.size() << "\n";

        // Local variables
        if (!f.locals.empty()) {
            out << "-- Locals:\n";
            for (auto& lv : f.locals) {
                out << "--   slot " << (int)lv.slot << ": " << lv.name
                    << " [pc " << lv.startPc << ".." << lv.endPc << "]\n";
            }
        }
        if (!f.upvalueNames.empty()) {
            out << "-- Upvalues:\n";
            for (size_t i = 0; i < f.upvalueNames.size(); i++)
                out << "--   [" << i << "] " << f.upvalueNames[i] << "\n";
        }

        // Constants
        if (!f.constants.empty()) {
            out << "-- Constants:\n";
            for (size_t i = 0; i < f.constants.size(); i++) {
                out << "--   K" << i << " = " << f.constants[i].toString(chunk.strings) << "\n";
            }
        }

        // Instructions (raw disassembly)
        out << "\n";
        for (int pc = 0; pc < (int)f.instructions.size(); pc++) {
            auto& inst = f.instructions[pc];
            int line = getLineForPc(f, pc);
            char lineStr[16] = "     ";
            if (line > 0) snprintf(lineStr, sizeof(lineStr), "L%-4d", line);

            char hexStr[16];
            snprintf(hexStr, sizeof(hexStr), "%08X", inst.value);

            // Print: [pc] line hex OP(raw_id) A B C / D
            uint8_t rawOp = inst.opcode();
            int mappedOp = opmap ? opmap->lookup(rawOp) : ((rawOp < NUM_STANDARD_OPS) ? rawOp : -1);
            const char* opName = (mappedOp >= 0 && mappedOp < NUM_STANDARD_OPS) ? STANDARD_OPNAMES[mappedOp] : "???";

            out << "  [" << std::setw(4) << pc << "] " << lineStr << " "
                << hexStr << "  OP" << std::setw(3) << (int)rawOp
                << " (" << std::setw(16) << std::left << opName << std::right << ")"
                << "  A=" << std::setw(3) << (int)inst.a()
                << " B=" << std::setw(3) << (int)inst.b()
                << " C=" << std::setw(3) << (int)inst.c()
                << " D=" << std::setw(6) << (int)inst.d();

            if (opmap) {
                out << "  ; mapped=" << opName;
            }

            // Annotate with constant references where possible
            // LOADK: A = K[D]
            if (mappedOp == 5 && inst.d() >= 0 && inst.d() < (int)f.constants.size()) {
                out << "  ; " << getLocalName(f, inst.a(), pc) << " = "
                    << f.constants[inst.d()].toString(chunk.strings);
            }
            // GETIMPORT: A = import K[D]
            else if (mappedOp == 12 && inst.d() >= 0 && inst.d() < (int)f.constants.size()) {
                out << "  ; " << getLocalName(f, inst.a(), pc) << " = import "
                    << f.constants[inst.d()].toString(chunk.strings);
            }
            // LOADN: A = D (number literal)
            else if (mappedOp == 4) {
                out << "  ; " << getLocalName(f, inst.a(), pc) << " = " << inst.d();
            }

            out << "\n";
        }
        out << "\n";
    }

    return out.str();
}
