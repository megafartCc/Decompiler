#pragma once
#include "deserializer.hpp"
#include <unordered_map>
#include <string>

// Standard Luau opcodes (open-source Luau order)
enum StdOp : int {
    OP_NOP = 0, OP_BREAK, OP_LOADNIL, OP_LOADB, OP_LOADN, OP_LOADK, OP_MOVE,
    OP_GETGLOBAL, OP_SETGLOBAL, OP_GETUPVAL, OP_SETUPVAL, OP_CLOSEUPVALS,
    OP_GETIMPORT, OP_GETTABLE, OP_SETTABLE, OP_GETTABLEKS, OP_SETTABLEKS,
    OP_GETTABLEN, OP_SETTABLEN, OP_NEWCLOSURE, OP_NAMECALL, OP_CALL, OP_RETURN,
    OP_JUMP, OP_JUMPBACK, OP_JUMPIF, OP_JUMPIFNOT,
    OP_JUMPIFEQ, OP_JUMPIFLE, OP_JUMPIFLT,
    OP_JUMPIFNOTEQ, OP_JUMPIFNOTLE, OP_JUMPIFNOTLT,
    OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_MOD, OP_POW,
    OP_ADDK, OP_SUBK, OP_MULK, OP_DIVK, OP_MODK, OP_POWK,
    OP_AND, OP_OR, OP_ANDK, OP_ORK,
    OP_CONCAT, OP_NOT, OP_MINUS, OP_LENGTH,
    OP_NEWTABLE, OP_DUPTABLE, OP_SETLIST,
    OP_FORNPREP, OP_FORNLOOP, OP_FORGLOOP, OP_FORGPREP_INEXT,
    OP_FASTCALL3, OP_FORGPREP_NEXT, OP_NATIVECALL,
    OP_GETVARARGS, OP_DUPCLOSURE, OP_PREPVARARGS, OP_LOADKX,
    OP_JUMPX, OP_FASTCALL, OP_COVERAGE, OP_CAPTURE,
    OP_SUBRK, OP_DIVRK,
    OP_FASTCALL1, OP_FASTCALL2, OP_FASTCALL2K,
    OP_FORGPREP,
    OP_JUMPXEQKNIL, OP_JUMPXEQKB, OP_JUMPXEQKN, OP_JUMPXEQKS,
    OP_IDIV, OP_IDIVK,
    OP_COUNT,
    OP_UNKNOWN = -1
};

const char* stdOpName(int op);

struct OpcodeMap {
    int toStd[256];    // shuffled -> standard (-1 = unknown)
    int fromStd[256];  // standard -> shuffled (-1 = unknown)
    float confidence[256];
    int totalMapped = 0;
    int detectedEncodeKey = -1;
    float mappingConfidence = 0.0f;
    bool usedFallback = false;
    int sampledFunctions = 0;
    int unknownOps = 0;
    int invalidAux = 0;
    int invalidJumpTargets = 0;

    void assign(int shuffled, int standard, float conf);
    int  lookup(uint8_t shuffled) const { return toStd[shuffled]; }
};

// Analyze bytecode and auto-detect opcode mapping
OpcodeMap autoDetectOpcodes(const Chunk& chunk);
