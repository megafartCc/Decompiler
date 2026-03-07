#include "automapper.hpp"
#include <algorithm>
#include <cstdio>
#include <map>
#include <set>
#include <cstring>

static const char* OP_NAMES[] = {
    "NOP","BREAK","LOADNIL","LOADB","LOADN","LOADK","MOVE",
    "GETGLOBAL","SETGLOBAL","GETUPVAL","SETUPVAL","CLOSEUPVALS",
    "GETIMPORT","GETTABLE","SETTABLE","GETTABLEKS","SETTABLEKS",
    "GETTABLEN","SETTABLEN","NEWCLOSURE","NAMECALL","CALL","RETURN",
    "JUMP","JUMPBACK","JUMPIF","JUMPIFNOT",
    "JUMPIFEQ","JUMPIFLE","JUMPIFLT","JUMPIFNOTEQ","JUMPIFNOTLE","JUMPIFNOTLT",
    "ADD","SUB","MUL","DIV","MOD","POW",
    "ADDK","SUBK","MULK","DIVK","MODK","POWK",
    "AND","OR","ANDK","ORK",
    "CONCAT","NOT","MINUS","LENGTH",
    "NEWTABLE","DUPTABLE","SETLIST",
    "FORNPREP","FORNLOOP","FORGLOOP","FORGPREP_INEXT",
    "FASTCALL3","FORGPREP_NEXT","NATIVECALL",
    "GETVARARGS","DUPCLOSURE","PREPVARARGS","LOADKX",
    "JUMPX","FASTCALL","COVERAGE","CAPTURE",
    "SUBRK","DIVRK","FASTCALL1","FASTCALL2","FASTCALL2K",
    "FORGPREP",
    "JUMPXEQKNIL","JUMPXEQKB","JUMPXEQKN","JUMPXEQKS",
    "IDIV","IDIVK",
};

const char* stdOpName(int op) {
    if (op >= 0 && op < OP_COUNT) return OP_NAMES[op];
    return "???";
}

void OpcodeMap::assign(int shuffled, int standard, float conf) {
    if (shuffled < 0 || shuffled > 255) return;
    if (toStd[shuffled] != OP_UNKNOWN) return;
    if (standard >= 0 && standard < 256 && fromStd[standard] != -1) return;
    toStd[shuffled] = standard;
    confidence[shuffled] = conf;
    if (standard >= 0 && standard < 256) fromStd[standard] = shuffled;
    totalMapped++;
}

OpcodeMap autoDetectOpcodes(const Chunk& chunk) {
    OpcodeMap m;
    memset(m.toStd, -1, sizeof(m.toStd));
    memset(m.fromStd, -1, sizeof(m.fromStd));
    memset(m.confidence, 0, sizeof(m.confidence));
    m.totalMapped = 0;

    // ==========================================
    // DETERMINISTIC MAPPING using encode_key=203
    // Formula: standard = (shuffled * 203) % 256
    // Inverse: shuffled = (standard * 227) % 256
    // ==========================================
    
    fprintf(stderr, "[mapper] Using deterministic encode_key=203\n");
    
    for (int std = 0; std < OP_COUNT; std++) {
        int shuffled = (std * 227) % 256;
        m.toStd[shuffled] = std;
        m.fromStd[std] = shuffled;
        m.confidence[shuffled] = 1.0f;
        m.totalMapped++;
    }

    fprintf(stderr, "[mapper] Mapped all %d opcodes deterministically\n", m.totalMapped);
    
    // Print key mappings for verification
    fprintf(stderr, "[mapper] LOADK      = OP%d\n", m.fromStd[OP_LOADK]);
    fprintf(stderr, "[mapper] NAMECALL   = OP%d\n", m.fromStd[OP_NAMECALL]);
    fprintf(stderr, "[mapper] CALL       = OP%d\n", m.fromStd[OP_CALL]);
    fprintf(stderr, "[mapper] RETURN     = OP%d\n", m.fromStd[OP_RETURN]);
    fprintf(stderr, "[mapper] GETIMPORT  = OP%d\n", m.fromStd[OP_GETIMPORT]);
    fprintf(stderr, "[mapper] GETTABLEKS = OP%d\n", m.fromStd[OP_GETTABLEKS]);
    fprintf(stderr, "[mapper] SETTABLEKS = OP%d\n", m.fromStd[OP_SETTABLEKS]);
    fprintf(stderr, "[mapper] MOVE       = OP%d\n", m.fromStd[OP_MOVE]);
    fprintf(stderr, "[mapper] JUMP       = OP%d\n", m.fromStd[OP_JUMP]);
    fprintf(stderr, "[mapper] NEWCLOSURE = OP%d\n", m.fromStd[OP_NEWCLOSURE]);
    fprintf(stderr, "[mapper] CAPTURE    = OP%d\n", m.fromStd[OP_CAPTURE]);
    fprintf(stderr, "[mapper] GETUPVAL   = OP%d\n", m.fromStd[OP_GETUPVAL]);
    fprintf(stderr, "[mapper] SETUPVAL   = OP%d\n", m.fromStd[OP_SETUPVAL]);
    
    return m;
}
