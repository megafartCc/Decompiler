#include "codegen.hpp"
#include <algorithm>
#include <cctype>
#include <sstream>
#include <iomanip>
#include <cstdio>
#include <unordered_map>
#include <optional>

// ==========================================
// Register tracker: tracks what value each register holds
// ==========================================
struct RegVal {
    enum Kind { UNKNOWN, NUMBER, STRING, UPVAL, TABLE_ACCESS, FUNC_RESULT, IMPORT, METHOD_CALL };
    Kind kind = UNKNOWN;
    double numVal = 0;
    std::string strVal;
    int upvalIdx = -1;
    std::string repr; // human-readable representation
};

struct RegTracker {
    RegVal regs[256];
    void clear() { for (auto& r : regs) r = {}; }
    void set(int r, RegVal v) { if (r >= 0 && r < 256) regs[r] = v; }
    RegVal get(int r) const { return (r >= 0 && r < 256) ? regs[r] : RegVal{}; }
};

struct SSATracker {
    std::unordered_map<int, int> versions; // slot -> current version
    std::unordered_map<int, std::unordered_map<int, std::string>> semanticNames; // slot -> version -> inferred name

    // Create a new version for the register
    int next(int slot) {
        return ++versions[slot];
    }

    // Get the current version of the register
    int current(int slot) const {
        auto it = versions.find(slot);
        return it != versions.end() ? it->second : 0;
    }
    
    // Bind a human-readable heuristic name to this specific register version
    void setSemanticName(int slot, int ver, const std::string& name) {
        semanticNames[slot][ver] = name;
    }
    
    // Retrieve a bound heuristic name if it exists
    std::string getSemanticName(int slot, int ver) const {
        auto slotIt = semanticNames.find(slot);
        if (slotIt != semanticNames.end()) {
            auto verIt = slotIt->second.find(ver);
            if (verIt != slotIt->second.end()) {
                return verIt->second;
            }
        }
        return "";
    }
    
    void clear() { 
        versions.clear(); 
        semanticNames.clear();
    }
};

// ==========================================
// Helpers
// ==========================================
static bool isIdentifierName(const std::string& value);

static std::string reg(const Function& f, int idx, int pc, const SSATracker& ssa, bool isAssignment = false) {
    // For parameters, use 'p' prefix
    if (idx < f.numParams) return "p" + std::to_string(idx);

    // For local variables, try to find their debug name
    for (auto& lv : f.locals) {
        if (lv.slot == idx && (pc < 0 || (pc >= lv.startPc && pc < lv.endPc))) {
            int ver = isAssignment ? const_cast<SSATracker&>(ssa).next(idx) : ssa.current(idx);
            if (isIdentifierName(lv.name)) {
                if (ver == 0) return lv.name; // Base uninitialized or param fallback
                return lv.name + "_" + std::to_string(ver);
            }
            if (ver == 0) return "v" + std::to_string(idx);
            return "v" + std::to_string(idx) + "_" + std::to_string(ver);
        }
    }

    // Determine the version
    int ver = isAssignment ? const_cast<SSATracker&>(ssa).next(idx) : ssa.current(idx);
    
    // HEURISTIC ENGINE: Prioritize checking for inferred Semantic Names!
    std::string semantic = ssa.getSemanticName(idx, ver);
    if (!semantic.empty()) {
        return semantic;
    }

    // Fallback to generic 'v' prefix with SSA version
    if (ver == 0) return "v" + std::to_string(idx); // Base uninitialized or param fallback
    return "v" + std::to_string(idx) + "_" + std::to_string(ver);
}

static std::string upval(const Function& f, int idx) {
    if (idx >= 0 && idx < (int)f.upvalueNames.size()) {
        if (!f.upvalueNames[idx].empty() && isIdentifierName(f.upvalueNames[idx])) return f.upvalueNames[idx];
    }
    return "upval_" + std::to_string(idx);
}
static std::string resolveReg(const RegTracker& rt, const Function& f, int slot, int pc, const SSATracker& ssa, bool allowLiteral, const std::string& indentStr);

static std::string constStr(const Function& f, int idx, const std::vector<std::string>& strings) {
    if (idx >= 0 && idx < (int)f.constants.size()) {
        return f.constants[idx].toString(strings);
    }
    return "K" + std::to_string(idx);
}

static std::string indent(int level) { return std::string(level * 4, ' '); }

static std::string trimWhitespace(std::string value) {
    while (!value.empty() && std::isspace((unsigned char)value.front())) {
        value.erase(value.begin());
    }
    while (!value.empty() && std::isspace((unsigned char)value.back())) {
        value.pop_back();
    }
    return value;
}

static std::string asCallableExpr(const std::string& expr) {
    std::string trimmed = trimWhitespace(expr);
    if (trimmed.empty()) {
        return expr;
    }

    if (trimmed.front() == '{' || trimmed.find('\n') != std::string::npos ||
        trimmed.rfind("function", 0) == 0 || trimmed == "nil" ||
        trimmed == "true" || trimmed == "false" || trimmed.front() == '"' ||
        std::isdigit((unsigned char)trimmed.front()) || trimmed.front() == '-') {
        return "(" + expr + ")";
    }

    return expr;
}

static std::string asIndexBaseExpr(const std::string& expr) {
    std::string trimmed = trimWhitespace(expr);
    if (trimmed.empty()) {
        return expr;
    }

    if (trimmed.front() == '{' || trimmed.find('\n') != std::string::npos ||
        trimmed.rfind("function", 0) == 0 || trimmed == "nil" ||
        trimmed == "true" || trimmed == "false" || trimmed.front() == '"' ||
        std::isdigit((unsigned char)trimmed.front()) || trimmed.front() == '-') {
        return "(" + expr + ")";
    }

    return expr;
}

static bool isIdentifierName(const std::string& value) {
    if (value.empty() || (!std::isalpha((unsigned char)value[0]) && value[0] != '_')) {
        return false;
    }

    for (char ch : value) {
        if (!std::isalnum((unsigned char)ch) && ch != '_') {
            return false;
        }
    }

    return true;
}

static std::string unquoteSimpleStringLiteral(const std::string& value) {
    if (value.size() >= 2 && value.front() == '"' && value.back() == '"') {
        return value.substr(1, value.size() - 2);
    }

    return value;
}

static std::string statementPrefixForExpr(const std::string& expr) {
    (void)expr;
    return "";
}

static bool isAssignableTarget(const std::string& expr) {
    std::string trimmed = trimWhitespace(expr);
    if (trimmed.empty()) {
        return false;
    }

    char first = trimmed.front();
    if (!std::isalpha((unsigned char)first) && first != '_') {
        return false;
    }

    if (trimmed == "nil" || trimmed == "true" || trimmed == "false") {
        return false;
    }

    return trimmed.find('\n') == std::string::npos;
}

static void emitAssignment(std::ostringstream& out, const std::string& indentStr,
                           const std::string& target, const std::string& value) {
    if (!isAssignableTarget(target)) {
        out << indentStr << "-- skipped invalid assignment target: "
            << target << " = " << value << "\n";
        return;
    }

    out << indentStr << target << " = " << value << "\n";
}

static std::string globalExprFromConst(const std::string& literal) {
    std::string key = unquoteSimpleStringLiteral(literal);
    return isIdentifierName(key) ? key : ("_G[" + literal + "]");
}

// Escape a string for display, truncating if too long
static std::string escapeStr(const std::string& s, int maxLen = 60) {
    std::string out;
    for (char ch : s) {
        if (out.size() >= (size_t)maxLen) { out += "..."; break; }
        if (ch >= 32 && ch < 127) out += ch;
        else { char buf[8]; snprintf(buf, sizeof(buf), "\\x%02X", (uint8_t)ch); out += buf; }
    }
    return out;
}




// ==========================================
// Table Folding Engine
// ==========================================
struct TableBuffer {
    bool active = false;
    std::string declaration;
    std::vector<std::pair<std::string, std::string>> entries; // <Key, Value>
    bool isListOnly = true;

    // Formats the buffer into a gorgeous inline Lua structure!
    std::string formatInline(const std::string& indentStr) const {
        if (entries.empty()) return "{}";
        
        std::ostringstream out;
        out << "{\n";
        std::string innerInd = indentStr + "    ";
        
        for (size_t i = 0; i < entries.size(); ++i) {
            out << innerInd;
            if (!entries[i].first.empty()) {
                // Determine if Dictionary Key needs brackets (e.g. non-identifiers or numbers)
                bool needsBrackets = false;
                for (char c : entries[i].first) {
                    if (!std::isalnum(c) && c != '_') { needsBrackets = true; break; }
                }
                if (std::isdigit(entries[i].first[0])) needsBrackets = true;
                if (entries[i].first == "nil" || entries[i].first == "true" ||
                    entries[i].first == "false" || entries[i].first == "and" ||
                    entries[i].first == "or" || entries[i].first == "not" ||
                    entries[i].first == "function" || entries[i].first == "end" ||
                    entries[i].first == "local" || entries[i].first == "return") {
                    needsBrackets = true;
                }
                
                if (needsBrackets) out << "[" << entries[i].first << "] = ";
                else out << entries[i].first << " = ";
            }
            
            out << entries[i].second;
            if (i < entries.size() - 1) out << ",";
            out << "\n";
        }
        out << indentStr << "}";
        return out.str();
    }
};

// Global tracker for the current function
static std::unordered_map<int, TableBuffer> activeTableBuffers;

// Detects if an expression references a buffered table, flushes it if necessary
static std::string resolveReg(const RegTracker& rt, const Function& f, int slot, int pc, const SSATracker& ssa, bool allowLiteral = true, const std::string& indentStr = "") {
    
    // HEURISTIC ENGINE: Flush active inline tables seamlessly when they are accessed!
    if (activeTableBuffers.count(slot) && activeTableBuffers[slot].active) {
        std::string folded = activeTableBuffers[slot].formatInline(indentStr);
        activeTableBuffers.erase(slot); // Mark as consumed
        return folded;
    }
    
    auto& rv = rt.regs[slot];
    if (!allowLiteral && (rv.kind == RegVal::NUMBER || rv.kind == RegVal::STRING)) return reg(f, slot, pc, ssa);
    if (!rv.repr.empty()) return rv.repr;
    return reg(f, slot, pc, ssa);
}

static std::string resolveRegForExpression(std::ostringstream& out, RegTracker& rt,
                                           const Function& f, int slot, int pc,
                                           const SSATracker& ssa,
                                           const std::string& indentStr,
                                           bool allowLiteral = true) {
    auto tableIt = activeTableBuffers.find(slot);
    if (tableIt != activeTableBuffers.end() && tableIt->second.active) {
        std::string name = reg(f, slot, pc, ssa, true);
        out << indentStr << name << " = " << tableIt->second.formatInline(indentStr) << "\n";
        activeTableBuffers.erase(tableIt);

        RegVal rv;
        rv.kind = RegVal::TABLE_ACCESS;
        rv.repr = name;
        rt.set(slot, rv);
        return name;
    }

    return resolveReg(rt, f, slot, pc, ssa, allowLiteral, indentStr);
}

// Annotate a string table index with the actual string content (for upval_0[N] lookups)
static std::string strAnnotation(const Chunk& chunk, int idx) {
    // String table indices are 1-based in references but 0-based in array
    if (idx > 0 && idx <= (int)chunk.strings.size()) {
        auto& s = chunk.strings[idx - 1]; // adjust for 1-based
        if (s.size() > 0 && s.size() <= 40)
            return " --[[ \"" + escapeStr(s, 30) + "\" ]]";
    }
    if (idx >= 0 && idx < (int)chunk.strings.size()) {
        auto& s = chunk.strings[idx]; // try 0-based
        if (s.size() > 0 && s.size() <= 40)
            return " --[[ \"" + escapeStr(s, 30) + "\" ]]";
    }
    return "";
}

// ==========================================
// Main code generation
// ==========================================
static void emitFunction(std::ostringstream& out, const Chunk& chunk, const OpcodeMap& opmap,
                          const Function& f, int indentLevel) {
    std::string ind = indent(indentLevel);
    std::string ind1 = indent(indentLevel + 1);

    // Function header
    std::string name = f.debugName.empty() ? "(anonymous)" : f.debugName;
    out << ind << "-- ======== proto#" << f.id << " \"" << name << "\"";
    if (f.lineDefined > 0) out << " (line " << f.lineDefined << ")";
    out << " ========\n";

    // Param list
    std::string params;
    SSATracker ssa;
    ssa.clear();

    for (int i = 0; i < f.numParams; i++) {
        if (i > 0) params += ", ";
        params += reg(f, i, 0, ssa, true);
    }
    if (f.isVararg) {
        if (!params.empty()) params += ", ";
        params += "...";
    }

    out << ind << "function proto_" << f.id << "(" << params << ")\n";

    RegTracker rt;
    rt.clear();

    int pc = 0;
    int numInst = (int)f.instructions.size();
    std::vector<bool> emitted(numInst, false);
    
    // Block tracking for if/then, for loops
    std::vector<int> blockEnds;

    // HEURISTIC ENGINE: Tracking inferred names and suffixing counts identically
    std::unordered_map<std::string, int> nameCounts;
    
    // Reset AST Table Folding memory buffer state for this function level!
    activeTableBuffers.clear();
    while (pc < numInst) {
        while (!blockEnds.empty() && pc == blockEnds.back()) {
            indentLevel--;
            ind1 = indent(indentLevel + 1);
            out << indent(indentLevel+1) << "end\n";
            blockEnds.pop_back();
        }

        if (emitted[pc]) { pc++; continue; }


        auto& inst = f.instructions[pc];
        int stdOp = opmap.lookup(inst.opcode());
        int A = inst.a(), B = inst.b(), C = inst.c();
        int16_t D = inst.d();

        // ==========================================
        // Pattern collapse: GETUPVAL + LOADN + GETTABLE → TABLE[N]
        // Pattern: getupval rX, N; loadn rY, NUM; gettable rZ, rX, rY
        // ==========================================
        bool collapsed = false;
        if (stdOp == OP_GETUPVAL && pc + 2 < numInst) {
            auto& next1 = f.instructions[pc + 1];
            auto& next2 = f.instructions[pc + 2];
            int op1 = opmap.lookup(next1.opcode());
            int op2 = opmap.lookup(next2.opcode());

            // Pattern: GETUPVAL rA, upN → LOADN rB, NUM → GETTABLE rC, rA, rB
            if (op1 == OP_LOADN && op2 == OP_GETTABLE) {
                int tableReg = A;
                int idxReg = next1.a();
                int destReg = next2.a();
                int16_t numVal = next1.d();

                if (next2.b() == tableReg && next2.c() == idxReg) {
                    std::string upvName = upval(f, B);
                    std::string expr = upvName + "[" + std::to_string(numVal) + "]";

                    // Check if this is ALSO followed by another GETTABLE using the result
                    // Pattern: result = upval[N] → then used as table in next GETTABLE
                    if (pc + 5 < numInst) {
                        auto& n3 = f.instructions[pc + 3];
                        auto& n4 = f.instructions[pc + 4];
                        auto& n5 = f.instructions[pc + 5];
                        int op3 = opmap.lookup(n3.opcode());
                        int op4 = opmap.lookup(n4.opcode());
                        int op5 = opmap.lookup(n5.opcode());

                        // Double chain: GETUPVAL→LOADN→GETTABLE → GETTABLE(result, prev_result)
                        if (op3 == OP_GETUPVAL && op4 == OP_LOADN && op5 == OP_GETTABLE) {
                            int tr2 = n3.a();
                            int ir2 = n4.a();
                            int dr2 = n5.a();
                            int16_t nv2 = n4.d();
                            if (n5.b() == tr2 && n5.c() == ir2) {
                                std::string expr2 = upval(f, n3.b()) + "[" + std::to_string(nv2) + "]";

                                // Triple chain?
                                if (pc + 8 < numInst) {
                                    auto& n6 = f.instructions[pc + 6];
                                    auto& n7 = f.instructions[pc + 7];
                                    auto& n8 = f.instructions[pc + 8];
                                    int op6 = opmap.lookup(n6.opcode());
                                    int op7 = opmap.lookup(n7.opcode());
                                    int op8 = opmap.lookup(n8.opcode());
                                    if (op6 == OP_GETUPVAL && op7 == OP_LOADN && op8 == OP_GETTABLE) {
                                        int16_t nv3 = n7.d();
                                        std::string expr3 = upval(f, n6.b()) + "[" + std::to_string(nv3) + "]";
                                        out << ind1 << reg(f, n8.a(), pc, ssa) << " = " << expr3 << strAnnotation(chunk, nv3) << "  -- via chain: "
                                            << expr << " → " << expr2 << " → " << expr3 << "\n";
                                        RegVal rv; rv.kind = RegVal::TABLE_ACCESS; rv.repr = expr3;
                                        rt.set(n8.a(), rv);
                                        emitted[pc] = emitted[pc+1] = emitted[pc+2] = true;
                                        emitted[pc+3] = emitted[pc+4] = emitted[pc+5] = true;
                                        emitted[pc+6] = emitted[pc+7] = emitted[pc+8] = true;
                                        pc += 9;
                                        collapsed = true;
                                        continue;
                                    }
                                }

                                out << ind1 << reg(f, dr2, pc, ssa) << " = " << expr2 << strAnnotation(chunk, nv2) << "  -- via " << expr << "\n";
                                RegVal rv; rv.kind = RegVal::TABLE_ACCESS; rv.repr = expr2;
                                rt.set(dr2, rv);
                                emitted[pc] = emitted[pc+1] = emitted[pc+2] = true;
                                emitted[pc+3] = emitted[pc+4] = emitted[pc+5] = true;
                                pc += 6;
                                collapsed = true;
                                continue;
                            }
                        }
                    }

                    out << ind1 << reg(f, destReg, pc, ssa) << " = " << expr << strAnnotation(chunk, numVal) << "\n";
                    RegVal rv; rv.kind = RegVal::TABLE_ACCESS; rv.repr = expr;
                    rt.set(destReg, rv);
                    emitted[pc] = emitted[pc+1] = emitted[pc+2] = true;
                    pc += 3;
                    collapsed = true;
                }
            }
        }
        if (collapsed) continue;

        // ==========================================
        // Standard instruction emission
        // ==========================================
        switch (stdOp) {
            case OP_RETURN:
                if (B == 0) out << ind1 << "do return end --[[ ... ]]\n";
                else if (B == 1) out << ind1 << "do return end\n";
                else {
                    out << ind1 << "do return ";
                    for (int i = 0; i < B - 1; i++) {
                        if (i > 0) out << ", ";
                        out << resolveReg(rt, f, A + i, pc, ssa, true, ind1);
                    }
                    out << " end\n";
                }
                break;

            case OP_PREPVARARGS:
                break; // internal, skip

            case OP_LOADNIL: {
                out << ind1 << reg(f, A, pc, ssa) << " = nil\n";
                RegVal rv; rv.kind = RegVal::UNKNOWN; rv.repr = "nil";
                rt.set(A, rv);
                break;
            }

            case OP_LOADB: {
                std::string val = B ? "true" : "false";
                // SUPPRESS DIRECT OUTPUT: Rely on AST tracking inline resolution!
                if (C != 0) out << ind1 << "-- skip " << C << " instructions\n";
                RegVal rv; rv.kind = RegVal::NUMBER; rv.repr = val; rt.set(A, rv);
                break;
            }

            case OP_LOADN: {
                // SUPPRESS DIRECT OUTPUT: Rely on AST tracking inline resolution!
                RegVal rv; rv.kind = RegVal::NUMBER; rv.numVal = D; rv.repr = std::to_string(D);
                rt.set(A, rv);
                break;
            }
            case OP_GETGLOBAL: {
                uint32_t aux = f.instructions[++pc].value;
                std::string glb = globalExprFromConst(constStr(f, aux, chunk.strings));
                // INLINER: Cache globally as string pointer, DO NOT spam intermediate assignments!
                RegVal rv; rv.kind = RegVal::UNKNOWN; rv.repr = glb; rt.set(A, rv);
                break;
            }
            case OP_SETGLOBAL: {
                uint32_t aux = f.instructions[++pc].value;
                out << ind1 << globalExprFromConst(constStr(f, aux, chunk.strings)) << " = " << resolveReg(rt, f, A, pc, ssa, true, ind1) << "\n";
                break;
            }

            case OP_LOADK: {
                std::string val = constStr(f, D, chunk.strings);
                // SUPPRESS DIRECT OUTPUT: Rely on AST tracking inline resolution!
                RegVal rv; rv.kind = RegVal::STRING; rv.repr = val;
                rt.set(A, rv);
                break;
            }

            case OP_MOVE: {
                std::string src = resolveReg(rt, f, B, pc, ssa);
                out << ind1 << reg(f, A, pc, ssa, true) << " = " << src << "\n";
                rt.set(A, rt.get(B));
                break;
            }

            case OP_GETUPVAL:
                out << ind1 << reg(f, A, pc, ssa, true) << " = " << upval(f, B) << "\n";
                { RegVal rv; rv.kind = RegVal::UPVAL; rv.upvalIdx = B; rt.set(A, rv); }
                break;
            case OP_SETUPVAL:
                out << ind1 << upval(f, B) << " = " << resolveReg(rt, f, A, pc, ssa) << "\n";
                break;
            case OP_CLOSEUPVALS: break;

            case OP_GETIMPORT: {
                uint32_t aux = f.instructions[++pc].value;
                std::string imp = "import_unknown";
                
                // V6 imports store the 30-bit importId in 'aux', NOT the constants array index!
                // We must scan the constants pool to find the matching Import definition.
                for (const auto& c : f.constants) {
                    if (c.type == ConstantType::Import && c.importId == aux) {
                        imp = c.toString(chunk.strings);
                        break;
                    }
                }

                out << ind1 << reg(f, A, pc, ssa, true) << " = " << imp << "\n";
                // NOTE: Do NOT use INLINER cache. Global APIs like 'game' or 'math' must be explicitly declared
                // so subsequent NAMECALL/CALL operations can resolve them properly instead of printing 'Kxxxx' table names!
                RegVal rv; rv.kind = RegVal::UNKNOWN; rv.repr = imp; rt.set(A, rv);
                break;
            }

            case OP_GETTABLE: {
                std::string expr = asIndexBaseExpr(resolveRegForExpression(out, rt, f, B, pc, ssa, ind1, true)) + "[" + resolveReg(rt, f, C, pc, ssa, true, ind1) + "]";
                // INLINER: Cache as table access!
                RegVal rv; rv.kind = RegVal::TABLE_ACCESS; rv.repr = expr; rt.set(A, rv);
                break;
            }
            case OP_SETTABLE: {
                if (activeTableBuffers.count(B) && activeTableBuffers[B].active) {
                    // Inject natively into memory buffer as [C]=A Dictionary formatting
                    std::string keyExpr = resolveReg(rt, f, C, pc, ssa, true, ind1); 
                    // To prevent `"1" = val` output inside the dict, we format properly
                    activeTableBuffers[B].isListOnly = false;
                    activeTableBuffers[B].entries.push_back({keyExpr, resolveReg(rt, f, A, pc, ssa, true, ind1)});
                } else {
                    std::string target = asIndexBaseExpr(resolveRegForExpression(out, rt, f, B, pc, ssa, ind1, true)) + "[" + resolveReg(rt, f, C, pc, ssa, true, ind1) + "]";
                    emitAssignment(out, ind1, target, resolveReg(rt, f, A, pc, ssa, true, ind1));
                }
                break;
            }
            case OP_GETTABLEKS: {
                uint32_t aux = f.instructions[++pc].value;
                std::string key = unquoteSimpleStringLiteral(constStr(f, aux, chunk.strings));
                // INLINER: Allow parsing underlying global table literals like 'game.Players' inside GETTABLEKS
                std::string base = asIndexBaseExpr(resolveRegForExpression(out, rt, f, B, pc, ssa, ind1, true));
                std::string expr = isIdentifierName(key) ? (base + "." + key) : (base + "[" + constStr(f, aux, chunk.strings) + "]");
                // INLINER: Cache as object property, block assignment printing!
                RegVal rv; rv.kind = RegVal::TABLE_ACCESS; rv.repr = expr; rt.set(A, rv);
                break;
            }

            case OP_SETTABLEKS: {
                std::string key = "???";
                std::string keyLiteral = "\"???\"";
                if (pc + 1 < numInst) {
                    uint32_t aux = f.instructions[pc + 1].value;
                    keyLiteral = constStr(f, aux, chunk.strings);
                    if (aux < f.constants.size() && f.constants[aux].type == ConstantType::String) {
                        key = f.constants[aux].strVal;
                    }
                }
                
                if (activeTableBuffers.count(B) && activeTableBuffers[B].active) {
                    // Inject directly into the Table folding buffer
                    activeTableBuffers[B].isListOnly = false;
                    activeTableBuffers[B].entries.push_back({key, resolveReg(rt, f, A, pc, ssa, true, ind1)});
                } else {
                    std::string base = asIndexBaseExpr(resolveRegForExpression(out, rt, f, B, pc, ssa, ind1, true));
                    std::string target = isIdentifierName(key) ? (base + "." + key) : (base + "[" + keyLiteral + "]");
                    emitAssignment(out, ind1, target, resolveReg(rt, f, A, pc, ssa, true, ind1));
                }
                pc++;
                break;
            }

            case OP_NAMECALL: {
                std::string method = "???";
                std::string methodLiteral = "\"???\"";
                if (pc + 1 < numInst) {
                    uint32_t aux = f.instructions[pc + 1].value;
                    methodLiteral = constStr(f, aux, chunk.strings);
                    if (aux < f.constants.size() && f.constants[aux].type == ConstantType::String) {
                        method = f.constants[aux].strVal;
                    }
                }
                std::string obj = asIndexBaseExpr(resolveRegForExpression(out, rt, f, B, pc, ssa, ind1, true)); // INLINER: Allow literal string lookup for Namecalls
                RegVal rv1;
                if (isIdentifierName(method)) {
                    rv1.kind = RegVal::METHOD_CALL;
                    rv1.repr = obj + ":" + method;
                } else {
                    rv1.kind = RegVal::TABLE_ACCESS;
                    rv1.repr = obj + "[" + methodLiteral + "]";
                }
                rt.set(A, rv1);
                pc++;
                break;
            }

            case OP_CALL: {
                std::string func = resolveRegForExpression(out, rt, f, A, pc, ssa, ind1, true); // INLINER: Allow literal lookup for Call handles
                std::string callable = asCallableExpr(func);
                std::string argsStr;
                std::string firstArgLiterals; // HEURISTIC ENGINE hook
                bool isMethod = (rt.get(A).kind == RegVal::METHOD_CALL);
                if (B == 0) {
                    argsStr = "";
                } else {
                    int startArg = isMethod ? 2 : 1;
                    for (int i = startArg; i < B; i++) {
                        if (i > startArg) argsStr += ", ";
                        std::string arg = resolveReg(rt, f, A + i, pc, ssa);
                        argsStr += arg;
                        if (i == startArg) firstArgLiterals = arg; // Capture the first real arg
                    }
                }
                
                // HEURISTIC ENGINE: Intercept and bind human-readable names to the results of APIs!
                if (C > 1 && !firstArgLiterals.empty()) {
                    std::string cleanArg = firstArgLiterals;
                    // Strip the double quotes if they exist around the argument
                    if (cleanArg.size() >= 2 && cleanArg.front() == '"' && cleanArg.back() == '"') {
                        cleanArg = cleanArg.substr(1, cleanArg.size() - 2);
                    }
                    
                    std::string inferredName = "";
                    if (func == "Instance.new") {
                        inferredName = cleanArg; // e.g. "Frame" 
                    } else if (func.find(":GetService") != std::string::npos) {
                        inferredName = cleanArg; // e.g. "TweenService"
                    }
                    
                    // Bind the inferred name cleanly to the output SSA version!
                    if (!inferredName.empty() && isIdentifierName(inferredName)) {
                        int currentVersionForRet = ssa.current(A);
                        int count = ++nameCounts[inferredName];
                        std::string finalName = inferredName;
                        if (count > 1) finalName += "_" + std::to_string(count); // "Frame_2"
                        // Since 'isAssignment=true' inside 'reg()' handles incrementing the version, 
                        // we must pre-emptively bind the NEXT version.
                        ssa.setSemanticName(A, currentVersionForRet + 1, finalName);
                    }
                }

                if (C == 0) {
                    if (pc + 1 < numInst) {
                        const auto& nextInst = f.instructions[pc + 1];
                        int nextOp = opmap.lookup(nextInst.opcode());
                        if (nextOp == OP_RETURN && nextInst.a() == A && nextInst.b() == 0) {
                            out << ind1 << "do return " << callable << "(" << argsStr << ") end\n";
                            rt.set(A, {});
                            pc++;
                            break;
                        }
                    }
                    out << ind1 << reg(f, A, pc, ssa, true) << " = " << callable << "(" << argsStr << ") --[[ multret ]]\n";
                } else if (C == 1) {
                    out << ind1 << statementPrefixForExpr(callable) << callable << "(" << argsStr << ")\n";
                } else {
                    std::string results;
                    for (int i = 0; i < C - 1; i++) {
                        if (i > 0) results += ", ";
                        results += reg(f, A + i, pc, ssa, true);
                        
                        if (activeTableBuffers.count(A+i)) {
                            activeTableBuffers.erase(A+i);
                        }
                    }
                    out << ind1 << results << " = " << callable << "(" << argsStr << ")\n";
                }
                // Invalidate result registers
                for (int i = 0; i < (C == 0 ? 10 : C - 1); i++) rt.set(A + i, {});
                break;
            }

            case OP_NEWCLOSURE: {
                std::string proto = "nil";
                if (D >= 0 && D < (int)f.childProtos.size()) proto = "proto_" + std::to_string(f.childProtos[D]);
                out << ind1 << reg(f, A, pc, ssa, true) << " = " << proto << "\n";
                break;
            }

            case OP_DUPCLOSURE: {
                if (D >= 0 && D < (int)f.constants.size() && f.constants[D].type == ConstantType::Closure) {
                    out << ind1 << reg(f, A, pc, ssa, true) << " = proto_" << f.constants[D].closureIdx << "\n";
                    break;
                }
                if (D >= 0 && D < (int)f.constants.size() && f.constants[D].type == ConstantType::Closure) {
                    out << ind1 << reg(f, A, pc, ssa, true) << " = function() -- closure → proto#" << f.constants[D].closureIdx << "\n";
                } else {
                    out << ind1 << reg(f, A, pc, ssa, true) << " = closure(K" << D << ")\n";
                }
                break;
            }

            case OP_CAPTURE:
                if (A == 0) out << ind1 << "-- capture val " << reg(f, B, pc, ssa) << "\n";
                else if (A == 1) out << ind1 << "-- capture ref " << reg(f, B, pc, ssa) << "\n";
                else if (A == 2) out << ind1 << "-- capture upval " << upval(f, B) << "\n";
                else out << ind1 << "-- capture[" << A << "] " << B << "\n";
                break;

            case OP_JUMP:
                if (D > 0) {
                    out << ind1 << "-- goto skip " << D << "\n";
                } else {
                    out << ind1 << "-- goto pc " << (pc + D + 1) << "\n";
                }
                break;

            case OP_JUMPBACK:
                // out << ind1 << "continue? loop back to " << (pc + D + 1) << "\n";
                break;

            case OP_JUMPIF:
                out << ind1 << "if " << resolveReg(rt, f, A, pc, ssa, true, ind1) << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;

            case OP_JUMPIFNOT:
                out << ind1 << "if not " << resolveReg(rt, f, A, pc, ssa, true, ind1) << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;

            case OP_JUMPIFEQ: {
                uint32_t aux = f.instructions[++pc].value;
                out << ind1 << "if " << resolveReg(rt, f, A, pc, ssa) << " == " << resolveReg(rt, f, aux, pc, ssa) << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_JUMPIFNOTEQ: {
                uint32_t aux = f.instructions[++pc].value;
                out << ind1 << "if " << resolveReg(rt, f, A, pc, ssa) << " ~= " << resolveReg(rt, f, aux, pc, ssa) << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_JUMPIFLE: {
                uint32_t aux = f.instructions[++pc].value;
                std::string lhs = resolveReg(rt, f, A, pc, ssa);
                std::string rhs = resolveReg(rt, f, aux, pc, ssa);
                if (!lhs.empty() && std::isdigit(lhs[0])) out << ind1 << "if " << rhs << " >= " << lhs << " then\n";
                else out << ind1 << "if " << lhs << " <= " << rhs << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_JUMPIFLT: {
                uint32_t aux = f.instructions[++pc].value;
                std::string lhs = resolveReg(rt, f, A, pc, ssa);
                std::string rhs = resolveReg(rt, f, aux, pc, ssa);
                if (!lhs.empty() && std::isdigit(lhs[0])) out << ind1 << "if " << rhs << " > " << lhs << " then\n";
                else out << ind1 << "if " << lhs << " < " << rhs << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_JUMPIFNOTLE: {
                uint32_t aux = f.instructions[++pc].value;
                std::string lhs = resolveReg(rt, f, A, pc, ssa);
                std::string rhs = resolveReg(rt, f, aux, pc, ssa);
                if (!lhs.empty() && std::isdigit(lhs[0])) out << ind1 << "if " << rhs << " <= " << lhs << " then\n";
                else out << ind1 << "if " << lhs << " > " << rhs << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_JUMPIFNOTLT: {
                uint32_t aux = f.instructions[++pc].value;
                std::string lhs = resolveReg(rt, f, A, pc, ssa);
                std::string rhs = resolveReg(rt, f, aux, pc, ssa);
                if (!lhs.empty() && std::isdigit(lhs[0])) out << ind1 << "if " << rhs << " < " << lhs << " then\n";
                else out << ind1 << "if " << lhs << " >= " << rhs << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }

            case OP_ADD: {
                std::string dest = reg(f, A, pc, ssa, true);
                std::string lhs = resolveReg(rt, f, B, pc, ssa, true, ind1);
                std::string rhs = resolveReg(rt, f, C, pc, ssa, true, ind1);
                if (dest == lhs && !dest.empty() && dest.find("v") != 0 && dest.find_first_of(".[") != std::string::npos) out << ind1 << dest << " += " << rhs << "\n";
                else if (dest == lhs && dest.find("v") != 0) out << ind1 << dest << " += " << rhs << "\n";
                else out << ind1 << dest << " = " << lhs << " + " << rhs << "\n";
                rt.set(A, {}); break;
            }
            case OP_SUB: {
                std::string dest = reg(f, A, pc, ssa, true);
                std::string lhs = resolveReg(rt, f, B, pc, ssa, true, ind1);
                std::string rhs = resolveReg(rt, f, C, pc, ssa, true, ind1);
                if (dest == lhs && !dest.empty() && dest.find("v") != 0 && dest.find_first_of(".[") != std::string::npos) out << ind1 << dest << " -= " << rhs << "\n";
                else if (dest == lhs && dest.find("v") != 0) out << ind1 << dest << " -= " << rhs << "\n";
                else out << ind1 << dest << " = " << lhs << " - " << rhs << "\n";
                rt.set(A, {}); break;
            }
            case OP_MUL: {
                std::string dest = reg(f, A, pc, ssa, true);
                std::string lhs = resolveReg(rt, f, B, pc, ssa, true, ind1);
                std::string rhs = resolveReg(rt, f, C, pc, ssa, true, ind1);
                if (dest == lhs && !dest.empty() && dest.find("v") != 0 && dest.find_first_of(".[") != std::string::npos) out << ind1 << dest << " *= " << rhs << "\n";
                else if (dest == lhs && dest.find("v") != 0) out << ind1 << dest << " *= " << rhs << "\n";
                else out << ind1 << dest << " = " << lhs << " * " << rhs << "\n";
                rt.set(A, {}); break;
            }
            case OP_DIV: {
                std::string dest = reg(f, A, pc, ssa, true);
                std::string lhs = resolveReg(rt, f, B, pc, ssa, true, ind1);
                std::string rhs = resolveReg(rt, f, C, pc, ssa, true, ind1);
                if (dest == lhs && !dest.empty() && dest.find("v") != 0 && dest.find_first_of(".[") != std::string::npos) out << ind1 << dest << " /= " << rhs << "\n";
                else if (dest == lhs && dest.find("v") != 0) out << ind1 << dest << " /= " << rhs << "\n";
                else out << ind1 << dest << " = " << lhs << " / " << rhs << "\n";
                rt.set(A, {}); break;
            }
            case OP_MOD: {
                std::string dest = reg(f, A, pc, ssa, true);
                std::string lhs = resolveReg(rt, f, B, pc, ssa, true, ind1);
                std::string rhs = resolveReg(rt, f, C, pc, ssa, true, ind1);
                if (dest == lhs && !dest.empty() && dest.find("v") != 0 && dest.find_first_of(".[") != std::string::npos) out << ind1 << dest << " %= " << rhs << "\n";
                else if (dest == lhs && dest.find("v") != 0) out << ind1 << dest << " %= " << rhs << "\n";
                else out << ind1 << dest << " = " << lhs << " % " << rhs << "\n";
                rt.set(A, {}); break;
            }
            case OP_POW: {
                std::string dest = reg(f, A, pc, ssa, true);
                std::string lhs = resolveReg(rt, f, B, pc, ssa, true, ind1);
                std::string rhs = resolveReg(rt, f, C, pc, ssa, true, ind1);
                if (dest == lhs && !dest.empty() && dest.find("v") != 0 && dest.find_first_of(".[") != std::string::npos) out << ind1 << dest << " ^= " << rhs << "\n";
                else if (dest == lhs && dest.find("v") != 0) out << ind1 << dest << " ^= " << rhs << "\n";
                else out << ind1 << dest << " = " << lhs << " ^ " << rhs << "\n";
                rt.set(A, {}); break;
            }

            case OP_ADDK: case OP_SUBK: case OP_MULK: case OP_DIVK: case OP_MODK: case OP_POWK: {
                const char* ops[] = { " + ", " - ", " * ", " / ", " % ", " ^ " };
                const char* compoundOps[] = { " += ", " -= ", " *= ", " /= ", " %= ", " ^= " };
                int idx = stdOp - OP_ADDK;
                
                std::string dest = reg(f, A, pc, ssa, true);
                std::string lhs = reg(f, B, pc, ssa);
                std::string rhs = constStr(f, C, chunk.strings);
                
                // Track literal constants into registers (no inline numerical replacement for math branches)
                if (dest == lhs && !dest.empty() && dest.find("v") != 0 && dest.find_first_of(".[") != std::string::npos) out << ind1 << dest << compoundOps[idx] << rhs << "\n";
                else if (dest == lhs && dest.find("v") != 0) out << ind1 << dest << compoundOps[idx] << rhs << "\n";
                else out << ind1 << dest << " = " << lhs << ops[idx] << rhs << "\n";
                
                rt.set(A, {}); break;
            }

            case OP_CONCAT:
                out << ind1 << reg(f, A, pc, ssa, true) << " = ";
                for (int i = B; i <= C; i++) { if (i > B) out << " .. "; out << resolveReg(rt, f, i, pc, ssa, true, ind1); }
                out << "\n"; rt.set(A, {}); break;
            case OP_NOT:
                out << ind1 << reg(f, A, pc, ssa) << " = not " << resolveReg(rt, f, B, pc, ssa, true, ind1) << "\n"; rt.set(A, {}); break;
            case OP_MINUS:
                out << ind1 << reg(f, A, pc, ssa) << " = -" << resolveReg(rt, f, B, pc, ssa, true, ind1) << "\n"; rt.set(A, {}); break;
            case OP_LENGTH:
                out << ind1 << reg(f, A, pc, ssa) << " = #" << resolveReg(rt, f, B, pc, ssa, true, ind1) << "\n"; rt.set(A, {}); break;

            case OP_NEWTABLE:
                // out << ind1 << reg(f, A, pc, ssa) << " = {}\n"; 
                activeTableBuffers[A].active = true;
                activeTableBuffers[A].declaration = "{}";
                rt.set(A, {}); pc++; break;

            case OP_FORNPREP: {
                std::string init = resolveReg(rt, f, A+2, pc, ssa);
                std::string limit = resolveReg(rt, f, A, pc, ssa);
                std::string step = resolveReg(rt, f, A+1, pc, ssa);
                
                std::string stepStr = "";
                if (step != "1") stepStr = ", " + step;
                
                out << ind1 << "for " << reg(f, A+2, pc, ssa, true) << " = " << init << ", " << limit << stepStr << " do\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_FORNLOOP:
                // Handled by block stack end
                break;
            case OP_FORGPREP:
            case OP_FORGPREP_NEXT:
            case OP_FORGPREP_INEXT: {
                std::string iter = resolveReg(rt, f, A, pc, ssa);
                out << ind1 << "for v" << A+3 << ", v" << A+4 << " in " << iter << " do\n";
                // FORGPREP jumps exactly over the loop body to FORGLOOP
                blockEnds.push_back(pc + D + 2); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_FORGLOOP:
                break;

            case OP_GETVARARGS:
                if (B == 0) out << ind1 << reg(f, A, pc, ssa) << " = nil --[[ ... ]]\n";
                else {
                    out << ind1;
                    for (int i = 0; i < B - 1; i++) { if (i > 0) out << ", "; out << reg(f, A + i, pc, ssa); }
                    out << " = nil --[[ ... ]]\n";
                }
                break;

            case OP_GETTABLEN:
                out << ind1 << reg(f, A, pc, ssa, true) << " = " << asIndexBaseExpr(resolveReg(rt, f, B, pc, ssa, true, ind1)) << "[" << (C + 1) << "]\n";
                rt.set(A, {}); break;
            case OP_SETTABLEN: {
                if (activeTableBuffers.count(B) && activeTableBuffers[B].active) {
                    activeTableBuffers[B].entries.push_back({"", resolveReg(rt, f, A, pc, ssa, true, ind1)});
                } else {
                    std::string target = asIndexBaseExpr(resolveReg(rt, f, B, pc, ssa, true, ind1)) + "[" + std::to_string(C + 1) + "]";
                    emitAssignment(out, ind1, target, resolveReg(rt, f, A, pc, ssa, true, ind1));
                }
                break;
            }

            case OP_SETLIST: {
                if (activeTableBuffers.count(A) && activeTableBuffers[A].active) {
                    int listCount = C > 0 ? C - 1 : 0;
                    for (int i = 0; i < listCount; i++) {
                        activeTableBuffers[A].entries.push_back({"", resolveReg(rt, f, B + i, pc, ssa, true, ind1)});
                    }
                } else {
                    out << ind1 << "-- setlist " << reg(f, A, pc, ssa) << " from " << reg(f, B, pc, ssa) << " count=" << C << "\n";
                }
                pc++; break;
            }
            case OP_DUPTABLE:
                // out << ind1 << reg(f, A, pc, ssa) << " = {--[[template K" << D << "]]}\n"; 
                activeTableBuffers[A].active = true;
                activeTableBuffers[A].declaration = "{--[[template K" + std::to_string(D) + "]]}";
                rt.set(A, {}); break;

            case OP_JUMPXEQKNIL: {
                uint32_t aux = f.instructions[++pc].value;
                out << ind1 << "if " << resolveReg(rt, f, A, pc, ssa, false) << " == nil then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_JUMPXEQKB: {
                uint32_t aux = f.instructions[++pc].value;
                std::string bVal = (aux & 1) ? "true" : "false";
                out << ind1 << "if " << resolveReg(rt, f, A, pc, ssa, false) << " == " << bVal << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_JUMPXEQKN: case OP_JUMPXEQKS: {
                uint32_t raw_aux = f.instructions[++pc].value;
                uint32_t aux = raw_aux & 0xFFFFFF; // Mask upper V6 flags
                out << ind1 << "if " << resolveReg(rt, f, A, pc, ssa, false) << " == " << constStr(f, aux, chunk.strings) << " then\n";
                blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }

            case OP_LOADKX: {
                uint32_t aux = f.instructions[++pc].value;
                out << ind1 << reg(f, A, pc, ssa) << " = " << constStr(f, aux, chunk.strings) << "\n";
                rt.set(A, {});
                break;
            }

            case OP_FASTCALL3: case OP_FASTCALL2: case OP_FASTCALL2K: case OP_COVERAGE: {
                uint32_t aux = f.instructions[++pc].value;
                break;
            }

            case OP_FASTCALL: case OP_FASTCALL1:
                break;

            default:
                if (inst.a() == 0 && inst.b() == 0 && inst.c() == 0 && inst.d() == 0) {
                    rt.set(A, {});
                    break;
                }
                // Unknown opcode: minimal annotation
                out << ind1 << "-- [OP" << (int)inst.opcode() << "] "
                    << reg(f, A, pc, ssa) << " ← ?(B=" << B << ", C=" << C << ", D=" << D << ")\n";
                rt.set(A, {}); // invalidate
                break;
        }
        pc++;
    }

    while (!blockEnds.empty()) {
        indentLevel--;
        out << indent(indentLevel+1) << "end\n";
        blockEnds.pop_back();
    }
    out << ind << "end\n\n";
}

std::string generateCode(const Chunk& chunk, const OpcodeMap& opmap) {
    std::ostringstream out;

    out << "-- ============================================\n";
    out << "-- Luau Decompiled Output\n";
    out << "-- Bytecode v" << (int)chunk.version << " | Types v" << (int)chunk.typesVersion << "\n";
    out << "-- " << chunk.strings.size() << " strings, " << chunk.functions.size() << " functions\n";
    out << "-- Main entry: proto#" << chunk.mainIndex << "\n";
    out << "-- Opcodes mapped: " << opmap.totalMapped << "/" << OP_COUNT << "\n";
    out << "-- ============================================\n\n";

    // Emit interesting strings from the string table
    out << "-- Notable strings in bytecode:\n";
    int shown = 0;
    for (size_t i = 0; i < chunk.strings.size() && shown < 40; i++) {
        auto& s = chunk.strings[i];
        if (s.size() >= 3 && s.size() <= 80) {
            bool interesting = false;
            // Check if it looks like an API name (has uppercase letter, not base64)
            for (char ch : s) if (ch >= 'A' && ch <= 'Z' && s.find('=') == std::string::npos) { interesting = true; break; }
            if (s == "game" || s == "math" || s == "table" || s == "task" || s == "pcall" || s == "pairs") interesting = true;
            if (s == "anticheat" || s == "detection") interesting = true;
            if (interesting) {
                out << "-- [" << i+1 << "] \"" << escapeStr(s) << "\"\n";
                shown++;
            }
        }
    }
    out << "\n";

    for (auto& f : chunk.functions)
        emitFunction(out, chunk, opmap, f, 0);

    return out.str();
}

std::string generateFunctionCode(const Chunk& chunk, const OpcodeMap& opmap, const Function& function) {
    std::ostringstream out;
    emitFunction(out, chunk, opmap, function, 0);
    return out.str();
}

std::string generateFunctionBodyCode(const Chunk& chunk, const OpcodeMap& opmap, const Function& function) {
    std::string full = generateFunctionCode(chunk, opmap, function);
    if (full.empty()) {
        return "";
    }

    std::vector<std::string> lines;
    {
        size_t start = 0;
        while (start <= full.size()) {
            size_t end = full.find('\n', start);
            if (end == std::string::npos) {
                lines.push_back(full.substr(start));
                break;
            }
            lines.push_back(full.substr(start, end - start));
            start = end + 1;
        }
    }

    size_t first = 0;
    while (first < lines.size() && trimWhitespace(lines[first]).empty()) {
        ++first;
    }

    size_t functionHeader = lines.size();
    for (size_t i = first; i < lines.size(); ++i) {
        std::string trimmed = trimWhitespace(lines[i]);
        if (trimmed.rfind("function ", 0) == 0) {
            functionHeader = i;
            break;
        }
    }
    if (functionHeader < lines.size()) {
        first = functionHeader + 1;
    }

    size_t last = lines.size();
    while (last > first && trimWhitespace(lines[last - 1]).empty()) {
        --last;
    }
    if (last > first && trimWhitespace(lines[last - 1]) == "end") {
        --last;
    }

    std::ostringstream body;
    for (size_t i = first; i < last; ++i) {
        std::string line = lines[i];
        if (line.rfind("    ", 0) == 0) {
            line = line.substr(4);
        }
        body << line;
        if (i + 1 < last) {
            body << "\n";
        }
    }
    return body.str();
}
