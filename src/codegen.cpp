#include "codegen.hpp"
#include <algorithm>
#include <sstream>
#include <iomanip>
#include <cstdio>
#include <unordered_map>
#include <optional>




struct RegVal {
    enum Kind { UNKNOWN, NUMBER, STRING, UPVAL, TABLE_ACCESS, FUNC_RESULT, IMPORT, METHOD_CALL };
    Kind kind = UNKNOWN;
    double numVal = 0;
    std::string strVal;
    int upvalIdx = -1;
    std::string repr; 
};

struct RegTracker {
    RegVal regs[256];
    void clear() { for (auto& r : regs) r = {}; }
    void set(int r, RegVal v) { if (r >= 0 && r < 256) regs[r] = v; }
    RegVal get(int r) const { return (r >= 0 && r < 256) ? regs[r] : RegVal{}; }
};

struct SSATracker {
    std::unordered_map<int, int> versions; 
    std::unordered_map<int, std::unordered_map<int, std::string>> semanticNames; 

    
    int next(int slot) {
        return ++versions[slot];
    }

    
    int current(int slot) const {
        auto it = versions.find(slot);
        return it != versions.end() ? it->second : 0;
    }
    
    
    void setSemanticName(int slot, int ver, const std::string& name) {
        semanticNames[slot][ver] = name;
    }
    
    
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




static std::string reg(const Function& f, int idx, int pc, const SSATracker& ssa, bool isAssignment = false) {
    
    if (idx < f.numParams) return "p" + std::to_string(idx);

    
    for (auto& lv : f.locals) {
        if (lv.slot == idx && (pc < 0 || (pc >= lv.startPc && pc < lv.endPc))) {
            int ver = isAssignment ? const_cast<SSATracker&>(ssa).next(idx) : ssa.current(idx);
            if (ver == 0) return lv.name; 
            return lv.name + "_" + std::to_string(ver);
        }
    }

    
    int ver = isAssignment ? const_cast<SSATracker&>(ssa).next(idx) : ssa.current(idx);
    
    
    std::string semantic = ssa.getSemanticName(idx, ver);
    if (!semantic.empty()) {
        return semantic;
    }

    
    if (ver == 0) return "v" + std::to_string(idx); 
    return "v" + std::to_string(idx) + "_" + std::to_string(ver);
}

static std::string upval(const Function& f, int idx) {
    if (idx >= 0 && idx < (int)f.upvalueNames.size()) {
        if (!f.upvalueNames[idx].empty()) return f.upvalueNames[idx];
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


static std::string escapeStr(const std::string& s, int maxLen = 60) {
    std::string out;
    for (char ch : s) {
        if (out.size() >= (size_t)maxLen) { out += "..."; break; }
        if (ch >= 32 && ch < 127) out += ch;
        else { char buf[8]; snprintf(buf, sizeof(buf), "\\x%02X", (uint8_t)ch); out += buf; }
    }
    return out;
}







struct TableBuffer {
    bool active = false;
    std::string declaration;
    std::vector<std::pair<std::string, std::string>> entries; 
    bool isListOnly = true;

    
    std::string formatInline(const std::string& indentStr) const {
        if (entries.empty()) return "{}";
        
        std::ostringstream out;
        out << "{\n";
        std::string innerInd = indentStr + "    ";
        
        for (size_t i = 0; i < entries.size(); ++i) {
            out << innerInd;
            if (!entries[i].first.empty()) {
                
                bool needsBrackets = false;
                for (char c : entries[i].first) {
                    if (!std::isalnum(c) && c != '_') { needsBrackets = true; break; }
                }
                if (std::isdigit(entries[i].first[0])) needsBrackets = true;
                
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


static std::unordered_map<int, TableBuffer> activeTableBuffers;


static std::string resolveReg(const RegTracker& rt, const Function& f, int slot, int pc, const SSATracker& ssa, bool allowLiteral = true, const std::string& indentStr = "") {
    
    
    if (activeTableBuffers.count(slot) && activeTableBuffers[slot].active) {
        std::string folded = activeTableBuffers[slot].formatInline(indentStr);
        activeTableBuffers.erase(slot); 
        return folded;
    }
    
    auto& rv = rt.regs[slot];
    if (!allowLiteral && (rv.kind == RegVal::NUMBER || rv.kind == RegVal::STRING)) return reg(f, slot, pc, ssa);
    if (!rv.repr.empty()) return rv.repr;
    return reg(f, slot, pc, ssa);
}


static std::string strAnnotation(const Chunk& chunk, int idx) {
    
    if (idx > 0 && idx <= (int)chunk.strings.size()) {
        auto& s = chunk.strings[idx - 1]; 
        if (s.size() > 0 && s.size() <= 40)
            return " --[[ \"" + escapeStr(s, 30) + "\" ]]";
    }
    if (idx >= 0 && idx < (int)chunk.strings.size()) {
        auto& s = chunk.strings[idx]; 
        if (s.size() > 0 && s.size() <= 40)
            return " --[[ \"" + escapeStr(s, 30) + "\" ]]";
    }
    return "";
}




static void emitFunction(std::ostringstream& out, const Chunk& chunk, const OpcodeMap& opmap,
                          const Function& f, int indentLevel) {
    std::string ind = indent(indentLevel);
    std::string ind1 = indent(indentLevel + 1);

    
    std::string name = f.debugName.empty() ? "(anonymous)" : f.debugName;
    out << ind << "-- ======== proto#" << f.id << " \"" << name << "\"";
    if (f.lineDefined > 0) out << " (line " << f.lineDefined << ")";
    out << " ========\n";

    
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

    out << ind << "function " << (f.debugName.empty() ? "" : f.debugName)
        << "(" << params << ")\n";

    RegTracker rt;
    rt.clear();

    int pc = 0;
    int numInst = (int)f.instructions.size();
    std::vector<bool> emitted(numInst, false);
    
    
    std::vector<int> blockEnds;

    
    std::unordered_map<std::string, int> nameCounts;
    
    
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

        
        
        
        
        bool collapsed = false;
        if (stdOp == OP_GETUPVAL && pc + 2 < numInst) {
            auto& next1 = f.instructions[pc + 1];
            auto& next2 = f.instructions[pc + 2];
            int op1 = opmap.lookup(next1.opcode());
            int op2 = opmap.lookup(next2.opcode());

            
            if (op1 == OP_LOADN && op2 == OP_GETTABLE) {
                int tableReg = A;
                int idxReg = next1.a();
                int destReg = next2.a();
                int16_t numVal = next1.d();

                if (next2.b() == tableReg && next2.c() == idxReg) {
                    std::string upvName = upval(f, B);
                    std::string expr = upvName + "[" + std::to_string(numVal) + "]";

                    
                    
                    if (pc + 5 < numInst) {
                        auto& n3 = f.instructions[pc + 3];
                        auto& n4 = f.instructions[pc + 4];
                        auto& n5 = f.instructions[pc + 5];
                        int op3 = opmap.lookup(n3.opcode());
                        int op4 = opmap.lookup(n4.opcode());
                        int op5 = opmap.lookup(n5.opcode());

                        
                        if (op3 == OP_GETUPVAL && op4 == OP_LOADN && op5 == OP_GETTABLE) {
                            int tr2 = n3.a();
                            int ir2 = n4.a();
                            int dr2 = n5.a();
                            int16_t nv2 = n4.d();
                            if (n5.b() == tr2 && n5.c() == ir2) {
                                std::string expr2 = upval(f, n3.b()) + "[" + std::to_string(nv2) + "]";

                                
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
                                            << expr << " â†’ " << expr2 << " â†’ " << expr3 << "\n";
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

        
        
        
        switch (stdOp) {
            case OP_RETURN:
                if (B == 0) out << ind1 << "return ...\n";
                else if (B == 1) out << ind1 << "return\n";
                else {
                    out << ind1 << "return ";
                    for (int i = 0; i < B - 1; i++) {
                        if (i > 0) out << ", ";
                        out << resolveReg(rt, f, A + i, pc, ssa, true, ind1);
                    }
                    out << "\n";
                }
                break;

            case OP_PREPVARARGS:
                break; 

            case OP_LOADNIL: {
                out << ind1 << reg(f, A, pc, ssa) << " = nil\n";
                RegVal rv; rv.kind = RegVal::UNKNOWN; rv.repr = "nil";
                rt.set(A, rv);
                break;
            }

            case OP_LOADB: {
                std::string val = B ? "true" : "false";
                
                if (C != 0) out << ind1 << "-- skip " << C << " instructions\n";
                RegVal rv; rv.kind = RegVal::NUMBER; rv.repr = val; rt.set(A, rv);
                break;
            }

            case OP_LOADN: {
                
                RegVal rv; rv.kind = RegVal::NUMBER; rv.numVal = D; rv.repr = std::to_string(D);
                rt.set(A, rv);
                break;
            }
            case OP_GETGLOBAL: {
                uint32_t aux = f.instructions[++pc].value;
                std::string glb = constStr(f, aux, chunk.strings);
                
                RegVal rv; rv.kind = RegVal::UNKNOWN; rv.repr = glb; rt.set(A, rv);
                break;
            }
            case OP_SETGLOBAL: {
                uint32_t aux = f.instructions[++pc].value;
                out << ind1 << constStr(f, aux, chunk.strings) << " = " << resolveReg(rt, f, A, pc, ssa, true, ind1) << "\n";
                break;
            }

            case OP_LOADK: {
                std::string val = constStr(f, D, chunk.strings);
                
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
                std::string imp = "import(...)";
                
                
                
                for (const auto& c : f.constants) {
                    if (c.type == ConstantType::Import && c.importId == aux) {
                        imp = c.toString(chunk.strings);
                        break;
                    }
                }

                out << ind1 << reg(f, A, pc, ssa, true) << " = " << imp << "\n";
                
                
                RegVal rv; rv.kind = RegVal::UNKNOWN; rv.repr = imp; rt.set(A, rv);
                break;
            }

            case OP_GETTABLE: {
                std::string expr = resolveReg(rt, f, B, pc, ssa, true, ind1) + "[" + resolveReg(rt, f, C, pc, ssa, true, ind1) + "]";
                
                RegVal rv; rv.kind = RegVal::TABLE_ACCESS; rv.repr = expr; rt.set(A, rv);
                break;
            }
            case OP_SETTABLE: {
                if (activeTableBuffers.count(B) && activeTableBuffers[B].active) {
                    
                    std::string keyExpr = resolveReg(rt, f, C, pc, ssa, true, ind1); 
                    
                    activeTableBuffers[B].isListOnly = false;
                    activeTableBuffers[B].entries.push_back({keyExpr, resolveReg(rt, f, A, pc, ssa, true, ind1)});
                } else {
                    out << ind1 << resolveReg(rt, f, B, pc, ssa, true, ind1) << "[" << resolveReg(rt, f, C, pc, ssa, true, ind1) << "] = " << resolveReg(rt, f, A, pc, ssa, true, ind1) << "\n";
                }
                break;
            }
            case OP_GETTABLEKS: {
                uint32_t aux = f.instructions[++pc].value;
                std::string key = constStr(f, aux, chunk.strings);
                
                std::string expr = resolveReg(rt, f, B, pc, ssa, true, ind1) + "." + key;
                
                RegVal rv; rv.kind = RegVal::TABLE_ACCESS; rv.repr = expr; rt.set(A, rv);
                break;
            }

            case OP_SETTABLEKS: {
                std::string key = "???";
                if (pc + 1 < numInst) {
                    uint32_t aux = f.instructions[pc + 1].value;
                    if (aux < f.constants.size() && f.constants[aux].type == ConstantType::String)
                        key = f.constants[aux].strVal;
                }
                
                if (activeTableBuffers.count(B) && activeTableBuffers[B].active) {
                    
                    activeTableBuffers[B].isListOnly = false;
                    activeTableBuffers[B].entries.push_back({key, resolveReg(rt, f, A, pc, ssa, true, ind1)});
                } else {
                    out << ind1 << resolveReg(rt, f, B, pc, ssa, true, ind1) << "." << key << " = " << resolveReg(rt, f, A, pc, ssa, true, ind1) << "\n";
                }
                pc++;
                break;
            }

            case OP_NAMECALL: {
                std::string method = "???";
                if (pc + 1 < numInst) {
                    uint32_t aux = f.instructions[pc + 1].value;
                    if (aux < f.constants.size() && f.constants[aux].type == ConstantType::String)
                        method = f.constants[aux].strVal;
                }
                std::string obj = resolveReg(rt, f, B, pc, ssa, true); 
                RegVal rv1; rv1.kind = RegVal::METHOD_CALL; rv1.repr = obj + ":" + method;
                rt.set(A, rv1);
                pc++;
                break;
            }

            case OP_CALL: {
                std::string func = resolveReg(rt, f, A, pc, ssa, true); 
                std::string argsStr;
                std::string firstArgLiterals; 
                bool isMethod = (rt.get(A).kind == RegVal::METHOD_CALL);
                if (B == 0) {
                    argsStr = "...";
                } else {
                    int startArg = isMethod ? 2 : 1;
                    for (int i = startArg; i < B; i++) {
                        if (i > startArg) argsStr += ", ";
                        std::string arg = resolveReg(rt, f, A + i, pc, ssa);
                        argsStr += arg;
                        if (i == startArg) firstArgLiterals = arg; 
                    }
                }
                
                
                if (C > 1 && !firstArgLiterals.empty()) {
                    std::string cleanArg = firstArgLiterals;
                    
                    if (cleanArg.size() >= 2 && cleanArg.front() == '"' && cleanArg.back() == '"') {
                        cleanArg = cleanArg.substr(1, cleanArg.size() - 2);
                    }
                    
                    std::string inferredName = "";
                    if (func == "Instance.new") {
                        inferredName = cleanArg; 
                    } else if (func.find(":GetService") != std::string::npos) {
                        inferredName = cleanArg; 
                    }
                    
                    
                    if (!inferredName.empty()) {
                        int currentVersionForRet = ssa.current(A);
                        int count = ++nameCounts[inferredName];
                        std::string finalName = inferredName;
                        if (count > 1) finalName += "_" + std::to_string(count); 
                        
                        
                        ssa.setSemanticName(A, currentVersionForRet + 1, finalName);
                    }
                }

                if (C == 0) {
                    if (pc + 1 < numInst) {
                        const auto& nextInst = f.instructions[pc + 1];
                        int nextOp = opmap.lookup(nextInst.opcode());
                        if (nextOp == OP_RETURN && nextInst.a() == A && nextInst.b() == 0) {
                            out << ind1 << "return " << func << "(" << argsStr << ")\n";
                            rt.set(A, {});
                            pc++;
                            break;
                        }
                    }
                    out << ind1 << reg(f, A, pc, ssa) << ", ... = " << func << "(" << argsStr << ")\n";
                } else if (C == 1) {
                    out << ind1 << func << "(" << argsStr << ")\n";
                } else {
                    std::string results;
                    for (int i = 0; i < C - 1; i++) {
                        if (i > 0) results += ", ";
                        results += reg(f, A + i, pc, ssa, true);
                        
                        
                        if (activeTableBuffers.count(A+i)) {
                            results += " = " + activeTableBuffers[A+i].formatInline(ind1);
                            activeTableBuffers.erase(A+i);
                        }
                    }
                    out << ind1 << results << " = " << func << "(" << argsStr << ")\n";
                }
                
                for (int i = 0; i < (C == 0 ? 10 : C - 1); i++) rt.set(A + i, {});
                break;
            }

            case OP_NEWCLOSURE: {
                std::string proto = "???";
                if (D >= 0 && D < (int)f.childProtos.size()) proto = "proto#" + std::to_string(f.childProtos[D]);
                out << ind1 << reg(f, A, pc, ssa, true) << " = function() -- " << proto << "\n";
                break;
            }

            case OP_DUPCLOSURE: {
                if (D >= 0 && D < (int)f.constants.size() && f.constants[D].type == ConstantType::Closure) {
                    out << ind1 << reg(f, A, pc, ssa, true) << " = function() -- closure â†’ proto#" << f.constants[D].closureIdx << "\n";
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
                    blockEnds.push_back(pc + D + 1); indentLevel++; ind1 = indent(indentLevel + 1);
                } else out << ind1 << "goto [" << (pc + D + 1) << "]\n";
                break;

            case OP_JUMPBACK:
                
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
                
                break;
            case OP_FORGPREP:
            case OP_FORGPREP_NEXT:
            case OP_FORGPREP_INEXT: {
                std::string iter = resolveReg(rt, f, A, pc, ssa);
                out << ind1 << "for v" << A+3 << ", v" << A+4 << " in " << iter << " do\n";
                
                blockEnds.push_back(pc + D + 2); indentLevel++; ind1 = indent(indentLevel + 1);
                break;
            }
            case OP_FORGLOOP:
                break;

            case OP_GETVARARGS:
                if (B == 0) out << ind1 << reg(f, A, pc, ssa) << ", ... = ...\n";
                else {
                    out << ind1;
                    for (int i = 0; i < B - 1; i++) { if (i > 0) out << ", "; out << reg(f, A + i, pc, ssa); }
                    out << " = ...\n";
                }
                break;

            case OP_GETTABLEN:
                out << ind1 << reg(f, A, pc, ssa, true) << " = " << resolveReg(rt, f, B, pc, ssa, true, ind1) << "[" << (C + 1) << "]\n";
                rt.set(A, {}); break;
            case OP_SETTABLEN: {
                if (activeTableBuffers.count(B) && activeTableBuffers[B].active) {
                    activeTableBuffers[B].entries.push_back({"", resolveReg(rt, f, A, pc, ssa, true, ind1)});
                } else {
                    out << ind1 << resolveReg(rt, f, B, pc, ssa, true, ind1) << "[" << (C + 1) << "] = " << resolveReg(rt, f, A, pc, ssa, true, ind1) << "\n";
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
                uint32_t aux = raw_aux & 0xFFFFFF; 
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
                
                out << ind1 << "-- [OP" << (int)inst.opcode() << "] "
                    << reg(f, A, pc, ssa) << " â† ?(B=" << B << ", C=" << C << ", D=" << D << ")\n";
                rt.set(A, {}); 
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

    
    out << "-- Notable strings in bytecode:\n";
    int shown = 0;
    for (size_t i = 0; i < chunk.strings.size() && shown < 40; i++) {
        auto& s = chunk.strings[i];
        if (s.size() >= 3 && s.size() <= 80) {
            bool interesting = false;
            
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
