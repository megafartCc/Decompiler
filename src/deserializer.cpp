#include "deserializer.hpp"
#include "reader.hpp"
#include "identifier_utils.hpp"
#include <algorithm>
#include <cstdio>
#include <cmath>
#include <cctype>

namespace {
static std::string escapeLuaStringLiteral(const std::string& value) {
    std::string escaped;
    escaped.reserve(value.size() + 8);
    for (unsigned char ch : value) {
        switch (ch) {
            case '\\':
                escaped += "\\\\";
                break;
            case '\"':
                escaped += "\\\"";
                break;
            case '\n':
                escaped += "\\n";
                break;
            case '\r':
                escaped += "\\r";
                break;
            case '\t':
                escaped += "\\t";
                break;
            default:
                if (ch < 32 || ch == 127) {
                    char buf[8];
                    std::snprintf(buf, sizeof(buf), "\\x%02X", static_cast<unsigned int>(ch));
                    escaped += buf;
                } else {
                    escaped.push_back(static_cast<char>(ch));
                }
                break;
        }
    }
    return "\"" + escaped + "\"";
}
} // namespace

// ==========================================
// Constant::toString
// ==========================================
std::string Constant::toString(const std::vector<std::string>& strings) const {
    switch (type) {
        case ConstantType::Nil:     return "nil";
        case ConstantType::Bool:    return boolVal ? "true" : "false";
        case ConstantType::Number: {
            if (std::isnan(numVal))
                return "0/0";
            if (std::isinf(numVal))
                return numVal < 0 ? "-math.huge" : "math.huge";
            // Pretty print integers vs floats
            if (numVal == (double)(int64_t)numVal && std::abs(numVal) < 1e15)
                return std::to_string((int64_t)numVal);
            char buf[64];
            snprintf(buf, sizeof(buf), "%.14g", numVal);
            return buf;
        }
        case ConstantType::String:
            return escapeLuaStringLiteral(strVal);
        case ConstantType::Import: {
            if (importNames.empty()) {
                return "import(...)";
            }
            std::string s;
            if (isLuaIdentifier(importNames[0])) {
                s = importNames[0];
            } else {
                s = "_G[" + escapeLuaStringLiteral(importNames[0]) + "]";
            }
            for (size_t i = 1; i < importNames.size(); i++) {
                if (isLuaIdentifier(importNames[i])) {
                    s += ".";
                    s += importNames[i];
                } else {
                    s += "[";
                    s += escapeLuaStringLiteral(importNames[i]);
                    s += "]";
                }
            }
            return s;
        }
        case ConstantType::Table:
            return "{table:" + std::to_string(tableKeys.size()) + " keys}";
        case ConstantType::Closure:
            return "<closure proto#" + std::to_string(closureIdx) + ">";
        case ConstantType::Vector: {
            char buf[128];
            snprintf(buf, sizeof(buf), "Vector3.new(%.4f, %.4f, %.4f)", vecX, vecY, vecZ);
            return buf;
        }
    }
    return "<?>";
}

// ==========================================
// Deserializer
// ==========================================
static std::string readStringRef(BytecodeReader& r, const std::vector<std::string>& strings) {
    int id = r.readVarInt();
    if (id == 0 || id > (int)strings.size()) return "";
    return strings[id - 1];
}

static std::vector<std::string> readStringTable(BytecodeReader& r) {
    int count = r.readVarInt();
    std::vector<std::string> strings;
    strings.reserve(count);
    for (int i = 0; i < count; i++) {
        int len = r.readVarInt();
        strings.push_back(r.readString(len));
    }
    return strings;
}

static Constant readConstant(BytecodeReader& r, const std::vector<std::string>& strings,
                              const std::vector<Constant>& constants) {
    Constant c;
    uint8_t rawType = r.readByte();
    uint8_t type = rawType;
    static int remapWarnCount = 0;

    // Some protected/custom chunks encode constant tags with high bits.
    // Preserve low-bit semantic tag as a best-effort recovery path.
    if (type > 7 && type != 9 && type != 64) {
        type = type & 7;
        if (remapWarnCount < 32) {
            fprintf(stderr, "[*] Remapped constant type %u -> %u\n", (unsigned)rawType, (unsigned)type);
            remapWarnCount++;
        }
    }

    c.type = (ConstantType)type;

    switch (c.type) {
        case 64:
        case 9:
        case ConstantType::Nil:
            break;
        case ConstantType::Bool:
            c.boolVal = r.readBool();
            break;
        case ConstantType::Number:
            c.numVal = r.readDouble();
            break;
        case ConstantType::String:
            c.strVal = readStringRef(r, strings);
            break;
        case ConstantType::Import: {
            c.importId = r.readUInt32();
            int count = (int)(c.importId >> 30);
            if (count > 0 && ((c.importId >> 20) & 1023) < constants.size()) {
                auto& k = constants[(c.importId >> 20) & 1023];
                if (k.type == ConstantType::String) c.importNames.push_back(k.strVal);
            }
            if (count > 1 && ((c.importId >> 10) & 1023) < constants.size()) {
                auto& k = constants[(c.importId >> 10) & 1023];
                if (k.type == ConstantType::String) c.importNames.push_back(k.strVal);
            }
            if (count > 2 && ((c.importId >> 0) & 1023) < constants.size()) {
                auto& k = constants[(c.importId >> 0) & 1023];
                if (k.type == ConstantType::String) c.importNames.push_back(k.strVal);
            }
            break;
        }
        case ConstantType::Table: {
            int size = r.readVarInt();
            for (int i = 0; i < size; i++)
                c.tableKeys.push_back(r.readVarInt());
            break;
        }
        case ConstantType::Closure:
            c.closureIdx = r.readVarInt();
            break;
        case ConstantType::Vector:
            c.vecX = r.readFloat();
            c.vecY = r.readFloat();
            c.vecZ = r.readFloat();
            c.vecW = r.readFloat();
            break;
        default:
            throw std::runtime_error("Unknown constant type: " + std::to_string(type));
    }
    return c;
}

static Function readFunction(BytecodeReader& r, const std::vector<std::string>& strings,
                              uint8_t version, uint8_t typesVersion) {
    Function f;
    f.maxStackSize = r.readByte();
    f.numParams    = r.readByte();
    f.numUpvalues  = r.readByte();
    f.isVararg     = r.readByte() == 1;

    if (version >= 4) {
        f.flags = r.readByte();
        int typesSize = r.readVarInt();
        f.typeInfoSize = typesSize;
        f.hasTypeInfo = typesSize > 0;
        if (typesSize > 0) {
            size_t start = r.position();
            f.typeInfoBlob.resize((size_t)typesSize);
            const uint8_t* raw = r.rawAt(start);
            std::copy(raw, raw + typesSize, f.typeInfoBlob.begin());
            r.skip(typesSize);
        }

        // Handle types version specific data (skip)
        if (typesVersion == 1) {
            // Already skipped via typesSize above
        }
    }

    // Instructions (uint32 each)
    {
        int count = r.readVarInt();
        f.instructions.reserve(count);
        for (int i = 0; i < count; i++) {
            RawInstruction inst;
            inst.value = r.readUInt32();
            f.instructions.push_back(inst);
        }
    }

    // Constants
    {
        int count = r.readVarInt();
        f.constants.reserve(count);
        for (int i = 0; i < count; i++) {
            f.constants.push_back(readConstant(r, strings, f.constants));
        }
    }

    // Child proto indices
    {
        int count = r.readVarInt();
        for (int i = 0; i < count; i++)
            f.childProtos.push_back(r.readVarInt());
    }

    f.lineDefined = r.readVarInt();
    f.debugName   = readStringRef(r, strings);

    // Line info
    if (r.readBool()) {
        f.hasLineInfo = true;
        f.lineGapLog = r.readByte();
        int instrCount = (int)f.instructions.size();
        int intervals = ((instrCount - 1) >> f.lineGapLog) + 1;

        f.lineOffsets.resize(instrCount);
        uint8_t lastOffset = 0;
        for (int i = 0; i < instrCount; i++) {
            lastOffset += r.readByte();
            f.lineOffsets[i] = lastOffset;
        }

        f.absLineInfo.resize(intervals);
        int32_t lastLine = 0;
        for (int i = 0; i < intervals; i++) {
            lastLine += r.readInt32();
            f.absLineInfo[i] = lastLine;
        }
    }

    // Debug info
    if (r.readBool()) {
        int sizeVars = r.readVarInt();
        for (int i = 0; i < sizeVars; i++) {
            LocalVarInfo v;
            v.name    = readStringRef(r, strings);
            v.startPc = r.readVarInt();
            v.endPc   = r.readVarInt();
            v.slot    = r.readByte();
            f.locals.push_back(v);
        }
        int sizeUpvals = r.readVarInt();
        for (int i = 0; i < sizeUpvals; i++)
            f.upvalueNames.push_back(readStringRef(r, strings));
    }

    return f;
}

Chunk deserialize(const uint8_t* data, size_t size) {
    BytecodeReader r(data, size);
    Chunk chunk;
    bool tolerantMode = false;

    uint8_t rawVersion = r.readByte();
    chunk.version = rawVersion;

    // Version 0 means error message follows
    if (chunk.version == 0) {
        std::string err;
        while (!r.eof()) err += (char)r.readByte();
        throw std::runtime_error("Bytecode contains error: " + err);
    }
    
    // Bypass version check since the official compiler uses v255 (which maps to v6)
    if (chunk.version == 255) chunk.version = 6;
    else if (chunk.version > 6) {
        // Non-standard streams sometimes encode flags in high bits.
        uint8_t coerced = chunk.version & 7;
        if (coerced == 0) coerced = 3;
        fprintf(stderr, "[*] Coerced non-standard bytecode version %u -> %u\n",
            (unsigned)chunk.version, (unsigned)coerced);
        chunk.version = coerced;
        tolerantMode = true;
    }

    fprintf(stderr, "[*] Bytecode version: %d\n", chunk.version);

    chunk.typesVersion = 0;
    if (chunk.version >= 4)
        chunk.typesVersion = r.readByte();

    // String table
    chunk.strings = readStringTable(r);
    fprintf(stderr, "[*] Loaded %zu strings\n", chunk.strings.size());

    // Types version 3: userdata remapping (skip)
    if (chunk.typesVersion == 3) {
        uint8_t idx = r.readByte();
        while (idx != 0) {
            r.readVarInt();
            idx = r.readByte();
        }
    }

    // Functions
    int funcCount = r.readVarInt();
    fprintf(stderr, "[*] Loading %d functions\n", funcCount);
    chunk.functions.reserve(funcCount);
    for (int i = 0; i < funcCount; i++) {
        try {
            Function f = readFunction(r, chunk.strings, chunk.version, chunk.typesVersion);
            f.id = i;
            chunk.functions.push_back(std::move(f));
        } catch (const std::exception& ex) {
            if (!tolerantMode) {
                throw;
            }
            fprintf(stderr, "[*] Tolerant stop while reading function %d/%d: %s\n", i, funcCount, ex.what());
            break;
        }
    }

    if (!r.eof()) {
        try {
            chunk.mainIndex = r.readVarInt();
        } catch (const std::exception& ex) {
            if (!tolerantMode) {
                throw;
            }
            fprintf(stderr, "[*] Tolerant main index fallback: %s\n", ex.what());
            chunk.mainIndex = chunk.functions.empty() ? 0 : (int)chunk.functions.size() - 1;
        }
    } else {
        chunk.mainIndex = chunk.functions.empty() ? 0 : (int)chunk.functions.size() - 1;
    }

    if (!chunk.functions.empty() && (chunk.mainIndex < 0 || chunk.mainIndex >= (int)chunk.functions.size())) {
        if (tolerantMode) {
            chunk.mainIndex = (int)chunk.functions.size() - 1;
        }
    }

    fprintf(stderr, "[*] Main function index: %d\n", chunk.mainIndex);
    fprintf(stderr, "[*] Bytes remaining: %zu\n", r.size() - r.position());

    return chunk;
}
