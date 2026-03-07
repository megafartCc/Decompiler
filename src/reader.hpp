#pragma once
#include <cstdint>
#include <string>
#include <vector>
#include <stdexcept>

// BytecodeReader: reads Luau bytecode binary format
class BytecodeReader {
public:
    BytecodeReader(const uint8_t* data, size_t size);

    uint8_t  readByte();
    bool     readBool();
    int32_t  readInt32();
    uint32_t readUInt32();
    float    readFloat();
    double   readDouble();
    int32_t  readVarInt();       // compressed int encoding
    std::string readString(int len);

    size_t   position() const { return pos_; }
    size_t   size()     const { return size_; }
    bool     eof()      const { return pos_ >= size_; }
    void     skip(size_t n);
    const uint8_t* rawAt(size_t offset) const;

private:
    const uint8_t* data_;
    size_t size_;
    size_t pos_;
};
