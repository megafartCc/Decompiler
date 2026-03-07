#include "reader.hpp"
#include <cstring>

BytecodeReader::BytecodeReader(const uint8_t* data, size_t size)
    : data_(data), size_(size), pos_(0) {}

uint8_t BytecodeReader::readByte() {
    if (pos_ >= size_) throw std::runtime_error("Unexpected end of bytecode");
    return data_[pos_++];
}

bool BytecodeReader::readBool() {
    return readByte() != 0;
}

int32_t BytecodeReader::readInt32() {
    if (pos_ + 4 > size_) throw std::runtime_error("Unexpected end of bytecode");
    int32_t val;
    std::memcpy(&val, data_ + pos_, 4);
    pos_ += 4;
    return val;
}

uint32_t BytecodeReader::readUInt32() {
    if (pos_ + 4 > size_) throw std::runtime_error("Unexpected end of bytecode");
    uint32_t val;
    std::memcpy(&val, data_ + pos_, 4);
    pos_ += 4;
    return val;
}

float BytecodeReader::readFloat() {
    if (pos_ + 4 > size_) throw std::runtime_error("Unexpected end of bytecode");
    float val;
    std::memcpy(&val, data_ + pos_, 4);
    pos_ += 4;
    return val;
}

double BytecodeReader::readDouble() {
    if (pos_ + 8 > size_) throw std::runtime_error("Unexpected end of bytecode");
    double val;
    std::memcpy(&val, data_ + pos_, 8);
    pos_ += 8;
    return val;
}


int32_t BytecodeReader::readVarInt() {
    uint32_t result = 0;
    int shift = 0;
    uint8_t byte;
    do {
        byte = readByte();
        result |= (uint32_t)(byte & 0x7F) << shift;
        shift += 7;
    } while (byte & 0x80);
    return (int32_t)result;
}

std::string BytecodeReader::readString(int len) {
    if (pos_ + len > size_) throw std::runtime_error("Unexpected end of bytecode");
    std::string s((const char*)(data_ + pos_), len);
    pos_ += len;
    return s;
}

void BytecodeReader::skip(size_t n) {
    if (pos_ + n > size_) throw std::runtime_error("Unexpected end of bytecode");
    pos_ += n;
}

const uint8_t* BytecodeReader::rawAt(size_t offset) const {
    return data_ + offset;
}
