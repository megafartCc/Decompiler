cmake_minimum_required(VERSION 3.16)
project(luau_decompiler LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(luau_decompiler
    src/main.cpp
    src/reader.cpp
    src/deserializer.cpp
    src/disassembler.cpp
    src/automapper.cpp
    src/ir.cpp
    src/cfg.cpp
    src/ssa.cpp
    src/analysis.cpp
    src/ast.cpp
    src/structurer.cpp
)

target_include_directories(luau_decompiler PRIVATE src)
