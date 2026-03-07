# Luau Decompiler

Fast C++ Luau bytecode decompiler with:

- opcode automapping
- IR/CFG/SSA analysis
- structured AST output
- strict structured output mode
- batch tree decompile script

## Install

### Option 1: Download Release (Recommended)

1. Go to **Releases**.
2. Download the latest `luau_decompiler-win64.zip`.
3. Extract and run `luau_decompiler.exe`.

### Option 2: Build From Source

Requirements:

- CMake 3.16+
- Visual Studio Build Tools (C++17) on Windows

Build:

```powershell
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --config Release
```

Binary output:

`build\Release\luau_decompiler.exe`

## Usage

```powershell
luau_decompiler.exe [--raw|--cfg|--ir|--ssa|--ast|--strict-structured] <file.luac> [output.lua]
```

Modes:

- `--strict-structured` decompiles and fails if low-level placeholders leak
- `--ast` emits structured AST dump
- `--ssa` emits analyzed SSA dump
- `--ir` emits normalized IR
- `--cfg` emits control-flow graph dump
- `--raw` emits mapped raw disassembly

## Batch Decompile Directory Trees

Use:

`tools/decompile_tree.ps1`

Example:

```powershell
powershell -ExecutionPolicy Bypass -File tools\decompile_tree.ps1 `
  -SourceRoot "C:\path\to\dump" `
  -OutputRoot "C:\path\to\out" `
  -DecompilerExe ".\build\Release\luau_decompiler.exe" `
  -Jobs 8 `
  -StrictStructured `
  -AllowRawFallback
```

This preserves folder structure and writes JSON manifests for results/errors.
