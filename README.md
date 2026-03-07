# Luau Decompiler

Fast C++ Luau bytecode decompiler with:

- opcode automapping
- IR/CFG/SSA analysis
- structured AST output
- strict structured output mode
- batch tree decompile script

## Install (Windows)

1. Open **Releases**.
2. Download `luau_decompiler-win64.zip`.
3. Extract it.
4. Run `luau_decompiler.exe`.

This repository is release-first. Downloading the release zip is the supported install path.

## Usage

```powershell
.\luau_decompiler.exe [--raw|--cfg|--ir|--ssa|--ast|--strict-structured] <file.luac> [output.lua]
```

Modes:

- `--strict-structured` decompiles and fails if low-level placeholders leak
- `--ast` emits structured AST dump
- `--ssa` emits analyzed SSA dump
- `--ir` emits normalized IR
- `--cfg` emits control-flow graph dump
- `--raw` emits mapped raw disassembly

## Batch Decompile Directory Trees

If you are using the release zip, run:

```powershell
powershell -ExecutionPolicy Bypass -File .\decompile_tree.ps1 `
  -SourceRoot "C:\path\to\dump" `
  -OutputRoot "C:\path\to\out" `
  -Jobs 8 `
  -StrictStructured `
  -AllowRawFallback
```

If you are running from this source repo, run:

```powershell
powershell -ExecutionPolicy Bypass -File tools\decompile_tree.ps1 `
  -SourceRoot "C:\path\to\dump" `
  -OutputRoot "C:\path\to\out" `
  -DecompilerExe "C:\path\to\luau_decompiler.exe" `
  -Jobs 8 `
  -StrictStructured `
  -AllowRawFallback
```

This preserves folder structure and writes JSON manifests for results/errors.
