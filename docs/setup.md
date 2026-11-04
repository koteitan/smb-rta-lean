[← Back](../README.md) | [English](setup.md) | [Japanese](setup-ja.md)

# Setup

Write a config file, put the ROM in place, and run `prove.py`. It does everything else and
ends with the list of theorems Lean has checked. Run the commands inside this repository.

## 1. Write the config file

Copy the template to `smbrta.json` outside the repository, in this repository's directory or
any directory above it (it is searched upward from the current directory), and set the paths.
Relative paths are relative to the directory of `smbrta.json`.

```bash
cp smbrta-tmpl.json ../smbrta.json
```

| key | what | |
|---|---|---|
| `rom` | a Super Mario Bros. (JU) ROM, iNES, mapper 0 | you put it there (step 2) |
| `disasm` | the disassembly `SMBDIS.ASM` | downloaded if missing |
| `proofProject` | a private Lean project for the generated proofs (they embed the ROM) | made |
| `syms` | the symbol file | made |
| `nestestRom`, `nestestLog`, `miniRom` | test data | made |

Instead of the search, you can give `--config FILE` or set `$SMBRTA_CONFIG`.

## 2. Put the ROM in place

Copy your Super Mario Bros. (JU) ROM to the path of `rom`. It is not in this repository.

```bash
cp /path/to/your/smb.nes PATH_OF_rom
```

## 3. Run prove.py

```bash
python3 prove.py
```

It stops with a message at the first step that fails. The proofs take about 2 minutes;
`python3 prove.py --full` also runs the full-search proofs (about 20 minutes more).
The build command is `lake build`; set `SMBRTA_BUILD` to use another one.

## What prove.py does

1. `tools/setup.py`:
   * checks the ROM: headerless PRG+CHR MD5 `8e3630186e35d477231bf8fd50e54cdd`;
   * downloads the disassembly if missing, and checks its SHA-256;
   * makes the private Lean project at `proofProject`: `lakefile.toml` (which requires this
     repository), `lean-toolchain`, the directory `Proof/`;
   * fetches the test data: the nestest CPU test ROM and log, the homemade test cartridge;
   * makes the symbol file: the values the model needs (RAM addresses, two code points, a few
     values), taken from the ROM and the disassembly. Every instruction of the disassembly is
     checked against the ROM (10,691 instructions), so a wrong address is caught.
2. builds this repository;
3. checks the emulator against the nestest log (`smbrta nestest`);
4. generates the private proof files: `Proof/Rom.lean` (the ROM, the symbols, the 1-1 start)
   and the theorem files (`smbrta gen-rom`, `smbrta gen-proofs`). Each theorem file only
   applies `native_decide` to a statement in `Theorems/`;
5. builds the private project: here Lean checks the theorems;
6. lists the checked theorems.

The files in `proofProject` contain the ROM: keep them private.

## The disassembly

`SMBDIS.ASM`, "A Comprehensive Super Mario Bros. Disassembly" by doppelganger, turns the ROM's
machine code back into 6502 assembly with names for RAM variables and routines
(`Player_X_Speed`, `PlayerCtrlRoutine`, …). It is used only to look up the addresses of the
names in `tools/smb-symbols.txt`. The tested file is in the gist `1wErt3r/4048722`
(<https://gist.github.com/1wErt3r/4048722>), https://gist.githubusercontent.com/1wErt3r/4048722/raw/7e8e9777a53a2f94fd968e79c891445a97a8ddde/SMBDIS.ASM, SHA-256 `e5c17c42783f430029ab90aa37c73d51c2c320898e533b3ff196dad38c50ae42`.
Another version still works if its names are the same.
