[← Back](../README.md) | [English](emulator.md) | [Japanese](emulator-ja.md)

# The emulator

A NES is written in Lean and the game's own code runs on it.

* `Smbrta/Cpu.lean` — the 6502 (2A03): all official opcodes and the stable unofficial ones,
  cycle-exact including page-cross and branch penalties.
* `Smbrta/Machine.lean` — 2 KiB RAM, NROM cartridge, controller, OAM DMA stall, and the PPU
  only as timing: vblank flag, NMI, sprite-0 hit. Nothing is drawn: the game logic does not
  depend on the picture. Optional RAM access tracking (bytes read before written, bytes
  written) is used to find what a frame carries.
* `Smbrta/Movie.lean` — FCEUX `.fm2` movies, frames from vblank to vblank.

**Checks.**

| check | result |
|---|---|
| nestest log (registers, flags, cycles) | all 8991 lines match |
| homemade test cartridge (frames, NMI, controller), also as a `native_decide` theorem | matches |
| two TAS movies from power-on (`smbrta run`) | both reach the axe of 8-4 |
| a second, independent emulator with a real PPU | same level changes and same clear frame |

**Trust.** `native_decide` trusts the Lean compiler (`Lean.ofReduceBool`).
