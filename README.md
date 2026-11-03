[English](README.md) | [Japanese](README-ja.md)

# smb-rta-lean

Super Mario Bros. speedrun facts, checked in Lean 4.

## Theorems

| theorem | statement | status |
|---|---|---|
| [Fast accel](Theorems/FastAccel.md) | If small Mario stands still on the ground at the start of a level, in a land area with nothing around him, then with a real controller he can reach the running top speed in 34 frames, and cannot in 33 or fewer. | 34 frames: theorem. 33 or fewer impossible: theorem on a relaxed model |
| [TAS fast accel](Theorems/TasFastAccel.md) | Under the same conditions, with Left+Right allowed, Mario can reach the running top speed in 32 frames, and cannot in 31 or fewer. | 32 frames: theorem. 30 or fewer impossible: theorem on a relaxed model. 31 impossible: exhaustive search |

Each page gives the statement, what Lean proves, the assumptions and how they were checked,
and how to reproduce it. A theorem is three files in `Theorems/`: `Name.lean` (the statement
and how it follows from a computation), `Name.md`, `Name-ja.md`.

## Common parts

* [Setup](docs/setup.md) — write `smbrta.json`, put the ROM in place, run `python3 prove.py` (the ROM is not included).
* [Emulator](docs/emulator.md) — the NES in Lean and how it was checked.
* [Method](docs/method.md) — models that run the game code, reachability certificates,
  relaxed models, pruned exact search.

## Layout

```
Smbrta/      the library: NES (Machine, Cpu), movies, symbols, certificates, models
Theorems/    one statement + one page (English, Japanese) per theorem
docs/        common pages
tools/       symbol extraction, test data
Config.lean  where the files outside the repository are (smbrta.json; template smbrta-tmpl.json)
Main.lean    command line (`smbrta`)
prove.py     runs everything, from smbrta.json to the checked theorems
```
