[English](README.md) | [Japanese](README-ja.md)

# smb-rta-lean

Super Mario Bros. speedrun facts, checked in Lean 4.

## Theorems

| theorem | statement | status |
|---|---|---|
| [Fast accel](Theorems/FastAccel.md) | If small Mario stands still on the ground at the start of a level, in a land area with nothing around him, then with a real controller he can reach the running top speed in 34 frames, and cannot in 33 or fewer. | 34 frames: theorem. 33 or fewer impossible: theorem on a relaxed model |
| [TAS fast accel](Theorems/TasFastAccel.md) | Under the same conditions, with Left+Right allowed, Mario can reach the running top speed in 32 frames, and cannot in 31 or fewer. | 32 frames: theorem. 30 or fewer impossible: theorem on a relaxed model. 31 impossible: exhaustive search |
| [Top speed bound](Theorems/TopSpeed.md) | Away from platforms, vines, pipes and similar objects, Mario never moves right by more than 2.5 px per frame; running at top speed and touching nothing moves exactly 2.5 px per frame. | per-routine checks: theorems; the routines being the only writers: from the disassembly |
| [Reach](Theorems/Reach.md) | From the start of 1-1, in n frames Mario never moves right by more than 2.5·n − 23.25 px (n ≥ 22) under the conditions of the top speed bound, and 2.5·n − 38.375 px (n ≥ 28) in the open area. | theorems under the assumptions of the top speed bound and of the horizontal frame; the TAS inputs move 2.5·n − 41.94 px |
| [The opening](Theorems/Opening.md) | From the start of 1-1, on open flat ground, Mario never moves right by more than 2.5·n − 41.94 px in n ≥ 32 frames; the TAS opening moves exactly that far. | theorem under the assumptions of the horizontal frame and of the jump lengths (search of about 4 s) |
| [The air speed cap](Theorems/AirCap.md) | Below 1.5625 px/frame Mario stays below it in the air, and can pass it only on a ground frame. So K air frames then n frames move him at most 1.5·K px plus a bound that depends only on n. | theorem under the assumptions of the horizontal frame (check of about 4 s) |
| [The height of a jump](Theorems/Jump.md) | From every takeoff speed and every way of pressing A: when Mario rises at the height of a direct grab of the flagpole, how soon he can land on a block, and how soon he can fall back to the ground. | theorem on the game's movement routine, without collisions (about 8 s) |
| [Grabbing the pole from below](Theorems/PoleGrab.md) | Beside the flagpole's base block Mario is pushed back, at most 1 px forward per frame, so where he can land is bounded and the hop adds nothing: too far behind at a given frame, he cannot grab the pole in time. | theorem about frames that follow the collision rules; the rules are checked against the routine on every state near the block (about 4 s) |

Each page gives the statement, what Lean proves, the assumptions and how they were checked,
and how to reproduce it. A theorem is three files in `Theorems/`: `Name.lean` (the statement
and how it follows from a computation), `Name.md`, `Name-ja.md`.

## Common parts

* [Setup](docs/setup.md) — write `smbrta.json`, put the ROM in place, run `python3 prove.py` (the ROM is not included).
* [Emulator](docs/emulator.md) — the NES in Lean and how it was checked.
* [The 1-1 route](docs/route-1-1.md) — work in progress toward a lower bound on the frame 1-2 starts (per segment: theorem, emulator check, open).
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
