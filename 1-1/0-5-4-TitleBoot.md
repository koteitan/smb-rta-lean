[← Back](README.md) | [English](0-5-4-TitleBoot.md) | [Japanese](0-5-4-TitleBoot-ja.md)

# From power-on to the press of Start

**Claim.** Take a run from power-on. The RAM at power-on is not known: it has no mark of a warm boot, or two of its bytes are 0. No frame before the press has Start or Select. The press is Start, with A or without it, and no other button. It comes on a frame from 32 to 508, counted from power-on. Then the machine after the frame of the press meets the condition `Press` of [From Start on the title to control](0-5-3-TitleStart.md).

**This is a theorem with hypotheses.** They are the fields of `TitleBoot.Run`, all listed below: one state (the machine at power-on) and conditions on single inputs. `Press` was the field `title.press` of the route. It is now the theorem `TitleStart.Begin.press`. The route's field is `title.boot`, of type `TitleBoot.Start`: the run comes from power-on as `TitleBoot.Run` says, or the machine after the press meets `Press` itself. The second case is the old assumption. It stays for the runs outside the class, so that no run is lost.

## What the game does

At power-on the reset code waits for the picture twice. It reads no RAM and stores to no RAM while it waits: this is the first frame. Then it looks at the last bytes of the RAM. If the six digits of the top score are digits and the byte `WarmBootValidation` holds the game's mark, it keeps the last 41 bytes (a warm boot). If not, it clears them too (a cold boot). It clears all other bytes, but for the 160 bytes of the stack's page that no code reads before it writes them.

Then the title screen is made, on frames 3 to 30. The menu runs from frame 31 on. On each frame of the menu the game core runs once with no buttons: the player stands on the first screen of 1-1. So the state of the title changes from frame to frame (the timers, the frame counter, the random bytes, the order of the sprites), but it does not depend on the buttons A, B and the directions.

Start alone, or A with Start, starts the game. A with Start starts in the world of the last game (`ContinueWorld`), which is world 1 after a cold boot. Select changes the number of players and sets the demo's timer again. B changes the world when the world selection is on (`WorldSelectEnableFlag`), which is off after a cold boot. The demo's timer starts at 24 on frame 4 and ticks every 21 frames. It runs out on frame 509: the demo starts, and Start then goes back to the title.

On frame 31 the game core has not run yet. A press on that frame starts the game, but `FetchNewGameTimerFlag` is 2 after it, not 1 as `Press` asks. From frame 32 on it is 1.

Start that is held does not count twice: a press on the frame after a frame with Start does nothing.

## The theorem

`pm n` is the machine `n` frames after power-on, `pi n` its input, `kp` the frame of the press. `P` is the reference at power-on: the cartridge after the reset (the program counter at the reset vector, dot 21 of the frame, the vblank flag set). The mark is the value of `WarmBootValidation` in the reference machine after the press (the reset code writes it).

```
PowerOn(m)    :  ∃ r,  |r| = 2048,  m = P with the RAM r,  and
                    r[WarmBootValidation] ≠ the mark
                 or r[WorldSelectEnableFlag] = r[ContinueWorld] = 0
noSS(i)       :  the input i has no Start and no Select
onlyStart(i)  :  the input i is Start, or A with Start
```

The fields of `TitleBoot.Run(m)`, for the machine `m` after the frame of the press:

```
next     pm(n + 1) = frame(pm n, pi n)
power    PowerOn(pm 0)                         (one state)
quiet    n < kp  ⟹  noSS(pi n)                (single inputs)
start    onlyStart(pi kp)                      (one input)
lo, hi   32 ≤ kp ≤ 508
after    m = pm(kp + 1)
```

The theorems (`title_check` is the check on the ROM, by `native_decide`; the window 32 to 508 is found by a search when the private proof is made, and it is in the context `titleCtx`):

```
TitleBoot.Run.press     :  Run(m)  ⟹  Press(m)
TitleBoot.Start(m)      =  power(Run(m))  |  press(Press(m))
TitleStart.Begin.press  :  Press(tm 0)                  (Begin.boot : TitleBoot.Start(tm 0);  it was the field press)
```

## The proof

**The first frame.** The abstract machine of `TaintRun` asks that the sprite-0 flag is a function of the dot. This is false at power-on: the flag is clear at dot 21. So the first frame is not walked. A tracked run of the reference (`PipeTransitionAll`) reads no byte of the RAM on the first frame, with each of the 64 inputs that have no Start and no Select. So every machine of `PowerOn` ends the first frame with the registers, the PPU state and the dot of the reference. Each step of that run is an opcode that does not store, or `STA` to an address outside the RAM. So no step writes RAM (`StepWrites`), and the RAM after the first frame is the RAM at power-on (`frame_keeps`, `boot_frame`).

**The first row.** It has nine states. One knows that the two bytes are 0. Eight know one bit of `WarmBootValidation`, which is not the mark's bit: a byte that is not the mark differs from it in one bit (`mask_of_ne`). From these eight the reset code's test of the mark fails, so the walk takes the cold boot and all of the RAM is cleared.

**Rows.** From there the abstract machine follows every machine: some bits are known, the others not, and a branch on a bit that is not known goes both ways. Row `j` holds the states when frame `j + 1` begins (`TitleBoot.Row`). The pad of a frame before the press has Start and Select known 0 and the other buttons not known.

* `linkOK`: every end of a row's frame is a state of the next row.
* `pressOK`: with the pad of the press (Start 1, A not known, the others 0), every end of a row's frame meets `Press`.

From frame 32 on the states know all the RAM but 178 bytes (194 after frame 2): the 160 bytes of the stack's page, the bytes that a warm boot keeps (the top score, the scores), and the buttons of the frame before. A row of the menu has two states: the frame begins at dot 0, or at dots 1 to 9. The rows of frames 2, 4 and 5 have 20, 226 and 177 states: the frames before them end inside a loop (of the reset code, of the routine that makes the title). The 508 rows have 1,440 states in all.

The menu tests the buttons twice (Start, then A with Start). With A not known the abstract machine could fail both tests. So the byte of the buttons is read in pieces by the bit of A, and the pieces stay apart.

The search is no part of the proof. `check` walks all 508 rows: 5,041 states of the tables for the frames before the press and 4,208 for the frame of the press. It takes about 3.8 s natively (the search 1.8 s, the first frame 0.2 s, the frames before the press 1.3 s, the frames of the press 0.6 s). With it the check of the ROM `title_check` takes about 8 s (4 s before). The proof is an induction on the frame: `pm (n + 1)` is in row `n` for `n < kp` (`Run.covered`), and the frame of the press from row `kp − 1` gives `Press` (`press_frame`).

## On real runs

`title-boot-check FM2`, exit code 0. Each run starts at power-on. The runs of the class have a RAM of 0, a RAM of bytes from a seed with the two bytes 0 (with the mark and a top score of digits, or not), a RAM of bytes from a seed without the mark, or a RAM of 255 in every byte.

```
group                                                              runs   leaves the title   meets Press
the class                                                           566         566               566
the press on frame 31                                                 2           2                 0
the press on frames 509 to 548                                       40           0                 0
the press after the first demo (frames 1600 to 2200, each 7th)       86          66                66
Select on frames before the press                                   200         200               200
Start with another button on frames before the press                200         109               109
Start with another button on the frame of the press                 100           0                 0
a RAM with the mark, a top score of digits, 1 in the first byte      20          20                 0
```

The movie's first Start is on frame 39. The movie is a run of the class.

## What is not proved

* **Select before the press.** Select sets the demo's timer to 24 again. A row would need one state for each value of the timer: about 6,200 frames to walk, not 477. All 200 such runs measured meet `Press`. For them the condition is still assumed (the second case of `TitleBoot.Start`).
* **Start before the press.** Start with another button does nothing on the title, but the rows ask for no Start. Of 200 such runs, 109 leave the title on the frame of the press, and all of these meet `Press` (assumed, as for Select). In the other 91, Start was held on the frame before: the press does nothing.
* **The press on frame 31.** The game starts, and `Press` is false (`FetchNewGameTimerFlag` is 2). Frame 0 and control are still as the theorems of [From Start on the title to control](0-5-3-TitleStart.md) say (timer 401, phase 2, speed 0). This is a real run outside both cases of `TitleBoot.Start`.
* **The press after frame 508.** The demo runs from frame 509 to 1628, and Start there goes back to the title. After the demo the title comes again: Start on frames 1658 to 2123 meets `Press` (measured: 66 of 66 presses that leave the title), and frame 1657 is like frame 31. The rows stop at 508.
* **A RAM with the mark and a byte of the two not 0.** With 1 in `WorldSelectEnableFlag`, `Press` is false on all 20 runs measured: the game starts in the hard mode.
* **Start with another button on the frame of the press.** The game does not start (0 of 100).
* **A reset.** `P` is the machine at power-on. A run after a reset, or the title after a game over, is not a run of `TitleBoot.Run`.

**Files.** `Theorems/TitleBoot.lean`, `Theorems/TitleStart.lean` (`bootOf`, `Begin.boot`, `Begin.press`), the private `Proof/TitleStart.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta title-boot-check FM2
```
