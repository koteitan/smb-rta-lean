[← Back](README.md) | [English](0-6-4-2-1-HurryFrame.md) | [Japanese](0-6-4-2-1-HurryFrame-ja.md)

# The frame that starts the hurry-up music

**Claim.** Take one whole frame that starts in control or in the player's entrance, with the hurry-up music off. If each of its instructions meets one condition on the machine, the frame ends with the music off, or with the timer at 100 or less. If it also ends with control, it ends with the music in the queue, or at the start of a frame in control with the music off: so the next frame starts as the first one did. A frame that starts in control ends with control, if none of its instructions writes the routine, the mode or the task by its address.

**This theorem has hypotheses.** They are conditions on this one frame: how it starts (`Start`), a condition on each instruction (`CleanM`), and for `frame_ctl` that no instruction writes the routine, the mode or the task by its address (`CtlStore`). They are checked on real frames. They are not proved for every run.

`HurryMusic.Run` had the field `music`: a frame that starts the music begins with the timer at 100 or less. It is now a theorem (`HurryMusic.Run.music`), from this walk. The timer is now read when the frame ends, not when it begins. `HurryMusic.Run` also had the field `start` on the frame that starts the music. It is now a theorem (`HurryMusic.Run.startAt`) by induction over the frames in control before it, from the same walk (`frame_startC`). The field `ctl` (each of these frames ends with control) is now a theorem too, from the walk with the stores of the three bytes cut (`frame_ctl`) and the hypothesis `noStore` on single instructions.

## What the game does

* The game queues the hurry-up music in its timer routine (`RunGameTimer`). The routine reads the timer's three digits. If they are 1, 0, 0, it puts the music into the event music queue. Then it lowers the digits by one, to 0, 9, 9.
* The sound routine runs earlier in the frame. It copies the queue into its buffer, and it sets the tempo's adder only when it loads the hurry-up music.
* So within one frame the music can appear only in the queue, and only from the timer routine. On a death the game queues the death music, which is another bit.

## The theorem

`m` is the machine when the frame begins and `i` its input. `frame(m, i)` is the machine when the frame ends, and `tr(j)` the machine after `j` instructions. `v` is the number of the hurry-up music; it has one bit.

```
off(m)    :  EventMusicQueue(m) & v = 0  ∧  EventMusicBuffer(m) & v = 0  ∧  NoteLengthTblAdder(m) = 0
timer(m)  =  100 · d₀ + 10 · d₁ + d₂            (the three digits, as CastleToLevel.timerOf)
Start(m)  :  FrameStart of PipeWrites (the idle loop, the stack, the dot, the mode and its task), with the routine of control
             or of the entrance, and the bytes of DigitModifier 0
CleanM(m) :  PipeWrites.Clean, with the music bytes, the digits and the bytes of DigitModifier among the protected bytes;
             but at the digits routine's stores through an index, and at the two stores into DigitModifier through an index,
             the digits and the bytes of DigitModifier are not protected

frame_music :  check = true,  Start(m),  off(m),  ∀ j, CleanM(tr(j))   ⟹   off(frame(m, i))  ∨  timer(frame(m, i)) ≤ 100
frame_start :  check = true,  Start(m),  off(m),  ∀ j, CleanM(tr(j)),  ctl(frame(m, i))   ⟹
               EventMusicQueue(frame(m, i)) & v ≠ 0  ∨  (Start(frame(m, i))  ∧  off(frame(m, i)))
frame_startC : the same, with Startᶜ(frame(m, i)) (the start of a frame in control) in place of Start(frame(m, i))

Startᶜ(m)    :  Start(m) with the routine of control
CtlStore(m)  :  the instruction at m.pc writes the routine, the mode or the task by its address (zero page or absolute)
frame_ctl    :  ctl_check = true,  Startᶜ(m),  off(m),  ∀ j, CleanM(tr(j)),  ∀ j, ¬ CtlStore(tr(j))   ⟹   ctl(frame(m, i))
ctl_of_start :  ctl_check = true,  Startᶜ(m)   ⟹   ctl(m)
```

`ctl(m)` says that `m` has control: the routine of control, the game's mode and the game core.

The frame may start with the routine of the entrance: on the first frame after a pipe, the entrance routine ends and the routine of control runs in the same frame, before the timer routine.

The six bytes of `DigitModifier` are what the digits routine adds to the digits. The game sets them just before it calls the routine, and the routine clears them. So they are 0 when a frame starts.

## The walk

The walk is the abstract machine of `TaintRun`, over one whole frame, as in `PipeWrites` and `FrameKeep`. A byte has known bits. The walk starts with the music bits off and the six bytes 0. The digits are not known.

* **The digits.** At the timer routine's load of the first digit into `Y`, the walk splits the digit into its 256 values. At its load of the second digit, the second and the third are split into 0 or their lowest bit 1. So on the path that queues the music the digits are known, 1, 0, 0, and the routine lowers them to 0, 9, 9.
* **The death music.** The game queues one more than a register: `X` holds the player's status, or `Y` the flag of the death music. At those two loads the byte is split into 0 or its lowest bit 1, so the queued value is known.
* **The digits routine.** It writes the digits and the six bytes through an index. On real frames it does so on the frame that starts the music. So at these stores the walk forgets the digits and the six bytes when the index is not known. `CleanM` asks there only that the store does not hit the other protected bytes.
* At the end of every path the music bits are off, or the digits are known and their value is at most 100 (`finM`).
* Also at the end of every path (`finS`): the music's bit is known to be set in the queue, or the path is at the start of the next frame (`FrameKeep.endOK`: the idle loop, the stack, the dot, the NMI, the joypad's strobe) with the six bytes known 0 and the music bits off. With the routine, the mode and the task of a machine with control, this is `Start` again (`frame_start`).

The check (`music_check`, by `native_decide`): the search finds a table of 75,437 states in 1,321,935 steps. The check walks every state of the table and the 4 start states (control or entrance, just before or just after the frame's first event), with both ends (`finS`). It takes 3 to 9 seconds natively, depending on the load of the machine (3.9 seconds with `finS`).

## A frame in control ends in control

`frame_ctl` is the same walk with two changes (as `FrameKeep.walkKC` for the frames above ground):

* It starts only from the start of a frame in control (`startsC`: just before or just after the frame's first event).
* A path stops at an instruction that writes the routine, the mode or the task by its address (`storesTo`). A real frame does not come there: that is the hypothesis `¬ CtlStore`. These three bytes are protected, so under `CleanM` a store through an index or a pointer does not change them either.
* At the end of every path the three bytes are known, with the values of control (`FrameKeep.knownAll` of `FrameKeep.guardK`). So the frame ends with control (`FrameKeep.ctl_of_known`).

The walk of the music and this walk are one walk `walkM` with two parameters: the bytes whose stores stop a path (none for the music), and the end condition (`finS` for the music).

The check (`hurry_ctl_check`, by `native_decide`, `ctlCheckOf`): the search finds a table of 5,519 states in 81,100 steps, with no failure. The check takes 0.33 s in a program. `Proof/HurryFrame.lean` builds in 5.7 to 8.4 seconds with both checks, depending on the load of the machine.

## On real frames

`hurry-check FM2`, exit code 0. The runs are those of [Runs with the hurry-up music](0-6-4-HurryMusic.md): the timer written near 100 on 12 frames of the movie, then the movie's inputs, or random inputs with pauses.

```
frames that start the music                   108  (the movie's inputs 56, random inputs 52)
  routine at their start                      control 94, entrance 14
  Start                                       108 of 108
  music bits off at the start                 108 of 108
  instructions with CleanM                    521,286 of 521,286
  timer at the end                            99 on all 108
  ending in the idle loop                     108 of 108
the movie's frames in control or entrance     833 frames, Start 833, off 833, CleanM on 4,034,601 of 4,034,601 instructions
frames from b to the music's frame            7,451 in the 108 runs; of the instructions of those that begin with control, CtlStore 0
```

## What is not proved

* `Start` and `CleanM` on the frame that starts the music. They are conditions on one frame and its instructions, of the same kind as those of `PipeWrites` and `FrameKeep`, checked above. In `HurryMusic.Run`, `Start` on that frame is now a theorem by `frame_start`, from the first frame of the frames in control before it ([runs with the hurry-up music](0-6-4-HurryMusic.md)). `Start` on that first frame is a theorem too: frame 1 from the press of Start on the title, the last frame of a change from the rows of the change ([the last frame of a change](0-6-4-2-2-2-1-HurryStart.md)).
* That the stores of the digits routine are the only stores through an index that hit the digits or the six bytes: this is part of `CleanM`, checked above.
* `¬ CtlStore` on each instruction of a frame in control before the music (`HurryMusic.Run.noStore`). It is a condition on single instructions, checked above. A frame that starts a change of area or a death writes the routine by its address. So in a run of `HurryMusic.Run` the frame `b` comes after the last such frame before the music.

**Files.** `Theorems/HurryFrame.lean` (`CleanM`, `Start`, `CleanAt`, `finS`, `frame_music`, `frame_start`, `frame_startC`, `ctlCheckOf`, `frame_ctl`, `ctl_of_start`), the private `Proof/HurryFrame.lean` (`music_check`, `hurry_ctl_check`). The symbol `Eng_PlayerEntrance` (`tools/smb-symbols.txt`).

**Reproduce.**
```
.lake/build/bin/smbrta music-check            # the search and the check, as a program
.lake/build/bin/smbrta hurry-ctl-check        # the walk of a frame in control with the stores cut, as a program
.lake/build/bin/smbrta hurry-check FM2        # the conditions on real frames
```
