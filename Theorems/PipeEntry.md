[← Back](../README.md) | [English](PipeEntry.md) | [Japanese](PipeEntry-ja.md)

# Entering the vertical pipe

**Statement.** The collision routine starts the vertical pipe routine exactly when Down is held, Mario is not rising, his
feet are in the landing depth of the pipe's top, and both feet are on the pipe (left foot in its left column, right foot
in its right column). So he has to be at a window of positions, and the position bounds keep him left of it through frame
367. No entry before frame 368.

The names come from the pipe's level object and the collision code. `c` is the pipe's left column on its page, `r` its top
row, `pg` its page, `a_R` and `a_L` the right and left foot's offsets from `x`, `a_Y` the feet's offset from `y`, `d` the landing depth.

```
a_L  = 15 − a_R                     (the feet are symmetric in his 16 px box; tested by pipeCheck)
T_y  = BlockBufferTopY + 16·r       the top of the pipe
x_lo = 16·(c + 1) − a_R             from here the right foot is in the right column
x_hi = 16·(c + 1) − 1 − a_L         up to here the left foot is in the left column
L    = 256·(256·pg + x_lo)          the window's left end as a position, in 1/256 px

rule(x, y, vy, ud)  ⇔  (ud ∧ 4 ≠ 0)  ∧  0 ≤ vy  ∧  T_y ≤ y + a_Y < T_y + d  ∧  x_lo ≤ x ≤ x_hi
```

Here `ud` is `Up_Down_Buttons` and `vy` the signed `Player_Y_Speed`. `vy = 0` counts, so a Mario standing on the pipe enters
when he presses Down: every ground frame runs the landing code. The TAS enters this way.

`P = 256·(256·page + x) + fraction`. `P₂(t)` is the position after the movement of frame `t`, which is what the collision of
frame `t` reads. `P'(t)` is the position after its collision. `Enter t` says that the collision of frame `t` enters the pipe. `P₀` is the
position at the first controllable frame. `N` and `D` are those of [The opening](Opening.md), and `v_top` the running top speed.

```
enters_eq_rule        :  pipeCheck  →  ∀ s ∈ cases,  enters(s) = rule(s)
unchanged_of_not_rule :  pipeCheck, s ∈ cases, ¬rule(s)  →  the routine number is unchanged
window_of_enters      :  pipeCheck, s ∈ cases, enters(s)  →  x_lo ≤ x ≤ x_hi
enter_needs           :  pipeCheck, s ∈ cases, enters(s), 0 ≤ f  →  L ≤ 256·(256·pg + x) + f
no_enter_left         :  pipeCheck, s ∈ cases, 0 ≤ f, 256·(256·pg + x) + f < L  →  ¬enters(s)

no_entry_of_left      :  (∀ t, Enter t → L ≤ P₂(t)),  (∀ t ≤ T, P₂(t) < L)  →  ∀ t ≤ T, ¬Enter t
no_entry_by           :  (∀ t, Enter t → L ≤ P₂(t)),  (∀ t ≤ N, P₂(t) ≤ B),  P'(N) ≤ B,  |v'(N)| ≤ v_top,
                         frames N, N + 1, … consecutive,  B + 16·v_top·(T − N) < L  →  ∀ t ≤ T, ¬Enter t
model_left            :  dist ≤ D in the first N steps,  dist ≤ D + c·k at step N + k,  P₀ + D + c·(T − N) < L
                         →  P₀ + dist < L at every step up to T

pipe_gap (private)    :  P₀ + D + 16·v_top·(367 − N)  <  L  ≤  P₀ + D + 16·v_top·(368 − N)
pipe_model, pipe_model_no_enter, pipe_no_entry (private)  :  no entry up to frame 367, in the model of `opening` and on frames
```

The bound at frame 367 is 112/256 px (0.44 px) short of `L`. At frame 368 it is 528/256 px past it.

Lean: `Theorems/PipeEntry.lean`, private `Proof/PipeEntry.lean` (`pipe_rules`, `pipe_gap`, `pipe_model`, `pipe_model_no_enter`, `pipe_no_entry`).

## How

`pipeCheck` runs the game's own `PlayerBGCollision` with the pipe's two top tiles written into the first block buffer, on every
state of `cases`, and compares the routine number with `rule`. On entering it also checks that he stands at the pipe's height
and that `x` did not change. Otherwise it checks that the routine number did not change. `rule_of_cases` carries this to frames.

The page is counted from the level data: the second bytes with bit 7 set among the object pairs up to and including the pipe's.
`levelOk` checks that the pipe's own object is the kind drawn with the tiles that can be entered, and that no object before it is of
that kind or sets the page directly.

From the rule to the bound: an entering frame has `L ≤ P₂`. Up to frame `N` the bound is the opening's `D`. After `N`,
each frame moves at most `16·v_top` ([Top speed bound](TopSpeed.md)). `pipe_gap` compares the two by `native_decide`.

## Compared with the TAS on the emulator

These are emulator runs, not Lean.

| run | result | agrees with `rule` |
|---|---|---|
| the TAS at frame 368, Down | entry, routine number as in `rule` | at the window's left end |
| Down at each of the frames 362 .. 367 | no entry | left of the window |
| no button from 368, Down at the first frame `x = x_hi` | entry | right end |
| no button from 368, Down at the first frame `x = x_hi + 1` | no entry | past the right end |
| Down + Right at frame 368 | no entry | the frame code clears `ud` (see below) |

The distance of the TAS equals the bound on every frame from 32 to 362, and it is behind the bound after that: on the pipe's top it holds no button and slows down.

## Assumptions (not proved in Lean)

* **The routine is checked alone.** The theorems are about frames (`Frame` of [Top speed bound](TopSpeed.md)) whose collision follows `rule`. In
  Lean this is the hypothesis `hE` of `pipe_no_entry`: an entering frame's state is in `cases`, on the pipe's page, at the position `P₂`. The
  routine is not joined to the rest of the frame.
* **The domain.** `cases` is a union, to keep it small: `x` from a few px left of the window to a few px right of it, heights from a few px above the top to the bottom of
  its top row, standing, every fall speed up to the top one in both air states, the rising speeds of a jump, Down or not, at top speed both ways and stopped;
  every speed with a moving direction that fits, at the ends of the window and of the landing depth, with Up and Down in all ways; the other facing
  directions; a big Mario who is not crouching; and every `x` of the page on a landing with Down. Other states are not run. From the code, the decision reads only the
  button bits, the sign of `vy`, the low nybble of `y` and the two foot tiles, but this is read, not checked.
* **A big crouching Mario** is not in `cases` (there is no symbol for the flag). From the code he takes the same path as a small Mario in the feet check.
* **The block buffer is written by hand** from the level object, not drawn by the game's object code. The first buffer is used, with page 0, because the routine reads
  the page only through its low bit. A real frame on the pipe's page reads the second buffer. Pages with the same low bit share a buffer; that the buffer holds the
  pipe's tiles only while Mario is near that page is read from the code. This is why `hE` says "on the pipe's page".
* **Only this routine starts the vertical pipe**, and only these tiles: read from the code. `levelOk` uses the object format as read from the code's area parser.
* **What Down means.** `rule` is about `Up_Down_Buttons` at the collision. The frame code clears it when Down is pressed on the ground with Left or Right held
  (read from the code; seen at frame 368). This only removes entries.
* **The position bound.** `hopen`, `hB`, `hv`, `hn` of `pipe_no_entry` are hypotheses. Those of [The opening](Opening.md) and of the [Top speed bound](TopSpeed.md) are their source, with their
  assumptions: the first `N` frames follow the model on open flat ground, and later frames follow `Frame`.
* **Not proved: that frame 368 is reached.** `pipe_gap` says only that the bound passes `L` at frame 368. The entry at 368 itself is the TAS on the emulator.

**Files.** `Theorems/PipeEntry.lean`, private `Proof/PipeEntry.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-check     # the routine against the rule, and the bound at 367 and 368, as a program (0 differ)
```
