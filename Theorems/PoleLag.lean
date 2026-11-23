import Theorems.PoleLate
/-!
# The pole's tiles: the parser's lag may grow up to 157 px

Rounds 31 and 32 carried `JV` (`N ≤ 7 ∧ S + 3·N < 32`, `PoleWrap.JV`) over the frames up to the touch's frame (`PoleStrict.invJ_onFrames`), and the field
`PoleJoin.Run.ctlU` asked, at each `UpdScrollVar` of a frame that comes to the player's routine, the screen buffers' control byte not 6 or `S + 3·N < 32` there.
`S + 3·N` is the parser's lag: the scroll counter of 32 px plus 3 px for each task left.

What the parser's invariant and the walks need of the lag is less than `JV`:
* no wrap of the counter at `UpdScrollVar`: `S + Y < 256` with the scroll's amount `Y ≤ 3`;
* for `N = 0`, a new column starts only with `32 ≤ S < 160` at `UpdScrollVar` (the code compares the counter with 32 as a signed byte, so from 160 on it starts
  none, and the strict walks of `PoleParserEnd` know the new column only for `S` in 32 ‥ 159).

`JY := N ≤ 7 ∧ S + 3·N < 157` gives both (`S < 157`, so `S + Y < 160`), and every frame keeps it (`PoleStrict.step_strict`):
* with the control byte not 6 (the strict forms): with `N ≥ 1`, `N` goes to `N − 1` and `S` keeps the amount, so the lag does not grow; with `N = 0` and
  `S ≥ 32` at `UpdScrollVar`, `N` goes to 7 and `S` loses 32, so `S + 3·N` ends below `160 − 32 + 21 = 149`;
* with the control byte 6, when the lag at `UpdScrollVar` is below 157 (`jy_weak`): the weak forms keep `N` or take one off and keep `S`, or start a new
  column, which takes 32 off `S` and sets `N` to 7.

So `ctlU` asks the control byte not 6 only where the lag at `UpdScrollVar` is 157 or more (round 35: `ctlU` is gone, `PoleJoin.Run.ctl6`). At control `JV` holds (`PoleStrict.jv₀`), so `JY` does
(`jy_of_jv`). On real runs the lag at `UpdScrollVar` stayed below 35 (`pole-keep parser`).

There is no game data in this file. Page: `1-1/f-6-17-15-PoleLag.md`.
-/

namespace Smbrta.PoleLag

open PoleParser

/-- **The parser's lag below 157**: `N ≤ 7` and `S + 3·N < 157` -/
def JY (v : Vals) : Prop := v.n ≤ 7 ∧ v.s + 3 * v.n < 157

/-- `JV` gives `JY` -/
theorem jy_of_jv {v : Vals} (h : PoleWrap.JV v) : JY v := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by omega⟩

/-- `JY` puts the counter below 157 -/
theorem s_lt {v : Vals} (h : JY v) : v.s < 157 := by
  obtain ⟨_, h2⟩ := h
  omega

/-- **`JY` after the parser's weak part**: `N` at most 7 and the lag below 157 at `UpdScrollVar`, and at the end `N` kept or less and `S` kept -/
theorem jy_weak {n s n' s' : Nat} (hn : n ≤ 7) (hl : s + 3 * n < 157) (h : n' ≤ n) (hs : s' = s) : n' ≤ 7 ∧ s' + 3 * n' < 157 := by
  omega

/-- **`JY` after a new column**: `N` set to 7 and 32 taken off a counter below 160 -/
theorem jy_col {s n' s' : Nat} (hs : 32 ≤ s) (hs2 : s < 160) (hn : n' = 7) (h : s' = s - 32) : n' ≤ 7 ∧ s' + 3 * n' < 157 := by
  omega

end Smbrta.PoleLag
