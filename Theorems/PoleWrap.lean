import Theorems.PoleParserEnd
/-!
# The pole's tiles: the scroll counter of 32 px under the strict rule

The field `PoleJoin.Run.parWrap` (until round 30; since round 31 it is gone, see `PoleStrict`) asked, on each frame before the touch's frame, at `UpdScrollVar`: if the screen's left edge moved by `Y` since the frame's start,
then `S + Y < 256` (`PoleJoin.NoWrapP`), with `S` the scroll counter of 32 px at the frame's start. The parser's invariant (`PoleParser.Inv`) is an equation and
does not bound `S`. The weak rule that `PoleParserEnd` proves of each frame (`RuleW`) does not bound it either: it allows a frame that keeps the parser's bytes
while the edge moves (the control byte of the screen's buffers 6 at `UpdScrollVar`, so the parser skips its task), and `S` then grows.

This file proves the bound under the **strict rule** (`Strict`): the edge moves at most 3 px, and the parser's part follows `Parse` with the control byte not 6.
Then `JV`: `N ≤ 7 ∧ S + 3·N < 32` is kept (`jv_strict`): a task is run on every frame with `N ≠ 0`, and 8 frames of at most 3 px move the counter by at most 24 px.
A frame that does not come to `UpdScrollVar` keeps the bytes, and so `JV` (`StrictF`, `jv_strictF`). So `S < 32` at every frame's start, and `NoWrapP` holds when
the edge moves at most 3 px (`noWrapP_of`, `parWrap_of_strict`).

What is not proved here: `JV` at control, that each frame before the touch follows `Strict` (the end walks of `PoleParserEnd` do not tell the path of the control
byte, so they give only `RuleW`), and that the edge moves at most 3 px a frame. Measured by `pole-keep parser`. Since round 31 all three are proved in `PoleStrict`
(with the one-state field `ctlU`: the control byte is not 6 at `UpdScrollVar`).

There is no game data in this file. Page: `1-1/f-6-17-11-PoleWrap.md`.
-/

namespace Smbrta.PoleWrap

open PoleParser
open PipeEntryRule (trace)

/-- **The bound on the counter and the tasks left**: `N ≤ 7` and `S + 3·N < 32` -/
def JV (v : Vals) : Prop := v.n ≤ 7 ∧ v.s + 3 * v.n < 32

/-- **The strict rule of one frame**: the scroll handler moves the counter and the edge by the same `y ≤ 3`, then the parser's part follows `Parse` with the control
byte not 6 -/
def Strict (a b : Vals) : Prop :=
  ∃ c, (∃ y, y ≤ 3 ∧ c.n = a.n ∧ c.col = a.col ∧ c.s = a.s + y ∧ c.edge = a.edge + y) ∧ Parse false c b

/-- the strict rule is a case of the rule -/
theorem rule_of_strict {a b : Vals} (h : Strict a b) : Rule a b := by
  obtain ⟨c, ⟨y, _, e1, e2, e3, e4⟩, hp⟩ := h
  exact ⟨false, c, ⟨y, e1, e2, e3, e4⟩, hp⟩

/-- **The strict rule keeps `JV`** -/
theorem jv_strict {a b : Vals} (h : JV a) (hr : Strict a b) : JV b := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨c, ⟨y, hy, e1, _, e3, _⟩, _, hp⟩ := hr
  simp only [Bool.false_eq_true, if_false] at hp
  by_cases hn : c.n = 0
  · rw [if_pos hn] at hp
    rcases hp with ⟨s1, _, f1, f2, _⟩ | ⟨_, f1, f2, _⟩
    · refine ⟨by omega, ?_⟩
      rw [f1, f2]
      omega
    · refine ⟨by omega, ?_⟩
      rw [f1, f2, hn]
      omega
  · rw [if_neg hn] at hp
    obtain ⟨f1, f2, _⟩ := hp
    refine ⟨by omega, ?_⟩
    rw [f1, f2]
    omega

/-- **A frame by the strict rule, or one that keeps the bytes**: a frame that does not come to `UpdScrollVar` (it ends paused) keeps the parser's bytes and the edge
(`PoleParser.keep_noCutP`, `EdgeStep.keep_noCut`) -/
def StrictF (a b : Vals) : Prop := Strict a b ∨ b = a

/-- `StrictF` keeps `JV` -/
theorem jv_strictF {a b : Vals} (h : JV a) (hr : StrictF a b) : JV b := by
  rcases hr with hr | hr
  · exact jv_strict h hr
  · rw [hr]; exact h

/-- **Frames by the strict rule keep `JV`** -/
theorem jv_frames {v : Nat → Vals} (h0 : JV (v 0)) (hr : ∀ j, StrictF (v j) (v (j + 1))) : ∀ n, JV (v n)
  | 0 => h0
  | n + 1 => jv_strictF (jv_frames h0 hr n) (hr n)

/-- `JV` puts the counter below 32 -/
theorem s_lt {v : Vals} (h : JV v) : v.s < 32 := by
  obtain ⟨_, h2⟩ := h
  omega

variable {sy : Syms} {m0 : Machine}

/-- the counter of `PoleJoin` is that of `PoleParser` -/
theorem parS_eq (m : Machine) : PoleJoin.parSOf sy m0 m = (valsOf (places sy m0) m).s := rfl

/-- **`NoWrapP` from `JV` at the frame's start**, when the edge moved by at most 3 px to `u` -/
theorem noWrapP_of {m u : Machine} (h : JV (valsOf (places sy m0) m))
    (hy : ∀ Y : UInt8, ScrollRule.left16 (ScrollRule.places sy m0) u = (ScrollRule.left16 (ScrollRule.places sy m0) m + Y.toNat) % 65536 → Y.toNat ≤ 3) :
    PoleJoin.NoWrapP sy m0 m u := by
  intro Y hY
  have h1 := hy Y hY
  have h2 := s_lt h
  rw [parS_eq]
  omega

/-- **The field `parWrap` from the strict rule**: on the frames of a run up to the touch's frame (`FrameKeep.Frames`), if `JV` holds at control, each frame
before the touch's frame follows `Strict` from its start to the next frame's start or keeps the bytes (`StrictF`), and at each `UpdScrollVar` of such a frame that
comes to the player's routine the edge moved by at most 3 px, then `NoWrapP` holds there: the statement of `parWrap` (round 30: asked only of a frame that comes to
the player's routine) -/
theorem parWrap_of_strict {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq)
    (h0 : JV (valsOf (places sy m0) (K.all 0)))
    (hS : ∀ n, n + 1 < K.ix g → StrictF (valsOf (places sy m0) (K.all n)) (valsOf (places sy m0) (K.all (n + 1))))
    (hy : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, (trace (K.all n) (K.inp n) k).pc = sy.UpdScrollVar → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      ∀ Y : UInt8, ScrollRule.left16 (ScrollRule.places sy m0) (trace (K.all n) (K.inp n) k) =
        (ScrollRule.left16 (ScrollRule.places sy m0) (K.all n) + Y.toNat) % 65536 → Y.toNat ≤ 3) :
    ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, (trace (K.all n) (K.inp n) k).pc = sy.UpdScrollVar → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      PoleJoin.NoWrapP sy m0 (K.all n) (trace (K.all n) (K.inp n) k) := by
  have hJ : ∀ n, n + 1 < K.ix g → JV (valsOf (places sy m0) (K.all n)) := by
    intro n
    induction n with
    | zero => exact fun _ => h0
    | succ n ih => exact fun hn => jv_strictF (ih (by omega)) (hS n (by omega))
  intro n hn n₀ a1 a2 k hk hf
  exact noWrapP_of (hJ n hn) (hy n hn n₀ a1 a2 k hk hf)

end Smbrta.PoleWrap
