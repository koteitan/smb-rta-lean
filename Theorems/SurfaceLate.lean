import Theorems.Route

/-!
# Above ground: a late touch of the pole

The frames above ground are read from the machines (`SurfaceFrames.OnFrames.reads`) when the position stays away from the ends of its range. From the position at control
and the bound on the move of each frame, it does so on the first `SurfaceFrames.farN` frames (745 with the machine at control). So the touch's analysis of
`PoleJoin` asks that the touch comes not later than that (`g ≤ farN`). The old field `farLate` of `OnFrames` assumed the range on the later frames.

A touch that comes later needs no analysis of the frames: the frames before it are enough for the bound. The timer ticks at most once in two frames, so each two frames of
play more add at least one frame to the sum `E + T` of `CastleToLevel.sum_ge` (`ticks_add_twice`). From `P3 = 492` frames of play above ground the sum is at least
`1588 + j` with no frame after the touch (`sum_ge_late`), and the rest of `level_ge` is the same (`level_ge_late`). On a run of `Route.Run` this is `level_ge_of_late`:
the touch is not before frame 492 above ground and the castle entry comes after the touch (`PoleJoin.Run.afterTouch`).

So the case `g ≤ farN` is the old route, and the case `farN < g` is this one: `route_1_1` makes the case split, and `farLate` is no longer a field.

There is no game data in this file. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.SurfaceLate

open CastleToLevel (ticks wait ticks_add_two_le ticks_le_self sub_ticks_mono level_ge_of_sum)

/-- **`2k` more frames of play tick the timer at most `k` times more**, when its period is at least two frames -/
theorem ticks_add_twice {q : Nat} (hq : 2 ≤ q) (p : Nat) : ∀ k, ticks q (p + 2 * k) ≤ ticks q p + k
  | 0 => by simp
  | k + 1 => by
    have h1 := ticks_add_twice hq p k
    have h2 := ticks_add_two_le hq (p + 2 * k)
    rw [show p + 2 * (k + 1) = p + 2 * k + 2 by omega]
    omega

/-- **The bound on the sum for a late touch**: with at least 492 frames of play above ground the sum is at least `1588 + j`, for any number of frames `W` from the
touch to the castle entry. As `CastleToLevel.sum_ge`, with `P3 − ticks(P3) ≥ 492 − ticks(240) − 126`. -/
theorem sum_ge_late {q t0 P1 X1 P2 X2 P3 W E T j : Nat} (hq : 2 ≤ q)
    (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hP1 : 368 ≤ P1) (hX1 : 91 ≤ X1) (hP2 : 111 ≤ P2) (hX2 : 282 ≤ X2) (hP3 : 492 ≤ P3)
    (hE : E = P1 + X1 + P2 + X2 + P3 + W + j)
    (hT : t0 ≤ T + (ticks q P1 + ticks q P2 + ticks q P3)) :
    1588 + j ≤ E + T := by
  have hq1 : 1 ≤ q := by omega
  have a1 := sub_ticks_mono hq1 hP1
  have a2 := sub_ticks_mono hq1 hP2
  have a3 := sub_ticks_mono hq1 hP3
  have b1 := ticks_le_self hq1 368
  have b2 := ticks_le_self hq1 111
  have b3 := ticks_le_self hq1 240
  have c1 := ticks_le_self hq1 P1
  have c2 := ticks_le_self hq1 P2
  have c3 := ticks_le_self hq1 P3
  have d : ticks q 492 ≤ ticks q 240 + 126 := ticks_add_twice hq 240 126
  have e := ticks_le_self hq1 492
  omega

/-- **The level does not change before frame 1748, for a late touch**: `CastleToLevel.level_ge` with `sum_ge_late` in place of `sum_ge` -/
theorem level_ge_late {q t0 P1 X1 P2 X2 P3 W E T D L c j : Nat} (hq : 2 ≤ q)
    (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hP1 : 368 ≤ P1) (hX1 : 91 ≤ X1) (hP2 : 111 ≤ P2) (hX2 : 282 ≤ X2) (hP3 : 492 ≤ P3)
    (hE : E = P1 + X1 + P2 + X2 + P3 + W + j)
    (hT : t0 ≤ T + (ticks q P1 + ticks q P2 + ticks q P3))
    (hD : 33 ≤ D)
    (hc : (c + E) % 21 = (3 + j) % 21)
    (hL : E + T + D + 107 + wait c (T + D) ≤ L) : 1748 + j ≤ L :=
  level_ge_of_sum (sum_ge_late hq ht0 hP1 hX1 hP2 hX2 hP3 hE hT) hD hc hL

/-- **The castle entry comes after the touch** (`PoleJoin.Run.afterTouch`), with the machine at control `SurfaceRun.above m0 n` of the private proof. The fraction's check
is stated on `above m0 n`, as the private proof has it, so that no instance of the machine is unfolded. -/
theorem afterTouch_above {sy : Syms} {m0 b : Machine} {vs : List Jump.VS} {n dx dy rows T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat}
    (R : PoleJoin.Run sy m0 b vs ⟨SurfaceRun.above m0 n, dx, dy, rows⟩ T J Nc F Sr ar) (st : SurfaceFrames.Start sy ⟨SurfaceRun.above m0 n, dx, dy, rows⟩ (R.seq 0))
    (hq : PoleJoin.fracCheck sy (SurfaceRun.above m0 n) = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) : R.g < R.c :=
  R.afterTouch st hq hk hc0

section
open Route

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : PipeTransitionAll.Names} {d₁ : PipeChangeEnd.Data}
  {nm₂ nx₂ nmS : PipeTransitionAll.Names} {fc : FlagRule.Ctx} {tc : TitleStart.Ctx}

/-- **The join for a late touch.** As `Route.level_ge_of_parts`, with the touch not before frame 492 above ground and the castle entry after the touch (`hgc`, from
`PoleJoin.Run.afterTouch`) in place of the cases of `PoleJoin.touch_castle`. -/
theorem level_ge_of_late {es es₁ : List Machine} {rt : StepWrites.Rt} (hq : 2 ≤ q) (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hw : 6 ≤ sy.StarFlagDelay.toNat)
    (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) (hsy : fc.sy = sy) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    (h₁ : 368 ≤ R.pipe.E)
    (h₃ : R.room.C + 111 ≤ R.room.E)
    (h₅ : 492 ≤ R.pole.g) (hgc : R.pole.g < R.pole.c) :
    1748 + R.j ≤ R.L := by
  have hc1 := R.change₁ hT₁ hB hK
  have hc2 := R.change₂ hS hT hQ hR hB hK
  have hE := R.hE
  exact level_ge_late (P1 := R.pipe.E) (X1 := R.room.C - R.pipe.E) (P2 := R.room.E - R.room.C) (X2 := R.Cs - R.room.E)
    (P3 := R.pole.g) (W := R.pole.c - R.pole.g) hq ht0 h₁ (by omega) (by omega) (by omega) h₅
    (by omega) (R.hT hB (by omega) (by omega) hgc) (R.hD hF) (R.hc hB (by omega) hgc) (R.hL hF hsy hw)

end

end Smbrta.SurfaceLate
