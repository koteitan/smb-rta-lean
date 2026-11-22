import Theorems.EdgeStep

/-!
# A frame that stops him at the screen's left edge (round 32, 1-1-e-2-10-3-21)

The field `Moves.stop` of `SurfaceFrames` speaks of a frame that moves right at the scroll handler `Q`, ends with the speed 0 and ends at the position of `Q`: the
position at `Q` is at most 1 px past that of the end of the frame before, `a`. On every measured frame of this kind the clamp at the screen's left edge stopped him,
with no push: at `Q` he was at the left edge.

This file has the arithmetic of that case: when at `Q` his pixel is at or left of the screen's left edge, the frame starts at or right of it, and the edge at `Q` is
that of the start, then his pixel at `Q` is at most that of the start, and the position at `Q` is at most 255 above that of the start (`stop_of_edge`).
`SurfaceFrames.OnFrames.stopAt` gives the edge (the frame keeps the edge's two bytes from its start to `Q`), and the field `Moves.stop` is asked only on the other
frames: those where he is right of the edge at `Q`, or the frame starts left of it.
-/

namespace Smbrta.StopEdge

/-- **At or left of the edge at `Q`, at or right of the same edge at `a`**: then the position at `Q` is at most 255 above that of `a`
(P = 256·pixel16 + the fraction) -/
theorem stop_of_edge (sy : Syms) (P : ScrollRule.Places) {a Q : Machine}
    (hq : EdgeStep.pixel16 sy Q ≤ ScrollRule.left16 P Q) (ha : ScrollRule.left16 P a ≤ EdgeStep.pixel16 sy a)
    (he : ScrollRule.left16 P Q = ScrollRule.left16 P a) : posP sy Q ≤ posP sy a + 255 := by
  have hf := (peek Q sy.SprObject_X_MoveForce).toNat_lt
  have hf' := (peek a sy.SprObject_X_MoveForce).toNat_lt
  have hle : EdgeStep.pixel16 sy Q ≤ EdgeStep.pixel16 sy a := by omega
  unfold EdgeStep.pixel16 at hle
  unfold posP
  omega

end Smbrta.StopEdge
