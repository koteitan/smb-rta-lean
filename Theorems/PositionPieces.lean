import Theorems.ScreenClamp

/-! Additive position effects of ordinary intervals and complete calls.
A partition of a whole frame into these pieces is still a hypothesis, not a
new Run field. -/
namespace Smbrta.PositionPieces
open FrameModel

/-- An interval of ordinary instructions keeps position; actual writes,
including stores of an unchanged value, must avoid all three position bytes. -/
theorem ordinary_interval {sy : Syms} {R : Machine} :
    ∀ k, (∀ j, j < k →
      ∀ a ∈ [sy.Player_X_Position,sy.Player_PageLoc,sy.SprObject_X_MoveForce],
        I a ∉ StepWrites.stepLocs (stepN j R)) →
      posP sy (stepN k R) = posP sy R
  | 0,_ => rfl
  | k+1,h => by
    rw [stepN_succ,ImpedePosition.ordinary_step (h k (by omega))]
    exact ordinary_interval k (fun j hj => h j (by omega))

/-- A complete collision push supplies an exact additive piece, away from
position wrap. The arbitrary caller stack is respected. -/
theorem impede_piece {sy : Syms} {m0 R : Machine}
    (hc : ImpedePosition.check sy m0 = true) (g : Good (Rom.of m0) R)
    (pc : R.pc = sy.ImpedePlayerMove)
    (hl : 256 ≤ posP sy R) (hr : posP sy R+256 < 0x1000000) :
    ∃ k, k ≤ 65 ∧ Good (Rom.of m0) (stepN k R) ∧
      (stepN k R).pc = ImpedePosition.returnPc R ∧ (stepN k R).s = R.s+1+1 ∧
      posP sy (stepN k R) = posP sy R +
        256*ImpedePosition.delta (R.ram.get! (ImpedePosition.sites sy m0).side)
          (peek R sy.Player_X_Speed) ∧ InFrameN (Rom.of m0) R k := by
  obtain ⟨k,hk,hg,hpc,hsp,_,_,_,hm,ifr⟩ := ImpedePosition.routine_return hc g pc
  exact ⟨k,hk,hg,hpc,hsp,ImpedePosition.exact_of_mod hl hr hm,ifr⟩

/-- A complete clamp supplies its exact live-edge target. No distance of the
live edge from the frame-start position is assumed implicitly. -/
theorem clamp_piece {sy : Syms} {m0 R : Machine}
    (hc : ScreenClamp.check sy m0 = true) (g : Good (Rom.of m0) R)
    (pc : R.pc = (ScreenClamp.places sy m0).entry) (hy : R.y ∈ [0,(1 : UInt8)])
    (range : 0 ≤ ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) R R.y ∧
      ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) R R.y < 0x1000000) :
    ∃ k, k ≤ 37 ∧ Good (Rom.of m0) (stepN k R) ∧
      (stepN k R).pc = ImpedePosition.returnPc R ∧ (stepN k R).s = R.s+1+1 ∧
      posP sy (stepN k R) = ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) R R.y ∧
      InFrameN (Rom.of m0) R k := by
  obtain ⟨k,hk,hg,hpc,hsp,_,hm,ifr⟩ := ScreenClamp.clamp_return hc g pc hy
  exact ⟨k,hk,hg,hpc,hsp,ScreenClamp.exact_target range hm,ifr⟩

/-- Exact finite composition. The per-piece equalities are explicit:
ordinary_interval supplies zero, impede_piece supplies a signed pixel, and
clamp_piece supplies target minus the clamp-entry position. -/
theorem position_sum (sy : Syms) (states : Nat → Machine) (effect : Nat → Int) :
    ∀ n, (∀ j, j < n →
      posP sy (states (j+1)) = posP sy (states j)+effect j) →
      posP sy (states n) = posP sy (states 0)+((List.range n).map effect).sum
  | 0,_ => by simp
  | n+1,h => by
    have old := position_sum sy states effect n (fun j hj => h j (by omega))
    have last := h n (by omega)
    simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,
      List.sum_cons,List.sum_nil]
    omega

/-- The same identity on chosen cuts of the actual frame trace. Constructing
these cuts and proving each local contract still has to be done for a frame. -/
theorem trace_sum {sy : Syms} {M : Machine} {input : UInt8}
    (cuts : Nat → Nat) (effect : Nat → Int) {n a b : Nat}
    (first : cuts 0 = a) (last : cuts n = b)
    (pieces : ∀ j, j < n →
      posP sy (PipeEntryRule.trace M input (cuts (j+1))) =
        posP sy (PipeEntryRule.trace M input (cuts j))+effect j) :
    posP sy (PipeEntryRule.trace M input b)-posP sy (PipeEntryRule.trace M input a) =
      ((List.range n).map effect).sum := by
  have h := position_sum sy (fun j => PipeEntryRule.trace M input (cuts j)) effect n pieces
  dsimp only at h
  rw [first,last] at h
  omega

/-- Any number of later pixel pushes adds to the last clamp target. This
does not bound their count, signs, or the live target relative to frame start. -/
theorem pushes_after_clamp {sy : Syms} (states : Nat → Machine) (d : Nat → Int)
    {target : Int} (start : posP sy (states 0) = target) :
    ∀ n, (∀ j, j < n →
      posP sy (states (j+1)) = posP sy (states j)+256*d j) →
      posP sy (states n) = target+256*((List.range n).map d).sum
  | 0,_ => by simpa using start
  | n+1,h => by
    have old := pushes_after_clamp states d start n (fun j hj => h j (by omega))
    have last := h n (by omega)
    simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,
      List.sum_cons,List.sum_nil]
    omega

end Smbrta.PositionPieces
