import Theorems.VertJump

/-!
# Off the block's top: the frames to the floor

The field `Off` of `RoomJoin` (item 1-1-c-7-8) said how a run gets from the block's top to the floor after `t0`, the first frame past the block's right end: a jump
from the block's top whose arc reaches the floor by the entering frame, or stepping off. Its arcs and the frames after `t0` were not tied to the machines. Since round 34
`RoomJoin.RoomRun.off_gap_of` follows the vertical bytes of the real frames after `t0` with the walks of the room's frames (`InRoom.air`, `InRoom.stand`,
`InRoom.jump`). This file has the checks on the ROM it uses, and their arithmetic:

* `offAt`: every takeoff from a stand at the height `y0`, for every stored speed, is the first state of a jump from `y0` (`Jump.arcStart`).
* `slowArcs`: every state of a jump from `y0` whose takeoff was below the air threshold is in the jump state with the fall force of such a takeoff (`slowF`).
* `allLayers`: the states of every layer of a search, each layer once (for `RoomJoin.pipeLands`).
* `above` of an arc (`Jump.Arc.above`): it counts the frames since the last state above the standing height; `above_after` bounds it from a state above it.

The walk of the frames after `t0` from a stand on the block's top is the check `RoomJoin.offB` on `RoomJoin.standFam` (the field `offStand`).

There is no game data in this file. Page: `1-1/c-7-8-2-OffDrop.md`.
-/

namespace Smbrta.OffDrop

open Jump (Arc VS arcStart arcSucc arcCheck arc_spec arc_k arcStart_k groundY standY falling)

/-- `vstep` on the machine of the player's routine with the stored speed 0 (the same as `RoomJoin.vstepR`) -/
abbrev stepR (sy : Syms) (m : Machine) (s : VS) (a : Bool) : VS := VertModel.vstepV sy m (FrameModel.ctrlStack sy m) s a 0

/-- the takeoff from a stand at the height `y` with the stored speed `abs` (the same as `RoomJoin.jumpOffR`) -/
abbrev offR (sy : Syms) (m : Machine) (y abs : UInt8) : VS := VertJump.jumpOff sy m (FrameModel.ctrlStack sy m) y abs

/-- **Near the floor**: he stands on the floor's height, or he is in the air and one frame in the air, with A or not, reaches the floor's height falling -/
def nearB (sy : Syms) (m : Machine) (s : VS) : Bool :=
  (s.st == 0 && decide (s.y.toNat = groundY sy)) ||
    (s.st != 0 && [true, false].any fun a => falling (stepR sy m s a) && decide (groundY sy ≤ (stepR sy m s a).y.toNat))

/-! ## The takeoffs -/

/-- **The check on the ROM of the takeoffs from `y0`**: for every stored speed, the takeoff from a stand at `y0` is the first state of a jump from `y0` -/
def offAt (sy : Syms) (m : Machine) (y0 h : Nat) : Bool :=
  (List.range 256).all fun v => (arcStart sy m y0 h).any fun x => x.s == offR sy m y0.toUInt8 v.toUInt8

theorem offAt_spec {sy : Syms} {m : Machine} {y0 h : Nat} (hc : offAt sy m y0 h = true) (abs : UInt8) :
    ∃ x ∈ arcStart sy m y0 h, x.s = offR sy m y0.toUInt8 abs := by
  have h1 := List.all_eq_true.mp hc abs.toNat (List.mem_range.2 abs.toNat_lt)
  obtain ⟨x, hx, e⟩ := List.any_eq_true.mp h1
  refine ⟨x, hx, ?_⟩
  simpa only [UInt8.ofNat_toNat, beq_iff_eq] using e

/-- the fall forces of the takeoffs from `y0` below the air threshold -/
def slowF (sy : Syms) (m : Machine) (y0 h : Nat) : List UInt8 := ((arcStart sy m y0 h).filter fun x => !x.fast).map (·.s.vfd)

/-- **The check on the ROM of the slow jumps from `y0`**: every state of a jump from `y0` whose takeoff was below the air threshold is in the jump state, with a fall
force of `slowF` -/
def slowArcs (sy : Syms) (m : Machine) (y0 h : Nat) : Bool :=
  let F := slowF sy m y0 h
  arcCheck sy m y0 h fun u => u.fast || (u.s.st == 1 && F.contains u.s.vfd)

theorem slowArcs_spec {sy : Syms} {m : Machine} {y0 h : Nat} (hc : slowArcs sy m y0 h = true) {x u : Arc} (hx : x ∈ arcStart sy m y0 h) {n : Nat}
    (hn : n ≤ Jump.arcFrames) (hr : Cert.Reach (arcSucc sy m h) x n u) (hs : x.fast = false) : u.s.st = 1 ∧ u.s.vfd ∈ slowF sy m y0 h := by
  have h1 := arc_spec hc x hx n u hn hr
  rw [(arc_k hr).2, hs] at h1
  simpa using h1

/-! ## Every layer of a search -/

/-- the states of the layers `0..n` from `L`, each layer once -/
def allLayers {σ : Type} [DecidableEq σ] [Hashable σ] (f : σ → List σ) (L : List σ) : Nat → List σ
  | 0 => L
  | n + 1 => L ++ allLayers f (Cert.nextS f L) n

theorem mem_allLayers {σ : Type} [DecidableEq σ] [Hashable σ] [LawfulHashable σ] {f : σ → List σ} :
    ∀ (n : Nat) {L : List σ} {x u : σ} {k : Nat}, x ∈ L → Cert.Reach f x k u → k ≤ n → u ∈ allLayers f L n
  | 0, _, _, _, _, hx, hr, hk => by
    have : _ = 0 := Nat.le_zero.mp hk
    subst this
    rw [hr.zero]
    exact hx
  | n + 1, L, x, u, k, hx, hr, hk => by
    cases hr with
    | refl => exact List.mem_append_left _ hx
    | @step _ t _ k' ht hrest =>
      exact List.mem_append_right _ (mem_allLayers n (Cert.mem_nextS f L hx ht) hrest (by omega))

/-! ## Paths -/

theorem reach_snoc {σ : Type} {f : σ → List σ} : ∀ {x u v : σ} {n : Nat}, Cert.Reach f x n u → v ∈ f u → Cert.Reach f x (n + 1) v
  | _, _, _, _, .refl _, h => .step h (.refl _)
  | _, _, _, _, .step h1 h2, h => .step h1 (reach_snoc h2 h)

theorem reach_trans {σ : Type} {f : σ → List σ} : ∀ {x w u : σ} {a b : Nat}, Cert.Reach f x a w → Cert.Reach f w b u → Cert.Reach f x (a + b) u
  | _, _, _, _, b, .refl _, h => by simpa using h
  | _, _, _, _, b, @Cert.Reach.step _ _ _ _ _ a h1 h2, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    exact .step h1 (reach_trans h2 h)

/-- before the ground, a jump goes on with A or not: the next state is `vstep` -/
theorem arcSucc_of {sy : Syms} {m : Machine} {h : Nat} {v : Arc} (hn : (falling v.s && decide (groundY sy ≤ v.s.y.toNat)) = false) (a : Bool) :
    ∃ v' ∈ arcSucc sy m h v, v'.s = Jump.vstep sy m v.s a 0 := by
  unfold arcSucc
  rw [hn]
  cases a <;> simp

theorem arcSucc_ne_of {sy : Syms} {m : Machine} {h : Nat} {v : Arc} (hn : (falling v.s && decide (groundY sy ≤ v.s.y.toNat)) = false) : arcSucc sy m h v ≠ [] := by
  unfold arcSucc
  rw [hn]
  simp

/-! ## The counter of the frames since he was above the standing height -/

/-- the counter of the first state: 0 above the standing height, 1 else -/
theorem arcStart_above {sy : Syms} {m : Machine} {y0 h : Nat} {x : Arc} (hx : x ∈ arcStart sy m y0 h) :
    x.above ≤ 1 ∧ (x.s.y.toNat < standY sy h → x.above = 0) := by
  unfold arcStart at hx
  obtain ⟨_, _, h2⟩ := List.mem_map.1 (List.mem_eraseDups.1 hx)
  rw [← h2]
  simp only
  split <;> simp_all

/-- one frame of a jump: the counter grows by one, or it is 0 above the standing height -/
theorem succ_above {sy : Syms} {m : Machine} {h : Nat} {x u : Arc} (hu : u ∈ arcSucc sy m h x) :
    u.above ≤ x.above + 1 ∧ (u.s.y.toNat < standY sy h → u.above = 0) := by
  unfold arcSucc at hu
  split at hu
  · simp at hu
  · simp only [List.mem_map] at hu
    obtain ⟨_, _, h2⟩ := hu
    rw [← h2]
    simp only
    split <;> simp_all

/-- the counter grows by at most one a frame -/
theorem reach_above {sy : Syms} {m : Machine} {h : Nat} : ∀ {x u : Arc} {n : Nat}, Cert.Reach (arcSucc sy m h) x n u → u.above ≤ x.above + n
  | _, _, _, .refl _ => by omega
  | _, _, _, @Cert.Reach.step _ _ _ y _ _ h1 h2 => by
    have e1 := (succ_above h1).1
    have e2 := reach_above h2
    omega

/-- **A state above the standing height bounds the counter**: if the state `j` frames after the takeoff state is above the standing height, the counter `n` frames
after the takeoff state is at most `n − j`; and it is at most `n + 1` -/
theorem above_after {sy : Syms} {m : Machine} {y0 h : Nat} {x u : Arc} (hx : x ∈ arcStart sy m y0 h) {n : Nat} (hr : Cert.Reach (arcSucc sy m h) x n u) :
    u.above ≤ n + 1 ∧ ∀ j w, j ≤ n → Cert.Reach (arcSucc sy m h) x j w → Cert.Reach (arcSucc sy m h) w (n - j) u → w.s.y.toNat < standY sy h → u.above ≤ n - j := by
  refine ⟨?_, fun j w _ h1 h2 hw => ?_⟩
  · have := reach_above hr
    have := (arcStart_above hx).1
    omega
  · have hw0 : w.above = 0 := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rw [h1.zero]
        rw [h1.zero] at hw
        exact (arcStart_above hx).2 hw
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨v, _, hv2⟩ := Cert.Reach.split j' 1 h1
        cases hv2 with
        | step h5 h6 =>
          have e := h6.zero
          subst e
          exact (succ_above h5).2 hw
    have := reach_above h2
    omega

end Smbrta.OffDrop
