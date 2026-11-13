import Theorems.RoomMap
import Theorems.StepWrites
import Theorems.VertAir

/-!
# The vertical bytes of a frame in the room

A frame of the room changes the vertical bytes (the height, the vertical speed and its fractions, the forces, the jump's origin, the state, and A and B) in the movement routine,
and in the collision routine when he lands or stands. Here two walks of one whole frame of the room (the abstract machine of `RoomMap`, which knows the room's bytes and the target
of every store) show where:
* `walkA`: from the frame's start to the player's routine no step writes these bytes, nor the jump's halt value and A and B of the frame before, nor the horizontal bytes; the
  frame comes to the player's routine at most once, and not at its end (`finR`): so it comes there before its end (`before_R`, `hbytes_at_R`).
* `walkB`: when the frame comes to the scroll handler in the air (the state 1 or 2) and rising (the vertical speed negative), no step from there to the frame's end writes these bytes
  (`after_Q`).
Each walk carries one bit (`AS.spent`, which nothing reads when the counter is not followed): in `walkA` it says that the frame has come to the player's routine, in `walkB` that it
came to the scroll handler in the air and rising. The bit is set by splitting the state at that place (`Ph.zone`).

There is no game data in this file. Page: `1-1/c-7-5-1-RoomVert.md`.
-/

namespace Smbrta.RoomVert

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop)
open ScreenPage (Places SiteOK PlacesOK CfgS clampS preS weaken coverS RoomCond startsR MaskOK Aids SearchS routeS)

/-! ## A walk with one bit -/

/-- a walk's bit: where it splits a state, what it asks of a state, what it asks of each piece -/
structure Ph where
  zone : AS → List AS
  pre : AS → Bool
  ok : AS → Bool

/-- the table has a state that covers `B`, with the same list `log` -/
def coverV (C : CfgS) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D && B.log == D.log
    | none => false

/-- from `A`, step by step as `RoomMap`'s walk, until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts. Before each step the
state is split by `ScreenPage`'s pieces, then by `zone`. The counter is never followed; the bit `spent` and the list `log` stay through a step. -/
def walkV (Z : Ph) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => Z.pre A && !A.rk && (preS C.P (clampS C.P A)).all fun A' => A'.spent == A.spent && A'.log == A.log && !A'.rk && (Z.zone A').all fun A₁ =>
    Z.ok A₁ && !A₁.rk && A₁.k == A.k && (RoomMap.stepT C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      B.spent == A₁.spent && B.log == A₁.log && !B.rk && (weaken C B).log == B.log &&
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverV C (clampS C.P (weaken C B))) || walkV Z C n (weaken C B)
      else B.k == A.k + 1 && C.fin B


/-! ## The walk covers the machine -/

section
variable {Z : Ph} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveV (Z : Ph) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkV Z C n A = true

theorem le_k_spent {B D : AS} (h : B.le D = true) : D.k = B.k ∧ D.spent = B.spent ∧ D.rk = B.rk := by
  simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm, h.2.symm, h.1.2.symm⟩

theorem cover_liveV (ht : C.t.all (walkV Z C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverV C B = true) :
    ∃ D, LiveV Z C F D m ∧ D.k = B.k ∧ D.spent = B.spent ∧ D.log = B.log := by
  unfold coverV at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨hle, hlog⟩ := h2
    obtain ⟨hk, hsp, _⟩ := le_k_spent hle
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk, hsp, hlog.symm⟩
  · cases h2

theorem clamp_spent {P : Places} (A : AS) : (clampS P A).spent = A.spent := by
  unfold clampS
  split <;> rfl

theorem clamp_log {P : Places} (A : AS) : (clampS P A).log = A.log := by
  unfold clampS
  split <;> rfl

theorem pre_of_live {A : AS} {m : Machine} (hl : LiveV Z C F A m) : Z.pre A = true ∧ A.rk = false := by
  obtain ⟨_, n, hw⟩ := hl
  cases n with
  | zero => simp [walkV] at hw
  | succ n =>
    simp only [walkV, Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨hw.1.1, hw.1.2⟩

/-- **One step.** The state is split by `ScreenPage`'s pieces and by `zone`; every piece that covers the machine meets `ok`, and the step goes on to a state of the walk,
with the same bit and list, or ends the frame in a state that `fin` accepts -/
theorem live_stepV (hO : PlacesOK C.E C.P) (ht : C.t.all (walkV Z C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hl : LiveV Z C F A m) (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) :
    ∃ A', Sim C.E F A' m ∧ A'.spent = A.spent ∧ A'.log = A.log ∧ A'.rk = false ∧ ∀ A₁ ∈ Z.zone A', Sim C.E F A₁ m →
      Z.ok A₁ = true ∧ A₁.rk = false ∧
      ((∃ A'', LiveV Z C F A'' (go step m).2 ∧ A''.k = A.k ∧ A''.spent = A₁.spent ∧ A''.log = A₁.log ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
       ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.spent = A₁.spent ∧ B.log = A₁.log ∧ Sim C.E F B (go step m).2)) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkV] at hw
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    obtain ⟨A', hA, hs1, hk1⟩ := ScreenPage.cov_preS hO hs0 hh
    simp only [walkV, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, hz⟩ := hw.2 A' hA
    refine ⟨A', hs1, h1, h2, h4, fun A₁ hA₁ hs₁ => ?_⟩
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, gw⟩ := hz A₁ hA₁
    obtain ⟨r, hr, hB⟩ := RoomMap.s_stepT hO hops hT hs₁ hh
    have hw2 := gw r hr
    refine ⟨g1, g2, ?_⟩
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨b1, b2⟩ := hB B rfl
      dsimp only at hw2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw2
      obtain ⟨⟨⟨⟨e1, e2⟩, _⟩, e4⟩, hw3⟩ := hw2
      rcases b2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        have hkB : B.k = A.k := by rw [k1, g3]
        rw [if_pos (by simp [hkB])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
        have hN : Sim C.E F (weaken C B) (go step m).2 ∧ (weaken C B).k = B.k ∧ (weaken C B).spent = B.spent := by
          unfold weaken
          split
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            obtain ⟨q1, q2, _⟩ := le_k_spent hc.2
            exact ⟨sim_le hc.2 b1, q1, q2⟩
          · exact ⟨b1, rfl, rfl⟩
        rcases hw3 with ⟨_, h5⟩ | h5
        · obtain ⟨D, hD, hk, hsp, hlg⟩ := cover_liveV ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h5
          refine ⟨D, hD, ?_, ?_, ?_, k2, k3⟩
          · rw [hk, ScreenPage.clamp_k, hN.2.1, hkB]
          · rw [hsp, clamp_spent, hN.2.2, e1]
          · rw [hlg, clamp_log, e4, e2]
        · exact ⟨_, ⟨hN.1, n, h5⟩, by rw [hN.2.1, hkB], by rw [hN.2.2, e1], by rw [e4, e2], k2, k3⟩
      · right
        have hkB : B.k ≠ A.k := by rw [k1, g3]; omega
        rw [if_neg (by simp [hkB])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact ⟨k2, B, hw3.2, e1, e2, b1⟩


/-- **One frame, with a fact `Φ` outside the abstract states.** `Φ j b l` speaks of the machine after `j` instructions, with the bit `b` and the list `l` of the state
that covers it. If it holds at the start and every piece that covers a machine keeps it, it holds at every instruction of the frame and at the frame's end. The pieces of
`zone` cover every machine that their state covers. -/
theorem frame_of_walkV (Φ : Nat → Bool → List Nat → Prop) (hO : PlacesOK C.E C.P) (ht : C.t.all (walkV Z C Fu) = true) (hops : C.ops = (aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E F A' x → ∃ A₁ ∈ Z.zone A', Sim C.E F A₁ x)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkV Z C Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, SiteOK C.P (trace m i j))
    (h0 : Φ 0 S.spent S.log)
    (hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E F A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
       A₁ ∈ Z.zone A' → Sim C.E F A₁ (trace m i j) → Z.ok A₁ = true → Φ (j + 1) A₁.spent A₁.log) :
    (∀ j, (trace m i j).frame = m.frame → ∃ A, Sim C.E F A (trace m i j) ∧ Z.pre A = true ∧ Φ j A.spent A.log) ∧
    ∃ J, (trace m i J).frame = m.frame + 1 ∧ (∀ j, j < J → (trace m i j).frame = m.frame) ∧ frame m i = trace m i J ∧
      ∃ B, C.fin B = true ∧ Sim C.E F B (trace m i J) ∧ Φ J B.spent B.log := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveV Z C F A (trace m i j) ∧ (∀ j', j' ≤ j → (trace m i j').frame = m.frame) ∧ m.fdot + 3 * j ≤ (trace m i j).fdot ∧
        Φ j A.spent A.log) ∨
      (∃ J, J ≤ j ∧ (trace m i J).frame = m.frame + 1 ∧ (∀ j', j' < J → (trace m i j').frame = m.frame) ∧ trace m i j = trace m i J ∧
        ∃ B, C.fin B = true ∧ Sim C.E F B (trace m i J) ∧ Φ J B.spent B.log) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, Fu, hw⟩, fun j' hj' => by rw [show j' = 0 by omega]; rfl, Nat.le_refl _, h0⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h4, h5⟩ | ⟨J, h1, h2, h3, h4, B, h5⟩
      · have h3 := h2 j (Nat.le_refl _)
        have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        obtain ⟨A', a1, a2, a3, a4, a5⟩ := live_stepV hO ht hops hT h1 (hk j) (by rw [← e2]; exact hk (j + 1))
        obtain ⟨A₁, b1, b2⟩ := hz A' _ a4 a1
        have hΦ := hstep j A' A₁ (by rw [a2, a3]; exact h5) a1 h3 a4 b1 b2
        obtain ⟨c1, _, c3⟩ := a5 A₁ b1 b2
        have hΦ' := hΦ c1
        rw [e2]
        rcases c3 with ⟨A'', d1, _, d3, d4, d5, d6⟩ | ⟨d1, B, d2, d3, d4, d5⟩
        · refine Or.inl ⟨A'', d1, fun j' hj' => ?_, by omega, by rw [d3, d4]; exact hΦ'⟩
          rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
          · exact h2 j' (by omega)
          · rw [show j' = j + 1 by omega, e2, d5, h3]
        · refine Or.inr ⟨j + 1, Nat.le_refl _, by rw [e2, d1, h3], fun j' hj' => h2 j' (by omega), by rw [e2], B, d2, by rw [e2]; exact d5, ?_⟩
          rw [d3, d4]
          exact hΦ'
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          rw [h4]
          simp [h2]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        exact Or.inr ⟨J, by omega, h2, h3, by rw [e2, h4], B, h5⟩
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases key j with ⟨A, h1, _, _, h5⟩ | ⟨J, h1, h2, _, h4, _⟩
    · exact ⟨A, h1.1, (pre_of_live h1).1, h5⟩
    · rw [h4, h2] at hj
      omega
  · rcases key fuelPerFrame with ⟨A, h1, _, h4, _⟩ | ⟨J, _, h2, h3, h4, B, h5⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨J, h2, h3, by rw [frame_trace, h4], B, h5⟩

end

/-! ## The bytes -/

/-- the RAM index of an address -/
abbrev I (a : UInt16) : Nat := (a &&& 0x7FF).toNat

/-- the bytes that `VertModel.vsOf` reads: the vertical bytes, the state, and A and B -/
def vKeep (sy : Syms) : List Nat :=
  [I sy.Player_Y_Position, I sy.Player_Y_MoveForce, I sy.Player_Y_Speed, I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown,
   I sy.JumpOrigin_Y_Position, I sy.Player_State, I sy.A_B_Buttons]

/-- with A and B of the frame before, and the jump's halt value: what the movement routine reads besides; the change of size and the collision bits, which the
player's routine reads; and the horizontal bytes (`FrameModel.hBytes`) -/
def vKeepA (sy : Syms) : List Nat :=
  vKeep sy ++ ([I sy.PreviousA_B_Buttons, I sy.DiffToHaltJump, I sy.PlayerChangeSizeFlag, I sy.Player_CollisionBits] ++ (FrameModel.hBytes sy).map I)

/-! ## Bits of a byte -/
/-- the byte, with the bit `b` known to be `v` -/
def withBit (x : AB) (b : UInt8) (v : Bool) : AB := if v then x.or (AB.known b) else x.and (AB.known (~~~b))

/-- the byte can be `c` -/
def canBe (x : AB) (c : UInt8) : Bool := c &&& x.k == x.v &&& x.k

/-- the byte can have the bit `b` -/
def canBit (x : AB) (b : UInt8) (v : Bool) : Bool := x.bit b != some (!v)

theorem getK_setK_self {A : AS} {i : Nat} {b : AB} (h1 : i < A.ram.size) (h2 : i < A.kn.size) : (A.setK i b).getK i = b := by
  show (⟨(A.ram.set! i b.v).get! i, (A.kn.set! i b.k).get! i⟩ : AB) = b
  rw [PipeTransitionAll.ba_get_set_self _ _ _ h1, PipeTransitionAll.ba_get_set_self _ _ _ h2]

theorem getK_setK_ne {A : AS} {i j : Nat} {b : AB} (h : i ≠ j) : (A.setK i b).getK j = A.getK j := by
  show (⟨(A.ram.set! i b.v).get! j, (A.kn.set! i b.k).get! j⟩ : AB) = ⟨A.ram.get! j, A.kn.get! j⟩
  rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ h, PipeTransitionAll.ba_get_set_ne _ _ _ _ h]

theorem setK_ram_size {A : AS} {i : Nat} {b : AB} : (A.setK i b).ram.size = A.ram.size := PipeTransitionAll.ba_size_set _ _ _
theorem setK_kn_size {A : AS} {i : Nat} {b : AB} : (A.setK i b).kn.size = A.kn.size := PipeTransitionAll.ba_size_set _ _ _

theorem u8_all {P : UInt8 → Prop} [DecidablePred P] (h : ∀ n : Fin 256, P (UInt8.ofNat n.val)) : ∀ x, P x := fun x => by
  have := h ⟨x.toNat, x.toNat_lt⟩
  simpa using this

/-- the bits used: one bit `c` set by `withBit` is known and set -/
theorem or_bit_k : ∀ n : Fin 256, ∀ c ∈ ([4, 8, 16, 32, 64, 128] : List UInt8),
    ((UInt8.ofNat n.val ||| (0xFF &&& c)) &&& c = c) ∧ ((UInt8.ofNat n.val ||| c) &&& c = c) := by decide +kernel

theorem and7f_k : ∀ n : Fin 256, ((UInt8.ofNat n.val ||| (0xFF &&& ~~~(~~~(0x80 : UInt8)))) &&& 0x80 = 0x80) ∧ ((UInt8.ofNat n.val &&& ~~~(0x80 : UInt8)) &&& 0x80 = 0) := by decide +kernel

theorem withBit_true_mem {x : AB} {y c : UInt8} (hc : c ∈ ([4, 8, 16, 32, 64, 128] : List UInt8)) (h : (withBit x c true).mem y) : y &&& c = c := by
  simp only [withBit, if_true] at h
  have hk : (x.or (AB.known c)).k &&& c = c := by
    show ((x.k &&& 0xFF) ||| (x.k &&& x.v) ||| (0xFF &&& c)) &&& c = c
    exact (u8_all (P := fun t => (t ||| (0xFF &&& c)) &&& c = c) (fun n => (or_bit_k n c hc).1)) _
  rw [bit_eq h hk]
  show (x.v ||| c) &&& c = c
  exact (u8_all (P := fun t => (t ||| c) &&& c = c) (fun n => (or_bit_k n c hc).2)) _

theorem withBit_false_mem {x : AB} {y : UInt8} (h : (withBit x 0x80 false).mem y) : y &&& 0x80 = 0 := by
  simp only [withBit, Bool.false_eq_true, if_false] at h
  have hk : (x.and (AB.known (~~~0x80))).k &&& 0x80 = 0x80 := by
    show ((x.k &&& 0xFF) ||| (x.k &&& ~~~x.v) ||| (0xFF &&& ~~~(~~~(0x80 : UInt8)))) &&& 0x80 = 0x80
    exact (u8_all (P := fun t => (t ||| (0xFF &&& ~~~(~~~(0x80 : UInt8)))) &&& 0x80 = 0x80) (fun n => (and7f_k n).1)) _
  rw [bit_eq h hk]
  show (x.v &&& ~~~0x80) &&& 0x80 = 0
  exact (u8_all (P := fun t => (t &&& ~~~(0x80 : UInt8)) &&& 0x80 = 0) (fun n => (and7f_k n).2)) _

theorem or_self_bit : ∀ n : Fin 256, ∀ c ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), UInt8.ofNat n.val &&& c = c → (UInt8.ofNat n.val ||| c) = UInt8.ofNat n.val := by decide +kernel

theorem and7f_self : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 → (UInt8.ofNat n.val &&& ~~~(0x80 : UInt8)) = UInt8.ofNat n.val := by decide +kernel

theorem withBit_true_of {x : AB} {y c : UInt8} (hc : c ∈ ([4, 8, 16, 32, 64, 128] : List UInt8)) (hm : x.mem y) (hy : y &&& c = c) : (withBit x c true).mem y := by
  simp only [withBit, if_true]
  have := mem_or hm (mem_known_self c)
  rwa [(u8_all (P := fun t => t &&& c = c → (t ||| c) = t) (fun n => or_self_bit n c hc)) y hy] at this

theorem withBit_false_of {x : AB} {y : UInt8} (hm : x.mem y) (hy : y &&& 0x80 = 0) : (withBit x 0x80 false).mem y := by
  simp only [withBit, Bool.false_eq_true, if_false]
  have := mem_and hm (mem_known_self (~~~(0x80 : UInt8)))
  rwa [(u8_all (P := fun t => t &&& 0x80 = 0 → (t &&& ~~~(0x80 : UInt8)) = t) and7f_self) y hy] at this

theorem canBe_of {x : AB} {y : UInt8} (h : x.mem y) : canBe x y = true := by
  simp only [canBe, beq_iff_eq]
  exact h

theorem canBit_of {x : AB} {y c : UInt8} (h : x.mem y) (b : Bool) (hy : (y &&& c != 0) = b) : canBit x c b = true := by
  simp only [canBit, AB.bit, bne_iff_ne, ne_eq]
  split
  · rename_i hk
    simp only [beq_iff_eq] at hk
    rw [← bit_eq h hk, hy]
    cases b <;> simp
  · simp

theorem mem_known {c y : UInt8} (h : (AB.known c).mem y) : y = c := known_eq h

/-! ## The walk to the player's routine -/

/-- the byte is known, with the value `v` -/
def knIs (b : AB) (v : UInt8) : Bool := b.isK && b.v == v

/-- **What the walk asks at the player's routine**: the stack pointer `S` of the player's routine, no NMI pending and the NMI off, the routine byte of control, the
area's type 1, 2 or 3, the jumpspring and the swimming flag 0, all known -/
def cutOK (sy : Syms) (S : UInt8) (A : AS) : Bool :=
  A.s == S && !A.nmi && A.ppuCtrl.bit 0x80 == some false && knIs (A.getK (I sy.GameEngineSubroutine)) sy.Eng_PlayerCtrl.toUInt8 &&
    (A.getK (I sy.AreaType)).isK && [(1 : UInt8), 2, 3].contains (A.getK (I sy.AreaType)).v &&
    knIs (A.getK (I sy.JumpspringAnimCtrl)) 0 && knIs (A.getK (I sy.SwimmingFlag)) 0

/-- the load of the pause byte just before the NMI's call of the mode's routine (`lda` of the byte, `lsr`, `bcs` over the call: `CtrlKeep.pauseA`) -/
def pzLd (sy : Syms) : UInt16 := LagFrames.modeCall sy - 6

/-- the pieces at the load of the pause byte `pz`: its low bit known, marked `[1]` (set) or `[0]` (clear) so that the search keeps them apart -/
def pzPieces (pz : Nat) (A : AS) : List AS :=
  (if canBit (A.getK pz) 1 true then [{ A.setK pz (withBit (A.getK pz) 1 true) with log := [1] }] else []) ++
    (if canBit (A.getK pz) 1 false then [{ A.setK pz (withBit (A.getK pz) 1 false) with log := [0] }] else [])

/-- the bit says that the frame has come to the player's routine `R`. The walk asks that it comes there once, that before it no step writes the bytes of `vKeepA`,
and that the state there meets `cutOK`. At the load of the pause byte `pz` before the call of the mode's routine the state is split on the byte's low bit; at `R` the mark
is cleared -/
def phA (sy : Syms) (E : Env) (S : UInt8) (pz : Nat) : Ph where
  zone := fun A =>
    if A.pc == sy.PlayerCtrlRoutine && !A.spent then [{ A with spent := true, log := [] }]
    else if A.pc == pzLd sy && !A.spent && A.log.isEmpty then pzPieces pz A else [A]
  pre := fun A => !(A.pc == sy.PlayerCtrlRoutine && A.spent) && (A.pc != sy.PlayerCtrlRoutine || cutOK sy S A)
  ok := fun A => A.spent || StepWrites.keepOK E (fun i => (vKeepA sy).contains i) A

/-- at the frame's end the state is not at the player's routine: the frame does not end there -/
def finR (sy : Syms) (B : AS) : Bool := B.pc != sy.PlayerCtrlRoutine

theorem finR_spec {sy : Syms} {B : AS} (h : finR sy B = true) : B.pc ≠ sy.PlayerCtrlRoutine := by
  simpa [finR] using h

/-- at the frame's end: not at the player's routine; and the frame has come there, or the low bit of the pause byte `pz` is known to be 1 (the game is paused) -/
def finA (sy : Syms) (pz : Nat) (B : AS) : Bool := finR sy B && (B.spent || (B.getK pz).bit 0x01 == some true)

theorem finA_pc {sy : Syms} {pz : Nat} {B : AS} (h : finA sy pz B = true) : B.pc ≠ sy.PlayerCtrlRoutine := by
  simp only [finA, Bool.and_eq_true] at h
  exact finR_spec h.1

/-! ## The walk from the scroll handler -/

/-- a piece in the air with the state `c` and rising, with the bit set -/
def upP (sy : Syms) (A : AS) (c : UInt8) : List AS :=
  if canBe (A.getK (I sy.Player_State)) c && canBit (A.getK (I sy.Player_Y_Speed)) 0x80 true then
    [{ (A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true) with spent := true }]
  else []

/-- a piece falling, marked `[2]` -/
def fallP (sy : Syms) (A : AS) : List AS :=
  if canBit (A.getK (I sy.Player_Y_Speed)) 0x80 false then [{ A.setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false) with log := [2] }] else []

/-- a piece with the state `c`, marked `[2]` -/
def knP (sy : Syms) (A : AS) (c : UInt8) : List AS :=
  if canBe (A.getK (I sy.Player_State)) c then [{ A.setK (I sy.Player_State) (AB.known c) with log := [2] }] else []

/-- the pieces with a bit of the state above bit 1, marked `[2]` -/
def hiP (sy : Syms) (A : AS) : List AS :=
  ([4, 8, 16, 32, 64, 128] : List UInt8).flatMap fun b =>
    if canBit (A.getK (I sy.Player_State)) b true then [{ A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true) with log := [2] }] else []

/-- the pieces at the scroll handler: in the air (the state 1 or 2) and rising (bit 7 of the vertical speed), with the bit set; and the other states, which together cover
the rest, marked `[2]`: falling, the state 0, the state 3, or a state with a bit above bit 1 -/
def piecesQ (sy : Syms) (A : AS) : List AS :=
  upP sy A 1 ++ upP sy A 2 ++ fallP sy A ++ knP sy A 0 ++ knP sy A 3 ++ hiP sy A

/-- the step of `A` may write a byte of `vKeep`: not the erase of a coin, which writes in the block buffers -/
def mayWriteV (sy : Syms) (E : Env) (P : Places) (A : AS) : Bool :=
  !(A.pc == P.erase && !A.nmi) && !StepWrites.keepOK E (fun i => (vKeep sy).contains i) A

/-- the bit says that the frame came to the scroll handler `Q` in the air and rising, and that no step has written the bytes of `vKeep` since. A step that may write them
drops the bit and marks the state `[1]`; such a state must end the frame out of the player's routine (`finB`). The other states at `Q` are marked `[2]`. The walk asks that
the frame comes to `Q` once. -/
def phB (sy : Syms) (E : Env) (P : Places) : Ph where
  zone := fun A =>
    if A.pc == sy.PlayerSubs && !A.spent && A.log.isEmpty then piecesQ sy A
    else if A.spent && mayWriteV sy E P A then [{ A with spent := false, log := [1] }]
    else [A]
  pre := fun A => !(A.pc == sy.PlayerSubs && (A.spent || !A.log.isEmpty))
  ok := fun A => !A.spent || !mayWriteV sy E P A

/-- at the frame's end: a state whose bytes of `vKeep` may have been written after `Q` ends out of the player's routine: the routine byte is known and is not the reference's -/
def finB (P : Places) (r : Machine) (B : AS) : Bool :=
  B.log != [1] || (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI)

/-! ## Finding the table: a search, no part of the proof -/

/-- the key: that of `RoomMap`'s search, and with the bit, the state -/
def keyV (sy : Syms) (Z : Aids) (E : Env) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := Z.key E A * 4 + A.log.length + (if A.log == [1] then 2 else 0)
  if A.spent then n * 65536 + num (A.getK (I sy.Player_State)) else n

def routeV (sy : Syms) (P : Places) (Z : Aids) (E : Env) (X : SearchS) (B0 : AS) : SearchS :=
  let B := clampS P (Z.norm B0)
  let K := keyV sy Z E B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D =>
    if B.le D then X else
    let J := D.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 then { J with hi := P.late } else J
    SearchS.put { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => SearchS.put { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

partial def runV (sy : Syms) (Ph' : Ph) (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let pieces := ((preS P (clampS P cur)).flatMap Ph'.zone)
    let rs := pieces.flatMap (RoomMap.stepT P E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := !Ph'.pre cur || pieces.any (fun A₁ => !Ph'.ok A₁) || rs.any (·.isNone)
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (Z.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          b.pc != sy.PlayerCtrlRoutine && b.pc != sy.PlayerSubs &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeV sy P Z E X b
    break
  return X

partial def searchV (sy : Syms) (Ph' : Ph) (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := keyV sy Z E A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runV sy Ph' P Z E ops X A
  return X

def searchOfV (sy : Syms) (Ph' : Ph) (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  searchV sy Ph' P Z E (aRows E).toArray ((startsR r K).foldl (routeV sy P Z E) {})

/-- the configuration from the table found -/
def cfgOfV (sy : Syms) (Ph' : Ph) (fin : AS → Bool) (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOfV sy Ph' P Z E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd]).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin, t := q.1, key := keyV sy Z E, idx := q.2.1, cut := q.2.2, norm := Z.norm, normAt := at0 }

/-- the check of a walk -/
def walkCheckV (sy : Syms) (Ph' : Ph) (fin : AS → Bool) (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOfV sy Ph' fin P Z E r K
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K && C.t.all (walkV Ph' C ScreenPage.fuelS) &&
    (startsR r K).all (walkV Ph' C ScreenPage.fuelS)


/-! ## What the check gives -/

/-- what the check of a walk says -/
structure OKV (Z : Ph) (E : Env) (P : Places) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) (Fu : Nat) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  table : C.t.all (walkV Z C Fu) = true
  starts : ∀ S ∈ startsR r K, walkV Z C Fu S = true

theorem okV_of_check {sy : Syms} {Z : Ph} {fin : AS → Bool} {P : Places} {Zd : Aids} {E : Env} {r : Machine} {K : List (Nat × UInt8)}
    (h : walkCheckV sy Z fin P Zd E r K = true) : OKV Z E P r K (cfgOfV sy Z fin P Zd E r K) ScreenPage.fuelS := by
  simp only [walkCheckV, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, h4, h5⟩

theorem cfgOfV_fin {sy : Syms} {Z : Ph} {fin : AS → Bool} {P : Places} {Zd : Aids} {E : Env} {r : Machine} {K : List (Nat × UInt8)} :
    (cfgOfV sy Z fin P Zd E r K).fin = fin := rfl

/-- with the counter not followed, the bit and the list are free -/
theorem sim_bits {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hr : A.rk = false) (b : Bool) (l : List Nat) :
    Sim E F { A with spent := b, log := l } m :=
  { hs with rkv := fun h => absurd h (by simp [hr]) }

theorem starts_bits {r : Machine} {K : List (Nat × UInt8)} {S : AS} (h : S ∈ startsR r K) : S.spent = false ∧ S.log = [] ∧ S.rk = false := by
  simp only [startsR, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩

/-- the next instruction of the frame -/
theorem trace_succ {m : Machine} {i : UInt8} {j : Nat} (hf : (trace m i j).frame = m.frame) (hh : (trace m i j).halted = false) :
    trace m i (j + 1) = (go step (trace m i j)).2 := by
  show nxt (m.frame + 1) (trace m i j) = _
  have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by simp [hf, hh]
  simp only [nxt, if_neg hc]

/-- the start of a frame in the room is covered by a start state of the walk -/
theorem start_of_room {Z : Ph} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV Z E P r K C Fu) {m : Machine}
    (hm : RoomCond E r K m) : ∃ S, walkV Z C Fu S = true ∧ Sim C.E (m.frame, 2) S m ∧ S.spent = false ∧ S.log = [] ∧ S.rk = false := by
  obtain ⟨S, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  obtain ⟨b1, b2, b3⟩ := starts_bits hS
  exact ⟨S, h.starts S hS, by rw [h.env]; exact hs, b1, b2, b3⟩

/-! ## The zone of the walk to the player's routine -/

theorem low_self1 : ∀ n : Fin 256, UInt8.ofNat n.val &&& 1 = 1 → (UInt8.ofNat n.val ||| 1) = UInt8.ofNat n.val := by decide +kernel
theorem low_self0 : ∀ n : Fin 256, UInt8.ofNat n.val &&& 1 = 0 → (UInt8.ofNat n.val &&& ~~~(1 : UInt8)) = UInt8.ofNat n.val := by decide +kernel
theorem low_cases : ∀ n : Fin 256, UInt8.ofNat n.val &&& 1 = 0 ∨ UInt8.ofNat n.val &&& 1 = 1 := by decide +kernel

theorem withLow_true {x : AB} {y : UInt8} (hm : x.mem y) (hy : y &&& 1 = 1) : (withBit x 1 true).mem y := by
  simp only [withBit, if_true]
  have := mem_or hm (mem_known_self 1)
  rwa [(u8_all (P := fun t => t &&& 1 = 1 → (t ||| 1) = t) low_self1) y hy] at this

theorem withLow_false {x : AB} {y : UInt8} (hm : x.mem y) (hy : y &&& 1 = 0) : (withBit x 1 false).mem y := by
  simp only [withBit, Bool.false_eq_true, if_false]
  have := mem_and hm (mem_known_self (~~~(1 : UInt8)))
  rwa [(u8_all (P := fun t => t &&& 1 = 0 → (t &&& ~~~(1 : UInt8)) = t) low_self0) y hy] at this

/-- the pieces at the load of the pause byte cover the state, with its bit `spent` and its counter -/
theorem pzPieces_cover {E : Env} {F : Nat × UInt8} {pz : Nat} (hpz : pz < 2048) {A : AS} {m : Machine} (hr : A.rk = false) (hs : Sim E F A m) :
    ∃ A₁ ∈ pzPieces pz A, Sim E F A₁ m := by
  have hm := hs.ram pz hpz
  rcases (u8_all (P := fun t => t &&& 1 = 0 ∨ t &&& 1 = 1) low_cases) (m.ram.get! pz) with e | e
  · have hc : canBit (A.getK pz) 1 false = true := canBit_of hm false (by rw [e]; rfl)
    refine ⟨{ A.setK pz (withBit (A.getK pz) 1 false) with log := [0] }, ?_, ?_⟩
    · unfold pzPieces
      rw [if_pos hc]
      exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    · exact sim_bits (PipeEntryRule.sim_setK' hs (withLow_false hm e)) hr _ [0]
  · have hc : canBit (A.getK pz) 1 true = true := canBit_of hm true (by rw [e]; rfl)
    refine ⟨{ A.setK pz (withBit (A.getK pz) 1 true) with log := [1] }, ?_, ?_⟩
    · unfold pzPieces
      rw [if_pos hc]
      exact List.mem_append_left _ (List.mem_singleton.2 rfl)
    · exact sim_bits (PipeEntryRule.sim_setK' hs (withLow_true hm e)) hr _ [1]

theorem pzPieces_keep {pz : Nat} {A A₁ : AS} (h : A₁ ∈ pzPieces pz A) : A₁.spent = A.spent ∧ A₁.pc = A.pc ∧ A₁.rk = A.rk := by
  unfold pzPieces at h
  rcases List.mem_append.1 h with h | h <;> split at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> exact ⟨rfl, rfl, rfl⟩

/-- the zone's pieces cover the state -/
theorem zoneA_cover {sy : Syms} {E E' : Env} {S : UInt8} {pz : Nat} (hpz : pz < 2048) {F : Nat × UInt8} {A' : AS} {x : Machine} (hr : A'.rk = false)
    (hs : Sim E' F A' x) : ∃ A₁ ∈ (phA sy E S pz).zone A', Sim E' F A₁ x := by
  show ∃ A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent then [{ A' with spent := true, log := [] }]
    else if A'.pc == pzLd sy && !A'.spent && A'.log.isEmpty then pzPieces pz A' else [A']), _
  split
  · exact ⟨_, List.mem_singleton.2 rfl, sim_bits hs hr true []⟩
  · split
    · exact pzPieces_cover hpz hr hs
    · exact ⟨A', List.mem_singleton.2 rfl, hs⟩

/-- a piece of the zone away from the first arrival at `R` keeps the bit, the place and the counter -/
theorem zoneA_other {sy : Syms} {E : Env} {S : UInt8} {pz : Nat} {A' A₁ : AS} (hA : A₁ ∈ (phA sy E S pz).zone A')
    (hc : ¬ ((A'.pc == sy.PlayerCtrlRoutine && !A'.spent) = true)) : A₁.spent = A'.spent ∧ A₁.pc = A'.pc ∧ A₁.rk = A'.rk := by
  change A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent then [{ A' with spent := true, log := [] }]
    else if A'.pc == pzLd sy && !A'.spent && A'.log.isEmpty then pzPieces pz A' else [A']) at hA
  rw [if_neg hc] at hA
  split at hA
  · exact pzPieces_keep hA
  · rw [List.mem_singleton.1 hA]
    exact ⟨rfl, rfl, rfl⟩

/-- the piece of the zone at the first arrival at `R` -/
theorem zoneA_R {sy : Syms} {E : Env} {S : UInt8} {pz : Nat} {A' A₁ : AS} (hA : A₁ ∈ (phA sy E S pz).zone A')
    (hc : (A'.pc == sy.PlayerCtrlRoutine && !A'.spent) = true) : A₁ = { A' with spent := true, log := [] } := by
  change A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent then [{ A' with spent := true, log := [] }]
    else if A'.pc == pzLd sy && !A'.spent && A'.log.isEmpty then pzPieces pz A' else [A']) at hA
  rw [if_pos hc] at hA
  exact List.mem_singleton.1 hA

/-! ## The frame up to the player's routine -/

/-- **The frame comes to the player's routine at most once, and before it no step writes the bytes of `vKeepA`.** The frame starts in the room's condition, and each
instruction meets `SiteOK`. -/
theorem before_R {sy : Syms} {E : Env} {S : UInt8} {pz : Nat} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (hpz : pz < 2048)
    (h : OKV (phA sy E S pz) E P r K C Fu)
    (hfin : ∀ B, C.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j, (trace m i j).frame = m.frame → (∀ j', j' < j → (trace m i j').pc ≠ sy.PlayerCtrlRoutine) → ∀ x ∈ vKeepA sy, (trace m i j).ram.get! x = m.ram.get! x) ∧
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerCtrlRoutine) ∧
    (∀ j d, ((trace m i (j + d)).frame ≥ m.frame + 1 || (trace m i (j + d)).halted) = false → (trace m i j).frame = m.frame) ∧
    (∀ j, (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j).frame = m.frame) := by
  obtain ⟨S0, hw, hs, s1, s2, s3⟩ := start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  let Φ : Nat → Bool → List Nat → Prop := fun j b _ =>
    (b = true ↔ ∃ j', j' < j ∧ (trace m i j').pc = sy.PlayerCtrlRoutine) ∧ (b = false → ∀ x ∈ vKeepA sy, (trace m i j).ram.get! x = m.ram.get! x)
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phA sy E S pz).zone A', Sim C.E (m.frame, 2) A₁ x :=
    fun _ _ hr hsx => zoneA_cover hpz hr hsx
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phA sy E S pz).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phA sy E S pz).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2⟩ hs' hf hr hA₁ hs₁ hok
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    by_cases hc : (A'.pc == sy.PlayerCtrlRoutine && !A'.spent) = true
    · rw [zoneA_R hA₁ hc]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      exact ⟨by simp only [true_iff]; exact ⟨j, by omega, by rw [hpc, hc.1]⟩, fun h => by simp at h⟩
    · obtain ⟨e1, _, _⟩ := zoneA_other hA₁ hc
      cases hb : A₁.spent with
      | true =>
        rw [e1] at hb
        rw [hb] at p1
        obtain ⟨j', a1, a2⟩ := p1.1 rfl
        exact ⟨by simp only [true_iff]; exact ⟨j', by omega, a2⟩, fun h => by simp at h⟩
      | false =>
        have hb' : A'.spent = false := by rw [← e1]; exact hb
        rw [hb'] at p1 p2 hc
        have hnr : (trace m i j).pc ≠ sy.PlayerCtrlRoutine := by
          rw [hpc]
          intro h2
          simp [h2] at hc
        refine ⟨⟨fun h => by simp at h, fun ⟨j', a1, a2⟩ => ?_⟩, fun _ x hx => ?_⟩
        · rcases Nat.lt_or_ge j' j with hlt | hge
          · exact absurd (p1.2 ⟨j', hlt, a2⟩) (by simp)
          · rw [show j' = j by omega] at a2
            exact absurd a2 hnr
        · have hok' : StepWrites.keepOK E (fun i => (vKeepA sy).contains i) A₁ = true := by
            have := hok
            simp only [phA, Bool.or_eq_true, hb, Bool.false_eq_true, false_or] at this
            exact this
          rw [trace_succ hf hs'.halted]
          have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
          rw [StepWrites.keep_step hs₂ hok' x (List.contains_iff_mem.2 hx)]
          exact p2 rfl x hx
  obtain ⟨hall, J, hJ1, hJ2, _, B, hB, hsB, _⟩ := frame_of_walkV (Z := phA sy E S pz) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide) (by rw [h.env]; exact h.pad) hz
    hw hs hk' ⟨by rw [s1]; simp, fun _ x _ => rfl⟩ hstep
  refine ⟨fun j hj hb x hx => ?_, fun j j' hlt hR hj' hR' => ?_, fun j d hl => ?_, fun j hR => ?_⟩
  rotate_left 3
  · -- the frame does not end at the player's routine: a state at its end is not there
    rcases Nat.lt_or_ge j J with h1 | h1
    · exact hJ2 j h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (j - J)
      rw [show J + (j - J) = j by omega] at e
      have e2 : (trace m i J).pc = B.pc := hsB.pc
      rw [← e, hR] at e2
      exact hfin B hB e2.symm
  rotate_left 2
  · rcases Nat.lt_or_ge j J with h1 | h1
    · exact hJ2 j h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (j + d - J)
      rw [show J + (j + d - J) = j + d by omega] at e
      rw [e, hJ1] at hl
      simp at hl
  · obtain ⟨A, _, _, q1, q2⟩ := hall j hj
    cases hA : A.spent with
    | true =>
      rw [hA] at q1
      obtain ⟨j', a1, a2⟩ := q1.1 rfl
      exact absurd a2 (hb j' a1)
    | false =>
      rw [hA] at q2
      exact q2 rfl x hx
  · obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = sy.PlayerCtrlRoutine := by rw [← hsA.pc]; exact hR'
    have hsp : A.spent = false := by
      simp only [phA, hApc, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true'] at hpre
      exact hpre.1
    rw [hsp] at q1
    exact absurd (q1.2 ⟨j, hlt, hR⟩) (by simp)


/-- **At the player's routine the horizontal bytes are those of the frame's start**: the frame comes there once and before its end, and no step before it writes
`vKeepA` (`before_R`). This is `Clean.before` on the room's frames. -/
theorem hbytes_at_R {sy : Syms} {E : Env} {S : UInt8} {pz : Nat} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (hpz : pz < 2048)
    (h : OKV (phA sy E S pz) E P r K C Fu)
    (hfin : ∀ B, C.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) {j : Nat} (hR : (trace m i j).pc = sy.PlayerCtrlRoutine) :
    ∀ a ∈ FrameModel.hBytes sy, peek (trace m i j) a = peek m a := by
  obtain ⟨a1, a2, _, a4⟩ := before_R hpz h hfin hm hk
  have hf := a4 j hR
  have hfirst : ∀ j', j' < j → (trace m i j').pc ≠ sy.PlayerCtrlRoutine := fun j' hj' hR' => a2 j' j hj' hR' hf hR
  intro a ha
  exact a1 j hf hfirst (I a) (List.mem_append_right _ (List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩)))

/-- **The machine at the player's routine**, as the walk gives it (`cutOK`): the program, no NMI pending and the NMI off, the stack pointer `S`, the routine byte of
control, the area's type 1, 2 or 3, the jumpspring and the swimming flag 0 -/
structure CutAt (sy : Syms) (E : Env) (S : UInt8) (m : Machine) : Prop where
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  nmi : m.nmiPending = false
  halted : m.halted = false
  trk : m.trk = false
  size : m.ram.size = 2048
  ctl : m.ppuCtrl &&& 0x80 = 0
  s : m.s = S
  eng : peek m sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8
  area : peek m sy.AreaType ∈ [(1 : UInt8), 2, 3]
  spring : peek m sy.JumpspringAnimCtrl = 0
  swim : peek m sy.SwimmingFlag = 0

theorem knIs_spec {b : AB} {v x : UInt8} (h : knIs b v = true) (hm : b.mem x) : x = v := by
  simp only [knIs, Bool.and_eq_true, beq_iff_eq] at h
  rw [isK_eq h.1 hm, h.2]

theorem bit80_off : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0x80 != 0) = false → UInt8.ofNat n.val &&& 0x80 = 0 := by decide +kernel

/-- a known bit 7 that is 0 -/
theorem off_of_bit {b : AB} {x : UInt8} (h : (b.bit 0x80 == some false) = true) (hm : b.mem x) : x &&& 0x80 = 0 := by
  unfold AB.bit at h
  split at h
  · rename_i hk
    simp only [beq_iff_eq, Option.some.injEq] at h hk
    have e : (x &&& b.k) &&& 0x80 = (b.v &&& b.k) &&& 0x80 := by rw [show x &&& b.k = b.v &&& b.k from hm]
    rw [UInt8.and_assoc, UInt8.and_assoc, hk] at e
    rw [e]
    have h1 := bit80_off ⟨b.v.toNat, b.v.toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at h1
    exact h1 h
  · simp at h

/-- **At the player's routine the machine is as `CutAt` says.** The frame starts in the room's condition, and each instruction meets `SiteOK`; at any instruction of the
frame at the player's routine the walk's state meets `cutOK`. -/
theorem cut_R {sy : Syms} {E : Env} {S : UInt8} {pz : Nat} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (hpz : pz < 2048)
    (h : OKV (phA sy E S pz) E P r K C Fu)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) {j : Nat}
    (hR : (trace m i j).pc = sy.PlayerCtrlRoutine) (hf : (trace m i j).frame = m.frame) : CutAt sy E S (trace m i j) := by
  obtain ⟨S0, hw, hs, _, _, _⟩ := start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phA sy E S pz).zone A', Sim C.E (m.frame, 2) A₁ x :=
    fun _ _ hr hsx => zoneA_cover hpz hr hsx
  obtain ⟨hall, _⟩ := frame_of_walkV (Z := phA sy E S pz) (fun _ _ _ => True) hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide) (by rw [h.env]; exact h.pad) hz
    hw hs hk' trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
  obtain ⟨A, hsA, hpre, _⟩ := hall j hf
  rw [h.env] at hsA
  have hApc : A.pc = sy.PlayerCtrlRoutine := by rw [← hsA.pc]; exact hR
  have hc : cutOK sy S A = true := by
    simp only [phA, hApc, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at hpre
    exact hpre.2
  simp only [cutOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hS, hn⟩, hctl⟩, heng⟩, hak⟩, hav⟩, hsp⟩, hsw⟩ := hc
  have hlt : ∀ a : UInt16, (a &&& 0x7FF).toNat < 2048 := fun a => PipeTransitionAll.mask_lt _
  refine ⟨hsA.prg, hsA.mask, by rw [hsA.nmi]; exact hn, hsA.halted, hsA.trk, hsA.size, off_of_bit (by rw [hctl]; rfl) hsA.ppuCtrl, by rw [hsA.s]; exact hS,
    knIs_spec heng (hsA.ram _ (hlt _)), ?_, knIs_spec hsp (hsA.ram _ (hlt _)), knIs_spec hsw (hsA.ram _ (hlt _))⟩
  have e := isK_eq hak (hsA.ram _ (hlt sy.AreaType))
  show (trace m i j).ram.get! (sy.AreaType &&& 0x7FF).toNat ∈ _
  rw [e]
  simpa using hav

/-- **A frame of the room that ends not paused comes to the player's routine**, a first time at an instruction `j` up to `fuelPerFrame`, before its end. The frame starts in
the room's condition, and each instruction meets `SiteOK`. The walk's states at the frame's end that have not come to the player's routine know the pause byte's low bit to
be 1 (`finA`). -/
theorem arrive_R {sy : Syms} {E : Env} {S : UInt8} {pz : Nat} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (hpz : pz < 2048)
    (h : OKV (phA sy E S pz) E P r K C Fu) (hfin : C.fin = finA sy pz) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j))
    (hu : (frame m i).ram.get! pz &&& 1 = 0) :
    ∃ j, (trace m i j).pc = sy.PlayerCtrlRoutine ∧ (trace m i j).frame = m.frame ∧ j ≤ fuelPerFrame ∧ ∀ j', j' < j → (trace m i j').pc ≠ sy.PlayerCtrlRoutine := by
  obtain ⟨S0, hw, hs, s1, _, _⟩ := start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phA sy E S pz).zone A', Sim C.E (m.frame, 2) A₁ x :=
    fun _ _ hr hsx => zoneA_cover hpz hr hsx
  let Φ : Nat → Bool → List Nat → Prop := fun j b _ => b = true → ∃ j', j' < j ∧ (trace m i j').pc = sy.PlayerCtrlRoutine
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phA sy E S pz).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phA sy E S pz).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ p1 hs' _ _ hA₁ _ _ hb
    by_cases hc : (A'.pc == sy.PlayerCtrlRoutine && !A'.spent) = true
    · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      exact ⟨j, by omega, by rw [hs'.pc, hc.1]⟩
    · obtain ⟨e1, _, _⟩ := zoneA_other hA₁ hc
      rw [e1] at hb
      obtain ⟨j', a1, a2⟩ := p1 hb
      exact ⟨j', by omega, a2⟩
  obtain ⟨_, J, hJ1, hJ2, hJ3, B, hB, hsB, hΦB⟩ := frame_of_walkV (Z := phA sy E S pz) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' (fun hb => by rw [s1] at hb; cases hb) hstep
  rw [hfin] at hB
  simp only [finA, Bool.and_eq_true, Bool.or_eq_true] at hB
  have hsp : B.spent = true := by
    rcases hB.2 with e | e
    · exact e
    · exfalso
      have h1 : (trace m i J).ram.get! pz &&& 1 = 1 := CtrlKeep.low_of_bit (by simpa using e) (hsB.ram pz hpz)
      rw [← hJ3, hu] at h1
      cases h1
  obtain ⟨j, hj, hR⟩ := hΦB hsp
  have hJf : J ≤ fuelPerFrame := by
    rcases Nat.lt_or_ge fuelPerFrame J with h1 | h1
    · exfalso
      have e1 := hJ2 fuelPerFrame h1
      have e2 : frame m i = trace m i fuelPerFrame := PipeEntryRule.frame_trace m i
      rw [← e2, hJ3, hJ1] at e1
      omega
    · exact h1
  obtain ⟨_, a2, _, _⟩ := before_R hpz h (fun B' hB' => by rw [hfin] at hB'; exact finA_pc hB') hm hk
  refine ⟨j, hR, hJ2 j hj, by omega, fun j' hj' hR' => a2 j' j hj' hR' (hJ2 j hj) hR⟩

/-! ## The frame from the scroll handler -/

/-- **In the air and rising**: the state 1 or 2, and the vertical speed negative -/
def Rising (sy : Syms) (m : Machine) : Prop :=
  (m.ram.get! (I sy.Player_State) = 1 ∨ m.ram.get! (I sy.Player_State) = 2) ∧ m.ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0x80

/-- the bytes of `vKeep` are out of the block buffers, and the state and the vertical speed are two bytes -/
def apartB (sy : Syms) (P : Places) : Bool :=
  (vKeep sy).all (fun x => decide (x < P.bufLo) || decide (P.bufLo + P.bufN ≤ x)) && I sy.Player_State != I sy.Player_Y_Speed

/-- **The erase of a coin writes only in the block buffers** -/
theorem erase_keep {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hO : PlacesOK E P) (hs : Sim E F A m) (hn : A.nmi = false)
    (hpc : A.pc = P.erase) (hh : SiteOK P m) {x : Nat} (hx : x < P.bufLo ∨ P.bufLo + P.bufN ≤ x) : (go step m).2.ram.get! x = m.ram.get! x := by
  apply StepWrites.step_ram
  intro hi
  unfold StepWrites.stepLocs at hi
  have hn' : m.nmiPending = false := by rw [hs.nmi]; exact hn
  rw [if_neg (by simp [hn']), if_neg (by simp [hs.halted])] at hi
  have hmp : m.pc = P.erase := by rw [hs.pc]; exact hpc
  have hpm : m.pc ≥ 0x8000 := by rw [hmp]; exact hO.erase.1
  rw [TaintRun.fetch_rom hpm] at hi
  have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91 := by rw [hs.prg, hs.mask, hmp]; exact hO.erase.2
  rw [hop] at hi
  have hw : StepWrites.wOf 0x91 = StepWrites.wIzy := rfl
  rw [hw] at hi
  obtain ⟨g1, g2, g3⟩ := hh.erase hmp
  have e : (StepWrites.wIzy).locs { m with pc := m.pc + 1 } = StepWrites.ramIdx (ScreenPage.writeAddr m) := rfl
  rw [e] at hi
  unfold StepWrites.ramIdx at hi
  rw [if_pos g1] at hi
  simp only [List.mem_singleton] at hi
  omega


/-! ### The pieces at the scroll handler -/

section
variable {E : Env} {F : Nat × UInt8}


theorem vy_cases : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 ∨ UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel

theorem st_cases : ∀ n : Fin 256, UInt8.ofNat n.val = 0 ∨ UInt8.ofNat n.val = 1 ∨ UInt8.ofNat n.val = 2 ∨ UInt8.ofNat n.val = 3 ∨
    ∃ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), UInt8.ofNat n.val &&& b = b := by decide +kernel

theorem hi_not12 : ∀ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), (1 : UInt8) &&& b ≠ b ∧ (2 : UInt8) &&& b ≠ b := by decide

theorem getK_up {sy : Syms} {A : AS} {c : UInt8} (hap : I sy.Player_State ≠ I sy.Player_Y_Speed) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) :
    ((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true)).getK
      (I sy.Player_State) = AB.known c ∧
    ((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true)).getK
      (I sy.Player_Y_Speed) = withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hvl : I sy.Player_Y_Speed < 2048 := PipeTransitionAll.mask_lt _
  constructor
  · rw [getK_setK_ne (Ne.symm hap), getK_setK_self (by rw [hsz.1]; exact hsl) (by rw [hsz.2]; exact hsl)]
  · rw [getK_setK_self (by rw [setK_ram_size, hsz.1]; exact hvl) (by rw [setK_kn_size, hsz.2]; exact hvl)]

theorem getK_one {A : AS} {i : Nat} {w : AB} (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) (hi : i < 2048) : (A.setK i w).getK i = w := by
  rw [getK_setK_self (by rw [hsz.1]; exact hi) (by rw [hsz.2]; exact hi)]

/-- every piece is in the air and rising with the bit set, or not in the air and rising, marked `[2]` -/
theorem piecesQ_class {sy : Syms} {A A₁ : AS} {x : Machine} (hap : I sy.Player_State ≠ I sy.Player_Y_Speed) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048)
    (h : A₁ ∈ piecesQ sy A) (hs : Sim E F A₁ x) :
    (A₁.spent = true ∧ A₁.log = A.log ∧ Rising sy x) ∨ (A₁.spent = A.spent ∧ A₁.log = [2] ∧ ¬ Rising sy x) := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hvl : I sy.Player_Y_Speed < 2048 := PipeTransitionAll.mask_lt _
  have up : ∀ c, (c = 1 ∨ c = 2) → A₁ ∈ upP sy A c → (A₁.spent = true ∧ A₁.log = A.log ∧ Rising sy x) := by
    intro c hc hm
    unfold upP at hm
    split at hm
    · obtain rfl := List.mem_singleton.1 hm
      have g := getK_up (c := c) hap hsz
      have h1 : (((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true)).getK
        (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have h2 : (((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true)).getK
        (I sy.Player_Y_Speed)).mem (x.ram.get! (I sy.Player_Y_Speed)) := hs.ram _ hvl
      rw [g.1] at h1
      rw [g.2] at h2
      refine ⟨rfl, rfl, ?_, withBit_true_mem (by decide) h2⟩
      rw [mem_known h1]
      exact hc
    · cases hm
  have notR : ∀ c, c ≠ 1 → c ≠ 2 → x.ram.get! (I sy.Player_State) = c → ¬ Rising sy x := by
    intro c h1 h2 h3 hr
    rcases hr.1 with e | e <;> rw [h3] at e
    · exact h1 e
    · exact h2 e
  simp only [piecesQ, List.mem_append] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact Or.inl (up 1 (Or.inl rfl) h)
  · exact Or.inl (up 2 (Or.inr rfl) h)
  · unfold fallP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      refine Or.inr ⟨rfl, rfl, fun hr => ?_⟩
      have h2 : ((A.setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).getK (I sy.Player_Y_Speed)).mem
        (x.ram.get! (I sy.Player_Y_Speed)) := hs.ram _ hvl
      rw [getK_one hsz hvl] at h2
      have := withBit_false_mem h2
      rw [hr.2] at this
      exact absurd this (by decide)
    · cases h
  · unfold knP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (AB.known 0)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      exact Or.inr ⟨rfl, rfl, notR 0 (by decide) (by decide) (mem_known h1)⟩
    · cases h
  · unfold knP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (AB.known 3)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      exact Or.inr ⟨rfl, rfl, notR 3 (by decide) (by decide) (mem_known h1)⟩
    · cases h
  · unfold hiP at h
    obtain ⟨b, hb, h⟩ := List.mem_flatMap.1 h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true)).getK (I sy.Player_State)).mem
        (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      have h3 := withBit_true_mem hb h1
      refine Or.inr ⟨rfl, rfl, fun hr => ?_⟩
      have hn := hi_not12 b hb
      rcases hr.1 with e | e <;> rw [e] at h3
      · exact hn.1 h3
      · exact hn.2 h3
    · cases h

/-- the pieces cover every machine of the state -/
theorem piecesQ_cover {sy : Syms} {A : AS} {x : Machine} (hr : A.rk = false) (hs : Sim E F A x) : ∃ A₁ ∈ piecesQ sy A, Sim E F A₁ x := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hvl : I sy.Player_Y_Speed < 2048 := PipeTransitionAll.mask_lt _
  have ms := hs.ram _ hsl
  have mv := hs.ram _ hvl
  generalize hst : x.ram.get! (I sy.Player_State) = st at ms
  generalize hvy : x.ram.get! (I sy.Player_Y_Speed) = vy at mv
  have upC : ∀ c, st = c → vy &&& 0x80 = 0x80 → ∃ A₁ ∈ upP sy A c, Sim E F A₁ x := by
    intro c hc hv
    subst hc
    have c1 : canBe (A.getK (I sy.Player_State)) st = true := canBe_of ms
    have c2 : canBit (A.getK (I sy.Player_Y_Speed)) 0x80 true = true := canBit_of mv true (by rw [hv]; decide)
    unfold upP
    rw [if_pos (by rw [c1, c2]; rfl)]
    exact ⟨_, List.mem_singleton.2 rfl, sim_bits (PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hs (by rw [hst]; exact mem_known_self st))
        (by rw [hvy]; exact withBit_true_of (by decide) mv hv)) hr true _⟩
  have L : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₁ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_left _ h
  have R : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₂ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_right _ h
  rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) vy with hv | hv
  · have c2 : canBit (A.getK (I sy.Player_Y_Speed)) 0x80 false = true := canBit_of mv false (by rw [hv]; decide)
    have hm : ({ A.setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false) with log := [2] } : AS) ∈ fallP sy A := by
      unfold fallP
      rw [if_pos c2]
      exact List.mem_singleton.2 rfl
    exact ⟨_, L (L (L (R hm))), sim_bits (PipeEntryRule.sim_setK' hs (by rw [hvy]; exact withBit_false_of mv hv)) hr _ _⟩
  · rcases (u8_all (P := fun t => t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ ∃ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), t &&& b = b) st_cases) st with
      e | e | e | e | ⟨b, hb, e⟩
    · have c1 : canBe (A.getK (I sy.Player_State)) 0 = true := by rw [← e]; exact canBe_of ms
      have hm : ({ A.setK (I sy.Player_State) (AB.known 0) with log := [2] } : AS) ∈ knP sy A 0 := by
        unfold knP
        rw [if_pos c1]
        exact List.mem_singleton.2 rfl
      exact ⟨_, L (L (R hm)), sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst, e]; exact mem_known_self 0)) hr _ _⟩
    · obtain ⟨A₁, h1, h2⟩ := upC 1 e hv
      exact ⟨A₁, L (L (L (L (L h1)))), h2⟩
    · obtain ⟨A₁, h1, h2⟩ := upC 2 e hv
      exact ⟨A₁, L (L (L (L (R h1)))), h2⟩
    · have c1 : canBe (A.getK (I sy.Player_State)) 3 = true := by rw [← e]; exact canBe_of ms
      have hm : ({ A.setK (I sy.Player_State) (AB.known 3) with log := [2] } : AS) ∈ knP sy A 3 := by
        unfold knP
        rw [if_pos c1]
        exact List.mem_singleton.2 rfl
      exact ⟨_, L (R hm), sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst, e]; exact mem_known_self 3)) hr _ _⟩
    · have c1 : canBit (A.getK (I sy.Player_State)) b true = true := canBit_of ms true (by
        rw [e]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      have hm : ({ A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true) with log := [2] } : AS) ∈ hiP sy A := by
        unfold hiP
        exact List.mem_flatMap.2 ⟨b, hb, by rw [if_pos c1]; exact List.mem_singleton.2 rfl⟩
      exact ⟨_, R hm, sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst]; exact withBit_true_of hb ms e)) hr _ _⟩
end


/-- a piece with the bit, that meets `ok`, keeps the bytes of `vKeep` over its step -/
theorem keepV_step {sy : Syms} {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {y : Machine} (hO : PlacesOK E P) (hap : apartB sy P = true)
    (hs : Sim E F A y) (hh : SiteOK P y) (hok : (phB sy E P).ok A = true) (hb : A.spent = true) :
    ∀ x ∈ vKeep sy, (go step y).2.ram.get! x = y.ram.get! x := by
  intro x hx
  have h1 : mayWriteV sy E P A = false := by simpa [phB, hb] using hok
  unfold mayWriteV at h1
  cases hc : (A.pc == P.erase && !A.nmi) with
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    simp only [apartB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hap
    exact erase_keep hO hs hc.2 hc.1 hh (hap.1 x hx)
  | false =>
    rw [hc] at h1
    simp only [Bool.not_false, Bool.true_and, Bool.not_eq_false'] at h1
    exact StepWrites.keep_step hs h1 x (List.contains_iff_mem.2 hx)

/-- **The frame from the scroll handler.** The frame comes to the scroll handler at most once. If it comes there in the air and rising, and ends in the player's routine, no
step from there to its end writes the bytes of `vKeep`. The frame starts in the room's condition, and each instruction meets `SiteOK`. -/
theorem after_Q {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV (phB sy E P) E P r K C Fu)
    (hfin : C.fin = finB P r) (hap : apartB sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerSubs → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerSubs) ∧
    (∀ j, (trace m i j).pc = sy.PlayerSubs → (trace m i j).frame = m.frame → Rising sy (trace m i j) → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       ∀ x ∈ vKeep sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) := by
  obtain ⟨S, hw, hs, s1, s2, s3⟩ := start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  have hsz : ∀ (A : AS) (y : Machine), Sim C.E (m.frame, 2) A y → A.ram.size = 2048 ∧ A.kn.size = 2048 := fun _ _ hs => ⟨hs.szR, hs.szK⟩
  have hap2 : I sy.Player_State ≠ I sy.Player_Y_Speed := by
    simp only [apartB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hap
    exact hap.2
  let Φ : Nat → Bool → List Nat → Prop := fun j b l =>
    (∀ j₀, j₀ < j → (trace m i j₀).pc = sy.PlayerSubs → (b = true ∨ l ≠ [])) ∧
    (b = true → l = [] ∧ ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = sy.PlayerSubs ∧ ∀ x ∈ vKeep sy, (trace m i j).ram.get! x = (trace m i j₀).ram.get! x) ∧
    (l = [2] → ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = sy.PlayerSubs ∧ ¬ Rising sy (trace m i j₀)) ∧
    (l = [] ∨ l = [1] ∨ l = [2])
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phB sy E P).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    show ∃ A₁ ∈ (if A'.pc == sy.PlayerSubs && !A'.spent && A'.log.isEmpty then piecesQ sy A'
      else if A'.spent && mayWriteV sy E P A' then [{ A' with spent := false, log := [1] }] else [A']), _
    split
    · exact piecesQ_cover hr hsx
    · split
      · exact ⟨_, List.mem_singleton.2 rfl, sim_bits hsx hr false [1]⟩
      · exact ⟨A', List.mem_singleton.2 rfl, hsx⟩
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phB sy E P).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phB sy E P).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2, p3, p4⟩ hs' hf hr hA₁ hs₁ hok
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    have keep : A₁.spent = true → ∀ x ∈ vKeep sy, (trace m i (j + 1)).ram.get! x = (trace m i j).ram.get! x := by
      intro hb x hx
      rw [trace_succ hf hs'.halted]
      have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
      exact keepV_step h.places hap hs₂ (hk j) hok hb x hx
    change A₁ ∈ (if A'.pc == sy.PlayerSubs && !A'.spent && A'.log.isEmpty then piecesQ sy A'
      else if A'.spent && mayWriteV sy E P A' then [{ A' with spent := false, log := [1] }] else [A']) at hA₁
    split at hA₁
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
      obtain ⟨⟨hq, hsp⟩, hlg⟩ := hc
      rcases piecesQ_class hap2 (hsz A' _ hs') hA₁ hs₁ with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
      · rw [c1, c2, hlg]
        refine ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨rfl, j, by omega, by rw [hpc, hq], keep c1⟩, fun h => by simp at h, Or.inl rfl⟩
      · rw [c1, c2, hsp]
        refine ⟨fun _ _ _ => Or.inr (by simp), fun h => by simp at h, fun _ => ⟨j, by omega, by rw [hpc, hq], c3⟩, Or.inr (Or.inr rfl)⟩
    · rename_i hc
      split at hA₁
      · obtain rfl := List.mem_singleton.1 hA₁
        exact ⟨fun _ _ _ => Or.inr (by simp), fun h => by simp at h, fun h => by simp at h, Or.inr (Or.inl rfl)⟩
      · obtain rfl := List.mem_singleton.1 hA₁
        refine ⟨fun j₀ hj₀ hq₀ => ?_, fun hb => ?_, fun hl => ?_, p4⟩
        · rcases Nat.lt_or_ge j₀ j with hlt | hge
          · exact p1 j₀ hlt hq₀
          · rw [show j₀ = j by omega, hpc] at hq₀
            simp only [hq₀, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_and] at hc
            cases hsp : A₁.spent with
            | true => exact Or.inl rfl
            | false => exact Or.inr (hc hsp)
        · obtain ⟨l1, j₀, a1, a2, a3⟩ := p2 hb
          exact ⟨l1, j₀, by omega, a2, fun x hx => by rw [keep hb x hx]; exact a3 x hx⟩
        · obtain ⟨j₀, a1, a2, a3⟩ := p3 hl
          exact ⟨j₀, by omega, a2, a3⟩
  have h0 : Φ 0 S.spent S.log := by
    refine ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun hb => ?_, fun hl => ?_, Or.inl s2⟩
    · rw [s1] at hb
      cases hb
    · rw [s2] at hl
      cases hl
  obtain ⟨hall, J, hJ1, hJ2, hJ3, B, hB1, hB2, hB3⟩ := frame_of_walkV (Z := phB sy E P) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0 hstep
  have uniq : ∀ j j', j < j' → (trace m i j).pc = sy.PlayerSubs → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerSubs := by
    intro j j' hlt hq hj' hq'
    obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = sy.PlayerSubs := by rw [← hsA.pc]; exact hq'
    simp only [phB, hApc, beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hpre
    rcases q1 j hlt hq with e | e
    · rw [hpre.1] at e
      cases e
    · exact e hpre.2
  refine ⟨uniq, fun jq hq hf hrise hrt x hx => ?_⟩
  have hjJ : jq < J := by
    rcases Nat.lt_or_ge jq J with h1 | h1
    · exact h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (jq - J)
      rw [show J + (jq - J) = jq by omega] at e
      rw [e, hJ1] at hf
      omega
  -- the end is in the player's routine, so the state at the end is not marked `[1]`
  have hl1 : B.log ≠ [1] := by
    intro hl
    rw [hfin] at hB1
    simp only [finB, hl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB1
    obtain ⟨⟨a1, a2⟩, a3⟩ := hB1
    have e := isK_eq a2 (hB2.ram _ a1)
    rw [← hJ3, hrt] at e
    exact a3 e.symm
  obtain ⟨q1, q2, q3, q4⟩ := hB3
  have only : ∀ j₀, j₀ < J → (trace m i j₀).pc = sy.PlayerSubs → j₀ = jq := by
    intro j₀ h1 h2
    rcases Nat.lt_trichotomy j₀ jq with e | e | e
    · exact absurd hq (uniq j₀ jq e h2 hf)
    · exact e
    · exact absurd h2 (uniq jq j₀ e hq (hJ2 j₀ h1))
  rcases q4 with e | e | e
  · rcases q1 jq hjJ hq with e2 | e2
    · obtain ⟨_, j₀, a1, a2, a3⟩ := q2 e2
      rw [only j₀ a1 a2] at a3
      rw [hJ3]
      exact a3 x hx
    · exact absurd e e2
  · exact absurd e hl1
  · obtain ⟨j₀, a1, a2, a3⟩ := q3 e
    rw [only j₀ a1 a2] at a3
    exact absurd hrise a3

/-! ## On the room -/

section
open ScreenPage (placesR envR refR aidsOf)

/-- the walk to the player's routine, on the room: a state at the frame's end is not at the player's routine, and has come there or knows the game paused -/
abbrev cfgA (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  cfgOfV sy (phA sy (envR sy nm m0) (FrameModel.ctrlStack sy m0) (CtrlKeep.pauseI sy m0)) (finA sy (CtrlKeep.pauseI sy m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

/-- the walk from the scroll handler, on the room -/
abbrev cfgB (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  cfgOfV sy (phB sy (envR sy nm m0) (placesR sy nm m0)) (finB (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

/-- the check of the walk to the player's routine -/
def checkA (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  walkCheckV sy (phA sy (envR sy nm m0) (FrameModel.ctrlStack sy m0) (CtrlKeep.pauseI sy m0)) (finA sy (CtrlKeep.pauseI sy m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

/-- the check of the walk from the scroll handler -/
def checkB (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  walkCheckV sy (phB sy (envR sy nm m0) (placesR sy nm m0)) (finB (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

end

/-! ## One frame in the room, in the air and rising -/

section
open VertAir (AtV vertAirOK vert_air)
open FrameModel (Rom stepN)

theorem vsOf_eq_of {sy : Syms} {m m' : Machine} (h : ∀ x ∈ vKeep sy, m.ram.get! x = m'.ram.get! x) : VertModel.vsOf sy m = VertModel.vsOf sy m' := by
  have e : ∀ a : UInt16, I a ∈ vKeep sy → peek m a = peek m' a := fun a ha => h _ ha
  unfold VertModel.vsOf
  rw [e _ (by simp [vKeep]), e _ (by simp [vKeep]), e _ (by simp [vKeep]), e _ (by simp [vKeep]), e _ (by simp [vKeep]), e _ (by simp [vKeep]),
    e _ (by simp [vKeep]), e _ (by simp [vKeep]), e sy.A_B_Buttons (by simp [vKeep])]

/-- **One frame of the room that is in the air and rising follows `vstep`.** The frame starts in the room's condition `M` in the air (the state 1 or 2), each
instruction meets `SiteOK`, the frame comes to the player's routine at instruction `k` in the state `AtV` and does not end in the next `moveLen` instructions. At the frame's
start the jump's halt value is 1 if the state is 1, and A of the frame before is A. If `vstep` on `vmach` with the stored speed 0 leaves him in the air and rising, and the
frame ends in the player's routine, the vertical bytes at the frame's end are `vstep`'s. The checks: the two walks of the room, `apartB`, `vertAirOK`. Each instruction of the frame
that is not at the idle loop `idle` runs at least 64 dots before the frame's end (`ht`): so the frame does not end during the movement (`FrameModel.trace_inFrame`). -/
theorem air_frame {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CB : CfgS} {Fa Fb : Nat}
    (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine) (hB : OKV (phB sy E P) E P r K CB Fb) (hfin : CB.fin = finB P r)
    (hap : apartB sy P = true) (hV : vertAirOK sy m0 S = true) {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (hrise : ((VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 1 ∨
        (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 2) ∧
      (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&& 0x80 = 0x80)
    (hrt : (frame M i).ram.get! P.rtI = r.ram.get! P.rtI) :
    VertModel.vsOf sy (frame M i) = VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 := by
  obtain ⟨a1, a2, _, a4⟩ := before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR.pc
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR.pc
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, I a ∈ vKeepA sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ ha
  have hvs : VertModel.vsOf sy (trace M i k) = VertModel.vsOf sy M :=
    vsOf_eq_of (fun x hx => hkeep x (List.mem_append_left _ hx))
  have est : peek (trace M i k) sy.Player_State = peek M sy.Player_State := eq _ (by simp [vKeepA, vKeep])
  obtain ⟨kk, _, _, hpc, _, hv, hIn⟩ := vert_air hV hR (by rw [est]; exact hst)
    (by rw [est, eq sy.DiffToHaltJump (by simp [vKeepA])]; exact hd)
    (by rw [eq sy.PreviousA_B_Buttons (by simp [vKeepA]), eq sy.A_B_Buttons (by simp [vKeepA, vKeep])]; exact hp)
  rw [hvs] at hv
  obtain ⟨htr, hfq⟩ := FrameModel.trace_inFrame hidle hfk hIn ht kk (Nat.le_refl kk)
  rw [← htr] at hpc hv
  obtain ⟨_, b2⟩ := after_Q hB hfin hap hm hk
  have hrs : Rising sy (trace M i (k + kk)) := by
    have e1 : (VertModel.vsOf sy (trace M i (k + kk))).st = (trace M i (k + kk)).ram.get! (I sy.Player_State) := rfl
    have e2 : (VertModel.vsOf sy (trace M i (k + kk))).vy = (trace M i (k + kk)).ram.get! (I sy.Player_Y_Speed) := rfl
    unfold Rising
    rw [← e1, ← e2, hv]
    exact hrise
  rw [vsOf_eq_of (b2 (k + kk) hpc hfq hrs hrt), hv]

end

/-! ## The checks, and one frame of a jump's first frames in the room -/

/-- **The checks on the ROM** of this file: the two walks of the room, the bytes apart, the movement routine in the air (`VertAir.vertAirOK`), and the jumps' first `k`
frames (`bridgeOK`) -/
structure VChecks (sy : Syms) (nm : Names) (m0 : Machine) (h k : Nat) : Prop where
  a : checkA sy nm m0 = true
  b : checkB sy nm m0 = true
  apart : apartB sy (ScreenPage.placesR sy nm m0) = true
  air : VertAir.vertAirOK sy m0 (FrameModel.ctrlStack sy m0) = true
  bridge : VertAir.bridgeOK sy m0 (FrameModel.ctrlStack sy m0) h k = true

/-- **A frame of the room on a jump's first frames follows `vstep` on `m0`.** The frame starts in the room's condition, on a state of a jump from the floor
(`arcSet`), and `vstep` on `m0` with its A leaves him on such a state, rising. The other conditions are those of `air_frame`. -/
theorem air_arc {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : VChecks sy nm m0 h kk) {idle : UInt16} (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) idle = true)
    {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : VertAir.AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i k))
    (htm : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (hu : VertModel.vsOf sy M ∈ (VertAir.arcSet sy m0 h kk).map (·.s))
    (ht : Jump.vstep sy m0 (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∈ (VertAir.arcSet sy m0 h kk).map (·.s))
    (hvy : (Jump.vstep sy m0 (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&& 0x80 = 0x80)
    (hrt : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    VertModel.vsOf sy (frame M i) = Jump.vstep sy m0 (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 := by
  obtain ⟨u, hu1, hu2⟩ := List.mem_map.1 hu
  obtain ⟨t, ht1, ht2⟩ := List.mem_map.1 ht
  obtain ⟨b1, b2⟩ := VertAir.bridge_of hV.bridge hu1
  obtain ⟨c1, _⟩ := VertAir.bridge_of hV.bridge ht1
  have hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2 := by
    have e : (VertModel.vsOf sy M).st = peek M sy.Player_State := rfl
    rw [← e, ← hu2]
    exact b1
  have hbr := b2 (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0)
  rw [hu2] at hbr
  rw [← hbr]
  refine air_frame (CtrlKeep.pauseI_lt sy m0) (okV_of_check hV.a) (fun B hB => finA_pc hB) (okV_of_check hV.b) rfl hV.apart hV.air hidle hm hs hR htm hst hd hp ⟨?_, ?_⟩ hrt
  · rw [hbr, ← ht2]
    exact c1
  · rw [hbr]
    exact hvy

end Smbrta.RoomVert
