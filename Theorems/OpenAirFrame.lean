import Theorems.OpenAir

/-!
# A frame of the opening in the air, or at a takeoff: what the walk of `OpenAir` shows

The facts `PhiA` that the walk carries along a frame, phase by phase (`OpenAir.Phase`), and the theorems on one frame from the cut of `CtrlKeep`:

* `air_frame`: a frame in the air comes to the scroll handler `Q` once from the player's routine on, at `k₁`; then to the return of the collision routine at `k₂`;
  there the halt relation holds, and if the height at `k₁` is below `y₀ + LandDepth` with the high byte 1 and the state 1 or 2, the vertical bytes at `k₂` are `land` of
  those at `k₁`, with the high byte 1 and the halt value of `k₁`.
* `take_frame`: a takeoff on the ground at `y₀` with the stored speed `u ≤ top` comes to the return at `k₂` with the vertical bytes of the model's takeoff `OpenAir.expT u`,
  the high byte 1 and the halt value 1.
* `gen_frame`: a takeoff of any speed comes to the return with the halt relation.

There is no game data in this file. Page: `1-1/a-5-7-2-OpenAir.md`.
-/

namespace Smbrta.OpenAir

open PipeTransition (frame)
open TaintRun (AS Sim Env AB)
open PipeWrites (Guard knownOf SG)
open FrameKeep (Watch CfgK Spot CleanK)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open OpenWalk (PhK walkP)
open RoomVert (canBe canBit withBit canBe_of canBit_of withBit_true_of withBit_false_of withBit_true_mem withBit_false_mem)

section
variable {E : Env} {F : Nat × UInt8}

/-! ## The abstract states -/

theorem sim_log {A : AS} {m : Machine} (hs : Sim E F A m) (l : List Nat) : Sim E F { A with log := l } m := { hs with }

theorem sim_forgetV (sy : Syms) {A : AS} {m : Machine} (hs : Sim E F A m) : Sim E F (forgetV sy A) m := by
  unfold forgetV
  generalize pAll sy = L
  induction L generalizing A with
  | nil => exact hs
  | cons i L ih => exact ih (PipeEntryRule.sim_setK' hs (TaintRun.mem_top _))

theorem forgetV_pc (sy : Syms) (A : AS) : (forgetV sy A).pc = A.pc := by
  unfold forgetV
  generalize pAll sy = L
  induction L generalizing A with
  | nil => rfl
  | cons i L ih => exact ih _

theorem forgetV_k (sy : Syms) (A : AS) : (forgetV sy A).k = A.k := by
  unfold forgetV
  generalize pAll sy = L
  induction L generalizing A with
  | nil => rfl
  | cons i L ih => exact ih _

/-- a known byte of a state that covers a machine is the machine's byte -/
theorem kn_val {A : AS} {m : Machine} (hs : Sim E F A m) {i : Nat} (hi : i < 2048) {v : UInt8} (h : knIs (A.getK i) v = true) : m.ram.get! i = v := by
  simp only [knIs, Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.2]
  exact PipeEntryRule.known_eq h.1 (hs.ram i hi)

theorem kn_ne {A : AS} {m : Machine} (hs : Sim E F A m) {i : Nat} (hi : i < 2048) (h : ((A.getK i).isK && (A.getK i).v != 1) = true) : m.ram.get! i ≠ 1 := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rw [PipeEntryRule.known_eq h.1 (hs.ram i hi)]
  exact h.2

end

/-! ## The facts along the frame -/

section
variable {sy : Syms}

/-- no instruction from `a` to before `b` is at `pc` -/
def NoPc (m : Machine) (i : UInt8) (pc : UInt16) (a b : Nat) : Prop := ∀ j, a ≤ j → j < b → (trace m i j).pc ≠ pc

/-- the bytes of `L` of `y` are those of `x` -/
def Keeps (L : List Nat) (x y : Machine) : Prop := ∀ b ∈ L, y.ram.get! b = x.ram.get! b

/-- the halt relation: in a jump the jump's halt value is 1 -/
def HaltM (sy : Syms) (m : Machine) : Prop := peek m sy.Player_State = 1 → peek m sy.DiffToHaltJump = 1

/-- at `Q`: the height below `y₀ + LandDepth`, the high byte 1, the state 1 or 2 -/
def Ok1 (sy : Syms) (K : Ctx) (m : Machine) : Prop :=
  (peek m sy.Player_Y_Position).toNat < K.y0.toNat + K.d.toNat ∧ peek m sy.Player_Y_HighPos = 1 ∧ (peek m sy.Player_State = 1 ∨ peek m sy.Player_State = 2)

/-- not landing: below `y₀`, or rising -/
def NotLand (sy : Syms) (K : Ctx) (m : Machine) : Prop := peek m sy.Player_Y_Position < K.y0 ∨ peek m sy.Player_Y_Speed &&& 0x80 ≠ 0

/-- landing: at or below `y₀`, falling -/
def LandM (sy : Syms) (K : Ctx) (m : Machine) : Prop := K.y0 ≤ peek m sy.Player_Y_Position ∧ peek m sy.Player_Y_Speed &&& 0x80 = 0

/-- the first arrival at `Q` from `n₀` on is `k₁` -/
def AtQ (sy : Syms) (m : Machine) (i : UInt8) (n₀ k₁ : Nat) : Prop := n₀ ≤ k₁ ∧ (trace m i k₁).pc = sy.PlayerSubs ∧ NoPc m i sy.PlayerSubs n₀ k₁

/-- **The facts after `j` instructions in the phase `l`** -/
def PhiA (sy : Syms) (K : Ctx) (ex : Nat → Jump.VS) (m : Machine) (i : UInt8) (n₀ j : Nat) (l : List Nat) : Prop :=
  match decode l with
  | .pre => NoPc m i sy.PlayerSubs n₀ j
  | .q1 | .q => ∃ k₁, AtQ sy m i n₀ k₁ ∧ k₁ < j ∧ NoPc m i sy.PlayerSubs (k₁ + 1) j ∧ NoPc m i K.cR (k₁ + 1) j ∧
      Keeps (pAll sy) (trace m i k₁) (trace m i j)
  | .k1 | .k => ∃ k₁, AtQ sy m i n₀ k₁ ∧ k₁ < j ∧ NoPc m i sy.PlayerSubs (k₁ + 1) j ∧ NoPc m i K.cR (k₁ + 1) j ∧
      Keeps (pAll sy) (trace m i k₁) (trace m i j) ∧ Ok1 sy K (trace m i k₁) ∧ NotLand sy K (trace m i k₁)
  | .l1 | .l => ∃ k₁, AtQ sy m i n₀ k₁ ∧ k₁ < j ∧ NoPc m i sy.PlayerSubs (k₁ + 1) j ∧ NoPc m i K.cR (k₁ + 1) j ∧
      Keeps (pRest sy) (trace m i k₁) (trace m i j) ∧ Ok1 sy K (trace m i k₁) ∧ LandM sy K (trace m i k₁)
  | .n1 | .n => ∃ k₁, AtQ sy m i n₀ k₁ ∧ k₁ < j ∧ NoPc m i sy.PlayerSubs (k₁ + 1) j ∧ NoPc m i K.cR (k₁ + 1) j ∧ ¬ Ok1 sy K (trace m i k₁)
  | .aft => ∃ k₁ k₂, AtQ sy m i n₀ k₁ ∧ k₁ < k₂ ∧ k₂ < j ∧ NoPc m i sy.PlayerSubs (k₁ + 1) j ∧ (trace m i k₂).pc = K.cR ∧ NoPc m i K.cR (k₁ + 1) k₂ ∧
      (Ok1 sy K (trace m i k₁) → VertModel.vsOf sy (trace m i k₂) = OpenJump.land K.y0 (VertModel.vsOf sy (trace m i k₁)) ∧
        peek (trace m i k₂) sy.Player_Y_HighPos = 1 ∧ HaltM sy (trace m i k₂))
  | .tk u => peek (trace m i n₀) sy.Player_XSpeedAbsolute = u.toUInt8 ∧ NoPc m i K.cR n₀ j
  | .tkd => ∃ k₂ u, n₀ ≤ k₂ ∧ k₂ < j ∧ (trace m i k₂).pc = K.cR ∧ NoPc m i K.cR n₀ k₂ ∧ peek (trace m i n₀) sy.Player_XSpeedAbsolute = u.toUInt8 ∧
      VertModel.vsOf sy (trace m i k₂) = ex u ∧ peek (trace m i k₂) sy.Player_Y_HighPos = 1 ∧ peek (trace m i k₂) sy.DiffToHaltJump = 1
  | .bad => False

/-- **The choice of a piece at `Q`**: an exact piece only if the machine meets `Ok1`, the rest only if it does not -/
def PsiA (sy : Syms) (K : Ctx) (m : Machine) (i : UInt8) (j : Nat) (A : AS) : Prop :=
  ((decode A.log = .k1 ∨ decode A.log = .l1) → Ok1 sy K (trace m i j)) ∧ (decode A.log = .n1 → ¬ Ok1 sy K (trace m i j))

end

/-! ## The pieces at `Q` -/

section
variable {E : Env} {F : Nat × UInt8} {sy : Syms}

theorem I_lt (a : UInt16) : I a < 2048 := PipeTransitionAll.mask_lt a

theorem peek_eq (m : Machine) (a : UInt16) : peek m a = m.ram.get! (I a) := rfl

theorem sim_atY {A : AS} {m : Machine} (hs : Sim E F A m) {y : UInt8} (hy : peek m sy.Player_Y_Position = y) (hh : peek m sy.Player_Y_HighPos = 1) :
    Sim E F (atY sy A y) m := by
  unfold atY
  refine PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hs ?_) ?_
  · rw [← peek_eq, hy]; exact TaintRun.mem_known_self _
  · rw [← peek_eq, hh]; exact TaintRun.mem_known_self _

theorem toUInt8_toNat (y : UInt8) : y.toNat.toUInt8 = y := by simp

/-- **A piece covers the machine at `Q`**: the exact one of its height (with bit 7 of the vertical speed, and the state when falling near the ground), if the machine
meets `Ok1`; the state itself marked `[9, 1]` if not -/
theorem split_cover (K : Ctx) (hyd : K.y0.toNat + K.d.toNat < 256) {A : AS} {m : Machine} (hs : Sim E F A m) :
    ∃ A₂ ∈ piecesQ sy K.y0 K.d A, Sim E F A₂ m ∧ ((decode A₂.log = .k1 ∨ decode A₂.log = .l1) → Ok1 sy K m) ∧ (decode A₂.log = .n1 → ¬ Ok1 sy K m) := by
  by_cases hok : Ok1 sy K m
  · have hok' := hok
    obtain ⟨hy, hhi, hst⟩ := hok
    generalize hY : peek m sy.Player_Y_Position = y at hy
    have cy : canBe (A.getK (I sy.Player_Y_Position)) y = true := canBe_of (by rw [← hY]; exact hs.ram _ (I_lt _))
    have ch : canBe (A.getK (I sy.Player_Y_HighPos)) 1 = true := canBe_of (by rw [← hhi]; exact hs.ram _ (I_lt _))
    have hsY := sim_atY (sy := sy) hs hY hhi
    have mvy : (A.getK (I sy.Player_Y_Speed)).mem (peek m sy.Player_Y_Speed) := hs.ram _ (I_lt _)
    have mst : (A.getK (I sy.Player_State)).mem (peek m sy.Player_State) := hs.ram _ (I_lt _)
    by_cases hlt : y < K.y0
    · refine ⟨{ atY sy A y with log := [2, 1] }, ?_, sim_log hsY _, fun _ => hok', fun h => by simp [decode] at h⟩
      unfold piecesQ
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.2 ⟨y.toNat, List.mem_range.2 (UInt8.lt_iff_toNat_lt.1 hlt), ?_⟩))
      simp only [toUInt8_toNat, cy, ch, Bool.and_self, if_true]
    · have hge : K.y0.toNat ≤ y.toNat := by
        have := UInt8.lt_iff_toNat_lt (a := y) (b := K.y0)
        by_cases h : y.toNat < K.y0.toNat
        · exact absurd (this.2 h) hlt
        · omega
      have hjd : y.toNat - K.y0.toNat < K.d.toNat := by omega
      have hyj : (K.y0.toNat + (y.toNat - K.y0.toNat)).toUInt8 = y := by
        rw [show K.y0.toNat + (y.toNat - K.y0.toNat) = y.toNat by omega]; exact toUInt8_toNat y
      have near : ∀ B, B ∈ ((if canBit (A.getK (I sy.Player_Y_Speed)) 0x80 true then
            [{ (atY sy A y).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true) with log := [2, 1] }] else []) ++
          ([(1 : UInt8), 2].filterMap fun c => if canBit (A.getK (I sy.Player_Y_Speed)) 0x80 false && canBe (A.getK (I sy.Player_State)) c then
            some { ((atY sy A y).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).setK (I sy.Player_State) (AB.known c) with
              log := [3, 1] } else none)) → B ∈ piecesQ sy K.y0 K.d A := by
        intro B hB
        unfold piecesQ
        refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨y.toNat - K.y0.toNat, List.mem_range.2 hjd, ?_⟩))
        simp only [hyj, cy, ch, Bool.and_self, if_true]
        exact hB
      rcases OpenFlat.and80_cases (peek m sy.Player_Y_Speed) with hv | hv
      · -- falling: the state 1 or 2
        have cv : canBit (A.getK (I sy.Player_Y_Speed)) 0x80 false = true := canBit_of mvy false (by simp [hv])
        rcases hst with hc | hc
        · refine ⟨{ ((atY sy A y).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).setK (I sy.Player_State) (AB.known 1) with
            log := [3, 1] }, near _ (List.mem_append_right _ (List.mem_filterMap.2 ⟨1, List.mem_cons_self, ?_⟩)), ?_, fun _ => hok', fun h => by simp [decode] at h⟩
          · have cs : canBe (A.getK (I sy.Player_State)) 1 = true := canBe_of (by rw [← hc]; exact mst)
            simp only [cv, cs, Bool.and_self, if_true]
          · exact sim_log (PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hsY (withBit_false_of mvy hv)) (by rw [← peek_eq, hc]; exact TaintRun.mem_known_self _)) _
        · refine ⟨{ ((atY sy A y).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).setK (I sy.Player_State) (AB.known 2) with
            log := [3, 1] }, near _ (List.mem_append_right _ (List.mem_filterMap.2 ⟨2, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)), ?_, fun _ => hok',
            fun h => by simp [decode] at h⟩
          · have cs : canBe (A.getK (I sy.Player_State)) 2 = true := canBe_of (by rw [← hc]; exact mst)
            simp only [cv, cs, Bool.and_self, if_true]
          · exact sim_log (PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hsY (withBit_false_of mvy hv)) (by rw [← peek_eq, hc]; exact TaintRun.mem_known_self _)) _
      · -- rising
        have cv : canBit (A.getK (I sy.Player_Y_Speed)) 0x80 true = true := canBit_of mvy true (by simp [hv])
        refine ⟨{ (atY sy A y).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true) with log := [2, 1] },
          near _ (List.mem_append_left _ (by simp only [cv, if_true]; exact List.mem_singleton.2 rfl)), ?_, fun _ => hok', fun h => by simp [decode] at h⟩
        exact sim_log (PipeEntryRule.sim_setK' hsY (withBit_true_of (by simp) mvy hv)) _
  · refine ⟨{ A with log := [9, 1] }, ?_, sim_log hs _, fun h => ?_, fun _ => hok⟩
    · unfold piecesQ
      exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    · rcases h with h | h <;> simp [decode] at h

end

/-! ## What a piece at the collision routine says -/

section
variable {E : Env} {F : Nat × UInt8} {sy : Syms}

theorem setK_pc (A : AS) (i : Nat) (b : AB) : (A.setK i b).pc = A.pc := rfl
theorem setK_k (A : AS) (i : Nat) (b : AB) : (A.setK i b).k = A.k := rfl

/-- a byte that the piece knows is the machine's -/
theorem val_of_set {A : AS} {m : Machine} {i : Nat} {c : UInt8} (hs : Sim E F (A.setK i (AB.known c)) m) (hi : i < 2048) : m.ram.get! i = c := by
  have h := hs.ram i hi
  have e : (A.setK i (AB.known c)).getK i = AB.known c := by
    apply RoomVert.getK_setK_self
    · have := hs.szR; rw [RoomVert.setK_ram_size] at this; omega
    · have := hs.szK; rw [RoomVert.setK_kn_size] at this; omega
  rw [e] at h
  exact TaintRun.known_eq h

/-- `Sim` of a state with more set on top: a set of another byte keeps the first -/
theorem sim_under {A : AS} {m : Machine} {i j : Nat} {b c : AB} (hs : Sim E F ((A.setK i b).setK j c) m) (hij : i ≠ j) (hi : i < 2048) :
    b.mem (m.ram.get! i) := by
  have h := hs.ram i hi
  rw [RoomVert.getK_setK_ne (Ne.symm hij)] at h
  have e : (A.setK i b).getK i = b := by
    apply RoomVert.getK_setK_self
    · have := hs.szR; rw [RoomVert.setK_ram_size, RoomVert.setK_ram_size] at this; omega
    · have := hs.szK; rw [RoomVert.setK_kn_size, RoomVert.setK_kn_size] at this; omega
  rwa [e] at h

/-- **What a piece of `piecesQ` says of the machine it covers**: the same `pc` and frames; an exact piece not landing (`[2, 1]`) is below `y₀` or rising, an exact
piece landing (`[3, 1]`) is at or below `y₀` and falling; or the piece is the rest (`[9, 1]`) -/
theorem piece_facts (K : Ctx) (hyd : K.y0.toNat + K.d.toNat < 256) (hYH : I sy.Player_Y_Position ≠ I sy.Player_Y_HighPos)
    (hYV : I sy.Player_Y_Position ≠ I sy.Player_Y_Speed) (hHV : I sy.Player_Y_HighPos ≠ I sy.Player_Y_Speed) (hVS : I sy.Player_Y_Speed ≠ I sy.Player_State)
    (hYS : I sy.Player_Y_Position ≠ I sy.Player_State) (hHS : I sy.Player_Y_HighPos ≠ I sy.Player_State)
    {A A₂ : AS} {m : Machine} (hA : A₂ ∈ piecesQ sy K.y0 K.d A) (hs : Sim E F A₂ m) :
    A₂.pc = A.pc ∧ A₂.k = A.k ∧ ((decode A₂.log = .k1 ∧ NotLand sy K m) ∨ (decode A₂.log = .l1 ∧ LandM sy K m) ∨ decode A₂.log = .n1) := by
  unfold piecesQ at hA
  rcases List.mem_append.1 hA with hA | hA
  · rcases List.mem_append.1 hA with hA | hA
    · -- below the ground's height
      obtain ⟨y, hy, he⟩ := List.mem_filterMap.1 hA
      split at he
      · cases he
        have hy' := List.mem_range.1 hy
        refine ⟨rfl, rfl, Or.inl ⟨rfl, Or.inl ?_⟩⟩
        have hs' : Sim E F (atY sy A y.toUInt8) m := { hs with }
        unfold atY at hs'
        have e := sim_under hs' hYH (I_lt _)
        show peek m sy.Player_Y_Position < K.y0
        rw [peek_eq, TaintRun.known_eq e]
        apply UInt8.lt_iff_toNat_lt.2
        simp only [UInt8.toNat_ofNat']
        omega
      · cases he
    · -- near the ground
      obtain ⟨j, hj, hm⟩ := List.mem_flatMap.1 hA
      have hj' := List.mem_range.1 hj
      dsimp only at hm
      by_cases hc0 : (canBe (A.getK (I sy.Player_Y_Position)) (K.y0.toNat + j).toUInt8 && canBe (A.getK (I sy.Player_Y_HighPos)) 1) = true
      · rw [if_pos hc0] at hm
        rcases List.mem_append.1 hm with hm | hm
        · by_cases hc1 : canBit (A.getK (I sy.Player_Y_Speed)) 0x80 true = true
          · rw [if_pos hc1, List.mem_singleton] at hm
            subst hm
            refine ⟨rfl, rfl, Or.inl ⟨rfl, Or.inr ?_⟩⟩
            have hs' : Sim E F ((atY sy A (K.y0.toNat + j).toUInt8).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true)) m := { hs with }
            have h := hs'.ram _ (I_lt sy.Player_Y_Speed)
            have e : ((atY sy A (K.y0.toNat + j).toUInt8).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true)).getK (I sy.Player_Y_Speed) =
                withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true := by
              apply RoomVert.getK_setK_self
              · have := hs'.szR; have := I_lt sy.Player_Y_Speed; rw [RoomVert.setK_ram_size] at *; omega
              · have := hs'.szK; have := I_lt sy.Player_Y_Speed; rw [RoomVert.setK_kn_size] at *; omega
            rw [e] at h
            have e2 := withBit_true_mem (c := 0x80) (by simp) h
            show peek m sy.Player_Y_Speed &&& 0x80 ≠ 0
            rw [peek_eq, e2]
            decide
          · rw [if_neg hc1] at hm
            cases hm
        · obtain ⟨c, hc, he⟩ := List.mem_filterMap.1 hm
          by_cases hc2 : (canBit (A.getK (I sy.Player_Y_Speed)) 0x80 false && canBe (A.getK (I sy.Player_State)) c) = true
          · rw [if_pos hc2] at he
            cases he
            refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)⟩
            · have hs' : Sim E F (((atY sy A (K.y0.toNat + j).toUInt8).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).setK
                  (I sy.Player_State) (AB.known c)) m := { hs with }
              unfold atY at hs'
              have h1 := hs'.ram _ (I_lt sy.Player_Y_Position)
              rw [RoomVert.getK_setK_ne (Ne.symm hYS), RoomVert.getK_setK_ne (Ne.symm hYV), RoomVert.getK_setK_ne (Ne.symm hYH)] at h1
              have e : (A.setK (I sy.Player_Y_Position) (AB.known (K.y0.toNat + j).toUInt8)).getK (I sy.Player_Y_Position) = AB.known (K.y0.toNat + j).toUInt8 := by
                apply RoomVert.getK_setK_self
                · have := hs'.szR; have := I_lt sy.Player_Y_Position; simp only [RoomVert.setK_ram_size] at *; omega
                · have := hs'.szK; have := I_lt sy.Player_Y_Position; simp only [RoomVert.setK_kn_size] at *; omega
              rw [e] at h1
              show K.y0 ≤ peek m sy.Player_Y_Position
              rw [peek_eq, TaintRun.known_eq h1]
              apply UInt8.le_iff_toNat_le.2
              simp only [UInt8.toNat_ofNat']
              omega
            · have hs' : Sim E F (((atY sy A (K.y0.toNat + j).toUInt8).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).setK
                  (I sy.Player_State) (AB.known c)) m := { hs with }
              have e := sim_under hs' hVS (I_lt _)
              show peek m sy.Player_Y_Speed &&& 0x80 = 0
              rw [peek_eq]
              exact withBit_false_mem e
          · rw [if_neg hc2] at he
            cases he
      · rw [if_neg hc0] at hm
        cases hm
  · rw [List.mem_singleton] at hA
    subst hA
    exact ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩

end

/-! ## The facts from one step to the next -/

section
variable {E : Env} {F : Nat × UInt8} {sy : Syms}

theorem trace_next {m : Machine} {i : UInt8} {j : Nat} (hf : (trace m i j).frame = m.frame) (hh : (trace m i j).halted = false) :
    trace m i (j + 1) = (go step (trace m i j)).2 := by
  show PipeEntryRule.nxt (m.frame + 1) (trace m i j) = _
  have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by simp [hf, hh]
  simp only [PipeEntryRule.nxt, if_neg hc]

theorem keeps_step {L : List Nat} {A : AS} {x : Machine} (hs : Sim E F A x) (hk : StepWrites.keepOK E (fun i => L.contains i) A = true) :
    Keeps L x (go step x).2 := fun b hb => StepWrites.keep_step hs hk b (List.contains_iff_mem.2 hb)

theorem keeps_trans {L : List Nat} {x y z : Machine} (h1 : Keeps L x y) (h2 : Keeps L y z) : Keeps L x z := fun b hb => (h2 b hb).trans (h1 b hb)

theorem keeps_refl (L : List Nat) (x : Machine) : Keeps L x x := fun _ _ => rfl

theorem noPc_succ {m : Machine} {i : UInt8} {pc : UInt16} {a j : Nat} (h : NoPc m i pc a j) (hj : (trace m i j).pc ≠ pc) : NoPc m i pc a (j + 1) := by
  intro j' h1 h2
  by_cases e : j' = j
  · rw [e]; exact hj
  · exact h j' h1 (by omega)

theorem noPc_nil {m : Machine} {i : UInt8} {pc : UInt16} (a : Nat) : NoPc m i pc a a := fun _ h1 h2 => by omega

/-- a byte of `pAll` -/
theorem peek_keep {L : List Nat} {x y : Machine} (h : Keeps L x y) {a : UInt16} (ha : I a ∈ L) : peek y a = peek x a := h _ ha

theorem mem_pAll {a : UInt16} (h : a = sy.Player_Y_Position ∨ a = sy.Player_Y_MoveForce ∨ a = sy.Player_Y_Speed ∨ a = sy.Player_YMF_Dummy ∨ a = sy.VerticalForce ∨
    a = sy.VerticalForceDown ∨ a = sy.JumpOrigin_Y_Position ∨ a = sy.Player_State ∨ a = sy.A_B_Buttons ∨ a = sy.Player_Y_HighPos ∨ a = sy.DiffToHaltJump) :
    I a ∈ pAll sy := by
  simp only [pAll, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem mem_pRest {a : UInt16} (h : a = sy.Player_YMF_Dummy ∨ a = sy.VerticalForce ∨ a = sy.VerticalForceDown ∨ a = sy.JumpOrigin_Y_Position ∨ a = sy.A_B_Buttons ∨
    a = sy.Player_Y_HighPos ∨ a = sy.DiffToHaltJump) : I a ∈ pRest sy := by
  simp only [pRest, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h | h | h <;> simp [h]

theorem vsOf_keep {x y : Machine} (h : Keeps (pAll sy) x y) : VertModel.vsOf sy y = VertModel.vsOf sy x := by
  unfold VertModel.vsOf
  rw [peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp)),
    peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp)),
    peek_keep h (mem_pAll (by simp))]

theorem ok1_keep (K : Ctx) {x y : Machine} (h : Keeps (pAll sy) x y) (hy : Ok1 sy K y) : Ok1 sy K x := by
  unfold Ok1 at hy ⊢
  rw [peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp))] at hy
  exact hy

theorem notLand_keep (K : Ctx) {x y : Machine} (h : Keeps (pAll sy) x y) (hy : NotLand sy K y) : NotLand sy K x := by
  unfold NotLand at hy ⊢
  rw [peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp))] at hy
  exact hy

theorem landM_keep (K : Ctx) {x y : Machine} (h : Keeps (pAll sy) x y) (hy : LandM sy K y) : LandM sy K x := by
  unfold LandM at hy ⊢
  rw [peek_keep h (mem_pAll (by simp)), peek_keep h (mem_pAll (by simp))] at hy
  exact hy

theorem lt80_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 → UInt8.ofNat n.val < 0x80 := by decide +kernel

theorem lt80 {x : UInt8} (h : x &&& 0x80 = 0) : x < 0x80 := by
  have := lt80_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h

theorem ge80_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 ≠ 0 → ¬ UInt8.ofNat n.val < 0x80 := by decide +kernel

theorem ge80 {x : UInt8} (h : x &&& 0x80 ≠ 0) : ¬ x < 0x80 := by
  have := ge80_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h

/-- `land` does nothing when not landing -/
theorem land_notLand (K : Ctx) {x : Machine} (h : NotLand sy K x) : OpenJump.land K.y0 (VertModel.vsOf sy x) = VertModel.vsOf sy x := by
  unfold OpenJump.land
  rw [if_neg]
  intro hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases h with h | h
  · exact absurd hc.2 (by
      show ¬ K.y0 ≤ peek x sy.Player_Y_Position
      intro h2
      exact absurd h (UInt8.not_lt.2 h2))
  · exact ge80 h hc.1.2

/-- the halt relation from the walk's knowledge -/
theorem haltM_of {A : AS} {x : Machine} (hs : Sim E F A x) (h : haltK sy A = true) : HaltM sy x := by
  intro h1
  unfold haltK at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd h1 (kn_ne hs (I_lt _) h)
  · exact kn_val hs (I_lt _) h

/-- the vertical bytes known -/
theorem vs_of_vsK {A : AS} {x : Machine} (hs : Sim E F A x) {s : Jump.VS} (h : vsK sy s A = true) :
    VertModel.vsOf sy x = s ∧ peek x sy.Player_Y_HighPos = 1 ∧ peek x sy.DiffToHaltJump = 1 := by
  unfold vsK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨?_, kn_val hs (I_lt _) h10, kn_val hs (I_lt _) h11⟩
  have hab : (peek x sy.A_B_Buttons &&& 0x80 != 0) = s.prevA := by
    have hb := h9
    unfold AB.bit at hb
    split at hb
    · rename_i hk
      simp only [beq_iff_eq, Option.some.injEq] at hk hb
      rw [peek_eq, TaintRun.bit_eq (hs.ram _ (I_lt _)) hk]
      exact hb
    · cases hb
  unfold VertModel.vsOf
  rw [show peek x sy.Player_Y_Position = s.y from kn_val hs (I_lt _) h1, show peek x sy.Player_Y_MoveForce = s.mf from kn_val hs (I_lt _) h2,
    show peek x sy.Player_Y_Speed = s.vy from kn_val hs (I_lt _) h3, show peek x sy.Player_YMF_Dummy = s.dummy from kn_val hs (I_lt _) h4,
    show peek x sy.VerticalForce = s.vf from kn_val hs (I_lt _) h5, show peek x sy.VerticalForceDown = s.vfd from kn_val hs (I_lt _) h6,
    show peek x sy.JumpOrigin_Y_Position = s.origin from kn_val hs (I_lt _) h7, show peek x sy.Player_State = s.st from kn_val hs (I_lt _) h8, hab]

/-- landed: the vertical bytes of the return are `land` of those at `Q` -/
theorem vs_landed (K : Ctx) {A : AS} {x z : Machine} (hs : Sim E F A z) (hl : landedK sy K.y0 A = true) (hk : Keeps (pRest sy) x z)
    (hok : Ok1 sy K x) (hL : LandM sy K x) : VertModel.vsOf sy z = OpenJump.land K.y0 (VertModel.vsOf sy x) := by
  unfold landedK at hl
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨⟨l1, l2⟩, l3⟩, l4⟩ := hl
  have hc : ((VertModel.vsOf sy x).st != 0 && (VertModel.vsOf sy x).vy < 0x80 && decide (K.y0 ≤ (VertModel.vsOf sy x).y)) = true := by
    simp only [VertModel.vsOf, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    refine ⟨⟨?_, lt80 hL.2⟩, hL.1⟩
    rcases hok.2.2 with h | h <;> rw [h] <;> decide
  unfold OpenJump.land
  rw [if_pos hc]
  unfold VertModel.vsOf
  rw [show peek z sy.Player_Y_Position = K.y0 from kn_val hs (I_lt _) l1, show peek z sy.Player_Y_Speed = 0 from kn_val hs (I_lt _) l2,
    show peek z sy.Player_Y_MoveForce = 0 from kn_val hs (I_lt _) l3, show peek z sy.Player_State = 0 from kn_val hs (I_lt _) l4,
    peek_keep hk (mem_pRest (by simp)), peek_keep hk (mem_pRest (by simp)), peek_keep hk (mem_pRest (by simp)), peek_keep hk (mem_pRest (by simp)),
    peek_keep hk (mem_pRest (by simp))]

end

/-! ## The facts along the frame: one step -/

section
variable {E : Env} {F : Nat × UInt8} {sy : Syms}

theorem keeps_symm {L : List Nat} {x y : Machine} (h : Keeps L x y) : Keeps L y x := fun b hb => (h b hb).symm

theorem keeps_rest {x y : Machine} (h : Keeps (pAll sy) x y) : Keeps (pRest sy) x y := by
  intro b hb
  apply h
  simp only [pRest, pAll, List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
  rcases hb with h | h | h | h | h | h | h <;> simp [h]

/-- **The facts `PhiA` go on over one step**: from the state `A₁` that covers the machine after `j` instructions, through a piece `A₂` of `zoneA` that covers it, chosen
as `PsiA` says and meeting `okA`. `hyd` and the six distinct indices are facts of the ROM and of the symbols. -/
theorem phi_step (K : Ctx) (ex : Nat → Jump.VS) (hyd : K.y0.toNat + K.d.toNat < 256) (hYH : I sy.Player_Y_Position ≠ I sy.Player_Y_HighPos)
    (hYV : I sy.Player_Y_Position ≠ I sy.Player_Y_Speed) (hHV : I sy.Player_Y_HighPos ≠ I sy.Player_Y_Speed) (hVS : I sy.Player_Y_Speed ≠ I sy.Player_State)
    (hYS : I sy.Player_Y_Position ≠ I sy.Player_State) (hHS : I sy.Player_Y_HighPos ≠ I sy.Player_State)
    {m : Machine} {i : UInt8} {n₀ j : Nat} {A₁ A₂ : AS}
    (hn : n₀ ≤ j) (hΦ : PhiA sy K ex m i n₀ j A₁.log) (hs1 : Sim E F A₁ (trace m i j)) (hf : (trace m i j).frame = m.frame)
    (hz : A₂ ∈ zoneA sy K ex A₁) (hs2 : Sim E F A₂ (trace m i j)) (hψ : PsiA sy K m i j A₂) (hok : okA sy K E A₂ = true) :
    PhiA sy K ex m i n₀ (j + 1) A₂.log := by
  have hst : trace m i (j + 1) = (go step (trace m i j)).2 := trace_next hf hs1.halted
  have hpc1 : (trace m i j).pc = A₁.pc := hs1.pc
  have kst : ∀ L, StepWrites.keepOK E (fun i => L.contains i) A₂ = true → Keeps L (trace m i j) (trace m i (j + 1)) := fun L hk => by
    rw [hst]; exact keeps_step hs2 hk
  cases hd : decode A₁.log with
  | pre =>
    simp only [PhiA, hd] at hΦ
    simp only [zoneA, hd] at hz
    by_cases hq : A₁.pc = sy.PlayerSubs
    · rw [if_pos (by simp [hq]), List.mem_singleton] at hz
      subst hz
      simp only [okA, decode] at hok
      simp only [PhiA, decode]
      exact ⟨j, ⟨hn, by rw [hpc1, hq], hΦ⟩, Nat.lt_succ_self j, noPc_nil _, noPc_nil _, kst _ hok⟩
    · rw [if_neg (by simp [hq]), List.mem_singleton] at hz
      subst hz
      simp only [PhiA, hd]
      exact noPc_succ hΦ (by rw [hpc1]; exact hq)
  | q1 =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5⟩ := hΦ
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    by_cases hr : A₁.pc = K.cR
    · simp [hr, okA, decode] at hok
    · have e : (A₁.pc == K.cR) = false := by simp [hr]
      simp only [e, okA, decode, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.false_eq_true, if_false] at hok ⊢
      exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok.1), noPc_succ h4 (by rw [hpc1]; exact hr), keeps_trans h5 (kst _ (by simpa [e] using hok.2))⟩
  | q =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5⟩ := hΦ
    simp only [zoneA, hd] at hz
    by_cases he : A₁.pc = K.cE
    · rw [if_pos (by simp [he])] at hz
      have hpc2 : (trace m i j).pc = A₂.pc := hs2.pc
      obtain ⟨_, _, hfacts⟩ := piece_facts K hyd hYH hYV hHV hVS hYS hHS hz hs2
      rcases hfacts with ⟨hdk, hnl⟩ | ⟨hdl, hlm⟩ | hdn
      · simp only [okA, hdk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
        obtain ⟨⟨hq, hr⟩, hk⟩ := hok
        simp only [PhiA, hdk]
        exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc2]; exact hq), noPc_succ h4 (by rw [hpc2]; exact hr), keeps_trans h5 (kst _ hk),
          ok1_keep K h5 (hψ.1 (Or.inl hdk)), notLand_keep K h5 hnl⟩
      · simp only [okA, hdl, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
        obtain ⟨⟨hq, hr⟩, hk⟩ := hok
        simp only [PhiA, hdl]
        exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc2]; exact hq), noPc_succ h4 (by rw [hpc2]; exact hr), keeps_trans (keeps_rest h5) (kst _ hk),
          ok1_keep K h5 (hψ.1 (Or.inr hdl)), landM_keep K h5 hlm⟩
      · simp only [okA, hdn, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
        simp only [PhiA, hdn]
        exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc2]; exact hok.1), noPc_succ h4 (by rw [hpc2]; exact hok.2),
          fun h => hψ.2 hdn (ok1_keep K (keeps_symm h5) h)⟩
    · rw [if_neg (by simp [he])] at hz
      by_cases hr : A₁.pc = K.cR
      · rw [if_pos (by simp [hr]), List.mem_singleton] at hz
        subst hz
        simp [okA, decode] at hok
      · rw [if_neg (by simp [hr]), List.mem_singleton] at hz
        subst hz
        simp only [okA, hd, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
        simp only [PhiA, hd]
        exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok.1), noPc_succ h4 (by rw [hpc1]; exact hr), keeps_trans h5 (kst _ hok.2)⟩
  | k1 =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5, h6, h7⟩ := hΦ
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    by_cases hr : A₁.pc = K.cR
    · simp [hr, okA, decode] at hok
    · have e : (A₁.pc == K.cR) = false := by simp [hr]
      simp only [e, okA, decode, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.false_eq_true, if_false] at hok ⊢
      exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok.1), noPc_succ h4 (by rw [hpc1]; exact hr), keeps_trans h5 (kst _ (by simpa [e] using hok.2)), h6, h7⟩
  | l1 =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5, h6, h7⟩ := hΦ
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    by_cases hr : A₁.pc = K.cR
    · simp [hr, okA, decode] at hok
    · have e : (A₁.pc == K.cR) = false := by simp [hr]
      simp only [e, okA, decode, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.false_eq_true, if_false] at hok ⊢
      exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok.1), noPc_succ h4 (by rw [hpc1]; exact hr), keeps_trans h5 (kst _ (by simpa [e] using hok.2)), h6, h7⟩
  | n1 =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5⟩ := hΦ
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    by_cases hr : A₁.pc = K.cR
    · simp [hr, okA, decode] at hok
    · have e : (A₁.pc == K.cR) = false := by simp [hr]
      simp only [e, okA, decode, bne_iff_ne, ne_eq, Bool.false_eq_true, if_false] at hok ⊢
      exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok), noPc_succ h4 (by rw [hpc1]; exact hr), h5⟩
  | k =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5, h6, h7⟩ := hΦ
    simp only [zoneA, hd] at hz
    by_cases hr : A₁.pc = K.cR
    · rw [if_pos (by simp [hr]), List.mem_singleton] at hz
      subst hz
      by_cases hh : haltK sy A₁ = true
      · simp only [hh, if_true, okA, decode, bne_iff_ne, ne_eq, forgetV_pc] at hok ⊢
        refine ⟨k₁, j, h1, h2, Nat.lt_succ_self j, noPc_succ h3 (by rw [hpc1]; exact hok), by rw [hpc1, hr], h4, fun _ => ⟨?_, ?_, haltM_of hs1 hh⟩⟩
        · rw [vsOf_keep h5, land_notLand K h7]
        · rw [peek_keep h5 (mem_pAll (by simp))]; exact h6.2.1
      · simp [hh, okA, decode] at hok
    · rw [if_neg (by simp [hr]), List.mem_singleton] at hz
      subst hz
      simp only [okA, hd, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
      simp only [PhiA, hd]
      exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok.1), noPc_succ h4 (by rw [hpc1]; exact hr), keeps_trans h5 (kst _ hok.2), h6, h7⟩
  | l =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5, h6, h7⟩ := hΦ
    simp only [zoneA, hd] at hz
    by_cases hr : A₁.pc = K.cR
    · rw [if_pos (by simp [hr]), List.mem_singleton] at hz
      subst hz
      by_cases hh : (landedK sy K.y0 A₁ && haltK sy A₁) = true
      · simp only [Bool.and_eq_true] at hh
        simp only [hh.1, hh.2, Bool.and_self, if_true, okA, decode, bne_iff_ne, ne_eq, forgetV_pc] at hok ⊢
        refine ⟨k₁, j, h1, h2, Nat.lt_succ_self j, noPc_succ h3 (by rw [hpc1]; exact hok), by rw [hpc1, hr], h4, fun _ => ⟨vs_landed K hs1 hh.1 h5 h6 h7, ?_,
          haltM_of hs1 hh.2⟩⟩
        rw [peek_keep h5 (mem_pRest (by simp))]; exact h6.2.1
      · simp only [Bool.and_eq_true] at hh
        by_cases h8 : landedK sy K.y0 A₁ = true
        · have h9 : haltK sy A₁ = false := by simpa [h8] using hh
          simp [h8, h9, okA, decode] at hok
        · have h9 : landedK sy K.y0 A₁ = false := by simpa using h8
          simp [h9, okA, decode] at hok
    · rw [if_neg (by simp [hr]), List.mem_singleton] at hz
      subst hz
      simp only [okA, hd, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
      simp only [PhiA, hd]
      exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok.1), noPc_succ h4 (by rw [hpc1]; exact hr), keeps_trans h5 (kst _ hok.2), h6, h7⟩
  | n =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, h1, h2, h3, h4, h5⟩ := hΦ
    simp only [zoneA, hd] at hz
    by_cases hr : A₁.pc = K.cR
    · rw [if_pos (by simp [hr]), List.mem_singleton] at hz
      subst hz
      simp only [okA, decode, bne_iff_ne, ne_eq, forgetV_pc] at hok ⊢
      exact ⟨k₁, j, h1, h2, Nat.lt_succ_self j, noPc_succ h3 (by rw [hpc1]; exact hok), by rw [hpc1, hr], h4, fun h => absurd h h5⟩
    · rw [if_neg (by simp [hr]), List.mem_singleton] at hz
      subst hz
      simp only [okA, hd, bne_iff_ne, ne_eq] at hok
      simp only [PhiA, hd]
      exact ⟨k₁, h1, by omega, noPc_succ h3 (by rw [hpc1]; exact hok), noPc_succ h4 (by rw [hpc1]; exact hr), h5⟩
  | aft =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₁, k₂, h1, h2, h3, h4, h5, h6, h7⟩ := hΦ
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    simp only [okA, hd, bne_iff_ne, ne_eq] at hok
    simp only [PhiA, hd]
    exact ⟨k₁, k₂, h1, h2, by omega, noPc_succ h4 (by rw [hpc1]; exact hok), h5, h6, h7⟩
  | tk u =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    simp only [zoneA, hd] at hz
    by_cases hr : A₁.pc = K.cR
    · rw [if_pos (by simp [hr]), List.mem_singleton] at hz
      subst hz
      by_cases hv : vsK sy (ex u) A₁ = true
      · simp only [hv, if_true, decode]
        obtain ⟨v1, v2, v3⟩ := vs_of_vsK hs1 hv
        exact ⟨j, u, hn, Nat.lt_succ_self j, by rw [hpc1, hr], h2, h1, v1, v2, v3⟩
      · simp [hv, okA, decode] at hok
    · rw [if_neg (by simp [hr]), List.mem_singleton] at hz
      subst hz
      simp only [PhiA, hd]
      exact ⟨h1, noPc_succ h2 (by rw [hpc1]; exact hr)⟩
  | tkd =>
    simp only [PhiA, hd] at hΦ
    obtain ⟨k₂, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hΦ
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    simp only [PhiA, hd]
    exact ⟨k₂, u, h1, by omega, h3, h4, h5, h6, h7, h8⟩
  | bad =>
    simp only [PhiA, hd] at hΦ

end

/-! ## The frame -/

section
variable {E : Env} {F : Nat × UInt8} {sy : Syms}

/-- the phases of a takeoff -/
def TkP : Phase → Prop
  | .tk _ => True
  | .tkd => True
  | _ => False

/-- **The facts along the frame, with the kind of start**: a takeoff's phases exactly when the state is 0 at the cut -/
def PhiT (sy : Syms) (K : Ctx) (ex : Nat → Jump.VS) (m : Machine) (i : UInt8) (n₀ j : Nat) (l : List Nat) : Prop :=
  PhiA sy K ex m i n₀ j l ∧ (TkP (decode l) ↔ peek (trace m i n₀) sy.Player_State = 0)

theorem psi_none {K : Ctx} {m : Machine} {i : UInt8} {j : Nat} {A : AS} (h1 : decode A.log ≠ .k1) (h2 : decode A.log ≠ .l1) (h3 : decode A.log ≠ .n1) :
    PsiA sy K m i j A :=
  ⟨fun h => h.elim (fun e => absurd e h1) (fun e => absurd e h2), fun h => absurd h h3⟩

/-- **A piece of `zoneA` covers the machine**, chosen as `PsiA` says -/
theorem zone_cover (K : Ctx) (ex : Nat → Jump.VS) (hyd : K.y0.toNat + K.d.toNat < 256) {A₁ : AS} {m : Machine} {i : UInt8} {j : Nat}
    (hs : Sim E F A₁ (trace m i j)) : ∃ A₂ ∈ zoneA sy K ex A₁, Sim E F A₂ (trace m i j) ∧ PsiA sy K m i j A₂ := by
  cases hd : decode A₁.log with
  | pre =>
    simp only [zoneA, hd]
    by_cases hq : A₁.pc = sy.PlayerSubs
    · rw [if_pos (by simp [hq])]
      exact ⟨_, List.mem_singleton.2 rfl, sim_log hs _, psi_none (by simp [decode]) (by simp [decode]) (by simp [decode])⟩
    · rw [if_neg (by simp [hq])]
      exact ⟨_, List.mem_singleton.2 rfl, hs, psi_none (by simp [hd]) (by simp [hd]) (by simp [hd])⟩
  | q =>
    simp only [zoneA, hd]
    by_cases he : A₁.pc = K.cE
    · rw [if_pos (by simp [he])]
      obtain ⟨A₂, h1, h2, h3, h4⟩ := split_cover (sy := sy) K hyd hs
      exact ⟨A₂, h1, h2, h3, h4⟩
    · rw [if_neg (by simp [he])]
      by_cases hr : A₁.pc = K.cR
      · rw [if_pos (by simp [hr])]
        exact ⟨_, List.mem_singleton.2 rfl, sim_log hs _, psi_none (by simp [decode]) (by simp [decode]) (by simp [decode])⟩
      · rw [if_neg (by simp [hr])]
        exact ⟨_, List.mem_singleton.2 rfl, hs, psi_none (by simp [hd]) (by simp [hd]) (by simp [hd])⟩
  | q1 | k1 | l1 | n1 =>
    simp only [zoneA, hd]
    refine ⟨_, List.mem_singleton.2 rfl, sim_log hs _, psi_none ?_ ?_ ?_⟩ <;> split <;> simp [decode]
  | k | l | n | tk u =>
    simp only [zoneA, hd]
    by_cases hr : A₁.pc = K.cR
    · rw [if_pos (by simp [hr])]
      refine ⟨_, List.mem_singleton.2 rfl, sim_log (sim_forgetV sy hs) _, psi_none ?_ ?_ ?_⟩ <;> (try split) <;> simp [decode]
    · rw [if_neg (by simp [hr])]
      exact ⟨_, List.mem_singleton.2 rfl, hs, psi_none (by simp [hd]) (by simp [hd]) (by simp [hd])⟩
  | aft | tkd | bad =>
    simp only [zoneA, hd]
    exact ⟨_, List.mem_singleton.2 rfl, hs, psi_none (by simp [hd]) (by simp [hd]) (by simp [hd])⟩

/-- **The zone keeps the kind of start**: a piece that meets `okA` is in a takeoff's phase exactly when the state before was -/
theorem tk_zone (K : Ctx) (ex : Nat → Jump.VS) (hyd : K.y0.toNat + K.d.toNat < 256) (hYH : I sy.Player_Y_Position ≠ I sy.Player_Y_HighPos)
    (hYV : I sy.Player_Y_Position ≠ I sy.Player_Y_Speed) (hHV : I sy.Player_Y_HighPos ≠ I sy.Player_Y_Speed) (hVS : I sy.Player_Y_Speed ≠ I sy.Player_State)
    (hYS : I sy.Player_Y_Position ≠ I sy.Player_State) (hHS : I sy.Player_Y_HighPos ≠ I sy.Player_State)
    {A₁ A₂ : AS} {x : Machine} (hz : A₂ ∈ zoneA sy K ex A₁) (hs2 : Sim E F A₂ x) (hok : okA sy K E A₂ = true) :
    (TkP (decode A₂.log) ↔ TkP (decode A₁.log)) := by
  have bad : decode A₂.log = .bad → False := fun h => by simp [okA, h] at hok
  cases hd : decode A₁.log with
  | q =>
    simp only [zoneA, hd] at hz
    by_cases he : A₁.pc = K.cE
    · rw [if_pos (by simp [he])] at hz
      obtain ⟨_, _, hf⟩ := piece_facts K hyd hYH hYV hHV hVS hYS hHS hz hs2
      rcases hf with ⟨h, _⟩ | ⟨h, _⟩ | h <;> simp [TkP, h]
    · rw [if_neg (by simp [he])] at hz
      by_cases hr : A₁.pc = K.cR
      · rw [if_pos (by simp [hr]), List.mem_singleton] at hz
        subst hz
        exact absurd (by simp [decode]) bad
      · rw [if_neg (by simp [hr]), List.mem_singleton] at hz
        subst hz
        rw [hd]
  | pre =>
    simp only [zoneA, hd] at hz
    split at hz
    · rw [List.mem_singleton] at hz
      subst hz
      simp [TkP, decode]
    · rw [List.mem_singleton] at hz
      subst hz
      rw [hd]
  | q1 | k1 | l1 | n1 =>
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    split <;> simp [TkP, decode]
  | k | l | n =>
    simp only [zoneA, hd] at hz
    split at hz
    · rw [List.mem_singleton] at hz
      subst hz
      (try split) <;> simp [TkP, decode]
    · rw [List.mem_singleton] at hz
      subst hz
      rw [hd]
  | tk u =>
    simp only [zoneA, hd] at hz
    split at hz
    · rw [List.mem_singleton] at hz
      subst hz
      split
      · simp [TkP, decode]
      · rename_i hv
        exact absurd (by simp [decode, hv]) bad
    · rw [List.mem_singleton] at hz
      subst hz
      rw [hd]
  | aft | tkd | bad =>
    simp only [zoneA, hd, List.mem_singleton] at hz
    subst hz
    rw [hd]

/-- **One whole frame by the walk of `OpenAir`**: from a start `S` at the instruction `n₀` with `PhiT`, the frame ends, after the return of the collision routine
(`finA`), with `PhiT` at its end -/
theorem walk_frame (K : Ctx) (ex : Nat → Jump.VS) (C : CfgK) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hfin : C.fin = finA)
    (ht : C.t.all (walkP K.R (phA sy K ex C.E) C FrameKeep.fuelK) = true) (hyd : K.y0.toNat + K.d.toNat < 256)
    (hYH : I sy.Player_Y_Position ≠ I sy.Player_Y_HighPos) (hYV : I sy.Player_Y_Position ≠ I sy.Player_Y_Speed) (hHV : I sy.Player_Y_HighPos ≠ I sy.Player_Y_Speed)
    (hVS : I sy.Player_Y_Speed ≠ I sy.Player_State) (hYS : I sy.Player_Y_Position ≠ I sy.Player_State) (hHS : I sy.Player_Y_HighPos ≠ I sy.Player_State)
    {m : Machine} {i : UInt8} {n₀ : Nat} {S : AS} (hw : walkP K.R (phA sy K ex C.E) C FrameKeep.fuelK S = true) (hs : Sim C.E (m.frame, 2) S (trace m i n₀))
    (hf : (trace m i n₀).frame = m.frame) (hd : m.fdot + 3 * n₀ ≤ (trace m i n₀).fdot)
    (hcl : ∀ j, CleanK C.G C.S.store (trace m i j)) (hr : ∀ j, (trace m i j).frame = m.frame → OpenFlat.RdOK1 K.R (trace m i j))
    (h0 : PhiT sy K ex m i n₀ n₀ S.log) :
    ∃ J, n₀ ≤ J ∧ (trace m i J).frame = m.frame + 1 ∧ (∀ j, n₀ ≤ j → j < J → (trace m i j).frame = m.frame) ∧ frame m i = trace m i J ∧
      ∃ B, finA B = true ∧ PhiT sy K ex m i n₀ J B.log := by
  obtain ⟨_, J, j1, j2, j3, j4, B, b1, _, b3⟩ := OpenWalk.frame_of_walkP (Φ := PhiT sy K ex m i n₀) (Ψ := PsiA sy K m i) ht hkl hops
    (show 2 ≤ (2 : UInt8).toNat by decide) hw hs hf hd hcl hr h0
    (fun j A₁ _ _ hs1 _ => zone_cover K ex hyd hs1)
    (fun j A₁ A₂ hn hΦ hs1 hf1 hz hs2 hψ hok => ⟨phi_step K ex hyd hYH hYV hHV hVS hYS hHS hn hΦ.1 hs1 hf1 hz hs2 hψ hok,
      (tk_zone K ex hyd hYH hYV hHV hVS hYS hHS hz hs2 hok).trans hΦ.2⟩)
  exact ⟨J, j1, j2, j3, j4, B, by rw [← hfin]; exact b1, b3⟩

/-- the end of a frame in the air: the phase `aft` -/
theorem end_air {K : Ctx} {ex : Nat → Jump.VS} {m : Machine} {i : UInt8} {n₀ J : Nat} {B : AS} (hst : peek (trace m i n₀) sy.Player_State ≠ 0)
    (hfin : finA B = true) (hΦ : PhiT sy K ex m i n₀ J B.log) :
    ∃ k₁ k₂, AtQ sy m i n₀ k₁ ∧ k₁ < k₂ ∧ k₂ < J ∧ NoPc m i sy.PlayerSubs (k₁ + 1) J ∧ (trace m i k₂).pc = K.cR ∧ NoPc m i K.cR (k₁ + 1) k₂ ∧
      (Ok1 sy K (trace m i k₁) → VertModel.vsOf sy (trace m i k₂) = OpenJump.land K.y0 (VertModel.vsOf sy (trace m i k₁)) ∧
        peek (trace m i k₂) sy.Player_Y_HighPos = 1 ∧ HaltM sy (trace m i k₂)) := by
  obtain ⟨h1, h2⟩ := hΦ
  unfold finA afterRet at hfin
  cases hd : decode B.log with
  | aft => simpa [PhiA, hd] using h1
  | tkd => exact absurd (h2.1 (by simp [TkP, hd])) hst
  | _ => simp [hd] at hfin

/-- the end of a takeoff: the phase `tkd` -/
theorem end_take {K : Ctx} {ex : Nat → Jump.VS} {m : Machine} {i : UInt8} {n₀ J : Nat} {B : AS} (hst : peek (trace m i n₀) sy.Player_State = 0)
    (hfin : finA B = true) (hΦ : PhiT sy K ex m i n₀ J B.log) :
    ∃ k₂ u, n₀ ≤ k₂ ∧ k₂ < J ∧ (trace m i k₂).pc = K.cR ∧ NoPc m i K.cR n₀ k₂ ∧ peek (trace m i n₀) sy.Player_XSpeedAbsolute = u.toUInt8 ∧
      VertModel.vsOf sy (trace m i k₂) = ex u ∧ peek (trace m i k₂) sy.Player_Y_HighPos = 1 ∧ peek (trace m i k₂) sy.DiffToHaltJump = 1 := by
  obtain ⟨h1, h2⟩ := hΦ
  unfold finA afterRet at hfin
  cases hd : decode B.log with
  | tkd => simpa [PhiA, hd] using h1
  | aft =>
    have := h2.2 hst
    simp [TkP, hd] at this
  | _ => simp [hd] at hfin

end

/-! ## After the return of the collision routine -/

/-- the bytes that the vertical model reads at the next frame, and the halt value: the height, its high byte, the vertical speed and its fraction (`OpenFlat.vertA`),
the height's fraction, the two forces, the jump's origin, the state, A and B, the jump's halt value -/
def vsA (sy : Syms) : List UInt16 :=
  OpenFlat.vertA sy ++ [sy.Player_YMF_Dummy, sy.VerticalForce, sy.VerticalForceDown, sy.JumpOrigin_Y_Position, sy.Player_State, sy.A_B_Buttons, sy.DiffToHaltJump]

/-- **From the return of the collision routine to the frame's end these bytes do not change**, on the frame from `m` with the input `i`: at every arrival at the return
after the first arrival at the player's routine, the bytes of `vsA` are those of the frame's end. `OpenFlat.AfterV` for more bytes. -/
def AfterVS (sy : Syms) (m0 m : Machine) (i : UInt8) : Prop :=
  ∀ k, CtrlKeep.arrAt sy m i ≤ k → (trace m i k).pc = OpenFlat.collRet sy m0 → ∀ x ∈ vsA sy, peek (frame m i) x = peek (trace m i k) x

theorem afterV_of {sy : Syms} {m0 m : Machine} {i : UInt8} (h : AfterVS sy m0 m i) : OpenFlat.AfterV sy m0 m i :=
  fun k h1 h2 x hx => h k h1 h2 x (List.mem_append_left _ hx)

/-- the bytes of `vsA` that stay assumed after the return of the collision routine: the height, its high byte, the vertical speed and its fraction
(`OpenFlat.vertA`), the height's fraction and the state. The other five (the vertical force down, the jump's origin, A and B, the jump's halt
value and vertical force) are a theorem (`OpenAfter.keep_ret_all`, a walk that follows each). -/
def vsR (sy : Syms) : List UInt16 := OpenFlat.vertA sy ++ [sy.Player_YMF_Dummy, sy.Player_State]

/-- **From the return of the collision routine to the frame's end the six bytes of `vsR` do not change**, on the frame from `m` with the input `i`: `AfterVS` for
the bytes that no walk gives (the enemies' code, the platforms and the jumpspring may write them) -/
def AfterVR (sy : Syms) (m0 m : Machine) (i : UInt8) : Prop :=
  ∀ k, CtrlKeep.arrAt sy m i ≤ k → (trace m i k).pc = OpenFlat.collRet sy m0 → ∀ x ∈ vsR sy, peek (frame m i) x = peek (trace m i k) x

theorem afterV_ofR {sy : Syms} {m0 m : Machine} {i : UInt8} (h : AfterVR sy m0 m i) : OpenFlat.AfterV sy m0 m i :=
  fun k h1 h2 x hx => h k h1 h2 x (List.mem_append_left _ hx)

/-! ## A real frame -/

/-- **The checks on the ROM of a frame's walk**: the walk (`airCheck`), the ground's height and `LandDepth` within a byte, four distinct bytes, and the walk of
`CtrlKeep` that follows the flag that disables the collision routine up to the player's routine -/
def airAll (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  airCheck sy m0 v && decide ((peek m0 sy.Player_Y_Position).toNat + sy.LandDepth.toUInt8.toNat < 256) &&
    decide (I sy.Player_Y_Position ≠ I sy.Player_Y_HighPos) && decide (I sy.Player_Y_Position ≠ I sy.Player_Y_Speed) &&
    decide (I sy.Player_Y_HighPos ≠ I sy.Player_Y_Speed) && decide (I sy.Player_Y_Speed ≠ I sy.Player_State) &&
    decide (I sy.Player_Y_Position ≠ I sy.Player_State) && decide (I sy.Player_Y_HighPos ≠ I sy.Player_State) &&
    CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) (OpenMap.dcdI sy m0) false)

section
variable {sy : Syms} {m0 : Machine}

/-- **A byte at the player's routine** is that of the frame's start, by a walk of `CtrlKeep` that follows it (as `OpenFlat.high_at_cut`) -/
theorem byte_at_cut {b : Nat} (hH : CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) b false) = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    {k : Nat} (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame) (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    (trace m i k).ram.get! b = m.ram.get! b := by
  obtain ⟨B, hB, hs⟩ := CtrlKeep.at_cut (C := CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) b false) hH rfl rfl rfl
    (CtrlKeep.cfg_start _ _ false h0) hcl hk hf hfirst
  simp only [CtrlKeep.atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB
  have h1 := hs.rkv hB.1.1.1.1.1.1
  rw [if_neg (by simp [hB.1.1.1.1.1.2])] at h1
  exact h1

/-- what `airAll` says -/
structure AirFacts (sy : Syms) (m0 : Machine) (v : UInt8) : Prop where
  walk : airCheck sy m0 v = true
  yd : (ctxOf sy m0 v).y0.toNat + (ctxOf sy m0 v).d.toNat < 256
  hYH : I sy.Player_Y_Position ≠ I sy.Player_Y_HighPos
  hYV : I sy.Player_Y_Position ≠ I sy.Player_Y_Speed
  hHV : I sy.Player_Y_HighPos ≠ I sy.Player_Y_Speed
  hVS : I sy.Player_Y_Speed ≠ I sy.Player_State
  hYS : I sy.Player_Y_Position ≠ I sy.Player_State
  hHS : I sy.Player_Y_HighPos ≠ I sy.Player_State
  dcd : CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) (OpenMap.dcdI sy m0) false) = true

theorem airFacts_of {v : UInt8} (h : airAll sy m0 v = true) : AirFacts sy m0 v := by
  simp only [airAll, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, h4⟩ := h
  exact ⟨h1, h2, a1, a2, a3, a4, a5, a6, h4⟩

/-- the cut: the first arrival at the player's routine, a state of the walk of the pause bit there, and the walk of `OpenAir` from each start -/
theorem at_cut {v : UInt8} (hc : CtrlKeep.ctrlCheck sy m0 = true) (hA : airCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hu : CtrlKeep.Unpaused sy m0 (frame m i)) :
    (trace m i (CtrlKeep.arrAt sy m i)).pc = sy.PlayerCtrlRoutine ∧ (trace m i (CtrlKeep.arrAt sy m i)).frame = m.frame ∧
      (∀ j, j < CtrlKeep.arrAt sy m i → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) ∧ m.fdot + 3 * CtrlKeep.arrAt sy m i ≤ (trace m i (CtrlKeep.arrAt sy m i)).fdot ∧
      ∃ B, Sim (CtrlKeep.envR m0 (sy.Player_X_Speed &&& 0x7FF).toNat) (m.frame, m.ram.get! (sy.Player_X_Speed &&& 0x7FF).toNat) B (trace m i (CtrlKeep.arrAt sy m i)) ∧
        ∀ S ∈ startsA sy (ctxOf sy m0 v) v B,
          walkP (ctxOf sy m0 v).R (phA sy (ctxOf sy m0 v) (expT sy m0) (PipeEntryRule.envOf m0)) (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)) FrameKeep.fuelK S = true := by
  have hA' : airCheckWith sy m0 (ctxOf sy m0 v) v (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)) = true := hA
  unfold airCheckWith at hA'
  simp only [Bool.and_eq_true] at hA'
  obtain ⟨ha1, ha2, ha3⟩ := CtrlKeep.arrive_at hc h0 hcl hu
  generalize hk0 : CtrlKeep.arrAt sy m i = k₀ at ha1 ha2 ha3 ⊢
  rcases CtrlKeep.cut_or_end2 (C := cfgPA sy m0 (ctxOf sy m0 v) v (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v))) hA'.1 rfl rfl rfl
      (CtrlKeep.cfg_start (CtrlKeep.cutTable sy m0 true) (sy.Player_X_Speed &&& 0x7FF).toNat true h0) hcl with
    ⟨k, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk : k = k₀ := OpenFlat.first_eq h1 h4 ha1 ha3
    subst hk
    have hw : hookA sy m0 (ctxOf sy m0 v) v (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)) B = true := hB2
    unfold hookA at hw
    exact ⟨h1, h2, h4, h5, B, hs, fun S hS => List.all_eq_true.1 hw S hS⟩
  · exact absurd ha1 (hno _ ha2)

/-- the table of the check walks -/
theorem table_ok {v : UInt8} (hA : airCheck sy m0 v = true) :
    (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)).t.all (walkP (ctxOf sy m0 v).R (phA sy (ctxOf sy m0 v) (expT sy m0) (PipeEntryRule.envOf m0))
      (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)) FrameKeep.fuelK) = true := by
  have hA' : airCheckWith sy m0 (ctxOf sy m0 v) v (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)) = true := hA
  unfold airCheckWith at hA'
  simp only [Bool.and_eq_true] at hA'
  exact hA'.2

theorem wff {m : Machine} {x : UInt16} {c : UInt8} (h : peek m x = c) : m.ram.get! (I x) &&& 0xFF = c &&& 0xFF := by
  rw [FrameKeep.and_ff, FrameKeep.and_ff]; exact h

/-- **A real frame in the air**: from the frame's start in control, in the state 1 or 2 with the halt relation, the jumpspring byte 0 and the collision routine not
disabled, each instruction meeting `CleanK` of `FrameKeep.guardK` and of `OpenFlat.guardQ` and `OpenFlat.RdOK1`: the frame comes to `Q` once from the player's routine on,
at `k₁`, then to the return of the collision routine at `k₂`; if `Ok1` holds at `k₁`, the vertical bytes at `k₂` are `land` of those at `k₁`, with the high byte 1 and
the halt relation -/
theorem air_real {v : UInt8} (hc : CtrlKeep.ctrlCheck sy m0 = true) (hA : AirFacts sy m0 v) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hcq : ∀ n, CleanK (OpenFlat.guardQ sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hr : ∀ n, (trace m i n).frame = m.frame → OpenFlat.RdOK1 (OpenFlat.rdOf sy m0) (trace m i n))
    (hu : CtrlKeep.Unpaused sy m0 (frame m i)) (hv : CtrlKeep.AreaOK sy v m) (hj : peek m sy.JumpspringAnimCtrl = 0)
    (hst : peek m sy.Player_State = 1 ∨ peek m sy.Player_State = 2) (hh : HaltM sy m) (hdc : m.ram.get! (OpenMap.dcdI sy m0) = 0) :
    ∃ k₁ k₂ J, CtrlKeep.arrAt sy m i ≤ k₁ ∧ k₁ < k₂ ∧ k₂ < J ∧ frame m i = trace m i J ∧ (trace m i J).frame = m.frame + 1 ∧
      (∀ j, CtrlKeep.arrAt sy m i ≤ j → j < J → (trace m i j).frame = m.frame) ∧
      (trace m i k₁).pc = sy.PlayerSubs ∧ (∀ j, CtrlKeep.arrAt sy m i ≤ j → j < J → (trace m i j).pc = sy.PlayerSubs → j = k₁) ∧
      (trace m i k₂).pc = OpenFlat.collRet sy m0 ∧
      (Ok1 sy (ctxOf sy m0 v) (trace m i k₁) → VertModel.vsOf sy (trace m i k₂) = OpenJump.land (peek m0 sy.Player_Y_Position) (VertModel.vsOf sy (trace m i k₁)) ∧
        peek (trace m i k₂) sy.Player_Y_HighPos = 1 ∧ HaltM sy (trace m i k₂)) := by
  obtain ⟨c1, c2, c3, c4, B, hs, hw⟩ := at_cut hc hA.walk h0 hcl hu
  have hdc' : (trace m i (CtrlKeep.arrAt sy m i)).ram.get! (OpenMap.dcdI sy m0) = 0 := (byte_at_cut hA.dcd h0 hcl c1 c2 c3).trans hdc
  generalize hk0 : CtrlKeep.arrAt sy m i = n₀ at c1 c2 c3 c4 hs hw hdc' ⊢
  have A := CtrlKeep.ctrl_keep hc h0 hcl c1 c2 c3
  have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (trace m i n₀) x = peek m x := A.keep
  have hva : ∀ w ∈ CtrlKeep.valA sy v, (trace m i n₀).ram.get! w.1 &&& w.2.1 = w.2.2 &&& w.2.1 := by
    intro w hw'
    simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hv.1)
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hv.2.1)
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hv.2.2)
  have hst' : peek (trace m i n₀) sy.Player_State = peek m sy.Player_State := kp _ (by simp [CtrlKeep.keepA])
  -- the start of the walk: the state 1 (with the halt value 1) or 2
  obtain ⟨S, hS, hsS, hlog⟩ : ∃ S ∈ startsA sy (ctxOf sy m0 v) v B, Sim (PipeEntryRule.envOf m0) (m.frame, 2) S (trace m i n₀) ∧ S.log = [] := by
    rcases hst with h1 | h1
    · refine ⟨_, List.mem_append_left _ List.mem_cons_self, sim_log (CtrlKeep.sim_toA hs (CtrlKeep.watchA_lt v) ?_) _, rfl⟩
      intro w hw'
      rcases List.mem_append.1 hw' with h | h
      · exact hva w h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl
        · exact wff (hst'.trans h1)
        · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans (hh h1))
        · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hj)
        · show (trace m i n₀).ram.get! (OpenMap.dcdI sy m0) &&& 0xFF = 0 &&& 0xFF
          rw [hdc']
    · refine ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), sim_log (CtrlKeep.sim_toA hs (CtrlKeep.watchA_lt v) ?_) _, rfl⟩
      intro w hw'
      rcases List.mem_append.1 hw' with h | h
      · exact hva w h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact wff (hst'.trans h1)
        · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hj)
        · show (trace m i n₀).ram.get! (OpenMap.dcdI sy m0) &&& 0xFF = 0 &&& 0xFF
          rw [hdc']
  have hne : peek (trace m i n₀) sy.Player_State ≠ 0 := by
    rw [hst']; rcases hst with h | h <;> rw [h] <;> decide
  have h0Φ : PhiT sy (ctxOf sy m0 v) (expT sy m0) m i n₀ n₀ S.log := by
    rw [hlog]
    exact ⟨noPc_nil _, ⟨fun h => h.elim, fun h => absurd h hne⟩⟩
  obtain ⟨J, j1, j2, j3, j4, B', b1, b2⟩ := walk_frame (ctxOf sy m0 v) (expT sy m0) (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)) rfl rfl rfl
    (table_ok hA.walk) hA.yd hA.hYH hA.hYV hA.hHV hA.hVS hA.hYS hA.hHS (hw S hS) hsS c2 c4 hcq hr h0Φ
  obtain ⟨k₁, k₂, ⟨a1, a2, a3⟩, e1, e2, e3, e4, _, e6⟩ := end_air hne b1 b2
  refine ⟨k₁, k₂, J, a1, e1, e2, j4, j2, j3, a2, fun j h1 h2 h3 => ?_, e4, e6⟩
  rcases Nat.lt_trichotomy j k₁ with h | h | h
  · exact absurd h3 (a3 j h1 h)
  · exact h
  · exact absurd h3 (e3 j (by omega) h2)

/-- **A real frame of a takeoff**: from the frame's start in control on the ground at `y₀` (the state 0, `GroundAt`) with the stored speed `u ≤ top`, a jump read at the
player's routine, the jumpspring byte 0 and the collision routine not disabled: the frame comes to the return of the collision routine at `k₂`, with the vertical
bytes of the model's takeoff `expT u`, the high byte 1 and the halt value 1. `hH` is the walk of `CtrlKeep` that follows the high byte (a part of `OpenFlat.flatCheck`). -/
theorem take_real {v : UInt8} (hc : CtrlKeep.ctrlCheck sy m0 = true) (hA : AirFacts sy m0 v)
    (hH : CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) (OpenFlat.I sy.Player_Y_HighPos) false) = true) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hcq : ∀ n, CleanK (OpenFlat.guardQ sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hr : ∀ n, (trace m i n).frame = m.frame → OpenFlat.RdOK1 (OpenFlat.rdOf sy m0) (trace m i n))
    (hu : CtrlKeep.Unpaused sy m0 (frame m i)) (hv : CtrlKeep.AreaOK sy v m) (hj : peek m sy.JumpspringAnimCtrl = 0)
    (hg : peek m sy.Player_State = 0) (hG : OpenFlat.GroundAt sy m0 m) (hab : (peek m sy.Player_XSpeedAbsolute).toNat ≤ TopSpeed.top sy)
    (hjump : (FrameModel.readIn sy (trace m i (CtrlKeep.arrAt sy m i))).jump = true) (hdc : m.ram.get! (OpenMap.dcdI sy m0) = 0) :
    ∃ k₂ J, CtrlKeep.arrAt sy m i ≤ k₂ ∧ k₂ < J ∧ frame m i = trace m i J ∧ (∀ j, CtrlKeep.arrAt sy m i ≤ j → j < J → (trace m i j).frame = m.frame) ∧
      (trace m i k₂).pc = OpenFlat.collRet sy m0 ∧ VertModel.vsOf sy (trace m i k₂) = expT sy m0 (peek m sy.Player_XSpeedAbsolute).toNat ∧
      peek (trace m i k₂) sy.Player_Y_HighPos = 1 ∧ peek (trace m i k₂) sy.DiffToHaltJump = 1 := by
  obtain ⟨c1, c2, c3, c4, B, hs, hw⟩ := at_cut hc hA.walk h0 hcl hu
  have hdc' : (trace m i (CtrlKeep.arrAt sy m i)).ram.get! (OpenMap.dcdI sy m0) = 0 := (byte_at_cut hA.dcd h0 hcl c1 c2 c3).trans hdc
  have hhi : peek (trace m i (CtrlKeep.arrAt sy m i)) sy.Player_Y_HighPos = peek m sy.Player_Y_HighPos := OpenFlat.high_at_cut hH h0 hcl c1 c2 c3
  generalize hk0 : CtrlKeep.arrAt sy m i = n₀ at c1 c2 c3 c4 hs hw hdc' hhi hjump ⊢
  have A := CtrlKeep.ctrl_keep hc h0 hcl c1 c2 c3
  have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (trace m i n₀) x = peek m x := A.keep
  have hst' : peek (trace m i n₀) sy.Player_State = 0 := (kp _ (by simp [CtrlKeep.keepA])).trans hg
  have hj2 := hjump
  unfold FrameModel.readIn at hj2
  simp only [hst', beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hj2
  generalize hu' : (peek m sy.Player_XSpeedAbsolute).toNat = u at hab
  have habs : peek (trace m i n₀) sy.Player_XSpeedAbsolute = u.toUInt8 := by
    rw [kp _ (by simp [CtrlKeep.keepA]), ← hu']; simp
  have hS : { CtrlKeep.toA (ctxOf sy m0 v).W (CtrlKeep.valA sy v ++ OpenFlat.groundW sy (ctxOf sy m0 v).y0 ++
      [((I sy.JumpspringAnimCtrl, 0xFF, 0) : Watch), ((ctxOf sy m0 v).dI, 0xFF, 0), (I sy.Player_XSpeedAbsolute, 0xFF, u.toUInt8)] ++
      [((I sy.SavedJoypadBits, 0x80, 0x80) : Watch), (I sy.PreviousA_B_Buttons, 0x80, 0)]) B with log := [5, u] } ∈ startsA sy (ctxOf sy m0 v) v B := by
    unfold startsA
    exact List.mem_append_right _ (List.mem_map.2 ⟨u, List.mem_range.2 (by omega), rfl⟩)
  have hsS : Sim (PipeEntryRule.envOf m0) (m.frame, 2) { CtrlKeep.toA (ctxOf sy m0 v).W (CtrlKeep.valA sy v ++ OpenFlat.groundW sy (ctxOf sy m0 v).y0 ++
      [((I sy.JumpspringAnimCtrl, 0xFF, 0) : Watch), ((ctxOf sy m0 v).dI, 0xFF, 0), (I sy.Player_XSpeedAbsolute, 0xFF, u.toUInt8)] ++
      [((I sy.SavedJoypadBits, 0x80, 0x80) : Watch), (I sy.PreviousA_B_Buttons, 0x80, 0)]) B with log := [5, u] } (trace m i n₀) := by
    refine sim_log (CtrlKeep.sim_toA hs (CtrlKeep.watchA_lt v) ?_) _
    intro w hw'
    simp only [CtrlKeep.valA, OpenFlat.groundW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with (((hw' | hw' | hw') | hw' | hw' | hw' | hw' | hw') | hw' | hw' | hw') | hw' | hw' <;> subst hw'
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hv.1)
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hv.2.1)
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hv.2.2)
    · exact wff hst'
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hG.1)
    · exact wff (hhi.trans hG.2.1)
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hG.2.2.1)
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hG.2.2.2)
    · exact wff ((kp _ (by simp [CtrlKeep.keepA])).trans hj)
    · show (trace m i n₀).ram.get! (OpenMap.dcdI sy m0) &&& 0xFF = 0 &&& 0xFF
      rw [hdc']
    · exact wff habs
    · show (trace m i n₀).ram.get! (I sy.SavedJoypadBits) &&& 0x80 = 0x80 &&& 0x80
      rcases OpenFlat.and80_cases (peek (trace m i n₀) sy.SavedJoypadBits) with h | h
      · exact absurd h hj2.1
      · exact h
    · show (trace m i n₀).ram.get! (I sy.PreviousA_B_Buttons) &&& 0x80 = 0 &&& 0x80
      exact hj2.2
  have h0Φ : PhiT sy (ctxOf sy m0 v) (expT sy m0) m i n₀ n₀ [5, u] := ⟨⟨habs, noPc_nil _⟩, ⟨fun _ => hst', fun _ => trivial⟩⟩
  obtain ⟨J, j1, _, j3, j4, B', b1, b2⟩ := walk_frame (ctxOf sy m0 v) (expT sy m0) (cfgAOf sy m0 (ctxOf sy m0 v) (searchA sy m0 v)) rfl rfl rfl
    (table_ok hA.walk) hA.yd hA.hYH hA.hYV hA.hHV hA.hVS hA.hYS hA.hHS (hw _ hS) hsS c2 c4 hcq hr h0Φ
  obtain ⟨k₂, u', e1, e2, e3, _, e5, e6, e7, e8⟩ := end_take hst' b1 b2
  have hex : expT sy m0 u' = expT sy m0 u := by
    unfold expT
    rw [← e5, habs]
  exact ⟨k₂, J, e1, e2, j4, j3, e3, by rw [e6, hex], e7, e8⟩

end

end Smbrta.OpenAir
