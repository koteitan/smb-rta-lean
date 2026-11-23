import Theorems.VertModel

/-!
# The vertical step in the air: the fall force stays, and a fall reads neither the jump force nor the jump's origin

`RoomJoin.vstepR` is `Jump.vstep` on the machine of the player's routine: it runs the game's movement routine (`PlayerMovementSubs`) by `runSub`. In the air (the state 1
or 2) the routine does not write the fall force, the jump's origin or the state: only a takeoff writes them, and in the air with the swimming flag 0 it takes none
(`air_keep`). In a fall (the state 2) it first copies the fall force into the jump force, and it does not read the jump's origin: two states that differ only in the jump
force and the jump's origin give the same next state, but the origin (`fall_same`).

The proof is the walk of two machines of `runSub` (`FrameModel.runSub2`), with the detours of `VertModel` for the horizontal parts (`VertModel.detours`). The walk knows
the state, A, A on the frame before, the routine and the bytes of `vmach` that the walk reads; in a fall the jump force and the jump's origin are free on the two machines.
At the routine's return it asks that the fall force, the jump's origin and the state were not written, and in a fall that the other vertical bytes are the same on both.
The check is `keepOK`, eight walks (the state 1 or 2, A or not, A on the frame before or not).

`RoomJoin.RoomRun.off_stand` uses these two facts in place of the field `offStand` (round 35, page `1-1/c-7-8-3-OffStand.md`).

There is no game data in this file.
-/

namespace Smbrta.OffStand

open FrameModel (Rom TS Tag walkD I stkI lookN tagImp pokeL nodupB GoodH)
open VertModel (vmach vstepV vH vList vIdx vRun outV detours stopV fuelV)

/-- a case of the walk: the state (1 or 2), A on this frame, A on the frame before -/
structure KCase where
  st : UInt8
  a : Bool
  pa : Bool
  deriving DecidableEq

/-- the eight cases -/
def kCases : List KCase :=
  [(1 : UInt8), 2].flatMap fun st => [true, false].flatMap fun a => [true, false].map fun pa => { st, a, pa }

/-- the bytes the walk knows at the routine's entry, with their values on the machine of `vstep`: the bytes `vstep` writes but the vertical ones (with the stored speed 0),
and the bytes of `vmach` that the walk reads (`VertModel.outV`) -/
def knownK (sy : Syms) (m0 : Machine) (S : UInt8) (c : KCase) : List (Nat × UInt8) :=
  [(I sy.Player_State, c.st), (I sy.A_B_Buttons, if c.a then 0x80 else 0), (I sy.PreviousA_B_Buttons, if c.pa then 0x80 else 0),
   (I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8), (I sy.Player_XSpeedAbsolute, 0), (I sy.Player_X_Speed, 0), (I sy.Left_Right_Buttons, 0)] ++
  (outV sy).map fun i => (i, (vmach sy m0 S).ram.get! i)

/-- the tags of the walk: the known bytes; in a fall the jump force and the jump's origin may differ on the two machines -/
def tagsK (sy : Syms) (m0 : Machine) (S : UInt8) (c : KCase) : List (Nat × Tag) :=
  (knownK sy m0 S c).map (fun p => (p.1, Tag.kn p.2 p.2)) ++
    (if c.st == 2 then [(I sy.VerticalForce, Tag.any), (I sy.JumpOrigin_Y_Position, Tag.any)] else [])

/-- the walk's start: the movement routine, with the stack pointer of `runSub`'s call and the registers 0; the bytes not tagged are the same on the two machines -/
def startK (sy : Syms) (m0 : Machine) (S : UInt8) (c : KCase) : TS :=
  FrameModel.leafQD sy.PlayerMovementSubs (S - 2) (Tag.kn 0 0) Tag.eq (tagsK sy m0 S c)

/-- the vertical bytes that a fall gives the same on the two machines -/
def sameK (sy : Syms) : List Nat :=
  [I sy.Player_Y_Position, I sy.Player_Y_MoveForce, I sy.Player_Y_Speed, I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown, I sy.Player_State]

/-- the bytes that the routine does not write: the fall force, the jump's origin, the state, and the return address of `runSub` -/
def keptK (sy : Syms) (S : UInt8) : List Nat :=
  [I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position, I sy.Player_State, stkI S, stkI (S - 1)]

/-- at the routine's return: the bytes of `keptK` were not written; in a fall the bytes of `sameK` are the same on the two machines -/
def goalK (sy : Syms) (S : UInt8) (c : KCase) (Q : TS) : Bool :=
  (keptK sy S).all (fun i => !Q.w i) && (c.st != 2 || (sameK sy).all fun i => tagImp (Q.ram i) Tag.eq)

/-- one case of the walk -/
def caseK (sy : Syms) (m0 : Machine) (S : UInt8) (c : KCase) : Bool :=
  FrameModel.tagsOK S (tagsK sy m0 S c) &&
    walkD (Rom.of m0) (detours sy (Rom.of m0) S) (stopV (Rom.of m0) S) (goalK sy S c) fuelV (startK sy m0 S c)

/-- **The check on the ROM**: the machine, the detours, the bytes of `vstep`, and the eight walks -/
def keepOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool :=
  FrameModel.baseOK m0 && (detours sy (Rom.of m0) S).all (·.ok (Rom.of m0)) && nodupB (vIdx sy) && (outV sy).all (fun i => !(vIdx sy).contains i) &&
    [I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position, I sy.Player_State].all (fun i => decide (i < 2048) && i != stkI S && i != stkI (S - 1)) &&
    kCases.all (caseK sy m0 S)

section proof

variable {sy : Syms} {m0 : Machine} {S : UInt8}

theorem kcase_mem {st : UInt8} (h : st = 1 ∨ st = 2) (a pa : Bool) : ({ st, a, pa } : KCase) ∈ kCases := by
  rcases h with rfl | rfl <;> cases a <;> cases pa <;> decide

theorem poke_size (m : Machine) (a : UInt16) (v : UInt8) (h : m.ram.size = 2048) : (poke m a v).ram.size = 2048 := by
  rw [FrameModel.poke_eq, PipeTransitionAll.ba_size_set]
  exact h

/-- two lists of pokes at the same addresses, whose values agree at the byte `i` -/
def Agree (i : Nat) : List (UInt16 × UInt8) → List (UInt16 × UInt8) → Prop
  | [], [] => True
  | p :: l₁, q :: l₂ => (p.1 = q.1 ∧ (I p.1 = i → p.2 = q.2)) ∧ Agree i l₁ l₂
  | _, _ => False

/-- two lists of pokes at the same addresses, whose values agree at the byte `i`, agree there -/
theorem pokeL_agree {i : Nat} : ∀ (l₁ l₂ : List (UInt16 × UInt8)), Agree i l₁ l₂ →
    ∀ (m₁ m₂ : Machine), m₁.ram.size = 2048 → m₂.ram.size = 2048 → m₁.ram.get! i = m₂.ram.get! i → (pokeL m₁ l₁).ram.get! i = (pokeL m₂ l₂).ram.get! i
  | [], [], _, _, _, _, _, h => h
  | [], _ :: _, hl, _, _, _, _, _ => hl.elim
  | _ :: _, [], hl, _, _, _, _, _ => hl.elim
  | p :: l₁, q :: l₂, hl, m₁, m₂, s1, s2, h => by
    obtain ⟨⟨e1, e2⟩, hl'⟩ := hl
    show (pokeL (poke m₁ p.1 p.2) l₁).ram.get! i = (pokeL (poke m₂ q.1 q.2) l₂).ram.get! i
    refine pokeL_agree l₁ l₂ hl' _ _ (poke_size _ _ _ s1) (poke_size _ _ _ s2) ?_
    by_cases hi : I p.1 = i
    · rw [← hi, FrameModel.poke_get_self _ _ s1, e1, FrameModel.poke_get_self _ _ s2, e2 hi]
    · rw [FrameModel.poke_get_ne _ _ _ hi, FrameModel.poke_get_ne _ _ _ (by rw [← e1]; exact hi), h]

/-- the machines of `vstep` of two states that differ only in the jump force and the jump's origin agree on every other byte -/
theorem vH_agree (gV : GoodH (Rom.of m0) (vmach sy m0 S)) (s : Jump.VS) (a : Bool) (abs v o : UInt8) {i : Nat} (h1 : i ≠ I sy.VerticalForce)
    (h2 : i ≠ I sy.JumpOrigin_Y_Position) : (vH sy m0 S s a abs).ram.get! i = (vH sy m0 S { s with vf := v, origin := o } a abs).ram.get! i := by
  show (pokeL (vmach sy m0 S) (vList sy s a abs)).ram.get! i = (pokeL (vmach sy m0 S) (vList sy { s with vf := v, origin := o } a abs)).ram.get! i
  refine pokeL_agree _ _ ?_ _ _ gV.size gV.size rfl
  exact ⟨⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun h => absurd h.symm h1⟩, ⟨rfl, fun _ => rfl⟩,
    ⟨rfl, fun h => absurd h.symm h2⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩,
    ⟨rfl, fun _ => rfl⟩, trivial⟩

/-- **The walk of a case on two machines of `vstep`** (`FrameModel.runSub2`): from a state in the air, and from the same state with another jump force and jump's origin
(the same state in a jump), the routine does not write the fall force, the jump's origin and the state; in a fall the other vertical bytes are the same on both -/
theorem run_K (hk : keepOK sy m0 S = true) {s : Jump.VS} (hst : s.st = 1 ∨ s.st = 2) (a : Bool) (v o : UInt8) (hs1 : s.st = 1 → v = s.vf ∧ o = s.origin) :
    (vRun sy m0 S s a 0).ram.get! (I sy.VerticalForceDown) = s.vfd ∧ (vRun sy m0 S s a 0).ram.get! (I sy.JumpOrigin_Y_Position) = s.origin ∧
      (vRun sy m0 S s a 0).ram.get! (I sy.Player_State) = s.st ∧
      (s.st = 2 → ∀ i ∈ sameK sy, (vRun sy m0 S s a 0).ram.get! i = (vRun sy m0 S { s with vf := v, origin := o } a 0).ram.get! i) := by
  simp only [keepOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨hbase, hds⟩, hnd⟩, hout⟩, hidx⟩, hcases⟩ := hk
  let c : KCase := { st := s.st, a, pa := s.prevA }
  have hc := hcases c (kcase_mem hst a s.prevA)
  simp only [caseK, Bool.and_eq_true] at hc
  obtain ⟨htags, hwalk⟩ := hc
  have gB := FrameModel.base_good hbase
  have gP := FrameModel.poke_good (E := Rom.of m0) sy.DiffToHaltJump 1 gB
  have gV : GoodH (Rom.of m0) (vmach sy m0 S) := ⟨gP.prg, gP.mask, gP.halted, gP.trk, gP.size⟩
  let s' : Jump.VS := { s with vf := v, origin := o }
  have g1 : GoodH (Rom.of m0) (vH sy m0 S s a 0) := FrameModel.pokeL_good _ gV
  have g2 : GoodH (Rom.of m0) (vH sy m0 S s' a 0) := FrameModel.pokeL_good _ gV
  have s1 : (vH sy m0 S s a 0).s = S := by
    show (pokeL (vmach sy m0 S) _).s = S
    rw [FrameModel.pokeL_s]
    rfl
  have s2 : (vH sy m0 S s' a 0).s = S := by
    show (pokeL (vmach sy m0 S) _).s = S
    rw [FrameModel.pokeL_s]
    rfl
  have hv1 : ∀ q ∈ vList sy s a 0, (vH sy m0 S s a 0).ram.get! (I q.1) = q.2 :=
    FrameModel.pokeL_get _ _ gV (by rw [show (vList sy s a 0).map (fun q => I q.1) = vIdx sy from rfl]; exact hnd)
  have hv2 : ∀ q ∈ vList sy s' a 0, (vH sy m0 S s' a 0).ram.get! (I q.1) = q.2 :=
    FrameModel.pokeL_get _ _ gV (by rw [show (vList sy s' a 0).map (fun q => I q.1) = vIdx sy from rfl]; exact hnd)
  have hoN : ∀ (t : Jump.VS), ∀ i ∈ outV sy, (vH sy m0 S t a 0).ram.get! i = (vmach sy m0 S).ram.get! i := by
    intro t i hi
    refine FrameModel.pokeL_out _ _ (fun q hq e => ?_)
    have h1 := hout i hi
    have h2 : I q.1 ∈ vIdx sy := by
      rw [show vIdx sy = (vList sy t a 0).map (fun q => I q.1) from rfl]
      exact List.mem_map.2 ⟨q, hq, rfl⟩
    rw [e] at h2
    have h3 := List.contains_iff_mem.2 h2
    rw [h1] at h3
    cases h3
  -- the known bytes, on both machines
  have hkn : ∀ q ∈ knownK sy m0 S c, (vH sy m0 S s a 0).ram.get! q.1 = q.2 ∧ (vH sy m0 S s' a 0).ram.get! q.1 = q.2 := by
    intro q hq
    simp only [knownK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · exact ⟨hv1 (sy.Player_State, s.st) (by simp [vList]), hv2 (sy.Player_State, s'.st) (by simp [vList])⟩
    · exact ⟨hv1 (sy.A_B_Buttons, if a then 0x80 else 0) (by simp [vList]), hv2 (sy.A_B_Buttons, if a then 0x80 else 0) (by simp [vList])⟩
    · exact ⟨hv1 (sy.PreviousA_B_Buttons, if s.prevA then 0x80 else 0) (by simp [vList]),
        hv2 (sy.PreviousA_B_Buttons, if s'.prevA then 0x80 else 0) (by simp [vList])⟩
    · exact ⟨hv1 (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (by simp [vList]), hv2 (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (by simp [vList])⟩
    · exact ⟨hv1 (sy.Player_XSpeedAbsolute, 0) (by simp [vList]), hv2 (sy.Player_XSpeedAbsolute, 0) (by simp [vList])⟩
    · exact ⟨hv1 (sy.Player_X_Speed, 0) (by simp [vList]), hv2 (sy.Player_X_Speed, 0) (by simp [vList])⟩
    · exact ⟨hv1 (sy.Left_Right_Buttons, 0) (by simp [vList]), hv2 (sy.Left_Right_Buttons, 0) (by simp [vList])⟩
    · exact ⟨hoN s i hi, hoN s' i hi⟩
  have hL : ∀ p ∈ tagsK sy m0 S c, p.1 < 2048 ∧ p.1 ≠ stkI (vH sy m0 S s a 0).s ∧ p.1 ≠ stkI ((vH sy m0 S s a 0).s - 1) ∧
      p.2.R ((vH sy m0 S s a 0).ram.get! p.1) ((vH sy m0 S s' a 0).ram.get! p.1) := by
    intro p hp
    have ht := List.all_eq_true.1 htags p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at ht
    rw [s1]
    refine ⟨ht.1.1, ht.1.2, ht.2, ?_⟩
    simp only [tagsK, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · obtain ⟨e1, e2⟩ := hkn q hq
      show (Tag.kn q.2 q.2).R _ _
      rw [e1, e2]
      exact FrameModel.Tag.R_kn _ _
    · split at hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> trivial
      · cases hp
  have hd : ∀ i, i < 2048 → i ≠ stkI (vH sy m0 S s a 0).s → i ≠ stkI ((vH sy m0 S s a 0).s - 1) → lookN i (tagsK sy m0 S c) = none →
      Tag.eq.R ((vH sy m0 S s a 0).ram.get! i) ((vH sy m0 S s' a 0).ram.get! i) := by
    intro i _ _ _ hn
    show _ = _
    rcases hst with h | h
    · obtain ⟨ev, eo⟩ := hs1 h
      show _ = (vH sy m0 S { s with vf := v, origin := o } a 0).ram.get! i
      rw [ev, eo]
    · have hne := FrameModel.lookN_none hn
      have hc2 : (c.st == 2) = true := by simp [c, h]
      have m1 : (I sy.VerticalForce, Tag.any) ∈ tagsK sy m0 S c := by
        simp only [tagsK, hc2, if_true]
        exact List.mem_append_right _ (.head _)
      have m2 : (I sy.JumpOrigin_Y_Position, Tag.any) ∈ tagsK sy m0 S c := by
        simp only [tagsK, hc2, if_true]
        exact List.mem_append_right _ (.tail _ (.head _))
      exact vH_agree gV s a 0 v o (fun e => hne _ m1 e.symm) (fun e => hne _ m2 e.symm)
  have hstop : ∀ Q, stopV (Rom.of m0) S Q = true → 0x8000 ≤ Q.pc ∧ FrameModel.lookupOp ((Rom.of m0).b Q.pc) FrameModel.insList = some .rts ∧
      FrameModel.idleAt (Rom.of m0) Q.pc = false ∧ Q.s = some (S - 2) := by
    intro Q hQ
    simp only [stopV, FrameModel.isRts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hQ
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hQ
    exact ⟨h1, by rw [h2]; exact FrameModel.lookup_rts, h3, h4⟩
  have hgoal : ∀ Q, goalK sy S c Q = true → Q.w (stkI (vH sy m0 S s a 0).s) = false ∧ Q.w (stkI ((vH sy m0 S s a 0).s - 1)) = false := by
    intro Q hQ
    rw [s1]
    simp only [goalK, keptK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hQ
    exact ⟨hQ.1 (stkI S) (by simp), hQ.1 (stkI (S - 1)) (by simp)⟩
  obtain ⟨Q, _, hg, hR, hW⟩ := FrameModel.runSub2 (ds := detours sy (Rom.of m0) S) hds hwalk (by decide) hstop hgoal g1 g2 (by rw [s1])
    (by rw [s1, s2]) (FrameModel.Tag.R_kn 0 0) rfl hL hd
  simp only [goalK, keptK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true, bne_iff_ne, ne_eq] at hg
  obtain ⟨hw, hsame⟩ := hg
  have keep1 : ∀ i ∈ [I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position, I sy.Player_State],
      (vRun sy m0 S s a 0).ram.get! i = (vH sy m0 S s a 0).ram.get! i := by
    intro i hi
    have hx := hidx i hi
    rw [s1] at hW
    exact (hW i hx.1.1 (hw i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; rcases hi with rfl | rfl | rfl <;> simp)) hx.1.2 hx.2).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [keep1 _ (by simp)]
    exact hv1 (sy.VerticalForceDown, s.vfd) (by simp [vList])
  · rw [keep1 _ (by simp)]
    exact hv1 (sy.JumpOrigin_Y_Position, s.origin) (by simp [vList])
  · rw [keep1 _ (by simp)]
    exact hv1 (sy.Player_State, s.st) (by simp [vList])
  · intro h2 i hi
    have hc2 : ¬c.st ≠ 2 := by simp [c, h2]
    have hs := (hsame.resolve_left hc2) i hi
    have hi2 : i < 2048 := by
      simp only [sameK, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact FrameModel.I_lt _
    exact FrameModel.tagImp_R hs (hR i hi2)

/-- **In the air the vertical step keeps the fall force, the jump's origin and the state** -/
theorem air_keep (hk : keepOK sy m0 S = true) {s : Jump.VS} (hst : s.st = 1 ∨ s.st = 2) (a : Bool) :
    (vstepV sy m0 S s a 0).vfd = s.vfd ∧ (vstepV sy m0 S s a 0).origin = s.origin ∧ (vstepV sy m0 S s a 0).st = s.st := by
  obtain ⟨h1, h2, h3, _⟩ := run_K hk hst a s.vf s.origin (fun _ => ⟨rfl, rfl⟩)
  rw [VertModel.vstepV_eq]
  exact ⟨h1, h2, h3⟩

/-- **In a fall the vertical step reads neither the jump force nor the jump's origin**: from the same state with another jump force and origin it gives the same next
state, but the origin, which stays -/
theorem fall_same (hk : keepOK sy m0 S = true) {s : Jump.VS} (hst : s.st = 2) (a : Bool) (v o : UInt8) :
    vstepV sy m0 S s a 0 = { vstepV sy m0 S { s with vf := v, origin := o } a 0 with origin := s.origin } := by
  obtain ⟨_, h2, _, h4⟩ := run_K hk (Or.inr hst) a v o (fun h => absurd (h.symm.trans hst) (by decide))
  have h4' := h4 hst
  rw [VertModel.vstepV_eq, VertModel.vstepV_eq]
  simp only [sameK, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h4'
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := h4'
  show Jump.VS.mk _ _ _ _ _ _ _ _ _ = Jump.VS.mk _ _ _ _ _ _ _ _ _
  simp only [VertModel.peek_I]
  rw [e1, e2, e3, e4, e5, e6, e7, h2]

end proof

end Smbrta.OffStand
