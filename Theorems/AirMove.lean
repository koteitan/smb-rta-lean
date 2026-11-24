import Theorems.StoredClean
import Theorems.VertAir

/-! # The air speed cap on a real frame (round 37)

`A` is the air threshold (`AirFastSpeed`). In the air with the stored speed below it (`s < A`), `X_Physics` sets the caps of the speed to `A − 1` to the right and to
`−(A − 1)` to the left. From `|v| ≤ A − 1`, `ImposeFriction` with these caps keeps `|v| ≤ A − 1` and stores `|v|`. So a frame that comes to its player's routine in the
air (or with a jump that starts there) with `s < A` and `|v| ≤ A − 1` comes to the mover, and to the end of its move, with `|v| ≤ A − 1` and the stored speed at most
`A − 1`, and the move is `16·v` (`FrameModel.tail_spec`). No condition on the collision bits or on the stored speed being `|v|`.

* `physAirOK`: the walk of `X_Physics` from the cut of each case in the air with Left or Right, once for each stored speed `s < A`, known: at its return the caps are
  `A − 1` and `−(A − 1)`, and the adder is an entry of the table (`capsAir`).
* `fricAirOK`: `ImposeFriction` on the real machine next to the model's machine, with the collision bits known only on their two low bits (`ImposeFriction` reads them
  only in `and` with Left/Right), on each such case.
* `fricCapCheck`: `ImposeFriction` with these caps, from every speed with `|v| ≤ A − 1`, every fraction, adder and side, and each value of the two low bits, ends with
  `|v| ≤ A − 1` and the stored speed `|v|`.
* `air_c4`: the frame from the player's routine to the mover; `air_pathA`: on to the end of the move, with the move; `air_pathB`: on to the end of the move, with the
  stored speed (the walk `storedTailOK`).

There is no game data in this file. Page: `1-1/c-7-8-6-AirMove.md`.
-/

namespace Smbrta.FrameModel

open Potential (HS HIn hstep hstepN norm)
open TopSpeed (absB)
open TaintRun (AB bt)

section airMove
variable {sy : Syms} {E : Rom}

/-- the cap of the speed to the right in the air below the threshold, `A − 1`, as a byte -/
def capR (sy : Syms) : UInt8 := (sy.AirFastSpeed.toNat - 1).toUInt8

/-- the cap to the left, `−(A − 1)` -/
def capL (sy : Syms) : UInt8 := 0 - capR sy

/-- a case in the air (or with a jump that starts) with Left or Right: `ImposeFriction` runs -/
def airLR (c : Case) : Bool := stOf c.n != 0 && lrOf c.n != 0

/-- the cut at `X_Physics` with the stored speed known -/
def c1S (sy : Syms) (c1 : Cut) (s : UInt8) : Cut := { c1 with K := (I sy.Player_XSpeedAbsolute, s) :: c1.K }

/-- the caps are those of the air below the threshold, and the adder is an entry of the table -/
def capsAir (sy : Syms) (m0 : Machine) (Q : TS) : Bool :=
  match (Q.ram (I sy.MaximumRightSpeed)).same, (Q.ram (I sy.MaximumLeftSpeed)).same, (Q.ram (I sy.FrictionAdderLow)).same, (Q.ram (I sy.FrictionAdderHigh)).same with
  | some mr, some ml, some lo, some hi => mr == capR sy && ml == capL sy && (adders sy m0).contains (lo, hi)
  | _, _, _, _ => false

/-- `X_Physics` in the air with Left or Right, with each stored speed below the threshold known -/
def physAirOK (sy : Syms) (m0 : Machine) (S : UInt8) (c : Case) : Bool :=
  let P := planOf sy m0 S c
  !airLR c || (List.range sy.AirFastSpeed.toNat).all fun s =>
    walkT (Rom.of m0) (fun Q => Q.pc == P.r1) (fun Q => goalC (afterLeaf P.c1 P.r1) (I sy.SavedJoypadBits :: watchH sy) Q && capsAir sy m0 Q) fuelS
      (startQ (c1S sy P.c1 s.toUInt8))

/-- the friction's tags of `frameCaseOK`, but the collision bits: known only on their two low bits, the value `cc` of the model's machine -/
def tagsFrC (sy : Syms) (cc : UInt8) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.FrictionAdderLow, .eq), (I sy.FrictionAdderHigh, .eq), (I sy.MaximumRightSpeed, .eq),
   (I sy.MaximumLeftSpeed, .eq), (I sy.Player_CollisionBits, .ab ⟨cc, 3⟩ (AB.known cc))]

/-- what `ImposeFriction` does not write: the facing, the moving direction, `RunningSpeed`, the position, and the bytes known at its cut -/
def watchFr (sy : Syms) (c3 : Cut) : List Nat :=
  [I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ c3.ids

/-- `ImposeFriction` next to the model's machine with the collision bits known on two bits, on a case in the air with Left or Right -/
def fricAirOK (sy : Syms) (m0 : Machine) (S : UInt8) (c : Case) : Bool :=
  let P := planOf sy m0 S c
  let lr := lrOf c.n
  !airLR c || [(0 : UInt8), 1, 2, 3].all fun cc =>
    leafAll (Rom.of m0) m0.s sy.ImposeFriction P.r3 (Tag.kn lr lr) (tagsFrC sy cc) [(I sy.Player_X_Speed, .eq), (I sy.Player_XSpeedAbsolute, .eq)] (watchFr sy P.c3)

/-- **`ImposeFriction` with the air caps**: from `|v| ≤ A − 1` it ends with `|v| ≤ A − 1` and the stored speed `|v|` -/
def fricCapCheck (sy : Syms) (m0 : Machine) : Bool :=
  TopSpeed.bytes.all fun v => TopSpeed.bytes.all fun f => (adders sy m0).all fun p => [(1 : UInt8), 2, 3].all fun lr => [(0 : UInt8), 1, 2, 3].all fun cc =>
    !decide ((sbyte v).natAbs + 1 ≤ sy.AirFastSpeed.toNat) ||
      (let r := runSub (pokeL m0 (fricL sy v f p.1 p.2 (capR sy) (capL sy) cc)) sy.ImposeFriction lr 0 0
       decide ((sbyte (r.ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat) &&
         r.ram.get! (I sy.Player_XSpeedAbsolute) == absB (r.ram.get! (I sy.Player_X_Speed)))

/-- **The check on the ROM** of the air cap -/
def airOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool :=
  allCases.all (fun c => physAirOK sy m0 S c && fricAirOK sy m0 S c) && fricCapCheck sy m0 && decide (17 ≤ sy.AirFastSpeed.toNat) &&
    decide (sy.AirFastSpeed.toNat ≤ 128)

/-- what the check says -/
structure AirFacts (sy : Syms) (m0 : Machine) (S : UInt8) : Prop where
  cases : ∀ c ∈ allCases, physAirOK sy m0 S c = true ∧ fricAirOK sy m0 S c = true
  fric : fricCapCheck sy m0 = true
  /-- `16·(A − 1)` is at least one pixel, and `A` at most 128 -/
  a17 : 17 ≤ sy.AirFastSpeed.toNat
  a128 : sy.AirFastSpeed.toNat ≤ 128

theorem airFacts_of {m0 : Machine} {S : UInt8} (h : airOK sy m0 S = true) : AirFacts sy m0 S := by
  simp only [airOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun c hc => h1 c hc, h2, h3, h4⟩

theorem physAirOK_spec {m0 : Machine} {S : UInt8} {c : Case} (h : physAirOK sy m0 S c = true) (hc : airLR c = true) {s : UInt8}
    (hs : s.toNat < sy.AirFastSpeed.toNat) :
    walkT (Rom.of m0) (fun Q => Q.pc == (planOf sy m0 S c).r1)
      (fun Q => goalC (afterLeaf (planOf sy m0 S c).c1 (planOf sy m0 S c).r1) (I sy.SavedJoypadBits :: watchH sy) Q && capsAir sy m0 Q) fuelS
      (startQ (c1S sy (planOf sy m0 S c).c1 s)) = true := by
  simp only [physAirOK, hc, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h
  have e := h s.toNat hs
  rw [show s.toNat.toUInt8 = s from UInt8.ofNat_toNat] at e
  exact e

theorem fricAirOK_spec {m0 : Machine} {S : UInt8} {c : Case} (h : fricAirOK sy m0 S c = true) (hc : airLR c = true) {cc : UInt8}
    (hcc : cc ∈ [(0 : UInt8), 1, 2, 3]) :
    leafAll (Rom.of m0) m0.s sy.ImposeFriction (planOf sy m0 S c).r3 (Tag.kn (lrOf c.n) (lrOf c.n)) (tagsFrC sy cc)
      [(I sy.Player_X_Speed, .eq), (I sy.Player_XSpeedAbsolute, .eq)] (watchFr sy (planOf sy m0 S c).c3) = true := by
  simp only [fricAirOK, hc, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  exact h cc hcc

theorem fricCapCheck_spec {m0 : Machine} (h : fricCapCheck sy m0 = true) {v f lo hi lr cc : UInt8} (hv : (sbyte v).natAbs + 1 ≤ sy.AirFastSpeed.toNat)
    (hp : (lo, hi) ∈ adders sy m0) (hlr : lr ∈ [(1 : UInt8), 2, 3]) (hcc : cc ∈ [(0 : UInt8), 1, 2, 3]) :
    (sbyte ((runSub (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤
        sy.AirFastSpeed.toNat ∧
      (runSub (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_XSpeedAbsolute) =
        absB ((runSub (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed)) := by
  simp only [fricCapCheck, List.all_eq_true] at h
  have e := h v (Potential.mem_bytes v) f (Potential.mem_bytes f) (lo, hi) hp lr hlr cc hcc
  simp only [hv, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at e
  exact e

/-- the caps of the air, from what the walk knows -/
theorem capsAir_spec {m0 : Machine} {Q : TS} {r r' : Machine} {m₀ n₀ : Machine} (he : capsAir sy m0 Q = true) (h : Lk E m₀ n₀ Q r r') :
    r.ram.get! (I sy.MaximumRightSpeed) = capR sy ∧ r.ram.get! (I sy.MaximumLeftSpeed) = capL sy ∧
      ∃ lo hi, r.ram.get! (I sy.FrictionAdderLow) = lo ∧ r.ram.get! (I sy.FrictionAdderHigh) = hi ∧ (lo, hi) ∈ adders sy m0 := by
  unfold capsAir at he
  split at he
  · rename_i mr ml lo hi h1 h2 h3 h4
    simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at he
    obtain ⟨⟨e1, e2⟩, e3⟩ := he
    refine ⟨?_, ?_, lo, hi, (Tag.same_spec h3 (h.ram _ (I_lt _))).1, (Tag.same_spec h4 (h.ram _ (I_lt _))).1, e3⟩
    · rw [(Tag.same_spec h1 (h.ram _ (I_lt _))).1, e1]
    · rw [(Tag.same_spec h2 (h.ram _ (I_lt _))).1, e2]
  · cases he

/-- the cut of the case at the player's routine, from `VertAir.AtV` -/
theorem at_startV {S : UInt8} {R : Machine} (h : VertAir.AtV sy E S R) : At E ((caseOf sy R).c0 sy S) R := by
  refine ⟨h.good, h.pc, h.s, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Case.c0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.eng
    · rfl
    · rfl
    · rfl
    · exact h.spring
    · exact h.swim
    · exact h.size
  · intro p hp
    simp only [Case.c0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact and80_mem _
  · intro v hv
    cases hv
  · intro v hv
    cases hv
  · intro v hv
    cases hv

theorem caseOf_memV {S : UInt8} {R : Machine} (h : VertAir.AtV sy E S R) : caseOf sy R ∈ allCases := by
  refine List.mem_flatMap.2 ⟨_, h.st, List.mem_flatMap.2 ⟨_, h.area, List.mem_flatMap.2 ⟨peek R sy.PreviousA_B_Buttons &&& 0x80 != 0, by cases (peek R sy.PreviousA_B_Buttons &&& 0x80 != 0) <;> simp, ?_⟩⟩⟩
  refine List.mem_map.2 ⟨(peek R sy.SavedJoypadBits).toNat, List.mem_range.2 (peek R sy.SavedJoypadBits).toNat_lt, ?_⟩
  simp [caseOf]

theorem and3_mem (x : UInt8) : x &&& 3 ∈ [(0 : UInt8), 1, 2, 3] := by
  have h := and3_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  rcases h with h | h | h | h <;> rw [h] <;> simp

theorem and3_self {cc : UInt8} (h : cc ∈ [(0 : UInt8), 1, 2, 3]) : cc &&& 3 = cc := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem absB_toNat (v : UInt8) : (absB v).toNat = (sbyte v).natAbs := by
  have h1 := v.toNat_lt
  simp only [absB, sbyte]
  by_cases h : v < 0x80
  · rw [if_pos h, if_pos h]
    omega
  · rw [if_neg h, if_neg h]
    have h2 : ¬ v.toNat < 128 := fun h3 => h (UInt8.lt_iff_toNat_lt.2 h3)
    rw [UInt8.toNat_sub, show (0 : UInt8).toNat = 0 from rfl]
    omega

/-- **`ImposeFriction` with the air caps, on a real machine**, from its cut to the mover: `|v| ≤ A − 1` stays, and the stored speed is `|v|` -/
theorem fric_cap {m0 : Machine} {c3 c4 : Cut} {r3 : UInt16} {lr cc : UInt8} {R : Machine} {lo hi : UInt8}
    (hb : GoodH (Rom.of m0) m0) (hchk : fricCapCheck sy m0 = true) (hnd : nodupB (fricIdx sy) = true)
    (hv : (sbyte (R.ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat)
    (h1 : leafAll (Rom.of m0) m0.s sy.ImposeFriction r3 (Tag.kn lr lr) (tagsFrC sy cc) [(I sy.Player_X_Speed, .eq), (I sy.Player_XSpeedAbsolute, .eq)]
      (watchFr sy c3) = true)
    (h2 : pieceOK (Rom.of m0) (afterLeaf c3 r3) c4 (watchM sy) fuelS = true) (hra : c3.ra = some lr) (hpc : c3.pc = sy.ImposeFriction)
    (hlr : lr ∈ [(1 : UInt8), 2, 3]) (hA : At (Rom.of m0) c3 R) (hK3 : ∀ p ∈ c3.K, p.1 < 2048)
    (e1 : R.ram.get! (I sy.MaximumRightSpeed) = capR sy) (e2 : R.ram.get! (I sy.MaximumLeftSpeed) = capL sy)
    (e3 : R.ram.get! (I sy.FrictionAdderLow) = lo) (e4 : R.ram.get! (I sy.FrictionAdderHigh) = hi) (m3 : (lo, hi) ∈ adders sy m0)
    (hcc : cc ∈ [(0 : UInt8), 1, 2, 3]) (hcb : R.ram.get! (I sy.Player_CollisionBits) &&& 3 = cc) :
    ∃ k, At (Rom.of m0) c4 (stepN k R) ∧ (sbyte ((stepN k R).ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat ∧
      (stepN k R).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN k R).ram.get! (I sy.Player_X_Speed)) ∧ Same3 sy (stepN k R) R ∧
      InFrameN (Rom.of m0) R k := by
  generalize hv0 : R.ram.get! (I sy.Player_X_Speed) = v at hv
  generalize hf0 : R.ram.get! (I sy.Player_X_MoveForce) = f
  have hH := pokeL_good (fricL sy v f lo hi (capR sy) (capL sy) cc) hb
  have hHs : (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)).s = m0.s := pokeL_s _ _
  have hget : ∀ q ∈ fricL sy v f lo hi (capR sy) (capL sy) cc, (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)).ram.get! (I q.1) = q.2 :=
    pokeL_get _ _ hb hnd
  have hrel : ∀ p ∈ tagsFrC sy cc, p.2.R (R.ram.get! p.1) ((pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)).ram.get! p.1) := by
    intro p hp
    simp only [tagsFrC, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show _ = _
      rw [hget (sy.Player_X_Speed, v) (by simp [fricL])]
      exact hv0
    · show _ = _
      rw [hget (sy.Player_X_MoveForce, f) (by simp [fricL])]
      exact hf0
    · show _ = _
      rw [hget (sy.FrictionAdderLow, lo) (by simp [fricL])]
      exact e3
    · show _ = _
      rw [hget (sy.FrictionAdderHigh, hi) (by simp [fricL])]
      exact e4
    · show _ = _
      rw [hget (sy.MaximumRightSpeed, capR sy) (by simp [fricL])]
      exact e1
    · show _ = _
      rw [hget (sy.MaximumLeftSpeed, capL sy) (by simp [fricL])]
      exact e2
    · refine ⟨?_, ?_⟩
      · show R.ram.get! (I sy.Player_CollisionBits) &&& 3 = cc &&& 3
        rw [hcb, and3_self hcc]
      · show (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)).ram.get! (I sy.Player_CollisionBits) &&& 0xFF = cc &&& 0xFF
        rw [hget (sy.Player_CollisionBits, cc) (by simp [fricL])]
  have hae : R.a = lr := hA.ra lr hra
  obtain ⟨k1, _, g1, p1, s1, o1, w1, _, _, _, C1⟩ := leaf_app h1 hA.good (by rw [hA.pc, hpc]) (by rw [hae]; exact Tag.R_kn _ _) hH hHs hrel
  have hAf := at_after (r := r3) hA g1 p1 s1 (fun p hp => w1 _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (hK3 p hp))
  obtain ⟨k2, _, A2, W2, _, C2⟩ := piece_spec h2 hAf
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  have oV : (stepN k1 R).ram.get! (I sy.Player_X_Speed) =
      (runSub (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) :=
    o1 (I sy.Player_X_Speed, .eq) (by simp)
  have oA : (stepN k1 R).ram.get! (I sy.Player_XSpeedAbsolute) =
      (runSub (pokeL m0 (fricL sy v f lo hi (capR sy) (capL sy) cc)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_XSpeedAbsolute) :=
    o1 (I sy.Player_XSpeedAbsolute, .eq) (by simp)
  have w1' : ∀ i, i ∈ [I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] → (stepN k1 R).ram.get! i = R.ram.get! i := by
    intro i hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl
    · exact w1 _ (by simp [watchFr]) (I_lt _)
    · exact w1 _ (by simp [watchFr]) (I_lt _)
    · exact w1 _ (by simp [watchFr]) (I_lt _)
  obtain ⟨q1, q2⟩ := fricCapCheck_spec (f := f) hchk hv m3 hlr hcc
  refine ⟨k1 + k2, by rw [e]; exact A2, ?_, ?_, ?_, InFrameN.add C1 C2⟩
  · rw [e, W2 _ (by simp [watchM]) (I_lt _), oV]
    exact q1
  · rw [e, W2 _ (by simp [watchM]) (I_lt _), W2 _ (by simp [watchM]) (I_lt _), oV, oA]
    exact q2
  · rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]

/-- **From the player's routine to the mover, in the air below the threshold**: at the mover `|v| ≤ A − 1`, the stored speed is at most `A − 1`, and the position is
that of the player's routine. With Left or Right `X_Physics` sets the air caps (`physAirOK`) and `ImposeFriction` keeps `|v| ≤ A − 1` and stores `|v|` (`fric_cap`);
with neither the speed and the stored speed stay -/
theorem air_c4 {m0 : Machine} {S : UInt8} {R : Machine} (hb : GoodH (Rom.of m0) m0) (hF : ModelFacts sy m0 S) (hX : AirFacts sy m0 S)
    (h : VertAir.AtV sy (Rom.of m0) S R) (hst : stOf (caseOf sy R).n ≠ 0)
    (hs : (R.ram.get! (I sy.Player_XSpeedAbsolute)).toNat < sy.AirFastSpeed.toNat)
    (hv : (sbyte (R.ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat) :
    ∃ k, At (Rom.of m0) (planOf sy m0 S (caseOf sy R)).c4 (stepN k R) ∧
      (sbyte ((stepN k R).ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat ∧
      ((stepN k R).ram.get! (I sy.Player_XSpeedAbsolute)).toNat + 1 ≤ sy.AirFastSpeed.toNat ∧ Same3 sy (stepN k R) R ∧ InFrameN (Rom.of m0) R k := by
  have hmem := caseOf_memV h
  have hA0 := at_startV h
  obtain ⟨hc, hc2⟩ := hF.cases _ hmem
  obtain ⟨hp1, hp2⟩ := hX.cases _ hmem
  generalize hcc : caseOf sy R = c at hmem hA0 hc hc2 hp1 hp2 hst ⊢
  have hph := fun (hl : airLR c = true) {s : UInt8} (hs' : s.toNat < sy.AirFastSpeed.toNat) => physAirOK_spec hp1 hl hs'
  have hfr := fun (hl : airLR c = true) {cc : UInt8} (hcc3 : cc ∈ [(0 : UInt8), 1, 2, 3]) => fricAirOK_spec hp2 hl hcc3
  simp only [caseOK, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [frameCaseOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hc2
  generalize planOf sy m0 S c = P at hc hc2 hph hfr ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, a9⟩, _⟩, _⟩ := hc
  obtain ⟨⟨⟨_, x1⟩, _⟩, _⟩ := hc2
  obtain ⟨k1, _, A1, W1, _, C1⟩ := piece_spec a1 hA0
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have wG : ∀ j ∈ I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy, j < 2048 → R1.ram.get! j = R.ram.get! j := W1
  have eS1 : R1.ram.get! (I sy.Player_XSpeedAbsolute) = R.ram.get! (I sy.Player_XSpeedAbsolute) := wG _ (by simp [watchH]) (I_lt _)
  simp only [if_neg hst] at a9
  by_cases hl : (lrOf c.n != 0) = true
  · -- in the air, with Left or Right: the caps of the air
    have hal : airLR c = true := by
      simp only [airLR, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨hst, by simpa using hl⟩
    have hw := hph hal hs
    have A1' : At (Rom.of m0) (c1S sy P.c1 (R.ram.get! (I sy.Player_XSpeedAbsolute))) R1 := by
      refine ⟨A1.good, A1.pc, A1.s, ?_, A1.B, A1.ra, A1.x, A1.cf⟩
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact eS1
      · exact A1.K p hp
    obtain ⟨k2, Q2, _, A2, W2, _, cg, L2, C2⟩ :=
      piece_specX (c' := afterLeaf P.c1 P.r1) (watch := I sy.SavedJoypadBits :: watchH sy) (extra := capsAir sy m0) hw A1'
    generalize hR2 : stepN k2 R1 = R2 at A2 W2 L2
    obtain ⟨c1e, c2e, lo, hi, c3e, c4e, m3⟩ := capsAir_spec cg L2
    have wX : ∀ j ∈ I sy.SavedJoypadBits :: watchH sy, j < 2048 → R2.ram.get! j = R1.ram.get! j := W2
    have hk : ∀ j ∈ watchH sy, j < 2048 → R2.ram.get! j = R.ram.get! j := fun j hj hl' => by
      rw [wX j (List.mem_cons_of_mem _ hj) hl', wG j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hl']
    rw [if_pos hl] at a9
    simp only [Bool.and_eq_true] at a9
    obtain ⟨g, fc⟩ := a9
    simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
    obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
    obtain ⟨k3, _, A3, W3, B3, C3⟩ := piece_spec g A2
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have hCaps : ∀ j ∈ capsL sy, R3.ram.get! j = R2.ram.get! j := fun j hj => by
      have hl' : j < 2048 := by
        simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
      exact W3 j (List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl'
    have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
      rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
    have hpos : Same3 sy R3 R := by
      refine ⟨?_, ?_, ?_⟩
      · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
    have hne : lrOf c.n ≠ 0 := by simpa using hl
    have hlr3 : lrOf c.n ∈ [(1 : UInt8), 2, 3] := by
      have h4 := lrOf_mem c.n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h4 ⊢
      rcases h4 with h4 | h4 | h4 | h4
      · exact absurd h4 hne
      · exact Or.inl h4
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr h4)
    have hcc3 := and3_mem (R3.ram.get! (I sy.Player_CollisionBits))
    obtain ⟨k6, A6, V6, S6, P6, C6⟩ := fric_cap hb hX.fric hF.fnd (by rw [e1]; exact hv) (hfr hal hcc3) d4 d1 d2 hlr3 A3 B3
      (by rw [hCaps _ (by simp [capsL])]; exact c1e) (by rw [hCaps _ (by simp [capsL])]; exact c2e) (by rw [hCaps _ (by simp [capsL])]; exact c3e)
      (by rw [hCaps _ (by simp [capsL])]; exact c4e) m3 hcc3 rfl
    have hfin : stepN (k1 + (k2 + (k3 + k6))) R = stepN k6 R3 := by
      rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3]
    refine ⟨k1 + (k2 + (k3 + k6)), by rw [hfin]; exact A6, by rw [hfin]; exact V6, ?_, ?_, ?_⟩
    · rw [hfin, S6, absB_toNat]
      exact V6
    · rw [hfin]
      obtain ⟨s1, s2, s3⟩ := P6
      obtain ⟨t1, t2, t3⟩ := hpos
      exact ⟨s1.trans t1, s2.trans t2, s3.trans t3⟩
    · exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 (InFrameN.add' C3 hR3 C6))
  · -- in the air, with neither: the speed and the stored speed stay
    obtain ⟨k2, _, _, A2, W2, _, _, _, C2⟩ :=
      piece_specX (c' := afterLeaf P.c1 P.r1) (watch := I sy.SavedJoypadBits :: watchH sy) (extra := capsGood sy m0) x1 A1
    generalize hR2 : stepN k2 R1 = R2 at A2 W2
    have hk : ∀ j ∈ watchH sy, j < 2048 → R2.ram.get! j = R.ram.get! j := fun j hj hl' => by
      rw [W2 j (List.mem_cons_of_mem _ hj) hl', wG j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hl']
    rw [if_neg hl] at a9
    obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec a9 A2
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have hfin : stepN (k1 + (k2 + k3)) R = R3 := by
      rw [stepN_add, hR1, stepN_add, hR2, hR3]
    have ek : ∀ j ∈ watchH sy, R3.ram.get! j = R.ram.get! j := fun j hj => by
      have hl' : j < 2048 := by
        simp only [watchH, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact I_lt _
      rw [W3 _ (by simp only [watchA]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hj)) hl', hk _ hj hl']
    refine ⟨k1 + (k2 + k3), by rw [hfin]; exact A3, ?_, ?_, ?_, ?_⟩
    · rw [hfin, ek _ (by simp [watchH])]
      exact hv
    · rw [hfin, ek _ (by simp [watchH])]
      omega
    · rw [hfin]
      exact ⟨ek _ (by simp [watchH]), ek _ (by simp [watchH]), ek _ (by simp [watchH])⟩
    · exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)

/-- **To the end of the move, with the move** (round 37): from the player's routine in the air below the threshold the frame comes to `PlayerSubs` with
`|v| ≤ A − 1` and the position moved by `16·v`, modulo the size of the position -/
theorem air_pathA {m0 : Machine} {S : UInt8} {R : Machine} (hOK : modelOK sy m0 S = true) (hX : airOK sy m0 S = true)
    (h : VertAir.AtV sy (Rom.of m0) S R) (hst : stOf (caseOf sy R).n ≠ 0)
    (hs : (R.ram.get! (I sy.Player_XSpeedAbsolute)).toNat < sy.AirFastSpeed.toNat)
    (hv : (sbyte (R.ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat) :
    ∃ k, (stepN k R).pc = sy.PlayerSubs ∧ (sbyte ((stepN k R).ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat ∧
      (posP sy (stepN k R) - posP sy R - 16 * sbyte ((stepN k R).ram.get! (I sy.Player_X_Speed))) % 0x1000000 = 0 ∧ InFrameN (Rom.of m0) R k := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  obtain ⟨k1, A1, V1, _, S1, C1⟩ := air_c4 hb hF (airFacts_of hX) h hst hs hv
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memV h)
  have e4 : t = (planOf sy m0 S (caseOf sy R)).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, _, _, p2, v2, _, _, _, _, q2, C2⟩ := tail_spec htl hF.digits A1
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  have ePk : posP sy (stepN k1 R) = posP sy R := by
    rw [posP_eq, posP_eq]
    obtain ⟨s1, s2, s3⟩ := S1
    show posOf ((stepN k1 R).ram.get! (I sy.Player_PageLoc)) ((stepN k1 R).ram.get! (I sy.Player_X_Position)) ((stepN k1 R).ram.get! (I sy.SprObject_X_MoveForce)) =
      posOf (R.ram.get! (I sy.Player_PageLoc)) (R.ram.get! (I sy.Player_X_Position)) (R.ram.get! (I sy.SprObject_X_MoveForce))
    rw [s1, s2, s3]
  refine ⟨k1 + k2, by rw [e]; exact p2, by rw [e, v2]; exact V1, ?_, InFrameN.add C1 C2⟩
  rw [e, v2, ← ePk]
  exact q2

/-- **To the end of the move, with the stored speed** (round 37): from the player's routine in the air below the threshold the frame comes to `PlayerSubs` with the
stored speed at most `A − 1` (the walk `storedTailOK` from the mover writes neither the speed nor the stored speed) -/
theorem air_pathB {m0 : Machine} {S : UInt8} {R : Machine} (hOK : modelOK sy m0 S = true) (hso : storedOK sy m0 S = true) (hX : airOK sy m0 S = true)
    (h : VertAir.AtV sy (Rom.of m0) S R) (hst : stOf (caseOf sy R).n ≠ 0)
    (hs : (R.ram.get! (I sy.Player_XSpeedAbsolute)).toNat < sy.AirFastSpeed.toNat)
    (hv : (sbyte (R.ram.get! (I sy.Player_X_Speed))).natAbs + 1 ≤ sy.AirFastSpeed.toNat) :
    ∃ k, (stepN k R).pc = sy.PlayerSubs ∧ ((stepN k R).ram.get! (I sy.Player_XSpeedAbsolute)).toNat + 1 ≤ sy.AirFastSpeed.toNat ∧
      InFrameN (Rom.of m0) R k := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  simp only [storedOK, Bool.and_eq_true, List.all_eq_true] at hso
  obtain ⟨k1, A1, _, B1, _, C1⟩ := air_c4 hb hF (airFacts_of hX) h hst hs hv
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memV h)
  have e4 : t = (planOf sy m0 S (caseOf sy R)).c4 := cutSame_eq hte
  have htl := hso.2 t ht
  rw [e4] at htl
  obtain ⟨k2, _, A2, W2, _, C2⟩ := piece_spec htl A1
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  refine ⟨k1 + k2, by rw [e]; exact A2.pc, ?_, InFrameN.add C1 C2⟩
  rw [e, W2 _ (by simp) (I_lt _)]
  exact B1

end airMove

end Smbrta.FrameModel
