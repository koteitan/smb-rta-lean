import Theorems.RoomMap
import Theorems.SideEntryEnd

/-!
# The side pipe's entering frame: from the write to the frame's end

`SideEntryEnd` shows that at the first write of the side pipe's routine in a frame the position is at or right of the mouth's left end. Here the walk of the room's frames
(`RoomMap`: it knows the room's bytes and the target of every store) follows the entering frame to its end. At the write it splits the position into the pieces at or right of
the mouth (`splitR`: page 0 and the pixel at or right of its left end, or a page with one bit known to be 1), under the hypothesis that the position is there (`HypW`, which
`SideEntryEnd` gives). The walk asks at every state that the routine byte is known not to be the side pipe's, or that it is the side pipe's and the position is at or right of the
mouth (`okS`), and that once it is the side pipe's it stays so (`okT`).

So on a frame of the room that writes the side pipe's routine, the position at the frame's end is at or right of the mouth's left end (`rest_end`), and with `SideEntryEnd` with
no hypothesis on the position (`mouth_of_rows`).

There is no game data in this file. Page: `1-1/c-7-18-2-SideEntryEnd.md`.
-/

namespace Smbrta.SideEntryRest

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open SideChangeBound
open TaintRun
open PipeEntryRule (trace frame_trace trace_stop nxt rt findOp envOf known_eq sim_setK' forget)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids SearchS clampS preS weaken coverS startsR RoomCond MaskOK)
open PoleEntryRule (Spots onCol AtRead TilesOK px ptrAt)
open SideEntryEnd (rightPieces pageBits rightCover isV posOK)

/-! ## The walk -/

/-- the places of the walk -/
structure SideP where
  /-- the room's places, of `ScreenPage` -/
  P : Places
  /-- the side pipe's places -/
  Q : Spots
  /-- the routine byte, and the side pipe's routine -/
  rtI : Nat
  ev : UInt8
  deriving Inhabited

/-- the position at or right of the mouth, in pieces: page 0 and the pixel at or right of its left end, or a page with one bit known to be 1 -/
def splitR (Q : Spots) (A : AS) : List AS :=
  (rightPieces Q.left).map (fun a => (A.setK Q.xI a).setK Q.pI (AB.known 0)) ++ pageBits.map fun b => A.setK Q.pI b

/-- the byte is known not to be `v`: a known bit differs -/
def notV (v : UInt8) (b : AB) : Bool := v &&& b.k != b.v &&& b.k

/-- the pieces of the position: at the write of the side pipe's routine, while the routine byte is not the side pipe's -/
def zoneP (S : SideP) (A : AS) : List AS :=
  if A.pc == S.Q.write && notV S.ev (A.getK S.rtI) then splitR S.Q A else [A]

/-- all the pieces before a step: those of `ScreenPage` (by `SiteOK`), then those of the position -/
def preP (S : SideP) (A : AS) : List AS := (preS S.P A).flatMap (zoneP S)

/-- the routine byte is known not to be the side pipe's, or it is the side pipe's and the position is at or right of the mouth -/
def okS (S : SideP) (B : AS) : Bool := notV S.ev (B.getK S.rtI) || (isV S.ev (B.getK S.rtI) && posOK S.Q B)

/-- once the routine byte is the side pipe's, it stays so -/
def okT (S : SideP) (A B : AS) : Bool := !isV S.ev (A.getK S.rtI) || isV S.ev (B.getK S.rtI)

/-- what the frame asks of one state: at the write, while the routine byte is not the side pipe's, the position is at or right of the mouth -/
def HypW (S : SideP) (m : Machine) : Prop := m.pc = S.Q.write → m.ram.get! S.rtI ≠ S.ev → S.Q.left ≤ px S.Q m

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end. At every state `okS`, at every step `okT`. The step is `RoomMap`'s. -/
def walkP (S : SideP) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => okS S A && (preP S (clampS C.P A)).all fun A₁ => (RoomMap.stepT C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      okS S B && okT S A B &&
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkP S C n (weaken C B)
      else B.k == A.k + 1

/-! ## Finding the table: a search, no part of the proof -/

/-- the key: that of `RoomMap`'s search; with the side pipe's routine, also the position -/
def keyP (S : SideP) (Z : Aids) (E : Env) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := Z.key E A
  if isV S.ev (A.getK S.rtI) then (n * 65536 + num (A.getK S.Q.xI)) * 65536 + num (A.getK S.Q.pI) else n

def routeP (S : SideP) (Z : Aids) (E : Env) (X : SearchS) (B0 : AS) : SearchS :=
  let B := clampS S.P (Z.norm B0)
  let K := keyP S Z E B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D =>
    if B.le D then X else
    let J := D.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 then { J with hi := S.P.late } else J
    SearchS.put { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => SearchS.put { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

partial def runP (S : SideP) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preP S (clampS S.P cur)).flatMap (RoomMap.stepT S.P E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := !okS S cur || rs.any fun r => match r with
      | none => true
      | some B => !okS S B || !okT S cur B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (Z.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          b.pc != S.Q.write && (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeP S Z E X b
    break
  return X

partial def searchP (S : SideP) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := keyP S Z E A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runP S Z E ops X A
  return X

def searchOf (S : SideP) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchP S Z E ops ((startsR r K).foldl (routeP S Z E) {})

/-- the configuration from the table found -/
def cfgOf (S : SideP) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOf S Z E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd]).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P := S.P, fin := fun _ => true, t := q.1, key := keyP S Z E, idx := q.2.1, cut := q.2.2, norm := Z.norm, normAt := at0 }

/-- **The check of the walk.** -/
def walkCheckP (S : SideP) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOf S Z E r K
  ScreenPage.placesOK E S.P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K &&
    decide (S.Q.xI < 2048) && decide (S.Q.pI < 2048) && decide (S.rtI < 2048) && decide (S.Q.left < 256) && rightCover S.Q.left &&
    C.t.all (walkP S C ScreenPage.fuelS) && (startsR r K).all (walkP S C ScreenPage.fuelS)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

/-- the split at the write covers a machine whose position is at or right of the mouth -/
theorem cov_splitR {Q : Spots} (hr : rightCover Q.left = true) {A : AS} {m : Machine} (hs : Sim E F A m) (hpx : Q.left ≤ px Q m) :
    ∃ B ∈ splitR Q A, Sim E F B m ∧ B.k = A.k := by
  unfold splitR
  by_cases h0 : m.ram.get! Q.pI = 0
  · have hpage : (AB.known 0).mem (m.ram.get! Q.pI) := by rw [h0]; exact mem_known_self _
    have hx : Q.left ≤ (m.ram.get! Q.xI).toNat := by
      unfold px at hpx
      rw [h0] at hpx
      simpa using hpx
    obtain ⟨a, ha, hm⟩ := SideEntryEnd.right_piece hr hx
    exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩), sim_setK' (sim_setK' hs hm) hpage, rfl⟩
  · obtain ⟨a, ha, hm⟩ := SideEntryEnd.page_bit h0
    exact ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩), sim_setK' hs hm, rfl⟩

/-- a byte known not to be `v` is not `v` -/
theorem ne_of_notV {v : UInt8} {b : AB} {x : UInt8} (h : notV v b = true) (hm : b.mem x) : x ≠ v := by
  intro e
  subst e
  simp only [notV, bne_iff_ne, ne_eq] at h
  exact h hm

/-- the pieces of a step cover every machine that meets `HypW` -/
theorem cov_zoneP {S : SideP} (hr : S.rtI < 2048) (hc : rightCover S.Q.left = true) {A : AS} {m : Machine}
    (hs : Sim E F A m) (hh : HypW S m) : ∃ B ∈ zoneP S A, Sim E F B m ∧ B.k = A.k := by
  unfold zoneP
  by_cases h : (A.pc == S.Q.write && notV S.ev (A.getK S.rtI)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact cov_splitR hc hs (hh (by rw [hs.pc]; exact h.1) (ne_of_notV h.2 (hs.ram _ hr)))
  · rw [if_neg h]
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_preP {S : SideP} (hO : PlacesOK E S.P) (hr : S.rtI < 2048) (hc : rightCover S.Q.left = true) {A : AS} {m : Machine}
    (hs : Sim E F A m) (hh : SiteOK S.P m) (hw : HypW S m) : ∃ B ∈ preP S A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, k1⟩ := ScreenPage.cov_preS hO hs hh
  obtain ⟨D, hD, h2, k2⟩ := cov_zoneP hr hc h1 hw
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h2, by rw [k2, k1]⟩

/-- `okS` on a covering state: the routine byte is not the side pipe's, or the position is at or right of the mouth -/
theorem of_okS {S : SideP} (hr : S.rtI < 2048) (hx : S.Q.xI < 2048) (hp : S.Q.pI < 2048) (hl : S.Q.left < 256) {B : AS} {m : Machine} (hs : Sim E F B m)
    (h : okS S B = true) : m.ram.get! S.rtI = S.ev → S.Q.left ≤ px S.Q m := by
  intro he
  simp only [okS, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h1 | ⟨_, h2⟩
  · exact absurd he (ne_of_notV h1 (hs.ram _ hr))
  · exact SideEntryEnd.px_of_posOK hx hp hl hs h2

/-- `okS` and `okT`: once the routine byte of the machine is the side pipe's, it is so after the step -/
theorem of_okT {S : SideP} (hr : S.rtI < 2048) {A B : AS} {m m' : Machine} (hs : Sim E F A m) (hs' : Sim E F B m') (h1 : okS S A = true) (h2 : okT S A B = true)
    (he : m.ram.get! S.rtI = S.ev) : m'.ram.get! S.rtI = S.ev := by
  simp only [okS, Bool.or_eq_true, Bool.and_eq_true] at h1
  have hA : isV S.ev (A.getK S.rtI) = true := by
    rcases h1 with h3 | ⟨h3, _⟩
    · exact absurd he (ne_of_notV h3 (hs.ram _ hr))
    · exact h3
  simp only [okT, hA, Bool.not_true, Bool.false_or] at h2
  simp only [isV, Bool.and_eq_true, beq_iff_eq] at h2
  rw [known_eq h2.1 (hs'.ram _ hr), h2.2]

end

/-! ## The walk covers the machine -/

section
variable {S : SideP} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveP (S : SideP) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkP S C n A = true

theorem okS_of_walkP {n : Nat} {A : AS} (h : walkP S C n A = true) : okS S A = true := by
  cases n with
  | zero => simp [walkP] at h
  | succ n =>
    simp only [walkP, Bool.and_eq_true] at h
    exact h.1

theorem cover_liveP (ht : C.t.all (walkP S C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ D, LiveP S C F D m ∧ D.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

/-- **One step of the walk**, as `RoomMap.live_stepT`: the next machine is covered by a live state in the same frame, or the frame ends in a state that passes `okS`; and once the
routine byte is the side pipe's, it stays so -/
theorem live_stepP (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hr : S.rtI < 2048) (hc : rightCover S.Q.left = true)
    (ht : C.t.all (walkP S C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hlv : LiveP S C F A m) (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) (hw : HypW S m) :
    ((∃ A', LiveP S C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
      ((go step m).2.frame = m.frame + 1 ∧ ∃ B, okS S B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2)) ∧
    (m.ram.get! S.rtI = S.ev → (go step m).2.ram.get! S.rtI = S.ev) := by
  obtain ⟨hs, n, hwk⟩ := hlv
  have hok := okS_of_walkP hwk
  cases n with
  | zero => simp [walkP] at hwk
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    have hhS : SiteOK S.P m := by rw [← hP]; exact hh
    have hOS : PlacesOK C.E S.P := by rw [← hP]; exact hO
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preP hOS hr hc hs0 hhS hw
    obtain ⟨r, hr1, hB⟩ := RoomMap.s_stepT hO hops hT hs1 hh
    simp only [walkP, List.all_eq_true, Bool.and_eq_true] at hwk
    have hw2 := hwk.2 A₁ hA r hr1
    have hkA : A₁.k = A.k := by rw [hk1, ScreenPage.clamp_k]
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rw [Bool.and_eq_true, Bool.and_eq_true] at hw2
      obtain ⟨⟨hokB, hokT⟩, hw3⟩ := hw2
      have hper : m.ram.get! S.rtI = S.ev → (go step m).2.ram.get! S.rtI = S.ev := of_okT hr hs h1 hok hokT
      refine ⟨?_, hper⟩
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hkA] at k1
        rw [if_pos (by simp [k1])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
        have hN : Sim C.E F (weaken C B) (go step m).2 ∧ (weaken C B).k = B.k := by
          unfold weaken
          split
          · rename_i hcd
            simp only [Bool.and_eq_true] at hcd
            have h5 := sim_le hcd.2 h1
            refine ⟨h5, ?_⟩
            have hle := hcd.2
            simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
            exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
          · exact ⟨h1, rfl⟩
        rcases hw3 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveP ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h3
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw3
        exact ⟨k2, B, hokB, k1, h1⟩

end

/-! ## The frame -/

/-- what the check says -/
structure RestOK (S : SideP) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) : Prop where
  places : PlacesOK E S.P
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  pl : C.P = S.P
  ops : C.ops = (aRows C.E).toArray
  xI : S.Q.xI < 2048
  pI : S.Q.pI < 2048
  rt : S.rtI < 2048
  left : S.Q.left < 256
  right : rightCover S.Q.left = true
  table : C.t.all (walkP S C ScreenPage.fuelS) = true
  starts : ∀ A ∈ startsR r K, walkP S C ScreenPage.fuelS A = true

theorem restOK_of_check {S : SideP} {Z : Aids} {E : Env} {r : Machine} {K : List (Nat × UInt8)} (h : walkCheckP S Z E r K = true) :
    RestOK S E r K (cfgOf S Z E r K) := by
  simp only [walkCheckP, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h10⟩, h11⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, h4, h5, h6, h7, h8, h10, h11⟩

/-- **The rest of the entering frame.** A frame that starts in the room's condition, with `SiteOK` on each instruction, and with the position at or right of the mouth at the
write while the routine byte is not the side pipe's (`HypW`, asked only while no instruction before has made it the side pipe's): if an instruction makes the routine byte the
side pipe's, the position at the frame's end is at or right of the mouth's left end. -/
theorem rest_end {S : SideP} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : RestOK S E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j))
    (hw : ∀ j, (∀ k, k ≤ j → (trace m i k).ram.get! S.rtI ≠ S.ev) → HypW S (trace m i j))
    (he : ∃ n, (trace m i n).ram.get! S.rtI ≠ S.ev ∧ (trace m i (n + 1)).ram.get! S.rtI = S.ev) :
    S.Q.left ≤ px S.Q (frame m i) := by
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hs0 : Sim C.E (m.frame, 2) S0 { m with pad := smbToPad i } := by
    rw [h.env]
    exact { hs with pad := by rw [h.pad]; exact mem_top _ }
  have hT : 2 ≤ (m.frame, (2 : UInt8)).2.toNat := by show 2 ≤ (2 : UInt8).toNat; decide
  -- the invariant: covered by a live state in the frame, or the frame has ended in a state that passes `okS`; and the routine byte stays the side pipe's
  have key : ∀ j, ((∃ A, LiveP S C (m.frame, 2) A (trace m i j) ∧ A.k = S0.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, okS S B = true ∧ Sim C.E (m.frame, 2) B (trace m i j))) ∧
      (∀ k, k ≤ j → (trace m i k).ram.get! S.rtI = S.ev → (trace m i j).ram.get! S.rtI = S.ev) := by
    intro j
    induction j with
    | zero =>
      refine ⟨Or.inl ⟨S0, ⟨hs0, ScreenPage.fuelS, h.starts S0 hS⟩, rfl, rfl, Nat.le_refl _⟩, fun k hk0 he0 => ?_⟩
      have : k = 0 := by omega
      subst this
      exact he0
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      -- `HypW` at `j`: before any write by the hypothesis, after it the routine byte is the side pipe's
      have hwj : HypW S (trace m i j) := by
        by_cases hb : ∀ k, k ≤ j → (trace m i k).ram.get! S.rtI ≠ S.ev
        · exact hw j hb
        · intro _ hne
          apply absurd _ hne
          have : ∃ k, k ≤ j ∧ (trace m i k).ram.get! S.rtI = S.ev :=
            Classical.byContradiction fun hn => hb (fun k hk he' => hn ⟨k, hk, he'⟩)
          obtain ⟨k, hk1, hk2⟩ := this
          exact ih2 k hk1 hk2
      rcases ih1 with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hk' (j + 1)
        rw [e2] at hh2 ⊢
        obtain ⟨hst, hper⟩ := live_stepP hO h.pl h.rt h.right h.table h.ops hT h1 (hk' j) hh2 hwj
        refine ⟨?_, fun k hk1 hk2 => ?_⟩
        · rcases hst with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, _, a4⟩
          · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
          · exact Or.inr ⟨by rw [a1, h3], B, a2, a4⟩
        · by_cases hkj : k ≤ j
          · exact hper (ih2 k hkj hk2)
          · have : k = j + 1 := by omega
            subst this
            rw [e2] at hk2
            exact hk2
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        refine ⟨Or.inr ⟨h1, B, h2, h4⟩, fun k hk1 hk2 => ?_⟩
        by_cases hkj : k ≤ j
        · exact ih2 k hkj hk2
        · have : k = j + 1 := by omega
          subst this
          rw [e2] at hk2
          exact hk2
  -- at `fuelPerFrame` the frame has ended
  have hend : ∃ B, okS S B = true ∧ Sim C.E (m.frame, 2) B (trace m i fuelPerFrame) ∧ (trace m i fuelPerFrame).frame = m.frame + 1 := by
    rcases (key fuelPerFrame).1 with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h3⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨B, h2, h3, h1⟩
  obtain ⟨B, hB1, hB2, hB3⟩ := hend
  obtain ⟨n, _, hn2⟩ := he
  -- the routine byte is the side pipe's at the frame's end
  have hstop : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by
    simp [hB3]
  have e3 : trace m i (fuelPerFrame + (n + 1)) = trace m i fuelPerFrame := trace_stop hstop (n + 1)
  have hev : (trace m i fuelPerFrame).ram.get! S.rtI = S.ev := by
    rw [← e3]
    exact (key (fuelPerFrame + (n + 1))).2 (n + 1) (by omega) hn2
  rw [frame_trace]
  exact of_okS h.rt h.xI h.pI h.left hB2 hB1 hev

/-! ## On the ROM -/

section
open ScreenPage (placesR envR refR aidsOf)

/-- the places, from the symbols and the ROM -/
def sidePOf (sy : Syms) (nm : Names) (m0 : Machine) : SideP :=
  { P := placesR sy nm m0, Q := SideEntryRule.spots sy m0, rtI := (sy.GameEngineSubroutine &&& 0x7FF).toNat, ev := SideEntryRule.vs sy }

/-- **The check on the ROM.** -/
def restCheck (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  walkCheckP (sidePOf sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

end

/-! ## The entering frame of the room -/

section
open ScreenPage (placesR envR refR aidsOf)
open PipeChangeEnd (Data InRowsT)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- the conditions of a guard do not look at the places cut -/
theorem clean_withCuts {G : PipeWrites.Guard} {c : List UInt16} {m : Machine} (h : PipeWrites.Clean G m) : PipeWrites.Clean { G with cuts := c } m :=
  ⟨h.store, h.read, h.jump, h.time⟩

theorem start_withCuts {G : PipeWrites.Guard} {c : List UInt16} {E : Env} {m : Machine} (h : PipeWrites.FrameStart G E m) :
    PipeWrites.FrameStart { G with cuts := c } E m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- the conditions of the room's guard are those of the walk of `SideEntryEnd` -/
theorem clean_E {m : Machine} (h : PipeWrites.Clean (SideFrame.roomG sy m0) m) : PipeWrites.Clean (SideEntryEnd.sideOfE sy m0).G m := by
  show PipeWrites.Clean { (SideFrame.sideOf sy m0).G with cuts := [PipeWrites.headAt sy m0, SideFrame.bumpAt sy m0] } m
  exact clean_withCuts (SideFrame.clean_side h)

theorem start_E {E : Env} {m : Machine} (h : PipeWrites.FrameStart (SideFrame.roomG sy m0) E m) : PipeWrites.FrameStart (SideEntryEnd.sideOfE sy m0).G E m := by
  show PipeWrites.FrameStart { (SideFrame.sideOf sy m0).G with cuts := [PipeWrites.headAt sy m0, SideFrame.bumpAt sy m0] } E m
  exact start_withCuts (SideFrame.start_side h)

/-- **The position at the end of the entering frame, on the real machines.** A frame of the room (from `b` to `a`, under the conditions of `RoomMap.map_of_rows`) that writes the
side pipe's routine ends with the position at or right of the mouth's left end. `SideEntryEnd` gives the position at the first write, `rest_end` carries it to the frame's end.
`hc`, `hs`, `hA`, `hB` and `hF` are checks on the ROM. -/
theorem mouth_of_rows (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hs : RoomMap.startCheckF sy nmS m0 = true)
    (hA : SideEntryEnd.sideEntryEndCheck sy m0 = true) (hB : restCheck sy nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    {k : Nat} (h1 : b ≤ k) (h2 : k < a) (hen : SideEntryRule.Enters sy (seq k) (inp k)) :
    SidePipe.mouthP sy 0 ≤ posP sy (frame (seq k) (inp k)) := by
  simp only [SideEntryEnd.sideEntryEndCheck, Bool.and_eq_true] at hA
  -- the first write, by the walk of `SideEntryEnd`
  have hw := SideEntryEnd.write_right_of_left (S := SideEntryEnd.sideOfE sy m0) (E := envOf m0) hA.2 rfl
    (start_E (RoomMap.start_of_rowsF hF hc hs next hin hctl sites stay k h1 h2))
    (fun j => ⟨clean_E (RoomMap.clean_of_rows hF hc next hin hctl sites stay k h1 h2 j),
      (RoomMap.map_of_rows hF hc next hin hctl sites stay).2 k h1 h2 j, by
        show (trace (seq k) (inp k) j).pc ∉ [PipeWrites.headAt sy m0, SideFrame.bumpAt sy m0]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨RoomMap.head_of_rows hF hc next hin hctl sites stay k h1 h2 j, RoomMap.bump_of_rows hF hc next hin hctl sites stay k h1 h2 j⟩⟩)
  -- the rest of the frame, by the walk of the room
  have hcond := (RoomMap.map_run hF.ok next (RoomMap.start_of_rows hc hin hctl) sites stay).1 k h1 h2
  obtain ⟨n, hn⟩ := hen
  have hx := rest_end (S := sidePOf sy nmS m0) (restOK_of_check hB) hcond (sites k h1 h2) (fun j hb hpc hne => hw j hb hpc)
    ⟨n, hn.1, hn.2⟩
  have h7 : (sidePOf sy nmS m0).Q.xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (sidePOf sy nmS m0).Q.pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  have h9 : (sidePOf sy nmS m0).Q.left = SidePipe.xLo sy := rfl
  unfold px at hx
  rw [h7, h8, h9] at hx
  unfold SidePipe.mouthP posP peek
  omega

end

end Smbrta.SideEntryRest
