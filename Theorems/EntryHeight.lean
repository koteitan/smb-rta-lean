import Theorems.SideEntryRest
import Theorems.RoomMusic

/-!
# The height at the side pipe's entry

`Route.ChangesBase.entry₂` asked the player's height (`Player_Y_Position`) at the side pipe's entry to be the reference's. Here it is proved for a frame of the room that
starts with the player's size of the reference (small), by one more walk of the room's frame (`RoomMap`'s machine).

The side pipe's code asks the player's state to be standing. The collision routine first makes the state not standing, and it makes it standing again only where the player
lands, right after it has rounded the height down to a row. So on a frame that enters, the height is a row's. The walk splits the height's high bits where the foot check
reads it (`topY`) and its values after the landing's store, so after the landing the height is known. Then it splits the column where the block buffer's address is
made (`lowA`), so the place of a side read is known, and the read takes the byte of the block buffers, of which the room's condition knows the bits that are 0 in the
map (`stepY`). Only one place of the map admits a side pipe's tile, and with the small player's offsets only one height reads it.

The walk and its frame theorem (`walkY`, `WalkOK`, `frame_end`) take the condition on the frame's end as a parameter; `EntryBuffer` uses them for the screen's buffer.

So a frame of the room that starts with the reference's size and ends with the side pipe's routine ends with the reference's height (`height_frame`), and on the real
machines (`height_of_rows`).

There is no game data in this file. Page: `1-1/d-2-5-4-EntryHeight.md`.
-/

namespace Smbrta.EntryHeight

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open SideChangeBound
open TaintRun
open PipeEntryRule (trace frame_trace trace_stop nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids SearchS clampS preS weaken coverS startsR RoomCond MaskOK)
open SideEntryEnd (isV)
open SideEntryRest (notV ne_of_notV)

/-! ## The walk -/

/-- the places of the walk -/
structure HP where
  /-- the room's places, of `ScreenPage` -/
  P : Places
  /-- the routine byte, and the side pipe's routine -/
  rtI : Nat
  ev : UInt8
  /-- the height, and the reference's height -/
  yI : Nat
  yv : UInt8
  /-- the foot check's read of the height, and the place after the landing's store of the height -/
  footAt : UInt16
  landAt : UInt16
  /-- the routine that makes the block buffer's address from the column -/
  colAt : UInt16
  /-- the byte where the block buffer routine saves the tile, and the place after the save -/
  tileI : Nat
  tileAt : UInt16
  /-- the pointer of the block buffer routine's read (two bytes), and the start of the side check: only for the search -/
  ptrI : Nat
  sideAt : UInt16
  deriving Inhabited

/-- the bit `c` of the byte `d` is known to be 1 -/
def bitSet (d : Nat) (c : UInt8) (A : AS) : Bool := (A.getK d).bit c == some true

/-- bits 5 and 4 of the byte `d`, if bit 6 is known to be 1 -/
def top2 (d : Nat) (C : AS) : List AS := if bitSet d 64 C then (splitBit d 32 C).flatMap (splitBit d 16) else [C]

/-- bit 6 of the byte `d` and then `top2`, if bit 7 is known to be 1 -/
def top1 (d : Nat) (B : AS) : List AS := if bitSet d 128 B then (splitBit d 64 B).flatMap (top2 d) else [B]

/-- the high bits of the byte `d`, as far as a compare with a height near the screen's bottom needs them: bit 7; if it is 1, bit 6; if both are 1, bits 5 and 4 -/
def topY (d : Nat) (A : AS) : List AS := (splitBit d 128 A).flatMap (top1 d)

/-- the five low bits of the accumulator -/
def lowA (A : AS) : List AS :=
  (PipeChangeEnd.bitA 16 A).flatMap fun B => (PipeChangeEnd.bitA 8 B).flatMap fun C => (PipeChangeEnd.bitA 4 C).flatMap fun D =>
    (PipeChangeEnd.bitA 2 D).flatMap (PipeChangeEnd.bitA 1)

/-- the pieces of the height's walk: at the foot check's read of the height, its high bits; after the landing's store of the height, its values; where the block
buffer's address is made, with the height known, the column; after the save of a tile, its values -/
def zoneY (S : HP) (A : AS) : List AS :=
  if A.pc == S.footAt then topY S.yI A
  else if A.pc == S.landAt then PipeEntryRule.splitAll S.yI A
  else if A.pc == S.colAt && (A.getK S.yI).isK then lowA A
  else if A.pc == S.tileAt then PipeEntryRule.splitAll S.tileI A
  else [A]

/-- all the pieces before a step: those of `ScreenPage` (by `SiteOK`), then those of the height -/
def preY (S : HP) (A : AS) : List AS := (preS S.P A).flatMap (zoneY S)

/-- a step: at the read of the block buffer routine with the place known, the machine's own step (it reads the byte of the block buffers); else the step of `RoomMap` -/
def stepY (P : Places) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if !A.nmi && A.pc == P.read && !ScreenPage.ptrNotKnown E A && A.y.isK then succs E ops A
  else RoomMap.stepT P E ops A

/-- at the frame's end: the routine byte is known not to be the side pipe's, or the height is the reference's -/
def finY (S : HP) (B : AS) : Bool := notV S.ev (B.getK S.rtI) || isV S.yv (B.getK S.yI)

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def walkY (S : HP) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preY S (clampS C.P A)).all fun A₁ => (stepY C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkY S C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-! ## Finding the table: a search, no part of the proof -/

/-- 64 bits that depend on every bit of a number: a hash table reads only the low 64 bits of a key -/
def mix64 (n : Nat) : Nat :=
  let rec go : Nat → Nat → UInt64 → UInt64
    | 0, _, h => h
    | f + 1, n, h =>
      if n == 0 then h else
      let h := (h ^^^ (n % 18446744073709551616).toUInt64) * 0x9E3779B97F4A7C15
      go f (n >>> 64) (h ^^^ (h >>> 32))
  (go 16 n 0xCBF29CE484222325).toNat

/-- the key: that of the room's search, the height, the player's state and the pointer of the read; and below them 64 mixed bits -/
def keyY (S : HP) (Z : Aids) (E : Env) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let K := Z.key E A + ((((num (A.getK S.yI)) * 65536 + num (A.getK S.P.stI)) * 65536 + num (A.getK S.ptrI)) * 65536 + num (A.getK (S.ptrI + 1))) * (1 <<< 300)
  K * 18446744073709551616 + mix64 K

/-- what a state forgets: what the room's search forgets; at the return of the collision routine the height and the low bits of the player's state, unless the
routine is the side pipe's; at the start of the side check the height, unless it is known; after the save of a tile the pointer of the read -/
def normY (S : HP) (Z : Aids) (A : AS) : AS :=
  let B := Z.norm A
  if A.pc == Z.colEnd && !isV S.ev (B.getK S.rtI) then
    (B.setK S.yI AB.top).setK S.P.stI ⟨(B.getK S.P.stI).v &&& 0xFC, (B.getK S.P.stI).k &&& 0xFC⟩
  else if A.pc == S.sideAt && !(B.getK S.yI).isK then B.setK S.yI AB.top
  else if A.pc == S.tileAt then (B.setK S.ptrI AB.top).setK (S.ptrI + 1) AB.top
  else B

/-- what a search uses to find a table: the key of a state, what a state forgets, the places where it stops a run of single steps, the places where it forgets
(with those of the room's search). No part of the proof: the walk checks the table that the search finds. -/
structure Opts where
  key : AS → Nat
  norm : AS → AS
  stops : List UInt16
  normAt : List UInt16

/-- the search of the height's walk -/
def optsY (S : HP) (Z : Aids) (E : Env) : Opts :=
  { key := keyY S Z E, norm := normY S Z, stops := [S.footAt, S.landAt, S.colAt, S.tileAt], normAt := [S.tileAt] }

/-- the waiting states go in the order of their first dot; the key is whole, so that two states with different keys do not take the same place -/
def putY (X : SearchS) (K : Nat) (B : AS) : SearchS :=
  let q := B.lo * (1 <<< 512) + (K % (1 <<< 512))
  let pend := match X.pendKey[K]? with
    | some r => X.pending.erase r
    | none => X.pending
  { X with pending := pend.insert q B, pendKey := X.pendKey.insert K q }

def routeY (P : Places) (O : Opts) (X : SearchS) (B0 : AS) : SearchS :=
  let B := clampS P (O.norm B0)
  let K := O.key B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D =>
    if B.le D then X else
    let J := D.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 then { J with hi := P.late } else J
    putY { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => putY { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

partial def runY (S : HP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preY S (clampS S.P cur)).flatMap (stepY S.P E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !fin B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (O.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          !O.stops.contains b.pc && (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeY S.P O X b
    break
  return X

partial def searchY (S : HP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := O.key A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runY S Z O fin E ops X A
  return X

def searchOf (S : HP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchY S Z O fin E ops ((startsR r K).foldl (routeY S.P O) {})

/-- the configuration from the table found -/
def cfgOf (S : HP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOf S Z O fin E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  -- the accumulator is taken apart first, so that each part is updated in place (projections of a shared tuple copy the array at each push; round 26)
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      match acc with
      | (arr, hm, ba) =>
        let i := arr.size
        let l := hm.getD e.1 []
        (arr.push e.2, hm.insert e.1 (i :: l), ba.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ O.normAt).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P := S.P, fin, t := q.1, key := O.key, idx := q.2.1, cut := q.2.2, norm := O.norm, normAt := at0 }

/-- **The check of a walk**, with the condition `fin` on the frame's end -/
def walkCheckY (S : HP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOf S Z O fin E r K
  ScreenPage.placesOK E S.P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K &&
    decide (S.rtI < 2048) && decide (S.yI < 2048) && decide (S.tileI < 2048) &&
    C.t.all (walkY S C ScreenPage.fuelS) && (startsR r K).all (walkY S C ScreenPage.fuelS)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem cov_top2 {d : Nat} (hd : d < 2048) : Cov E F (top2 d) := by
  intro A m hs
  unfold top2
  split
  · exact PipeWrites.cov_then (cov_bit hd (by decide)) (cov_bit hd (by decide)) A m hs
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_top1 {d : Nat} (hd : d < 2048) : Cov E F (top1 d) := by
  intro A m hs
  unfold top1
  split
  · exact PipeWrites.cov_then (cov_bit hd (by decide)) (cov_top2 hd) A m hs
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- the split of the height's high bits covers every machine -/
theorem cov_topY {d : Nat} (hd : d < 2048) : Cov E F (topY d) :=
  PipeWrites.cov_then (cov_bit hd (by decide)) (cov_top1 hd)

/-- the split of the accumulator's low bits covers every machine -/
theorem cov_lowA : Cov E F lowA := by
  have c1 : Cov E F (PipeChangeEnd.bitA 16) := PipeChangeEnd.cov_bitA (by decide)
  have c2 : Cov E F (PipeChangeEnd.bitA 8) := PipeChangeEnd.cov_bitA (by decide)
  have c3 : Cov E F (PipeChangeEnd.bitA 4) := PipeChangeEnd.cov_bitA (by decide)
  have c4 : Cov E F (PipeChangeEnd.bitA 2) := PipeChangeEnd.cov_bitA (by decide)
  have c5 : Cov E F (PipeChangeEnd.bitA 1) := PipeChangeEnd.cov_bitA (by decide)
  exact PipeWrites.cov_then c1 (PipeWrites.cov_then c2 (PipeWrites.cov_then c3 (PipeWrites.cov_then c4 c5)))

/-- the pieces of the height's walk cover every machine: no hypothesis on the machine -/
theorem cov_zoneY {S : HP} (hy : S.yI < 2048) (ht : S.tileI < 2048) : Cov E F (zoneY S) := by
  intro A m hs
  unfold zoneY
  by_cases h1 : (A.pc == S.footAt) = true
  · rw [if_pos h1]
    exact cov_topY hy A m hs
  rw [if_neg h1]
  by_cases h2 : (A.pc == S.landAt) = true
  · rw [if_pos h2]
    exact PipeEntryRule.cov_all hy A m hs
  rw [if_neg h2]
  by_cases h3 : (A.pc == S.colAt && (A.getK S.yI).isK) = true
  · rw [if_pos h3]
    exact cov_lowA A m hs
  rw [if_neg h3]
  by_cases h4 : (A.pc == S.tileAt) = true
  · rw [if_pos h4]
    exact PipeEntryRule.cov_all ht A m hs
  rw [if_neg h4]
  exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_preY {S : HP} (hO : PlacesOK E S.P) (hy : S.yI < 2048) (ht : S.tileI < 2048) {A : AS} {m : Machine}
    (hs : Sim E F A m) (hh : SiteOK S.P m) : ∃ B ∈ preY S A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, k1⟩ := ScreenPage.cov_preS hO hs hh
  obtain ⟨D, hD, h2, k2⟩ := cov_zoneY hy ht B m h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h2, k2.trans k1⟩

/-- **One step of the height's walk**: the machine's own step is sound at any place, and `RoomMap`'s under `SiteOK` -/
theorem s_stepY {P : Places} {ops : Array (AM Unit)} (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hs : Sim E F A m) (hh : SiteOK P m) :
    ∃ r ∈ stepY P E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold stepY
  split
  · exact s_succs hops hT hs
  · exact RoomMap.s_stepT hO hops hT hs hh

end

/-! ## The walk covers the machine -/

section
variable {S : HP} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveY (S : HP) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkY S C n A = true

theorem cover_liveY (ht : C.t.all (walkY S C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ D, LiveY S C F D m ∧ D.k = B.k := by
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

/-- **One step of the walk**, as `ScreenPage.live_stepS`: the next machine is covered by a live state in the same frame, or the frame ends in a state that `fin` accepts -/
theorem live_stepY (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (ht : C.t.all (walkY S C Fu) = true)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveY S C F A m)
    (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) :
    (∃ A', LiveY S C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkY] at hw
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    have hhS : SiteOK S.P m := by rw [← hP]; exact hh
    have hOS : PlacesOK C.E S.P := by rw [← hP]; exact hO
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preY hOS hy htl hs0 hhS
    obtain ⟨r, hr, hB⟩ := s_stepY hO hops hT hs1 hh
    simp only [walkY, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    have hkA : A₁.k = A.k := by rw [hk1, ScreenPage.clamp_k]
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hkA] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        have hN : Sim C.E F (weaken C B) (go step m).2 ∧ (weaken C B).k = B.k := by
          unfold weaken
          split
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            have h5 := sim_le hc.2 h1
            refine ⟨h5, ?_⟩
            have hle := hc.2
            simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
            exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
          · exact ⟨h1, rfl⟩
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveY ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h3
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `A₀` that succeeds covers the frame of every machine of `A₀`, for every input, if each instruction meets `SiteOK`. -/
theorem frame_of_walkY (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (ht : C.t.all (walkY S C Fu) = true)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {A₀ : AS} {m : Machine} {i : UInt8} (hw : walkY S C Fu A₀ = true) (hs : Sim C.E F A₀ m) (hk : ∀ j, SiteOK C.P (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F A₀ { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveY S C F A (trace m i j) ∧ A.k = A₀.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨A₀, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hk (j + 1)
        rw [e2] at hh2 ⊢
        rcases live_stepY hO hP hy htl ht hops hT h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3, h4⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h3, h4⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact ⟨h1, B, h2, h3, h4⟩

end

/-! ## The frame -/

/-- what the check says -/
structure WalkOK (S : HP) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) : Prop where
  places : PlacesOK E S.P
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  pl : C.P = S.P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = fin
  rt : S.rtI < 2048
  yI : S.yI < 2048
  tileI : S.tileI < 2048
  table : C.t.all (walkY S C ScreenPage.fuelS) = true
  starts : ∀ A ∈ startsR r K, walkY S C ScreenPage.fuelS A = true

theorem walkOK_of_check {S : HP} {Z : Aids} {O : Opts} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)}
    (h : walkCheckY S Z O fin E r K = true) : WalkOK S fin E r K (cfgOf S Z O fin E r K) := by
  simp only [walkCheckY, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, rfl, h4, h5, h6, h7, h8⟩

/-- **The end of a frame of the room.** A frame that starts in the room's condition with the bits `K`, with `SiteOK` on each instruction, ends in a machine that a
state accepted by `fin` covers. -/
theorem frame_end {S : HP} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOK S fin E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j)) : ∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  obtain ⟨_, B, h2, _, h4⟩ := frame_of_walkY (i := i) hO h.pl h.yI h.tileI h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) hw hs'
    (by rw [h.pl]; exact hk)
  rw [h.fin] at h2
  rw [h.env] at h4
  exact ⟨B, h2, h4⟩

/-- **The height at the end of the entering frame.** A frame that starts in the room's condition (with the bits `K`: the map's bits and the player's size), with `SiteOK`
on each instruction: if it ends with the side pipe's routine, it ends with the reference's height. -/
theorem height_frame {S : HP} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOK S (finY S) E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j)) (hrt : (frame m i).ram.get! S.rtI = S.ev) :
    (frame m i).ram.get! S.yI = S.yv := by
  obtain ⟨B, h2, h4⟩ := frame_end h hm hk
  simp only [finY, Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd hrt (ne_of_notV h2 (h4.ram _ h.rt))
  · simp only [isV, Bool.and_eq_true, beq_iff_eq] at h2
    rw [PipeEntryRule.known_eq h2.1 (h4.ram _ h.yI), h2.2]

/-! ## On the ROM -/

section
open ScreenPage (placesR envR refR aidsOf)
open PipeEntryRule (findOp)

/-- the player's size, as a RAM index -/
def sizeI (sy : Syms) : Nat := (sy.PlayerSize &&& 0x7FF).toNat

/-- the height, as a RAM index -/
def heightI (sy : Syms) : Nat := (sy.Player_Y_Position &&& 0x7FF).toNat

/-- the places, from the symbols and the ROM. The routine of the block buffer's address is the target of the first `JSR` of the block buffer routine. -/
def hpOf (sy : Syms) (nm : Names) (m0 : Machine) : HP :=
  let read := findOp m0 sy.BlockBufferCollision 0xB1 64
  let jsr := findOp m0 sy.BlockBufferCollision 0x20 64
  { P := placesR sy nm m0
    rtI := (sy.GameEngineSubroutine &&& 0x7FF).toNat
    ev := SideEntryRule.vs sy
    yI := heightI sy
    yv := (SideTransition.entry m0).ram.get! (heightI sy)
    footAt := ScreenPage.findOpZ m0 sy.DoFootCheck 0xA5 sy.Player_Y_Position.toUInt8 16
    landAt := ScreenPage.findJsr m0 sy.DoFootCheck sy.HandlePipeEntry 160
    colAt := (romByte m0 (jsr + 1)).toUInt16 ||| ((romByte m0 (jsr + 2)).toUInt16 <<< 8)
    tileI := (romByte m0 (read + 3)).toNat
    tileAt := read + 4
    ptrI := (romByte m0 (read + 1)).toNat
    sideAt := sy.DoPlayerSideCheck }

/-- what the search forgets and keeps apart: as the room's search, but the offset of the collision routine's adders is not forgotten -/
def aidsY (sy : Syms) (nm : Names) (m0 : Machine) : Aids :=
  let Z := aidsOf sy nm m0
  let side := (romByte m0 (sy.DoFootCheck + 1)).toNat
  { Z with temps := Z.temps.filter (· != side) }

/-- the known bits: those of `RoomMap`, and the player's size -/
def knownY (sy : Syms) (nm : Names) (m0 : Machine) : List (Nat × UInt8) := RoomMap.knownT sy nm m0 ++ [(sizeI sy, 0xFF)]

/-- **The check on the ROM.** -/
def heightCheck (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  walkCheckY (hpOf sy nm m0) (aidsY sy nm m0) (optsY (hpOf sy nm m0) (aidsY sy nm m0) (envR sy nm m0)) (finY (hpOf sy nm m0)) (envR sy nm m0) (refR m0) (knownY sy nm m0)

/-- each reference `V` of the entry that lists the height has the height of the reference entry -/
def refsCheck (sy : Syms) (m0 : Machine) (V : List (Machine × List Nat)) : Bool :=
  V.all fun v => !v.2.contains (heightI sy) || v.1.ram.get! (heightI sy) == (SideTransition.entry m0).ram.get! (heightI sy)

/-- what the checks give -/
structure Facts (sy : Syms) (nm : Names) (m0 : Machine) (V : List (Machine × List Nat)) : Prop where
  walk : heightCheck sy nm m0 = true
  refs : ∀ v ∈ V, heightI sy ∈ v.2 → v.1.ram.get! (heightI sy) = (SideTransition.entry m0).ram.get! (heightI sy)

theorem factsOf {sy : Syms} {nm : Names} {m0 : Machine} {V : List (Machine × List Nat)} (h1 : heightCheck sy nm m0 = true) (h2 : refsCheck sy m0 V = true) :
    Facts sy nm m0 V := by
  refine ⟨h1, fun v hv hi => ?_⟩
  simp only [refsCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h2
  rcases h2 v hv with h | h
  · rw [List.contains_iff_mem.2 hi] at h
    cases h
  · exact h

end

/-! ## The entering frame of the room -/

section
open ScreenPage (placesR envR refR)
open PipeChangeEnd (Data InRowsT)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **The height at the end of the entering frame, on the real machines.** A frame `k` of the room (from `b` to `a`, under the conditions of `RoomMap.map_of_rows`) that
starts with the player's size of the reference and ends with the side pipe's routine ends with the height of the reference entry. `RoomMap.cond_of_rows` gives the room's
condition with the map's bits at the frame's start. `hF`, `hc`, `hH` are checks on the ROM. -/
theorem height_of_rows (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hH : heightCheck sy nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    {k : Nat} (h1 : b ≤ k) (h2 : k < a)
    (hsz : (seq k).ram.get! (sizeI sy) = (refR m0).ram.get! (sizeI sy))
    (hrt : (frame (seq k) (inp k)).ram.get! (placesR sy nmS m0).rtI = (placesR sy nmS m0).eng) :
    (frame (seq k) (inp k)).ram.get! (heightI sy) = (SideTransition.entry m0).ram.get! (heightI sy) := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay k h1 h2
  have hY : RoomCond (envR sy nmS m0) (refR m0) (knownY sy nmS m0) (seq k) :=
    RoomMusic.roomCond_append hcond (fun p hp => by
      have e1 : p = (sizeI sy, (0xFF : UInt8)) := List.mem_singleton.1 hp
      rw [e1]
      show (seq k).ram.get! (sizeI sy) &&& 0xFF = (refR m0).ram.get! (sizeI sy) &&& 0xFF
      rw [hsz])
  exact height_frame (S := hpOf sy nmS m0) (walkOK_of_check hH) hY (sites k h1 h2) hrt

end

end Smbrta.EntryHeight
