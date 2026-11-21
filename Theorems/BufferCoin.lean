import Theorems.BufferControl

/-!
# A frame that starts with the control at 6 left of the mouth does not enter

`Route.Run.buffer₂` asks that the frame that enters the side pipe does not start with the control of the screen's buffers at 6 (the value after a frame that erased
a coin). Here half of it: a frame of the room that starts with the control at 6, on page 0, with the position `x` in `[lo, hi)`, comes to the end of the move
(`PlayerSubs`) only left of the mouth's left end. So `SideFrame.entry_right_of_left` (the walk of one whole frame, `side_frame_check`) says that it does not enter.

The move adds the speed's high four bits (sign extended) and a carry to the position, so it moves the position by at most 8 px for every value of the speed byte.
The abstract machine adds bytes with all their bits known or none. So at this add the walk splits the accumulator (the position), the added byte and the carry
into their values (`zoneM`): at the end of the move the position is known, and it is at most 8 px right of its piece at the frame's start. Every state at the end of
the move must be one of the table (`walkG`), and the check asks of each of them that it is left of the mouth (`posLeft`). At the start of the scroll handler the
search forgets the position again.

There is no game data in this file. Page: `1-1/d-2-5-5-2-BufferCoin.md`.
-/

namespace Smbrta.BufferCoin

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace trace_stop nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids SearchS clampS preS weaken coverS startsR RoomCond MaskOK placesR envR refR aidsOf)
open EntryHeight (HP Opts preY stepY mix64 putY routeY)

/-! ## The pieces of the move -/

/-- the flag bit `b` (the carry for `b = 1`), in its two values if it is not known -/
def bitP (b : UInt8) (A : AS) : List AS :=
  match A.p.bit b with
  | some _ => [A]
  | none => [{ A with p := A.p.or (AB.known b) }, { A with p := A.p.and (AB.known (~~~b)) }]

/-- the places of the walk: the add of the move, the position and its page, the end of the move, the start of the scroll handler, the mouth's left end -/
structure MP where
  /-- the start of the move routine, the add of the speed's high bits to the position, and the byte it adds -/
  moveAt : UInt16
  /-- the compare of the speed's high bits with 8, and the compare of the added byte with 0 (the sign of the move) -/
  cmpAt : UInt16
  cmp0At : UInt16
  addAt : UInt16
  tI : Nat
  /-- the add of the climbing routine's table to the position -/
  climbAt : UInt16
  /-- the position on the page, and the page -/
  xI : Nat
  pI : Nat
  /-- the end of the move (`PlayerSubs`), and the start of the scroll handler that it calls -/
  subs : UInt16
  scrollAt : UInt16
  /-- the mouth's left end -/
  left : Nat
  deriving Inhabited

/-- at the compare of the speed's high bits with 8, bit 3 of the accumulator; at the compare of the added byte with 0, the accumulator in its values (the
abstract compare subtracts with all bits known or none); at the add of the climbing routine, the accumulator in its values; at the move's add, with the index register known to be 0 (the player): the
carry, the added byte and the accumulator, each in its values -/
def zoneM (M : MP) (A : AS) : List AS :=
  if A.pc == M.cmpAt && A.x.isK && A.x.v == 0 then PipeChangeEnd.bitA 8 A
  else if A.pc == M.cmp0At && A.x.isK && A.x.v == 0 then PipeChangeEnd.allBits PipeChangeEnd.bitA A
  else if A.pc == M.addAt && A.x.isK && A.x.v == 0 then
    ((bitP 1 A).flatMap (SideFrame.fillB M.tI)).flatMap (PipeChangeEnd.allBits PipeChangeEnd.bitA)
  else if A.pc == M.climbAt then PipeChangeEnd.allBits PipeChangeEnd.bitA A
  else [A]

/-- the pieces before a step: those of the room's walk, then those of the move -/
def preZ (S : HP) (M : MP) (A : AS) : List AS := (preY S A).flatMap (zoneM M)

/-- the walk of `EntryHeight` with the pieces of the move; a state at the end of the move must be one of the table -/
def walkG (S : HP) (M : MP) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preZ S M (clampS C.P A)).all fun A₁ => (stepY C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then
        if (weaken C B).pc == M.subs then C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))
        else (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkG S M C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-- the known value of a byte, if it is known -/
def kv (B : AS) (i : Nat) : Option UInt8 := if (B.getK i).isK then some (B.getK i).v else none

/-- left of the mouth: the page known to be 0, and every value of the position's piece left of `left` -/
def posLeft (M : MP) (B : AS) : Bool :=
  kv B M.pI == some 0 && (List.range 256).all fun n => !SideFrame.memB (B.getK M.xI) n.toUInt8 || decide (n < M.left)

/-! ## The search: no part of the proof -/

/-- the key: that of the buffer's walk (the room's and the control), the position and the page, and in the move routine up to the store of the sum, and at the
store of the climbing routine's sum, the byte added and the accumulator (so that the pieces made there are not joined) -/
def keyG (Z : Aids) (E : Env) (c : Nat) (M : MP) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let t := if (M.moveAt ≤ A.pc && A.pc ≤ M.addAt + 2) || A.pc == M.climbAt + 3 then num (A.getK M.tI) * 65536 + num A.a else 0
  let K := (Z.key E A * (1 <<< 32) + t) * (1 <<< 48) + (num (A.getK c) * 65536 + num (A.getK M.xI)) * 65536 + num (A.getK M.pI)
  K * 18446744073709551616 + mix64 K

/-- what a state forgets: what the room's search forgets, and at the start of the scroll handler the position -/
def normG (Z : Aids) (M : MP) (A : AS) : AS :=
  let B := Z.norm A
  if A.pc == M.scrollAt then B.setK M.xI AB.top else B

def optsG (Z : Aids) (E : Env) (c : Nat) (M : MP) : Opts :=
  { key := keyG Z E c M, norm := normG Z M, stops := [M.addAt, M.subs, M.addAt + 10], normAt := [M.scrollAt] }

partial def runG (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preZ S M (clampS S.P cur)).flatMap (stepY S.P E ops)
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

partial def searchG (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := O.key A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runG S M Z O fin E ops X A
  return X

def searchOfG (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchG S M Z O fin E ops ((startsR r K).foldl (routeY S.P O) {})

/-- the configuration from the table found; the table has every state at the end of the move -/
def cfgOfG (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOfG S M Z O fin E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2 || q.2.pc == M.subs
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ O.normAt).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P := S.P, fin, t := q.1, key := O.key, idx := q.2.1, cut := q.2.2, norm := O.norm, normAt := at0 }

/-- **The check of the walk**: the walk with the pieces of the move from the start states passes, every frame end meets `fin`, and every state of the table at the
end of the move is left of the mouth -/
def walkCheckG (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOfG S M Z O fin E r K
  ScreenPage.placesOK E S.P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K &&
    decide (S.yI < 2048) && decide (S.tileI < 2048) && decide (M.tI < 2048) && decide (M.xI < 2048) && decide (M.pI < 2048) &&
    C.t.all (fun D => D.pc != M.subs || posLeft M D) && (startsR r K).all (fun A => A.pc != M.subs) &&
    C.t.all (walkG S M C ScreenPage.fuelS) && (startsR r K).all (walkG S M C ScreenPage.fuelS)

/-- the search from the start states of several references with their known bits, into one table (round 25: one search for all pieces) -/
def searchOfG2 (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (rs : List (Machine × List (Nat × UInt8))) : SearchS :=
  let ops := (aRows E).toArray
  searchG S M Z O fin E ops ((rs.flatMap fun p => startsR p.1 p.2).foldl (routeY S.P O) {})

/-- the configuration from the one table -/
def cfgOfG2 (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (rs : List (Machine × List (Nat × UInt8))) : CfgS :=
  let X := searchOfG2 S M Z O fin E rs
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2 || q.2.pc == M.subs
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ O.normAt).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P := S.P, fin, t := q.1, key := O.key, idx := q.2.1, cut := q.2.2, norm := O.norm, normAt := at0 }

/-- **The check of the walks from several references with one table** -/
def walkCheckG2 (S : HP) (M : MP) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (rs : List (Machine × List (Nat × UInt8))) : Bool :=
  let C := cfgOfG2 S M Z O fin E rs
  ScreenPage.placesOK E S.P && E.pad.v == 0 && E.pad.k == 0 &&
    decide (S.yI < 2048) && decide (S.tileI < 2048) && decide (M.tI < 2048) && decide (M.xI < 2048) && decide (M.pI < 2048) &&
    C.t.all (fun D => D.pc != M.subs || posLeft M D) && C.t.all (walkG S M C ScreenPage.fuelS) &&
    rs.all fun p => ScreenPage.maskOK p.1 p.2 && (startsR p.1 p.2).all (fun A => A.pc != M.subs) && (startsR p.1 p.2).all (walkG S M C ScreenPage.fuelS)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem cov_bitP {b : UInt8} (hb : b ∈ bitList) : Cov E F (bitP b) := by
  intro A m hs
  unfold bitP
  cases e : A.p.bit b with
  | some _ => exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | none =>
    obtain ⟨j, hj⟩ := bit_of_list b hb
    have hbb : ∀ i, i < 8 → bt b i = decide (i = j.1) := fun i hi => hj ⟨i, hi⟩
    by_cases hx : m.p &&& b = 0
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), { hs with p := ?_ }, rfl⟩
      have := mem_and hs.p (mem_known_self (~~~b))
      rwa [and_not_self_of hx] at this
    · refine ⟨_, List.mem_cons_self, { hs with p := ?_ }, rfl⟩
      have := mem_or hs.p (mem_known_self b)
      rwa [or_self_of hbb (bit_of_ne hbb hx)] at this

theorem cov_allA : Cov E F (PipeChangeEnd.allBits PipeChangeEnd.bitA) :=
  PipeChangeEnd.cov_allBits fun _ hb => PipeChangeEnd.cov_bitA hb

/-- the pieces of the move cover every machine -/
theorem cov_zoneM {M : MP} (ht : M.tI < 2048) : Cov E F (zoneM M) := by
  intro A m hs
  unfold zoneM
  by_cases h1 : (A.pc == M.cmpAt && A.x.isK && A.x.v == 0) = true
  · rw [if_pos h1]
    exact PipeChangeEnd.cov_bitA (by decide) A m hs
  rw [if_neg h1]
  by_cases h2 : (A.pc == M.cmp0At && A.x.isK && A.x.v == 0) = true
  · rw [if_pos h2]
    exact cov_allA A m hs
  rw [if_neg h2]
  by_cases h3 : (A.pc == M.addAt && A.x.isK && A.x.v == 0) = true
  · rw [if_pos h3]
    exact PipeWrites.cov_then (PipeWrites.cov_then (cov_bitP (by decide)) (SideFrame.cov_fill ht)) cov_allA A m hs
  rw [if_neg h3]
  by_cases h4 : (A.pc == M.climbAt) = true
  · rw [if_pos h4]
    exact cov_allA A m hs
  rw [if_neg h4]
  exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_preZ {S : HP} {M : MP} (hO : PlacesOK E S.P) (hy : S.yI < 2048) (ht : S.tileI < 2048) (htM : M.tI < 2048) {A : AS} {m : Machine}
    (hs : Sim E F A m) (hh : SiteOK S.P m) : ∃ B ∈ preZ S M A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, k1⟩ := EntryHeight.cov_preY hO hy ht hs hh
  obtain ⟨D, hD, h2, k2⟩ := cov_zoneM htM B m h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h2, k2.trans k1⟩

end

/-! ## The walk covers the machine -/

section
variable {S : HP} {M : MP} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveG (S : HP) (M : MP) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkG S M C n A = true

/-- a state of the table -/
def InTab (C : CfgS) (A : AS) : Prop := ∃ i : Nat, C.t[i]? = some A

theorem cover_liveG (ht : C.t.all (walkG S M C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ D, LiveG S M C F D m ∧ D.k = B.k ∧ InTab C D := by
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
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk, i, e⟩
  · cases h2

/-- **One step of the walk**: the next machine is covered by a live state in the same frame, a state of the table if it is at the end of the move; or the frame
ends -/
theorem live_stepG (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (htM : M.tI < 2048) (ht : C.t.all (walkG S M C Fu) = true)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveG S M C F A m)
    (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) :
    (∃ A', LiveG S M C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧
      ((go step m).2.pc = M.subs → InTab C A')) ∨
    (go step m).2.frame = m.frame + 1 := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkG] at hw
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    have hhS : SiteOK S.P m := by rw [← hP]; exact hh
    have hOS : PlacesOK C.E S.P := by rw [← hP]; exact hO
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preZ hOS hy htl htM hs0 hhS
    obtain ⟨r, hr, hB⟩ := EntryHeight.s_stepY hO hops hT hs1 hh
    simp only [walkG, List.all_eq_true] at hw
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
        have hpc : (go step m).2.pc = (weaken C B).pc := hN.1.pc
        by_cases hq : ((weaken C B).pc == M.subs) = true
        · rw [if_pos hq] at hw2
          simp only [Bool.and_eq_true] at hw2
          obtain ⟨D, hD, hk, hT'⟩ := cover_liveG ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) hw2.2
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3, fun _ => hT'⟩
        · rw [if_neg hq] at hw2
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
          have hne : (go step m).2.pc ≠ M.subs := by
            intro e
            apply hq
            rw [← hpc, e]
            simp
          rcases hw2 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD, hk, _⟩ := cover_liveG ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h3
            exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3, fun e => absurd e hne⟩
          · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3, fun e => absurd e hne⟩
      · right
        exact k2

/-- **The frame up to its end.** A walk from `A₀` that succeeds, from a state not at the end of the move: every machine of the frame of a machine of `A₀`, before
the frame's end, at the end of the move, is covered by a state of the table, if each instruction meets `SiteOK`. -/
theorem subs_of_walkG (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (htM : M.tI < 2048) (ht : C.t.all (walkG S M C Fu) = true)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {A₀ : AS} {m : Machine} {i : UInt8} (hw : walkG S M C Fu A₀ = true) (hs : Sim C.E F A₀ m) (h0 : A₀.pc ≠ M.subs) (hk : ∀ j, SiteOK C.P (trace m i j)) :
    ∀ j, (trace m i j).frame ≤ m.frame → (trace m i j).pc = M.subs → ∃ D, InTab C D ∧ Sim C.E F D (trace m i j) := by
  have hs0 : Sim C.E F A₀ { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveG S M C F A (trace m i j) ∧ (trace m i j).frame = m.frame ∧ ((trace m i j).pc = M.subs → InTab C A)) ∨
      (trace m i j).frame = m.frame + 1 := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨A₀, ⟨hs0, Fu, hw⟩, rfl, fun e => absurd (hs0.pc.symm.trans e) h0⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h3, _⟩ | h1
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hk (j + 1)
        rw [e2] at hh2 ⊢
        rcases live_stepG hO hP hy htl htM ht hops hT h1 (hk j) hh2 with ⟨A', a1, _, a3, _, a5⟩ | a1
        · exact Or.inl ⟨A', a1, by rw [a3, h3], a5⟩
        · exact Or.inr (by rw [a1, h3])
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr h1
  intro j hf hq
  rcases key j with ⟨A, h1, _, h3⟩ | h1
  · exact ⟨A, h3 hq, h1.1⟩
  · omega

end

/-! ## The frame -/

/-- what the check says -/
structure WalkOKG (S : HP) (M : MP) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) : Prop where
  places : PlacesOK E S.P
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  pl : C.P = S.P
  ops : C.ops = (aRows C.E).toArray
  yI : S.yI < 2048
  tileI : S.tileI < 2048
  tI : M.tI < 2048
  xI : M.xI < 2048
  pI : M.pI < 2048
  left : ∀ D ∈ C.t, D.pc = M.subs → posLeft M D = true
  start : ∀ A ∈ startsR r K, A.pc ≠ M.subs
  table : C.t.all (walkG S M C ScreenPage.fuelS) = true
  starts : ∀ A ∈ startsR r K, walkG S M C ScreenPage.fuelS A = true

theorem walkOKG_of_check {S : HP} {M : MP} {Z : Aids} {O : Opts} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)}
    (h : walkCheckG S M Z O fin E r K = true) : WalkOKG S M E r K (cfgOfG S M Z O fin E r K) := by
  simp only [walkCheckG, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  refine ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, h4, h5, h6, h7, h8, ?_, ?_, h11, h12⟩
  · intro D hD hq
    have := Array.all_eq_true_iff_forall_mem.1 h9 D hD
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with h | h
    · exact absurd hq h
    · exact h
  · intro A hA hq
    have := h10 A hA
    simp only [bne_iff_ne, ne_eq] at this
    exact this hq

/-- what the check of several references says, for each of them -/
theorem walkOKG_of_check2 {S : HP} {M : MP} {Z : Aids} {O : Opts} {fin : AS → Bool} {E : Env} {rs : List (Machine × List (Nat × UInt8))}
    (h : walkCheckG2 S M Z O fin E rs = true) {r : Machine} {K : List (Nat × UInt8)} (hr : (r, K) ∈ rs) :
    WalkOKG S M E r K (cfgOfG2 S M Z O fin E rs) := by
  simp only [walkCheckG2, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  obtain ⟨⟨k1, k2⟩, k3⟩ := h11 (r, K) hr
  refine ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec k1, rfl, rfl, rfl, h4, h5, h6, h7, h8, ?_, ?_, h10, k3⟩
  · intro D hD hq
    have := Array.all_eq_true_iff_forall_mem.1 h9 D hD
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with h | h
    · exact absurd hq h
    · exact h
  · intro A hA hq
    have := k2 A hA
    simp only [bne_iff_ne, ne_eq] at this
    exact this hq

/-- the position of a machine of a state that `posLeft` accepts is left of the mouth -/
theorem left_of_posLeft {E : Env} {F : Nat × UInt8} {M : MP} {D : AS} {m : Machine} (hs : Sim E F D m) (hx : M.xI < 2048) (hp : M.pI < 2048)
    (h : posLeft M D = true) : 256 * (m.ram.get! M.pI).toNat + (m.ram.get! M.xI).toNat < M.left := by
  simp only [posLeft, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hk : (D.getK M.pI).isK = true ∧ (D.getK M.pI).v = 0 := by
    unfold kv at h1
    split at h1
    · rename_i hk
      simp only [beq_iff_eq, Option.some.injEq] at h1
      exact ⟨hk, h1⟩
    · simp at h1
  have e1 : m.ram.get! M.pI = 0 := by
    rw [PipeEntryRule.known_eq hk.1 (hs.ram _ hp), hk.2]
  have hm := hs.ram _ hx
  have h3 := h2 (m.ram.get! M.xI).toNat (m.ram.get! M.xI).toNat_lt
  have e3 : (m.ram.get! M.xI).toNat.toUInt8 = m.ram.get! M.xI := UInt8.ofNat_toNat
  rw [e3] at h3
  rcases h3 with h3 | h3
  · rw [SideFrame.memB_iff.2 hm] at h3
    cases h3
  · rw [e1]
    simpa using h3

/-- **At the end of the move, left of the mouth.** A frame that starts in the room's condition with the bits `K` of `r`, with `SiteOK` on each instruction, comes to
the end of the move, before the frame's end, only left of the mouth's left end -/
theorem subs_left {S : HP} {M : MP} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOKG S M E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j)) :
    ∀ j, (trace m i j).frame ≤ m.frame → (trace m i j).pc = M.subs →
      256 * ((trace m i j).ram.get! M.pI).toNat + ((trace m i j).ram.get! M.xI).toNat < M.left := by
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  intro j hf hq
  obtain ⟨D, ⟨n, hn⟩, hD⟩ := subs_of_walkG (i := i) hO h.pl h.yI h.tileI h.tI h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad)
    hw hs' (h.start S0 hS) (by rw [h.pl]; exact hk) j hf hq
  have hDm : D ∈ C.t := Array.mem_of_getElem? hn
  have hDq : D.pc = M.subs := by rw [← hD.pc]; exact hq
  have hD' : Sim E (m.frame, 2) D (trace m i j) := by rw [← h.env]; exact hD
  exact left_of_posLeft hD' h.xI h.pI (h.left D hDm hDq)

/-! ## The pieces of the start -/

/-- the values from `lo` before `hi`, as pieces whose known bits are a run of high bits: the aligned blocks -/
def rangePieces (lo hi : Nat) : List AB :=
  let rec go : Nat → Nat → List AB
    | 0, _ => []
    | f + 1, a =>
      if hi ≤ a then [] else
      let b := ((List.range 9).reverse.find? fun j => a % 2 ^ j == 0 && a + 2 ^ j ≤ hi).getD 0
      ⟨a.toUInt8, (256 - 2 ^ b : Nat).toUInt8⟩ :: go f (a + 2 ^ b)
  go 256 lo

/-- every value from `lo` before `hi` is in a piece -/
def rangeCover (lo hi : Nat) : Bool := (List.range 256).all fun n => !(decide (lo ≤ n) && decide (n < hi)) || (rangePieces lo hi).any fun a => SideFrame.memB a n.toUInt8

/-! ## On the ROM -/

/-- the places on the ROM: the compare is the first compare with an immediate byte in `MoveObjectHorizontally`, the add of the move is its second add of a byte
of the zero page (the first adds the speed's low bits to the fraction); the climbing routine is the fourth of the jump table at `MoveSubs`, and its add of the
table to the position its first add with an index; the scroll handler is the target of the call at `PlayerSubs` -/
def mpOf (sy : Syms) (m0 : Machine) : MP :=
  let a1 := PipeEntryRule.findOp m0 sy.MoveObjectHorizontally 0x65 64
  let a2 := PipeEntryRule.findOp m0 (a1 + 2) 0x65 64
  let climb := (romByte m0 (sy.MoveSubs + 9)).toUInt16 ||| ((romByte m0 (sy.MoveSubs + 10)).toUInt16 <<< 8)
  { moveAt := sy.MoveObjectHorizontally, climbAt := PipeEntryRule.findOp m0 climb 0x7D 64, cmpAt := PipeEntryRule.findOp m0 sy.MoveObjectHorizontally 0xC9 64,
    cmp0At := PipeEntryRule.findOp m0 (PipeEntryRule.findOp m0 sy.MoveObjectHorizontally 0xC9 64 + 2) 0xC9 64, addAt := a2, tI := (romByte m0 (a2 + 1)).toNat, xI := (sy.Player_X_Position &&& 0x7FF).toNat, pI := (sy.Player_PageLoc &&& 0x7FF).toNat,
    subs := sy.PlayerSubs, scrollAt := (romByte m0 (sy.PlayerSubs + 1)).toUInt16 ||| ((romByte m0 (sy.PlayerSubs + 2)).toUInt16 <<< 8),
    left := SidePipe.xLo sy }

/-- the reference with the control at 6, the page 0 and the position's piece `a` -/
def ref6x (nm : Names) (M : MP) (r : Machine) (a : AB) : Machine := { r with ram := ((r.ram.set! (EntryBuffer.ctlI nm) 6).set! M.pI 0).set! M.xI a.v }

/-- the known bits for the piece `a`: those of the buffer's walk (the room's and the control), the page and the piece's bits of the position -/
def knownG (sy : Syms) (nm : Names) (m0 : Machine) (M : MP) (a : AB) : List (Nat × UInt8) := EntryBuffer.knownB sy nm m0 ++ [(M.pI, 0xFF), (M.xI, a.k)]

/-- the reference and the known bits for the piece `a` -/
def startG (sy : Syms) (nm : Names) (m0 : Machine) (a : AB) : Machine × List (Nat × UInt8) :=
  (ref6x nm (mpOf sy m0) (refR m0) a, knownG sy nm m0 (mpOf sy m0) a)

/-- the walks for the pieces `as`, with one table (round 25; until round 24 one walk and one table for each piece) -/
abbrev walkAll (sy : Syms) (nm : Names) (m0 : Machine) (as : List AB) : Bool :=
  walkCheckG2 (EntryBuffer.hpB sy nm m0) (mpOf sy m0) (aidsOf sy nm m0) (optsG (aidsOf sy nm m0) (envR sy nm m0) (EntryBuffer.ctlI nm) (mpOf sy m0)) (fun _ => true)
    (envR sy nm m0) (as.map (startG sy nm m0))

/-- **The check on the ROM**: the pieces of `[16, 181)` cover it, the room's known bits list neither the position, nor the page, nor the control, these are three
different bytes, and the walks of all pieces pass with one table (`walkAll`; round 25: one search for all pieces, about half the time of seven) -/
def coinCheck (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let M := mpOf sy m0
  let c := EntryBuffer.ctlI nm
  rangeCover 16 181 && (RoomMap.knownT sy nm m0).all (fun p => p.1 != M.xI && p.1 != M.pI && p.1 != c) &&
    M.xI != M.pI && M.xI != c && M.pI != c && decide (c < 2048) && walkAll sy nm m0 (rangePieces 16 181)

/-! ## On real frames -/

/-- the room's condition for a piece: from the room's condition of `r`, with the control at 6, the page at 0 and the position in the piece `a` -/
theorem cond_piece {E : Env} {r m : Machine} {K : List (Nat × UInt8)} {c xI pI : Nat} {a : AB}
    (hm : RoomCond E r K m) (hK : ∀ q ∈ K, (¬q.1 = xI ∧ ¬q.1 = pI) ∧ ¬q.1 = c)
    (h1 : xI ≠ pI) (h2 : xI ≠ c) (h3 : pI ≠ c) (hc : c < r.ram.size) (hp : pI < r.ram.size) (hx : xI < r.ram.size)
    (e6 : m.ram.get! c = 6) (e0 : m.ram.get! pI = 0) (ex : a.mem (m.ram.get! xI)) :
    RoomCond E { r with ram := ((r.ram.set! c 6).set! pI 0).set! xI a.v } (K ++ [(c, 0xFF)] ++ [(pI, 0xFF), (xI, a.k)]) m := by
  have hsz1 : (r.ram.set! c 6).size = r.ram.size := PipeTransitionAll.ba_size_set _ _ _
  have hsz2 : ((r.ram.set! c 6).set! pI 0).size = r.ram.size := by rw [PipeTransitionAll.ba_size_set, hsz1]
  refine { hm with bytes := ?_ }
  intro q hq
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  show m.ram.get! q.1 &&& q.2 = (((r.ram.set! c 6).set! pI 0).set! xI a.v).get! q.1 &&& q.2
  rcases hq with (hq | hq) | hq | hq
  · obtain ⟨⟨n1, n2⟩, n3⟩ := hK q hq
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (Ne.symm n1), PipeTransitionAll.ba_get_set_ne _ _ _ _ (Ne.symm n2),
      PipeTransitionAll.ba_get_set_ne _ _ _ _ (Ne.symm n3)]
    exact hm.bytes q hq
  · subst hq
    show m.ram.get! c &&& 0xFF = (((r.ram.set! c 6).set! pI 0).set! xI a.v).get! c &&& 0xFF
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ h2, PipeTransitionAll.ba_get_set_ne _ _ _ _ h3,
      PipeTransitionAll.ba_get_set_self _ _ _ hc, e6]
  · subst hq
    show m.ram.get! pI &&& 0xFF = (((r.ram.set! c 6).set! pI 0).set! xI a.v).get! pI &&& 0xFF
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ h1, PipeTransitionAll.ba_get_set_self _ _ _ (by rw [hsz1]; exact hp), e0]
  · subst hq
    show m.ram.get! xI &&& a.k = (((r.ram.set! c 6).set! pI 0).set! xI a.v).get! xI &&& a.k
    rw [PipeTransitionAll.ba_get_set_self _ _ _ (by rw [hsz2]; exact hx)]
    exact ex

section
open PipeChangeEnd (Data InRowsT)
variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **A frame of the room that starts with the control at 6, on page 0, with the position from 16 before 181 px, does not enter.** Under the conditions of
`RoomMap.map_of_rows` on the frames from `b` before `a`: the walk of this file says that the frame comes to the end of the move only left of the mouth's left end, and
the walk of one whole frame (`SideFrame.entry_right_of_left`) says that a frame that enters comes there at or right of it. `hF`, `hc`, `hs`, `hC`, `hS` are checks on the
ROM. -/
theorem no_enter (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hs : RoomMap.startCheckF sy nmS m0 = true)
    (hC : coinCheck sy nmS m0 = true) (hS : SideFrame.sideFrameCheck sy m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    {k : Nat} (h1 : b ≤ k) (h2 : k < a) (hen : SideEntryRule.Enters sy (seq k) (inp k))
    (h6 : (seq k).ram.get! (EntryBuffer.ctlI nmS) = 6) (hp : (seq k).ram.get! (sy.Player_PageLoc &&& 0x7FF).toNat = 0)
    (hx1 : 16 ≤ ((seq k).ram.get! (sy.Player_X_Position &&& 0x7FF).toNat).toNat) (hx2 : ((seq k).ram.get! (sy.Player_X_Position &&& 0x7FF).toNat).toNat < 181) :
    False := by
  simp only [coinCheck, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨⟨⟨hcov, hK⟩, n1⟩, n2⟩, n3⟩, hcl⟩, hW⟩ := hC
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay k h1 h2
  -- the piece of the position
  obtain ⟨x, hxdef⟩ : ∃ x, (seq k).ram.get! (sy.Player_X_Position &&& 0x7FF).toNat = x := ⟨_, rfl⟩
  rw [hxdef] at hx1 hx2
  have hpc := List.all_eq_true.1 hcov x.toNat (List.mem_range.2 x.toNat_lt)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt] at hpc
  obtain ⟨a', ha', hma⟩ : ∃ a' ∈ rangePieces 16 181, SideFrame.memB a' x.toNat.toUInt8 = true := by
    rcases hpc with (hpc | hpc) | hpc
    · omega
    · omega
    · exact List.any_eq_true.1 hpc
  have e3 : x.toNat.toUInt8 = x := UInt8.ofNat_toNat
  rw [e3] at hma
  have hmem := SideFrame.memB_iff.1 hma
  rw [← hxdef] at hmem
  -- the walk for the piece
  have hw := walkOKG_of_check2 hW (r := ref6x nmS (mpOf sy m0) (refR m0) a') (K := knownG sy nmS m0 (mpOf sy m0) a') (List.mem_map.2 ⟨a', ha', rfl⟩)
  have hsz : (refR m0).ram.size = 2048 := by
    have := hw.mask.szR
    simp only [ref6x, PipeTransitionAll.ba_size_set] at this
    exact this
  have hcR := cond_piece (r := refR m0) (c := EntryBuffer.ctlI nmS) (xI := (mpOf sy m0).xI) (pI := (mpOf sy m0).pI) hcond hK n1 n2 n3
    (by rw [hsz]; exact hcl) (by rw [hsz]; exact hw.pI) (by rw [hsz]; exact hw.xI) h6 hp hmem
  have hleft := subs_left hw hcR (sites k h1 h2)
  -- the walk of one whole frame
  obtain ⟨n, j, hwj, hj, hq, hge⟩ := SideFrame.entry_right_of_left hS hen (RoomMap.start_of_rowsF hF hc hs next hin hctl sites stay k h1 h2)
    (fun _ _ j _ => ⟨RoomMap.clean_of_rows hF hc next hin hctl sites stay k h1 h2 j, (RoomMap.map_of_rows hF hc next hin hctl sites stay).2 k h1 h2 j,
      RoomMap.head_of_rows hF hc next hin hctl sites stay k h1 h2 j⟩)
  have hlt := hleft j (SideFrame.frame_before hwj j hj) hq
  have h7 : (SideEntryRule.spots sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (SideEntryRule.spots sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  have h9 : (mpOf sy m0).left = SidePipe.xLo sy := rfl
  have h10 : (mpOf sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h11 : (mpOf sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold PoleEntryRule.px at hge
  rw [h7, h8] at hge
  rw [h9, h10, h11] at hlt
  omega

end

/-- what the checks on the ROM give for the screen's first buffer at the side pipe's entry: those of `EntryBuffer` (the walk of the entering frame with the control
known, and the references' other bytes), those of the control through the room (`BufferControl.Facts`), the walks of this file, and the walk of one whole frame of
`SideFrame`. `Route.RoomChecks.buffer` asks it -/
structure FactsB (sy : Syms) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nmS : Names) (m0 : Machine) (V : List (Machine × List Nat)) (L : List Nat) : Prop
    extends EntryBuffer.Facts sy nmS m0 V L where
  ctl : BufferControl.Facts sy nm₁ d₁ nmS m0
  coin : coinCheck sy nmS m0 = true
  side : SideFrame.sideFrameCheck sy m0 = true

end Smbrta.BufferCoin
