import Theorems.RoomLate

/-!
# A split before the add of the block buffer's address

The room's walks (`RoomLate`, `LoopTime`) know, at the coin's erase (`STA (zp),Y`), the pointer's high byte (the block buffers' page), but not its low byte: the
routine that makes the address adds the column (the accumulator's low four bits, not known) to the low byte of the buffer's start (one of two, by `Y`, whose bit 0
is not known), and the abstract machine's `ADC` gives a result only when every bit of both values is known (`TaintRun.aadc`).

Here the walk splits the state before that add (`splitK`, at the program counter `pc0`): by each bit of the accumulator and of `Y` that is not known (`bitA`,
`bitY` of `PipeChangeEnd`), when there are at most six such bits. Each piece is a state of the machine's, so the split is sound (`cov_splitK`), and in each piece
the add is exact: the low byte of the pointer is known. The search keeps the states apart by the known bits that a function `kb` picks (`keyK`; on the ROM bit 7
of the pointer's low byte, which tells the two block buffers apart), and joins the rest: so in the table the pointer into the first block buffer is known to be
there.

`walkK`, `frame_of_walkK`, `walkCheckK`, `KOK`, `frameK` are `RoomLate`'s `walkST`, `frame_of_walkST`, `walkCheckST`, `STOK`, `frameST` with the split before each
step; `routeK`, `runK`, `searchK`, `searchBK`, `cfgBK` are its search (no part of the proof) with the split and the key.

There is no game data in this file. Page: `1-1/d-2-4-2-5-EraseSplit.md`.
-/

namespace Smbrta.EraseSplit

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken coverS startsR)
open RoomPause (Reg pstep Ph InCls)
open RoomLate (LateS sclamp sim_sclamp sclamp_k sclamp_spent)

/-! ## The split -/

/-- **The split**: at `pc0`, the accumulator and `Y` by each of their bits that is not known, if there are at most six such bits -/
def splitK (pc0 : UInt16) (A : AS) : List AS :=
  if A.pc == pc0 && decide (PipeChangeEnd.unkBits A.a + PipeChangeEnd.unkBits A.y ≤ 6) then
    (PipeChangeEnd.allBits PipeChangeEnd.bitA A).flatMap (PipeChangeEnd.allBits PipeChangeEnd.bitY)
  else [A]

theorem cov_splitK {E : Env} {F : Nat × UInt8} (pc0 : UInt16) : Cov E F (splitK pc0) := by
  intro A m hs
  unfold splitK
  split
  · exact cov_flat (PipeChangeEnd.cov_allBits (fun _ hb => PipeChangeEnd.cov_bitY hb))
      (PipeChangeEnd.cov_allBits (fun _ hb => PipeChangeEnd.cov_bitA hb) A m hs)
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- a split that changes only registers keeps the flag of the counter's fall -/
def SpentKeep (f : AS → List AS) : Prop := ∀ A, ∀ B ∈ f A, B.spent = A.spent

theorem spent_bitA (b : UInt8) : SpentKeep (PipeChangeEnd.bitA b) := by
  intro A B hB
  unfold PipeChangeEnd.bitA at hB
  split at hB
  · rw [List.mem_singleton.1 hB]
  · rcases List.mem_cons.1 hB with e | e
    · rw [e]
    · rw [List.mem_singleton.1 e]

theorem spent_bitY (b : UInt8) : SpentKeep (PipeChangeEnd.bitY b) := by
  intro A B hB
  unfold PipeChangeEnd.bitY at hB
  split at hB
  · rw [List.mem_singleton.1 hB]
  · rcases List.mem_cons.1 hB with e | e
    · rw [e]
    · rw [List.mem_singleton.1 e]

theorem spent_allBits {f : UInt8 → AS → List AS} (hf : ∀ b, SpentKeep (f b)) : SpentKeep (PipeChangeEnd.allBits f) := by
  intro A
  unfold PipeChangeEnd.allBits
  have key : ∀ (L : List UInt8) (l : List AS), (∀ C ∈ l, C.spent = A.spent) → ∀ B ∈ L.foldl (fun l b => l.flatMap (f b)) l, B.spent = A.spent := by
    intro L
    induction L with
    | nil => exact fun l h => h
    | cons b L ih =>
      intro l hl
      apply ih
      intro C hC
      obtain ⟨C0, h0, h1⟩ := List.mem_flatMap.1 hC
      rw [hf b C0 C h1]
      exact hl C0 h0
  exact key _ [A] (fun C hC => by rw [List.mem_singleton.1 hC])

theorem spent_splitK (pc0 : UInt16) : SpentKeep (splitK pc0) := by
  intro A B hB
  unfold splitK at hB
  split at hB
  · obtain ⟨C, h0, h1⟩ := List.mem_flatMap.1 hB
    rw [spent_allBits spent_bitY C B h1, spent_allBits spent_bitA A C h0]
  · rw [List.mem_singleton.1 hB]

/-! ## The walk with the split before each step -/

section
variable {G : Reg} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8} {sq : UInt16 → Bool} {D : Nat} {pc0 : UInt16}

/-- `RoomLate.walkST` with the split `splitK pc0` before each step -/
def walkK (pc0 : UInt16) (G : Reg) (C : CfgS) (chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => chk (sclamp sq D A) && ((splitK pc0 (sclamp sq D A)).flatMap (pstep C.P C.E C.ops G)).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (sclamp sq D (weaken C B))) || walkK pc0 G C chk sq D n (weaken C B)
      else B.k == A.k + 1 && C.fin B && chk B

/-- `A` covers `m` with `Ph`, and a walk from `A` succeeds -/
def LiveK (pc0 : UInt16) (G : Reg) (C : CfgS) (chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ Ph G A m ∧ ∃ n, walkK pc0 G C chk sq D n A = true

theorem chkK_of_walk {n : Nat} {A : AS} (h : walkK pc0 G C chk sq D n A = true) : chk (sclamp sq D A) = true := by
  cases n with
  | zero => simp [walkK] at h
  | succ n =>
    simp only [walkK, Bool.and_eq_true] at h
    exact h.1

theorem cover_liveK (ht : C.t.all (walkK pc0 G C chk sq D Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph G B m) (h : coverS C B = true) :
    ∃ D', LiveK pc0 G C chk sq D F D' m ∧ D'.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D' e
    have hle : B.le D' = true := h2
    have hk : D'.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D', ⟨sim_le hle hs, RoomPause.ph_of_spent (StepWrites.le_pc_spent hle).2 hp, Fu, hall⟩, hk⟩
  · cases h2

/-- **One step of the walk**, as `RoomLate.live_stepST`: the machine is in a piece of the split, and the step of that piece covers it -/
theorem live_stepK {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkK pc0 G C chk sq D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine} (hl : LiveK pc0 G C chk sq D F A m)
    (hr : R m) (hl2 : LateS sq D (go step m).2) :
    (∃ A', LiveK pc0 G C chk sq D F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph G B (go step m).2) := by
  obtain ⟨hs, hp, n, hw⟩ := hl
  cases n with
  | zero => simp [walkK] at hw
  | succ n =>
    have hs1 : Sim C.E F (sclamp sq D A) m := sim_sclamp hD hs (hS hr)
    have hp1 : Ph G (sclamp sq D A) m := RoomPause.ph_of_spent (sclamp_spent sq D A).symm hp
    have hh : SiteOK C.P m := hQ hs1 (chkK_of_walk hw) hr
    obtain ⟨A2, hA2, hs2, hk2⟩ := cov_splitK (E := C.E) (F := F) pc0 _ m hs1
    have hp2 : Ph G A2 m := RoomPause.ph_of_spent (spent_splitK pc0 _ A2 hA2).symm hp1
    obtain ⟨r, hr', hB⟩ := RoomPause.s_pstep hO hops hT h0 hg hkb hs2 hh hp2
    simp only [walkK, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 r (List.mem_flatMap.2 ⟨A2, hA2, hr'⟩)
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨g1, g2, g3⟩ := hB B rfl
      dsimp only at hw2
      rcases g2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk2, sclamp_k] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        obtain ⟨n1, n2, n3⟩ := RoomPause.weaken_of (C := C) g1
        have hpW : Ph G (weaken C B) (go step m).2 := RoomPause.ph_of_spent n3.symm g3
        rcases hw2 with ⟨_, h3⟩ | h3
        · have hpC : Ph G (sclamp sq D (weaken C B)) (go step m).2 := RoomPause.ph_of_spent (sclamp_spent sq D _).symm hpW
          obtain ⟨D', hD', hk⟩ := cover_liveK ht (sim_sclamp hD n1 hl2) hpC h3
          exact ⟨D', hD', by rw [hk, sclamp_k, n2, k1], k2, k3⟩
        · exact ⟨_, ⟨n1, hpW, n, h3⟩, by rw [n2, k1], k2, k3⟩
      · right
        rw [hk2, sclamp_k] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.2, hw2.2, k1, g1, g3⟩

/-- **One frame**, as `RoomLate.frame_of_walkST`, for the walk with the split -/
theorem frame_of_walkK {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkK pc0 G C chk sq D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkK pc0 G C chk sq D Fu S = true) (hs : Sim C.E F S m) (hph : Ph G S m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteOK C.P (trace m i j)) ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have key : ∀ j, (∃ A, LiveK pc0 G C chk sq D F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j) ∧ Ph G B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, hph0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h3, h4, h5⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hS (hk (j + 1))
        rw [e2] at hh2 ⊢
        rcases live_stepK hQ hS hD hO ht hops hT h0 hg hkb h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a5⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', by rw [a3, h2], a4, a5⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h3, h4, h5⟩
  refine ⟨fun j => ?_, ?_⟩
  · rcases key j with ⟨A, ⟨h1, _, n, h1'⟩, _, _, _⟩ | ⟨_, B, _, h2', _, h4, _⟩
    · exact hQ (sim_sclamp hD h1 (hS (hk j))) (chkK_of_walk h1') (hk j)
    · exact hQ h4 h2' (hk j)
  · rw [frame_trace]
    rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨_, B, h2, _, _, h4, _⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨B, h2, h4⟩

end

/-! ## Finding the table: a search with the split and the key, no part of the proof, and the check -/

section
open ScreenPage (SearchS)

/-- the bit 7 of a RAM byte, as the state knows it: not known, known 0, known 1 -/
def bit7Key (i : Nat) (A : AS) : Nat :=
  let b := A.getK i
  if b.k &&& 0x80 == 0 then 0 else if b.v &&& 0x80 == 0 then 1 else 2

/-- the search's key: `RoomPause.keyP`, and what `kb` picks -/
def keyK (Z : Aids) (E : Env) (kb : AS → Nat) (A : AS) : Nat := RoomPause.keyP Z E A * 4 + kb A

/-- `RoomLate.routeST` with the key `keyK` -/
def routeK (P : Places) (Z : Aids) (E : Env) (kb : AS → Nat) (sq : UInt16 → Bool) (D : Nat) (X : SearchS) (B0 : AS) : SearchS :=
  let B := sclamp sq D (clampS P (Z.norm B0))
  let K := keyK Z E kb B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D' =>
    if B.le D' then X else
    let J := D'.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 && sq J.pc then { J with hi := D } else J
    RoomPause.putP { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => RoomPause.putP { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

/-- `RoomLate.runST` with the split before each step -/
partial def runK (pc0 : UInt16) (P : Places) (Z : Aids) (E : Env) (kb : AS → Nat) (ops : Array (AM Unit)) (G : Reg) (sq : UInt16 → Bool) (D : Nat) (X0 : SearchS)
    (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (splitK pc0 (sclamp sq D cur)).flatMap (pstep P E ops G)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (Z.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
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
        X := routeK P Z E kb sq D X b
    break
  return X

/-- `RoomLate.searchST` with `runK` -/
partial def searchK (pc0 : UInt16) (P : Places) (Z : Aids) (E : Env) (kb : AS → Nat) (ops : Array (AM Unit)) (G : Reg) (sq : UInt16 → Bool) (D : Nat) (X0 : SearchS) :
    SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := keyK Z E kb A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runK pc0 P Z E kb ops G sq D X A
  return X

/-- `RoomLate.searchBT` with `searchK` -/
def searchBK (pc0 : UInt16) (P : Places) (Z : Aids) (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8)))
    (sq : UInt16 → Bool) (D : Nat) : SearchS :=
  let Z := RoomPause.aidsP Z G
  let ops := (aRows E).toArray
  let S0 := RK.flatMap fun q => startsR q.1 q.2
  let S := match pre with
    | some fpc => (S0.flatMap (BufferRecords.preWalk P E ops G fpc)).map (BufferRecords.forgetL fz)
    | none => S0
  searchK pc0 P Z E kb ops G sq D (S.foldl (routeK P Z E kb sq D) {})

/-- the table of `searchBK`, as `RoomLate.cfgBT`, with the key `keyK` -/
def cfgBK (pc0 : UInt16) (P : Places) (Z0 : Aids) (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8)))
    (fin : AS → Bool) (sq : UInt16 → Bool) (D : Nat) : CfgS :=
  let Z := RoomPause.aidsP Z0 G
  let X := searchBK pc0 P Z0 E kb G pre fz RK sq D
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      match acc with
      | (arr, hm, ba) =>
        let i := arr.size
        let l := hm.getD e.1 []
        (arr.push e.2, hm.insert e.1 (i :: l), ba.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ pre.toList).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin, t := q.1, key := keyK Z E kb, idx := q.2.1, cut := q.2.2,
    norm := fun A => if pre == some A.pc then BufferRecords.forgetL fz (Z.norm A) else Z.norm A, normAt := at0 }

/-- **The check of the walk with the split**, as `RoomLate.walkCheckST` -/
def walkCheckK (pc0 : UInt16) (P : Places) (Z : Aids) (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16) (fz : List Nat)
    (RK : List (Machine × List (Nat × UInt8))) (fin chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) : Bool :=
  let C := cfgBK pc0 P Z E kb G pre fz RK fin sq D
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && StepWrites.tabOK G.SB G.T && decide (G.gI < 2048) &&
    G.keepB.all (fun p => decide (p.1 < 2048)) && decide (D < dotsPerFrame) && C.t.all (walkK pc0 G C chk sq D ScreenPage.fuelS) &&
    RK.all (fun q => ScreenPage.maskOK q.1 q.2 && (startsR q.1 q.2).all (walkK pc0 G C chk sq D ScreenPage.fuelS))

/-- what the check says -/
structure KOK (pc0 : UInt16) (E : Env) (P : Places) (G : Reg) (RK : List (Machine × List (Nat × UInt8))) (C : CfgS) (fin chk : AS → Bool) (sq : UInt16 → Bool)
    (D : Nat) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = fin
  tab : StepWrites.tabOK G.SB G.T = true
  gI : G.gI < 2048
  keepI : ∀ p ∈ G.keepB, p.1 < 2048
  dD : D < dotsPerFrame
  table : C.t.all (walkK pc0 G C chk sq D ScreenPage.fuelS) = true
  starts : ∀ q ∈ RK, ScreenPage.MaskOK q.1 q.2 ∧ ∀ S ∈ startsR q.1 q.2, walkK pc0 G C chk sq D ScreenPage.fuelS S = true

theorem kok_of_check {pc0 : UInt16} {P : Places} {Z : Aids} {E : Env} {kb : AS → Nat} {G : Reg} {pre : Option UInt16} {fz : List Nat}
    {RK : List (Machine × List (Nat × UInt8))} {fin chk : AS → Bool} {sq : UInt16 → Bool} {D : Nat} (h : walkCheckK pc0 P Z E kb G pre fz RK fin chk sq D = true) :
    KOK pc0 E P G RK (cfgBK pc0 P Z E kb G pre fz RK fin sq D) fin chk sq D := by
  simp only [walkCheckK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h4⟩, h5⟩, hkb⟩, hD⟩, h6⟩, h7⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  refine ⟨ScreenPage.placesOK_spec h1, hp, rfl, rfl, rfl, rfl, h4, h5, fun p hp => hkb p hp, hD, h6, ?_⟩
  intro q hq
  have := h7 q hq
  exact ⟨ScreenPage.maskOK_spec this.1, fun S hS => this.2 S hS⟩

end

/-- **One frame of the room from a reference of `RK`**, as `RoomLate.frameST`, for the walk with the split -/
theorem frameK {pc0 : UInt16} {E : Env} {P : Places} {G : Reg} {RK : List (Machine × List (Nat × UInt8))} {C : CfgS} {fin chk : AS → Bool} {sq : UInt16 → Bool}
    {D : Nat} {R : Machine → Prop} (h : KOK pc0 E P G RK C fin chk sq D)
    (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → chk A = true → R m → SiteOK P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) {r : Machine} {K : List (Nat × UInt8)} (hq : (r, K) ∈ RK)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hc : InCls G m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteOK P (trace m i j)) ∧ ∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  obtain ⟨hM, hw0⟩ := h.starts _ hq
  obtain ⟨S0, hS0, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) hM h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := hw0 S0 hS0
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → chk A = true → R m' → SiteOK C.P m' := by
    intro A m' hs2 hc2 hr
    rw [h.pl]
    rw [h.env] at hs2
    exact hQ hs2 hc2 hr
  have := frame_of_walkK (G := G) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) hQ' hS h.dD hO h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide)
    (by rw [h.env]; exact h.pad) h.tab h.gI h.keepI hw hs' (Or.inr hc) hk
  rw [h.pl, h.fin, h.env] at this
  exact this

/-! ## The place of the split on the ROM -/

/-- the routine that makes the block buffer's address: the target of the first `JSR` in the block buffer routine -/
def addrRoutine (sy : Syms) (m0 : Machine) : UInt16 :=
  let q := PipeEntryRule.findOp m0 sy.BlockBufferCollision 0x20 64
  (romByte m0 (q + 1)).toUInt16 ||| ((romByte m0 (q + 2)).toUInt16 <<< 8)

/-- **The place of the split**: that routine's add of the low byte of the buffer's start (`ADC abs,Y`) -/
def adcAt (sy : Syms) (m0 : Machine) : UInt16 := PipeEntryRule.findOp m0 (addrRoutine sy m0) 0x79 32

/-- bit 7 of the accumulator, as the state knows it -/
def bit7A (A : AS) : Nat := if A.a.k &&& 0x80 == 0 then 0 else if A.a.v &&& 0x80 == 0 then 1 else 2

/-- the key's part on the ROM: bit 7 of the pointer's low byte of the block buffer routine's read, and, at the store of the add's result (right after the add),
bit 7 of the accumulator. The places are found once. -/
def ptrKey (sy : Syms) (m0 : Machine) : AS → Nat :=
  let zR := (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 + 1)).toNat
  let st := adcAt sy m0 + 3
  fun A => bit7Key zR A + (if A.pc == st then 3 * bit7A A else 0)

end Smbrta.EraseSplit
