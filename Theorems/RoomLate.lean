import Theorems.BufferRecords

/-!
# The time of the room's frames from the walk

Until round 28 the route asked `SiteParts.Late` on every instruction of the room's frames (the field `roomLate`): away from the idle loop the dot is at most
`late`, 6000 dots before the frame's end. The walks of the room clamp the abstract state's last dot to `late` before each step (`ScreenPage.clampS`), and that
clamp is what `Late` paid for; the searches also widen the last dot to `late` when a state is joined a third time.

Here the walk itself bounds the time, but in the sound routine. The abstract state's last dot `hi` bounds the machine's dot (`Sim.hi`), and each step adds the
instruction's cycles. The walk `walkST` checks at every state that the state is at the idle loop or that its last dot is at most `late` (`timeOK`), and it covers
a state by a state of the table with no clamp to `late`. Only in the sound routine's code (from the address `lo` on in the ROM) it clamps the last dot to `D`
(`sclamp`): there the frame's instructions are asked to run at dot `D` or earlier (`LateS`). The sound routine is the one part of the handler where the walk does not
know the loops' counts: it follows the music data through a pointer and offsets that it does not know, and a loop that reads a zero byte, or shifts a byte that the
walk knows only as zero, goes on for ever in the walk (on a real run the song's data end it). So `Late` holds at every machine of the frame from the check and `LateS`
(`late_of_time`), and the clamp of `RoomPause.pstep` changes nothing on the way.

The table comes from a search (`searchST`, no part of the proof) that never widens the time outside the sound routine's code: it joins states with the same key and
takes the larger last dot. In the sound routine's code it widens the last dot to `D` at the third join, as the walk's clamp allows.

`frame_of_walkST` is `BufferRecords.frame_of_walkPCE` for this walk; it asks `LateS` of the frame, not `Late`. `walkCheckST`, `STOK`, `frameST` are
`BufferRecords`'s `walkCheckB`, `BOK`, `frameB` for it.

On the ROM (`recCheckT`) the walks (ii) and (iii) of `BufferRecords`, from the patterns of the screen buffers, are walked with the time (`walk2T`, `walk3T`, with
`sndLo` = `SoundEngine` and `sndDot` = 9,000). The walks (i) and (iv), from buffers that the walk does not know, are as in `BufferRecords`: with the time they fail
at the screen update, whose loop over the records then has no count the walk knows. So `late_sites_of_rows` asks `Late` on the frames `BufferRecords.U` and
`LateS` on the others.

There is no game data in this file. Page: `1-1/d-2-4-2-3-RoomLate.md`.
-/

namespace Smbrta.RoomLate

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken coverS startsR)
open RoomPause (Reg pstep Ph InCls)
open SiteParts (Late Off)

/-! ## The time's check -/

/-- **The time's check**: the state is at the idle loop, or its last dot is at most `late` -/
def timeOK (P : Places) (A : AS) : Bool := A.pc == P.idle || decide (A.hi ≤ P.late)

theorem late_of_time {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hs : Sim E F A m) (h : timeOK P A = true) : Late P m := by
  intro hm
  simp only [timeOK, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd (hs.pc.trans h) hm
  · exact Nat.le_trans hs.hi h

/-! ## The sound routine's time -/

/-- **The sound routine's time**: an instruction of the sound routine's code (from `lo` on in the ROM) runs at dot `D` or earlier -/
def LateS (lo : UInt16) (D : Nat) (m : Machine) : Prop := lo ≤ m.pc → m.fdot ≤ D

/-- the clamp of the last dot to `D` in the sound routine's code -/
def sclamp (lo : UInt16) (D : Nat) (A : AS) : AS := if decide (lo ≤ A.pc) && decide (D < A.hi) then { A with hi := D } else A

theorem sim_sclamp {E : Env} {F : Nat × UInt8} {lo : UInt16} {D : Nat} (hD : D < dotsPerFrame) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : LateS lo D m) :
    Sim E F (sclamp lo D A) m := by
  unfold sclamp
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 : lo ≤ m.pc := by rw [hs.pc]; exact hc.1
    exact { hs with hi := hh h1, lim := hD }
  · exact hs

theorem sclamp_k (lo : UInt16) (D : Nat) (A : AS) : (sclamp lo D A).k = A.k := by
  unfold sclamp
  split <;> rfl

theorem sclamp_spent (lo : UInt16) (D : Nat) (A : AS) : (sclamp lo D A).spent = A.spent := by
  unfold sclamp
  split <;> rfl

/-! ## The walk: no clamp to `late`, the clamp to `D` in the sound routine's code -/

section
variable {G : Reg} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8} {lo : UInt16} {D : Nat}

/-- from `A`, step by step with `RoomPause.pstep`, as `SiteParts.walkPC`, and `chk` holds at every state of the way and at the frame's end; the last dot is clamped
to `D` in the sound routine's code (`sclamp`), and nowhere else -/
def walkST (G : Reg) (C : CfgS) (chk : AS → Bool) (lo : UInt16) (D : Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => chk (sclamp lo D A) && (pstep C.P C.E C.ops G (sclamp lo D A)).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (sclamp lo D (weaken C B))) || walkST G C chk lo D n (weaken C B)
      else B.k == A.k + 1 && C.fin B && chk B

/-- `A` covers `m` with `Ph`, and a walk from `A` succeeds -/
def LiveST (G : Reg) (C : CfgS) (chk : AS → Bool) (lo : UInt16) (D : Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ Ph G A m ∧ ∃ n, walkST G C chk lo D n A = true

theorem chkS_of_walk {n : Nat} {A : AS} (h : walkST G C chk lo D n A = true) : chk (sclamp lo D A) = true := by
  cases n with
  | zero => simp [walkST] at h
  | succ n =>
    simp only [walkST, Bool.and_eq_true] at h
    exact h.1

theorem cover_liveST (ht : C.t.all (walkST G C chk lo D Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph G B m) (h : coverS C B = true) :
    ∃ D', LiveST G C chk lo D F D' m ∧ D'.k = B.k := by
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

/-- **One step of the walk**, as `SiteParts.live_stepPC`, with `SiteOK` at the machine from `R` and the check at the clamped state (`hQ`), and `LateS` at both
machines (`hS`, `hl2`) -/
theorem live_stepST {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hS : ∀ {m : Machine}, R m → LateS lo D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkST G C chk lo D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine} (hl : LiveST G C chk lo D F A m)
    (hr : R m) (hl2 : LateS lo D (go step m).2) :
    (∃ A', LiveST G C chk lo D F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph G B (go step m).2) := by
  obtain ⟨hs, hp, n, hw⟩ := hl
  cases n with
  | zero => simp [walkST] at hw
  | succ n =>
    have hs1 : Sim C.E F (sclamp lo D A) m := sim_sclamp hD hs (hS hr)
    have hp1 : Ph G (sclamp lo D A) m := RoomPause.ph_of_spent (sclamp_spent lo D A).symm hp
    have hh : SiteOK C.P m := hQ hs1 (chkS_of_walk hw) hr
    obtain ⟨r, hr', hB⟩ := RoomPause.s_pstep hO hops hT h0 hg hkb hs1 hh hp1
    simp only [walkST, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 r hr'
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨g1, g2, g3⟩ := hB B rfl
      dsimp only at hw2
      rcases g2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [sclamp_k] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        obtain ⟨n1, n2, n3⟩ := RoomPause.weaken_of (C := C) g1
        have hpW : Ph G (weaken C B) (go step m).2 := RoomPause.ph_of_spent n3.symm g3
        rcases hw2 with ⟨_, h3⟩ | h3
        · have hpC : Ph G (sclamp lo D (weaken C B)) (go step m).2 := RoomPause.ph_of_spent (sclamp_spent lo D _).symm hpW
          obtain ⟨D', hD', hk⟩ := cover_liveST ht (sim_sclamp hD n1 hl2) hpC h3
          exact ⟨D', hD', by rw [hk, sclamp_k, n2, k1], k2, k3⟩
        · exact ⟨_, ⟨n1, hpW, n, h3⟩, by rw [n2, k1], k2, k3⟩
      · right
        rw [sclamp_k] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.2, hw2.2, k1, g1, g3⟩

/-- **One frame.** A walk from `S` that succeeds, with `Ph` at the start, covers the frame of every machine of `S`, if each instruction meets `R`; then each
instruction meets `SiteOK`, and the frame ends in a state that `C.fin` accepts. Unlike `BufferRecords.frame_of_walkPCE`, `R` need give only `LateS`, not `Late`. -/
theorem frame_of_walkST {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hS : ∀ {m : Machine}, R m → LateS lo D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkST G C chk lo D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkST G C chk lo D Fu S = true) (hs : Sim C.E F S m) (hph : Ph G S m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteOK C.P (trace m i j)) ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have key : ∀ j, (∃ A, LiveST G C chk lo D F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
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
        rcases live_stepST hQ hS hD hO ht hops hT h0 hg hkb h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a5⟩
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
    · exact hQ (sim_sclamp hD h1 (hS (hk j))) (chkS_of_walk h1') (hk j)
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

/-! ## Finding the table: a search, no part of the proof, and the check -/

section
open ScreenPage (SearchS)

/-- `RoomPause.routeP` with the clamp to `D` in the sound routine's code, and the time widened only there (to `D`, at the third join of a key) -/
def routeST (P : Places) (Z : Aids) (E : Env) (lo : UInt16) (D : Nat) (X : SearchS) (B0 : AS) : SearchS :=
  let B := sclamp lo D (clampS P (Z.norm B0))
  let K := RoomPause.keyP Z E B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D' =>
    if B.le D' then X else
    let J := D'.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 && decide (lo ≤ J.pc) then { J with hi := D } else J
    RoomPause.putP { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => RoomPause.putP { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

/-- `RoomPause.runP` with `routeST` and the clamp to `D` before each step -/
partial def runST (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (G : Reg) (lo : UInt16) (D : Nat) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := pstep P E ops G (sclamp lo D cur)
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
        X := routeST P Z E lo D X b
    break
  return X

/-- `RoomPause.searchP` with `runST` -/
partial def searchST (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (G : Reg) (lo : UInt16) (D : Nat) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := RoomPause.keyP Z E A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runST P Z E ops G lo D X A
  return X

/-- `BufferRecords.searchB` with `searchST` -/
def searchBT (P : Places) (Z : Aids) (E : Env) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (lo : UInt16) (D : Nat) :
    SearchS :=
  let Z := RoomPause.aidsP Z G
  let ops := (aRows E).toArray
  let S0 := RK.flatMap fun q => startsR q.1 q.2
  let S := match pre with
    | some fpc => (S0.flatMap (BufferRecords.preWalk P E ops G fpc)).map (BufferRecords.forgetL fz)
    | none => S0
  searchST P Z E ops G lo D (S.foldl (routeST P Z E lo D) {})

/-- the table of `searchBT`, as `BufferRecords.cfgB` -/
def cfgBT (P : Places) (Z0 : Aids) (E : Env) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin : AS → Bool)
    (lo : UInt16) (D : Nat) : CfgS :=
  let Z := RoomPause.aidsP Z0 G
  let X := searchBT P Z0 E G pre fz RK lo D
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      match acc with
      | (arr, hm, ba) =>
        let i := arr.size
        let l := hm.getD e.1 []
        (arr.push e.2, hm.insert e.1 (i :: l), ba.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ pre.toList).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin, t := q.1, key := RoomPause.keyP Z E, idx := q.2.1, cut := q.2.2,
    norm := fun A => if pre == some A.pc then BufferRecords.forgetL fz (Z.norm A) else Z.norm A, normAt := at0 }

/-- **The check of the walk with the time, from several references**, as `BufferRecords.walkCheckB` -/
def walkCheckST (P : Places) (Z : Aids) (E : Env) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin chk : AS → Bool)
    (lo : UInt16) (D : Nat) : Bool :=
  let C := cfgBT P Z E G pre fz RK fin lo D
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && StepWrites.tabOK G.SB G.T && decide (G.gI < 2048) &&
    G.keepB.all (fun p => decide (p.1 < 2048)) && decide (D < dotsPerFrame) && C.t.all (walkST G C chk lo D ScreenPage.fuelS) &&
    RK.all (fun q => ScreenPage.maskOK q.1 q.2 && (startsR q.1 q.2).all (walkST G C chk lo D ScreenPage.fuelS))

/-- what the check says -/
structure STOK (E : Env) (P : Places) (G : Reg) (RK : List (Machine × List (Nat × UInt8))) (C : CfgS) (fin chk : AS → Bool) (lo : UInt16) (D : Nat) : Prop where
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
  table : C.t.all (walkST G C chk lo D ScreenPage.fuelS) = true
  starts : ∀ q ∈ RK, ScreenPage.MaskOK q.1 q.2 ∧ ∀ S ∈ startsR q.1 q.2, walkST G C chk lo D ScreenPage.fuelS S = true

theorem stok_of_check {P : Places} {Z : Aids} {E : Env} {G : Reg} {pre : Option UInt16} {fz : List Nat} {RK : List (Machine × List (Nat × UInt8))}
    {fin chk : AS → Bool} {lo : UInt16} {D : Nat} (h : walkCheckST P Z E G pre fz RK fin chk lo D = true) :
    STOK E P G RK (cfgBT P Z E G pre fz RK fin lo D) fin chk lo D := by
  simp only [walkCheckST, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
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

/-- **One frame of the room from a reference of `RK`**, with the music bytes in a class, as `BufferRecords.frameB`: with `R` on each instruction (which gives
`LateS`), `SiteOK` on each instruction, and the frame ends in a state that `fin` accepts -/
theorem frameST {E : Env} {P : Places} {G : Reg} {RK : List (Machine × List (Nat × UInt8))} {C : CfgS} {fin chk : AS → Bool} {lo : UInt16} {D : Nat}
    {R : Machine → Prop} (h : STOK E P G RK C fin chk lo D) (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → chk A = true → R m → SiteOK P m)
    (hS : ∀ {m : Machine}, R m → LateS lo D m) {r : Machine} {K : List (Nat × UInt8)} (hq : (r, K) ∈ RK)
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
  have := frame_of_walkST (G := G) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) hQ' hS h.dD hO h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide)
    (by rw [h.env]; exact h.pad) h.tab h.gI h.keepI hw hs' (Or.inr hc) hk
  rw [h.pl, h.fin, h.env] at this
  exact this

/-! ## The two walks from the patterns, with the time, on the ROM -/

section
open BufferRecords (InPat Pat recCheck rec_parts patOK starts0 starts6 fin0 noRegs zO zOC fpcOf ptrBytes ref6 cond_pat idx_of_all end0 reads_all)
open EntryBuffer (ctlI)
open ScreenPage (placesR envR refR)
variable {sy : Syms} {nmS : Names} {m0 : Machine} {T : List StepWrites.SState}

/-- the sound routine's code: from the symbol `SoundEngine` on in the ROM -/
def sndLo (sy : Syms) : UInt16 := sy.SoundEngine

/-- the dot by which the sound routine's instructions are asked to run -/
def sndDot : Nat := 9000

/-- what the route asks on each instruction of a frame that the walks with the time follow: `LateS` and three parts of `SiteOK` -/
structure RestS (P : Places) (lo : UInt16) (D : Nat) (m : Machine) : Prop where
  lateS : LateS lo D m
  read : SiteParts.Read P m
  erase : SiteParts.Erase P m
  xbit : SiteParts.Xbit P m

/-- the search's aids with the places where A and Y, or X, are forgotten (the returns of the calls of `ScreenPage.aidsOf`) kept only where the call's target is
in the ROM: `ScreenPage.jsrRets` takes every byte `0x20` as a call, and the high byte of a picture register's address is `0x20` too, so it also forgets A and Y
after a read of the picture's status, where the wait for the sprite-0 flag tests A. The aids are no part of the proof: the walk checks that it only forgets. -/
def fixCuts (m0 : Machine) (Z : Aids) : Aids :=
  { Z with cutAY := Z.cutAY.filter (fun q => decide (0x80 ≤ romByte m0 (q - 1))), cutX := Z.cutX.filter (fun q => decide (0x80 ≤ romByte m0 (q - 1))) }

/-- the check at each state of the walks with the time: the offset's, the read's at every pointer, and the time's -/
def chkT (P : Places) (E : Env) (A : AS) : Bool := SiteParts.chk0 P E [] A && timeOK P A

/-- (ii) with the time: from the patterns of `L`, the control at 0 -/
def walk2T (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckST (placesR sy nm m0) (fixCuts m0 (noRegs (zO sy nm m0))) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0) (starts0 nm m0 L)
    (fin0 (ctlI nm) L L6) (chkT (placesR sy nm m0) (envR sy nm m0)) (sndLo sy) sndDot

/-- (iii) with the time: from the patterns of `L6`, the control at 6 -/
def walk3T (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckST (placesR sy nm m0) (fixCuts m0 (noRegs (zOC sy nm m0))) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0) (starts6 nm m0 L6)
    (fun _ => true) (chkT (placesR sy nm m0) (envR sy nm m0)) (sndLo sy) sndDot

/-- **The check on the ROM**: `BufferRecords.recCheck` with the walks (ii) and (iii) replaced by the walks with the time -/
def recCheckT (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  (RoomMusic.knownM nm).all (fun p => p.1 != ctlI nm) && decide (ctlI nm < 2048) && L.all (patOK (SiteParts.knownMC nm)) &&
    L6.all (patOK (SiteParts.knownMC nm)) && BufferRecords.walk1 sy nm m0 T L L6 && walk2T sy nm m0 T L L6 && walk3T sy nm m0 T L6 && BufferRecords.walk4 sy nm m0 T

theorem recT_parts {L L6 : List (List (Nat × UInt8))} (h : recCheckT sy nmS m0 T L L6 = true) :
    (RoomMusic.knownM nmS).all (fun p => p.1 != ctlI nmS) = true ∧ ctlI nmS < 2048 ∧ (∀ s ∈ L, patOK (SiteParts.knownMC nmS) s = true) ∧
    (∀ s ∈ L6, patOK (SiteParts.knownMC nmS) s = true) ∧ BufferRecords.walk1 sy nmS m0 T L L6 = true ∧ walk2T sy nmS m0 T L L6 = true ∧ walk3T sy nmS m0 T L6 = true ∧
    BufferRecords.walk4 sy nmS m0 T = true := by
  simp only [recCheckT, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨List.all_eq_true.2 h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- the walks (i) and (iv) of `recCheckT` are those of `recCheck`: with them and the two walks of `recCheckT`, `recCheck`'s frame theorems for (i) and (iv) apply -/
theorem rec_of_T {L L6 : List (List (Nat × UInt8))} (h : recCheckT sy nmS m0 T L L6 = true) :
    (RoomMusic.knownM nmS).all (fun p => p.1 != ctlI nmS) = true ∧ ctlI nmS < 2048 ∧ BufferRecords.walk1 sy nmS m0 T L L6 = true ∧
    BufferRecords.walk4 sy nmS m0 T = true := by
  obtain ⟨h1, h2, _, _, h5, _, _, h8⟩ := recT_parts h
  exact ⟨h1, h2, h5, h8⟩

/-- the check with the time at a state gives `SiteOK` from `RestS` -/
theorem siteOK_of_T {F : Nat × UInt8} {A : AS} {m : Machine} (hI : (placesR sy nmS m0).offI < 2048) (hs : Sim (envR sy nmS m0) F A m)
    (hc : chkT (placesR sy nmS m0) (envR sy nmS m0) A = true) {lo : UInt16} {D : Nat} (hr : RestS (placesR sy nmS m0) lo D m) : SiteOK (placesR sy nmS m0) m := by
  simp only [chkT, SiteParts.chk0, Bool.and_eq_true] at hc
  exact SiteParts.siteOK_of (late_of_time hs hc.2) (reads_all hs hc.1.2) hr.read hr.erase (SiteParts.off_of_ok hI hs hc.1.1) hr.xbit

/-- **(ii) with the time: a frame from the control at 0 in a pattern of `L`**: from `RestS` (no `Late`), `SiteOK` on each instruction, and the frame ends in the
class of `L` or of `L6` -/
theorem rec_frame2T (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckT sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 0 L m) (hk : ∀ j, RestS (placesR sy nmS m0) (sndLo sy) sndDot (trace m i j)) :
    (∀ j, SiteOK (placesR sy nmS m0) (trace m i j)) ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, w1, w2, _, _⟩ := recT_parts hO
  have w := stok_of_check w2
  have hsz : (refR m0).ram.size = 2048 := ((BufferRecords.bok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := BufferControl.cond0 hm (hv.trans h2.symm)
  have hm2 := cond_pat s hm1 hsz (hL s hs1) hs2
  obtain ⟨h1, B, hf, hs⟩ := frameST (R := RestS (placesR sy nmS m0) (sndLo sy) sndDot) w (fun hs hc2 hr => siteOK_of_T hI hs hc2 hr) (fun hr => hr.lateS)
    (List.mem_map_of_mem (f := fun s => (BufferRecords.refPat (refR m0) s, BufferRecords.knownPat (SiteParts.knownMC nmS) s)) hs1) hm2 hc hk
  exact ⟨h1, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf hs⟩

/-- **(iii) with the time: a frame from the control at 6 in a pattern of `L6`**: from `RestS` (no `Late`), `SiteOK` on each instruction -/
theorem rec_frame3T (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckT sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 6 L6 m) (hk : ∀ j, RestS (placesR sy nmS m0) (sndLo sy) sndDot (trace m i j)) :
    ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, hL6, w1, _, w3, _⟩ := recT_parts hO
  have w := stok_of_check w3
  have hsz0 : (refR m0).ram.size = 2048 := ((BufferRecords.bok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv
  have hsz : (ref6 nmS m0).ram.size = 2048 := by
    show ((refR m0).ram.set! (ctlI nmS) 6).size = 2048
    rw [PipeTransitionAll.ba_size_set, hsz0]
  have hm2 := cond_pat s hm1 hsz (hL6 s hs1) hs2
  exact (frameST (R := RestS (placesR sy nmS m0) (sndLo sy) sndDot) w (fun hs hc2 hr => siteOK_of_T hI hs hc2 hr) (fun hr => hr.lateS)
    (List.mem_map_of_mem (f := fun s => (BufferRecords.refPat (ref6 nmS m0) s, BufferRecords.knownPat (SiteParts.knownMC nmS) s)) hs1) hm2 hc hk).1

/-- **(i) A frame from the control at 0** with nothing known of the buffers, as `BufferRecords.rec_frame1` under `recCheckT`: from `Rest` (with `Late`) and
`Reads` through the screen update's pointer, `SiteOK` on each instruction, and the frame ends in the class of `L` or of `L6` -/
theorem rec_frame1T (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckT sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 0) (hk : ∀ j, SiteParts.Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) (trace m i j)) :
    (∀ j, SiteOK (placesR sy nmS m0) (trace m i j)) ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, w1, _, _, _⟩ := recT_parts hO
  have w := BufferRecords.bok_of_check w1
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  have hQ : ∀ {F : Nat × UInt8} {A : AS} {m' : Machine}, Sim (envR sy nmS m0) F A m' →
      SiteParts.chk0 (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) A = true → SiteParts.Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) m' →
      SiteOK (placesR sy nmS m0) m' := by
    intro F A m' hs hc2 hr
    simp only [SiteParts.chk0, Bool.and_eq_true] at hc2
    exact SiteParts.siteOK_of_rest hr (SiteParts.reads_of_ok hs hc2.2 hr.reads) (SiteParts.off_of_ok hI hs hc2.1)
  obtain ⟨h1, B, hf, hs⟩ := BufferRecords.frameB (R := SiteParts.Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0)) w hQ (fun hr => hr.late)
    (List.mem_singleton_self _) (BufferControl.cond0 hm (hv.trans h2.symm)) hc hk
  exact ⟨h1, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf hs⟩

/-- **(iv) A frame from the control at 6** with nothing known of the buffers, as `BufferRecords.rec_frame4` under `recCheckT` -/
theorem rec_frame4T (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckT sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 6) (hk : ∀ j, SiteParts.Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) (trace m i j))
    (ho : ∀ j, SiteParts.Off (placesR sy nmS m0) (trace m i j)) : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, _, w1, _, _, w4⟩ := recT_parts hO
  have w := BufferRecords.bok_of_check w4
  have hsz0 : (refR m0).ram.size = 2048 := ((BufferRecords.bok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hm1 := BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv
  refine (BufferRecords.frameB (R := fun m' => SiteParts.Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) m' ∧ SiteParts.Off (placesR sy nmS m0) m') w ?_
    (fun hr => hr.1.late) (List.mem_singleton_self _) hm1 hc (fun j => ⟨hk j, ho j⟩)).1
  intro F A m' hs hc2 hr
  exact SiteParts.siteOK_of_rest hr.1 (SiteParts.reads_of_ok hs hc2 hr.1.reads) hr.2

end

/-! ## The room's frames -/

section
open PipeChangeEnd (Data InRowsT)
open BufferRecords (U InPat)
open EntryBuffer (ctlI)
open ScreenPage (placesR envR refR)
variable {sy : Syms} {nm nmS : Names} {d : Data} {m0 : Machine}

/-- **`SiteOK` on every instruction of every frame of the room, with the time from the walks**: as `BufferRecords.records_sites_of_rows`, but `Late` is asked
only on the frames `U` (the room's first frame and the frames after a frame that starts with the control at 6), and on the other frames only `LateS`: the sound
routine's instructions run at dot `sndDot` or earlier. On those frames the walks with the time (`recCheckT`) give `Late` on every instruction. -/
theorem late_sites_of_rows {V : List (Machine × List Nat)} {T : List StepWrites.SState} {L L6 : List (List (Nat × UInt8))}
    (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true) (hK : BufferControl.keepCheck sy nmS m0 = true)
    (hs : BufferControl.startCheckC sy nm d (PipeTransition.entry m0) nmS m0 = true) (hM : RoomMusic.Facts sy m0 nm d V nmS T)
    (hO : recCheckT sy nmS m0 T L L6 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true) (h0 : ScreenPage.Room sy nmS m0 (seq b))
    (rest : ∀ n, b ≤ n → n < a → ∀ j, SiteParts.Read (placesR sy nmS m0) (trace (seq n) (inp n) j) ∧ SiteParts.Erase (placesR sy nmS m0) (trace (seq n) (inp n) j) ∧
      SiteParts.Xbit (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (late : ∀ n, b ≤ n → n < a → U (ctlI nmS) seq b n → ∀ j, Late (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (lateS : ∀ n, b ≤ n → n < a → ¬ U (ctlI nmS) seq b n → ∀ j, LateS (sndLo sy) sndDot (trace (seq n) (inp n) j))
    (reads : ∀ n, b ≤ n → n < a → U (ctlI nmS) seq b n → ∀ j, SiteParts.ReadsAt (SiteParts.ptrS sy m0) (trace (seq n) (inp n) j))
    (off6 : ∀ n, b < n → n < a → (seq n).ram.get! (ctlI nmS) = 6 → (seq (n - 1)).ram.get! (ctlI nmS) = 6 → ∀ j, Off (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j) := by
  have hq : RoomMusic.emq nmS < 2048 := by
    have : RoomMusic.emq nmS ≤ 0x7FF := Nat.and_le_right
    omega
  obtain ⟨hx, ht⟩ := RoomMusic.start_of_invL hq hM.bit hM.start hin hctl
  have hm0 : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq b) := RoomMusic.roomCond_append h0 hx
  have hb0 : (seq b).ram.get! (ctlI nmS) = 0 := (BufferControl.start_ctl hs hin hctl).trans (BufferControl.keep_parts hK).2.1
  have key : ∀ k, b + k ≤ a → (∀ n, b ≤ n → n < b + k → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j)) ∧
      (b + k < a → RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq (b + k)) ∧ InCls (RoomMusic.regM sy m0 nmS T) (seq (b + k)) ∧
        (InPat (ctlI nmS) 0 L (seq (b + k)) ∨ InPat (ctlI nmS) 6 L6 (seq (b + k)) ∨ U (ctlI nmS) seq b (b + k))) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun n h1 h2 => by omega, fun _ => ⟨hm0, ht, Or.inr (Or.inr (Or.inl rfl))⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨sites, hmk⟩ := ih (by omega)
      obtain ⟨hmc, hcls, hC⟩ := hmk (by omega)
      have hctl06 := BufferControl.ctl_of_rows hF hc hK hs next hin hctl (a := b + k) sites (fun q a1 a2 => stay q a1 (by omega)) (b + k) (by omega) (Nat.le_refl _)
      have hR := rest (b + k) (by omega) (by omega)
      have hRS : U (ctlI nmS) seq b (b + k) → ∀ j, SiteParts.Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) (trace (seq (b + k)) (inp (b + k)) j) := fun hu j =>
        ⟨late (b + k) (by omega) (by omega) hu j, reads (b + k) (by omega) (by omega) hu j, (hR j).1, (hR j).2.1, (hR j).2.2⟩
      have hRT : ¬ U (ctlI nmS) seq b (b + k) → ∀ j, RestS (placesR sy nmS m0) (sndLo sy) sndDot (trace (seq (b + k)) (inp (b + k)) j) := fun hu j =>
        ⟨lateS (b + k) (by omega) (by omega) hu j, (hR j).1, (hR j).2.1, (hR j).2.2⟩
      -- the frame `b + k`: `SiteOK`, and, if it starts with the control at 0, the class of the next frame
      have hnow : (∀ j, SiteOK (placesR sy nmS m0) (trace (seq (b + k)) (inp (b + k)) j)) ∧
          ((seq (b + k)).ram.get! (ctlI nmS) = 0 →
            InPat (ctlI nmS) 0 L (frame (seq (b + k)) (inp (b + k))) ∨ InPat (ctlI nmS) 6 L6 (frame (seq (b + k)) (inp (b + k)))) := by
        by_cases hu : U (ctlI nmS) seq b (b + k)
        · rcases hctl06 with h0' | h6
          · obtain ⟨h1, h2⟩ := rec_frame1T hK hO hmc hcls h0' (hRS hu)
            exact ⟨h1, fun _ => h2⟩
          · -- the frame before started with the control at 6 too
            have hprev : b < b + k ∧ (seq (b + k - 1)).ram.get! (ctlI nmS) = 6 := by
              rcases hu with e | ⟨e1, e2⟩
              · exfalso
                have hk0 : k = 0 := by omega
                rw [hk0, Nat.add_zero, hb0] at h6
                exact absurd h6 (by decide)
              · exact ⟨e1, e2⟩
            exact ⟨rec_frame4T hK hO hmc hcls h6 (hRS hu) (off6 (b + k) hprev.1 (by omega) h6 hprev.2), fun h0' => absurd (h6.symm.trans h0') (by decide)⟩
        · rcases hC with hp0 | hp6 | hu'
          · obtain ⟨h1, h2⟩ := rec_frame2T hK hO hmc hcls hp0 (hRT hu)
            exact ⟨h1, fun _ => h2⟩
          · exact ⟨rec_frame3T hK hO hmc hcls hp6 (hRT hu), fun h0' => absurd (hp6.1.symm.trans h0') (by decide)⟩
          · exact absurd hu' hu
      refine ⟨fun n h1 h2 => ?_, fun hlt => ?_⟩
      · rcases Nat.lt_or_ge n (b + k) with h3 | h3
        · exact sites n h1 h3
        · have e : n = b + k := by omega
          rw [e]
          exact hnow.1
      · have hstep := RoomPause.pause_step hM.walk hmc hnow.1 hcls
        have e1 : b + (k + 1) = b + k + 1 := rfl
        have hcond : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq (b + k + 1)) := by
          rw [next]
          rcases hstep.2 with h3 | ⟨h3, _⟩
          · exact h3
          · exfalso
            apply h3
            rw [← next]
            exact stay (b + k + 1) (by omega) (by omega)
        rw [e1]
        refine ⟨hcond, by rw [next]; exact hstep.1, ?_⟩
        rcases hctl06 with h0' | h6
        · rcases hnow.2 h0' with h3 | h3
          · left; rw [next]; exact h3
          · right; left; rw [next]; exact h3
        · right; right; right
          have e2 : b + k + 1 - 1 = b + k := by omega
          rw [e2]
          exact ⟨by omega, h6⟩
  intro n h1 h2
  exact (key (n + 1 - b) (by omega)).1 n h1 (by omega)


end

end Smbrta.RoomLate
