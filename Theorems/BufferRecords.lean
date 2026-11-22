import Theorems.SiteParts

/-!
# The screen buffers' records at a frame's start in the room

Round 27 (`SiteParts`) left two parts of `SiteOK` as fields on the room's frames: `Reads` through the screen update's pointer into the screen's buffer (`roomReads`),
and `Off` on the frames that start with the control of the screen's buffers at 6 (`roomOff₆`). The walk did not know what the screen update reads: the buffer
that the frame before wrote.

Here the frames of the room are put in classes by what their start knows of the two screen buffers (`Pat`: some bytes have given values):

* `InPat c 0 L`: the control at 0 and the first buffer's record headers and end mark as a pattern of the list `L`;
* `InPat c 6 L6`: the control at 6, and the first buffer's offset, its records and the second buffer's records as a pattern of `L6`;
* else nothing is known (`U`: the room's first frame, or a frame after a frame that starts with the control at 6).

A frame that starts with the control at 0 ends in one of the first two classes (`fin0`): the walk from the control at 0 keeps the offset apart, and the records
are written at known places with known headers.

The walk of `RoomMusic` with a check at each state (`SiteParts.walkPC`) is run four times (`recCheck`):

* (i) from the control at 0 with nothing known of the buffers: the offset's check and the read's check but at the screen update's pointer; at the end `fin0`;
* (ii) from each pattern of `L`, the control at 0: the offset's check and the read's check at every pointer; at the end `fin0`;
* (iii) from each pattern of `L6`, the control at 6, with the offset and the control kept apart: the same checks;
* (iv) from the control at 6 with nothing known: the read's check but at the screen update's pointer (as in round 27).

The search of (ii) and (iii) starts after the screen update (`preWalk`): each start is walked alone through the screen update, which reads the records of the
pattern, so the screen update's pointer is known at every read. The lists `L`, `L6` and the music table come from a program; the check does not depend on how they
were found.

So `SiteOK` holds on every instruction of the room's frames (`records_sites_of_rows`) from `Late`, `Read`, `Erase`, `Xbit`, from `Reads` through the screen
update's pointer only on the frames `U`, and from `Off` only on the frames that start with the control at 6 after a frame that starts with it at 6.

There is no game data in this file. Page: `1-1/d-2-4-2-2-BufferRecords.md`.
-/

namespace Smbrta.BufferRecords

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken coverS startsR placesR envR refR aidsOf)
open RoomPause (Reg pstep Ph InCls)
open SiteParts (Late ReadsAt Off Rest walkPC LivePC)
open EntryBuffer (ctlI)

/-! ## Patterns of bytes -/

/-- the bytes of `s` have the values that `s` gives -/
def Pat (s : List (Nat × UInt8)) (m : Machine) : Prop := ∀ p ∈ s, m.ram.get! p.1 = p.2

/-- the state knows the bytes of `s` with the values that `s` gives -/
def knowsPat (s : List (Nat × UInt8)) (B : AS) : Bool := s.all fun p => (B.getK p.1).isK && (B.getK p.1).v == p.2

/-- the reference with the bytes of `s` set -/
def refPat (r : Machine) : List (Nat × UInt8) → Machine
  | [] => r
  | p :: s => refPat { r with ram := r.ram.set! p.1 p.2 } s

/-- the known bits `K` and all bits of the bytes of `s` -/
def knownPat (K : List (Nat × UInt8)) : List (Nat × UInt8) → List (Nat × UInt8)
  | [] => K
  | p :: s => knownPat (K ++ [(p.1, 0xFF)]) s

/-- the bytes of `s` are RAM bytes, none of them is listed in `K` or twice in `s` -/
def patOK (K : List (Nat × UInt8)) : List (Nat × UInt8) → Bool
  | [] => true
  | p :: s => decide (p.1 < 2048) && K.all (fun q => q.1 != p.1) && patOK (K ++ [(p.1, 0xFF)]) s

theorem idx_of_patOK : ∀ {K : List (Nat × UInt8)} {s : List (Nat × UInt8)}, patOK K s = true → ∀ p ∈ s, p.1 < 2048
  | _, [], _, p, hp => by simp at hp
  | _, q :: s, h, p, hp => by
    simp only [patOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hp with e | e
    · rw [e]; exact h.1.1
    · exact idx_of_patOK h.2 p e

section
variable {E : Env} {m : Machine}

/-- the room's condition, and one more byte with its value in the reference -/
theorem cond_set {r : Machine} {K : List (Nat × UInt8)} {c : Nat} {v : UInt8} (hm : RoomCond E r K m) (hK : K.all (fun p => p.1 != c) = true)
    (hc : c < r.ram.size) (hv : m.ram.get! c = v) : RoomCond E { r with ram := r.ram.set! c v } (K ++ [(c, 0xFF)]) m := by
  have h1 : RoomCond E { r with ram := r.ram.set! c v } K m := by
    refine { hm with bytes := ?_ }
    intro p hp
    have hne : c ≠ p.1 := by
      have h := List.all_eq_true.1 hK p hp
      simp only [bne_iff_ne, ne_eq] at h
      exact fun e => h e.symm
    show m.ram.get! p.1 &&& p.2 = (r.ram.set! c v).get! p.1 &&& p.2
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ hne]
    exact hm.bytes p hp
  refine BufferControl.cond0 h1 ?_
  show m.ram.get! c = (r.ram.set! c v).get! c
  rw [hv, PipeTransitionAll.ba_get_set_self _ _ _ hc]

/-- **The room's condition with a pattern**: the bytes of `s` join the known bits, with their values in the reference -/
theorem cond_pat : ∀ (s : List (Nat × UInt8)) {r : Machine} {K : List (Nat × UInt8)}, RoomCond E r K m → r.ram.size = 2048 → patOK K s = true → Pat s m →
    RoomCond E (refPat r s) (knownPat K s) m
  | [], _, _, hm, _, _, _ => hm
  | p :: s, r, K, hm, hsz, hok, hp => by
    simp only [patOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨h1, h2⟩, h3⟩ := hok
    have hm' := cond_set hm h2 (by rw [hsz]; exact h1) (hp p (by simp))
    have hsz' : ({ r with ram := r.ram.set! p.1 p.2 } : Machine).ram.size = 2048 := by
      show (r.ram.set! p.1 p.2).size = 2048
      rw [PipeTransitionAll.ba_size_set, hsz]
    exact cond_pat s hm' hsz' h3 (fun q hq => hp q (List.mem_cons_of_mem _ hq))

theorem pat_of_knows {s : List (Nat × UInt8)} {B : AS} {F : Nat × UInt8} (hI : ∀ p ∈ s, p.1 < 2048) (h : knowsPat s B = true) (hs : Sim E F B m) :
    Pat s m := by
  intro p hp
  have h1 := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  rw [PipeEntryRule.known_eq h1.1 (hs.ram p.1 (hI p hp)), h1.2]

end

/-! ## The classes at a frame's end -/

/-- the state knows the control at `v` -/
def ctlIs (c : Nat) (v : UInt8) (B : AS) : Bool := (B.getK c).isK && (B.getK c).v == v

/-- the state knows a pattern of `L` -/
def anyPat (L : List (List (Nat × UInt8))) (B : AS) : Bool := L.any fun s => knowsPat s B

/-- at the end of a frame that starts with the control at 0: the control at 0 and a pattern of `L`, or at 6 and a pattern of `L6` -/
def fin0 (c : Nat) (L L6 : List (List (Nat × UInt8))) (B : AS) : Bool := (ctlIs c 0 B && anyPat L B) || (ctlIs c 6 B && anyPat L6 B)

/-- **The class of a frame's start**: the control at `v`, and the bytes of a pattern of `L` -/
def InPat (c : Nat) (v : UInt8) (L : List (List (Nat × UInt8))) (m : Machine) : Prop := m.ram.get! c = v ∧ ∃ s ∈ L, Pat s m

section
variable {E : Env} {m : Machine} {F : Nat × UInt8}

theorem ctl_of_is {c : Nat} {v : UInt8} {B : AS} (hc : c < 2048) (h : ctlIs c v B = true) (hs : Sim E F B m) : m.ram.get! c = v := by
  simp only [ctlIs, Bool.and_eq_true, beq_iff_eq] at h
  rw [PipeEntryRule.known_eq h.1 (hs.ram c hc), h.2]

theorem inPat_of {c : Nat} {v : UInt8} {L : List (List (Nat × UInt8))} {B : AS} (hc : c < 2048) (hI : ∀ s ∈ L, ∀ p ∈ s, p.1 < 2048)
    (h1 : ctlIs c v B = true) (h2 : anyPat L B = true) (hs : Sim E F B m) : InPat c v L m := by
  refine ⟨ctl_of_is hc h1 hs, ?_⟩
  obtain ⟨s, hs1, hs2⟩ := List.any_eq_true.1 h2
  exact ⟨s, hs1, pat_of_knows (hI s hs1) hs2 hs⟩

theorem end0 {c : Nat} {L L6 : List (List (Nat × UInt8))} {B : AS} (hc : c < 2048) (hI : ∀ s ∈ L, ∀ p ∈ s, p.1 < 2048) (hI6 : ∀ s ∈ L6, ∀ p ∈ s, p.1 < 2048)
    (h : fin0 c L L6 B = true) (hs : Sim E F B m) : InPat c 0 L m ∨ InPat c 6 L6 m := by
  simp only [fin0, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (inPat_of hc hI h1 h2 hs)
  · exact Or.inr (inPat_of hc hI6 h1 h2 hs)

end

/-! ## One frame, with its end -/

section
variable {G : Reg} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

/-- **One frame**, as `SiteParts.frame_of_walkPC`, and the frame ends in a state that `C.fin` accepts -/
theorem frame_of_walkPCE {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hL : ∀ {m : Machine}, R m → Late C.P m)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkPC G C chk Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkPC G C chk Fu S = true) (hs : Sim C.E F S m) (hph : Ph G S m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteOK C.P (trace m i j)) ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have key : ∀ j, (∃ A, LivePC G C chk F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
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
        have hh2 := hL (hk (j + 1))
        rw [e2] at hh2 ⊢
        rcases SiteParts.live_stepPC hQ hO ht hops hT h0 hg hkb h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a5⟩
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
    · exact hQ h1 (SiteParts.chkP_of_walk h1') (hk j)
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

/-! ## The walks: a search, no part of the proof, and the check -/

/-- the states at `fpc` on every path from `A0`, each path walked alone (a search: no part of the proof) -/
partial def preWalk (P : Places) (E : Env) (ops : Array (AM Unit)) (G : Reg) (fpc : UInt16) (A0 : AS) : List AS := Id.run do
  let mut out : List AS := []
  let mut stack : List AS := [A0]
  let mut n := 0
  while n < 100000 do
    match stack with
    | [] => break
    | A :: rest =>
      stack := rest
      n := n + 1
      for r in pstep P E ops G A do
        match r with
        | none => pure ()
        | some B =>
          if B.k == A.k then
            if B.pc == fpc then out := B :: out else stack := B :: stack
  return out

/-- the state with the bytes `l` forgotten -/
def forgetL (l : List Nat) (A : AS) : AS := l.foldl (fun B i => B.setK i AB.top) A

/-- `RoomPause`'s search from the starts of the references `RK`. With `pre = some fpc` the search starts at `fpc`, from the states that `preWalk` finds there,
with the bytes `fz` forgotten. -/
def searchB (P : Places) (Z : Aids) (E : Env) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) : ScreenPage.SearchS :=
  let Z := RoomPause.aidsP Z G
  let ops := (aRows E).toArray
  let S0 := RK.flatMap fun q => startsR q.1 q.2
  let S := match pre with
    | some fpc => (S0.flatMap (preWalk P E ops G fpc)).map (forgetL fz)
    | none => S0
  RoomPause.searchP P Z E ops G (S.foldl (RoomPause.routeP P Z E) {})

/-- the table of `searchB`, with `fin` at the frame's end; at `fpc` the walk may forget the bytes `fz` -/
def cfgB (P : Places) (Z0 : Aids) (E : Env) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin : AS → Bool) : CfgS :=
  let Z := RoomPause.aidsP Z0 G
  let X := searchB P Z0 E G pre fz RK
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
    norm := fun A => if pre == some A.pc then forgetL fz (Z.norm A) else Z.norm A, normAt := at0 }

/-- **The check of a walk with a check at each state, from several references** -/
def walkCheckB (P : Places) (Z : Aids) (E : Env) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin chk : AS → Bool) : Bool :=
  let C := cfgB P Z E G pre fz RK fin
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && StepWrites.tabOK G.SB G.T && decide (G.gI < 2048) &&
    G.keepB.all (fun p => decide (p.1 < 2048)) && C.t.all (walkPC G C chk ScreenPage.fuelS) &&
    RK.all (fun q => ScreenPage.maskOK q.1 q.2 && (startsR q.1 q.2).all (walkPC G C chk ScreenPage.fuelS))

/-- what the check says -/
structure BOK (E : Env) (P : Places) (G : Reg) (RK : List (Machine × List (Nat × UInt8))) (C : CfgS) (fin chk : AS → Bool) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = fin
  tab : StepWrites.tabOK G.SB G.T = true
  gI : G.gI < 2048
  keepI : ∀ p ∈ G.keepB, p.1 < 2048
  table : C.t.all (walkPC G C chk ScreenPage.fuelS) = true
  starts : ∀ q ∈ RK, ScreenPage.MaskOK q.1 q.2 ∧ ∀ S ∈ startsR q.1 q.2, walkPC G C chk ScreenPage.fuelS S = true

theorem bok_of_check {P : Places} {Z : Aids} {E : Env} {G : Reg} {pre : Option UInt16} {fz : List Nat} {RK : List (Machine × List (Nat × UInt8))}
    {fin chk : AS → Bool} (h : walkCheckB P Z E G pre fz RK fin chk = true) : BOK E P G RK (cfgB P Z E G pre fz RK fin) fin chk := by
  simp only [walkCheckB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h4⟩, h5⟩, hkb⟩, h6⟩, h7⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  refine ⟨ScreenPage.placesOK_spec h1, hp, rfl, rfl, rfl, rfl, h4, h5, fun p hp => hkb p hp, h6, ?_⟩
  intro q hq
  have := h7 q hq
  exact ⟨ScreenPage.maskOK_spec this.1, fun S hS => this.2 S hS⟩

/-- **One frame of the room from a reference of `RK`**, with the music bytes in a class: with `R` on each instruction, `SiteOK` on each instruction, and the frame
ends in a state that `fin` accepts -/
theorem frameB {E : Env} {P : Places} {G : Reg} {RK : List (Machine × List (Nat × UInt8))} {C : CfgS} {fin chk : AS → Bool} {R : Machine → Prop}
    (h : BOK E P G RK C fin chk) (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → chk A = true → R m → SiteOK P m)
    (hL : ∀ {m : Machine}, R m → Late P m) {r : Machine} {K : List (Nat × UInt8)} (hq : (r, K) ∈ RK)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hc : InCls G m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteOK P (trace m i j)) ∧ ∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  obtain ⟨hM, hw0⟩ := h.starts _ hq
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) hM h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := hw0 S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → chk A = true → R m' → SiteOK C.P m' := by
    intro A m' hs2 hc2 hr
    rw [h.pl]
    rw [h.env] at hs2
    exact hQ hs2 hc2 hr
  have hL' : ∀ {m' : Machine}, R m' → Late C.P m' := by
    intro m' hr
    rw [h.pl]
    exact hL hr
  have := frame_of_walkPCE (G := G) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) hQ' hL' hO h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide)
    (by rw [h.env]; exact h.pad) h.tab h.gI h.keepI hw hs' (Or.inr hc) hk
  rw [h.pl, h.fin, h.env] at this
  exact this

/-! ## The four walks on the ROM -/

section
variable {sy : Syms} {nmS : Names} {m0 : Machine} {T : List StepWrites.SState}

/-- the place after the call of the screen update in the handler -/
def fpcOf (sy : Syms) (m0 : Machine) : UInt16 := ScreenPage.findJsr m0 sy.NonMaskableInterrupt sy.UpdateScreen 256 + 3

/-- the two bytes of the screen update's pointer -/
def ptrBytes (sy : Syms) (m0 : Machine) : List Nat := (SiteParts.ptrS sy m0).flatMap fun z => [z.toNat, z.toNat + 1]

/-- the search keeps the first buffer's offset apart -/
def zO (sy : Syms) (nm : Names) (m0 : Machine) : Aids := SiteParts.keepOff (aidsOf sy nm m0) (placesR sy nm m0).offI

/-- the search's aids with no place where the registers are forgotten: the three places of the screen update, which the walks from the patterns walk with
the registers known (their search starts after the screen update, so nothing else changes) -/
def noRegs (Z : Aids) : Aids := { Z with regs := [] }

/-- the reference with the control at 6 -/
def ref6 (nm : Names) (m0 : Machine) : Machine := BufferControl.ref6 (ctlI nm) (refR m0)

/-- the starts of the patterns -/
def starts0 (nm : Names) (m0 : Machine) (L : List (List (Nat × UInt8))) : List (Machine × List (Nat × UInt8)) :=
  L.map fun s => (refPat (refR m0) s, knownPat (SiteParts.knownMC nm) s)

def starts6 (nm : Names) (m0 : Machine) (L6 : List (List (Nat × UInt8))) : List (Machine × List (Nat × UInt8)) :=
  L6.map fun s => (refPat (ref6 nm m0) s, knownPat (SiteParts.knownMC nm) s)

/-- (i) from the control at 0, nothing known of the buffers: the offset's check and the read's check but at the screen update's pointer -/
def walk1 (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckB (placesR sy nm m0) (zO sy nm m0) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) none [] [(refR m0, SiteParts.knownMC nm)] (fin0 (ctlI nm) L L6)
    (SiteParts.chk0 (placesR sy nm m0) (envR sy nm m0) (SiteParts.ptrS sy m0))

/-- (ii) from the patterns of `L`, the control at 0: the offset's check and the read's check at every pointer -/
def walk2 (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckB (placesR sy nm m0) (noRegs (zO sy nm m0)) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0) (starts0 nm m0 L)
    (fin0 (ctlI nm) L L6) (SiteParts.chk0 (placesR sy nm m0) (envR sy nm m0) [])

/-- the search keeps the first buffer's offset and the control apart -/
def zOC (sy : Syms) (nm : Names) (m0 : Machine) : Aids := let Z := zO sy nm m0; { Z with keep := Z.keep ++ [ctlI nm] }

/-- (iii) from the patterns of `L6`, the control at 6: the offset's check and the read's check at every pointer -/
def walk3 (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckB (placesR sy nm m0) (noRegs (zOC sy nm m0)) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0) (starts6 nm m0 L6)
    (fun _ => true) (SiteParts.chk0 (placesR sy nm m0) (envR sy nm m0) [])

/-- (iv) from the control at 6, nothing known of the buffers: the read's check but at the screen update's pointer -/
def walk4 (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) : Bool :=
  walkCheckB (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) none [] [(ref6 nm m0, SiteParts.knownMC nm)] (fun _ => true)
    (SiteParts.readsOK (envR sy nm m0) (SiteParts.ptrS sy m0))

/-- **The check on the ROM**: the room's known bits of `RoomMusic` do not list the control, the patterns are of RAM bytes not otherwise known, and the four walks -/
def recCheck (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  (RoomMusic.knownM nm).all (fun p => p.1 != ctlI nm) && decide (ctlI nm < 2048) && L.all (patOK (SiteParts.knownMC nm)) &&
    L6.all (patOK (SiteParts.knownMC nm)) && walk1 sy nm m0 T L L6 && walk2 sy nm m0 T L L6 && walk3 sy nm m0 T L6 && walk4 sy nm m0 T

theorem rec_parts {L L6 : List (List (Nat × UInt8))} (h : recCheck sy nmS m0 T L L6 = true) :
    (RoomMusic.knownM nmS).all (fun p => p.1 != ctlI nmS) = true ∧ ctlI nmS < 2048 ∧ (∀ s ∈ L, patOK (SiteParts.knownMC nmS) s = true) ∧
    (∀ s ∈ L6, patOK (SiteParts.knownMC nmS) s = true) ∧ walk1 sy nmS m0 T L L6 = true ∧ walk2 sy nmS m0 T L L6 = true ∧ walk3 sy nmS m0 T L6 = true ∧
    walk4 sy nmS m0 T = true := by
  simp only [recCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨List.all_eq_true.2 h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem idx_of_all {K : List (Nat × UInt8)} {L : List (List (Nat × UInt8))} (h : ∀ s ∈ L, patOK K s = true) : ∀ s ∈ L, ∀ p ∈ s, p.1 < 2048 :=
  fun s hs => idx_of_patOK (h s hs)

/-- the read's check at every pointer gives `Reads` -/
theorem reads_all {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : SiteParts.readsOK E [] A = true) : SiteParts.Reads m :=
  SiteParts.reads_of_ok hs h (fun _ _ h3 => by simp at h3)

/-- **(i) A frame from the control at 0** with nothing known of the buffers: from the four parts and `Reads` through the screen update's pointer, `SiteOK` on each
instruction, and the frame ends in the class of `L` or of `L6` -/
theorem rec_frame1 (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheck sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 0) (hk : ∀ j, Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) (trace m i j)) :
    (∀ j, SiteOK (placesR sy nmS m0) (trace m i j)) ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, w1, _, _, _⟩ := rec_parts hO
  have w := bok_of_check w1
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  have hQ : ∀ {F : Nat × UInt8} {A : AS} {m' : Machine}, Sim (envR sy nmS m0) F A m' →
      SiteParts.chk0 (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) A = true → Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) m' →
      SiteOK (placesR sy nmS m0) m' := by
    intro F A m' hs hc2 hr
    simp only [SiteParts.chk0, Bool.and_eq_true] at hc2
    exact SiteParts.siteOK_of_rest hr (SiteParts.reads_of_ok hs hc2.2 hr.reads) (SiteParts.off_of_ok hI hs hc2.1)
  obtain ⟨h1, B, hf, hs⟩ := frameB (R := Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0)) w hQ (fun hr => hr.late) (List.mem_singleton_self _)
    (BufferControl.cond0 hm (hv.trans h2.symm)) hc hk
  exact ⟨h1, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf hs⟩

/-- **(ii) A frame from the control at 0 in a pattern of `L`**: from the four parts, `SiteOK` on each instruction, and the frame ends in the class of `L` or of
`L6` -/
theorem rec_frame2 (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheck sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 0 L m) (hk : ∀ j, Rest (placesR sy nmS m0) [] (trace m i j)) :
    (∀ j, SiteOK (placesR sy nmS m0) (trace m i j)) ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, w1, w2, _, _⟩ := rec_parts hO
  have w := bok_of_check w2
  have hsz : (refR m0).ram.size = 2048 := ((bok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := BufferControl.cond0 hm (hv.trans h2.symm)
  have hm2 := cond_pat s hm1 hsz (hL s hs1) hs2
  have hQ : ∀ {F : Nat × UInt8} {A : AS} {m' : Machine}, Sim (envR sy nmS m0) F A m' →
      SiteParts.chk0 (placesR sy nmS m0) (envR sy nmS m0) [] A = true → Rest (placesR sy nmS m0) [] m' → SiteOK (placesR sy nmS m0) m' := by
    intro F A m' hs hc2 hr
    simp only [SiteParts.chk0, Bool.and_eq_true] at hc2
    exact SiteParts.siteOK_of_rest hr (reads_all hs hc2.2) (SiteParts.off_of_ok hI hs hc2.1)
  obtain ⟨h1, B, hf, hs⟩ := frameB (R := Rest (placesR sy nmS m0) []) w hQ (fun hr => hr.late)
    (List.mem_map_of_mem (f := fun s => (refPat (refR m0) s, knownPat (SiteParts.knownMC nmS) s)) hs1) hm2 hc hk
  exact ⟨h1, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf hs⟩

/-- **(iii) A frame from the control at 6 in a pattern of `L6`**: from the four parts alone, `SiteOK` on each instruction (the walk knows the first buffer's offset
that the frame before left, and the second buffer's records) -/
theorem rec_frame3 (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheck sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 6 L6 m) (hk : ∀ j, Rest (placesR sy nmS m0) [] (trace m i j)) :
    ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, hL6, w1, _, w3, _⟩ := rec_parts hO
  have w := bok_of_check w3
  have hsz0 : (refR m0).ram.size = 2048 := ((bok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv
  have hsz : (ref6 nmS m0).ram.size = 2048 := by
    show ((refR m0).ram.set! (ctlI nmS) 6).size = 2048
    rw [PipeTransitionAll.ba_size_set, hsz0]
  have hm2 := cond_pat s hm1 hsz (hL6 s hs1) hs2
  have hQ : ∀ {F : Nat × UInt8} {A : AS} {m' : Machine}, Sim (envR sy nmS m0) F A m' →
      SiteParts.chk0 (placesR sy nmS m0) (envR sy nmS m0) [] A = true → Rest (placesR sy nmS m0) [] m' → SiteOK (placesR sy nmS m0) m' := by
    intro F A m' hs hc2 hr
    simp only [SiteParts.chk0, Bool.and_eq_true] at hc2
    exact SiteParts.siteOK_of_rest hr (reads_all hs hc2.2) (SiteParts.off_of_ok hI hs hc2.1)
  exact (frameB (R := Rest (placesR sy nmS m0) []) w hQ (fun hr => hr.late)
    (List.mem_map_of_mem (f := fun s => (refPat (ref6 nmS m0) s, knownPat (SiteParts.knownMC nmS) s)) hs1) hm2 hc hk).1

/-- **(iv) A frame from the control at 6** with nothing known of the buffers: from the four parts, `Reads` through the screen update's pointer and `Off`, `SiteOK`
on each instruction -/
theorem rec_frame4 (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheck sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 6) (hk : ∀ j, Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) (trace m i j))
    (ho : ∀ j, Off (placesR sy nmS m0) (trace m i j)) : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, _, w1, _, _, w4⟩ := rec_parts hO
  have w := bok_of_check w4
  have hsz0 : (refR m0).ram.size = 2048 := ((bok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hm1 := BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv
  refine (frameB (R := fun m' => Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) m' ∧ Off (placesR sy nmS m0) m') w ?_ (fun hr => hr.1.late)
    (List.mem_singleton_self _) hm1 hc (fun j => ⟨hk j, ho j⟩)).1
  intro F A m' hs hc2 hr
  exact SiteParts.siteOK_of_rest hr.1 (SiteParts.reads_of_ok hs hc2 hr.1.reads) hr.2

end

/-! ## The room's frames -/

section
open PipeChangeEnd (Data InRowsT)
variable {sy : Syms} {nm nmS : Names} {d : Data} {m0 : Machine}

/-- **The frames whose start may be in no class**: the room's first frame `b`, and a frame after a frame that starts with the control of the screen's buffers
at 6 -/
def U (c : Nat) (seq : Nat → Machine) (b n : Nat) : Prop := n = b ∨ (b < n ∧ (seq (n - 1)).ram.get! c = 6)

/-- **`SiteOK` on every instruction of every frame of the room, with the buffers' records**: from `Late`, `Read`, `Erase`, `Xbit` on every frame, from `Reads`
through the screen update's pointer only on the frames with `U` (`reads`: the room's first frame and the frames after a frame that starts with the control at
6), and from `Off` only on the frames that start with the control at 6 after a frame that starts with it at 6 (`off6`); under the conditions of `RoomMap.map_of_rows`, with the checks of
`BufferControl`, of `RoomMusic` (`hM`, with its table `T`) and `recCheck` with the same table. The frames are taken in order: at a frame's start the room's
condition, the control at 0 or 6, the music bytes in a class and the frame's class (`InPat` of `L`, of `L6`, or `U`) come from the frames before it. -/
theorem records_sites_of_rows {V : List (Machine × List Nat)} {T : List StepWrites.SState} {L L6 : List (List (Nat × UInt8))}
    (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true) (hK : BufferControl.keepCheck sy nmS m0 = true)
    (hs : BufferControl.startCheckC sy nm d (PipeTransition.entry m0) nmS m0 = true) (hM : RoomMusic.Facts sy m0 nm d V nmS T)
    (hO : recCheck sy nmS m0 T L L6 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true) (h0 : ScreenPage.Room sy nmS m0 (seq b))
    (rest : ∀ n, b ≤ n → n < a → ∀ j, Rest (placesR sy nmS m0) [] (trace (seq n) (inp n) j))
    (reads : ∀ n, b ≤ n → n < a → U (ctlI nmS) seq b n → ∀ j, ReadsAt (SiteParts.ptrS sy m0) (trace (seq n) (inp n) j))
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
      have hR : ∀ j, Rest (placesR sy nmS m0) [] (trace (seq (b + k)) (inp (b + k)) j) := rest (b + k) (by omega) (by omega)
      have hRS : U (ctlI nmS) seq b (b + k) → ∀ j, Rest (placesR sy nmS m0) (SiteParts.ptrS sy m0) (trace (seq (b + k)) (inp (b + k)) j) := fun hu j =>
        ⟨(hR j).late, reads (b + k) (by omega) (by omega) hu j, (hR j).read, (hR j).erase, (hR j).xbit⟩
      -- the frame `b + k`: `SiteOK`, and, if it starts with the control at 0, the class of the next frame
      have hnow : (∀ j, SiteOK (placesR sy nmS m0) (trace (seq (b + k)) (inp (b + k)) j)) ∧
          ((seq (b + k)).ram.get! (ctlI nmS) = 0 →
            InPat (ctlI nmS) 0 L (frame (seq (b + k)) (inp (b + k))) ∨ InPat (ctlI nmS) 6 L6 (frame (seq (b + k)) (inp (b + k)))) := by
        rcases hC with hp0 | hp6 | hu
        · obtain ⟨h1, h2⟩ := rec_frame2 hK hO hmc hcls hp0 hR
          exact ⟨h1, fun _ => h2⟩
        · exact ⟨rec_frame3 hK hO hmc hcls hp6 hR, fun h0' => absurd (hp6.1.symm.trans h0') (by decide)⟩
        · rcases hctl06 with h0' | h6
          · obtain ⟨h1, h2⟩ := rec_frame1 hK hO hmc hcls h0' (hRS hu)
            exact ⟨h1, fun _ => h2⟩
          · -- the frame before started with the control at 6 too
            have hprev : b < b + k ∧ (seq (b + k - 1)).ram.get! (ctlI nmS) = 6 := by
              rcases hu with e | ⟨e1, e2⟩
              · exfalso
                have hk0 : k = 0 := by omega
                rw [hk0, Nat.add_zero, hb0] at h6
                exact absurd h6 (by decide)
              · exact ⟨e1, e2⟩
            exact ⟨rec_frame4 hK hO hmc hcls h6 (hRS hu) (off6 (b + k) hprev.1 (by omega) h6 hprev.2), fun h0' => absurd (h6.symm.trans h0') (by decide)⟩
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

end Smbrta.BufferRecords
