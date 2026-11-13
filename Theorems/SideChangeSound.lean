import Theorems.StepWrites
import Theorems.SoundWalk
import Theorems.ControlStart

/-!
# The change out of the side pipe, with the sound's bytes in tables

The rows of `SideChangeEnd` know the sound's bytes. So a press of Start on the pipe's frames, which leaves the pause sound playing at the exit, puts the machine
out of the rows: that was the hypothesis `Quiet`. Here the rows forget the sound's bytes outside the sound routine. A table of states of the sound's bytes is
carried beside the rows, outside the abstract states (`StepWrites.Ph`). At the call of the routine a state is split by the table, the routine is walked with the bytes
known, and at the return the bytes go into a second table and are forgotten (`StepWrites.tsuccs`). Each row has the two tables of its frame (`SRow`).

The rows start from the states at the exit with the sound's bytes forgotten, and the first table holds the kinds of the pause sound at the exit (`kinds`): silent with any
pause flag, the sound of the unpause at any count, or the unpause pressed on the frame of the exit. So the condition at the exit is `QuietK`, weaker than `Quiet`.
These are the rows of the time: `dg` says that the game timer is not 000, so in the last row every state has control.
There is no game data in this file. Page: `1-1/d-3-4-2-SideChangeSound.md`.
-/

namespace Smbrta.SideChangeSound

open TaintRun (AS Env AB AM Sim aRows coverIn sim_le walkFuel bitList)
open SideChangeEnd (Row Ctx rowCfg rowEnv statesOK InvL Covered mOf normD sim_normD nextStatesD coreFrame noStart noStartPad two_le sim_pad sim_unpad
  core_of_known left_of_covered)
open StepWrites (Rt SState SIn entails tabOK Ph twalk tsuccs tframe_of_walk retag forgetAll aLocs keepOK joinUnder tsearch sIn_entails)
open PipeTransition (frame)
open PipeTransitionAll (Names)

/-! ## The tables of a frame: a search, no part of the proof -/

/-- what the search of a frame gives: the writes to the routine's bytes outside it before the return and after it, the routine's bytes at the returns, the states
of the search, and the states at the frame's end -/
structure Scan where
  wb : List SState
  wa : List SState
  rets : List SState
  out : Array AS
  ends : List AS

/-- the frame's search with the call split by `T`, and nothing asked at the return or of a write outside the routine. Its states are those of the walk with `tsuccs`
when the walk does not fail, so they serve as its table. -/
def scan (E : Env) (R : Rt) (keep : List Nat) (T : List SState) (Rs : List AS) : Scan := Id.run do
  let ops := (aRows E).toArray
  let mark := fun (tag : Nat) (B : AS) => ({ B with k := B.k + 1, log := [tag] } : AS)
  let P : Nat → Bool := fun i => R.SB.contains i
  let step := fun (A : AS) =>
    let rs := if R.inR A.pc || A.pc == R.call then tsuccs E ops R T [[]] A
      else (SideChangeEnd.xsuccs E ops A).map (·.map (retag A.spent))
    let extra : List AS :=
      if R.inR A.pc then (SideChangeEnd.xsuccs E ops A).filterMap fun o => o.bind fun B => if B.pc == R.ret && B.k == A.k then some (mark 1 B) else none
      else if A.pc != R.call && !keepOK E P A then [mark 2 A]
      else []
    rs ++ extra.map some
  let X := tsearch step E keep Rs
  let mut wb : List SState := []
  let mut wa : List SState := []
  let mut rets : List SState := []
  let mut ends : List AS := []
  for Z in X.ends do
    if Z.log == [1] then
      let u : SState := R.SB.map fun i => (i, Z.getK i)
      if !rets.contains u then rets := rets ++ [u]
    else if Z.log == [2] then
      let A := ({ Z with k := Z.k - 1, log := [] } : AS)
      match aLocs E A with
      | some L =>
        for o in SideChangeEnd.xsuccs E ops A do
          match o with
          | some B =>
            let w : SState := (L.filter fun i => R.SB.contains i).map fun i => (i, B.getK i)
            if A.spent then
              if !wa.contains w then wa := wa ++ [w]
            else if !wb.contains w then wb := wb ++ [w]
          | none => pure ()
      | none => pure ()
    else ends := Z :: ends
  return { wb, wa, rets, out := X.out, ends := ends.reverse }

/-! ## Rows with tables -/

/-- a row, with the tables of its frame: the routine's bytes are in a state of `T0` before the call, and of `T1` after the return -/
structure SRow where
  row : Row
  T0 : List SState
  T1 : List SState

/-- the index of a table of states, as `SideChangeEnd.rowsFrom` makes it -/
def indexOf (E : Env) (keep : List Nat) (t : Array AS) : Std.HashMap Nat (List Nat) × ByteArray :=
  let P := t.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := TaintRun.keyOf E keep A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  (P.1, P.2.1)

/-- `left` on the first state -/
def leftHead (c : Ctx) (R : List AS) : Nat := (R.head?.map (fun S => c.left (mOf S))).getD 0

/-- the rows from the states `Rs` and the table `T`, for `n` frames. For each frame: the writes before the return are joined into `T` (the first table), the bytes at the
returns with the writes after them make the second table, and the states of the search are the table of the walk. The next table holds the first table if a path of the frame does not
come to the return, and the second if one does. -/
def rowsFromS (c : Ctx) (R : Rt) : Nat → List AS → List SState → List SRow
  | 0, Rs, T => [{ row := { core := false, R := Rs, v := leftHead c Rs, t := #[], idx := {}, cut := ByteArray.empty }, T0 := T, T1 := [] }]
  | n + 1, Rs, T =>
    let core := Rs.any fun S => coreFrame c.sy c.eng (mOf S)
    let e : Env := if core then { c.E with pad := noStartPad } else c.E
    let s1 := scan e R c.keep T Rs
    let T0 := joinUnder s1.wb T
    let s2 := if s1.wb.isEmpty then s1 else scan e R c.keep T0 Rs
    let T1 := joinUnder s2.wa s2.rets
    let I := indexOf e c.keep s2.out
    let ends := s2.ends
    { row := { core, R := Rs, v := leftHead c Rs, t := s2.out, idx := I.1, cut := I.2 }, T0, T1 } ::
      rowsFromS c R n ((nextStatesD c.E (n == 0) ends).map (retag false))
        ((if ends.any (!·.spent) then T0 else []) ++ (if ends.any (·.spent) then T1 else []))

/-! ## The check of the rows -/

/-- every state of `T` is in a state of `T'` -/
def incl (T T' : List SState) : Bool := T.all fun t => T'.any (entails t)

/-- at the frame's end: a state of the next row, and the table that holds there (the first before the return, the second after it) is in the next row's first table -/
def finS (D : List Nat) (inc0 inc1 : Bool) (R' : List AS) (B : AS) : Bool :=
  !B.rk && (if B.spent then inc1 else inc0) && R'.any fun S => (normD D ({ B with k := 0, spent := false } : AS)).le S

/-- a frame from a row to the next -/
def linkS (c : Ctx) (R : Rt) (r r' : SRow) : Bool :=
  let C := rowCfg c r.row
  let fin := finS c.E.D (incl r.T0 r'.T0) (incl r.T1 r'.T0) r'.row.R
  statesOK c r.row && statesOK c r'.row && decide (r.row.v ≤ r'.row.v + 1) && tabOK R.SB r.T0 && tabOK R.SB r.T1 &&
    C.t.all (twalk C R r.T0 r.T1 fin walkFuel) && r.row.R.all (twalk C R r.T0 r.T1 fin walkFuel)

/-- all the frames: `left` is 0 at the last row -/
def chainS (c : Ctx) (R : Rt) : List SRow → Bool
  | [] => true
  | [r] => statesOK c r.row && r.row.v == 0
  | r :: r' :: t => linkS c R r r' && chainS c R (r' :: t)

/-! ## The side pipe -/

/-- what the rows have in common: those of the rows of the time of `SideChangeEnd`, and the search keeps the routine's bytes apart -/
def soundCtx (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (SB : List Nat) : Ctx :=
  { SideChangeEnd.timeCtx sy nm nx e A B with keep := (SideChangeEnd.timeCtx sy nm nx e A B).keep ++ SB }

/-- the four bytes of the pause sound, as RAM indices: the queue, the buffer, the sound's pause flag, the counter of the first square's effect -/
structure PauseIdx where
  q : Nat
  b : Nat
  f : Nat
  c : Nat

/-- the bytes of the pause sound, from the names -/
def pauseIdx (nx : Names) : PauseIdx :=
  ⟨SideChangeEnd.adI nx "PauseSoundQueue", SideChangeEnd.adI nx "PauseSoundBuffer", SideChangeEnd.adI nx "PauseModeFlag", SideChangeEnd.adI nx "Squ1_SfxLenCounter"⟩

/-- **The pause sound at the exit.** Silent: the queue and the buffer of the pause sound have the values of the reference machine `x`, and the flag any value. Or the
sound of the unpause plays: the buffer and the flag hold the unpause sound's value, and the counter is from 1 to the sound's length. Or the unpause was pressed on the frame
of the exit: the queue holds the unpause sound's value, and the flag the pause sound's. `SideChangeEnd.Quiet` was the first case with the flag 0 or not. -/
def QuietK (sy : Syms) (ix : PauseIdx) (x m : Machine) : Prop :=
  (m.ram.get! ix.q = x.ram.get! ix.q ∧ m.ram.get! ix.b = x.ram.get! ix.b) ∨
  (m.ram.get! ix.q = x.ram.get! ix.q ∧ m.ram.get! ix.b = sy.UnpauseSfxValue.toUInt8 ∧ m.ram.get! ix.f = sy.UnpauseSfxValue.toUInt8 ∧
    1 ≤ (m.ram.get! ix.c).toNat ∧ (m.ram.get! ix.c).toNat ≤ sy.PauseSfxLength.toNat) ∨
  (m.ram.get! ix.q = sy.UnpauseSfxValue.toUInt8 ∧ m.ram.get! ix.b = x.ram.get! ix.b ∧ m.ram.get! ix.f = sy.PauseSfxValue.toUInt8)

/-- **The kinds of the pause sound at the exit**, as states of the table: the cases of `QuietK`. Silent with the flag 0, or with one bit of the flag 1; the unpause sound
with each count from 1 to the length; the unpause pressed. -/
def kinds (sy : Syms) (ix : PauseIdx) (x : Machine) : List SState :=
  let q0 := (ix.q, AB.known (x.ram.get! ix.q))
  let b0 := (ix.b, AB.known (x.ram.get! ix.b))
  let U := AB.known sy.UnpauseSfxValue.toUInt8
  ([[q0, b0, (ix.f, AB.known 0)]] ++ bitList.map fun bt => [q0, b0, (ix.f, (⟨bt, bt⟩ : AB))]) ++
    ((List.range sy.PauseSfxLength.toNat).map fun j => [q0, (ix.b, U), (ix.f, U), (ix.c, AB.known (j + 1).toUInt8)]) ++
    [[(ix.q, U), b0, (ix.f, AB.known sy.PauseSfxValue.toUInt8)]]

/-- the bytes of the exit's list that are sound bytes, other than the four of the pause sound, with the values of the reference machine -/
def soundBase (SB K : List Nat) (ix : PauseIdx) (x : Machine) : SState :=
  (SB.filter fun i => K.contains i && i != ix.q && i != ix.b && i != ix.f && i != ix.c).map fun i => (i, AB.known (x.ram.get! i))

/-- the first table: the kinds, each with the other sound bytes of the exit -/
def tableAt (sy : Syms) (SB K : List Nat) (ix : PauseIdx) (x : Machine) : List SState :=
  (kinds sy ix x).map (soundBase SB K ix x ++ ·)

/-- the bytes of the state at the exit, without the two bytes of the pause sound that `SideChangeEnd.Quiet` asked -/
def exitKnownK (nx : Names) : List Nat := SideChangeBound.bytesOf nx SideChangeEnd.exitNames

/-- the states at the exit, as `SideChangeEnd.endBase`, with the bytes of `exitKnownK` known -/
def baseK (nx : Names) (e : Machine) (A : Nat) : List AS :=
  SideChangeEnd.exitStarts (SideChangeEnd.refExit e A) (exitKnownK nx) (SideChangeEnd.adI nx "GamePauseStatus")

/-- the start states of the rows: the routine's bytes forgotten, and the timer not 000 (`dg`) -/
def startsK (R : Rt) (base : List AS) : List AS := base.map fun S => retag false ({ forgetAll R.SB S with dg := true } : AS)

/-- **the rows** -/
def rowsK (c : Ctx) (R : Rt) (nx : Names) (e : Machine) (A B : Nat) (T : List SState) : List SRow := rowsFromS c R B (startsK R (baseK nx e A)) T

/-! ## A frame from a row to the next -/

section
variable {c : Ctx} {R : Rt}

/-- a machine is in a row: a state of the row covers it, and the routine's bytes are in a state of the row's first table (`Ph`) -/
def CoveredS (c : Ctx) (R : Rt) (r : SRow) (m : Machine) : Prop := ∃ S ∈ r.row.R, Sim c.E (m.frame, 2) S m ∧ Ph R r.T0 r.T1 S m

theorem sIn_incl {T T' : List SState} (h : incl T T' = true) {t : SState} (ht : t ∈ T) {m : Machine} (hm : SIn t m) : ∃ t' ∈ T', SIn t' m := by
  obtain ⟨t', ht', he⟩ := List.any_eq_true.1 (List.all_eq_true.1 h t ht)
  exact ⟨t', ht', sIn_entails hm he⟩

/-- at the frame's end `Ph` goes over to the next row's first table -/
theorem ph_next {T0 T1 T0' T1' : List SState} {B D : AS} {m : Machine} (hp : Ph R T0 T1 B m) (hpc : B.pc = D.pc) (hsp : D.spent = false)
    (h0 : B.spent = false → incl T0 T0' = true) (h1 : B.spent = true → incl T1 T0' = true) : Ph R T0' T1' D m := by
  rcases hp with h | ⟨hs, t, ht, hm⟩ | ⟨hs, t, ht, hm⟩
  · left
    rw [← hpc]
    exact h
  · obtain ⟨t', ht', hm'⟩ := sIn_incl (h0 hs) ht hm
    exact Or.inr (Or.inl ⟨hsp, t', ht', hm'⟩)
  · obtain ⟨t', ht', hm'⟩ := sIn_incl (h1 hs) ht hm
    exact Or.inr (Or.inl ⟨hsp, t', ht', hm'⟩)

theorem normD_pc (D : List Nat) (B : AS) : (normD D B).pc = B.pc := by
  unfold normD
  split <;> rfl

theorem normD_spent (D : List Nat) (B : AS) : (normD D B).spent = B.spent := by
  unfold normD
  split <;> rfl

/-- **A frame from a row to the next.** -/
theorem link_frameS (hE : c.E.pad = AB.top) {r r' : SRow} (h : linkS c R r r' = true) {m : Machine} (hc : CoveredS c R r m) {i : UInt8}
    (hi : coreFrame c.sy c.eng m = true → noStart i = true) : CoveredS c R r' (frame m i) := by
  simp only [linkS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, _⟩, _⟩, ht0⟩, ht1⟩, h4⟩, h5⟩ := h
  obtain ⟨S, hS, hs, hp⟩ := hc
  have h1' := h1
  simp only [statesOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true] at h1'
  obtain ⟨⟨⟨⟨⟨_, _⟩, a3⟩, _⟩, _⟩, a6⟩ := h1' S hS
  have hs1 : Sim (rowCfg c r.row).E (m.frame, 2) S { m with pad := smbToPad i } := by
    show Sim (rowEnv c r.row) (m.frame, 2) S { m with pad := smbToPad i }
    unfold rowEnv
    split
    · rename_i hcore
      apply sim_pad hs
      have hcf : coreFrame c.sy c.eng (mOf S) = true := by
        rcases a6 with a6 | a6
        · rw [hcore] at a6
          cases a6
        · exact a6
      have hn := hi (core_of_known hs a3 hcf)
      have e : smbToPad i &&& 0x08 = 0 := by simpa [noStart] using hn
      show smbToPad i &&& 0x08 = 0 &&& 0x08
      rw [e]
      rfl
    · exact { hs with pad := by rw [hE]; exact TaintRun.mem_top _ }
  obtain ⟨_, B, g2, _, g4, g5⟩ := tframe_of_walk (C := rowCfg c r.row) (F := (m.frame, 2)) h4 rfl two_le ht0 ht1 (List.all_eq_true.1 h5 S hS) hs1 hp
  have g4' : Sim c.E (m.frame, 2) B (frame m i) := by
    have e4 : Sim (rowEnv c r.row) (m.frame, 2) B (frame m i) := g4
    unfold rowEnv at e4
    split at e4
    · exact sim_unpad hE e4
    · exact e4
  simp only [finS, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at g2
  obtain ⟨⟨hrk, hinc⟩, D, hD, hle⟩ := g2
  have hbase : Sim c.E ((frame m i).frame, 2) ({ B with k := 0, spent := false } : AS) (frame m i) := by
    refine { g4' with fr := ?_, rkv := ?_ }
    · show (frame m i).frame = (frame m i).frame + 0
      rfl
    · intro hr2
      have : B.rk = true := hr2
      rw [hrk] at this
      cases this
  have hps := StepWrites.le_pc_spent hle
  rw [normD_pc, normD_spent] at hps
  refine ⟨D, hD, sim_le hle (sim_normD hbase), ph_next g5 hps.1 hps.2.symm (fun h0 => ?_) (fun h1 => ?_)⟩
  · rw [h0] at hinc
    simpa using hinc
  · rw [h1] at hinc
    simpa using hinc

/-- a machine is in one of the rows -/
def InvS (c : Ctx) (R : Rt) : List SRow → Machine → Prop
  | [], _ => False
  | r :: t, m => CoveredS c R r m ∨ InvS c R t m

theorem left_of_coveredS {r : SRow} {m : Machine} (hr : statesOK c r.row = true) (h : CoveredS c R r m) : c.left m = r.row.v := by
  obtain ⟨S, hS, hs, _⟩ := h
  exact left_of_covered hr ⟨S, hS, hs⟩

/-- **A frame in the rows.** `left` is 0 already, or the machine stays in the rows and `left` falls by at most one. -/
theorem chain_stepS (hE : c.E.pad = AB.top) : ∀ (l : List SRow), chainS c R l = true → ∀ {m : Machine}, InvS c R l m → ∀ {i : UInt8},
    (coreFrame c.sy c.eng m = true → noStart i = true) → c.left m = 0 ∨ (InvS c R l (frame m i) ∧ c.left m ≤ c.left (frame m i) + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ m h
    cases h
  | cons r t ih =>
    intro hl m h i hi
    cases t with
    | nil =>
      simp only [chainS, Bool.and_eq_true, beq_iff_eq] at hl
      rcases h with h | h
      · left
        rw [left_of_coveredS hl.1 h, hl.2]
      · cases h
    | cons r2 t2 =>
      simp only [chainS, Bool.and_eq_true] at hl
      obtain ⟨h1, h2⟩ := hl
      rcases h with h | h
      · right
        have hn := link_frameS hE h1 h hi
        refine ⟨Or.inr (Or.inl hn), ?_⟩
        simp only [linkS, Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, _⟩, _⟩, _⟩ := h1
        rw [left_of_coveredS a1 h, left_of_coveredS a2 hn]
        exact a3
      · rcases ih h2 h hi with h3 | ⟨h3, h4⟩
        · exact Or.inl h3
        · exact Or.inr ⟨Or.inr h3, h4⟩

theorem states_of_chainS : ∀ (l : List SRow), chainS c R l = true → ∀ r ∈ l, statesOK c r.row = true
  | [], _, r, hr => by cases hr
  | [r0], h, r, hr => by
    simp only [chainS, Bool.and_eq_true] at h
    rw [List.mem_singleton] at hr
    rw [hr]
    exact h.1
  | r0 :: r1 :: t, h, r, hr => by
    simp only [chainS, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hr with e | hr
    · rw [e]
      simp only [linkS, Bool.and_eq_true] at h1
      obtain ⟨⟨⟨⟨⟨⟨a1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h1
      exact a1
    · exact states_of_chainS (r1 :: t) h2 r hr

/-- the rows without their tables are rows of `SideChangeEnd`: what reads the rows (`SurfaceFrames.start_of_invL`, `ControlStart.ctl_of_invL`) works on them -/
theorem invL_of_invS : ∀ {l : List SRow} {m : Machine}, InvS c R l m → InvL c (l.map (·.row)) m
  | [], _, h => by cases h
  | r :: t, m, h => by
    rcases h with ⟨S, hS, hs, _⟩ | h
    · exact Or.inl ⟨S, hS, hs⟩
    · exact Or.inr (invL_of_invS h)

/-- **Control where `left` is 0**, in rows that pass `zeroCtl` -/
theorem ctl_of_zeroS {sy : Syms} {l : List SRow} (hl : chainS c R l = true) (hz : SideChangeEnd.zeroCtl sy (l.map (·.row)) = true) {m : Machine} (h : InvS c R l m)
    (h0 : c.left m = 0) : controllable sy m = true := by
  refine SideChangeEnd.ctl_of_zero (fun r hr => ?_) hz (invL_of_invS h) h0
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
  exact states_of_chainS l hl r0 hr0

/-- the first row of the rows from `Rs` has the states `Rs` -/
theorem rowsFromS_head (n : Nat) (Rs : List AS) (T : List SState) : ∃ r t, rowsFromS c R n Rs T = r :: t ∧ r.row.R = Rs := by
  cases n with
  | zero => exact ⟨_, _, rfl, rfl⟩
  | succ n => exact ⟨_, _, rfl, rfl⟩

/-- the first table of the first row holds `T` -/
def headIncl (l : List SRow) (T : List SState) : Bool :=
  match l with
  | r :: _ => incl T r.T0
  | [] => false

/-- a machine of the first states, with the routine's bytes in a state of `T`, is in the rows -/
theorem inv_headS (n : Nat) (Rs : List AS) (T : List SState) (hh : headIncl (rowsFromS c R n Rs T) T = true) {m : Machine} {S : AS} (hS : S ∈ Rs)
    (hs : Sim c.E (m.frame, 2) S m) (hsp : S.spent = false) {t : SState} (ht : t ∈ T) (hm : SIn t m) : InvS c R (rowsFromS c R n Rs T) m := by
  obtain ⟨r, l, e, hr⟩ := rowsFromS_head (c := c) (R := R) n Rs T
  rw [e] at hh ⊢
  simp only [headIncl] at hh
  obtain ⟨t', ht', hm'⟩ := sIn_incl hh ht hm
  exact Or.inl ⟨S, by rw [hr]; exact hS, hs, Or.inr (Or.inl ⟨hsp, t', ht', hm'⟩)⟩

end


/-! ## The kinds at the exit -/

section

theorem bit_of_ne {v : UInt8} (h : v ≠ 0) : ∃ b ∈ bitList, v &&& b = b := by
  have hj : ∃ j, j < 8 ∧ TaintRun.bt v j = true := by
    apply Classical.byContradiction
    intro hno
    apply h
    apply TaintRun.bt_ext
    intro i hi
    rw [TaintRun.bt_zero hi]
    cases hc : TaintRun.bt v i with
    | true => exact absurd ⟨i, hi, hc⟩ hno
    | false => rfl
  obtain ⟨j, hj8, hjb⟩ := hj
  obtain ⟨b, hbm, hbb⟩ := TaintRun.bit_list ⟨j, hj8⟩
  refine ⟨b, hbm, TaintRun.bt_ext fun i hi => ?_⟩
  rw [TaintRun.bt_and, hbb ⟨i, hi⟩]
  by_cases hij : i = j
  · subst hij
    simp [hjb]
  · simp [hij]

theorem mem_eq {w v : UInt8} (h : w = v) : (AB.known v).mem w := by
  rw [h]
  exact TaintRun.mem_known_self v

theorem bit_self : ∀ b ∈ bitList, b &&& b = b := by decide

theorem sIn_append {a b : SState} {m : Machine} (h1 : SIn a m) (h2 : SIn b m) : SIn (a ++ b) m := fun p hp =>
  (List.mem_append.1 hp).elim (h1 p) (h2 p)

/-- **A machine with `QuietK` has the bytes of one of the kinds.** -/
theorem kinds_of_quiet {sy : Syms} {ix : PauseIdx} {x m : Machine} (h : QuietK sy ix x m) : ∃ kd ∈ kinds sy ix x, SIn kd m := by
  unfold kinds
  rcases h with ⟨hq, hb⟩ | ⟨hq, hb, hf, hc1, hc2⟩ | ⟨hq, hb, hf⟩
  · by_cases h0 : m.ram.get! ix.f = 0
    · refine ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl List.mem_cons_self))))), ?_⟩
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_eq hq
      · exact mem_eq hb
      · exact mem_eq h0
    · obtain ⟨bt, hbt, hv⟩ := bit_of_ne h0
      refine ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨bt, hbt, rfl⟩)))))), ?_⟩
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_eq hq
      · exact mem_eq hb
      · show m.ram.get! ix.f &&& bt = bt &&& bt
        rw [hv, bit_self bt hbt]
  · refine ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨(m.ram.get! ix.c).toNat - 1, List.mem_range.2 (by omega), rfl⟩)))), ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_eq hq
    · exact mem_eq hb
    · exact mem_eq hf
    · refine mem_eq ?_
      have e : (m.ram.get! ix.c).toNat - 1 + 1 = (m.ram.get! ix.c).toNat := by omega
      rw [e]
      exact (UInt8.ofNat_toNat).symm
  · refine ⟨_, List.mem_append.2 (Or.inr List.mem_cons_self), ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact mem_eq hq
    · exact mem_eq hb
    · exact mem_eq hf

/-- **`Quiet` gives `QuietK`**: the old condition at the exit is the first case of the new one -/
theorem quietK_of_quiet {sy : Syms} {nx : Names} {e : Machine} {A : Nat} {m : Machine} (h : SideChangeEnd.Quiet (SideChangeEnd.quietBytes nx e A) m) :
    QuietK sy (pauseIdx nx) (SideChangeEnd.refExit e A) m := by
  have key : ∀ n, n ∈ ["PauseSoundBuffer", "PauseSoundQueue"] →
      m.ram.get! (SideChangeEnd.adI nx n) = (SideChangeEnd.refExit e A).ram.get! (SideChangeEnd.adI nx n) := by
    intro n hn
    refine h (SideChangeEnd.adI nx n, (SideChangeEnd.refExit e A).ram.get! (SideChangeEnd.adI nx n)) (List.mem_map.2 ⟨SideChangeEnd.adI nx n, ?_, rfl⟩)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl <;> simp [SideChangeBound.bytesOf, SideChangeEnd.quietNames, SideChangeEnd.adI, UInt16.toNat_and]
  exact Or.inl ⟨key _ (by simp), key _ (by simp)⟩

end

/-! ## The statement for the side pipe -/

section
open SideChangeBound (Entry During leftAt sideEnv refsOf startsOf keepOf exitBytes tableFrom leftCheck startsOK Statement)
open SideChangeEnd (Entry2 During2 refs2 refExit exitSplits keep2 duringLe duringCheck TimerOK Paused pauseCheck notPausedRows digitsOf adI timeEnv)
open TaintRun (ExitAt)

/-- the first table of the side pipe's rows -/
abbrev tableOf (sy : Syms) (nx : Names) (e : Machine) (A : Nat) (R : Rt) : List SState := tableAt sy R.SB (exitKnownK nx) (pauseIdx nx) (refExit e A)

/-- the context of the side pipe's rows -/
abbrev ctxOf (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) : Ctx := soundCtx sy nm nx e A B R.SB

/-- **the side pipe's rows** -/
abbrev rowsOf (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) : List SRow :=
  rowsK (ctxOf sy nm nx e A B R) R nx e A B (tableOf sy nx e A R)

/-- a machine is in the side pipe's rows -/
def InRowsK (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) (m : Machine) : Prop :=
  InvS (ctxOf sy nm nx e A B R) R (rowsOf sy nm nx e A B R) m

/-- **the whole check on the ROM**: the pipe's frames up to the exit, the state at the exit, the rows, control where `left` is 0, no paused state in the rows, the paused
frames of the pipe -/
def endCheckL (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) (l : List SRow) : Bool :=
  let x := refExit e A
  let base := baseK nx e A
  let rows := l.map (·.row)
  startsOK (refs2 nm nx e) && duringLe nm nx e && decide (2 ≤ A) && decide (0 < B) &&
    base.all (fun S => !S.dg && StepWrites.soundLe S (soundBase R.SB (exitKnownK nx) (pauseIdx nx) x)) &&
    duringCheck (sideEnv nm e) (exitSplits nm nx e) sy (keepOf nm) (keep2 nm nx) (startsOf (refs2 nm nx e)) base [] (exitBytes sy nm x) &&
    leftCheck (sideEnv nm e) sy nm sy.EngSidePipe (tableFrom sy nm B x) B (startsOf (refsOf nm e)) x &&
    pauseCheck sy nm nx e &&
    headIncl l (tableOf sy nx e A R) && chainS (ctxOf sy nm nx e A B R) R l && SideChangeEnd.zeroCtl sy rows && notPausedRows (adI nx "GamePauseStatus") rows &&
    (peek x sy.OperMode_Task).toUInt16 != sy.Task_GameCore

/-- the check with the side pipe's rows -/
def endCheckK (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) : Bool := endCheckL sy nm nx e A B R (rowsOf sy nm nx e A B R)

/-- **The statement.** As `SideChangeEnd.EndStatement`, with the rows of this file: a frame that leaves the pipe with `QuietK` and the timer not 000 at the exit is in the rows -/
structure EndStatementK (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) : Prop where
  /-- the condition here gives the condition of `SideChangeBound` -/
  entry : ∀ M, Entry2 nm nx e A M → Entry nm e A M
  /-- an entry is in the state during the pipe -/
  during : ∀ M, Entry2 nm nx e A M → During2 nm nx e M
  /-- this state is the state during the pipe of `SideChangeBound` -/
  toDuring : ∀ m, During2 nm nx e m → During nm e m
  /-- one frame of the pipe, for any input. A frame that leaves the pipe has the exit's bytes; with the pause sound as `QuietK` says and the timer not 000, it is in the rows -/
  step : ∀ m, During2 nm nx e m → ∀ i, During2 nm nx e (frame m i) ∨
    (ExitAt (exitBytes sy nm (refExit e A)) (frame m i) ∧ (QuietK sy (pauseIdx nx) (refExit e A) (frame m i) → TimerOK nx (frame m i) → InRowsK sy nm nx e A B R (frame m i)))
  /-- a frame in the rows: `left` is 0 already, or the machine stays in the rows and `left` falls by at most one -/
  rows : ∀ m, InRowsK sy nm nx e A B R m → ∀ i, (coreFrame sy sy.EngSidePipe m = true → noStart i = true) →
    leftAt sy nm e A B m = 0 ∨ (InRowsK sy nm nx e A B R (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i) + 1)
  /-- in the rows, `left` is 0 only with control -/
  zero : ∀ m, InRowsK sy nm nx e A B R m → leftAt sy nm e A B m = 0 → controllable sy m = true
  /-- `left` is not 0 during the pipe -/
  duringLeft : ∀ m, During2 nm nx e m → leftAt sy nm e A B m ≠ 0
  /-- a frame of the pipe that ends paused takes nothing off `left` -/
  pauseKeeps : ∀ m, During2 nm nx e m → ∀ i, Paused nx (frame m i) → During2 nm nx e (frame m i) → leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i)
  /-- no machine of the rows is paused -/
  rowsNotPaused : ∀ m, InRowsK sy nm nx e A B R m → ¬ Paused nx m
  /-- a machine with the bytes of the exit has no control: the reference machine at the exit is not in the game core -/
  exitOff : ∀ m, ExitAt (exitBytes sy nm (refExit e A)) m → controllable sy m = false

theorem endStatementK_of_check {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} {R : Rt} (h : endCheckK sy nm nx e A B R = true) :
    EndStatementK sy nm nx e A B R := by
  simp only [endCheckK, endCheckL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h6⟩, hB⟩, hb⟩, h7⟩, hl⟩, hp⟩, hh⟩, hc⟩, hz⟩, hn⟩, hx⟩ := h
  have hD := SideChangeEnd.duringOK_of_check h7
  have hL := SideChangeBound.leftOK_of_check hl
  have hE2 : (sideEnv nm e).pad = TaintRun.AB.top := rfl
  have hE : (ctxOf sy nm nx e A B R).E.pad = TaintRun.AB.top := rfl
  refine ⟨?_, fun M hM => SideChangeBound.inv_of_entry h1 hE2 h6 hM, fun m hm => SideChangeEnd.during_le h2 hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M hM
    refine ⟨hM.dot, hM.flags, hM.s0, hM.ctrl, hM.strobe, hM.halted, hM.trk, hM.prg, hM.mask, hM.size, ?_, hM.timer⟩
    obtain ⟨v, hv, a1, a2, a3⟩ := hM.ref
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.1 hv
    exact ⟨v0, hv0, a1, a2, fun i hi => a3 i (List.mem_append_left _ hi)⟩
  · intro m hm i
    rcases SideChangeEnd.during_step hD hE2 hm i with g | ⟨_, g1, g2⟩
    · exact Or.inl g
    · refine Or.inr ⟨g1, fun hq ht => ?_⟩
      obtain ⟨D, hD1, hs⟩ := g2 (fun q hq => by cases hq)
      have hbD := hb D hD1
      have hs2 : Sim (timeEnv nm nx e) ((frame m i).frame, 2) D (frame m i) :=
        SideChangeEnd.sim_splits' (l := exitSplits nm nx e) (SideChangeEnd.sim_D (D := digitsOf nx) hs hbD.1)
      have hdg : (timeEnv nm nx e).D.any (fun j => (frame m i).ram.get! j != 0) = true := by
        obtain ⟨j, hj, hne⟩ := ht
        exact List.any_eq_true.2 ⟨j, hj, by simpa using hne⟩
      have hs3 : Sim (timeEnv nm nx e) ((frame m i).frame, 2) (retag false ({ forgetAll R.SB D with dg := true } : AS)) (frame m i) :=
        StepWrites.sim_retag false { StepWrites.sim_forgetAll R.SB hs2 with dg := fun _ => hdg }
      obtain ⟨kd, hkd, hkm⟩ := kinds_of_quiet hq
      exact inv_headS B _ _ hh (List.mem_map.2 ⟨D, hD1, rfl⟩) hs3 rfl (List.mem_map.2 ⟨kd, hkd, rfl⟩) (sIn_append (StepWrites.sIn_of_le hs hbD.2) hkm)
  · intro m hm i hi
    exact chain_stepS hE _ hc hm hi
  · intro m hm h0
    exact ctl_of_zeroS hc hz hm h0
  · intro m hm
    have h0 := SideChangeBound.left_of_inv hL (SideChangeEnd.during_le h2 hm)
    show PipeChangeBound.leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B m ≠ 0
    rw [h0]
    omega
  · intro m hm i hpz hm'
    have e1 := SideChangeBound.left_of_inv hL (SideChangeEnd.during_le h2 hm)
    have e2 := SideChangeBound.left_of_inv hL (SideChangeEnd.during_le h2 hm')
    show PipeChangeBound.leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B m ≤ PipeChangeBound.leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B (frame m i)
    rw [e1, e2]
    have := SideChangeEnd.pause_keeps hp hm i hpz hm'
    omega
  · intro m hm hP
    exact SideChangeEnd.not_paused_rows hn (invL_of_invS hm) hP
  · intro m hm
    have e1 : peek m sy.OperMode_Task = peek (refExit e A) sy.OperMode_Task :=
      hm ((sy.OperMode_Task &&& 0x7FF).toNat, peek (refExit e A) sy.OperMode_Task) (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
    simp only [bne_iff_ne, ne_eq] at hx
    cases hc2 : controllable sy m with
    | false => rfl
    | true =>
      exfalso
      simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc2
      rw [e1] at hc2
      exact hx hc2.1.2

end

/-! ## A run -/

section
open SideChangeBound (Statement leftAt exitBytes)
open SideChangeEnd (Entry2 During2 refExit TimerOK Paused)
open TaintRun (ExitAt)

/-- **The change of a run.** The fields of `SideChangeEnd.EndRun`, with `QuietK` in place of `Quiet` and the timer at the exit (`TimerOK`). -/
structure EndRunK (sy : Syms) (nm nx : Names) (e : Machine) (A : Nat) where
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (inp n)
  lag : Nat → Prop
  dec : DecidablePred lag
  cnt : Nat → Nat
  hcnt : ∀ n, cnt (n + 1) = cnt n + (@ite _ (lag n) (dec n) 0 1)
  a : Nat
  b : Nat
  order : a ≤ b
  /-- the condition on the state at the entry -/
  entry : Entry2 nm nx e A (seq a)
  /-- control at `b` -/
  atCtl : controllable sy (seq b) = true
  /-- a lag frame ends paused -/
  lagPaused : ∀ n, a ≤ n → n < b → lag n → Paused nx (seq (n + 1))
  /-- no Start on the frames of the game core after the pipe -/
  noStart : ∀ n, a ≤ n → n < b → coreFrame sy sy.EngSidePipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- at the exit, the pause sound is one of the kinds -/
  quiet : ∀ n, a ≤ n → n ≤ b → ExitAt (exitBytes sy nm (refExit e A)) (seq n) → QuietK sy (pauseIdx nx) (refExit e A) (seq n)
  /-- at the exit, the game timer is not 000 -/
  time : ∀ n, a ≤ n → n ≤ b → ExitAt (exitBytes sy nm (refExit e A)) (seq n) → TimerOK nx (seq n)

variable {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} {R : Rt} {es : List Machine}

/-- during the pipe or in the rows -/
def StK (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) (m : Machine) : Prop := During2 nm nx e m ∨ InRowsK sy nm nx e A B R m

/-- one frame -/
theorem st_stepK (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) {m : Machine} {i : UInt8} (h : StK sy nm nx e A B R m)
    (hi : coreFrame sy sy.EngSidePipe m = true → noStart i = true)
    (hq : ExitAt (exitBytes sy nm (refExit e A)) (frame m i) → QuietK sy (pauseIdx nx) (refExit e A) (frame m i) ∧ TimerOK nx (frame m i)) :
    leftAt sy nm e A B m = 0 ∨ (StK sy nm nx e A B R (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i) + 1) := by
  rcases h with h | h
  · right
    refine ⟨?_, S.fall _ (T.toDuring _ h) _⟩
    rcases T.step m h i with g | ⟨g1, g2⟩
    · exact Or.inl g
    · exact Or.inr (g2 (hq g1).1 (hq g1).2)
  · rcases T.rows m h i hi with g | ⟨g1, g2⟩
    · exact Or.inl g
    · exact Or.inr ⟨Or.inr g1, g2⟩

/-- one frame that ends paused: it takes nothing off `left` -/
theorem st_step_pausedK (T : EndStatementK sy nm nx e A B R) {m : Machine} {i : UInt8} (h : StK sy nm nx e A B R m)
    (hi : coreFrame sy sy.EngSidePipe m = true → noStart i = true)
    (hq : ExitAt (exitBytes sy nm (refExit e A)) (frame m i) → QuietK sy (pauseIdx nx) (refExit e A) (frame m i) ∧ TimerOK nx (frame m i))
    (hp : Paused nx (frame m i)) :
    leftAt sy nm e A B m = 0 ∨ (StK sy nm nx e A B R (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i)) := by
  rcases h with h | h
  · rcases T.step m h i with g | ⟨g1, g2⟩
    · exact Or.inr ⟨Or.inl g, T.pauseKeeps m h i hp g⟩
    · exact absurd hp (T.rowsNotPaused _ (g2 (hq g1).1 (hq g1).2))
  · rcases T.rows m h i hi with g | ⟨g1, _⟩
    · exact Or.inl g
    · exact absurd hp (T.rowsNotPaused _ g1)

theorem EndRunK.cnt_mono (R' : EndRunK sy nm nx e A) (n : Nat) : R'.cnt n ≤ R'.cnt (n + 1) := by
  rw [R'.hcnt n]
  omega

/-- the exit's conditions of a run, on the frame after `n` -/
theorem EndRunK.exitAt (R' : EndRunK sy nm nx e A) {n : Nat} (h1 : R'.a ≤ n) (h2 : n < R'.b) :
    ExitAt (exitBytes sy nm (refExit e A)) (frame (R'.seq n) (R'.inp n)) →
      QuietK sy (pauseIdx nx) (refExit e A) (frame (R'.seq n) (R'.inp n)) ∧ TimerOK nx (frame (R'.seq n) (R'.inp n)) := by
  intro hx
  rw [← R'.next n] at hx ⊢
  exact ⟨R'.quiet _ (by omega) (by omega) hx, R'.time _ (by omega) (by omega) hx⟩

/-- **The bound on the change**: `change₂` of `Route`, with `A + B = 282`. -/
theorem EndRunK.bound (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (R' : EndRunK sy nm nx e A) : R'.cnt R'.a + (A + B) ≤ R'.cnt R'.b := by
  have key : ∀ d, R'.a + d ≤ R'.b → R'.cnt R'.a + (A + B) ≤ R'.cnt (R'.a + d) ∨
      (StK sy nm nx e A B R (R'.seq (R'.a + d)) ∧ R'.cnt R'.a + (A + B) ≤ R'.cnt (R'.a + d) + leftAt sy nm e A B (R'.seq (R'.a + d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      right
      refine ⟨Or.inl (T.during _ R'.entry), ?_⟩
      have := S.atEntry _ (T.entry _ R'.entry)
      simp only [Nat.add_zero]
      omega
    | succ d ih =>
      intro hd
      have e1 : R'.a + (d + 1) = R'.a + d + 1 := rfl
      rw [e1]
      have hn := R'.next (R'.a + d)
      rcases ih (by omega) with h | ⟨h1, h2⟩
      · left
        have := R'.cnt_mono (R'.a + d)
        omega
      · have hi := R'.noStart (R'.a + d) (by omega) (by omega)
        have hq := R'.exitAt (n := R'.a + d) (by omega) (by omega)
        have hc := R'.hcnt (R'.a + d)
        by_cases hl : R'.lag (R'.a + d)
        · rw [@if_pos _ (R'.dec _) hl] at hc
          have hp := R'.lagPaused (R'.a + d) (by omega) (by omega) hl
          rw [hn] at hp
          rcases st_step_pausedK T h1 hi hq hp with g | ⟨g1, g2⟩
          · left
            omega
          · right
            rw [hn]
            exact ⟨g1, by omega⟩
        · rw [@if_neg _ (R'.dec _) hl] at hc
          rcases st_stepK S T h1 hi hq with g | ⟨g1, g2⟩
          · left
            omega
          · right
            rw [hn]
            exact ⟨g1, by omega⟩
  have hb := R'.order
  have e2 : R'.a + (R'.b - R'.a) = R'.b := by omega
  rcases key (R'.b - R'.a) (by omega) with h | ⟨_, h⟩
  · rw [e2] at h
    exact h
  · rw [e2, S.atControl _ R'.atCtl] at h
    omega

/-- **Each machine from the entry up to the first control is in the pipe's frames or in the rows**, when `b` is the first control after the entry -/
theorem EndRunK.way (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (R' : EndRunK sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : ∀ d, R'.a + d ≤ R'.b → StK sy nm nx e A B R (R'.seq (R'.a + d)) := by
  intro d
  induction d with
  | zero => exact fun _ => Or.inl (T.during _ R'.entry)
  | succ d ih =>
    intro hd
    have e1 : R'.a + (d + 1) = R'.a + d + 1 := rfl
    rw [e1, R'.next (R'.a + d)]
    rcases st_stepK S T (ih (by omega)) (R'.noStart (R'.a + d) (by omega) (by omega)) (R'.exitAt (n := R'.a + d) (by omega) (by omega)) with g | ⟨g1, _⟩
    · rcases ih (by omega) with h | h
      · exact absurd g (T.duringLeft _ h)
      · have := T.zero _ h g
        rw [hc _ (by omega) (by omega)] at this
        cases this
    · exact g1

/-- **`left` is not 0 before control**, on a run of the change, if `b` is the first control after the entry -/
theorem EndRunK.first (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (R' : EndRunK sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : ∀ n, R'.a ≤ n → n < R'.b → leftAt sy nm e A B (R'.seq n) ≠ 0 := by
  intro n h1 h2 h0
  obtain ⟨d, rfl⟩ : ∃ d, n = R'.a + d := ⟨n - R'.a, by omega⟩
  rcases EndRunK.way S T R' hc d (by omega) with h | h
  · exact T.duringLeft _ h h0
  · have := T.zero _ h h0
    rw [hc _ h1 h2] at this
    cases this

/-- **The machine at control is in the rows**, if `b` is the first control after the entry -/
theorem EndRunK.inRows (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (R' : EndRunK sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : InRowsK sy nm nx e A B R (R'.seq R'.b) := by
  have hb := R'.order
  have e2 : R'.a + (R'.b - R'.a) = R'.b := by omega
  have h := EndRunK.way S T R' hc (R'.b - R'.a) (by omega)
  rw [e2] at h
  rcases h with h | h
  · exact absurd (S.atControl _ R'.atCtl) (T.duringLeft _ h)
  · exact h

/-- **The last frame before control is in the rows, with `left` 1**, if `b` is the first control after the entry. This is what `HurryStart` reads from the rows. -/
theorem EndRunK.last (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (R' : EndRunK sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    R'.a + 1 ≤ R'.b ∧ InvL (ctxOf sy nm nx e A B R) ((rowsOf sy nm nx e A B R).map (·.row)) (R'.seq (R'.b - 1)) ∧
      leftAt sy nm e A B (R'.seq (R'.b - 1)) = 1 := by
  have h0 := S.atControl _ R'.atCtl
  have hab : R'.a + 1 ≤ R'.b := by
    refine Nat.lt_of_le_of_ne R'.order fun heq => ?_
    have hd := T.duringLeft _ (T.during _ R'.entry)
    rw [heq] at hd
    exact hd h0
  have e1 : R'.a + (R'.b - 1 - R'.a) = R'.b - 1 := by omega
  have hw := EndRunK.way S T R' hc (R'.b - 1 - R'.a) (by omega)
  rw [e1] at hw
  have hn := R'.next (R'.b - 1)
  rw [show R'.b - 1 + 1 = R'.b by omega] at hn
  have hf1 := EndRunK.first S T R' hc (R'.b - 1) (by omega) (by omega)
  rcases hw with h | h
  · exfalso
    rcases T.step _ h (R'.inp (R'.b - 1)) with g | ⟨g1, _⟩
    · rw [← hn] at g
      exact T.duringLeft _ g h0
    · rw [← hn] at g1
      have := T.exitOff _ g1
      rw [R'.atCtl] at this
      cases this
  · rcases T.rows _ h (R'.inp (R'.b - 1)) (R'.noStart _ (by omega) (by omega)) with g | ⟨g1, g2⟩
    · exact absurd g hf1
    · rw [← hn, h0] at g2
      exact ⟨hab, invL_of_invS h, by omega⟩

end

/-! ## What reads the rows: the state at control -/

section
open SideChangeBound (Statement)
variable {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} {R : Rt} {es : List Machine}

/-- the check on the ROM: in every state of the rows with control, the state of `c` (as `SurfaceFrames.startCheck` on the rows of `SideChangeEnd`) -/
def startCheckK (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) (c : PoleJoin.Box) : Bool :=
  SurfaceFrames.rowsStart sy c.m ((rowsOf sy nm nx e A B R).map (·.row))

/-- the check on the ROM: the entry has the program of `m0`, and every state of the rows with control is as `FrameKeep` needs it (as `ControlStart.ctlCheck`) -/
def ctlCheckK (sy : Syms) (m0 : Machine) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) : Bool :=
  decide (e.prg = m0.prg) && decide (e.prgMask = m0.prgMask) && ControlStart.rowsCtl sy (FrameKeep.guardK sy m0) ((rowsOf sy nm nx e A B R).map (·.row))

/-- **the checks on the ROM of the rows, with the rows made once**: `endCheckK`, `startCheckK`, `ctlCheckK` -/
def sideCheckK (sy : Syms) (m0 : Machine) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) (c : PoleJoin.Box) : Bool :=
  let l := rowsOf sy nm nx e A B R
  endCheckL sy nm nx e A B R l && SurfaceFrames.rowsStart sy c.m (l.map (·.row)) &&
    (decide (e.prg = m0.prg) && decide (e.prgMask = m0.prgMask) && ControlStart.rowsCtl sy (FrameKeep.guardK sy m0) (l.map (·.row)))

theorem sideCheckK_parts {m0 : Machine} {c : PoleJoin.Box} (h : sideCheckK sy m0 nm nx e A B R c = true) :
    endCheckK sy nm nx e A B R = true ∧ startCheckK sy nm nx e A B R c = true ∧ ctlCheckK sy m0 nm nx e A B R = true := by
  simp only [sideCheckK, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_⟩
  · unfold endCheckK
    exact h.1.1
  · unfold startCheckK
    exact h.1.2
  · unfold ctlCheckK
    simp only [Bool.and_eq_true]
    exact h.2

/-- **The state at control, on a real run**, from the rows of this file -/
theorem EndRunK.start {c : PoleJoin.Box} (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (hk : startCheckK sy nm nx e A B R c = true)
    (R' : EndRunK sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : SurfaceFrames.Start sy c (R'.seq R'.b) := by
  unfold startCheckK at hk
  exact SurfaceFrames.start_of_invL hk (invL_of_invS (EndRunK.inRows S T R' hc)) R'.atCtl

/-- **The machine at control is as `FrameKeep` needs it**, on a real run, from the rows of this file -/
theorem EndRunK.atCtl' {m0 : Machine} (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (hk : ctlCheckK sy m0 nm nx e A B R = true)
    (R' : EndRunK sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : FrameKeep.AtCtl sy m0 (R'.seq R'.b) := by
  simp only [ctlCheckK, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨hp, hmk⟩, h0⟩ := hk
  exact ControlStart.ctl_of_invL hp hmk h0 (invL_of_invS (EndRunK.inRows S T R' hc)) R'.atCtl

end

end Smbrta.SideChangeSound
