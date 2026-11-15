import Theorems.RoomMusic

/-!
# The level's number from the vertical pipe's entry to the side pipe's entry

`entry₂` of the route asked that the level's number (`AreaNumber`) at the side pipe's entry is that of a reference. Only the code of a level's end, of a warp and of the
title stores to it (read from the disassembly), but the walks of the first change and of the room did not know it: in round 14 the vertical pipe's entry (`PipeChangeEnd.Entry`) and
its exit did not list it (since round 15 the entry lists it, and `Run.area₁` is a theorem; the exit still does not). Here three walks carry it, each a copy of a walk of the route with the byte known in its start states:

* the vertical pipe's frames: the walk `zcheck` of `PipeChangeEnd` from the start states of the entry with the byte known, asked to end in the states at the exit with the
  byte known (`pipeCheckA`);
* the last frames of the change, from the exit to the room's first control: the rows with tables of `PipeChangeEnd` from the states at the exit with the byte known; every
  state of every row knows it (`rowsCheckA`). They have as many rows and states as part b's rows (44 rows, 1,906 states);
* the room's frames: the walk of `RoomPause` with the byte in a table of one state (`roomCheckA`).

So the byte has the entry's value at the side pipe's entry if it has it at the vertical pipe's entry (`PipeRunK.areaB`, `area_run`). Part b's runs give the order of the
frames and the conditions at the exit; the walks here give the byte.

There is no game data in this file. Page: `1-1/d-2-5-3-AreaKeep.md`.
-/

namespace Smbrta.AreaKeep

open TaintRun
open PipeTransition (frame)
open PipeTransitionAll (Names)
open PipeEntryRule (trace)
open PipeChangeEnd (Data envOf startsP baseK pauseI refX During DuringV InRowsK EndStatement PipeRunK leftP exitQ zcfgOf zcheck ZCfg ZOK rtc ctxK timeCtx
  timeEnv tableP grpP pauseIx afterF soundBaseP QuietP SongAt Entry)
open ScreenPage (Places SiteOK RoomCond placesR envR refR knownOf Room)
open StepWrites (SState SIn)

/-! ## The byte -/

/-- the level's number, as a RAM index -/
def areaI (nm : Names) : Nat := RoomMusic.ix nm "AreaNumber"

/-- the state knows the byte `i` with the value `v` -/
def setA (i : Nat) (v : UInt8) (S : AS) : AS := S.setK i (AB.known v)

/-! ## The vertical pipe's frames -/

/-- the start states of the pipe's walk, with the byte known as in the entry `e` -/
def startsA (d : Data) (e : Machine) (i : Nat) : List AS := (startsP d e).map (setA i (e.ram.get! i))

/-- the states at the exit, with the byte known as in the entry `e` -/
def baseA (d : Data) (e : Machine) (i : Nat) : List AS := (baseK d e).map (setA i (e.ram.get! i))

/-- the two tables of the pipe's walk from these start states: the counter followed, and the counter at 1 -/
def cfgRa (d : Data) (e : Machine) (i : Nat) : ZCfg := zcfgOf d.places d.jump (envOf d e) d.ckeys d.keep [(pauseI d, 1)] d.hints (startsA d e i)
def cfgOa (d : Data) (e : Machine) (i : Nat) : ZCfg :=
  zcfgOf d.places d.jump (envOf d e) d.ckeys (pauseI d :: d.keep) [(pauseI d, 1)] d.hints ((startsA d e i).map (toOne (envOf d e)))

/-- **The check of the pipe's frames with the byte**: the walk of `PipeChangeEnd.zcheck` from `startsA`, ending in `baseA`; and every start state, also with the counter
at 1, knows that the pipe's routine runs in the game core -/
def pipeCheckA (sy : Syms) (nm : Names) (d : Data) (e : Machine) (i : Nat) : Bool :=
  (startsA d e i).all (SideChangeBound.pipeOK sy sy.EngVerticalPipe) && ((startsA d e i).map (toOne (envOf d e))).all (SideChangeBound.pipeOK sy sy.EngVerticalPipe) &&
    zcheck (cfgRa d e i) (cfgOa d e i) (envOf d e) (pauseI d) (startsA d e i) (baseA d e i) [] (SideChangeBound.exitBytes sy nm (refX e))

/-! ## The last frames of the change -/

/-- the start states of the rows: those of `PipeChangeEnd.startsK`, from the states at the exit with the byte -/
def startsKA (R : StepWrites.Rt) (d : Data) (e : Machine) (i : Nat) : List AS :=
  ((baseA d e i).flatMap fun S => d.xshape.map fun r => SideChangeEnd.refine r S).map fun S =>
    StepWrites.retag false ({ StepWrites.forgetAll R.SB S with dg := true } : AS)

/-- **the rows with tables from the exit with the byte**: those of `PipeChangeEnd.rowsKc` from `startsKA` -/
def rowsA (c : SideChangeEnd.Ctx) (d : Data) (e : Machine) (i : Nat) : List SoundRows.SRow :=
  SoundRows.rowsFromS (ctxK c d e) (rtc c d e) (grpP (pauseIx d.nx)) afterF (startsKA (rtc c d e) d e i) (tableP c.sy (rtc c d e) d (refX e))

/-- a machine is in these rows -/
def InRowsA (sy : Syms) (nm : Names) (d : Data) (e : Machine) (i : Nat) (m : Machine) : Prop :=
  SoundRows.InvS (ctxK (timeCtx sy nm d e) d e) (rtc (timeCtx sy nm d e) d e) (rowsA (timeCtx sy nm d e) d e i) m

/-- every state of every row knows the byte `i` with the value `v` -/
def knowsRows (i : Nat) (v : UInt8) (l : List SoundRows.SRow) : Bool := l.all fun r => r.row.R.all fun S => knownIs S (i, v)

/-- **The check of the rows with the byte**: the states at the exit know the sound's bytes of the first table, the first row's table is under the first table, a frame
goes from a row to the next, and every state of every row knows the byte with the entry's value -/
def rowsCheckA (sy : Syms) (nm : Names) (d : Data) (e : Machine) (i : Nat) : Bool :=
  let c := timeCtx sy nm d e
  let R := rtc c d e
  let l := rowsA c d e i
  (baseA d e i).all (fun S => !S.dg && StepWrites.soundLe S (soundBaseP R d (refX e))) && SoundRows.headIncl l (tableP c.sy R d (refX e)) &&
    SoundRows.chainS (ctxK c d e) R l && knowsRows i (e.ram.get! i) l

/-! ## The room's frames -/

/-- **the region and the table**: the region of `RoomPause` (the sound routine, the pads, the pause routine), the byte, and a table of one state: the byte with the
value `v` -/
def regA (sy : Syms) (m0 : Machine) (nm : Names) (i : Nat) (v : UInt8) : RoomPause.Reg :=
  let call := ScreenPage.findJsr m0 sy.NonMaskableInterrupt sy.SoundEngine 256
  { call, ret := call + 9, SB := [i], gI := RoomMusic.ix nm "GamePauseStatus", T := [[(i, AB.known v)]], keepB := [], needG := false }

/-- the configuration of the room's walk with the byte -/
abbrev cfgA (sy : Syms) (nm : Names) (m0 : Machine) (i : Nat) (v : UInt8) : ScreenPage.CfgS :=
  RoomPause.cfgOfP (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (regA sy m0 nm i v) (refR m0) (knownOf nm)

/-- **The check of the room's frames with the byte** -/
def roomCheckA (sy : Syms) (nm : Names) (m0 : Machine) (i : Nat) (v : UInt8) : Bool :=
  RoomPause.walkCheck (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (regA sy m0 nm i v) (refR m0) (knownOf nm)

/-! ## The small checks -/

/-- **The small checks**: the byte is in RAM, it is a byte of the 11 of `RoomMusic.restIdxM` and not the routine's; the reference at the exit is not in the game core
(so a machine at the exit is not in the pipe's routine); each reference of the side pipe's entry that lists the byte has the vertical pipe's entry's value -/
def smallCheck (sy : Syms) (e : Machine) (V : List (Machine × List Nat)) (nmS : Names) (m0 : Machine) : Bool :=
  let i := areaI nmS
  decide (i < 2048) && (RoomMusic.restIdxM nmS).contains i && i != (placesR sy nmS m0).rtI &&
    (peek (refX e) sy.OperMode_Task).toUInt16 != sy.Task_GameCore &&
    V.all fun v => !v.2.contains i || v.1.ram.get! i == e.ram.get! i

/-! ## The proofs: the pipe's frames -/

section
variable {sy : Syms} {nm : Names} {d : Data} {e : Machine} {es : List Machine} {i : Nat}

/-- what the check of the pipe's frames gives: the walk, and the pipe's routine at its start states -/
theorem zok_of_check (h : pipeCheckA sy nm d e i = true) :
    ZOK (cfgRa d e i) (cfgOa d e i) (envOf d e) (pauseI d) (startsA d e i) (baseA d e i) [] (SideChangeBound.exitBytes sy nm (refX e)) ∧
      (∀ S ∈ startsA d e i, SideChangeBound.pipeOK sy sy.EngVerticalPipe S = true) ∧
      (∀ S ∈ startsA d e i, SideChangeBound.pipeOK sy sy.EngVerticalPipe (toOne (envOf d e) S) = true) := by
  simp only [pipeCheckA, zcheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.not_eq_true', List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨p1, p2⟩, ⟨⟨⟨⟨⟨z1, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩⟩ := h
  refine ⟨⟨z1, rfl, rfl, rfl, rfl, rfl, fun S hS => ?_, z3, z4, z5, z6⟩, p1, p2⟩
  have := z2 S hS
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- a state that knows the byte with the machine's value -/
theorem sim_setA {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) {v : UInt8} (hv : m.ram.get! i = v) : Sim E F (setA i v S) m :=
  SideChangeEnd.sim_refine hs (SidePause.mem_known_of_eq hv)

/-- **The entry is in the pipe's walk with the byte**: the entry is in the state during the pipe (`EndStatement.during`), with the counter at least its first value,
and the byte has the entry's value -/
theorem duringA_of_entry (T : EndStatement sy nm d e es) {M : Machine} (hM : Entry d e M) (hv : M.ram.get! i = e.ram.get! i) :
    InvAt (envOf d e) (startsA d e i) M := by
  obtain ⟨S, hS, hc⟩ := T.during M hM
  refine ⟨setA i (e.ram.get! i) S, List.mem_map.2 ⟨S, hS, rfl⟩, ?_⟩
  rcases hc with ⟨c1, c2⟩ | ⟨c1, _⟩
  · exact Or.inl ⟨c1, sim_setA c2 hv⟩
  · exfalso
    have a1 := hM.1.timer
    have a2 : (tm (envOf d e) M) = M.ram.get! (envOf d e).rkI := rfl
    rw [a2] at c1
    rw [c1] at a1
    exact absurd a1 (by decide)

/-- a machine of the pipe's walk with the byte is in the pipe's routine -/
theorem inPipe_of_A (h : pipeCheckA sy nm d e i = true) {m : Machine} (hm : InvAt (envOf d e) (startsA d e i) m) :
    PipeChangeBound.inPipe sy sy.EngVerticalPipe m = true := by
  obtain ⟨_, h1, h2⟩ := zok_of_check h
  obtain ⟨S, hS, (⟨_, hs⟩ | ⟨_, hs⟩)⟩ := hm
  · exact SideChangeBound.inPipe_of_sim hs (h1 S hS)
  · exact SideChangeBound.inPipe_of_sim hs (h2 S hS)

/-- **A machine at the exit is not in the pipe's routine**: the exit's bytes have the reference's task, which is not the game core -/
theorem not_inPipe_of_exit (h : (peek (refX e) sy.OperMode_Task).toUInt16 != sy.Task_GameCore) {m : Machine} (hx : ExitAt (exitQ sy nm e) m) :
    PipeChangeBound.inPipe sy sy.EngVerticalPipe m = false := by
  have h1 := hx _ List.mem_cons_self
  have e1 : peek m sy.OperMode_Task = peek (refX e) sy.OperMode_Task := h1
  simp only [PipeChangeBound.inPipe, e1, Bool.and_eq_false_iff]
  left
  simpa using h

/-! ## The proofs: the last frames of the change -/

/-- **A machine at the exit is in the rows with the byte**: a state of `baseA` covers it, the pause sound is as `QuietP` says, the screen buffer has a form of the table,
and the game timer is not 000 (as `PipeChangeEnd.inRowsK_of_exit`) -/
theorem rowsA_of_exit (hc : rowsCheckA sy nm d e i = true)
    (h : ∃ D ∈ baseA d e i, Sim (envOf d e) (m.frame, 2) D m) (hq : QuietP sy d (refX e) m) (hr : SongAt d.xshape m) (ht : SideChangeEnd.TimerOK d.nx m) :
    InRowsA sy nm d e i m := by
  unfold rowsCheckA at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hb, hh⟩, _⟩, _⟩ := hc
  obtain ⟨D, hD, hs⟩ := h
  obtain ⟨r, hr1, hr2⟩ := hr
  have hbD : D.dg = false ∧ StepWrites.soundLe D (soundBaseP (rtc (timeCtx sy nm d e) d e) d (refX e)) = true := by
    have h2 := List.all_eq_true.1 hb D hD
    rw [Bool.and_eq_true] at h2
    refine ⟨?_, h2.2⟩
    cases hdd : D.dg with
    | false => rfl
    | true =>
      rw [hdd] at h2
      cases h2.1
  have hs1 : Sim (timeEnv d e) (m.frame, 2) D m := SideChangeEnd.sim_D hs hbD.1
  have hs2 := SideChangeEnd.sim_refines hr2 hs1
  have hdg : (timeEnv d e).D.any (fun j => m.ram.get! j != 0) = true := by
    obtain ⟨j, hj, hne⟩ := ht
    exact List.any_eq_true.2 ⟨j, hj, by simpa using hne⟩
  have hs3 := PipeChangeEnd.sim_start (rtc (timeCtx sy nm d e) d e).SB hs2 hdg
  obtain ⟨kd, hkd, hkm⟩ := PipeChangeEnd.kinds_of_quietP hq
  have hS : StepWrites.retag false ({ StepWrites.forgetAll (rtc (timeCtx sy nm d e) d e).SB (SideChangeEnd.refine r D) with dg := true } : AS) ∈
      startsKA (rtc (timeCtx sy nm d e) d e) d e i :=
    List.mem_map.2 ⟨SideChangeEnd.refine r D, List.mem_flatMap.2 ⟨D, hD, List.mem_map.2 ⟨r, hr1, rfl⟩⟩, rfl⟩
  have hT : soundBaseP (rtc (timeCtx sy nm d e) d e) d (refX e) ++ kd ∈ tableP (timeCtx sy nm d e).sy (rtc (timeCtx sy nm d e) d e) d (refX e) :=
    List.mem_map.2 ⟨kd, hkd, rfl⟩
  unfold InRowsA
  unfold rowsA at hh ⊢
  exact SoundRows.inv_headS (grpP (pauseIx d.nx)) afterF _ _ hh hS hs3 rfl hT (SoundRows.sIn_append (StepWrites.sIn_of_le hs hbD.2) hkm)

/-- **A frame in the rows with the byte**: `left` is 0 already, or the machine stays in these rows -/
theorem rowsA_step (hc : rowsCheckA sy nm d e i = true) {m : Machine} (hm : InRowsA sy nm d e i m) {u : UInt8}
    (hu : SideChangeEnd.coreFrame sy sy.EngVerticalPipe m = true → SideChangeEnd.noStart u = true) :
    leftP sy nm e m = 0 ∨ InRowsA sy nm d e i (frame m u) := by
  unfold rowsCheckA at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨_, hK⟩, _⟩ := hc
  rcases SoundRows.chain_stepS rfl _ hK hm hu with g | ⟨g, _⟩
  · exact Or.inl g
  · exact Or.inr g

/-- **A machine in the rows with the byte has the entry's value of it** -/
theorem area_of_rowsA (hc : rowsCheckA sy nm d e i = true) {m : Machine} (hm : InRowsA sy nm d e i m) : m.ram.get! i = e.ram.get! i := by
  unfold rowsCheckA at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨_, hk⟩ := hc
  obtain ⟨r, hr, S, hS, hs, _⟩ := SoundRows.mem_of_invS hm
  exact sim_known hs (List.all_eq_true.1 (List.all_eq_true.1 hk r hr) S hS)

/-! ## The proofs: the whole change -/

/-- **The byte at the room's first control has the entry's value**, on a run of the change into the room, if it has it at the entry and `b` is the first control
after the entry. Part b's walks give the pipe's frames, the exit and the rows (`EndStatement.pauseStep`, `rowsK`, `zeroK`); the walks with the byte go beside them. -/
theorem PipeRunK.areaB (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false)
    (hP : pipeCheckA sy nm d e i = true) (hW : rowsCheckA sy nm d e i = true) (hX : (peek (refX e) sy.OperMode_Task).toUInt16 != sy.Task_GameCore)
    (h0 : (R.seq R.a).ram.get! i = e.ram.get! i) : (R.seq R.b).ram.get! i = e.ram.get! i := by
  have hZ := (zok_of_check hP).1
  have hEp : (envOf d e).pad = TaintRun.AB.top := rfl
  have key : ∀ k, R.a + k ≤ R.b → (DuringV sy d e (R.seq (R.a + k)) ∧ InvAt (envOf d e) (startsA d e i) (R.seq (R.a + k))) ∨
      (InRowsK sy nm d e (R.seq (R.a + k)) ∧ InRowsA sy nm d e i (R.seq (R.a + k))) := by
    intro k
    induction k with
    | zero => exact fun _ => Or.inl ⟨R.atEntry T, duringA_of_entry T R.entry h0⟩
    | succ k ih =>
      intro hk
      have e1 : R.a + (k + 1) = R.a + k + 1 := rfl
      rw [e1]
      have hgap : R.a ≤ R.a + k := by omega
      have hlt : R.a + k < R.b := by omega
      rcases ih (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hPl := R.places _ hgap hlt (T.inRoutine _ h1.1)
        rw [R.next (R.a + k)]
        rcases T.pauseStep _ h1 (R.inp (R.a + k)) hPl with g | ⟨g1, g2, g3, g4⟩ <;>
          rcases PipeChangeEnd.z_step hZ hEp h2 (R.inp (R.a + k)) hPl with ⟨a1, _, _⟩ | ⟨_, b1, b2, _⟩
        · exact Or.inl ⟨g, a1⟩
        · exfalso
          have := not_inPipe_of_exit hX b1
          rw [T.inRoutine _ g.1] at this
          cases this
        · exfalso
          have := not_inPipe_of_exit hX g1
          rw [inPipe_of_A hP a1] at this
          cases this
        · rw [← R.next (R.a + k)] at g1 g2 g3 g4 b2 ⊢
          obtain ⟨q1, q2⟩ := R.quiet _ (by omega) (by omega) g1
          have hq := T.pauseExit _ g2 q1
          obtain ⟨D, hD, hs⟩ := b2 (fun _ h => by cases h)
          exact Or.inr ⟨g4 hq q2, rowsA_of_exit hW ⟨D, hD, hs⟩ hq q2 g3⟩
      · have hi := R.noStart _ hgap hlt
        rcases T.rowsK _ h1 (R.inp (R.a + k)) hi with g | ⟨g, _⟩
        · have := T.zeroK _ h1 g
          rw [hc _ hgap hlt] at this
          cases this
        · rcases rowsA_step hW h2 hi with g' | g'
          · have := T.zeroK _ h1 g'
            rw [hc _ hgap hlt] at this
            cases this
          · rw [R.next]
            exact Or.inr ⟨g, g'⟩
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  have h := key (R.b - R.a) (by omega)
  rw [e2] at h
  have h0' := T.atControl _ R.atCtl
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd h0' (PipeChangeEnd.during_left T h.1)
  · exact area_of_rowsA hW h

end

/-! ## The proofs: the room's frames -/

section
variable {sy : Syms} {m0 : Machine} {nmS : Names} {i : Nat} {v : UInt8}

/-- what the check of the room's frames gives -/
theorem roomOK_of_check (h : roomCheckA sy nmS m0 i v = true) :
    RoomPause.PauseOK (envR sy nmS m0) (placesR sy nmS m0) (refR m0) (knownOf nmS) (regA sy m0 nmS i v) (cfgA sy nmS m0 i v) ScreenPage.fuelS :=
  RoomPause.pauseOK_of_check h

/-- **The byte through the room's frames.** The room's first control `c` is in the room's condition and has the byte with the value `v`. Each frame from `c` to `e`
meets `SiteOK` and starts in the player's routine, and `e` has another routine. Then `e` has the byte with the value `v`. -/
theorem area_run (hF : RoomPause.PauseOK (envR sy nmS m0) (placesR sy nmS m0) (refR m0) (knownOf nmS) (regA sy m0 nmS i v) (cfgA sy nmS m0 i v) ScreenPage.fuelS)
    (hrt : ((placesR sy nmS m0).rtI, (0xFF : UInt8)) ∈ knownOf nmS)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (hce : c ≤ e)
    (h0 : Room sy nmS m0 (seq c)) (hv : (seq c).ram.get! i = v)
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    (he : (seq e).ram.get! (placesR sy nmS m0).rtI ≠ (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    (seq e).ram.get! i = v := by
  have hc0 : ∃ t ∈ (regA sy m0 nmS i v).T, SIn t (seq c) := by
    refine ⟨[(i, AB.known v)], List.mem_singleton_self _, fun p hp => ?_⟩
    rw [List.mem_singleton] at hp
    subst hp
    exact SidePause.mem_known_of_eq hv
  obtain ⟨t, ht, hm⟩ := (RoomPause.pause_run hF hrt next hce h0 hc0 hs hr he).1
  have ht' : t = [(i, AB.known v)] := List.mem_singleton.1 ht
  subst ht'
  exact SidePause.eq_of_mem_known (hm _ (List.mem_singleton_self _))

end

/-! ## For the route -/

/-- what the checks on the ROM give for the level's number: the three walks and the small checks -/
structure Facts (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : Data) (V : List (Machine × List Nat)) (nmS : Names) : Prop where
  pipe : pipeCheckA sy nm₁ d₁ (PipeTransition.entry m0) (areaI nmS) = true
  rows : rowsCheckA sy nm₁ d₁ (PipeTransition.entry m0) (areaI nmS) = true
  room : RoomPause.PauseOK (envR sy nmS m0) (placesR sy nmS m0) (refR m0) (knownOf nmS)
    (regA sy m0 nmS (areaI nmS) ((PipeTransition.entry m0).ram.get! (areaI nmS))) (cfgA sy nmS m0 (areaI nmS) ((PipeTransition.entry m0).ram.get! (areaI nmS))) ScreenPage.fuelS
  small : smallCheck sy (PipeTransition.entry m0) V nmS m0 = true

theorem factsOf {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : Data} {V : List (Machine × List Nat)} {nmS : Names}
    (h1 : pipeCheckA sy nm₁ d₁ (PipeTransition.entry m0) (areaI nmS) = true) (h2 : rowsCheckA sy nm₁ d₁ (PipeTransition.entry m0) (areaI nmS) = true)
    (h3 : roomCheckA sy nmS m0 (areaI nmS) ((PipeTransition.entry m0).ram.get! (areaI nmS)) = true) (h4 : smallCheck sy (PipeTransition.entry m0) V nmS m0 = true) :
    Facts sy m0 nm₁ d₁ V nmS :=
  ⟨h1, h2, roomOK_of_check h3, h4⟩

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : Data} {V : List (Machine × List Nat)} {nmS : Names}

/-- the parts of the small check -/
theorem small_parts (h : smallCheck sy (PipeTransition.entry m0) V nmS m0 = true) :
    areaI nmS < 2048 ∧ areaI nmS ∈ RoomMusic.restIdxM nmS ∧ areaI nmS ≠ (placesR sy nmS m0).rtI ∧
      (peek (refX (PipeTransition.entry m0)) sy.OperMode_Task).toUInt16 != sy.Task_GameCore ∧
      ∀ v ∈ V, areaI nmS ∈ v.2 → v.1.ram.get! (areaI nmS) = (PipeTransition.entry m0).ram.get! (areaI nmS) := by
  simp only [smallCheck, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, by simpa using h4, fun v hv hi => ?_⟩
  rcases h5 v hv with h | h
  · simp [hi] at h
  · exact h

end

end Smbrta.AreaKeep
