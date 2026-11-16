import Theorems.RoomMusic

/-!
# The level's number from the vertical pipe's entry to the side pipe's entry

`entry₂` of the route asked that the level's number (`AreaNumber`) at the side pipe's entry is that of a reference. Only the code of a level's end, of a warp and of the
title stores to it (read from the disassembly). The byte comes to the side pipe's entry in three steps:

* at the vertical pipe's entry it has the reference's value: the entry's condition lists it (`PipeChangeEnd.entryNames`, round 15; `Route.Run.area₁`);
* from the entry to the room's first control: the exit's list has it too (`PipeChangeEnd.exitNames`, round 16), so part b's walk of the pipe's frames ends with it
  known, and every state of part b's rows after the exit knows it (`ScreenStart.roomCheck`, `ScreenStart.area_of_rows`). In round 14 two copies of part b's walks
  with the byte known stood here (`pipeCheckA`, `rowsCheckA`); they are gone;
* the room's frames: the walk of `RoomPause` with the byte in a table of one state (`roomCheckA`, `area_run`). This file has only this step.

So the byte has the entry's value at the side pipe's entry (`Route.Run.area₂`).

There is no game data in this file. Page: `1-1/d-2-5-3-AreaKeep.md`.
-/

namespace Smbrta.AreaKeep

open TaintRun
open PipeTransition (frame)
open PipeTransitionAll (Names)
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK RoomCond placesR envR refR knownOf Room)
open StepWrites (SState SIn)

/-! ## The byte -/

/-- the level's number, as a RAM index -/
def areaI (nm : Names) : Nat := RoomMusic.ix nm "AreaNumber"

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

/-- **The small checks**: the byte is in RAM, it is a byte of the 11 of `RoomMusic.restIdxM` and not the routine's; each reference of the side pipe's entry that
lists the byte has the vertical pipe's entry's value -/
def smallCheck (sy : Syms) (e : Machine) (V : List (Machine × List Nat)) (nmS : Names) (m0 : Machine) : Bool :=
  let i := areaI nmS
  decide (i < 2048) && (RoomMusic.restIdxM nmS).contains i && i != (placesR sy nmS m0).rtI &&
    V.all fun v => !v.2.contains i || v.1.ram.get! i == e.ram.get! i

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

/-- what the checks on the ROM give for the level's number: the room's walk and the small checks -/
structure Facts (sy : Syms) (m0 : Machine) (V : List (Machine × List Nat)) (nmS : Names) : Prop where
  room : RoomPause.PauseOK (envR sy nmS m0) (placesR sy nmS m0) (refR m0) (knownOf nmS)
    (regA sy m0 nmS (areaI nmS) ((PipeTransition.entry m0).ram.get! (areaI nmS))) (cfgA sy nmS m0 (areaI nmS) ((PipeTransition.entry m0).ram.get! (areaI nmS))) ScreenPage.fuelS
  small : smallCheck sy (PipeTransition.entry m0) V nmS m0 = true

theorem factsOf {sy : Syms} {m0 : Machine} {V : List (Machine × List Nat)} {nmS : Names}
    (h3 : roomCheckA sy nmS m0 (areaI nmS) ((PipeTransition.entry m0).ram.get! (areaI nmS)) = true) (h4 : smallCheck sy (PipeTransition.entry m0) V nmS m0 = true) :
    Facts sy m0 V nmS :=
  ⟨roomOK_of_check h3, h4⟩

section
variable {sy : Syms} {m0 : Machine} {V : List (Machine × List Nat)} {nmS : Names}

/-- the parts of the small check -/
theorem small_parts (h : smallCheck sy (PipeTransition.entry m0) V nmS m0 = true) :
    areaI nmS < 2048 ∧ areaI nmS ∈ RoomMusic.restIdxM nmS ∧ areaI nmS ≠ (placesR sy nmS m0).rtI ∧
      ∀ v ∈ V, areaI nmS ∈ v.2 → v.1.ram.get! (areaI nmS) = (PipeTransition.entry m0).ram.get! (areaI nmS) := by
  simp only [smallCheck, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun v hv hi => ?_⟩
  rcases h5 v hv with h | h
  · simp [hi] at h
  · exact h

end

end Smbrta.AreaKeep
