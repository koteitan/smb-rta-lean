import Theorems.EntryHeight

/-!
# The screen's buffer at the side pipe's entry

`Route.ChangesBase.entry₂` asked five bytes of the first screen buffer at the side pipe's entry (its offset and four of its bytes) to be those of a reference. Here they
are proved for a frame of the room that starts with the control of the screen's buffers at the reference's value (0: the screen update of this frame empties the first
buffer), by one more walk of the room's frame (the walk of `EntryHeight`, with no split of the height).

On such a frame the screen update empties the first buffer. A frame that enters the side pipe takes no coin: a coin ends the collision routine before the side pipe's
code, or it is the tile of the side check in place of the pipe's. The timer's digits are not written, since the timer's code does not run with the side pipe's routine. So
only the colour rotation writes the buffer, and the frame ends with the buffer empty or with the one record of the colour rotation: the two references (`buffer_frame`).

What stays assumed is the control at the frame's start. A coin erased on the frame before sets it, and then the screen update keeps the first buffer's records.

There is no game data in this file. Page: `1-1/d-2-5-5-EntryBuffer.md`.
-/

namespace Smbrta.EntryBuffer

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open SideChangeBound
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond)
open SideEntryEnd (isV)
open SideEntryRest (notV ne_of_notV)
open EntryHeight (HP Opts WalkOK walkCheckY walkOK_of_check frame_end mix64)

/-! ## The walk's end, and its search -/

/-- at the frame's end: the routine byte is known not to be the side pipe's, or the bytes `L` that a reference of `V` lists are known with its values -/
def finB (S : HP) (V : List (Machine × List Nat)) (L : List Nat) (B : AS) : Bool :=
  notV S.ev (B.getK S.rtI) || V.any fun v => v.2.all fun i => !L.contains i || knownIs B (i, v.1.ram.get! i)

/-- the key of the search: the room's, the byte `c` (the control of the screen's buffers), and with the side pipe's routine the bytes `L`; below them 64 mixed
bits. No part of the proof. The control keeps the states at the frame's end with the control set apart from the states at the frame's start, which know it. -/
def keyB (S : HP) (Z : Aids) (E : Env) (c : Nat) (L : List Nat) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let x := if isV S.ev (A.getK S.rtI) then L.foldl (fun n i => n * 65536 + num (A.getK i)) 1 else 0
  let K := Z.key E A + (x * 65536 + num (A.getK c)) * (1 <<< 300)
  K * 18446744073709551616 + mix64 K

/-- the search of the buffer's walk: it forgets what the room's search forgets -/
def optsB (S : HP) (Z : Aids) (E : Env) (c : Nat) (L : List Nat) : Opts := { key := keyB S Z E c L, norm := Z.norm, stops := [], normAt := [] }

/-! ## The frame -/

/-- **The bytes `L` at the end of the entering frame.** A frame that starts in the room's condition (with the bits `K`: the map's bits and the control of the screen's
buffers), with `SiteOK` on each instruction: if it ends with the side pipe's routine, the bytes `L` have the values of a reference of `V` (those that it lists). -/
theorem buffer_frame {S : HP} {V : List (Machine × List Nat)} {L : List Nat} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS}
    (h : WalkOK S (finB S V L) E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j)) (hrt : (frame m i).ram.get! S.rtI = S.ev) :
    ∃ v ∈ V, ∀ j ∈ v.2, j ∈ L → (frame m i).ram.get! j = v.1.ram.get! j := by
  obtain ⟨B, h2, h4⟩ := frame_end h hm hk
  simp only [finB, Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd hrt (ne_of_notV h2 (h4.ram _ h.rt))
  · obtain ⟨v, hv, h3⟩ := List.any_eq_true.1 h2
    refine ⟨v, hv, fun j hj hjL => ?_⟩
    have h5 := List.all_eq_true.1 h3 j hj
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h5
    rcases h5 with h5 | h5
    · rw [List.contains_iff_mem.2 hjL] at h5
      cases h5
    · exact sim_known h4 h5

/-! ## On the ROM -/

section
open ScreenPage (placesR envR refR aidsOf)

/-- the control of the screen's buffers, as a RAM index -/
def ctlI (nm : Names) : Nat := (nm.ad "VRAM_Buffer_AddrCtrl").toNat &&& 0x7FF

/-- the five bytes of the first screen buffer that the entry asks: its offset and four of its bytes, those of `ScreenPage.restNames` -/
def bufIdx (nm : Names) : List Nat :=
  (ScreenPage.restNames.filter fun p => p.1 == "VRAM_Buffer1_Offset" || p.1 == "VRAM_Buffer1").flatMap fun p =>
    (List.range p.2.2).map fun j => ((nm.ad p.1).toNat + p.2.1 + j) &&& 0x7FF

/-- the places: the room's and the routine byte; no place of the height's walk -/
def hpB (sy : Syms) (nm : Names) (m0 : Machine) : HP :=
  { P := placesR sy nm m0, rtI := (sy.GameEngineSubroutine &&& 0x7FF).toNat, ev := SideEntryRule.vs sy, yI := 0, yv := 0,
    footAt := 0, landAt := 0, colAt := 0, tileI := 0, tileAt := 0, ptrI := 0, sideAt := 0 }

/-- the known bits: those of `RoomMap`, and the control of the screen's buffers -/
def knownB (sy : Syms) (nm : Names) (m0 : Machine) : List (Nat × UInt8) := RoomMap.knownT sy nm m0 ++ [(ctlI nm, 0xFF)]

/-- **The check on the ROM.** -/
def bufferCheck (sy : Syms) (nm : Names) (m0 : Machine) (V : List (Machine × List Nat)) : Bool :=
  walkCheckY (hpB sy nm m0) (aidsOf sy nm m0) (optsB (hpB sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (ctlI nm) (bufIdx nm)) (finB (hpB sy nm m0) V (bufIdx nm))
    (envR sy nm m0) (refR m0) (knownB sy nm m0)

/-- the references `V` agree on the bytes `L`: a byte that one lists, each lists, with the same value -/
def agreeCheck (V : List (Machine × List Nat)) (L : List Nat) : Bool :=
  V.all fun v => V.all fun w => L.all fun i => !v.2.contains i || (w.2.contains i && w.1.ram.get! i == v.1.ram.get! i)

/-- what the checks give. `L` is the other bytes that the entry asks. -/
structure Facts (sy : Syms) (nm : Names) (m0 : Machine) (V : List (Machine × List Nat)) (L : List Nat) : Prop where
  walk : bufferCheck sy nm m0 V = true
  agree : ∀ v ∈ V, ∀ w ∈ V, ∀ i ∈ L, i ∈ v.2 → i ∈ w.2 ∧ w.1.ram.get! i = v.1.ram.get! i

theorem factsOf {sy : Syms} {nm : Names} {m0 : Machine} {V : List (Machine × List Nat)} {L : List Nat} (h1 : bufferCheck sy nm m0 V = true)
    (h2 : agreeCheck V L = true) : Facts sy nm m0 V L := by
  refine ⟨h1, fun v hv w hw i hi hiv => ?_⟩
  simp only [agreeCheck, List.all_eq_true] at h2
  have h3 := h2 v hv w hw i hi
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at h3
  rcases h3 with h3 | ⟨h3, h4⟩
  · rw [List.contains_iff_mem.2 hiv] at h3
    cases h3
  · exact ⟨List.contains_iff_mem.1 h3, h4⟩

end

/-! ## The entering frame of the room -/

section
open ScreenPage (placesR envR refR)
open PipeChangeEnd (Data InRowsT)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine} {V : List (Machine × List Nat)}

/-- **The screen's buffer at the end of the entering frame, on the real machines.** A frame `k` of the room (from `b` to `a`, under the conditions of
`RoomMap.map_of_rows`) that starts with the control of the screen's buffers of the reference and ends with the side pipe's routine ends with the five bytes of the first
screen buffer of a reference of `V`. `hF`, `hc`, `hH` are checks on the ROM. -/
theorem buffer_of_rows (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hH : bufferCheck sy nmS m0 V = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    {k : Nat} (h1 : b ≤ k) (h2 : k < a)
    (hc0 : (seq k).ram.get! (ctlI nmS) = (refR m0).ram.get! (ctlI nmS))
    (hrt : (frame (seq k) (inp k)).ram.get! (placesR sy nmS m0).rtI = (placesR sy nmS m0).eng) :
    ∃ v ∈ V, ∀ j ∈ v.2, j ∈ bufIdx nmS → (frame (seq k) (inp k)).ram.get! j = v.1.ram.get! j := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay k h1 h2
  have hB : RoomCond (envR sy nmS m0) (refR m0) (knownB sy nmS m0) (seq k) :=
    RoomMusic.roomCond_append hcond (fun p hp => by
      have e1 : p = (ctlI nmS, (0xFF : UInt8)) := List.mem_singleton.1 hp
      rw [e1]
      show (seq k).ram.get! (ctlI nmS) &&& 0xFF = (refR m0).ram.get! (ctlI nmS) &&& 0xFF
      rw [hc0])
  exact buffer_frame (S := hpB sy nmS m0) (walkOK_of_check hH) hB (sites k h1 h2) hrt

end

end Smbrta.EntryBuffer
