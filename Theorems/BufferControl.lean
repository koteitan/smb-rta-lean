import Theorems.EntryBuffer

/-!
# The control of the screen's buffers through the room

`Route.Run` asks (field `buffer₂`) that the frame that enters the side pipe starts with the control of the screen's buffers (`VRAM_Buffer_AddrCtrl`) at the
reference's value 0, or else that the five bytes of the first screen buffer at the entry are those of a reference. With the control at 0 the five bytes are proved
(`EntryBuffer.buffer_of_rows`).

Here a step toward the control at 0: on every frame of the room the control is 0 or 6 when the frame starts. The screen update at the start of each frame sets it
to 0; in the room the only other store to it is the erase of a coin, which sets it to 6 (so that the next frame's screen update draws the second buffer). The walk
of `EntryBuffer` (the room's walk with the control known, `walkK`) from a frame that starts with the control at 0, and from one that starts with it at 6, ends with
the control known to be 0 or 6 (`keepCheck`, `keep_frame`, `ctl_step`). The rows of the first change know the control at the room's first control: the reference's
value 0 (`startCheckC`, `start_ctl`). So every frame of the room from the first control to the side pipe's entry starts with the control at 0 or 6 (`ctl_run`,
`ctl_of_rows`, `Route.Run.ctl₂`).

What stays assumed is that the value is not 6 at the start of the entering frame: that the frame before it erases no coin. The coins of the map are at least three
columns left of the side pipe's mouth, but a proof needs the position on two frames, which this walk does not follow.

There is no game data in this file. Page: `1-1/d-2-5-5-1-BufferControl.md`.
-/

namespace Smbrta.BufferControl

open PipeTransition (frame)
open PipeTransitionAll (Names)
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (SiteOK RoomCond placesR envR refR aidsOf)
open EntryBuffer (ctlI hpB knownB optsB)
open EntryHeight (WalkOK walkCheckY walkOK_of_check frame_end)

/-! ## The walks -/

/-- at the frame's end: the control known to be 0 or 6 -/
def finK (c : Nat) (B : AS) : Bool := (B.getK c).isK && ((B.getK c).v == 0 || (B.getK c).v == 6)

/-- the reference machine with the control at 6 -/
def ref6 (c : Nat) (r : Machine) : Machine := { r with ram := r.ram.set! c 6 }

/-- the room's walk with the control known (that of `EntryBuffer`), from the reference `r`, with the condition `finK` at the frame's end -/
abbrev walkK (sy : Syms) (nm : Names) (m0 r : Machine) : Bool :=
  walkCheckY (hpB sy nm m0) (aidsOf sy nm m0) (optsB (hpB sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (ctlI nm) (EntryBuffer.bufIdx nm)) (finK (ctlI nm))
    (envR sy nm m0) r (knownB sy nm m0)

/-- **The check on the ROM**: the room's list of known bits does not list the control, the reference's control is 0, and the walks from the control at 0 and at 6 -/
def keepCheck (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  (RoomMap.knownT sy nm m0).all (fun p => p.1 != ctlI nm) && (refR m0).ram.get! (ctlI nm) == 0 && decide (ctlI nm < 2048) &&
    walkK sy nm m0 (refR m0) && walkK sy nm m0 (ref6 (ctlI nm) (refR m0))

/-! ## One frame -/

/-- **The control at a frame's end.** A frame that starts in the room's condition, with `SiteOK` on each instruction, ends with the control at 0 or 6, if the walk
from that condition succeeds -/
theorem keep_frame {S : EntryHeight.HP} {c : Nat} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : ScreenPage.CfgS}
    (h : WalkOK S (finK c) E r K C) (hc : c < 2048) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j)) :
    (frame m i).ram.get! c = 0 ∨ (frame m i).ram.get! c = 6 := by
  obtain ⟨B, h2, h4⟩ := frame_end h hm hk
  simp only [finK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h2
  have e := PipeEntryRule.known_eq h2.1 (h4.ram c hc)
  rcases h2.2 with h3 | h3
  · left
    rw [e, h3]
  · right
    rw [e, h3]

/-- the room's condition, with the control at the reference's value -/
theorem cond0 {E : Env} {r m : Machine} {K : List (Nat × UInt8)} {c : Nat} (hm : RoomCond E r K m) (hv : m.ram.get! c = r.ram.get! c) :
    RoomCond E r (K ++ [(c, 0xFF)]) m :=
  RoomMusic.roomCond_append hm (fun p hp => by
    rw [List.mem_singleton.1 hp]
    show m.ram.get! c &&& 0xFF = r.ram.get! c &&& 0xFF
    rw [hv])

/-- the room's condition with the control at 6, for the reference with the control at 6: the list `K` does not list the control -/
theorem cond6 {E : Env} {r m : Machine} {K : List (Nat × UInt8)} {c : Nat} (hm : RoomCond E r K m) (hK : K.all (fun p => p.1 != c) = true)
    (hc : c < r.ram.size) (hv : m.ram.get! c = 6) : RoomCond E (ref6 c r) (K ++ [(c, 0xFF)]) m := by
  have h1 : RoomCond E (ref6 c r) K m := by
    refine { hm with bytes := ?_ }
    intro p hp
    have hne : c ≠ p.1 := by
      have h := List.all_eq_true.1 hK p hp
      simp only [bne_iff_ne, ne_eq] at h
      exact fun e => h e.symm
    show m.ram.get! p.1 &&& p.2 = (r.ram.set! c 6).get! p.1 &&& p.2
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ hne]
    exact hm.bytes p hp
  refine cond0 h1 ?_
  show m.ram.get! c = (r.ram.set! c 6).get! c
  rw [hv, PipeTransitionAll.ba_get_set_self _ _ _ hc]

section
variable {sy : Syms} {nmS : Names} {m0 : Machine}

theorem keep_parts (h : keepCheck sy nmS m0 = true) :
    (RoomMap.knownT sy nmS m0).all (fun p => p.1 != ctlI nmS) = true ∧ (refR m0).ram.get! (ctlI nmS) = 0 ∧ ctlI nmS < 2048 ∧
    walkK sy nmS m0 (refR m0) = true ∧ walkK sy nmS m0 (ref6 (ctlI nmS) (refR m0)) = true := by
  simp only [keepCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **One frame of the room keeps the control at 0 or 6**: a frame that starts in the room's condition (with the map's bits) and with the control at 0 or 6, with
`SiteOK` on each instruction, ends with the control at 0 or 6 -/
theorem ctl_step (hK : keepCheck sy nmS m0 = true) {m : Machine} {i : UInt8}
    (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMap.knownT sy nmS m0) m)
    (hk : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j))
    (hv : m.ram.get! (ctlI nmS) = 0 ∨ m.ram.get! (ctlI nmS) = 6) :
    (frame m i).ram.get! (ctlI nmS) = 0 ∨ (frame m i).ram.get! (ctlI nmS) = 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := keep_parts hK
  rcases hv with hv | hv
  · exact keep_frame (S := hpB sy nmS m0) (walkOK_of_check h4) h3 (cond0 hm (hv.trans h2.symm)) hk
  · have w := walkOK_of_check (S := hpB sy nmS m0) h5
    have hsz : ((refR m0).ram.set! (ctlI nmS) 6).size = 2048 := w.mask.szR
    rw [PipeTransitionAll.ba_size_set] at hsz
    exact keep_frame w h3 (cond6 hm h1 (by rw [hsz]; exact h3) hv) hk

end

/-! ## The room's frames -/

section
open PipeChangeEnd (Data InRowsT)
variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **Every frame of the room keeps the control at 0 or 6.** Under the conditions of `RoomMap.map_of_rows` on the frames from `b` before `a`, if frame `b` starts
with the control at 0 or 6, every frame from `b` to `a` starts with it at 0 or 6. -/
theorem ctl_run (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hK : keepCheck sy nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    (h0 : (seq b).ram.get! (ctlI nmS) = 0 ∨ (seq b).ram.get! (ctlI nmS) = 6) :
    ∀ n, b ≤ n → n ≤ a → (seq n).ram.get! (ctlI nmS) = 0 ∨ (seq n).ram.get! (ctlI nmS) = 6 := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay
  have key : ∀ k, b + k ≤ a → (seq (b + k)).ram.get! (ctlI nmS) = 0 ∨ (seq (b + k)).ram.get! (ctlI nmS) = 6 := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      have e1 : b + (k + 1) = b + k + 1 := rfl
      rw [e1, next]
      exact ctl_step hK (hcond (b + k) (by omega) (by omega)) (sites (b + k) (by omega) (by omega)) (ih (by omega))
  intro n h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, n = b + k := ⟨n - b, by omega⟩
  exact key k h2

/-- **The check on the ROM at the room's first control**: every state of the rows of the time of the first change knows the bits of the room's condition and the
control, with the reference's values (as `RoomMap.startCheckT`, with the control) -/
def startCheckC (sy : Syms) (nm : Names) (d : Data) (e : Machine) (nmS : Names) (m0 : Machine) : Bool :=
  ScreenPage.maskOK (refR m0) (knownB sy nmS m0) && ScreenStart.rowsR sy (refR m0) (knownB sy nmS m0) (PipeChangeEnd.timeRows (PipeChangeEnd.timeCtx sy nm d e) d e)

theorem and_ff_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0xFF = UInt8.ofNat n.val := by decide +kernel

theorem and_ff (x : UInt8) : x &&& 0xFF = x := by
  have := and_ff_all ⟨x.toNat, x.toNat_lt⟩
  simpa using this

/-- **The control at the room's first control** is the reference's: a machine with control in the rows of the time of the first change -/
theorem start_ctl (hs : startCheckC sy nm d e nmS m0 = true) {m : Machine} (h : InRowsT sy nm d e m) (hm : controllable sy m = true) :
    m.ram.get! (ctlI nmS) = (refR m0).ram.get! (ctlI nmS) := by
  simp only [startCheckC, Bool.and_eq_true] at hs
  obtain ⟨h1, h4⟩ := hs
  have hc0 : RoomCond (PipeChangeEnd.timeEnv d e) (refR m0) (knownB sy nmS m0) m := ScreenStart.room_of_invL (ScreenPage.maskOK_spec h1) h4 h hm
  have hb := hc0.bytes (ctlI nmS, 0xFF) (List.mem_append_right _ (List.mem_singleton_self _))
  rw [and_ff, and_ff] at hb
  exact hb

/-- what the checks on the ROM give -/
structure Facts (sy : Syms) (nm₁ : Names) (d₁ : Data) (nmS : Names) (m0 : Machine) : Prop where
  keep : keepCheck sy nmS m0 = true
  start : startCheckC sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true

/-- **Every frame of the room starts with the control at 0 or 6**, on the real machines: from the room's first control `b` (a machine with control in the rows of
the time of the first change) to `a`, under the conditions of `RoomMap.map_of_rows` -/
theorem ctl_of_rows (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hK : keepCheck sy nmS m0 = true)
    (hs : startCheckC sy nm d e nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n ≤ a → (seq n).ram.get! (ctlI nmS) = 0 ∨ (seq n).ram.get! (ctlI nmS) = 6 := by
  have h0 : (seq b).ram.get! (ctlI nmS) = 0 := (start_ctl hs hin hctl).trans (keep_parts hK).2.1
  exact ctl_run hF hc hK next hin hctl sites stay (Or.inl h0)

/-- **Not 6 is the reference's value**: on a frame of the room the control is 0 or 6 (`ctl_of_rows`), and the reference's is 0 (`keepCheck`); so a control that is
not 6 is the reference's -/
theorem ref_of_ne6 (hK : keepCheck sy nmS m0 = true) {m : Machine} (h06 : m.ram.get! (ctlI nmS) = 0 ∨ m.ram.get! (ctlI nmS) = 6)
    (hne : m.ram.get! (ctlI nmS) ≠ 6) : m.ram.get! (ctlI nmS) = (refR m0).ram.get! (ctlI nmS) := by
  rw [(keep_parts hK).2.1]
  rcases h06 with h | h
  · exact h
  · exact absurd h hne

end

end Smbrta.BufferControl
