import Theorems.RoomStart
import Theorems.ScreenPage

/-!
# The condition at the first control in the room, from the rows of the change

`ScreenPage.Room` is a condition on the state at the first control in the room: the frame has ended in the idle loop, and some bytes have the bits of a reference machine. `PipeChangeEnd` proves rows of
states up to that control. In these rows a machine with control is in a start state of the condition, but for five bytes that the rows do not know as the reference does (`restNames`): the condition
at the exit of the vertical pipe does not list three of them, the area's setup may set one bit of the fourth, and the fifth, a sound queue, has another value when the sound is paused. So `Room` comes
from the rows and a condition on these five bytes (`RestAt`, `room_of_rows`). No game data. Page: `1-1/d-2-4-1-ScreenStart.md`.
-/

namespace Smbrta.ScreenStart

open SideChangeBound
open SideChangeEnd
open PipeChangeEnd
open ScreenPage (Room RoomCond MaskOK maskOK maskOK_spec startsR room_of_sim knownOf refR envR)
open PipeTransitionAll (Names)

/-- the bytes of the condition that the rows do not know as the reference does -/
def restNames : List String := ["SecondaryHardMode", "PlayerStatus", "WorldNumber", "AreaMusicBuffer_Alt", "AreaMusicQueue"]

/-- these bytes as RAM indices -/
def restIdx (nm : Names) : List Nat := restNames.map fun n => ((nm.ad n) &&& 0x7FF).toNat

/-- the bits of the condition that the rows give -/
def rowK (nm : Names) : List (Nat × UInt8) := (knownOf nm).filter fun p => !(restIdx nm).contains p.1

/-- **The condition on the five bytes**: their bits of the condition are those of the reference machine -/
def RestAt (nm : Names) (m0 m : Machine) : Prop :=
  ∀ p ∈ knownOf nm, p.1 ∈ restIdx nm → m.ram.get! p.1 &&& p.2 = (refR m0).ram.get! p.1 &&& p.2

/-- a state of a row: it says whether it has control, and if it has, it is under a start state of the condition without the five bytes -/
def rowR (sy : Syms) (r : Machine) (K : List (Nat × UInt8)) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) && (!controllable sy (mOf S) || (startsR r K).any (S.le ·))

/-- every state of the rows -/
def rowsR (sy : Syms) (r : Machine) (K : List (Nat × UInt8)) (l : List Row) : Bool := l.all fun w => w.R.all (rowR sy r K)

/-- **The check on the ROM**: the mask of the bits, the same ROM in both environments, and the states of the rows of the two cases -/
def roomCheck (sy : Syms) (nm : Names) (d : Data) (e : Machine) (nmS : Names) (m0 : Machine) : Bool :=
  maskOK (refR m0) (rowK nmS) && decide ((envOf d e).prg.data = (envR sy nmS m0).prg.data) && (envOf d e).mask == (envR sy nmS m0).mask &&
    rowsR sy (refR m0) (rowK nmS) (rowsA (ctxOf sy nm d e) d e) && rowsR sy (refR m0) (rowK nmS) (rowsB (ctxOf sy nm d e) d e)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- the condition does not depend on the environment but for the ROM -/
theorem roomCond_env {E E' : Env} {r : Machine} {K : List (Nat × UInt8)} {m : Machine} (h : RoomCond E r K m) (hp : E.prg = E'.prg) (hm : E.mask = E'.mask) :
    RoomCond E' r K m :=
  { h with prg := h.prg.trans hp, mask := h.mask.trans hm }

/-- the five bytes added -/
theorem room_of_rest {E : Env} {r m : Machine} (h : RoomCond E r (rowK nmS) m)
    (hr : ∀ p ∈ knownOf nmS, p.1 ∈ restIdx nmS → m.ram.get! p.1 &&& p.2 = r.ram.get! p.1 &&& p.2) : RoomCond E r (knownOf nmS) m := by
  refine { h with bytes := fun p hp => ?_ }
  by_cases hi : p.1 ∈ restIdx nmS
  · exact hr p hp hi
  · refine h.bytes p (List.mem_filter.2 ⟨hp, ?_⟩)
    simp only [Bool.not_eq_true']
    cases hc : (restIdx nmS).contains p.1 with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.1 hc) hi

/-- a covered machine with control meets the condition without the five bytes -/
theorem room_of_state {E : Env} {F : Nat × UInt8} {r : Machine} {K : List (Nat × UInt8)} {S : AS} {m : Machine} (hM : MaskOK r K) (hs : Sim E F S m)
    (hr : rowR sy r K S = true) (h : controllable sy m = true) : RoomCond E r K m := by
  simp only [rowR, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨T, hT, hle⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · exact room_of_sim hM hT (TaintRun.sim_le hle hs)

theorem room_of_invL {C : Ctx} {r : Machine} {K : List (Nat × UInt8)} (hM : MaskOK r K) : ∀ {l : List Row}, rowsR sy r K l = true → ∀ {m : Machine}, InvL C l m →
    controllable sy m = true → RoomCond C.E r K m
  | [], _, _, h, _ => by cases h
  | w :: t, hl, _, h, hc => by
    simp only [rowsR, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact room_of_state hM hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact room_of_invL hM hl.2 h hc

theorem ba_eq {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- **The condition at the first control in the room**, for a machine with control in the rows, from the five bytes. -/
theorem room_of_rows (hc : roomCheck sy nm d e nmS m0 = true) {m : Machine} (h : InRows sy nm d e m) (hm : controllable sy m = true) (hr : RestAt nmS m0 m) :
    Room sy nmS m0 m := by
  simp only [roomCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have hM := maskOK_spec h1
  have hp := ba_eq h2
  have hc0 : RoomCond (envOf d e) (refR m0) (rowK nmS) m := by
    rcases h with h | h
    · exact room_of_invL hM h4 h hm
    · exact room_of_invL hM h5 h hm
  exact room_of_rest (roomCond_env hc0 hp h3) hr

end Smbrta.ScreenStart
