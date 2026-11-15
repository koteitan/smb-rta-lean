import Theorems.RoomStart
import Theorems.ScreenPage

/-!
# The condition at the first control in the room, from the rows of the change

`ScreenPage.Room` is a condition on the state at the first control in the room: the frame has ended in the idle loop, and some bytes have the bits of a reference machine. `PipeChangeEnd` proves rows of
states up to that control, and rows of the time (`PipeChangeEnd.timeRows`) for a run whose time is not up at the exit. In the rows of the time a machine with control is in a start state of the condition
(`roomCheck`, `room_of_rows`). The condition at the exit of the vertical pipe gives the world, the hard mode and the bits of Mario's status and of the saved song; the sound's pause flag is 0 there, so the
sound routines run and take the song's queue as in the reference. No game data. Page: `1-1/d-2-4-1-ScreenStart.md`.
-/

namespace Smbrta.ScreenStart

open SideChangeBound
open SideChangeEnd
open PipeChangeEnd
open ScreenPage (Room RoomCond MaskOK maskOK maskOK_spec startsR room_of_sim knownOf refR envR)
open PipeTransitionAll (Names)

/-- a state of a row: it says whether it has control, and if it has, it is under a start state of the condition -/
def rowR (sy : Syms) (r : Machine) (K : List (Nat × UInt8)) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) && (!controllable sy (mOf S) || (startsR r K).any (S.le ·))

/-- every state of the rows -/
def rowsR (sy : Syms) (r : Machine) (K : List (Nat × UInt8)) (l : List Row) : Bool := l.all fun w => w.R.all (rowR sy r K)

/-- the level's number in the room's names, as a RAM index (`AreaKeep.areaI` is this number) -/
def areaI (nmS : Names) : Nat := (nmS.ad "AreaNumber").toNat &&& 0x7FF

/-- **The check on the ROM**: the mask of the bits, the same ROM in both environments, and the states of the rows of the time; and the two lists of names agree on the
level's number: its index in the room's names is a byte that the vertical pipe's entry knows (round 15, for `Route.Run.area₁`) -/
def roomCheck (sy : Syms) (nm : Names) (d : Data) (e : Machine) (nmS : Names) (m0 : Machine) : Bool :=
  maskOK (refR m0) (knownOf nmS) && decide ((timeEnv d e).prg.data = (envR sy nmS m0).prg.data) && (timeEnv d e).mask == (envR sy nmS m0).mask &&
    rowsR sy (refR m0) (knownOf nmS) (timeRows (timeCtx sy nm d e) d e) && d.known.contains (areaI nmS)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- the condition does not depend on the environment but for the ROM -/
theorem roomCond_env {E E' : Env} {r : Machine} {K : List (Nat × UInt8)} {m : Machine} (h : RoomCond E r K m) (hp : E.prg = E'.prg) (hm : E.mask = E'.mask) :
    RoomCond E' r K m :=
  { h with prg := h.prg.trans hp, mask := h.mask.trans hm }

/-- a covered machine with control meets the condition -/
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

/-- **The condition at the first control in the room**, for a machine with control in the rows of the time. -/
theorem room_of_rows (hc : roomCheck sy nm d e nmS m0 = true) {m : Machine} (h : InRowsT sy nm d e m) (hm : controllable sy m = true) : Room sy nmS m0 m := by
  simp only [roomCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩ := hc
  have hM := maskOK_spec h1
  have hp := ba_eq h2
  have hc0 : RoomCond (timeEnv d e) (refR m0) (knownOf nmS) m := room_of_invL hM h4 h hm
  exact roomCond_env hc0 hp h3

/-- **The level's number is a byte that the vertical pipe's entry knows**: a machine with the condition at the entry (`PipeChangeEnd.Entry`) has it with the reference
entry's value -/
theorem area_of_entry (hc : roomCheck sy nm d e nmS m0 = true) {m : Machine} (h : Entry d e m) : m.ram.get! (areaI nmS) = e.ram.get! (areaI nmS) := by
  simp only [roomCheck, Bool.and_eq_true] at hc
  obtain ⟨v, hv, _, _, hb⟩ := h.1.ref
  cases List.mem_singleton.1 hv
  exact hb _ (List.contains_iff_mem.1 hc.2)

end Smbrta.ScreenStart
