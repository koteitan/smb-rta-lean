import Theorems.SurfaceFrames
import Theorems.FrameKeep

/-!
# Above ground: the machine at control, as the walk of one whole frame needs it

`SideChangeEnd` proves rows of abstract states for the frames of the change out of the side pipe, up to the frame of control. `SurfaceFrames.EndRun.start` reads the
horizontal state at control from the last row. Here the same rows give what `FrameKeep` needs of the machine at control (`FrameKeep.AtCtl`): the castle flag
(`StarFlagTaskControl`) is down, and the frame starts in the idle loop in control (`FrameKeep.StartK`: the stack pointer, the dot's window, the NMI on, the joypad's strobe off, the
routine, the mode, the task). In every state of the rows that has control these are known (`ctlCheck`, a check on the ROM).
So on a real run of the change the machine at control has them (`EndRun.atCtl`), under the same conditions as `EndRun.start`.
With `FrameKeep.Frames` this gives no castle flag up to the touch (`PoleJoin.Run.noCastle_of`) and the start of every frame up to the touch (`FrameKeep.Frames.start`).
There is no game data in this file. Page: `1-1/f-6-2-ControlStart.md`.
-/

namespace Smbrta.ControlStart

open TaintRun (AS Sim Env)
open SideChangeBound
open SideChangeEnd
open SurfaceFrames (ctlBytes startCheck controllable_of_known no_ctl_during)
open PipeTransitionAll (Names)
open PipeTransition (frame)
open PipeWrites (Guard)

variable {sy : Syms}

/-- a state of a row: it says whether it has control, and if it has, it knows that the castle flag is down, and it is the start of a frame (`FrameKeep.endOK`) -/
def rowCtl (sy : Syms) (G : Guard) (S : AS) : Bool :=
  (ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || (knowsAd S sy.StarFlagTaskControl && peek (mOf S) sy.StarFlagTaskControl == 0 && FrameKeep.endOK G S))

/-- every state of the rows -/
def rowsCtl (sy : Syms) (G : Guard) (l : List Row) : Bool := l.all fun r => r.R.all (rowCtl sy G)

/-- **The check on the ROM**: the entry has the program of `m0`, and in the rows of the two cases of the pause flag a state with control is as `rowCtl` says. -/
def ctlCheck (sy : Syms) (m0 : Machine) (nm nx : Names) (e : Machine) (A B : Nat) : Bool :=
  decide (e.prg = m0.prg) && decide (e.prgMask = m0.prgMask) &&
    rowsCtl sy (FrameKeep.guardK sy m0) (rows0 (rowCtx sy nm nx e A B) nx e A B) && rowsCtl sy (FrameKeep.guardK sy m0) (rows1 (rowCtx sy nm nx e A B) nx e A B)

variable {m0 : Machine}

/-- a covered machine with control is as `FrameKeep` needs it -/
theorem ctl_of_state {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowCtl sy (FrameKeep.guardK sy m0) S = true)
    (h : controllable sy m = true) (hp : E.prg = m0.prg) (hmk : E.mask = m0.prgMask) : FrameKeep.AtCtl sy m0 m := by
  simp only [rowCtl, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨⟨k1, e1⟩, he⟩
  · have := controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · refine ⟨FrameKeep.start_of_sim hs he hp hmk (FrameKeep.known_of_ctl h), ?_⟩
    unfold CastleWalk.castle
    rw [peek_of_known hs k1, e1]
    rfl

theorem ctl_of_invL {C : Ctx} (hp : C.E.prg = m0.prg) (hmk : C.E.mask = m0.prgMask) :
    ∀ {l : List Row}, rowsCtl sy (FrameKeep.guardK sy m0) l = true → ∀ {m : Machine}, InvL C l m → controllable sy m = true → FrameKeep.AtCtl sy m0 m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsCtl, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact ctl_of_state hs (List.all_eq_true.1 hl.1 S hS) hc hp hmk
    · exact ctl_of_invL hp hmk hl.2 h hc

/-- **A machine in the rows that has control is as `FrameKeep` needs it.** -/
theorem ctl_of_rows {nm nx : Names} {e : Machine} {A B : Nat} (hk : ctlCheck sy m0 nm nx e A B = true) {m : Machine} (h : InRows sy nm nx e A B m)
    (hm : controllable sy m = true) : FrameKeep.AtCtl sy m0 m := by
  simp only [ctlCheck, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨hp, hmk⟩, h0⟩, h1⟩ := hk
  rcases h with h | h
  · exact ctl_of_invL hp hmk h0 h hm
  · exact ctl_of_invL hp hmk h1 h hm

variable {nm nx : Names} {e : Machine} {c : PoleJoin.Box} {A B : Nat} {es : List Machine}

/-- **The machine at control is in the rows**, on a real run, under the conditions of `SurfaceFrames.EndRun.start`: the condition at the entry, no Start on the game core's frames,
the sound's pause bytes at the exit, and `left` not 0 before control. `hc` says that no machine in the pipe's frames has control. -/
theorem EndRun.inRows (S : Statement sy nm e es A B) (T : EndStatement sy nm nx e A B) (hc : startCheck sy nm nx e A B c = true) (R : EndRun sy nm nx e A B)
    (hf : ∀ n, R.a ≤ n → n < R.b → leftAt sy nm e A B (R.seq n) ≠ 0) : InRows sy nm nx e A B (R.seq R.b) := by
  have key : ∀ d, R.a + d ≤ R.b → St sy nm nx e A B (R.seq (R.a + d)) := by
    intro d
    induction d with
    | zero => exact fun _ => Or.inl (T.during _ R.entry)
    | succ d ih =>
      intro hd
      have e1 : R.a + (d + 1) = R.a + d + 1 := rfl
      rw [e1, R.next (R.a + d)]
      have h1 := ih (by omega)
      have hn := R.next (R.a + d)
      have hq : ExitAt (exitBytes sy nm (refExit e A)) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) →
          SideChangeEnd.Quiet (quietBytes nx e A) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) := by
        intro hx
        rw [← hn] at hx ⊢
        exact R.quiet _ (by omega) (by omega) hx
      rcases st_step S T h1 (R.noStart (R.a + d) (by omega) (by omega)) hq with g | ⟨g1, _⟩
      · exact absurd g (hf _ (by omega) (by omega))
      · exact g1
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  have h := key (R.b - R.a) (by omega)
  rw [e2] at h
  rcases h with h | h
  · have := no_ctl_during hc (T.toDuring _ h)
    rw [R.atCtl] at this
    cases this
  · exact h

/-- **The machine at control above ground is as `FrameKeep` needs it**: the start of a frame in control, with the castle flag down. On a real run of the change, under the conditions of
`SurfaceFrames.EndRun.start`. `hk` is the check on the ROM. -/
theorem EndRun.atCtl (S : Statement sy nm e es A B) (T : EndStatement sy nm nx e A B) (hc : startCheck sy nm nx e A B c = true) (hk : ctlCheck sy m0 nm nx e A B = true)
    (R : EndRun sy nm nx e A B) (hf : ∀ n, R.a ≤ n → n < R.b → leftAt sy nm e A B (R.seq n) ≠ 0) : FrameKeep.AtCtl sy m0 (R.seq R.b) :=
  ctl_of_rows hk (EndRun.inRows S T hc R hf) R.atCtl

end Smbrta.ControlStart
