import Theorems.PipeEntry
import Theorems.PipeEntryRule
import Theorems.PipeWrites
import Theorems.PipeFrames
import Theorems.OpenFrames
import Theorems.LagFrames
import Theorems.RoomJoin
import Theorems.PoleJoin
import Theorems.CastleToLevel
import Theorems.PipeChangeBound
import Theorems.SideChangeBound
import Theorems.SideChangeEnd
import Theorems.PipeChangeEnd
import Theorems.FlagRule
import Theorems.ScreenPage
import Theorems.RoomStart
import Theorems.ScreenStart
import Theorems.TitleStart
import Theorems.EntryKeep
import Theorems.ControlStart
import Theorems.StartRun
import Theorems.RoomMap
import Theorems.SideEntryRest

/-!
# The whole route: 1-2 does not start before frame 1748

The parts of the route are joined here into one statement. `Run` lists what a run has to satisfy, one named field per assumption. `level_ge_of_parts` is the
arithmetic of the join: from the bounds of the parts it concludes the level change's frame. The private proof applies the theorems of the parts for the numbers of the game.
No field is proved for every run: this says which assumptions the bound rests on. Page: `1-1/0-1-Route.md`.

Frames are numbered from the first controllable frame of 1-1. The fields of the parts (`pipe.E`, `room.C`, `room.E`, `Cs`, `pole.g`, `pole.c`) count frames without the `lag` frames of
`CastleToLevel.Frames`. `E` and the frames of `clock` count all frames. The three facts about the timers in the whole run are proved here from the rule on single frames: `Run.hE`, `Run.hT`, `Run.hc`.
The counters before frame 0 come from the machine when frame 0 begins (`read₀`), as those after the castle entry come from the machine after it (`flag`). That machine shows `t0`
and the phase 2, and the speed at control is 0: this comes from one condition on the machine after the press of Start on the title (`title`, `TitleStart.Begin`).
The frames after the castle entry are in `flag`, on the real machines of `base`. From one condition at the castle entry and the check `hF` of the ROM, the rule holds on every
frame up to the level change (`FlagRule.flagOf_after`), and the two facts about them are proved from it: `Run.hD`, `Run.hL`.

The run has one sequence of real machines, every frame counted or not (`Base`, the field `base`). The parts take their machines from it: `pipe`'s counted frame 1 is frame 1
(`Run.pipeAt`), `room`'s frames are the frames from `b₁` on (`Run.roomCtl`, `Run.roomEnter`), `pole`'s frames up to the touch are the frames from `b₂` on (`Run.atCtl`). These were links
(fields) before; now they are theorems from the definitions of the parts' machines.
The two changes of area are proved here from the same sequence (`Changes`): `Run.change₁` from a condition on the state at the entry and conditions at places of the pipe's frames (`PipeChangeEnd`),
the condition at the entry from the press of Start on the title, the frames from control to the entry and a part of the condition that stays assumed (`Run.entry₁`, `EntryKeep`),
`Run.change₂` from `SideChangeBound` and `SideChangeEnd`. A `lag` frame takes nothing off the number of frames left. In the first change this follows from `paused₁`: a `lag` frame is a paused frame.
In both changes `left` is not 0 before control: this follows from the time at the exit (`time₁`, `time₂`) and the first control (`ctlFirst₁`, `ctlFirst₂`).
-/

namespace Smbrta.Route

open CastleToLevel (ticks wait level_ge Frames Segs Flag Kind seen)
open PipeTransitionAll (Names)

/-- Up to the vertical pipe: the hypotheses of `PipeFrames.no_entry_of_start`, with the entry on real frames (`PipeWrites.rule_on_frameS`: the walk takes the position at the end of the move,
the frame model's `P₂`), and the frame `E` on which he enters. The frames up to `E`
are read from their own machines (`own`), and the frames not counted between them keep the speed and the position (`lags`, `LagFrames`, `LagPause`): `Pipe.reads`. So they follow each other
and keep the top speed: `Pipe.next`, `Pipe.speed`. That he stands still at control is `Run.still`, and that he is at the position of `m0` is `Run.pipePos`. That every frame from control
to the entry, and so the entering frame, starts in the idle loop in control is a theorem from the machine at control (`Pipe.startE`, `Run.pipeStart₁`). That the entry is after control
is a theorem too (`Pipe.one_le`, `Run.pipeOne`). The bound of the opening at frame `N` comes from each of the first `N` frames being a step of the opening's model (`opening`,
`Run.pipeOpenB`). -/
structure Pipe (sy : Syms) (m0 : Machine) (g : Nat) (N : Nat) (D : Int) (S : FrameKeep.RealRun) where
  amax : Int
  fr : Nat → TopSpeed.Frame (TopSpeed.top sy : Int) amax
  /-- the frame he enters the vertical pipe, counted -/
  E : Nat
  /-- the frames from control to the entry, counted or not, frames of `S`: the counted frame `t` begins at `S.seq (ixOf gap t)` (`Pipe.fm`, a definition). Each instruction
  is `Clean`, and each counted frame ends in control. A frame not counted ends paused (the low bit of the pause byte `g` is 1), and none of its instructions writes the pause
  byte through an index or a pointer. So it does not call the routine of the mode (`LagPause`), and it keeps the speed, the subspeed and the position and ends in control by the
  check of `LagFrames` -/
  lags : PipeFrames.Lags sy m0 g S E
  /-- its instructions up to the routine's write: stores through an index or a pointer, reads through a pointer, jumps, time -/
  clean : ∀ t, PipeEntryRule.Enters sy (lags.fm t) (lags.inp t) → ∀ n, PipeEntryRule.WriteStep sy (lags.fm t) (lags.inp t) n → ∀ j, j ≤ n →
    PipeWrites.Clean (PipeWrites.guardOf sy m0) (PipeEntryRule.trace (lags.fm t) (lags.inp t) j)
  /-- the pipe's right tile is only at its place, when the right foot is read -/
  tiles : ∀ t, PipeEntryRule.Enters sy (lags.fm t) (lags.inp t) → ∀ n, PipeEntryRule.WriteStep sy (lags.fm t) (lags.inp t) n → ∀ j, j ≤ n →
    PipeEntryRule.AtRead (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (lags.fm t) (lags.inp t) j) → PipeEntryRule.TilesOK (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (lags.fm t) (lags.inp t) j)
  /-- up to the write, it does not come to the scroll handler's store of the position (at the screen's edges), nor to the routine of the head's collision with a block -/
  edge : ∀ t, PipeEntryRule.Enters sy (lags.fm t) (lags.inp t) → ∀ n, PipeEntryRule.WriteStep sy (lags.fm t) (lags.inp t) n → ∀ j, j ≤ n →
    (PipeEntryRule.trace (lags.fm t) (lags.inp t) j).pc ≠ PipeWrites.edgeStore sy m0 ∧ (PipeEntryRule.trace (lags.fm t) (lags.inp t) j).pc ≠ PipeWrites.headAt sy m0
  /-- `P₂` is the position at the end of the move (`PlayerSubs`), up to the write: the frame model's `P₂` -/
  moved : ∀ t, PipeEntryRule.Enters sy (lags.fm t) (lags.inp t) → ∀ n j, PipeEntryRule.WriteStep sy (lags.fm t) (lags.inp t) n → j ≤ n →
    (PipeEntryRule.trace (lags.fm t) (lags.inp t) j).pc = sy.PlayerSubs → (fr t).P₂ = posP sy (PipeEntryRule.trace (lags.fm t) (lags.inp t) j)
  /-- each of the first `N` counted frames is a step of the opening's model (`OpenFrames.OpenRun`): the horizontal state follows `hstep`, the position moves by `16·v`, and the
  frames in the air follow the measured jump lengths. With the check of the opening this gives the old field `openB`, the bound at the end of frame `N` (`Run.pipeOpenB`). The bound
  up to frame `N` (the old field `openP`) is not needed: the position at control is that of `m0` (`Run.pipeP1`), and up to frame `N` the top speed bounds it
  (`PipeFrames.no_entry_of_start`). -/
  opening : OpenFrames.OpenRun sy m0 (Opening.jumpLens sy m0) N E lags.fm
  /-- frame `E` enters: the routine byte is the pipe's at its end -/
  enter : PipeEntryRule.Enters sy (lags.fm E) (lags.inp E)
  /-- the frames from 1 to `E` are read from the machines: frame `t` begins with the speed, subspeed and position of `fm t`, and before `E` it ends with those of its own end -/
  own : PipeFrames.ReadsOwn sy E lags.fm lags.inp fr

/-- the machine when the counted frame `t` begins: frame `ixOf gap t` of the run -/
abbrev Pipe.fm {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (p : Pipe sy m0 g N D S) : Nat → Machine := p.lags.fm

/-- the input of the counted frame `t` -/
abbrev Pipe.inp {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (p : Pipe sy m0 g N D S) : Nat → UInt8 := p.lags.inp

/-- **The machine of `pipe` at control is the real run's frame 1**: the counted frame 1 is frame 1 by the definition of `PipeFrames.ixOf` (the old link `Run.pipeAt`) -/
theorem Pipe.fm_one {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (p : Pipe sy m0 g N D S) : p.fm 1 = S.seq 1 := rfl

theorem ixOf_eq_zero (g : Nat → Nat) : ∀ e, e = 0 → PipeFrames.ixOf g e = 0
  | _, rfl => rfl

/-- **The entry is not on frame 0**: an entering frame ends with the pipe's routine (`Enters`), and frame 0 ends in control, with the routine of control (`hctl`). The two
routines differ (`hne`, a check on the ROM). So `1 ≤ E`: the old field `one_le`. -/
theorem Pipe.one_le {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hne : sy.Eng_PlayerCtrl.toUInt8 ≠ PipeEntryRule.vp sy)
    (hctl : controllable sy (S.seq 1) = true) (p : Pipe sy m0 g N D S) : 1 ≤ p.E := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have he : PipeEntryRule.Enters sy (S.seq (PipeFrames.ixOf p.lags.gap p.E)) (S.inp (PipeFrames.ixOf p.lags.gap p.E)) := p.enter
  rw [ixOf_eq_zero p.lags.gap p.E h] at he
  have h2 : PipeEntryRule.rt sy (S.seq 1) = PipeEntryRule.vp sy := by
    rw [S.next 0]
    exact he.2
  simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hctl
  have h3 := hctl.2
  unfold PipeEntryRule.rt at h2
  rw [h2] at h3
  apply hne
  rw [← h3]
  simp

/-- the frames from 1 to `E` read from the machines, the end of frame `t` from the machine of the next counted frame: the old field `reads`, from the frames not counted.
`hc` and `hk` are checks on the ROM, `hs` the start of the machine at control (`Run.pipeStart₁`). -/
theorem Pipe.reads {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) : PipeFrames.Reads sy p.E p.fm p.fr :=
  PipeFrames.reads_of_lags hc hk hp p.lags p.own hs

/-- **The entering frame starts in the idle loop, in control**: the old field `start`, by induction from the machine at control over every frame up to the entry
(`PipeFrames.Lags.starts`). `hc` and `hk` are checks on the ROM, `hs` the start of the machine at control (`Run.pipeStart₁`). -/
theorem Pipe.startE {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S)
    (hE : 1 ≤ p.E) (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) :
    PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm p.E) :=
  p.lags.startE hc hk hp hE hs

/-- the frames up to the entry follow each other: the old field `next`, from the frames read from the machines -/
theorem Pipe.next {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) :
    ∀ t, 1 ≤ t → t < p.E → PoleGrab.Next (p.fr t) (p.fr (t + 1)) :=
  PipeFrames.next_of_reads (p.reads hc hk hp hs)

/-- the speed at the end of frame `N` is at most the top speed, when `1 ≤ N ≤ E` and he stands still at control (`Run.still`): the old field `speed` -/
theorem Pipe.speed {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S)
    (hs₀ : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) (hs : SurfaceFrames.vOf sy (p.fm 1) = 0)
    (h16 : 16 ≤ (TopSpeed.top sy : Int)) (h1 : 1 ≤ N) (h2 : N ≤ p.E) :
    -(TopSpeed.top sy : Int) ≤ (p.fr N).v' ∧ (p.fr N).v' ≤ (TopSpeed.top sy : Int) :=
  PipeFrames.speed_end h16 (p.reads hc hk hp hs₀) hs N h1 h2

/-- the frames left in the change into the room, read from a machine: `PipeChangeBound.leftOf` with the table of the reference entry -/
abbrev left₁ (sy : Syms) (nm : Names) (m0 : Machine) : Machine → Nat :=
  PipeChangeBound.leftOf sy nm sy.EngVerticalPipe (PipeChangeBound.tableOf sy nm (PipeTransition.entry m0) 48 43) 43

/-- the frames left in the change out of the side pipe, read from a machine -/
abbrev left₂ (sy : Syms) (nm : Names) (m0 : Machine) : Machine → Nat :=
  SideChangeBound.leftAt sy nm (SideTransition.entry m0) 160 122

/-- the first `n` from `a` on, within `d`, with `p n`; `a + d` if there is none -/
def firstWith (p : Nat → Bool) : Nat → Nat → Nat
  | a, 0 => a
  | a, d + 1 => if p a = true then a else firstWith p (a + 1) d

theorem firstWith_ge (p : Nat → Bool) : ∀ (a d : Nat), a ≤ firstWith p a d
  | a, 0 => Nat.le_refl a
  | a, d + 1 => by
    simp only [firstWith]
    split
    · exact Nat.le_refl a
    · have := firstWith_ge p (a + 1) d
      omega

theorem firstWith_at (p : Nat → Bool) : ∀ (a d : Nat), p (a + d) = true → p (firstWith p a d) = true
  | a, 0, h => h
  | a, d + 1, h => by
    simp only [firstWith]
    split
    · assumption
    · exact firstWith_at p (a + 1) d (by rw [show a + 1 + d = a + (d + 1) by omega]; exact h)

theorem firstWith_first (p : Nat → Bool) : ∀ (a d n : Nat), a ≤ n → n < firstWith p a d → p n = false
  | a, 0, n, h1, h2 => by simp only [firstWith] at h2; omega
  | a, d + 1, n, h1, h2 => by
    simp only [firstWith] at h2
    split at h2
    · omega
    · rename_i hc
      by_cases hn : n = a
      · subst hn
        cases h : p n with
        | false => rfl
        | true => exact absurd h hc
      · exact firstWith_first p (a + 1) d n (by omega) h2

/-- the first frame from `a` on, within `d` frames, whose machine has control; `a + d` if there is none -/
abbrev firstCtl (sy : Syms) (seq : Nat → Machine) (a d : Nat) : Nat := firstWith (fun n => controllable sy (seq n)) a d

/-- the end of the room: the first frame from `b` on, within `d` frames, whose machine has left the player's routine (the routine of the reference machine `ScreenPage.refR`); `b + d`
if there is none -/
abbrev roomEnd (sy : Syms) (nmS : Names) (m0 : Machine) (seq : Nat → Machine) (b d : Nat) : Nat :=
  firstWith (fun n => (seq n).ram.get! (ScreenPage.placesR sy nmS m0).rtI != (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nmS m0).rtI) b d

/-- the entry into the vertical pipe: the first frame from 1 (the first control) on, within `d` frames, whose machine has no control; `1 + d` if there is none -/
abbrev upEnd (sy : Syms) (seq : Nat → Machine) (d : Nat) : Nat := firstWith (fun n => !controllable sy (seq n)) 1 d

/-- **The real frames of a run**, counted or not, numbered as `kind` numbers the frames: `seq n` is the machine when frame `n` begins and `inp n` its input, each frame the real
frame of the one before (`FrameKeep.RealRun`). `dA`, `dB`, `dR`, `d₂` bound the searches of the entries and the controls of the two changes (`Base.a₁`, `Base.b₁`, `Base.a₂`, `Base.b₂`).
The parts and the changes all take their machines from it. -/
structure Base extends FrameKeep.RealRun where
  dA : Nat
  dB : Nat
  dR : Nat
  d₂ : Nat

/-- **The entry into the vertical pipe**: the first machine from the first control on that has no control -/
def Base.a₁ (sy : Syms) (B : Base) : Nat := upEnd sy B.seq B.dA

/-- **The end of the first change**: the first machine with control from the entry on, within `dB` frames -/
def Base.b₁ (sy : Syms) (B : Base) : Nat := firstCtl sy B.seq (B.a₁ sy) B.dB

/-- **The entry into the side pipe**: the first machine from the room's first control on that has left the player's routine -/
def Base.a₂ (sy : Syms) (nmS : Names) (m0 : Machine) (B : Base) : Nat := roomEnd sy nmS m0 B.seq (B.b₁ sy) B.dR

/-- **The end of the second change**: the first machine with control from the entry on -/
def Base.b₂ (sy : Syms) (nmS : Names) (m0 : Machine) (B : Base) : Nat := firstCtl sy B.seq (B.a₂ sy nmS m0) B.d₂

/-- The two changes of area on the real machines of a run, those of `B`. `e₁`, `c₂`, `e₂`, `c₃` count frames without the `lag` frames, as `Segs` does. -/
structure Changes (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (B : Base) (kind : Nat → Kind) (e₁ c₂ e₂ c₃ : Nat) where
  /-- the first change: the machine after frame `e₁` is `B.seq a₁`, the first from the first control on that has no control (`Base.a₁`), and the machine after frame `c₂`
  is `B.seq b₁`, the first with control from there on (`Base.b₁`) -/
  ha₁ : seen kind (B.a₁ sy) = e₁ + 1
  hb₁ : seen kind (B.b₁ sy) = c₂ + 1
  /-- the part of the condition on the machine at the entry that the press of Start and the frames from control do not give: the bytes of `EntryKeep.restNames`
  (`Run.entry₁` gives the whole condition) -/
  entryRest₁ : EntryKeep.Rest d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))
  /-- each instruction of the frames from control to the entry is `Clean`, with the bytes that the frames keep, the buttons left and right and the pipe's timer
  (`EntryKeep.held`, `EntryKeep.timerI`) among the bytes that a store through an index or a pointer does not touch (that each of these frames starts in the idle loop in control
  is `Run.upStart₁`) -/
  upClean₁ : ∀ n, 1 ≤ n → n < B.a₁ sy → ∀ j, PipeWrites.Clean (EntryKeep.guardOf sy m0 d₁ (PipeTransition.entry m0)) (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- control within `dB` frames of the entry -/
  ctlBy₁ : controllable sy (B.seq (B.a₁ sy + B.dB)) = true
  /-- a `lag` frame is a paused frame: the low bit of the pause byte is set when it ends -/
  paused₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → kind n = .lag → PipeChangeEnd.Paused d₁ (B.seq (n + 1))
  /-- on a frame of the pipe's routine, each instruction meets the condition at the places -/
  places₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → PipeChangeBound.inPipe sy sy.EngVerticalPipe (B.seq n) = true → ∀ j, PipeChangeEnd.PlaceOK d₁.places (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- at the exit, the sound's bytes, the song and the screen buffer are as the condition says -/
  quiet₁ : ∀ n, B.a₁ sy ≤ n → n ≤ B.b₁ sy → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (B.seq n) →
    SideChangeEnd.Quiet (PipeChangeEnd.quietQ d₁ (PipeTransition.entry m0)) (B.seq n) ∧ PipeChangeEnd.SongAt d₁.song (B.seq n) ∧ PipeChangeEnd.SongAt d₁.xshape (B.seq n)
  /-- no Start on the frames of the game core after the pipe -/
  noStart₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → SideChangeEnd.coreFrame sy sy.EngVerticalPipe (B.seq n) = true → SideChangeEnd.noStart (B.inp n) = true
  /-- at the exit, the sound's pause flag is 0 and the game timer is not 000: the time is not up on the way -/
  time₁ : ∀ n, B.a₁ sy ≤ n → n ≤ B.b₁ sy → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (B.seq n) → SideChangeEnd.TimeOK d₁.nx (B.seq n)
  /-- the second change: the machine after frame `e₂` is `B.seq a₂`, the first from `b₁` on that has left the player's routine (`Base.a₂`), and the machine after frame `c₃`
  is `B.seq b₂`, the first with control from there on (`Base.b₂`) -/
  ha₂ : seen kind (B.a₂ sy nmS m0) = e₂ + 1
  hb₂ : seen kind (B.b₂ sy nmS m0) = c₃ + 1
  /-- at the entry, the bytes of the condition that the room does not give have the values of a reference machine: the routine (so the routine that the room left for is the side pipe's),
  the player's vertical position, the screen's buffer, the sound, the level's number (16 bytes). The room gives the rest (`ScreenPage.entry_rest`). -/
  entry₂ : ScreenPage.EntryRest nmS (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) (B.seq (B.a₂ sy nmS m0))
  /-- the room, from control to the side pipe: each instruction (the rows of the first change give `ScreenPage.Room` at control) -/
  roomSites : ∀ n, B.b₁ sy ≤ n → n < B.a₂ sy nmS m0 → ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nmS m0) (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- control within `d₂` frames of the entry -/
  ctlBy₂ : controllable sy (B.seq (B.a₂ sy nmS m0 + B.d₂)) = true
  /-- a `lag` frame ends paused -/
  paused₂ : ∀ n, B.a₂ sy nmS m0 ≤ n → n < B.b₂ sy nmS m0 → kind n = .lag → SideChangeEnd.Paused nx₂ (B.seq (n + 1))
  /-- no Start on the frames of the game core after the pipe -/
  noStart₂ : ∀ n, B.a₂ sy nmS m0 ≤ n → n < B.b₂ sy nmS m0 → SideChangeEnd.coreFrame sy sy.EngSidePipe (B.seq n) = true → SideChangeEnd.noStart (B.inp n) = true
  /-- at the exit, the game timer is not 000: the time is not up on the way -/
  time₂ : ∀ n, B.a₂ sy nmS m0 ≤ n → n ≤ B.b₂ sy nmS m0 → SideChangeBound.ExitAt (SideChangeBound.exitBytes sy nm₂ (SideChangeEnd.refExit (SideTransition.entry m0) 160)) (B.seq n) →
    SideChangeEnd.TimerOK nx₂ (B.seq n)
  /-- at the exit, the sound's pause bytes have the reference's values -/
  quiet₂ : ∀ n, B.a₂ sy nmS m0 ≤ n → n ≤ B.b₂ sy nmS m0 → SideChangeBound.ExitAt (SideChangeBound.exitBytes sy nm₂ (SideChangeEnd.refExit (SideTransition.entry m0) 160)) (B.seq n) →
    SideChangeEnd.Quiet (SideChangeEnd.quietBytes nx₂ (SideTransition.entry m0) 160) (B.seq n)

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {B : Base} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat}

/-- the indices of `B` as fields of the changes: `chg.a₁` is `base.a₁`, and so on -/
abbrev Changes.a₁ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : Nat := B.a₁ sy
abbrev Changes.b₁ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : Nat := B.b₁ sy
abbrev Changes.a₂ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : Nat := B.a₂ sy nmS m0
abbrev Changes.b₂ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : Nat := B.b₂ sy nmS m0

/-- each frame from the first control to the entry begins with control: it holds by the choice of `a₁` -/
theorem Changes.upStay (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : ∀ n, 1 ≤ n → n < B.a₁ sy → controllable sy (B.seq n) = true := fun n h1 h2 => by
  have h := firstWith_first _ 1 B.dA n h1 h2
  simpa using h

/-- the end of the first change is not before its entry: it holds by the choice of `b₁` -/
theorem Changes.order₁ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : B.a₁ sy ≤ B.b₁ sy := firstWith_ge _ _ B.dB

/-- control at the end of the first change, by the choice of `b₁` -/
theorem Changes.ctl₁ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : controllable sy (B.seq (B.b₁ sy)) = true :=
  firstWith_at (fun n => controllable sy (B.seq n)) _ B.dB C.ctlBy₁

/-- `b₁` is the first control after the entry, by the choice of `b₁` -/
theorem Changes.ctlFirst₁ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → controllable sy (B.seq n) = false :=
  fun n h1 h2 => firstWith_first (fun n => controllable sy (B.seq n)) _ B.dB n h1 h2

theorem Changes.roomOrder (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : B.b₁ sy ≤ B.a₂ sy nmS m0 := firstWith_ge _ (B.b₁ sy) B.dR

/-- each frame from the room's first control to the entry starts in the player's routine, by the choice of `a₂` -/
theorem Changes.roomStay (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : ∀ n, B.b₁ sy ≤ n → n < B.a₂ sy nmS m0 →
    (B.seq n).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nmS m0).rtI := fun n h1 h2 => by
  have h := firstWith_first _ (B.b₁ sy) B.dR n h1 h2
  simpa using h

theorem Changes.order₂ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : B.a₂ sy nmS m0 ≤ B.b₂ sy nmS m0 := firstWith_ge _ (B.a₂ sy nmS m0) B.d₂

/-- control at the end -/
theorem Changes.ctl₂ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : controllable sy (B.seq (B.b₂ sy nmS m0)) = true :=
  firstWith_at (fun n => controllable sy (B.seq n)) (B.a₂ sy nmS m0) B.d₂ C.ctlBy₂

/-- `b₂` is the first control after the entry, by the choice of `b₂` -/
theorem Changes.ctlFirst₂ (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : ∀ n, B.a₂ sy nmS m0 ≤ n → n < B.b₂ sy nmS m0 → controllable sy (B.seq n) = false :=
  fun n h1 h2 => firstWith_first (fun n => controllable sy (B.seq n)) (B.a₂ sy nmS m0) B.d₂ n h1 h2

/-- the entry is after control: `a₁` is not 0 -/
theorem Changes.one_le (_C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : 1 ≤ B.a₁ sy := firstWith_ge _ 1 B.dA

end

/-- the frames left, added to the frames counted, do not fall from `a` to `b` -/
theorem counted_ge {kind : Nat → Kind} {seq : Nat → Machine} {left : Machine → Nat} {a b : Nat} (hab : a ≤ b)
    (keep : ∀ n, a ≤ n → n < b → kind n = .lag → left (seq n) ≤ left (seq (n + 1)))
    (fall : ∀ n, a ≤ n → n < b → kind n ≠ .lag → left (seq n) ≤ left (seq (n + 1)) + 1) :
    seen kind a + left (seq a) ≤ seen kind b + left (seq b) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have h1 := ih (by omega) (fun n h2 h3 => keep n h2 (by omega)) (fun n h2 h3 => fall n h2 (by omega))
    have e : a + (d + 1) = a + d + 1 := rfl
    rw [e]
    simp only [seen]
    by_cases hk : kind (a + d) = .lag
    · have := keep (a + d) (by omega) (by omega) hk
      rw [if_pos hk]
      omega
    · have := fall (a + d) (by omega) (by omega) hk
      rw [if_neg hk]
      omega

/-- the frames counted from `a` to `b` are at most the frames from `a` to `b` -/
theorem seen_le_add (kind : Nat → Kind) {a b : Nat} (hab : a ≤ b) : seen kind b ≤ seen kind a + (b - a) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega)
    have e : a + (d + 1) = a + d + 1 := rfl
    rw [e]
    simp only [seen]
    split <;> omega

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {B : Base} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat}

/-- the first change as `PipeChangeEnd.PipeRun`, with the condition at the entry (`Run.entry₁`) -/
def Changes.run₁ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃)
    (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : PipeChangeEnd.PipeRun sy nm₁ d₁ (PipeTransition.entry m0) where
  seq := B.seq
  inp := B.inp
  next := B.next
  lag := fun n => kind n = .lag
  dec := fun _ => inferInstance
  cnt := seen kind
  hcnt := fun _ => rfl
  a := B.a₁ sy
  b := B.b₁ sy
  order := C.order₁
  entry := he
  atCtl := C.ctl₁
  lagPaused := C.paused₁
  places := C.places₁
  quiet := C.quiet₁
  noStart := C.noStart₁

/-- **The change into the room takes at least 91 frames**, from the condition at the entry and the conditions at the places. `hT` is what the check on the ROM gives. -/
theorem Changes.bound₁ {es : List Machine} (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : e₁ + 91 ≤ c₂ := by
  have h := (C.run₁ he).bound hT
  have h1 : (C.run₁ he).cnt (C.run₁ he).a = e₁ + 1 := C.ha₁
  have h2 : (C.run₁ he).cnt (C.run₁ he).b = c₂ + 1 := C.hb₁
  have h3 : PipeChangeEnd.timerF + PipeChangeEnd.afterF = 91 := rfl
  rw [h1, h2, h3] at h
  omega

/-- **`left` is not 0 before control** in the change into the room: from the time at the exit and the first control (`PipeChangeEnd.PipeRun.first`) -/
theorem Changes.first₁ {es : List Machine} (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → left₁ sy nm₁ m0 (B.seq n) ≠ 0 :=
  (C.run₁ he).first hT C.time₁ C.ctlFirst₁

end

/-- the checks on the ROM that the room needs: what one frame in the room does, two facts about the names, and the condition at the room's first control from the rows of the first change -/
structure RoomChecks (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) : Prop where
  facts : ScreenPage.RoomFacts sy nmS m0 160 (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0))
  timer : (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)).rkI = (ScreenPage.placesR sy nmS m0).timerI
  rt : ScreenPage.entryEnvOK sy nmS m0 (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) = true
  pipe : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) [PipeTransition.entry m0]
  start : ScreenStart.roomCheck sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {B : Base} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat}

/-- **The condition at the first control in the room**, from the rows of the time of the first change: the time at the exit and the first control -/
theorem Changes.roomAt (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    ScreenPage.Room sy nmS m0 (B.seq (B.b₁ sy)) :=
  ScreenStart.room_of_rows hR.start ((C.run₁ he).inRowsT hR.pipe C.time₁ C.ctlFirst₁) C.ctl₁

/-- the second change as `SideChangeEnd.EndRun` -/
def Changes.run₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃)
    (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : SideChangeEnd.EndRun sy nm₂ nx₂ (SideTransition.entry m0) 160 122 where
  seq := B.seq
  inp := B.inp
  next := B.next
  lag := fun n => kind n = .lag
  dec := fun _ => inferInstance
  cnt := seen kind
  hcnt := fun _ => rfl
  a := B.a₂ sy nmS m0
  b := B.b₂ sy nmS m0
  order := C.order₂
  entry := ScreenPage.entry_rest hR.facts hR.timer hR.rt B.next C.roomOrder (C.roomAt hR he) C.roomSites C.roomStay C.entry₂
  atCtl := C.ctl₂
  lagPaused := C.paused₂
  noStart := C.noStart₂
  quiet := C.quiet₂

/-- **The change out of the side pipe takes at least 282 frames**, from the single frames. `hS` and `hT` are what the checks on the ROM give. -/
theorem Changes.bound₂ {es : List Machine}
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : e₂ + 282 ≤ c₃ := by
  have h := (C.run₂ hR he).bound hS hT
  have h1 : (C.run₂ hR he).cnt (C.run₂ hR he).a = e₂ + 1 := C.ha₂
  have h2 : (C.run₂ hR he).cnt (C.run₂ hR he).b = c₃ + 1 := C.hb₂
  rw [h1, h2] at h
  omega

/-- **The room has at least one frame**: `b₁ < a₂`. The machine at the room's first control is in the player's routine (`Changes.roomAt`: the routine is a byte of the
condition), the machine at the entry is in the side pipe's (`entry₂` and the check `RoomChecks.rt`), and the two routines differ (`RoomChecks.facts`). -/
theorem Changes.b₁_lt_a₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    B.b₁ sy < B.a₂ sy nmS m0 := by
  have ho : B.b₁ sy ≤ B.a₂ sy nmS m0 := C.roomOrder
  refine Nat.lt_of_le_of_ne ho fun heq => ?_
  have h1 : (B.seq (B.b₁ sy)).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nmS m0).rtI :=
    ScreenPage.byte_of_ff ((C.roomAt hR he).bytes _ hR.facts.rt)
  have hV := hR.rt
  simp only [ScreenPage.entryEnvOK, ScreenPage.entryRtOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hV
  obtain ⟨⟨⟨hV1, hV2⟩, _⟩, _⟩ := hV
  obtain ⟨v, hv, hb⟩ := C.entry₂
  obtain ⟨a1, a2⟩ := hV1 v hv
  have h2 : (B.seq (B.a₂ sy nmS m0)).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.placesR sy nmS m0).eng := by
    rw [hb _ a1 hV2]
    exact a2
  rw [← heq, h1] at h2
  exact hR.facts.ne h2

end

/-- A run through 1-1, and every assumption of the bound. `base` is the one sequence of real frames of the run, counted or not. The parts are `pipe` (part a), `room` (part c),
`pole` (parts e, f), `chg` (parts b, d); each takes its machines from `base`: `pipe`'s counted frame 1 is frame 1 (`Run.pipeAt`), `room`'s first control is frame `b₁`
(`Run.roomCtl`) and its entering frame is a frame in the room (`Run.roomEnter`), `pole`'s control is frame `b₂` (`Run.atCtl`). The fields below them join these, the frames of
the run with their timers (`clock`), the start from the title (`title`) and the level change (from the castle to 1-2). -/
structure Run (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) (rN : RoomJoin.Nums)
    (b : Machine) (vs : List Jump.VS) (PA : PoleJoin.Box) (Ts J Nc : Nat) (F : Int) (q t0 : Nat) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (fc : FlagRule.Ctx)
    (tc : TitleStart.Ctx) where
  /-- the real frames of the run, numbered as `clock` numbers them, and the bounds of the searches of the two changes -/
  base : Base
  /-- `pipe`'s frames are frames of `base`, its counted frame 1 frame 1; the pause byte is that of the names of the title -/
  pipe : Pipe sy m0 tc.gps N D base.toRealRun
  /-- `room`'s frames are the frames of `base` from the end of the first change (`Base.b₁`) on -/
  room : RoomJoin.RoomRun sy m0 rN base.toRealRun (base.b₁ sy)
  /-- `pole` counts its frames from control above ground: the frames of `base` from the end of the second change (`Base.b₂`) on -/
  pole : PoleJoin.Run sy m0 b vs PA Ts J Nc F base.toRealRun (base.b₂ sy nmS m0)
  /-- control above ground -/
  Cs : Nat
  /-- the frame of each change on which no timer runs, counted as `pipe.E` is -/
  z₁ : Nat
  z₂ : Nat
  hz₁ : pipe.E ≤ z₁ ∧ z₁ < room.C
  hz₂ : room.E ≤ z₂ ∧ z₂ < Cs
  /-- the castle entry, counting all frames -/
  E : Nat
  /-- every frame up to the castle entry: its kind and its counters, by the rule on one frame -/
  clock : Frames q E ⟨pipe.E, z₁, room.C, room.E, z₂, Cs, Cs + pole.g, Cs + pole.c⟩
  /-- the two changes of area, on the real machines of `base` -/
  chg : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS base clock.kind pipe.E room.C room.E Cs
  /-- from the press of Start on the title to frame 0: one condition on the machine after the press, no Start on frame 0 in the game core (Start before it may pause the
  game), and frame 0 is the frame before the first control -/
  title : TitleStart.Begin sy tc base.seq base.inp
  /-- the counters of `clock` before frame 0 are those of the machine when frame 0 begins, as `flag` says of the machine after the castle entry (`t_E`, `ph_E`) -/
  read₀ : (clock.s 0).t = CastleToLevel.timerOf tc.nm (base.seq 0) ∧ clock.ph 0 = CastleToLevel.phaseOf tc.nm (base.seq 0)
  /-- the level change -/
  L : Nat
  /-- the frames after the castle entry, up to the level change, on the real machines of `base`: one condition at the castle entry, no Start, and the level change
  after frame `L` -/
  flag : FlagRule.After fc base.seq base.inp E clock.T clock.c L

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {fc : FlagRule.Ctx}
  {tc : TitleStart.Ctx}

/-- the frames on which no timer runs, other than one in each change -/
def Run.j (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Nat := R.clock.j

/-- the game timer at the castle entry -/
def Run.T (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Nat := R.clock.T

/-- the interval timer's phase at the castle entry -/
def Run.c (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Nat := R.clock.c

/-- **The machine of `pipe` at control is the machine when frame 1 begins**: `pipe`'s counted frame 1 is frame 1 of `base` (`Pipe.fm_one`). The old field `pipeAt`. -/
theorem Run.pipeAt (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.pipe.fm 1 = R.base.seq 1 :=
  R.pipe.fm_one

/-- **The vertical pipe is entered after control**: `1 ≤ pipe.E`, since frame 0 ends in control (`title`) and an entering frame does not (`Pipe.one_le`). `hK` gives the check
that the two routines differ. The old field `pipe.one_le`. -/
theorem Run.pipeOne (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : 1 ≤ R.pipe.E :=
  R.pipe.one_le (EntryKeep.keepOK_of_check hK.keep).ne R.title.ctl

/-- **The machine of `room` at first control is the machine at the end of the first change**: `room`'s frames begin at frame `b₁` of `base` (`RoomJoin.RoomRun.fm_C`).
The old field `roomCtl`. -/
theorem Run.roomCtl (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.fm R.room.C = R.base.seq (R.base.b₁ sy) :=
  R.room.fm_C

/-- **The frames of `pole` begin at the machine at the end of the second change**: `pole`'s frames begin at frame `b₂` of `base` (`PoleJoin.Run.seq0`). The old field `atCtl`. -/
theorem Run.atCtl (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.pole.seq 0 = R.base.seq (R.base.b₂ sy nmS m0) :=
  R.pole.seq0

/-- **Each frame from control to the vertical pipe's entry starts in the idle loop in control**: by induction from the press of Start on the title (`title`), under `upClean₁`.
Each of these frames begins with control, by the choice of `a₁`. `hB` and `hK` are the checks on the ROM. The old field `upStart₁`. -/
theorem Run.upStart₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, 1 ≤ n → n < R.base.a₁ sy → PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (R.base.seq n) :=
  EntryKeep.starts_of_title hB hK R.title R.base.next R.chg.upStay R.chg.upClean₁

/-- **The condition at the vertical pipe's entry**, from the press of Start on the title (`title`), the frames from control to the entry (`Run.upStart₁`, `upClean₁`) and the part
that stays assumed (`entryRest₁`). `hB` and `hK` are the checks on the ROM. The old field `entry₁`. -/
theorem Run.entry₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (R.base.seq (R.base.a₁ sy)) :=
  EntryKeep.entry_of_title hB hK R.title R.base.next R.chg.one_le (R.upStart₁ hB hK) R.chg.upClean₁ R.chg.entryRest₁

/-- the change into the room takes at least 91 frames -/
theorem Run.change₁ {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.pipe.E + 91 ≤ R.room.C :=
  R.chg.bound₁ hT₁ (R.entry₁ hB hK)

/-- the change out of the side pipe takes at least 282 frames -/
theorem Run.change₂ {es : List Machine} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.E + 282 ≤ R.Cs :=
  R.chg.bound₂ hS hT hR (R.entry₁ hB hK)

/-- every frame after the castle entry, up to the level change: its counters, by the rule on one frame. `hF` is the check of the ROM. -/
def Run.flagRun (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) :
    Flag fc.lim fc.w0 R.E R.clock.T R.clock.c R.L :=
  FlagRule.flagOf_after hF R.base.next R.flag

/-- the frames of the flag and the fireworks after the timer's count -/
def Run.Df (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) : Nat := (R.flagRun hF).D

/-- the segments are in order. `hgc`: the castle entry is after the touch (`PoleJoin.Run.afterTouch`, or the bound of the join). -/
theorem Run.segsOk (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (h₃ : R.room.C ≤ R.room.E) (hgc : R.pole.g < R.pole.c) :
    Segs.Ok ⟨R.pipe.E, R.z₁, R.room.C, R.room.E, R.z₂, R.Cs, R.Cs + R.pole.g, R.Cs + R.pole.c⟩ := by
  have h3 := R.hz₁
  have h4 := R.hz₂
  have h5 := hgc
  exact ⟨h3.1, h3.2, h₃, h4.1, h4.2, by simp only; omega, by simp only; omega⟩

/-- the castle entry's frame: the frames of the parts and the frames of `j` -/
theorem Run.hE (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.E = R.Cs + R.pole.c + R.j :=
  R.clock.hE

/-- **The machine when frame 0 begins**: the timer shows `t0`, the value before its first tick, and the interval timers' phase is 2. From the press of Start on the title;
`hB` is the check on the ROM. The old field `zero`. -/
theorem Run.zero (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) :
    CastleToLevel.timerOf tc.nm (R.base.seq 0) = t0 ∧ CastleToLevel.phaseOf tc.nm (R.base.seq 0) = 2 :=
  R.title.timer hB (R.base.next 0)

/-- **He stands still at control**, when frame 1 begins: from the press of Start on the title. The old field `pipe.still`. -/
theorem Run.still (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) :
    SurfaceFrames.vOf sy (R.pipe.fm 1) = 0 := by
  rw [R.pipeAt]
  exact R.title.still hB (R.base.next 0)

/-- **The machine at control of `pipe` starts a frame in the idle loop, in control**: from the press of Start on the title. `hB` and `hT` are checks on the ROM. -/
theorem Run.pipeStart₁ (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true)
    (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) :
    PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (R.pipe.fm 1) := by
  rw [R.pipeAt]
  exact StartRun.Begin.start₁G hB hT R.title (R.base.next 0)

/-- **The position at control is that of `m0`**: `pipe`'s machine at control is frame 1 (`Run.pipeAt`), and from the press of Start on the title frame 0 ends with the position
of `m0` (`StartRun.Begin.pos₁`). `hB` and `hP` are checks on the ROM. -/
theorem Run.pipePos (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true)
    (hP : StartRun.titlePosCheck sy tc m0 = true) : posP sy (R.pipe.fm 1) = posP sy m0 := by
  rw [R.pipeAt]
  exact StartRun.Begin.pos₁ hB hP R.title (R.base.next 0)

/-- **Frame 1 begins at the position of `m0`**: the frames are read from the machines (`Pipe.reads`), and `Run.pipePos`. With the top speed this bounds the position up to
frame `N` (`PipeFrames.no_entry_of_start`): the old field `openP`. `hc`, `hk`, `hp`, `hB`, `hP`, `hT`, `hK` are checks on the ROM. -/
theorem Run.pipeP1 (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 tc.gps = true)
    (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true)
    (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : (R.pipe.fr 1).P = posP sy m0 :=
  ((R.pipe.reads hc hk hp (R.pipeStart₁ hB hT)).P 1 (Nat.le_refl 1) (R.pipeOne hK)).trans (R.pipePos hB hP)

/-- **The horizontal state at control is that of `m0`**: from the press of Start on the title (`StartRun.Begin.hs₁`). `hB` and `hP` are checks on the ROM. -/
theorem Run.pipeHS (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true)
    (hP : StartRun.titlePosCheck sy tc m0 = true) : Potential.startHS sy (R.pipe.fm 1) = Potential.startHS sy m0 := by
  rw [R.pipeAt]
  exact StartRun.Begin.hs₁ hB hP R.title (R.base.next 0)

/-- **The bound of the opening at the end of frame `N`** (the old field `openB`): the first `N` frames are steps of the model (`opening`), and the model does not get past `D` in
`N` steps (`hopt`, the check of `Opening`). The start is that of `m0` (`Run.pipeHS`, `Run.pipePos`). `hc`, `hk`, `hp`, `hB`, `hP`, `hT` are checks on the ROM. -/
theorem Run.pipeOpenB (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 tc.gps = true)
    (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true)
    (hopt : ∀ k u, k ≤ N → Cert.Reach (Opening.succ sy m0 (Opening.jumpLens sy m0)) (Opening.start sy m0) k u → u.2 ≤ D) (h1 : 1 ≤ N)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : N < R.pipe.E → (R.pipe.fr N).P' ≤ posP sy m0 + D :=
  R.pipe.opening.openB (R.pipeHS hB hP) hopt (R.pipe.reads hc hk hp (R.pipeStart₁ hB hT)) (R.pipePos hB hP) h1

/-- the timer before frame 0, read from the machine when frame 0 begins -/
theorem Run.s_zero (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) : (R.clock.s 0).t = t0 :=
  R.read₀.1.trans (R.zero hB).1

/-- the phase before frame 0, read from the machine when frame 0 begins -/
theorem Run.ph_zero (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) : R.clock.ph 0 = 2 :=
  R.read₀.2.trans (R.zero hB).2

/-- the game timer at the castle entry: it stops at the touch, and each stretch of play takes at most one off per `q` frames, rounded up -/
theorem Run.hT (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) (hq₁ : 1 ≤ q) (h₃ : R.room.C ≤ R.room.E)
    (hgc : R.pole.g < R.pole.c) :
    t0 ≤ R.T + (ticks q R.pipe.E + ticks q (R.room.E - R.room.C) + ticks q R.pole.g) := by
  have h := R.clock.hT hq₁ (R.segsOk h₃ hgc) (R.s_zero hB)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

/-- the interval timer's phase at the castle entry: the grid of the last wait -/
theorem Run.hc (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) (h₃ : R.room.C ≤ R.room.E)
    (hgc : R.pole.g < R.pole.c) :
    (R.c + R.E) % 21 = (3 + R.j) % 21 :=
  R.clock.hc (R.segsOk h₃ hgc) (R.ph_zero hB)

/-- the room's first control comes before the entry into the side pipe: `room.C ≤ room.E`, from the frames of `base` (the counts `chg.hb₁`, `chg.ha₂`) -/
theorem Run.room_le (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.C ≤ R.room.E := by
  have h1 : seen R.clock.kind (R.base.b₁ sy) = R.room.C + 1 := R.chg.hb₁
  have h2 : seen R.clock.kind (R.base.a₂ sy nmS m0) = R.room.E + 1 := R.chg.ha₂
  have h3 := CastleToLevel.seen_mono R.clock.kind R.chg.roomOrder
  omega

/-- **The state at control above ground**, on the real machines: it comes from the last row of the change, under the change's conditions. `left` is not 0 before control,
from the time at the exit and the first control (`SideChangeEnd.EndRun.first`). `hc` is the check on the ROM. -/
theorem Run.start {es : List Machine} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hc : SurfaceFrames.startCheck sy nm₂ nx₂ (SideTransition.entry m0) 160 122 PA = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    SurfaceFrames.Start sy PA (R.pole.seq 0) := by
  rw [R.atCtl]
  exact SurfaceFrames.EndRun.start hS hT hc (R.chg.run₂ hR (R.entry₁ hB hK)) ((R.chg.run₂ hR (R.entry₁ hB hK)).firstF hT R.chg.time₂ R.chg.ctlFirst₂)

/-- **The machine at control above ground, as the walk of one whole frame needs it**, on the real machines: the start of a frame in control, with the castle flag down. From the last
row of the change, under the same conditions as `Run.start`. `hc` and `hk` are checks on the ROM. With `PoleJoin.Run.keep` it gives no castle flag up to the touch
(`PoleJoin.Run.noCastle_of`) and the start of every frame up to the touch (`FrameKeep.Frames.start`). -/
theorem Run.atCtl₀ {es : List Machine} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hc : SurfaceFrames.startCheck sy nm₂ nx₂ (SideTransition.entry m0) 160 122 PA = true)
    (hk : ControlStart.ctlCheck sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    FrameKeep.AtCtl sy m0 (R.pole.seq 0) := by
  rw [R.atCtl]
  exact ControlStart.EndRun.atCtl hS hT hc hk (R.chg.run₂ hR (R.entry₁ hB hK)) ((R.chg.run₂ hR (R.entry₁ hB hK)).firstF hT R.chg.time₂ R.chg.ctlFirst₂)

/-- **The state at first control in the room**, on the real machines: it comes from the last row of the change into the room, under the change's conditions and `Changes.first₁`. `hc` is the check on
the ROM. -/
theorem Run.roomStart {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hc : RoomStart.startCheck sy nm₁ d₁ (PipeTransition.entry m0) (RoomJoin.room sy rN) rN.startY rN.startW rN.fallF = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    RoomJoin.StartAt sy rN (R.room.fm R.room.C) := by
  rw [R.roomCtl]
  exact RoomStart.PipeRun.start hT₁ hc (R.chg.run₁ (R.entry₁ hB hK)) (R.chg.first₁ hT₁ (R.entry₁ hB hK))

/-- **The frame of `room` that enters the side pipe is a frame of `base` in the room**, from its first control to the entry: frame `b₁ + (E − 1 − C)`. It is before `a₂`
since the room counts no more frames than there are (`seen_le_add`, with `chg.hb₁`, `chg.ha₂`) and the room has a frame (`Changes.b₁_lt_a₂`). `hR`, `hB`, `hK` are
checks on the ROM. The old field `roomEnter`. -/
theorem Run.roomEnter (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∃ k, R.base.b₁ sy ≤ k ∧ k < R.base.a₂ sy nmS m0 ∧ R.room.fm (R.room.E - 1) = R.base.seq k ∧ R.room.pad R.room.E = R.base.inp k := by
  refine ⟨R.base.b₁ sy + (R.room.E - 1 - R.room.C), Nat.le_add_right _ _, ?_, rfl, rfl⟩
  have h1 : seen R.clock.kind (R.base.b₁ sy) = R.room.C + 1 := R.chg.hb₁
  have h2 : seen R.clock.kind (R.base.a₂ sy nmS m0) = R.room.E + 1 := R.chg.ha₂
  have h3 := seen_le_add R.clock.kind R.chg.roomOrder
  have h4 := R.chg.b₁_lt_a₂ hR (R.entry₁ hB hK)
  omega

/-- **The side pipe's tiles at the reads of the room's entering frame**, on the real machines: `RoomMap.map_of_rows` on the frames of `base` in the room, from the rows of the change into
the room, and `Run.roomEnter`. `hT₁`, `hM`, `hS` are checks on the ROM. The old field `room.tiles`. -/
theorem Run.roomTiles {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.TilesE := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter hR hB hK
  have he := R.entry₁ hB hK
  have h := (RoomMap.map_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay).2 k h1 h2
  intro n j _ _ ha
  rw [e1, e2] at ha ⊢
  exact h j ha

/-- **The room's entering frame starts in control**, on the real machines: `RoomMap.start_of_rowsF` on the frames of `base` in the room, from the rows of the change into the room,
and `Run.roomEnter`. `hT₁`, `hM`, `hS`, `hF` are checks on the ROM. The old field `room.startE`. -/
theorem Run.roomStartE {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hF : RoomMap.startCheckF sy nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.StartE := by
  obtain ⟨k, h1, h2, e1, _⟩ := R.roomEnter hR hB hK
  have he := R.entry₁ hB hK
  have h := RoomMap.start_of_rowsF (a := R.base.a₂ sy nmS m0) hM hS hF R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay k h1 h2
  show PipeWrites.FrameStart (SideFrame.roomG sy m0) (PipeEntryRule.envOf m0) (R.room.fm (R.room.E - 1))
  rw [e1]
  exact h

/-- **`Clean` on each instruction of the room's entering frame up to the write**, on the real machines: `RoomMap.clean_of_rows` on the frames of `base` in the room, and
`Run.roomEnter`. The old field `room.cleanE`. -/
theorem Run.roomCleanE {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.CleanE := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter hR hB hK
  have he := R.entry₁ hB hK
  have h := RoomMap.clean_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay k h1 h2
  intro n _ j _
  show PipeWrites.Clean (SideFrame.roomG sy m0) (PipeEntryRule.trace (R.room.fm (R.room.E - 1)) (R.room.pad R.room.E) j)
  rw [e1, e2]
  exact h j

/-- **The room's entering frame does not come to the routine of the head's collision with a block**, on the real machines: `RoomMap.head_of_rows` on the frames of `base` in the
room, and `Run.roomEnter`. Once part of the field `room.edgeE`. -/
theorem Run.roomHeadE {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.HeadE := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter hR hB hK
  have he := R.entry₁ hB hK
  have h := RoomMap.head_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay k h1 h2
  intro j
  show (PipeEntryRule.trace (R.room.fm (R.room.E - 1)) (R.room.pad R.room.E) j).pc ≠ PipeWrites.headAt sy m0
  rw [e1, e2]
  exact h j

/-- **No frame of `room` before the entry comes to the head's collision with a block**, on the real machines: neither to its routine (`PipeWrites.headAt`) nor to the bump on a
solid block (`SideFrame.bumpAt`). `RoomMap.head_of_rows` and `RoomMap.bump_of_rows` on the frames of `base` in the room: the room's frame `n + 1` is frame `b₁ + (n − C)`,
before the entering frame (`Run.roomEnter`), so before `a₂`. `hT₁`, `hM`, `hS`, `hR`, `hB`, `hK` are checks on the ROM. With it the field `room.vframes` no longer asks that he does
not hit his head. -/
theorem Run.roomBump {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → ∀ j, (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc ≠ PipeWrites.headAt sy m0 ∧
      (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc ≠ SideFrame.bumpAt sy m0 := by
  intro n hC hE j
  have h1 : seen R.clock.kind (R.base.b₁ sy) = R.room.C + 1 := R.chg.hb₁
  have h2 : seen R.clock.kind (R.base.a₂ sy nmS m0) = R.room.E + 1 := R.chg.ha₂
  have h3 := seen_le_add R.clock.kind R.chg.roomOrder
  have h4 := R.chg.b₁_lt_a₂ hR (R.entry₁ hB hK)
  have hk : R.base.b₁ sy + (n - R.room.C) < R.base.a₂ sy nmS m0 := by omega
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁
  exact ⟨RoomMap.head_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ (Nat.le_add_right _ _) hk j,
    RoomMap.bump_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ (Nat.le_add_right _ _) hk j⟩

/-- **The room's entering frame ends with the position at or right of the mouth's left end**, on the real machines: `SideEntryRest.mouth_of_rows` on the frames of `base` in
the room (the walk of `SideEntryEnd` up to the write, the walk of the room from there to the frame's end), at the frame of `Run.roomEnter`. `hT₁`, `hM`, `hS`, `hF`, `hEnd`, `hRest`
are checks on the ROM. With the reading of `P(E)` at the frame's end (`room.read_PE`) it replaces the old field `room.movedE`. -/
theorem Run.roomMouthE {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hF : RoomMap.startCheckF sy nmS m0 = true)
    (hEnd : SideEntryEnd.sideEntryEndCheck sy m0 = true) (hRest : SideEntryRest.restCheck sy nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    SidePipe.mouthP sy 0 ≤ posP sy (PipeTransition.frame (R.room.fm (R.room.E - 1)) (R.room.pad R.room.E)) := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter hR hB hK
  have he := R.entry₁ hB hK
  have hen : SideEntryRule.Enters sy (R.base.seq k) (R.base.inp k) := by
    rw [← e1, ← e2]
    exact R.room.enters
  rw [e1, e2]
  exact SideEntryRest.mouth_of_rows (a := R.base.a₂ sy nmS m0) hM hS hF hEnd hRest R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁)
    R.chg.ctl₁ R.chg.roomSites R.chg.roomStay h1 h2 hen

/-- **What the room's frames give**: the entering frame ends with the position at or right of the mouth, and no frame before it comes to the head's collision with a block -/
theorem Run.inRoom {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hF : RoomMap.startCheckF sy nmS m0 = true)
    (hEnd : SideEntryEnd.sideEntryEndCheck sy m0 = true) (hRest : SideEntryRest.restCheck sy nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.InRoom :=
  ⟨R.roomMouthE hT₁ hM hS hF hEnd hRest hR hB hK, R.roomBump hT₁ hM hS hR hB hK⟩

/-- the frames after the timer's count: at least 33 -/
theorem Run.hD (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) : 33 ≤ R.Df hF :=
  (R.flagRun hF).hD

/-- the level change is not before the first grid point after the sum -/
theorem Run.hL (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) (hsy : fc.sy = sy)
    (hw : 6 ≤ sy.StarFlagDelay.toNat) : R.E + R.T + R.Df hF + 107 + wait R.c (R.T + R.Df hF) ≤ R.L :=
  (R.flagRun hF).hL (by show 6 ≤ fc.sy.StarFlagDelay.toNat; rw [hsy]; exact hw)

/-- **The join.** The bounds of the parts give the bound on the level change. The touch comes as the three cases of `PoleJoin.touch_castle`.
`hT₁`, `hS` and `hT` are the checks of the two changes on the ROM, `hR` those of the room, `hF` that of the star flag, `hB` that of the start from the title, `hK` those of the
frames from control to the vertical pipe's entry. -/
theorem level_ge_of_parts {es es₁ : List Machine} (hq : 2 ≤ q) (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hw : 6 ≤ sy.StarFlagDelay.toNat)
    (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) (hsy : fc.sy = sy) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    (h₁ : 368 ≤ R.pipe.E)
    (h₃ : R.room.C + 111 ≤ R.room.E)
    (h₅ : (234 ≤ R.pole.g ∧ R.pole.g + 132 ≤ R.pole.c) ∨ (240 ≤ R.pole.g ∧ R.pole.g ≤ 241 ∧ R.pole.g + 126 ≤ R.pole.c) ∨
      (242 ≤ R.pole.g ∧ R.pole.g + 125 ≤ R.pole.c)) :
    1748 + R.j ≤ R.L := by
  have hc1 := R.change₁ hT₁ hB hK
  have hc2 := R.change₂ hS hT hR hB hK
  have hE := R.hE
  have hgc : R.pole.g < R.pole.c := by
    rcases h₅ with ⟨_, b⟩ | ⟨_, _, b⟩ | ⟨_, b⟩ <;> omega
  exact level_ge (P1 := R.pipe.E) (X1 := R.room.C - R.pipe.E) (P2 := R.room.E - R.room.C) (X2 := R.Cs - R.room.E)
    (P3 := R.pole.g) (W := R.pole.c - R.pole.g) hq ht0 h₁ (by omega) (by omega) (by omega)
    (by rcases h₅ with ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b⟩
        · exact Or.inl ⟨a, by omega⟩
        · exact Or.inr (Or.inl ⟨a, b, by omega⟩)
        · exact Or.inr (Or.inr ⟨a, by omega⟩))
    (by omega) (R.hT hB (by omega) (by omega) hgc) (R.hD hF) (R.hc hB (by omega) hgc) (R.hL hF hsy hw)

end Smbrta.Route
