import Theorems.PipeEntry
import Theorems.PipeEntryRule
import Theorems.PipeWrites
import Theorems.PipeFrames
import Theorems.OpenFrames
import Theorems.LagFrames
import Theorems.RoomJoin
import Theorems.RoomVert
import Theorems.RoomPair
import Theorems.RoomBlocks
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
import Theorems.SideChangeSound
import Theorems.SidePause
import Theorems.RoomPause
import Theorems.PhaseFrame
import Theorems.RoomMusic
import Theorems.EntryRoutine
import Theorems.UpClean
import Theorems.AreaKeep
import Theorems.EntryHeight
import Theorems.EntryBuffer

/-!
# The whole route: 1-2 does not start before frame 1748

The parts of the route are joined here into one statement. `Run` lists what a run has to satisfy, one named field per assumption. `level_ge_of_parts` is the
arithmetic of the join: from the bounds of the parts it concludes the level change's frame. The private proof applies the theorems of the parts for the numbers of the game.
No field is proved for every run: this says which assumptions the bound rests on. Page: `1-1/0-1-Route.md`.

Frames are numbered from the first controllable frame of 1-1. The fields of the parts (`pipe.E`, `room.C`, `room.E`, `Cs`, `pole.g`, `pole.c`) count frames without the `lag` frames of
`CastleToLevel.Frames`. `E` and the frames of `clock` count all frames. The three facts about the timers in the whole run are proved here from the rule on single frames: `Run.hE`, `Run.hT`, `Run.hc`.
The counters before frame 0 come from the machine when frame 0 begins (`read₀`), as those after the castle entry come from the machine after it (`flag`). That machine shows `t0`
and the phase 2, and the speed at control is 0: this comes from the press of Start on the title (`title`, `TitleStart.Begin`), for a run from power-on with nothing
assumed of the machine after the press (`TitleBoot.Run`), for another run from one condition on that machine.
The frames after the castle entry are in `flag`, on the real machines of `base`. From one condition on the first frame after the castle entry where the area parser is
done (`flag.G`), the rule on the frames before it (`flag.pre`) and the check `hF` of the ROM, the rule holds on every frame up to the level change, with any inputs: a frame
that ends paused keeps the counters (`FlagRule.flagOf_after`). The two facts about these frames are proved from it: `Run.hD`, `Run.hL`.

The run has one sequence of real machines, every frame counted or not (`Base`, the field `base`). The parts take their machines from it: `pipe`'s counted frames are the
frames from frame 1 on that end not paused (`Run.pipeKeep₁`), `room`'s frames are the frames from `b₁` on that end not paused (`Run.roomCtl`, `Run.roomEnter`;
in the room a paused frame is a `lag` frame, `roomLag`, so `room` finds its frames by `a₂`: `Run.roomMany`), `pole`'s frames up to the touch are the frames from `b₂` on (`Run.atCtl`). These were links
(fields) before; now they are theorems from the definitions of the parts' machines.
The two changes of area are proved here from the same sequence (`Changes`): `Run.change₁` from a condition on the state at the entry and conditions at places of the pipe's frames (`PipeChangeEnd`),
the condition at the entry from the press of Start on the title, the frames from control to the entry and a part of the condition that stays assumed (`Run.entry₁`, `EntryKeep`),
`Run.change₂` from `SideChangeBound` and `SideChangeEnd`. A `lag` frame takes nothing off the number of frames left. In the first change this follows from `paused₁`: a `lag` frame is a paused frame.
In both changes `left` is not 0 before control: this follows from the time at the vertical pipe's entry (`time₁`) and at the side pipe's entry (`time₂`), and the first control (`ctlFirst₁`, `ctlFirst₂`).
Above ground the kinds of `clock` are not tied to the machines. When each frame from `b₂` to `E` is a `lag` frame exactly when it ends paused (`Run.LagUp`, not a field), the
castle entry `E` of `clock` is the counted frame `c` of `pole` (`Run.castle_join`); page `1-1/0-5-2-1-CastleJoin.md`. `LagUp` follows from the phase of `clock` being the
machine's on each frame above ground (`Run.PhaseUp`) and the machine's rule of the phase on each frame (`Run.lagUp_of`); that rule is proved on the frames up to the touch's
frame (`PhaseFrame`, page `1-1/0-5-2-1-1-PhaseFrame.md`).
-/

namespace Smbrta.Route

open CastleToLevel (ticks wait level_ge Frames Segs Flag Kind seen)
open PipeTransitionAll (Names)

/-- Up to the vertical pipe: the hypotheses of `PipeFrames.no_entry_of_start`, with the entry on real frames (`PipeWrites.rule_on_frameS`: the walk takes the position at the end of the move,
the frame model's `P₂`), and the frame `E` on which he enters. The frames up to `E`
are read from their own machines (`own`), and the frames not counted between them keep the speed and the position (`lags`, `LagFrames`, `LagPause`): `Pipe.reads`. So they follow each other
and keep the top speed: `Pipe.next`, `Pipe.speed`. That he stands still at control is `Run.still`, and that he is at the position of `m0` is `Run.pipePos`. That every frame from control
to the entry, and so the entering frame, starts in the idle loop in control is a theorem from the machine at control (`Pipe.startE`, `Run.pipeStart₁`). That the entry is after control
is a theorem too (`Pipe.one_le`, `Run.pipeOne`). The bound of the opening at frame `N` comes from each of the first `N` frames being a step of the opening's model
(`Run.pipeOpening`, `Run.pipeOpenB`), which follows from conditions on single frames (`opening`). The conditions on each instruction that were fields here (`lags.clean`,
`clean`, `opening.cleanK`) follow from the one condition `chg.upCleanU` (`Run.lagsClean`, `Run.pipeClean`, `Run.pipeReal`). -/
structure Pipe (sy : Syms) (m0 : Machine) (g : Nat) (N : Nat) (D : Int) (S : FrameKeep.RealRun) where
  amax : Int
  fr : Nat → TopSpeed.Frame (TopSpeed.top sy : Int) amax
  /-- the frame he enters the vertical pipe, counted -/
  E : Nat
  /-- the frames from frame 1 to the entry, counted or not, frames of `S`: the counted frame `t` begins at `S.seq (ixP g S dP t)` (`Pipe.fm`, a definition): a counted frame
  is a frame that ends with the game not paused (the low bit of the pause byte `g` is 0), found within `dP` frames, so a frame not counted ends paused, by the definition.
  Each counted frame ends in control. Each instruction is `Clean` with the pause byte protected too (no store through an index or a pointer writes it): the old field
  `lags.clean`, now `Run.lagsClean` from `chg.upCleanU`. So a frame not counted does not call the routine of the mode (`LagPause`), and it keeps the speed, the subspeed,
  the position and the bytes of `LagFrames.lagI` and ends in control by the check of `LagFrames`. The instructions of the entering frame are `Clean` (the old field
  `clean`, now `Run.pipeClean`). -/
  lags : PipeFrames.Lags sy m0 g S E
  /-- the pipe's right tile is only at its place, when the right foot is read -/
  tiles : ∀ t, PipeEntryRule.Enters sy (lags.fm t) (lags.inp t) → ∀ n, PipeEntryRule.WriteStep sy (lags.fm t) (lags.inp t) n → ∀ j, j ≤ n →
    PipeEntryRule.AtRead (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (lags.fm t) (lags.inp t) j) → PipeEntryRule.TilesOK (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (lags.fm t) (lags.inp t) j)
  /-- up to the write, it does not come to the scroll handler's store of the position (at the screen's edges), nor to the routine of the head's collision with a block -/
  edge : ∀ t, PipeEntryRule.Enters sy (lags.fm t) (lags.inp t) → ∀ n, PipeEntryRule.WriteStep sy (lags.fm t) (lags.inp t) n → ∀ j, j ≤ n →
    (PipeEntryRule.trace (lags.fm t) (lags.inp t) j).pc ≠ PipeWrites.edgeStore sy m0 ∧ (PipeEntryRule.trace (lags.fm t) (lags.inp t) j).pc ≠ PipeWrites.headAt sy m0
  /-- `P₂` is the position at the end of the move (`PlayerSubs`), up to the write: the frame model's `P₂` -/
  moved : ∀ t, PipeEntryRule.Enters sy (lags.fm t) (lags.inp t) → ∀ n j, PipeEntryRule.WriteStep sy (lags.fm t) (lags.inp t) n → j ≤ n →
    (PipeEntryRule.trace (lags.fm t) (lags.inp t) j).pc = sy.PlayerSubs → (fr t).P₂ = posP sy (PipeEntryRule.trace (lags.fm t) (lags.inp t) j)
  /-- the first `N` counted frames, on single frames, their instructions and their starts (`OpenFrames.RealB`): the instructions of every frame up to the counted frame `N` meet
  `OpenMap.MapOK` (the read of the block buffer routine in the first buffer), from the scroll handler on it changes none of five horizontal bytes, does not set a speed
  that is not 0 to 0 and leaves the collision bits all 1 (`after`, `OpenFrames.AfterR`; frame `N` may also end at the left end of the level), the page is not 255 when
  the counted frame `N + 1` begins; from the return of the collision routine on seven bytes of the vertical model do not change (`afterV`). After the scroll handler
  the moving direction, the running speed, the stored speed and the speed are theorems (the walks of part e, `OpenFrames.Real.frame_step`), and after the return of
  the collision routine four more bytes of the vertical model (`OpenFrames.Real.afterVS`, the walk of `OpenAfter`). That none of the instructions of a counted frame
  writes the routine, the mode or the task by its address (the old field `noStore`) is a theorem: the frame ends in control (`lags.ctl`, `OpenFrames.Real.noStore`,
  the walks of `OpenStore`).
  The flat ground (the old field `flat`) is a theorem (`OpenFrames.Real.flat`, the walks of `OpenFlat`); so is the vertical model on each frame
  in the air or with a jump (the old field `vert`, `OpenFrames.Real.vertOK`, the walks of `OpenAir` and `OpenVert`), and with it the lengths of the jumps (the old field
  `jump`, `OpenFrames.Real.jumpV`, the search of `OpenJump`) and the ground's height of every counted frame on the ground (the old field `ground`,
  `OpenFrames.Real.ground_all`).
  The player's state 0, 1 or 2 and no jumpspring when each frame begins are a theorem (`OpenFrames.Real.stSpring`). That a frame does not end during the movement is a theorem
  (`FrameModel.trace_inFrame` with `CleanK.time`), and so is the page at the ends of the frames before frame `N` (the search of `OpenLeft`). That each of them is a step of the opening's model (the old field
  `opening`; `OpenFrames.OpenRunM`: frame `N` is a step or ends at the left end of the level) is a theorem (`OpenFrames.Real.toRunM`): the movement by
  `FrameModel.move_model`, the state at the player's routine by the walk of `CtrlKeep`. With the check of the opening this gives the bound at the end of frame `N`
  (`Run.pipeOpenB`). The bound up to frame `N` is not needed: the position at control
  is that of `m0` (`Run.pipeP1`), and up to frame `N` the top speed bounds it (`PipeFrames.no_entry_of_start`). That the instructions of each meet `CleanK` of
  `FrameKeep.guardE` (the old field `opening.cleanK`) follows from `chg.upCleanU` (`Run.pipeReal`). -/
  opening : OpenFrames.RealB sy m0 (Opening.jumpLens sy m0) N E lags
  /-- frame `E` enters: the routine byte is the pipe's at its end -/
  enter : PipeEntryRule.Enters sy (lags.fm E) (lags.inp E)
  /-- the frames from 1 to `E` are read from the machines: frame `t` begins with the speed, subspeed and position of `fm t`, and before `E` it ends with those of its own end -/
  own : PipeFrames.ReadsOwn sy E lags.fm lags.inp fr

/-- the machine when the counted frame `t` begins: frame `ixP g S dP t` of the run -/
abbrev Pipe.fm {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (p : Pipe sy m0 g N D S) : Nat → Machine := p.lags.fm

/-- the input of the counted frame `t` -/
abbrev Pipe.inp {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (p : Pipe sy m0 g N D S) : Nat → UInt8 := p.lags.inp

/-- **The frames from frame 1 to the counted frame 1 keep the bytes of the walk** (`LagFrames.lagI`): they end paused (`PipeFrames.lags_keep0`). `hc`, `hk` and `hp` are
checks on the ROM, `hs` the start of frame 1. -/
theorem Pipe.keep₁ {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S) (hcl : p.lags.CleanP) (hE : 1 ≤ p.E)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) :
    ∀ b ∈ LagFrames.lagI sy, (p.fm 1).ram.get! b = (S.seq 1).ram.get! b :=
  PipeFrames.lags_keep0 hc hk hp p.lags hcl hs 0 hE

/-- **The entry is not on frame 0**: an entering frame ends with the pipe's routine (`Enters`), and frame 0 ends in control, with the routine of control (`hctl`). The two
routines differ (`hne`, a check on the ROM). So `1 ≤ E`: the old field `one_le`. -/
theorem Pipe.one_le {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hne : sy.Eng_PlayerCtrl.toUInt8 ≠ PipeEntryRule.vp sy)
    (hctl : controllable sy (S.seq 1) = true) (p : Pipe sy m0 g N D S) : 1 ≤ p.E := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have he : PipeEntryRule.Enters sy (S.seq (PipeFrames.ixP g S p.lags.dP p.E)) (S.inp (PipeFrames.ixP g S p.lags.dP p.E)) := p.enter
  generalize p.lags.dP = d at he
  rw [h] at he
  change PipeEntryRule.Enters sy (S.seq 0) (S.inp 0) at he
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
`hc` and `hk` are checks on the ROM, `hs` the start of frame 1 (`Run.pipeStart₁`). -/
theorem Pipe.reads {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S) (hcl : p.lags.CleanP)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) : PipeFrames.Reads sy p.E p.fm p.fr :=
  PipeFrames.reads_of_lags hc hk hp p.lags hcl p.own hs

/-- **The entering frame starts in the idle loop, in control**: the old field `start`, by induction from the machine at control over every frame up to the entry
(`PipeFrames.Lags.starts`). `hc` and `hk` are checks on the ROM, `hs` the start of frame 1 (`Run.pipeStart₁`). -/
theorem Pipe.startE {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S) (hcl : p.lags.CleanP)
    (hE : 1 ≤ p.E) (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) :
    PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm p.E) :=
  p.lags.startE hc hk hp hcl hE hs

/-- the frames up to the entry follow each other: the old field `next`, from the frames read from the machines -/
theorem Pipe.next {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S) (hcl : p.lags.CleanP)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) :
    ∀ t, 1 ≤ t → t < p.E → PoleGrab.Next (p.fr t) (p.fr (t + 1)) :=
  PipeFrames.next_of_reads (p.reads hc hk hp hcl hs)

/-- the speed at the end of frame `N` is at most the top speed, when `1 ≤ N ≤ E` and he stands still at control (`Run.still`): the old field `speed` -/
theorem Pipe.speed {sy : Syms} {m0 : Machine} {g N : Nat} {D : Int} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (p : Pipe sy m0 g N D S) (hcl : p.lags.CleanP)
    (hs₀ : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (hs : SurfaceFrames.vOf sy (p.fm 1) = 0)
    (h16 : 16 ≤ (TopSpeed.top sy : Int)) (h1 : 1 ≤ N) (h2 : N ≤ p.E) :
    -(TopSpeed.top sy : Int) ≤ (p.fr N).v' ∧ (p.fr N).v' ≤ (TopSpeed.top sy : Int) :=
  PipeFrames.speed_end h16 (p.reads hc hk hp hcl hs₀) hs N h1 h2

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

/-- the bytes `L` of a machine have the values of a reference of `V` (on the bytes that the reference lists): `RoomMusic.EntryRestM` is this with `L = RoomMusic.restIdxM` -/
def EntryAt (L : List Nat) (V : List (Machine × List Nat)) (m : Machine) : Prop :=
  ∃ v ∈ V, ∀ i ∈ v.2, i ∈ L → m.ram.get! i = v.1.ram.get! i

/-- the 10 bytes of `RoomMusic.EntryRestM` without the routine byte -/
def restIdxR (sy : Syms) (nmS : Names) (m0 : Machine) : List Nat :=
  (RoomMusic.restIdxM nmS).filter fun i => i != (ScreenPage.placesR sy nmS m0).rtI

/-- the 9 bytes of `restIdxR` without the level's number. `Run` asked them at the side pipe's entry in round 14; since round 15 it asks the 3 bytes of `restIdxB`
(`ChangesBase.entry₂`). The level's number comes from the vertical pipe's entry (`Run.area₁`, `Run.area₂`). -/
def restIdxA (sy : Syms) (nmS : Names) (m0 : Machine) : List Nat :=
  (restIdxR sy nmS m0).filter fun i => i != AreaKeep.areaI nmS

/-- the 8 bytes of `restIdxA` without the player's height. The height comes from the room's entering frame when it starts with a small player (`EntryHeight`,
`Run.y₂`); for another size `Run.height₂` asks it. -/
def restIdxY (sy : Syms) (nmS : Names) (m0 : Machine) : List Nat :=
  (restIdxA sy nmS m0).filter fun i => i != EntryHeight.heightI sy

/-- the 3 bytes of `restIdxY` without the five bytes of the first screen buffer: what `Run` asks at the side pipe's entry (`ChangesBase.entry₂`). The buffer's bytes
come from the room's entering frame when it starts with the control of the screen's buffers at 0 (`EntryBuffer`, `Run.buf₂`); else `Run.buffer₂` asks them. -/
def restIdxB (sy : Syms) (nmS : Names) (m0 : Machine) : List Nat :=
  (restIdxY sy nmS m0).filter fun i => !(EntryBuffer.bufIdx nmS).contains i

/-- The two changes of area on the real machines of a run, those of `B`, without the condition on the pause sound at the side pipe's exit (`Changes`, `ChangesK`).
`e₁`, `c₂`, `e₂`, `c₃` count frames without the `lag` frames, as `Segs` does. `L` is the list of bytes that `entry₂` asks at the side pipe's entry: by default the 11 bytes
of `RoomMusic.restIdxM`, as `HurryMusic` and `HurryStart` take them; `Run` takes the 10 bytes of `restIdxR`. -/
structure ChangesBase (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (B : Base) (kind : Nat → Kind) (e₁ c₂ e₂ c₃ : Nat)
    (L : List Nat := RoomMusic.restIdxM nmS) where
  /-- the first change: the machine after frame `e₁` is `B.seq a₁`, the first from the first control on that has no control (`Base.a₁`), and the machine after frame `c₂`
  is `B.seq b₁`, the first with control from there on (`Base.b₁`) -/
  ha₁ : seen kind (B.a₁ sy) = e₁ + 1
  hb₁ : seen kind (B.b₁ sy) = c₂ + 1
  /-- the part of the condition on the machine at the entry that the press of Start and the frames from control do not give: the bytes of `EntryKeep.restNames`
  (`Run.entry₁` gives the whole condition) -/
  entryRest₁ : EntryKeep.Rest d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))
  /-- **each instruction of the frames from control to the entry meets `CleanK` of the union guard** (`UpClean.guardU`): `Clean` with the bytes of the guard of
  `EntryKeep` (the bytes that the frames keep, the buttons left and right, the pipe's timer, the six bytes of the pause), of `LagPause.guardP` and of `FrameKeep.guardE`
  among the bytes that a store through an index or a pointer does not touch, but the move routine's store of the fraction (`UpClean.qOf`, with the index 0). It gives the
  four old conditions: `upClean₁` (`ChangesBase.upClean₁`), `pipe.lags.clean` (`Run.lagsClean`), `pipe.clean` (`Run.pipeClean`), `pipe.opening.cleanK`
  (`Run.pipeReal`). That each of these frames starts in the idle loop in control is `Run.upStart₁`. Before round 15 the condition was `UpClean.CleanU`, with an `if` on a
  check of the ROM inside it; the check is now one of `EntryKeep.Checks` (`q`). -/
  upCleanU : ∀ n, 1 ≤ n → n < B.a₁ sy → ∀ j,
    FrameKeep.CleanK (UpClean.guardU sy m0 d₁ (PipeTransition.entry m0)) (UpClean.qOf sy m0) (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- control within `dB` frames of the entry -/
  ctlBy₁ : controllable sy (B.seq (B.a₁ sy + B.dB)) = true
  /-- a `lag` frame is a paused frame: the low bit of the pause byte is set when it ends -/
  paused₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → kind n = .lag → PipeChangeEnd.Paused d₁ (B.seq (n + 1))
  /-- on a frame of the pipe's routine, each instruction meets the condition at the places -/
  places₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → PipeChangeBound.inPipe sy sy.EngVerticalPipe (B.seq n) = true → ∀ j, PipeChangeEnd.PlaceOK d₁.places (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- no Start on the frames of the game core after the pipe -/
  noStart₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → SideChangeEnd.coreFrame sy sy.EngVerticalPipe (B.seq n) = true → SideChangeEnd.noStart (B.inp n) = true
  /-- the second change: the machine after frame `e₂` is `B.seq a₂`, the first from `b₁` on that has left the player's routine (`Base.a₂`), and the machine after frame `c₃`
  is `B.seq b₂`, the first with control from there on (`Base.b₂`) -/
  ha₂ : seen kind (B.a₂ sy nmS m0) = e₂ + 1
  hb₂ : seen kind (B.b₂ sy nmS m0) = c₃ + 1
  /-- at the entry, the bytes `L` of the condition that the room does not give have the values of a reference machine. With the default `L` (`RoomMusic.restIdxM`, 11 bytes):
  the routine (so the routine that the room left for is the side pipe's), the player's vertical position, the screen's buffer, the area music's buffer, the event music's
  queue, the added note length, the level's number. `Run` asks `restIdxR`, the 10 of them without the routine: the room's entering frame gives the routine (`Run.rt₂`).
  The room's frames give five more music bytes from the area music's buffer (`RoomMusic.entryRest_of`), and the rest (`ScreenPage.entry_rest`). -/
  entry₂ : EntryAt L (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) (B.seq (B.a₂ sy nmS m0))
  /-- the room, from control to the side pipe: each instruction (the rows of the first change give `ScreenPage.Room` at control) -/
  roomSites : ∀ n, B.b₁ sy ≤ n → n < B.a₂ sy nmS m0 → ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nmS m0) (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- control within `d₂` frames of the entry -/
  ctlBy₂ : controllable sy (B.seq (B.a₂ sy nmS m0 + B.d₂)) = true
  /-- a `lag` frame ends paused -/
  paused₂ : ∀ n, B.a₂ sy nmS m0 ≤ n → n < B.b₂ sy nmS m0 → kind n = .lag → SideChangeEnd.Paused nx₂ (B.seq (n + 1))
  /-- no Start on the frames of the game core after the pipe -/
  noStart₂ : ∀ n, B.a₂ sy nmS m0 ≤ n → n < B.b₂ sy nmS m0 → SideChangeEnd.coreFrame sy sy.EngSidePipe (B.seq n) = true → SideChangeEnd.noStart (B.inp n) = true
  /-- at the side pipe's entry, the game timer is not 000. The pipe's frames do not store to its digits, so it is not 000 at the exit either
  (`SidePause.PipeQ.step`); before, this field asked it at the exit. -/
  time₂ : SideChangeEnd.TimerOK nx₂ (B.seq (B.a₂ sy nmS m0))

/-- **The two changes of area, as `Run` asks them.** At the room's first control bits 1 to 6 of the pause byte are 0: the rows of the first change know them
(`ChangesK.pauseBits₂`). With it the room's frames give the condition on the pause at the side pipe's entry (`ChangesK.pause₂`): the pause is silent, or the unpause
sound plays with the pause timer one more than its counter, or the unpause was pressed on that frame (`SidePause.PauseE`). The pipe's frames carry it to the exit for
any input (`SidePause.PipeQ`), where the pause sound is as `SideChangeSound.QuietK` says; the rows of `SideChangeSound` follow the sound's bytes in tables after it. -/
structure ChangesK (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (B : Base) (kind : Nat → Kind) (e₁ c₂ e₂ c₃ : Nat)
    (L : List Nat := RoomMusic.restIdxM nmS)
    extends ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L where
  /-- at the vertical pipe's exit, the queue of the pause sound is as at the reference, so the unpause was not pressed on the frame of the exit, and when the pause sound
  is silent the two squares' effects and the song's bytes are as at the reference and in a row (`PipeChangeEnd.QuietRest`); the screen buffer has a form of the table -/
  quiet₁ : ∀ n, B.a₁ sy ≤ n → n ≤ B.b₁ sy → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (B.seq n) →
    PipeChangeEnd.QuietRest d₁ (PipeChangeEnd.refX (PipeTransition.entry m0)) (B.seq n) ∧ PipeChangeEnd.SongAt d₁.xshape (B.seq n)
  /-- at the vertical pipe's entry, the game timer is not 000. The pipe's frames do not store to its digits, so it is not 000 at the exit either
  (`PipeChangeEnd.EndStatement.pauseStep`); before round 13, this field asked it at the exit. -/
  time₁ : SideChangeEnd.TimerOK d₁.nx (B.seq (B.a₁ sy))

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {B : Base} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {L : List Nat}

/-- the indices of `B` as fields of the changes: `chg.a₁` is `base.a₁`, and so on -/
abbrev ChangesBase.a₁ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : Nat := B.a₁ sy
abbrev ChangesBase.b₁ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : Nat := B.b₁ sy
abbrev ChangesBase.a₂ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : Nat := B.a₂ sy nmS m0
abbrev ChangesBase.b₂ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : Nat := B.b₂ sy nmS m0

/-- each frame from the first control to the entry begins with control: it holds by the choice of `a₁` -/
theorem ChangesBase.upStay (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : ∀ n, 1 ≤ n → n < B.a₁ sy → controllable sy (B.seq n) = true := fun n h1 h2 => by
  have h := firstWith_first _ 1 B.dA n h1 h2
  simpa using h

/-- the end of the first change is not before its entry: it holds by the choice of `b₁` -/
theorem ChangesBase.order₁ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : B.a₁ sy ≤ B.b₁ sy := firstWith_ge _ _ B.dB

/-- control at the end of the first change, by the choice of `b₁` -/
theorem ChangesBase.ctl₁ (C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : controllable sy (B.seq (B.b₁ sy)) = true :=
  firstWith_at (fun n => controllable sy (B.seq n)) _ B.dB C.ctlBy₁

/-- `b₁` is the first control after the entry, by the choice of `b₁` -/
theorem ChangesBase.ctlFirst₁ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → controllable sy (B.seq n) = false :=
  fun n h1 h2 => firstWith_first (fun n => controllable sy (B.seq n)) _ B.dB n h1 h2

theorem ChangesBase.roomOrder (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : B.b₁ sy ≤ B.a₂ sy nmS m0 := firstWith_ge _ (B.b₁ sy) B.dR

/-- each frame from the room's first control to the entry starts in the player's routine, by the choice of `a₂` -/
theorem ChangesBase.roomStay (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : ∀ n, B.b₁ sy ≤ n → n < B.a₂ sy nmS m0 →
    (B.seq n).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nmS m0).rtI := fun n h1 h2 => by
  have h := firstWith_first _ (B.b₁ sy) B.dR n h1 h2
  simpa using h

theorem ChangesBase.order₂ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : B.a₂ sy nmS m0 ≤ B.b₂ sy nmS m0 := firstWith_ge _ (B.a₂ sy nmS m0) B.d₂

/-- control at the end -/
theorem ChangesBase.ctl₂ (C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : controllable sy (B.seq (B.b₂ sy nmS m0)) = true :=
  firstWith_at (fun n => controllable sy (B.seq n)) (B.a₂ sy nmS m0) B.d₂ C.ctlBy₂

/-- `b₂` is the first control after the entry, by the choice of `b₂` -/
theorem ChangesBase.ctlFirst₂ (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : ∀ n, B.a₂ sy nmS m0 ≤ n → n < B.b₂ sy nmS m0 → controllable sy (B.seq n) = false :=
  fun n h1 h2 => firstWith_first (fun n => controllable sy (B.seq n)) (B.a₂ sy nmS m0) B.d₂ n h1 h2

/-- the entry is after control: `a₁` is not 0 -/
theorem ChangesBase.one_le (_C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) : 1 ≤ B.a₁ sy := firstWith_ge _ 1 B.dA

/-- **The old field `upClean₁`**: each instruction of the frames from control to the entry is `Clean` of the guard of `EntryKeep`, from `upCleanU`, when frame 1 begins
with the ROM's program (`h1`; `Run.upClean₁` has it from the press of Start on the title). `hq` is the check of the ROM (`EntryKeep.Checks.q`). -/
theorem ChangesBase.upClean₁ (C : ChangesBase sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) (hq : UpClean.qCheck sy m0 d₁ (PipeTransition.entry m0) = true)
    (h1 : (B.seq 1).prg = m0.prg ∧ (B.seq 1).prgMask = m0.prgMask) :
    ∀ n, 1 ≤ n → n < B.a₁ sy → ∀ j, PipeWrites.Clean (EntryKeep.guardOf sy m0 d₁ (PipeTransition.entry m0)) (PipeEntryRule.trace (B.seq n) (B.inp n) j) :=
  UpClean.upClean₁_of (S := B.toRealRun) hq h1 C.upCleanU

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
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {B : Base} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {L : List Nat}

/-- the first change as `PipeChangeEnd.PipeRunK`, with the condition at the entry (`Run.entry₁`) -/
def ChangesK.run₁ (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L)
    (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : PipeChangeEnd.PipeRunK sy nm₁ d₁ (PipeTransition.entry m0) where
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
  entry := he.entry
  atCtl := C.ctl₁
  lagPaused := C.paused₁
  places := C.places₁
  pause := he.pause
  quiet := C.quiet₁
  noStart := C.noStart₁
  time := C.time₁

/-- **The change into the room takes at least 91 frames**, from the condition at the entry and the conditions at the places, with the rows with tables. `hT` is what the check
on the ROM gives. -/
theorem ChangesK.bound₁ {es : List Machine} (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : e₁ + 91 ≤ c₂ := by
  have h := (C.run₁ he).bound hT
  have h1 : (C.run₁ he).cnt (C.run₁ he).a = e₁ + 1 := C.ha₁
  have h2 : (C.run₁ he).cnt (C.run₁ he).b = c₂ + 1 := C.hb₁
  have h3 : PipeChangeEnd.timerF + PipeChangeEnd.afterF = 91 := rfl
  rw [h1, h2, h3] at h
  omega

/-- **`left` is not 0 before control** in the change into the room: from the rows with tables and the first control (`PipeChangeEnd.PipeRunK.first`) -/
theorem ChangesK.first₁ {es : List Machine} (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → left₁ sy nm₁ m0 (B.seq n) ≠ 0 :=
  (C.run₁ he).first hT C.ctlFirst₁

end

/-- the checks on the ROM that the room needs: what one frame in the room does, two facts about the names, and the condition at the room's first control from the rows of the first change -/
structure RoomChecks (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) : Prop where
  facts : ScreenPage.RoomFacts sy nmS m0 160 (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0))
  timer : (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)).rkI = (ScreenPage.placesR sy nmS m0).timerI
  rt : ScreenPage.entryEnvOK sy nmS m0 (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) = true
  pipe : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) [PipeTransition.entry m0]
  start : ScreenStart.roomCheck sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true
  /-- the room's frames with the six bytes of the pause in a table, and the pause at the room's first control from the rows of the first change -/
  pause : RoomPause.Facts sy m0 nm₁ d₁ nx₂ nmS
  /-- the pause byte of the names of the side pipe is that of the vertical pipe's data -/
  pauseG : (SidePause.pauseBytesOf nx₂).g = PipeChangeEnd.pauseI d₁
  /-- the room's frames with the music bytes in a table, and the music at the room's first control from the rows of the first change -/
  music : ∃ T, RoomMusic.Facts sy m0 nm₁ d₁ (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) nmS T
  /-- the block map in the room and the start of its walk from the rows of the first change (`RoomMap`), and the two walks of the side pipe's entering frame
  (`SideEntryEnd`, `SideEntryRest`): with them the room's entering frame ends in the side pipe's routine (`EntryRoutine.rt_of_rows`, `Run.rt₂`) -/
  map : RoomMap.MapFacts sy nmS m0
  mapStart : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true
  mapStartF : RoomMap.startCheckF sy nmS m0 = true
  sideEnd : SideEntryEnd.sideEntryEndCheck sy m0 = true
  sideRest : SideEntryRest.restCheck sy nmS m0 = true
  /-- the walks of the vertical pipe's frames, of the last frames of the change and of the room's frames with the level's number known, and their small checks: with
  them the level's number at the side pipe's entry is that of the vertical pipe's entry (`AreaKeep`, `Run.area₂`) -/
  area : AreaKeep.Facts sy m0 nm₁ d₁ (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) nmS
  /-- the walk of the room's frame that follows the height, with the player's size of the reference known, and the references' height: with them a frame of the
  room that starts with that size and ends with the side pipe's routine ends with the height of the reference entry (`EntryHeight`, `Run.y₂`) -/
  height : EntryHeight.Facts sy nmS m0 (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0))
  /-- the walk of the room's frame with the control of the screen's buffers known at its start, and the references agree on the other bytes that the entry asks:
  with them a frame of the room that starts with the control of the reference and ends with the side pipe's routine ends with the five bytes of the first screen
  buffer of a reference (`EntryBuffer`, `Run.buf₂`) -/
  buffer : EntryBuffer.Facts sy nmS m0 (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) (restIdxB sy nmS m0)

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {B : Base} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {L : List Nat}

/-- **The condition at the first control in the room**, from the rows with tables of the first change and the first control -/
theorem ChangesK.roomAt (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L) (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    ScreenPage.Room sy nmS m0 (B.seq (B.b₁ sy)) :=
  ScreenStart.room_of_rows hR.start ((C.run₁ he).inRowsT hR.pipe C.ctlFirst₁) C.ctl₁

/-- **The routine at the side pipe's entry is the side pipe's**: `entry₂` with the default 11 bytes and the check `RoomChecks.rt`. In `Run`, `chg` asks 10 bytes and
`Run.rt₂` proves this from the room's entering frame -/
theorem ChangesK.rt₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) :
    (B.seq (B.a₂ sy nmS m0)).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.placesR sy nmS m0).eng := by
  have hV := hR.rt
  simp only [ScreenPage.entryEnvOK, ScreenPage.entryRtOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hV
  obtain ⟨⟨⟨hV1, hV2⟩, _⟩, _⟩ := hV
  obtain ⟨v, hv, hb⟩ := C.entry₂
  obtain ⟨_, hM⟩ := hR.music
  obtain ⟨a1, a2⟩ := hV1 v hv
  rw [hb _ a1 (RoomMusic.rt_mem hM hV2)]
  exact a2

/-- bits 0 to 6 clear give bits 1 to 6 clear -/
theorem low6_of_low7 {x : UInt8} (h : x &&& 0x7F = 0) : x &&& 0x7E = 0 := by
  have e : x &&& 0x7E = (x &&& 0x7F) &&& 0x7E := by
    rw [UInt8.and_assoc]
    rfl
  rw [e, h]
  rfl

/-- **At the room's first control bits 1 to 6 of the pause byte are 0** (it was the field `pauseBits₂`): the machine there is in the rows with tables of the first
change, whose states know bits 0 to 6 of the pause byte (`PipeChangeEnd.PipeRunK.pauseBits`). The states at the exit know them, because the walk of the pipe's
frames keeps the bits 1 to 6 that the entry knows (`PipeChangeEnd.baseK`). -/
theorem ChangesK.pauseBits₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃ L)
    (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    (B.seq (B.b₁ sy)).ram.get! (SidePause.pauseBytesOf nx₂).g &&& 0x7E = 0 := by
  have h : (B.seq (B.b₁ sy)).ram.get! (PipeChangeEnd.pauseI d₁) &&& 0x7F = 0 := (C.run₁ he).pauseBits hR.pipe C.ctlFirst₁
  rw [hR.pauseG]
  exact low6_of_low7 h

/-- **At the side pipe's entry the pause is silent, or the unpause sound plays with the pause timer one more than its counter, or the unpause was pressed**
(`SidePause.PauseE`; it was the field `pause₂`). From the room's first control (the room's condition, the rows of the time of the first change, `ChangesK.pauseBits₂`),
by the room's frames with the six bytes of the pause in a table (`RoomPause.pauseE_run`). -/
theorem ChangesK.pause₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃)
    (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    SidePause.PauseE sy (SideChangeSound.pauseIdx nx₂) (SidePause.pauseBytesOf nx₂) (B.seq (B.a₂ sy nmS m0)) :=
  RoomPause.pauseE_run hR.pause hR.facts.rt B.next C.roomOrder (C.roomAt hR he) ((C.run₁ he).inRowsT hR.pipe C.ctlFirst₁) C.ctl₁ (C.pauseBits₂ hR he)
    C.roomSites C.roomStay (fun h => hR.facts.ne (by rw [← h]; exact C.rt₂ hR))

/-- **The 16 bytes of `EntryRest` at the side pipe's entry** (it was the field `entry₂`): 11 of them from `entry₂`, the music's pointer, square 1's offset, the event
music's buffer and the noise effect's buffer from the room's frames with the music bytes in a table (`RoomMusic.music_run`, `RoomMusic.entryRest_of`). -/
theorem ChangesK.entryRest₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃)
    (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    ScreenPage.EntryRest nmS (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) (B.seq (B.a₂ sy nmS m0)) := by
  obtain ⟨_, hM⟩ := hR.music
  exact RoomMusic.entryRest_of hM (RoomMusic.music_run hM hR.facts.rt B.next C.roomOrder (C.roomAt hR he) ((C.run₁ he).inRowsT hR.pipe C.ctlFirst₁) C.ctl₁
    C.roomSites C.roomStay (fun h => hR.facts.ne (by rw [← h]; exact C.rt₂ hR))) C.entry₂

/-- the second change as `SidePause.EndRunQ`: the condition on the pause at the entry, and the timer not 000 at the entry -/
def ChangesK.run₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃)
    (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : SidePause.EndRunQ sy nm₂ nx₂ (SideTransition.entry m0) 160 where
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
  entry := ScreenPage.entry_rest hR.facts hR.timer hR.rt B.next C.roomOrder (C.roomAt hR he) C.roomSites C.roomStay (C.entryRest₂ hR he)
  pause := C.pause₂ hR he
  atCtl := C.ctl₂
  lagPaused := C.paused₂
  noStart := C.noStart₂
  timeE := C.time₂


/-- **The change out of the side pipe takes at least 282 frames**, from the single frames. `hS` and `hT` are what the checks on the ROM give, `rt` the place of the sound
routine. -/
theorem ChangesK.bound₂ {es : List Machine} {rt : StepWrites.Rt}
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) : e₂ + 282 ≤ c₃ := by
  have h := (C.run₂ hR he).bound hS hT hQ
  have h1 : (C.run₂ hR he).cnt (C.run₂ hR he).a = e₂ + 1 := C.ha₂
  have h2 : (C.run₂ hR he).cnt (C.run₂ hR he).b = c₃ + 1 := C.hb₂
  rw [h1, h2] at h
  omega

/-- **The room has at least one frame**: `b₁ < a₂`. The machine at the room's first control is in the player's routine (`Changes.roomAt`: the routine is a byte of the
condition), the machine at the entry is in the side pipe's (`entry₂` with the default 11 bytes and the check `RoomChecks.rt`), and the two routines differ
(`RoomChecks.facts`). `Run` uses `Run.b₁_lt_a₂` instead. -/
theorem ChangesK.b₁_lt_a₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    B.b₁ sy < B.a₂ sy nmS m0 := by
  have ho : B.b₁ sy ≤ B.a₂ sy nmS m0 := C.roomOrder
  refine Nat.lt_of_le_of_ne ho fun heq => ?_
  have h1 : (B.seq (B.b₁ sy)).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nmS m0).rtI :=
    ScreenPage.byte_of_ff ((C.roomAt hR he).bytes _ hR.facts.rt)
  have hV := hR.rt
  simp only [ScreenPage.entryEnvOK, ScreenPage.entryRtOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hV
  obtain ⟨⟨⟨hV1, hV2⟩, _⟩, _⟩ := hV
  obtain ⟨v, hv, hb⟩ := C.entry₂
  obtain ⟨_, hM⟩ := hR.music
  obtain ⟨a1, a2⟩ := hV1 v hv
  have h2 : (B.seq (B.a₂ sy nmS m0)).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.placesR sy nmS m0).eng := by
    rw [hb _ a1 (RoomMusic.rt_mem hM hV2)]
    exact a2
  rw [← heq, h1] at h2
  exact hR.facts.ne h2

/-- **The 11 bytes from the 10 and the routine**: the references of the entry know the routine byte with the side pipe's routine (`RoomChecks.rt`), so a machine with
the bytes of `restIdxR` of a reference and the side pipe's routine has the bytes of `RoomMusic.restIdxM` of it -/
theorem entryAt_of_rt (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) {m : Machine}
    (hrt : m.ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.placesR sy nmS m0).eng)
    (h : EntryAt (restIdxR sy nmS m0) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m) :
    EntryAt (RoomMusic.restIdxM nmS) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m := by
  have hV := hR.rt
  simp only [ScreenPage.entryEnvOK, ScreenPage.entryRtOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hV
  obtain ⟨⟨⟨hV1, _⟩, _⟩, _⟩ := hV
  obtain ⟨v, hv, hb⟩ := h
  refine ⟨v, hv, fun i hi hiL => ?_⟩
  by_cases e : i = (ScreenPage.placesR sy nmS m0).rtI
  · rw [e, hrt, (hV1 v hv).2]
  · exact hb i hi (List.mem_filter.2 ⟨hiL, bne_iff_ne.2 e⟩)

end

/-- A run through 1-1, and every assumption of the bound. `base` is the one sequence of real frames of the run, counted or not. The parts are `pipe` (part a), `room` (part c),
`pole` (parts e, f), `chg` (parts b, d); each takes its machines from `base`: `pipe`'s counted frames are the frames from frame 1 on that end not paused (`Run.pipeKeep₁`), `room`'s frames are the frames from `b₁` on that end not paused, its first control is frame `b₁`
(`Run.roomCtl`) and its entering frame is a frame in the room (`Run.roomEnter`), `pole`'s control is frame `b₂` (`Run.atCtl`). The fields below them join these, the frames of
the run with their timers (`clock`), the start from the title (`title`) and the level change (from the castle to 1-2). -/
structure Run (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) (rN : RoomJoin.Nums)
    (b : Machine) (vs : List Jump.VS) (PA : PoleJoin.Box) (Ts J Nc : Nat) (F : Int) (q t0 : Nat) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (fc : FlagRule.Ctx)
    (tc : TitleStart.Ctx) where
  /-- the real frames of the run, numbered as `clock` numbers them, and the bounds of the searches of the two changes -/
  base : Base
  /-- `pipe`'s frames are frames of `base`, its counted frame 1 frame 1; the pause byte is that of the names of the title -/
  pipe : Pipe sy m0 tc.gps N D base.toRealRun
  /-- `room`'s frames are the frames of `base` from the end of the first change (`Base.b₁`) on that end not paused, up to the entry into the side pipe (`Base.a₂`) -/
  room : RoomJoin.RoomRun sy m0 rN base.toRealRun (base.b₁ sy) (base.a₂ sy nmS m0 - base.b₁ sy)
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
  /-- the two changes of area, on the real machines of `base`. At the side pipe's entry it asks the 3 bytes of `restIdxB`; the routine comes from `room`'s entering
  frame (`Run.rt₂`), the level's number from the vertical pipe's entry (`Run.area₂`), where the press of Start on the title and the frames from control give it
  (`Run.area₁`, a theorem since round 15; it was a field), the height from the entering frame or from `height₂` (`Run.y₂`), the screen
  buffer's five bytes from the entering frame or from `buffer₂` (`Run.buf₂`), and `Run.chgK` is the changes with the 11 bytes -/
  chg : ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS base clock.kind pipe.E room.C room.E Cs (restIdxB sy nmS m0)
  /-- the search for the side pipe's entry (`Base.a₂`) looks at least one frame past the room's first control. With it the room has a frame (`Run.b₁_lt_a₂`) -/
  dR_pos : 1 ≤ base.dR
  /-- the frame that enters the side pipe starts with the player's size of the reference (small), or the height at the entry is the reference entry's. For a small
  player the height is proved (`EntryHeight.height_of_rows`, `Run.y₂`); before, `entry₂` asked the height of every run. A big player's height stays assumed: the walk
  does not know the floor's tiles, and without the floor a big player enters one row lower. -/
  height₂ : (base.seq (base.a₂ sy nmS m0 - 1)).ram.get! (EntryHeight.sizeI sy) = (ScreenPage.refR m0).ram.get! (EntryHeight.sizeI sy) ∨
    (base.seq (base.a₂ sy nmS m0)).ram.get! (EntryHeight.heightI sy) = (SideTransition.entry m0).ram.get! (EntryHeight.heightI sy)
  /-- the frame that enters the side pipe starts with the control of the screen's buffers of the reference (0: this frame's screen update empties the first buffer),
  or the five bytes of the first screen buffer at the entry are those of a reference of the entry. With the control at 0 the bytes are proved
  (`EntryBuffer.buffer_of_rows`, `Run.buf₂`); before, `entry₂` asked them of every run. The control is not 0 when the frame before erased a coin. -/
  buffer₂ : (base.seq (base.a₂ sy nmS m0 - 1)).ram.get! (EntryBuffer.ctlI nmS) = (ScreenPage.refR m0).ram.get! (EntryBuffer.ctlI nmS) ∨
    EntryAt (EntryBuffer.bufIdx nmS) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) (base.seq (base.a₂ sy nmS m0))
  /-- in the room, from its first control to the entry into the side pipe, a frame that ends paused is a `lag` frame. With the counts `chg.hb₁`, `chg.ha₂` it says that
  `room.E − room.C` frames of the room end not paused (`Run.roomMany`), so that `room`'s frames, the frames that end not paused, are frames of the room -/
  roomLag : ∀ n, base.b₁ sy ≤ n → n < base.a₂ sy nmS m0 → ¬ FrameKeep.Unpaused sy m0 (base.seq (n + 1)) → clock.kind n = .lag
  /-- from the press of Start on the title to frame 0. The press (`title.boot`): the run comes from power-on, with one state, the machine at power-on (its RAM not
  known: without the mark of a warm boot, or 0 in two bytes), no Start and no Select before the press, and the press in the window of frames `tc.first` to `tc.last`
  (`TitleBoot.Start.power`); or the machine after the press meets the condition itself (`TitleBoot.Start.press`). The condition is the theorem
  `TitleStart.Begin.press`. From the press any input (Start before frame 0 may pause the game); and frame 0 is the frame before the first control. -/
  title : TitleStart.Begin sy tc base.seq base.inp
  /-- the counters of `clock` before frame 0 are those of the machine when frame 0 begins, as `flag` says of the machine after the castle entry (`t_E`, `ph_E`) -/
  read₀ : (clock.s 0).t = CastleToLevel.timerOf tc.nm (base.seq 0) ∧ clock.ph 0 = CastleToLevel.phaseOf tc.nm (base.seq 0)
  /-- the level change -/
  L : Nat
  /-- the frames after the castle entry, up to the level change, on the real machines of `base`: one condition on the first frame `flag.G` after the castle entry
  where the area parser is done, the rule on the frames before it (`flag.pre`), and the level change after frame `L`. Any input: Start may pause the game. -/
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

/-- **The vertical pipe is entered after control**: `1 ≤ pipe.E`, since frame 0 ends in control (`title`) and an entering frame does not (`Pipe.one_le`). `hK` gives the check
that the two routines differ. The old field `pipe.one_le`. -/
theorem Run.pipeOne (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : 1 ≤ R.pipe.E :=
  R.pipe.one_le (EntryKeep.keepOK_of_check hK.keep).ne R.title.ctl

/-- **The machine of `room` at first control is the machine at the end of the first change**: `room`'s frames begin at frame `b₁` of `base` (`RoomJoin.RoomRun.fe_C`).
The old field `roomCtl`. -/
theorem Run.roomCtl (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.fe R.room.C = R.base.seq (R.base.b₁ sy) :=
  R.room.fe_C

/-- **The frames of `pole` begin at the machine at the end of the second change**: `pole`'s frames begin at frame `b₂` of `base` (`PoleJoin.Run.seq0`). The old field `atCtl`. -/
theorem Run.atCtl (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.pole.seq 0 = R.base.seq (R.base.b₂ sy nmS m0) :=
  R.pole.seq0

/-- **Frame 1 begins with the ROM's program**: it starts in the idle loop in control, from the press of Start on the title (`EntryKeep.Begin.start`). `hB` and `hK` are
the checks on the ROM. -/
theorem Run.prg₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    (R.base.seq 1).prg = m0.prg ∧ (R.base.seq 1).prgMask = m0.prgMask :=
  UpClean.prg_of_start (EntryKeep.Begin.start hB hK.near R.title (R.base.next 0)).1

/-- **The old field `upClean₁`**: each instruction of the frames from control to the entry is `Clean` of the guard of `EntryKeep`, from `upCleanU`
(`ChangesBase.upClean₁`, with `Run.prg₁`). `hB` and `hK` are the checks on the ROM. -/
theorem Run.upClean₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, 1 ≤ n → n < R.base.a₁ sy → ∀ j, PipeWrites.Clean (EntryKeep.guardOf sy m0 d₁ (PipeTransition.entry m0)) (PipeEntryRule.trace (R.base.seq n) (R.base.inp n) j) :=
  R.chg.upClean₁ hK.q (R.prg₁ hB hK)

/-- **Each frame from control to the vertical pipe's entry starts in the idle loop in control**: by induction from the press of Start on the title (`title`), under `upClean₁`
(`Run.upClean₁`). Each of these frames begins with control, by the choice of `a₁`. `hB` and `hK` are the checks on the ROM. The old field `upStart₁`. -/
theorem Run.upStart₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, 1 ≤ n → n < R.base.a₁ sy → PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (R.base.seq n) :=
  EntryKeep.starts_of_title hB hK R.title R.base.next R.chg.upStay (R.upClean₁ hB hK)

/-- **The condition at the vertical pipe's entry, with the pause**, from the press of Start on the title (`title`), the frames from control to the entry (`Run.upStart₁`,
`upClean₁`) and the part that stays assumed (`entryRest₁`): `Entry`, and the six bytes of the pause in a class that is not paused (`PauseV`, it was the field `pause₁`).
`hB` and `hK` are the checks on the ROM. The old fields `entry₁` and `pause₁`. -/
theorem Run.entry₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    PipeChangeEnd.EntryV sy d₁ (PipeTransition.entry m0) (R.base.seq (R.base.a₁ sy)) :=
  EntryKeep.entryV_of_title hB hK R.title R.base.next R.chg.one_le (R.upStart₁ hB hK) (R.upClean₁ hB hK) R.chg.entryRest₁

/-- **The counted frame `pipe.E`, the entering frame, begins before the entry `a₁` of the first change.** If not, frame `a₁ − 1` is frame 0 or a frame of `pipe` before
its entering frame. Frame 0 ends in control (`title`), a counted frame before the entering frame ends in control (`lags.ctl`), and a frame not counted keeps the routine
(`Lags.known_end`: it starts in control, `Run.upStart₁`, and its instructions are `Clean` with the pause byte protected, by `upCleanU`, since it is before `a₁`). So
frame `a₁` begins with the routine of control. But it begins with the pipe's routine: the routine byte is one of `entryRest₁`, and its value at the reference entry is the
pipe's routine (the list check of `EntryKeep`). With the definition of `a₁` (the first frame without control) this gives `pipe.lags.ix pipe.E + 1 = a₁`; only the bound is
needed. `hB`, `hK`, `hc`, `hp` are checks on the ROM, `hg` says that the pause byte of `pipe` is the byte that the NMI tests (`OpenFrames.Checks.pause`). -/
theorem Run.entryIx (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hc : LagFrames.lagCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.pipe.lags.ix R.pipe.E < R.base.a₁ sy := by
  rcases Nat.lt_or_ge (R.pipe.lags.ix R.pipe.E) (R.base.a₁ sy) with h | h
  · exact h
  · exfalso
    have hl := hK.lists
    have hr : (R.base.seq (R.base.a₁ sy)).ram.get! (EntryKeep.guardOf sy m0 d₁ (PipeTransition.entry m0)).rtI = PipeEntryRule.vp sy := by
      simp only [EntryKeep.listCheck, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hl
      obtain ⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, _⟩ := hl
      exact (R.chg.entryRest₁.1 _ h2 h3).trans h4
    have hC := EntryKeep.keepOK_of_check hK.keep
    have ha := R.chg.one_le
    obtain ⟨p, hp1⟩ : ∃ p, R.base.a₁ sy = p + 1 := ⟨R.base.a₁ sy - 1, by omega⟩
    have hk : ∀ x ∈ (PipeWrites.guardOf sy m0).known, (R.base.seq (p + 1)).ram.get! x.1 = x.2 := by
      by_cases hp0 : p = 0
      · subst hp0
        exact StartRun.known_ctl R.title.ctl
      · have hpre := R.prg₁ hB hK
        exact R.pipe.lags.known_end hc hp (n := p) (by omega) (by omega) (R.upStart₁ hB hK p (by omega) (by omega))
          (fun k => UpClean.cleanP_of_U hK.q hg (R.chg.upCleanU p (by omega) (by omega) k) (UpClean.prg_on hpre (by omega) k).1 (UpClean.prg_on hpre (by omega) k).2)
    have h1 : (R.base.seq (p + 1)).ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat = sy.Eng_PlayerCtrl.toUInt8 :=
      hk ((sy.GameEngineSubroutine &&& 0x7FF).toNat, sy.Eng_PlayerCtrl.toUInt8) (by simp [PipeWrites.guardOf])
    rw [← hp1] at h1
    exact hC.ne (h1.symm.trans hr)

/-- **The old field `pipe.lags.clean`**: each instruction of each frame from frame 1 to the entering frame, counted or not, is `Clean` with the pause byte protected, from
`upCleanU`: these frames are before `a₁` (`Run.entryIx`). `hB`, `hK`, `hc`, `hp` are checks on the ROM, `hg` the pause byte (`OpenFrames.Checks.pause`). -/
theorem Run.lagsClean (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hc : LagFrames.lagCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.pipe.lags.CleanP := fun n h1 h2 k =>
  have hpre := R.prg₁ hB hK
  UpClean.cleanP_of_U hK.q hg (R.chg.upCleanU n h1 (Nat.lt_trans h2 (R.entryIx hB hK hc hp hg)) k) (UpClean.prg_on hpre h1 k).1 (UpClean.prg_on hpre h1 k).2

/-- **The old field `pipe.clean`**: each instruction of the entering frame is `Clean`, from `upCleanU`: the entering frame is before `a₁` (`Run.entryIx`). `hB`, `hK`, `hc`,
`hp` are checks on the ROM, `hg` the pause byte. -/
theorem Run.pipeClean (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hc : LagFrames.lagCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ j, PipeWrites.Clean (PipeWrites.guardOf sy m0) (PipeEntryRule.trace (R.pipe.fm R.pipe.E) (R.pipe.inp R.pipe.E) j) := fun j =>
  have hpre := R.prg₁ hB hK
  have h1 : 1 ≤ R.pipe.lags.ix R.pipe.E := R.pipe.lags.one_le_ix (R.pipeOne hK)
  UpClean.cleanW_of_U hK.q (R.chg.upCleanU _ h1 (R.entryIx hB hK hc hp hg) j) (UpClean.prg_on hpre h1 j).1 (UpClean.prg_on hpre h1 j).2

/-- **The first `N` counted frames with the conditions on their instructions** (`OpenFrames.Real`): `pipe.opening`, `CleanK` of `FrameKeep.guardE` on each instruction (the
old field `opening.cleanK`) and `Clean` with the pause byte (`Run.lagsClean`), both from `upCleanU`. `hB`, `hK`, `hc`, `hp` are checks on the ROM, `hg` the pause byte. -/
theorem Run.pipeReal (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hc : LagFrames.lagCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    OpenFrames.Real sy m0 (Opening.jumpLens sy m0) N R.pipe.E R.pipe.lags :=
  { R.pipe.opening with
    cleanK := fun t h1 _ h3 k =>
      have hix : R.pipe.lags.ix t < R.pipe.lags.ix R.pipe.E :=
        Nat.lt_of_lt_of_le (PipeFrames.ixP_lt tc.gps R.base.toRealRun R.pipe.lags.dP t) (R.pipe.lags.ix_mono h3)
      UpClean.cleanE_of_U (R.chg.upCleanU _ (R.pipe.lags.one_le_ix h1) (Nat.lt_trans hix (R.entryIx hB hK hc hp hg)) k)
    lagsClean := R.lagsClean hB hK hc hp hg }

/-- the change into the room takes at least 91 frames -/
theorem Run.change₁ {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.pipe.E + 91 ≤ R.room.C :=
  R.chg.bound₁ hT₁ (R.entry₁ hB hK)

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

/-- **Frame 1 starts a frame in the idle loop, in control**: from the press of Start on the title. `hB` and `hT` are checks on the ROM. -/
theorem Run.pipeStart₁ (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true)
    (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) :
    PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (R.base.seq 1) :=
  StartRun.Begin.start₁G hB hT R.title (R.base.next 0)

/-- **The machine at control of `pipe` has the bytes of the walk of frame 1**: `pipe`'s counted frame 1 is the first frame from frame 1 on that ends not paused, and the frames
before it keep these bytes (`Pipe.keep₁`, with `Run.lagsClean`). `hc`, `hk`, `hp`, `hB`, `hT` and `hK` are checks on the ROM, `hg` the pause byte. (Before, the counted frame 1 was frame 1 by the definition: the old `Run.pipeAt`.) -/
theorem Run.pipeKeep₁ (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hB : TitleStart.check sy tc t0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps)
    (hE : 1 ≤ R.pipe.E) : ∀ x ∈ LagFrames.lagI sy, (R.pipe.fm 1).ram.get! x = (R.base.seq 1).ram.get! x :=
  R.pipe.keep₁ hc hk hp (R.lagsClean hB hK hc hp hg) hE (R.pipeStart₁ hB hT)

/-- **He stands still at control**, when the counted frame 1 begins: from the press of Start on the title, and the frames before it (`Run.pipeKeep₁`). The old field
`pipe.still`. -/
theorem Run.still (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hB : TitleStart.check sy tc t0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps)
    (hE : 1 ≤ R.pipe.E) : SurfaceFrames.vOf sy (R.pipe.fm 1) = 0 := by
  have e := OpenFrames.peek_keep (R.pipeKeep₁ hc hk hp hB hT hK hg hE) (x := sy.Player_X_Speed) (Or.inl (by simp [FrameModel.hBytes]))
  show sbyte (peek (R.pipe.fm 1) sy.Player_X_Speed) = 0
  rw [e]
  exact R.title.still hB (R.base.next 0)

/-- **The position at control is that of `m0`**: from the press of Start on the title frame 0 ends with the position of `m0` (`StartRun.Begin.pos₁`), and the frames up to
the counted frame 1 keep it (`Run.pipeKeep₁`). `hc`, `hk`, `hp`, `hB`, `hP`, `hT` are checks on the ROM. -/
theorem Run.pipePos (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true)
    (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (hE : 1 ≤ R.pipe.E) : posP sy (R.pipe.fm 1) = posP sy m0 := by
  rw [(OpenFrames.keep_parts (v := 0) (R.pipeKeep₁ hc hk hp hB hT hK hg hE)).2.1]
  exact StartRun.Begin.pos₁ hB hP R.title (R.base.next 0)

/-- **Frame 1 begins at the position of `m0`**: the frames are read from the machines (`Pipe.reads`), and `Run.pipePos`. With the top speed this bounds the position up to
frame `N` (`PipeFrames.no_entry_of_start`): the old field `openP`. `hc`, `hk`, `hp`, `hB`, `hP`, `hT`, `hK` are checks on the ROM. -/
theorem Run.pipeP1 (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 tc.gps = true)
    (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true)
    (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    (R.pipe.fr 1).P = posP sy m0 :=
  ((R.pipe.reads hc hk hp (R.lagsClean hB hK hc hp hg) (R.pipeStart₁ hB hT)).P 1 (Nat.le_refl 1) (R.pipeOne hK)).trans (R.pipePos hc hk hp hB hP hT hK hg (R.pipeOne hK))

/-- **The horizontal state at control is that of `m0`**: from the press of Start on the title (`StartRun.Begin.hs₁`) and the frames up to the counted frame 1
(`Run.pipeKeep₁`). `hc`, `hk`, `hp`, `hB`, `hP`, `hT` are checks on the ROM. -/
theorem Run.pipeHS (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true)
    (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (hE : 1 ≤ R.pipe.E) : Potential.startHS sy (R.pipe.fm 1) = Potential.startHS sy m0 := by
  rw [(OpenFrames.keep_parts (v := 0) (R.pipeKeep₁ hc hk hp hB hT hK hg hE)).1]
  exact StartRun.Begin.hs₁ hB hP R.title (R.base.next 0)

/-- **The state at control holds what the first frames need** (`OpenFrames.Held`) and he is on the ground, at the ground's height: the bytes of the title's check
(`StartRun.Begin.bytesAll₁`) are those of `m0`, `m0` holds them (`hm`), and the frames up to the counted frame 1 keep them (`Run.pipeKeep₁`). `hc`, `hk`, `hp`, `hB`, `hP`,
`hT` are checks on the ROM. -/
theorem Run.pipeHeld (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true)
    (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (hE : 1 ≤ R.pipe.E) {v : UInt8}
    (hm : OpenFrames.Held sy v m0 ∧ peek m0 sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 m0) :
    OpenFrames.Held sy v (R.pipe.fm 1) ∧ peek (R.pipe.fm 1) sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 (R.pipe.fm 1) := by
  have h₀ := OpenFrames.held_of_bytes (StartRun.Begin.bytesAll₁ hB hP R.title (R.base.next 0)) hm
  have hk₁ := R.pipeKeep₁ hc hk hp hB hT hK hg hE
  refine ⟨(OpenFrames.keep_parts hk₁).2.2 h₀.1, ?_, OpenFrames.ground_keep hk₁ h₀.2.2⟩
  rw [OpenFrames.peek_keep hk₁ (x := sy.Player_State) (by simp)]
  exact h₀.2.1

/-- **At the counted frame 1 bit 7 of A and B of the frame before is that of A and B** (`PrevKeep.PrevOK`): the two bytes are among those of the title's check
(`StartRun.Begin.bytesAll₁`), the frames up to the counted frame 1 keep them (`Run.pipeKeep₁`), and `m0` has the relation (`h0`). `hc`, `hk`, `hp`, `hB`, `hP`, `hT` are checks
on the ROM. -/
theorem Run.pipePrev (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true)
    (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps) (hE : 1 ≤ R.pipe.E) (h0 : PrevKeep.PrevOK sy m0) :
    PrevKeep.PrevOK sy (R.pipe.fm 1) := by
  have hb := StartRun.Begin.bytesAll₁ hB hP R.title (R.base.next 0)
  have hk₁ := R.pipeKeep₁ hc hk hp hB hT hK hg hE
  unfold PrevKeep.PrevOK at h0 ⊢
  rw [show peek (R.pipe.fm 1) sy.PreviousA_B_Buttons = peek m0 sy.PreviousA_B_Buttons from
      (hk₁ _ OpenFrames.ab_lagI.2).trans (hb _ (by simp [StartRun.posI, StartRun.hsI, StartRun.stI, LagFrames.I])),
    show peek (R.pipe.fm 1) sy.A_B_Buttons = peek m0 sy.A_B_Buttons from
      (hk₁ _ OpenFrames.ab_lagI.1).trans (hb _ (by simp [StartRun.posI, StartRun.hsI, StartRun.stI, LagFrames.I]))]
  exact h0

/-- **The speed of each counted frame up to the entry is at most the top speed**: the frames are read from the machines (`Pipe.reads`), the speed is 0 at control
(`Run.still`), and a frame changes the speed by at most the top speed's bound (`PipeFrames.speed_of_reads`). `hc`, `hk`, `hp`, `hB`, `hT`, `h16` are checks on the ROM. -/
theorem Run.pipeSpeed (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 tc.gps = true) (hB : TitleStart.check sy tc t0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hg : CtrlKeep.pauseI sy m0 = tc.gps)
    (h16 : 16 ≤ TopSpeed.top sy) (hE : 1 ≤ R.pipe.E) :
    ∀ t, 1 ≤ t → t ≤ R.pipe.E → (sbyte (peek (R.pipe.fm t) sy.Player_X_Speed)).natAbs ≤ TopSpeed.top sy := by
  intro t h1 h2
  have hR := R.pipe.reads hc hk hp (R.lagsClean hB hK hc hp hg) (R.pipeStart₁ hB hT)
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have h := PipeFrames.speed_of_reads (top := (TopSpeed.top sy : Int)) (by omega) hR (R.still hc hk hp hB hT hK hg hE) n h2
  rw [hR.v (n + 1) (by omega) h2] at h
  show (SurfaceFrames.vOf sy (R.pipe.fm (n + 1))).natAbs ≤ TopSpeed.top sy
  omega

/-- **Each of the first `N` counted frames is a step of the opening's model, or frame `N` ends at the left end of the level** (the old field `opening`): from the
conditions on single frames (`pipe.opening`, with the conditions on each instruction from `chg.upCleanU`: `Run.pipeReal`, `OpenFrames.Real.toRunM`). The position at
the end of a frame is modulo `2²⁴` here. `hc`, `hk`, `hp`, `hB`, `hP`, `hT`, `C`, `hM`, `hTM` are checks on the ROM. -/
def Run.pipeOpening {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 tc.gps = true)
    (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true)
    (C : OpenFrames.Checks sy m0 (Opening.jumpLens sy m0) Zb v tc.gps) (hM : OpenMap.mapCheck sy m0 = true) (hTM : OpenMap.titleMapCheck sy tc m0 = true)
    (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hE : 1 ≤ R.pipe.E) :
    OpenFrames.OpenRunM sy m0 (Opening.jumpLens sy m0) N R.pipe.E R.pipe.fm :=
  (R.pipeReal hB hK hc hp C.pause).toRunM hc hk hp C hM (R.pipeStart₁ hB hT) (OpenMap.Begin.map₁ hB hTM R.title (R.base.next 0)).1 (R.pipeHeld hc hk hp hB hP hT hK C.pause hE C.start).1
    (R.pipeHeld hc hk hp hB hP hT hK C.pause hE C.start).2.1 (R.pipeHeld hc hk hp hB hP hT hK C.pause hE C.start).2.2 (R.pipeSpeed hc hk hp hB hT hK C.pause C.top16 hE)
    ((R.pipeReal hB hK hc hp C.pause).stSpring hc hp hM (R.pipeStart₁ hB hT) (OpenMap.Begin.map₁ hB hTM R.title (R.base.next 0)).1)
    (R.pipePrev hc hk hp hB hP hT hK C.pause hE C.prev0)

/-- **The bound of the opening at the end of frame `N`** (the old field `openB`): each of the first `N − 1` frames is a step of the model, and frame `N` is a step or
ends at the left end of the level (`Run.pipeOpening`). The model does not get past `D` in `N` steps (`hopt`, the check of `Opening`), and the position at the end of
a step is exact by the bounds of the model: `hopt` and `hL` (`OpenLeft`: no input gets left of the position at control in fewer than `N` frames, and `P(m₀) + D < 2²⁴`),
and on frame `N` by the page of the next counted frame (`opening.page`). At the left end of the level he is below 1 px, and the machine at control is at least 1 px
from it (`C.left`). The start is that of `m0` (`Run.pipeHS`, `Run.pipePos`). `hc`, `hk`, `hp`, `hB`, `hP`, `hT`, `C`, `hopt`, `hL` are checks on the ROM. -/
theorem Run.pipeOpenB {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 tc.gps = true)
    (hB : TitleStart.check sy tc t0 = true) (hP : StartRun.titlePosCheck sy tc m0 = true) (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true)
    (C : OpenFrames.Checks sy m0 (Opening.jumpLens sy m0) Zb v tc.gps) (hM : OpenMap.mapCheck sy m0 = true) (hTM : OpenMap.titleMapCheck sy tc m0 = true)
    (hopt : ∀ k u, k ≤ N → Cert.Reach (Opening.succ sy m0 (Opening.jumpLens sy m0)) (Opening.start sy m0) k u → u.2 ≤ D)
    (hL : (∀ k u, k < N → Cert.Reach (Opening.succ sy m0 (Opening.jumpLens sy m0)) (Opening.start sy m0) k u → -posP sy m0 ≤ u.2) ∧ posP sy m0 + D < 0x1000000)
    (hK : EntryKeep.Checks sy m0 d₁ tc) (h1 : 1 ≤ N) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    N < R.pipe.E → (R.pipe.fr N).P' ≤ posP sy m0 + D := fun hN => by
  have h0 : (0 : Int) ≤ D := hopt 0 (Opening.start sy m0) (Nat.zero_le N) (.refl _)
  have hD : 256 ≤ posP sy m0 + D := by
    have := C.left
    omega
  exact (R.pipeOpening hc hk hp hB hP hT C hM hTM hK (by omega)).openB (R.pipeHS hc hk hp hB hP hT hK C.pause (by omega))
    (R.pipePos hc hk hp hB hP hT hK C.pause (by omega)) hopt hL.1 hL.2 R.pipe.opening.page hD
    (R.pipe.reads hc hk hp (R.lagsClean hB hK hc hp C.pause) (R.pipeStart₁ hB hT)) h1 hN

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

/-- **`room.E − room.C` frames of the room end not paused**: of the frames from `b₁` to `a₂`, `clock` counts `room.E − room.C` that are not `lag` frames (`chg.hb₁`,
`chg.ha₂`), and each of them ends not paused (`roomLag`). So `room`'s frames up to the entry are frames of the room (`Run.roomIdx`). -/
theorem Run.roomMany (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.E - R.room.C ≤ R.room.ups := by
  have h1 : seen R.clock.kind (R.base.b₁ sy) = R.room.C + 1 := R.chg.hb₁
  have h2 : seen R.clock.kind (R.base.a₂ sy nmS m0) = R.room.E + 1 := R.chg.ha₂
  have ho := R.chg.roomOrder
  have key : ∀ d, R.base.b₁ sy + d ≤ R.base.a₂ sy nmS m0 → seen R.clock.kind (R.base.b₁ sy + d) ≤
      seen R.clock.kind (R.base.b₁ sy) + FrameKeep.upTo (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₁ sy)) d := by
    intro d
    induction d with
    | zero => intro _; simp [FrameKeep.upTo]
    | succ d ih =>
      intro hd
      have h3 := ih (by omega)
      show seen R.clock.kind (R.base.b₁ sy + d + 1) ≤ _
      rw [FrameKeep.upTo_succ]
      simp only [seen]
      by_cases hl : R.clock.kind (R.base.b₁ sy + d) = .lag
      · rw [if_pos hl]
        split <;> omega
      · have hu : FrameKeep.Unpaused sy m0 (R.base.seq (R.base.b₁ sy + d + 1)) := by
          by_cases h : FrameKeep.Unpaused sy m0 (R.base.seq (R.base.b₁ sy + d + 1))
          · exact h
          · exact absurd (R.roomLag (R.base.b₁ sy + d) (by omega) (by omega) h) hl
        have hf : FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₁ sy) (d + 1) = true := by
          simp only [FrameKeep.upAt, beq_iff_eq]
          exact hu
        rw [if_neg hl, hf]
        simp only [if_true]
        omega
  have h := key (R.base.a₂ sy nmS m0 - R.base.b₁ sy) (by omega)
  rw [show R.base.b₁ sy + (R.base.a₂ sy nmS m0 - R.base.b₁ sy) = R.base.a₂ sy nmS m0 by omega] at h
  show R.room.E - R.room.C ≤ FrameKeep.upTo (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₁ sy)) (R.base.a₂ sy nmS m0 - R.base.b₁ sy)
  omega

/-- **The room's frame `n + 1` before the entry is a frame of `base` in the room**: it begins at frame `b₁ + ix (n + 1 − C) − 1` (`RoomJoin.RoomRun.fm`, a definition), between
`b₁` and `a₂`. From `Run.roomMany`: the counted frame `n + 1 − C` is found by `a₂` -/
theorem Run.roomIdx (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) {n : Nat} (hC : R.room.C ≤ n) (hE : n < R.room.E) :
    R.base.b₁ sy ≤ R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) ∧ R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) < R.base.a₂ sy nmS m0 := by
  have hm := R.roomMany
  obtain ⟨a1, a2, _⟩ := R.room.ix_at (k := n + 1 - R.room.C) (by omega) (by omega)
  have ho := R.chg.roomOrder
  exact ⟨Nat.le_add_right _ _, by omega⟩

/-- **The state at first control in the room**, on the real machines: it comes from the last row of the change into the room, under the change's conditions and `Changes.first₁`. `hc` is the check on
the ROM. -/
theorem Run.roomStart {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hc : RoomStart.startCheck sy nm₁ d₁ (PipeTransition.entry m0) (RoomJoin.room sy rN) rN.startY rN.startW rN.fallF = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    RoomJoin.StartAt sy rN (R.room.fe R.room.C) := by
  rw [R.roomCtl]
  exact RoomStart.PipeRunK.start hT₁ hc (R.chg.run₁ (R.entry₁ hB hK)) R.chg.ctlFirst₁

/-- **The room has a frame**: `b₁ < a₂`. The machine at the room's first control is in the player's routine (`ChangesK.roomAt`: the routine is a byte of the room's
condition), so the search of `a₂` does not stop there, and it looks at least one frame further (`dR_pos`). Before, this came from the routine byte of `entry₂`
(`ChangesK.b₁_lt_a₂`). `hR`, `hB`, `hK` are checks on the ROM. -/
theorem Run.b₁_lt_a₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.base.b₁ sy < R.base.a₂ sy nmS m0 := by
  have h1 : (R.base.seq (R.base.b₁ sy)).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nmS m0).rtI :=
    ScreenPage.byte_of_ff ((R.chg.roomAt hR (R.entry₁ hB hK)).bytes _ hR.facts.rt)
  obtain ⟨d, hd⟩ : ∃ d, R.base.dR = d + 1 := ⟨R.base.dR - 1, by have := R.dR_pos; omega⟩
  show R.base.b₁ sy < roomEnd sy nmS m0 R.base.seq (R.base.b₁ sy) R.base.dR
  rw [hd]
  simp only [roomEnd, firstWith, h1, bne_self_eq_false, Bool.false_eq_true, if_false]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (firstWith_ge _ _ _)

/-- **The frame of `room` that enters the side pipe is a frame of `base` in the room**, from its first control to the entry: frame `b₁ + ix (E − C) − 1`, the frame that ends
as the `(E − C)`-th frame from `b₁` on that ends not paused. It is before `a₂` by `Run.roomIdx`; when `E = C` it is frame `b₁`, and the room has a frame (`Run.b₁_lt_a₂`).
`hR`, `hB`, `hK` are checks on the ROM. The old field `roomEnter`. -/
theorem Run.roomEnter (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∃ k, R.base.b₁ sy ≤ k ∧ k < R.base.a₂ sy nmS m0 ∧ R.room.fm (R.room.E - 1) = R.base.seq k ∧ R.room.pad R.room.E = R.base.inp k := by
  have h4 := R.b₁_lt_a₂ hR hB hK
  have hC1 : 1 ≤ R.room.C := by
    have := R.hz₁
    omega
  rcases Nat.lt_or_ge R.room.C R.room.E with h | h
  · obtain ⟨hk0, hk⟩ := R.roomIdx (n := R.room.E - 1) (by omega) (by omega)
    exact ⟨_, hk0, hk, rfl, rfl⟩
  · have hle := R.room_le
    have z : R.room.ix 0 = 0 := FrameKeep.nthUp_zero
    have e : R.room.E - 1 + 1 - R.room.C = 0 := by omega
    refine ⟨R.base.b₁ sy, Nat.le_refl _, h4, ?_, ?_⟩
    · show R.base.seq (R.base.b₁ sy + (R.room.ix (R.room.E - 1 + 1 - R.room.C) - 1)) = _
      rw [e, z]
      rfl
    · show R.base.inp (R.base.b₁ sy + (R.room.ix (R.room.E - 1 + 1 - R.room.C) - 1)) = _
      rw [e, z]
      rfl

/-- **The routine at the side pipe's entry is the side pipe's** (it was the routine byte of `entry₂`, now the theorem): the room's entering frame (`room.enters`) is a
frame `k` of `base` from `b₁` on and before `a₂` (`Run.roomEnter`), and it ends in the side pipe's routine (`EntryRoutine.rt_of_rows`: the walks of `SideEntryEnd` and
`SideEntryRest`). Every frame from `b₁` before `a₂` begins in the player's routine (`ChangesBase.roomStay`), so `k + 1` is not before `a₂`: `a₂ = k + 1`. `hR`, `hB`, `hK`
are checks on the ROM. -/
theorem Run.rt₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    (R.base.seq (R.base.a₂ sy nmS m0)).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.placesR sy nmS m0).eng := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter hR hB hK
  have he := R.entry₁ hB hK
  have hen : SideEntryRule.Enters sy (R.base.seq k) (R.base.inp k) := by
    rw [← e1, ← e2]
    exact R.room.enters
  have hk := EntryRoutine.rt_of_rows hR.map hR.mapStart hR.mapStartF hR.sideEnd hR.sideRest R.base.next ((R.chg.run₁ he).inRowsT hR.pipe R.chg.ctlFirst₁)
    R.chg.ctl₁ R.chg.roomSites R.chg.roomStay h1 h2 hen
  rw [← R.base.next k] at hk
  have ha : R.base.a₂ sy nmS m0 = k + 1 := by
    rcases Nat.lt_or_ge (k + 1) (R.base.a₂ sy nmS m0) with h | h
    · exact absurd ((R.chg.roomStay (k + 1) (by omega) h).symm.trans hk) hR.facts.ne
    · omega
  rw [ha]
  exact hk

/-- **The level's number at the vertical pipe's entry is the reference entry's** (the old field `area₁`, 1-1-d-2-5-3): it is one of the bytes of the condition at the
entry (`PipeChangeEnd.Entry`, `Run.entry₁`). The condition at the press of Start on the title knows it (`TitleStart.areaNames`), frame 0 ends with it
(`EntryKeep.nearCheck`), and each frame from control to the entry keeps it: the walk of one frame does not store to it, and the guard of `upCleanU` protects it from the
stores through an index or a pointer (`EntryKeep.keepCheck`). `hR` gives that the room's names and the entry's list agree on the byte (`ScreenStart.area_of_entry`);
`hB` and `hK` are the checks on the ROM. -/
theorem Run.area₁ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    (R.base.seq (R.base.a₁ sy)).ram.get! (AreaKeep.areaI nmS) = (PipeTransition.entry m0).ram.get! (AreaKeep.areaI nmS) :=
  ScreenStart.area_of_entry hR.start (R.entry₁ hB hK).entry

/-- **The level's number at the side pipe's entry is the vertical pipe's entry's** (it was a byte of `entry₂`, now the theorem): at the vertical pipe's entry it has the
reference's value (`Run.area₁`); the walks of the pipe's frames and of the rows with the byte known go beside the walks of part b up to the room's first control
(`AreaKeep.PipeRunK.areaB`), and the room's walk with the byte in a table carries it to the side pipe's entry (`AreaKeep.area_run`). `hR`, `hB`, `hK` are checks on the ROM. -/
theorem Run.area₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    (R.base.seq (R.base.a₂ sy nmS m0)).ram.get! (AreaKeep.areaI nmS) = (PipeTransition.entry m0).ram.get! (AreaKeep.areaI nmS) := by
  have he := R.entry₁ hB hK
  have hX := (AreaKeep.small_parts hR.area.small).2.2.2.1
  have hb := AreaKeep.PipeRunK.areaB hR.pipe (R.chg.run₁ he) R.chg.ctlFirst₁ hR.area.pipe hR.area.rows hX (R.area₁ hR hB hK)
  exact AreaKeep.area_run hR.area.room hR.facts.rt R.base.next R.chg.roomOrder (R.chg.roomAt hR he) hb R.chg.roomSites R.chg.roomStay
    (fun h => hR.facts.ne (by rw [← h]; exact R.rt₂ hR hB hK))

/-- **The 10 bytes from the 9 and the level's number**: each reference of the entry that lists the level's number has the vertical pipe's entry's value
(`AreaKeep.smallCheck`) -/
theorem entryAt_of_area (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) {m : Machine}
    (ha : m.ram.get! (AreaKeep.areaI nmS) = (PipeTransition.entry m0).ram.get! (AreaKeep.areaI nmS))
    (h : EntryAt (restIdxA sy nmS m0) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m) :
    EntryAt (restIdxR sy nmS m0) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m := by
  have hV := (AreaKeep.small_parts hR.area.small).2.2.2.2
  obtain ⟨v, hv, hb⟩ := h
  refine ⟨v, hv, fun i hi hiL => ?_⟩
  by_cases e : i = AreaKeep.areaI nmS
  · subst e
    rw [ha, hV v hv hi]
  · exact hb i hi (List.mem_filter.2 ⟨hiL, bne_iff_ne.2 e⟩)

/-- **The height at the side pipe's entry is the reference entry's** (it was a byte of `entry₂`, now the theorem). The frame before `a₂` is a frame of the room
(`Run.b₁_lt_a₂`) and it ends with the side pipe's routine (`Run.rt₂`). If it starts with the reference's size, the walk of `EntryHeight` gives the height
(`EntryHeight.height_of_rows`, on the room's condition with the map's bits of `RoomMap.cond_of_rows`); else `height₂` asks it. `hR`, `hB`, `hK` are checks on the ROM. -/
theorem Run.y₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    (R.base.seq (R.base.a₂ sy nmS m0)).ram.get! (EntryHeight.heightI sy) = (SideTransition.entry m0).ram.get! (EntryHeight.heightI sy) := by
  rcases R.height₂ with hs | hy
  · have hlt := R.b₁_lt_a₂ hR hB hK
    have he := R.entry₁ hB hK
    obtain ⟨k, hk⟩ : ∃ k, R.base.a₂ sy nmS m0 = k + 1 := ⟨R.base.a₂ sy nmS m0 - 1, by omega⟩
    have hrt := R.rt₂ hR hB hK
    rw [hk] at hrt hs ⊢
    rw [Nat.add_sub_cancel] at hs
    rw [R.base.next k] at hrt ⊢
    exact EntryHeight.height_of_rows hR.map hR.mapStart hR.height.walk R.base.next ((R.chg.run₁ he).inRowsT hR.pipe R.chg.ctlFirst₁)
      R.chg.ctl₁ R.chg.roomSites R.chg.roomStay (show R.base.b₁ sy ≤ k by omega) (show k < R.base.a₂ sy nmS m0 by omega) hs hrt
  · exact hy

/-- **The 9 bytes from the 8 and the height**: each reference of the entry that lists the height has the reference entry's value (`EntryHeight.refsCheck`) -/
theorem entryAt_of_y (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) {m : Machine}
    (hy : m.ram.get! (EntryHeight.heightI sy) = (SideTransition.entry m0).ram.get! (EntryHeight.heightI sy))
    (h : EntryAt (restIdxY sy nmS m0) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m) :
    EntryAt (restIdxA sy nmS m0) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m := by
  obtain ⟨v, hv, hb⟩ := h
  refine ⟨v, hv, fun i hi hiL => ?_⟩
  by_cases e : i = EntryHeight.heightI sy
  · subst e
    rw [hy, hR.height.refs v hv hi]
  · exact hb i hi (List.mem_filter.2 ⟨hiL, bne_iff_ne.2 e⟩)

/-- **The five bytes of the first screen buffer at the side pipe's entry are those of a reference** (they were bytes of `entry₂`, now the theorem). The frame before
`a₂` is a frame of the room (`Run.b₁_lt_a₂`) and it ends with the side pipe's routine (`Run.rt₂`). If it starts with the control of the screen's buffers of the
reference, the walk of `EntryBuffer` gives the bytes (`EntryBuffer.buffer_of_rows`); else `buffer₂` asks them. `hR`, `hB`, `hK` are checks on the ROM. -/
theorem Run.buf₂ (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    EntryAt (EntryBuffer.bufIdx nmS) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) (R.base.seq (R.base.a₂ sy nmS m0)) := by
  rcases R.buffer₂ with hs | hy
  · have hlt := R.b₁_lt_a₂ hR hB hK
    have he := R.entry₁ hB hK
    obtain ⟨k, hk⟩ : ∃ k, R.base.a₂ sy nmS m0 = k + 1 := ⟨R.base.a₂ sy nmS m0 - 1, by omega⟩
    have hrt := R.rt₂ hR hB hK
    rw [hk] at hrt hs ⊢
    rw [Nat.add_sub_cancel] at hs
    rw [R.base.next k] at hrt ⊢
    exact EntryBuffer.buffer_of_rows hR.map hR.mapStart hR.buffer.walk R.base.next ((R.chg.run₁ he).inRowsT hR.pipe R.chg.ctlFirst₁)
      R.chg.ctl₁ R.chg.roomSites R.chg.roomStay (show R.base.b₁ sy ≤ k by omega) (show k < R.base.a₂ sy nmS m0 by omega) hs hrt
  · exact hy

/-- **The 8 bytes from the 3 and the screen buffer's five**: the references of the entry agree on the 3 bytes (`EntryBuffer.agreeCheck`), so the reference of the
buffer's bytes also gives the others -/
theorem entryAt_of_buf (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) {m : Machine}
    (hb : EntryAt (EntryBuffer.bufIdx nmS) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m)
    (h : EntryAt (restIdxB sy nmS m0) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m) :
    EntryAt (restIdxY sy nmS m0) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) m := by
  obtain ⟨v, hv, hbv⟩ := hb
  obtain ⟨w, hw, hcw⟩ := h
  refine ⟨v, hv, fun i hi hiL => ?_⟩
  by_cases e : i ∈ EntryBuffer.bufIdx nmS
  · exact hbv i hi e
  · have hiB : i ∈ restIdxB sy nmS m0 := List.mem_filter.2 ⟨hiL, by simpa using e⟩
    obtain ⟨a1, a2⟩ := hR.buffer.agree v hv w hw i hiB hi
    rw [hcw i a1 hiB, a2]

/-- **The changes with the 11 bytes at the side pipe's entry**, as `ChangesK` asks them by default (`HurryMusic`, `HurryStart` take them so): `chg` asks the 3 bytes of
`restIdxB`, the screen buffer's bytes are `Run.buf₂` (`entryAt_of_buf`), the height is `Run.y₂` (`entryAt_of_y`), the level's number is `Run.area₂`
(`entryAt_of_area`) and the routine is `Run.rt₂` (`entryAt_of_rt`). -/
def Run.chgK (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS R.base R.clock.kind R.pipe.E R.room.C R.room.E R.Cs :=
  { R.chg with entry₂ := entryAt_of_rt hR (R.rt₂ hR hB hK) (entryAt_of_area hR (R.area₂ hR hB hK)
      (entryAt_of_y hR (R.y₂ hR hB hK) (entryAt_of_buf hR (R.buf₂ hR hB hK) R.chg.entry₂))) }

/-- the change out of the side pipe takes at least 282 frames -/
theorem Run.change₂ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.E + 282 ≤ R.Cs :=
  (R.chgK hR hB hK).bound₂ hS hT hQ hR (R.entry₁ hB hK)

/-- **The state at control above ground**, on the real machines: it comes from the last row of the change, under the change's conditions. `left` is not 0 before control,
from the time at the exit and the first control (`SideChangeEnd.EndRun.first`). `hc` is the check on the ROM. -/
theorem Run.start {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hc : SideChangeSound.startCheckK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt PA = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    SurfaceFrames.Start sy PA (R.pole.seq 0) := by
  rw [R.atCtl]
  exact ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)).start hS hT hQ hc R.chg.ctlFirst₂

/-- **The machine at control above ground, as the walk of one whole frame needs it**, on the real machines: the start of a frame in control, with the castle flag down. From the last
row of the change, under the same conditions as `Run.start`. `hc` and `hk` are checks on the ROM. With `PoleJoin.Run.keep` it gives no castle flag up to the touch
(`PoleJoin.Run.noCastle_of`) and the start of every frame up to the touch (`FrameKeep.Frames.start`). -/
theorem Run.atCtl₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hk : SideChangeSound.ctlCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    FrameKeep.AtCtl sy m0 (R.pole.seq 0) := by
  rw [R.atCtl]
  exact ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)).atCtl' hS hT hQ hk R.chg.ctlFirst₂

/-- **The side pipe's tiles at the reads of the room's entering frame**, on the real machines: `RoomMap.map_of_rows` on the frames of `base` in the room, from the rows of the change into
the room, and `Run.roomEnter`. `hT₁`, `hM`, `hS` are checks on the ROM. The old field `room.tiles`. -/
theorem Run.roomTiles {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.TilesE := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter hR hB hK
  have he := R.entry₁ hB hK
  have h := (RoomMap.map_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.ctlFirst₁) R.chg.ctl₁
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
  have h := RoomMap.start_of_rowsF (a := R.base.a₂ sy nmS m0) hM hS hF R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.ctlFirst₁) R.chg.ctl₁
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
  have h := RoomMap.clean_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.ctlFirst₁) R.chg.ctl₁
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
  have h := RoomMap.head_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay k h1 h2
  intro j
  show (PipeEntryRule.trace (R.room.fm (R.room.E - 1)) (R.room.pad R.room.E) j).pc ≠ PipeWrites.headAt sy m0
  rw [e1, e2]
  exact h j

/-- **No frame of `room` before the entry comes to the head's collision with a block**, on the real machines: neither to its routine (`PipeWrites.headAt`) nor to the bump on a
solid block (`SideFrame.bumpAt`). `RoomMap.head_of_rows` and `RoomMap.bump_of_rows` on the frames of `base` in the room: the room's frame `n + 1` begins at frame
`b₁ + ix (n + 1 − C) − 1`, before `a₂` (`Run.roomIdx`). `hT₁`, `hM`, `hS`, `hB`, `hK` are checks on the ROM. With it the field `room.vfloor` no longer asks that he does
not hit his head. -/
theorem Run.roomBump {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → ∀ j, (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc ≠ PipeWrites.headAt sy m0 ∧
      (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc ≠ SideFrame.bumpAt sy m0 := by
  intro n hC hE j
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  exact ⟨RoomMap.head_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk j,
    RoomMap.bump_of_rows (a := R.base.a₂ sy nmS m0) hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk j⟩

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
  exact SideEntryRest.mouth_of_rows (a := R.base.a₂ sy nmS m0) hM hS hF hEnd hRest R.base.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.ctlFirst₁)
    R.chg.ctl₁ R.chg.roomSites R.chg.roomStay h1 h2 hen

/-- an instruction that meets `SiteOK` of the room and is not at the idle loop runs at least 64 dots before the frame's end: the room's `late` is 6000 dots before it -/
theorem late_of {nmS : Names} {m0 m : Machine} (h : ScreenPage.SiteOK (ScreenPage.placesR sy nmS m0) m) (hn : m.pc ≠ (ScreenPage.placesR sy nmS m0).idle) :
    m.fdot ≤ dotsPerFrame - 64 := by
  have e : (ScreenPage.placesR sy nmS m0).late = dotsPerFrame - 6000 := rfl
  have h1 := h.late hn
  rw [e] at h1
  omega

/-- **Each frame of `room` before the entry comes to the player's routine before its end**, on the real machines: `RoomVert.before_R` on the frames of `base` in the room (the
walk to the player's routine; its states at the frame's end are not there). `hV` are the checks of `RoomVert`. -/
theorem Run.roomArrive {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → ∀ j, (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc = sy.PlayerCtrlRoutine →
      (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).frame = (R.room.fm n).frame := by
  intro n hC hE
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk
  have hsites := R.chg.roomSites _ hk0 hk
  exact (RoomVert.before_R (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun _ hB' => RoomVert.finA_pc hB') hcond hsites).2.2.2

/-- **At the player's routine in each frame of `room` before the entry, the horizontal bytes are those of the frame's start**, on the real machines:
`RoomVert.hbytes_at_R` on the frames of `base` in the room (the walk to the player's routine keeps them). The old part `before` of `room.clean`. -/
theorem Run.roomBefore {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → ∀ j, (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc = sy.PlayerCtrlRoutine →
      ∀ a ∈ FrameModel.hBytes sy, peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j) a = peek (R.room.fm n) a := by
  intro n hC hE j hj
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk
  have hsites := R.chg.roomSites _ hk0 hk
  exact RoomVert.hbytes_at_R (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun _ hB' => RoomVert.finA_pc hB') hcond hsites hj

/-- **In each frame of `room` before the entry, at the player's routine the player's state is that of the frame's start**, on the real machines: `RoomVert.st_at_R` on
the frames of `base` in the room, as `Run.roomBefore` -/
theorem Run.roomStR {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → ∀ j, (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc = sy.PlayerCtrlRoutine →
      peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j) sy.Player_State = peek (R.room.fm n) sy.Player_State := by
  intro n hC hE j hj
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk
  have hsites := R.chg.roomSites _ hk0 hk
  exact RoomVert.st_at_R (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun _ hB' => RoomVert.finA_pc hB') hcond hsites hj

/-- **Each frame of `room` before the entry that ends with the game not paused comes to the player's routine, a first time at `room.arr n`**, on the real machines:
`RoomVert.arrive_R` on the frames of `base` in the room (the walk to the player's routine splits the pause byte's low bit at its load before the call of the mode's routine;
its states at the frame's end that have not come there know the game paused), and `CtrlKeep.arrAt_eq`. -/
theorem Run.roomReach {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → CtrlKeep.Unpaused sy m0 (PipeTransition.frame (R.room.fm n) (R.room.inAt n)) →
      (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) (R.room.arr n)).pc = sy.PlayerCtrlRoutine := by
  intro n hC hE hu
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk
  have hsites := R.chg.roomSites _ hk0 hk
  obtain ⟨j, hj, _, hjf, hfirst⟩ := RoomVert.arrive_R (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) rfl hcond hsites hu
  show (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) (CtrlKeep.arrAt sy (R.room.fm n) (R.room.inAt n))).pc = sy.PlayerCtrlRoutine
  rw [CtrlKeep.arrAt_eq hj hfirst hjf]
  exact hj

/-- **At the player's routine in each frame of `room` before the entry, the machine is in the state `VertAir.AtV`**, on the real machines: `RoomVert.cut_R` (the walk to
the player's routine knows there the stack, the NMI, the routine byte, the area's type, the jumpspring and the swimming flag), `RoomPair.quad_run` (at the frame's start the
player's state is 0, 1 or 2 and the change of size is 0: two walks of the room's frames, and the rows of the change at the first control), and `RoomVert.before_R` (no step
before the routine writes these two bytes). `hF` gives the program. The old part of `room.clean`'s `at_ctrl` and `at_frame` but the values. -/
theorem Run.roomCut {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hF : RoomMap.startCheckF sy nmS m0 = true)
    (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise) (hQ : RoomPair.QuadWalks sy nmS m0) (hP : RoomPair.Checks sy nmS m0 nm₁ d₁ rN.vStart)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → ∀ j, (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc = sy.PlayerCtrlRoutine →
      VertAir.AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j) := by
  intro n hC hE j hj
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk
  have hsites := R.chg.roomSites _ hk0 hk
  have hA := RoomVert.okV_of_check hV.a
  obtain ⟨a1, a2, _, a4⟩ := RoomVert.before_R (CtrlKeep.pauseI_lt sy m0) hA (fun _ hB' => RoomVert.finA_pc hB') hcond hsites
  have hf := a4 j hj
  have hfirst : ∀ j', j' < j → (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j').pc ≠ sy.PlayerCtrlRoutine := fun j' hj' hR' => a2 j' j hj' hR' hf hj
  have hkeep := a1 j hf hfirst
  have eq : ∀ a : UInt16, RoomVert.I a ∈ RoomVert.vKeepA sy → peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j) a = peek (R.room.fm n) a :=
    fun a ha => hkeep _ ha
  have c := RoomVert.cut_R (CtrlKeep.pauseI_lt sy m0) hA hcond hsites hj hf
  have hq := RoomPair.quad_run hQ hP hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk
  have hfs := RoomMap.frameStart_of_cond hF hcond
  have hprg : (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).prg = m0.prg := by
    rw [c.prg, ← hcond.prg]
    exact hfs.prg
  have hmask : (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).prgMask = m0.prgMask := by
    rw [c.mask, ← hcond.mask]
    exact hfs.mask
  refine ⟨⟨hprg, hmask, c.nmi, c.halted, c.trk, c.size, c.ctl⟩, hj, c.s, c.eng, c.area, ?_, c.spring, c.swim, ?_⟩
  · rw [eq sy.Player_State (by simp [RoomVert.vKeepA, RoomVert.vKeep])]
    rcases hq.st with e | e | e <;> rw [e] <;> simp
  · rw [eq sy.PlayerChangeSizeFlag (by simp [RoomVert.vKeepA])]
    exact hq.size

/-- **Each instruction of each frame of `room` before the entry that is not at the idle loop runs at least 64 dots before the frame's end**: `roomSites` and `late_of` -/
theorem Run.roomTime
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → ∀ j, (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).pc ≠ (ScreenPage.placesR sy nmS m0).idle →
      (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) j).fdot ≤ dotsPerFrame - 64 := by
  intro n hC hE j hj
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  exact late_of (R.chg.roomSites _ hk0 hk j) hj

/-- **A frame of `room` on a jump's first frames follows `vstep`**, on the real machines: `RoomVert.air_arc` on the frames of `base` in the room. The room's frame `n + 1` is the
frame from `b₁ + ix (n + 1 − C) − 1` of `base` (`Run.roomIdx`); it starts in the room's condition (`RoomMap.cond_of_rows`), its instructions meet `SiteOK` (`roomSites`), and before the entering frame it ends in
the player's routine (`roomStay`). `SiteOK` puts each instruction away from the idle loop 6000 dots before the frame's end (`late_of`), so the frame does not end during the
movement. `hV` are the checks of `RoomVert`, `hI` says that the idle loop is a `JMP` to itself. -/
theorem Run.roomVert {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hI : FrameModel.idleAt (FrameModel.Rom.of m0) (ScreenPage.placesR sy nmS m0).idle = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    {n : Nat} (hC : R.room.C ≤ n) (hE : n + 1 < R.room.E) {k : Nat}
    (hAt : VertAir.AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k))
    (hd : peek (R.room.fm n) sy.Player_State = 1 → peek (R.room.fm n) sy.DiffToHaltJump = 1)
    (hp : peek (R.room.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (R.room.fm n) sy.A_B_Buttons &&& 0x80)
    (hu : VertModel.vsOf sy (R.room.fm n) ∈ (VertAir.arcSet sy m0 rN.h rN.rise).map (·.s))
    (ht : Jump.vstep sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∈
      (VertAir.arcSet sy m0 rN.h rN.rise).map (·.s))
    (hvy : (Jump.vstep sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&&
      0x80 = 0x80) :
    VertModel.vsOf sy (PipeTransition.frame (R.room.fm n) (R.room.inAt n)) =
      Jump.vstep sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0 := by
  obtain ⟨hk0, hk1⟩ := R.roomIdx hC (show n < R.room.E by omega)
  obtain ⟨_, hk2⟩ := R.roomIdx (n := n + 1) (by omega) hE
  have hm := R.roomMany
  have hlt := R.room.ix_lt (k := n + 1 - R.room.C) (by omega)
  have h1 := (R.room.ix_at (k := n + 1 - R.room.C) (by omega) (by omega)).1
  rw [show n + 1 + 1 - R.room.C = n + 1 - R.room.C + 1 by omega] at hk2
  have hk : R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1 < R.base.a₂ sy nmS m0 := by omega
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk1
  have hsites := R.chg.roomSites _ hk0 hk1
  have hstay := R.chg.roomStay (R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1) (by omega) hk
  rw [R.base.next] at hstay
  exact RoomVert.air_arc hV hI hcond hsites hAt (fun j hj => late_of (hsites j) hj) hd hp hu ht hvy hstay

/-- **Every frame of `room` in the air before the entering frame follows `vstep` up to the landing**, on the real machines: `RoomFall.jump_room` on the frames of `base`
in the room, as `Run.roomVert`. The frame starts in the room's condition (`RoomMap.cond_of_rows`), its instructions meet `SiteOK` (`roomSites`), it ends in the player's
routine (`roomStay`), and at its start the player's state is 0, 1 or 2 (`RoomPair.quad_run`), so 1 or 2. `hV`, `hF` are the checks of `RoomVert` and `RoomFall`. -/
theorem Run.roomAir {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hF : RoomFall.FChecks sy nmS m0 rN.h) (hI : FrameModel.idleAt (FrameModel.Rom.of m0) (ScreenPage.placesR sy nmS m0).idle = true)
    (hQ : RoomPair.QuadWalks sy nmS m0) (hP : RoomPair.Checks sy nmS m0 nm₁ d₁ rN.vStart)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    {n : Nat} (hC : R.room.C ≤ n) (hE : n + 1 < R.room.E) (hst0 : peek (R.room.fm n) sy.Player_State ≠ 0) {k : Nat}
    (hAt : VertAir.AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k))
    (hd : peek (R.room.fm n) sy.Player_State = 1 → peek (R.room.fm n) sy.DiffToHaltJump = 1)
    (hp : peek (R.room.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (R.room.fm n) sy.A_B_Buttons &&& 0x80) :
    ((RoomJoin.vstepR sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)).st = 1 ∨
     (RoomJoin.vstepR sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)).st = 2) ∧
    (VertModel.vsOf sy (PipeTransition.frame (R.room.fm n) (R.room.inAt n)) =
       RoomJoin.vstepR sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) ∨
     (Jump.falling (RoomJoin.vstepR sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)) = true ∧
      VertModel.vsOf sy (PipeTransition.frame (R.room.fm n) (R.room.inAt n)) =
        VertAir.land (RoomJoin.vstepR sy m0 (VertModel.vsOf sy (R.room.fm n)) (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)))) := by
  obtain ⟨hk0, hk1⟩ := R.roomIdx hC (show n < R.room.E by omega)
  obtain ⟨_, hk2⟩ := R.roomIdx (n := n + 1) (by omega) hE
  have hm := R.roomMany
  have hlt := R.room.ix_lt (k := n + 1 - R.room.C) (by omega)
  have h1 := (R.room.ix_at (k := n + 1 - R.room.C) (by omega) (by omega)).1
  rw [show n + 1 + 1 - R.room.C = n + 1 - R.room.C + 1 by omega] at hk2
  have hk : R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1 < R.base.a₂ sy nmS m0 := by omega
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk1
  have hsites := R.chg.roomSites _ hk0 hk1
  have hstay := R.chg.roomStay (R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1) (by omega) hk
  rw [R.base.next] at hstay
  have hq := RoomPair.quad_run hQ hP hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk1
  have hst : peek (R.room.fm n) sy.Player_State = 1 ∨ peek (R.room.fm n) sy.Player_State = 2 := by
    rcases hq.st with e | e | e
    · exact absurd e hst0
    · exact Or.inl e
    · exact Or.inr e
  exact RoomFall.jump_room hV hF hI hcond hsites hAt (fun j hj => late_of (hsites j) hj) hst hd hp hstay

/-- **Every frame of `room` before the entering frame that starts standing with no jump in its input at the player's routine ends as `RoomJoin.StandNext` allows**, on the
real machines: `RoomStand.stand_room` on the frames of `base` in the room, as `Run.roomAir`. The frame starts in the room's condition (`RoomMap.cond_of_rows`), its instructions
meet `SiteOK` (`roomSites`), and it ends in the player's routine (`roomStay`). `hV`, `hSt` are the checks of `RoomVert` and `RoomStand`. -/
theorem Run.roomStand {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hSt : RoomStand.SChecks sy nmS m0) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    {n : Nat} (hC : R.room.C ≤ n) (hE : n + 1 < R.room.E) (hst0 : peek (R.room.fm n) sy.Player_State = 0) {k : Nat}
    (hRk : (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k).pc = sy.PlayerCtrlRoutine)
    (hn : (FrameModel.readIn sy (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k)).jump = false) :
    RoomJoin.StandNext (VertModel.vsOf sy (R.room.fm n)) (VertModel.vsOf sy (PipeTransition.frame (R.room.fm n) (R.room.inAt n))) := by
  obtain ⟨hk0, hk1⟩ := R.roomIdx hC (show n < R.room.E by omega)
  obtain ⟨_, hk2⟩ := R.roomIdx (n := n + 1) (by omega) hE
  have hm := R.roomMany
  have hlt := R.room.ix_lt (k := n + 1 - R.room.C) (by omega)
  have h1 := (R.room.ix_at (k := n + 1 - R.room.C) (by omega) (by omega)).1
  rw [show n + 1 + 1 - R.room.C = n + 1 - R.room.C + 1 by omega] at hk2
  have hk : R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1 < R.base.a₂ sy nmS m0 := by omega
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk1
  have hsites := R.chg.roomSites _ hk0 hk1
  have hstay := R.chg.roomStay (R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1) (by omega) hk
  rw [R.base.next] at hstay
  exact RoomStand.stand_room hV hSt hcond hsites hRk hst0 hn hstay

/-- **Every frame of `room` before the entering frame that comes to the player's routine with a jump in its input ends on the takeoff of its height**, on the real
machines: `RoomJump.jump_room` on the frames of `base` in the room, as `Run.roomVert`. The frame starts in the room's condition (`RoomMap.cond_of_rows`), its instructions
meet `SiteOK` (`roomSites`), and it ends in the player's routine (`roomStay`). `hV` are the checks of `RoomVert`, `hJ` is the walk of two machines on a takeoff. -/
theorem Run.roomJump {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hJ : VertJump.jumpOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hI : FrameModel.idleAt (FrameModel.Rom.of m0) (ScreenPage.placesR sy nmS m0).idle = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    {n : Nat} (hC : R.room.C ≤ n) (hE : n + 1 < R.room.E) {k : Nat}
    (hAt : VertAir.AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k))
    (hj : (FrameModel.readIn sy (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k)).jump = true) :
    VertModel.vsOf sy (PipeTransition.frame (R.room.fm n) (R.room.inAt n)) =
      VertJump.jumpOff sy m0 (FrameModel.ctrlStack sy m0) (peek (R.room.fm n) sy.Player_Y_Position)
        (peek (PipeEntryRule.trace (R.room.fm n) (R.room.inAt n) k) sy.Player_XSpeedAbsolute) := by
  obtain ⟨hk0, hk1⟩ := R.roomIdx hC (show n < R.room.E by omega)
  obtain ⟨_, hk2⟩ := R.roomIdx (n := n + 1) (by omega) hE
  have hm := R.roomMany
  have hlt := R.room.ix_lt (k := n + 1 - R.room.C) (by omega)
  have h1 := (R.room.ix_at (k := n + 1 - R.room.C) (by omega) (by omega)).1
  rw [show n + 1 + 1 - R.room.C = n + 1 - R.room.C + 1 by omega] at hk2
  have hk : R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1 < R.base.a₂ sy nmS m0 := by omega
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk1
  have hsites := R.chg.roomSites _ hk0 hk1
  have hstay := R.chg.roomStay (R.base.b₁ sy + (R.room.ix (n + 1 - R.room.C) - 1) + 1) (by omega) hk
  rw [R.base.next] at hstay
  exact RoomJump.jump_room hV hJ hI hcond hsites hAt (fun j hj => late_of (hsites j) hj) hj hstay

/-- **The blocks of the room's map stay on every frame of `base` in the room**: from the first control `b₁` to the frame `a₂` of the side pipe's entry, at the start of
each frame every byte of the block buffers that is not a coin in the map has the map's value (`RoomBlocks.blocks_run`). The machine at `b₁` is a machine with control
in the rows of the change into the room (`inRowsT`, `ctl₁`); each frame before `a₂` meets `SiteOK` (`roomSites`) and starts in the player's routine (`roomStay`).
`hW` are the checks of `RoomBlocks`, `hRw` the rows' check with the blocks. No theorem of the route uses it yet. -/
theorem Run.roomBlocks {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hW : RoomBlocks.BChecks sy nmS m0) (hRw : RoomBlocks.rowsCheckR sy nm₁ d₁ nmS m0 rN.vStart = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.base.b₁ sy ≤ n → n ≤ R.base.a₂ sy nmS m0 → RoomBlocks.SolidR sy nmS m0 (R.base.seq n) :=
  RoomBlocks.blocks_run hW hRw hM hS R.base.next ((R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁) R.chg.ctl₁ R.chg.roomSites R.chg.roomStay

/-- **At the end of each frame of `room` before the entry, in a jump the jump's halt value is 1, and bit 7 of A of the frame before is bit 7 of A**, on the real machines:
`RoomPair.pair_run` on the frames of `base` in the room. The room's frame `n + 1` begins at frame `b₁ + ix (n + 1 − C) − 1` of `base`, before `a₂`
(`Run.roomIdx`); the rows of the change give both at the
first control, and each frame of the room keeps them (two walks). `hP` are the checks of `RoomPair`. The old fields `room.halt` and `room.prevA`. -/
theorem Run.roomPair {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hP : RoomPair.Checks sy nmS m0 nm₁ d₁ rN.vStart)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → (peek (R.room.fm n) sy.Player_State = 1 → peek (R.room.fm n) sy.DiffToHaltJump = 1) ∧
      peek (R.room.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (R.room.fm n) sy.A_B_Buttons &&& 0x80 := by
  intro n hC hE
  obtain ⟨hk0, hk⟩ := R.roomIdx hC hE
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have h := RoomPair.pair_run (a := R.base.a₂ sy nmS m0) hP hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay _ hk0 hk
  exact ⟨h.halt, h.prevA⟩

/-- **The vertical state at first control in the room is a state of `rN.vStart`**, on the real machines: the rows of the change into the room know the vertical bytes of
a machine with control (`RoomPair.v_of_rows`), and the room's first control is a machine of the rows (`Run.roomCtl`). `hP` are the checks of `RoomPair`. -/
theorem Run.roomV0 {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁) (hP : RoomPair.Checks sy nmS m0 nm₁ d₁ rN.vStart)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    SurfaceFrames.vsOf sy (R.room.fe R.room.C) ∈ rN.vStart := by
  rw [R.roomCtl]
  exact RoomPair.v_of_rows hP.rows ((R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁) R.chg.ctl₁

/-- **The frames between the end of the room's frame `n` and the start of its frame `n + 1` keep what the model reads**, on the real machines: the horizontal state,
the position and the vertical state. They end paused (`RoomJoin.RoomRun.between`), they are frames of `base` in the room (`Run.roomIdx`), so each starts in the room's
condition (`RoomMap.cond_of_rows`) and meets `SiteOK` (`roomSites`), and the walk to the player's routine says that it does not come there and keeps the bytes of
`RoomVert.vKeepA` (`RoomVert.paused_R`). `hV` are the checks of `RoomVert`. -/
theorem Run.roomKeep {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hV : RoomVert.VChecks sy nmS m0 rN.h rN.rise)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.room.C ≤ n → n < R.room.E → FrameModel.readHS sy (R.room.fm n) = FrameModel.readHS sy (R.room.fe n) ∧ posP sy (R.room.fm n) = posP sy (R.room.fe n) ∧
      SurfaceFrames.vsOf sy (R.room.fm n) = SurfaceFrames.vsOf sy (R.room.fe n) := by
  intro n hC hE
  have hm := R.roomMany
  obtain ⟨_, hk⟩ := R.roomIdx hC hE
  have hlt : R.room.ix (n - R.room.C) < R.room.ix (n + 1 - R.room.C) := by
    have := R.room.ix_lt (k := n - R.room.C) (by omega)
    rwa [show n - R.room.C + 1 = n + 1 - R.room.C by omega] at this
  have hin := (R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁
  have hA := RoomVert.okV_of_check hV.a
  have step : ∀ d, R.room.ix (n - R.room.C) + d ≤ R.room.ix (n + 1 - R.room.C) - 1 → ∀ x ∈ RoomVert.vKeepA sy,
      (R.base.seq (R.base.b₁ sy + (R.room.ix (n - R.room.C) + d))).ram.get! x = (R.base.seq (R.base.b₁ sy + R.room.ix (n - R.room.C))).ram.get! x := by
    intro d
    induction d with
    | zero => intro _ x _; rfl
    | succ d ih =>
      intro hd x hx
      have hkk : R.base.b₁ sy + (R.room.ix (n - R.room.C) + d) < R.base.a₂ sy nmS m0 := by omega
      have hp := R.room.between hC (by omega) (k := R.room.ix (n - R.room.C) + d) (by omega) (by omega)
      have hcond := RoomMap.cond_of_rows hM hS R.base.next hin R.chg.ctl₁ R.chg.roomSites R.chg.roomStay (R.base.b₁ sy + (R.room.ix (n - R.room.C) + d))
        (Nat.le_add_right _ _) hkk
      have hsites := R.chg.roomSites (R.base.b₁ sy + (R.room.ix (n - R.room.C) + d)) (Nat.le_add_right _ _) hkk
      have hp1 : (PipeTransition.frame (R.base.seq (R.base.b₁ sy + (R.room.ix (n - R.room.C) + d))) (R.base.inp (R.base.b₁ sy + (R.room.ix (n - R.room.C) + d)))).ram.get!
          (CtrlKeep.pauseI sy m0) &&& 1 = 1 := by
        rw [← R.base.next]
        exact PipeFrames.and1_of_ne hp
      have e := RoomVert.paused_R (CtrlKeep.pauseI_lt sy m0) hA rfl hcond hsites hp1 x hx
      rw [← R.base.next] at e
      show (R.base.seq (R.base.b₁ sy + (R.room.ix (n - R.room.C) + d) + 1)).ram.get! x = _
      rw [e]
      exact ih (by omega) x hx
  have hall := step (R.room.ix (n + 1 - R.room.C) - 1 - R.room.ix (n - R.room.C)) (by omega)
  rw [show R.room.ix (n - R.room.C) + (R.room.ix (n + 1 - R.room.C) - 1 - R.room.ix (n - R.room.C)) = R.room.ix (n + 1 - R.room.C) - 1 by omega] at hall
  obtain ⟨a1, a2, a3⟩ := RoomVert.model_eq_of hall
  exact ⟨a1, a2, a3⟩

/-- **What the room's frames give**: the entering frame ends with the position at or right of the mouth, no frame before it comes to the head's collision with a block, a
frame on a jump's first frames follows `vstep`, a frame in the air follows `vstep` up to the landing, a frame that starts standing with no new press of A keeps the height
or lands, a frame that starts standing with a new press of A ends on the takeoff of its height, at the player's routine the player's state is that of the frame's start, at the end of each frame before the entry the jump's halt value and A of the frame before are as the movement routine needs,
and each frame before the entry comes to the player's routine before its end and runs each instruction away from the idle loop at least 64 dots before it; the vertical
state at first control is a state of `rN.vStart`.
`hV` are the checks of the room's walks (`RoomVert`, `RoomPair`), of the rows at first control and of the idle loop. -/
theorem Run.inRoom {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hF : RoomMap.startCheckF sy nmS m0 = true)
    (hEnd : SideEntryEnd.sideEntryEndCheck sy m0 = true) (hRest : SideEntryRest.restCheck sy nmS m0 = true) (hV : RoomPair.RoomWalks sy nmS m0 rN.h rN.rise nm₁ d₁ rN.vStart)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.InRoom :=
  ⟨R.roomMany, R.roomKeep hT₁ hM hS hV.vert hB hK, R.roomMouthE hT₁ hM hS hF hEnd hRest hR hB hK, R.roomBump hT₁ hM hS hB hK,
    fun _ hC hE _ hAt hd hp hu ht hvy => R.roomVert hT₁ hM hS hV.vert hV.idle hB hK hC hE hAt hd hp hu ht hvy,
    fun _ hC hE hst _ hAt hd hp => R.roomAir hT₁ hM hS hV.vert hV.fall hV.idle hV.quad hV.pair hB hK hC hE hst hAt hd hp,
    fun _ hC hE hst _ hRk hn => R.roomStand hT₁ hM hS hV.vert hV.stand hB hK hC hE hst hRk hn,
    R.roomPair hT₁ hM hS hV.pair hB hK, R.room_le, ⟨_, hV.idle, R.roomTime⟩, R.roomArrive hT₁ hM hS hV.vert hB hK,
    R.roomReach hT₁ hM hS hV.vert hB hK, R.roomCut hT₁ hM hS hF hV.vert hV.quad hV.pair hB hK, R.roomBefore hT₁ hM hS hV.vert hB hK,
    R.roomV0 hT₁ hV.pair hB hK, R.roomStR hT₁ hM hS hV.vert hB hK,
    fun _ hC hE _ hAt hj => R.roomJump hT₁ hM hS hV.vert hV.jump hV.idle hB hK hC hE hAt hj⟩

/-- the frames after the timer's count: at least 33 -/
theorem Run.hD (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) : 33 ≤ R.Df hF :=
  (R.flagRun hF).hD

/-- the level change is not before the first grid point after the sum -/
theorem Run.hL (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) (hsy : fc.sy = sy)
    (hw : 6 ≤ sy.StarFlagDelay.toNat) : R.E + R.T + R.Df hF + 107 + wait R.c (R.T + R.Df hF) ≤ R.L :=
  (R.flagRun hF).hL (by show 6 ≤ fc.sy.StarFlagDelay.toNat; rw [hsy]; exact hw)

/-! ## Above ground: the clock's `lag` frames and the frames that end paused

`pole` counts the frames from `b₂` on that end not paused (`FrameKeep.Keep`), and `clock` the frames that are not `lag` frames. Above ground nothing ties the two but their
number up to the castle entry: `clock` counts `Cs + pole.c` frames up to `E` (`Segs.last`). When each frame from `b₂` to `E` is a `lag` frame exactly when it ends paused
(`Run.LagUp`, one frame at a time), the two count the same frames: the counted frame `j` of `pole` is the frame of `clock` with the count `Cs + j` (`Run.count_up`), the
castle entry `E` of `clock` is the counted frame `c` of `pole` (`Run.castle_join`), the `lag` frames above ground are the frames that end paused (`Run.j_up`), and the castle
flag of `pole.atCastle` is that of the machine after `E` (`Run.atCastle_of_flag`). `LagUp` is not a field of `Run`: these theorems take it. -/

/-- **Above ground, a frame is a `lag` frame exactly when it ends paused**: each frame from control above ground (`b₂`) to the castle entry `E` -/
def Run.LagUp (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Prop :=
  ∀ n, R.base.b₂ sy nmS m0 ≤ n → n ≤ R.E → (R.clock.kind n = .lag ↔ ¬ FrameKeep.Unpaused sy m0 (R.base.seq (n + 1)))

/-- with `LagUp`, from `b₂` on `clock` counts the frames that end not paused -/
theorem Run.seen_up (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) :
    ∀ d, R.base.b₂ sy nmS m0 + d ≤ R.E + 1 → seen R.clock.kind (R.base.b₂ sy nmS m0 + d) =
      seen R.clock.kind (R.base.b₂ sy nmS m0) + FrameKeep.upTo (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) d := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have hk := hL (R.base.b₂ sy nmS m0 + d) (by omega) (by omega)
    show seen R.clock.kind (R.base.b₂ sy nmS m0 + d + 1) = _
    rw [FrameKeep.upTo_succ]
    simp only [seen]
    rw [h1]
    by_cases hl : R.clock.kind (R.base.b₂ sy nmS m0 + d) = .lag
    · have hu := hk.1 hl
      have hf : FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0) (d + 1) = false := by
        simp only [FrameKeep.upAt, beq_eq_false_iff_ne]
        exact hu
      rw [if_pos hl, hf]
      simp
    · have hu : FrameKeep.Unpaused sy m0 (R.base.seq (R.base.b₂ sy nmS m0 + d + 1)) := by
        by_cases h : FrameKeep.Unpaused sy m0 (R.base.seq (R.base.b₂ sy nmS m0 + d + 1))
        · exact h
        · exact absurd (hk.2 h) hl
      have hf : FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0) (d + 1) = true := by
        simp only [FrameKeep.upAt, beq_iff_eq]
        exact hu
      rw [if_neg hl, hf]
      simp only [if_true]
      omega

/-- the castle entry is after control above ground, and `clock` counts the frames from `b₂` to `E` that end not paused: `pole.c` of them, the last one frame `E` -/
theorem Run.up_E (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) (hgc : R.pole.g < R.pole.c) :
    R.base.b₂ sy nmS m0 ≤ R.E ∧
      FrameKeep.upTo (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) (R.E + 1 - R.base.b₂ sy nmS m0) = R.pole.c ∧
      FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0) (R.E + 1 - R.base.b₂ sy nmS m0) = true := by
  have hb : seen R.clock.kind (R.base.b₂ sy nmS m0) = R.Cs + 1 := R.chg.hb₂
  have hE : seen R.clock.kind R.E = R.Cs + R.pole.c := R.clock.seen_E
  have hr : R.clock.kind R.E ≠ .lag := R.clock.runs_E
  have hE1 : seen R.clock.kind (R.E + 1) = R.Cs + R.pole.c + 1 := by
    simp only [seen]
    rw [if_neg hr, hE]
  have h1 := R.pole.one_le
  have haE : R.base.b₂ sy nmS m0 ≤ R.E := by
    rcases Nat.lt_or_ge R.E (R.base.b₂ sy nmS m0) with h | h
    · have := CastleToLevel.seen_mono R.clock.kind (show R.E + 1 ≤ R.base.b₂ sy nmS m0 by omega)
      omega
    · exact h
  refine ⟨haE, ?_, ?_⟩
  · have hD := R.seen_up hL (R.E + 1 - R.base.b₂ sy nmS m0) (by omega)
    rw [show R.base.b₂ sy nmS m0 + (R.E + 1 - R.base.b₂ sy nmS m0) = R.E + 1 by omega] at hD
    omega
  · have hu : FrameKeep.Unpaused sy m0 (R.base.seq (R.E + 1)) := by
      by_cases h : FrameKeep.Unpaused sy m0 (R.base.seq (R.E + 1))
      · exact h
      · exact absurd ((hL R.E haE (Nat.le_refl _)).2 h) hr
    simp only [FrameKeep.upAt, beq_iff_eq]
    rw [show R.base.b₂ sy nmS m0 + (R.E + 1 - R.base.b₂ sy nmS m0) = R.E + 1 by omega]
    exact hu

/-- **The castle entry of `clock` is the counted frame `c` of `pole`**: the machine after frame `E` is the machine at the end of the counted frame `c`. With `LagUp`; `hgc`
says that the touch comes before the castle entry (as `Run.hT`, `Run.hc`). The counted frame `c` is a real frame of the run by `pole.toCastle`. -/
theorem Run.castle_join (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) (hgc : R.pole.g < R.pole.c) :
    R.base.seq (R.E + 1) = R.pole.seq R.pole.c ∧
      FrameKeep.ixOf sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0) R.pole.keep.top R.pole.c = R.E + 1 - R.base.b₂ sy nmS m0 := by
  obtain ⟨haE, hup, hf⟩ := R.up_E hL hgc
  have h1 := R.pole.one_le
  obtain ⟨_, s2, s3⟩ := FrameKeep.nthUp_spec R.pole.toCastle
  have hlt : ∀ k, k < R.E + 1 - R.base.b₂ sy nmS m0 →
      FrameKeep.upTo (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) k < R.pole.c := by
    intro k hk
    have e : R.E + 1 - R.base.b₂ sy nmS m0 = (R.E - R.base.b₂ sy nmS m0) + 1 := by omega
    have hs := FrameKeep.upTo_succ (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) (R.E - R.base.b₂ sy nmS m0)
    rw [← e, hf, hup] at hs
    have hm := FrameKeep.upTo_mono (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) (show k ≤ R.E - R.base.b₂ sy nmS m0 by omega)
    simp only [if_true] at hs
    omega
  have hn : FrameKeep.nthUp (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top R.pole.c = R.E + 1 - R.base.b₂ sy nmS m0 := by
    rcases Nat.lt_trichotomy (FrameKeep.nthUp (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top R.pole.c) (R.E + 1 - R.base.b₂ sy nmS m0) with h | h | h
    · have := hlt _ h
      omega
    · exact h
    · have := s3 _ h
      omega
  refine ⟨?_, hn⟩
  show R.base.seq (R.E + 1) = R.base.seq (R.base.b₂ sy nmS m0 + FrameKeep.nthUp (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top R.pole.c)
  rw [hn, show R.base.b₂ sy nmS m0 + (R.E + 1 - R.base.b₂ sy nmS m0) = R.E + 1 by omega]

/-- **The counted frame `j` of `pole` is the frame of `clock` with the count `Cs + j`**, for `1 ≤ j ≤ c`: a frame `n` from `b₂` to `E` that is not a `lag` frame, after which
the machine is `pole.seq j`, and before which `clock` has counted `Cs + j` frames. With `LagUp`. -/
theorem Run.count_up (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) (hgc : R.pole.g < R.pole.c) :
    ∀ j, 1 ≤ j → j ≤ R.pole.c → ∃ n, R.base.b₂ sy nmS m0 ≤ n ∧ n ≤ R.E ∧ R.base.seq (n + 1) = R.pole.seq j ∧ R.clock.kind n ≠ .lag ∧ seen R.clock.kind n = R.Cs + j := by
  intro j hj1 hj2
  obtain ⟨haE, hup, _⟩ := R.up_E hL hgc
  have hc := (R.castle_join hL hgc).2
  have hb : seen R.clock.kind (R.base.b₂ sy nmS m0) = R.Cs + 1 := R.chg.hb₂
  have hjt : j ≤ FrameKeep.upTo (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top := Nat.le_trans hj2 R.pole.toCastle
  obtain ⟨a1, a2, a3⟩ := FrameKeep.nthUp_at hj1 hjt
  obtain ⟨_, _, s3⟩ := FrameKeep.nthUp_spec hjt
  -- the counted frame `j` ends no later than the counted frame `c`
  have hle : FrameKeep.nthUp (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top j ≤ R.E + 1 - R.base.b₂ sy nmS m0 := by
    rcases Nat.lt_or_ge (R.E + 1 - R.base.b₂ sy nmS m0) (FrameKeep.nthUp (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top j) with h | h
    · have := s3 _ h
      omega
    · exact h
  generalize hx : FrameKeep.nthUp (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top j = x at a1 a2 a3 hle
  have hs := R.seen_up hL x (by omega)
  refine ⟨R.base.b₂ sy nmS m0 + (x - 1), by omega, by omega, ?_, ?_, ?_⟩
  · show R.base.seq (R.base.b₂ sy nmS m0 + (x - 1) + 1) = R.base.seq (R.base.b₂ sy nmS m0 + FrameKeep.nthUp (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) R.pole.keep.top j)
    rw [hx, show R.base.b₂ sy nmS m0 + (x - 1) + 1 = R.base.b₂ sy nmS m0 + x by omega]
  · intro hl
    have hu := (hL _ (by omega) (by omega)).1 hl
    rw [show R.base.b₂ sy nmS m0 + (x - 1) + 1 = R.base.b₂ sy nmS m0 + x by omega] at hu
    simp only [FrameKeep.upAt, beq_iff_eq] at a2
    exact hu a2
  · have hs1 := R.seen_up hL (x - 1) (by omega)
    have hs2 := FrameKeep.upTo_succ (FrameKeep.upAt sy m0 R.base.toRealRun (R.base.b₂ sy nmS m0)) (x - 1)
    rw [show x - 1 + 1 = x by omega, a2, a3] at hs2
    simp only [if_true] at hs2
    omega

/-- **The kind of the counted frame `j` of `pole` in `clock`**: a frame of play before the touch (`j < g`), an `auto` frame from the touch to the castle entry. From
`Run.count_up` and the plan of `clock`. With `LagUp`. -/
theorem Run.kind_up (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) (hgc : R.pole.g < R.pole.c) :
    ∀ j, 1 ≤ j → j ≤ R.pole.c → ∃ n, R.base.b₂ sy nmS m0 ≤ n ∧ n ≤ R.E ∧ R.base.seq (n + 1) = R.pole.seq j ∧
      R.clock.kind n = (if j < R.pole.g then .play else .auto) := by
  intro j hj1 hj2
  obtain ⟨n, h1, h2, h3, h4, h5⟩ := R.count_up hL hgc j hj1 hj2
  refine ⟨n, h1, h2, h3, ?_⟩
  have hS := R.segsOk R.room_le hgc
  rcases R.clock.plan n h2 with h | h
  · exact absurd h h4
  · rw [h, h5]
    split
    · exact CastleToLevel.Segs.kind_play₃ hS (by simp only; omega) (by simp only; omega)
    · exact CastleToLevel.Segs.kind_after hS (by simp only; omega)

/-- **Above ground the `lag` frames are the frames that end paused**: the `lag` frames up to the castle entry are those before `b₂`, and the `E + 1 − b₂ − c` frames from
`b₂` to `E` that end paused. With `LagUp`. -/
theorem Run.j_up (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) (hgc : R.pole.g < R.pole.c) :
    R.j = CastleToLevel.count R.clock.kind .lag (R.base.b₂ sy nmS m0) + (R.E + 1 - R.base.b₂ sy nmS m0 - R.pole.c) := by
  obtain ⟨haE, _, _⟩ := R.up_E hL hgc
  have hb : seen R.clock.kind (R.base.b₂ sy nmS m0) = R.Cs + 1 := R.chg.hb₂
  have hE : seen R.clock.kind R.E = R.Cs + R.pole.c := R.clock.seen_E
  have a1 := CastleToLevel.seen_add_lag R.clock.kind R.E
  have a2 := CastleToLevel.seen_add_lag R.clock.kind (R.base.b₂ sy nmS m0)
  have e : R.j = CastleToLevel.count R.clock.kind .lag R.E := rfl
  have hE1 : seen R.clock.kind (R.E + 1) = R.Cs + R.pole.c + 1 := by
    simp only [seen]
    rw [if_neg R.clock.runs_E, hE]
  have a3 := seen_le_add R.clock.kind (show R.base.b₂ sy nmS m0 ≤ R.E + 1 by omega)
  omega

/-- **The castle flag of `pole.atCastle` is that of the machine after the castle entry**: `flag` says the star flag's task is 2 there (`FlagRule.After.task_E`), and with
`LagUp` that machine is `pole.seq c` (`Run.castle_join`). So with `LagUp` the field `pole.atCastle` follows from `flag`. -/
theorem Run.atCastle_of_flag (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) (hgc : R.pole.g < R.pole.c) (hsy : fc.sy = sy) :
    CastleWalk.castle sy (R.pole.seq R.pole.c) = true := by
  rw [← (R.castle_join hL hgc).1]
  have h := R.flag.task_E
  simp only [FlagRule.Ctx.task, hsy] at h
  simp only [CastleWalk.castle, peek, h]
  decide

/-! ## Above ground: the phase of `clock` and the phase of the machine

`PhaseFrame` proves what a frame in control does to the phase (the interval timer's control): it keeps it exactly when it ends paused, and else moves it as the clock's rule
moves it on a frame on which the timers run (`PhaseFrame.PhaseRule`). So, frame by frame, `LagUp` is the same as the phase of `clock` being the machine's at both ends of
the frame (`Run.PhaseAt`, which `read₀` says at frame 0 and `flag` after `E`): `Run.lag_of_phase` and `Run.phase_succ_iff`. The kinds of `clock` above ground are not
tied to the machines, so neither `LagUp` nor `PhaseUp` follows from the fields: `Run.lagUp_of` takes `PhaseUp`. -/

/-- **The phase of `clock` is the machine's** when frame `n` begins, as `read₀` says at frame 0 -/
def Run.PhaseAt (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (n : Nat) : Prop := R.clock.ph n = CastleToLevel.phaseOf tc.nm (R.base.seq n)

/-- **Above ground the phase of `clock` is the machine's** when each frame from `b₂` to `E + 1` begins -/
def Run.PhaseUp (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Prop := ∀ n, R.base.b₂ sy nmS m0 ≤ n → n ≤ R.E + 1 → R.PhaseAt n

/-- the phase of the names of the title is the byte of `PhaseFrame` (the operand of the `DEC` of `DecTimers`): a check on the ROM -/
abbrev PhaseName (sy : Syms) (m0 : Machine) (tc : TitleStart.Ctx) : Prop := ((tc.nm.ad "IntervalTimerControl") &&& 0x7FF).toNat = PhaseFrame.phaseI sy m0

theorem phaseOf_eq (hN : PhaseName sy m0 tc) (m : Machine) : CastleToLevel.phaseOf tc.nm m = (m.ram.get! (PhaseFrame.phaseI sy m0)).toNat := by
  unfold CastleToLevel.phaseOf peek
  rw [hN]

/-- above ground no frame is a `setup` frame: the counts of the `setup` frames are those of the changes, before `Cs` -/
theorem Run.not_setup (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : ∀ n, R.base.b₂ sy nmS m0 ≤ n → n ≤ R.E → R.clock.kind n ≠ .setup := by
  intro n h1 h2 hs
  have hb : seen R.clock.kind (R.base.b₂ sy nmS m0) = R.Cs + 1 := R.chg.hb₂
  have hm := CastleToLevel.seen_mono R.clock.kind h1
  have hz1 := R.hz₁
  have hz2 := R.hz₂
  have hr := R.room_le
  rcases R.clock.plan n h2 with h | h
  · rw [hs] at h
    cases h
  · rw [hs] at h
    simp only [CastleToLevel.Segs.kind] at h
    split at h
    · cases h
    · split at h
      · omega
      · split at h
        · cases h
        · split at h
          · omega
          · split at h <;> cases h

/-- **One frame above ground: `LagUp` from the phase.** If the phase of `clock` is the machine's when frame `n` begins and when it ends, and the frame follows the
machine's rule of the phase, then frame `n` is a `lag` frame exactly when it ends paused. -/
theorem Run.lag_of_phase (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hN : PhaseName sy m0 tc) {n : Nat} (h1 : R.base.b₂ sy nmS m0 ≤ n) (h2 : n ≤ R.E)
    (hp : R.PhaseAt n) (hp' : R.PhaseAt (n + 1)) (hr : PhaseFrame.PhaseRule sy m0 (R.base.seq n) (R.base.seq (n + 1))) :
    R.clock.kind n = .lag ↔ ¬ FrameKeep.Unpaused sy m0 (R.base.seq (n + 1)) := by
  unfold Run.PhaseAt at hp hp'
  rw [phaseOf_eq hN] at hp hp'
  have hs := R.clock.step n h2
  have hns := R.not_setup n h1 h2
  generalize R.clock.kind n = x at hs hns
  cases x with
  | lag =>
    refine ⟨fun _ hu => ?_, fun _ => rfl⟩
    rcases hr with ⟨hpa, _⟩ | ⟨_, he⟩
    · exact hpa hu
    · have h3 := hs.2
      rw [hp, hp', he] at h3
      exact PhaseFrame.next_ne _ h3
  | play =>
    refine ⟨(fun h => by cases h), fun hu => ?_⟩
    rcases hr with ⟨_, he⟩ | ⟨hu', _⟩
    · have h3 := hs.2
      rw [hp, hp', he] at h3
      exact absurd h3.symm (PhaseFrame.next_ne _)
    · exact absurd hu' hu
  | auto =>
    refine ⟨(fun h => by cases h), fun hu => ?_⟩
    rcases hr with ⟨_, he⟩ | ⟨hu', _⟩
    · have h3 := hs.2
      rw [hp, hp', he] at h3
      exact absurd h3.symm (PhaseFrame.next_ne _)
    · exact absurd hu' hu
  | setup => exact absurd rfl hns

/-- **How far the clock's rule carries the phase**: if the phase of `clock` is the machine's when frame `n` begins and the frame follows the machine's rule of the phase,
then it is the machine's when the frame ends exactly when frame `n` is a `lag` frame exactly when it ends paused (`LagUp` at `n`). So from `read₀` at frame 0 the rule
`clock.step` gives the phase of no later frame without a tie of the kinds to the machines. -/
theorem Run.phase_succ_iff (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hN : PhaseName sy m0 tc) {n : Nat} (h1 : R.base.b₂ sy nmS m0 ≤ n) (h2 : n ≤ R.E)
    (hp : R.PhaseAt n) (hr : PhaseFrame.PhaseRule sy m0 (R.base.seq n) (R.base.seq (n + 1))) :
    R.PhaseAt (n + 1) ↔ (R.clock.kind n = .lag ↔ ¬ FrameKeep.Unpaused sy m0 (R.base.seq (n + 1))) := by
  refine ⟨fun hp' => R.lag_of_phase hN h1 h2 hp hp' hr, fun hk => ?_⟩
  have hp0 := hp
  unfold Run.PhaseAt at hp ⊢
  rw [phaseOf_eq hN] at hp ⊢
  have hs := R.clock.step n h2
  have hns := R.not_setup n h1 h2
  generalize hx : R.clock.kind n = x at hs hns hk
  cases x with
  | lag =>
    have hpa := hk.1 rfl
    rcases hr with ⟨_, he⟩ | ⟨hu, _⟩
    · rw [hs.2, hp, he]
    · exact absurd hu hpa
  | play =>
    have hu : FrameKeep.Unpaused sy m0 (R.base.seq (n + 1)) := by
      by_cases h : FrameKeep.Unpaused sy m0 (R.base.seq (n + 1))
      · exact h
      · exact absurd (hk.2 h) (by intro e; cases e)
    rcases hr with ⟨hpa, _⟩ | ⟨_, he⟩
    · exact absurd hu hpa
    · rw [hs.2, hp, he]
      rfl
  | auto =>
    have hu : FrameKeep.Unpaused sy m0 (R.base.seq (n + 1)) := by
      by_cases h : FrameKeep.Unpaused sy m0 (R.base.seq (n + 1))
      · exact h
      · exact absurd (hk.2 h) (by intro e; cases e)
    rcases hr with ⟨hpa, _⟩ | ⟨_, he⟩
    · exact absurd hu hpa
    · rw [hs.2, hp, he]
      rfl
  | setup => exact absurd rfl hns

/-- **`LagUp` from the phase**: the phase of `clock` is the machine's on every frame above ground (`PhaseUp`), and each frame from `b₂` to `E` follows the machine's rule
of the phase -/
theorem Run.lagUp_of_phase (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hN : PhaseName sy m0 tc) (hP : R.PhaseUp)
    (hr : ∀ n, R.base.b₂ sy nmS m0 ≤ n → n ≤ R.E → PhaseFrame.PhaseRule sy m0 (R.base.seq n) (R.base.seq (n + 1))) : R.LagUp :=
  fun n h1 h2 => R.lag_of_phase hN h1 h2 (hP n h1 (by omega)) (hP (n + 1) (by omega) (by omega)) (hr n h1 h2)

/-- **The frames in control above ground follow the machine's rule of the phase**: each frame of `pole.keep` up to the touch's frame (`PhaseFrame.frames_phase`). The
frames begin at control (`pole.seq 0`, frame `b₂`) in the idle loop in control with the watched bits of `FrameKeep` (`Run.atCtl₀` and `PoleJoin.Run.watched₀` give them),
the master timer control 0 and the phase at most 20 there; each instruction meets `PhaseFrame.KeepsPhase` besides `keep.cleanE`. `hc`, `hPc`, `hTc` are checks on the ROM. -/
theorem Run.rule_up (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : FrameKeep.keepCheckOf sy m0 = true) (hPc : PhaseFrame.phaseCheck sy m0 = true) (hTc : PhaseFrame.tcCheck sy m0 = true)
    (hs0 : FrameKeep.StartK sy m0 (R.pole.seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (R.pole.seq 0))
    (htc : (R.base.seq (R.base.b₂ sy nmS m0)).ram.get! (PhaseFrame.tcI sy) = 0)
    (hp : ((R.base.seq (R.base.b₂ sy nmS m0)).ram.get! (PhaseFrame.phaseI sy m0)).toNat ≤ 20)
    (hk : ∀ n, n < R.pole.keep.toFrames.ix R.pole.g → ∀ j,
      PhaseFrame.KeepsPhase sy m0 (PipeEntryRule.trace (R.base.seq (R.base.b₂ sy nmS m0 + n)) (R.base.inp (R.base.b₂ sy nmS m0 + n)) j)) :
    ∀ n, n < R.pole.keep.toFrames.ix R.pole.g →
      PhaseFrame.PhaseRule sy m0 (R.base.seq (R.base.b₂ sy nmS m0 + n)) (R.base.seq (R.base.b₂ sy nmS m0 + n + 1)) :=
  fun n hn => (PhaseFrame.frames_phase hc hPc hTc R.pole.keep.toFrames hs0 h0 htc hp hk n hn).2.2

/-- **`LagUp` from single frames and single states**: the phase of `clock` is the machine's above ground (`PhaseUp`); at control the frame starts in control with the
watched bits and the master timer control 0; each instruction of the frames up to the touch's frame meets `KeepsPhase`; and each frame after the touch's frame up to `E`
follows the machine's rule of the phase (`hA`, not proved: no walk follows those frames). The frames up to the touch's frame follow the rule by `Run.rule_up`. -/
theorem Run.lagUp_of (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hN : PhaseName sy m0 tc) (hB : TitleStart.check sy tc t0 = true) (hc : FrameKeep.keepCheckOf sy m0 = true)
    (hPc : PhaseFrame.phaseCheck sy m0 = true) (hTc : PhaseFrame.tcCheck sy m0 = true)
    (hs0 : FrameKeep.StartK sy m0 (R.pole.seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (R.pole.seq 0))
    (htc : (R.base.seq (R.base.b₂ sy nmS m0)).ram.get! (PhaseFrame.tcI sy) = 0) (hP : R.PhaseUp)
    (hk : ∀ n, n < R.pole.keep.toFrames.ix R.pole.g → ∀ j,
      PhaseFrame.KeepsPhase sy m0 (PipeEntryRule.trace (R.base.seq (R.base.b₂ sy nmS m0 + n)) (R.base.inp (R.base.b₂ sy nmS m0 + n)) j))
    (hA : ∀ n, R.base.b₂ sy nmS m0 + R.pole.keep.toFrames.ix R.pole.g ≤ n → n ≤ R.E →
      PhaseFrame.PhaseRule sy m0 (R.base.seq n) (R.base.seq (n + 1))) : R.LagUp := by
  by_cases hbE : R.base.b₂ sy nmS m0 ≤ R.E
  · have h20 : ((R.base.seq (R.base.b₂ sy nmS m0)).ram.get! (PhaseFrame.phaseI sy m0)).toNat ≤ 20 := by
      have h1 := hP _ (Nat.le_refl _) (by omega)
      unfold Run.PhaseAt at h1
      rw [phaseOf_eq hN] at h1
      have h2 := R.clock.ph_lt (by rw [R.ph_zero hB]; decide) (R.base.b₂ sy nmS m0) (by omega)
      omega
    refine R.lagUp_of_phase hN hP fun n h1 h2 => ?_
    by_cases hn : n < R.base.b₂ sy nmS m0 + R.pole.keep.toFrames.ix R.pole.g
    · have h := R.rule_up hc hPc hTc hs0 h0 htc h20 hk (n - R.base.b₂ sy nmS m0) (by omega)
      rw [show R.base.b₂ sy nmS m0 + (n - R.base.b₂ sy nmS m0) = n by omega] at h
      exact h
    · exact hA n (by omega) h2
  · intro n h1 h2
    omega

/-- **The castle flag of `pole.atCastle` from single frames and single states**: `Run.lagUp_of` and `Run.atCastle_of_flag`. The field `pole.atCastle` would follow from
the hypotheses of `Run.lagUp_of`, of which `PhaseUp` and `hA` are not fields and not proved. -/
theorem Run.atCastle_of_phase (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hN : PhaseName sy m0 tc) (hB : TitleStart.check sy tc t0 = true) (hc : FrameKeep.keepCheckOf sy m0 = true)
    (hPc : PhaseFrame.phaseCheck sy m0 = true) (hTc : PhaseFrame.tcCheck sy m0 = true)
    (hs0 : FrameKeep.StartK sy m0 (R.pole.seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (R.pole.seq 0))
    (htc : (R.base.seq (R.base.b₂ sy nmS m0)).ram.get! (PhaseFrame.tcI sy) = 0) (hP : R.PhaseUp)
    (hk : ∀ n, n < R.pole.keep.toFrames.ix R.pole.g → ∀ j,
      PhaseFrame.KeepsPhase sy m0 (PipeEntryRule.trace (R.base.seq (R.base.b₂ sy nmS m0 + n)) (R.base.inp (R.base.b₂ sy nmS m0 + n)) j))
    (hA : ∀ n, R.base.b₂ sy nmS m0 + R.pole.keep.toFrames.ix R.pole.g ≤ n → n ≤ R.E →
      PhaseFrame.PhaseRule sy m0 (R.base.seq n) (R.base.seq (n + 1)))
    (hgc : R.pole.g < R.pole.c) (hsy : fc.sy = sy) : CastleWalk.castle sy (R.pole.seq R.pole.c) = true :=
  R.atCastle_of_flag (R.lagUp_of hN hB hc hPc hTc hs0 h0 htc hP hk hA) hgc hsy

/-! ## Which frame is the castle entry

`flag` reads the machine after frame `E`, and `flag.task_E` says that the castle flag is up there (`Run.castle_E`). Nothing in `Run` says that it is down before. `FirstCastle`
says so, on the start of each frame from control above ground (`b₂`) to `E`. With it, `E` is the first frame from `b₂` on that ends with the castle flag (`Run.E_first`),
and with `LagUp` the counted frame `c` of `pole` is the first counted frame with the castle flag (`Run.c_first`). Up to the end of the touch's frame it is a theorem
(`Run.noCastle_up`, the walk of `FrameKeep`); the frames after it, up to `E`, are the hypothesis `hA` of `Run.firstCastle_of`. `FirstCastle` is not a field: the
theorems take it. -/

/-- **The castle flag is down when each frame from `b₂` to `E` begins** -/
def Run.FirstCastle (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Prop :=
  ∀ n, R.base.b₂ sy nmS m0 ≤ n → n ≤ R.E → CastleWalk.castle sy (R.base.seq n) = false

/-- **The castle flag is up when frame `E + 1` begins**: `flag.task_E` -/
theorem Run.castle_E (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hsy : fc.sy = sy) : CastleWalk.castle sy (R.base.seq (R.E + 1)) = true := by
  have h := R.flag.task_E
  simp only [FlagRule.Ctx.task, hsy] at h
  simp only [CastleWalk.castle, peek, h]
  decide

/-- **Up to the end of the touch's frame the castle flag is down**, when each frame from `b₂` begins, counted or not: the walk of `FrameKeep` keeps the watched bits
(`FrameKeep.Frames.all_watched`). `hc` is the walk's check on the ROM; `hs0`, `h0` are the machine at control, as in `Run.lagUp_of`. -/
theorem Run.noCastle_up (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : FrameKeep.keepCheckOf sy m0 = true) (hs0 : FrameKeep.StartK sy m0 (R.pole.seq 0))
    (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (R.pole.seq 0)) :
    ∀ n, n ≤ R.pole.keep.toFrames.ix R.pole.g → CastleWalk.castle sy (R.base.seq (R.base.b₂ sy nmS m0 + n)) = false :=
  fun n hn => FrameKeep.castle_of_watched (R.pole.keep.toFrames.all_watched hc hs0 h0 n hn)

/-- **`FirstCastle` from the frames after the touch's frame**: up to the end of the touch's frame it is `Run.noCastle_up`; on the frames after it, up to `E`, the castle
flag is down when the frame begins (`hA`, not proved: no walk follows those frames) -/
theorem Run.firstCastle_of (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hc : FrameKeep.keepCheckOf sy m0 = true) (hs0 : FrameKeep.StartK sy m0 (R.pole.seq 0))
    (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (R.pole.seq 0))
    (hA : ∀ n, R.base.b₂ sy nmS m0 + R.pole.keep.toFrames.ix R.pole.g < n → n ≤ R.E → CastleWalk.castle sy (R.base.seq n) = false) : R.FirstCastle := by
  intro n h1 h2
  by_cases h : n ≤ R.base.b₂ sy nmS m0 + R.pole.keep.toFrames.ix R.pole.g
  · have e := R.noCastle_up hc hs0 h0 (n - R.base.b₂ sy nmS m0) (by omega)
    rwa [show R.base.b₂ sy nmS m0 + (n - R.base.b₂ sy nmS m0) = n by omega] at e
  · exact hA n (by omega) h2

/-- **`E` is the first frame from `b₂` on that ends with the castle flag**, with `FirstCastle` -/
theorem Run.E_first (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : R.FirstCastle) :
    ∀ n, R.base.b₂ sy nmS m0 ≤ n → CastleWalk.castle sy (R.base.seq (n + 1)) = true → R.E ≤ n := by
  intro n h1 h2
  by_cases h : R.E ≤ n
  · exact h
  · have e := hF (n + 1) (by omega) (by omega)
    rw [h2] at e
    cases e

/-- **The counted frame `c` of `pole` is the first counted frame with the castle flag**, with `LagUp` and `FirstCastle`: on each counted frame before it the flag is down.
`pole.atCastle` says it is up at `c`. -/
theorem Run.c_first (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hL : R.LagUp) (hgc : R.pole.g < R.pole.c) (hF : R.FirstCastle) :
    ∀ j, j < R.pole.c → CastleWalk.castle sy (R.pole.seq j) = false := by
  intro j hj
  obtain ⟨haE, _, _⟩ := R.up_E hL hgc
  rcases Nat.eq_zero_or_pos j with h0 | hj1
  · rw [h0, R.atCtl]
    exact hF _ (Nat.le_refl _) haE
  · obtain ⟨n, h1, h2, h3, _, h5⟩ := R.count_up hL hgc j hj1 (by omega)
    have hE : seen R.clock.kind R.E = R.Cs + R.pole.c := R.clock.seen_E
    have hne : n ≠ R.E := fun e => by
      rw [e, hE] at h5
      omega
    rw [← h3]
    exact hF (n + 1) (by omega) (by omega)

/-- **The join.** The bounds of the parts give the bound on the level change. The touch comes as the three cases of `PoleJoin.touch_castle`.
`hT₁`, `hS` and `hT` are the checks of the two changes on the ROM, `hR` those of the room, `hF` that of the star flag, `hB` that of the start from the title, `hK` those of the
frames from control to the vertical pipe's entry. -/
theorem level_ge_of_parts {es es₁ : List Machine} {rt : StepWrites.Rt} (hq : 2 ≤ q) (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hw : 6 ≤ sy.StarFlagDelay.toNat)
    (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) (hsy : fc.sy = sy) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    (h₁ : 368 ≤ R.pipe.E)
    (h₃ : R.room.C + 111 ≤ R.room.E)
    (h₅ : (234 ≤ R.pole.g ∧ R.pole.g + 132 ≤ R.pole.c) ∨ (240 ≤ R.pole.g ∧ R.pole.g ≤ 241 ∧ R.pole.g + 126 ≤ R.pole.c) ∨
      (242 ≤ R.pole.g ∧ R.pole.g + 125 ≤ R.pole.c)) :
    1748 + R.j ≤ R.L := by
  have hc1 := R.change₁ hT₁ hB hK
  have hc2 := R.change₂ hS hT hQ hR hB hK
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
