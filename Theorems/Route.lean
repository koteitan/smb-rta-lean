import Theorems.PipeEntry
import Theorems.PipeEntryRule
import Theorems.PipeWrites
import Theorems.PipeFrames
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

/-!
# The whole route: 1-2 does not start before frame 1748

The parts of the route are joined here into one statement. `Run` lists what a run has to satisfy, one named field per assumption. `level_ge_of_parts` is the
arithmetic of the join: from the bounds of the parts it concludes the level change's frame. The private proof applies the theorems of the parts for the numbers of the game.
No field is proved for every run: this says which assumptions the bound rests on. Page: `1-1/0-1-Route.md`.

Frames are numbered from the first controllable frame of 1-1. The fields of the parts (`pipe.E`, `room.C`, `room.E`, `Cs`, `pole.g`, `pole.c`) count frames without the `lag` frames of
`CastleToLevel.Frames`. `E` and the frames of `clock` count all frames. The three facts about the timers in the whole run are proved here from the rule on single frames: `Run.hE`, `Run.hT`, `Run.hc`.
The counters before frame 0 come from the machine when frame 0 begins (`read₀`), as those after the castle entry come from the machine after it (`flag`). That machine shows `t0`
and the phase 2, and the speed at control is 0: this comes from one condition on the machine after the press of Start on the title (`title`, `TitleStart.Begin`).
The frames after the castle entry are in `flag`, on the real machines of `chg`. From one condition at the castle entry and the check `hF` of the ROM, the rule holds on every
frame up to the level change (`FlagRule.flagOf_after`), and the two facts about them are proved from it: `Run.hD`, `Run.hL`.

The two changes of area are proved here from one sequence of real machines (`Changes`): `Run.change₁` from a condition on the state at the entry and conditions at places of the pipe's frames (`PipeChangeEnd`),
the condition at the entry from the press of Start on the title, the frames from control to the entry and a part of the condition that stays assumed (`Run.entry₁`, `EntryKeep`),
`Run.change₂` from `SideChangeBound` and `SideChangeEnd`. A `lag` frame takes nothing off the number of frames left. In the first change this follows from `paused₁`: a `lag` frame is a paused frame.
In both changes `left` is not 0 before control: this follows from the time at the exit (`time₁`, `time₂`) and the first control (`ctlFirst₁`, `ctlFirst₂`).
-/

namespace Smbrta.Route

open CastleToLevel (ticks wait level_ge Frames Segs Flag Kind seen)
open PipeTransitionAll (Names)

/-- Up to the vertical pipe: the hypotheses of `PipeFrames.no_entry_of_reads`, with the entry on real frames (`PipeWrites.rule_on_frameS`: the walk takes the position at the end of the move,
the frame model's `P₂`), and the frame `E` on which he enters. The frames up to `E`
are read from their own machines (`own`), and the frames not counted between them keep the speed and the position (`lags`, `LagFrames`): `Pipe.reads`. So they follow each other
and keep the top speed: `Pipe.next`, `Pipe.speed`. That he stands still at control is `Run.still`. That every frame from control to the entry, and so the entering frame,
starts in the idle loop in control is a theorem from the machine at control (`Pipe.startE`, `Run.pipeStart₁`). -/
structure Pipe (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) where
  amax : Int
  fr : Nat → TopSpeed.Frame (TopSpeed.top sy : Int) amax
  /-- the machine when counted frame `t` begins, and its input -/
  fm : Nat → Machine
  inp : Nat → UInt8
  /-- its instructions up to the routine's write: stores through an index or a pointer, reads through a pointer, jumps, time -/
  clean : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n, PipeEntryRule.WriteStep sy (fm t) (inp t) n → ∀ j, j ≤ n →
    PipeWrites.Clean (PipeWrites.guardOf sy m0) (PipeEntryRule.trace (fm t) (inp t) j)
  /-- the pipe's right tile is only at its place, when the right foot is read -/
  tiles : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n, PipeEntryRule.WriteStep sy (fm t) (inp t) n → ∀ j, j ≤ n →
    PipeEntryRule.AtRead (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (fm t) (inp t) j) → PipeEntryRule.TilesOK (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (fm t) (inp t) j)
  /-- up to the write, it does not come to the scroll handler's store of the position (at the screen's edges), nor to the routine of the head's collision with a block -/
  edge : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n, PipeEntryRule.WriteStep sy (fm t) (inp t) n → ∀ j, j ≤ n →
    (PipeEntryRule.trace (fm t) (inp t) j).pc ≠ PipeWrites.edgeStore sy m0 ∧ (PipeEntryRule.trace (fm t) (inp t) j).pc ≠ PipeWrites.headAt sy m0
  /-- `P₂` is the position at the end of the move (`PlayerSubs`), up to the write: the frame model's `P₂` -/
  moved : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n j, PipeEntryRule.WriteStep sy (fm t) (inp t) n → j ≤ n →
    (PipeEntryRule.trace (fm t) (inp t) j).pc = sy.PlayerSubs → (fr t).P₂ = posP sy (PipeEntryRule.trace (fm t) (inp t) j)
  /-- the position up to frame `N`, within the bound of the opening -/
  openP : ∀ t, t ≤ N → (fr t).P₂ ≤ posP sy m0 + D
  openB : (fr N).P' ≤ posP sy m0 + D
  /-- the frame he enters the vertical pipe -/
  E : Nat
  /-- it is a frame from control on -/
  one_le : 1 ≤ E
  enter : PipeEntryRule.Enters sy (fm E) (inp E)
  /-- the frames from 1 to `E` are read from the machines: frame `t` begins with the speed, subspeed and position of `fm t`, and before `E` it ends with those of its own end -/
  own : PipeFrames.ReadsOwn sy E fm inp fr
  /-- the frames from control to the entry, counted or not: each instruction is `Clean`, and each counted frame ends in control. If a frame not counted calls the routine
  of the mode, it keeps the speed, the subspeed and the position, and it ends in control (a frame not counted that does not call it does so by the check of `LagFrames`) -/
  lags : PipeFrames.Lags sy m0 E fm inp

/-- the frames from 1 to `E` read from the machines, the end of frame `t` from the machine of the next counted frame: the old field `reads`, from the frames not counted.
`hc` and `hk` are checks on the ROM, `hs` the start of the machine at control (`Run.pipeStart₁`). -/
theorem Pipe.reads {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (p : Pipe sy m0 N D)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) : PipeFrames.Reads sy p.E p.fm p.fr :=
  PipeFrames.reads_of_lags hc hk p.own p.lags hs

/-- **The entering frame starts in the idle loop, in control**: the old field `start`, by induction from the machine at control over every frame up to the entry
(`PipeFrames.Lags.starts`). `hc` and `hk` are checks on the ROM, `hs` the start of the machine at control (`Run.pipeStart₁`). -/
theorem Pipe.startE {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (p : Pipe sy m0 N D)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) :
    PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm p.E) :=
  p.lags.startE hc hk p.one_le hs

/-- the frames up to the entry follow each other: the old field `next`, from the frames read from the machines -/
theorem Pipe.next {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (p : Pipe sy m0 N D)
    (hs : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) :
    ∀ t, 1 ≤ t → t < p.E → PoleGrab.Next (p.fr t) (p.fr (t + 1)) :=
  PipeFrames.next_of_reads (p.reads hc hk hs)

/-- the speed at the end of frame `N` is at most the top speed, when `1 ≤ N ≤ E` and he stands still at control (`Run.still`): the old field `speed` -/
theorem Pipe.speed {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (p : Pipe sy m0 N D)
    (hs₀ : PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (p.fm 1)) (hs : SurfaceFrames.vOf sy (p.fm 1) = 0)
    (h16 : 16 ≤ (TopSpeed.top sy : Int)) (h1 : 1 ≤ N) (h2 : N ≤ p.E) :
    -(TopSpeed.top sy : Int) ≤ (p.fr N).v' ∧ (p.fr N).v' ≤ (TopSpeed.top sy : Int) :=
  PipeFrames.speed_end h16 (p.reads hc hk hs₀) hs N h1 h2

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

/-- The two changes of area on the real machines of a run. There is one sequence of machines, for both changes, numbered as `kind` numbers the frames. `e₁`, `c₂`, `e₂`, `c₃` count frames without
the `lag` frames, as `Segs` does. -/
structure Changes (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (kind : Nat → Kind) (e₁ c₂ e₂ c₃ : Nat) where
  /-- the machine when frame `n` begins, so `seq (n + 1)` is what frame `n` leaves -/
  seq : Nat → Machine
  /-- the input of frame `n` -/
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = PipeTransition.frame (seq n) (inp n)
  /-- the first change: the machine after frame `e₁`, the first from the first control on that has no control (`Changes.a₁`), and the machine after frame `c₂`, the first with
  control from there on (`b₁`). `dA` and `dB` are bounds on the frames to them. -/
  dA : Nat
  dB : Nat
  b₁ : Nat
  /-- `b₁` is the first frame from the entry on, within `dB` frames, whose machine has control -/
  firstB₁ : b₁ = firstCtl sy seq (upEnd sy seq dA) dB
  ha₁ : seen kind (upEnd sy seq dA) = e₁ + 1
  hb₁ : seen kind b₁ = c₂ + 1
  /-- the part of the condition on the machine at the entry that the press of Start and the frames from control do not give: the bytes of `EntryKeep.restNames`
  (`Run.entry₁` gives the whole condition) -/
  entryRest₁ : EntryKeep.Rest d₁ (PipeTransition.entry m0) (seq (upEnd sy seq dA))
  /-- each instruction of the frames from control to the entry is `Clean`, with the bytes that the frames keep, the buttons left and right and the pipe's timer
  (`EntryKeep.held`, `EntryKeep.timerI`) among the bytes that a store through an index or a pointer does not touch (that each of these frames starts in the idle loop in control
  is `Run.upStart₁`) -/
  upClean₁ : ∀ n, 1 ≤ n → n < upEnd sy seq dA → ∀ j, PipeWrites.Clean (EntryKeep.guardOf sy m0 d₁ (PipeTransition.entry m0)) (PipeEntryRule.trace (seq n) (inp n) j)
  /-- control within `dB` frames of the entry -/
  ctlBy₁ : controllable sy (seq (upEnd sy seq dA + dB)) = true
  /-- a `lag` frame is a paused frame: the low bit of the pause byte is set when it ends -/
  paused₁ : ∀ n, upEnd sy seq dA ≤ n → n < b₁ → kind n = .lag → PipeChangeEnd.Paused d₁ (seq (n + 1))
  /-- on a frame of the pipe's routine, each instruction meets the condition at the places -/
  places₁ : ∀ n, upEnd sy seq dA ≤ n → n < b₁ → PipeChangeBound.inPipe sy sy.EngVerticalPipe (seq n) = true → ∀ j, PipeChangeEnd.PlaceOK d₁.places (PipeEntryRule.trace (seq n) (inp n) j)
  /-- at the exit, the sound's bytes, the song and the screen buffer are as the condition says -/
  quiet₁ : ∀ n, upEnd sy seq dA ≤ n → n ≤ b₁ → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (seq n) →
    SideChangeEnd.Quiet (PipeChangeEnd.quietQ d₁ (PipeTransition.entry m0)) (seq n) ∧ PipeChangeEnd.SongAt d₁.song (seq n) ∧ PipeChangeEnd.SongAt d₁.xshape (seq n)
  /-- no Start on the frames of the game core after the pipe -/
  noStart₁ : ∀ n, upEnd sy seq dA ≤ n → n < b₁ → SideChangeEnd.coreFrame sy sy.EngVerticalPipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- at the exit, the sound's pause flag is 0 and the game timer is not 000: the time is not up on the way -/
  time₁ : ∀ n, upEnd sy seq dA ≤ n → n ≤ b₁ → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (seq n) → SideChangeEnd.TimeOK d₁.nx (seq n)
  /-- the second change: the machine after frame `e₂`, the first from `b₁` on that has left the player's routine (`Changes.a₂`), and the machine after frame `c₃`, the first with control from
  there on (`Changes.b₂`). `dR` and `d₂` are bounds on the frames to them. -/
  dR : Nat
  d₂ : Nat
  ha₂ : seen kind (roomEnd sy nmS m0 seq b₁ dR) = e₂ + 1
  hb₂ : seen kind (firstCtl sy seq (roomEnd sy nmS m0 seq b₁ dR) d₂) = c₃ + 1
  /-- at the entry, the bytes of the condition that the room does not give have the values of a reference machine: the routine (so the routine that the room left for is the side pipe's),
  the player's vertical position, the screen's buffer, the sound, the level's number (16 bytes). The room gives the rest (`ScreenPage.entry_rest`). -/
  entry₂ : ScreenPage.EntryRest nmS (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) (seq (roomEnd sy nmS m0 seq b₁ dR))
  /-- the room, from control to the side pipe: each instruction (the rows of the first change give `ScreenPage.Room` at control) -/
  roomSites : ∀ n, b₁ ≤ n → n < (roomEnd sy nmS m0 seq b₁ dR) → ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nmS m0) (PipeEntryRule.trace (seq n) (inp n) j)
  /-- control within `d₂` frames of the entry -/
  ctlBy₂ : controllable sy (seq ((roomEnd sy nmS m0 seq b₁ dR) + d₂)) = true
  /-- a `lag` frame ends paused -/
  paused₂ : ∀ n, (roomEnd sy nmS m0 seq b₁ dR) ≤ n → n < firstCtl sy seq (roomEnd sy nmS m0 seq b₁ dR) d₂ → kind n = .lag → SideChangeEnd.Paused nx₂ (seq (n + 1))
  /-- no Start on the frames of the game core after the pipe -/
  noStart₂ : ∀ n, (roomEnd sy nmS m0 seq b₁ dR) ≤ n → n < firstCtl sy seq (roomEnd sy nmS m0 seq b₁ dR) d₂ → SideChangeEnd.coreFrame sy sy.EngSidePipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- at the exit, the sound's pause flag is 0 and the game timer is not 000: the time is not up on the way -/
  time₂ : ∀ n, (roomEnd sy nmS m0 seq b₁ dR) ≤ n → n ≤ firstCtl sy seq (roomEnd sy nmS m0 seq b₁ dR) d₂ → SideChangeBound.ExitAt (SideChangeBound.exitBytes sy nm₂ (SideChangeEnd.refExit (SideTransition.entry m0) 160)) (seq n) →
    SideChangeEnd.TimeOK nx₂ (seq n)
  /-- at the exit, the sound's pause bytes have the reference's values -/
  quiet₂ : ∀ n, (roomEnd sy nmS m0 seq b₁ dR) ≤ n → n ≤ firstCtl sy seq (roomEnd sy nmS m0 seq b₁ dR) d₂ → SideChangeBound.ExitAt (SideChangeBound.exitBytes sy nm₂ (SideChangeEnd.refExit (SideTransition.entry m0) 160)) (seq n) →
    SideChangeEnd.Quiet (SideChangeEnd.quietBytes nx₂ (SideTransition.entry m0) 160) (seq n)

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat}

/-- **The entry into the vertical pipe**: the first machine from the first control on that has no control -/
def Changes.a₁ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : Nat := upEnd sy C.seq C.dA

/-- each frame from the first control to the entry begins with control: it holds by the choice of `a₁` -/
theorem Changes.upStay (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : ∀ n, 1 ≤ n → n < C.a₁ → controllable sy (C.seq n) = true := fun n h1 h2 => by
  have h := firstWith_first _ 1 C.dA n h1 h2
  simpa using h

/-- the end of the first change is not before its entry: no longer a field, it holds by the choice of `b₁` -/
theorem Changes.order₁ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : C.a₁ ≤ C.b₁ := by
  rw [C.firstB₁]
  exact firstWith_ge _ _ C.dB

/-- control at the end of the first change: no longer a field, it holds by the choice of `b₁` -/
theorem Changes.ctl₁ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : controllable sy (C.seq C.b₁) = true := by
  rw [C.firstB₁]
  exact firstWith_at (fun n => controllable sy (C.seq n)) _ C.dB C.ctlBy₁

/-- `b₁` is the first control after the entry: no longer a field, it holds by the choice of `b₁` -/
theorem Changes.ctlFirst₁ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : ∀ n, C.a₁ ≤ n → n < C.b₁ → controllable sy (C.seq n) = false :=
  fun n h1 h2 => firstWith_first (fun n => controllable sy (C.seq n)) _ C.dB n h1 (by rw [C.firstB₁] at h2; exact h2)

/-- **The entry into the side pipe**: the first machine from the room's first control on that has left the player's routine -/
def Changes.a₂ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : Nat := roomEnd sy nmS m0 C.seq C.b₁ C.dR

/-- **The end of the second change**: the first machine with control from the entry on -/
def Changes.b₂ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : Nat := firstCtl sy C.seq C.a₂ C.d₂

theorem Changes.roomOrder (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : C.b₁ ≤ C.a₂ := firstWith_ge _ C.b₁ C.dR

/-- each frame from the room's first control to the entry starts in the player's routine: no longer a field, it holds by the choice of `a₂` -/
theorem Changes.roomStay (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : ∀ n, C.b₁ ≤ n → n < C.a₂ →
    (C.seq n).ram.get! (ScreenPage.placesR sy nmS m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nmS m0).rtI := fun n h1 h2 => by
  have h := firstWith_first _ C.b₁ C.dR n h1 h2
  simpa using h

theorem Changes.order₂ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : C.a₂ ≤ C.b₂ := firstWith_ge _ C.a₂ C.d₂

/-- control at the end -/
theorem Changes.ctl₂ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : controllable sy (C.seq C.b₂) = true :=
  firstWith_at (fun n => controllable sy (C.seq n)) C.a₂ C.d₂ C.ctlBy₂

/-- `b₂` is the first control after the entry: no longer a field, it holds by the choice of `b₂` -/
theorem Changes.ctlFirst₂ (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : ∀ n, C.a₂ ≤ n → n < C.b₂ → controllable sy (C.seq n) = false :=
  fun n h1 h2 => firstWith_first (fun n => controllable sy (C.seq n)) C.a₂ C.d₂ n h1 h2

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

/-- the entry is after control: `a₁` is not 0 -/
theorem Changes.one_le {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) :
    1 ≤ C.a₁ := firstWith_ge _ 1 C.dA

/-- the first change as `PipeChangeEnd.PipeRun`, with the condition at the entry (`Run.entry₁`) -/
def Changes.run₁ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃)
    (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (C.seq C.a₁)) : PipeChangeEnd.PipeRun sy nm₁ d₁ (PipeTransition.entry m0) where
  seq := C.seq
  inp := C.inp
  next := C.next
  lag := fun n => kind n = .lag
  dec := fun _ => inferInstance
  cnt := seen kind
  hcnt := fun _ => rfl
  a := C.a₁
  b := C.b₁
  order := C.order₁
  entry := he
  atCtl := C.ctl₁
  lagPaused := C.paused₁
  places := C.places₁
  quiet := C.quiet₁
  noStart := C.noStart₁

/-- **The change into the room takes at least 91 frames**, from the condition at the entry and the conditions at the places. `hT` is what the check on the ROM gives. -/
theorem Changes.bound₁ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {es : List Machine}
    (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (C.seq C.a₁)) : e₁ + 91 ≤ c₂ := by
  have h := (C.run₁ he).bound hT
  have h1 : (C.run₁ he).cnt (C.run₁ he).a = e₁ + 1 := C.ha₁
  have h2 : (C.run₁ he).cnt (C.run₁ he).b = c₂ + 1 := C.hb₁
  have h3 : PipeChangeEnd.timerF + PipeChangeEnd.afterF = 91 := rfl
  rw [h1, h2, h3] at h
  omega

/-- **`left` is not 0 before control** in the change into the room: from the time at the exit and the first control (`PipeChangeEnd.PipeRun.first`) -/
theorem Changes.first₁ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {es : List Machine}
    (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (C.seq C.a₁)) :
    ∀ n, C.a₁ ≤ n → n < C.b₁ → left₁ sy nm₁ m0 (C.seq n) ≠ 0 :=
  (C.run₁ he).first hT C.time₁ C.ctlFirst₁

/-- the checks on the ROM that the room needs: what one frame in the room does, two facts about the names, and the condition at the room's first control from the rows of the first change -/
structure RoomChecks (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) : Prop where
  facts : ScreenPage.RoomFacts sy nmS m0 160 (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0))
  timer : (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)).rkI = (ScreenPage.placesR sy nmS m0).timerI
  rt : ScreenPage.entryEnvOK sy nmS m0 (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) = true
  pipe : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) [PipeTransition.entry m0]
  start : ScreenStart.roomCheck sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true

/-- **The condition at the first control in the room**, from the rows of the time of the first change: the time at the exit and the first control -/
theorem Changes.roomAt {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (C.seq C.a₁)) : ScreenPage.Room sy nmS m0 (C.seq C.b₁) :=
  ScreenStart.room_of_rows hR.start ((C.run₁ he).inRowsT hR.pipe C.time₁ C.ctlFirst₁) C.ctl₁

/-- the second change as `SideChangeEnd.EndRun` -/
def Changes.run₂ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃)
    (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (C.seq C.a₁)) : SideChangeEnd.EndRun sy nm₂ nx₂ (SideTransition.entry m0) 160 122 where
  seq := C.seq
  inp := C.inp
  next := C.next
  lag := fun n => kind n = .lag
  dec := fun _ => inferInstance
  cnt := seen kind
  hcnt := fun _ => rfl
  a := C.a₂
  b := C.b₂
  order := C.order₂
  entry := ScreenPage.entry_rest hR.facts hR.timer hR.rt C.next C.roomOrder (C.roomAt hR he) C.roomSites C.roomStay C.entry₂
  atCtl := C.ctl₂
  lagPaused := C.paused₂
  noStart := C.noStart₂
  quiet := C.quiet₂

/-- **The change out of the side pipe takes at least 282 frames**, from the single frames. `hS` and `hT` are what the checks on the ROM give. -/
theorem Changes.bound₂ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {es : List Machine}
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (C.seq C.a₁)) : e₂ + 282 ≤ c₃ := by
  have h := (C.run₂ hR he).bound hS hT
  have h1 : (C.run₂ hR he).cnt (C.run₂ hR he).a = e₂ + 1 := C.ha₂
  have h2 : (C.run₂ hR he).cnt (C.run₂ hR he).b = c₃ + 1 := C.hb₂
  rw [h1, h2] at h
  omega

/-- A run through 1-1, and every assumption of the bound. The parts are `pipe` (part a), `room` (part c), `pole` (parts e, f), `chg` (parts b, d); the fields below them join these, the frames of
the run with their timers (`clock`), the start from the title (`title`) and the level change (from the castle to 1-2). -/
structure Run (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) (rN : RoomJoin.Nums)
    (b : Machine) (vs : List Jump.VS) (PA : PoleJoin.Box) (Ts J Nc : Nat) (F : Int) (q t0 : Nat) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (fc : FlagRule.Ctx)
    (tc : TitleStart.Ctx) where
  pipe : Pipe sy m0 N D
  room : RoomJoin.RoomRun sy m0 rN
  /-- `pole` counts its frames from control above ground -/
  pole : PoleJoin.Run sy m0 b vs PA Ts J Nc F
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
  /-- the two changes of area, on the real machines of the frames of `clock` -/
  chg : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS clock.kind pipe.E room.C room.E Cs
  /-- from the press of Start on the title to frame 0: one condition on the machine after the press, no Start on frame 0 in the game core (Start before it may pause the
  game), and frame 0 is the frame before the first control -/
  title : TitleStart.Begin sy tc chg.seq chg.inp
  /-- the counters of `clock` before frame 0 are those of the machine when frame 0 begins, as `flag` says of the machine after the castle entry (`t_E`, `ph_E`) -/
  read₀ : (clock.s 0).t = CastleToLevel.timerOf tc.nm (chg.seq 0) ∧ clock.ph 0 = CastleToLevel.phaseOf tc.nm (chg.seq 0)
  /-- the machine of `pipe` at control is `chg`'s machine when frame 1 begins -/
  pipeAt : pipe.fm 1 = chg.seq 1
  /-- the frames of `pole` begin at the machine at the end of the second change -/
  atCtl : pole.seq 0 = chg.seq chg.b₂
  /-- the machine of `room` at first control is the machine at the end of the first change -/
  roomCtl : room.fm room.C = chg.seq chg.b₁
  /-- the frame of `room` that enters the side pipe is a frame of `chg` in the room, from its first control to the entry -/
  roomEnter : ∃ k, chg.b₁ ≤ k ∧ k < chg.a₂ ∧ room.fm (room.E - 1) = chg.seq k ∧ room.pad room.E = chg.inp k
  /-- the level change -/
  L : Nat
  /-- the frames after the castle entry, up to the level change, on the real machines of `chg`: one condition at the castle entry, no Start, and the level change
  after frame `L` -/
  flag : FlagRule.After fc chg.seq chg.inp E clock.T clock.c L

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {fc : FlagRule.Ctx}
  {tc : TitleStart.Ctx}

/-- the frames on which no timer runs, other than one in each change -/
def Run.j (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Nat := R.clock.j

/-- the game timer at the castle entry -/
def Run.T (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Nat := R.clock.T

/-- the interval timer's phase at the castle entry -/
def Run.c (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : Nat := R.clock.c

/-- **Each frame from control to the vertical pipe's entry starts in the idle loop in control**: by induction from the press of Start on the title (`title`), under `upClean₁`.
Each of these frames begins with control, by the choice of `a₁`. `hB` and `hK` are the checks on the ROM. The old field `upStart₁`. -/
theorem Run.upStart₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, 1 ≤ n → n < R.chg.a₁ → PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (R.chg.seq n) :=
  EntryKeep.starts_of_title hB hK R.title R.chg.next R.chg.upStay R.chg.upClean₁

/-- **The condition at the vertical pipe's entry**, from the press of Start on the title (`title`), the frames from control to the entry (`Run.upStart₁`, `upClean₁`) and the part
that stays assumed (`entryRest₁`). `hB` and `hK` are the checks on the ROM. The old field `entry₁`. -/
theorem Run.entry₁ (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (R.chg.seq R.chg.a₁) :=
  EntryKeep.entry_of_title hB hK R.title R.chg.next R.chg.one_le (R.upStart₁ hB hK) R.chg.upClean₁ R.chg.entryRest₁

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
  FlagRule.flagOf_after hF R.chg.next R.flag

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
    CastleToLevel.timerOf tc.nm (R.chg.seq 0) = t0 ∧ CastleToLevel.phaseOf tc.nm (R.chg.seq 0) = 2 :=
  R.title.timer hB (R.chg.next 0)

/-- **He stands still at control**, when frame 1 begins: from the press of Start on the title. The old field `pipe.still`. -/
theorem Run.still (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) :
    SurfaceFrames.vOf sy (R.pipe.fm 1) = 0 := by
  rw [R.pipeAt]
  exact R.title.still hB (R.chg.next 0)

/-- **The machine at control of `pipe` starts a frame in the idle loop, in control**: from the press of Start on the title. `hB` and `hT` are checks on the ROM. -/
theorem Run.pipeStart₁ (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true)
    (hT : StartRun.titleCheck sy tc (PipeWrites.guardOf sy m0) m0 = true) :
    PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (R.pipe.fm 1) := by
  rw [R.pipeAt]
  exact StartRun.Begin.start₁G hB hT R.title (R.chg.next 0)

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

/-- the room's first control comes before the entry into the side pipe: `room.C ≤ room.E`, from the frames of `chg` -/
theorem Run.room_le (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.C ≤ R.room.E := by
  have h1 : seen R.clock.kind R.chg.b₁ = R.room.C + 1 := R.chg.hb₁
  have h2 : seen R.clock.kind R.chg.a₂ = R.room.E + 1 := R.chg.ha₂
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
  exact SurfaceFrames.EndRun.start hS hT hc (R.chg.run₂ hR (R.entry₁ hB hK)) ((R.chg.run₂ hR (R.entry₁ hB hK)).first hT R.chg.time₂ R.chg.ctlFirst₂)

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
  exact ControlStart.EndRun.atCtl hS hT hc hk (R.chg.run₂ hR (R.entry₁ hB hK)) ((R.chg.run₂ hR (R.entry₁ hB hK)).first hT R.chg.time₂ R.chg.ctlFirst₂)

/-- **The state at first control in the room**, on the real machines: it comes from the last row of the change into the room, under the change's conditions and `Changes.first₁`. `hc` is the check on
the ROM. -/
theorem Run.roomStart {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hc : RoomStart.startCheck sy nm₁ d₁ (PipeTransition.entry m0) (RoomJoin.room sy rN) rN.startY rN.startW rN.fallF = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    RoomJoin.StartAt sy rN (R.room.fm R.room.C) := by
  rw [R.roomCtl]
  exact RoomStart.PipeRun.start hT₁ hc (R.chg.run₁ (R.entry₁ hB hK)) (R.chg.first₁ hT₁ (R.entry₁ hB hK))

/-- **The side pipe's tiles at the reads of the room's entering frame**, on the real machines: `RoomMap.map_of_rows` on the frames of `chg` in the room, from the rows of the change into
the room, and `roomEnter`. `hT₁`, `hM`, `hS` are checks on the ROM. The old field `room.tiles`. -/
theorem Run.roomTiles {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.TilesE := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter
  have he := R.entry₁ hB hK
  have h := (RoomMap.map_of_rows (a := R.chg.a₂) hM hS R.chg.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay).2 k h1 h2
  intro n j _ _ ha
  rw [e1, e2] at ha ⊢
  exact h j ha

/-- **The room's entering frame starts in control**, on the real machines: `RoomMap.start_of_rowsF` on the frames of `chg` in the room, from the rows of the change into the room,
and `roomEnter`. `hT₁`, `hM`, `hS`, `hF` are checks on the ROM. The old field `room.startE`. -/
theorem Run.roomStartE {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hF : RoomMap.startCheckF sy nmS m0 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.StartE := by
  obtain ⟨k, h1, h2, e1, _⟩ := R.roomEnter
  have he := R.entry₁ hB hK
  have h := RoomMap.start_of_rowsF (a := R.chg.a₂) hM hS hF R.chg.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay k h1 h2
  show PipeWrites.FrameStart (SideFrame.roomG sy m0) (PipeEntryRule.envOf m0) (R.room.fm (R.room.E - 1))
  rw [e1]
  exact h

/-- **`Clean` on each instruction of the room's entering frame up to the write**, on the real machines: `RoomMap.clean_of_rows` on the frames of `chg` in the room, and
`roomEnter`. The old field `room.cleanE`. -/
theorem Run.roomCleanE {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.CleanE := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter
  have he := R.entry₁ hB hK
  have h := RoomMap.clean_of_rows (a := R.chg.a₂) hM hS R.chg.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay k h1 h2
  intro n _ j _
  show PipeWrites.Clean (SideFrame.roomG sy m0) (PipeEntryRule.trace (R.room.fm (R.room.E - 1)) (R.room.pad R.room.E) j)
  rw [e1, e2]
  exact h j

/-- **The room's entering frame does not come to the routine of the head's collision with a block**, on the real machines: `RoomMap.head_of_rows` on the frames of `chg` in the
room, and `roomEnter`. Once part of the field `room.edgeE`. -/
theorem Run.roomHeadE {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.HeadE := by
  obtain ⟨k, h1, h2, e1, e2⟩ := R.roomEnter
  have he := R.entry₁ hB hK
  have h := RoomMap.head_of_rows (a := R.chg.a₂) hM hS R.chg.next ((R.chg.run₁ he).inRowsT hT₁ R.chg.time₁ R.chg.ctlFirst₁) R.chg.ctl₁
    R.chg.roomSites R.chg.roomStay k h1 h2
  intro j
  show (PipeEntryRule.trace (R.room.fm (R.room.E - 1)) (R.room.pad R.room.E) j).pc ≠ PipeWrites.headAt sy m0
  rw [e1, e2]
  exact h j

/-- **What the room's frames give about its entering frame**: the tiles, the start in control, `Clean`, no head's collision -/
theorem Run.inRoom {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true) (hF : RoomMap.startCheckF sy nmS m0 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    R.room.InRoom :=
  ⟨R.roomTiles hT₁ hM hS hB hK, R.roomStartE hT₁ hM hS hF hB hK, R.roomCleanE hT₁ hM hS hB hK, R.roomHeadE hT₁ hM hS hB hK⟩

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
