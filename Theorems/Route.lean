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
`Run.change₂` from `SideChangeBound` and `SideChangeEnd`. A `lag` frame takes nothing off the number of frames left. In the first change this follows from `paused₁`: a `lag` frame is a paused frame.
In both changes `left` is not 0 before control: this follows from the time at the exit (`time₁`, `time₂`) and the first control (`ctlFirst₁`, `ctlFirst₂`).
-/

namespace Smbrta.Route

open CastleToLevel (ticks wait level_ge Frames Segs Flag Kind seen)
open PipeTransitionAll (Names)

/-- Up to the vertical pipe: the hypotheses of `PipeFrames.no_entry_of_reads`, with the entry on real frames (`PipeWrites`), and the frame `E` on which he enters. The frames up to `E`
are read from their own machines (`own`), and the frames not counted between them keep the speed and the position (`lags`, `LagFrames`): `Pipe.reads`. So they follow each other
and keep the top speed: `Pipe.next`, `Pipe.speed`. That he stands still at control is `Run.still`. -/
structure Pipe (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) where
  amax : Int
  fr : Nat → TopSpeed.Frame (TopSpeed.top sy : Int) amax
  /-- the machine when counted frame `t` begins, and its input -/
  fm : Nat → Machine
  inp : Nat → UInt8
  /-- a frame that enters starts in the idle loop, in control -/
  start : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → PipeWrites.FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (fm t)
  /-- its instructions up to the routine's write: stores through an index or a pointer, reads through a pointer, jumps, time -/
  clean : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n, PipeEntryRule.WriteStep sy (fm t) (inp t) n → ∀ j, j ≤ n →
    PipeWrites.Clean (PipeWrites.guardOf sy m0) (PipeEntryRule.trace (fm t) (inp t) j)
  /-- the pipe's right tile is only at its place, when the right foot is read -/
  tiles : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n, PipeEntryRule.WriteStep sy (fm t) (inp t) n → ∀ j, j ≤ n →
    PipeEntryRule.AtRead (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (fm t) (inp t) j) → PipeEntryRule.TilesOK (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (fm t) (inp t) j)
  /-- `P₂` is the position when the block buffer routine is entered for the right foot, up to the write -/
  pos : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n j, PipeEntryRule.WriteStep sy (fm t) (inp t) n → j ≤ n →
    PipeEntryRule.AtEntry (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (fm t) (inp t) j) →
    ∃ f : Int, 0 ≤ f ∧ (fr t).P₂ = 256 * (PipeEntryRule.px (PipeWrites.guardOf sy m0).P (PipeEntryRule.trace (fm t) (inp t) j) : Int) + f
  /-- the position up to frame `N`, within the bound of the opening -/
  openP : ∀ t, t ≤ N → (fr t).P₂ ≤ posP sy m0 + D
  openB : (fr N).P' ≤ posP sy m0 + D
  /-- the frame he enters the vertical pipe -/
  E : Nat
  enter : PipeEntryRule.Enters sy (fm E) (inp E)
  /-- the frames from 1 to `E` are read from the machines: frame `t` begins with the speed, subspeed and position of `fm t`, and before `E` it ends with those of its own end -/
  own : PipeFrames.ReadsOwn sy E fm inp fr
  /-- the frames not counted between them: each starts in the idle loop and its instructions are `Clean`; if it calls the routine of the mode, it keeps the three values -/
  lags : PipeFrames.Lags sy m0 E fm inp

/-- the frames from 1 to `E` read from the machines, the end of frame `t` from the machine of the next counted frame: the old field `reads`, from the frames not counted.
`hc` is the check on the ROM. -/
theorem Pipe.reads {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} (hc : LagFrames.lagCheck sy m0 = true) (p : Pipe sy m0 N D) : PipeFrames.Reads sy p.E p.fm p.fr :=
  PipeFrames.reads_of_lags hc p.own p.lags

/-- the frames up to the entry follow each other: the old field `next`, from the frames read from the machines -/
theorem Pipe.next {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} (hc : LagFrames.lagCheck sy m0 = true) (p : Pipe sy m0 N D) :
    ∀ t, 1 ≤ t → t < p.E → PoleGrab.Next (p.fr t) (p.fr (t + 1)) :=
  PipeFrames.next_of_reads (p.reads hc)

/-- the speed at the end of frame `N` is at most the top speed, when `1 ≤ N ≤ E` and he stands still at control (`Run.still`): the old field `speed` -/
theorem Pipe.speed {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} (hc : LagFrames.lagCheck sy m0 = true) (p : Pipe sy m0 N D) (hs : SurfaceFrames.vOf sy (p.fm 1) = 0)
    (h16 : 16 ≤ (TopSpeed.top sy : Int)) (h1 : 1 ≤ N) (h2 : N ≤ p.E) :
    -(TopSpeed.top sy : Int) ≤ (p.fr N).v' ∧ (p.fr N).v' ≤ (TopSpeed.top sy : Int) :=
  PipeFrames.speed_end h16 (p.reads hc) hs N h1 h2

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

/-- The two changes of area on the real machines of a run. There is one sequence of machines, for both changes, numbered as `kind` numbers the frames. `e₁`, `c₂`, `e₂`, `c₃` count frames without
the `lag` frames, as `Segs` does. -/
structure Changes (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (kind : Nat → Kind) (e₁ c₂ e₂ c₃ : Nat) where
  /-- the machine when frame `n` begins, so `seq (n + 1)` is what frame `n` leaves -/
  seq : Nat → Machine
  /-- the input of frame `n` -/
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = PipeTransition.frame (seq n) (inp n)
  /-- the first change: the machine after frame `e₁`, and the machine after frame `c₂` -/
  a₁ : Nat
  b₁ : Nat
  order₁ : a₁ ≤ b₁
  ha₁ : seen kind a₁ = e₁ + 1
  hb₁ : seen kind b₁ = c₂ + 1
  /-- the condition on the machine at the entry -/
  entry₁ : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (seq a₁)
  /-- control at the end -/
  ctl₁ : controllable sy (seq b₁) = true
  /-- a `lag` frame is a paused frame: the low bit of the pause byte is set when it ends -/
  paused₁ : ∀ n, a₁ ≤ n → n < b₁ → kind n = .lag → PipeChangeEnd.Paused d₁ (seq (n + 1))
  /-- on a frame of the pipe's routine, each instruction meets the condition at the places -/
  places₁ : ∀ n, a₁ ≤ n → n < b₁ → PipeChangeBound.inPipe sy sy.EngVerticalPipe (seq n) = true → ∀ j, PipeChangeEnd.PlaceOK d₁.places (PipeEntryRule.trace (seq n) (inp n) j)
  /-- at the exit, the sound's bytes, the song and the screen buffer are as the condition says -/
  quiet₁ : ∀ n, a₁ ≤ n → n ≤ b₁ → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (seq n) →
    SideChangeEnd.Quiet (PipeChangeEnd.quietQ d₁ (PipeTransition.entry m0)) (seq n) ∧ PipeChangeEnd.SongAt d₁.song (seq n) ∧ PipeChangeEnd.SongAt d₁.xshape (seq n)
  /-- no Start on the frames of the game core after the pipe -/
  noStart₁ : ∀ n, a₁ ≤ n → n < b₁ → SideChangeEnd.coreFrame sy sy.EngVerticalPipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- `b₁` is the first control after the entry -/
  ctlFirst₁ : ∀ n, a₁ ≤ n → n < b₁ → controllable sy (seq n) = false
  /-- at the exit, the sound's pause flag is 0 and the game timer is not 000: the time is not up on the way -/
  time₁ : ∀ n, a₁ ≤ n → n ≤ b₁ → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (seq n) → SideChangeEnd.TimeOK d₁.nx (seq n)
  /-- the second change: the machine after frame `e₂`, the first from `b₁` on that has left the player's routine (`Changes.a₂`), and the machine after frame `c₃`, the first with control from
  there on (`Changes.b₂`). `dR` and `d₂` are bounds on the frames to them. -/
  dR : Nat
  d₂ : Nat
  ha₂ : seen kind (roomEnd sy nmS m0 seq b₁ dR) = e₂ + 1
  hb₂ : seen kind (firstCtl sy seq (roomEnd sy nmS m0 seq b₁ dR) d₂) = c₃ + 1
  /-- at the entry, the bytes of the condition that the room does not give have the values of a reference machine: the routine (so the routine that the room left for is the side pipe's),
  the player's state and height, the screen's buffer, the sound, the next area. The room gives the rest (`ScreenPage.entry_rest`). -/
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

/-- the first change as `PipeChangeEnd.PipeRun` -/
def Changes.run₁ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) :
    PipeChangeEnd.PipeRun sy nm₁ d₁ (PipeTransition.entry m0) where
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
  entry := C.entry₁
  atCtl := C.ctl₁
  lagPaused := C.paused₁
  places := C.places₁
  quiet := C.quiet₁
  noStart := C.noStart₁

/-- **The change into the room takes at least 91 frames**, from the condition at the entry and the conditions at the places. `hT` is what the check on the ROM gives. -/
theorem Changes.bound₁ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {es : List Machine}
    (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : e₁ + 91 ≤ c₂ := by
  have h := C.run₁.bound hT
  have h1 : C.run₁.cnt C.run₁.a = e₁ + 1 := C.ha₁
  have h2 : C.run₁.cnt C.run₁.b = c₂ + 1 := C.hb₁
  have h3 : PipeChangeEnd.timerF + PipeChangeEnd.afterF = 91 := rfl
  rw [h1, h2, h3] at h
  omega

/-- **`left` is not 0 before control** in the change into the room: from the time at the exit and the first control (`PipeChangeEnd.PipeRun.first`) -/
theorem Changes.first₁ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {es : List Machine}
    (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : ∀ n, C.a₁ ≤ n → n < C.b₁ → left₁ sy nm₁ m0 (C.seq n) ≠ 0 :=
  C.run₁.first hT C.time₁ C.ctlFirst₁

/-- the checks on the ROM that the room needs: what one frame in the room does, two facts about the names, and the condition at the room's first control from the rows of the first change -/
structure RoomChecks (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) : Prop where
  facts : ScreenPage.RoomFacts sy nmS m0 160 (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0))
  timer : (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)).rkI = (ScreenPage.placesR sy nmS m0).timerI
  rt : ScreenPage.entryEnvOK sy nmS m0 (SideChangeBound.sideEnv nm₂ (SideTransition.entry m0)) (SideChangeEnd.refs2 nm₂ nx₂ (SideTransition.entry m0)) = true
  pipe : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) [PipeTransition.entry m0]
  start : ScreenStart.roomCheck sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true

/-- **The condition at the first control in the room**, from the rows of the time of the first change: the time at the exit and the first control -/
theorem Changes.roomAt {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : ScreenPage.Room sy nmS m0 (C.seq C.b₁) :=
  ScreenStart.room_of_rows hR.start (C.run₁.inRowsT hR.pipe C.time₁ C.ctlFirst₁) C.ctl₁

/-- the second change as `SideChangeEnd.EndRun` -/
def Changes.run₂ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) :
    SideChangeEnd.EndRun sy nm₂ nx₂ (SideTransition.entry m0) 160 122 where
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
  entry := ScreenPage.entry_rest hR.facts hR.timer hR.rt C.next C.roomOrder (C.roomAt hR) C.roomSites C.roomStay C.entry₂
  atCtl := C.ctl₂
  lagPaused := C.paused₂
  noStart := C.noStart₂
  quiet := C.quiet₂

/-- **The change out of the side pipe takes at least 282 frames**, from the single frames. `hS` and `hT` are what the checks on the ROM give. -/
theorem Changes.bound₂ {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {es : List Machine}
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (C : Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS kind e₁ c₂ e₂ c₃) : e₂ + 282 ≤ c₃ := by
  have h := (C.run₂ hR).bound hS hT
  have h1 : (C.run₂ hR).cnt (C.run₂ hR).a = e₂ + 1 := C.ha₂
  have h2 : (C.run₂ hR).cnt (C.run₂ hR).b = c₃ + 1 := C.hb₂
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
  /-- from the press of Start on the title to frame 0: one condition on the machine after the press, no Start on the frames of the game core before control, and frame 0 is the
  frame before the first control -/
  title : TitleStart.Begin sy tc chg.seq chg.inp
  /-- the counters of `clock` before frame 0 are those of the machine when frame 0 begins, as `flag` says of the machine after the castle entry (`t_E`, `ph_E`) -/
  read₀ : (clock.s 0).t = CastleToLevel.timerOf tc.nm (chg.seq 0) ∧ clock.ph 0 = CastleToLevel.phaseOf tc.nm (chg.seq 0)
  /-- the machine of `pipe` at control is `chg`'s machine when frame 1 begins -/
  pipeAt : pipe.fm 1 = chg.seq 1
  /-- the frames of `pole` begin at the machine at the end of the second change -/
  atCtl : pole.seq 0 = chg.seq chg.b₂
  /-- the machine of `room` at first control is the machine at the end of the first change -/
  roomCtl : room.fm room.C = chg.seq chg.b₁
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

/-- the change into the room takes at least 91 frames -/
theorem Run.change₁ {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.pipe.E + 91 ≤ R.room.C :=
  R.chg.bound₁ hT₁

/-- the change out of the side pipe takes at least 282 frames -/
theorem Run.change₂ {es : List Machine} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : R.room.E + 282 ≤ R.Cs :=
  R.chg.bound₂ hS hT hR

/-- every frame after the castle entry, up to the level change: its counters, by the rule on one frame. `hF` is the check of the ROM. -/
def Run.flagRun (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) :
    Flag fc.lim fc.w0 R.E R.clock.T R.clock.c R.L :=
  FlagRule.flagOf_after hF R.chg.next R.flag

/-- the frames of the flag and the fireworks after the timer's count -/
def Run.Df (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) : Nat := (R.flagRun hF).D

/-- the segments are in order -/
theorem Run.segsOk (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (h₃ : R.room.C ≤ R.room.E) :
    Segs.Ok ⟨R.pipe.E, R.z₁, R.room.C, R.room.E, R.z₂, R.Cs, R.Cs + R.pole.g, R.Cs + R.pole.c⟩ := by
  have h3 := R.hz₁
  have h4 := R.hz₂
  have h5 := R.pole.afterTouch
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

/-- the timer before frame 0, read from the machine when frame 0 begins -/
theorem Run.s_zero (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) : (R.clock.s 0).t = t0 :=
  R.read₀.1.trans (R.zero hB).1

/-- the phase before frame 0, read from the machine when frame 0 begins -/
theorem Run.ph_zero (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) : R.clock.ph 0 = 2 :=
  R.read₀.2.trans (R.zero hB).2

/-- the game timer at the castle entry: it stops at the touch, and each stretch of play takes at most one off per `q` frames, rounded up -/
theorem Run.hT (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) (hq₁ : 1 ≤ q) (h₃ : R.room.C ≤ R.room.E) :
    t0 ≤ R.T + (ticks q R.pipe.E + ticks q (R.room.E - R.room.C) + ticks q R.pole.g) := by
  have h := R.clock.hT hq₁ (R.segsOk h₃) (R.s_zero hB)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

/-- the interval timer's phase at the castle entry: the grid of the last wait -/
theorem Run.hc (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hB : TitleStart.check sy tc t0 = true) (h₃ : R.room.C ≤ R.room.E) :
    (R.c + R.E) % 21 = (3 + R.j) % 21 :=
  R.clock.hc (R.segsOk h₃) (R.ph_zero hB)

/-- **The state at control above ground**, on the real machines: it comes from the last row of the change, under the change's conditions. `left` is not 0 before control,
from the time at the exit and the first control (`SideChangeEnd.EndRun.first`). `hc` is the check on the ROM. -/
theorem Run.start {es : List Machine} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122) (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hc : SurfaceFrames.startCheck sy nm₂ nx₂ (SideTransition.entry m0) 160 122 PA = true)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : SurfaceFrames.Start sy PA (R.pole.seq 0) := by
  rw [R.atCtl]
  exact SurfaceFrames.EndRun.start hS hT hc (R.chg.run₂ hR) ((R.chg.run₂ hR).first hT R.chg.time₂ R.chg.ctlFirst₂)

/-- **The state at first control in the room**, on the real machines: it comes from the last row of the change into the room, under the change's conditions and `Changes.first₁`. `hc` is the check on
the ROM. -/
theorem Run.roomStart {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hc : RoomStart.startCheck sy nm₁ d₁ (PipeTransition.entry m0) (RoomJoin.room sy rN) rN.startY rN.startW rN.fallF = true)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) : RoomJoin.StartAt sy rN (R.room.fm R.room.C) := by
  rw [R.roomCtl]
  exact RoomStart.PipeRun.start hT₁ hc R.chg.run₁ (R.chg.first₁ hT₁)

/-- the frames after the timer's count: at least 33 -/
theorem Run.hD (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) : 33 ≤ R.Df hF :=
  (R.flagRun hF).hD

/-- the level change is not before the first grid point after the sum -/
theorem Run.hL (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) (hsy : fc.sy = sy)
    (hw : 6 ≤ sy.StarFlagDelay.toNat) : R.E + R.T + R.Df hF + 107 + wait R.c (R.T + R.Df hF) ≤ R.L :=
  (R.flagRun hF).hL (by show 6 ≤ fc.sy.StarFlagDelay.toNat; rw [hsy]; exact hw)

/-- **The join.** The bounds of the parts give the bound on the level change. The touch comes as the three cases of `PoleJoin.touch_castle`.
`hT₁`, `hS` and `hT` are the checks of the two changes on the ROM, `hR` those of the room, `hF` that of the star flag, `hB` that of the start from the title. -/
theorem level_ge_of_parts {es es₁ : List Machine} (hq : 2 ≤ q) (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hw : 6 ≤ sy.StarFlagDelay.toNat)
    (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hF : FlagRule.Checked fc (FlagRule.dataOf fc)) (hsy : fc.sy = sy) (hB : TitleStart.check sy tc t0 = true)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    (h₁ : 368 ≤ R.pipe.E)
    (h₃ : R.room.C + 111 ≤ R.room.E)
    (h₅ : (234 ≤ R.pole.g ∧ R.pole.g + 132 ≤ R.pole.c) ∨ (240 ≤ R.pole.g ∧ R.pole.g ≤ 241 ∧ R.pole.g + 126 ≤ R.pole.c) ∨
      (242 ≤ R.pole.g ∧ R.pole.g + 125 ≤ R.pole.c)) :
    1748 + R.j ≤ R.L := by
  have hc1 := R.change₁ hT₁
  have hc2 := R.change₂ hS hT hR
  have hE := R.hE
  have hgc := R.pole.afterTouch
  exact level_ge (P1 := R.pipe.E) (X1 := R.room.C - R.pipe.E) (P2 := R.room.E - R.room.C) (X2 := R.Cs - R.room.E)
    (P3 := R.pole.g) (W := R.pole.c - R.pole.g) hq ht0 h₁ (by omega) (by omega) (by omega)
    (by rcases h₅ with ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b⟩
        · exact Or.inl ⟨a, by omega⟩
        · exact Or.inr (Or.inl ⟨a, b, by omega⟩)
        · exact Or.inr (Or.inr ⟨a, by omega⟩))
    (by omega) (R.hT hB (by omega) (by omega)) (R.hD hF) (R.hc hB (by omega)) (R.hL hF hsy hw)

end Smbrta.Route
