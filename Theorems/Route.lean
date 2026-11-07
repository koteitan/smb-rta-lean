import Theorems.PipeEntry
import Theorems.PipeEntryRule
import Theorems.RoomJoin
import Theorems.PoleJoin
import Theorems.CastleToLevel
import Theorems.PipeChangeBound
import Theorems.SideChangeBound
import Theorems.SideChangeEnd

/-!
# The whole route: 1-2 does not start before frame 1748

The parts of the route are joined here into one statement. `Run` lists what a run has to satisfy, one named field per assumption. `level_ge_of_parts` is the
arithmetic of the join: from the bounds of the parts it concludes the level change's frame. The private proof applies the theorems of the parts for the numbers of the game.
No field is proved for every run: this says which assumptions the bound rests on. Page: `1-1/0-1-Route.md`.

Frames are numbered from the first controllable frame of 1-1. The fields of the parts (`pipe.E`, `room.C`, `room.E`, `Cs`, `pole.g`, `pole.c`) count frames without the `lag` frames of
`CastleToLevel.Frames`. `E` and the frames of `clock` count all frames. The three facts about the timers in the whole run are proved here from the rule on single frames: `Run.hE`, `Run.hT`, `Run.hc`.
The frames after the castle entry are in `flag`, and the two facts about them are proved in the same way: `Run.hD`, `Run.hL`.

The two changes of area are proved here from single frames of one sequence of real machines (`Changes`): `Run.change₁`, `Run.change₂`. A frame takes at most one off the number of frames left, a `lag` frame takes nothing off it.
-/

namespace Smbrta.Route

open CastleToLevel (ticks wait level_ge Frames Segs Flag Kind seen)
open PipeTransitionAll (Names)

/-- Up to the vertical pipe: the hypotheses of `PipeEntry.no_entry_by`, with the entry on real frames (`PipeEntryRule`), and the frame `E` on which he enters. -/
structure Pipe (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) where
  amax : Int
  fr : Nat → TopSpeed.Frame (TopSpeed.top sy : Int) amax
  /-- the machine when counted frame `t` begins, and its input -/
  fm : Nat → Machine
  inp : Nat → UInt8
  /-- the routine's write ends one pass of the foot check -/
  pass : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n, PipeEntryRule.WriteStep sy (fm t) (inp t) n →
    PipeEntryRule.Pass (PipeEntryRule.spots sy m0) (PipeEntryRule.envOf m0) (PipeEntryRule.trace (fm t) (inp t)) n
  /-- `P₂` is the position when the block buffer routine is entered for the right foot, before the write -/
  pos : ∀ t, PipeEntryRule.Enters sy (fm t) (inp t) → ∀ n j, PipeEntryRule.WriteStep sy (fm t) (inp t) n → j < n →
    PipeEntryRule.AtEntry (PipeEntryRule.spots sy m0) (PipeEntryRule.trace (fm t) (inp t) j) →
    ∃ f : Int, 0 ≤ f ∧ (fr t).P₂ = 256 * (PipeEntryRule.px (PipeEntryRule.spots sy m0) (PipeEntryRule.trace (fm t) (inp t) j) : Int) + f
  /-- the position up to frame `N`, within the bound of the opening -/
  openP : ∀ t, t ≤ N → (fr t).P₂ ≤ posP sy m0 + D
  openB : (fr N).P' ≤ posP sy m0 + D
  speed : -(TopSpeed.top sy : Int) ≤ (fr N).v' ∧ (fr N).v' ≤ (TopSpeed.top sy : Int)
  /-- after frame `N` the frames follow each other -/
  next : ∀ j, PoleGrab.Next (fr (N + j)) (fr (N + j + 1))
  /-- the frame he enters the vertical pipe -/
  E : Nat
  enter : PipeEntryRule.Enters sy (fm E) (inp E)

/-- the frames left in the change into the room, read from a machine: `PipeChangeBound.leftOf` with the table of the reference entry -/
abbrev left₁ (sy : Syms) (nm : Names) (m0 : Machine) : Machine → Nat :=
  PipeChangeBound.leftOf sy nm sy.EngVerticalPipe (PipeChangeBound.tableOf sy nm (PipeTransition.entry m0) 48 43) 43

/-- the frames left in the change out of the side pipe, read from a machine -/
abbrev left₂ (sy : Syms) (nm : Names) (m0 : Machine) : Machine → Nat :=
  SideChangeBound.leftAt sy nm (SideTransition.entry m0) 160 122

/-- The two changes of area on the real machines of a run. There is one sequence of machines, for both changes, numbered as `kind` numbers the frames. `e₁`, `c₂`, `e₂`, `c₃` count frames without
the `lag` frames, as `Segs` does. -/
structure Changes (sy : Syms) (m0 : Machine) (nm₁ nm₂ nx₂ : Names) (kind : Nat → Kind) (e₁ c₂ e₂ c₃ : Nat) where
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
  entry₁ : PipeChangeBound.EntryCond sy nm₁ sy.EngVerticalPipe 48 (seq a₁)
  /-- control at the end -/
  ctl₁ : controllable sy (seq b₁) = true
  /-- a `lag` frame takes nothing off the frames left -/
  keep₁ : ∀ n, a₁ ≤ n → n < b₁ → kind n = .lag → left₁ sy nm₁ m0 (seq n) ≤ left₁ sy nm₁ m0 (seq (n + 1))
  /-- any other frame takes at most one off -/
  fall₁ : ∀ n, a₁ ≤ n → n < b₁ → kind n ≠ .lag → left₁ sy nm₁ m0 (seq n) ≤ left₁ sy nm₁ m0 (seq (n + 1)) + 1
  /-- the second change: the machine after frame `e₂`, and the machine after frame `c₃` -/
  a₂ : Nat
  b₂ : Nat
  order₂ : a₂ ≤ b₂
  ha₂ : seen kind a₂ = e₂ + 1
  hb₂ : seen kind b₂ = c₃ + 1
  /-- the condition on the machine at the entry -/
  entry₂ : SideChangeEnd.Entry2 nm₂ nx₂ (SideTransition.entry m0) 160 (seq a₂)
  /-- control at the end -/
  ctl₂ : controllable sy (seq b₂) = true
  /-- a `lag` frame takes nothing off the frames left -/
  keep₂ : ∀ n, a₂ ≤ n → n < b₂ → kind n = .lag → left₂ sy nm₂ m0 (seq n) ≤ left₂ sy nm₂ m0 (seq (n + 1))
  /-- no Start on the frames of the game core after the pipe -/
  noStart₂ : ∀ n, a₂ ≤ n → n < b₂ → SideChangeEnd.coreFrame sy sy.EngSidePipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- at the exit, the sound's pause bytes have the reference's values -/
  quiet₂ : ∀ n, a₂ ≤ n → n ≤ b₂ → SideChangeBound.ExitAt (SideChangeBound.exitBytes sy nm₂ (SideChangeEnd.refExit (SideTransition.entry m0) 160)) (seq n) →
    SideChangeEnd.Quiet (SideChangeEnd.quietBytes nx₂ (SideTransition.entry m0) 160) (seq n)

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

/-- **The change into the room takes at least 91 frames**, from the single frames. `hk` is the check on the ROM that no key of the table is a state of control. -/
theorem Changes.bound₁ {sy : Syms} {m0 : Machine} {nm₁ nm₂ nx₂ : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat}
    (hk : PipeChangeBound.keysOK sy sy.EngVerticalPipe (PipeChangeBound.tableOf sy nm₁ (PipeTransition.entry m0) 48 43) = true)
    (C : Changes sy m0 nm₁ nm₂ nx₂ kind e₁ c₂ e₂ c₃) : e₁ + 91 ≤ c₂ := by
  have h := counted_ge C.order₁ C.keep₁ C.fall₁
  rw [C.ha₁, C.hb₁] at h
  have h0 : left₁ sy nm₁ m0 (C.seq C.b₁) = 0 := PipeChangeBound.left_zero_of_ctl hk C.ctl₁
  have h1 : 48 + 43 ≤ left₁ sy nm₁ m0 (C.seq C.a₁) := PipeChangeBound.left_of_entry _ 43 C.entry₁
  omega

/-- the second change as `SideChangeEnd.EndRun` -/
def Changes.run₂ {sy : Syms} {m0 : Machine} {nm₁ nm₂ nx₂ : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} (C : Changes sy m0 nm₁ nm₂ nx₂ kind e₁ c₂ e₂ c₃) :
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
  entry := C.entry₂
  atCtl := C.ctl₂
  lagKeeps := C.keep₂
  noStart := C.noStart₂
  quiet := C.quiet₂

/-- **The change out of the side pipe takes at least 282 frames**, from the single frames. `hS` and `hT` are what the checks on the ROM give. -/
theorem Changes.bound₂ {sy : Syms} {m0 : Machine} {nm₁ nm₂ nx₂ : Names} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat} {es : List Machine}
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122)
    (C : Changes sy m0 nm₁ nm₂ nx₂ kind e₁ c₂ e₂ c₃) : e₂ + 282 ≤ c₃ := by
  have h := C.run₂.bound hS hT
  have h1 : C.run₂.cnt C.run₂.a = e₂ + 1 := C.ha₂
  have h2 : C.run₂.cnt C.run₂.b = c₃ + 1 := C.hb₂
  rw [h1, h2] at h
  omega

/-- A run through 1-1, and every assumption of the bound. The parts are `pipe` (part a), `room` (part c), `pole` (parts e, f), `chg` (parts b, d); the fields below them join these, the frames of
the run with their timers (`clock`) and the level change (from the castle to 1-2). -/
structure Run (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) (rN : RoomJoin.Nums)
    (b : Machine) (vs : List Jump.VS) (PA : PoleJoin.Box) (Ts J Nc : Nat) (F : Int) (q t0 : Nat) (nm₁ nm₂ nx₂ : Names) where
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
  clock : Frames q t0 E ⟨pipe.E, z₁, room.C, room.E, z₂, Cs, Cs + pole.g, Cs + pole.c⟩
  /-- the two changes of area, on the real machines of the frames of `clock` -/
  chg : Changes sy m0 nm₁ nm₂ nx₂ clock.kind pipe.E room.C room.E Cs
  /-- the level change -/
  L : Nat
  /-- every frame after the castle entry, up to the level change: its counters, by the rule on one frame -/
  flag : Flag sy.StarFlagTopY.toNat sy.StarFlagDelay.toNat E clock.T clock.c L

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ nm₂ nx₂ : Names}

/-- the frames on which no timer runs, other than one in each change -/
def Run.j (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : Nat := R.clock.j

/-- the game timer at the castle entry -/
def Run.T (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : Nat := R.clock.T

/-- the interval timer's phase at the castle entry -/
def Run.c (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : Nat := R.clock.c

/-- the change into the room takes at least 91 frames -/
theorem Run.change₁ (hk : PipeChangeBound.keysOK sy sy.EngVerticalPipe (PipeChangeBound.tableOf sy nm₁ (PipeTransition.entry m0) 48 43) = true)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : R.pipe.E + 91 ≤ R.room.C :=
  R.chg.bound₁ hk

/-- the change out of the side pipe takes at least 282 frames -/
theorem Run.change₂ {es : List Machine} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : R.room.E + 282 ≤ R.Cs :=
  R.chg.bound₂ hS hT

/-- the frames of the flag and the fireworks after the timer's count -/
def Run.Df (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : Nat := R.flag.D

/-- the segments are in order, when a change is longer than the timer's period -/
theorem Run.segsOk (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) (hq : q ≤ 90) (h₃ : R.pipe.E + 91 ≤ R.room.C ∧ R.room.C ≤ R.room.E ∧ R.room.E + 282 ≤ R.Cs) :
    Segs.Ok q ⟨R.pipe.E, R.z₁, R.room.C, R.room.E, R.z₂, R.Cs, R.Cs + R.pole.g, R.Cs + R.pole.c⟩ := by
  obtain ⟨h1, h₃, h2⟩ := h₃
  have h3 := R.hz₁
  have h4 := R.hz₂
  have h5 := R.pole.afterTouch
  exact ⟨h3.1, h3.2, by simp only; omega, h₃, h4.1, h4.2, by simp only; omega, by simp only; omega, by simp only; omega⟩

/-- the castle entry's frame: the frames of the parts and the frames of `j` -/
theorem Run.hE (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : R.E = R.Cs + R.pole.c + R.j :=
  R.clock.hE

/-- the game timer at the castle entry: it stops at the touch, and each stretch of play takes at most one off per `q` frames, rounded up -/
theorem Run.hT (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) (hq₁ : 1 ≤ q) (hq : q ≤ 90) (h₃ : R.pipe.E + 91 ≤ R.room.C ∧ R.room.C ≤ R.room.E ∧ R.room.E + 282 ≤ R.Cs) :
    t0 ≤ R.T + (ticks q R.pipe.E + ticks q (R.room.E - R.room.C) + ticks q R.pole.g) := by
  have h := R.clock.hT hq₁ (R.segsOk hq h₃)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

/-- the interval timer's phase at the castle entry: the grid of the last wait -/
theorem Run.hc (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) (hq : q ≤ 90) (h₃ : R.pipe.E + 91 ≤ R.room.C ∧ R.room.C ≤ R.room.E ∧ R.room.E + 282 ≤ R.Cs) :
    (R.c + R.E) % 21 = (3 + R.j) % 21 :=
  R.clock.hc (R.segsOk hq h₃)

/-- the frames after the timer's count: at least 33 -/
theorem Run.hD (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) : 33 ≤ R.Df :=
  R.flag.hD

/-- the level change is not before the first grid point after the sum -/
theorem Run.hL (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂) (hw : 6 ≤ sy.StarFlagDelay.toNat) :
    R.E + R.T + R.Df + 107 + wait R.c (R.T + R.Df) ≤ R.L :=
  R.flag.hL hw

/-- **The join.** The bounds of the parts give the bound on the level change. The touch comes as the three cases of `PoleJoin.touch_castle`. `q ≤ 90`: a change is longer than the timer's period.
`hk`, `hS` and `hT` are the checks of the two changes on the ROM. -/
theorem level_ge_of_parts {es : List Machine} (hq : 2 ≤ q ∧ q ≤ 90) (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hw : 6 ≤ sy.StarFlagDelay.toNat)
    (hk : PipeChangeBound.keysOK sy sy.EngVerticalPipe (PipeChangeBound.tableOf sy nm₁ (PipeTransition.entry m0) 48 43) = true)
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ nm₂ nx₂)
    (h₁ : 368 ≤ R.pipe.E)
    (h₃ : R.room.C + 111 ≤ R.room.E)
    (h₅ : (234 ≤ R.pole.g ∧ R.pole.g + 132 ≤ R.pole.c) ∨ (240 ≤ R.pole.g ∧ R.pole.g ≤ 241 ∧ R.pole.g + 126 ≤ R.pole.c) ∨
      (242 ≤ R.pole.g ∧ R.pole.g + 125 ≤ R.pole.c)) :
    1748 + R.j ≤ R.L := by
  have hc1 := R.change₁ hk
  have hc2 := R.change₂ hS hT
  have hE := R.hE
  have hgc := R.pole.afterTouch
  exact level_ge (P1 := R.pipe.E) (X1 := R.room.C - R.pipe.E) (P2 := R.room.E - R.room.C) (X2 := R.Cs - R.room.E)
    (P3 := R.pole.g) (W := R.pole.c - R.pole.g) hq.1 ht0 h₁ (by omega) (by omega) (by omega)
    (by rcases h₅ with ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b⟩
        · exact Or.inl ⟨a, by omega⟩
        · exact Or.inr (Or.inl ⟨a, b, by omega⟩)
        · exact Or.inr (Or.inr ⟨a, by omega⟩))
    (by omega) (R.hT (by omega) hq.2 (by omega)) R.hD (R.hc hq.2 (by omega)) (R.hL hw)

end Smbrta.Route
