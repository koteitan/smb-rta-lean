import Theorems.PipeEntry
import Theorems.RoomJoin
import Theorems.PoleJoin
import Theorems.CastleToLevel

/-!
# The whole route: 1-2 does not start before frame 1748

The parts of the route are joined here into one statement. `Run` lists what a run has to satisfy, one named field per assumption. `level_ge_of_parts` is the
arithmetic of the join: from the bounds of the parts it concludes the level change's frame. The private proof applies the theorems of the parts for the numbers of the game.
No field is proved for every run: this says which assumptions the bound rests on. Page: `1-1/0-1-Route.md`.

Frames are numbered from the first controllable frame of 1-1. The fields of the parts (`pipe.E`, `room.C`, `room.E`, `Cs`, `pole.g`, `pole.c`) count frames without the `lag` frames of
`CastleToLevel.Frames`. `E` and the frames of `clock` count all frames. The three facts about the timers in the whole run are proved here from the rule on single frames: `Run.hE`, `Run.hT`, `Run.hc`.
-/

namespace Smbrta.Route

open CastleToLevel (ticks wait level_ge Frames Segs)

/-- Up to the vertical pipe: the hypotheses of `PipeEntry.no_entry_by`, and the frame `E` on which he enters. -/
structure Pipe (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) where
  amax : Int
  fr : Nat → TopSpeed.Frame (TopSpeed.top sy : Int) amax
  Enter : Nat → Prop
  /-- an entry is the collision routine's, on a state near the pipe's top, at the position of the frame -/
  rule : ∀ t, Enter t → ∃ c ∈ PipeEntry.cases sy, PipeEntry.enters sy (PipeEntry.withPipe sy m0) c = true ∧
    ∃ f : Int, 0 ≤ f ∧ (fr t).P₂ = 256 * (256 * ((PipeEntry.pipePage sy m0 : Nat) : Int) + (c.x.toNat : Int)) + f
  /-- the position up to frame `N`, within the bound of the opening -/
  openP : ∀ t, t ≤ N → (fr t).P₂ ≤ posP sy m0 + D
  openB : (fr N).P' ≤ posP sy m0 + D
  speed : -(TopSpeed.top sy : Int) ≤ (fr N).v' ∧ (fr N).v' ≤ (TopSpeed.top sy : Int)
  /-- after frame `N` the frames follow each other -/
  next : ∀ j, PoleGrab.Next (fr (N + j)) (fr (N + j + 1))
  /-- the frame he enters the vertical pipe -/
  E : Nat
  enter : Enter E

/-- A run through 1-1, and every assumption of the bound. The parts are `pipe` (segment a), `room` (segment c), `pole` (segments e, f); the fields below them join these and the changes of
area (2, 4), the frames of the run with their timers (`clock`) and the level change (from the castle to 1-2). -/
structure Run (sy : Syms) (m0 : Machine) (N : Nat) (D : Int) (rN : RoomJoin.Nums)
    (b : Machine) (vs : List Jump.VS) (PA : PoleJoin.Box) (Ts J Nc : Nat) (F : Int) (q t0 : Nat) where
  pipe : Pipe sy m0 N D
  room : RoomJoin.RoomRun sy m0 rN
  /-- `pole` counts its frames from control above ground -/
  pole : PoleJoin.Run sy m0 b vs PA Ts J Nc F
  /-- control above ground -/
  Cs : Nat
  /-- the change into the bonus room takes at least 91 frames -/
  change₁ : pipe.E + 91 ≤ room.C
  /-- the change out of the side pipe takes at least 282 frames -/
  change₂ : room.E + 282 ≤ Cs
  /-- the frame of each change on which no timer runs, counted as `pipe.E` is -/
  z₁ : Nat
  z₂ : Nat
  hz₁ : pipe.E ≤ z₁ ∧ z₁ < room.C
  hz₂ : room.E ≤ z₂ ∧ z₂ < Cs
  /-- the castle entry, counting all frames -/
  E : Nat
  /-- every frame up to the castle entry: its kind and its counters, by the rule on one frame -/
  clock : Frames q t0 E ⟨pipe.E, z₁, room.C, room.E, z₂, Cs, Cs + pole.g, Cs + pole.c⟩
  /-- the flag and fireworks after the timer's count -/
  Df : Nat
  hD : 33 ≤ Df
  /-- the level change -/
  L : Nat
  hL : E + clock.T + Df + 107 + wait clock.c (clock.T + Df) ≤ L

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat}

/-- the frames on which no timer runs, other than one in each change -/
def Run.j (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0) : Nat := R.clock.j

/-- the game timer at the castle entry -/
def Run.T (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0) : Nat := R.clock.T

/-- the interval timer's phase at the castle entry -/
def Run.c (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0) : Nat := R.clock.c

/-- the segments are in order, when a change is longer than the timer's period -/
theorem Run.segsOk (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0) (hq : q ≤ 90) (h₃ : R.room.C ≤ R.room.E) :
    Segs.Ok q ⟨R.pipe.E, R.z₁, R.room.C, R.room.E, R.z₂, R.Cs, R.Cs + R.pole.g, R.Cs + R.pole.c⟩ := by
  have h1 := R.change₁
  have h2 := R.change₂
  have h3 := R.hz₁
  have h4 := R.hz₂
  have h5 := R.pole.afterTouch
  exact ⟨h3.1, h3.2, by simp only; omega, h₃, h4.1, h4.2, by simp only; omega, by simp only; omega, by simp only; omega⟩

/-- the castle entry's frame: the frames of the parts and the frames of `j` -/
theorem Run.hE (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0) : R.E = R.Cs + R.pole.c + R.j :=
  R.clock.hE

/-- the game timer at the castle entry: it stops at the touch, and each stretch of play takes at most one off per `q` frames, rounded up -/
theorem Run.hT (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0) (hq₁ : 1 ≤ q) (hq : q ≤ 90) (h₃ : R.room.C ≤ R.room.E) :
    t0 ≤ R.T + (ticks q R.pipe.E + ticks q (R.room.E - R.room.C) + ticks q R.pole.g) := by
  have h := R.clock.hT hq₁ (R.segsOk hq h₃)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

/-- the interval timer's phase at the castle entry: the grid of the last wait -/
theorem Run.hc (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0) (hq : q ≤ 90) (h₃ : R.room.C ≤ R.room.E) :
    (R.c + R.E) % 21 = (3 + R.j) % 21 :=
  R.clock.hc (R.segsOk hq h₃)

/-- **The join.** The bounds of the parts give the bound on the level change. The touch comes as the three cases of `PoleJoin.touch_castle`. `q ≤ 90`: a change is longer than the timer's period. -/
theorem level_ge_of_parts (hq : 2 ≤ q ∧ q ≤ 90) (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0)
    (h₁ : 368 ≤ R.pipe.E)
    (h₃ : R.room.C + 111 ≤ R.room.E)
    (h₅ : (234 ≤ R.pole.g ∧ R.pole.g + 132 ≤ R.pole.c) ∨ (240 ≤ R.pole.g ∧ R.pole.g ≤ 241 ∧ R.pole.g + 126 ≤ R.pole.c) ∨
      (242 ≤ R.pole.g ∧ R.pole.g + 125 ≤ R.pole.c)) :
    1748 + R.j ≤ R.L := by
  have hc1 := R.change₁
  have hc2 := R.change₂
  have hE := R.hE
  have hgc := R.pole.afterTouch
  exact level_ge (P1 := R.pipe.E) (X1 := R.room.C - R.pipe.E) (P2 := R.room.E - R.room.C) (X2 := R.Cs - R.room.E)
    (P3 := R.pole.g) (W := R.pole.c - R.pole.g) hq.1 ht0 h₁ (by omega) (by omega) (by omega)
    (by rcases h₅ with ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b⟩
        · exact Or.inl ⟨a, by omega⟩
        · exact Or.inr (Or.inl ⟨a, b, by omega⟩)
        · exact Or.inr (Or.inr ⟨a, by omega⟩))
    (by omega) (R.hT (by omega) hq.2 (by omega)) R.hD (R.hc hq.2 (by omega)) R.hL

end Smbrta.Route
