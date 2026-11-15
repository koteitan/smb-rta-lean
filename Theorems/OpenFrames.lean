import Theorems.Opening
import Theorems.PipeFrames
import Theorems.OpenMap
import Theorems.OpenFlat
import Theorems.OpenJump
import Theorems.OpenAirFrame
import Theorems.GuardE

/-!
# The opening on real frames: each of the first `N` frames is a step of the model

`Route.Pipe` assumed the bound of the opening on the real frames: the position at the end of frame `N` is at most `P₀ + D` (`openB`). The bound is proved on a model
(`Opening`: the horizontal frame `hstep` and the measured jump lengths). Here the bound is a theorem, from a condition on each of the first `N` frames: the frame is a step of the
model (`OpenRun.step`). The model's state is read from the machines: the horizontal state (`Potential.startHS`) and the position; the frames left in the air are a sequence of
numbers (`air`), 0 at control.

* `OpenRun.reach`: frame `t` begins in a state that the model reaches in `t − 1` steps from the start, with the distance `P(t) − P(1)`.
* `OpenRun.endB`: with the bound of the model (`Opening.opt_of_check`, a check on the ROM), the position at the end of frame `N` is at most `P(1) + D`.
* `OpenRunM.toRun`: a real frame gives the position at its end only modulo `2²⁴`. The bounds of the model to the right (`Opening`) and to the left (`OpenLeft`) make it
  exact at the ends of the first `N − 1` frames; at the end of frame `N`, the page of the next counted frame (not 255) does.

There is no game data in this file. Page: `1-1/a-5-4-OpenFrames.md`.
-/

namespace Smbrta.OpenFrames

open Potential (HS HIn inputsN hstep startHS)
open Opening (Lens valid modes succ start)

variable {sy : Syms} {m0 : Machine} {lens : Lens} {N E : Nat} {fm : Nat → Machine}

/-- **Each of the first `N` frames is a step of the opening's model.** For each counted frame `t` from 1 to `N`, before the entering frame `E`: an input `i` of the model, valid for
the frames left in the air (`air t`: on the ground when 0, else in the air with no jump start); the frames left in the air after it are those the model allows (on a jump start,
between the lengths of a one-frame press and of a held A for the speed at the takeoff, `Opening.modes`); the horizontal state at the next counted frame is `hstep` of this one on
`i`, and the position has moved by `16·v` (no wall, no edge of the screen). -/
structure OpenRun (sy : Syms) (m0 : Machine) (lens : Lens) (N E : Nat) (fm : Nat → Machine) where
  /-- the frames left in the air, when frame `t` begins -/
  air : Nat → Nat
  /-- on the ground at control -/
  air₁ : air 1 = 0
  /-- the step of each frame -/
  step : ∀ t, 1 ≤ t → t ≤ N → t < E → ∃ i ∈ inputsN, valid (air t) i = true ∧ air (t + 1) ∈ modes lens (startHS sy (fm t)) (air t) i ∧
    startHS sy (fm (t + 1)) = hstep sy m0 (startHS sy (fm t)) i ∧ posP sy (fm (t + 1)) = posP sy (fm t) + 16 * sbyte (startHS sy (fm (t + 1))).v

/-- a path of `Reach` with one step more at its end -/
theorem reach_snoc {σ : Type} {f : σ → List σ} : ∀ {x y z : σ} {k : Nat}, Cert.Reach f x k y → z ∈ f y → Cert.Reach f x (k + 1) z
  | _, _, _, _, .refl _, h => .step h (.refl _)
  | _, _, _, _, .step h1 h2, h => .step h1 (reach_snoc h2 h)

/-- the model's state when the counted frame `t` begins: the horizontal state, the frames left in the air, the distance from control -/
def stOf (O : OpenRun sy m0 lens N E fm) (t : Nat) : Opening.St := ((startHS sy (fm t), O.air t), posP sy (fm t) - posP sy (fm 1))

/-- **Frame `t` begins in a state that the model reaches in `t − 1` steps from the start**, when the horizontal state at control is that of the start (`hs`) -/
theorem OpenRun.reach (O : OpenRun sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) :
    ∀ k, k ≤ N → 1 + k ≤ E → Cert.Reach (succ sy m0 lens) (start sy m0) k (stOf O (1 + k))
  | 0, _, _ => by
    have e : stOf O 1 = start sy m0 := by
      show ((startHS sy (fm 1), O.air 1), posP sy (fm 1) - posP sy (fm 1)) = ((startHS sy m0, 0), 0)
      rw [hs, O.air₁, Int.sub_self]
    rw [Nat.add_zero, e]
    exact .refl _
  | k + 1, h1, h2 => by
    have ih := O.reach hs k (by omega) (by omega)
    refine reach_snoc ih ?_
    obtain ⟨i, hi, hv, hm, he, hp⟩ := O.step (1 + k) (by omega) (by omega) (by omega)
    unfold succ
    refine List.mem_flatMap.2 ⟨i, List.mem_filter.2 ⟨hi, hv⟩, List.mem_map.2 ⟨O.air (1 + k + 1), hm, ?_⟩⟩
    show ((hstep sy m0 (startHS sy (fm (1 + k))) i, O.air (1 + k + 1)), (posP sy (fm (1 + k)) - posP sy (fm 1)) + 16 * sbyte (hstep sy m0 (startHS sy (fm (1 + k))) i).v) =
      ((startHS sy (fm (1 + (k + 1))), O.air (1 + (k + 1))), posP sy (fm (1 + (k + 1))) - posP sy (fm 1))
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, ← he, hp]
    congr 1
    omega

/-- **The bound of the opening on real frames.** If the model does not get past `D` in `N` steps (`hopt`, the check of `Opening`), the counted frame `N + 1` begins at most `D`
right of control -/
theorem OpenRun.endB (O : OpenRun sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D) (hN : N < E) : posP sy (fm (N + 1)) ≤ posP sy (fm 1) + D := by
  have h := hopt N _ (Nat.le_refl _) (O.reach hs N (Nat.le_refl _) (by omega))
  have e : (stOf O (1 + N)).2 = posP sy (fm (1 + N)) - posP sy (fm 1) := rfl
  rw [e, show 1 + N = N + 1 by omega] at h
  omega

/-- **The old field `openB`**: the frames are read from the machines (`PipeFrames.Reads`), and the position at control is `P₀` -/
theorem OpenRun.openB {top amax : Int} {fr : Nat → TopSpeed.Frame top amax} (O : OpenRun sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D) (R : PipeFrames.Reads sy E fm fr) (hP : posP sy (fm 1) = posP sy m0) (h1 : 1 ≤ N) :
    N < E → (fr N).P' ≤ posP sy m0 + D := fun hN => by
  rw [R.P' N h1 hN, ← hP]
  exact O.endB hs hopt hN

/-! ### The position modulo `2²⁴`

The movement of a real frame gives the position at its end only modulo `2²⁴` (`FrameModel.move_model`): the page can wrap. `OpenRunM` is `OpenRun` with that. Two searches on
the model put the model's next position inside `[0, 2²⁴)`: no input gets past `D` in `N` frames (`Opening`, `hopt`), and none gets left of the position at control in fewer
than `N` frames (`OpenLeft`, `hlow`). So the position at the end of each of the first `N − 1` frames is exact (`OpenRunM.next`). At the end of frame `N` the left search does
not reach (the model gets a little left of position 0 in `N` frames): there the page of the next counted frame is not 255 (`hlast`). -/

/-- **Each of the first `N` frames is a step of the model, with the position modulo `2²⁴`** -/
structure OpenRunM (sy : Syms) (m0 : Machine) (lens : Lens) (N E : Nat) (fm : Nat → Machine) where
  air : Nat → Nat
  air₁ : air 1 = 0
  step : ∀ t, 1 ≤ t → t ≤ N → t < E → ∃ i ∈ inputsN, valid (air t) i = true ∧ air (t + 1) ∈ modes lens (startHS sy (fm t)) (air t) i ∧
    startHS sy (fm (t + 1)) = hstep sy m0 (startHS sy (fm t)) i ∧ (posP sy (fm (t + 1)) - posP sy (fm t) - 16 * sbyte (startHS sy (fm (t + 1))).v) % 0x1000000 = 0

/-- the model's state when the counted frame `t` begins -/
def stOfM (O : OpenRunM sy m0 lens N E fm) (t : Nat) : Opening.St := ((startHS sy (fm t), O.air t), posP sy (fm t) - posP sy (fm 1))

/-- a page that is not 255 puts the position below `0xFF0000` -/
theorem posP_lt_of_page {m : Machine} (h : peek m sy.Player_PageLoc ≠ 0xFF) : posP sy m < 0xFF0000 := by
  have h1 := (peek m sy.Player_PageLoc).toNat_lt
  have h2 := (peek m sy.Player_X_Position).toNat_lt
  have h3 := (peek m sy.SprObject_X_MoveForce).toNat_lt
  have h4 : (peek m sy.Player_PageLoc).toNat ≠ 255 := fun e => h (UInt8.toNat_inj.1 (by rw [e]; rfl))
  rw [FrameModel.posP_eq]
  unfold FrameModel.posOf
  omega

theorem posP_range (m : Machine) : 0 ≤ posP sy m ∧ posP sy m < 0x1000000 := by
  have := FrameModel.posOf_range (peek m sy.Player_PageLoc) (peek m sy.Player_X_Position) (peek m sy.SprObject_X_MoveForce)
  rw [← FrameModel.posP_eq] at this
  exact this

/-- **The position at the frame's end is exact**, from the position modulo `2²⁴` and the next position of the model inside `[0, 2²⁴)` -/
theorem exact_of_mod {P P' v : Int} (h : (P' - P - 16 * v) % 0x1000000 = 0) (h1 : 0 ≤ P') (h2 : P' < 0x1000000) (h3 : 0 ≤ P + 16 * v) (h4 : P + 16 * v < 0x1000000) :
    P' = P + 16 * v := by
  omega

/-- the same with the page at the frame's end not 255 in place of the lower bound -/
theorem exact_of_page {P P' v : Int} (h : (P' - P - 16 * v) % 0x1000000 = 0) (h1 : 0 ≤ P') (h2 : P' < 0xFF0000) (h3 : 0 ≤ P) (hv : -128 ≤ v)
    (h4 : P + 16 * v < 0x1000000) : P' = P + 16 * v := by
  omega

/-- **The next counted frame's position is exact**, and it begins in a state that the model reaches. `hopt` is the bound of `Opening`, `hlow` the bound of `OpenLeft`
(both checks on the ROM), `htop` keeps them inside `2²⁴`, and `hlast` is the page at the start of the counted frame `N + 1`. -/
theorem OpenRunM.next (O : OpenRunM sy m0 lens N E fm) (hP : posP sy (fm 1) = posP sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D)
    (hlow : ∀ k u, k < N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → -posP sy m0 ≤ u.2) (htop : posP sy m0 + D < 0x1000000)
    (hlast : N < E → peek (fm (N + 1)) sy.Player_PageLoc ≠ 0xFF) {k : Nat} (hk : k < N) (hE : 1 + k < E)
    (hr : Cert.Reach (succ sy m0 lens) (start sy m0) k (stOfM O (1 + k))) :
    posP sy (fm (1 + k + 1)) = posP sy (fm (1 + k)) + 16 * sbyte (startHS sy (fm (1 + k + 1))).v ∧
      Cert.Reach (succ sy m0 lens) (start sy m0) (k + 1) (stOfM O (1 + k + 1)) := by
  obtain ⟨i, hi, hv, hm, he, hmod⟩ := O.step (1 + k) (by omega) (by omega) (by omega)
  have hu : ((hstep sy m0 (startHS sy (fm (1 + k))) i, O.air (1 + k + 1)), (posP sy (fm (1 + k)) - posP sy (fm 1)) + 16 * sbyte (hstep sy m0 (startHS sy (fm (1 + k))) i).v)
      ∈ succ sy m0 lens (stOfM O (1 + k)) := by
    unfold succ
    exact List.mem_flatMap.2 ⟨i, List.mem_filter.2 ⟨hi, hv⟩, List.mem_map.2 ⟨O.air (1 + k + 1), hm, rfl⟩⟩
  have hr' := reach_snoc hr hu
  have h1 : (posP sy (fm (1 + k)) - posP sy (fm 1)) + 16 * sbyte (hstep sy m0 (startHS sy (fm (1 + k))) i).v ≤ D := hopt (k + 1) _ (by omega) hr'
  rw [← he] at h1
  obtain ⟨a1, a2⟩ := posP_range (sy := sy) (fm (1 + k))
  obtain ⟨b1, b2⟩ := posP_range (sy := sy) (fm (1 + k + 1))
  have hpos : posP sy (fm (1 + k + 1)) = posP sy (fm (1 + k)) + 16 * sbyte (startHS sy (fm (1 + k + 1))).v := by
    by_cases hkN : k + 1 < N
    · have h2 : -posP sy m0 ≤ (posP sy (fm (1 + k)) - posP sy (fm 1)) + 16 * sbyte (hstep sy m0 (startHS sy (fm (1 + k))) i).v := hlow (k + 1) _ hkN hr'
      rw [← he] at h2
      exact exact_of_mod hmod b1 b2 (by omega) (by omega)
    · have h3 := hlast (by omega)
      rw [show N + 1 = 1 + k + 1 by omega] at h3
      have := FrameModel.sbyte_range (startHS sy (fm (1 + k + 1))).v
      exact exact_of_page hmod b1 (posP_lt_of_page h3) a1 (by omega) (by omega)
  refine ⟨hpos, ?_⟩
  have e : stOfM O (1 + k + 1) = ((hstep sy m0 (startHS sy (fm (1 + k))) i, O.air (1 + k + 1)),
      (posP sy (fm (1 + k)) - posP sy (fm 1)) + 16 * sbyte (hstep sy m0 (startHS sy (fm (1 + k))) i).v) := by
    have h2 : posP sy (fm (1 + k + 1)) - posP sy (fm 1) = (posP sy (fm (1 + k)) - posP sy (fm 1)) + 16 * sbyte (hstep sy m0 (startHS sy (fm (1 + k))) i).v := by
      have h3 := hpos
      rw [he] at h3
      omega
    show ((startHS sy (fm (1 + k + 1)), O.air (1 + k + 1)), posP sy (fm (1 + k + 1)) - posP sy (fm 1)) = _
    rw [h2, he]
  rw [e]
  exact hr'

/-- every counted frame up to `N + 1` begins in a state that the model reaches -/
theorem OpenRunM.reachAll (O : OpenRunM sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) (hP : posP sy (fm 1) = posP sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D)
    (hlow : ∀ k u, k < N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → -posP sy m0 ≤ u.2) (htop : posP sy m0 + D < 0x1000000)
    (hlast : N < E → peek (fm (N + 1)) sy.Player_PageLoc ≠ 0xFF) :
    ∀ k, k ≤ N → 1 + k ≤ E → Cert.Reach (succ sy m0 lens) (start sy m0) k (stOfM O (1 + k))
  | 0, _, _ => by
    have e : stOfM O 1 = start sy m0 := by
      show ((startHS sy (fm 1), O.air 1), posP sy (fm 1) - posP sy (fm 1)) = ((startHS sy m0, 0), 0)
      rw [hs, O.air₁, Int.sub_self]
    rw [Nat.add_zero, e]
    exact .refl _
  | k + 1, h1, h2 => by
    have ih := O.reachAll hs hP hopt hlow htop hlast k (by omega) (by omega)
    rw [show 1 + (k + 1) = 1 + k + 1 by omega]
    exact (O.next hP hopt hlow htop hlast (by omega) (by omega) ih).2

/-- **The positions are exact**: `OpenRunM` with the two bounds of the model and the page at the start of the counted frame `N + 1` is `OpenRun` -/
def OpenRunM.toRun (O : OpenRunM sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) (hP : posP sy (fm 1) = posP sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D)
    (hlow : ∀ k u, k < N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → -posP sy m0 ≤ u.2) (htop : posP sy m0 + D < 0x1000000)
    (hlast : N < E → peek (fm (N + 1)) sy.Player_PageLoc ≠ 0xFF) : OpenRun sy m0 lens N E fm where
  air := O.air
  air₁ := O.air₁
  step := fun t h1 h2 h3 => by
    obtain ⟨i, hi, hv, hm, he, _⟩ := O.step t h1 h2 h3
    have hn := (O.next hP hopt hlow htop hlast (k := t - 1) (by omega) (by omega) (O.reachAll hs hP hopt hlow htop hlast (t - 1) (by omega) (by omega))).1
    rw [show 1 + (t - 1) = t by omega] at hn
    exact ⟨i, hi, hv, hm, he, hn⟩

/-! ## The frames of the opening on the machines

`OpenRun` asked that each frame is a step of the model. Here this is a theorem from conditions on single frames and states (`Real`): the movement of the frame is
`FrameModel.move_model` (proved for every value of the bytes, by walks of two machines; the frame does not end during it, by `FrameModel.trace_inFrame` and the time of
`CleanK`), the state at the player's routine is the walk of `CtrlKeep` from the frame's start
in control, and the frames not counted keep the bytes of the walk of `LagFrames`. The model's input is the one the player's routine reads (`inOf`). The frames left in the air
are read from the machines (`airT`): 0 when the frame begins on the ground, else the counted frames up to the first that begins on the ground, up to the horizon
`min (N + 1) E`. -/

open PipeTransition (frame)
open PipeEntryRule (trace)
open PipeWrites (FrameStart guardOf)
open PipeFrames (Lags landFrom landFrom_ge landFrom_self landFrom_succ landFrom_at)

/-- the input of the counted frame `t`, as the player's routine reads it: at the first arrival there (`CtrlKeep.arrAt`) -/
def inOf (sy : Syms) (fm : Nat → Machine) (inp : Nat → UInt8) (t : Nat) : HIn :=
  FrameModel.readIn sy (trace (fm t) (inp t) (CtrlKeep.arrAt sy (fm t) (inp t)))

/-- A of the counted frame `t`, as the player's routine reads it: bit 7 of the joypad's bits at the first arrival there -/
def aOf (sy : Syms) (fm : Nat → Machine) (inp : Nat → UInt8) (t : Nat) : Bool :=
  peek (trace (fm t) (inp t) (CtrlKeep.arrAt sy (fm t) (inp t))) sy.SavedJoypadBits &&& 0x80 != 0

/-- the counted frame `t` begins on the ground -/
def groundB (sy : Syms) (fm : Nat → Machine) (t : Nat) : Bool := peek (fm t) sy.Player_State == 0

/-! ### The vertical model on the counted frames -/

/-- **The model's next height before `land` is in the window** at the counted frame `t` in the air: below the ground's height plus `LandDepth`, and the high byte after
the model's step is 1 -/
def NextIn (sy : Syms) (m0 : Machine) (fm : Nat → Machine) (inp : Nat → UInt8) (t : Nat) : Prop :=
  (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy (fm t)) (aOf sy fm inp t) 0).y.toNat <
    (peek m0 sy.Player_Y_Position).toNat + sy.LandDepth.toUInt8.toNat ∧
  OpenJump.hiAfter sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy (fm t)) (aOf sy fm inp t) 0 = 1

/-- **What the vertical model asks of the counted frame `t`**: at a takeoff (on the ground, a jump read) on the ground at the ground's height with the stored speed at
most the top speed; in the air the high byte of the height 1, the halt relation (in a jump the jump's halt value is 1) and the model's next height in the window -/
def VPre (sy : Syms) (m0 : Machine) (fm : Nat → Machine) (inp : Nat → UInt8) (t : Nat) : Prop :=
  (peek (fm t) sy.Player_State = 0 → (inOf sy fm inp t).jump = true ∧ OpenFlat.GroundAt sy m0 (fm t) ∧
      (peek (fm t) sy.Player_XSpeedAbsolute).toNat ≤ TopSpeed.top sy) ∧
  (peek (fm t) sy.Player_State ≠ 0 → peek (fm t) sy.Player_Y_HighPos = 1 ∧ OpenAir.HaltM sy (fm t) ∧ NextIn sy m0 fm inp t)

/-- **The model's vertical step at the counted frame `t`** (`OpenJump.vstepO`): the next counted frame has the high byte of the height 1 and the halt relation, and its
vertical bytes are the model's step: at a takeoff from `ground0` with A and the stored speed, in the air from the frame's own with its A and the stored speed 0 -/
def VStep (sy : Syms) (m0 : Machine) (fm : Nat → Machine) (inp : Nat → UInt8) (t : Nat) : Prop :=
  peek (fm (t + 1)) sy.Player_Y_HighPos = 1 ∧ OpenAir.HaltM sy (fm (t + 1)) ∧
  (peek (fm t) sy.Player_State = 0 → VertModel.vsOf sy (fm (t + 1)) = OpenJump.vstepO sy m0 (FrameModel.ctrlStack sy m0) (peek m0 sy.Player_Y_Position)
      (OpenJump.ground0 (peek m0 sy.Player_Y_Position)) true (peek (fm t) sy.Player_XSpeedAbsolute)) ∧
  (peek (fm t) sy.Player_State ≠ 0 → VertModel.vsOf sy (fm (t + 1)) =
      OpenJump.vstepO sy m0 (FrameModel.ctrlStack sy m0) (peek m0 sy.Player_Y_Position) (VertModel.vsOf sy (fm t)) (aOf sy fm inp t) 0)

/-- **The counted frames from 1 to `N` before `E` follow the vertical model**, when they meet `VPre` -/
def VertOK (sy : Syms) (m0 : Machine) (N E : Nat) (fm : Nat → Machine) (inp : Nat → UInt8) : Prop :=
  ∀ t, 1 ≤ t → t ≤ N → t < E → VPre sy m0 fm inp t → VStep sy m0 fm inp t

/-- **The frame from the scroll handler on**, from the machine `Q` there to the frame's end `b`: it changes no byte of the horizontal state or of the position (no wall, no
edge of the screen), and it ends with the stored speed `|v|` and the collision bits all 1 (the collision routine found nothing) -/
def After (sy : Syms) (Q b : Machine) : Prop :=
  (∀ x ∈ FrameModel.hBytes sy, peek b x = peek Q x) ∧ peek b sy.Player_XSpeedAbsolute = TopSpeed.absB (peek b sy.Player_X_Speed) ∧ peek b sy.Player_CollisionBits = 0xFF

/-- **What stays assumed of the first `N` counted frames**, before the entry `E`: conditions on single frames, on their instructions and on their starts. The frames are those of
`L` (`PipeFrames.Lags`): the counted frame `t` begins at `L.fm t` with the input `L.inp t`. -/
structure Real (sy : Syms) (m0 : Machine) (lens : Lens) (N E : Nat) {g : Nat} {S : FrameKeep.RealRun} (L : Lags sy m0 g S E) : Prop where
  /-- each instruction of the frame meets `CleanK` of `FrameKeep.guardE`: `PipeWrites.Clean` with the castle flag, the position's fraction, the pause byte, the area's
  type, the swimming flag, the change of size, A and B, A and B of the frame before, the moving direction, the running speed and the stored speed protected too, but the
  move routine's own store (the old fields `cleanK` and `spare`; `guardE` in place of `guardF` for `GuardE.prev_endE`) -/
  cleanK : ∀ t, 1 ≤ t → t ≤ N → t < E → ∀ k, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k)
  /-- **no instruction of a counted frame writes the routine, the mode or the task byte by its address** (as `FrameKeep.Frames.noStore` above ground) -/
  noStore : ∀ t, 1 ≤ t → t ≤ N → t < E → ∀ k, FrameKeep.CtlStore sy (trace (L.fm t) (L.inp t) k) = false
  /-- each instruction of each frame from frame 1 to the counted frame `N`, counted or not, meets `OpenMap.MapOK`: a store through an index or a pointer does not write the
  player's state, the jumpspring byte, the block buffers or the collision flag, and the read of the block buffer routine is in the first buffer. With the walk of `OpenMap` this gives the old
  fields `st` (the player's state is 0, 1 or 2 when the frame begins) and `spring` (no jumpspring when the frame begins): `Real.stSpring` -/
  map : ∀ n, 1 ≤ n → n ≤ L.ix N → n < L.ix E → ∀ k, OpenMap.MapOK sy m0 (trace (S.seq n) (S.inp n) k)
  /-- the page is not 255 when the counted frame `N + 1` begins: at the end of frame `N` he has not gone left of position 0 (at the ends of the frames before it, this is
  the search of `OpenLeft`) -/
  page : N < E → peek (L.fm (N + 1)) sy.Player_PageLoc ≠ 0xFF
  /-- from the scroll handler on: `After` -/
  after : ∀ t, 1 ≤ t → t ≤ N → t < E → ∀ k, CtrlKeep.arrAt sy (L.fm t) (L.inp t) ≤ k → (trace (L.fm t) (L.inp t) k).pc = sy.PlayerSubs →
    After sy (trace (L.fm t) (L.inp t) k) (frame (L.fm t) (L.inp t))
  /-- **from the return of the collision routine on, the bytes of the vertical model do not change**: at the return after the first arrival at the player's routine, the
  height, its high byte, the vertical speed and its fraction, the height's fraction, the two forces, the jump's origin, the state, A and B and the jump's halt value are
  those of the frame's end (`OpenAir.AfterVS`). The walks follow these bytes up to the return; after it the walk does not know the enemies, and their code may write
  the vertical speed (a stomp) or the state (a platform) -/
  afterV : ∀ t, 1 ≤ t → t ≤ N → t < E → OpenAir.AfterVS sy m0 (L.fm t) (L.inp t)

/-- **What the frame's start holds, frame after frame**: the stored speed is `|v|`, the collision bits are all 1, and the area's type is `v` with no swimming and no change
of size -/
def Held (sy : Syms) (v : UInt8) (m : Machine) : Prop :=
  peek m sy.Player_XSpeedAbsolute = TopSpeed.absB (peek m sy.Player_X_Speed) ∧ peek m sy.Player_CollisionBits = 0xFF ∧ CtrlKeep.AreaOK sy v m

/-- **The checks on the ROM** that the frames of the opening use: the movement (`FrameModel.modelOK`), the walk up to the player's routine (`CtrlKeep.ctrlCheck`), the walk of
the whole frame with the area's type `v` (`CtrlKeep.afterCheck`), the inputs of the model (`normIdem`), a bound `Zb` above every jump's length (`lensZ`), the
state of `m0` (`start`), and the walks of a frame on the ground (`OpenFlat.flatCheck`). -/
structure Checks (sy : Syms) (m0 : Machine) (lens : Lens) (Zb : Nat) (v : UInt8) (g : Nat) : Prop where
  model : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true
  ctrl : CtrlKeep.ctrlCheck sy m0 = true
  after : CtrlKeep.afterCheck sy m0 v = true
  v3 : v ∈ [(1 : UInt8), 2, 3]
  norm : Potential.normIdem = true
  lensZ : (lens.toList.all fun p => decide (p.2 < Zb)) = true
  Zb0 : 0 < Zb
  /-- the machine `m0` holds `Held` and is on the ground, at the ground's height: the state at control is that of `m0` (`StartRun.titlePosCheck`) -/
  start : Held sy v m0 ∧ peek m0 sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 m0
  /-- the pause byte that the NMI tests (`CtrlKeep.pauseI`, read from the ROM) is `g` -/
  pause : CtrlKeep.pauseI sy m0 = g
  /-- the idle loop is a `JMP` to itself -/
  idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true
  /-- the walks of a frame on the ground (`OpenFlat.flatCheck`) -/
  flat : OpenFlat.flatCheck sy m0 v = true
  /-- the top speed is at least 16 -/
  top16 : 16 ≤ TopSpeed.top sy
  /-- the search of the jumps of the opening's vertical model, with the lengths `lens` (`OpenJump.arcCheck`) -/
  jumps : OpenJump.arcCheck sy m0 (FrameModel.ctrlStack sy m0) (peek m0 sy.Player_Y_Position) sy.LandDepth.toUInt8 lens = true
  /-- the walk of a frame in the air or at a takeoff (`OpenAir.airAll`) -/
  air : OpenAir.airAll sy m0 v = true
  /-- the movement routine in the air, with the high byte of the height (`OpenVert.vertAirHOK`) -/
  vh : OpenVert.vertAirHOK sy m0 (FrameModel.ctrlStack sy m0) = true
  /-- the walk of a frame for A and B of the frame before (`PrevKeep.prevCheck`, part e's) -/
  prev : PrevKeep.prevCheck sy m0 v = true
  /-- bit 7 of A and B of the frame before is that of A and B on `m0` -/
  prev0 : PrevKeep.PrevOK sy m0

/-- every length of `lens` is below `Zb` -/
theorem Checks.lens_lt {Zb g : Nat} {v : UInt8} (C : Checks sy m0 lens Zb v g) (k : Nat) : (lens[k]!).2 < Zb := by
  by_cases h : k < lens.size
  · rw [getElem!_pos lens k h]
    have h1 := C.lensZ
    simp only [List.all_eq_true, decide_eq_true_eq] at h1
    exact h1 _ (Array.getElem_mem_toList h)
  · rw [getElem!_neg lens k h]
    exact C.Zb0

theorem keepA_of {x : UInt16} (h : x ∈ FrameModel.hBytes sy ∨ x = sy.Player_CollisionBits ∨ x = sy.Player_XSpeedAbsolute ∨ x = sy.AreaType ∨
    x = sy.JumpspringAnimCtrl ∨ x = sy.SwimmingFlag ∨ x = sy.PlayerChangeSizeFlag ∨ x = sy.Player_State) : x ∈ CtrlKeep.keepA sy := by
  unfold CtrlKeep.keepA
  simp only [FrameModel.hBytes, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h
  · rcases h with h | h | h | h | h | h | h | h <;> simp [h]
  all_goals simp [h]

/-- **The movement of a real frame**: `FrameModel.clean_frame`, with the position at the frame's end modulo `2²⁴` in place of `far`. The frame does not end during the
movement (`FrameModel.trace_inFrame`): the player's routine comes in the frame of `M` (`hfr`), each instruction but the idle loop runs at least 64 dots before the frame's
end (`htime`, the condition `time` of `FrameKeep.CleanK`), and the idle loop is a `JMP` to itself (`hidle`, a check on the ROM). This was the field `longer`. -/
theorem move_mod {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} (hOK : FrameModel.modelOK sy m0 S = true) (hat : FrameModel.AtCtrl sy (FrameModel.Rom.of m0) S (trace M i n₀))
    (hbef : ∀ a ∈ FrameModel.hBytes sy, peek (trace M i n₀) a = peek M a)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hfr : (trace M i n₀).frame = M.frame)
    (htime : ∀ n, (trace M i n).pc ≠ sy.EndlessLoop → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hafter : ∀ j, n₀ ≤ j → (trace M i j).pc = sy.PlayerSubs → ∀ a ∈ FrameModel.hBytes sy, peek (frame M i) a = peek (trace M i j) a) :
    FrameModel.readHS sy (frame M i) = hstep sy m0 (FrameModel.readHS sy M) (FrameModel.readIn sy (trace M i n₀)) ∧
      (posP sy (frame M i) - posP sy M - 16 * sbyte (FrameModel.readHS sy (frame M i)).v) % 0x1000000 = 0 ∧ ∃ j, n₀ ≤ j ∧ (trace M i j).pc = sy.PlayerSubs := by
  obtain ⟨k, hk, _, hpc, h1, h2, hC⟩ := FrameModel.move_model hOK hat
  have e0 := (FrameModel.trace_inFrame hidle hfr hC htime k (Nat.le_refl k)).1
  have e1 := hafter (n₀ + k) (by omega) (by rw [e0]; exact hpc)
  rw [e0] at e1
  have e2 : FrameModel.readHS sy (trace M i n₀) = FrameModel.readHS sy M := FrameModel.readHS_congr hbef
  have e3 : posP sy (trace M i n₀) = posP sy M := FrameModel.posP_congr hbef
  have e4 := FrameModel.readHS_congr (sy := sy) e1
  have e5 := FrameModel.posP_congr (sy := sy) e1
  rw [e2] at h1
  rw [e3] at h2
  rw [← e4] at h1 h2
  rw [← e5] at h2
  exact ⟨h1, h2, n₀ + k, by omega, by rw [e0]; exact hpc⟩

theorem and_ff (x : UInt8) : x &&& 255 = x := by
  apply UInt8.toNat_inj.1
  rw [UInt8.toNat_and]
  have h := x.toNat_lt
  show x.toNat &&& 255 = x.toNat
  rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- the old fields `st` and `spring` of `Real`: when each of the first `N` counted frames begins, the player's state is 0, 1 or 2 and the jumpspring byte is 0 -/
def StSpring {g : Nat} {S : FrameKeep.RealRun} (sy : Syms) (L : Lags sy m0 g S E) (N E' : Nat) : Prop :=
  ∀ t, 1 ≤ t → t ≤ N → t < E' → peek (L.fm t) sy.Player_State ∈ [(0 : UInt8), 1, 2] ∧ peek (L.fm t) sy.JumpspringAnimCtrl = 0

/-- **The player's state and the jumpspring byte when each of the first `N` counted frames begins** (the old fields `st` and `spring`): every frame from frame 1 on, counted
or not, keeps the block buffers of `m0`, the jumpspring byte 0 and the player's state 0, 1 or 2 (`OpenMap.Lags.mapAt`, with the field `map`), and they hold at frame 1
(`hm₁`, from the title's check). `hc`, `hp`, `hM` are checks on the ROM. -/
theorem Real.stSpring {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} (hc : LagFrames.lagCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true)
    (hM : OpenMap.mapCheck sy m0 = true) (O : Real sy m0 lens N E L) (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1))
    (hm₁ : OpenMap.MapAt sy m0 (S.seq 1)) : StSpring sy L N E := by
  intro t h1 h2 h3
  have hmono : L.ix t ≤ L.ix N := L.ix_mono h2
  have hmE : L.ix t ≤ L.ix E := L.ix_mono (Nat.le_of_lt h3)
  have hA := OpenMap.Lags.mapAt hc hp hM L hs₁ hm₁ hmE
    (fun n a1 a2 k => O.map n a1 (Nat.le_of_lt (Nat.lt_of_lt_of_le a2 hmono)) (Nat.lt_of_lt_of_le a2 hmE) k) (L.ix t) (L.one_le_ix h1) (Nat.le_refl _)
  obtain ⟨hw, hst⟩ := hA
  refine ⟨?_, ?_⟩
  · show (S.seq (L.ix t)).ram.get! (OpenMap.stI sy) ∈ [(0 : UInt8), 1, 2]
    rcases OpenMap.le2 hst with h | h | h <;> simp [h]
  · have h : (S.seq (L.ix t)).ram.get! (OpenMap.jI sy) &&& 0xFF = 0 &&& 0xFF := hw (OpenMap.jI sy, 0xFF, 0) (List.mem_append_right _ (List.Mem.head _))
    show (S.seq (L.ix t)).ram.get! (OpenMap.jI sy) = 0
    rw [and_ff, and_ff] at h
    exact h

/-- **One counted frame of the opening**: from its start in control (`hs`) with what the frames before left (`hh`), the frame follows `hstep` on the input its player's
routine reads, the position moves by `16·v` modulo `2²⁴`, and the frame's end holds again what the next frame needs (`Held`, before the frames not counted). -/
theorem Real.frame_step {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (C : Checks sy m0 lens Zb v g) (O : Real sy m0 lens N E L)
    {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ N) (h3 : t < E) (hs : FrameKeep.StartK sy m0 (L.fm t)) (hh : Held sy v (L.fm t))
    (hm : peek (L.fm t) sy.Player_State ∈ [(0 : UInt8), 1, 2] ∧ peek (L.fm t) sy.JumpspringAnimCtrl = 0) :
    startHS sy (frame (L.fm t) (L.inp t)) = hstep sy m0 (startHS sy (L.fm t)) (inOf sy L.fm L.inp t) ∧
      (posP sy (frame (L.fm t) (L.inp t)) - posP sy (L.fm t) - 16 * sbyte (startHS sy (frame (L.fm t) (L.inp t))).v) % 0x1000000 = 0 ∧
      Held sy v (frame (L.fm t) (L.inp t)) ∧
      peek (trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t))) sy.Player_State = peek (L.fm t) sy.Player_State := by
  generalize hM : L.fm t = M at hs hh ⊢
  generalize hi : L.inp t = i
  have hclF : ∀ k, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace M i k) := by
    rw [← hM, ← hi]; exact fun k => FrameKeep.cleanK_of_E (O.cleanK t h1 h2 h3 k)
  have hcl : ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace M i k) := fun k => FrameKeep.cleanK_of_F (hclF k)
  have hu : CtrlKeep.Unpaused sy m0 (frame M i) := by
    rw [← hM, ← hi]
    show (frame (L.fm t) (L.inp t)).ram.get! (CtrlKeep.pauseI sy m0) &&& 1 = 0
    rw [C.pause, ← S.next]
    exact L.unpaused h1 (by omega)
  have hin : inOf sy L.fm L.inp t = FrameModel.readIn sy (trace M i (CtrlKeep.arrAt sy M i)) := by
    unfold inOf; rw [hM, hi]
  rw [hin]
  generalize hn : CtrlKeep.arrAt sy M i = n₀
  have harr := CtrlKeep.arrive_at C.ctrl hs hcl hu
  rw [hn] at harr
  have A := CtrlKeep.ctrl_keep C.ctrl hs hcl harr.1 harr.2.1 harr.2.2
  have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (trace M i n₀) x = peek M x := A.keep
  obtain ⟨hab, hbits, harea, hswim, hsize⟩ := hh
  obtain ⟨hst, hspr⟩ := hm
  rw [hM] at hst hspr
  have hat : FrameModel.AtCtrl sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i n₀) := by
    refine ⟨A.good, harr.1, A.s, A.eng, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kp _ (keepA_of (by simp)), harea]; exact C.v3
    · rw [kp _ (keepA_of (by simp))]; exact hst
    · rw [kp _ (keepA_of (by simp))]; exact hspr
    · rw [kp _ (keepA_of (by simp)), hswim]
    · rw [kp _ (keepA_of (by simp)), hsize]
    · rw [kp _ (keepA_of (by simp)), kp _ (keepA_of (by simp [FrameModel.hBytes]))]; exact hab
    · rw [kp _ (keepA_of (by simp)), hbits]; exact SurfaceFrames.ff_and _
  have haf : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → After sy (trace M i k) (frame M i) := by
    intro k hk hpc
    have := O.after t h1 h2 h3 k (by rw [hM, hi, hn]; exact hk) (by rw [hM, hi]; exact hpc)
    rw [hM, hi] at this
    exact this
  obtain ⟨r1, r2, j, hj, hpc⟩ := move_mod C.model hat (fun a ha => kp a (keepA_of (Or.inl ha))) C.idle harr.2.1 (fun n hn => (hcl n).time hn)
    (fun j hj hpc a ha => (haf j hj hpc).1 a ha)
  obtain ⟨_, hab', hbits'⟩ := haf j hj hpc
  have hA := (SurfaceFrames.area_endF C.ctrl C.after hs hclF ⟨harea, hswim, hsize⟩).1
  refine ⟨?_, r2, ⟨hab', hbits', hA⟩, kp _ (keepA_of (by simp))⟩
  rw [← SurfaceFrames.readHS_eq, ← SurfaceFrames.readHS_eq]
  exact r1

/-- every counted frame from control to the entry starts in the idle loop in control, for the guard of the walks of `CtrlKeep` (`Lags.starts`) -/
theorem startK_of {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true)
    (hp : LagPause.pauseCheck sy m0 g = true) (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ E) :
    FrameKeep.StartK sy m0 (L.fm t) :=
  StartRun.start_mono (L.startAt hc hk hp hs₁ h1 h2) rfl rfl (fun _ hp => hp)

theorem lagI_mem {x : UInt16} (h : x ∈ FrameModel.hBytes sy ∨ x = sy.Player_XSpeedAbsolute ∨ x = sy.Player_CollisionBits ∨ x = sy.AreaType ∨ x = sy.SwimmingFlag ∨
    x = sy.PlayerChangeSizeFlag ∨ x = sy.Player_State) : LagFrames.I x ∈ LagFrames.lagI sy := by
  simp only [FrameModel.hBytes, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [LagFrames.lagI, LagFrames.vfpI, LagFrames.ctlI, LagFrames.moreI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h | h | h
  · rcases h with h | h | h | h | h | h | h | h <;> simp [h]
  all_goals simp [h]

theorem vertI_mem {x : UInt16} (h : x ∈ OpenFlat.vertA sy) : LagFrames.I x ∈ LagFrames.lagI sy := by
  simp only [OpenFlat.vertA, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [LagFrames.lagI, LagFrames.vfpI, LagFrames.ctlI, LagFrames.moreI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h <;> simp [h]

/-- the frames not counted keep `GroundAt` -/
theorem ground_keep {m m' : Machine} (h : ∀ b ∈ LagFrames.lagI sy, m'.ram.get! b = m.ram.get! b) (hg : OpenFlat.GroundAt sy m0 m) : OpenFlat.GroundAt sy m0 m' :=
  OpenFlat.groundAt_congr (fun _ hx => h _ (vertI_mem hx)) hg

/-- the bytes that the frames not counted keep, as `peek` -/
theorem peek_keep {m m' : Machine} (h : ∀ b ∈ LagFrames.lagI sy, m'.ram.get! b = m.ram.get! b) {x : UInt16}
    (hx : x ∈ FrameModel.hBytes sy ∨ x = sy.Player_XSpeedAbsolute ∨ x = sy.Player_CollisionBits ∨ x = sy.AreaType ∨ x = sy.SwimmingFlag ∨
      x = sy.PlayerChangeSizeFlag ∨ x = sy.Player_State) : peek m' x = peek m x :=
  h _ (lagI_mem hx)

/-- the frames not counted keep the horizontal state, the position and `Held` -/
theorem keep_parts {m m' : Machine} {v : UInt8} (h : ∀ b ∈ LagFrames.lagI sy, m'.ram.get! b = m.ram.get! b) :
    startHS sy m' = startHS sy m ∧ posP sy m' = posP sy m ∧ (Held sy v m → Held sy v m') := by
  have hb : ∀ x ∈ FrameModel.hBytes sy, peek m' x = peek m x := fun x hx => peek_keep h (Or.inl hx)
  refine ⟨?_, ?_, ?_⟩
  · rw [← SurfaceFrames.readHS_eq, ← SurfaceFrames.readHS_eq]
    exact FrameModel.readHS_congr hb
  · exact FrameModel.posP_congr hb
  · intro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [peek_keep h (by simp), peek_keep h (Or.inl (by simp [FrameModel.hBytes]))]; exact h1
    · rw [peek_keep h (by simp)]; exact h2
    · show peek m' sy.AreaType = v
      rw [peek_keep h (by simp)]; exact h3
    · show peek m' sy.SwimmingFlag = 0
      rw [peek_keep h (by simp)]; exact h4
    · show peek m' sy.PlayerChangeSizeFlag = 0
      rw [peek_keep h (by simp)]; exact h5

/-- **The flat ground** (the old field `flat`): a counted frame that begins on the ground at the ground's height and whose player's routine reads no jump is followed by a
counted frame that begins on the ground at the ground's height. The frame is covered by the walks of `OpenFlat` (`OpenFlat.flat_end`): up to the player's routine the walk of
`CtrlKeep`, from there the walk with the tiles of the first block buffer up to the return of the collision routine (there on the ground at the ground's height), then the
walk of `FrameKeep`. So the frame ends on the ground or out of control, and it ends in control (`Lags.known_end`); from the return on the vertical bytes do not change
(`afterV`). The frames not counted keep the state and the vertical bytes (`lags_keepI`). The reads of the block buffer routine are in the first buffer (`map`), with the
bytes of `m0` (the walk of `OpenMap`, `OpenMap.map_reads`). `hc`, `hk`, `hp`, `C`, `hM` are checks on the ROM, `hs₁`, `hm₁` the start of frame 1. -/
theorem Real.flat {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true)
    (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (C : Checks sy m0 lens Zb v g) (hM : OpenMap.mapCheck sy m0 = true)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (hm₁ : OpenMap.MapAt sy m0 (S.seq 1)) (O : Real sy m0 lens N E L)
    {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ N) (h3 : t < E) (hh : Held sy v (L.fm t)) (hspr : peek (L.fm t) sy.JumpspringAnimCtrl = 0)
    (hg : peek (L.fm t) sy.Player_State = 0) (hG : OpenFlat.GroundAt sy m0 (L.fm t)) (hj : (inOf sy L.fm L.inp t).jump = false) :
    peek (L.fm (t + 1)) sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 (L.fm (t + 1)) := by
  have hix : L.ix t < L.ix E := Nat.lt_of_lt_of_le (PipeFrames.ixP_lt g S L.dP t) (L.ix_mono h3)
  have hixN : L.ix t ≤ L.ix N := L.ix_mono h2
  have h1ix : 1 ≤ L.ix t := L.one_le_ix h1
  have hmap : ∀ k, OpenMap.MapOK sy m0 (trace (L.fm t) (L.inp t) k) := fun k => O.map (L.ix t) h1ix hixN hix k
  have hsG : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (L.fm t) := L.startAt hc hk hp hs₁ h1 (Nat.le_of_lt h3)
  have hsK : FrameKeep.StartK sy m0 (L.fm t) := startK_of hc hk hp hs₁ h1 (Nat.le_of_lt h3)
  have hmA : OpenMap.MapAt sy m0 (L.fm t) :=
    OpenMap.Lags.mapAt hc hp hM L hs₁ hm₁ (b := L.ix t) (Nat.le_of_lt hix)
      (fun n a1 a2 k => O.map n a1 (Nat.le_trans (Nat.le_of_lt a2) hixN) (Nat.lt_of_lt_of_le a2 (Nat.le_of_lt hix)) k) (L.ix t) h1ix (Nat.le_refl _)
  have hclF : ∀ k, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k) :=
    fun k => FrameKeep.cleanK_of_E (O.cleanK t h1 h2 h3 k)
  have hcl : ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k) := fun k => FrameKeep.cleanK_of_F (hclF k)
  have hcq : ∀ k, FrameKeep.CleanK (OpenFlat.guardQ sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k) := fun k => OpenFlat.cleanQ_of (hclF k) (hmap k)
  have hcM : ∀ k, FrameKeep.CleanK (OpenMap.guardM sy m0) StartRun.noSpot.store (trace (L.fm t) (L.inp t) k) :=
    fun k => OpenMap.cleanK_of (L.cleanG (L.ix t) h1ix hix k) (hmap k)
  have hrM : ∀ k, OpenMap.RdOK (OpenMap.rdOf sy m0) (trace (L.fm t) (L.inp t) k) := fun k => OpenMap.rdOK_of (hmap k)
  have hr : ∀ k, (trace (L.fm t) (L.inp t) k).frame = (L.fm t).frame → OpenFlat.RdOK1 (OpenFlat.rdOf sy m0) (trace (L.fm t) (L.inp t) k) := fun k hf =>
    OpenFlat.rdOK1_of (hmap k) (fun hpc hn => OpenMap.map_reads hM (OpenMap.start_M hsG) hmA.1 hmA.2 hcM hrM hf hpc hn)
  have hu : CtrlKeep.Unpaused sy m0 (frame (L.fm t) (L.inp t)) := by
    show (frame (L.fm t) (L.inp t)).ram.get! (CtrlKeep.pauseI sy m0) &&& 1 = 0
    rw [C.pause, ← S.next]
    exact L.unpaused h1 (by omega)
  have hjump : (FrameModel.readIn sy (trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t)))).jump = false := hj
  obtain ⟨B, hfin, hsB, hgx⟩ := OpenFlat.flat_end C.ctrl C.flat hsK hcl hcq hr hu hh.2.2 hg hG hspr hjump (OpenAir.afterV_of (O.afterV t h1 h2 h3))
  have hkn := L.known_end hc hp h1ix hix hsG
  rw [S.next] at hkn
  have k1 := hkn _ (List.Mem.head _)
  have k2 := hkn _ (List.Mem.tail _ (List.Mem.head _))
  have k3 := hkn _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  -- the frame ends in control: not out of control
  have hnx : OpenFlat.finX sy B = false := by
    cases hx : OpenFlat.finX sy B
    · rfl
    · exfalso
      unfold OpenFlat.finX at hx
      simp only [Bool.or_eq_true] at hx
      rcases hx with (h | h) | h
      · exact OpenMap.excl_mem h (by have := hsB.ram _ (PipeTransitionAll.mask_lt sy.GameEngineSubroutine); rwa [k1] at this)
      · exact OpenMap.excl_mem h (by have := hsB.ram _ (PipeTransitionAll.mask_lt sy.OperMode_Task); rwa [k3] at this)
      · exact OpenMap.excl_mem h (by have := hsB.ram _ (PipeTransitionAll.mask_lt sy.OperMode); rwa [k2] at this)
  have hend : peek (frame (L.fm t) (L.inp t)) sy.Player_State = 0 := by
    unfold OpenFlat.finF at hfin
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hfin
    rcases hfin with ((h | h) | h) | h
    · have e := PipeEntryRule.known_eq h.1 (hsB.ram _ (PipeTransitionAll.mask_lt sy.Player_State))
      rw [h.2] at e
      exact e
    · exact absurd (OpenMap.excl_mem h (by have := hsB.ram _ (PipeTransitionAll.mask_lt sy.GameEngineSubroutine); rwa [k1] at this)) id
    · exact absurd (OpenMap.excl_mem h (by have := hsB.ram _ (PipeTransitionAll.mask_lt sy.OperMode_Task); rwa [k3] at this)) id
    · exact absurd (OpenMap.excl_mem h (by have := hsB.ram _ (PipeTransitionAll.mask_lt sy.OperMode); rwa [k2] at this)) id
  have hgE : OpenFlat.GroundAt sy m0 (frame (L.fm t) (L.inp t)) := by
    rcases hgx with hx | hx
    · rw [hnx] at hx; cases hx
    · exact hx
  have hl := PipeFrames.lags_keepI hc hk hp L hs₁ t h3
  refine ⟨?_, ground_keep hl hgE⟩
  rw [peek_keep hl (x := sy.Player_State) (by simp)]
  exact hend

/-- the last counted frame up to `t` that begins on the ground: from it to `t` he is in the air -/
theorem last_ground {fm : Nat → Machine} (h1 : peek (fm 1) sy.Player_State = 0) : ∀ t, 1 ≤ t →
    ∃ t0, 1 ≤ t0 ∧ t0 ≤ t ∧ peek (fm t0) sy.Player_State = 0 ∧ ∀ s, t0 < s → s ≤ t → peek (fm s) sy.Player_State ≠ 0 := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hg : peek (fm (t + 1)) sy.Player_State = 0
    · exact ⟨t + 1, by omega, Nat.le_refl _, hg, fun s h2 h3 => by omega⟩
    · by_cases ht1 : t = 0
      · subst ht1; exact absurd h1 hg
      · obtain ⟨t0, a1, a2, a3, a4⟩ := ih (by omega)
        refine ⟨t0, a1, by omega, a3, fun s h2 h3 => ?_⟩
        by_cases hs : s ≤ t
        · exact a4 s h2 hs
        · rw [show s = t + 1 by omega]; exact hg

/-- **The length of a jump, up to the horizon** (the old field `jump`), with the ground's height at the landing: a jump started on the counted frame `t ≤ N` (`t < E`)
lands `n` counted frames later, `n` between the lengths `lens` for the speed when the frame begins, by the counted frame `min (N + 1) E`; the frames between begin in the
air, and the counted frame `t + n` begins on the ground at the ground's height. Or the counted frames from `t + 1` to `min (N + 1) E` all begin in the air, and their
number is below the longest length. The frames follow the vertical model (`hV`), and the search of `OpenJump` covers every jump of the model (`OpenJump.lands_by`). `hh`
gives the stored speed `|v|`, `hv` the speed at most the top speed, `hG` the ground's height at the takeoff. -/
theorem Real.jumpV {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (C : Checks sy m0 lens Zb v g) (hV : VertOK sy m0 N E L.fm L.inp)
    {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ N) (h3 : t < E) (hh : Held sy v (L.fm t)) (hv : (sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs ≤ TopSpeed.top sy)
    (hg : peek (L.fm t) sy.Player_State = 0) (hG : OpenFlat.GroundAt sy m0 (L.fm t)) (hj : (inOf sy L.fm L.inp t).jump = true) :
    (∃ n, 1 ≤ n ∧ t + n ≤ min (N + 1) E ∧ (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 ≤ n ∧
      n ≤ (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).2 ∧
      (∀ d, 1 ≤ d → d < n → peek (L.fm (t + d)) sy.Player_State ≠ 0) ∧ peek (L.fm (t + n)) sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 (L.fm (t + n))) ∨
    ((∀ d, 1 ≤ d → t + d ≤ min (N + 1) E → peek (L.fm (t + d)) sy.Player_State ≠ 0) ∧
      min (N + 1) E - t < (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).2) := by
  have hab : (peek (L.fm t) sy.Player_XSpeedAbsolute).toNat ≤ TopSpeed.top sy := by
    rw [hh.1, SurfaceFrames.absB_natAbs]; exact hv
  generalize hV' : (sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs = V at hv ⊢
  have habs : peek (L.fm t) sy.Player_XSpeedAbsolute = V.toUInt8 := by
    rw [hh.1, ← hV', ← SurfaceFrames.absB_natAbs]
    simp
  let u : Nat → Jump.VS := fun e => VertModel.vsOf sy (L.fm (t + e))
  let a : Nat → Bool := fun e => aOf sy L.fm L.inp (t + e)
  let pre : Nat → UInt8 := fun e => if e = 1 then (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (OpenJump.ground0 (peek m0 sy.Player_Y_Position)) true V.toUInt8).y
    else (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (u (e - 1)) (a (e - 1)) 0).y
  let ph : Nat → UInt8 := fun e => if e = 1 then OpenJump.hiAfter sy m0 (FrameModel.ctrlStack sy m0) (OpenJump.ground0 (peek m0 sy.Player_Y_Position)) true V.toUInt8
    else OpenJump.hiAfter sy m0 (FrameModel.ctrlStack sy m0) (u (e - 1)) (a (e - 1)) 0
  let P : Nat → Prop := fun e => peek (L.fm (t + e)) sy.Player_Y_HighPos = 1 ∧ OpenAir.HaltM sy (L.fm (t + e))
  -- the takeoff
  have hT := hV t h1 h2 h3 ⟨fun _ => ⟨hj, hG, hab⟩, fun h0 => absurd hg h0⟩
  -- the frames in the air follow the model
  have hstep : ∀ e, 1 ≤ e → e < min (N + 1) E - t → (∀ e', 1 ≤ e' → e' ≤ e → (u e').st ≠ 0) → P e →
      (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (u e) (a e) 0).y.toNat < (peek m0 sy.Player_Y_Position).toNat + sy.LandDepth.toUInt8.toNat ∧
        OpenJump.hiAfter sy m0 (FrameModel.ctrlStack sy m0) (u e) (a e) 0 = 1 →
      P (e + 1) ∧ pre (e + 1) = (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (u e) (a e) 0).y ∧
      ph (e + 1) = OpenJump.hiAfter sy m0 (FrameModel.ctrlStack sy m0) (u e) (a e) 0 ∧
      u (e + 1) = OpenJump.land (peek m0 sy.Player_Y_Position) (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (u e) (a e) 0) := by
    intro e e1 e2 hair hPe hb
    have ha : peek (L.fm (t + e)) sy.Player_State ≠ 0 := hair e e1 (Nat.le_refl _)
    have hS := hV (t + e) (by omega) (by omega) (by omega) ⟨fun h0 => absurd h0 ha, fun _ => ⟨hPe.1, hPe.2, hb⟩⟩
    refine ⟨?_, by simp only [pre, show e + 1 ≠ 1 by omega, if_false, show e + 1 - 1 = e by omega],
      by simp only [ph, show e + 1 ≠ 1 by omega, if_false, show e + 1 - 1 = e by omega], ?_⟩
    · show peek (L.fm (t + (e + 1))) sy.Player_Y_HighPos = 1 ∧ OpenAir.HaltM sy (L.fm (t + (e + 1)))
      rw [show t + (e + 1) = t + e + 1 by omega]
      exact ⟨hS.1, hS.2.1⟩
    · show VertModel.vsOf sy (L.fm (t + (e + 1))) = _
      rw [show t + (e + 1) = t + e + 1 by omega, hS.2.2.2 ha]
      rfl
  rcases OpenJump.lands_by C.jumps (u := u) (a := a) (pre := pre) (ph := ph) (P := P) (v := V) hv (h := min (N + 1) E - t) (by omega)
      ⟨by simp [pre], by simp [ph], by
        show VertModel.vsOf sy (L.fm (t + 1)) = _
        rw [hT.2.2.1 hg, habs]
        rfl⟩ ⟨hT.1, hT.2.1⟩ hstep with
    ⟨n, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ | ⟨hair, hlt⟩
  · exact Or.inl ⟨n, n1, by omega, n3, n4, fun d d1 d2 => n5 d d1 d2, n6, n7, n10.1, n8, n9⟩
  · exact Or.inr ⟨fun d d1 d2 => hair d d1 (by omega), hlt⟩

/-- **Every counted frame of the first `N` that begins on the ground begins at the ground's height** (the old field `ground`): by induction on the counted frames. The
counted frame 1 is at the ground's height (`hG₁`, from the press of Start on the title). After a counted frame that begins on the ground with no jump it is `Real.flat`.
After a counted frame in the air or with a jump, the last counted frame on the ground before it is a takeoff (a frame on the ground with no jump stays on the ground:
`Real.flat`), and the jump lands at the ground's height (`Real.jumpV`: the frame is before the horizon, so the jump has landed by it). `hh`, `hm` and `hv` are what each
counted frame holds when it begins (`Held`, the player's state 0, 1 or 2 and no jumpspring, the speed at most the top speed). -/
theorem Real.ground_all {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true)
    (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (C : Checks sy m0 lens Zb v g) (hM : OpenMap.mapCheck sy m0 = true)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (hm₁ : OpenMap.MapAt sy m0 (S.seq 1)) (O : Real sy m0 lens N E L)
    (hV : VertOK sy m0 N E L.fm L.inp)
    (hh : ∀ t, 1 ≤ t → t ≤ N → t < E → Held sy v (L.fm t)) (hm : StSpring sy L N E)
    (hv : ∀ t, 1 ≤ t → t ≤ N → t < E → (sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs ≤ TopSpeed.top sy)
    (hg₁ : peek (L.fm 1) sy.Player_State = 0) (hG₁ : OpenFlat.GroundAt sy m0 (L.fm 1)) :
    ∀ t, 1 ≤ t → t ≤ N → t < E → peek (L.fm t) sy.Player_State = 0 → OpenFlat.GroundAt sy m0 (L.fm t) := by
  have key : ∀ d, 1 + d ≤ N → 1 + d < E → peek (L.fm (1 + d)) sy.Player_State = 0 → OpenFlat.GroundAt sy m0 (L.fm (1 + d)) := by
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      intro hd hE hst
      cases d with
      | zero => exact hG₁
      | succ d =>
        rw [show 1 + (d + 1) = 1 + d + 1 by omega] at hst ⊢
        by_cases hflat : peek (L.fm (1 + d)) sy.Player_State = 0 ∧ (inOf sy L.fm L.inp (1 + d)).jump = false
        · exact (O.flat hc hk hp C hM hs₁ hm₁ (t := 1 + d) (by omega) (by omega) (by omega) (hh (1 + d) (by omega) (by omega) (by omega))
            (hm (1 + d) (by omega) (by omega) (by omega)).2 hflat.1 (ih d (by omega) (by omega) (by omega) hflat.1) hflat.2).2
        · -- the last counted frame on the ground up to `1 + d` is a takeoff
          obtain ⟨t0, a1, a2, a3, a4⟩ := last_ground hg₁ (1 + d) (by omega)
          have hG0 : OpenFlat.GroundAt sy m0 (L.fm t0) := by
            have := ih (t0 - 1) (by omega) (by omega) (by omega) (by rw [show 1 + (t0 - 1) = t0 by omega]; exact a3)
            rwa [show 1 + (t0 - 1) = t0 by omega] at this
          have hj0 : (inOf sy L.fm L.inp t0).jump = true := by
            cases hj : (inOf sy L.fm L.inp t0).jump
            · exfalso
              by_cases he : t0 = 1 + d
              · subst he; exact hflat ⟨a3, hj⟩
              · have := (O.flat hc hk hp C hM hs₁ hm₁ (t := t0) a1 (by omega) (by omega) (hh t0 a1 (by omega) (by omega))
                  (hm t0 a1 (by omega) (by omega)).2 a3 hG0 hj).1
                exact a4 (t0 + 1) (by omega) (by omega) this
            · rfl
          rcases Real.jumpV C hV a1 (by omega) (by omega) (hh t0 a1 (by omega) (by omega)) (hv t0 a1 (by omega) (by omega)) a3 hG0 hj0 with
            ⟨n, n1, _, _, _, n4, n5, n6⟩ | ⟨hair, _⟩
          · -- the landing is the counted frame `1 + d + 1`
            have hn : t0 + n = 1 + d + 1 := by
              rcases Nat.lt_trichotomy (t0 + n) (1 + d + 1) with h | h | h
              · exact absurd n5 (a4 (t0 + n) (by omega) (by omega))
              · exact h
              · exact absurd hst (by
                  have := n4 (1 + d + 1 - t0) (by omega) (by omega)
                  rwa [show t0 + (1 + d + 1 - t0) = 1 + d + 1 by omega] at this)
            rw [← hn]; exact n6
          · exfalso
            have := hair (1 + d + 1 - t0) (by omega) (by omega)
            rw [show t0 + (1 + d + 1 - t0) = 1 + d + 1 by omega] at this
            exact this hst
  intro t h1 h2 h3 hst
  have := key (t - 1) (by omega) (by omega) (by rw [show 1 + (t - 1) = t by omega]; exact hst)
  rwa [show 1 + (t - 1) = t by omega] at this

/-! ### The frames left in the air, for the model

The model needs the frames left in the air only up to the counted frame `N + 1` (and before `E`): the horizon `H = min (N + 1) E`. A jump that has not landed by `H` is
given as many frames as it has left up to `H`, and at least `L_tap − 1` after the takeoff (`airT`); its length beyond `H` is not needed. -/

theorem landFrom_none {p : Nat → Bool} : ∀ (t d : Nat), (∀ j, t ≤ j → j < t + d → p j = false) → landFrom p t d = t + d
  | t, 0, _ => rfl
  | t, d + 1, h => by
    rw [landFrom_succ (h t (Nat.le_refl _) (by omega)), landFrom_none (t + 1) d (fun j h1 h2 => h j (by omega) (by omega))]
    omega

/-- the two lengths of a jump for the speed of the counted frame `t` -/
def lensAt (sy : Syms) (lens : Lens) (fm : Nat → Machine) (t : Nat) : Nat × Nat := lens[(sbyte (peek (fm t) sy.Player_X_Speed)).natAbs]!

/-- **The frames left in the air when the counted frame `t` begins, for the model**, with the horizon `H`: 0 on the ground; after a takeoff at `t − 1`, the frames to the
first counted frame on the ground if it comes by `H`, else `max (L_tap − 1) (H − t)`; in the air after the air, one less than before -/
def airT (sy : Syms) (lens : Lens) (fm : Nat → Machine) (H : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 =>
    if groundB sy fm (t + 1) then 0
    else if groundB sy fm t then
      (if groundB sy fm (landFrom (groundB sy fm) (t + 1) (H - (t + 1))) then landFrom (groundB sy fm) (t + 1) (H - (t + 1)) - (t + 1)
       else max ((lensAt sy lens fm t).1 - 1) (H - t - 1))
    else airT sy lens fm H t - 1

theorem airT_ground {fm : Nat → Machine} {H t : Nat} (h1 : 1 ≤ t) (h : peek (fm t) sy.Player_State = 0) : airT sy lens fm H t = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp [airT, groundB, h]

theorem airT_air {fm : Nat → Machine} {H t : Nat} (h0 : peek (fm t) sy.Player_State ≠ 0) (h1 : peek (fm (t + 1)) sy.Player_State ≠ 0) :
    airT sy lens fm H (t + 1) = airT sy lens fm H t - 1 := by
  simp [airT, groundB, h0, h1]

theorem airT_take {fm : Nat → Machine} {H t : Nat} (h0 : peek (fm t) sy.Player_State = 0) (h1 : peek (fm (t + 1)) sy.Player_State ≠ 0) :
    airT sy lens fm H (t + 1) = if groundB sy fm (landFrom (groundB sy fm) (t + 1) (H - (t + 1))) then landFrom (groundB sy fm) (t + 1) (H - (t + 1)) - (t + 1)
      else max ((lensAt sy lens fm t).1 - 1) (H - t - 1) := by
  simp [airT, groundB, h0, h1]

/-- in the air after the takeoff at `t0`, one frame less at each counted frame -/
theorem airT_run {fm : Nat → Machine} {H t0 : Nat} : ∀ e, 1 ≤ e → (∀ e', 1 ≤ e' → e' ≤ e → peek (fm (t0 + e')) sy.Player_State ≠ 0) →
    airT sy lens fm H (t0 + e) = airT sy lens fm H (t0 + 1) - (e - 1)
  | 0, h, _ => absurd h (by omega)
  | e + 1, _, hair => by
    by_cases he : e = 0
    · subst he; rfl
    · rw [show t0 + (e + 1) = t0 + e + 1 by omega, airT_air (hair e (by omega) (by omega)) (by rw [show t0 + e + 1 = t0 + (e + 1) by omega]; exact hair (e + 1) (by omega) (Nat.le_refl _)),
        airT_run e (by omega) (fun e' a1 a2 => hair e' a1 (by omega))]
      omega

/-- **The frames left in the air after a takeoff**: the value at the counted frame after a takeoff at `t`, in the two cases of `Real.jumpV` -/
theorem airT_after {fm : Nat → Machine} {H t n : Nat} (hg : peek (fm t) sy.Player_State = 0) (h1 : 1 ≤ n) (hn : t + n ≤ H)
    (hair : ∀ d, 1 ≤ d → d < n → peek (fm (t + d)) sy.Player_State ≠ 0) (hl : peek (fm (t + n)) sy.Player_State = 0) : airT sy lens fm H (t + 1) = n - 1 := by
  by_cases hn1 : n = 1
  · subst hn1
    exact airT_ground (by omega) hl
  · have ha1 : peek (fm (t + 1)) sy.Player_State ≠ 0 := hair 1 (by omega) (by omega)
    have e := landFrom_at (p := groundB sy fm) (n - 1) (t + 1) (H - (t + 1))
      (fun j h2 h3 => by
        have := hair (j - t) (by omega) (by omega)
        rw [show t + (j - t) = j by omega] at this
        simp [groundB, this])
      (by rw [show t + 1 + (n - 1) = t + n by omega]; simp [groundB, hl]) (by omega)
    rw [airT_take hg ha1, e, show t + 1 + (n - 1) = t + n by omega]
    simp [groundB, hl]
    omega

theorem airT_after_air {fm : Nat → Machine} {H t : Nat} (hg : peek (fm t) sy.Player_State = 0) (htH : t < H)
    (hair : ∀ d, 1 ≤ d → t + d ≤ H → peek (fm (t + d)) sy.Player_State ≠ 0) : airT sy lens fm H (t + 1) = max ((lensAt sy lens fm t).1 - 1) (H - t - 1) := by
  have ha1 : peek (fm (t + 1)) sy.Player_State ≠ 0 := hair 1 (by omega) (by omega)
  have e := landFrom_none (p := groundB sy fm) (t + 1) (H - (t + 1)) (fun j h2 h3 => by
    have := hair (j - t) (by omega) (by omega)
    rw [show t + (j - t) = j by omega] at this
    simp [groundB, this])
  have hH : groundB sy fm H = false := by
    have := hair (H - t) (by omega) (by omega)
    rw [show t + (H - t) = H by omega] at this
    simp [groundB, this]
  rw [airT_take hg ha1, e, show t + 1 + (H - (t + 1)) = H by omega, hH]
  rfl

/-! ### The vertical model on real frames -/

theorem vsA_lagI {x : UInt16} (hx : x ∈ OpenAir.vsA sy) : LagFrames.I x ∈ LagFrames.lagI sy := by
  simp only [OpenAir.vsA, OpenFlat.vertA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [LagFrames.lagI, LagFrames.vfpI, LagFrames.ctlI, LagFrames.moreI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hx with (hx | hx | hx | hx) | hx | hx | hx | hx | hx | hx | hx <;> simp [hx]

theorem ab_lagI : LagFrames.I sy.A_B_Buttons ∈ LagFrames.lagI sy ∧ LagFrames.I sy.PreviousA_B_Buttons ∈ LagFrames.lagI sy := by
  simp [LagFrames.lagI, LagFrames.vfpI, LagFrames.ctlI, LagFrames.moreI]

theorem vsOf_of_vsA {m m' : Machine} (h : ∀ x ∈ OpenAir.vsA sy, peek m' x = peek m x) : VertModel.vsOf sy m' = VertModel.vsOf sy m := by
  unfold VertModel.vsOf
  rw [h _ (by simp [OpenAir.vsA, OpenFlat.vertA]), h _ (by simp [OpenAir.vsA, OpenFlat.vertA]), h _ (by simp [OpenAir.vsA, OpenFlat.vertA]),
    h _ (by simp [OpenAir.vsA]), h _ (by simp [OpenAir.vsA]), h _ (by simp [OpenAir.vsA]), h _ (by simp [OpenAir.vsA]), h _ (by simp [OpenAir.vsA]),
    h _ (by simp [OpenAir.vsA])]

theorem haltM_of_vsA {m m' : Machine} (h : ∀ x ∈ OpenAir.vsA sy, peek m' x = peek m x) (hm : OpenAir.HaltM sy m) : OpenAir.HaltM sy m' := by
  unfold OpenAir.HaltM at hm ⊢
  rw [h _ (by simp [OpenAir.vsA]), h _ (by simp [OpenAir.vsA])]
  exact hm

theorem vsOf_keepA {m R : Machine} (h : ∀ x ∈ CtrlKeep.keepA sy, peek R x = peek m x) : VertModel.vsOf sy R = VertModel.vsOf sy m := by
  unfold VertModel.vsOf
  rw [h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]),
    h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]),
    h _ (by simp [CtrlKeep.keepA])]

/-- **Bit 7 of A and B of the frame before is that of A and B when each counted frame begins** (`PrevKeep.PrevOK`): at the counted frame 1 (`hpv₁`); each counted frame
keeps it (`GuardE.prev_endE`, the walk of part e: `CleanK` of `guardE` and no store by address to the routine, the mode or the task, the fields `cleanK` and `noStore`); the
frames not counted keep both bytes (`PipeFrames.lags_keepI`). -/
theorem Real.prevAll {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true)
    (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (C : Checks sy m0 lens Zb v g)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (O : Real sy m0 lens N E L)
    (hh : ∀ t, 1 ≤ t → t ≤ N → t < E → Held sy v (L.fm t)) (hpv₁ : PrevKeep.PrevOK sy (L.fm 1)) :
    ∀ t, 1 ≤ t → t ≤ N + 1 → t ≤ E → PrevKeep.PrevOK sy (L.fm t) := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
    intro h1 h2 h3
    by_cases ht : t = 0
    · subst ht; exact hpv₁
    · have hpv := ih (by omega) (by omega) (by omega)
      have he := GuardE.prev_endE C.ctrl C.prev (startK_of hc hk hp hs₁ (by omega) (by omega)) (O.cleanK t (by omega) (by omega) (by omega))
        (O.noStore t (by omega) (by omega) (by omega)) (hh t (by omega) (by omega) (by omega)).2.2 hpv
      have hl := PipeFrames.lags_keepI hc hk hp L hs₁ t (by omega)
      unfold PrevKeep.PrevOK at he ⊢
      rw [show peek (L.fm (t + 1)) sy.PreviousA_B_Buttons = peek (frame (L.fm t) (L.inp t)) sy.PreviousA_B_Buttons from hl _ ab_lagI.2,
        show peek (L.fm (t + 1)) sy.A_B_Buttons = peek (frame (L.fm t) (L.inp t)) sy.A_B_Buttons from hl _ ab_lagI.1]
      exact he

/-- **Each counted frame from 1 to `N` that is a takeoff or in the air follows the vertical model** (the old field `vert`). A takeoff: the walk of `OpenAir` from the
player's routine computes every vertical byte (`OpenAir.take_real`). In the air: the movement routine follows `vstep` up to `Q` (`OpenVert.vert_airH`, with the halt relation
and A of the frame before, `Real.prevAll`, at the player's routine), and from `Q` the walk of `OpenAir` keeps the vertical bytes up to the return of the collision routine,
or lands him (`OpenAir.air_real`); the walk comes to `Q` once, so the two arrivals are one. After the return the bytes do not change (`afterV`), and the frames not counted
keep them (`PipeFrames.lags_keepI`). The flag that disables the collision routine is 0 when each frame begins (`OpenMap`). `hc`, `hk`, `hp`, `C`, `hM` are checks on the
ROM, `hs₁`, `hm₁` the start of frame 1. -/
theorem Real.vertOK {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true)
    (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (C : Checks sy m0 lens Zb v g) (hM : OpenMap.mapCheck sy m0 = true)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (hm₁ : OpenMap.MapAt sy m0 (S.seq 1)) (O : Real sy m0 lens N E L)
    (hh : ∀ t, 1 ≤ t → t ≤ N → t < E → Held sy v (L.fm t)) (hm : StSpring sy L N E) (hpv₁ : PrevKeep.PrevOK sy (L.fm 1)) :
    VertOK sy m0 N E L.fm L.inp := by
  intro t h1 h2 h3 hpre
  have hpvt := O.prevAll hc hk hp C hs₁ hh hpv₁ t h1 (by omega) (by omega)
  have hA := OpenAir.airFacts_of C.air
  have hix : L.ix t < L.ix E := Nat.lt_of_lt_of_le (PipeFrames.ixP_lt g S L.dP t) (L.ix_mono h3)
  have hixN : L.ix t ≤ L.ix N := L.ix_mono h2
  have h1ix : 1 ≤ L.ix t := L.one_le_ix h1
  have hmap : ∀ k, OpenMap.MapOK sy m0 (trace (L.fm t) (L.inp t) k) := fun k => O.map (L.ix t) h1ix hixN hix k
  have hsG : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (L.fm t) := L.startAt hc hk hp hs₁ h1 (Nat.le_of_lt h3)
  have hsK : FrameKeep.StartK sy m0 (L.fm t) := startK_of hc hk hp hs₁ h1 (Nat.le_of_lt h3)
  have hmA : OpenMap.MapAt sy m0 (L.fm t) :=
    OpenMap.Lags.mapAt hc hp hM L hs₁ hm₁ (b := L.ix t) (Nat.le_of_lt hix)
      (fun n a1 a2 k => O.map n a1 (Nat.le_trans (Nat.le_of_lt a2) hixN) (Nat.lt_of_lt_of_le a2 (Nat.le_of_lt hix)) k) (L.ix t) h1ix (Nat.le_refl _)
  have hclF : ∀ k, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k) :=
    fun k => FrameKeep.cleanK_of_E (O.cleanK t h1 h2 h3 k)
  have hcl : ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k) := fun k => FrameKeep.cleanK_of_F (hclF k)
  have hcq : ∀ k, FrameKeep.CleanK (OpenFlat.guardQ sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k) := fun k => OpenFlat.cleanQ_of (hclF k) (hmap k)
  have hcM : ∀ k, FrameKeep.CleanK (OpenMap.guardM sy m0) StartRun.noSpot.store (trace (L.fm t) (L.inp t) k) :=
    fun k => OpenMap.cleanK_of (L.cleanG (L.ix t) h1ix hix k) (hmap k)
  have hrM : ∀ k, OpenMap.RdOK (OpenMap.rdOf sy m0) (trace (L.fm t) (L.inp t) k) := fun k => OpenMap.rdOK_of (hmap k)
  have hr : ∀ k, (trace (L.fm t) (L.inp t) k).frame = (L.fm t).frame → OpenFlat.RdOK1 (OpenFlat.rdOf sy m0) (trace (L.fm t) (L.inp t) k) := fun k hf =>
    OpenFlat.rdOK1_of (hmap k) (fun hpc hn => OpenMap.map_reads hM (OpenMap.start_M hsG) hmA.1 hmA.2 hcM hrM hf hpc hn)
  have hu : CtrlKeep.Unpaused sy m0 (frame (L.fm t) (L.inp t)) := by
    show (frame (L.fm t) (L.inp t)).ram.get! (CtrlKeep.pauseI sy m0) &&& 1 = 0
    rw [C.pause, ← S.next]
    exact L.unpaused h1 (by omega)
  have hdc : (L.fm t).ram.get! (OpenMap.dcdI sy m0) = 0 := by
    have := hmA.1 (OpenMap.dcdI sy m0, 0xFF, 0) (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)))
    rw [FrameKeep.and_ff, FrameKeep.and_ff] at this
    exact this
  have hl := PipeFrames.lags_keepI hc hk hp L hs₁ t h3
  -- the bytes of the next counted frame from those at a return of the collision routine
  have nxt : ∀ k₂, CtrlKeep.arrAt sy (L.fm t) (L.inp t) ≤ k₂ → (trace (L.fm t) (L.inp t) k₂).pc = OpenFlat.collRet sy m0 →
      ∀ x ∈ OpenAir.vsA sy, peek (L.fm (t + 1)) x = peek (trace (L.fm t) (L.inp t) k₂) x := fun k₂ e1 e2 x hx =>
    (hl _ (vsA_lagI hx)).trans (O.afterV t h1 h2 h3 k₂ e1 e2 x hx)
  obtain ⟨hab, hbits, hv⟩ := hh t h1 h2 h3
  obtain ⟨hst, hspr⟩ := hm t h1 h2 h3
  by_cases hg : peek (L.fm t) sy.Player_State = 0
  · -- a takeoff
    obtain ⟨hj, hG, habs⟩ := hpre.1 hg
    have hF : OpenFlat.flatCheckWith sy m0 v (OpenFlat.cfgBOf sy m0 v (OpenFlat.searchB sy m0 v)) (OpenFlat.cfgCOf sy m0 v (OpenFlat.searchB sy m0 v)) = true := C.flat
    obtain ⟨k₂, J, e1, _, _, _, e3, e4, e5, e6⟩ := OpenAir.take_real C.ctrl hA (OpenFlat.flatCheck_parts hF).2.2.2 hsK hcl hcq hr hu hv hspr hg hG habs hj hdc
    have hn := nxt k₂ e1 e3
    refine ⟨by rw [hn _ (by simp [OpenAir.vsA, OpenFlat.vertA])]; exact e5, ?_, fun _ => ?_, fun h0 => absurd hg h0⟩
    · exact haltM_of_vsA hn (fun _ => e6)
    · rw [vsOf_of_vsA hn, e4]
      unfold OpenAir.expT
      simp
  · -- in the air
    obtain ⟨hhi, hhalt, hnext⟩ := hpre.2 hg
    have hst12 : peek (L.fm t) sy.Player_State = 1 ∨ peek (L.fm t) sy.Player_State = 2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with h | h | h
      · exact absurd h hg
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨k₁, k₂, J, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := OpenAir.air_real C.ctrl hA hsK hcl hcq hr hu hv hspr hst12 hhalt hdc
    -- the movement routine, from the player's routine to `Q`
    obtain ⟨c1, c2, c3⟩ := CtrlKeep.arrive_at C.ctrl hsK hcl hu
    have A := CtrlKeep.ctrl_keep C.ctrl hsK hcl c1 c2 c3
    have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t))) x = peek (L.fm t) x := A.keep
    have hF : OpenFlat.flatCheckWith sy m0 v (OpenFlat.cfgBOf sy m0 v (OpenFlat.searchB sy m0 v)) (OpenFlat.cfgCOf sy m0 v (OpenFlat.searchB sy m0 v)) = true := C.flat
    have hhiR := OpenFlat.high_at_cut (OpenFlat.flatCheck_parts hF).2.2.2 hsK hcl c1 c2 c3
    have hAV : VertAir.AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t))) := by
      refine ⟨A.good, c1, A.s, A.eng, ?_, ?_, ?_, ?_, ?_⟩
      · rw [kp _ (by simp [CtrlKeep.keepA]), hv.1]; exact C.v3
      · rw [kp _ (by simp [CtrlKeep.keepA])]; exact hst
      · rw [kp _ (by simp [CtrlKeep.keepA])]; exact hspr
      · rw [kp _ (by simp [CtrlKeep.keepA]), hv.2.1]
      · rw [kp _ (by simp [CtrlKeep.keepA]), hv.2.2]
    obtain ⟨k, _, _, hpcQ, _, hvs, hstQ, hIF, hhiQ⟩ := OpenVert.vert_airH C.vh hAV (by rw [hhiR]; exact hhi)
      (by rw [kp _ (by simp [CtrlKeep.keepA])]; exact hst12)
      (fun h => by
        rw [kp sy.DiffToHaltJump (by simp [CtrlKeep.keepA])]
        exact hhalt (by rw [← kp sy.Player_State (by simp [CtrlKeep.keepA])]; exact h))
      (by rw [kp _ (by simp [CtrlKeep.keepA]), kp _ (by simp [CtrlKeep.keepA])]; exact hpvt)
    have hT := FrameModel.trace_inFrame C.idle c2 hIF (fun n hn => (hcl n).time hn) k (Nat.le_refl k)
    rw [← hT.1] at hpcQ hvs hhiQ
    -- the arrival at `Q` of the movement routine is the walk's
    have hkJ : CtrlKeep.arrAt sy (L.fm t) (L.inp t) + k < J := by
      rcases Nat.lt_or_ge (CtrlKeep.arrAt sy (L.fm t) (L.inp t) + k) J with h | h
      · exact h
      · exfalso
        have hs : ((trace (L.fm t) (L.inp t) J).frame ≥ (L.fm t).frame + 1 || (trace (L.fm t) (L.inp t) J).halted) = true := by simp [a5]
        have e := PipeEntryRule.trace_stop hs (CtrlKeep.arrAt sy (L.fm t) (L.inp t) + k - J)
        rw [show J + (CtrlKeep.arrAt sy (L.fm t) (L.inp t) + k - J) = CtrlKeep.arrAt sy (L.fm t) (L.inp t) + k by omega] at e
        have := hT.2
        rw [e, a5] at this
        omega
    have hk₁ : CtrlKeep.arrAt sy (L.fm t) (L.inp t) + k = k₁ := a8 _ (by omega) hkJ hpcQ
    rw [hk₁] at hvs hhiQ
    have hvsR : VertModel.vsOf sy (trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t))) = VertModel.vsOf sy (L.fm t) := vsOf_keepA kp
    rw [hvsR] at hvs hhiQ hstQ
    have hok : OpenAir.Ok1 sy (OpenAir.ctxOf sy m0 v) (trace (L.fm t) (L.inp t) k₁) := by
      refine ⟨?_, ?_, ?_⟩
      · show (VertModel.vsOf sy (trace (L.fm t) (L.inp t) k₁)).y.toNat < _
        rw [hvs]; exact hnext.1
      · rw [hhiQ]; exact hnext.2
      · show (VertModel.vsOf sy (trace (L.fm t) (L.inp t) k₁)).st = 1 ∨ (VertModel.vsOf sy (trace (L.fm t) (L.inp t) k₁)).st = 2
        rw [hvs]; exact hstQ
    obtain ⟨b1, b2, b3⟩ := a10 hok
    have hn := nxt k₂ (by omega) a9
    refine ⟨by rw [hn _ (by simp [OpenAir.vsA, OpenFlat.vertA])]; exact b2, haltM_of_vsA hn b3, fun h0 => absurd h0 hg, fun _ => ?_⟩
    rw [vsOf_of_vsA hn, b1, hvs]
    rfl

/-- **Each of the first `N` counted frames is a step of the opening's model, with the position modulo `2²⁴`**, from the conditions on single frames (`Real`). The frames
left in the air are read from the machines up to the horizon `min (N + 1) E` (`airT`). At control he is on the ground and the frame's start holds `Held` (`h₁`, from the
press of Start on the title). `hc`, `hk`, `hp`, `C` and `hM` are checks on the ROM, `hs₁` and `hm₁` the start of frame 1. -/
def Real.toRunM {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true)
    (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (C : Checks sy m0 lens Zb v g) (hM : OpenMap.mapCheck sy m0 = true)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (hm₁ : OpenMap.MapAt sy m0 (S.seq 1)) (h₁ : Held sy v (L.fm 1)) (hg₁ : peek (L.fm 1) sy.Player_State = 0)
    (hG₁ : OpenFlat.GroundAt sy m0 (L.fm 1)) (hv : ∀ t, 1 ≤ t → t ≤ E → (sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs ≤ TopSpeed.top sy)
    (O : Real sy m0 lens N E L) (hm : StSpring sy L N E) (hpv₁ : PrevKeep.PrevOK sy (L.fm 1)) : OpenRunM sy m0 lens N E L.fm := by
  -- the frames not counted after the counted frame `t`
  have lk : ∀ t, 1 ≤ t → t < E → ∀ b ∈ LagFrames.lagI sy, (L.fm (t + 1)).ram.get! b = (frame (L.fm t) (L.inp t)).ram.get! b :=
    fun t _ h2 => PipeFrames.lags_keepI hc hk hp L hs₁ t h2
  -- `Held` at each counted frame, by induction
  have held : ∀ d, d ≤ N → 1 + d ≤ E → Held sy v (L.fm (1 + d)) := by
    intro d
    induction d with
    | zero => exact fun _ _ => h₁
    | succ d ih =>
      intro hd hE
      have hh := ih (by omega) (by omega)
      have fs := O.frame_step C (t := 1 + d) (by omega) (by omega) (by omega) (startK_of hc hk hp hs₁ (by omega) (by omega)) hh (hm (1 + d) (by omega) (by omega) (by omega))
      rw [show 1 + (d + 1) = 1 + d + 1 by omega]
      exact (keep_parts (lk (1 + d) (by omega) (by omega))).2.2 fs.2.2.1
  have heldT : ∀ t, 1 ≤ t → t ≤ N → t < E → Held sy v (L.fm t) := fun t h1 h2 h3 => by
    have := held (t - 1) (by omega) (by omega)
    rwa [show 1 + (t - 1) = t by omega] at this
  -- the vertical model on the counted frames
  have hV : VertOK sy m0 N E L.fm L.inp := O.vertOK hc hk hp C hM hs₁ hm₁ heldT hm hpv₁
  -- on the ground at the ground's height, at each counted frame on the ground
  have gr := O.ground_all hc hk hp C hM hs₁ hm₁ hV heldT hm (fun t h1 _ h3 => hv t h1 (Nat.le_of_lt h3)) hg₁ hG₁
  -- the last counted frame on the ground before a frame in the air is a takeoff, and what `Real.jumpV` says of it
  have takeoff : ∀ t0, 1 ≤ t0 → t0 ≤ N → t0 < E → peek (L.fm t0) sy.Player_State = 0 → peek (L.fm (t0 + 1)) sy.Player_State ≠ 0 → t0 + 1 ≤ N →
      (inOf sy L.fm L.inp t0).jump = true := by
    intro t0 a1 a2 a3 a4 a5 a6
    cases hj : (inOf sy L.fm L.inp t0).jump
    · exfalso
      exact a5 (O.flat hc hk hp C hM hs₁ hm₁ a1 a2 a3 (heldT t0 a1 a2 a3) (hm t0 a1 a2 a3).2 a4 (gr t0 a1 a2 a3 a4) hj).1
    · rfl
  -- in the air: at least one frame left, and one less at the next counted frame
  have air_facts : ∀ t, 1 ≤ t → t ≤ N → t < E → peek (L.fm t) sy.Player_State ≠ 0 →
      1 ≤ airT sy lens L.fm (min (N + 1) E) t ∧ airT sy lens L.fm (min (N + 1) E) (t + 1) = airT sy lens L.fm (min (N + 1) E) t - 1 := by
    intro t h1 h2 h3 hst
    obtain ⟨t0, a1, a2, a3, a4⟩ := last_ground hg₁ t h1
    have ht0 : t0 < t := by
      rcases Nat.lt_or_ge t0 t with h | h
      · exact h
      · exact absurd (show t0 = t by omega ▸ a3) hst
    have hn1 : peek (L.fm (t0 + 1)) sy.Player_State ≠ 0 := a4 (t0 + 1) (by omega) (by omega)
    have hj0 := takeoff t0 a1 (by omega) (by omega) a3 hn1 (by omega)
    have hrun := airT_run (lens := lens) (H := min (N + 1) E) (fm := L.fm) (t0 := t0) (t - t0) (by omega) (fun e' b1 b2 => a4 (t0 + e') (by omega) (by omega))
    rw [show t0 + (t - t0) = t by omega] at hrun
    rcases Real.jumpV C hV a1 (by omega) (by omega) (heldT t0 a1 (by omega) (by omega)) (hv t0 a1 (by omega)) a3 (gr t0 a1 (by omega) (by omega) a3) hj0 with
      ⟨n, n1, nH, _, _, n4, n5, _⟩ | ⟨hair, _⟩
    · have hlt : t < t0 + n := by
        rcases Nat.lt_or_ge t (t0 + n) with h | h
        · exact h
        · exact absurd n5 (a4 (t0 + n) (by omega) h)
      have hA := airT_after (lens := lens) a3 n1 nH n4 n5
      rw [hA] at hrun
      refine ⟨by omega, ?_⟩
      by_cases he : t + 1 = t0 + n
      · rw [he, airT_ground (by omega) n5, hrun]
        omega
      · have ha' : peek (L.fm (t + 1)) sy.Player_State ≠ 0 := by
          have := n4 (t + 1 - t0) (by omega) (by omega)
          rwa [show t0 + (t + 1 - t0) = t + 1 by omega] at this
        exact airT_air hst ha'
    · have hA := airT_after_air (lens := lens) a3 (by omega) hair
      rw [hA] at hrun
      refine ⟨by omega, ?_⟩
      have ha' : peek (L.fm (t + 1)) sy.Player_State ≠ 0 := by
        have := hair (t + 1 - t0) (by omega) (by omega)
        rwa [show t0 + (t + 1 - t0) = t + 1 by omega] at this
      exact airT_air hst ha'
  refine ⟨airT sy lens L.fm (min (N + 1) E), airT_ground (Nat.le_refl 1) hg₁, ?_⟩
  intro t h1 h2 h3
  have hh := heldT t h1 h2 h3
  obtain ⟨s1, s2, _, s4⟩ := O.frame_step C h1 h2 h3 (startK_of hc hk hp hs₁ h1 (by omega)) hh (hm t h1 h2 h3)
  obtain ⟨k1, k2, _⟩ := keep_parts (v := v) (lk t h1 h3)
  have hmem : inOf sy L.fm L.inp t ∈ Potential.inputs := FrameModel.readIn_mem (FrameModel.joy_of_model C.model) _
  -- the input as the routine reads it, on the ground or in the air
  have est : (inOf sy L.fm L.inp t).st = if peek (L.fm t) sy.Player_State == 0 then 0 else 1 := by
    unfold inOf FrameModel.readIn
    rw [s4]
  have ejp : peek (L.fm t) sy.Player_State ≠ 0 → (inOf sy L.fm L.inp t).jump = false := by
    intro hne
    unfold inOf FrameModel.readIn
    rw [s4]
    simp [hne]
  refine ⟨Potential.norm (inOf sy L.fm L.inp t), FastTakeoff.norm_mem hmem, ?_, ?_, ?_, ?_⟩
  rotate_left 2
  · rw [k1, s1, FastTakeoff.hstep_norm C.norm hmem]
  · rw [k2, k1]; exact s2
  · by_cases hg : peek (L.fm t) sy.Player_State = 0
    · rw [airT_ground h1 hg]
      simp [Opening.valid, FastTakeoff.norm_st, est, hg]
    · obtain ⟨p1, _⟩ := air_facts t h1 h2 h3 hg
      obtain ⟨r, hr⟩ : ∃ r, airT sy lens L.fm (min (N + 1) E) t = r + 1 := ⟨airT sy lens L.fm (min (N + 1) E) t - 1, by omega⟩
      rw [hr]
      simp [Opening.valid, FastTakeoff.norm_st, FastTakeoff.norm_jump, est, hg, ejp hg]
  · by_cases hg : peek (L.fm t) sy.Player_State = 0
    · rw [airT_ground h1 hg]
      cases hj : (inOf sy L.fm L.inp t).jump
      · have hf := (O.flat hc hk hp C hM hs₁ hm₁ h1 h2 h3 hh (hm t h1 h2 h3).2 hg (gr t h1 h2 h3 hg) hj).1
        rw [airT_ground (by omega) hf]
        simp [Opening.modes, FastTakeoff.norm_jump, hj]
      · have hord := OpenJump.lens_ord C.jumps (sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs
        simp only [Opening.modes, FastTakeoff.norm_jump, hj, if_true, beq_self_eq_true]
        rcases Real.jumpV C hV h1 h2 h3 hh (hv t h1 (Nat.le_of_lt h3)) hg (gr t h1 h2 h3 hg) hj with ⟨n, n1, nH, n2, n3, n4, n5, _⟩ | ⟨hair, hlt⟩
        · rw [airT_after (lens := lens) hg n1 nH n4 n5]
          refine List.mem_map.2 ⟨n - 1 - ((lens[(sbyte (startHS sy (L.fm t)).v).natAbs]!).1 - 1), List.mem_range.2 ?_, ?_⟩
          · show n - 1 - ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1) <
              (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).2 + 1 - (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1
            omega
          · show (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1 + (n - 1 - ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1)) = n - 1
            omega
        · rw [airT_after_air (lens := lens) hg (by omega) hair]
          refine List.mem_map.2 ⟨max ((lensAt sy lens L.fm t).1 - 1) (min (N + 1) E - t - 1) - ((lens[(sbyte (startHS sy (L.fm t)).v).natAbs]!).1 - 1),
            List.mem_range.2 ?_, ?_⟩
          · show max ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1) (min (N + 1) E - t - 1) -
                ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1) <
              (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).2 + 1 - (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1
            omega
          · show (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1 + (max ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1)
                (min (N + 1) E - t - 1) - ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1)) =
              max ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1) (min (N + 1) E - t - 1)
            omega
    · obtain ⟨_, p2⟩ := air_facts t h1 h2 h3 hg
      obtain ⟨r, hr⟩ : ∃ r, airT sy lens L.fm (min (N + 1) E) t = r + 1 := ⟨airT sy lens L.fm (min (N + 1) E) t - 1, by have := (air_facts t h1 h2 h3 hg).1; omega⟩
      rw [p2, hr]
      simp [Opening.modes]

/-- **Each of the first `N` counted frames is a step of the opening's model**: `Real.toRunM`, with the positions exact (`OpenRunM.toRun`). The horizontal state and the
position at control are those of `m0` (`hs`, `hP`); `hopt` (the bound of `Opening`), `hlow` (the bound of `OpenLeft`) and `htop` are checks on the ROM. The page at the start
of the counted frame `N + 1` is the field `page`. -/
def Real.toRun {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true)
    (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (C : Checks sy m0 lens Zb v g) (hM : OpenMap.mapCheck sy m0 = true)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (hm₁ : OpenMap.MapAt sy m0 (S.seq 1)) (h₁ : Held sy v (L.fm 1)) (hg₁ : peek (L.fm 1) sy.Player_State = 0)
    (hG₁ : OpenFlat.GroundAt sy m0 (L.fm 1)) (hv : ∀ t, 1 ≤ t → t ≤ E → (sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs ≤ TopSpeed.top sy)
    (hs : startHS sy (L.fm 1) = startHS sy m0) (hP : posP sy (L.fm 1) = posP sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D)
    (hlow : ∀ k u, k < N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → -posP sy m0 ≤ u.2) (htop : posP sy m0 + D < 0x1000000)
    (O : Real sy m0 lens N E L) (hm : StSpring sy L N E) (hpv₁ : PrevKeep.PrevOK sy (L.fm 1)) : OpenRun sy m0 lens N E L.fm :=
  (O.toRunM hc hk hp C hM hs₁ hm₁ h₁ hg₁ hG₁ hv hm hpv₁).toRun hs hP hopt hlow htop O.page

instance (sy : Syms) (v : UInt8) (m : Machine) : Decidable (Held sy v m) := by unfold Held CtrlKeep.AreaOK; infer_instance

/-- **The state at control, from the bytes of the title's check**: if the horizontal state's bytes and the bytes of `StartRun.stI` of `m'` are those of `m`, and `m` holds
`Held` and is on the ground, so is `m'` -/
theorem held_of_bytes {m m' : Machine} {v : UInt8} (h : ∀ i ∈ StartRun.posI sy ++ StartRun.hsI sy ++ StartRun.stI sy, m'.ram.get! i = m.ram.get! i)
    (hm : Held sy v m ∧ peek m sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 m) : Held sy v m' ∧ peek m' sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 m' := by
  have hp : ∀ x, (x = sy.Player_X_Speed ∨ x = sy.Player_XSpeedAbsolute ∨ x = sy.Player_CollisionBits ∨ x = sy.Player_State ∨ x = sy.AreaType ∨
      x = sy.SwimmingFlag ∨ x = sy.PlayerChangeSizeFlag) → peek m' x = peek m x := by
    intro x hx
    apply h
    simp only [StartRun.posI, StartRun.hsI, StartRun.stI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [peek]
  have hv : ∀ x ∈ OpenFlat.vertA sy, peek m' x = peek m x := by
    intro x hx
    apply h
    simp only [OpenFlat.vertA, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [StartRun.posI, StartRun.hsI, StartRun.stI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := hm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, OpenFlat.groundAt_congr hv h7⟩
  · rw [hp _ (by simp), hp _ (by simp)]; exact h1
  · rw [hp _ (by simp)]; exact h2
  · show peek m' sy.AreaType = v
    rw [hp _ (by simp)]; exact h3
  · show peek m' sy.SwimmingFlag = 0
    rw [hp _ (by simp)]; exact h4
  · show peek m' sy.PlayerChangeSizeFlag = 0
    rw [hp _ (by simp)]; exact h5
  · rw [hp _ (by simp)]; exact h6

/-- **The checks, from those of part e** (`SurfaceFrames.numbersCheck`, for the machine at control above ground `B.m`): the movement, the two walks and the idle loop are the
same checks on `m0`; the area's type of `B.m` is that of `m0` (`he`). The rest are small checks on `m0` and `lens`, and the pause byte `g`. -/
theorem checks_of {B : PoleJoin.Box} {J Zb g : Nat} {lens : Lens} (hn : SurfaceFrames.Numbers sy m0 B J) (he : (peek B.m sy.AreaType == peek m0 sy.AreaType) = true)
    (hnorm : Potential.normIdem = true) (hl : ((lens.toList.all fun p => decide (p.2 < Zb)) && decide (0 < Zb) && decide (16 ≤ TopSpeed.top sy)) = true)
    (hs : decide (Held sy (peek m0 sy.AreaType) m0 ∧ peek m0 sy.Player_State = 0 ∧ OpenFlat.GroundAt sy m0 m0) = true) (hg : (CtrlKeep.pauseI sy m0 == g) = true)
    (hf : OpenFlat.flatCheck sy m0 (peek m0 sy.AreaType) = true)
    (hj : OpenJump.arcCheck sy m0 (FrameModel.ctrlStack sy m0) (peek m0 sy.Player_Y_Position) sy.LandDepth.toUInt8 lens = true)
    (ha : OpenAir.airAll sy m0 (peek m0 sy.AreaType) = true) (hvh : OpenVert.vertAirHOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hp0 : PrevKeep.prevOKB sy m0 = true) :
    Checks sy m0 lens Zb (peek m0 sy.AreaType) g := by
  have e : peek B.m sy.AreaType = peek m0 sy.AreaType := by simpa using he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl hs
  refine ⟨hn.model, hn.ctrl, ?_, ?_, hnorm, hl.1.1, hl.1.2, hs, by simpa using hg, hn.idle, hf, hl.2, hj, ha, hvh, ?_, by simpa [PrevKeep.prevOKB] using hp0⟩
  · rw [← e]; exact hn.after
  · rw [← e]; exact hn.area3
  · rw [← e]; exact hn.prev

end Smbrta.OpenFrames
