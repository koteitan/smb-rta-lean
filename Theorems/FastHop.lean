import Theorems.Jump

/-!
# The fast hop beside the flagpole

A jump reads the stored absolute speed. A hit stops Mario but does not clear that byte, so a jump right after a hit can
be fast with no speed left. The byte stays high only while nothing updates it: a ground frame or a press of Left or Right
in the air writes `|v|` into it, and that is small after a hit. So a fast hop needs no Left or Right after the hit, and
then every frame pushes him back. Page: `FastHop.md`.

`absCheck` runs the game's movement routine from a stopped Mario with a high stored speed. The theorems are about frames
that follow it.
-/

namespace Smbrta.FastHop

open TopSpeed (Frame bytes collBits)
open PoleGrab (InBlock Side Next Low landing_left side_step low_of_inBlock hop_le grab_le no_grab_near)

/-- a stopped Mario with a stored speed `abs` -/
structure Case where
  abs : UInt8
  f : UInt8
  lr : UInt8
  bits : UInt8
  /-- `Player_State`: 0 on the ground, 1 jumping, 2 falling -/
  st : UInt8
  fd : UInt8
  md : UInt8
  rs : UInt8
  deriving Repr, Inhabited

def move (sy : Syms) (m : Machine) (c : Case) : Machine :=
  let m := poke m sy.Player_XSpeedAbsolute c.abs
  let m := poke m sy.Player_X_Speed 0
  let m := poke m sy.Player_X_MoveForce c.f
  let m := poke m sy.Left_Right_Buttons c.lr
  let m := poke m sy.Player_CollisionBits c.bits
  let m := poke m sy.Player_State c.st
  let m := poke m sy.PlayerFacingDir c.fd
  let m := poke m sy.Player_MovingDir c.md
  let m := poke m sy.RunningSpeed c.rs
  let m := poke m sy.A_B_Buttons 0
  let m := poke m sy.PreviousA_B_Buttons 0
  let m := poke m sy.SavedJoypadBits c.lr
  let m := poke m sy.GameEngineSubroutine sy.Eng_PlayerCtrl.toUInt8
  runSub m sy.PlayerMovementSubs 0 0 0

/-- in the air with no Left or Right: nothing changes. Otherwise the stored speed becomes the speed, which is below the air
threshold -/
def caseOk (sy : Syms) (m : Machine) (c : Case) : Bool :=
  let r := move sy m c
  let abs' := peek r sy.Player_XSpeedAbsolute
  let v' := peek r sy.Player_X_Speed
  if c.st != 0 && c.lr == 0 then
    abs' == c.abs && v' == 0 && peek r sy.Player_MovingDir == c.md
  else
    abs' == TopSpeed.absB v' && decide (abs'.toNat < sy.AirFastSpeed.toNat)

/-- stored speeds: the air threshold and the top; every fraction; the facing and moving directions that give a doubled adder or
not; both running speeds -/
def cases (sy : Syms) : List Case :=
  [sy.AirFastSpeed.toUInt8, (TopSpeed.top sy).toUInt8].flatMap fun abs => bytes.flatMap fun f =>
    [(0 : UInt8), 1, 2, 3].flatMap fun lr => collBits.flatMap fun bits => [(0 : UInt8), 1, 2].flatMap fun st =>
      [(1 : UInt8), 2].flatMap fun md => (Potential.rsVals sy).map fun rs =>
        { abs, f, lr, bits, st, fd := 1, md, rs }

def absCheck (sy : Syms) (m : Machine) : Bool := (cases sy).all (caseOk sy m)

/-! ## On frames -/

/-- what a frame does to the stored speed: `ran` is a ground frame, or Left or Right pressed in the air -/
structure AbsStep where
  abs : Nat
  abs' : Nat
  ran : Bool

/-- the frame follows `absCheck`, with `A` the air threshold -/
def Follows (A : Nat) (s : AbsStep) : Prop :=
  (s.ran = true → s.abs' < A) ∧ (s.ran = false → s.abs' = s.abs)

/-- if the stored speed is still at least `A` after frame `t`, nothing updated it from frame `j` on -/
theorem no_update {A : Nat} (fa : Nat → AbsStep) (hf : ∀ t, Follows A (fa t))
    (hc : ∀ t, (fa (t + 1)).abs = (fa t).abs') (j : Nat) :
    ∀ d, A ≤ (fa (j + d)).abs' → (fa j).ran = false
  | 0, h => by
    cases hr : (fa j).ran with
    | false => rfl
    | true =>
      have := (hf (j + 0)).1 (by simpa using hr)
      omega
  | d + 1, h => by
    rw [show j + (d + 1) = (j + d) + 1 by omega] at h
    cases hr : (fa (j + d + 1)).ran with
    | true =>
      have := (hf (j + d + 1)).1 hr
      omega
    | false =>
      have h1 := (hf (j + d + 1)).2 hr
      have h2 := hc (j + d)
      exact no_update fa hf hc j d (by omega)

variable {top amax : Int}

/-- a fast hop: with no Left or Right from the frame `e` on, each frame with the feet inside pushes him back (he still moves right
by direction: `absCheck` keeps the moving direction). Landing at `L = e + n + 1`, the hop is one frame, and `g = L + 2`: he is
short of `P₀` -/
theorem fast_hop_short (hA : amax ≤ 512) (fr : Nat → Frame top amax) (Pf P₀ : Int) (e n : Nat)
    (h1 : (fr e).P < Pf) (h2 : Pf ≤ (fr e).P₂) (hve : (fr e).v₂ ≤ top) (he : InBlock (fr e))
    (hfar : Pf + 16 * top ≤ P₀ + 224)
    (hn : ∀ j, j ≤ n → Next (fr (e + j)) (fr (e + j + 1)))
    (hb : ∀ j, j < n → InBlock (fr (e + j + 1)) ∧ (fr (e + j + 1)).P' = (fr (e + j + 1)).P₂ - 256)
    (hs : Side (fr (e + n + 1)))
    (hL : Next (fr (e + n + 1)) (fr (e + n + 1 + 1)))
    (hT : Next (fr (e + n + 1 + 0 + 1)) (fr (e + n + 1 + 0 + 2)))
    (hsT : Side (fr (e + n + 1 + 0 + 1))) :
    (fr (e + n + 1 + 1 + 1)).P₂ < P₀ := by
  obtain ⟨h3, h4⟩ := landing_left hA fr e h1 h2 he n hn hb
  have h5 := side_step hA h3 hs
  have hland : (fr (e + n + 1)).P' ≤ (fr e).P₂ - 256 := by omega
  have := no_grab_near hA fr Pf P₀ e (e + n + 1) 1 h1 hve hfar hland (PoleGrab.low_of_side hs hL) hL
    (fun j hj => by have : j = 0 := by omega
                    subst this; exact hT)
    (fun j hj => by have : j = 0 := by omega
                    subst this; exact hsT) (by omega)
  exact this

end Smbrta.FastHop
