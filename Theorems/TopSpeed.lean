import Smbrta
import Theorems.FastAccel

/-!
# Top speed bound: nothing moves Mario right faster than running

Position in 1/256 px: `P = 256·(256·page + x) + fraction`. In a frame, the player's
horizontal bytes are changed only by these routines (all writers in the ROM, listed from the
disassembly; the others are platforms, vines, whirlpools, pipes, flagpole, axe, loopback,
level entry, the left screen edge and death):

* `GetPlayerAnimSpeed` (on the ground): may stop a skid (speed 0) and sets `RunningSpeed`,
* `X_Physics`: the speed caps and the friction adder, from tables,
* `ImposeFriction`: speed ± adder, clamped to the caps,
* `MoveObjectHorizontally`: `P += 16·v`,
* `ImpedePlayerMove` (side collision): speed 0 and `P ± 256` away from the wall.

Each routine is checked alone on every value of the bytes it reads, in their normal ranges
(`*Check`). Together they give: `|v| ≤ v_top` is kept, and `P` grows by at most `16·v_top`
per frame. Page: `TopSpeed.md`.
-/

namespace Smbrta.TopSpeed

def top (sy : Syms) : Nat := sy.RunTopSpeed.toNat

/-- speeds `-top .. top` as bytes -/
def speedsB (sy : Syms) : List UInt8 :=
  (List.range (2 * top sy + 1)).map fun i => (256 + i - top sy).toUInt8
def bytes : List UInt8 := (List.range 256).map (·.toUInt8)
def upTo (n : Nat) : List UInt8 := (List.range (n + 1)).map (·.toUInt8)
/-- collision bits: only the two low bits may be cleared -/
def collBits : List UInt8 := [0xFC, 0xFD, 0xFE, 0xFF]
/-- `RunningSpeed` values: 0, or a speed from the routine's threshold up to the top -/
def runSpds (sy : Syms) : List UInt8 :=
  0 :: ((List.range (top sy + 1)).filter (· ≥ sy.RunSpeedMin.toNat)).map (·.toUInt8)
/-- running timer values: 0 .. the reset value -/
def runTmrs (sy : Syms) : List UInt8 := upTo sy.RunTimerReset.toNat
/-- `Player_State` on the ground or in the air (climbing never runs these routines) -/
def states : List UInt8 := [0, 1, 2]
/-- directions: none, right, left, both (as the Left/Right button bits) -/
def dirs : List UInt8 := [0, 1, 2, 3]
def facings : List UInt8 := [1, 2, 3]
/-- `AreaType`: water and the three land areas -/
def areas : List UInt8 := [0, 1, 2, 3]
/-- A and B button bits -/
def abBits : List UInt8 := [0x00, 0x40, 0x80, 0xC0]
/-- pages checked for the mover and the side collision: both ends of the range of level pages
(0 .. 31); the page byte enters these routines only through one add-with-carry -/
def pages : List UInt8 := [0, 1, 30, 31]
def absB (v : UInt8) : UInt8 := if v < 0x80 then v else 0 - v
def inSpeed (sy : Syms) (v : UInt8) : Bool := (sbyte v).natAbs ≤ top sy

/-- (b) `ImposeFriction` keeps `|v| ≤ top`, sets `Player_XSpeedAbsolute = |v|`, and raises the
speed with its fraction (`V = 256·v + fraction`) to at most `max(V, 0)` + the adder (a cap can
raise a speed that is too far left up to the left cap, which is negative) -/
def frictionCheck (sy : Syms) (m0 : Machine) : Bool :=
  (speedsB sy).all fun v => bytes.all fun fr => (adders sy m0).all fun (lo, hi) =>
  (maxRs sy m0).all fun mr => (maxLs sy m0).all fun ml => (upTo 3).all fun a => collBits.all fun cb =>
    let m := poke m0 sy.Player_X_Speed v
    let m := poke m sy.Player_X_MoveForce fr
    let m := poke m sy.FrictionAdderLow lo
    let m := poke m sy.FrictionAdderHigh hi
    let m := poke m sy.MaximumRightSpeed mr
    let m := poke m sy.MaximumLeftSpeed ml
    let m := poke m sy.Player_CollisionBits cb
    let m := runSub m sy.ImposeFriction a 0 0
    let v' := peek m sy.Player_X_Speed
    let V := 256 * sbyte v + fr.toNat
    let V' := 256 * sbyte v' + (peek m sy.Player_X_MoveForce).toNat
    inSpeed sy v' && peek m sy.Player_XSpeedAbsolute == absB v' &&
    V' ≤ max V 0 + (256 * hi.toNat + lo.toNat : Int)

/-- (a) `X_Physics` sets the caps and the adder from the tables, and the running timer to 0 ..
the reset value -/
def physicsCheck (sy : Syms) (m0 : Machine) : Bool :=
  states.all fun st => (upTo (top sy)).all fun ab => areas.all fun ar => dirs.all fun lr =>
  dirs.all fun md => abBits.all fun bt => (runTmrs sy).all fun rt => (runSpds sy).all fun rs =>
  facings.all fun fd =>
    let m := poke m0 sy.Player_State st
    let m := poke m sy.Player_XSpeedAbsolute ab
    let m := poke m sy.AreaType ar
    let m := poke m sy.Left_Right_Buttons lr
    let m := poke m sy.Player_MovingDir md
    let m := poke m sy.A_B_Buttons bt
    let m := poke m sy.RunningTimer rt
    let m := poke m sy.RunningSpeed rs
    let m := poke m sy.GameEngineSubroutine sy.Eng_PlayerCtrl.toUInt8
    let m := poke m sy.PlayerFacingDir fd
    let m := runSub m sy.X_Physics 0 0 0
    (maxRs sy m0).contains (peek m sy.MaximumRightSpeed) &&
    (maxLs sy m0).contains (peek m sy.MaximumLeftSpeed) &&
    (adders sy m0).contains (peek m sy.FrictionAdderLow, peek m sy.FrictionAdderHigh) &&
    (runTmrs sy).contains (peek m sy.RunningTimer)

/-- (c) `MoveObjectHorizontally` for the player adds `16·v` to `P` (mod 2^24) -/
def moverCheck (sy : Syms) (m0 : Machine) : Bool :=
  (speedsB sy).all fun v => bytes.all fun fr => bytes.all fun x => pages.all fun pg =>
    let m := poke m0 sy.Player_X_Speed v
    let m := poke m sy.SprObject_X_MoveForce fr
    let m := poke m sy.Player_X_Position x
    let m := poke m sy.Player_PageLoc pg
    let m' := runSub m sy.MoveObjectHorizontally 0 0 0
    (posP sy m' - posP sy m - 16 * sbyte v) % 0x1000000 == 0 &&
    peek m' sy.Player_X_Speed == v

/-- (d) `ImpedePlayerMove`: speed 0 or unchanged; `P` moves by -256, 0 or +256, and +256 only
when the speed was at most 0 -/
def impedeCheck (sy : Syms) (m0 : Machine) : Bool :=
  (upTo 3).all fun side => (speedsB sy).all fun v => bytes.all fun x => pages.all fun pg =>
  collBits.all fun cb =>
    let m := poke m0 sy.Player_X_Speed v
    let m := poke m sy.Player_X_Position x
    let m := poke m sy.Player_PageLoc pg
    let m := poke m sy.Player_CollisionBits cb
    let m := poke m 0 side
    let m' := runSub m sy.ImpedePlayerMove 0 0 0
    let d := (posP sy m' - posP sy m) % 0x1000000
    let v' := peek m' sy.Player_X_Speed
    (v' == 0 || v' == v) && collBits.contains (peek m' sy.Player_CollisionBits) &&
    (d == 0 || d == 0x1000000 - 256 || (d == 256 && sbyte v ≤ 0))

/-- (e) `GetPlayerAnimSpeed`: speed and fraction unchanged, or both 0 (a stopped skid);
`RunningSpeed` stays in range; the moving direction becomes the facing direction or stays -/
def animCheck (sy : Syms) (m0 : Machine) : Bool :=
  (speedsB sy).all fun v => bytes.all fun inp => dirs.all fun md => facings.all fun fd =>
  (runSpds sy).all fun rs => [0, 0x80, 0xFF].all fun fr =>
    let m := poke m0 sy.Player_X_Speed v
    let m := poke m sy.Player_XSpeedAbsolute (absB v)
    let m := poke m sy.SavedJoypadBits inp
    let m := poke m sy.Player_MovingDir md
    let m := poke m sy.PlayerFacingDir fd
    let m := poke m sy.RunningSpeed rs
    let m := poke m sy.Player_X_MoveForce fr
    let m' := runSub m sy.GetPlayerAnimSpeed 0 0 0
    let v' := peek m' sy.Player_X_Speed
    let fr' := peek m' sy.Player_X_MoveForce
    ((v' == v && fr' == fr) || (v' == 0 && fr' == 0)) && (runSpds sy).contains (peek m' sy.RunningSpeed) &&
    [md, fd].contains (peek m' sy.Player_MovingDir)

/-! ## Running at top speed reaches the bound -/

/-- fast accel, then `k` frames of Right+B -/
def runWitness (k : Nat) : List UInt8 := FastAccel.witness ++ List.replicate k 0x41

/-- after fast accel, each of the next `k` frames moves `P` by exactly `16·top` on the full emulator -/
def attainCheck (sy : Syms) (ctx : Machine) (k : Nat) : Bool :=
  let m := playFull ctx FastAccel.witness
  ((List.range k).foldl (fun (acc : Bool × Machine) _ =>
    let m' := runFrame acc.2 (smbToPad 0x41)
    (acc.1 && posP sy m' - posP sy acc.2 == 16 * (top sy : Int), m')) (true, m)).1

/-! ## Putting the routines together

One frame, as the checks describe it. The assumption is that a frame changes the player's
speed `v`, subspeed `f` (`Player_X_MoveForce`) and position `P` only through these routines, in
this order: `GetPlayerAnimSpeed` (`anim`), `X_Physics` + `ImposeFriction` (`friction`, `gain`;
the adder is a table entry, so at most `amax`), `MoveObjectHorizontally` (`move`),
`ImpedePlayerMove` (`impede*`). The subspeed is written only by the first two (and by the
climbing code, which is not in a running frame). -/

structure Frame (top amax : Int) where
  v : Int
  f : Int
  P : Int
  v₁ : Int
  f₁ : Int
  v₂ : Int
  f₂ : Int
  P₂ : Int
  v' : Int
  f' : Int
  P' : Int
  anim : (v₁ = v ∧ f₁ = f) ∨ (v₁ = 0 ∧ f₁ = 0)
  friction : (-top ≤ v₁ ∧ v₁ ≤ top) → (-top ≤ v₂ ∧ v₂ ≤ top)
  friction_gain : 256 * v₂ + f₂ ≤ max (256 * v₁ + f₁) 0 + amax
  frac : 0 ≤ f₂ ∧ f₂ ≤ 255
  move : P₂ = P + 16 * v₂
  impedeV : v' = v₂ ∨ v' = 0
  impedeF : f' = f₂
  impedeP : P' = P₂ ∨ P' = P₂ - 256 ∨ (P' = P₂ + 256 ∧ v₂ ≤ 0)

/-- one frame keeps `|v| ≤ top` and moves `P` by at most `16·top` -/
theorem Frame.bound {top amax : Int} (f : Frame top amax) (h16 : 16 ≤ top) (hv : -top ≤ f.v ∧ f.v ≤ top) :
    (-top ≤ f.v' ∧ f.v' ≤ top) ∧ f.P' - f.P ≤ 16 * top := by
  have h1 : -top ≤ f.v₁ ∧ f.v₁ ≤ top := by
    rcases f.anim with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  have h2 := f.friction h1
  have hm := f.move
  refine ⟨?_, ?_⟩
  · rcases f.impedeV with h | h <;> rw [h] <;> omega
  · rcases f.impedeP with h | h | ⟨h, hneg⟩ <;> rw [h] <;> omega

/-- `GainBound` for one frame: `V' ≤ max(V, 0) + amax`, with `V = 256·v + f` -/
theorem Frame.gain {top amax : Int} (f : Frame top amax) (h255 : 255 ≤ amax) :
    256 * f.v' + f.f' ≤ max (256 * f.v + f.f) 0 + amax := by
  have hg := f.friction_gain
  have hfr := f.frac
  have hF := f.impedeF
  have hA : max (256 * f.v₁ + f.f₁) 0 ≤ max (256 * f.v + f.f) 0 := by
    rcases f.anim with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega
  rcases f.impedeV with h | h <;> rw [h] <;> omega

/-- the most one frame can move `P`, when `max(V, 0) ≤ w` before it -/
def adv (top amax w : Int) : Int := max (16 * min top ((w + amax) / 256)) 256

/-- one frame moves `P` by at most `adv`: the speed it moves with is at most `(w + amax) / 256`,
and a push out of a wall (+256) only comes with a speed `≤ 0` -/
theorem Frame.adv_le {top amax : Int} (f : Frame top amax) (w : Int) (hv : -top ≤ f.v ∧ f.v ≤ top)
    (hw : max (256 * f.v + f.f) 0 ≤ w) : f.P' - f.P ≤ adv top amax w := by
  unfold adv
  have h1 : -top ≤ f.v₁ ∧ f.v₁ ≤ top := by
    rcases f.anim with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  have h2 := f.friction h1
  have hg := f.friction_gain
  have hfr := f.frac
  have hm := f.move
  have hA : max (256 * f.v₁ + f.f₁) 0 ≤ max (256 * f.v + f.f) 0 := by
    rcases f.anim with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega
  rcases f.impedeP with h | h | ⟨h, hneg⟩ <;> rw [h] <;> omega

/-- frames that follow each other -/
def Chain {top amax : Int} : List (Frame top amax) → Prop
  | [] => True
  | [_] => True
  | f :: g :: rest => g.v = f.v' ∧ g.f = f.f' ∧ g.P = f.P' ∧ Chain (g :: rest)

/-- in `n` chained frames, `P` grows by at most `16·top·n` -/
theorem chain_bound {top amax : Int} (h16 : 16 ≤ top) :
    ∀ (fs : List (Frame top amax)) (f : Frame top amax), Chain (f :: fs) → (-top ≤ f.v ∧ f.v ≤ top) →
      (fs.getLastD f).P' - f.P ≤ 16 * top * (fs.length + 1)
  | [], f, _, hv => by
    have := (f.bound h16 hv).2
    simp only [List.getLastD_nil, List.length_nil]
    omega
  | g :: rest, f, hc, hv => by
    obtain ⟨hgv, _, hgP, hrest⟩ := hc
    have hf := f.bound h16 hv
    have hg : -top ≤ g.v ∧ g.v ≤ top := by rw [hgv]; exact hf.1
    have ih := chain_bound h16 rest g hrest hg
    have hlast : ((g :: rest).getLastD f) = (rest.getLastD g) := List.getLastD_cons
    rw [hlast]
    simp only [List.length_cons] at ih ⊢
    have e : 16 * top * (((rest.length + 1 : Nat) : Int) + 1) =
        16 * top * ((rest.length : Int) + 1) + 16 * top := by
      push_cast
      rw [show (rest.length : Int) + 1 + 1 = ((rest.length : Int) + 1) + 1 from rfl, Int.mul_add, Int.mul_one]
    rw [e]
    omega

end Smbrta.TopSpeed
