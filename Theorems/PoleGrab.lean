import Theorems.TopSpeed
import Theorems.Potential

/-!
# Grabbing the flagpole from below

The direct grab needs Mario rising inside the pole's range, which lies past the left edge of the
base block. Beside the block the collision routine pushes him back; moving left turns the push of
his feet to the right, at most one pixel per frame. These facts bound where he can land, so where
he can be when he hops. Page: `PoleGrab.md`.

`poleCheck` runs `PlayerBGCollision` on every state near the block and compares with the rules below.
The theorems are about frames (`TopSpeed.Frame`) whose collision part follows these rules.
-/

namespace Smbrta.PoleGrab

open TopSpeed (Frame speedsB bytes)

/-! ## The routine against the rules -/

def column (sy : Syms) : Nat := sy.FlagColumnByte.toNat / 16
/-- the row of the base block: the operand of its store, against the metatile buffer -/
def baseRow (sy : Syms) : Nat := sy.FlagBaseOperand.toNat - sy.MetatileBuffer.toNat % 256
/-- the left edge of the pole's column, in pixels -/
def colX (sy : Syms) : Nat := 16 * column sy
/-- the top of the base block, in pixels -/
def topY (sy : Syms) : Nat := sy.BlockBufferTopY.toNat + 16 * baseRow sy

/-- a machine with the pole's column and an empty column left of it in the first block buffer -/
def withPole (sy : Syms) (m0 : Machine) : Machine :=
  (List.range 13).foldl (fun m r =>
    let tile : UInt8 := if r == 0 then sy.FlagBallTile.toUInt8
      else if r < baseRow sy then sy.FlagShaftTile.toUInt8
      else if r == baseRow sy then sy.FlagBaseTile.toUInt8 else sy.GroundTile.toUInt8
    let left : UInt8 := if r ≤ baseRow sy then 0 else sy.GroundTile.toUInt8
    let base := sy.Block_Buffer_1 + (column sy + 16 * r).toUInt16
    poke (poke m base tile) (base - 1) left) m0

structure Case where
  x : UInt8
  y : UInt8
  v : UInt8
  md : UInt8
  vy : UInt8
  st : UInt8
  fd : UInt8
  deriving Repr, Inhabited

def collide (sy : Syms) (m : Machine) (c : Case) : Machine :=
  let m := poke m sy.Player_PageLoc 0
  let m := poke m sy.Player_X_Position c.x
  let m := poke m sy.SprObject_X_MoveForce 0x5A
  let m := poke m sy.Player_Y_Position c.y
  let m := poke m sy.Player_X_Speed c.v
  let m := poke m sy.Player_MovingDir c.md
  let m := poke m sy.Player_Y_Speed c.vy
  let m := poke m sy.Player_State c.st
  let m := poke m sy.PlayerFacingDir c.fd
  let m := poke m sy.GameEngineSubroutine sy.Eng_PlayerCtrl.toUInt8
  runSub m sy.PlayerBGCollision 0 0 0

/-- the rules -/
def ruleOk (sy : Syms) (m : Machine) (c : Case) : Bool :=
  let r := collide sy m c
  let x' := peek r sy.Player_X_Position
  let v' := peek r sy.Player_X_Speed
  let y' := peek r sy.Player_Y_Position
  let st' := peek r sy.Player_State
  let eng' := peek r sy.GameEngineSubroutine
  let bits := peek r sy.Player_CollisionBits
  let cx := colX sy
  let ty := topY sy
  let xn := c.x.toNat
  let foot := c.y.toNat + sy.FeetAdderY.toNat
  let sideY := c.y.toNat + sy.SideAdderY.toNat
  let side := cx ≤ xn + sy.SideAdderX.toNat
  let feet := cx ≤ xn + sy.FeetAdderX.toNat
  let inRange := side && sy.ClimbLowNybble.toNat ≤ xn % 16 && xn % 16 < sy.ClimbHighNybble.toNat
  let sv := sbyte c.v
  let same := x' == c.x && v' == c.v
  let keepF := peek r sy.SprObject_X_MoveForce == 0x5A && peek r sy.Player_PageLoc == 0
  let engSame := eng'.toUInt16 == sy.Eng_PlayerCtrl
  -- a hit on the right blocks the Right bit, a hit on the left the Left bit
  let pushL := x' == c.x - 1 && v' == 0 && bits == 0xFE
  let pushR := x' == c.x + 1 && v' == 0 && bits == 0xFD
  let sideRule := if 0 ≤ sv then pushL else same && bits == 0xFE
  keepF &&
  (if 0 ≤ sbyte c.vy then
    if ty + sy.LandDepth.toNat ≤ foot && foot < ty + 16 && feet then
      -- falling with the feet inside the block
      (if c.md == 1 then pushL else pushR) && y' == c.y && st' != 0 && engSame
    else if ty ≤ foot && foot < ty + sy.LandDepth.toNat && feet then
      -- falling onto the top of the block: he lands, above the height of a direct grab
      y'.toNat + sy.FeetAdderY.toNat == ty && (if inRange then eng' == 4 else st' == 0 && engSame && same)
    else if ty + 16 ≤ foot then
      -- the ground
      y'.toNat + sy.FeetAdderY.toNat == ty + 16 && st' == 0 && engSame && (if side then sideRule else same)
    else if side && ty ≤ sideY then
      sideRule && y' == c.y && st' != 0 && engSame
    else
      same && y' == c.y && st' != 0 && engSame
  else
    y' == c.y && st' != 0 &&
    (if ty ≤ sideY then engSame && (if side then sideRule else same)
     else if inRange then eng' == 4 else engSame && same))

/-- from the height of the top of the block to below the ground's top -/
def caseYs (sy : Syms) : List UInt8 :=
  (List.range 20).map fun i => (topY sy - sy.FeetAdderY.toNat + i).toUInt8
/-- from where the side of the block is reached to past the range's left end -/
def caseXs (sy : Syms) : List UInt8 :=
  (List.range 5).map fun i => (colX sy - sy.SideAdderX.toNat + i).toUInt8
/-- moving left, he moves slowly here: he has just been stopped -/
def caseVs (sy : Syms) : List UInt8 := (speedsB sy).filter fun v => decide (-12 ≤ sbyte v)

/-- fall speed and state: rising only in the first frames of a jump (at most one step below the fast jump
speed and one above), falling up to the top fall speed, on the ground only at its height -/
def caseVyStates (sy : Syms) (y : UInt8) : List (UInt8 × UInt8) :=
  let jf := sy.FastJumpSpeed.toUInt8
  let ground := topY sy + 16
  let foot := y.toNat + sy.FeetAdderY.toNat
  let falling := (List.range (sy.MaxFallSpeed.toNat + 1)).flatMap fun vy =>
    [(vy.toUInt8, (1 : UInt8)), (vy.toUInt8, 2)]
  if foot < ground then [(jf, 1), (jf + 1, 1), (jf + 2, 1)] ++ falling
  else if foot == ground then (0, 0) :: falling
  else falling

/-- every state near the block, the speed with a moving direction that fits it (`Potential.mds`).
The facing direction is read only when he lands on the ground. -/
def cases (sy : Syms) : List Case :=
  (caseXs sy).flatMap fun x => (caseYs sy).flatMap fun y => (caseVs sy).flatMap fun v =>
    (Potential.mds v).flatMap fun md => (caseVyStates sy y).flatMap fun (vy, st) =>
      (if topY sy + 16 ≤ y.toNat + sy.FeetAdderY.toNat then [(1 : UInt8), 2, 3] else [1]).map fun fd =>
        { x, y, v, md, vy, st, fd }

def poleCheck (sy : Syms) (m : Machine) : Bool :=
  let mp := withPole sy m
  (cases sy).all (ruleOk sy mp)

/-- with the Left bit blocked (after a push to the right), a stopped Mario does not start moving left
in the air -/
def maskCheck (sy : Syms) (m : Machine) : Bool :=
  let mb := poke m sy.Player_CollisionBits 0xFD
  bytes.all fun f => Potential.facings.all fun fd => [(0 : UInt8), 1, 2, 3].all fun md =>
    (Potential.rsVals sy).all fun rs =>
      (Potential.inputsN.filter fun i => i.st == 1 && !i.jump).all fun i =>
        decide (0 ≤ sbyte (Potential.hstep sy mb { v := 0, f, fd, md, rs } i).v)

/-! ## From the rules to the position

Frames are numbered: `fr t` is frame `t`. The rules, on frames: -/

variable {top amax : Int}

/-- consecutive frames -/
def Next (f g : Frame top amax) : Prop := g.v = f.v' ∧ g.f = f.f' ∧ g.P = f.P'

/-- beside the block, below its top: moving right or stopped, speed 0 and 1 px back; moving left,
nothing -/
def Side (f : Frame top amax) : Prop :=
  (0 ≤ f.v₂ ∧ f.v' = 0 ∧ f.P' = f.P₂ - 256) ∨ (f.v₂ < 0 ∧ f.v' = f.v₂ ∧ f.P' = f.P₂)

/-- falling with the feet inside the block: speed 0; moving right, 1 px back; otherwise 1 px either
way, by the moving direction -/
def InBlock (f : Frame top amax) : Prop :=
  f.v' = 0 ∧ ((1 ≤ f.v₂ ∧ f.P' = f.P₂ - 256) ∨ (f.v₂ ≤ 0 ∧ (f.P' = f.P₂ - 256 ∨ f.P' = f.P₂ + 256)))

/-- a push to the right blocks the Left button on the next frame: from speed 0 he does not start moving left
(`maskCheck`) -/
def MaskL (f g : Frame top amax) : Prop := f.P' = f.P₂ + 256 → 0 ≤ g.v₂

/-- no speed to the right before the frame, beyond a fraction -/
def Low (f : Frame top amax) : Prop := f.v ≤ 0 ∧ 0 ≤ f.f ∧ f.f ≤ 255

theorem speed_le_two (hA : amax ≤ 512) {f : Frame top amax} (h : Low f) : f.v₂ ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hg := f.friction_gain
  have hf := f.frac
  rcases f.anim with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> rw [h4, h5] at hg <;> omega

theorem low_of_side {f g : Frame top amax} (hs : Side f) (hn : Next f g) : Low g := by
  obtain ⟨h1, h2, _⟩ := hn
  have hf := f.frac
  have hi := f.impedeF
  rcases hs with ⟨_, h3, _⟩ | ⟨h3, h4, _⟩ <;> refine ⟨by omega, by omega, by omega⟩

theorem low_of_inBlock {f g : Frame top amax} (hb : InBlock f) (hn : Next f g) : Low g := by
  obtain ⟨h1, h2, _⟩ := hn
  have hf := f.frac
  have hi := f.impedeF
  have h3 := hb.1
  exact ⟨by omega, by omega, by omega⟩

/-- a frame at the side of the block moves him at least 1/16 px back -/
theorem side_step (hA : amax ≤ 512) {f : Frame top amax} (hl : Low f) (hs : Side f) :
    f.P' ≤ f.P - 16 := by
  have h2 := speed_le_two hA hl
  have hm := f.move
  rcases hs with ⟨_, _, h⟩ | ⟨h1, _, h⟩ <;> omega

/-- a frame with the feet inside moves him at most 1 px forward -/
theorem inBlock_step (hA : amax ≤ 512) {f : Frame top amax} (hl : Low f) (hb : InBlock f) :
    f.P' ≤ f.P + 256 := by
  have h2 := speed_le_two hA hl
  have hm := f.move
  rcases hb.2 with ⟨_, h⟩ | ⟨h1, h | h⟩ <;> omega

theorem inside_le (hA : amax ≤ 512) (fr : Nat → Frame top amax) (e : Nat) (he : InBlock (fr e)) :
    ∀ n, (∀ j, j ≤ n → Next (fr (e + j)) (fr (e + j + 1))) → (∀ j, j < n → InBlock (fr (e + j + 1))) →
      Low (fr (e + n + 1)) ∧ (fr (e + n + 1)).P ≤ (fr e).P' + 256 * (n : Int)
  | 0, hn, _ => by
    have h := hn 0 (Nat.le_refl _)
    simp only [Nat.add_zero] at h ⊢
    exact ⟨low_of_inBlock he h, by have := h.2.2; omega⟩
  | n + 1, hn, hb => by
    obtain ⟨h1, h2⟩ := inside_le hA fr e he n (fun j hj => hn j (by omega)) (fun j hj => hb j (by omega))
    have hbn := hb n (Nat.lt_succ_self _)
    have hnx := hn (n + 1) (Nat.le_refl _)
    have h3 := inBlock_step hA h1 hbn
    have h4 := hnx.2.2
    rw [show e + (n + 1) = e + n + 1 by omega] at hnx ⊢
    rw [show e + (n + 1) = e + n + 1 by omega] at h4
    refine ⟨low_of_inBlock hbn hnx, ?_⟩
    rw [show e + n + 1 + 1 = e + n + 1 + 1 from rfl]
    push_cast
    omega

/-- the frame he moves over the block moves him back -/
theorem entry_back {Pf : Int} {f : Frame top amax} (h1 : f.P < Pf) (h2 : Pf ≤ f.P₂) (hb : InBlock f) :
    f.P' = f.P₂ - 256 := by
  have hm := f.move
  rcases hb.2 with ⟨_, h⟩ | ⟨h3, _⟩
  · exact h
  · omega

/-- landing `n + 2` frames after moving over the block: `x(L) ≤ x(e) + k − 3 + 1/8` -/
theorem landing_far (hA : amax ≤ 512) (fr : Nat → Frame top amax) (e n : Nat) {Pf : Int}
    (h1 : (fr e).P < Pf) (h2 : Pf ≤ (fr e).P₂) (he : InBlock (fr e))
    (hn : ∀ j, j ≤ n + 1 → Next (fr (e + j)) (fr (e + j + 1)))
    (hb : ∀ j, j ≤ n → InBlock (fr (e + j + 1)))
    (hs : Side (fr (e + n + 2))) (hm : MaskL (fr (e + n + 1)) (fr (e + n + 2))) :
    (fr (e + n + 2)).P' ≤ (fr e).P₂ + 256 * (n : Int) - 224 := by
  obtain ⟨h3, h4⟩ := inside_le hA fr e he n (fun j hj => hn j (by omega)) (fun j hj => hb j (by omega))
  have hbn := hb n (Nat.le_refl _)
  have hnx := hn (n + 1) (Nat.le_refl _)
  rw [show e + (n + 1) = e + n + 1 by omega, show e + n + 1 + 1 = e + n + 2 by omega] at hnx
  have hL := low_of_inBlock hbn hnx
  have h5 := speed_le_two hA hL
  have h6 := speed_le_two hA h3
  have h7 := entry_back h1 h2 he
  have h8 := side_step hA hL hs
  have h9 := hnx.2.2
  have hmv := (fr (e + n + 1)).move
  have hmvL := (fr (e + n + 2)).move
  by_cases hr : (fr (e + n + 1)).P' = (fr (e + n + 1)).P₂ + 256
  · have h10 := hm hr
    rcases hbn.2 with ⟨_, h⟩ | ⟨h11, _⟩
    · omega
    · rcases hs with ⟨_, _, h⟩ | ⟨h12, _, _⟩
      · omega
      · omega
  · rcases hbn.2 with ⟨_, h⟩ | ⟨h11, h | h⟩
    · omega
    · omega
    · exact absurd h hr

/-- landing on the frame after moving over the block -/
theorem landing_one (hA : amax ≤ 512) {Pf : Int} {f g : Frame top amax} (h1 : f.P < Pf) (h2 : Pf ≤ f.P₂)
    (hb : InBlock f) (hn : Next f g) (hs : Side g) : g.P' ≤ f.P₂ - 256 := by
  have h3 := entry_back h1 h2 hb
  have h4 := side_step hA (low_of_inBlock hb hn) hs
  have h5 := hn.2.2
  omega

/-- landing on the frame that moves him past the side of the block -/
theorem landing_zero {Pf : Int} {f : Frame top amax} (h1 : f.P < Pf) (h2 : Pf ≤ f.P₂) (hs : Side f) :
    f.P' ≤ f.P₂ - 256 := by
  have hm := f.move
  rcases hs with ⟨_, _, h⟩ | ⟨h3, _, _⟩
  · omega
  · omega

/-- without Left or Right after moving over the block, every frame moves him back -/
theorem landing_left (hA : amax ≤ 512) (fr : Nat → Frame top amax) (e : Nat) {Pf : Int}
    (h1 : (fr e).P < Pf) (h2 : Pf ≤ (fr e).P₂) (he : InBlock (fr e)) :
    ∀ n, (∀ j, j ≤ n → Next (fr (e + j)) (fr (e + j + 1))) →
      (∀ j, j < n → InBlock (fr (e + j + 1)) ∧ (fr (e + j + 1)).P' = (fr (e + j + 1)).P₂ - 256) →
      Low (fr (e + n + 1)) ∧ (fr (e + n + 1)).P ≤ (fr e).P₂ - 256
  | 0, hn, _ => by
    have h := hn 0 (Nat.le_refl _)
    simp only [Nat.add_zero] at h ⊢
    have h3 := entry_back h1 h2 he
    exact ⟨low_of_inBlock he h, by have := h.2.2; omega⟩
  | n + 1, hn, hb => by
    obtain ⟨h3, h4⟩ := landing_left hA fr e h1 h2 he n (fun j hj => hn j (by omega)) (fun j hj => hb j (by omega))
    obtain ⟨h5, h6⟩ := hb n (Nat.lt_succ_self _)
    have hnx := hn (n + 1) (Nat.le_refl _)
    rw [show e + (n + 1) = e + n + 1 by omega] at hnx ⊢
    have h7 := speed_le_two hA h3
    have h8 := (fr (e + n + 1)).move
    have h9 := hnx.2.2
    refine ⟨low_of_inBlock h5 hnx, ?_⟩
    omega

/-- on the ground and in the hop, every frame beside the block moves him back -/
theorem hop_le (hA : amax ≤ 512) (fr : Nat → Frame top amax) (L : Nat) (hL : Low (fr (L + 1)))
    (h0 : Next (fr L) (fr (L + 1))) :
    ∀ m, (∀ j, j < m → Next (fr (L + j + 1)) (fr (L + j + 2))) → (∀ j, j < m → Side (fr (L + j + 1))) →
      Low (fr (L + m + 1)) ∧ (fr (L + m + 1)).P ≤ (fr L).P' - 16 * (m : Int)
  | 0, _, _ => by
    simp only [Nat.add_zero]
    exact ⟨hL, by have := h0.2.2; push_cast; omega⟩
  | m + 1, hn, hs => by
    obtain ⟨h1, h2⟩ := hop_le hA fr L hL h0 m (fun j hj => hn j (by omega)) (fun j hj => hs j (by omega))
    have hsm := hs m (Nat.lt_succ_self _)
    have hnx := hn m (Nat.lt_succ_self _)
    have h3 := side_step hA h1 hsm
    have h4 := hnx.2.2
    rw [show L + (m + 1) + 1 = L + m + 2 by omega]
    refine ⟨low_of_side hsm hnx, ?_⟩
    push_cast
    omega

/-- the frame after the hop moves him at most 1/8 px -/
theorem grab_le (hA : amax ≤ 512) {g : Frame top amax} (hl : Low g) : g.P₂ ≤ g.P + 32 := by
  have h := speed_le_two hA hl
  have hm := g.move
  omega

/-- landing at least two frames after moving over the block, in time, and a hop of at least two frames:
at the grab he is short of `P₀`. `Pf` is where his feet get over the block: `e` moves him past it, `L = e + n + 2`
lands, `g = L + m + 1` would grab. `B` bounds `P` at frame `t`, and `P` moves at most `16·top` per frame before
it. -/
theorem no_grab_far (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax)
    (Pf P₀ B : Int) (e n m t : Nat)
    (h1 : (fr e).P < Pf) (h2 : Pf ≤ (fr e).P₂) (hve : (fr e).v₂ ≤ top) (he : InBlock (fr e))
    (hn : ∀ j, j ≤ n + 1 → Next (fr (e + j)) (fr (e + j + 1)))
    (hb : ∀ j, j ≤ n → InBlock (fr (e + j + 1)))
    (hs : Side (fr (e + n + 2))) (hm : MaskL (fr (e + n + 1)) (fr (e + n + 2)))
    (hn2 : Next (fr (e + n + 2)) (fr (e + n + 2 + 1)))
    (hn3 : ∀ j, j < m → Next (fr (e + n + 2 + j + 1)) (fr (e + n + 2 + j + 2)))
    (hs3 : ∀ j, j < m → Side (fr (e + n + 2 + j + 1))) (hm2 : 2 ≤ m)
    (hB : ∀ d : Nat, e + d = t → (fr e).P₂ + 16 * top * (d : Int) ≤ B) (hgap : B + 32 < P₀)
    (hfar : Pf + 16 * top ≤ P₀ + 224) (htime : e + n + 2 ≤ t + 3) :
    (fr (e + n + 2 + m + 1)).P₂ < P₀ := by
  have h3 := landing_far hA fr e n h1 h2 he hn hb hs hm
  obtain ⟨h4, h5⟩ := hop_le hA fr (e + n + 2) (low_of_side hs hn2) hn2 m hn3 hs3
  have h6 := grab_le hA h4
  have hmv := (fr e).move
  have hm' : (2 : Int) ≤ m := by omega
  have hP : (fr (e + n + 2)).P' < P₀ := by
    cases n with
    | zero => omega
    | succ n' =>
      -- `d ≥ n'` frames from `e` to `t`
      obtain ⟨d, hd⟩ : ∃ d, e + d = t := ⟨t - e, by omega⟩
      have h7 := hB d hd
      have hdn : (n' : Int) ≤ d := by omega
      have h8 : 256 * (d : Int) ≤ 16 * top * d :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      push_cast at h3
      omega
  omega

/-- when the landing leaves him 1 px behind where he moved over the block (`k ≤ 1`, or no Left or Right), any
hop of at least one frame leaves him short of `P₀` -/
theorem no_grab_near (hA : amax ≤ 512) (fr : Nat → Frame top amax) (Pf P₀ : Int) (e L m : Nat)
    (h1 : (fr e).P < Pf) (hve : (fr e).v₂ ≤ top) (hfar : Pf + 16 * top ≤ P₀ + 224)
    (hland : (fr L).P' ≤ (fr e).P₂ - 256) (hl : Low (fr (L + 1))) (hn2 : Next (fr L) (fr (L + 1)))
    (hn3 : ∀ j, j < m → Next (fr (L + j + 1)) (fr (L + j + 2)))
    (hs3 : ∀ j, j < m → Side (fr (L + j + 1))) (hm1 : 1 ≤ m) :
    (fr (L + m + 1)).P₂ < P₀ := by
  obtain ⟨h4, h5⟩ := hop_le hA fr L hl hn2 m hn3 hs3
  have h6 := grab_le hA h4
  have hmv := (fr e).move
  have hm' : (1 : Int) ≤ m := by omega
  omega

end Smbrta.PoleGrab
