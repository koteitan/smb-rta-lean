import Theorems.Jump

/-!
# Entering the side pipe

Mario enters the side pipe on a frame that lands on the ground (or stands on it) with his right side in the
pipe's mouth, facing right. In the air the pipe stops him. Page: `SidePipe.md`.

`sideCheck` runs `PlayerBGCollision` on every state near the mouth and compares with `rule`. The other theorems
are about frames: an entry frame is a frame on the ground, at the mouth or past its left end, and the fall to that
frame takes the time that `Theorems/Jump.lean` gives.
-/

namespace Smbrta.SidePipe

open TopSpeed (speedsB)

/-- the pipe's column: the room's level object, in its high nybble -/
def column (sy : Syms) : Nat := sy.RoomPipeByte.toNat / 16
/-- the leftmost `x` with his right side in the mouth -/
def xLo (sy : Syms) : Nat := 16 * column sy - sy.SideAdderX.toNat
/-- the rightmost one -/
def xHi (sy : Syms) : Nat := xLo sy + 15
/-- the position of the mouth's left end on page `pg` -/
def mouthP (sy : Syms) (pg : Nat) : Int := 256 * (256 * (pg : Int) + (xLo sy : Int))

/-- the row of the mouth: the row just above the ground -/
def lowRow (sy : Syms) : Nat := PoleGrab.baseRow sy

/-- a machine with the pipe in the first block buffer: the mouth, the part above it, what lies right of them, and
the ground under it all; the column left of it empty down to the ground -/
def withPipe (sy : Syms) (m0 : Machine) : Machine :=
  (List.range 13).foldl (fun m r =>
    let c := column sy
    let at' (col : Nat) := sy.Block_Buffer_1 + (col + 16 * r).toUInt16
    let ground := lowRow sy < r
    let tile : UInt8 :=
      if ground then sy.GroundTile.toUInt8
      else if r == lowRow sy then sy.SidePipeTile.toUInt8
      else if r + 1 == lowRow sy then sy.SidePipeTopTile.toUInt8 else 0
    let right : UInt8 := if ground || tile == 0 then tile else tile + 1
    let left : UInt8 := if ground then sy.GroundTile.toUInt8 else 0
    poke (poke (poke m (at' c) tile) (at' (c + 1)) right) (at' (c - 1)) left) m0

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
  let m := poke m sy.Player_Y_Position c.y
  let m := poke m sy.Player_X_Speed c.v
  let m := poke m sy.Player_MovingDir c.md
  let m := poke m sy.Player_Y_Speed c.vy
  let m := poke m sy.Player_State c.st
  let m := poke m sy.PlayerFacingDir c.fd
  let m := poke m sy.GameEngineSubroutine sy.Eng_PlayerCtrl.toUInt8
  runSub m sy.PlayerBGCollision 0 0 0

/-- the routine started the side pipe routine -/
def enters (sy : Syms) (m : Machine) (c : Case) : Bool :=
  peek (collide sy m c) sy.GameEngineSubroutine == sy.EngSidePipe.toUInt8

/-- the frame lands on the ground, or stands on it: not rising, feet in the landing depth of the ground -/
def onGround (sy : Syms) (c : Case) : Bool :=
  let foot := c.y.toNat + sy.FeetAdderY.toNat
  let g := Jump.groundY sy + sy.FeetAdderY.toNat
  c.vy < 0x80 && decide (g ≤ foot) && decide (foot < g + sy.LandDepth.toNat)

def inMouth (sy : Syms) (c : Case) : Bool := decide (xLo sy ≤ c.x.toNat) && decide (c.x.toNat ≤ xHi sy)

/-- the rule -/
def rule (sy : Syms) (c : Case) : Bool := onGround sy c && inMouth sy c && c.fd == 1

/-- entered exactly by the rule; otherwise the routine number is unchanged -/
def ruleOk (sy : Syms) (m : Machine) (c : Case) : Bool :=
  enters sy m c == rule sy c &&
    (rule sy c || peek (collide sy m c) sy.GameEngineSubroutine == sy.Eng_PlayerCtrl.toUInt8)

/-- from a few pixels left of the mouth to the last `x` with his right side in it. Further right his left side
reaches the mouth too; a lower bound does not need that part. -/
def caseXs (sy : Syms) : List UInt8 := (List.range 20).map fun i => (xLo sy - 4 + i).toUInt8
/-- from where his side reaches the part above the mouth to just below the landing depth -/
def caseYs (sy : Syms) : List UInt8 :=
  (List.range 32).map fun i => (Jump.groundY sy - 24 + i).toUInt8
/-- the heights of the ground's landing depth, and just outside -/
def edgeYs (sy : Syms) : List UInt8 :=
  (List.range (sy.LandDepth.toNat + 2)).map fun i => (Jump.groundY sy - 1 + i).toUInt8
/-- fall speed and state at the height `y`: standing; falling up to the top fall speed and one more; rising at a jump's
speeds, only above the ground (the first frame of a jump is already above it) -/
def vyStates (sy : Syms) (y : UInt8) : List (UInt8 × UInt8) :=
  (0, 0) :: ((List.range (sy.MaxFallSpeed.toNat + 2)).flatMap fun vy => [(vy.toUInt8, 1), (vy.toUInt8, 2)]) ++
    if y.toNat < Jump.groundY sy then
      (List.range (256 - sy.FastJumpSpeed.toNat)).map fun i => ((sy.FastJumpSpeed.toNat + i).toUInt8, 1)
    else []
def fewSpeeds (sy : Syms) : List (UInt8 × UInt8) :=
  [((TopSpeed.top sy).toUInt8, 1), ((256 - TopSpeed.top sy).toUInt8, 2), (0, 1), (0, 2)]
def allSpeeds (sy : Syms) : List (UInt8 × UInt8) :=
  (speedsB sy).flatMap fun v => (Potential.mds v).map fun md => (v, md)

def product (xs ys : List UInt8) (vst : UInt8 → List (UInt8 × UInt8)) (vmd : List (UInt8 × UInt8)) (fds : List UInt8) :
    List Case :=
  xs.flatMap fun x => ys.flatMap fun y => (vst y).flatMap fun (vy, st) =>
    vmd.flatMap fun (v, md) => fds.map fun fd => { x, y, v, md, vy, st, fd }

/-- The domain: every position and height with every fall speed and state at a few speeds; every speed at the ends
of the mouth and of the landing depth; the other facing directions on the ground -/
def cases (sy : Syms) : List Case :=
  let ends := [(xLo sy - 1).toUInt8, (xLo sy).toUInt8, (xHi sy).toUInt8]
  let g := Jump.groundY sy
  let stops : List UInt8 := [g.toUInt8, (g + sy.LandDepth.toNat - 1).toUInt8, (g + sy.LandDepth.toNat).toUInt8]
  product (caseXs sy) (caseYs sy) (vyStates sy) (fewSpeeds sy) [1] ++
  product ends stops (fun _ => [(0, 0), (sy.MaxFallSpeed.toUInt8, 2)]) (allSpeeds sy) [1] ++
  product (caseXs sy) (edgeYs sy) (fun _ => [(0, 0), (1, 2)]) [(0, 1), (0, 2)] [2, 3]

def sideCheck (sy : Syms) (m : Machine) : Bool :=
  let mp := withPipe sy m
  (cases sy).all (ruleOk sy mp)

/-! ## From the check to the rule -/

variable {sy : Syms} {m : Machine} {c : Case}

theorem ruleOk_of_check (h : sideCheck sy m = true) (hc : c ∈ cases sy) : ruleOk sy (withPipe sy m) c = true := by
  simp only [sideCheck, List.all_eq_true] at h
  exact h c hc

/-- on every state of the domain the routine enters exactly by the rule -/
theorem enters_eq_rule (h : sideCheck sy m = true) (hc : c ∈ cases sy) :
    enters sy (withPipe sy m) c = rule sy c := by
  have hk := ruleOk_of_check h hc
  simp only [ruleOk, Bool.and_eq_true, beq_iff_eq] at hk
  exact hk.1

/-- an entry is on the ground -/
theorem ground_of_enters (h : sideCheck sy m = true) (hc : c ∈ cases sy) (he : enters sy (withPipe sy m) c = true) :
    onGround sy c = true := by
  rw [enters_eq_rule h hc] at he
  simp only [rule, Bool.and_eq_true] at he
  exact he.1.1

/-- an entry is in the mouth -/
theorem mouth_of_enters (h : sideCheck sy m = true) (hc : c ∈ cases sy) (he : enters sy (withPipe sy m) c = true) :
    xLo sy ≤ c.x.toNat ∧ c.x.toNat ≤ xHi sy := by
  rw [enters_eq_rule h hc] at he
  simp only [rule, inMouth, Bool.and_eq_true, decide_eq_true_eq] at he
  exact he.1.2

/-- left of the mouth there is no entry -/
theorem no_enter_left (h : sideCheck sy m = true) (hc : c ∈ cases sy) {pg : Nat} {f : Int} (hf : 0 ≤ f)
    (hP : 256 * (256 * (pg : Int) + (c.x.toNat : Int)) + f < mouthP sy pg) :
    enters sy (withPipe sy m) c = false := by
  cases he : enters sy (withPipe sy m) c with
  | false => rfl
  | true =>
    have := (mouth_of_enters h hc he).1
    unfold mouthP at hP
    omega

/-! ## From the rule to the frame

`E` is the entry frame. It is a frame on the ground, so the fall has ended by then. -/

/-- leaving the block by a jump: `d` frames from the last frame above its top to the ground. If he is not past the end
of the block by frame `N`, the last frame before he is past it is at least `N`, and that frame is above the top. -/
theorem entry_after_jump {P : Nat → Int} {goal : Int} {N d t E : Nat} (hN : ∀ s, s ≤ N → P s < goal)
    (ht : goal ≤ P (t + 1)) (hd : t + d ≤ E) : N + d ≤ E := by
  have : N ≤ t := by
    by_cases hc : N ≤ t
    · exact hc
    · have := hN (t + 1) (by omega)
      omega
  omega

/-- stepping off the block: `w` frames from the first frame past the end to the ground -/
theorem entry_after_step {P : Nat → Int} {goal : Int} {N w t E : Nat} (hN : ∀ s, s ≤ N → P s < goal)
    (ht : goal ≤ P t) (hw : t + w ≤ E) : N + 1 + w ≤ E := by
  have : N + 1 ≤ t := by
    by_cases hc : N + 1 ≤ t
    · exact hc
    · have := hN t (by omega)
      omega
  omega

/-- a slow jump from the block at frame `T`: at most `c` per frame in the air, at least `air` air frames. If `P` before the
takeoff is at most `B (T − 1)` and this falls short of the mouth for every takeoff in time, frame `E` is not at the mouth -/
theorem slow_short {P : Nat → Int} {L c : Int} {air T E : Nat} {B : Int} (hc : 0 ≤ c)
    (hT : P (T + air) ≤ B + c * ((air : Int) + 1)) (hE : T + air = E) (hshort : B + c * ((air : Int) + 1) < L) :
    P E < L := by
  rw [← hE]
  omega

end Smbrta.SidePipe
