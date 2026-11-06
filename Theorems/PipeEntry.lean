import Theorems.PoleGrab

/-!
# Entering the vertical pipe

The collision routine starts the vertical pipe routine when Mario stands on the pipe with both feet, on
a frame he lands, with Down held. So he has to be at the window where both feet are on the pipe's top.
If the position bounds keep him left of that window, he does not enter. Page: `PipeEntry.md`.

`pipeCheck` runs `PlayerBGCollision` on every state near the pipe's top and compares with `rule`.
The frame theorems are about frames (`TopSpeed.Frame`) whose collision follows `rule`.
-/

namespace Smbrta.PipeEntry

open TopSpeed (Frame speedsB)
open PoleGrab (Next)

/-! ## The pipe, from its level object -/

/-- the pipe's left column on its page: the high nybble of the object -/
def column (sy : Syms) : Nat := sy.PipeColumnByte.toNat / 16
/-- the pipe's top row: the low nybble of the object -/
def row (sy : Syms) : Nat := sy.PipeColumnByte.toNat % 16
/-- the top of the pipe, in pixels -/
def topY (sy : Syms) : Nat := sy.BlockBufferTopY.toNat + 16 * row sy
/-- Mario's height standing on the pipe -/
def standY (sy : Syms) : Nat := topY sy - sy.FeetAdderY.toNat
/-- the left foot's offset from `x`: the feet lie symmetrically in his 16-pixel box. `pipeCheck` tests this
against the routine. -/
def footL (sy : Syms) : Nat := 15 - sy.FeetAdderX.toNat
/-- the left end of the window: the right foot reaches the right column -/
def xLo (sy : Syms) : Nat := 16 * (column sy + 1) - sy.FeetAdderX.toNat
/-- the right end of the window: the left foot is still in the left column -/
def xHi (sy : Syms) : Nat := 16 * (column sy + 1) - 1 - footL sy

/-- the position of the window's left end on page `pg`, with `P = 256·(256·pg + x) + fraction` -/
def windowP (sy : Syms) (pg : Nat) : Int := 256 * (256 * (pg : Int) + (xLo sy : Int))

/-! ## The pipe's page, from the level data -/

/-- the object pairs after the level data's header: at most `n` -/
def pairs (sy : Syms) (m : Machine) (n : Nat) : List (UInt8 × UInt8) :=
  (List.range n).map fun i =>
    (romByte m (sy.L_GroundArea6 + (2 + 2 * i).toUInt16), romByte m (sy.L_GroundArea6 + (3 + 2 * i).toUInt16))

/-- enough for a level -/
def maxPairs : Nat := 128

/-- the pairs before the pipe's -/
def before (sy : Syms) (m : Machine) : List (UInt8 × UInt8) :=
  (pairs sy m maxPairs).takeWhile fun p => p.1 != sy.PipeColumnByte.toUInt8

/-- the pipe's pair and the pairs after it -/
def fromPipe (sy : Syms) (m : Machine) : List (UInt8 × UInt8) :=
  (pairs sy m maxPairs).dropWhile fun p => p.1 != sy.PipeColumnByte.toUInt8

def pageBit (p : UInt8 × UInt8) : Bool := p.2 ≥ 0x80

/-- the pipe's page: second bytes with bit 7 set among the pairs up to and including its own -/
def pipePage (sy : Syms) (m : Machine) : Nat :=
  (before sy m).countP pageBit + ((fromPipe sy m).head?.map pageBit == some true).toNat

/-- a vertical pipe with the usage bit, the one drawn with the tiles that can be entered -/
def warp (p : UInt8 × UInt8) : Bool := p.1 % 16 < 12 && p.2 &&& 0x78 == 0x78

/-- a row 13 object may set the page directly -/
def pageControl (p : UInt8 × UInt8) : Bool := p.1 % 16 == 13

/-- the pipe's object is found and is such a pipe; before it no such pipe, and the page is the count -/
def levelOk (sy : Syms) (m : Machine) : Bool :=
  (fromPipe sy m).head?.map warp == some true &&
    (before sy m).all fun p => !warp p && !pageControl p

/-! ## The routine against the rule -/

/-- a machine with the pipe's top in the first block buffer, all else down to that row empty. The routine reads
the page only through its low bit. -/
def withPipe (sy : Syms) (m0 : Machine) : Machine :=
  (List.range (row sy + 1)).foldl (fun m r =>
    (List.range 16).foldl (fun m c =>
      let tile : UInt8 :=
        if r != row sy then 0
        else if c == column sy then sy.PipeLeftTile.toUInt8
        else if c == column sy + 1 then sy.PipeRightTile.toUInt8 else 0
      poke m (sy.Block_Buffer_1 + (c + 16 * r).toUInt16) tile) m) m0

structure Case where
  x : UInt8
  y : UInt8
  v : UInt8
  md : UInt8
  vy : UInt8
  st : UInt8
  /-- `Up_Down_Buttons` -/
  ud : UInt8
  fd : UInt8
  /-- `PlayerSize`: 1 small, 0 big -/
  size : UInt8
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
  let m := poke m sy.Up_Down_Buttons c.ud
  let m := poke m sy.PlayerSize c.size
  let m := poke m sy.GameEngineSubroutine sy.Eng_PlayerCtrl.toUInt8
  runSub m sy.PlayerBGCollision 0 0 0

/-- after the routine: it started the vertical pipe routine -/
def enteredIn (sy : Syms) (r : Machine) : Bool :=
  peek r sy.GameEngineSubroutine == sy.EngVerticalPipe.toUInt8

def enters (sy : Syms) (m : Machine) (c : Case) : Bool := enteredIn sy (collide sy m c)

def down (ud : UInt8) : Bool := ud &&& 4 != 0
def falling (vy : UInt8) : Bool := decide (0 ≤ sbyte vy)
/-- the feet in the landing depth of the pipe's top -/
def onTop (sy : Syms) (y : UInt8) : Bool :=
  decide (topY sy ≤ y.toNat + sy.FeetAdderY.toNat) && decide (y.toNat + sy.FeetAdderY.toNat < topY sy + sy.LandDepth.toNat)
/-- left foot in the left column, right foot in the right column -/
def inWindow (sy : Syms) (x : UInt8) : Bool := decide (xLo sy ≤ x.toNat) && decide (x.toNat ≤ xHi sy)

/-- the rule -/
def rule (sy : Syms) (c : Case) : Bool := down c.ud && falling c.vy && onTop sy c.y && inWindow sy c.x

/-- entered exactly by the rule. On entering he stands on the pipe where he is; otherwise the routine number is
unchanged. -/
def ruleOk (sy : Syms) (m : Machine) (c : Case) : Bool :=
  let r := collide sy m c
  enteredIn sy r == rule sy c &&
    (if rule sy c then
      (peek r sy.Player_Y_Position).toNat == standY sy && peek r sy.Player_X_Position == c.x
    else peek r sy.GameEngineSubroutine == sy.Eng_PlayerCtrl.toUInt8)

/-- how far the checks go left and right of the window -/
def margin : Nat := 4
def caseXs (sy : Syms) : List UInt8 :=
  (List.range (xHi sy + 2 * margin + 1 - xLo sy)).map fun i => (xLo sy - margin + i).toUInt8
/-- the ends of the window, and just outside -/
def edgeXs (sy : Syms) : List UInt8 :=
  [xLo sy - 1, xLo sy, xHi sy, xHi sy + 1].map (·.toUInt8)
def allXs : List UInt8 := TopSpeed.bytes
/-- from a few pixels above the pipe's top to the bottom of its top row. Lower, the feet are in another row. -/
def caseYs (sy : Syms) : List UInt8 :=
  (List.range 22).map fun i => (standY sy - 6 + i).toUInt8
/-- the heights in the landing depth -/
def landYs (sy : Syms) : List UInt8 :=
  (List.range sy.LandDepth.toNat).map fun i => (standY sy + i).toUInt8
/-- both ends of the landing depth, and just below -/
def edgeYs (sy : Syms) : List UInt8 :=
  [standY sy, standY sy + sy.LandDepth.toNat - 1, standY sy + sy.LandDepth.toNat].map (·.toUInt8)
/-- fall speed and state: standing; falling up to the top fall speed; rising at the speeds of a jump -/
def vyStates (sy : Syms) : List (UInt8 × UInt8) :=
  (0, 0) :: ((List.range (sy.MaxFallSpeed.toNat + 1)).flatMap fun vy => [(vy.toUInt8, 1), (vy.toUInt8, 2)]) ++
    (List.range (256 - sy.FastJumpSpeed.toNat)).map fun i => ((sy.FastJumpSpeed.toNat + i).toUInt8, 1)
/-- all speeds, with the moving directions that fit -/
def allSpeeds (sy : Syms) : List (UInt8 × UInt8) :=
  (speedsB sy).flatMap fun v => (Potential.mds v).map fun md => (v, md)
/-- top speed both ways, and stopped -/
def fewSpeeds (sy : Syms) : List (UInt8 × UInt8) :=
  [((TopSpeed.top sy).toUInt8, 1), ((256 - TopSpeed.top sy).toUInt8, 2), (0, 1), (0, 2)]

def product (xs ys : List UInt8) (vst : List (UInt8 × UInt8)) (uds : List UInt8)
    (vmd : List (UInt8 × UInt8)) (fds : List UInt8) (size : UInt8) : List Case :=
  xs.flatMap fun x => ys.flatMap fun y => vst.flatMap fun (vy, st) => uds.flatMap fun ud =>
    vmd.flatMap fun (v, md) => fds.map fun fd => { x, y, v, md, vy, st, ud, fd, size }

/-- The domain, as a union so that it stays small:
every position and height near the pipe with every fall speed and state, Down or not, at the speeds that
`fewSpeeds` lists; every speed at the ends of the window and of the landing depth, with Up and Down in all ways; the
other facing directions; a big Mario; and every `x` of the page on a landing with Down. -/
def cases (sy : Syms) : List Case :=
  product (caseXs sy) (caseYs sy) (vyStates sy) [0, 4] (fewSpeeds sy) [1] 1 ++
  product (edgeXs sy) (edgeYs sy) [(0, 0), (sy.MaxFallSpeed.toUInt8, 2)] [0, 4, 8, 12] (allSpeeds sy) [1] 1 ++
  product (caseXs sy) (caseYs sy) [(0, 0), (0, 2)] [0, 4] [(0, 1)] [2, 3] 1 ++
  product (caseXs sy) (caseYs sy) (vyStates sy) [0, 4] [(0, 1)] [1] 0 ++
  product allXs (landYs sy) [(0, 0), (1, 2)] [4] [(0, 1)] [1] 1

def pipeCheck (sy : Syms) (m : Machine) : Bool :=
  let mp := withPipe sy m
  (cases sy).all (ruleOk sy mp)

/-! ## From the check to the rule -/

variable {sy : Syms} {m : Machine} {c : Case}

theorem ruleOk_of_check (h : pipeCheck sy m = true) (hc : c ∈ cases sy) : ruleOk sy (withPipe sy m) c = true := by
  simp only [pipeCheck, List.all_eq_true] at h
  exact h c hc

/-- on every state of the domain the routine enters exactly by the rule -/
theorem enters_eq_rule (h : pipeCheck sy m = true) (hc : c ∈ cases sy) :
    enters sy (withPipe sy m) c = rule sy c := by
  have hk := ruleOk_of_check h hc
  simp only [ruleOk, Bool.and_eq_true, beq_iff_eq] at hk
  exact hk.1

/-- without the rule the routine number is unchanged -/
theorem unchanged_of_not_rule (h : pipeCheck sy m = true) (hc : c ∈ cases sy) (hr : rule sy c = false) :
    peek (collide sy (withPipe sy m) c) sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8 := by
  have hk := ruleOk_of_check h hc
  simp only [ruleOk, hr, Bool.and_eq_true, beq_iff_eq] at hk
  simpa using hk.2

theorem window_of_rule (h : rule sy c = true) : xLo sy ≤ c.x.toNat ∧ c.x.toNat ≤ xHi sy := by
  simp only [rule, inWindow, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- entering needs `x` in the window -/
theorem window_of_enters (h : pipeCheck sy m = true) (hc : c ∈ cases sy)
    (he : enters sy (withPipe sy m) c = true) : xLo sy ≤ c.x.toNat ∧ c.x.toNat ≤ xHi sy :=
  window_of_rule (by rw [← enters_eq_rule h hc]; exact he)

/-- the same as a position on page `pg`: `P ≥` the window's left end -/
theorem enter_needs (h : pipeCheck sy m = true) (hc : c ∈ cases sy)
    (he : enters sy (withPipe sy m) c = true) (pg : Nat) {f : Int} (hf : 0 ≤ f) :
    windowP sy pg ≤ 256 * (256 * (pg : Int) + (c.x.toNat : Int)) + f := by
  have := (window_of_enters h hc he).1
  unfold windowP
  omega

/-- left of the window, the routine does not enter -/
theorem no_enter_left (h : pipeCheck sy m = true) (hc : c ∈ cases sy) {pg : Nat} {f : Int} (hf : 0 ≤ f)
    (hP : 256 * (256 * (pg : Int) + (c.x.toNat : Int)) + f < windowP sy pg) :
    enters sy (withPipe sy m) c = false := by
  cases he : enters sy (withPipe sy m) c with
  | false => rfl
  | true =>
    have := enter_needs h hc he pg hf
    omega

/-! ## From the rule to the frames

Frames are numbered: `fr t` is frame `t`, `Enter t` says that its collision enters the pipe, and `P₂` is the position
the collision reads. -/

variable {top amax : Int}

/-- no frame left of the window enters -/
theorem no_entry_of_left (fr : Nat → Frame top amax) (Enter : Nat → Prop) (L : Int) (T : Nat)
    (hrule : ∀ t, Enter t → L ≤ (fr t).P₂) (hleft : ∀ t, t ≤ T → (fr t).P₂ < L) :
    ∀ t, t ≤ T → ¬ Enter t := by
  intro t ht he
  have h1 := hrule t he
  have h2 := hleft t ht
  omega

/-- the move of a frame is at most `16·top` -/
theorem p2_le (f : Frame top amax) (hv : -top ≤ f.v ∧ f.v ≤ top) : f.P₂ ≤ f.P + 16 * top := by
  have h1 : -top ≤ f.v₁ ∧ f.v₁ ≤ top := by
    rcases f.anim with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  have h2 := f.friction h1
  have hm := f.move
  omega

/-- after frame `N`, each frame moves at most `16·top` -/
theorem chain_le (h16 : 16 ≤ top) (fr : Nat → Frame top amax) (N : Nat) (B : Int)
    (hB : (fr N).P' ≤ B) (hv : -top ≤ (fr N).v' ∧ (fr N).v' ≤ top)
    (hn : ∀ j, Next (fr (N + j)) (fr (N + j + 1))) :
    ∀ k : Nat, (fr (N + k + 1)).P₂ ≤ B + 16 * top * ((k : Int) + 1) ∧
      (fr (N + k + 1)).P' ≤ B + 16 * top * ((k : Int) + 1) ∧
      (-top ≤ (fr (N + k + 1)).v' ∧ (fr (N + k + 1)).v' ≤ top)
  | 0 => by
    obtain ⟨h1, _, h2⟩ := hn 0
    simp only [Nat.add_zero] at h1 h2 ⊢
    have hg : -top ≤ (fr (N + 1)).v ∧ (fr (N + 1)).v ≤ top := by rw [h1]; exact hv
    have hb := (fr (N + 1)).bound h16 hg
    have hp := p2_le (fr (N + 1)) hg
    have e : 16 * top * (((0 : Nat) : Int) + 1) = 16 * top := by simp
    rw [e]
    refine ⟨by omega, by have := hb.2; omega, hb.1⟩
  | k + 1 => by
    obtain ⟨_, h3, h4⟩ := chain_le h16 fr N B hB hv hn k
    obtain ⟨h1, _, h2⟩ := hn (k + 1)
    rw [show N + (k + 1) = N + k + 1 by omega] at h1 h2 ⊢
    have hg : -top ≤ (fr (N + k + 1 + 1)).v ∧ (fr (N + k + 1 + 1)).v ≤ top := by rw [h1]; exact h4
    have hb := (fr (N + k + 1 + 1)).bound h16 hg
    have hp := p2_le (fr (N + k + 1 + 1)) hg
    have e : 16 * top * (((k + 1 : Nat) : Int) + 1) = 16 * top * ((k : Int) + 1) + 16 * top := by
      push_cast
      rw [show (k : Int) + 1 + 1 = ((k : Int) + 1) + 1 from rfl, Int.mul_add, Int.mul_one]
    rw [e]
    refine ⟨by omega, by have := hb.2; omega, hb.1⟩

/-- up to frame `N` the position is at most `B`; after it each frame moves at most `16·top`. If that leaves him left
of `L` at frame `T`, and entering needs `L`, there is no entry by frame `T`. -/
theorem no_entry_by (h16 : 16 ≤ top) (fr : Nat → Frame top amax) (Enter : Nat → Prop) (L B : Int) (N T : Nat)
    (hrule : ∀ t, Enter t → L ≤ (fr t).P₂)
    (hopen : ∀ t, t ≤ N → (fr t).P₂ ≤ B)
    (hB : (fr N).P' ≤ B) (hv : -top ≤ (fr N).v' ∧ (fr N).v' ≤ top)
    (hn : ∀ j, Next (fr (N + j)) (fr (N + j + 1)))
    (hgap : B + 16 * top * ((T - N : Nat) : Int) < L) :
    ∀ t, t ≤ T → ¬ Enter t := by
  have hc : 0 ≤ 16 * top := by omega
  refine no_entry_of_left fr Enter L T hrule fun t ht => ?_
  by_cases htN : t ≤ N
  · have h1 := hopen t htN
    have h0 : 0 ≤ 16 * top * ((T - N : Nat) : Int) := Int.mul_nonneg hc (by omega)
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, t = N + k + 1 := ⟨t - N - 1, by omega⟩
    have h1 := (chain_le h16 fr N B hB hv hn k).1
    have h2 : 16 * top * ((k : Int) + 1) ≤ 16 * top * ((T - N : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hc
    omega

/-- the rule on frames: an entering frame's state is in the domain, on page `pg`, at the position its collision reads -/
theorem rule_of_cases (h : pipeCheck sy m = true) (fr : Nat → Frame top amax) (Enter : Nat → Prop) (pg : Nat)
    (hE : ∀ t, Enter t → ∃ c ∈ cases sy, enters sy (withPipe sy m) c = true ∧
      ∃ f : Int, 0 ≤ f ∧ (fr t).P₂ = 256 * (256 * (pg : Int) + (c.x.toNat : Int)) + f) :
    ∀ t, Enter t → windowP sy pg ≤ (fr t).P₂ := by
  intro t he
  obtain ⟨c, hc, hen, f, hf, hP⟩ := hE t he
  rw [hP]
  exact enter_needs h hc hen pg hf

/-- the same bound for a search like `Opening.opening`: up to `N` steps the distance is at most `D`, after them it
grows by at most `c` per step. If that leaves him left of `L` at step `T`, it does at every step up to `T`. -/
theorem model_left {σ : Type} {succ : σ → List σ} {s0 : σ} {dist : σ → Int} {P₀ D c L : Int} {N T : Nat}
    (hc : 0 ≤ c)
    (h1 : ∀ k u, k ≤ N → Cert.Reach succ s0 k u → dist u ≤ D)
    (h2 : ∀ k u, Cert.Reach succ s0 (N + k) u → dist u ≤ D + c * (k : Int))
    (hgap : P₀ + D + c * ((T - N : Nat) : Int) < L) :
    ∀ t u, t ≤ T → Cert.Reach succ s0 t u → P₀ + dist u < L := by
  intro t u ht hr
  by_cases htN : t ≤ N
  · have h3 := h1 t u htN hr
    have h0 : 0 ≤ c * ((T - N : Nat) : Int) := Int.mul_nonneg hc (by omega)
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, t = N + k := ⟨t - N, by omega⟩
    have h3 := h2 k u hr
    have h4 : c * (k : Int) ≤ c * ((T - N : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hc
    omega

end Smbrta.PipeEntry
