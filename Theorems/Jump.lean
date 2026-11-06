import Theorems.PoleGrab

/-!
# The height of a jump

`vstep` is one frame of the vertical bytes, on the game's movement routine, without collisions.
Page: `Jump.md`.
-/

namespace Smbrta.Jump

open TopSpeed (top)

/-- the vertical state -/
structure VS where
  y : UInt8
  mf : UInt8
  vy : UInt8
  dummy : UInt8
  vf : UInt8
  vfd : UInt8
  origin : UInt8
  /-- `Player_State`: 0 ground, 1 jump, 2 fall -/
  st : UInt8
  /-- A on the previous frame -/
  prevA : Bool
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- one frame, with A pressed or not, and the absolute speed that a jump reads -/
def vstep (sy : Syms) (m0 : Machine) (s : VS) (a : Bool) (abs : UInt8) : VS :=
  let m := poke m0 sy.Player_Y_Position s.y
  let m := poke m sy.Player_Y_MoveForce s.mf
  let m := poke m sy.Player_Y_Speed s.vy
  let m := poke m sy.Player_YMF_Dummy s.dummy
  let m := poke m sy.VerticalForce s.vf
  let m := poke m sy.VerticalForceDown s.vfd
  let m := poke m sy.JumpOrigin_Y_Position s.origin
  let m := poke m sy.Player_State s.st
  let m := poke m sy.Player_XSpeedAbsolute abs
  let m := poke m sy.Player_X_Speed 0
  let m := poke m sy.Left_Right_Buttons 0
  let m := poke m sy.A_B_Buttons (if a then 0x80 else 0)
  let m := poke m sy.PreviousA_B_Buttons (if s.prevA then 0x80 else 0)
  let m := poke m sy.GameEngineSubroutine sy.Eng_PlayerCtrl.toUInt8
  let r := runSub m sy.PlayerMovementSubs 0 0 0
  { y := peek r sy.Player_Y_Position, mf := peek r sy.Player_Y_MoveForce, vy := peek r sy.Player_Y_Speed,
    dummy := peek r sy.Player_YMF_Dummy, vf := peek r sy.VerticalForce, vfd := peek r sy.VerticalForceDown,
    origin := peek r sy.JumpOrigin_Y_Position, st := peek r sy.Player_State, prevA := a }

/-- the top of the ground, as Mario's height: one row below the top of the flagpole's base block -/
def groundY (sy : Syms) : Nat := PoleGrab.topY sy + 16 - sy.FeetAdderY.toNat
/-- his height standing on a block `h` rows above the ground -/
def standY (sy : Syms) (h : Nat) : Nat := groundY sy - 16 * h
/-- from this height down, the side of that block stops him -/
def cornerY (sy : Syms) (h : Nat) : Nat := standY sy h + sy.FeetAdderY.toNat - sy.SideAdderY.toNat

def falling (s : VS) : Bool := s.vy < 0x80

/-- a jump followed frame by frame -/
structure Arc where
  s : VS
  /-- frames since the takeoff frame -/
  k : Nat
  /-- the last of these frames at or below the corner's height -/
  low : Nat
  /-- frames since he was last above the standing height -/
  above : Nat
  /-- at the takeoff, at the air threshold or more -/
  fast : Bool
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- every next frame, with A pressed or not, until he reaches the ground -/
def arcSucc (sy : Syms) (m : Machine) (h : Nat) (x : Arc) : List Arc :=
  if falling x.s && decide (groundY sy ≤ x.s.y.toNat) then []
  else [true, false].map fun a =>
    let t := vstep sy m x.s a 0
    { s := t, k := x.k + 1, low := if cornerY sy h ≤ t.y.toNat then x.k + 1 else x.low,
      above := if t.y.toNat < standY sy h then 0 else x.above + 1, fast := x.fast }

/-- the takeoff frame from the height `y0`, for every takeoff speed -/
def arcStart (sy : Syms) (m : Machine) (y0 h : Nat) : List Arc :=
  let g : VS := { y := y0.toUInt8, mf := 0, vy := 0, dummy := 0, vf := 0, vfd := 0, origin := 0, st := 0, prevA := false }
  ((List.range (top sy + 1)).map fun v =>
    let t := vstep sy m g true v.toUInt8
    ({ s := t, k := 0, low := 0, above := if t.y.toNat < standY sy h then 0 else 1,
       fast := decide (sy.AirFastSpeed.toNat ≤ v) } : Arc)).eraseDups

/-- the frames of a jump: long enough that every jump is over -/
def arcFrames : Nat := 80

/-- all states of all layers -/
def arcAll (sy : Syms) (m : Machine) (y0 h : Nat) : List Arc := Id.run do
  let mut l := arcStart sy m y0 h
  let mut out := l
  for _ in [0:arcFrames] do
    l := Cert.nextS (arcSucc sy m h) l
    out := out ++ l
  return out

/-- stepping off a block at the standing height: the frames until the ground, with the fall force and the
carried fraction left from before -/
def walkFrames (sy : Syms) (m : Machine) (h : Nat) (vfd d0 : UInt8) : Nat := Id.run do
  let mut s : VS := { y := (standY sy h).toUInt8, mf := 0, vy := 0, dummy := d0, vf := vfd, vfd, origin := 0, st := 2, prevA := false }
  for j in [0:arcFrames] do
    s := vstep sy m s false 0
    if groundY sy ≤ s.y.toNat then return j + 1
  return arcFrames

/-! ## What the search shows -/

/-- `P` on every frame of every jump from the height `y0` -/
def arcCheck (sy : Syms) (m : Machine) (y0 h : Nat) (P : Arc → Bool) : Bool :=
  Cert.checkPrunedS (arcSucc sy m h) P (fun _ _ => true) arcFrames (arcStart sy m y0 h)

theorem arc_spec {sy : Syms} {m : Machine} {y0 h : Nat} {P : Arc → Bool} (hc : arcCheck sy m y0 h P = true) :
    ∀ x ∈ arcStart sy m y0 h, ∀ n u, n ≤ arcFrames → Cert.Reach (arcSucc sy m h) x n u → P u = true :=
  Cert.prunedS_spec (arcSucc sy m h) P (fun _ _ => true) (fun _ _ h0 => by simp at h0) arcFrames _ hc

theorem mem_arcSucc {sy : Syms} {m : Machine} {h : Nat} {x u : Arc} (hu : u ∈ arcSucc sy m h x) :
    u.k = x.k + 1 ∧ u.fast = x.fast := by
  unfold arcSucc at hu
  split at hu
  · simp at hu
  · simp only [List.mem_map] at hu
    obtain ⟨_, _, h2⟩ := hu
    rw [← h2]
    exact ⟨rfl, rfl⟩

/-- the counter `k` is the number of frames, and the takeoff class stays -/
theorem arc_k {sy : Syms} {m : Machine} {h : Nat} :
    ∀ {x u : Arc} {n : Nat}, Cert.Reach (arcSucc sy m h) x n u → u.k = x.k + n ∧ u.fast = x.fast
  | _, _, _, .refl _ => ⟨by simp, rfl⟩
  | _, _, _, @Cert.Reach.step _ _ _ y _ _ h1 h2 => by
    obtain ⟨h3, h4⟩ := mem_arcSucc h1
    obtain ⟨h5, h6⟩ := arc_k h2
    exact ⟨by omega, by rw [h6, h4]⟩

/-- the takeoff frame has `k = 0` -/
theorem arcStart_k {sy : Syms} {m : Machine} {y0 h : Nat} {x : Arc} (hx : x ∈ arcStart sy m y0 h) : x.k = 0 := by
  unfold arcStart at hx
  obtain ⟨_, _, h2⟩ := List.mem_map.1 (List.mem_eraseDups.1 hx)
  rw [← h2]

/-- rising at the height of a direct grab, only on the given frame of a slow or a fast jump -/
def riseOk (sy : Syms) (h ks kf : Nat) (x : Arc) : Bool :=
  falling x.s || !(decide (sy.FlagGrabY.toNat ≤ x.s.y.toNat) && decide (x.s.y.toNat < cornerY sy h)) ||
    x.k == (if x.fast then kf else ks)

/-- falling onto the block (height `h`), the frame and the last frame at the corner's height are at least one
of the given pairs -/
def windowOk (sy : Syms) (h : Nat) (slow fast : List (Nat × Nat)) (x : Arc) : Bool :=
  !(falling x.s && decide (standY sy h ≤ x.s.y.toNat) && decide (x.s.y.toNat < standY sy h + sy.LandDepth.toNat)) ||
    (if x.fast then fast else slow).any fun q => decide (q.1 ≤ x.low) && decide (q.2 ≤ x.k)

/-- reaching the ground from a jump off the block: the frames since he was above it, and in the air -/
def dropOk (sy : Syms) (aboveS aboveF airS : Nat) (x : Arc) : Bool :=
  !(falling x.s && decide (groundY sy ≤ x.s.y.toNat)) ||
    (if x.fast then decide (aboveF ≤ x.above) else decide (aboveS ≤ x.above) && decide (airS ≤ x.k))

/-- the fall forces of the jumps -/
def forces (sy : Syms) (m : Machine) : List UInt8 :=
  ((arcStart sy m (groundY sy) 1).map (·.s.vfd)).eraseDups

/-- stepping off the block takes at least `w` frames, for every fall force and carried fraction -/
def walkOk (sy : Syms) (m : Machine) (h w : Nat) : Bool :=
  (forces sy m).all fun f => TopSpeed.bytes.all fun d => decide (w ≤ walkFrames sy m h f d)

/-- what the search finds, for the numbers of the checks -/
structure Summary where
  slow : List (Nat × Nat)
  fast : List (Nat × Nat)
  aboveS : Nat
  aboveF : Nat
  airS : Nat
  walk : Nat
  deriving Repr, Inhabited

def summary (sy : Syms) (m : Machine) (h : Nat) : Summary :=
  let gy := groundY sy
  let st := standY sy h
  let up := arcAll sy m gy h
  let win := up.filter fun x => falling x.s && decide (st ≤ x.s.y.toNat) && decide (x.s.y.toNat < st + sy.LandDepth.toNat)
  let pairs (f : Bool) : List (Nat × Nat) :=
    let ps := ((win.filter (·.fast == f)).map fun x => (x.low, x.k)).eraseDups
    (ps.filter fun p => !ps.any fun q => q != p && decide (q.1 ≤ p.1) && decide (q.2 ≤ p.2)).mergeSort
      (fun a b => decide (a.1 ≤ b.1))
  let bl := arcAll sy m st h
  let land (f : Bool) := bl.filter fun x => x.fast == f && falling x.s && decide (gy ≤ x.s.y.toNat)
  let mn (l : List Nat) := l.foldl min 1000
  { slow := pairs false, fast := pairs true,
    aboveS := mn ((land false).map (·.above)), aboveF := mn ((land true).map (·.above)),
    airS := mn ((land false).map (·.k)),
    walk := mn ((forces sy m).flatMap fun f => TopSpeed.bytes.map fun d => walkFrames sy m h f d) }

end Smbrta.Jump
