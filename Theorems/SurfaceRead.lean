import Theorems.FrameTime
import Theorems.CtrlKeep

/-!
# Above ground: a real frame read as a `TopSpeed.Frame`

`PoleJoin.Run` had the frames `fr` as data, and the field `reads` of `SurfaceFrames.OnFrames` said that they are read from the machines. Here a frame is a definition on
the machines: `frameE` for a frame before the touch, `frameH` for the touch's frame. Each one starts with the speed, the subspeed and the position of the machine where the
frame starts, by the definition. When the frame meets the conditions of `ReadE` (resp. `ReadH`) on one frame, the rest is read from the real frame too:

* `frame_readE`: from the player's routine (`FrameModel.AtFrame`), with nothing written to the horizontal bytes before it, the frame's time (`FrameModel.InTime`), the
  position away from both ends of its range, and what the collision routine and the rest of the frame do (`CollideE`), the frame is a `TopSpeed.Frame` that ends with the
  bytes of the frame's end. It is `FrameModel.frame_readR` with `CollideE` in place of `FrameModel.Collide`: at the screen's left edge the scroll handler sets the
  position to the edge, which `Collide` does not allow; `CollideE` allows it, as `TopSpeed.Frame.impedeP` does, when he moves left or not at all, and asks that it does not
  move him left there.
* `frame_readH`: the touch's frame, up to the scroll handler. The touch moves him after it, so the frame's end is not that of a `Frame`; its `P₂` is the position at the
  scroll handler.

There is no game data in this file. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.SurfaceRead

open FrameModel (AtFrame InTime hBytes moveLen frame_pathI tail_spec facts_of base_good stepN stepN_add trace_inFrame InFrameN posP_congr posP_eq posOf_range sbyte_range
  speed_int planOf caseOf cutSame_eq caseOf_memF I I_lt)
open TopSpeed (top Frame)
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms}

/-- **What the collision routine and the rest of the frame do**, from the scroll handler `Q` to the frame's end `b`; `M` is the machine where the frame starts. The speed
stays or becomes 0, the subspeed stays, and the position stays, goes 1 px back, or, when he moves left or not at all, goes right but not past 1 px right of where the frame
started: the push of a block on his left and the screen's left edge. -/
structure CollideE (sy : Syms) (M Q b : Machine) : Prop where
  v : peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed ∨ peek b sy.Player_X_Speed = 0
  f : peek b sy.Player_X_MoveForce = peek Q sy.Player_X_MoveForce
  P : posP sy b = posP sy Q ∨ posP sy b = posP sy Q - 256 ∨
    (posP sy Q ≤ posP sy b ∧ posP sy b ≤ posP sy M + 256 ∧ sbyte (peek Q sy.Player_X_Speed) ≤ 0)

/-- **`CollideE` but the speed**: the subspeed stays, and the position as in `CollideE`. The speed's part `CollideE.v` is a theorem on the frames above ground
(`CollideKeep.speed_end`: a walk from the scroll handler to the frame's end). -/
structure CollideR (sy : Syms) (M Q b : Machine) : Prop where
  f : peek b sy.Player_X_MoveForce = peek Q sy.Player_X_MoveForce
  P : posP sy b = posP sy Q ∨ posP sy b = posP sy Q - 256 ∨
    (posP sy Q ≤ posP sy b ∧ posP sy b ≤ posP sy M + 256 ∧ sbyte (peek Q sy.Player_X_Speed) ≤ 0)

/-- `CollideR` and the speed's part give `CollideE` -/
theorem CollideR.toE {M Q b : Machine} (h : CollideR sy M Q b)
    (v : peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed ∨ peek b sy.Player_X_Speed = 0) : CollideE sy M Q b := ⟨v, h.f, h.P⟩

/-- `CollideE` reads only the position of the frame's start -/
theorem CollideE.ofP {M M' Q b : Machine} (h : CollideE sy M Q b) (e : posP sy M = posP sy M') : CollideE sy M' Q b :=
  ⟨h.v, h.f, by rw [← e]; exact h.P⟩

/-- `CollideE` as a check, for a program -/
def collideEB (sy : Syms) (M Q b : Machine) : Bool :=
  (peek b sy.Player_X_Speed == peek Q sy.Player_X_Speed || peek b sy.Player_X_Speed == 0) && peek b sy.Player_X_MoveForce == peek Q sy.Player_X_MoveForce &&
    (posP sy b == posP sy Q || posP sy b == posP sy Q - 256 ||
      (decide (posP sy Q ≤ posP sy b) && decide (posP sy b ≤ posP sy M + 256) && decide (sbyte (peek Q sy.Player_X_Speed) ≤ 0)))

/-- the position is away from both ends of its range -/
def Far (sy : Syms) (m : Machine) : Prop := 2048 ≤ posP sy m ∧ posP sy m + 2048 < 0x1000000

/-- **What a frame up to the scroll handler needs to be read**: the frame of `M` with the input `i`, which comes to the player's routine at the instruction `n₀`. The
checks on the ROM of `FrameModel` (`modelOK`) and of the friction (`TopSpeed.frictionCheck`); the state at the player's routine; nothing writes the horizontal bytes before
it; the frame's time, with the idle loop `EndlessLoop`; the position away from both ends of its range. -/
structure ReadH (sy : Syms) (m0 M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  model : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true
  fric : TopSpeed.frictionCheck sy m0 = true
  at_frame : AtFrame sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i n₀)
  before : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a
  time : InTime (FrameModel.Rom.of m0) sy.EndlessLoop M i n₀
  far : Far sy M

/-- **What a whole frame needs to be read**: `ReadH`, and what the collision routine and the rest of the frame do at each arrival at the scroll handler -/
structure ReadE (sy : Syms) (m0 M : Machine) (i : UInt8) (n₀ : Nat) : Prop extends ReadH sy m0 M i n₀ where
  collide : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → CollideE sy M (trace M i k) (frame M i)

/-! ## A real frame is a `TopSpeed.Frame` -/

/-- **The frame up to the scroll handler is a `TopSpeed.Frame`** that ends there: the walks of `FrameModel.frame_pathI` and `FrameModel.tail_spec`, as in
`FrameModel.frame_readR`. It comes to the scroll handler at the instruction `k`, and `v₂`, `f₂`, `P₂` are the bytes there. -/
theorem read_move {m0 M : Machine} {i : UInt8} {n₀ : Nat} (h : ReadH sy m0 M i n₀) :
    ∃ f : Frame (top sy : Int) (amax sy m0), ∃ k, n₀ ≤ k ∧ (trace M i k).pc = sy.PlayerSubs ∧
      f.v = sbyte (peek M sy.Player_X_Speed) ∧ f.f = ((peek M sy.Player_X_MoveForce).toNat : Int) ∧ f.P = posP sy M ∧
      f.v₂ = sbyte (peek (trace M i k) sy.Player_X_Speed) ∧ f.f₂ = ((peek (trace M i k) sy.Player_X_MoveForce).toNat : Int) ∧ f.P₂ = posP sy (trace M i k) ∧
      f.v' = f.v₂ ∧ f.f' = f.f₂ ∧ f.P' = f.P₂ := by
  have hF := facts_of h.model
  have hb := base_good hF.base
  obtain ⟨k1, v₁, f₁, b1, A1, an, G1, S1, I1⟩ := frame_pathI hb h.fric hF h.at_frame
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h.at_frame)
  have e4 : t = (planOf sy m0 (FrameModel.ctrlStack sy m0) (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, b2, g2, p2, v2, ff2, d2, r2, m2, q2, I2⟩ := tail_spec htl hF.digits A1
  have e0 := (trace_inFrame h.time.loop h.time.start (InFrameN.add' I1 rfl I2) h.time.time (k1 + k2) (Nat.le_refl _)).1
  rw [stepN_add] at e0
  generalize hB : stepN k2 (stepN k1 (trace M i n₀)) = B at e0 v2 ff2 q2 p2
  have ev : peek (trace M i n₀) sy.Player_X_Speed = peek M sy.Player_X_Speed := h.before _ (by simp [hBytes])
  have ef : peek (trace M i n₀) sy.Player_X_MoveForce = peek M sy.Player_X_MoveForce := h.before _ (by simp [hBytes])
  have eP : posP sy (trace M i n₀) = posP sy M := posP_congr h.before
  obtain ⟨g1, g2'⟩ := G1
  have ePk : posP sy (stepN k1 (trace M i n₀)) = posP sy (trace M i n₀) := by
    rw [posP_eq, posP_eq]
    obtain ⟨s1, s2, s3⟩ := S1
    show FrameModel.posOf ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_PageLoc)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Position))
        ((stepN k1 (trace M i n₀)).ram.get! (I sy.SprObject_X_MoveForce)) =
      FrameModel.posOf ((trace M i n₀).ram.get! (I sy.Player_PageLoc)) ((trace M i n₀).ram.get! (I sy.Player_X_Position)) ((trace M i n₀).ram.get! (I sy.SprObject_X_MoveForce))
    rw [s1, s2, s3]
  have hv2 : B.ram.get! (I sy.Player_X_Speed) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed) := v2
  have hf2 : B.ram.get! (I sy.Player_X_MoveForce) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce) := ff2
  have hr1 := speed_int g1
  have hmove : posP sy B = posP sy M + 16 * sbyte (B.ram.get! (I sy.Player_X_Speed)) := by
    rw [hv2]
    obtain ⟨a1, a2⟩ := posOf_range (peek B sy.Player_PageLoc) (peek B sy.Player_X_Position) (peek B sy.SprObject_X_MoveForce)
    rw [← posP_eq] at a1 a2
    have a3 := sbyte_range ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed))
    have a4 := h.far
    unfold Far at a4
    rw [ePk, eP] at q2
    omega
  have hfr1 := ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce)).toNat_lt
  refine ⟨{ v := sbyte (peek M sy.Player_X_Speed), f := ((peek M sy.Player_X_MoveForce).toNat : Int), P := posP sy M,
            v₁ := sbyte v₁, f₁ := (f₁.toNat : Int),
            v₂ := sbyte (B.ram.get! (I sy.Player_X_Speed)), f₂ := ((B.ram.get! (I sy.Player_X_MoveForce)).toNat : Int), P₂ := posP sy B,
            v' := sbyte (B.ram.get! (I sy.Player_X_Speed)), f' := ((B.ram.get! (I sy.Player_X_MoveForce)).toNat : Int), P' := posP sy B,
            anim := ?_, friction := ?_, friction_gain := ?_, frac := ?_, move := hmove, impedeV := Or.inl rfl, impedeF := rfl, impedeP := Or.inl rfl },
    n₀ + (k1 + k2), by omega, by rw [e0]; exact p2, rfl, rfl, rfl, by rw [e0]; rfl, by rw [e0]; rfl, by rw [e0], rfl, rfl, rfl⟩
  · rcases an with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [a1]
        exact congrArg sbyte ev
      · rw [a2]
        exact congrArg (fun x : UInt8 => (x.toNat : Int)) ef
    · right
      rw [a1, a2]
      exact ⟨rfl, rfl⟩
  · intro _
    rw [hv2]
    exact hr1
  · rw [hv2, hf2]
    exact g2'
  · rw [hf2]
    omega

/-- **A real frame is a `TopSpeed.Frame`**, with `CollideE` for the part after the scroll handler: `FrameModel.frame_readR` with the screen's left edge. The collision
routine and the rest of the frame move him at most 1 px left from the end of the move (`P₂ − 256 ≤ P'`). -/
theorem frame_readE {m0 M : Machine} {i : UInt8} {n₀ : Nat} (h : ReadE sy m0 M i n₀) :
    ∃ f : Frame (top sy : Int) (amax sy m0), f.v = sbyte (peek M sy.Player_X_Speed) ∧ f.f = ((peek M sy.Player_X_MoveForce).toNat : Int) ∧ f.P = posP sy M ∧
      f.v' = sbyte (peek (frame M i) sy.Player_X_Speed) ∧ f.f' = ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int) ∧ f.P' = posP sy (frame M i) ∧
      f.P₂ - 256 ≤ f.P' := by
  obtain ⟨c, k, hk, hpc, e1, e2, e3, e4, e5, e6, _, _, _⟩ := read_move h.toReadH
  have hco := h.collide k hk hpc
  generalize hQ : trace M i k = Q at hco e4 e5 e6
  generalize hb : frame M i = b at hco ⊢
  refine ⟨{ c with
      v' := sbyte (peek b sy.Player_X_Speed), f' := ((peek b sy.Player_X_MoveForce).toNat : Int), P' := posP sy b,
      impedeV := ?_, impedeF := ?_, impedeP := ?_ }, e1, e2, e3, rfl, rfl, rfl, ?_⟩
  · rcases hco.v with e | e
    · left
      show sbyte (peek b sy.Player_X_Speed) = c.v₂
      rw [e, e4]
    · right
      show sbyte (peek b sy.Player_X_Speed) = 0
      rw [e]
      rfl
  · show ((peek b sy.Player_X_MoveForce).toNat : Int) = c.f₂
    rw [hco.f, e5]
  · show posP sy b = c.P₂ ∨ posP sy b = c.P₂ - 256 ∨ (posP sy b ≤ c.P + 256 ∧ c.v₂ ≤ 0)
    rw [e6, e3, e4]
    rcases hco.P with e | e | ⟨_, e7, e8⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨e7, e8⟩)
  · show c.P₂ - 256 ≤ posP sy b
    rw [e6]
    rcases hco.P with e | e | ⟨e7, _, _⟩ <;> omega

/-! ## The frames as definitions -/

/-- a frame that starts at `v`, `f`, `P` and stops there: what `frameE` and `frameH` are when the conditions fail -/
def stillFrame (sy : Syms) (m0 : Machine) (v f P : Int) : Frame (top sy : Int) (amax sy m0) :=
  { v, f, P, v₁ := v, f₁ := f, v₂ := 0, f₂ := 0, P₂ := P, v' := 0, f' := 0, P' := P,
    anim := Or.inl ⟨rfl, rfl⟩, friction := fun h => by omega,
    friction_gain := by have := FastAccel.amax_nonneg sy m0; omega,
    frac := by omega, move := by omega, impedeV := Or.inl rfl, impedeF := rfl, impedeP := Or.inl rfl }

/-- a frame with its start replaced by equal values -/
def withStart {tp am : Int} (c : Frame tp am) (v f P : Int) (hv : c.v = v) (hf : c.f = f) (hP : c.P = P) : Frame tp am :=
  { c with
    v, f, P
    anim := by rw [← hv, ← hf]; exact c.anim
    move := by rw [← hP]; exact c.move
    impedeP := by rw [← hP]; exact c.impedeP }

/-- a frame with its end replaced by equal values -/
def withEnd {tp am : Int} (c : Frame tp am) (v' f' P' : Int) (hv : c.v' = v') (hf : c.f' = f') (hP : c.P' = P') : Frame tp am :=
  { c with
    v', f', P'
    impedeV := by rw [← hv]; exact c.impedeV
    impedeF := by rw [← hf]; exact c.impedeF
    impedeP := by rw [← hP]; exact c.impedeP }

/-- `M` has the horizontal bytes of `a`: the `lag` frames between them keep them -/
def Same (sy : Syms) (a M : Machine) : Prop := ∀ x ∈ hBytes sy, peek M x = peek a x

theorem Same.v {a M : Machine} (h : Same sy a M) : sbyte (peek M sy.Player_X_Speed) = sbyte (peek a sy.Player_X_Speed) := by
  rw [h _ (by simp [hBytes])]

theorem Same.f {a M : Machine} (h : Same sy a M) : ((peek M sy.Player_X_MoveForce).toNat : Int) = ((peek a sy.Player_X_MoveForce).toNat : Int) := by
  rw [h _ (by simp [hBytes])]

theorem Same.P {a M : Machine} (h : Same sy a M) : posP sy M = posP sy a := posP_congr h

open Classical in
/-- **A frame before the touch, read from the machines**: the frame of `M` with the input `i`, which comes to the player's routine at the instruction `n₀`; `a` is the
machine at the end of the counted frame before (`M`, or earlier by `lag` frames). It starts with the speed, the subspeed and the position of `a`. If the frame meets `ReadE`
and `M` has the horizontal bytes of `a`, it is the `TopSpeed.Frame` of `frame_readE`, and it ends with those of the frame's end; else it stops where it starts (`stillFrame`). -/
noncomputable def frameE (sy : Syms) (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : Frame (top sy : Int) (amax sy m0) :=
  if h : ReadE sy m0 M i n₀ ∧ Same sy a M then
    let c := Classical.choose (frame_readE h.1)
    have s := Classical.choose_spec (frame_readE h.1)
    withEnd (withStart c _ _ _ (s.1.trans h.2.v) (s.2.1.trans h.2.f) (s.2.2.1.trans h.2.P)) _ _ _ s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1
  else stillFrame sy m0 (sbyte (peek a sy.Player_X_Speed)) ((peek a sy.Player_X_MoveForce).toNat : Int) (posP sy a)

open Classical in
/-- **The touch's frame, read from the machines, up to the scroll handler**: it starts with the speed, the subspeed and the position of `a`. If the frame meets `ReadH` and
`M` has the horizontal bytes of `a`, it is the `TopSpeed.Frame` of `read_move`: `P₂` is the position at the scroll handler; else it stops where it starts. -/
noncomputable def frameH (sy : Syms) (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : Frame (top sy : Int) (amax sy m0) :=
  if h : ReadH sy m0 M i n₀ ∧ Same sy a M then
    let c := Classical.choose (read_move h.1)
    have s := Classical.choose_spec (read_move h.1)
    withStart c _ _ _ ((Classical.choose_spec s).2.2.1.trans h.2.v) ((Classical.choose_spec s).2.2.2.1.trans h.2.f) ((Classical.choose_spec s).2.2.2.2.1.trans h.2.P)
  else stillFrame sy m0 (sbyte (peek a sy.Player_X_Speed)) ((peek a sy.Player_X_MoveForce).toNat : Int) (posP sy a)

theorem frameE_v (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : (frameE sy m0 a M i n₀).v = sbyte (peek a sy.Player_X_Speed) := by
  unfold frameE; split <;> rfl

theorem frameE_f (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : (frameE sy m0 a M i n₀).f = ((peek a sy.Player_X_MoveForce).toNat : Int) := by
  unfold frameE; split <;> rfl

theorem frameE_P (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : (frameE sy m0 a M i n₀).P = posP sy a := by
  unfold frameE; split <;> rfl

theorem frameH_v (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : (frameH sy m0 a M i n₀).v = sbyte (peek a sy.Player_X_Speed) := by
  unfold frameH; split <;> rfl

theorem frameH_f (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : (frameH sy m0 a M i n₀).f = ((peek a sy.Player_X_MoveForce).toNat : Int) := by
  unfold frameH; split <;> rfl

theorem frameH_P (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : (frameH sy m0 a M i n₀).P = posP sy a := by
  unfold frameH; split <;> rfl

/-- **A frame that meets `ReadE` ends with the bytes of the frame's end**, and the part after the scroll handler moves him at most 1 px left from the end of the move -/
theorem frameE_end {m0 a M : Machine} {i : UInt8} {n₀ : Nat} (h : ReadE sy m0 M i n₀) (hs : Same sy a M) :
    (frameE sy m0 a M i n₀).v' = sbyte (peek (frame M i) sy.Player_X_Speed) ∧ (frameE sy m0 a M i n₀).f' = ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int) ∧
      (frameE sy m0 a M i n₀).P' = posP sy (frame M i) ∧ (frameE sy m0 a M i n₀).P₂ - 256 ≤ (frameE sy m0 a M i n₀).P' := by
  have s := Classical.choose_spec (frame_readE h)
  unfold frameE
  rw [dif_pos ⟨h, hs⟩]
  refine ⟨rfl, rfl, rfl, ?_⟩
  show (Classical.choose (frame_readE h)).P₂ - 256 ≤ posP sy (frame M i)
  have e := s.2.2.2.2.2.1
  have l := s.2.2.2.2.2.2
  omega

/-- **The touch's frame that meets `ReadH`**: `P₂` and `v₂` are the position and the speed at an arrival at the scroll handler -/
theorem frameH_move {m0 a M : Machine} {i : UInt8} {n₀ : Nat} (h : ReadH sy m0 M i n₀) (hs : Same sy a M) :
    ∃ k, n₀ ≤ k ∧ (trace M i k).pc = sy.PlayerSubs ∧ (frameH sy m0 a M i n₀).P₂ = posP sy (trace M i k) ∧
      (frameH sy m0 a M i n₀).v₂ = sbyte (peek (trace M i k) sy.Player_X_Speed) := by
  have s := Classical.choose_spec (read_move h)
  obtain ⟨hk, hpc, _, _, _, e4, _, e6, _⟩ := Classical.choose_spec s
  refine ⟨Classical.choose s, hk, hpc, ?_, ?_⟩
  · unfold frameH
    rw [dif_pos ⟨h, hs⟩]
    exact e6
  · unfold frameH
    rw [dif_pos ⟨h, hs⟩]
    exact e4

/-! ## On real frames: a program, no part of the proof -/

/-- what fails of the conditions of one frame, from the machine `a` at the end of the counted frame before, the machine `M` where the frame starts (`a`, or later by `lag`
frames) and the input `i`: `last` for the touch's frame, where `CollideE` is not asked. `loose` says that at some arrival at the scroll handler `CollideE` holds and `FrameModel.Collide` does not. -/
structure ReadScan where
  fails : List String
  /-- the frame's end -/
  next : Machine
  /-- `FrameModel.Collide` fails at an arrival at the scroll handler where `CollideE` holds -/
  loose : Bool
  /-- the position's change over the frame -/
  dP : Int

def readScan (sy : Syms) (m0 a M : Machine) (i : UInt8) (last : Bool) : ReadScan := Id.run do
  let S := FrameModel.ctrlStack sy m0
  let t := M.frame + 1
  let mut c : Machine := { M with pad := i }
  let mut n := 0
  let mut arr : Option (Nat × Machine) := none
  let mut subs : List Machine := []
  let mut late := false
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if arr.isNone && c.pc == sy.PlayerCtrlRoutine then arr := some (n, c)
    if arr.isSome && c.pc == sy.PlayerSubs then subs := c :: subs
    if c.pc != sy.EndlessLoop && decide (c.fdot > dotsPerFrame - 64) then late := true
    c := (PipeTransitionAll.go step c).2
    n := n + 1
  let b := c
  let mut f : List String := []
  if !([(0 : UInt8), 1, 2].contains (peek a sy.Player_State) && peek a sy.JumpspringAnimCtrl == 0) then f := "state" :: f
  if !(TopSpeed.collBits sy).contains (peek a sy.Player_CollisionBits) then f := "coll" :: f
  if !TopSpeed.inSpeed sy (peek a sy.Player_X_Speed) then f := "speed" :: f
  if !(decide (2048 ≤ posP sy a) && decide (posP sy a + 2048 < 0x1000000)) then f := "far" :: f
  if !(CtrlKeep.keepA sy).all (fun x => peek M x == peek a x) then f := "lag" :: f
  if late then f := "time" :: f
  let mut loose := false
  match arr with
  | none => f := "no arrival" :: f
  | some (n0, R) =>
    let at0 := (FrameModel.atFails sy S R).filter fun w => w != "stored speed" && w != "mask"
    f := at0 ++ f
    if !(FrameModel.hBytes sy).all (fun x => peek R x == peek M x) then f := "before" :: f
    if n ≤ n0 + moveLen then f := "longer" :: f
    if subs.isEmpty then f := "no scroll handler" :: f
    if !last then
      if !subs.all (fun Q => collideEB sy M Q b) then f := "collide" :: f
      for Q in subs do
        let vok := peek b sy.Player_X_Speed == peek Q sy.Player_X_Speed || peek b sy.Player_X_Speed == 0
        let d := posP sy b - posP sy Q
        let pok := d == 0 || d == -256 || (d == 256 && decide (sbyte (peek Q sy.Player_X_Speed) ≤ 0))
        if collideEB sy M Q b && !(vok && pok) then loose := true
  return { fails := f, next := b, loose, dP := posP sy b - posP sy a }

end Smbrta.SurfaceRead
