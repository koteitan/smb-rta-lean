import Theorems.Opening
import Theorems.PipeFrames

/-!
# The opening on real frames: each of the first `N` frames is a step of the model

`Route.Pipe` assumed the bound of the opening on the real frames: the position at the end of frame `N` is at most `P₀ + D` (`openB`). The bound is proved on a model
(`Opening`: the horizontal frame `hstep` and the measured jump lengths). Here the bound is a theorem, from a condition on each of the first `N` frames: the frame is a step of the
model (`OpenRun.step`). The model's state is read from the machines: the horizontal state (`Potential.startHS`) and the position; the frames left in the air are a sequence of
numbers (`air`), 0 at control.

* `OpenRun.reach`: frame `t` begins in a state that the model reaches in `t − 1` steps from the start, with the distance `P(t) − P(1)`.
* `OpenRun.endB`: with the bound of the model (`Opening.opt_of_check`, a check on the ROM), the position at the end of frame `N` is at most `P(1) + D`.

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

/-! ## The frames of the opening on the machines

`OpenRun` asked that each frame is a step of the model. Here this is a theorem from conditions on single frames and states (`Real`): the movement of the frame is
`FrameModel.move_model` (proved for every value of the bytes, by walks of two machines), the state at the player's routine is the walk of `CtrlKeep` from the frame's start
in control, and the frames not counted keep the bytes of the walk of `LagFrames`. The model's input is the one the player's routine reads (`inOf`). The frames left in the air
are read from the machines (`airOf`): 0 when the frame begins on the ground, else the counted frames up to the first that begins on the ground. -/

open PipeTransition (frame)
open PipeEntryRule (trace)
open PipeWrites (FrameStart guardOf)
open PipeFrames (Lags landFrom landFrom_ge landFrom_self landFrom_succ landFrom_at)

/-- the input of the counted frame `t`, as the player's routine reads it: at the first arrival there (`CtrlKeep.arrAt`) -/
def inOf (sy : Syms) (fm : Nat → Machine) (inp : Nat → UInt8) (t : Nat) : HIn :=
  FrameModel.readIn sy (trace (fm t) (inp t) (CtrlKeep.arrAt sy (fm t) (inp t)))

/-- the counted frame `t` begins on the ground -/
def groundB (sy : Syms) (fm : Nat → Machine) (t : Nat) : Bool := peek (fm t) sy.Player_State == 0

/-- **The frames left in the air when the counted frame `t` begins**, read from the machines: up to the first counted frame from `t` on that begins on the ground, looking up
to the counted frame `Z` -/
def airOf (sy : Syms) (fm : Nat → Machine) (Z t : Nat) : Nat := landFrom (groundB sy fm) t (Z - t) - t

theorem airOf_ground {fm : Nat → Machine} {Z t : Nat} (h : peek (fm t) sy.Player_State = 0) : airOf sy fm Z t = 0 := by
  unfold airOf
  rw [landFrom_self (by simp [groundB, h])]
  omega

/-- in the air, one frame less is left at the next counted frame -/
theorem airOf_air {fm : Nat → Machine} {Z t : Nat} (h : peek (fm t) sy.Player_State ≠ 0) (hZ : t < Z) :
    airOf sy fm Z t = airOf sy fm Z (t + 1) + 1 := by
  unfold airOf
  have hf : groundB sy fm t = false := by simp [groundB, h]
  rw [show Z - t = (Z - (t + 1)) + 1 by omega, landFrom_succ hf]
  have := landFrom_ge (groundB sy fm) (t + 1) (Z - (t + 1))
  omega

/-- after a jump that lands `n` counted frames later, `n − 1` frames are left at the next counted frame -/
theorem airOf_jump {fm : Nat → Machine} {Z t n : Nat} (h1 : 1 ≤ n) (hn : t + n ≤ Z) (hair : ∀ d, 1 ≤ d → d < n → peek (fm (t + d)) sy.Player_State ≠ 0)
    (hl : peek (fm (t + n)) sy.Player_State = 0) : airOf sy fm Z (t + 1) = n - 1 := by
  unfold airOf
  have e := landFrom_at (p := groundB sy fm) (n - 1) (t + 1) (Z - (t + 1))
    (fun j h2 h3 => by
      have := hair (j - t) (by omega) (by omega)
      rw [show t + (j - t) = j by omega] at this
      simp [groundB, this])
    (by rw [show t + 1 + (n - 1) = t + n by omega]; simp [groundB, hl]) (by omega)
  rw [e]
  omega

/-- **The frame from the scroll handler on**, from the machine `Q` there to the frame's end `b`: it changes no byte of the horizontal state or of the position (no wall, no
edge of the screen), and it ends with the stored speed `|v|` and the collision bits all 1 (the collision routine found nothing) -/
def After (sy : Syms) (Q b : Machine) : Prop :=
  (∀ x ∈ FrameModel.hBytes sy, peek b x = peek Q x) ∧ peek b sy.Player_XSpeedAbsolute = TopSpeed.absB (peek b sy.Player_X_Speed) ∧ peek b sy.Player_CollisionBits = 0xFF

/-- **What stays assumed of the first `N` counted frames**, before the entry `E`: conditions on single frames, on their instructions and on their starts. The frames are those of
`L` (`PipeFrames.Lags`): the counted frame `t` begins at `L.fm t` with the input `L.inp t`. -/
structure Real (sy : Syms) (m0 : Machine) (lens : Lens) (N E : Nat) {g : Nat} {S : FrameKeep.RealRun} (L : Lags sy m0 g S E) : Prop where
  /-- each instruction of the frame meets `CleanK` (`PipeWrites.Clean` with the castle flag and the position's fraction protected too, but the move routine's own store) -/
  cleanK : ∀ t, 1 ≤ t → t ≤ N → t < E → ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace (L.fm t) (L.inp t) k)
  /-- no store of the frame through an index or a pointer writes the pause byte, the area's type, the swimming flag or the change of size -/
  spare : ∀ t, 1 ≤ t → t ≤ N → t < E → ∀ k, CtrlKeep.Spare sy m0 (trace (L.fm t) (L.inp t) k)
  /-- the player's state is 0, 1 or 2 when the frame begins -/
  st : ∀ t, 1 ≤ t → t ≤ N → t < E → peek (L.fm t) sy.Player_State ∈ [(0 : UInt8), 1, 2]
  /-- no jumpspring when the frame begins -/
  spring : ∀ t, 1 ≤ t → t ≤ N → t < E → peek (L.fm t) sy.JumpspringAnimCtrl = 0
  /-- the page is below 128 when the frame begins, and when the frame after it begins -/
  page : ∀ t, 1 ≤ t → t ≤ N + 1 → t ≤ E → posP sy (L.fm t) < 0x800000
  /-- the frame does not end during the movement -/
  longer : ∀ t, 1 ≤ t → t ≤ N → t < E →
    ((trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t) + FrameModel.moveLen)).frame ≥ (L.fm t).frame + 1 ||
      (trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t) + FrameModel.moveLen)).halted) = false
  /-- from the scroll handler on: `After` -/
  after : ∀ t, 1 ≤ t → t ≤ N → t < E → ∀ k, CtrlKeep.arrAt sy (L.fm t) (L.inp t) ≤ k → (trace (L.fm t) (L.inp t) k).pc = sy.PlayerSubs →
    After sy (trace (L.fm t) (L.inp t) k) (frame (L.fm t) (L.inp t))
  /-- **the flat ground**: a frame that begins on the ground and does not start a jump is followed by a counted frame that begins on the ground -/
  flat : ∀ t, 1 ≤ t → t ≤ N → t < E → peek (L.fm t) sy.Player_State = 0 → (inOf sy L.fm L.inp t).jump = false → peek (L.fm (t + 1)) sy.Player_State = 0
  /-- **the length of a jump**: a jump started on the counted frame `t` lands `n` counted frames later, `n` between the lengths `lens` for the speed when the frame begins:
  the frames between begin in the air, and the counted frame `t + n` begins on the ground -/
  jump : ∀ t, 1 ≤ t → t ≤ N → t < E → peek (L.fm t) sy.Player_State = 0 → (inOf sy L.fm L.inp t).jump = true →
    ∃ n, 1 ≤ n ∧ (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 ≤ n ∧ n ≤ (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).2 ∧
      (∀ d, 1 ≤ d → d < n → peek (L.fm (t + d)) sy.Player_State ≠ 0) ∧ peek (L.fm (t + n)) sy.Player_State = 0

/-- **What the frame's start holds, frame after frame**: the stored speed is `|v|`, the collision bits are all 1, and the area's type is `v` with no swimming and no change
of size -/
def Held (sy : Syms) (v : UInt8) (m : Machine) : Prop :=
  peek m sy.Player_XSpeedAbsolute = TopSpeed.absB (peek m sy.Player_X_Speed) ∧ peek m sy.Player_CollisionBits = 0xFF ∧ CtrlKeep.AreaOK sy v m

/-- **The checks on the ROM** that the frames of the opening use: the movement (`FrameModel.modelOK`), the walk up to the player's routine (`CtrlKeep.ctrlCheck`), the walk of
the whole frame with the area's type `v` (`CtrlKeep.afterCheck`), the inputs of the model (`normIdem`), a bound `Zb` above every jump's length (`lensZ`), and the
state of `m0` (`start`). -/
structure Checks (sy : Syms) (m0 : Machine) (lens : Lens) (Zb : Nat) (v : UInt8) (g : Nat) : Prop where
  model : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true
  ctrl : CtrlKeep.ctrlCheck sy m0 = true
  after : CtrlKeep.afterCheck sy m0 v = true
  v3 : v ∈ [(1 : UInt8), 2, 3]
  norm : Potential.normIdem = true
  lensZ : (lens.toList.all fun p => decide (p.2 < Zb)) = true
  Zb0 : 0 < Zb
  /-- the machine `m0` holds `Held` and is on the ground: the state at control is that of `m0` (`StartRun.titlePosCheck`) -/
  start : Held sy v m0 ∧ peek m0 sy.Player_State = 0
  /-- the pause byte that the NMI tests (`CtrlKeep.pauseI`, read from the ROM) is `g` -/
  pause : CtrlKeep.pauseI sy m0 = g

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

/-- **The movement of a real frame, with the page below 128** at its start and its end: `FrameModel.clean_frame` with the page in place of `far` -/
theorem move_page {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} (hOK : FrameModel.modelOK sy m0 S = true) (hat : FrameModel.AtCtrl sy (FrameModel.Rom.of m0) S (trace M i n₀))
    (hbef : ∀ a ∈ FrameModel.hBytes sy, peek (trace M i n₀) a = peek M a)
    (hlong : ((trace M i (n₀ + FrameModel.moveLen)).frame ≥ M.frame + 1 || (trace M i (n₀ + FrameModel.moveLen)).halted) = false)
    (hafter : ∀ j, n₀ ≤ j → (trace M i j).pc = sy.PlayerSubs → ∀ a ∈ FrameModel.hBytes sy, peek (frame M i) a = peek (trace M i j) a)
    (hp1 : posP sy M < 0x800000) (hp2 : posP sy (frame M i) < 0x800000) :
    FrameModel.readHS sy (frame M i) = hstep sy m0 (FrameModel.readHS sy M) (FrameModel.readIn sy (trace M i n₀)) ∧
      posP sy (frame M i) = posP sy M + 16 * sbyte (FrameModel.readHS sy (frame M i)).v ∧ ∃ j, n₀ ≤ j ∧ (trace M i j).pc = sy.PlayerSubs := by
  obtain ⟨k, hk, _, hpc, h1, h2⟩ := FrameModel.move_model hOK hat
  have e0 := FrameModel.trace_steps hlong k hk
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
  refine ⟨h1, ?_, n₀ + k, by omega, by rw [e0]; exact hpc⟩
  obtain ⟨a1, _⟩ := FrameModel.posOf_range (peek M sy.Player_PageLoc) (peek M sy.Player_X_Position) (peek M sy.SprObject_X_MoveForce)
  obtain ⟨b1, _⟩ := FrameModel.posOf_range (peek (frame M i) sy.Player_PageLoc) (peek (frame M i) sy.Player_X_Position) (peek (frame M i) sy.SprObject_X_MoveForce)
  rw [← FrameModel.posP_eq] at a1 b1
  have a3 := FrameModel.sbyte_range (FrameModel.readHS sy (frame M i)).v
  omega

/-- **One counted frame of the opening**: from its start in control (`hs`) with what the frames before left (`hh`), the frame follows `hstep` on the input its player's
routine reads, the position moves by `16·v`, and the frame's end holds again what the next frame needs (`Held`, before the frames not counted). -/
theorem Real.frame_step {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (C : Checks sy m0 lens Zb v g) (O : Real sy m0 lens N E L)
    {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ N) (h3 : t < E) (hs : FrameKeep.StartK sy m0 (L.fm t)) (hh : Held sy v (L.fm t))
    (hp2 : posP sy (frame (L.fm t) (L.inp t)) < 0x800000) :
    startHS sy (frame (L.fm t) (L.inp t)) = hstep sy m0 (startHS sy (L.fm t)) (inOf sy L.fm L.inp t) ∧
      posP sy (frame (L.fm t) (L.inp t)) = posP sy (L.fm t) + 16 * sbyte (startHS sy (frame (L.fm t) (L.inp t))).v ∧
      Held sy v (frame (L.fm t) (L.inp t)) ∧
      peek (trace (L.fm t) (L.inp t) (CtrlKeep.arrAt sy (L.fm t) (L.inp t))) sy.Player_State = peek (L.fm t) sy.Player_State := by
  generalize hM : L.fm t = M at hs hh hp2 ⊢
  generalize hi : L.inp t = i at hp2 ⊢
  have hcl : ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace M i k) := by
    rw [← hM, ← hi]; exact O.cleanK t h1 h2 h3
  have hsp : ∀ k, CtrlKeep.Spare sy m0 (trace M i k) := by
    rw [← hM, ← hi]; exact O.spare t h1 h2 h3
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
  have hst := O.st t h1 h2 h3
  have hspr := O.spring t h1 h2 h3
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
  have hlong := O.longer t h1 h2 h3
  rw [hM, hi, hn] at hlong
  have haf : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → After sy (trace M i k) (frame M i) := by
    intro k hk hpc
    have := O.after t h1 h2 h3 k (by rw [hM, hi, hn]; exact hk) (by rw [hM, hi]; exact hpc)
    rw [hM, hi] at this
    exact this
  have hp1 := O.page t h1 (by omega) (by omega)
  rw [hM] at hp1
  obtain ⟨r1, r2, j, hj, hpc⟩ := move_page C.model hat (fun a ha => kp a (keepA_of (Or.inl ha))) hlong (fun j hj hpc a ha => (haf j hj hpc).1 a ha) hp1 hp2
  obtain ⟨_, hab', hbits'⟩ := haf j hj hpc
  have hA := (CtrlKeep.area_end C.ctrl C.after hs hcl hsp ⟨harea, hswim, hsize⟩).1
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

/-- **Each of the first `N` counted frames is a step of the opening's model**, from the conditions on single frames (`Real`). The frames left in the air are read from the
machines (`airOf`, looking up to the counted frame `N + Zb`). At control he is on the ground and the frame's start holds `Held` (`h₁`, from the press of Start on the title). `hc`, `hk`, `hp` and `C` are checks on the
ROM, `hs₁` the start of frame 1. -/
def Real.toRun {g : Nat} {S : FrameKeep.RealRun} {L : Lags sy m0 g S E} {Zb : Nat} {v : UInt8} (hc : LagFrames.lagCheck sy m0 = true)
    (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (C : Checks sy m0 lens Zb v g)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (h₁ : Held sy v (L.fm 1)) (hg₁ : peek (L.fm 1) sy.Player_State = 0)
    (O : Real sy m0 lens N E L) : OpenRun sy m0 lens N E L.fm := by
  -- the frames not counted after the counted frame `t`
  have lk : ∀ t, 1 ≤ t → t < E → ∀ b ∈ LagFrames.lagI sy, (L.fm (t + 1)).ram.get! b = (frame (L.fm t) (L.inp t)).ram.get! b :=
    fun t _ h2 => PipeFrames.lags_keepI hc hk hp L hs₁ t h2
  -- the frame's end is below page 128: it is the start of the next counted frame
  have pe : ∀ t, 1 ≤ t → t ≤ N → t < E → posP sy (frame (L.fm t) (L.inp t)) < 0x800000 := by
    intro t h1 h2 h3
    rw [← (keep_parts (v := v) (lk t h1 h3)).2.1]
    exact O.page (t + 1) (by omega) (by omega) (by omega)
  -- `Held` at each counted frame, by induction
  have held : ∀ d, d ≤ N → 1 + d ≤ E → Held sy v (L.fm (1 + d)) := by
    intro d
    induction d with
    | zero => exact fun _ _ => h₁
    | succ d ih =>
      intro hd hE
      have hh := ih (by omega) (by omega)
      have fs := O.frame_step C (t := 1 + d) (by omega) (by omega) (by omega) (startK_of hc hk hp hs₁ (by omega) (by omega)) hh (pe _ (by omega) (by omega) (by omega))
      rw [show 1 + (d + 1) = 1 + d + 1 by omega]
      exact (keep_parts (lk (1 + d) (by omega) (by omega))).2.2 fs.2.2.1
  refine ⟨airOf sy L.fm (N + Zb), airOf_ground hg₁, ?_⟩
  intro t h1 h2 h3
  have hh := held (t - 1) (by omega) (by omega)
  rw [show 1 + (t - 1) = t by omega] at hh
  obtain ⟨s1, s2, _, s4⟩ := O.frame_step C h1 h2 h3 (startK_of hc hk hp hs₁ h1 (by omega)) hh (pe t h1 h2 h3)
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
  · rw [k2, k1, s2]
  · by_cases hg : peek (L.fm t) sy.Player_State = 0
    · rw [airOf_ground hg]
      simp [Opening.valid, FastTakeoff.norm_st, est, hg]
    · rw [airOf_air hg (by have := C.Zb0; omega)]
      simp [Opening.valid, FastTakeoff.norm_st, FastTakeoff.norm_jump, est, hg, ejp hg]
  · by_cases hg : peek (L.fm t) sy.Player_State = 0
    · rw [airOf_ground hg]
      cases hj : (inOf sy L.fm L.inp t).jump
      · have hf := O.flat t h1 h2 h3 hg hj
        rw [airOf_ground hf]
        simp [Opening.modes, FastTakeoff.norm_jump, hj]
      · obtain ⟨n, n1, n2, n3, n4, n5⟩ := O.jump t h1 h2 h3 hg hj
        have hZ := C.lens_lt (sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs
        rw [airOf_jump n1 (by omega) n4 n5]
        simp only [Opening.modes, FastTakeoff.norm_jump, hj, if_true, beq_self_eq_true]
        refine List.mem_map.2 ⟨n - 1 - ((lens[(sbyte (startHS sy (L.fm t)).v).natAbs]!).1 - 1), List.mem_range.2 ?_, ?_⟩
        · show n - 1 - ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1) <
            (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).2 + 1 - (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1
          omega
        · show (lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1 + (n - 1 - ((lens[(sbyte (peek (L.fm t) sy.Player_X_Speed)).natAbs]!).1 - 1)) = n - 1
          omega
    · rw [airOf_air hg (by have := C.Zb0; omega)]
      simp [Opening.modes]

instance (sy : Syms) (v : UInt8) (m : Machine) : Decidable (Held sy v m) := by unfold Held CtrlKeep.AreaOK; infer_instance

/-- **The state at control, from the bytes of the title's check**: if the horizontal state's bytes and the bytes of `StartRun.stI` of `m'` are those of `m`, and `m` holds
`Held` and is on the ground, so is `m'` -/
theorem held_of_bytes {m m' : Machine} {v : UInt8} (h : ∀ i ∈ StartRun.posI sy ++ StartRun.hsI sy ++ StartRun.stI sy, m'.ram.get! i = m.ram.get! i)
    (hm : Held sy v m ∧ peek m sy.Player_State = 0) : Held sy v m' ∧ peek m' sy.Player_State = 0 := by
  have hp : ∀ x, (x = sy.Player_X_Speed ∨ x = sy.Player_XSpeedAbsolute ∨ x = sy.Player_CollisionBits ∨ x = sy.Player_State ∨ x = sy.AreaType ∨
      x = sy.SwimmingFlag ∨ x = sy.PlayerChangeSizeFlag) → peek m' x = peek m x := by
    intro x hx
    apply h
    simp only [StartRun.posI, StartRun.hsI, StartRun.stI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [peek]
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hp _ (by simp), hp _ (by simp)]; exact h1
  · rw [hp _ (by simp)]; exact h2
  · show peek m' sy.AreaType = v
    rw [hp _ (by simp)]; exact h3
  · show peek m' sy.SwimmingFlag = 0
    rw [hp _ (by simp)]; exact h4
  · show peek m' sy.PlayerChangeSizeFlag = 0
    rw [hp _ (by simp)]; exact h5
  · rw [hp _ (by simp)]; exact h6

/-- **The checks, from those of part e** (`SurfaceFrames.numbersCheck`, for the machine at control above ground `B.m`): the movement and the two walks are the same checks on
`m0`; the area's type of `B.m` is that of `m0` (`he`). The rest are small checks on `m0` and `lens`, and the pause byte `g`. -/
theorem checks_of {B : PoleJoin.Box} {J Zb g : Nat} {lens : Lens} (hn : SurfaceFrames.Numbers sy m0 B J) (he : (peek B.m sy.AreaType == peek m0 sy.AreaType) = true)
    (hnorm : Potential.normIdem = true) (hl : ((lens.toList.all fun p => decide (p.2 < Zb)) && decide (0 < Zb)) = true)
    (hs : decide (Held sy (peek m0 sy.AreaType) m0 ∧ peek m0 sy.Player_State = 0) = true) (hg : (CtrlKeep.pauseI sy m0 == g) = true) :
    Checks sy m0 lens Zb (peek m0 sy.AreaType) g := by
  have e : peek B.m sy.AreaType = peek m0 sy.AreaType := by simpa using he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl hs
  refine ⟨hn.model, hn.ctrl, ?_, ?_, hnorm, hl.1, hl.2, hs, by simpa using hg⟩
  · rw [← e]; exact hn.after
  · rw [← e]; exact hn.area3

end Smbrta.OpenFrames
