import Theorems.PipeChangeEnd
import Theorems.SurfaceFrames
import Theorems.RoomJoin

/-!
# The state at the first control in the room, from the rows of the change

`PipeChangeEnd` proves rows of states for the frames after the vertical pipe, up to the frame of control. Here: in these rows a machine with control has the horizontal state of the room's start, its
pixel is the room's start pixel, and it falls from the start's height with the stored speed 0 (`startCheck`, `start_of_rows`). On a run of the change in which `left` is not 0 before control, the machine at control is in the rows (`PipeRun.inRows`), so it has that state
(`PipeRun.start`). This is `RoomJoin.StartAt`, which `RoomJoin.RoomRun.entry_ge` takes. No game data. Page: `1-1/c-7-2-RoomStart.md`.
-/

namespace Smbrta.RoomStart

open SideChangeBound
open SideChangeEnd
open PipeChangeEnd
open PipeChangeBound (inPipe leftOf)
open PipeTransitionAll (Names)
open PipeTransition (frame)
open FastTakeoff (Room)

/-- the bytes of the horizontal state and of the pixel -/
def hsBytes (sy : Syms) : List UInt16 :=
  [sy.Player_X_Speed, sy.Player_X_MoveForce, sy.PlayerFacingDir, sy.Player_MovingDir, sy.RunningSpeed, sy.Player_PageLoc, sy.Player_X_Position]

/-- the pixel: the page and `x` -/
def pixOf (sy : Syms) (m : Machine) : Nat := (peek m sy.Player_PageLoc).toNat * 256 + (peek m sy.Player_X_Position).toNat

/-- the bytes of the vertical state that the room's start reads, and the stored speed -/
def vBytes (sy : Syms) : List UInt16 :=
  [sy.Player_State, sy.Player_Y_Position, sy.Player_YMF_Dummy, sy.Player_Y_Speed, sy.Player_Y_MoveForce, sy.VerticalForceDown, sy.Player_XSpeedAbsolute]

/-- in the air, at most `yMax` down and `wMax` fast, with the fall force `vfd`, and the stored speed 0 -/
def vOK (sy : Syms) (yMax wMax : Int) (vfd : Nat) (m : Machine) : Bool :=
  peek m sy.Player_State == 2 && decide (256 * ((peek m sy.Player_Y_Position).toNat : Int) + ((peek m sy.Player_YMF_Dummy).toNat : Int) ≤ yMax) &&
    decide (256 * ((peek m sy.Player_Y_Speed).toNat : Int) + ((peek m sy.Player_Y_MoveForce).toNat : Int) ≤ wMax) &&
    (peek m sy.VerticalForceDown).toNat == vfd && peek m sy.Player_XSpeedAbsolute == 0

/-- a state of a row: it says whether it has control, and if it has, it knows the bytes of the horizontal state, of the pixel and of the vertical state, and they are the room's start -/
def rowOK (sy : Syms) (rm : Room) (yMax wMax : Int) (vfd : Nat) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || ((hsBytes sy).all (knowsAd S) && FrameModel.readHS sy (mOf S) == rm.s0 &&
      decide (rm.P0 ≤ 256 * (pixOf sy (mOf S) : Int)) && decide (256 * (pixOf sy (mOf S) : Int) + 255 ≤ rm.P1) &&
      (vBytes sy).all (knowsAd S) && vOK sy yMax wMax vfd (mOf S)))

/-- every state of the rows -/
def rowsOK (sy : Syms) (rm : Room) (yMax wMax : Int) (vfd : Nat) (l : List Row) : Bool := l.all fun r => r.R.all (rowOK sy rm yMax wMax vfd)

/-- the check on the ROM of the old rows: in the rows of the two cases of `PipeChangeEnd`, a machine with control has the state of the room's start -/
def startCheckO (sy : Syms) (nm : Names) (d : Data) (e : Machine) (rm : Room) (yMax wMax : Int) (vfd : Nat) : Bool :=
  rowsOK sy rm yMax wMax vfd (rowsA (ctxOf sy nm d e) d e) && rowsOK sy rm yMax wMax vfd (rowsB (ctxOf sy nm d e) d e)

/-- **The check on the ROM**: in the rows where `left` is 0 of the rows with tables (`PipeChangeEnd.timeRows`), a machine with control has the state of the room's start -/
def startCheck (sy : Syms) (nm : Names) (d : Data) (e : Machine) (rm : Room) (yMax wMax : Int) (vfd : Nat) : Bool :=
  rowsOK sy rm yMax wMax vfd (timeRows (timeCtx sy nm d e) d e)

/-- what the check gives on a machine -/
structure StartOf (sy : Syms) (rm : Room) (yMax wMax : Int) (vfd : Nat) (m : Machine) : Prop where
  hs : FrameModel.readHS sy m = rm.s0
  P0 : rm.P0 ≤ posP sy m
  P1 : posP sy m ≤ rm.P1
  v : vOK sy yMax wMax vfd m = true

variable {sy : Syms} {rm : Room} {N : RoomJoin.Nums} {yMax wMax : Int} {vfd : Nat}

/-- the position from the pixel and the fraction -/
theorem posP_pix (m : Machine) : posP sy m = 256 * (pixOf sy m : Int) + ((peek m sy.SprObject_X_MoveForce).toNat : Int) := by
  unfold posP pixOf
  omega

/-- `vOK` reads only known bytes -/
theorem vOK_of_known {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hk : (vBytes sy).all (knowsAd S) = true)
    (h : vOK sy yMax wMax vfd (mOf S) = true) : vOK sy yMax wMax vfd m = true := by
  simp only [vBytes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hk
  simp only [vOK, peek_of_known hs k1, peek_of_known hs k2, peek_of_known hs k3, peek_of_known hs k4, peek_of_known hs k5, peek_of_known hs k6, peek_of_known hs k7]
  exact h

/-- a covered machine with control has the room's start -/
theorem start_of_state {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowOK sy rm yMax wMax vfd S = true) (h : controllable sy m = true) :
    StartOf sy rm yMax wMax vfd m := by
  simp only [rowOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq, decide_eq_true_eq] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | h1
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · obtain ⟨⟨⟨⟨⟨hb, he⟩, hp0⟩, hp1⟩, hvk⟩, hv⟩ := h1
    simp only [hsBytes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hb
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hb
    have hhs : FrameModel.readHS sy m = FrameModel.readHS sy (mOf S) := by
      simp only [FrameModel.readHS, peek_of_known hs k1, peek_of_known hs k2, peek_of_known hs k3, peek_of_known hs k4, peek_of_known hs k5]
    have hpix : pixOf sy m = pixOf sy (mOf S) := by
      simp only [pixOf, peek_of_known hs k6, peek_of_known hs k7]
    have hP := posP_pix (sy := sy) m
    have hf : (peek m sy.SprObject_X_MoveForce).toNat < 256 := UInt8.toNat_lt _
    refine ⟨hhs.trans he, ?_, ?_, vOK_of_known hs hvk hv⟩
    · rw [hP, hpix]
      omega
    · rw [hP, hpix]
      omega

theorem start_of_invL {C : Ctx} : ∀ {l : List Row}, rowsOK sy rm yMax wMax vfd l = true → ∀ {m : Machine}, InvL C l m → controllable sy m = true →
    StartOf sy rm yMax wMax vfd m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsOK, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact start_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact start_of_invL hl.2 h hc

/-- **A machine in the old rows that has control has the room's start.** -/
theorem start_of_rows {nm : Names} {d : Data} {e : Machine} (hc : startCheckO sy nm d e rm yMax wMax vfd = true) {m : Machine} (h : InRows sy nm d e m)
    (hm : controllable sy m = true) : StartOf sy rm yMax wMax vfd m := by
  simp only [startCheckO, Bool.and_eq_true] at hc
  rcases h with h | h
  · exact start_of_invL hc.1 h hm
  · exact start_of_invL hc.2 h hm

variable {nm : Names} {d : Data} {e : Machine} {es : List Machine}

/-- `left` is not 0 on a state of the pipe's frames: it is the timer and the frames after it -/
theorem left_during (T : EndStatement sy nm d e es) {m : Machine} (h : During d e m) : leftP sy nm e m ≠ 0 := by
  have hp := T.inRoutine _ h
  show leftOf sy nm sy.EngVerticalPipe _ afterF m ≠ 0
  unfold leftOf
  rw [if_pos hp]
  have : afterF = 43 := rfl
  omega

/-- **The machine at control is in the rows**, on a run of the change in which `left` is not 0 before control. In the rows `left` is 0 only on the last row: there he has control, or the time is up. -/
theorem PipeRun.inRows (T : EndStatement sy nm d e es) (R : PipeRun sy nm d e)
    (hf : ∀ n, R.a ≤ n → n < R.b → leftP sy nm e (R.seq n) ≠ 0) : InRows sy nm d e (R.seq R.b) := by
  have key : ∀ k, R.a + k ≤ R.b → During d e (R.seq (R.a + k)) ∨ InRows sy nm d e (R.seq (R.a + k)) := by
    intro k
    induction k with
    | zero => exact fun _ => Or.inl (T.during _ R.entry)
    | succ k ih =>
      intro hk
      have e1 : R.a + (k + 1) = R.a + k + 1 := rfl
      rw [e1]
      have hn := R.next (R.a + k)
      have hgap : R.a ≤ R.a + k := by omega
      have hlt : R.a + k < R.b := by omega
      rcases ih (by omega) with h1 | h1
      · have hP := R.places _ hgap hlt (T.inRoutine _ h1)
        obtain ⟨_, g2⟩ := T.step _ h1 (R.inp (R.a + k)) hP
        rw [hn]
        rcases g2 with g2 | ⟨g2, g3⟩
        · exact Or.inl g2
        · rw [← hn] at g2 g3 ⊢
          obtain ⟨q1, q2, q3⟩ := R.quiet _ (by omega) (by omega) g2
          exact Or.inr (g3 q1 q2 q3)
      · rcases T.rows _ h1 (R.inp (R.a + k)) (R.noStart _ hgap hlt) with g | ⟨g1, _⟩
        · exact absurd g (hf _ hgap hlt)
        · rw [hn]
          exact Or.inr g1
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  have h := key (R.b - R.a) (by omega)
  rw [e2] at h
  rcases h with h | h
  · exact absurd (T.atControl _ R.atCtl) (left_during T h)
  · exact h

/-- **A machine with control in the rows that the room's checks read has the room's start.** -/
theorem start_of_rowsT {nm : Names} {d : Data} {e : Machine} (hc : startCheck sy nm d e rm yMax wMax vfd = true) {m : Machine} (h : InRowsT sy nm d e m)
    (hm : controllable sy m = true) : StartOf sy rm yMax wMax vfd m :=
  start_of_invL hc h hm

/-- **The state at the first control in the room, on a real run**, from the conditions of the change with the rows with tables, if `b` is the first control after the entry -/
theorem PipeRunK.start (T : EndStatement sy nm d e es) (hc : startCheck sy nm d e (RoomJoin.room sy N) N.startY N.startW N.fallF = true) (R : PipeRunK sy nm d e)
    (hf : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) : RoomJoin.StartAt sy N (R.seq R.b) := by
  obtain ⟨h1, h2, h3, h4⟩ := start_of_rowsT hc (PipeRunK.inRowsT T R hf) R.atCtl
  simp only [vOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h4
  obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩ := h4
  exact ⟨h1, h2, h3, ⟨g1, g2, g3, g4⟩, g5⟩

/-- **The state at the first control in the room, on a real run**, from the old conditions of the change and `left` not 0 before control. -/
theorem PipeRun.start (T : EndStatement sy nm d e es) (hc : startCheckO sy nm d e (RoomJoin.room sy N) N.startY N.startW N.fallF = true) (R : PipeRun sy nm d e)
    (hf : ∀ n, R.a ≤ n → n < R.b → leftP sy nm e (R.seq n) ≠ 0) : RoomJoin.StartAt sy N (R.seq R.b) := by
  obtain ⟨h1, h2, h3, h4⟩ := start_of_rows hc (PipeRun.inRows T R hf) R.atCtl
  simp only [vOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h4
  obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩ := h4
  exact ⟨h1, h2, h3, ⟨g1, g2, g3, g4⟩, g5⟩

end Smbrta.RoomStart

namespace Smbrta.RoomStart

open SideChangeBound
open SideChangeEnd
open FastTakeoff (Room)

/-! ## On the rows: a program, no part of the proof -/

/-- the states of the rows, those with control, and those that fail `rowOK` -/
def rowCount (sy : Syms) (rm : Room) (yMax wMax : Int) (vfd : Nat) (l : List Row) : Nat × Nat × Nat :=
  l.foldl (fun acc r => r.R.foldl (fun a S =>
    (a.1 + 1, a.2.1 + (if (SurfaceFrames.ctlBytes sy).all (knowsAd S) && controllable sy (mOf S) then 1 else 0), a.2.2 + (if rowOK sy rm yMax wMax vfd S then 0 else 1))) acc) (0, 0, 0)

/-- the states of the rows with control -/
def ctlStates (sy : Syms) (l : List Row) : List AS :=
  l.flatMap fun r => r.R.filter fun S => (SurfaceFrames.ctlBytes sy).all (knowsAd S) && controllable sy (mOf S)

end Smbrta.RoomStart
