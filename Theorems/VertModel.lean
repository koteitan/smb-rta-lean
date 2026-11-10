import Theorems.FrameModel
import Theorems.Jump

/-!
# A real frame and the vertical model

`Jump.vstep` runs the game's movement routine (`PlayerMovementSubs`) by `runSub` on a machine where the horizontal bytes are 0. A real frame runs the same routine with its own horizontal
bytes, and the routine's horizontal parts (`X_Physics`, the ground's routine, the air's Left and Right, the jump's sound, the vertical move's first test) take other paths on the two machines.
The walk of two machines with detours (`FrameModel.walkD`) follows the vertical parts on both, and lets each machine run alone through the horizontal parts.

* `vstepV`: `vstep` on the machine with the stack pointer of the player's routine and the jump's halt value 1. With 0 there (as on the machine at the start of the level) the jump's
  test differs; the value is 1 after any jump, and it is read only in a jump.
* `vertOK`: the check on the ROM, in each case of the state, the area, the buttons A and B, and A on the frame before.

There is no game data in this file. Page: `0-0/0-3-2-FrameModel.md`.
-/

namespace Smbrta.VertModel

open FrameModel (Rom Cut TS Tag FT Detour detourQ walkD walkDWhy pieceOK goalC I stkI lookN AtCtrl firstEnd cutOf firstRtsS findPat startQ tagImp leafQS isRts
  pokeL nodupB stepN At Good GoodH)
open TaintRun (AB)

/-! ## The model -/

/-- the machine `vstep` runs on here: the stack pointer of the player's routine, and the jump's halt value 1 -/
def vmach (sy : Syms) (m0 : Machine) (S : UInt8) : Machine := { poke m0 sy.DiffToHaltJump 1 with s := S }

/-- one frame of the vertical bytes, on that machine -/
def vstepV (sy : Syms) (m0 : Machine) (S : UInt8) (s : Jump.VS) (a : Bool) (abs : UInt8) : Jump.VS := Jump.vstep sy (vmach sy m0 S) s a abs

/-- the vertical bytes of a machine, as `Jump.vstep` has them (the same as `SurfaceFrames.vsOf`) -/
def vsOf (sy : Syms) (m : Machine) : Jump.VS :=
  { y := peek m sy.Player_Y_Position, mf := peek m sy.Player_Y_MoveForce, vy := peek m sy.Player_Y_Speed, dummy := peek m sy.Player_YMF_Dummy, vf := peek m sy.VerticalForce,
    vfd := peek m sy.VerticalForceDown, origin := peek m sy.JumpOrigin_Y_Position, st := peek m sy.Player_State, prevA := (peek m sy.A_B_Buttons &&& 0x80) != 0 }

/-- what `vstep` writes into the machine before it runs the routine -/
def vList (sy : Syms) (s : Jump.VS) (a : Bool) (abs : UInt8) : List (UInt16 × UInt8) :=
  [(sy.Player_Y_Position, s.y), (sy.Player_Y_MoveForce, s.mf), (sy.Player_Y_Speed, s.vy), (sy.Player_YMF_Dummy, s.dummy), (sy.VerticalForce, s.vf),
   (sy.VerticalForceDown, s.vfd), (sy.JumpOrigin_Y_Position, s.origin), (sy.Player_State, s.st), (sy.Player_XSpeedAbsolute, abs), (sy.Player_X_Speed, 0),
   (sy.Left_Right_Buttons, 0), (sy.A_B_Buttons, if a then 0x80 else 0), (sy.PreviousA_B_Buttons, if s.prevA then 0x80 else 0),
   (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8)]

/-- the machine `vstep` runs the routine on -/
def vH (sy : Syms) (m0 : Machine) (S : UInt8) (s : Jump.VS) (a : Bool) (abs : UInt8) : Machine := pokeL (vmach sy m0 S) (vList sy s a abs)

/-- the bytes `vstep` writes -/
def vIdx (sy : Syms) : List Nat := (vList sy default false 0).map fun p => I p.1

/-- the result of the routine on the machine of `vstep` -/
def vRun (sy : Syms) (m0 : Machine) (S : UInt8) (s : Jump.VS) (a : Bool) (abs : UInt8) : Machine := runSub (vH sy m0 S s a abs) sy.PlayerMovementSubs 0 0 0

theorem vstepV_eq (sy : Syms) (m0 : Machine) (S : UInt8) (s : Jump.VS) (a : Bool) (abs : UInt8) :
    vstepV sy m0 S s a abs = Jump.VS.mk (peek (vRun sy m0 S s a abs) sy.Player_Y_Position) (peek (vRun sy m0 S s a abs) sy.Player_Y_MoveForce)
      (peek (vRun sy m0 S s a abs) sy.Player_Y_Speed) (peek (vRun sy m0 S s a abs) sy.Player_YMF_Dummy) (peek (vRun sy m0 S s a abs) sy.VerticalForce)
      (peek (vRun sy m0 S s a abs) sy.VerticalForceDown) (peek (vRun sy m0 S s a abs) sy.JumpOrigin_Y_Position) (peek (vRun sy m0 S s a abs) sy.Player_State) a := rfl

/-- the vertical bytes but the state -/
def vIds (sy : Syms) : List Nat :=
  [I sy.Player_Y_Position, I sy.Player_Y_MoveForce, I sy.Player_Y_Speed, I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position]

/-! ## The cases -/

/-- what decides the path of the movement routine: the state, the buttons A and B, and A on the frame before -/
structure VCase where
  st : UInt8
  ab : UInt8
  prevA : Bool
  deriving Inhabited, BEq

def vCases : List VCase :=
  [(0 : UInt8), 1, 2].flatMap fun st => [(0 : UInt8), 0x40, 0x80, 0xC0].flatMap fun ab => [false, true].map fun prevA => { st, ab, prevA }

/-- A on the frame before, as a byte -/
def VCase.pv (c : VCase) : UInt8 := if c.prevA then 0x80 else 0

/-- A on this frame -/
def VCase.a (c : VCase) : Bool := c.ab &&& 0x80 != 0

/-- what decides the path from the player's routine to the movement routine: also the area and all the buttons -/
structure PCase where
  st : UInt8
  area : UInt8
  raw : UInt8
  prevA : Bool
  deriving Inhabited, BEq

def pCases : List PCase :=
  [(0 : UInt8), 1, 2].flatMap fun st => [(1 : UInt8), 2, 3].flatMap fun area => [false, true].flatMap fun prevA => (List.range 256).map fun r => { st, area, raw := r.toUInt8, prevA }

def PCase.pv (c : PCase) : UInt8 := if c.prevA then 0x80 else 0

/-- the cut at the player's routine -/
def PCase.c0 (sy : Syms) (S : UInt8) (c : PCase) : Cut :=
  { pc := sy.PlayerCtrlRoutine, s := S,
    K := [(I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8), (I sy.AreaType, c.area), (I sy.Player_State, c.st), (I sy.SavedJoypadBits, c.raw),
          (I sy.JumpspringAnimCtrl, 0), (I sy.SwimmingFlag, 0), (I sy.PlayerChangeSizeFlag, 0)],
    B := [(I sy.PreviousA_B_Buttons, ⟨c.pv, 0x80⟩)] }

/-- the bytes the first piece keeps -/
def watchP (sy : Syms) : List Nat := vIds sy ++ [I sy.Player_XSpeedAbsolute, I sy.PreviousA_B_Buttons, I sy.DiffToHaltJump]

/-- the bytes known when the movement routine is entered -/
def idsP (sy : Syms) : List Nat :=
  [I sy.GameEngineSubroutine, I sy.Player_State, I sy.A_B_Buttons, I sy.JumpspringAnimCtrl, I sy.SwimmingFlag, I sy.PlayerChangeSizeFlag]

/-- the cut when the movement routine is entered, found on the first path -/
def PCase.cP (sy : Syms) (E : Rom) (S : UInt8) (c : PCase) : Cut :=
  match firstEnd E sy.PlayerMovementSubs FrameModel.fuelW (startQ (c.c0 sy S)) with
  | some Q => cutOf (idsP sy) false false Q
  | none => default

/-- the tags of the two machines when the routine is entered: the real one, and the one of `vstep` -/
def vTags (sy : Syms) (m : Machine) (c : VCase) : List (Nat × Tag) :=
  (vIds sy).map (·, .eq) ++
  [(I sy.Player_State, Tag.kn c.st c.st), (I sy.Player_XSpeedAbsolute, .eq), (I sy.A_B_Buttons, Tag.kn c.ab (c.ab &&& 0x80)),
   (I sy.PreviousA_B_Buttons, .ab ⟨c.pv, 0x80⟩ (AB.known c.pv)), (I sy.GameEngineSubroutine, Tag.kn sy.Eng_PlayerCtrl.toUInt8 sy.Eng_PlayerCtrl.toUInt8),
   (I sy.JumpspringAnimCtrl, Tag.kn 0 (peek m sy.JumpspringAnimCtrl)), (I sy.SwimmingFlag, Tag.kn 0 (peek m sy.SwimmingFlag)),
   (I sy.PlayerChangeSizeFlag, Tag.kn 0 (peek m sy.PlayerChangeSizeFlag)),
   (I sy.DiffToHaltJump, if c.st == 1 then Tag.kn 1 1 else .ab AB.top (AB.known 1))]

/-- the walk's start -/
def vStartQ (sy : Syms) (m : Machine) (S : UInt8) (c : VCase) : TS := leafQS sy.PlayerMovementSubs (S - 2) (vTags sy m c)

/-- `lda` of a byte, as the code has it -/
def ldaPat (a : UInt16) : List UInt8 := if a < 0x100 then [0xA5, a.toUInt8] else [0xAD, a.toUInt8, (a >>> 8).toUInt8]

/-- the bytes a detour keeps: the vertical ones, the state, the buttons, the flags of the walk, the return address of the routine -/
def keepV (sy : Syms) (S : UInt8) : List Nat :=
  vIds sy ++ [I sy.Player_State, I sy.A_B_Buttons, I sy.PreviousA_B_Buttons, I sy.GameEngineSubroutine, I sy.JumpspringAnimCtrl, I sy.SwimmingFlag, I sy.PlayerChangeSizeFlag,
    I sy.DiffToHaltJump, stkI S, stkI (S - 1)]

/-- the horizontal parts that the two machines run apart -/
def detours (sy : Syms) (E : Rom) (S : UInt8) : List Detour :=
  let kA := I sy.Player_XSpeedAbsolute :: stkI (S - 2) :: stkI (S - 3) :: keepV sy S
  let ret := sy.ProcMove + 2
  let rtsG := firstRtsS E (S - 2) 400 (startQ { pc := sy.OnGroundStateSub, s := S - 2, K := [(I sy.JumpspringAnimCtrl, 0)] })
  let afterLR := findPat E sy.LRAir (ldaPat sy.GameEngineSubroutine) 40
  [ { c := { pc := sy.PlayerMovementSubs, s := S - 2, K := [] }, c' := { pc := sy.ProcMove, s := S - 2, K := [] }, keep := kA, fuel := 20 },
    { c := { pc := sy.X_Physics, s := S - 4, K := [(stkI (S - 2), (ret >>> 8).toUInt8), (stkI (S - 3), ret.toUInt8)] },
      c' := { pc := sy.ProcMove + 3, s := S - 2, K := [] }, keep := kA, fuel := 60 },
    { c := { pc := sy.PJumpSnd, s := S - 4, K := [] }, c' := { pc := sy.X_Physics, s := S - 4, K := [] }, keep := kA, fuel := 10 },
    { c := { pc := sy.OnGroundStateSub, s := S - 2, K := [(I sy.JumpspringAnimCtrl, 0)] }, c' := { pc := rtsG, s := S - 2, K := [] }, keep := keepV sy S, fuel := 200 },
    { c := { pc := sy.LRAir, s := S - 2, K := [(I sy.JumpspringAnimCtrl, 0)] }, c' := { pc := afterLR, s := S - 2, K := [] }, keep := keepV sy S, fuel := 150 },
    { c := { pc := sy.MovePlayerVertically, s := S - 2, K := [(I sy.JumpspringAnimCtrl, 0)] }, c' := { pc := sy.NoJSChk, s := S - 2, K := [], x := some 0 },
      keep := keepV sy S, fuel := 10 } ]

/-- the walk stops at the routine's return -/
def stopV (E : Rom) (S : UInt8) (Q : TS) : Bool := isRts E Q.pc && Q.s == some (S - 2)

/-- at the return: the vertical bytes and the state are the same; the buttons and the stack of `runSub` were not written; in a jump the halt value is 1 -/
def goalV (sy : Syms) (S : UInt8) (Q : TS) : Bool :=
  Q.s == some (S - 2) && (I sy.Player_State :: vIds sy).all (fun i => tagImp (Q.ram i) .eq) && [I sy.A_B_Buttons, stkI S, stkI (S - 1)].all (fun i => !Q.w i) &&
  (match (Q.ram (I sy.Player_State)).same with
   | some v => v != 1 || (Q.ram (I sy.DiffToHaltJump)).same == some 1
   | none => false)

/-- the fuel of the walk -/
def fuelV : Nat := 600

/-- the fuel of the first piece -/
def fuelP : Nat := 60

/-- the return address of the routine, on the stack, from the first case -/
def retLo (sy : Syms) (E : Rom) (S : UInt8) : UInt8 := (lookN (stkI (S - 1)) ((default : PCase).cP sy E S).K).getD 0
def retHi (sy : Syms) (E : Rom) (S : UInt8) : UInt8 := (lookN (stkI S) ((default : PCase).cP sy E S).K).getD 0
/-- where the routine returns to -/
def retPc (sy : Syms) (E : Rom) (S : UInt8) : UInt16 := ((retLo sy E S).toUInt16 ||| ((retHi sy E S).toUInt16 <<< 8)) + 1

/-- the scroll handler -/
def cS (sy : Syms) (S : UInt8) : Cut := { pc := sy.PlayerSubs, s := S, K := [] }
def watchR (sy : Syms) : List Nat := vIds sy ++ [I sy.Player_State, I sy.A_B_Buttons, I sy.DiffToHaltJump]

/-- what the first piece knows when the movement routine is entered -/
def knownP (sy : Syms) (E : Rom) (S : UInt8) (c : PCase) : List (Nat × UInt8) :=
  [(I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8), (I sy.Player_State, c.st), (I sy.A_B_Buttons, c.raw &&& 0xC0), (I sy.JumpspringAnimCtrl, 0), (I sy.SwimmingFlag, 0),
    (I sy.PlayerChangeSizeFlag, 0), (stkI (S - 1), retLo sy E S), (stkI S, retHi sy E S)]

/-- a case of the first piece: from the player's routine to the movement routine, with what it knows there -/
def prefixOK (sy : Syms) (E : Rom) (S : UInt8) (c : PCase) : Bool :=
  let cP := c.cP sy E S
  pieceOK E (c.c0 sy S) cP (watchP sy) fuelP && cP.pc == sy.PlayerMovementSubs && cP.s == S - 2 && (knownP sy E S c).all (cP.K.contains ·)

/-- a case of the movement routine, on the two machines -/
def caseOK (sy : Syms) (m0 : Machine) (S : UInt8) (c : VCase) : Bool :=
  let E := Rom.of m0
  walkD E (detours sy E S) (stopV E S) (goalV sy S) fuelV (vStartQ sy (vmach sy m0 S) S c)

/-- the last piece: from the routine's return to the scroll handler -/
def lastOK (sy : Syms) (E : Rom) (S : UInt8) : Bool :=
  pieceOK E { pc := retPc sy E S, s := S, K := [] } (cS sy S) (watchR sy) 40

/-- the bytes that `vstep` does not write but the walk reads -/
def outV (sy : Syms) : List Nat := [I sy.JumpspringAnimCtrl, I sy.SwimmingFlag, I sy.PlayerChangeSizeFlag, I sy.DiffToHaltJump]

/-- the check on the ROM -/
def vertOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool :=
  let E := Rom.of m0
  FrameModel.baseOK m0 && (detours sy E S).all (·.ok E) && vCases.all (fun c => FrameModel.tagsOK S (vTags sy (vmach sy m0 S) c)) && nodupB (vIdx sy) &&
    (outV sy).all (fun i => !(vIdx sy).contains i) && pCases.all (prefixOK sy E S) && vCases.all (caseOK sy m0 S) && lastOK sy E S

/-- what `vertOK` says, one fact per field -/
structure VFacts (sy : Syms) (m0 : Machine) (S : UInt8) : Prop where
  base : FrameModel.baseOK m0 = true
  ds : ∀ d ∈ detours sy (Rom.of m0) S, d.ok (Rom.of m0) = true
  tags : ∀ c ∈ vCases, FrameModel.tagsOK S (vTags sy (vmach sy m0 S) c) = true
  idx : nodupB (vIdx sy) = true
  out : ∀ i ∈ outV sy, (vIdx sy).contains i = false
  pre : ∀ c ∈ pCases, prefixOK sy (Rom.of m0) S c = true
  cases : ∀ c ∈ vCases, caseOK sy m0 S c = true
  last : lastOK sy (Rom.of m0) S = true

theorem vfacts_of {sy : Syms} {m0 : Machine} {S : UInt8} (h : vertOK sy m0 S = true) : VFacts sy m0 S := by
  simp only [vertOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## The proof -/

section proof

variable {sy : Syms} {m0 : Machine}

theorem peek_I (m : Machine) (a : UInt16) : peek m a = m.ram.get! (I a) := rfl

theorem ab_all : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0xC0) ∈ [(0 : UInt8), 0x40, 0x80, 0xC0] ∧
    (((UInt8.ofNat n.val &&& 0xC0) &&& 0x80 != 0) = (UInt8.ofNat n.val &&& 0x80 != 0)) ∧
    ((if (UInt8.ofNat n.val &&& 0x80 != 0) = true then (0x80 : UInt8) else 0) = (UInt8.ofNat n.val &&& 0xC0) &&& 0x80) := by decide +kernel

theorem ab_facts (x : UInt8) : (x &&& 0xC0) ∈ [(0 : UInt8), 0x40, 0x80, 0xC0] ∧ (((x &&& 0xC0) &&& 0x80 != 0) = (x &&& 0x80 != 0)) ∧
    ((if (x &&& 0x80 != 0) = true then (0x80 : UInt8) else 0) = (x &&& 0xC0) &&& 0x80) := by
  have h := ab_all ⟨x.toNat, x.toNat_lt⟩
  simpa using h

theorem pcase_mem {st area raw : UInt8} {prevA : Bool} (h1 : st ∈ [(0 : UInt8), 1, 2]) (h2 : area ∈ [(1 : UInt8), 2, 3]) :
    ({ st, area, raw, prevA } : PCase) ∈ pCases := by
  simp only [pCases, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨st, h1, area, h2, prevA, by cases prevA <;> simp, raw.toNat, raw.toNat_lt, ?_⟩
  simp

theorem vcase_mem {st ab : UInt8} {prevA : Bool} (h1 : st ∈ [(0 : UInt8), 1, 2]) (h2 : ab ∈ [(0 : UInt8), 0x40, 0x80, 0xC0]) :
    ({ st, ab, prevA } : VCase) ∈ vCases := by
  simp only [vCases, List.mem_flatMap, List.mem_map]
  exact ⟨st, h1, ab, h2, prevA, by cases prevA <;> simp, rfl⟩

/-- **The vertical movement of a real frame.** From the player's routine to the scroll handler, the vertical bytes read from the machine follow `vstep` on the machine
`vmach`: with A of this frame and the stored speed. Two conditions on the state at the player's routine: in a jump the jump's halt value is 1, and A on the frame before is
the A that the machine holds. -/
theorem vert_model {S : UInt8} {R : Machine} (hOK : vertOK sy m0 S = true) (h : FrameModel.AtCtrl0 sy (Rom.of m0) S R)
    (hd : peek R sy.Player_State = 1 → peek R sy.DiffToHaltJump = 1)
    (hp : peek R sy.PreviousA_B_Buttons &&& 0x80 = peek R sy.A_B_Buttons &&& 0x80) :
    ∃ k, k ≤ FrameModel.moveLen ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧ (stepN k R).s = S ∧
      vsOf sy (stepN k R) = vstepV sy m0 S (vsOf sy R) (peek R sy.SavedJoypadBits &&& 0x80 != 0) (peek R sy.Player_XSpeedAbsolute) ∧
      (peek (stepN k R) sy.Player_State = 1 → peek (stepN k R) sy.DiffToHaltJump = 1) := by
  have F := vfacts_of hOK
  have gB := FrameModel.base_good F.base
  obtain ⟨abm, a80, ab80⟩ := ab_facts (peek R sy.SavedJoypadBits)
  -- the first piece: from the player's routine to the movement routine
  let pc : PCase := { st := peek R sy.Player_State, area := peek R sy.AreaType, raw := peek R sy.SavedJoypadBits, prevA := peek R sy.PreviousA_B_Buttons &&& 0x80 != 0 }
  have hpm : pc ∈ pCases := pcase_mem h.st h.area
  have hA0 : At (Rom.of m0) (pc.c0 sy S) R := by
    refine ⟨h.good, h.pc, h.s, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      simp only [PCase.c0, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.eng
      · rfl
      · rfl
      · rfl
      · exact h.spring
      · exact h.swim
      · exact h.size
    · intro q hq
      simp only [PCase.c0, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact FrameModel.and80_mem _
    · intro v hv
      simp [PCase.c0] at hv
    · intro v hv
      simp [PCase.c0] at hv
    · intro v hv
      simp [PCase.c0] at hv
  have hpre := F.pre pc hpm
  simp only [prefixOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hpre
  obtain ⟨⟨⟨hpiece, hPpc⟩, hPs⟩, hK⟩ := hpre
  obtain ⟨kP, fP, AP, WP, _⟩ := FrameModel.piece_specI hpiece hA0
  have kX : ∀ q ∈ knownP sy (Rom.of m0) S pc, (stepN kP R).ram.get! q.1 = q.2 := fun q hq => AP.K q (List.contains_iff_mem.1 (hK q hq))
  have kmem : ∀ q, q ∈ knownP sy (Rom.of m0) S pc → (stepN kP R).ram.get! q.1 = q.2 := kX
  have wX : ∀ i ∈ watchP sy, i < 2048 → (stepN kP R).ram.get! i = R.ram.get! i := WP
  generalize hX : stepN kP R = X at AP kX kmem wX
  -- the machine of `vstep`
  let s0 := vsOf sy R
  let a := peek R sy.SavedJoypadBits &&& 0x80 != 0
  let ab := peek R sy.Player_XSpeedAbsolute
  have gP := FrameModel.poke_good (E := Rom.of m0) sy.DiffToHaltJump 1 gB
  have gV : GoodH (Rom.of m0) (vmach sy m0 S) := ⟨gP.prg, gP.mask, gP.halted, gP.trk, gP.size⟩
  have gH : GoodH (Rom.of m0) (vH sy m0 S s0 a ab) := FrameModel.pokeL_good _ gV
  have hHs : (vH sy m0 S s0 a ab).s = S := by
    show (pokeL (vmach sy m0 S) _).s = S
    rw [FrameModel.pokeL_s]
    rfl
  have hv : ∀ q ∈ vList sy s0 a ab, (vH sy m0 S s0 a ab).ram.get! (I q.1) = q.2 :=
    FrameModel.pokeL_get _ _ gV (by rw [show (vList sy s0 a ab).map (fun q => I q.1) = vIdx sy from rfl]; exact F.idx)
  have hout : ∀ i ∈ outV sy, (vH sy m0 S s0 a ab).ram.get! i = (vmach sy m0 S).ram.get! i := by
    intro i hi
    refine FrameModel.pokeL_out _ _ (fun q hq e => ?_)
    have h1 := F.out i hi
    have h2 : I q.1 ∈ vIdx sy := by
      rw [show vIdx sy = (vList sy s0 a ab).map (fun q => I q.1) from rfl]
      exact List.mem_map.2 ⟨q, hq, rfl⟩
    rw [e] at h2
    have h3 := List.contains_iff_mem.2 h2
    rw [h1] at h3
    cases h3
  have hV1 : (vmach sy m0 S).ram.get! (I sy.DiffToHaltJump) = 1 := FrameModel.poke_get_self _ _ gB.size
  -- the case of the walk
  let vc : VCase := { st := peek R sy.Player_State, ab := peek R sy.SavedJoypadBits &&& 0xC0, prevA := peek R sy.PreviousA_B_Buttons &&& 0x80 != 0 }
  have hvm : vc ∈ vCases := vcase_mem h.st abm
  have hc := F.cases vc hvm
  have htags := F.tags vc hvm
  simp only [FrameModel.tagsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at htags
  have hpv : vc.pv = (if s0.prevA then 0x80 else 0) := by
    show (if (peek R sy.PreviousA_B_Buttons &&& 0x80 != 0) = true then (0x80 : UInt8) else 0) = if ((peek R sy.A_B_Buttons &&& 0x80) != 0) = true then 0x80 else 0
    rw [hp]
  have hL : ∀ q ∈ vTags sy (vmach sy m0 S) vc, q.1 < 2048 ∧ q.1 ≠ stkI (vH sy m0 S s0 a ab).s ∧ q.1 ≠ stkI ((vH sy m0 S s0 a ab).s - 1) ∧
      q.2.R (X.ram.get! q.1) ((vH sy m0 S s0 a ab).ram.get! q.1) := by
    intro q hq
    obtain ⟨⟨t1, t2⟩, t3⟩ := htags q hq
    rw [hHs]
    refine ⟨t1, t2, t3, ?_⟩
    have wv : ∀ u : UInt16, I u ∈ watchP sy → X.ram.get! (I u) = peek R u := fun u hu => wX _ hu (FrameModel.I_lt _)
    simp only [vTags, vIds, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (wv sy.Player_Y_Position (List.mem_append_left _ (.head _))).trans (hv (sy.Player_Y_Position, s0.y) (.head _)).symm
    · exact (wv sy.Player_Y_MoveForce (List.mem_append_left _ (.tail _ (.head _)))).trans (hv (sy.Player_Y_MoveForce, s0.mf) (.tail _ (.head _))).symm
    · exact (wv sy.Player_Y_Speed (List.mem_append_left _ (.tail _ (.tail _ (.head _))))).trans (hv (sy.Player_Y_Speed, s0.vy) (.tail _ (.tail _ (.head _)))).symm
    · exact (wv sy.Player_YMF_Dummy (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _)))))).trans (hv (sy.Player_YMF_Dummy, s0.dummy) (.tail _ (.tail _ (.tail _ (.head _))))).symm
    · exact (wv sy.VerticalForce (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))).trans (hv (sy.VerticalForce, s0.vf) (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))).symm
    · exact (wv sy.VerticalForceDown (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))).trans (hv (sy.VerticalForceDown, s0.vfd) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))).symm
    · exact (wv sy.JumpOrigin_Y_Position (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))).trans (hv (sy.JumpOrigin_Y_Position, s0.origin) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))).symm
    · -- the state
      have e1 : X.ram.get! (I sy.Player_State) = peek R sy.Player_State := kmem (I sy.Player_State, pc.st) (.tail _ (.head _))
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.Player_State) = s0.st := hv (sy.Player_State, s0.st) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
      rw [e1, e2]
      exact FrameModel.Tag.R_kn _ _
    · -- the stored speed
      have e1 : X.ram.get! (I sy.Player_XSpeedAbsolute) = peek R sy.Player_XSpeedAbsolute := wv sy.Player_XSpeedAbsolute (List.mem_append_right _ (.head _))
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.Player_XSpeedAbsolute) = ab := hv (sy.Player_XSpeedAbsolute, ab) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
      show X.ram.get! (I sy.Player_XSpeedAbsolute) = (vH sy m0 S s0 a ab).ram.get! (I sy.Player_XSpeedAbsolute)
      rw [e1, e2]
    · -- A and B
      have e1 : X.ram.get! (I sy.A_B_Buttons) = peek R sy.SavedJoypadBits &&& 0xC0 := kmem (I sy.A_B_Buttons, pc.raw &&& 0xC0) (.tail _ (.tail _ (.head _)))
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.A_B_Buttons) = if a then 0x80 else 0 := hv (sy.A_B_Buttons, if a then 0x80 else 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
      rw [e1, e2]
      show (FrameModel.Tag.kn _ _).R _ (if (peek R sy.SavedJoypadBits &&& 0x80 != 0) = true then (0x80 : UInt8) else 0)
      rw [ab80]
      exact FrameModel.Tag.R_kn _ _
    · -- A on the frame before
      have e1 : X.ram.get! (I sy.PreviousA_B_Buttons) = peek R sy.PreviousA_B_Buttons := wv sy.PreviousA_B_Buttons (List.mem_append_right _ (.tail _ (.head _)))
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.PreviousA_B_Buttons) = if s0.prevA then 0x80 else 0 :=
        hv (sy.PreviousA_B_Buttons, if s0.prevA then 0x80 else 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
      rw [e1, e2, ← hpv]
      exact ⟨FrameModel.and80_mem _, TaintRun.mem_known_self _⟩
    · have e1 : X.ram.get! (I sy.GameEngineSubroutine) = sy.Eng_PlayerCtrl.toUInt8 := kmem (I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (.head _)
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.GameEngineSubroutine) = sy.Eng_PlayerCtrl.toUInt8 :=
        hv (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))
      rw [e1, e2]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.JumpspringAnimCtrl) = 0 := kmem (I sy.JumpspringAnimCtrl, 0) (.tail _ (.tail _ (.tail _ (.head _))))
      rw [e1, hout (I sy.JumpspringAnimCtrl) (.head _)]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.SwimmingFlag) = 0 := kmem (I sy.SwimmingFlag, 0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
      rw [e1, hout (I sy.SwimmingFlag) (.tail _ (.head _))]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.PlayerChangeSizeFlag) = 0 := kmem (I sy.PlayerChangeSizeFlag, 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
      rw [e1, hout (I sy.PlayerChangeSizeFlag) (.tail _ (.tail _ (.head _)))]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.DiffToHaltJump) = peek R sy.DiffToHaltJump := wv sy.DiffToHaltJump (List.mem_append_right _ (.tail _ (.tail _ (.head _))))
      rw [e1, hout (I sy.DiffToHaltJump) (.tail _ (.tail _ (.tail _ (.head _)))), hV1]
      by_cases h1 : peek R sy.Player_State = 1
      · have e2 : (vc.st == 1) = true := by simp [vc, h1]
        simp only [e2, if_true]
        rw [hd h1]
        exact FrameModel.Tag.R_kn _ _
      · have e2 : (vc.st == 1) = false := by simp [vc, h1]
        simp only [e2, Bool.false_eq_true, if_false]
        exact ⟨TaintRun.mem_top _, TaintRun.mem_known_self _⟩
  -- the walk with detours, to the routine's return
  have hstop : ∀ Q, stopV (Rom.of m0) S Q = true → 0x8000 ≤ Q.pc ∧ FrameModel.lookupOp ((Rom.of m0).b Q.pc) FrameModel.insList = some .rts ∧
      FrameModel.idleAt (Rom.of m0) Q.pc = false ∧ Q.s = some (S - 2) := by
    intro Q hQ
    simp only [stopV, isRts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hQ
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hQ
    exact ⟨h1, by rw [h2]; exact FrameModel.lookup_rts, h3, h4⟩
  have hgoal : ∀ Q, goalV sy S Q = true → Q.w (stkI (vH sy m0 S s0 a ab).s) = false ∧ Q.w (stkI ((vH sy m0 S s0 a ab).s - 1)) = false := by
    intro Q hQ
    rw [hHs]
    simp only [goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hQ
    exact ⟨hQ.1.2 (stkI S) (.tail _ (.head _)), hQ.1.2 (stkI (S - 1)) (.tail _ (.tail _ (.head _)))⟩
  obtain ⟨k, Q, hk, hs, hg, gX', pcX', sX', rel, fix⟩ :=
    FrameModel.leafD_spec (ain := 0) F.ds hc (by decide) hstop hgoal AP.good (by rw [AP.pc, hPpc]) (by rw [AP.s, hPs]) gH (by rw [hHs]) hL
  simp only [goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨_, heq⟩, hw⟩, hdt⟩ := hg
  have veq : ∀ i ∈ I sy.Player_State :: vIds sy, (stepN k X).ram.get! i = (vRun sy m0 S s0 a ab).ram.get! i := by
    intro i hi
    have hi2 : i < 2048 := by
      simp only [vIds, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact FrameModel.I_lt _
    exact FrameModel.tagImp_R (heq i hi) (rel i hi2)
  -- the return, on the real machine
  obtain ⟨p1, p2, p3, _⟩ := hstop Q hs
  obtain ⟨y1, y2, y3, y4⟩ := FrameModel.step_rts gX' (by rw [pcX']; exact p1) (by rw [pcX']; exact p2) (by rw [pcX']; exact p3)
  rw [← FrameModel.stepN_one] at y1 y2 y3 y4
  obtain ⟨sp1, sp2⟩ := FrameModel.stack_two S
  have r1 : (stepN k X).ram.get! (stkI (S - 1)) = retLo sy (Rom.of m0) S := by
    rw [fix _ (FrameModel.mask_stk _) (hw (stkI (S - 1)) (.tail _ (.tail _ (.head _))))]
    exact kmem (stkI (S - 1), retLo sy (Rom.of m0) S) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  have r2 : (stepN k X).ram.get! (stkI S) = retHi sy (Rom.of m0) S := by
    rw [fix _ (FrameModel.mask_stk _) (hw (stkI S) (.tail _ (.head _)))]
    exact kmem (stkI S, retHi sy (Rom.of m0) S) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have hYpc : (stepN 1 (stepN k X)).pc = retPc sy (Rom.of m0) S := by
    rw [y1, sX', sp2, sp1, r1, r2]
    rfl
  have hYs : (stepN 1 (stepN k X)).s = S := by rw [y2, sX', sp2]
  -- the last piece, to the scroll handler
  have hAY : At (Rom.of m0) { pc := retPc sy (Rom.of m0) S, s := S, K := [] } (stepN 1 (stepN k X)) :=
    ⟨y4, hYpc, hYs, (fun q hq => by cases hq), (fun q hq => by cases hq), (fun v hv => by cases hv), (fun v hv => by cases hv), (fun v hv => by cases hv)⟩
  obtain ⟨kL, fL, AL, WL, _⟩ := FrameModel.piece_specI F.last hAY
  have wZ : ∀ i ∈ watchR sy, i < 2048 → (stepN kL (stepN 1 (stepN k X))).ram.get! i = (stepN k X).ram.get! i := by
    intro i hi hl
    rw [WL i hi hl, y3]
  have eZ : stepN (kP + (k + (1 + kL))) R = stepN kL (stepN 1 (stepN k X)) := by
    rw [FrameModel.stepN_add, hX, FrameModel.stepN_add, FrameModel.stepN_add]
  refine ⟨kP + (k + (1 + kL)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : FrameModel.moveLen = 728 := rfl
    have e2 : fuelP = 60 := rfl
    have e3 : fuelV = 600 := rfl
    rw [e1]
    rw [e2] at fP
    rw [e3] at hk
    omega
  · rw [eZ]
    exact AL.good
  · rw [eZ]
    exact AL.pc
  · rw [eZ]
    exact AL.s
  · rw [eZ, vstepV_eq]
    have wv : ∀ u : UInt16, I u ∈ I sy.Player_State :: vIds sy →
        peek (stepN kL (stepN 1 (stepN k X))) u = peek (vRun sy m0 S s0 a ab) u := by
      intro u hu
      rw [peek_I, peek_I, wZ (I u) (by
        simp only [List.mem_cons] at hu
        rcases hu with hu | hu
        · rw [hu]
          exact List.mem_append_right _ (.head _)
        · exact List.mem_append_left _ hu) (FrameModel.I_lt _)]
      exact veq _ hu
    have wab : peek (stepN kL (stepN 1 (stepN k X))) sy.A_B_Buttons = peek R sy.SavedJoypadBits &&& 0xC0 := by
      rw [peek_I, wZ (I sy.A_B_Buttons) (List.mem_append_right _ (.tail _ (.head _))) (FrameModel.I_lt _),
        fix _ (FrameModel.I_lt _) (hw (I sy.A_B_Buttons) (.head _))]
      exact kmem (I sy.A_B_Buttons, pc.raw &&& 0xC0) (.tail _ (.tail _ (.head _)))
    show Jump.VS.mk _ _ _ _ _ _ _ _ _ = _
    rw [wv sy.Player_Y_Position (.tail _ (.head _)), wv sy.Player_Y_MoveForce (.tail _ (.tail _ (.head _))), wv sy.Player_Y_Speed (.tail _ (.tail _ (.tail _ (.head _)))),
      wv sy.Player_YMF_Dummy (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), wv sy.VerticalForce (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), wv sy.VerticalForceDown (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))),
      wv sy.JumpOrigin_Y_Position (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), wv sy.Player_State (.head _), wab, a80]
  · rw [eZ]
    intro hst
    have e1 : (stepN k X).ram.get! (I sy.Player_State) = 1 := by
      rw [← wZ (I sy.Player_State) (List.mem_append_right _ (.head _)) (FrameModel.I_lt _)]
      exact hst
    cases hq : (Q.ram (I sy.Player_State)).same with
    | none =>
      rw [hq] at hdt
      cases hdt
    | some v =>
      rw [hq] at hdt
      have e2 := (FrameModel.Tag.same_spec hq (rel _ (FrameModel.I_lt _))).1
      rw [e1] at e2
      subst e2
      simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hdt
      have e3 := (FrameModel.Tag.same_spec hdt (rel _ (FrameModel.I_lt _))).1
      show (stepN kL (stepN 1 (stepN k X))).ram.get! (I sy.DiffToHaltJump) = 1
      rw [wZ (I sy.DiffToHaltJump) (List.mem_append_right _ (.tail _ (.tail _ (.head _)))) (FrameModel.I_lt _)]
      exact e3

end proof

/-! ## On the ROM: a program, no part of the proof -/

/-- why a case fails -/
def caseWhy (sy : Syms) (m0 : Machine) (S : UInt8) (c : VCase) : List String :=
  let E := Rom.of m0
  match walkDWhy E (detours sy E S) (stopV E S) (goalV sy S) fuelV (vStartQ sy (vmach sy m0 S) S c) with
  | some (pc, w) => [s!"walk at {pc}: {w}"]
  | none => []

end Smbrta.VertModel
