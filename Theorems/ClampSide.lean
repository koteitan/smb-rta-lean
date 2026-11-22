import Theorems.ScrollRule

/-!
# Above ground: the side of the clamp at the screen's edge

At the end of the scroll handler the game calls the routine of the player's offscreen bits (`ChkPOffscr`, `ScrollRule.Places.chk`). It reads the screen's right
edge and then its left edge, each as a pixel and a page, and his pixel and page. From the bits it finds it calls the clamp at the screen's edge
(`ScreenClamp`) with `Y = 0` (the left edge) or `Y = 1` (the right edge), or it does not call it. `ScreenClamp` and `ScrollRule` follow the clamp and the
scroll, but not this choice: `ScrollRule.tailCheck` walks the routine without its branches.

Here (`chk_end`): from the routine's start the machine comes to the clamp's entry with `Y = t` when `selM R = some t`, and to the scroll handler's return
instruction when `selM R = none`, with the position, the two edges and the stack above it kept. `selM` is read from the two differences, each 16 bits: the
right edge minus his pixel, and the left edge minus his pixel (`sideBits`, `xOf`, `divX`, `selOf`, with the routine's tables read from the ROM).

`side_rel` turns this into a statement about pixels: when the right edge is the left edge plus 255 (modulo 2¹⁶), the routine leaves him at most 255 px right of
the left edge and not left of it, counted modulo 2¹⁶ (`left_after`): it clamps him to the left edge when he is at or left of it, or more than 255 px right of
it; to the right edge minus the clamp's amount when he is in the last pixels before the right edge; and else leaves him where he is. This is the fact
"the clamp keeps him at or right of the screen's left edge" that the old field `SurfaceFrames.OnFrames.nearStep` needs: round 30 makes `nearStep` the theorem
`SurfaceFrames.OnFrames.nearStepAt`, with the right edge's relation and the rest of the frame after the return instruction as the new fields `rightRel` and
`endKeep`. Round 31: `rightRel` is gone (`RightEdge`: `SurfaceFrames.OnFrames.relAll`, `SurfaceFrames.OnFrames.pageAll`), and the pieces keep his speed too
(`W0`), for the field `clampR` at the clamp's entry. `Moves.stop` needs it too, with the edge at the frame's start.

The proof is by pieces of the ROM's code with known values (as `ScreenClamp`, `ScrollRule`): the check `check` walks each piece for every value of the bytes it
compares (the low bytes and the pages of the two differences, the low difference in the divide, the stack byte at the calls). The addresses come from the ROM:
the call at the routine's start and the operands of its instructions. No game data. Page: `1-1/e-2-10-3-18-ClampSide.md`.
-/

namespace Smbrta.ClampSide
open FrameModel ImpedePosition

/-- the places of the clamp's choice, read from the program -/
structure Places where
  /-- the routine's start (`ChkPOffscr`), the offscreen bits' routine, its loop over the two edges, the load of the edge's page, the call of the divide, and the load of the bits -/
  chk : UInt16
  gx : UInt16
  loop : UInt16
  pgL : UInt16
  div : UInt16
  ld : UInt16
  /-- the clamp's entry and the scroll handler's return instruction (`ScreenClamp.places`) -/
  entry : UInt16
  ret : UInt16
  /-- the zero-page bytes of the saved index and of the low difference -/
  z04 : Nat
  z07 : Nat
  /-- the tables of the offsets and of the bits -/
  dxo : UInt16
  tbl : UInt16
  /-- the divide's compare value, its adder, its mask, and the mask of the routine's test for the right edge -/
  thr : UInt8
  add : UInt8
  msk : UInt8
  m20 : UInt8
  /-- the edges' pixel and page (the left edge, and one byte after it the right edge), and the position -/
  edgeX : UInt16
  edgeP : UInt16
  /-- the clamp's table of amounts -/
  table : UInt16
  x : Nat
  page : Nat
  frac : Nat
  /-- round 31: his speed, which the routine of the offscreen bits keeps (for the field `clampR` at the clamp's entry) -/
  speed : Nat
  deriving Inhabited

/-- the places: the offscreen bits' routine is the target of the call at the routine's start; the rest are fixed offsets in it, which the pieces check -/
def places (sy : Syms) (m0 : Machine) : Places :=
  let E := Rom.of m0
  let S := ScrollRule.places sy m0
  let C := ScreenClamp.places sy m0
  let gx := E.w (S.chk + 3)
  let loop := gx + 4
  let div := loop + 27
  let ld := loop + 36
  let dv := E.w (div + 7)
  { chk := S.chk, gx, loop, pgL := loop + 8, div, ld, entry := C.entry, ret := C.ret,
    z04 := (E.b (gx + 1)).toNat, z07 := (E.b (loop + 7)).toNat, dxo := E.w (loop + 14), tbl := E.w (ld + 1),
    thr := E.b (div + 1), add := E.b (div + 5), msk := E.b (dv + 12), m20 := E.b (S.chk + 16),
    edgeX := C.edgeX, edgeP := C.edgeP, table := C.table, x := C.x, page := C.page, frac := C.frac, speed := I sy.Player_X_Speed }

/-- the edge's pixel and page for `Y = y` (0: left, 1: right) -/
def eX (P : Places) (y : UInt8) : Nat := I (P.edgeX + y.toUInt16)
def eP (P : Places) (y : UInt8) : Nat := I (P.edgeP + y.toUInt16)

theorem eX_zero (P : Places) : eX P 0 = I P.edgeX := by unfold eX; simp
theorem eP_zero (P : Places) : eP P 0 = I P.edgeP := by unfold eP; simp

/-- the bytes every piece keeps: the position and the two edges (round 31: and his speed) -/
def W0 (P : Places) : List Nat := [P.x, P.page, P.frac, eX P 0, eX P 1, eP P 0, eP P 1, P.speed]

/-- the return address of the call at the routine's start -/
def retLo (P : Places) : UInt8 := (P.chk + 4).toUInt8
def retHi (P : Places) : UInt8 := ((P.chk + 4) >>> 8).toUInt8

/-! ## The choice, as the code makes it -/

/-- the low byte of `e − v` and its carry (no borrow) -/
def lo (e v : UInt8) : UInt8 × Bool := adcC e (~~~v) true
/-- the high byte of the difference, with the carry `c` of the low byte -/
def hi (e v : UInt8) (c : Bool) : UInt8 := (adcC e (~~~v) c).1

/-- the divide: the index of the bits from the low difference `d` -/
def divX (P : Places) (y d xin : UInt8) : UInt8 :=
  if P.thr ≤ d then xin else if y == 0 then ((d >>> 3) &&& P.msk) + P.add else (d >>> 3) &&& P.msk

/-- the index of the bits for the edge `y`, from the low byte and the high byte of the difference -/
def xOf (E : Rom) (P : Places) (y l h : UInt8) : UInt8 :=
  if h &&& 0x80 != 0 then E.b (P.dxo + y.toUInt16)
  else if h == 0 then divX P y l (E.b (P.dxo + 1 + y.toUInt16))
  else E.b (P.dxo + 1 + y.toUInt16)

/-- the bits -/
def bitsOf (E : Rom) (P : Places) (v : UInt8) : UInt8 := E.b (P.tbl + v.toUInt16)

/-- the clamp's selector from the bits: bit 7 the left edge, the routine's mask the right edge, else no clamp -/
def selOf (P : Places) (b : UInt8) : Option UInt8 :=
  if b &&& 0x80 != 0 then some 0 else if b &&& P.m20 != 0 then some 1 else none

/-- the bits of the edge `y`, from the edge's pixel `e` and page `ep` and his pixel `v` and page `p` -/
def sideBits (E : Rom) (P : Places) (y e v ep p : UInt8) : UInt8 :=
  bitsOf E P (xOf E P y (lo e v).1 (hi ep p (lo e v).2))

/-- **the clamp's selector on a machine**: the right edge first; if its bits are 0, the left edge -/
def selM (E : Rom) (P : Places) (R : Machine) : Option UInt8 :=
  let bR := sideBits E P 1 (R.ram.get! (eX P 1)) (R.ram.get! P.x) (R.ram.get! (eP P 1)) (R.ram.get! P.page)
  if bR != 0 then selOf P bR
  else selOf P (sideBits E P 0 (R.ram.get! (eX P 0)) (R.ram.get! P.x) (R.ram.get! (eP P 0)) (R.ram.get! P.page))

/-! ## The pieces -/

/-- a piece with a known stack pointer, and `Y` known at its start or its end when asked -/
def startSY (c : Cut) (y : Option UInt8) : TS := { startQ c with y := match y with | some v => Tag.kn v v | none => .eq }
def goalSY (c : Cut) (watch : List Nat) (y : Option UInt8) (Q : TS) : Bool :=
  goalC c watch Q && (match y with | some v => Q.y.same == some v | none => true)
def pieceSY (E : Rom) (c c' : Cut) (watch : List Nat) (y y' : Option UInt8) (fuel : Nat) : Bool :=
  walkT E (fun Q => Q.pc == c'.pc) (goalSY c' watch y') fuel (startSY c y)

/-- four stack bytes above `s` -/
def stk4 (s : UInt8) : List Nat := [stkI (s + 1), stkI (s + 1 + 1), stkI (s + 1 + 1 + 1), stkI (s + 1 + 1 + 1 + 1)]

/-- the routine's start: the call of the offscreen bits' routine, up to its loop with `Y = 1` -/
def jCheck (E : Rom) (P : Places) (s : UInt8) : Bool :=
  pieceSY E { pc := P.chk, s, K := [] } { pc := P.loop, s := s - 1 - 1, K := [(stkI s, retHi P), (stkI (s - 1), retLo P), (P.z04, 0)], x := some 0 }
    (W0 P ++ [stkI (s + 1), stkI (s + 1 + 1)]) none (some 1) 8

/-- the low byte of the difference of the edge's pixel and his -/
def s1Check (E : Rom) (P : Places) (y e v : UInt8) : Bool :=
  ScreenClamp.pieceY E { pc := P.loop, s := 0, K := [(eX P y, e), (P.x, v)], x := some 0 }
    { pc := P.pgL, s := 0, K := [(P.z07, (lo e v).1)], x := some 0, cf := some (lo e v).2 } (W0 P ++ [P.z04] ++ stackI) y 8

/-- where the high byte `h` of the difference leads: the bits, or the divide -/
def s2Goal (E : Rom) (P : Places) (y h : UInt8) : Cut :=
  if h &&& 0x80 != 0 then { pc := P.ld, s := 0, K := [], x := some (E.b (P.dxo + y.toUInt16)) }
  else if h == 0 then { pc := P.div, s := 0, K := [], x := some (E.b (P.dxo + 1 + y.toUInt16)) }
  else { pc := P.ld, s := 0, K := [], x := some (E.b (P.dxo + 1 + y.toUInt16)) }

/-- the high byte of the difference, with the carry of the low byte -/
def s2Check (E : Rom) (P : Places) (y ep p : UInt8) (c : Bool) : Bool :=
  ScreenClamp.pieceY E { pc := P.pgL, s := 0, K := [(eP P y, ep), (P.page, p)], x := some 0, cf := some c }
    (s2Goal E P y (hi ep p c)) (W0 P ++ [P.z04, P.z07] ++ stackI) y 12

/-- the divide (a call), from the low difference `d` -/
def s3Check (E : Rom) (P : Places) (y d s : UInt8) : Bool :=
  pieceSY E { pc := P.div, s, K := [(P.z07, d)], x := some (E.b (P.dxo + 1 + y.toUInt16)) }
    { pc := P.ld, s, K := [], x := some (divX P y d (E.b (P.dxo + 1 + y.toUInt16))) } (W0 P ++ [P.z04] ++ stk4 s) (some y) (some y) 24

/-- where the bits lead: the loop again with `Y = 0` (bits 0 on the right edge), or the return of the offscreen bits' routine and the routine's test, to
the clamp's entry with its selector or to the scroll handler's return -/
def s4Goal (E : Rom) (P : Places) (y v s : UInt8) : Cut × Option UInt8 × List Nat :=
  let b := bitsOf E P v
  if b == 0 && y == 1 then ({ pc := P.loop, s, K := [], x := some 0 }, some 0, W0 P ++ [P.z04] ++ stk4 s)
  else match selOf P b with
    | some t => ({ pc := P.entry, s := s + 1 + 1, K := [] }, some t, W0 P ++ [stkI (s + 1 + 1 + 1), stkI (s + 1 + 1 + 1 + 1)])
    | none => ({ pc := P.ret, s := s + 1 + 1, K := [] }, none, W0 P ++ [stkI (s + 1 + 1 + 1), stkI (s + 1 + 1 + 1 + 1)])

def s4Check (E : Rom) (P : Places) (y v s : UInt8) : Bool :=
  let g := s4Goal E P y v s
  pieceSY E { pc := P.ld, s, K := [(P.z04, 0), (stkI (s + 1), retLo P), (stkI (s + 1 + 1), retHi P)], x := some v } g.1 g.2.2 (some y) g.2.1 40

/-- every index of the bits is below 16 -/
def xBound (E : Rom) (P : Places) : Bool :=
  [(0 : UInt8), 1].all fun y => decide (E.b (P.dxo + y.toUInt16) < 16) && decide (E.b (P.dxo + 1 + y.toUInt16) < 16) &&
    (List.range 256).all fun d => decide (divX P y d.toUInt8 (E.b (P.dxo + 1 + y.toUInt16)) < 16)

def checkParts (E : Rom) (P : Places) : Bool :=
  [P.x, P.page, P.frac, P.z04, P.z07, P.speed].all (fun i => decide (i < 2048)) && xBound E P &&
  (List.range 256).all (fun s => jCheck E P s.toUInt8) &&
  [(0 : UInt8), 1].all (fun y => (List.range 256).all fun e => (List.range 256).all fun v => s1Check E P y e.toUInt8 v.toUInt8) &&
  [(0 : UInt8), 1].all (fun y => (List.range 256).all fun ep => (List.range 256).all fun p => [false, true].all fun c => s2Check E P y ep.toUInt8 p.toUInt8 c) &&
  [(0 : UInt8), 1].all (fun y => (List.range 256).all fun d => (List.range 256).all fun s => s3Check E P y d.toUInt8 s.toUInt8) &&
  [(0 : UInt8), 1].all (fun y => (List.range 16).all fun v => (List.range 256).all fun s => s4Check E P y v.toUInt8 s.toUInt8)

/-- **The check on the ROM** -/
def check (sy : Syms) (m0 : Machine) : Bool := checkParts (Rom.of m0) (places sy m0)

/-! ## What the check says -/

structure Facts (E : Rom) (P : Places) : Prop where
  lt : ∀ i ∈ [P.x, P.page, P.frac, P.z04, P.z07, P.speed], i < 2048
  xb : xBound E P = true
  j : ∀ s, jCheck E P s = true
  s1 : ∀ y, y ∈ [(0 : UInt8), 1] → ∀ e v, s1Check E P y e v = true
  s2 : ∀ y, y ∈ [(0 : UInt8), 1] → ∀ ep p c, s2Check E P y ep p c = true
  s3 : ∀ y, y ∈ [(0 : UInt8), 1] → ∀ d s, s3Check E P y d s = true
  s4 : ∀ y, y ∈ [(0 : UInt8), 1] → ∀ v : UInt8, v.toNat < 16 → ∀ s, s4Check E P y v s = true

theorem facts_of_check {E : Rom} {P : Places} (h : checkParts E P = true) : Facts E P := by
  unfold checkParts at h
  obtain ⟨h, h4⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h3⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h2⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h1⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, hj⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h0, hx⟩ := Bool.and_eq_true_iff.1 h
  refine ⟨fun i hi => by simpa using List.all_eq_true.1 h0 i hi, hx, ScrollRule.all256 hj, ?_, ?_, ?_, ?_⟩
  · intro y hy e v
    have a := List.all_eq_true.1 h1 y hy
    exact ScrollRule.all256 (f := fun v => s1Check E P y e v) (ScrollRule.all256 (f := fun e => (List.range 256).all fun v => s1Check E P y e v.toUInt8) a e) v
  · intro y hy ep p c
    have a := List.all_eq_true.1 h2 y hy
    have b := ScrollRule.all256 (f := fun p => [false, true].all fun c => s2Check E P y ep p c)
      (ScrollRule.all256 (f := fun ep => (List.range 256).all fun p => [false, true].all fun c => s2Check E P y ep p.toUInt8 c) a ep) p
    exact List.all_eq_true.1 b c (by cases c <;> simp)
  · intro y hy d s
    have a := List.all_eq_true.1 h3 y hy
    exact ScrollRule.all256 (f := fun s => s3Check E P y d s) (ScrollRule.all256 (f := fun d => (List.range 256).all fun s => s3Check E P y d s.toUInt8) a d) s
  · intro y hy v hv s
    have a := List.all_eq_true.1 h4 y hy
    have b := List.all_eq_true.1 a v.toNat (List.mem_range.2 hv)
    simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 b s.toNat (List.mem_range.2 s.toNat_lt)

section
variable {E : Rom} {P : Places}

theorem lt_x (F : Facts E P) : P.x < 2048 := F.lt _ (by simp)
theorem lt_page (F : Facts E P) : P.page < 2048 := F.lt _ (by simp)
theorem lt_frac (F : Facts E P) : P.frac < 2048 := F.lt _ (by simp)
theorem lt_z04 (F : Facts E P) : P.z04 < 2048 := F.lt _ (by simp)
theorem lt_z07 (F : Facts E P) : P.z07 < 2048 := F.lt _ (by simp)

theorem lt_W0 (F : Facts E P) {i : Nat} (h : i ∈ W0 P) : i < 2048 := by
  simp only [W0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lt_x F
  · exact lt_page F
  · exact lt_frac F
  all_goals first | exact I_lt _ | exact F.lt _ (by simp)

theorem lt_stk4 {s : UInt8} {i : Nat} (h : i ∈ stk4 s) : i < 2048 := by
  simp only [stk4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact mask_stk _

theorem eX_mem {y : UInt8} (hy : y ∈ [(0 : UInt8), 1]) : eX P y ∈ W0 P := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [W0]

theorem eP_mem {y : UInt8} (hy : y ∈ [(0 : UInt8), 1]) : eP P y ∈ W0 P := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [W0]

theorem stk4_sub {s : UInt8} {i : Nat} (h : i ∈ stk4 s) : i ∈ stackI := by
  simp only [stk4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact stack_mem _

/-- a machine at a cut, from its parts -/
theorem mkAtX {R : Machine} {pc : UInt16} {K : List (Nat × UInt8)} {x : Option UInt8} {cf : Option Bool}
    (hg : Good E R) (hp : R.pc = pc) (hk : ∀ q ∈ K, R.ram.get! q.1 = q.2) (hx : ∀ v, x = some v → R.x = v)
    (hc : ∀ b, cf = some b → TaintRun.bt R.p 0 = b) : At E { pc, s := R.s, K, x, cf } R :=
  ⟨hg, hp, rfl, hk, (fun _ h => by cases h), (fun _ h => by cases h), hx, hc⟩

theorem lk_startSY {c : Cut} {y : Option UInt8} {m : Machine} (h : At E c m) (hy : ∀ v, y = some v → m.y = v) :
    Lk E m m (startSY c y) m m := by
  have H := lk_self h
  refine ⟨H.gl, H.gr, H.pcl, H.pcr, ⟨H.regs.a, H.regs.x, ?_, H.regs.c, H.regs.z, H.regs.nf⟩, H.s, H.s0, H.ram, H.fixl, H.fixr⟩
  show (match y with | some v => Tag.kn v v | none => Tag.eq).R m.y m.y
  cases hv : y with
  | none => rfl
  | some v => rw [hy v hv]; exact Tag.R_kn _ _

/-- a piece with a known stack pointer, on a real machine -/
theorem pieceSY_spec {c c' : Cut} {watch : List Nat} {y y' : Option UInt8} {fuel : Nat} {m : Machine}
    (hc : pieceSY E c c' watch y y' fuel = true) (h : At E c m) (hy : ∀ v, y = some v → m.y = v) :
    ∃ k, k ≤ fuel ∧ At E c' (stepN k m) ∧ (∀ v, y' = some v → (stepN k m).y = v) ∧
      (∀ i ∈ watch, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∧ InFrameN E m k := by
  obtain ⟨k, Q, h1, _, h3, h4, h5⟩ := walkT_spec (m₀ := m) (n₀ := m) fuel (startSY c y) m m hc (lk_startSY h hy)
  simp only [goalSY, Bool.and_eq_true] at h3
  obtain ⟨a, b, _⟩ := at_of_goal h3.1 h4
  refine ⟨k, h1, a, ?_, b, fun j hj => by obtain ⟨_, _, _, _, c1, _⟩ := h5 j hj; exact c1⟩
  intro v hv
  have h6 := h3.2
  rw [hv] at h6
  simp only [beq_iff_eq] at h6
  exact (Tag.same_spec h6 h4.regs.y).1

/-- every index of the bits is below 16 -/
theorem xOf_lt (F : Facts E P) {y : UInt8} (hy : y ∈ [(0 : UInt8), 1]) (l h : UInt8) : (xOf E P y l h).toNat < 16 := by
  have hb := List.all_eq_true.1 F.xb y hy
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb
  have h4 : ∀ d : UInt8, divX P y d (E.b (P.dxo + 1 + y.toUInt16)) < 16 := by
    intro d
    have e := List.all_eq_true.1 h3 d.toNat (List.mem_range.2 d.toNat_lt)
    simpa only [UInt8.ofNat_toNat, decide_eq_true_eq] using e
  have lt16 : ∀ u : UInt8, u < 16 → u.toNat < 16 := fun u hu => by
    have := UInt8.lt_iff_toNat_lt.1 hu
    simpa using this
  unfold xOf
  split
  · exact lt16 _ h1
  · split
    · exact lt16 _ (h4 l)
    · exact lt16 _ h2

/-- the difference's bytes on a machine, for the edge `y` -/
def lowM (P : Places) (y : UInt8) (M : Machine) : UInt8 × Bool := lo (M.ram.get! (eX P y)) (M.ram.get! P.x)
def highM (P : Places) (y : UInt8) (M : Machine) : UInt8 := hi (M.ram.get! (eP P y)) (M.ram.get! P.page) (lowM P y M).2
def xM (E : Rom) (P : Places) (y : UInt8) (M : Machine) : UInt8 := xOf E P y (lowM P y M).1 (highM P y M)

theorem mem_w1 {s : UInt8} {i : Nat} (h : i ∈ W0 P ++ [P.z04] ++ stk4 s) : i ∈ W0 P ++ [P.z04] ++ stackI := by
  simp only [List.mem_append] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (stk4_sub h)

theorem mem_w2 {s : UInt8} {i : Nat} (h : i ∈ W0 P ++ [P.z04] ++ stk4 s) : i ∈ W0 P ++ [P.z04, P.z07] ++ stackI := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inr (stk4_sub h)

theorem lt_w (F : Facts E P) {s : UInt8} {i : Nat} (h : i ∈ W0 P ++ [P.z04] ++ stk4 s) : i < 2048 := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (h | h) | h
  · exact lt_W0 F h
  · rw [h]; exact lt_z04 F
  · exact lt_stk4 h

/-- **one edge**: from the loop with `Y = y` and `X = 0` to the load of the bits, with `X` the index of the bits (`xM`); the position, the two edges, the
saved index and four stack bytes above are kept -/
theorem side_run (F : Facts E P) {M : Machine} {y : UInt8} (hy2 : y ∈ [(0 : UInt8), 1]) (hg : Good E M) (hpc : M.pc = P.loop)
    (hx : M.x = 0) (hy : M.y = y) :
    ∃ k, Good E (stepN k M) ∧ (stepN k M).pc = P.ld ∧ (stepN k M).s = M.s ∧ (stepN k M).y = y ∧ (stepN k M).x = xM E P y M ∧
      (∀ i ∈ W0 P ++ [P.z04] ++ stk4 M.s, (stepN k M).ram.get! i = M.ram.get! i) ∧ InFrameN E M k := by
  have A0 : At E { pc := P.loop, s := M.s, K := [(eX P y, M.ram.get! (eX P y)), (P.x, M.ram.get! P.x)], x := some 0 } M := by
    refine mkAtX hg hpc ?_ (fun v hv => by cases hv; exact hx) (fun _ h => by cases h)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> rfl
  obtain ⟨k1, _, A1, y1, W1, C1⟩ := ScreenClamp.pieceY_spec (F.s1 y hy2 (M.ram.get! (eX P y)) (M.ram.get! P.x)) A0 hy
  generalize hM1 : stepN k1 M = M1 at A1 y1 W1
  have w1 : ∀ i ∈ W0 P ++ [P.z04] ++ stk4 M.s, M1.ram.get! i = M.ram.get! i := fun i hi => W1 i (mem_w1 hi) (lt_w F hi)
  have w1' : ∀ i ∈ W0 P, M1.ram.get! i = M.ram.get! i := fun i hi => w1 i (by simp [hi])
  have s1 : M1.s = M.s := A1.s
  have z7 : M1.ram.get! P.z07 = (lowM P y M).1 := A1.K _ (List.mem_singleton.2 rfl)
  have A2 : At E { pc := P.pgL, s := M1.s, K := [(eP P y, M.ram.get! (eP P y)), (P.page, M.ram.get! P.page)], x := some 0, cf := some (lowM P y M).2 } M1 := by
    refine mkAtX A1.good A1.pc ?_ (fun v hv => A1.x v hv) (fun b hb => A1.cf b hb)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact w1' _ (eP_mem hy2)
    · exact w1' _ (by simp [W0])
  obtain ⟨k2, _, A3, y2, W2, C2⟩ := ScreenClamp.pieceY_spec (F.s2 y hy2 (M.ram.get! (eP P y)) (M.ram.get! P.page) (lowM P y M).2) A2 y1
  generalize hM2 : stepN k2 M1 = M2 at A3 y2 W2
  have w2 : ∀ i ∈ W0 P ++ [P.z04] ++ stk4 M.s, M2.ram.get! i = M.ram.get! i := fun i hi => (W2 i (mem_w2 hi) (lt_w F hi)).trans (w1 i hi)
  have z7' : M2.ram.get! P.z07 = (lowM P y M).1 := (W2 _ (by simp) (lt_z07 F)).trans z7
  have s2 : M2.s = M.s := A3.s.trans s1
  have e12 : stepN (k1 + k2) M = M2 := by rw [stepN_add, hM1, hM2]
  have hh : highM P y M = hi (M.ram.get! (eP P y)) (M.ram.get! P.page) (lowM P y M).2 := rfl
  unfold s2Goal at A3
  split at A3
  · rename_i h7
    refine ⟨k1 + k2, by rw [e12]; exact A3.good, by rw [e12]; exact A3.pc, by rw [e12]; exact s2, by rw [e12]; exact y2, ?_, by rw [e12]; exact w2,
      InFrameN.add' C1 hM1 C2⟩
    rw [e12, A3.x _ rfl]
    unfold xM xOf
    rw [← hh] at h7
    rw [if_pos h7]
  · rename_i h7
    split at A3
    · rename_i h8
      have A4 : At E { pc := P.div, s := M2.s, K := [(P.z07, (lowM P y M).1)], x := some (E.b (P.dxo + 1 + y.toUInt16)) } M2 :=
        mkAtX A3.good A3.pc (fun q hq => by rw [List.mem_singleton.1 hq]; exact z7') (fun v hv => A3.x v hv) (fun _ h => by cases h)
      obtain ⟨k3, _, A5, y3, W3, C3⟩ := pieceSY_spec (F.s3 y hy2 (lowM P y M).1 M2.s) A4 (fun v hv => by cases hv; exact y2)
      generalize hM3 : stepN k3 M2 = M3 at A5 y3 W3
      have e13 : stepN (k1 + k2 + k3) M = M3 := by rw [stepN_add, e12, hM3]
      refine ⟨k1 + k2 + k3, by rw [e13]; exact A5.good, by rw [e13]; exact A5.pc, by rw [e13]; exact A5.s.trans s2, by rw [e13]; exact y3 _ rfl, ?_, ?_,
        InFrameN.add' (InFrameN.add' C1 hM1 C2) e12 C3⟩
      · rw [e13, A5.x _ rfl]
        unfold xM xOf
        rw [← hh] at h7 h8
        rw [if_neg h7, if_pos h8]
      · rw [e13]
        intro i hi
        refine (W3 i ?_ (lt_w F hi)).trans (w2 i hi)
        rw [s2]
        exact hi
    · rename_i h8
      refine ⟨k1 + k2, by rw [e12]; exact A3.good, by rw [e12]; exact A3.pc, by rw [e12]; exact s2, by rw [e12]; exact y2, ?_, by rw [e12]; exact w2,
        InFrameN.add' C1 hM1 C2⟩
      rw [e12, A3.x _ rfl]
      unfold xM xOf
      rw [← hh] at h7 h8
      rw [if_neg h7, if_neg h8]

/-- the end of the routine for a selector -/
def finOf (P : Places) (o : Option UInt8) (s : UInt8) : Cut × Option UInt8 × List Nat :=
  match o with
  | some t => ({ pc := P.entry, s := s + 1 + 1, K := [] }, some t, W0 P ++ [stkI (s + 1 + 1 + 1), stkI (s + 1 + 1 + 1 + 1)])
  | none => ({ pc := P.ret, s := s + 1 + 1, K := [] }, none, W0 P ++ [stkI (s + 1 + 1 + 1), stkI (s + 1 + 1 + 1 + 1)])

theorem s4Goal_loop {v s : UInt8} (h : bitsOf E P v = 0) :
    s4Goal E P 1 v s = ({ pc := P.loop, s, K := [], x := some 0 }, some 0, W0 P ++ [P.z04] ++ stk4 s) := by
  unfold s4Goal
  simp [h]

theorem s4Goal_fin {y v s : UInt8} (h : bitsOf E P v ≠ 0 ∨ y = 0) : s4Goal E P y v s = finOf P (selOf P (bitsOf E P v)) s := by
  have hc : (bitsOf E P v == 0 && y == 1) = false := by
    rcases h with h | h
    · simp [h]
    · subst h; simp
  unfold s4Goal
  rw [if_neg (by rw [hc]; simp)]
  unfold finOf
  rfl

/-- the end of the routine: at the clamp's entry with `Y = t` (`o = some t`) or at the scroll handler's return instruction (`o = none`), with the stack `s` -/
def EndAt (P : Places) (o : Option UInt8) (s : UInt8) (R : Machine) : Prop :=
  R.s = s ∧ match o with
    | some t => R.pc = P.entry ∧ R.y = t
    | none => R.pc = P.ret

theorem fin_run (F : Facts E P) {M : Machine} {y v : UInt8} (hy2 : y ∈ [(0 : UInt8), 1]) (hv : v.toNat < 16) (hg : Good E M) (hpc : M.pc = P.ld)
    (hx : M.x = v) (hyv : M.y = y) (hz : M.ram.get! P.z04 = 0) (hlo : M.ram.get! (stkI (M.s + 1)) = retLo P) (hhi : M.ram.get! (stkI (M.s + 1 + 1)) = retHi P)
    (hb : bitsOf E P v ≠ 0 ∨ y = 0) :
    ∃ k, Good E (stepN k M) ∧ EndAt P (selOf P (bitsOf E P v)) (M.s + 1 + 1) (stepN k M) ∧
      (∀ i ∈ W0 P ++ [stkI (M.s + 1 + 1 + 1), stkI (M.s + 1 + 1 + 1 + 1)], (stepN k M).ram.get! i = M.ram.get! i) ∧ InFrameN E M k := by
  have A : At E { pc := P.ld, s := M.s, K := [(P.z04, 0), (stkI (M.s + 1), retLo P), (stkI (M.s + 1 + 1), retHi P)], x := some v } M := by
    refine mkAtX hg hpc ?_ (fun u hu => by cases hu; exact hx) (fun _ h => by cases h)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hz
    · exact hlo
    · exact hhi
  have hc := F.s4 y hy2 v hv M.s
  unfold s4Check at hc
  rw [s4Goal_fin hb] at hc
  obtain ⟨k, _, A1, y1, W1, C1⟩ := pieceSY_spec hc A (fun u hu => by cases hu; exact hyv)
  refine ⟨k, A1.good, ?_, ?_, C1⟩
  · cases ho : selOf P (bitsOf E P v) with
    | some t =>
      rw [ho] at A1 y1
      exact ⟨A1.s, A1.pc, y1 t rfl⟩
    | none =>
      rw [ho] at A1
      exact ⟨A1.s, A1.pc⟩
  · intro i hi
    have hi' : i ∈ (finOf P (selOf P (bitsOf E P v)) M.s).2.2 := by
      cases selOf P (bitsOf E P v) <;> exact hi
    have hl : i < 2048 := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h | h
      · exact lt_W0 F h
      all_goals (rw [h]; exact mask_stk _)
    exact W1 i hi' hl

theorem loop_run (F : Facts E P) {M : Machine} {v : UInt8} (hv : v.toNat < 16) (hg : Good E M) (hpc : M.pc = P.ld)
    (hx : M.x = v) (hyv : M.y = 1) (hz : M.ram.get! P.z04 = 0) (hlo : M.ram.get! (stkI (M.s + 1)) = retLo P) (hhi : M.ram.get! (stkI (M.s + 1 + 1)) = retHi P)
    (hb : bitsOf E P v = 0) :
    ∃ k, Good E (stepN k M) ∧ (stepN k M).pc = P.loop ∧ (stepN k M).s = M.s ∧ (stepN k M).y = 0 ∧ (stepN k M).x = 0 ∧
      (∀ i ∈ W0 P ++ [P.z04] ++ stk4 M.s, (stepN k M).ram.get! i = M.ram.get! i) ∧ InFrameN E M k := by
  have A : At E { pc := P.ld, s := M.s, K := [(P.z04, 0), (stkI (M.s + 1), retLo P), (stkI (M.s + 1 + 1), retHi P)], x := some v } M := by
    refine mkAtX hg hpc ?_ (fun u hu => by cases hu; exact hx) (fun _ h => by cases h)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hz
    · exact hlo
    · exact hhi
  have hc := F.s4 1 (by simp) v hv M.s
  unfold s4Check at hc
  rw [s4Goal_loop hb] at hc
  obtain ⟨k, _, A1, y1, W1, C1⟩ := pieceSY_spec hc A (fun u hu => by cases hu; exact hyv)
  exact ⟨k, A1.good, A1.pc, A1.s, y1 0 rfl, A1.x 0 rfl, fun i hi => W1 i hi (lt_w F hi), C1⟩

theorem xM_congr {y : UInt8} (hy2 : y ∈ [(0 : UInt8), 1]) {M R : Machine} (h : ∀ i ∈ W0 P, M.ram.get! i = R.ram.get! i) : xM E P y M = xM E P y R := by
  unfold xM highM lowM
  rw [h _ (eX_mem hy2), h _ (eP_mem hy2), h _ (by simp [W0] : P.x ∈ W0 P), h _ (by simp [W0] : P.page ∈ W0 P)]

theorem selM_eq (R : Machine) :
    selM E P R = if bitsOf E P (xM E P 1 R) != 0 then selOf P (bitsOf E P (xM E P 1 R)) else selOf P (bitsOf E P (xM E P 0 R)) := rfl

/-- **The routine of the offscreen bits and its test, on a real machine**: from its start (`ChkPOffscr`) the machine comes, with the stack of its start, to the
clamp's entry with `Y = t` when `selM R = some t`, and to the scroll handler's return instruction when `selM R = none`; the position, the two edges and the
two stack bytes above (the scroll handler's return address) are kept. -/
theorem chk_run (F : Facts E P) {R : Machine} (hg : Good E R) (hpc : R.pc = P.chk) :
    ∃ k, Good E (stepN k R) ∧ EndAt P (selM E P R) R.s (stepN k R) ∧
      (∀ i ∈ W0 P ++ [stkI (R.s + 1), stkI (R.s + 1 + 1)], (stepN k R).ram.get! i = R.ram.get! i) ∧ InFrameN E R k := by
  have A0 : At E { pc := P.chk, s := R.s, K := [] } R :=
    mkAtX (x := none) (cf := none) hg hpc (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k1, _, A1, y1, W1, C1⟩ := pieceSY_spec (F.j R.s) A0 (fun _ h => by cases h)
  generalize hM1 : stepN k1 R = M1 at A1 y1 W1
  have s1 : M1.s = R.s - 1 - 1 := A1.s
  have hz1 : M1.ram.get! P.z04 = 0 := A1.K (P.z04, 0) (by simp)
  have hhi1 : M1.ram.get! (stkI R.s) = retHi P := A1.K (stkI R.s, retHi P) (by simp)
  have hlo1 : M1.ram.get! (stkI (R.s - 1)) = retLo P := A1.K (stkI (R.s - 1), retLo P) (by simp)
  have lt1 : ∀ i ∈ W0 P ++ [stkI (R.s + 1), stkI (R.s + 1 + 1)], i < 2048 := by
    intro i hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h
    · exact lt_W0 F h
    all_goals (rw [h]; exact mask_stk _)
  have w1 : ∀ i ∈ W0 P ++ [stkI (R.s + 1), stkI (R.s + 1 + 1)], M1.ram.get! i = R.ram.get! i := fun i hi => W1 i hi (lt1 i hi)
  have w1' : ∀ i ∈ W0 P, M1.ram.get! i = R.ram.get! i := fun i hi => w1 i (by simp [hi])
  have st1 : M1.s + 1 = R.s - 1 := by rw [s1, ScrollRule.sub2_add1]
  have st2 : M1.s + 1 + 1 = R.s := by rw [s1, ScrollRule.sub2_add2]
  -- the right edge
  obtain ⟨k2, g2, pc2, s2, y2, x2, w2, C2⟩ := side_run F (y := 1) (by simp) A1.good A1.pc (A1.x _ rfl) (y1 _ rfl)
  generalize hM2 : stepN k2 M1 = M2 at g2 pc2 s2 y2 x2 w2
  have e12 : stepN (k1 + k2) R = M2 := by rw [stepN_add, hM1, hM2]
  have w2' : ∀ i ∈ W0 P, M2.ram.get! i = R.ram.get! i := fun i hi => (w2 i (by simp [hi])).trans (w1' i hi)
  have z2 : M2.ram.get! P.z04 = 0 := (w2 _ (by simp)).trans hz1
  have lo2 : M2.ram.get! (stkI (M2.s + 1)) = retLo P := by
    rw [s2, w2 _ (by simp [stk4]), st1]; exact hlo1
  have hi2 : M2.ram.get! (stkI (M2.s + 1 + 1)) = retHi P := by
    rw [s2, w2 _ (by simp [stk4]), st2]; exact hhi1
  have up2 : ∀ i ∈ [stkI (R.s + 1), stkI (R.s + 1 + 1)], M2.ram.get! i = R.ram.get! i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rw [← st2, w2 _ (by simp [stk4])]; rw [st2]; exact w1 _ (by simp)
    · rw [← st2, w2 _ (by simp [stk4])]; rw [st2]; exact w1 _ (by simp)
  have xr : xM E P 1 M1 = xM E P 1 R := xM_congr (by simp) w1'
  rw [xr] at x2
  have ss : M2.s + 1 + 1 = R.s := by rw [s2]; exact st2
  by_cases hb : bitsOf E P (xM E P 1 R) = 0
  · -- the left edge
    obtain ⟨k3, g3, pc3, s3, y3, x3, w3, C3⟩ := loop_run F (xOf_lt F (by simp) _ _) g2 pc2 x2 y2 z2 lo2 hi2 hb
    generalize hM3 : stepN k3 M2 = M3 at g3 pc3 s3 y3 x3 w3
    obtain ⟨k4, g4, pc4, s4, y4, x4, w4, C4⟩ := side_run F (y := 0) (by simp) g3 pc3 x3 y3
    generalize hM4 : stepN k4 M3 = M4 at g4 pc4 s4 y4 x4 w4
    have w3' : ∀ i ∈ W0 P, M3.ram.get! i = R.ram.get! i := fun i hi => (w3 i (by simp [hi])).trans (w2' i hi)
    have xl : xM E P 0 M3 = xM E P 0 R := xM_congr (by simp) w3'
    rw [xl] at x4
    have s34 : M4.s = M2.s := s4.trans s3
    have z4 : M4.ram.get! P.z04 = 0 := (w4 _ (by simp)).trans ((w3 _ (by simp)).trans z2)
    have lo4 : M4.ram.get! (stkI (M4.s + 1)) = retLo P := by
      rw [s34, ← s3, w4 _ (by simp [stk4]), s3, w3 _ (by simp [stk4])]; exact lo2
    have hi4 : M4.ram.get! (stkI (M4.s + 1 + 1)) = retHi P := by
      rw [s34, ← s3, w4 _ (by simp [stk4]), s3, w3 _ (by simp [stk4])]; exact hi2
    obtain ⟨k5, g5, E5, w5, C5⟩ := fin_run F (y := 0) (by simp) (xOf_lt F (by simp) _ _) g4 pc4 x4 y4 z4 lo4 hi4 (Or.inr rfl)
    have e15 : stepN (k1 + k2 + k3 + k4 + k5) R = stepN k5 M4 := by rw [stepN_add, stepN_add, stepN_add, e12, hM3, hM4]
    refine ⟨k1 + k2 + k3 + k4 + k5, by rw [e15]; exact g5, ?_, ?_,
      InFrameN.add' (InFrameN.add' (InFrameN.add' (InFrameN.add' C1 hM1 C2) e12 C3) (by rw [stepN_add, e12, hM3]) C4)
        (by rw [stepN_add, stepN_add, e12, hM3, hM4]) C5⟩
    · rw [e15, selM_eq, if_neg (by simp [hb])]
      rw [s34, ss] at E5
      exact E5
    · intro i hi
      rw [e15]
      have hW : ∀ j ∈ W0 P ++ [stkI (R.s + 1), stkI (R.s + 1 + 1)], M4.ram.get! j = R.ram.get! j := by
        intro j hj
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with h | h | h
        · exact (w4 j (by simp [h])).trans (w3' j h)
        · rw [h, ← ss, ← s3, w4 _ (by simp [stk4]), s3, w3 _ (by simp [stk4]), ss]; exact up2 _ (by simp)
        · rw [h, ← ss, ← s3, w4 _ (by simp [stk4]), s3, w3 _ (by simp [stk4]), ss]; exact up2 _ (by simp)
      have hi' : i ∈ W0 P ++ [stkI (M4.s + 1 + 1 + 1), stkI (M4.s + 1 + 1 + 1 + 1)] := by
        rw [s34, ss]; exact hi
      exact (w5 i hi').trans (hW i hi)
  · -- the right edge decides
    obtain ⟨k5, g5, E5, w5, C5⟩ := fin_run F (y := 1) (by simp) (xOf_lt F (by simp) _ _) g2 pc2 x2 y2 z2 lo2 hi2 (Or.inl hb)
    have e15 : stepN (k1 + k2 + k5) R = stepN k5 M2 := by rw [stepN_add, e12]
    refine ⟨k1 + k2 + k5, by rw [e15]; exact g5, ?_, ?_, InFrameN.add' (InFrameN.add' C1 hM1 C2) e12 C5⟩
    · rw [e15, selM_eq, if_pos (by simp [hb])]
      rw [ss] at E5
      exact E5
    · intro i hi
      rw [e15]
      have hi' : i ∈ W0 P ++ [stkI (M2.s + 1 + 1 + 1), stkI (M2.s + 1 + 1 + 1 + 1)] := by
        rw [ss]; exact hi
      refine (w5 i hi').trans ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h | h
      · exact w2' i h
      · exact up2 i (by simp [h])
      · exact up2 i (by simp [h])

/-! ## In pixels -/

/-- his pixel with its page, and the edge's (`y = 0` the left edge, `y = 1` the right edge), as numbers below 2¹⁶ -/
def pix16 (P : Places) (M : Machine) : Nat := (M.ram.get! P.page).toNat * 256 + (M.ram.get! P.x).toNat
def edge16 (P : Places) (y : UInt8) (M : Machine) : Nat := (M.ram.get! (eP P y)).toNat * 256 + (M.ram.get! (eX P y)).toNat

/-- the clamp's amount for `Y = y` -/
def amt (E : Rom) (P : Places) (y : UInt8) : Nat := (E.b (P.table + y.toUInt16)).toNat

theorem pix16_lt (P : Places) (M : Machine) : pix16 P M < 65536 := by
  unfold pix16; have := (M.ram.get! P.page).toNat_lt; have := (M.ram.get! P.x).toNat_lt; omega

theorem edge16_lt (P : Places) (y : UInt8) (M : Machine) : edge16 P y M < 65536 := by
  unfold edge16; have := (M.ram.get! (eP P y)).toNat_lt; have := (M.ram.get! (eX P y)).toNat_lt; omega

theorem compl_nat (v : UInt8) : (~~~v).toNat = 255 - v.toNat := by
  have h := ScreenClamp.complement_sum ⟨v.toNat, v.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  have := v.toNat_lt
  omega

/-- **the two bytes of a difference**: the low byte and the high byte that the code finds are those of `(256·ep + e) − (256·p + v)` modulo 2¹⁶ -/
theorem lo_hi (e v ep p : UInt8) :
    (lo e v).1.toNat = ((ep.toNat * 256 + e.toNat) + 65536 - (p.toNat * 256 + v.toNat)) % 65536 % 256 ∧
      (hi ep p (lo e v).2).toNat = ((ep.toNat * 256 + e.toNat) + 65536 - (p.toNat * 256 + v.toNat)) % 65536 / 256 := by
  unfold hi lo
  have h1 := adcC_nat e (~~~v) true
  generalize adcC e (~~~v) true = q at h1 ⊢
  have h2 := adcC_nat ep (~~~p) q.2
  generalize adcC ep (~~~p) q.2 = r at h2 ⊢
  rw [compl_nat] at h1 h2
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  have := e.toNat_lt; have := v.toNat_lt; have := ep.toNat_lt; have := p.toNat_lt; have := q1.toNat_lt; have := r1.toNat_lt
  cases q2 <;> cases r2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> constructor <;> omega

/-- the selector from the difference `d` of the right edge and his pixel, when the left edge is 255 px left of the right edge -/
def xD (E : Rom) (P : Places) (y : UInt8) (d : Nat) : UInt8 := xOf E P y (d % 256).toUInt8 (d / 256).toUInt8
def selD (E : Rom) (P : Places) (d : Nat) : Option UInt8 :=
  let bR := bitsOf E P (xD E P 1 d)
  if bR != 0 then selOf P bR else selOf P (bitsOf E P (xD E P 0 ((d + 65536 - 255) % 65536)))

/-- the check of the pixels: no clamp only when he is at most 255 px right of the left edge, and the left clamp's amount is 0 -/
def relCheck (E : Rom) (P : Places) : Bool :=
  amt E P 0 == 0 && (List.range 65536).all fun d => (selD E P d).isSome || decide (d ≤ 255)

theorem xM_eq {y : UInt8} (R : Machine) :
    xM E P y R = xD E P y ((edge16 P y R + 65536 - pix16 P R) % 65536) := by
  obtain ⟨h1, h2⟩ := lo_hi (R.ram.get! (eX P y)) (R.ram.get! P.x) (R.ram.get! (eP P y)) (R.ram.get! P.page)
  unfold xM xD highM lowM
  have e1 : (lo (R.ram.get! (eX P y)) (R.ram.get! P.x)).1 = (((edge16 P y R + 65536 - pix16 P R) % 65536) % 256).toUInt8 := by
    unfold edge16 pix16
    rw [← h1]; simp
  have e2 : (hi (R.ram.get! (eP P y)) (R.ram.get! P.page) (lo (R.ram.get! (eX P y)) (R.ram.get! P.x)).2) =
      (((edge16 P y R + 65536 - pix16 P R) % 65536) / 256).toUInt8 := by
    unfold edge16 pix16
    rw [← h2]; simp
  rw [e1, e2]

/-- with the right edge 255 px right of the left edge (modulo 2¹⁶), the selector is `selD` of the difference of the right edge and his pixel -/
theorem selM_rel (R : Machine) (hrel : edge16 P 1 R % 65536 = (edge16 P 0 R + 255) % 65536) :
    selM E P R = selD E P ((edge16 P 1 R + 65536 - pix16 P R) % 65536) := by
  rw [selM_eq, xM_eq, xM_eq]
  unfold selD
  have hl := edge16_lt P 0 R
  have hr := edge16_lt P 1 R
  have hp := pix16_lt P R
  have e : (edge16 P 0 R + 65536 - pix16 P R) % 65536 = ((edge16 P 1 R + 65536 - pix16 P R) % 65536 + 65536 - 255) % 65536 := by omega
  rw [e]

/-! ## The clamp, keeping the edges -/

/-- the two edges' bytes -/
def EW (P : Places) : List Nat := [eX P 0, eX P 1, eP P 0, eP P 1]

/-- the pieces of `ScreenClamp`, which also keep the bytes `L` -/
def cpX (E : Rom) (C : ScreenClamp.Places) (L : List Nat) (y x : UInt8) : Bool :=
  ScreenClamp.pieceY E (ScreenClamp.cX C y x) (ScreenClamp.cP E C y x) ([I (C.edgeP + y.toUInt16), C.page, C.frac] ++ L ++ stackI) y 12
def cpP (E : Rom) (C : ScreenClamp.Places) (L : List Nat) (y p : UInt8) (c : Bool) : Bool :=
  ScreenClamp.pieceY E (ScreenClamp.cPage C y p c) (ScreenClamp.cTail C p c) ([C.x, C.frac] ++ L ++ stackI) y 8
def cpT (E : Rom) (C : ScreenClamp.Places) (L : List Nat) (y : UInt8) : Bool :=
  ScreenClamp.pieceY E (ScreenClamp.cT C) (ScreenClamp.cR C) ([C.x, C.page, C.frac] ++ L ++ stackI) y 16
def clampCheck (E : Rom) (C : ScreenClamp.Places) (L : List Nat) : Bool :=
  L.all (fun i => decide (i < 2048)) &&
  [(0 : UInt8), 1].all fun y =>
    (List.range 256).all (fun x => cpX E C L y x.toUInt8) && (List.range 256).all (fun p => [false, true].all fun c => cpP E C L y p.toUInt8 c) && cpT E C L y

theorem clamp_run {C : ScreenClamp.Places} {L : List Nat} (hcc : clampCheck E C L = true) (F : ScreenClamp.Facts E C) {R : Machine} {y : UInt8}
    (hg : Good E R) (hpc : R.pc = C.entry) (hy : R.y = y) (hys : y ∈ [(0 : UInt8), 1]) :
    ∃ k, Good E (stepN k R) ∧ (stepN k R).pc = C.ret ∧ (stepN k R).s = R.s ∧ (stepN k R).ram.get! C.frac = R.ram.get! C.frac ∧
      (posOf ((stepN k R).ram.get! C.page) ((stepN k R).ram.get! C.x) ((stepN k R).ram.get! C.frac) - ScreenClamp.target E C R y) % 0x1000000 = 0 ∧
      (∀ i ∈ L ++ stackI, (stepN k R).ram.get! i = R.ram.get! i) ∧ InFrameN E R k := by
  unfold clampCheck at hcc
  obtain ⟨hL0, hcc⟩ := Bool.and_eq_true_iff.1 hcc
  have hL : ∀ i ∈ L, i < 2048 := fun i hi => by simpa using List.all_eq_true.1 hL0 i hi
  have H := List.all_eq_true.1 hcc y hys
  obtain ⟨⟨hX, hP⟩, hT⟩ := Bool.and_eq_true_iff.1 H |>.imp_left Bool.and_eq_true_iff.1
  have fX : ∀ x : UInt8, cpX E C L y x = true := fun x => by
    simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 hX x.toNat (List.mem_range.2 x.toNat_lt)
  have fP : ∀ (p : UInt8) (c : Bool), cpP E C L y p c = true := fun p c => by
    have h1 := List.all_eq_true.1 hP p.toNat (List.mem_range.2 p.toNat_lt)
    simp only [UInt8.ofNat_toNat] at h1
    exact List.all_eq_true.1 h1 c (by cases c <;> simp)
  have lt : ∀ i ∈ L ++ stackI, i < 2048 := by
    intro i hi
    rcases List.mem_append.1 hi with h | h
    · exact hL i h
    · exact stack_bound h
  let x := peek R (C.edgeX + y.toUInt16)
  let p := peek R (C.edgeP + y.toUInt16)
  let d := ScreenClamp.amount E C y
  have A0 : At E {ScreenClamp.cX C y x with s := R.s} R := by
    apply mkAt hg hpc
    · intro q hq; obtain rfl := List.mem_singleton.1 hq; rfl
    · intro u h; cases h
    · intro b h; cases h
  obtain ⟨k1, _, A1, y1, W1, C1⟩ := ScreenClamp.pieceY_spec (fX x) A0 hy
  generalize hR1 : stepN k1 R = R1 at A1 y1 W1
  have p1 : R1.ram.get! (I (C.edgeP + y.toUInt16)) = p := W1 _ (by simp) (I_lt _)
  have AP : At E {ScreenClamp.cPage C y p (adcC x (~~~d) true).2 with s := R1.s} R1 := by
    apply mkAt A1.good A1.pc
    · intro q hq; obtain rfl := List.mem_singleton.1 hq; exact p1
    · intro u h; cases h
    · exact A1.cf
  obtain ⟨k2, _, A2, y2, W2, C2⟩ := ScreenClamp.pieceY_spec (fP p _) AP y1
  generalize hR2 : stepN k2 R1 = R2 at A2 y2 W2
  have AT : At E {ScreenClamp.cT C with s := R2.s} R2 := by
    apply mkAt A2.good A2.pc <;> intro u h <;> cases h
  obtain ⟨k3, _, A3, _, W3, C3⟩ := ScreenClamp.pieceY_spec hT AT y2
  have F' := F
  have px : (stepN k3 R2).ram.get! C.x = (adcC x (~~~d) true).1 :=
    (W3 _ (by simp) F'.x_lt).trans ((W2 _ (by simp) F'.x_lt).trans (A1.K _ (.head _)))
  have pg : (stepN k3 R2).ram.get! C.page = (adcC p 0xFF (adcC x (~~~d) true).2).1 :=
    (W3 _ (by simp) F'.page_lt).trans (A2.K _ (.head _))
  have pf : (stepN k3 R2).ram.get! C.frac = R.ram.get! C.frac :=
    (W3 _ (by simp) F'.frac_lt).trans ((W2 _ (by simp) F'.frac_lt).trans (W1 _ (by simp) F'.frac_lt))
  refine ⟨k1 + (k2 + k3), ?_⟩
  have eq : stepN (k1 + (k2 + k3)) R = stepN k3 R2 := by rw [stepN_add, hR1, stepN_add, hR2]
  rw [eq]
  refine ⟨A3.good, A3.pc, A3.s.trans (A2.s.trans A1.s), pf, ?_, ?_, InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)⟩
  · rw [px, pg, pf]
    let A := posOf (adcC p 0xFF (adcC x (~~~d) true).2).1 (adcC x (~~~d) true).1 (R.ram.get! C.frac)
    let B := posOf p x (R.ram.get! C.frac)
    change (A - (B - 256 * (d.toNat : Int))) % 0x1000000 = 0
    have eq : A - (B - 256 * (d.toNat : Int)) = A - B + 256 * (d.toNat : Int) := by omega
    rw [eq]
    exact ScreenClamp.sub_pos_mod p x (R.ram.get! C.frac) d
  · intro i hi
    have hb := lt i hi
    have m3 : i ∈ [C.x, C.page, C.frac] ++ L ++ stackI := by
      rcases List.mem_append.1 hi with h | h
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ h
    have m2 : i ∈ [C.x, C.frac] ++ L ++ stackI := by
      rcases List.mem_append.1 hi with h | h
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ h
    have m1 : i ∈ [I (C.edgeP + y.toUInt16), C.page, C.frac] ++ L ++ stackI := by
      rcases List.mem_append.1 hi with h | h
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ h
    exact (W3 i m3 hb).trans ((W2 i m2 hb).trans (W1 i m1 hb))

theorem selOf_mem {b t : UInt8} (h : selOf P b = some t) : t = 0 ∨ t = 1 := by
  unfold selOf at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inr rfl
    · cases h

theorem selM_mem {R : Machine} {t : UInt8} (h : selM E P R = some t) : t = 0 ∨ t = 1 := by
  rw [selM_eq] at h
  split at h <;> exact selOf_mem h

end

/-- his pixel after the routine and the clamp, for the selector `o` -/
def pixAfter (E : Rom) (P : Places) (o : Option UInt8) (R : Machine) : Nat :=
  match o with
  | none => pix16 P R
  | some t => (edge16 P t R + 65536 - amt E P t) % 65536

theorem pixAfter_none (E : Rom) (P : Places) (R : Machine) : pixAfter E P none R = pix16 P R := rfl
theorem pixAfter_some (E : Rom) (P : Places) (t : UInt8) (R : Machine) : pixAfter E P (some t) R = (edge16 P t R + 65536 - amt E P t) % 65536 := rfl

/-- **The check on the ROM**: the pieces of the choice, the clamp's pieces that keep the edges, and the check of the pixels -/
def checkAll (sy : Syms) (m0 : Machine) : Bool :=
  check sy m0 && clampCheck (Rom.of m0) (ScreenClamp.places sy m0) (EW (places sy m0)) && relCheck (Rom.of m0) (places sy m0)

/-- **The routine of the offscreen bits, the clamp and the scroll handler's return instruction, on a real machine**: from the routine's start (`ChkPOffscr`) the
machine comes to the scroll handler's return instruction with the stack of the start, the two edges, the fraction and the two stack bytes above kept; his pixel
(with its page) is his pixel at the start when `selM R = none`, and else the edge `t` minus the clamp's amount (modulo 2¹⁶), `selM R = some t`. -/
theorem clamp_end {sy : Syms} {m0 : Machine} (hc : checkAll sy m0 = true) (hcC : ScreenClamp.check sy m0 = true) {R : Machine}
    (hg : Good (Rom.of m0) R) (hpc : R.pc = (places sy m0).chk) :
    ∃ k, Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = (places sy m0).ret ∧ (stepN k R).s = R.s ∧
      (∀ i ∈ EW (places sy m0), (stepN k R).ram.get! i = R.ram.get! i) ∧
      (stepN k R).ram.get! (places sy m0).frac = R.ram.get! (places sy m0).frac ∧
      (∀ i ∈ [stkI (R.s + 1), stkI (R.s + 1 + 1)], (stepN k R).ram.get! i = R.ram.get! i) ∧
      pix16 (places sy m0) (stepN k R) = pixAfter (Rom.of m0) (places sy m0) (selM (Rom.of m0) (places sy m0) R) R ∧
      InFrameN (Rom.of m0) R k := by
  unfold checkAll at hc
  obtain ⟨hc, _⟩ := Bool.and_eq_true_iff.1 hc
  obtain ⟨hP, hCC⟩ := Bool.and_eq_true_iff.1 hc
  have F := facts_of_check hP
  have FC := ScreenClamp.facts_of_check hcC
  have c1 : (ScreenClamp.places sy m0).entry = (places sy m0).entry := rfl
  have c2 : (ScreenClamp.places sy m0).ret = (places sy m0).ret := rfl
  have c3 : (ScreenClamp.places sy m0).x = (places sy m0).x := rfl
  have c4 : (ScreenClamp.places sy m0).page = (places sy m0).page := rfl
  have c5 : (ScreenClamp.places sy m0).frac = (places sy m0).frac := rfl
  have c6 : (ScreenClamp.places sy m0).edgeX = (places sy m0).edgeX := rfl
  have c7 : (ScreenClamp.places sy m0).edgeP = (places sy m0).edgeP := rfl
  have c8 : (ScreenClamp.places sy m0).table = (places sy m0).table := rfl
  generalize Rom.of m0 = E at F FC hCC hg ⊢
  generalize ScreenClamp.places sy m0 = C at FC hCC c1 c2 c3 c4 c5 c6 c7 c8
  generalize places sy m0 = P at F hCC hpc c1 c2 c3 c4 c5 c6 c7 c8 ⊢
  obtain ⟨k1, g1, E1, w1, C1⟩ := chk_run F hg hpc
  generalize hM : stepN k1 R = M at g1 E1 w1
  have wM : ∀ i ∈ W0 P, M.ram.get! i = R.ram.get! i := fun i hi => w1 i (by simp [hi])
  have upM : ∀ i ∈ [stkI (R.s + 1), stkI (R.s + 1 + 1)], M.ram.get! i = R.ram.get! i := fun i hi => w1 i (by simp_all)
  have ew : ∀ i ∈ EW P, i ∈ W0 P := by intro i hi; simp only [EW, W0, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega
  cases hs : selM E P R with
  | none =>
    rw [hs] at E1
    obtain ⟨s1, pc1⟩ := E1
    refine ⟨k1, by rw [hM]; exact g1, by rw [hM]; exact pc1, by rw [hM]; exact s1, fun i hi => by rw [hM]; exact wM i (ew i hi),
      by rw [hM]; exact wM _ (by simp [W0]), fun i hi => by rw [hM]; exact upM i hi, ?_, C1⟩
    rw [hM, pixAfter_none]
    unfold pix16
    rw [wM _ (by simp [W0] : P.page ∈ W0 P), wM _ (by simp [W0] : P.x ∈ W0 P)]
  | some t =>
    rw [hs] at E1
    obtain ⟨s1, pc1, y1⟩ := E1
    have ht := selM_mem hs
    have ht' : t ∈ [(0 : UInt8), 1] := by rcases ht with rfl | rfl <;> simp
    obtain ⟨k2, g2, pc2, s2, f2, m2, w2, C2⟩ := clamp_run hCC FC g1 (by rw [c1]; exact pc1) y1 ht'
    generalize hM2 : stepN k2 M = M2 at g2 pc2 s2 f2 m2 w2
    have e12 : stepN (k1 + k2) R = M2 := by rw [stepN_add, hM, hM2]
    rw [c2] at pc2
    rw [c5] at f2
    rw [c3, c4, c5] at m2
    have wE : ∀ i ∈ EW P, M2.ram.get! i = R.ram.get! i := fun i hi => (w2 i (List.mem_append_left _ hi)).trans (wM i (ew i hi))
    refine ⟨k1 + k2, by rw [e12]; exact g2, by rw [e12]; exact pc2, by rw [e12, s2, s1], fun i hi => by rw [e12]; exact wE i hi,
      by rw [e12]; exact f2.trans (wM _ (by simp [W0])), fun i hi => ?_, ?_, InFrameN.add' C1 hM C2⟩
    · rw [e12]
      have hs' : i ∈ stackI := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> exact stack_mem _
      exact (w2 i (List.mem_append_right _ hs')).trans (upM i hi)
    · rw [e12]
      rw [pixAfter_some]
      have ex : M.ram.get! (eX P t) = R.ram.get! (eX P t) := wM _ (eX_mem ht')
      have ep : M.ram.get! (eP P t) = R.ram.get! (eP P t) := wM _ (eP_mem ht')
      unfold ScreenClamp.target ScreenClamp.amount at m2
      rw [c5, c6, c7, c8, f2] at m2
      have e3 : peek M (P.edgeP + t.toUInt16) = R.ram.get! (eP P t) := ep
      have e4 : peek M (P.edgeX + t.toUInt16) = R.ram.get! (eX P t) := ex
      rw [e3, e4] at m2
      unfold posOf at m2
      unfold pix16 edge16 amt
      have := (M2.ram.get! P.page).toNat_lt; have := (M2.ram.get! P.x).toNat_lt; have := (R.ram.get! (eP P t)).toNat_lt
      have := (R.ram.get! (eX P t)).toNat_lt; have := (E.b (P.table + t.toUInt16)).toNat_lt; have := (M.ram.get! P.frac).toNat_lt
      have := (M2.ram.get! P.frac).toNat_lt
      omega

/-- the pixels of `clamp_end`'s result (with the right edge 255 px right of the left edge, modulo 2¹⁶): his pixel after the routine and the clamp is the left
edge's or at most 255 px right of it, counted modulo 2¹⁶ -/
theorem left_of {sy : Syms} {m0 : Machine} (hc : checkAll sy m0 = true) {R R' : Machine}
    (hrel : edge16 (places sy m0) 1 R % 65536 = (edge16 (places sy m0) 0 R + 255) % 65536)
    (hp : pix16 (places sy m0) R' = pixAfter (Rom.of m0) (places sy m0) (selM (Rom.of m0) (places sy m0) R) R) :
    (pix16 (places sy m0) R' + 65536 - edge16 (places sy m0) 0 R) % 65536 < 256 := by
  have hc' := hc
  unfold checkAll at hc'
  obtain ⟨_, hr⟩ := Bool.and_eq_true_iff.1 hc'
  unfold relCheck at hr
  obtain ⟨h0, hall⟩ := Bool.and_eq_true_iff.1 hr
  have a0 : amt (Rom.of m0) (places sy m0) 0 = 0 := by simpa using h0
  generalize Rom.of m0 = E at hp a0 hall
  generalize places sy m0 = P at hp a0 hall hrel ⊢
  have hl := edge16_lt P 0 R; have hr1 := edge16_lt P 1 R; have hpR := pix16_lt P R
  rw [selM_rel R hrel] at hp
  have hd : (edge16 P 1 R + 65536 - pix16 P R) % 65536 < 65536 := Nat.mod_lt _ (by omega)
  have hsel := List.all_eq_true.1 hall _ (List.mem_range.2 hd)
  cases hs : selD E P ((edge16 P 1 R + 65536 - pix16 P R) % 65536) with
  | none =>
    rw [hs] at hp hsel
    simp only [Option.isSome_none, Bool.false_or, decide_eq_true_eq] at hsel
    rw [hp, pixAfter_none]
    omega
  | some t =>
    rw [hs] at hp
    have ht : t = 0 ∨ t = 1 := by
      unfold selD at hs
      dsimp only at hs
      split at hs <;> exact selOf_mem hs
    rw [pixAfter_some] at hp
    rcases ht with rfl | rfl
    · rw [hp, a0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hl, Nat.add_sub_cancel_left]; decide
    · rw [hp]
      have := (E.b (P.table + (1 : UInt8).toUInt16)).toNat_lt
      unfold amt
      omega

/-- **The clamp keeps him on the screen** (with the right edge 255 px right of the left edge, modulo 2¹⁶): at the scroll handler's return instruction his pixel is
the left edge's or at most 255 px right of it, counted modulo 2¹⁶ -/
theorem left_after {sy : Syms} {m0 : Machine} (hc : checkAll sy m0 = true) (hcC : ScreenClamp.check sy m0 = true) {R : Machine}
    (hg : Good (Rom.of m0) R) (hpc : R.pc = (places sy m0).chk)
    (hrel : edge16 (places sy m0) 1 R % 65536 = (edge16 (places sy m0) 0 R + 255) % 65536) :
    ∃ k, Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = (places sy m0).ret ∧ (stepN k R).s = R.s ∧
      (∀ i ∈ EW (places sy m0), (stepN k R).ram.get! i = R.ram.get! i) ∧
      (stepN k R).ram.get! (places sy m0).frac = R.ram.get! (places sy m0).frac ∧
      (∀ i ∈ [stkI (R.s + 1), stkI (R.s + 1 + 1)], (stepN k R).ram.get! i = R.ram.get! i) ∧
      (pix16 (places sy m0) (stepN k R) + 65536 - edge16 (places sy m0) 0 R) % 65536 < 256 ∧ InFrameN (Rom.of m0) R k := by
  obtain ⟨k, g, pc, s, we, f, up, hp, C⟩ := clamp_end hc hcC hg hpc
  exact ⟨k, g, pc, s, we, f, up, left_of hc hrel hp, C⟩

end Smbrta.ClampSide
