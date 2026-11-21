import Theorems.ScreenClamp
import Theorems.SurfaceRead

/-!
# Above ground: the scroll's rule

The scroll handler is the first call at the end of the player's routine (`PlayerSubs`). Its first part moves the screen's left edge, before the clamp at the
screen's edge (`ScreenClamp`). Here, from its entry to the clamp's call (`ChkPOffscr`), on real machines:

* the left edge (pixel and page, the two operands of the clamp: `ScreenClamp.places`) moves by `Y` pixels, with `Y ≤ X`, where `X` is the scroll's
  amount (the byte the move stores, plus the platforms' force on the scroll), and the edge moves only when the scroll lock is 0, the byte of his place on the
  screen is at least the code's threshold, the side collision's timer is 0 and `1 ≤ X ≤ 128`;
* the position (pixel, page, fraction) and the return address are kept.

The whole call of the scroll handler, from `PlayerSubs` to the instruction after it, keeps the stack and moves the edge so too (`scroll_call`); with the edge as a
position (`SurfaceRead.edgeOf`) the edge is kept, or it is at most `256·Y` further, `Y ≤ X` (`scroll_edge`). After the scroll, the clamp and the routine of the offscreen
bits do not write the edge. This is a part of the field `edge` of `SurfaceFrames.OnFrames`, which stays: the keep of the edge before the call and after it, and
that the scroll is allowed only when he is far enough right of the edge (a relation with the frame before), are not proved.

The proof is by pieces of the ROM's code with known values (as `ScreenClamp`): the check `check` walks each piece for every value of the byte it branches on.
The addresses come from the ROM: the operands of the scroll handler's instructions, found from the call at the player's routine's end. No game data.
Page: `1-1/e-2-10-3-12-ScrollRule.md`.
-/

namespace Smbrta.ScrollRule
open FrameModel ImpedePosition

/-- the places of the scroll's part of the scroll handler: the program counters of its cuts and the RAM indices of the bytes it reads -/
structure Places where
  entry : UInt16
  lock : UInt16
  pfs1 : UInt16
  side : UInt16
  ldy : UInt16
  near : UInt16
  ldy2 : UInt16
  scr : UInt16
  pg : UInt16
  init : UInt16
  chk : UInt16
  /-- the call of the scroll handler (the end of the player's routine) and the scroll handler's return -/
  subs : UInt16
  ret : UInt16
  /-- the immediates of the scroll handler's two tests of his place on the screen and of its test of the amount -/
  thr1 : UInt8
  thr2 : UInt8
  two : UInt8
  xs : Nat
  plat : Nat
  lockB : Nat
  pfs : Nat
  sideB : Nat
  lx : Nat
  lp : Nat
  x : Nat
  page : Nat
  frac : Nat
  deriving Inhabited

/-- the target of a relative branch at `a` -/
def brT (E : Rom) (a : UInt16) : UInt16 :=
  let r := E.b (a + 1)
  if r < 0x80 then a + 2 + r.toUInt16 else a + 2 + r.toUInt16 - 256

/-- the places, read from the program: the scroll handler is the target of the call at the player's routine's end; its loads (`LDA`, `LDY` absolute) in order -/
def places (sy : Syms) (m0 : Machine) : Places :=
  let E := Rom.of m0
  let entry := E.w (sy.PlayerSubs + 1)
  let lock := PipeEntryRule.findOp m0 (entry + 3) 0xAD 16
  let pfs1 := lock + 5
  let side := PipeEntryRule.findOp m0 (pfs1 + 3) 0xAD 16
  let ldy := PipeEntryRule.findOp m0 (side + 3) 0xAC 8
  let near := PipeEntryRule.findOp m0 (ldy + 3) 0xAD 16
  let ldy2 := PipeEntryRule.findOp m0 (near + 3) 0xAC 8
  let scr := ldy2 + 3
  let pg := PipeEntryRule.findOp m0 (scr + 1) 0xAD 32
  let C := ScreenClamp.places sy m0
  { entry, lock, pfs1, side, ldy, near, ldy2, scr, pg,
    init := brT E (lock + 3), chk := E.w (PipeEntryRule.findOp m0 pg 0x4C 48 + 1), subs := sy.PlayerSubs, ret := C.ret,
    thr1 := E.b (pfs1 + 4), thr2 := E.b (near + 4), two := E.b (ldy + 8),
    xs := I (E.w (entry + 1)), plat := I (E.w (entry + 5)), lockB := I (E.w (lock + 1)), pfs := I (E.w (pfs1 + 1)), sideB := I (E.w (side + 1)),
    lx := I C.edgeX, lp := I C.edgeP, x := I sy.Player_X_Position, page := I sy.Player_PageLoc, frac := I sy.SprObject_X_MoveForce }

/-- the bytes kept by every piece: the position -/
def posW (P : Places) : List Nat := [P.x, P.page, P.frac]

/-- the two bytes above the stack: the return address of the scroll handler's call -/
def stk2 (s : UInt8) : List Nat := [stkI (s + 1), stkI (s + 1 + 1)]

/-- the return address of the scroll handler's call, as the call pushes it: the low byte and the high byte of the call's last byte -/
def retLo (P : Places) : UInt8 := (P.subs + 2).toUInt8
def retHi (P : Places) : UInt8 := ((P.subs + 2) >>> 8).toUInt8

/-- the scroll's amount is allowed by `x` (`1 ≤ x ≤ 128`): the decrement is not negative -/
def xOK (x : UInt8) : Bool := (x - 1) < 0x80

/-! ## The pieces -/

/-- a piece that starts with Y unknown and ends with Y known -/
def goal0Y (c : Cut) (watch : List Nat) (y : UInt8) (Q : TS) : Bool := goal0 c watch Q && Q.y.same == some y
def piece0Y (E : Rom) (c c' : Cut) (watch : List Nat) (y : UInt8) (fuel : Nat) : Bool :=
  walkT E (fun Q => Q.pc == c'.pc) (goal0Y c' watch y) fuel (start0 c)

/-- the cuts -/
def cA (P : Places) (a b : UInt8) : Cut := { pc := P.entry, s := 0, K := [(P.xs, a), (P.plat, b)] }
def cB (P : Places) (a : UInt8) : Cut := { pc := P.lock, s := 0, K := [(P.xs, a)] }
def cLock (P : Places) (v : UInt8) : Cut := { pc := P.lock, s := 0, K := [(P.lockB, v)] }
def cPfs (P : Places) (w : UInt8) : Cut := { pc := P.pfs1, s := 0, K := [(P.pfs, w)] }
def cSide (P : Places) (t : UInt8) : Cut := { pc := P.side, s := 0, K := [(P.sideB, t)] }
def cLdy (P : Places) (x : UInt8) : Cut := { pc := P.ldy, s := 0, K := [(P.xs, x)] }
def cNear (P : Places) (w : UInt8) : Cut := { pc := P.near, s := 0, K := [(P.pfs, w)] }
def cLdy2 (P : Places) (x : UInt8) : Cut := { pc := P.ldy2, s := 0, K := [(P.xs, x)] }
def cScr (P : Places) (u : UInt8) : Cut := { pc := P.scr, s := 0, K := [(P.lx, u)] }
def cPg (P : Places) (s p : UInt8) (c : Bool) : Cut := { pc := P.pg, s, K := [(P.lp, p)], cf := some c }
def cAt (pc : UInt16) : Cut := { pc, s := 0, K := [] }
def cAtS (pc : UInt16) (s : UInt8) : Cut := { pc, s, K := [] }

/-- the piece from the entry to the load of the scroll lock: the amount is stored -/
def amountCheck (E : Rom) (P : Places) (a b : UInt8) : Bool :=
  piece0 E (cA P a b) (cB P (a + b)) ([P.lx, P.lp, P.lockB, P.pfs, P.sideB] ++ posW P ++ stackI) 12
/-- the scroll lock -/
def lockCheck (E : Rom) (P : Places) (v : UInt8) : Bool :=
  piece0 E (cLock P v) (cAt (if v == 0 then P.pfs1 else P.init)) ([P.lx, P.lp, P.xs, P.pfs, P.sideB] ++ posW P ++ stackI) 8
/-- his place on the screen, at least the first threshold -/
def pfsCheck (E : Rom) (P : Places) (w : UInt8) : Bool :=
  piece0 E (cPfs P w) (cAt (if w < P.thr1 then P.init else P.side)) ([P.lx, P.lp, P.xs, P.pfs, P.sideB] ++ posW P ++ stackI) 8
/-- the side collision's timer -/
def sideCheck (E : Rom) (P : Places) (t : UInt8) : Bool :=
  piece0 E (cSide P t) (cAt (if t == 0 then P.ldy else P.init)) ([P.lx, P.lp, P.xs, P.pfs] ++ posW P ++ stackI) 8
/-- the amount: not allowed, or `Y` is the amount or 1 below it -/
def ldyCheck (E : Rom) (P : Places) (x : UInt8) : Bool :=
  if xOK x then piece0Y E (cLdy P x) (cAt P.near) ([P.lx, P.lp, P.xs, P.pfs] ++ posW P ++ stackI) (if x < P.two then x else x - 1) 12
  else piece0 E (cLdy P x) (cAt P.init) ([P.lx, P.lp] ++ posW P ++ stackI) 12
/-- his place on the screen, at least the second threshold: `Y` is the amount again -/
def nearCheck (E : Rom) (P : Places) (y w : UInt8) : Bool :=
  ScreenClamp.pieceY E (cNear P w) (cAt (if w < P.thr2 then P.scr else P.ldy2)) ([P.lx, P.lp, P.xs] ++ posW P ++ stackI) y 8
def ldy2Check (E : Rom) (P : Places) (x : UInt8) : Bool :=
  piece0Y E (cLdy2 P x) (cAt P.scr) ([P.lx, P.lp] ++ posW P ++ stackI) x 8
/-- the scroll: the left edge's pixel moves by `Y`, with the carry -/
def scrCheck (E : Rom) (P : Places) (y u : UInt8) : Bool :=
  ScreenClamp.pieceY E (cScr P u) { pc := P.pg, s := 0, K := [(P.lx, (adcC u y false).1)], cf := some (adcC u y false).2 } ([P.lp] ++ posW P ++ stackI) y 16
/-- the page with the carry, and the screen's right edge (a call) up to the clamp's call -/
def pgCheck (E : Rom) (P : Places) (s p : UInt8) (c : Bool) : Bool :=
  pieceOK E (cPg P s p c) { pc := P.chk, s, K := [(P.lp, (adcC p 0 c).1)] } ([P.lx] ++ posW P ++ stk2 s) 40
/-- the call of the scroll handler at the end of the player's routine: the return address on the stack -/
def jsrCheck (E : Rom) (P : Places) (s : UInt8) : Bool :=
  pieceOK E (cAtS P.subs s) { pc := P.entry, s := s - 1 - 1, K := [(stkI s, retHi P), (stkI (s - 1), retLo P)] }
    ([P.lx, P.lp, P.xs, P.plat, P.lockB, P.pfs, P.sideB] ++ posW P) 2
/-- from the clamp's call to the scroll handler's return, with the return address: the left edge is kept (the clamp, the offscreen bits) -/
def tailCheck (E : Rom) (P : Places) (s : UInt8) : Bool :=
  pieceOK E { pc := P.chk, s, K := [(stkI (s + 1), retLo P), (stkI (s + 1 + 1), retHi P)] } (cAtS (P.subs + 3) (s + 1 + 1)) [P.lx, P.lp] 400
/-- no scroll -/
def initCheck (E : Rom) (P : Places) : Bool :=
  piece0 E (cAt P.init) (cAt P.chk) ([P.lx, P.lp] ++ posW P ++ stackI) 8

def checkParts (E : Rom) (P : Places) : Bool :=
  [P.xs, P.plat, P.lockB, P.pfs, P.sideB, P.lx, P.lp, P.x, P.page, P.frac].all (fun i => decide (i < 2048)) &&
  (List.range 256).all (fun a => (List.range 256).all fun b => amountCheck E P a.toUInt8 b.toUInt8) &&
  (List.range 256).all (fun v => lockCheck E P v.toUInt8) &&
  (List.range 256).all (fun w => pfsCheck E P w.toUInt8) &&
  (List.range 256).all (fun t => sideCheck E P t.toUInt8) &&
  (List.range 256).all (fun x => ldyCheck E P x.toUInt8) &&
  (List.range 256).all (fun y => (List.range 256).all fun w => nearCheck E P y.toUInt8 w.toUInt8) &&
  (List.range 256).all (fun x => ldy2Check E P x.toUInt8) &&
  (List.range 256).all (fun y => (List.range 256).all fun u => scrCheck E P y.toUInt8 u.toUInt8) &&
  (List.range 256).all (fun s => (List.range 256).all fun p => [false, true].all fun c => pgCheck E P s.toUInt8 p.toUInt8 c) &&
  initCheck E P &&
  (List.range 256).all (fun s => jsrCheck E P s.toUInt8) && (List.range 256).all (fun s => tailCheck E P s.toUInt8)

/-- **The check on the ROM** -/
def check (sy : Syms) (m0 : Machine) : Bool := checkParts (Rom.of m0) (places sy m0)

/-! ## What the check says -/

structure Facts (E : Rom) (P : Places) : Prop where
  lt : ∀ i ∈ [P.xs, P.plat, P.lockB, P.pfs, P.sideB, P.lx, P.lp, P.x, P.page, P.frac], i < 2048
  amount : ∀ a b, amountCheck E P a b = true
  lock : ∀ v, lockCheck E P v = true
  pfs : ∀ w, pfsCheck E P w = true
  side : ∀ t, sideCheck E P t = true
  ldy : ∀ x, ldyCheck E P x = true
  near : ∀ y w, nearCheck E P y w = true
  ldy2 : ∀ x, ldy2Check E P x = true
  scr : ∀ y u, scrCheck E P y u = true
  pg : ∀ s p c, pgCheck E P s p c = true
  init : initCheck E P = true
  jsr : ∀ s, jsrCheck E P s = true
  tail : ∀ s, tailCheck E P s = true

theorem all256 {f : UInt8 → Bool} (h : (List.range 256).all (fun n => f n.toUInt8) = true) (x : UInt8) : f x = true := by
  simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 h x.toNat (List.mem_range.2 x.toNat_lt)

theorem facts_of_check {E : Rom} {P : Places} (h : checkParts E P = true) : Facts E P := by
  simp only [checkParts, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hA⟩, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩, hH⟩, hI⟩, hJ⟩, hK⟩, hL⟩ := h
  refine ⟨fun i hi => by simpa using List.all_eq_true.1 h0 i hi, fun a b => ?_, all256 hB, all256 hC, all256 hD, all256 hE, fun y w => ?_, all256 hG,
    fun y u => ?_, fun s p c => ?_, hJ, all256 hK, all256 hL⟩
  · exact all256 (f := fun b => amountCheck E P a b) (all256 (f := fun a => (List.range 256).all fun b => amountCheck E P a b.toUInt8) hA a) b
  · exact all256 (f := fun w => nearCheck E P y w) (all256 (f := fun y => (List.range 256).all fun w => nearCheck E P y w.toUInt8) hF y) w
  · exact all256 (f := fun u => scrCheck E P y u) (all256 (f := fun y => (List.range 256).all fun u => scrCheck E P y u.toUInt8) hH y) u
  · have h1 := all256 (f := fun p => [false, true].all fun c => pgCheck E P s p c)
      (all256 (f := fun s => (List.range 256).all fun p => [false, true].all fun c => pgCheck E P s p.toUInt8 c) hI s) p
    exact List.all_eq_true.1 h1 c (by cases c <;> simp)

/-- a piece that starts with Y unknown and ends with Y known -/
theorem piece0Y_spec {E : Rom} {c c' : Cut} {watch : List Nat} {y : UInt8} {fuel : Nat} {m : Machine}
    (hc : piece0Y E c c' watch y fuel = true) (h : At E {c with s := m.s} m) :
    ∃ k, k ≤ fuel ∧ At E {c' with s := m.s} (stepN k m) ∧ (stepN k m).y = y ∧
      (∀ i ∈ watch, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∧ InFrameN E m k := by
  obtain ⟨k,Q,hk,_,hg,H1,hh⟩ := walkT_spec fuel (start0 c) m m hc (lk_start0 h)
  have hg0 : goal0 c' watch Q = true ∧ Q.y.same = some y := by simpa only [goal0Y,Bool.and_eq_true,beq_iff_eq] using hg
  have hg1 : Q.s.isNone = true ∧ goalC {c' with s := 0} watch {Q with s := some 0} = true := by
    simpa only [goal0,Bool.and_eq_true] using hg0.1
  have hn := Option.isNone_iff_eq_none.1 hg1.1
  have hs := H1.s0 hn
  have H2 : Lk E m m {Q with s := some m.s} (stepN k m) (stepN k m) := by
    refine ⟨H1.gl,H1.gr,H1.pcl,H1.pcr,⟨H1.regs.a,H1.regs.x,H1.regs.y,H1.regs.c,H1.regs.z,H1.regs.nf⟩,?_,?_,H1.ram,H1.fixl,H1.fixr⟩
    · intro v hv; have e := Option.some.inj hv; simpa only [← e] using hs
    · intro hv; cases hv
  have hg2 : goalC {c' with s := m.s} watch {Q with s := some m.s} = true := by
    simpa only [goalC,beq_self_eq_true] using hg1.2
  obtain ⟨ha,hw,_⟩ := at_of_goal hg2 H2
  exact ⟨k,hk,ha,(Tag.same_spec hg0.2 H1.regs.y).1,hw,
    fun j hj => by obtain ⟨_,_,_,_,hi,_⟩ := hh j hj; exact hi⟩

/-! ## Segments of the run -/

/-- from `R` to `R'` in some steps in the frame, with the stack kept and the bytes `W` kept -/
def Seg (E : Rom) (W : List Nat) (R R' : Machine) : Prop :=
  ∃ k, stepN k R = R' ∧ InFrameN E R k ∧ R'.s = R.s ∧ ∀ i ∈ W, i < 2048 → R'.ram.get! i = R.ram.get! i

theorem Seg.trans {E : Rom} {W W1 W2 : List Nat} {R R1 R2 : Machine} (h1 : Seg E W1 R R1) (h2 : Seg E W2 R1 R2)
    (h : ∀ i ∈ W, i ∈ W1 ∧ i ∈ W2) : Seg E W R R2 := by
  obtain ⟨k1, e1, f1, s1, w1⟩ := h1
  obtain ⟨k2, e2, f2, s2, w2⟩ := h2
  refine ⟨k1 + k2, by rw [stepN_add, e1, e2], InFrameN.add' f1 e1 f2, s2.trans s1, fun i hi hl => ?_⟩
  exact (w2 i (h i hi).2 hl).trans (w1 i (h i hi).1 hl)

theorem seg_of {E : Rom} {W : List Nat} {R : Machine} {k : Nat} (hs : (stepN k R).s = R.s)
    (hw : ∀ i ∈ W, i < 2048 → (stepN k R).ram.get! i = R.ram.get! i) (hf : InFrameN E R k) : Seg E W R (stepN k R) :=
  ⟨k, rfl, hf, hs, hw⟩

/-- the left edge in pixels, with the page, modulo 2¹⁶ -/
def left16 (P : Places) (m : Machine) : Nat := (m.ram.get! P.lp).toNat * 256 + (m.ram.get! P.lx).toNat

/-- the scroll's amount `X`: the byte the move stores plus the platforms' force -/
def amountOf (P : Places) (m : Machine) : UInt8 := m.ram.get! P.xs + m.ram.get! P.plat

/-- **What allows the scroll**: the scroll lock is 0, his place on the screen is at least the threshold of the code (`thr1`), the side collision's timer is 0, and
`1 ≤ X ≤ 128` (the decrement of `X` is not negative) -/
def Allows (P : Places) (m : Machine) : Prop :=
  m.ram.get! P.lockB = 0 ∧ P.thr1 ≤ m.ram.get! P.pfs ∧ m.ram.get! P.sideB = 0 ∧ xOK (amountOf P m) = true

theorem xOK_range (x : UInt8) (h : xOK x = true) : 1 ≤ x.toNat ∧ x.toNat ≤ 128 := by
  have key : ∀ n : Fin 256, xOK n.val.toUInt8 = true → 1 ≤ n.val.toUInt8.toNat ∧ n.val.toUInt8.toNat ≤ 128 := by decide +kernel
  have k := key ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at k
  exact k h

theorem dec_toNat (x : UInt8) (h : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  have key : ∀ n : Fin 256, 1 ≤ n.val.toUInt8.toNat → (n.val.toUInt8 - 1).toNat = n.val.toUInt8.toNat - 1 := by decide +kernel
  have k := key ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at k
  exact k h

theorem le_of_not_lt' {x t : UInt8} (h : ¬ x < t) : t ≤ x := by
  rcases Nat.lt_or_ge x.toNat t.toNat with h1 | h1
  · exact absurd (UInt8.lt_iff_toNat_lt.2 h1) h
  · exact UInt8.le_iff_toNat_le.2 h1

/-- the end of a scroll: the edge's pixel with the carry into the page -/
theorem left_add (u y p : UInt8) :
    ((adcC p 0 (adcC u y false).2).1.toNat * 256 + (adcC u y false).1.toNat) = (p.toNat * 256 + u.toNat + y.toNat) % 65536 := by
  have h1 := adcC_nat u y false
  have h2 := adcC_nat p 0 (adcC u y false).2
  have hu := u.toNat_lt
  have hy := y.toNat_lt
  have hp := p.toNat_lt
  generalize adcC u y false = q at h1 h2 ⊢
  obtain ⟨qx, qc⟩ := q
  generalize adcC p 0 qc = r at h2 ⊢
  obtain ⟨rp, rc⟩ := r
  have hq := qx.toNat_lt
  have hr := rp.toNat_lt
  have h0 : (0 : UInt8).toNat = 0 := rfl
  rw [h0] at h2
  cases qc <;> cases rc <;> simp only [if_true, if_false, Bool.false_eq_true] at h1 h2 ⊢ <;> omega

section
variable {E : Rom} {P : Places}

/-- the end of the scroll's part: at the clamp's call, the stack and the position kept, and the left edge kept or moved by `Y` with the scroll allowed -/
def Ends (E : Rom) (P : Places) (R R' : Machine) : Prop :=
  Good E R' ∧ R'.pc = P.chk ∧ R'.s = R.s ∧ (∀ i ∈ posW P, R'.ram.get! i = R.ram.get! i) ∧ (∀ i ∈ stk2 R.s, R'.ram.get! i = R.ram.get! i) ∧
    (left16 P R' = left16 P R ∨
      (Allows P R ∧ ∃ Y : UInt8, Y.toNat ≤ (amountOf P R).toNat ∧ left16 P R' = (left16 P R + Y.toNat) % 65536))

theorem lt_lx (F : Facts E P) : P.lx < 2048 := F.lt _ (by simp)
theorem lt_lp (F : Facts E P) : P.lp < 2048 := F.lt _ (by simp)
theorem lt_xs (F : Facts E P) : P.xs < 2048 := F.lt _ (by simp)
theorem lt_pfs (F : Facts E P) : P.pfs < 2048 := F.lt _ (by simp)
theorem lt_side (F : Facts E P) : P.sideB < 2048 := F.lt _ (by simp)
theorem lt_lock (F : Facts E P) : P.lockB < 2048 := F.lt _ (by simp)
theorem lt_pos (F : Facts E P) {i : Nat} (h : i ∈ posW P) : i < 2048 := by
  simp only [posW, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> exact F.lt _ (by simp)

/-- the bytes that the pieces before the scroll keep: the left edge, the position, the return address -/
def kw (P : Places) (s : UInt8) : List Nat := [P.lx, P.lp] ++ posW P ++ stk2 s

theorem stk_in {s : UInt8} {L : List Nat} : ∀ j ∈ stk2 s, j ∈ L ++ stackI := by
  intro j hj
  simp only [stk2, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> exact List.mem_append_right _ (stack_mem _)

theorem stk_lt {s : UInt8} {j : Nat} (hj : j ∈ stk2 s) : j < 2048 := by
  simp only [stk2, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> exact mask_stk _

theorem mem_w {i : Nat} {L : List Nat} {s : UInt8} (h : i ∈ kw P s) (hx : P.lx ∈ L) (hp : P.lp ∈ L) (hq : ∀ j ∈ posW P, j ∈ L)
    (hs : ∀ j ∈ stk2 s, j ∈ L) : i ∈ L := by
  rcases List.mem_append.1 h with h0 | h0
  · rcases List.mem_append.1 h0 with h1 | h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl
      · exact hx
      · exact hp
    · exact hq i h1
  · exact hs i h0

theorem pos_in {L L' : List Nat} : ∀ j ∈ posW P, j ∈ L ++ posW P ++ L' :=
  fun _ hj => List.mem_append_left _ (List.mem_append_right _ hj)

theorem pos_in2 {L : List Nat} : ∀ j ∈ posW P, j ∈ L ++ posW P :=
  fun _ hj => List.mem_append_right _ hj

theorem left_keep (F : Facts E P) {R R' : Machine} {W : List Nat} (h : Seg E W R R') (hx : P.lx ∈ W) (hp : P.lp ∈ W) : left16 P R' = left16 P R := by
  obtain ⟨_, _, _, _, w⟩ := h
  unfold left16
  rw [w _ hx (lt_lx F), w _ hp (lt_lp F)]

theorem finish (F : Facts E P) {R R' : Machine} {W : List Nat} (h : Seg E W R R') (hW : ∀ i ∈ posW P, i ∈ W) (hS : ∀ i ∈ stk2 R.s, i ∈ W) (hg : Good E R') (hpc : R'.pc = P.chk)
    (hl : left16 P R' = left16 P R ∨
      (Allows P R ∧ ∃ Y : UInt8, Y.toNat ≤ (amountOf P R).toNat ∧ left16 P R' = (left16 P R + Y.toNat) % 65536)) :
    ∃ k, Ends E P R (stepN k R) ∧ InFrameN E R k := by
  obtain ⟨k, e, f, s, w⟩ := h
  subst e
  exact ⟨k, ⟨hg, hpc, s, fun i hi => w i (hW i hi) (lt_pos F hi), fun i hi => w i (hS i hi) (stk_lt hi), hl⟩, f⟩

/-- the way out without a scroll: from the start of `InitScrlAmt` to the clamp's call -/
theorem exit_init (F : Facts E P) {R Ri : Machine} (h : Seg E (kw P R.s) R Ri) (hg : Good E Ri) (hpc : Ri.pc = P.init) :
    ∃ k, Ends E P R (stepN k R) ∧ InFrameN E R k := by
  have A : At E {cAt P.init with s := Ri.s} Ri := mkAt hg hpc (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k, _, A1, W1, C1⟩ := piece0_spec F.init A
  have S : Seg E (kw P R.s) R (stepN k Ri) :=
    h.trans (seg_of A1.s W1 C1) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  exact finish F S (fun i hi => List.mem_append_left _ (List.mem_append_right _ hi)) (fun i hi => List.mem_append_right _ hi) A1.good A1.pc
    (Or.inl (left_keep F S (by simp [kw]) (by simp [kw])))

theorem kat {R : Machine} {i : Nat} {v : UInt8} (h : R.ram.get! i = v) : ∀ q ∈ [(i, v)], R.ram.get! q.1 = q.2 := by
  intro q hq
  rw [List.mem_singleton.1 hq]
  exact h

/-- **The scroll's rule**, on real machines: from the scroll handler's entry to the clamp's call, the stack and the position are kept, and the left edge is kept or
moves by `Y`, with `Y ≤ X` (the scroll's amount `amountOf`), and only when the scroll is allowed (`Allows`). `hc` is the check on the ROM. -/
theorem scroll_of_facts (F : Facts E P) {R : Machine} (hg : Good E R) (hpc : R.pc = P.entry) :
    ∃ k, Ends E P R (stepN k R) ∧ InFrameN E R k := by
  -- the amount
  have A0 : At E {cA P (R.ram.get! P.xs) (R.ram.get! P.plat) with s := R.s} R := by
    refine mkAt hg hpc ?_ (fun _ h => by cases h) (fun _ h => by cases h)
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · rfl
    · rw [List.mem_singleton.1 hq]
  obtain ⟨k1, _, A1, W1, C1⟩ := piece0_spec (F.amount _ _) A0
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have S1 : Seg E (kw P R.s) R R1 :=
    ⟨k1, hR1, C1, A1.s, fun i hi hl => W1 i (mem_w hi (by simp) (by simp) pos_in stk_in) hl⟩
  have x1 : R1.ram.get! P.xs = amountOf P R := A1.K _ (List.mem_singleton.2 rfl)
  have lk1 : R1.ram.get! P.lockB = R.ram.get! P.lockB := W1 _ (by simp) (lt_lock F)
  have pf1 : R1.ram.get! P.pfs = R.ram.get! P.pfs := W1 _ (by simp) (lt_pfs F)
  have sd1 : R1.ram.get! P.sideB = R.ram.get! P.sideB := W1 _ (by simp) (lt_side F)
  -- the scroll lock
  have B0 : At E {cLock P (R1.ram.get! P.lockB) with s := R1.s} R1 :=
    mkAt A1.good A1.pc (kat rfl) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k2, _, A2, W2, C2⟩ := piece0_spec (F.lock _) B0
  generalize hR2 : stepN k2 R1 = R2 at A2 W2
  have S2 : Seg E (kw P R.s) R R2 :=
    S1.trans ⟨k2, hR2, C2, A2.s, W2⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  by_cases hv : R.ram.get! P.lockB = 0
  case neg =>
    have hpc2 : R2.pc = P.init := by
      have e := A2.pc
      rw [lk1] at e
      simpa [cAt, hv] using e
    exact exit_init F S2 A2.good hpc2
  have hpc2 : R2.pc = P.pfs1 := by
    have e := A2.pc
    rw [lk1] at e
    simpa [cAt, hv] using e
  have x2 : R2.ram.get! P.xs = amountOf P R := (W2 _ (by simp) (lt_xs F)).trans x1
  have pf2 : R2.ram.get! P.pfs = R.ram.get! P.pfs := (W2 _ (by simp) (lt_pfs F)).trans pf1
  have sd2 : R2.ram.get! P.sideB = R.ram.get! P.sideB := (W2 _ (by simp) (lt_side F)).trans sd1
  -- his place on the screen
  have C0 : At E {cPfs P (R2.ram.get! P.pfs) with s := R2.s} R2 :=
    mkAt A2.good hpc2 (kat rfl) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k3, _, A3, W3, C3⟩ := piece0_spec (F.pfs _) C0
  generalize hR3 : stepN k3 R2 = R3 at A3 W3
  have S3 : Seg E (kw P R.s) R R3 :=
    S2.trans ⟨k3, hR3, C3, A3.s, W3⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  by_cases hw : R.ram.get! P.pfs < P.thr1
  · have hpc3 : R3.pc = P.init := by
      have e := A3.pc
      rw [pf2] at e
      simpa [cAt, hw] using e
    exact exit_init F S3 A3.good hpc3
  have hpc3 : R3.pc = P.side := by
    have e := A3.pc
    rw [pf2] at e
    simpa [cAt, hw] using e
  have x3 : R3.ram.get! P.xs = amountOf P R := (W3 _ (by simp) (lt_xs F)).trans x2
  have pf3 : R3.ram.get! P.pfs = R.ram.get! P.pfs := (W3 _ (by simp) (lt_pfs F)).trans pf2
  have sd3 : R3.ram.get! P.sideB = R.ram.get! P.sideB := (W3 _ (by simp) (lt_side F)).trans sd2
  -- the side collision's timer
  have D0 : At E {cSide P (R3.ram.get! P.sideB) with s := R3.s} R3 :=
    mkAt A3.good hpc3 (kat rfl) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k4, _, A4, W4, C4⟩ := piece0_spec (F.side _) D0
  generalize hR4 : stepN k4 R3 = R4 at A4 W4
  have S4 : Seg E (kw P R.s) R R4 :=
    S3.trans ⟨k4, hR4, C4, A4.s, W4⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  by_cases ht : R.ram.get! P.sideB = 0
  case neg =>
    have hpc4 : R4.pc = P.init := by
      have e := A4.pc
      rw [sd3] at e
      simpa [cAt, ht] using e
    exact exit_init F S4 A4.good hpc4
  have hpc4 : R4.pc = P.ldy := by
    have e := A4.pc
    rw [sd3] at e
    simpa [cAt, ht] using e
  have x4 : R4.ram.get! P.xs = amountOf P R := (W4 _ (by simp) (lt_xs F)).trans x3
  have pf4 : R4.ram.get! P.pfs = R.ram.get! P.pfs := (W4 _ (by simp) (lt_pfs F)).trans pf3
  -- the amount, decremented
  have E0 : At E {cLdy P (amountOf P R) with s := R4.s} R4 :=
    mkAt A4.good hpc4 (kat x4) (fun _ h => by cases h) (fun _ h => by cases h)
  have hE := F.ldy (amountOf P R)
  unfold ldyCheck at hE
  by_cases hx : xOK (amountOf P R) = true
  case neg =>
    rw [if_neg hx] at hE
    obtain ⟨k5, _, A5, W5, C5⟩ := piece0_spec hE E0
    have S5 : Seg E (kw P R.s) R (stepN k5 R4) :=
      S4.trans (seg_of A5.s W5 C5) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
    exact exit_init F S5 A5.good A5.pc
  rw [if_pos hx] at hE
  obtain ⟨k5, _, A5, y5, W5, C5⟩ := piece0Y_spec hE E0
  generalize hR5 : stepN k5 R4 = R5 at A5 y5 W5
  have S5 : Seg E (kw P R.s) R R5 :=
    S4.trans ⟨k5, hR5, C5, A5.s, W5⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  have x5 : R5.ram.get! P.xs = amountOf P R := (W5 _ (by simp) (lt_xs F)).trans x4
  have pf5 : R5.ram.get! P.pfs = R.ram.get! P.pfs := (W5 _ (by simp) (lt_pfs F)).trans pf4
  have hX := xOK_range _ hx
  -- the scroll's amount Y at the scroll, and its bounds
  have hYS : ∃ Rs : Machine, Seg E (kw P R.s) R Rs ∧ Good E Rs ∧ Rs.pc = P.scr ∧ Rs.y.toNat ≤ (amountOf P R).toNat := by
    have N0 : At E {cNear P (R.ram.get! P.pfs) with s := R5.s} R5 :=
      mkAt A5.good A5.pc (kat pf5) (fun _ h => by cases h) (fun _ h => by cases h)
    obtain ⟨k6, _, A6, y6, W6, C6⟩ := ScreenClamp.pieceY_spec (F.near _ _) N0 y5
    have S6 : Seg E (kw P R.s) R (stepN k6 R5) :=
      S5.trans (seg_of A6.s W6 C6) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
    have hy1 : (if amountOf P R < P.two then amountOf P R else amountOf P R - 1).toNat ≤ (amountOf P R).toNat := by
      by_cases h2 : amountOf P R < P.two
      · rw [if_pos h2]; exact Nat.le_refl _
      · rw [if_neg h2, dec_toNat _ hX.1]; omega
    by_cases hn : R.ram.get! P.pfs < P.thr2
    · have hpc6 : (stepN k6 R5).pc = P.scr := by
        have e := A6.pc
        simpa [cAt, hn] using e
      refine ⟨stepN k6 R5, S6, A6.good, hpc6, ?_⟩
      rw [y6]
      exact hy1
    · have hpc6 : (stepN k6 R5).pc = P.ldy2 := by
        have e := A6.pc
        simpa [cAt, hn] using e
      have x6 : (stepN k6 R5).ram.get! P.xs = amountOf P R := (W6 _ (by simp) (lt_xs F)).trans x5
      have G0 : At E {cLdy2 P (amountOf P R) with s := (stepN k6 R5).s} (stepN k6 R5) :=
        mkAt A6.good hpc6 (kat x6) (fun _ h => by cases h) (fun _ h => by cases h)
      obtain ⟨k7, _, A7, y7, W7, C7⟩ := piece0Y_spec (F.ldy2 _) G0
      refine ⟨stepN k7 (stepN k6 R5), S6.trans (seg_of A7.s W7 C7) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩), A7.good, A7.pc, ?_⟩
      rw [y7]
      omega
  obtain ⟨Rs, Ss, gs, pcs, ys2⟩ := hYS
  -- the scroll
  have lxs : Rs.ram.get! P.lx = R.ram.get! P.lx := by
    obtain ⟨_, _, _, _, w⟩ := Ss
    exact w _ (by simp [kw]) (lt_lx F)
  have lps : Rs.ram.get! P.lp = R.ram.get! P.lp := by
    obtain ⟨_, _, _, _, w⟩ := Ss
    exact w _ (by simp [kw]) (lt_lp F)
  have H0 : At E {cScr P (R.ram.get! P.lx) with s := Rs.s} Rs :=
    mkAt gs pcs (kat lxs) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k8, _, A8, _, W8, C8⟩ := ScreenClamp.pieceY_spec (F.scr _ _) H0 rfl
  generalize hR8 : stepN k8 Rs = R8 at A8 W8
  have S8 : Seg E (posW P ++ stk2 R.s) R R8 :=
    Ss.trans ⟨k8, hR8, C8, A8.s, W8⟩ (fun i hi => by
      rcases List.mem_append.1 hi with h1 | h1
      · exact ⟨List.mem_append_left _ (List.mem_append_right _ h1), pos_in i h1⟩
      · exact ⟨List.mem_append_right _ h1, stk_in i h1⟩)
  have s8 : R8.s = R.s := by obtain ⟨_, _, _, e, _⟩ := S8; exact e
  have lx8 : R8.ram.get! P.lx = (adcC (R.ram.get! P.lx) Rs.y false).1 := A8.K _ (List.mem_singleton.2 rfl)
  have lp8 : R8.ram.get! P.lp = R.ram.get! P.lp := (W8 _ (by simp) (lt_lp F)).trans lps
  -- the page and the screen's right edge
  have I0 : At E (cPg P R8.s (R.ram.get! P.lp) (adcC (R.ram.get! P.lx) Rs.y false).2) R8 :=
    mkAt A8.good A8.pc (kat lp8) (fun _ h => by cases h) (fun b hb => by cases hb; exact A8.cf _ rfl)
  obtain ⟨k9, _, A9, W9, _, C9⟩ := piece_spec (F.pg _ _ _) I0
  generalize hR9 : stepN k9 R8 = R9 at A9 W9
  have s9 : R9.s = R8.s := A9.s
  have S9 : Seg E (posW P ++ stk2 R.s) R R9 :=
    S8.trans ⟨k9, hR9, C9, s9, W9⟩ (fun i hi => by
      refine ⟨hi, ?_⟩
      rw [s8]
      rcases List.mem_append.1 hi with h1 | h1
      · exact List.mem_append_left _ (List.mem_append_right _ h1)
      · exact List.mem_append_right _ h1)
  have lp9 : R9.ram.get! P.lp = (adcC (R.ram.get! P.lp) 0 (adcC (R.ram.get! P.lx) Rs.y false).2).1 := A9.K _ (List.mem_singleton.2 rfl)
  have lx9 : R9.ram.get! P.lx = (adcC (R.ram.get! P.lx) Rs.y false).1 := (W9 _ (by simp) (lt_lx F)).trans lx8
  refine finish F S9 (fun i hi => List.mem_append_left _ hi) (fun i hi => List.mem_append_right _ hi) A9.good A9.pc (Or.inr ⟨⟨?_, ?_, ?_, hx⟩, Rs.y, ys2, ?_⟩)
  · exact hv
  · exact le_of_not_lt' hw
  · exact ht
  · unfold left16
    rw [lp9, lx9, left_add]

end

/-- **The scroll's rule**, on real machines: from the scroll handler's entry to the clamp's call, the stack, the position and the return address are kept, and the
left edge is kept or moves by `Y`, with `Y ≤ X` (the scroll's amount `amountOf`), and only when the scroll is allowed (`Allows`). `hc` is the check on the
ROM. -/
theorem scroll_rule {sy : Syms} {m0 : Machine} (hc : check sy m0 = true) {R : Machine} (hg : Good (Rom.of m0) R) (hpc : R.pc = (places sy m0).entry) :
    ∃ k, Ends (Rom.of m0) (places sy m0) R (stepN k R) ∧ InFrameN (Rom.of m0) R k :=
  scroll_of_facts (facts_of_check hc) hg hpc

theorem sub2_add1 (s : UInt8) : s - 1 - 1 + 1 = s - 1 := by
  have key : ∀ n : Fin 256, n.val.toUInt8 - 1 - 1 + 1 = n.val.toUInt8 - 1 := by decide +kernel
  have k := key ⟨s.toNat, s.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat] using k

theorem sub2_add2 (s : UInt8) : s - 1 - 1 + 1 + 1 = s := by
  have key : ∀ n : Fin 256, n.val.toUInt8 - 1 - 1 + 1 + 1 = n.val.toUInt8 := by decide +kernel
  have k := key ⟨s.toNat, s.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat] using k

/-- **The scroll handler's call, as a whole**, on real machines: from the call at the end of the player's routine (`PlayerSubs`) to the instruction after it, the
stack is kept, and the left edge is kept or moves by `Y` with `Y ≤ X`, only when the scroll is allowed, all read at the call. After the scroll the clamp at
the screen's edge and the offscreen bits do not write the edge (`tailCheck`). -/
theorem scroll_call {sy : Syms} {m0 : Machine} (hc : check sy m0 = true) {Q : Machine} (hg : Good (Rom.of m0) Q) (hpc : Q.pc = sy.PlayerSubs) :
    ∃ k, Good (Rom.of m0) (stepN k Q) ∧ (stepN k Q).pc = sy.PlayerSubs + 3 ∧ (stepN k Q).s = Q.s ∧
      (left16 (places sy m0) (stepN k Q) = left16 (places sy m0) Q ∨
        (Allows (places sy m0) Q ∧ ∃ Y : UInt8, Y.toNat ≤ (amountOf (places sy m0) Q).toNat ∧
          left16 (places sy m0) (stepN k Q) = (left16 (places sy m0) Q + Y.toNat) % 65536)) ∧ InFrameN (Rom.of m0) Q k := by
  have F := facts_of_check hc
  have hsub : (places sy m0).subs = sy.PlayerSubs := rfl
  rw [← hsub] at hpc ⊢
  generalize Rom.of m0 = E at F hg ⊢
  generalize places sy m0 = P at F hpc ⊢
  -- the call
  have J0 : At E (cAtS P.subs Q.s) Q := mkAt hg hpc (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k1, _, A1, W1, _, C1⟩ := piece_spec (F.jsr Q.s) J0
  generalize hR1 : stepN k1 Q = R1 at A1 W1
  have s1 : R1.s = Q.s - 1 - 1 := A1.s
  have hi1 : R1.ram.get! (stkI Q.s) = retHi P := A1.K (stkI Q.s, retHi P) (by simp)
  have lo1 : R1.ram.get! (stkI (Q.s - 1)) = retLo P := A1.K (stkI (Q.s - 1), retLo P) (by simp)
  -- the scroll and the clamp's call
  obtain ⟨k2, ⟨g2, pc2, s2, _, st2, L2⟩, C2⟩ := scroll_of_facts F A1.good A1.pc
  generalize hR2 : stepN k2 R1 = R2 at g2 pc2 s2 st2 L2
  have lo2 : R2.ram.get! (stkI (R2.s + 1)) = retLo P := by
    rw [s2, s1, sub2_add1]
    have e := st2 (stkI (R1.s + 1)) (by simp [stk2])
    rw [s1, sub2_add1] at e
    rw [e, lo1]
  have hi2 : R2.ram.get! (stkI (R2.s + 1 + 1)) = retHi P := by
    rw [s2, s1, sub2_add2]
    have e := st2 (stkI (R1.s + 1 + 1)) (by simp [stk2])
    rw [s1, sub2_add2] at e
    rw [e, hi1]
  -- the clamp, up to the return
  have T0 : At E { pc := P.chk, s := R2.s, K := [(stkI (R2.s + 1), retLo P), (stkI (R2.s + 1 + 1), retHi P)] } R2 := by
    refine mkAt g2 pc2 ?_ (fun _ h => by cases h) (fun _ h => by cases h)
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact lo2
    · rw [List.mem_singleton.1 hq]
      exact hi2
  obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec (F.tail R2.s) T0
  have s3 : (stepN k3 R2).s = Q.s := by
    rw [A3.s]
    show R2.s + 1 + 1 = Q.s
    rw [s2, s1, sub2_add2]
  have lx3 : (stepN k3 R2).ram.get! P.lx = R2.ram.get! P.lx := W3 _ (by simp) (lt_lx F)
  have lp3 : (stepN k3 R2).ram.get! P.lp = R2.ram.get! P.lp := W3 _ (by simp) (lt_lp F)
  have L3 : left16 P (stepN k3 R2) = left16 P R2 := by unfold left16; rw [lx3, lp3]
  have L1 : left16 P R1 = left16 P Q := by
    unfold left16
    rw [W1 _ (by simp) (lt_lx F), W1 _ (by simp) (lt_lp F)]
  have k1' : ∀ i ∈ [P.xs, P.plat, P.lockB, P.pfs, P.sideB], R1.ram.get! i = Q.ram.get! i := fun i hi =>
    W1 i (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))) (F.lt i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; rcases hi with h | h | h | h | h <;> simp [h]))
  have hA : amountOf P R1 = amountOf P Q := by unfold amountOf; rw [k1' _ (by simp), k1' _ (by simp)]
  have hAl : Allows P R1 → Allows P Q := by
    intro ⟨a1, a2, a3, a4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← k1' _ (by simp)]; exact a1
    · rw [← k1' _ (by simp)]; exact a2
    · rw [← k1' _ (by simp)]; exact a3
    · rw [← hA]; exact a4
  refine ⟨k1 + (k2 + k3), ?_⟩
  have eq : stepN (k1 + (k2 + k3)) Q = stepN k3 R2 := by rw [stepN_add, hR1, stepN_add, hR2]
  rw [eq]
  refine ⟨A3.good, A3.pc, s3, ?_, InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)⟩
  rw [L3, ← L1]
  rcases L2 with h | ⟨ha, Y, y2, hy⟩
  · exact Or.inl h
  · exact Or.inr ⟨hAl ha, Y, by rw [← hA]; exact y2, hy⟩

/-- **The screen's left edge as a position** (`SurfaceRead.edgeOf`) on a machine with the program of `m0`: `256·left16 + 255` -/
theorem edgeOf_left16 {sy : Syms} {m0 m : Machine} (hp : m.prg = m0.prg) (hk : m.prgMask = m0.prgMask) :
    SurfaceRead.edgeOf sy m = (left16 (places sy m0) m : Int) * 256 + 255 := by
  unfold SurfaceRead.edgeOf left16
  rw [SurfaceRead.places_congr hp hk]
  show ((((peek m (ScreenClamp.places sy m0).edgeP).toNat * 256 + (peek m (ScreenClamp.places sy m0).edgeX).toNat : Nat) : Int) * 256 + 255) = _
  rfl

/-- **The scroll handler's call, with the edge as a position**: from the call at the end of the player's routine to the instruction after it, the screen's left edge
(`SurfaceRead.edgeOf`) is kept, or the scroll is allowed and the edge is at most `256·Y` further, with `Y ≤ X`; the stack is kept. -/
theorem scroll_edge {sy : Syms} {m0 : Machine} (hc : check sy m0 = true) {Q : Machine} (hg : Good (Rom.of m0) Q) (hpc : Q.pc = sy.PlayerSubs) :
    ∃ k, Good (Rom.of m0) (stepN k Q) ∧ (stepN k Q).pc = sy.PlayerSubs + 3 ∧ (stepN k Q).s = Q.s ∧
      (SurfaceRead.edgeOf sy (stepN k Q) = SurfaceRead.edgeOf sy Q ∨
        (Allows (places sy m0) Q ∧ ∃ Y : UInt8, Y.toNat ≤ (amountOf (places sy m0) Q).toNat ∧
          SurfaceRead.edgeOf sy (stepN k Q) ≤ SurfaceRead.edgeOf sy Q + 256 * (Y.toNat : Int))) ∧ InFrameN (Rom.of m0) Q k := by
  obtain ⟨k, g, pc, sp, hl, f⟩ := scroll_call hc hg hpc
  refine ⟨k, g, pc, sp, ?_, f⟩
  rw [edgeOf_left16 g.prg g.mask, edgeOf_left16 hg.prg hg.mask]
  rcases hl with h | ⟨ha, Y, y2, hy⟩
  · exact Or.inl (by rw [h])
  · refine Or.inr ⟨ha, Y, y2, ?_⟩
    rw [hy]
    have := Nat.mod_le (left16 (places sy m0) Q + Y.toNat) 65536
    omega

end Smbrta.ScrollRule
