import Theorems.ClampSide

/-!
# Above ground: the screen's right edge in the scroll handler

The routine of the offscreen bits (`ClampSide.places.chk`) reads the screen's right edge as well as its left edge. The right edge's two bytes are one byte after
the left edge's (`ClampSide.eX P 1`, `ClampSide.eP P 1`). Its relation to the left edge is

  Rel(m):   right16(m) ≡ left16(m) + 255   (mod 2¹⁶),   left16 = 256·page + pixel of the left edge, right16 the same of the right edge.

Here (`scroll_rel`), on a real machine `Q` at the scroll handler's call (`PlayerSubs`): there is `k` with `stepN k Q` at the routine of the offscreen bits, with the
stack and the return address of the call as `ScrollRule.jsrCheck` leaves them, his position kept, and Rel(Q) → Rel(stepN k Q). The proof is by pieces of the code:

* the call (`jsr0Check`, for every stack byte);
* one walk from the scroll handler's entry with nothing known (`w1Check`): every path ends at the routine of the offscreen bits with both edges kept, or at the call of
  the routine that sets the right edge from the left edge (GetScreenPosition) with the right edge kept;
* that call (`jsrCheck`, for every stack byte), the routine's body (`gspCheck`, for every pixel and page of the left edge: it stores the left edge plus 255 with the
  carry), its return (`rtsOK`), and the rest to the routine of the offscreen bits (`tailCheck`: both edges kept).

No game data: the places are found from the program (the first call after the scroll's load of the left edge's page, its target, the target's return). With the
walks of `EdgeStep` (which follow the right edge's two bytes too) and the clamp (`ClampSide.clamp_end` keeps both edges) this gives Rel at the end of every
counted frame, from Rel at control (`SurfaceFrames.OnFrames.relAll`), and so the first half of the old field `rightRel`. Page: `1-1/e-2-10-3-19-RightEdge.md`.
-/

namespace Smbrta.RightEdge
open FrameModel ImpedePosition

/-- the places: the scroll handler's call and entry, the routine of the offscreen bits, the call of the right edge's routine in the scroll (the first `JSR` after the
load of the left edge's page), its target and the target's `RTS`, and the bytes of the two edges and of the position -/
structure Places where
  subs : UInt16
  entry : UInt16
  chk : UInt16
  jsr : UInt16
  gsp : UInt16
  rts : UInt16
  lx : Nat
  lp : Nat
  rx : Nat
  rp : Nat
  /-- round 31: his speed, kept up to the routine of the offscreen bits (for the field `clampR` at the clamp's entry) -/
  sp : Nat
  deriving Inhabited

def places (sy : Syms) (m0 : Machine) : Places :=
  let E := Rom.of m0
  let S := ScrollRule.places sy m0
  let C := ClampSide.places sy m0
  let jsr := PipeEntryRule.findOp m0 S.pg 0x20 32
  let gsp := E.w (jsr + 1)
  { subs := S.subs, entry := S.entry, chk := S.chk, jsr, gsp, rts := PipeEntryRule.findOp m0 gsp 0x60 32,
    lx := ClampSide.eX C 0, lp := ClampSide.eP C 0, rx := ClampSide.eX C 1, rp := ClampSide.eP C 1, sp := I sy.Player_X_Speed }

/-- `1` as a word -/
theorem one16 : (1 : UInt8).toUInt16 = 1 := by decide

/-- the right edge's bytes, one byte after the left edge's -/
theorem eX_one (C : ClampSide.Places) : ClampSide.eX C 1 = (C.edgeX + 1 &&& 0x7FF).toNat := by
  unfold ClampSide.eX I
  rw [one16]
theorem eP_one (C : ClampSide.Places) : ClampSide.eP C 1 = (C.edgeP + 1 &&& 0x7FF).toNat := by
  unfold ClampSide.eP I
  rw [one16]

/-- **The right edge's relation** to the left edge, modulo 2¹⁶ -/
def Rel (C : ClampSide.Places) (m : Machine) : Prop :=
  ClampSide.edge16 C 1 m % 65536 = (ClampSide.edge16 C 0 m + 255) % 65536

/-- the edges' four bytes, and his speed -/
def edges (P : Places) : List Nat := [P.lx, P.lp, P.rx, P.rp, P.sp]

/-- the return address of the call of the right edge's routine -/
def gLo (P : Places) : UInt8 := (P.jsr + 2).toUInt8
def gHi (P : Places) : UInt8 := ((P.jsr + 2) >>> 8).toUInt8

/-! ## The pieces -/

/-- the scroll handler's call: the return address on the stack, the edges and the position kept -/
def jsr0Check (E : Rom) (S : ScrollRule.Places) (P : Places) (s : UInt8) : Bool :=
  pieceOK E (ScrollRule.cAtS P.subs s)
    { pc := P.entry, s := s - 1 - 1, K := [(stkI s, ScrollRule.retHi S), (stkI (s - 1), ScrollRule.retLo S)] } (edges P ++ ScrollRule.posW S) 2

/-- the bytes the first walk keeps up to the routine of the offscreen bits, and up to the call of the right edge's routine -/
def wA (S : ScrollRule.Places) (P : Places) : List Nat := edges P ++ ScrollRule.posW S ++ stackI
def wB (S : ScrollRule.Places) (P : Places) : List Nat := [P.rx, P.rp, P.sp] ++ ScrollRule.posW S ++ stackI

def stop1 (P : Places) (Q : TS) : Bool := Q.pc == P.chk || Q.pc == P.jsr
def goal1 (S : ScrollRule.Places) (P : Places) (Q : TS) : Bool :=
  if Q.pc == P.chk then goal0 (ScrollRule.cAt P.chk) (wA S P) Q else goal0 (ScrollRule.cAt P.jsr) (wB S P) Q

/-- **the first walk**: from the scroll handler's entry, the stack unknown and kept, every byte unknown, every branch both ways -/
def w1Check (E : Rom) (S : ScrollRule.Places) (P : Places) : Bool :=
  walkT E (stop1 P) (goal1 S P) 64 (start0 (ScrollRule.cAt P.entry))

/-- the call of the right edge's routine -/
def jsrCheck (E : Rom) (S : ScrollRule.Places) (P : Places) (s : UInt8) : Bool :=
  pieceOK E (ScrollRule.cAtS P.jsr s) { pc := P.gsp, s := s - 1 - 1, K := [(stkI s, gHi P), (stkI (s - 1), gLo P)] }
    (edges P ++ ScrollRule.posW S ++ ScrollRule.stk2 s) 2

/-- the right edge's routine: the left edge plus 255, with the carry into the page -/
def gspCheck (E : Rom) (S : ScrollRule.Places) (P : Places) (u p : UInt8) : Bool :=
  piece0 E { pc := P.gsp, s := 0, K := [(P.lx, u), (P.lp, p)] }
    { pc := P.rts, s := 0, K := [(P.rx, (adcC u 0xFF false).1), (P.rp, (adcC p 0 (adcC u 0xFF false).2).1)] } ([P.lx, P.lp, P.sp] ++ ScrollRule.posW S ++ stackI) 8

/-- the routine's return is an `RTS` -/
def rtsOK (E : Rom) (P : Places) : Bool := decide (0x8000 ≤ P.rts) && E.b P.rts == 0x60 && !idleAt E P.rts

/-- from the instruction after the call to the routine of the offscreen bits -/
def tailCheck (E : Rom) (S : ScrollRule.Places) (P : Places) : Bool :=
  piece0 E (ScrollRule.cAt (P.jsr + 3)) (ScrollRule.cAt P.chk) (wA S P) 8

def checkParts (E : Rom) (S : ScrollRule.Places) (P : Places) : Bool :=
  (List.range 256).all (fun s => jsr0Check E S P s.toUInt8) && w1Check E S P &&
  (List.range 256).all (fun s => jsrCheck E S P s.toUInt8) &&
  (List.range 256).all (fun u => (List.range 256).all fun p => gspCheck E S P u.toUInt8 p.toUInt8) &&
  rtsOK E P && tailCheck E S P

/-- **The check on the ROM** -/
def check (sy : Syms) (m0 : Machine) : Bool := checkParts (Rom.of m0) (ScrollRule.places sy m0) (places sy m0)

/-! ## What the pieces say -/

section
variable {E : Rom} {S : ScrollRule.Places} {P : Places}

structure Facts (E : Rom) (S : ScrollRule.Places) (P : Places) : Prop where
  jsr0 : ∀ s, jsr0Check E S P s = true
  w1 : w1Check E S P = true
  jsr : ∀ s, jsrCheck E S P s = true
  gsp : ∀ u p, gspCheck E S P u p = true
  rts : rtsOK E P = true
  tail : tailCheck E S P = true

theorem facts_of_check (h : checkParts E S P = true) : Facts E S P := by
  simp only [checkParts, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨ScrollRule.all256 h0, h1, ScrollRule.all256 h2, fun u p => ?_, h4, h5⟩
  exact ScrollRule.all256 (f := fun p => gspCheck E S P u p) (ScrollRule.all256 (f := fun u => (List.range 256).all fun p => gspCheck E S P u p.toUInt8) h3 u) p

/-- what a walk's end with `goal0` says of the machine -/
theorem goal0_at {c : Cut} {watch : List Nat} {Q : TS} {m m' : Machine} (hg : goal0 c watch Q = true) (H : Lk E m m Q m' m') :
    At E {c with s := m.s} m' ∧ ∀ i ∈ watch, i < 2048 → m'.ram.get! i = m.ram.get! i := by
  have hg0 : Q.s.isNone = true ∧ goalC {c with s := 0} watch {Q with s := some 0} = true := by
    simpa only [goal0, Bool.and_eq_true] using hg
  have hn : Q.s = none := Option.isNone_iff_eq_none.1 hg0.1
  have hs := H.s0 hn
  have H' : Lk E m m {Q with s := some m.s} m' m' := by
    refine ⟨H.gl, H.gr, H.pcl, H.pcr, ⟨H.regs.a, H.regs.x, H.regs.y, H.regs.c, H.regs.z, H.regs.nf⟩, ?_, ?_, H.ram, H.fixl, H.fixr⟩
    · intro v hv
      have e := Option.some.inj hv
      simpa only [← e] using hs
    · intro hv; cases hv
  have hg' : goalC {c with s := m.s} watch {Q with s := some m.s} = true := by
    have h1 := hg0.2
    simpa only [goalC, beq_self_eq_true] using h1
  obtain ⟨ha, hw, _⟩ := at_of_goal hg' H'
  exact ⟨ha, hw⟩

/-- **the first walk on a real machine**: from the scroll handler's entry it comes to the routine of the offscreen bits with `wA` kept, or to the call of the right
edge's routine with `wB` kept, the stack kept -/
theorem w1_spec (h : w1Check E S P = true) {m : Machine} (hA : At E {ScrollRule.cAt P.entry with s := m.s} m) :
    ∃ k, InFrameN E m k ∧
      ((At E {ScrollRule.cAt P.chk with s := m.s} (stepN k m) ∧ ∀ i ∈ wA S P, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∨
       (At E {ScrollRule.cAt P.jsr with s := m.s} (stepN k m) ∧ ∀ i ∈ wB S P, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i)) := by
  obtain ⟨k, Q, _, _, hg, H, hh⟩ := walkT_spec (m₀ := m) (n₀ := m) 64 (start0 (ScrollRule.cAt P.entry)) m m h (lk_start0 hA)
  refine ⟨k, fun j hj => by obtain ⟨_, _, _, _, hi, _⟩ := hh j hj; exact hi, ?_⟩
  unfold goal1 at hg
  split at hg
  · exact Or.inl (goal0_at hg H)
  · exact Or.inr (goal0_at hg H)

end

/-- the two bytes of a 16-bit number, put together again -/
theorem bytes16 (v : UInt16) : v.toUInt8.toUInt16 ||| ((v >>> 8).toUInt8.toUInt16 <<< 8) = v := by
  apply UInt16.toNat_inj.1
  have hv := v.toNat_lt
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16, UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
  have h8 : (8 : UInt16).toNat % 16 = 8 := rfl
  rw [h8]
  have hb : v.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hs : (v.toNat >>> 8 % 2 ^ 8) <<< 8 % 2 ^ 16 = (v.toNat >>> 8 % 2 ^ 8) <<< 8 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  rw [hs, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem edges_lt {P : Places} {sy : Syms} {m0 : Machine} (h : P = places sy m0) : ∀ i ∈ edges P, i < 2048 := by
  intro i hi
  subst h
  simp only [edges, places, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact I_lt _

theorem posW_lt {sy : Syms} {m0 : Machine} : ∀ i ∈ ScrollRule.posW (ScrollRule.places sy m0), i < 2048 := by
  intro i hi
  simp only [ScrollRule.posW, ScrollRule.places, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact I_lt _

/-! ## The scroll handler, from its call to the routine of the offscreen bits -/

section Run
variable {sy : Syms} {m0 : Machine}

/-- **The right edge's relation through the scroll's part of the scroll handler.** From a real machine `Q` at the scroll handler's call (`PlayerSubs`) the run comes in
`k` steps, in the frame, to the routine of the offscreen bits, with the stack 2 below, the call's return address on it, his position kept, and the right edge's
relation kept (on the paths without a scroll both edges are kept; on the path with a scroll the right edge's routine sets it from the left edge, which is kept to
the end). `hc` is the check on the ROM. -/
theorem scroll_rel (hc : check sy m0 = true) {Q : Machine} (hg : Good (Rom.of m0) Q) (hpc : Q.pc = sy.PlayerSubs) :
    ∃ k, Good (Rom.of m0) (stepN k Q) ∧ (stepN k Q).pc = (ClampSide.places sy m0).chk ∧ (stepN k Q).s = Q.s - 1 - 1 ∧
      (stepN k Q).ram.get! (stkI Q.s) = ScrollRule.retHi (ScrollRule.places sy m0) ∧
      (stepN k Q).ram.get! (stkI (Q.s - 1)) = ScrollRule.retLo (ScrollRule.places sy m0) ∧
      (∀ i ∈ ScrollRule.posW (ScrollRule.places sy m0), (stepN k Q).ram.get! i = Q.ram.get! i) ∧
      (stepN k Q).ram.get! (I sy.Player_X_Speed) = Q.ram.get! (I sy.Player_X_Speed) ∧ InFrameN (Rom.of m0) Q k ∧
      (Rel (ClampSide.places sy m0) Q → Rel (ClampSide.places sy m0) (stepN k Q)) := by
  have F := facts_of_check hc
  generalize hS : ScrollRule.places sy m0 = S at F
  generalize hP : places sy m0 = P at F
  have eChk : (ClampSide.places sy m0).chk = P.chk := by rw [← hP]; rfl
  have eLx : ClampSide.eX (ClampSide.places sy m0) 0 = P.lx := by rw [← hP]; rfl
  have eLp : ClampSide.eP (ClampSide.places sy m0) 0 = P.lp := by rw [← hP]; rfl
  have eRx : ClampSide.eX (ClampSide.places sy m0) 1 = P.rx := by rw [← hP]; rfl
  have eRp : ClampSide.eP (ClampSide.places sy m0) 1 = P.rp := by rw [← hP]; rfl
  have eSub : P.subs = sy.PlayerSubs := by rw [← hP]; rfl
  have eEnt : P.entry = S.entry := by rw [← hP, ← hS]; rfl
  have hE : ∀ i ∈ edges P, i < 2048 := edges_lt hP.symm
  have hW : ∀ i ∈ ScrollRule.posW S, i < 2048 := by rw [← hS]; exact posW_lt
  have hSt : ∀ i ∈ stackI, i < 2048 := fun i hi => stack_bound hi
  have mE : ∀ {L : List Nat} {i : Nat}, i ∈ edges P → i ∈ edges P ++ L := fun h => List.mem_append_left _ h
  have mEx : P.lx ∈ edges P := by simp [edges]
  have mEp : P.lp ∈ edges P := by simp [edges]
  have mRx : P.rx ∈ edges P := by simp [edges]
  have mRp : P.rp ∈ edges P := by simp [edges]
  have mSp : P.sp ∈ edges P := by simp [edges]
  have eSp : I sy.Player_X_Speed = P.sp := by rw [← hP]; rfl
  -- the relation from the four bytes
  have relOf : ∀ {a b : Machine}, a.ram.get! P.lx = b.ram.get! P.lx → a.ram.get! P.lp = b.ram.get! P.lp → a.ram.get! P.rx = b.ram.get! P.rx →
      a.ram.get! P.rp = b.ram.get! P.rp → Rel (ClampSide.places sy m0) b → Rel (ClampSide.places sy m0) a := by
    intro a b h1 h2 h3 h4 hr
    unfold Rel ClampSide.edge16 at hr ⊢
    rw [eLx, eLp, eRx, eRp] at hr ⊢
    rw [h1, h2, h3, h4]
    exact hr
  -- the call
  have J0 : At (Rom.of m0) (ScrollRule.cAtS P.subs Q.s) Q :=
    mkAt hg (by rw [eSub]; exact hpc) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k1, _, A1, W1, _, C1⟩ := piece_spec (F.jsr0 Q.s) J0
  generalize hQ1 : stepN k1 Q = Q1 at A1 W1
  have sQ1 : Q1.s = Q.s - 1 - 1 := A1.s
  have hi1 : Q1.ram.get! (stkI Q.s) = ScrollRule.retHi S := A1.K (stkI Q.s, ScrollRule.retHi S) (by simp)
  have lo1 : Q1.ram.get! (stkI (Q.s - 1)) = ScrollRule.retLo S := A1.K (stkI (Q.s - 1), ScrollRule.retLo S) (by simp)
  have k1E : ∀ i ∈ edges P, Q1.ram.get! i = Q.ram.get! i := fun i hi => W1 i (mE hi) (hE i hi)
  have k1W : ∀ i ∈ ScrollRule.posW S, Q1.ram.get! i = Q.ram.get! i := fun i hi => W1 i (List.mem_append_right _ hi) (hW i hi)
  -- the first walk
  have A1' : At (Rom.of m0) {ScrollRule.cAt P.entry with s := Q1.s} Q1 :=
    mkAt A1.good (A1.pc.trans rfl) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k2, C2, H2⟩ := w1_spec F.w1 A1'
  rcases H2 with ⟨A2, W2⟩ | ⟨A2, W2⟩
  · -- no call of the right edge's routine: both edges kept
    refine ⟨k1 + k2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [stepN_add, hQ1]; exact A2.good
    · rw [stepN_add, hQ1, A2.pc, eChk]; rfl
    · rw [stepN_add, hQ1, A2.s, sQ1]
    · rw [stepN_add, hQ1, W2 _ (List.mem_append_right _ (stack_mem _)) (mask_stk _), hi1]
    · rw [stepN_add, hQ1, W2 _ (List.mem_append_right _ (stack_mem _)) (mask_stk _), lo1]
    · intro i hi
      rw [stepN_add, hQ1, W2 i (List.mem_append_left _ (List.mem_append_right _ hi)) (hW i hi), k1W i hi]
    · rw [stepN_add, hQ1, eSp]
      exact (W2 _ (List.mem_append_left _ (List.mem_append_left _ mSp)) (hE _ mSp)).trans (k1E _ mSp)
    · exact InFrameN.add' C1 hQ1 C2
    · intro hr
      rw [stepN_add, hQ1]
      have kk : ∀ i ∈ edges P, (stepN k2 Q1).ram.get! i = Q.ram.get! i := fun i hi =>
        (W2 i (List.mem_append_left _ (List.mem_append_left _ hi)) (hE i hi)).trans (k1E i hi)
      exact relOf (kk _ mEx) (kk _ mEp) (kk _ mRx) (kk _ mRp) hr
  · -- the call of the right edge's routine
    generalize hQ2 : stepN k2 Q1 = Q2 at A2 W2
    have sQ2 : Q2.s = Q1.s := A2.s
    have J2 : At (Rom.of m0) (ScrollRule.cAtS P.jsr Q2.s) Q2 :=
      mkAt A2.good A2.pc (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec (F.jsr Q2.s) J2
    generalize hQ3 : stepN k3 Q2 = Q3 at A3 W3
    have sQ3 : Q3.s = Q2.s - 1 - 1 := A3.s
    have ghi : Q3.ram.get! (stkI Q2.s) = gHi P := A3.K (stkI Q2.s, gHi P) (by simp)
    have glo : Q3.ram.get! (stkI (Q2.s - 1)) = gLo P := A3.K (stkI (Q2.s - 1), gLo P) (by simp)
    -- the routine's body
    have A3' : At (Rom.of m0) {{ pc := P.gsp, s := 0, K := [(P.lx, Q3.ram.get! P.lx), (P.lp, Q3.ram.get! P.lp)] : Cut } with s := Q3.s} Q3 := by
      refine mkAt A3.good A3.pc ?_ (fun _ h => by cases h) (fun _ h => by cases h)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    obtain ⟨k4, _, A4, W4, C4⟩ := piece0_spec (F.gsp (Q3.ram.get! P.lx) (Q3.ram.get! P.lp)) A3'
    generalize hQ4 : stepN k4 Q3 = Q4 at A4 W4
    have rx4 : Q4.ram.get! P.rx = (adcC (Q3.ram.get! P.lx) 0xFF false).1 := A4.K (P.rx, (adcC (Q3.ram.get! P.lx) 0xFF false).1) (by simp)
    have rp4 : Q4.ram.get! P.rp = (adcC (Q3.ram.get! P.lp) 0 (adcC (Q3.ram.get! P.lx) 0xFF false).2).1 :=
      A4.K (P.rp, (adcC (Q3.ram.get! P.lp) 0 (adcC (Q3.ram.get! P.lx) 0xFF false).2).1) (by simp)
    have lx4 : Q4.ram.get! P.lx = Q3.ram.get! P.lx := W4 _ (by simp) (hE _ mEx)
    have lp4 : Q4.ram.get! P.lp = Q3.ram.get! P.lp := W4 _ (by simp) (hE _ mEp)
    have sQ4 : Q4.s = Q3.s := A4.s
    -- the return
    have hr := F.rts
    simp only [rtsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hr
    have hr1 : 0x8000 ≤ Q4.pc := by rw [A4.pc]; exact hr.1.1
    have hr2 : lookupOp ((Rom.of m0).b Q4.pc) insList = some .rts := by rw [A4.pc, hr.1.2]; exact lookup_rts
    have hr3 : idleAt (Rom.of m0) Q4.pc = false := by rw [A4.pc]; exact hr.2
    obtain ⟨rp5, rs5, rm5, rg5⟩ := step_rts A4.good hr1 hr2 hr3
    rw [← stepN_one] at rp5 rs5 rm5 rg5
    have C5 : InFrameN (Rom.of m0) Q4 1 := fun j hj => by
      have e : j = 0 := by omega
      subst e
      exact inFrame_rts A4.good hr1 hr2 hr3
    generalize hQ5 : stepN 1 Q4 = Q5 at rp5 rs5 rm5 rg5
    have lo4 : Q4.ram.get! (stkI (Q4.s + 1)) = gLo P := by
      rw [sQ4, sQ3, ScrollRule.sub2_add1, W4 _ (List.mem_append_right _ (stack_mem _)) (mask_stk _)]
      exact glo
    have hi4 : Q4.ram.get! (stkI (Q4.s + 1 + 1)) = gHi P := by
      rw [sQ4, sQ3, ScrollRule.sub2_add2, W4 _ (List.mem_append_right _ (stack_mem _)) (mask_stk _)]
      exact ghi
    have pc5 : Q5.pc = P.jsr + 3 := by
      rw [rp5, lo4, hi4]
      unfold gLo gHi
      rw [bytes16, UInt16.add_assoc]
      rfl
    have sQ5 : Q5.s = Q2.s := by
      rw [rs5, sQ4, sQ3, ScrollRule.sub2_add2]
    -- the tail
    have A5 : At (Rom.of m0) {ScrollRule.cAt (P.jsr + 3) with s := Q5.s} Q5 :=
      mkAt rg5 pc5 (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    obtain ⟨k6, _, A6, W6, C6⟩ := piece0_spec F.tail A5
    generalize hQ6 : stepN k6 Q5 = Q6 at A6 W6
    have eQ : stepN (k1 + (k2 + (k3 + (k4 + (1 + k6))))) Q = Q6 := by
      rw [stepN_add, hQ1, stepN_add, hQ2, stepN_add, hQ3, stepN_add, hQ4, stepN_add, hQ5, hQ6]
    have r54 : ∀ i, Q5.ram.get! i = Q4.ram.get! i := fun i => by rw [rm5]
    have sQ2' : Q2.s = Q.s - 1 - 1 := sQ2.trans sQ1
    -- the stack bytes of the scroll handler's call, from `Q1` to `Q6`
    have stk : ∀ t, t = stkI (Q2.s + 1) ∨ t = stkI (Q2.s + 1 + 1) → Q6.ram.get! t = Q1.ram.get! t := by
      intro t ht
      have m3 : t ∈ edges P ++ ScrollRule.posW S ++ ScrollRule.stk2 Q2.s := by
        apply List.mem_append_right
        rcases ht with rfl | rfl <;> simp [ScrollRule.stk2]
      have ms : t ∈ stackI := by rcases ht with rfl | rfl <;> exact stack_mem _
      have hl : t < 2048 := hSt t ms
      rw [W6 t (List.mem_append_right _ ms) hl, r54, W4 t (List.mem_append_right _ ms) hl, W3 t m3 hl,
        W2 t (List.mem_append_right _ ms) hl]
    -- his position, from `Q` to `Q6`
    have pos : ∀ i ∈ ScrollRule.posW S, Q6.ram.get! i = Q.ram.get! i := by
      intro i hi
      have hl := hW i hi
      rw [W6 i (List.mem_append_left _ (List.mem_append_right _ hi)) hl, r54, W4 i (List.mem_append_left _ (List.mem_append_right _ hi)) hl,
        W3 i (List.mem_append_left _ (List.mem_append_right _ hi)) hl, W2 i (List.mem_append_left _ (List.mem_append_right _ hi)) hl, k1W i hi]
    -- the edges at `Q6`, from the routine's body
    have e64 : ∀ i ∈ edges P, Q6.ram.get! i = Q4.ram.get! i := fun i hi => by
      rw [W6 i (List.mem_append_left _ (List.mem_append_left _ hi)) (hE i hi), r54]
    have hrel : Rel (ClampSide.places sy m0) Q6 := by
      unfold Rel ClampSide.edge16
      rw [eLx, eLp, eRx, eRp, e64 _ mEx, e64 _ mEp, e64 _ mRx, e64 _ mRp, rx4, rp4, lx4, lp4, ScrollRule.left_add]
      have h255 : (0xFF : UInt8).toNat = 255 := rfl
      rw [h255]
      omega
    have spd : Q6.ram.get! P.sp = Q.ram.get! P.sp := by
      have hl := hE _ mSp
      rw [W6 _ (List.mem_append_left _ (List.mem_append_left _ mSp)) hl, r54, W4 _ (List.mem_append_left _ (List.mem_append_left _ (by simp))) hl,
        W3 _ (List.mem_append_left _ (List.mem_append_left _ mSp)) hl, W2 _ (List.mem_append_left _ (List.mem_append_left _ (by simp))) hl, k1E _ mSp]
    refine ⟨k1 + (k2 + (k3 + (k4 + (1 + k6)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩
    · rw [eQ]; exact A6.good
    · rw [eQ, A6.pc, eChk]; rfl
    · rw [eQ, A6.s, sQ5, sQ2']
    · rw [eQ]
      have e := stk (stkI Q.s) (Or.inr (by rw [sQ2', ScrollRule.sub2_add2]))
      rw [e, hi1]
    · rw [eQ]
      have e := stk (stkI (Q.s - 1)) (Or.inl (by rw [sQ2', ScrollRule.sub2_add1]))
      rw [e, lo1]
    · intro i hi
      rw [eQ]
      exact pos i hi
    · rw [eQ, eSp]
      exact spd
    · exact InFrameN.add' C1 hQ1 (InFrameN.add' C2 hQ2 (InFrameN.add' C3 hQ3 (InFrameN.add' C4 hQ4 (InFrameN.add' C5 hQ5 C6))))
    · rw [eQ]; exact hrel

end Run

end Smbrta.RightEdge
