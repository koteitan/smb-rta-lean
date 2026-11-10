import Theorems.PipeEntryRule
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# The screen's page in the room, and the long timer of the side pipe

The condition at the entry of the side pipe has `timer ≥ 160`: at the entry frame the screen is on the first page, and the code sets the long timer. Here one whole frame in the room is followed with the abstract
machine of `TaintRun.lean`. A frame that starts in a condition on one state (`RoomCond`) ends in it, or it has left the player's routine with the page and the lock unchanged, and if it entered the side pipe, the timer is the
long one (`room_step`). So over the frames from the first control to the entry the page and the lock stay, and the entry has the long timer (`room_run`, `RoomRun.timer`).

What stays assumed is on one instruction of a frame (`SiteOK`): the dot, that an `LDA (zp),Y` does not read a register, the tile that the block buffer routine reads, the place that a coin is erased at, the offset of the screen's
buffer, the low bits of the position in the pipe's code. And the condition on one state at the first control. The steps through a pointer that the machine does not know are proved here against `step` (`s_readStep`,
`s_writeStep`), so `TaintRun.lean` is not changed. There is no game data in this file: the known bytes are given by their names, and their values come from a reference machine. Page: `1-1/d-2-4-ScreenPage.md`.
-/

namespace Smbrta.ScreenPage

open PipeTransition (frame run zeros)
open PipeTransitionAll (go ba_get_set_self ba_get_set_ne ba_size_set go_bind)
open SideChangeBound
open TaintRun (AB mem_known_self mem_top bt bt_and bt_not bt_ext bt_zero)
open PipeEntryRule (trace nxt frame_trace trace_stop)

/-! ## Instructions through a pointer that the abstract machine does not know -/

/-- the address that the `LDA (zp),Y` at `m.pc` reads -/
def readAddr (m : Machine) : UInt16 := (go mIzyR { m with pc := m.pc + 1 }).1

/-- the byte that the `LDA (zp),Y` at `m.pc` reads -/
def readVal (m : Machine) : UInt8 :=
  let r := go mIzyR { m with pc := m.pc + 1 }
  (go (rd r.1) r.2).1

/-- the address that the `STA (zp),Y` at `m.pc` writes -/
def writeAddr (m : Machine) : UInt16 := (go mIzy { m with pc := m.pc + 1 }).1

/-- the address is in the RAM or the ROM, not at a register -/
def RamRom (a : UInt16) : Prop := a < 0x2000 ∨ 0x8000 ≤ a

section
variable {E : Env} {F : Nat × UInt8}

/-- the two bytes of the pointer are read, and nothing changes -/
theorem s_zp (z : UInt8) : Snd E F TT (Pure.pure () : AM Unit) (rd16zp z) := by
  refine snd_leaf fun A m hs a A' he => ?_
  have he2 : some ((), A) = some (a, A') := he
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj he2)
  have hlt : ∀ x : UInt8, x.toUInt16 < 0x2000 := by
    intro x
    apply UInt16.lt_iff_toNat_lt.2
    have := TaintRun.toUInt16_le x
    show x.toUInt16.toNat < 8192
    omega
  have e : go (rd16zp z) m = ((m.ram.get! (z.toUInt16 &&& 0x7FF).toNat).toUInt16 ||| ((m.ram.get! ((z + 1).toUInt16 &&& 0x7FF).toNat).toUInt16 <<< 8), m) := by
    show go (rd z.toUInt16 >>= fun lo => rd (z + 1).toUInt16 >>= fun hi => Pure.pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) m = _
    rw [go_bind, TaintRun.rd_ram (hlt z) hs.trk]
    simp only
    rw [go_bind, TaintRun.rd_ram (hlt (z + 1)) hs.trk]
    rfl
  rw [e]
  exact ⟨trivial, hs, rfl, rfl⟩

/-- the abstract address of a read through a pointer not known: the operand, and a page penalty that may come -/
def aPtrR (E : Env) : AM Unit :=
  afetch E >>= fun _ => (Pure.pure () : AM Unit) >>= fun _ => (MonadState.get : AM AS) >>= fun _ => atick 0 1 >>= fun _ => Pure.pure ()

def aPtrW (E : Env) : AM Unit :=
  afetch E >>= fun _ => (Pure.pure () : AM Unit) >>= fun _ => (MonadState.get : AM AS) >>= fun _ => Pure.pure ()

theorem s_tick01 (b e : UInt16) : Snd E F TT (atick 0 1) (pagePenalty b e) := by
  unfold pagePenalty
  split
  · exact s_tick (Nat.zero_le _) (Nat.le_refl _)
  · exact s_tick0

theorem s_ptrR : Snd E F (α := Unit) (β := UInt16) TT (aPtrR E) mIzyR :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    exact Snd.bind (s_zp _) fun _ _ _ => Snd.get fun _ _ _ => Snd.bind (s_tick01 _ _) fun _ _ _ => Snd.pure trivial

theorem s_ptrW : Snd E F (α := Unit) (β := UInt16) TT (aPtrW E) mIzy :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    exact Snd.bind (s_zp _) fun _ _ _ => Snd.get fun _ _ _ => Snd.pure trivial

/-! ### The read -/

set_option maxRecDepth 100000 in
theorem op_B1 : opTable[(0xB1 : UInt8).toNat]?.getD opJAM = opLDA mIzyR := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

set_option maxRecDepth 100000 in
theorem cyc_B1 : (cycTable.get! (0xB1 : UInt8).toNat).toNat = 5 := by decide

set_option maxRecDepth 100000 in
theorem op_91 : opTable[(0x91 : UInt8).toNat]?.getD opJAM = opSTA mIzy := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

set_option maxRecDepth 100000 in
theorem cyc_91 : (cycTable.get! (0x91 : UInt8).toNat).toNat = 6 := by decide

/-- `LDA (zp),Y` through a pointer not known, with the byte read in `v` -/
def readStep (E : Env) (v : AB) (A : AS) : Option AS :=
  ((((aPtrR E >>= fun _ => asetA v) >>= fun _ => atick 5 5) { A with pc := A.pc + 1 }).map (·.2))

/-- `STA (zp),Y` through a pointer not known -/
def writeStep (E : Env) (A : AS) : Option AS :=
  ((aPtrW E >>= fun _ => atick 6 6) { A with pc := A.pc + 1 }).map (·.2)

variable {E : Env} {F : Nat × UInt8}

theorem step_at {m : Machine} {op : UInt8} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = op) (hne : op ≠ 0x4C) :
    go step m = go ((opTable[op.toNat]?.getD opJAM) >>= fun _ => tick (cycTable.get! op.toNat).toNat) { m with pc := m.pc + 1 } := by
  rw [TaintRun.step_op hn hh hp, hop]
  unfold TaintRun.stepK
  have h : (op == 0x4C) = false := beq_eq_false_iff_ne.2 hne
  simp only [h, Bool.false_and, Bool.false_eq_true, if_false]

/-- the wide address: everything that is not a register -/
def wideAd : TaintRun.AAd := ⟨0x8000, 0x1FFF⟩

theorem ard_wide (A : AS) : ard E wideAd A = some (AB.top, A) := by
  unfold ard
  have h1 : (wideAd.lo == wideAd.hi) = false := by decide
  have h2 : (decide (wideAd.lo ≤ wideAd.hi) && (decide (wideAd.hi < 0x2000) || decide (0x8000 ≤ wideAd.lo))) = false := by decide
  have h3 : (decide (wideAd.hi < wideAd.lo) && decide (wideAd.hi < 0x2000) && decide (0x8000 ≤ wideAd.lo)) = true := by decide
  simp only [h1, h2, h3, Bool.false_eq_true, if_false, if_true]

theorem adR_wide {a : UInt16} (h : RamRom a) : AdR wideAd a := by
  right
  refine ⟨by decide, ?_⟩
  rcases h with h | h
  · right
    have h1 := UInt16.lt_iff_toNat_lt.1 h
    apply UInt16.le_iff_toNat_le.2
    have h2 : (0x2000 : UInt16).toNat = 8192 := rfl
    have h3 : wideAd.hi.toNat = 8191 := rfl
    rw [h3]
    omega
  · left
    exact h

theorem s_readStep {A : AS} {m : Machine} {v : AB} {B : AS} (hs : Sim E F A m) (hn : A.nmi = false) (hp : 0x8000 ≤ A.pc)
    (hop : E.prg.get! (A.pc &&& E.mask).toNat = 0xB1) (had : RamRom (readAddr m)) (hv : v.mem (readVal m)) (hB : readStep E v A = some B) :
    Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  have hn2 : m.nmiPending = false := by rw [hs.nmi]; exact hn
  have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
  have hop2 : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 := by rw [hs.prg, hs.mask, hs.pc]; exact hop
  rw [step_at hn2 hs.halted hpm hop2 (by decide), op_B1, cyc_B1]
  have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
    pc := by
      show m.pc + 1 = A.pc + 1
      rw [hs.pc] }
  unfold readStep at hB
  cases he : ((aPtrR E >>= fun _ => asetA v) >>= fun _ => atick 5 5) { A with pc := A.pc + 1 } with
  | none =>
    rw [he] at hB
    cases hB
  | some p =>
    rw [he] at hB
    obtain ⟨u, B1⟩ := p
    have hB1 : B1 = B := Option.some.inj hB
    subst hB1
    obtain ⟨_, A3, h1, h2⟩ := abind_some he
    obtain ⟨_, A2, h3, h4⟩ := abind_some h1
    obtain ⟨_, s2, a2⟩ := s_ptrR (E := E) (F := F) _ _ hs1 _ _ h3
    obtain ⟨_, s3, a3⟩ := TaintRun.s_ard (E := E) (F := F) (adR_wide had) A2 _ s2 _ _ (ard_wide A2)
    obtain ⟨_, s4, a4⟩ := TaintRun.s_setA (E := E) (F := F) hv A2 _ s3 _ _ h4
    obtain ⟨_, s5, a5⟩ := TaintRun.s_tick (E := E) (F := F) (Nat.le_refl 5) (Nat.le_refl 5) A3 _ s4 _ _ h2
    have h9 := TaintRun.tick_adv s4 h2
    have e : go ((opLDA mIzyR) >>= fun _ => tick 5) { m with pc := m.pc + 1 } = go (tick 5) (go (setA (readVal m)) (go (rd (readAddr m)) (go mIzyR { m with pc := m.pc + 1 }).2).2).2 := by
      rw [go_bind]
      have e2 : go (opLDA mIzyR) { m with pc := m.pc + 1 } = go (mIzyR >>= fun ad => rd ad >>= fun v => setA v) { m with pc := m.pc + 1 } := rfl
      rw [e2, go_bind, go_bind]
      rfl
    rw [e]
    refine ⟨s5, TaintRun.steprel_same hs s5 ?_ ?_⟩
    · exact a5.1.trans (a4.1.trans (a3.1.trans a2.1))
    · rw [h9]
      have b1 := a4.2
      have b2 := a3.2
      have b3 := a2.2
      have b4 : ({ m with pc := m.pc + 1 } : Machine).fdot = m.fdot := rfl
      omega

/-- a byte of the RAM with no known bits may take any value -/
theorem sim_wr {A : AS} {m : Machine} {i : Nat} (v : UInt8) (hE : E.D = []) (hk : A.kn.get! i = 0) (hr : A.rk = false) (hs : Sim E F A m) :
    Sim E F A { m with ram := m.ram.set! i v } := by
  refine { hs with
    size := by show (m.ram.set! i v).size = 2048; rw [ba_size_set]; exact hs.size
    ram := ?_
    dg := ?_
    rkv := ?_ }
  · intro j hj
    show (A.getK j).mem ((m.ram.set! i v).get! j)
    by_cases h : i = j
    · subst h
      rw [ba_get_set_self _ _ _ (by rw [hs.size]; exact hj)]
      show v &&& A.kn.get! i = A.ram.get! i &&& A.kn.get! i
      rw [hk]
      apply bt_ext
      intro b hb
      rw [bt_and, bt_and, bt_zero hb, Bool.and_false, Bool.and_false]
    · rw [ba_get_set_ne _ _ _ _ h]
      exact hs.ram j hj
  · intro hd
    have := hs.dg hd
    rw [hE] at this
    exact absurd this (by simp)
  · intro h
    rw [hr] at h
    cases h

theorem s_writeStep {A : AS} {m : Machine} {B : AS} (hE : E.D = []) (hs : Sim E F A m) (hn : A.nmi = false) (hp : 0x8000 ≤ A.pc)
    (hop : E.prg.get! (A.pc &&& E.mask).toNat = 0x91) (hr : A.rk = false) (had : writeAddr m < 0x2000) (hk : A.kn.get! (writeAddr m &&& 0x7FF).toNat = 0) (hB : writeStep E A = some B) :
    Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  have hn2 : m.nmiPending = false := by rw [hs.nmi]; exact hn
  have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
  have hop2 : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91 := by rw [hs.prg, hs.mask, hs.pc]; exact hop
  rw [step_at hn2 hs.halted hpm hop2 (by decide), op_91, cyc_91]
  have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
    pc := by
      show m.pc + 1 = A.pc + 1
      rw [hs.pc] }
  unfold writeStep at hB
  cases he : (aPtrW E >>= fun _ => atick 6 6) { A with pc := A.pc + 1 } with
  | none =>
    rw [he] at hB
    cases hB
  | some p =>
    rw [he] at hB
    obtain ⟨u, B1⟩ := p
    have hB1 : B1 = B := Option.some.inj hB
    subst hB1
    obtain ⟨_, A2, h1, h2⟩ := abind_some he
    obtain ⟨_, s2, a2⟩ := s_ptrW (E := E) (F := F) _ _ hs1 _ _ h1
    -- the state after the operand has the same bytes
    have hA2 : A2.kn = A.kn ∧ A2.rk = A.rk := by
      unfold aPtrW afetch at h1
      simp only [bind, StateT.bind] at h1
      split at h1
      · have h5 := TaintRun.some_pair h1
        rw [← h5.2]
        exact ⟨rfl, rfl⟩
      · cases h1
    have hk2 : A2.kn.get! (writeAddr m &&& 0x7FF).toNat = 0 := by rw [hA2.1]; exact hk
    generalize hm2 : (go mIzy { m with pc := m.pc + 1 }).2 = m2 at s2 a2
    have e : go ((opSTA mIzy) >>= fun _ => tick 6) { m with pc := m.pc + 1 } = go (tick 6) (go (wr (writeAddr m) m2.a) m2).2 := by
      rw [go_bind]
      have e2 : go (opSTA mIzy) { m with pc := m.pc + 1 } = go (mIzy >>= fun ad => (MonadState.get : M Machine) >>= fun t => wr ad t.a) { m with pc := m.pc + 1 } := rfl
      rw [e2, go_bind, hm2]
      rfl
    have s3 := sim_wr (E := E) (F := F) (i := (writeAddr m &&& 0x7FF).toNat) m2.a hE hk2 (by rw [hA2.2]; exact hr) s2
    have e3 : (go (wr (writeAddr m) m2.a) m2).2 = { m2 with ram := m2.ram.set! (writeAddr m &&& 0x7FF).toNat m2.a } := by
      rw [TaintRun.wr_ram _ had s2.trk]
    rw [e, e3]
    have b1 : ({ m2 with ram := m2.ram.set! (writeAddr m &&& 0x7FF).toNat m2.a } : Machine).frame = m2.frame := rfl
    have b5 : ({ m2 with ram := m2.ram.set! (writeAddr m &&& 0x7FF).toNat m2.a } : Machine).fdot = m2.fdot := rfl
    generalize ({ m2 with ram := m2.ram.set! (writeAddr m &&& 0x7FF).toNat m2.a } : Machine) = M3 at s3 b1 b5 ⊢
    obtain ⟨_, s5, a5⟩ := TaintRun.s_tick (E := E) (F := F) (Nat.le_refl 6) (Nat.le_refl 6) A2 _ s3 _ _ h2
    have h9 := TaintRun.tick_adv s3 h2
    have b2 : ({ m with pc := m.pc + 1 } : Machine).frame = m.frame := rfl
    have b4 : ({ m with pc := m.pc + 1 } : Machine).fdot = m.fdot := rfl
    have b3 := a2.2
    have c1 := a2.1
    rw [b2] at c1
    rw [b4] at b3
    refine ⟨s5, TaintRun.steprel_same hs s5 ?_ ?_⟩
    · exact a5.1.trans (b1.trans c1)
    · rw [h9, b5]
      omega

end

/-! ## The conditions on one frame -/

/-- the places and bytes that the conditions name -/
structure Places where
  /-- the idle loop -/
  idle : UInt16
  /-- no instruction of the handler comes after this dot -/
  late : Nat
  /-- the read of the block buffer routine -/
  read : UInt16
  /-- the byte where the routine keeps its offset, and the offsets of the head -/
  saveI : Nat
  heads : List UInt8
  /-- the tiles that a read may give, and those that a read for the head may give -/
  tiles : List UInt8
  headTiles : List UInt8
  /-- the write that erases a coin, and the bytes of the block buffers -/
  erase : UInt16
  bufLo : Nat
  bufN : Nat
  /-- the offset of the screen's buffer, and the places that use it as an index -/
  offI : Nat
  offAt : List UInt16
  /-- the position, and the place where the side pipe's code reads it -/
  xI : Nat
  xAt : UInt16
  /-- the bytes of the result: the page, the lock, the routine, the timer -/
  pageI : Nat
  lockI : Nat
  rtI : Nat
  timerI : Nat
  /-- the pipe's routine and the long timer -/
  eng : UInt8
  long : UInt8
  /-- the player's state, and the place where the side pipe's code reads it -/
  stI : Nat
  stAt : UInt16
  /-- the player's height on the screen, and the place where the collision routine reads it -/
  hpI : Nat
  hpAt : UInt16
  deriving Inhabited

/-- **What stays assumed about one instruction of a frame.** -/
structure SiteOK (P : Places) (m : Machine) : Prop where
  /-- the handler is done before the frame's end -/
  late : m.pc ≠ P.idle → m.fdot ≤ P.late
  /-- an `LDA (zp),Y` reads RAM or ROM -/
  reads : 0x8000 ≤ m.pc → m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 → RamRom (readAddr m)
  /-- the block buffer routine reads a tile of the list -/
  read : m.pc = P.read → readVal m ∈ P.tiles ∧ (m.ram.get! P.saveI ∈ P.heads → readVal m ∈ P.headTiles)
  /-- the coin is erased in the block buffers -/
  erase : m.pc = P.erase → writeAddr m < 0x2000 ∧ P.bufLo ≤ (writeAddr m &&& 0x7FF).toNat ∧ (writeAddr m &&& 0x7FF).toNat < P.bufLo + P.bufN
  /-- the screen's buffer is not full -/
  off : m.pc ∈ P.offAt → (m.ram.get! P.offI).toNat < 64
  /-- the position's low bits are not zero when the side pipe's code reads them -/
  xbit : m.pc = P.xAt → m.ram.get! P.xI &&& 0x0F ≠ 0

/-! ## The walk -/

/-- the dot is at most `late`, away from the idle loop -/
def clampS (P : Places) (A : AS) : AS :=
  if A.pc != P.idle && decide (P.late < A.hi) then { A with hi := P.late } else A

/-- the pieces before a step. At the places that use the screen buffer's offset: its values below 64. At the side pipe's read of the position: a set low bit. At the side pipe's read
of the player's state: its two low bits. At the collision routine's read of the player's height on the screen: all its bits. -/
def preS (P : Places) (A : AS) : List AS :=
  if P.offAt.contains A.pc then PipeEntryRule.splitAll P.offI (A.setK P.offI ((A.getK P.offI).and (AB.known 0x3F)))
  else if A.pc == P.xAt then [1, 2, 4, 8].map fun b => A.setK P.xI ((A.getK P.xI).or (AB.known b))
  else if A.pc == P.stAt then (TaintRun.splitBit P.stI 1 A).flatMap (TaintRun.splitBit P.stI 2)
  else if A.pc == P.hpAt then PipeEntryRule.splitAll P.hpI A
  else [A]

/-- the tiles of a read -/
def tilesFor (P : Places) (A : AS) : List UInt8 :=
  let sv := A.getK P.saveI
  if sv.isK && P.heads.contains sv.v then P.headTiles else P.tiles

/-- no byte of the block buffers has a known bit -/
def bufFree (P : Places) (A : AS) : Bool := (List.range P.bufN).all fun j => A.kn.get! (P.bufLo + j) == 0

/-- the operand of the instruction is a zero page pointer that is not known -/
def ptrNotKnown (E : Env) (A : AS) : Bool :=
  let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
  !((A.getK z.toNat).isK && (A.getK (z + 1).toNat).isK)

/-- a step: the machine's own, or a step through a pointer not known -/
def stepS (P : Places) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if A.nmi then succs E ops A
  else if A.pc == P.read then (tilesFor P A).map fun v => readStep E (AB.known v) A
  else if A.pc == P.erase then [if bufFree P A && !A.rk then writeStep E A else none]
  else if decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1 && ptrNotKnown E A then [readStep E AB.top A]
  else succs E ops A

/-- the table and what the check uses -/
structure CfgS where
  E : Env
  ops : Array (AM Unit)
  P : Places
  /-- at the frame's end -/
  fin : AS → Bool
  /-- the states of the table -/
  t : Array AS
  /-- the table's key of a state, candidates for a key, and the program counters with states: no part of the proof -/
  key : AS → Nat
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray
  /-- what a state forgets at some program counters: no part of the proof, since the walk checks that it only forgets -/
  norm : AS → AS
  normAt : ByteArray

def coverS (C : CfgS) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D
    | none => false

/-- the state, with what it may forget at this program counter -/
def weaken (C : CfgS) (B : AS) : AS :=
  if C.normAt.get! B.pc.toNat != 0 && B.le (C.norm B) then C.norm B else B

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def walkS (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preS C.P (clampS C.P A)).all fun A₁ => (stepS C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkS C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-! ## The walk covers the machine -/

section
variable {E : Env} {F : Nat × UInt8} {P : Places}

/-- what the places must be, on the ROM -/
structure PlacesOK (E : Env) (P : Places) : Prop where
  late : P.late < dotsPerFrame
  read : 0x8000 ≤ P.read ∧ E.prg.get! (P.read &&& E.mask).toNat = 0xB1
  erase : 0x8000 ≤ P.erase ∧ E.prg.get! (P.erase &&& E.mask).toNat = 0x91
  offI : P.offI < 2048
  xI : P.xI < 2048
  saveI : P.saveI < 2048
  stI : P.stI < 2048
  hpI : P.hpI < 2048
  noD : E.D = []

theorem sim_clamp {A : AS} {m : Machine} (hP : P.late < dotsPerFrame) (hs : Sim E F A m) (hh : m.pc ≠ P.idle → m.fdot ≤ P.late) : Sim E F (clampS P A) m := by
  unfold clampS
  split
  · rename_i hc
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hc
    have h1 : m.pc ≠ P.idle := by rw [hs.pc]; exact hc.1
    exact { hs with hi := hh h1, lim := hP }
  · exact hs

theorem clamp_k (A : AS) : (clampS P A).k = A.k := by
  unfold clampS
  split <;> rfl

theorem clamp_pc (A : AS) : (clampS P A).pc = A.pc := by
  unfold clampS
  split <;> rfl

set_option maxRecDepth 100000 in
theorem or_bit_all : ((List.range 256).all fun n => (n.toUInt8 &&& 0x0F == 0) || ([1, 2, 4, 8] : List UInt8).any fun b => (n.toUInt8 ||| b) == n.toUInt8) = true := by decide

set_option maxRecDepth 100000 in
theorem and3F_all : ((List.range 64).all fun n => n.toUInt8 &&& 0x3F == n.toUInt8) = true := by decide

theorem or_bit_of {x : UInt8} (h : x &&& 0x0F ≠ 0) : ∃ b ∈ ([1, 2, 4, 8] : List UInt8), (x ||| b) = x := by
  have h1 := List.all_eq_true.1 or_bit_all x.toNat (List.mem_range.2 x.toNat_lt)
  have e : x.toNat.toUInt8 = x := by simp
  rw [e] at h1
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h1
  rcases h1 with h2 | ⟨b, hb, h2⟩
  · exact absurd h2 h
  · exact ⟨b, hb, h2⟩

theorem and3F {x : UInt8} (h : x.toNat < 64) : x &&& 0x3F = x := by
  have h1 := List.all_eq_true.1 and3F_all x.toNat (List.mem_range.2 h)
  have e : x.toNat.toUInt8 = x := by simp
  rw [e] at h1
  exact beq_iff_eq.1 h1

theorem cov_preS (hO : PlacesOK E P) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK P m) : ∃ B ∈ preS P A, Sim E F B m ∧ B.k = A.k := by
  unfold preS
  by_cases h1 : P.offAt.contains A.pc = true
  · rw [if_pos h1]
    have hpc : m.pc ∈ P.offAt := by rw [hs.pc]; exact List.mem_of_elem_eq_true h1
    have hlt := hh.off hpc
    have hv : ((A.getK P.offI).and (AB.known 0x3F)).mem (m.ram.get! P.offI) := by
      have := TaintRun.mem_and (hs.ram _ hO.offI) (mem_known_self (0x3F : UInt8))
      rwa [and3F hlt] at this
    have hs2 := PipeEntryRule.sim_setK' hs hv
    obtain ⟨B, h2, h3, h4⟩ := PipeEntryRule.cov_all hO.offI _ m hs2
    exact ⟨B, h2, h3, h4⟩
  · rw [if_neg h1]
    by_cases h2 : (A.pc == P.xAt) = true
    · rw [if_pos h2]
      have hpc : m.pc = P.xAt := by rw [hs.pc]; exact beq_iff_eq.1 h2
      obtain ⟨b, hb, he⟩ := or_bit_of (hh.xbit hpc)
      refine ⟨_, List.mem_map.2 ⟨b, hb, rfl⟩, ?_, rfl⟩
      apply PipeEntryRule.sim_setK' hs
      have := TaintRun.mem_or (hs.ram _ hO.xI) (mem_known_self b)
      rwa [he] at this
    · rw [if_neg h2]
      by_cases h3 : (A.pc == P.stAt) = true
      · rw [if_pos h3]
        have c1 : TaintRun.Cov E F (TaintRun.splitBit P.stI 1) := TaintRun.cov_bit hO.stI (by decide)
        have c2 : TaintRun.Cov E F (TaintRun.splitBit P.stI 2) := TaintRun.cov_bit hO.stI (by decide)
        obtain ⟨B, hB, hs1, hk1⟩ := c1 A m hs
        obtain ⟨D, hD, hs2, hk2⟩ := c2 B m hs1
        exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, hs2, hk2.trans hk1⟩
      · rw [if_neg h3]
        by_cases h4 : (A.pc == P.hpAt) = true
        · rw [if_pos h4]
          exact PipeEntryRule.cov_all hO.hpI A m hs
        · rw [if_neg h4]
          exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem mem_tilesFor {A : AS} {m : Machine} {x : UInt8} (hO : PlacesOK E P) (hs : Sim E F A m) (h1 : x ∈ P.tiles) (h2 : m.ram.get! P.saveI ∈ P.heads → x ∈ P.headTiles) : x ∈ tilesFor P A := by
  unfold tilesFor
  simp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    apply h2
    have e := PipeEntryRule.known_eq hc.1 (hs.ram _ hO.saveI)
    rw [e]
    exact List.mem_of_elem_eq_true hc.2
  · exact h1

theorem s_stepS {ops : Array (AM Unit)} (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK P m) :
    ∃ r ∈ stepS P E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold stepS
  by_cases hn : A.nmi = true
  · rw [if_pos hn]
    exact s_succs hops hT hs
  · rw [if_neg hn]
    have hn' : A.nmi = false := by simpa using hn
    have hreads : 0x8000 ≤ A.pc → E.prg.get! (A.pc &&& E.mask).toNat = 0xB1 → RamRom (readAddr m) := by
      intro g1 g2
      exact hh.reads (by rw [hs.pc]; exact g1) (by rw [hs.prg, hs.mask, hs.pc]; exact g2)
    by_cases h1 : (A.pc == P.read) = true
    · rw [if_pos h1]
      have hpc : A.pc = P.read := beq_iff_eq.1 h1
      have hm : m.pc = P.read := by rw [hs.pc]; exact hpc
      obtain ⟨h3, h4⟩ := hh.read hm
      have g1 : 0x8000 ≤ A.pc := by rw [hpc]; exact hO.read.1
      have g2 : E.prg.get! (A.pc &&& E.mask).toNat = 0xB1 := by rw [hpc]; exact hO.read.2
      refine ⟨_, List.mem_map.2 ⟨readVal m, mem_tilesFor hO hs h3 h4, rfl⟩, fun B hB => ?_⟩
      exact s_readStep hs hn' g1 g2 (hreads g1 g2) (mem_known_self _) hB
    · rw [if_neg h1]
      by_cases h3 : (A.pc == P.erase) = true
      · rw [if_pos h3]
        have hpc : A.pc = P.erase := beq_iff_eq.1 h3
        have hm : m.pc = P.erase := by rw [hs.pc]; exact hpc
        refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
        split at hB
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          obtain ⟨g1, g2, g3⟩ := hh.erase hm
          have hk : A.kn.get! (writeAddr m &&& 0x7FF).toNat = 0 := by
            have h5 := List.all_eq_true.1 hc.1 ((writeAddr m &&& 0x7FF).toNat - P.bufLo) (List.mem_range.2 (by omega))
            have h6 : P.bufLo + ((writeAddr m &&& 0x7FF).toNat - P.bufLo) = (writeAddr m &&& 0x7FF).toNat := by omega
            rw [h6] at h5
            exact beq_iff_eq.1 h5
          exact s_writeStep hO.noD hs hn' (by rw [hpc]; exact hO.erase.1) (by rw [hpc]; exact hO.erase.2) hc.2 g1 hk hB
        · cases hB
      · rw [if_neg h3]
        by_cases h2 : (decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1 && ptrNotKnown E A) = true
        · rw [if_pos h2]
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
          obtain ⟨⟨g1, g2⟩, _⟩ := h2
          refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
          exact s_readStep hs hn' g1 g2 (hreads g1 g2) (mem_top _) hB
        · rw [if_neg h2]
          exact s_succs hops hT hs

end

section
variable {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveS (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkS C n A = true

theorem cover_liveS (ht : C.t.all (walkS C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ D, LiveS C F D m ∧ D.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

theorem live_stepS (hO : PlacesOK C.E C.P) (ht : C.t.all (walkS C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveS C F A m)
    (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) :
    (∃ A', LiveS C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkS] at hw
  | succ n =>
    have hs0 := sim_clamp hO.late hs hh.late
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preS hO hs0 hh
    obtain ⟨r, hr, hB⟩ := s_stepS hO hops hT hs1 hh
    simp only [walkS, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    have hkA : A₁.k = A.k := by rw [hk1, clamp_k]
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hkA] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        have hN : Sim C.E F (weaken C B) (go step m).2 ∧ (weaken C B).k = B.k := by
          unfold weaken
          split
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            have h5 := sim_le hc.2 h1
            refine ⟨h5, ?_⟩
            have hle := hc.2
            simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
            exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
          · exact ⟨h1, rfl⟩
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveS ht (sim_clamp hO.late hN.1 hh2.late) h3
          exact ⟨D, hD, by rw [hk, clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S`, for every input, if each instruction meets `SiteOK`. -/
theorem frame_of_walkS (hO : PlacesOK C.E C.P) (ht : C.t.all (walkS C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkS C Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, SiteOK C.P (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveS C F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hk (j + 1)
        rw [e2] at hh2 ⊢
        rcases live_stepS hO ht hops hT h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3, h4⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h3, h4⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact ⟨h1, B, h2, h3, h4⟩

end

/-! ## The state at a frame's start -/

/-- the known bits as a mask -/
def maskOf (K : List (Nat × UInt8)) : ByteArray := K.foldl (fun b p => b.set! p.1 p.2) (ByteArray.mk (Array.replicate 2048 0))

/-- the abstract state at a frame's start, from the reference machine `r`, for dot 0 (`low`) or dots `1..9`. The bits `K` are known. -/
def startR (r : Machine) (K : List (Nat × UInt8)) (low : Bool) : AS :=
  { a := AB.top, x := AB.top, y := AB.top, s := r.s, p := AB.top, pc := r.pc, ram := r.ram, kn := maskOf K, ppuCtrl := ⟨0x80, 0x80⟩, ppuMask := AB.top,
    vb := !low, nmi := !low, lo := if low then 0 else 1, hi := if low then 0 else 9, padShift := AB.top, strobe := false, dg := false, k := 0, rk := false, spent := false }

def startsR (r : Machine) (K : List (Nat × UInt8)) : List AS := [startR r K true, startR r K false]

/-- **The condition on the state at a frame's start in the room.** The frame before ended in the idle loop, and the listed bits are those of the reference machine. All other bytes are free. -/
structure RoomCond (E : Env) (r : Machine) (K : List (Nat × UInt8)) (m : Machine) : Prop where
  dot : m.fdot < 10
  flags : (m.fdot = 0 ∧ m.vblank = false ∧ m.nmiPending = false) ∨ (1 ≤ m.fdot ∧ m.vblank = true ∧ m.nmiPending = true)
  s0 : m.sprite0 = true
  ctrl : m.ppuCtrl &&& 0x80 = 0x80
  strobe : m.padStrobe = false
  halted : m.halted = false
  trk : m.trk = false
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  size : m.ram.size = 2048
  pc : m.pc = r.pc
  s : m.s = r.s
  bytes : ∀ p ∈ K, m.ram.get! p.1 &&& p.2 = r.ram.get! p.1 &&& p.2

/-- `RoomCond` as a check, for a program -/
def roomOK (E : Env) (r : Machine) (K : List (Nat × UInt8)) (m : Machine) : Bool :=
  decide (m.fdot < 10) && ((m.fdot == 0 && !m.vblank && !m.nmiPending) || (decide (1 ≤ m.fdot) && m.vblank && m.nmiPending)) && m.sprite0 &&
  m.ppuCtrl &&& 0x80 == 0x80 && !m.padStrobe && !m.halted && !m.trk && decide (m.prg.data = E.prg.data) && m.prgMask == E.mask && m.ram.size == 2048 &&
  m.pc == r.pc && m.s == r.s && K.all fun p => m.ram.get! p.1 &&& p.2 == r.ram.get! p.1 &&& p.2

/-- the mask is what the list says -/
def maskOK (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  r.ram.size == 2048 && (maskOf K).size == 2048 && K.all (fun p => decide (p.1 < 2048) && (maskOf K).get! p.1 == p.2) &&
    (List.range 2048).all fun i => (maskOf K).get! i == 0 || K.any fun p => p.1 == i

section
variable {E : Env} {r : Machine} {K : List (Nat × UInt8)}

structure MaskOK (r : Machine) (K : List (Nat × UInt8)) : Prop where
  szR : r.ram.size = 2048
  szK : (maskOf K).size = 2048
  listed : ∀ p ∈ K, p.1 < 2048 ∧ (maskOf K).get! p.1 = p.2
  rest : ∀ i, i < 2048 → (maskOf K).get! i = 0 ∨ ∃ p ∈ K, p.1 = i

theorem maskOK_spec (h : maskOK r K = true) : MaskOK r K := by
  simp only [maskOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun i hi => h4 i (List.mem_range.2 hi)⟩

/-- the state at a frame's start covers the machine -/
theorem sim_of_room (hM : MaskOK r K) (hp : E.pad = AB.top) {F : Nat × UInt8} {m : Machine} (h : RoomCond E r K m) (hfr : m.frame = F.1) :
    ∃ S ∈ startsR r K, Sim E F S m := by
  have key : ∀ low : Bool, (low = true ↔ m.fdot = 0) → Sim E F (startR r K low) m := by
    intro low hl
    have hvb : m.vblank = !low ∧ m.nmiPending = !low := by
      rcases h.flags with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
      · have : low = true := hl.2 a1
        subst this
        exact ⟨a2, a3⟩
      · have : low = false := by
          cases low with
          | false => rfl
          | true =>
            have := hl.1 rfl
            omega
        subst this
        exact ⟨a2, a3⟩
    have hlo : (if low = true then 0 else 1) ≤ m.fdot := by
      cases low with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have : m.fdot ≠ 0 := fun h0 => by
          have := hl.2 h0
          cases this
        omega
    have hhi : m.fdot ≤ (if low = true then 0 else 9) := by
      have hd := h.dot
      cases low with
      | true =>
        have := hl.1 rfl
        simp only [if_true]
        omega
      | false =>
        simp only [Bool.false_eq_true, if_false]
        omega
    refine ⟨mem_top _, mem_top _, mem_top _, mem_top _, h.s, h.pc, h.prg, h.mask, ?_, mem_top _, hvb.1, hvb.2, ?_, hlo, hhi, ?_, by rw [hp]; exact mem_top _, mem_top _, h.strobe, h.halted, h.trk, h.size, ?_, ?_, hM.szR, hM.szK, ?_, ?_⟩
    · show m.ppuCtrl &&& 0x80 = (0x80 : UInt8) &&& 0x80
      rw [h.ctrl]
      decide
    · rw [h.s0]
      have : m.fdot ≤ 9 := by have := h.dot; omega
      exact (s0f_small this).symm
    · show (if low = true then 0 else 9) < dotsPerFrame
      split <;> decide
    · intro i hi
      show AB.mem ⟨r.ram.get! i, (maskOf K).get! i⟩ (m.ram.get! i)
      rcases hM.rest i hi with h5 | ⟨p, hp1, h6⟩
      · show m.ram.get! i &&& (maskOf K).get! i = r.ram.get! i &&& (maskOf K).get! i
        rw [h5]
        apply bt_ext
        intro j hj
        rw [bt_and, bt_and, bt_zero hj, Bool.and_false, Bool.and_false]
      · subst h6
        have h7 := (hM.listed p hp1).2
        show m.ram.get! p.1 &&& (maskOf K).get! p.1 = r.ram.get! p.1 &&& (maskOf K).get! p.1
        rw [h7]
        exact h.bytes p hp1
    · intro hd
      cases hd
    · show m.frame = F.1 + 0
      rw [hfr]
      rfl
    · intro hd
      cases hd
  by_cases hd : m.fdot = 0
  · exact ⟨_, List.mem_cons_self, key true ⟨fun _ => hd, fun _ => rfl⟩⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), key false ⟨fun h0 => (by cases h0), fun h0 => absurd h0 hd⟩⟩

/-- a machine in a start state meets the condition -/
theorem room_of_sim (hM : MaskOK r K) {F : Nat × UInt8} {S : AS} {m : Machine} (hS : S ∈ startsR r K) (hs : Sim E F S m) : RoomCond E r K m := by
  have common : ∀ low : Bool, S = startR r K low → RoomCond E r K m := by
    intro low he
    subst he
    have hlo : (if low = true then 0 else 1) ≤ m.fdot := hs.lo
    have hhi : m.fdot ≤ (if low = true then 0 else 9) := hs.hi
    have hv : m.vblank = !low := hs.vb
    have hn : m.nmiPending = !low := hs.nmi
    have h9 : m.fdot ≤ 9 := by
      cases low with
      | true => simp only [if_true] at hhi; omega
      | false => simp only [Bool.false_eq_true, if_false] at hhi; exact hhi
    refine ⟨by omega, ?_, ?_, ?_, hs.strobe, hs.halted, hs.trk, hs.prg, hs.mask, hs.size, hs.pc, hs.s, ?_⟩
    · cases low with
      | true =>
        left
        simp only [if_true] at hhi
        exact ⟨by omega, hv, hn⟩
      | false =>
        right
        simp only [Bool.false_eq_true, if_false] at hlo
        exact ⟨hlo, hv, hn⟩
    · rw [hs.s0]
      exact s0f_small h9
    · have h1 : m.ppuCtrl &&& 0x80 = (0x80 : UInt8) &&& 0x80 := hs.ppuCtrl
      rw [h1]
      decide
    · intro p hp
      have h1 := hM.listed p hp
      have h2 : m.ram.get! p.1 &&& (maskOf K).get! p.1 = r.ram.get! p.1 &&& (maskOf K).get! p.1 := hs.ram p.1 h1.1
      rwa [h1.2] at h2
  simp only [startsR, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with h | h
  · exact common _ h
  · exact common _ h

end

/-! ## What a frame leaves -/

/-- the frame's end is under a start state of the condition for `r` and `K` -/
def endUnder (r : Machine) (K : List (Nat × UInt8)) (B : AS) : Bool := (startsR r K).any (fun S => ({ B with k := 0 } : AS).le S)

/-- at the frame's end: a start state; or the page and the lock are those of the reference machine and another routine runs, and if it is the pipe's, the timer is the long one and the end is
under a start state of each reference `W` of the entry -/
def finR (P : Places) (r : Machine) (K : List (Nat × UInt8)) (W : List (Machine × List (Nat × UInt8))) (B : AS) : Bool :=
  endUnder r K B ||
  (knownIs B (P.pageI, r.ram.get! P.pageI) && knownIs B (P.lockI, r.ram.get! P.lockI) && decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI &&
    ((B.getK P.rtI).v != P.eng || (knownIs B (P.timerI, P.long) && W.all fun w => endUnder w.1 w.2 B)))

/-- **What a frame leaves when it leaves the condition.** If it enters the pipe, the state meets the condition of each reference `W` of the entry. -/
structure Leaves (E : Env) (P : Places) (r : Machine) (W : List (Machine × List (Nat × UInt8))) (m : Machine) : Prop where
  page : m.ram.get! P.pageI = r.ram.get! P.pageI
  lock : m.ram.get! P.lockI = r.ram.get! P.lockI
  other : m.ram.get! P.rtI ≠ r.ram.get! P.rtI
  long : m.ram.get! P.rtI = P.eng → m.ram.get! P.timerI = P.long
  entry : m.ram.get! P.rtI = P.eng → ∀ w ∈ W, RoomCond E w.1 w.2 m

/-- what the check says -/
structure RoomOK (E : Env) (P : Places) (r : Machine) (K : List (Nat × UInt8)) (W : List (Machine × List (Nat × UInt8))) (C : CfgS) (Fu : Nat) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  mask : MaskOK r K
  masks : ∀ w ∈ W, MaskOK w.1 w.2
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = finR P r K W
  table : C.t.all (walkS C Fu) = true
  starts : ∀ S ∈ startsR r K, walkS C Fu S = true

/-- a frame's end under a start state meets the condition -/
theorem room_of_end {E : Env} {r : Machine} {K : List (Nat × UInt8)} (hM : MaskOK r K) {B : AS} {m : Machine} {f : Nat} (hs : Sim E (f, 2) B m) (h : endUnder r K B = true) :
    RoomCond E r K m := by
  simp only [endUnder, List.any_eq_true] at h
  obtain ⟨D, hD, hle⟩ := h
  have hs2 : Sim E (m.frame, 2) ({ B with k := 0 } : AS) m := { hs with fr := rfl }
  exact room_of_sim hM hD (sim_le hle hs2)

/-- **One frame in the room.** -/
theorem room_step {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {W : List (Machine × List (Nat × UInt8))} {C : CfgS} {Fu : Nat} (h : RoomOK E P r K W C Fu)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) : RoomCond E r K (frame m i) ∨ Leaves E P r W (frame m i) := by
  obtain ⟨S, hS, hs⟩ := sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S hS
  have hs' : Sim C.E (m.frame, 2) S m := by rw [h.env]; exact hs
  obtain ⟨h1, B, h2, h3, h4⟩ := frame_of_walkS (i := i) hO h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) hw hs' (by rw [h.pl]; exact hk)
  rw [h.env] at h4
  rw [h.fin] at h2
  unfold finR at h2
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, List.all_eq_true] at h2
  rcases h2 with h2 | ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩
  · left
    exact room_of_end h.mask h4 h2
  · right
    have e := PipeEntryRule.known_eq a4 (h4.ram _ a3)
    refine ⟨sim_known h4 a1, sim_known h4 a2, ?_, ?_, ?_⟩
    · rw [e]
      exact a5
    · intro hq
      rw [e] at hq
      rcases a6 with a7 | a7
      · exact absurd hq a7
      · exact sim_known h4 a7.1
    · intro hq w hw
      rw [e] at hq
      rcases a6 with a7 | a7
      · exact absurd hq a7
      · exact room_of_end (h.masks w hw) h4 (a7.2 w hw)

/-- **Every frame from the start in the room up to the entry.** `seq` lists the frames of a run. The state at frame `c` meets the condition. Each frame before `e` meets `SiteOK` on each instruction and
starts in the player's routine. `e` has the pipe's routine. Then every frame before `e` starts in the condition, and the frame before `e` leaves it as `Leaves` says. -/
theorem room_leaves {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {W : List (Machine × List (Nat × UInt8))} {C : CfgS} {Fu : Nat} (h : RoomOK E P r K W C Fu)
    (hrt : (P.rtI, (0xFF : UInt8)) ∈ K) (hne : r.ram.get! P.rtI ≠ P.eng)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (hce : c ≤ e)
    (h0 : RoomCond E r K (seq c))
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK P (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! P.rtI = r.ram.get! P.rtI)
    (he : (seq e).ram.get! P.rtI = P.eng) :
    (∀ n, c ≤ n → n < e → RoomCond E r K (seq n)) ∧ Leaves E P r W (seq e) := by
  have rtOf : ∀ {m : Machine}, RoomCond E r K m → m.ram.get! P.rtI = r.ram.get! P.rtI := by
    intro m hm
    have := hm.bytes _ hrt
    simp only at this
    have e1 : ∀ x : UInt8, x &&& 0xFF = x := fun x => by
      apply bt_ext
      intro j hj
      rw [bt_and, TaintRun.bt_ff hj, Bool.and_true]
    rwa [e1, e1] at this
  have key : ∀ d, c + d ≤ e → RoomCond E r K (seq (c + d)) ∨ (c + d = e ∧ Leaves E P r W (seq e)) := by
    intro d
    induction d with
    | zero => exact fun _ => Or.inl h0
    | succ d ih =>
      intro hd
      have e1 : c + (d + 1) = c + d + 1 := rfl
      rcases ih (by omega) with h1 | ⟨h1, _⟩
      · have h2 := room_step h h1 (hs (c + d) (by omega) (by omega))
        rw [← next, ← e1] at h2
        rcases h2 with h3 | h3
        · exact Or.inl h3
        · right
          by_cases h4 : c + (d + 1) = e
          · exact ⟨h4, by rw [← h4]; exact h3⟩
          · exfalso
            exact h3.other (hr (c + (d + 1)) (by omega) (by omega))
      · omega
  constructor
  · intro n h1 h2
    obtain ⟨d, rfl⟩ : ∃ d, n = c + d := ⟨n - c, by omega⟩
    rcases key d (by omega) with h3 | ⟨h3, _⟩
    · exact h3
    · omega
  · obtain ⟨d, hd⟩ : ∃ d, e = c + d := ⟨e - c, by omega⟩
    rcases key d (by omega) with h3 | ⟨_, h3⟩
    · exfalso
      rw [← hd] at h3
      have := rtOf h3
      rw [he] at this
      exact hne this.symm
    · exact h3

/-- **Every frame from the start in the room up to the entry**: the frames before `e` start in the condition, and the timer at `e` is the long one. -/
theorem room_run {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {W : List (Machine × List (Nat × UInt8))} {C : CfgS} {Fu : Nat} (h : RoomOK E P r K W C Fu)
    (hrt : (P.rtI, (0xFF : UInt8)) ∈ K) (hne : r.ram.get! P.rtI ≠ P.eng)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (hce : c ≤ e)
    (h0 : RoomCond E r K (seq c))
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK P (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! P.rtI = r.ram.get! P.rtI)
    (he : (seq e).ram.get! P.rtI = P.eng) :
    (∀ n, c ≤ n → n < e → RoomCond E r K (seq n)) ∧ (seq e).ram.get! P.timerI = P.long ∧ (seq e).ram.get! P.pageI = r.ram.get! P.pageI ∧ (seq e).ram.get! P.lockI = r.ram.get! P.lockI := by
  obtain ⟨h1, h3⟩ := room_leaves h hrt hne next hce h0 hs hr he
  exact ⟨h1, h3.long he, h3.page, h3.lock⟩

/-! ## Finding the table: a search, no part of the proof -/

/-- what the search forgets, and what it keeps apart -/
structure Aids where
  /-- the bytes that keep states apart -/
  keep : List Nat
  /-- the temporary bytes -/
  temps : List Nat
  first : Nat
  /-- places where the registers are forgotten -/
  regs : List UInt16
  /-- places where the temporaries are forgotten; at `sideA`, `sideB` the first one stays; at `sideA` also Y -/
  ends : List UInt16
  sideA : UInt16
  sideB : UInt16
  /-- the return of the collision routine -/
  colEnd : UInt16
  /-- returns where A and Y, and X and the temporaries, are dead -/
  cutAY : List UInt16
  cutX : List UInt16
  /-- places where the accumulator keeps states apart -/
  aAt : List UInt16
  aLo : UInt16
  aHi : UInt16
  /-- the ranges where the buffer's offset keeps states apart -/
  offR : List (UInt16 × UInt16)
  offI : Nat
  deriving Inhabited

def Aids.norm (Z : Aids) (A : AS) : AS :=
  let forget := fun (l : List Nat) (B : AS) => l.foldl (fun C i => C.setK i AB.top) B
  let A := if Z.cutAY.contains A.pc then { A with a := AB.top, y := AB.top } else A
  let A := if Z.cutX.contains A.pc then { forget Z.temps A with x := AB.top } else A
  if A.pc == Z.colEnd then
    { forget Z.temps A with a := AB.top, x := AB.top, y := AB.top }
  else if Z.regs.contains A.pc then { A with x := AB.top, y := AB.top }
  else if Z.ends.contains A.pc then
    let side := A.pc == Z.sideA || A.pc == Z.sideB
    let B := forget (if side then Z.temps.filter (· != Z.first) else Z.temps) A
    { B with a := AB.top, x := AB.top, y := if A.pc == Z.sideA then A.y else AB.top }
  else A

/-- states with the same key are joined -/
def Aids.key (Z : Aids) (E : Env) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := keyOf E Z.keep A
  let n := if Z.aAt.contains A.pc || (Z.aLo < A.pc && A.pc < Z.aHi) then n * 65536 + num A.a else n
  if Z.offR.any (fun q => q.1 ≤ A.pc && A.pc ≤ q.2) then n * 65536 + num (A.getK Z.offI) else n

structure SearchS where
  pending : Std.TreeMap Nat AS compare := {}
  pendKey : Std.HashMap Nat Nat := {}
  done : Std.HashMap Nat AS := {}
  vis : Std.HashMap Nat Nat := {}
  arr : Std.HashMap Nat Nat := {}
  leaders : Std.HashMap Nat Unit := {}
  steps : Nat := 0
  forks : Nat := 0
  fails : Nat := 0
  joins : Nat := 0
  firstFail : Option AS := none
  ends : Array AS := #[]

/-- the waiting states go in the order of their first dot -/
def SearchS.put (X : SearchS) (K : Nat) (B : AS) : SearchS :=
  let q := B.lo * (1 <<< 200) + (K % (1 <<< 200))
  let pend := match X.pendKey[K]? with
    | some r => X.pending.erase r
    | none => X.pending
  { X with pending := pend.insert q B, pendKey := X.pendKey.insert K q }

def routeS (P : Places) (Z : Aids) (E : Env) (X : SearchS) (B0 : AS) : SearchS :=
  let B := clampS P (Z.norm B0)
  let K := Z.key E B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D =>
    if B.le D then X else
    let J := D.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 then { J with hi := P.late } else J
    SearchS.put { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => SearchS.put { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

partial def runS (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preS P (clampS P cur)).flatMap (stepS P E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (Z.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeS P Z E X b
    break
  return X

partial def searchS (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := Z.key E A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runS P Z E ops X A
  return X

/-- with a limit on the steps -/
partial def searchLim (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (lim : Nat) : SearchS := Id.run do
  let ops := (aRows E).toArray
  let mut X : SearchS := (startsR r K).foldl (routeS P Z E) {}
  while X.steps ≤ lim do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let k := Z.key E A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase k }
      X := runS P Z E ops X A
  return X

def searchOf (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchS P Z E ops ((startsR r K).foldl (routeS P Z E) {})

/-- the configuration from the table found: the states that two paths come into -/
def cfgOf (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (W : List (Machine × List (Nat × UInt8))) : CfgS :=
  let X := searchOf P Z E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd]).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin := finR P r K W, t := q.1, key := Z.key E, idx := q.2.1, cut := q.2.2, norm := Z.norm, normAt := at0 }

/-- the fuel of a walk -/
def fuelS : Nat := 100000

/-- the places as a check -/
def placesOK (E : Env) (P : Places) : Bool :=
  let opAt := fun (a : UInt16) (o : UInt8) => decide (0x8000 ≤ a) && E.prg.get! (a &&& E.mask).toNat == o
  decide (P.late < dotsPerFrame) && opAt P.read 0xB1 && opAt P.erase 0x91 && decide (P.offI < 2048) && decide (P.xI < 2048) && decide (P.saveI < 2048) &&
    decide (P.stI < 2048) && decide (P.hpI < 2048) && E.D.isEmpty

theorem placesOK_spec {E : Env} {P : Places} (h : placesOK E P = true) : PlacesOK E P := by
  simp only [placesOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h8⟩, h9⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h8, h9, h7⟩

/-- **The check.** -/
def walkCheck (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (W : List (Machine × List (Nat × UInt8))) : Bool :=
  let C := cfgOf P Z E r K W
  placesOK E P && E.pad.v == 0 && E.pad.k == 0 && maskOK r K && W.all (fun w => maskOK w.1 w.2) && C.t.all (walkS C fuelS) && (startsR r K).all (walkS C fuelS)

theorem roomOK_of_check {P : Places} {Z : Aids} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {W : List (Machine × List (Nat × UInt8))} (h : walkCheck P Z E r K W = true) :
    RoomOK E P r K W (cfgOf P Z E r K W) fuelS := by
  simp only [walkCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h3'⟩, h4⟩, h5⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨placesOK_spec h1, hp, maskOK_spec h3, fun w hw => maskOK_spec (h3' w hw), rfl, rfl, rfl, rfl, h4, h5⟩

/-! ## The places of the game, from the symbols -/

section
open PipeEntryRule (findOp)
open PipeTransitionAll (Names)

/-- the returns of the `JSR`s between two places, by the bytes of the ROM: a byte that only looks like one does no harm, since this is only for the search -/
def jsrRets (m0 : Machine) (a b : UInt16) : List UInt16 :=
  (List.range (b.toNat - a.toNat)).filterMap fun j =>
    let q := a + j.toUInt16
    if romByte m0 q == 0x20 then some (q + 3) else none

/-- the first `JSR` of `target` from `a` on, within `n` bytes -/
def findJsr (m0 : Machine) (a target : UInt16) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m0 a == 0x20 && romByte m0 (a + 1) == target.toUInt8 && romByte m0 (a + 2) == (target >>> 8).toUInt8 then a else findJsr m0 (a + 1) target n

/-- the place after the first `STA zp` from `a` on, within `n` bytes -/
def nextStore (m0 : Machine) (a : UInt16) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m0 a == 0x85 then a else nextStore m0 (a + 1) n

/-- the first `op z` (an instruction on the zero page byte `z`) from `a` on, within `n` bytes -/
def findOpZ (m0 : Machine) (a : UInt16) (op z : UInt8) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m0 a == op && romByte m0 (a + 1) == z then a else findOpZ m0 (a + 1) op z n

/-- the tiles in the block buffers of the reference machine, and the empty tile -/
def tilesOf (lo n : Nat) (r : Machine) : List UInt8 :=
  (((List.range n).map fun j => r.ram.get! (lo + j)) ++ [0]).eraseDups

/-- the places. `r` is the reference machine. -/
def placesOf (sy : Syms) (nm : Names) (m0 r : Machine) : Places :=
  let read := findOp m0 sy.BlockBufferCollision 0xB1 64
  let bufLo := (sy.Block_Buffer_1 &&& 0x7FF).toNat
  let bufN := 2 * (sy.Block_Buffer_2 - sy.Block_Buffer_1).toNat
  { idle := r.pc
    late := dotsPerFrame - 6000
    read
    saveI := (romByte m0 (sy.BlockBufferCollision + 2)).toNat
    heads := [romByte m0 sy.BlockBufferAdderData, romByte m0 (sy.BlockBufferAdderData + 1), romByte m0 (sy.BlockBufferAdderData + 2)]
    tiles := tilesOf bufLo bufN r
    headTiles := [0, sy.CoinTile.toUInt8]
    erase := findOp m0 sy.ErACM 0x91 16
    bufLo
    bufN
    offI := ((nm.ad "VRAM_Buffer1_Offset") &&& 0x7FF).toNat
    offAt := [sy.OutputNumbers, findOp m0 sy.ColorRotation 0xAE 16, sy.GetPlayerColors]
    xI := (sy.Player_X_Position &&& 0x7FF).toNat
    xAt := findOp m0 sy.PlyrPipe 0xA5 16
    pageI := ((nm.ad "ScreenLeft_PageLoc") &&& 0x7FF).toNat
    lockI := ((nm.ad "ScrollLock") &&& 0x7FF).toNat
    rtI := (sy.GameEngineSubroutine &&& 0x7FF).toNat
    timerI := ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat
    eng := sy.EngSidePipe.toUInt8
    long := romByte m0 sy.AreaChangeTimerData
    stI := (sy.Player_State &&& 0x7FF).toNat
    stAt := findOpZ m0 sy.ContSChk 0xA4 sy.Player_State.toUInt8 32
    hpI := (sy.Player_Y_HighPos &&& 0x7FF).toNat
    hpAt := findOpZ m0 sy.PlayerBGCollision 0xA5 sy.Player_Y_HighPos.toUInt8 64 }

/-- what the search forgets and keeps apart -/
def aidsOf (sy : Syms) (nm : Names) (m0 : Machine) : Aids :=
  let read := findOp m0 sy.BlockBufferCollision 0xB1 64
  let s0 := nextStore m0 sy.DoFootCheck 64
  let s1 := nextStore m0 (s0 + 2) 64
  let z0 := (romByte m0 (s0 + 1)).toNat
  let z1 := (romByte m0 (s1 + 1)).toNat
  let z2 := (romByte m0 (read - 2)).toNat
  let z3 := (romByte m0 (read + 3)).toNat
  let z4 := (romByte m0 (sy.BlockBufferCollision + 2)).toNat
  let z5 := (romByte m0 (nextStore m0 sy.BlockBufferCollision 64 + 1)).toNat
  let z6 := (romByte m0 (read + 1)).toNat
  let side := (romByte m0 (sy.DoFootCheck + 1)).toNat
  let rt := (sy.GameEngineSubroutine &&& 0x7FF).toNat
  let cuts := jsrRets m0 sy.GameEngine sy.ExitEng
  { keep := [z3, z0, z1, z4, side, rt]
    temps := [z0, z1, z2, z3, z4, z5, z6, z6 + 1, side]
    first := z0
    regs := [sy.UpdateScreen, sy.OutputToVRAM, sy.RepeatByte]
    ends := [sy.DoFootCheck, sy.DoPlayerSideCheck, sy.SideCheckLoop, sy.BHalf]
    sideA := sy.SideCheckLoop
    sideB := sy.BHalf
    colEnd := findJsr m0 sy.PlayerSubs sy.PlayerBGCollision 64 + 3
    cutAY := cuts ++ jsrRets m0 sy.NonMaskableInterrupt sy.SkipMainOper
    cutX := cuts.drop 9
    aAt := [read + 2, sy.MoveSubs, sy.JumpEngine, findOpZ m0 sy.PlayerBGCollision 0xA5 sy.Player_Y_HighPos.toUInt8 64 + 2]
    aLo := sy.ProcMove
    aHi := sy.MoveSubs
    offR := [(sy.OutputNumbers, sy.ExitOutputN), (sy.ColorRotation, sy.ExitColorRot), (sy.UpdateNumber, sy.NoZSup), (sy.GetPlayerColors, sy.SetVRAMOffset)]
    offI := ((nm.ad "VRAM_Buffer1_Offset") &&& 0x7FF).toNat }

/-- the environment of the walk: the pad is not known; the frame counter and the player's state are read in pieces -/
def envOf (nm : Names) (sy : Syms) (r : Machine) : Env :=
  { prg := r.prg, mask := r.prgMask, pad := AB.top, D := [], splits := [(((nm.ad "FrameCounter") &&& 0x7FF).toNat, 7), ((sy.Player_State &&& 0x7FF).toNat, 3)] }

end

/-! ## The room -/

section
open PipeTransitionAll (Names)

/-- the bits that the condition knows: a name, an offset, a number of bytes, and the bits. The values come from the reference machine. -/
def roomNames : List (String × Nat × Nat × UInt8) :=
  [("GameEngineSubroutine", 0, 1, 255), ("Enemy_Flag", 0, 6, 255), ("Enemy_ID", 5, 1, 255), ("Player_State", 0, 1, 252), ("Block_State", 0, 2, 255),
   ("Misc_State", 0, 9, 255), ("EnemyData", 0, 1, 255), ("EnemyDataHigh", 0, 1, 255), ("AreaMusicBuffer", 0, 1, 251), ("AreaMusicQueue", 0, 1, 255),
   ("FloateyNum_Timer", 0, 6, 255), ("VineFlagOffset", 0, 1, 255), ("Block_RepFlag", 0, 2, 255), ("Cannon_PageLoc", 0, 6, 255), ("Cannon_X_Position", 0, 6, 255),
   ("Cannon_Y_Position", 0, 4, 255), ("EnemyFrenzyBuffer", 0, 1, 255), ("SecondaryHardMode", 0, 1, 255), ("EnemyFrenzyQueue", 0, 1, 255), ("SprDataOffset", 0, 1, 255),
   ("SwimmingFlag", 0, 1, 255), ("JumpspringAnimCtrl", 0, 1, 255), ("FireballThrowingTimer", 0, 1, 255), ("ScreenLeft_PageLoc", 0, 1, 255), ("ScreenRight_PageLoc", 0, 1, 255),
   ("ScreenRight_X_Pos", 0, 1, 255), ("AreaParserTaskNum", 0, 1, 255), ("ScrollLock", 0, 1, 255), ("EnemyDataOffset", 0, 1, 255), ("EnemyObjectPageLoc", 0, 1, 255),
   ("ScrollThirtyTwo", 0, 1, 255), ("CloudTypeOverride", 0, 1, 255), ("AreaType", 0, 1, 255), ("CurrentPlayer", 0, 1, 255), ("PlayerStatus", 0, 1, 254),
   ("WorldNumber", 0, 1, 255), ("OperMode", 0, 1, 255), ("OperMode_Task", 0, 1, 255), ("StarInvincibleTimer", 0, 1, 255), ("AreaMusicBuffer_Alt", 0, 1, 251),
   ("ScreenRoutineTask", 0, 1, 255), ("DisableScreenFlag", 0, 1, 255), ("Fireball_State", 0, 2, 255), ("JoypadOverride", 0, 1, 255), ("GameTimerExpiredFlag", 0, 1, 255),
   ("AreaPointer", 0, 1, 255), ("EntrancePage", 0, 1, 255), ("PrimaryHardMode", 0, 1, 255)]

/-- the list of bits, as RAM indices -/
def knownOf (nm : Names) : List (Nat × UInt8) :=
  roomNames.flatMap fun p => (List.range p.2.2.1).map fun j => (((nm.ad p.1).toNat + p.2.1 + j) &&& 0x7FF, p.2.2.2)

/-- the bytes of the condition at the entry of the side pipe that the walk does not give: a name, an offset, a number of bytes. The routine is the entry itself; the player's
vertical position; the screen's buffer; the sound; the level's number, which the rows of the change into the room do not know. The walk gives the player's state and his height on
the screen: the side pipe's code and the collision routine read them in pieces (`Places.stAt`, `Places.hpAt`). -/
def restNames : List (String × Nat × Nat) :=
  [("GameEngineSubroutine", 0, 1), ("Player_Y_Position", 0, 1), ("VRAM_Buffer1_Offset", 0, 1), ("VRAM_Buffer1", 0, 3), ("VRAM_Buffer1", 7, 1),
   ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1), ("MusicData", 0, 2), ("MusicOffset_Square1", 0, 1), ("NoiseSoundBuffer", 0, 1), ("EventMusicQueue", 0, 1), ("NoteLengthTblAdder", 0, 1),
   ("AreaNumber", 0, 1)]

/-- these bytes as RAM indices -/
def restIdx (nm : Names) : List Nat :=
  restNames.flatMap fun p => (List.range p.2.2).map fun j => ((nm.ad p.1).toNat + p.2.1 + j) &&& 0x7FF

/-- the names this file needs -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  ((["VRAM_Buffer1_Offset", "ScreenLeft_PageLoc", "ScrollLock", "ChangeAreaTimer", "FrameCounter", "GamePauseStatus", "PlayerStatus", "CoinTally", "PlayerScoreDisplay", "GameTimerDisplay", "HalfwayPage", "Hidden1UpFlag", "PseudoRandomBitReg"] ++ roomNames.map (·.1) ++ restNames.map (·.1)).eraseDups).filterMap fun n =>
    (PipeTransitionAll.asmValue ls n).map (n, ·)

/-- the references `V` of the condition at the entry, without the bytes `restIdx`, as known bits -/
def entryW (nm : Names) (V : List (Machine × List Nat)) : List (Machine × List (Nat × UInt8)) :=
  V.map fun v => (v.1, (v.2.filter fun i => !(restIdx nm).contains i).map fun i => (i, (0xFF : UInt8)))

/-- **The condition on the bytes `restIdx` at the entry**: they have the values of a reference machine of the condition at the entry -/
def EntryRest (nm : Names) (V : List (Machine × List Nat)) (m : Machine) : Prop :=
  ∃ v ∈ V, ∀ i ∈ v.2, i ∈ restIdx nm → m.ram.get! i = v.1.ram.get! i

/-- the reference machine: the real machine on the frame before the entry into the side pipe -/
abbrev refR (m0 : Machine) : Machine := SideTransition.pre m0

abbrev placesR (sy : Syms) (nm : Names) (m0 : Machine) : Places := placesOf sy nm m0 (refR m0)

abbrev envR (sy : Syms) (nm : Names) (m0 : Machine) : Env := envOf nm sy (refR m0)

/-- **The condition at a frame's start in the room.** -/
abbrev Room (sy : Syms) (nm : Names) (m0 m : Machine) : Prop := RoomCond (envR sy nm m0) (refR m0) (knownOf nm) m

/-- **The check on the ROM.** The walks, with the references `V` of the condition at the entry, and: the routine, the page and the lock are known bytes; the reference has the player's routine,
the first page and the lock on; the long timer is at least `A`. -/
def roomCheck (sy : Syms) (nm : Names) (m0 : Machine) (A : Nat) (V : List (Machine × List Nat)) : Bool :=
  let P := placesR sy nm m0
  let r := refR m0
  let K := knownOf nm
  walkCheck P (aidsOf sy nm m0) (envR sy nm m0) r K (entryW nm V) &&
    K.contains (P.rtI, 0xFF) && K.contains (P.pageI, 0xFF) && K.contains (P.lockI, 0xFF) &&
    r.ram.get! P.rtI != P.eng && r.ram.get! P.pageI == 0 && r.ram.get! P.lockI != 0 && decide (A ≤ P.long.toNat)

/-- **A run from the first control in the room to the entry into the side pipe.** `seq` lists the frames. Frame `c` is the first control, frame `e` ends the entry frame. -/
structure RoomRun (sy : Syms) (nm : Names) (m0 : Machine) where
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (inp n)
  c : Nat
  e : Nat
  order : c ≤ e
  /-- the condition on one state -/
  start : Room sy nm m0 (seq c)
  /-- what each instruction of each frame meets -/
  sites : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nm m0) (trace (seq n) (inp n) j)
  /-- each frame before the entry starts in the player's routine -/
  stay : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nm m0).rtI = (refR m0).ram.get! (placesR sy nm m0).rtI
  /-- the frame before `e` is the entry -/
  enter : (seq e).ram.get! (placesR sy nm m0).rtI = (placesR sy nm m0).eng

variable {sy : Syms} {nm : Names} {m0 : Machine} {A : Nat} {V : List (Machine × List Nat)}

/-- what the check gives -/
structure RoomFacts (sy : Syms) (nm : Names) (m0 : Machine) (A : Nat) (V : List (Machine × List Nat)) : Prop where
  ok : RoomOK (envR sy nm m0) (placesR sy nm m0) (refR m0) (knownOf nm) (entryW nm V)
    (cfgOf (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (knownOf nm) (entryW nm V)) fuelS
  rt : ((placesR sy nm m0).rtI, (0xFF : UInt8)) ∈ knownOf nm
  page : ((placesR sy nm m0).pageI, (0xFF : UInt8)) ∈ knownOf nm
  lock : ((placesR sy nm m0).lockI, (0xFF : UInt8)) ∈ knownOf nm
  ne : (refR m0).ram.get! (placesR sy nm m0).rtI ≠ (placesR sy nm m0).eng
  page0 : (refR m0).ram.get! (placesR sy nm m0).pageI = 0
  lock1 : (refR m0).ram.get! (placesR sy nm m0).lockI ≠ 0
  long : A ≤ (placesR sy nm m0).long.toNat

theorem roomFacts_of_check (h : roomCheck sy nm m0 A V = true) : RoomFacts sy nm m0 A V := by
  simp only [roomCheck, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨roomOK_of_check h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem byte_of_ff {x y : UInt8} (h : x &&& 0xFF = y &&& 0xFF) : x = y := by
  have e1 : ∀ z : UInt8, z &&& 0xFF = z := fun z => by
    apply bt_ext
    intro j hj
    rw [bt_and, TaintRun.bt_ff hj, Bool.and_true]
  rwa [e1, e1] at h

/-- **One frame keeps the page and the lock.** -/
theorem room_keeps (h : RoomFacts sy nm m0 A V) {m : Machine} {i : UInt8} (hm : Room sy nm m0 m) (hk : ∀ j, SiteOK (placesR sy nm m0) (trace m i j)) :
    (frame m i).ram.get! (placesR sy nm m0).pageI = m.ram.get! (placesR sy nm m0).pageI ∧ (frame m i).ram.get! (placesR sy nm m0).lockI = m.ram.get! (placesR sy nm m0).lockI := by
  have p1 := byte_of_ff (hm.bytes _ h.page)
  have p2 := byte_of_ff (hm.bytes _ h.lock)
  simp only at p1 p2
  rw [p1, p2]
  rcases room_step h.ok hm hk with h1 | h1
  · exact ⟨byte_of_ff (h1.bytes _ h.page), byte_of_ff (h1.bytes _ h.lock)⟩
  · exact ⟨h1.page, h1.lock⟩

/-- **The screen and the lock in the room.** On every frame from the first control to the entry, the screen is on the first page and the scroll lock is on. -/
theorem RoomRun.screen (h : RoomFacts sy nm m0 A V) (R : RoomRun sy nm m0) :
    ∀ n, R.c ≤ n → n ≤ R.e → (R.seq n).ram.get! (placesR sy nm m0).pageI = 0 ∧ (R.seq n).ram.get! (placesR sy nm m0).lockI ≠ 0 := by
  obtain ⟨h1, _, h3, h4⟩ := room_run h.ok h.rt h.ne R.next R.order R.start R.sites R.stay R.enter
  intro n a b
  rw [show (0 : UInt8) = 0 from rfl]
  by_cases hn : n < R.e
  · have hr := h1 n a hn
    have p1 := byte_of_ff (hr.bytes _ h.page)
    have p2 := byte_of_ff (hr.bytes _ h.lock)
    simp only at p1 p2
    rw [p1, p2]
    exact ⟨h.page0, h.lock1⟩
  · have : n = R.e := by omega
    subst this
    rw [h3, h4]
    exact ⟨h.page0, h.lock1⟩

/-- **The entry has the long timer.** -/
theorem RoomRun.timer (h : RoomFacts sy nm m0 A V) (R : RoomRun sy nm m0) : A ≤ ((R.seq R.e).ram.get! (placesR sy nm m0).timerI).toNat := by
  obtain ⟨_, h2, _, _⟩ := room_run h.ok h.rt h.ne R.next R.order R.start R.sites R.stay R.enter
  rw [h2]
  exact h.long

/-- the condition at the entry of the side pipe, without the timer, and the timer -/
theorem entry_of_timer {E : Env} {V : List (Machine × List Nat)} {c c' : Nat} {m : Machine} (h : EntryCond E V c' m) (ht : c ≤ (m.ram.get! E.rkI).toNat) : EntryCond E V c m :=
  { h with timer := ht }

/-- the reference machines of a condition at the entry know the routine, and it is the pipe's -/
def entryRtOK (P : Places) (V : List (Machine × List Nat)) : Bool :=
  V.all fun v => v.2.contains P.rtI && v.1.ram.get! P.rtI == P.eng

/-- **The replacement of the timer in the condition at the entry.** From the condition at the entry without the timer, and the fields of `RoomRun` other than `enter`, comes the condition with the timer. -/
theorem entry_long {E : Env} {V V' : List (Machine × List Nat)} (h : RoomFacts sy nm m0 A V') (hE : E.rkI = (placesR sy nm m0).timerI) (hV : entryRtOK (placesR sy nm m0) V = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (order : c ≤ e)
    (start : Room sy nm m0 (seq c))
    (sites : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nm m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nm m0).rtI = (refR m0).ram.get! (placesR sy nm m0).rtI)
    (h0 : EntryCond E V 0 (seq e)) : EntryCond E V A (seq e) := by
  have enter : (seq e).ram.get! (placesR sy nm m0).rtI = (placesR sy nm m0).eng := by
    obtain ⟨v, hv, _, _, h3⟩ := h0.ref
    simp only [entryRtOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hV
    obtain ⟨a1, a2⟩ := hV v hv
    rw [h3 _ a1]
    exact a2
  refine entry_of_timer h0 ?_
  rw [hE]
  exact RoomRun.timer h ⟨seq, inp, next, c, e, order, start, sites, stay, enter⟩

/-- the condition at the entry and the room: the references know the routine and it is the pipe's; the routine is one of the bytes `restIdx`; the environment has the room's ROM -/
def entryEnvOK (sy : Syms) (nm : Names) (m0 : Machine) (E : Env) (V : List (Machine × List Nat)) : Bool :=
  entryRtOK (placesR sy nm m0) V && (restIdx nm).contains (placesR sy nm m0).rtI && decide (E.prg.data = (envR sy nm m0).prg.data) && E.mask == (envR sy nm m0).mask

/-- **The condition at the entry, from the room.** From the condition at the first control, `SiteOK` and the player's routine on each frame up to the entry, and the bytes `restIdx` at the
entry, comes the whole condition at the entry, with the timer at least `A`. -/
theorem entry_rest {E : Env} (h : RoomFacts sy nm m0 A V) (hE : E.rkI = (placesR sy nm m0).timerI) (hV : entryEnvOK sy nm m0 E V = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (order : c ≤ e)
    (start : Room sy nm m0 (seq c))
    (sites : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nm m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nm m0).rtI = (refR m0).ram.get! (placesR sy nm m0).rtI)
    (rest : EntryRest nm V (seq e)) : EntryCond E V A (seq e) := by
  simp only [entryEnvOK, entryRtOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hV
  obtain ⟨⟨⟨hV1, hV2⟩, hV3⟩, hV4⟩ := hV
  obtain ⟨v, hv, hb⟩ := rest
  have enter : (seq e).ram.get! (placesR sy nm m0).rtI = (placesR sy nm m0).eng := by
    obtain ⟨a1, a2⟩ := hV1 v hv
    rw [hb _ a1 hV2]
    exact a2
  obtain ⟨_, hL⟩ := room_leaves h.ok h.rt h.ne next order start sites stay enter
  have hw : (v.1, (v.2.filter fun i => !(restIdx nm).contains i).map fun i => (i, (0xFF : UInt8))) ∈ entryW nm V := List.mem_map.2 ⟨v, hv, rfl⟩
  have hc := hL.entry enter _ hw
  have hp := SideTransition.byteArray_eq hV3
  refine ⟨hc.dot, hc.flags, hc.s0, hc.ctrl, hc.strobe, hc.halted, hc.trk, hc.prg.trans hp.symm, hc.mask.trans hV4.symm, hc.size, ⟨v, hv, hc.pc, hc.s, fun i hi => ?_⟩, ?_⟩
  · by_cases hr : i ∈ restIdx nm
    · exact hb i hi hr
    · have hf : (i, (0xFF : UInt8)) ∈ (v.2.filter fun i => !(restIdx nm).contains i).map fun i => (i, (0xFF : UInt8)) :=
        List.mem_map.2 ⟨i, List.mem_filter.2 ⟨hi, by simp [hr]⟩, rfl⟩
      exact byte_of_ff (hc.bytes _ hf)
  · rw [hE, hL.long enter]
    exact h.long

end

/-! ## On real frames: a program, no part of the proof -/

/-- `SiteOK` at one instruction: the number of the part that fails, or 0 -/
def siteBad (P : Places) (m : Machine) : Nat :=
  if m.pc != P.idle && decide (P.late < m.fdot) then 1
  else if decide (0x8000 ≤ m.pc) && m.prg.get! (m.pc &&& m.prgMask).toNat == 0xB1 && !(decide (readAddr m < 0x2000) || decide (0x8000 ≤ readAddr m)) then 2
  else if m.pc == P.read && !P.tiles.contains (readVal m) then 3
  else if m.pc == P.read && P.heads.contains (m.ram.get! P.saveI) && !P.headTiles.contains (readVal m) then 4
  else if m.pc == P.erase && !(decide (writeAddr m < 0x2000) && decide (P.bufLo ≤ (writeAddr m &&& 0x7FF).toNat) && decide ((writeAddr m &&& 0x7FF).toNat < P.bufLo + P.bufN)) then 5
  else if P.offAt.contains m.pc && !decide ((m.ram.get! P.offI).toNat < 64) then 6
  else if m.pc == P.xAt && m.ram.get! P.xI &&& 0x0F == 0 then 7
  else 0

/-- what real frames say about the conditions -/
structure Report where
  frames : Nat := 0
  /-- instructions that fail `SiteOK`, by part -/
  bad : List Nat := [0, 0, 0, 0, 0, 0, 0]
  /-- the last dot of a handler -/
  maxDot : Nat := 0
  /-- frames that end out of the condition and out of `Leaves`: with every instruction `SiteOK`, and with some instruction not -/
  left : Nat := 0
  leftBad : Nat := 0
  /-- frames that start in the condition and end in `Leaves`, with the pipe's routine, and among them the timer's value is not the long one -/
  entries : Nat := 0
  shortT : Nat := 0
  /-- frames that end with another routine -/
  other : Nat := 0
  /-- pause frames among the frames -/
  paused : Nat := 0
  /-- entries where the bytes `restIdx` are not those of a reference; entries where they are but the whole condition at the entry fails, on frames with every instruction `SiteOK`, and on others -/
  restNo : Nat := 0
  condNo : Nat := 0
  condNoBad : Nat := 0
  deriving Inhabited

def Report.show (r : Report) : String :=
  s!"frames {r.frames} (paused {r.paused}); not SiteOK by part (dot, register read, tile, head tile, erase, offset, x) {r.bad}; last dot {r.maxDot}; out of the condition and of Leaves {r.left}, and on frames not SiteOK {r.leftBad}; entries {r.entries}, short timer {r.shortT}, without the bytes left to the entry {r.restNo}, with them but not the condition at the entry {r.condNo} (on frames not SiteOK {r.condNoBad}); other routines {r.other}"

/-- the frame ends of the walk from one state, for a program -/
def walkEnds (C : CfgS) : Nat → AS → List AS
  | 0, _ => []
  | n + 1, A => (preS C.P (clampS C.P A)).flatMap fun A₁ => (stepS C.P C.E C.ops A₁).flatMap fun r =>
    match r with
    | none => []
    | some B =>
      if B.k == A.k then
        if C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B)) then [] else walkEnds C n (weaken C B)
      else [B]

/-- `EntryRest` as a check, for a program -/
def restOK (nm : PipeTransitionAll.Names) (V : List (Machine × List Nat)) (m : Machine) : Bool :=
  V.any fun v => v.2.all fun i => !(restIdx nm).contains i || m.ram.get! i == v.1.ram.get! i

/-- one real frame with the bits `pad` of the controller. `ent` says of the machine after an entry whether the bytes left to the entry and the whole condition at the entry hold. -/
def scanFrame (P : Places) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (pauseI : Nat) (m : Machine) (pad : UInt8) (r0 : Report)
    (ent : Machine → Bool × Bool := fun _ => (true, true)) : Report × Machine := Id.run do
  let t := m.frame + 1
  let mut c : Machine := { m with pad }
  let mut R := { r0 with frames := r0.frames + 1, paused := r0.paused + (if m.ram.get! pauseI &&& 1 != 0 then 1 else 0) }
  let mut n := 0
  let mut clean := true
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    let b := siteBad P c
    if b != 0 then
      R := { R with bad := R.bad.set (b - 1) (R.bad.getD (b - 1) 0 + 1) }
      clean := false
    if c.pc != P.idle && decide (c.fdot > R.maxDot) && c.frame == m.frame then R := { R with maxDot := c.fdot }
    c := (go step c).2
    n := n + 1
  if !roomOK E r K c then
    let page := c.ram.get! P.pageI == r.ram.get! P.pageI && c.ram.get! P.lockI == r.ram.get! P.lockI
    let rt := c.ram.get! P.rtI
    if !page || rt == r.ram.get! P.rtI then
      R := if clean then { R with left := R.left + 1 } else { R with leftBad := R.leftBad + 1 }
    else if rt == P.eng then
      let q := ent c
      let n1 : Nat := if q.1 then 0 else 1
      let n2 : Nat := if q.1 && !q.2 && clean then 1 else 0
      let n3 : Nat := if q.1 && !q.2 && !clean then 1 else 0
      R := { R with entries := R.entries + 1, shortT := R.shortT + (if c.ram.get! P.timerI == P.long then 0 else 1) }
      R := { R with restNo := R.restNo + n1, condNo := R.condNo + n2, condNoBad := R.condNoBad + n3 }
    else R := { R with other := R.other + 1 }
  return (R, c)

end Smbrta.ScreenPage
