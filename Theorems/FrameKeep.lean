import Theorems.PipeWrites
import Theorems.CastleWalk
import Theorems.LagFrames

/-!
# One frame in control keeps watched bits

`PipeWrites` follows a whole frame in control with the abstract machine of `TaintRun`, and asks one condition on each instruction (`Clean`). Here the same walk watches some bits of RAM:
known when the frame starts, they are known at its end, with the same values. The bits are the castle flag (`StarFlagTaskControl`, all bits 0) and the low 4 bits of the
position's fraction (`SprObject_X_MoveForce`).

Two steps are not the machine's usual abstract steps:
* `ADC zp` with the low 4 bits of `A`, of the byte and the carry known: the low 4 bits of the sum are known (`aadcL`). The move routine adds the speed's low 4 bits times 16 to the fraction this way.
* at the entry of the move routine an index that is not known is split into 9 pieces: 0, or its lowest bit 1 at bit `b` (`xPieces`). With the index 0 the routine's store of
  the fraction knows its target; with an index not 0 the store is not the player's.

The condition on one instruction is `PipeWrites.Clean` with the watched bytes among the bytes that a store with a target not known does not touch, but the
move routine's store with the index 0 is not asked: that is the player's own store of the fraction, and there the walk knows the target (`CleanK`). The frame starts as in `PipeWrites`
(`FrameStart`). The split of the index at the move routine covers the player's move (index 0) and the other objects' moves (index not 0).

Every path of the walk ends at the start of the next frame (`endOK`): in the idle loop with the stack pointer of control, in one of the two windows of the dot, with the NMI on and the
joypad's strobe off. With the known bytes on the machine at the frame's end (the routine, the mode, the task: `known_of_ctl`) this is `FrameStart` again
(`start_of_sim`, `keep_frame_start`). `Frames` lists the frames of a run, counted or not (`lag` frames), as real frames one after the other, and what they need, frame by frame; that each
frame starts in control, and that the `lag` frames keep the watched bits, are theorems from the machine at control (`Frames.all_start`, `Frames.start`).

A second walk (`walkKC`, `ctlKeepCheck`) stops a path at an instruction that writes the routine, the mode or the task byte by its address (`storesTo`), and asks at the frame's
end that the three bytes still have the values of control. So a frame in control that writes none of them by its address ends in control (`keep_frame_startC`); this is how the
frames before the touch end in control (`Frames.noStore`, `Frames.ctlAll`).

A frame of `Frames` is counted when it ends with the game not paused (the low bit of the pause byte 0, `upAt`): the counted frame `j` is the `j`-th such frame (`ixOf`, by
a count `upTo` and a search `firstLe`). So the counted frames come in order (`Frames.order`), each ends not paused (`Frames.up`), and the frames between them end paused
(`Frames.down`); these are theorems from the definition. The condition on each instruction of the frames of a run is `CleanK` of `guardE`: `guardK` with eighteen more bytes
protected (`spareK`: the pause byte, the area's type, the swimming flag, the change of size; `spareE`: A and B, A and B of the frame before, the moving direction, the
running speed, the stored speed; `collE`: the player's collision bits; `speedE`: the player's speed; `vertE`: the vertical force down, the jump's origin, the jump's halt
value; `faceE`: the player's facing and subspeed; `stateE`: the player's state and the vertical force). The walks of this file use `guardK`; `CleanK` of `guardE` gives `CleanK` of `guardF`
(`cleanK_of_E`), and that gives `CleanK` of `guardK` (`cleanK_of_F`).
There is no game data in this file. Page: `1-1/f-6-19-FrameKeep.md`.
-/

namespace Smbrta.FrameKeep

open PipeTransition (frame)
open PipeTransitionAll (go ba_get_set_self ba_get_set_ne ba_size_set)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop findOp)
open PipeWrites (Guard Clean Plain FrameStart wTarget opAt rTarget tableOf gsucc customOf capT jumpP startG zeros keepKn leK joinK knownOf guardOf SG)

/-! ## What the walk watches -/

/-- a watched byte: its RAM index, the bits watched, and their values -/
abbrev Watch := Nat × UInt8 × UInt8

/-- the watched bits are known in `B`, with their values -/
def watchOK (W : List Watch) (B : AS) : Bool :=
  W.all fun w => decide (w.1 < 2048) && ((B.getK w.1).k &&& w.2.1 == w.2.1) && ((B.getK w.1).v &&& w.2.1 == w.2.2 &&& w.2.1)

/-- the watched bits of a machine have their values -/
def Watched (W : List Watch) (m : Machine) : Prop := ∀ w ∈ W, m.ram.get! w.1 &&& w.2.1 = w.2.2 &&& w.2.1

/-- the move routine: its entry, and its store of the fraction -/
structure Spot where
  entry : UInt16
  store : UInt16
  /-- the zero page bytes that the search keeps inside the routine: no part of the proof -/
  temps : List Nat
  deriving Inhabited

/-! ## The condition on one instruction -/

/-- **What stays assumed of one instruction**: `PipeWrites.Clean`, but the store of the move routine with the index 0 (the player's fraction) is not asked. -/
structure CleanK (G : Guard) (q : UInt16) (m : Machine) : Prop where
  /-- a store through an index or a pointer is `Plain`, but at `q` with the index 0 -/
  store : ∀ t, wTarget (opAt m) m = some t → ¬ (m.pc = q ∧ m.x = 0) → Plain G.prot t
  /-- `LDA (zp),Y` does not read a register -/
  read : opAt m = 0xB1 → rTarget m < 0x2000 ∨ 0x8000 ≤ rTarget m
  /-- the index of the jump is in its table -/
  jump : m.pc = G.je → ∀ n, G.jumps.lookup (tableOf m).toNat = some n → m.a.toNat < n
  /-- the time -/
  time : m.pc ≠ G.idle → m.fdot ≤ G.late

theorem clean_of {G : Guard} {q : UInt16} {m : Machine} (h : CleanK G q m) (hq : ¬ (m.pc = q ∧ m.x = 0)) : Clean G m :=
  ⟨fun t ht => h.store t ht hq, h.read, h.jump, h.time⟩

/-! ## The steps -/

/-- `ADC` with the low 4 bits of `A` and of the byte and the carry known: the low 4 bits of the sum are known -/
def aadcL (v : AB) : AM Unit := fun A =>
  let c := A.p.and (AB.known 1)
  let r : AB := ⟨(A.a.v + v.v + c.v) &&& 0x0F, 0x0F⟩
  let p := (((((A.p.and (AB.known 0x3C)).or (AB.ite none 0x01 0)).or (AB.ite none 0x02 0)).or (AB.top.and (AB.known 0x80))).or (AB.ite none 0x40 0))
  if A.a.k &&& 0x0F == 0x0F && v.k &&& 0x0F == 0x0F && c.isK then some ((), { A with a := r, p := p }) else none

/-- the zero page byte that the instruction at `A.pc` names -/
def zpOf (E : Env) (A : AS) : AB := A.getK (E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toNat

/-- an `ADC zp` with the low 4 bits of `A` and of the byte and the carry known, but not every bit -/
def lowAdc (E : Env) (A : AS) : Bool :=
  !A.nmi && decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0x65 &&
    A.a.k &&& 0x0F == 0x0F && (zpOf E A).k &&& 0x0F == 0x0F && (A.p.and (AB.known 1)).isK && !(A.a.isK && (zpOf E A).isK)

/-- the abstract `ADC zp` of the low bits -/
def aSumL (E : Env) : AM Unit := aZp E >>= fun ad => ard E ad >>= aadcL

/-- the index has a known bit 1: it is not 0 -/
def nonZero (b : AB) : Bool := b.k &&& b.v != 0

/-- the abstract successors: at the move routine's store the index is known, or known not to be 0; the low-bits `ADC zp`; else the steps of `PipeWrites` -/
def kstep (S : Spot) (G : Guard) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if !A.nmi && A.pc == S.store then
    (if A.x.isK && E.prg.get! (A.pc &&& E.mask).toNat == 0x9D then succs E ops A else if nonZero A.x then gsucc G E ops A else [none])
  else if lowAdc E A then [((aSumL E >>= fun _ => atick (cycOf 0x65) (cycOf 0x65)) { A with pc := A.pc + 1 }).map (·.2)]
  else gsucc G E ops A

/-- the pieces of a byte: 0, or its lowest bit 1 at `b` -/
def xPieces : List AB := AB.known 0 :: (List.range 8).map fun b => ⟨(1 <<< b).toUInt8, ((1 <<< (b + 1)) - 1).toUInt8⟩

/-- the index at the move routine's entry: 0, or not 0 -/
def splitX (S : Spot) (B : AS) : List AS :=
  if B.pc == S.entry && !B.x.isK && !nonZero B.x then xPieces.map fun x => { B with x } else [B]

/-- the pieces before a step: the time, the jump's table, the index at the move routine -/
def preK (S : Spot) (G : Guard) (A : AS) : List AS := (jumpP G (capT G A)).flatMap (splitX S)

/-! ## The walk -/

/-- the table -/
structure CfgK where
  E : Env
  ops : Array (AM Unit)
  S : Spot
  G : Guard
  W : List Watch
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray
  /-- the table's key of a state: no part of the proof -/
  key : AS → Nat
  /-- what the frame's end must meet besides the watched bits and `endOK` -/
  fin : AS → Bool

def coverK (C : CfgK) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false

/-- the state after the frame's end is the start of a frame as `FrameStart` asks, but for the known bytes: in the idle loop with the stack pointer of control, in one of the two
windows of the dot, with the NMI on and the joypad's strobe off -/
def endOK (G : Guard) (B : AS) : Bool :=
  B.pc == G.idle && B.s == G.s0 && ((B.lo == 0 && B.hi == 0 && !B.vb && !B.nmi) || (decide (1 ≤ B.lo) && decide (B.hi ≤ 9) && B.vb && B.nmi)) &&
    B.ppuCtrl.bit 0x80 == some true && !B.strobe

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end with the watched bits known, the start of the next frame (`endOK`), and `fin` -/
def walkK (C : CfgK) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK C.S C.G A).all fun A₁ => (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverK C B) || walkK C n B
      else B.k == A.k + 1 && watchOK C.W B && endOK C.G B && C.fin B

/-- the abstract state when the frame starts: that of `PipeWrites`, with the watched bits known -/
def startK (G : Guard) (W : List Watch) (late : Bool) : AS :=
  W.foldl (fun A w => A.setK w.1 ⟨w.2.2 &&& w.2.1, w.2.1⟩) (startG G late)

/-! ## Finding the table: a search, no part of the proof -/

/-- in the move routine -/
def inMove (S : Spot) (pc : UInt16) : Bool := decide (S.entry ≤ pc) && decide (pc ≤ S.store + 2)

/-- what the search forgets: the bytes outside `prot` and the free stack; inside the move routine it keeps its temporaries; near the jump routine nothing -/
def normK (S : Spot) (G : Guard) (A0 : AS) : AS :=
  let A := { A0 with padShift := AB.top }
  if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
  let keep := if inMove S A.pc then S.temps ++ G.prot else G.prot
  let B := PipeWrites.AS.forgetW keep A
  let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
  { B with kn }

/-- the key: states with the same key are joined -/
def keyK (S : Spot) (G : Guard) (W : List Watch) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := num (A.getK G.rtI)
  let n := W.foldl (fun n w => n * 65536 + num (A.getK w.1)) n
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0)
  let n := if G.je ≤ A.pc && A.pc ≤ G.je + 18 then (n * 65536 + num A.a) * 65536 + num A.y else n
  let n := if inMove S A.pc then n * 65536 + num A.x else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + stackHash A

/-- the search's step into the table, with the table's key `key` -/
def routeKW (S : Spot) (G : Guard) (key : AS → Nat) (X : SG) (B0 : AS) : SG :=
  let B := normK S G B0
  let K := key B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

def routeK (S : Spot) (G : Guard) (W : List Watch) (X : SG) (B0 : AS) : SG := routeKW S G (keyK S G W) X B0

partial def runKW (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preK S G cur).flatMap (kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !watchOK W B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeKW S G key X b
    break
  return X

partial def searchKW (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (ops : Array (AM Unit)) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      X := runKW S G E W key ops X A
  return X

partial def runK (S : Spot) (G : Guard) (E : Env) (W : List Watch) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := runKW S G E W (keyK S G W) ops X0 A0

partial def searchK (S : Spot) (G : Guard) (E : Env) (W : List Watch) (ops : Array (AM Unit)) (X0 : SG) : SG := searchKW S G E W (keyK S G W) ops X0

def searchOfKW (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) : SG :=
  let ops := (aRows E).toArray
  searchKW S G E W key ops ([startK G W false, startK G W true].foldl (routeKW S G key) {})

def searchOfK (S : Spot) (G : Guard) (E : Env) (W : List Watch) : SG := searchOfKW S G E W (keyK S G W)

/-- the table, from the search: every state that was reached more than once -/
def tableOfKW (key : AS → Nat) (X : SG) : Array AS × Std.HashMap Nat (List Nat) × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat (List Nat) := {}
  let mut cut := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert (key A) (t.size :: idx.getD (key A) [])
      cut := cut.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, cut)

def tableOfK (S : Spot) (G : Guard) (W : List Watch) (X : SG) : Array AS × Std.HashMap Nat (List Nat) × ByteArray := tableOfKW (keyK S G W) X

/-- the table with the key `key` and the frame's end condition `fin` -/
def cfgOfKW (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (fin : AS → Bool) : CfgK :=
  let q := tableOfKW key (searchOfKW S G E W key)
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, fin }

def cfgOfK (S : Spot) (G : Guard) (E : Env) (W : List Watch) : CfgK := cfgOfKW S G E W (keyK S G W) fun _ => true

/-- the fuel of a walk -/
def fuelK : Nat := 20000

/-- **The check.** -/
def keepCheckW (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (fin : AS → Bool) : Bool :=
  let C := cfgOfKW S G E W key fin
  decide (G.late < dotsPerFrame) && W.all (fun w => decide (w.1 < 2048)) &&
    C.t.all (walkK C fuelK) && walkK C fuelK (startK G W false) && walkK C fuelK (startK G W true)

/-- **The check**, with the end condition `fin` true -/
def keepCheck (S : Spot) (G : Guard) (E : Env) (W : List Watch) : Bool := keepCheckW S G E W (keyK S G W) fun _ => true

/-! ## The steps follow the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem and0F (y : UInt8) : (y &&& 0x0F).toNat = y.toNat % 16 := by
  have h := PipeWrites.and_0F ⟨y.toNat, y.toNat_lt⟩
  simpa using h

/-- the known low 4 bits of a byte -/
theorem low_of_mem {b : AB} {x : UInt8} (hk : b.k &&& 0x0F = 0x0F) (h : b.mem x) : x &&& 0x0F = b.v &&& 0x0F := by
  have e : (x &&& b.k) &&& 0x0F = (b.v &&& b.k) &&& 0x0F := by rw [show x &&& b.k = b.v &&& b.k from h]
  rwa [UInt8.and_assoc, UInt8.and_assoc, hk] at e

/-- the sum of the machine, as bytes -/
theorem sum_u8 (a b c : UInt8) : (a.toUInt16 + b.toUInt16 + c.toUInt16).toUInt8 = a + b + c := by
  apply UInt8.toNat_inj.1
  have h1 := a.toNat_lt
  have h2 := b.toNat_lt
  have h3 := c.toNat_lt
  simp [UInt8.toNat_add]

/-- the low 4 bits of a sum come from the low 4 bits of its terms -/
theorem low_add {a a' b b' c : UInt8} (ha : a &&& 0x0F = a' &&& 0x0F) (hb : b &&& 0x0F = b' &&& 0x0F) : (a + b + c) &&& 0x0F = ((a' + b' + c) &&& 0x0F) &&& 0x0F := by
  have e1 : (a &&& 0x0F).toNat = (a' &&& 0x0F).toNat := by rw [ha]
  have e2 : (b &&& 0x0F).toNat = (b' &&& 0x0F).toNat := by rw [hb]
  rw [and0F, and0F] at e1 e2
  apply UInt8.toNat_inj.1
  rw [and0F, and0F, and0F, UInt8.toNat_add, UInt8.toNat_add, UInt8.toNat_add, UInt8.toNat_add]
  omega

/-- **The low-bits sum** follows `adc` -/
theorem s_adcL {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (aadcL v) (adc x) := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold aadcL at he
  simp only at he
  split at he
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    obtain ⟨rfl, rfl⟩ := some_pair he
    have hcm : (A.p.and (AB.known 1)).mem (m.p &&& 1) := mem_and hs.p (mem_known_self _)
    have e3 := isK_eq h3 hcm
    have ea := low_of_mem h1 hs.a
    have ex := low_of_mem h2 h
    have hp := hs.p
    refine ⟨trivial, { hs with a := ?_, p := ?_ }, rfl, rfl⟩
    · show ((m.a.toUInt16 + x.toUInt16 + (m.p &&& 1).toUInt16).toUInt8) &&& 0x0F = ((A.a.v + v.v + (A.p.and (AB.known 1)).v) &&& 0x0F) &&& 0x0F
      rw [sum_u8, e3]
      exact low_add ea ex
    · exact mem_or (mem_or (mem_or (mem_or (mem_and hp (mem_known_self _)) (mem_iteN _ _ _)) (mem_iteN _ _ _)) (mem_and (mem_top _) (mem_known_self _))) (mem_iteN _ _ _)
  · cases he

set_option maxRecDepth 100000 in
theorem op_65 : opTable[(0x65 : UInt8).toNat]?.getD opJAM = opADC mZp := by rw [PipeTransitionAll.opTable_eq]; rfl

theorem s_sumL : Snd E F TT (aSumL E) (opADC mZp) :=
  Snd.bind s_mZp fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_adcL hv

/-- an index with a known bit 1 is not 0 -/
theorem ne_of_nonZero {b : AB} {x : UInt8} (h : nonZero b = true) (hm : b.mem x) : x ≠ 0 := by
  intro hx
  subst hx
  simp only [nonZero, bne_iff_ne, ne_eq] at h
  apply h
  have e : (0 : UInt8) &&& b.k = b.v &&& b.k := hm
  rw [UInt8.and_comm, ← e]
  simp

set_option maxRecDepth 100000 in
/-- **A step of the machine**, with the steps of this walk -/
theorem s_kstep {S : Spot} {G : Guard} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat)
    (hc : CleanK G S.store m) (hs : Sim E F A m) :
    ∃ r ∈ kstep S G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold kstep
  by_cases h1 : (!A.nmi && A.pc == S.store) = true
  · rw [if_pos h1]
    by_cases h2 : (A.x.isK && E.prg.get! (A.pc &&& E.mask).toNat == 0x9D) = true
    · rw [if_pos h2]
      exact s_succs hops hT hs
    · rw [if_neg h2]
      by_cases h3 : nonZero A.x = true
      · rw [if_pos h3]
        have hx := ne_of_nonZero h3 hs.x
        exact PipeWrites.s_gsucc hops hT (clean_of hc fun h => hx h.2) hs
      · rw [if_neg h3]
        exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  · rw [if_neg h1]
    by_cases h4 : lowAdc E A = true
    · rw [if_pos h4]
      simp only [lowAdc, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at h4
      obtain ⟨⟨⟨⟨⟨⟨hn, hp⟩, hop⟩, _⟩, _⟩, _⟩, _⟩ := h4
      have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
        pc := by
          show m.pc + 1 = A.pc + 1
          rw [hs.pc] }
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      refine PipeWrites.custom_step hs hn hp hop (by decide) (by decide) (fun u A₂ he => ?_) B hB
      rw [op_65]
      obtain ⟨_, g1, g2⟩ := s_sumL _ _ hs1 _ _ he
      exact ⟨g1, g2⟩
    · rw [if_neg h4]
      by_cases hn : A.nmi = true
      · have e : gsucc G E ops A = succs E ops A := by
          unfold gsucc
          simp [hn]
        rw [e]
        exact s_succs hops hT hs
      · have hq : A.pc ≠ S.store := by
          intro hq
          apply h1
          simp [hn, hq]
        exact PipeWrites.s_gsucc hops hT (clean_of hc fun h => hq (hs.pc ▸ h.1)) hs

/-! ### The pieces -/

theorem sim_capK {G : Guard} {q : UInt16} {A : AS} {m : Machine} (hc : CleanK G q m) (hs : Sim E F A m) : Sim E F (capT G A) m := by
  unfold capT
  by_cases h : (A.pc != G.idle && decide (G.late < A.hi)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hl := hs.lim
    exact { hs with
      hi := hc.time (by rw [hs.pc]; exact h1)
      lim := by
        show G.late < dotsPerFrame
        omega }
  · rw [if_neg h]
    exact hs

theorem cov_jumpK {G : Guard} {q : UInt16} {A : AS} {m : Machine} (hc : CleanK G q m) (hs : Sim E F A m) : ∃ B ∈ jumpP G A, Sim E F B m := by
  unfold jumpP
  by_cases h : (A.pc == G.je && !A.a.isK) = true
  · rw [if_pos h]
    have hpc : m.pc = G.je := by
      rw [hs.pc]
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    cases hp : ptrOf (A.getK (0x100 + A.s.toNat + 1)) (A.getK (0x100 + A.s.toNat + 2)) with
    | none => exact ⟨A, List.mem_singleton.2 rfl, hs⟩
    | some r =>
      simp only
      cases hl : G.jumps.lookup (r + 1).toNat with
      | none => exact ⟨A, List.mem_singleton.2 rfl, hs⟩
      | some n =>
        simp only
        have hsz : A.s.toNat < 256 := A.s.toNat_lt
        have e1 := hs.ram (0x100 + A.s.toNat + 1) (by omega)
        have e2 := hs.ram (0x100 + A.s.toNat + 2) (by omega)
        have e3 := TaintRun.ptrOf_ok hp e1 e2
        have ht : tableOf m = r + 1 := by
          unfold tableOf
          rw [hs.s, e3]
        have hlt := hc.jump hpc n (by rw [ht]; exact hl)
        refine ⟨_, List.mem_map.2 ⟨m.a.toNat, List.mem_range.2 hlt, rfl⟩, ?_⟩
        refine { hs with a := ?_ }
        have e4 : m.a.toNat.toUInt8 = m.a := by simp
        show (AB.known m.a.toNat.toUInt8).mem m.a
        rw [e4]
        exact mem_known_self _
  · rw [if_neg h]
    exact ⟨A, List.mem_singleton.2 rfl, hs⟩

set_option maxRecDepth 100000 in
theorem xPieces_all : (List.range 256).all (fun n => xPieces.any fun p => (n.toUInt8 &&& p.k) == (p.v &&& p.k)) = true := by decide

theorem xPieces_cover (y : UInt8) : ∃ p ∈ xPieces, p.mem y := by
  have h := List.all_eq_true.1 xPieces_all y.toNat (List.mem_range.2 y.toNat_lt)
  obtain ⟨p, hp, he⟩ := List.any_eq_true.1 h
  refine ⟨p, hp, ?_⟩
  have e : y.toNat.toUInt8 = y := by simp
  rw [e] at he
  exact beq_iff_eq.1 he

theorem cov_splitX (S : Spot) : Cov E F (splitX S) := by
  intro B m hs
  unfold splitX
  split
  · obtain ⟨p, hp, hm⟩ := xPieces_cover m.x
    exact ⟨{ B with x := p }, List.mem_map.2 ⟨p, hp, rfl⟩, { hs with x := hm }, rfl⟩
  · exact ⟨B, List.mem_singleton.2 rfl, hs, rfl⟩

theorem k_of_sim {A B : AS} {m : Machine} (h1 : Sim E F A m) (h2 : Sim E F B m) : B.k = A.k := by
  have a1 := h1.fr
  have a2 := h2.fr
  omega

/-- **The pieces cover the machine** -/
theorem cov_preK {S : Spot} {G : Guard} {A : AS} {m : Machine} (hc : CleanK G S.store m) (hs : Sim E F A m) :
    ∃ B ∈ preK S G A, Sim E F B m ∧ B.k = A.k := by
  have h1 := sim_capK hc hs
  obtain ⟨B, hB, h2⟩ := cov_jumpK hc h1
  obtain ⟨D, hD, h3, h4⟩ := cov_splitX S B m h2
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans (k_of_sim hs h2)⟩

end

/-! ## The walk covers the frame -/

section
variable {C : CfgK} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveK (C : CfgK) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkK C n A = true

theorem cover_liveK (ht : C.t.all (walkK C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverK C B = true) :
    ∃ D, LiveK C F D m ∧ D.k = B.k := by
  unfold coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepK (ht : C.t.all (walkK C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hl : LiveK C F A m) (hh : CleanK C.G C.S.store m) :
    (∃ A', LiveK C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, watchOK C.W B = true ∧ endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkK] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := s_kstep hops hT hh hs1
    simp only [walkK, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveK ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.1.2, hw2.1.2, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S`, for every input, if each instruction meets `CleanK`. -/
theorem frame_of_walkK (ht : C.t.all (walkK C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkK C Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, watchOK C.W B = true ∧ endOK C.G B = true ∧ C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveK C F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, watchOK C.W B = true ∧ endOK C.G B = true ∧ C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h2'', h3, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rw [e2]
        rcases live_stepK ht hkl hops hT h1 (hk j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a2'', a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', a2'', by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h2'', h3, h4⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h2', h2'', h3, h4⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact ⟨h1, B, h2, h2', h2'', h3, h4⟩

end

/-! ## The frame -/

section
variable {E : Env} {F : Nat × UInt8}

theorem sim_watch {W : List Watch} {m : Machine} (hw : Watched W m) :
    ∀ (l : List Watch), (∀ w ∈ l, w ∈ W) → ∀ A, Sim E F A m → Sim E F (l.foldl (fun A w => A.setK w.1 ⟨w.2.2 &&& w.2.1, w.2.1⟩) A) m := by
  intro l
  induction l with
  | nil => exact fun _ _ h => h
  | cons w l ih =>
    intro hl A hs
    simp only [List.foldl_cons]
    refine ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ (PipeEntryRule.sim_setK' hs ?_)
    show m.ram.get! w.1 &&& w.2.1 = (w.2.2 &&& w.2.1) &&& w.2.1
    rw [hw w (hl w List.mem_cons_self), UInt8.and_assoc, UInt8.and_self]

/-- the state when the frame starts covers the machine -/
theorem sim_startK {G : Guard} {W : List Watch} (hE : E.pad = AB.top) {m : Machine} (h : FrameStart G E m) (hw : Watched W m) :
    ∃ b : Bool, Sim E (m.frame, 2) (startK G W b) m := by
  obtain ⟨b, hs⟩ := PipeWrites.sim_startG hE h
  exact ⟨b, sim_watch hw W (fun _ h => h) _ hs⟩

/-- the watched bits of the frame's end -/
theorem watched_of {W : List Watch} {B : AS} {m : Machine} (hk : watchOK W B = true) (hs : Sim E F B m) : Watched W m := by
  intro w hw
  have h := List.all_eq_true.1 hk w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e : m.ram.get! w.1 &&& (B.getK w.1).k = (B.getK w.1).v &&& (B.getK w.1).k := hs.ram w.1 h1
  show m.ram.get! w.1 &&& w.2.1 = w.2.2 &&& w.2.1
  calc m.ram.get! w.1 &&& w.2.1 = m.ram.get! w.1 &&& ((B.getK w.1).k &&& w.2.1) := by rw [h2]
    _ = (m.ram.get! w.1 &&& (B.getK w.1).k) &&& w.2.1 := by rw [UInt8.and_assoc]
    _ = ((B.getK w.1).v &&& (B.getK w.1).k) &&& w.2.1 := by rw [e]
    _ = (B.getK w.1).v &&& ((B.getK w.1).k &&& w.2.1) := by rw [UInt8.and_assoc]
    _ = (B.getK w.1).v &&& w.2.1 := by rw [h2]
    _ = w.2.2 &&& w.2.1 := h3

/-- what the check says, with the key `key` and the end condition `fin` -/
structure KeepOKW (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (fin : AS → Bool) : Prop where
  late : G.late < dotsPerFrame
  table : (cfgOfKW S G E W key fin).t.all (walkK (cfgOfKW S G E W key fin) fuelK) = true
  s0 : walkK (cfgOfKW S G E W key fin) fuelK (startK G W false) = true
  s1 : walkK (cfgOfKW S G E W key fin) fuelK (startK G W true) = true

theorem keepOKW_of_check {S : Spot} {G : Guard} {E : Env} {W : List Watch} {key : AS → Nat} {fin : AS → Bool} (h : keepCheckW S G E W key fin = true) :
    KeepOKW S G E W key fin := by
  simp only [keepCheckW, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, _⟩, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- what the check says -/
abbrev KeepOK (S : Spot) (G : Guard) (E : Env) (W : List Watch) : Prop := KeepOKW S G E W (keyK S G W) fun _ => true

theorem keepOK_of_check {S : Spot} {G : Guard} {E : Env} {W : List Watch} (h : keepCheck S G E W = true) : KeepOK S G E W := keepOKW_of_check h

/-- **The frame's end**, from the walk with the end condition `fin`: a state that covers the machine at the frame's end, with the watched bits known, the start of a frame
(`endOK`), and `fin` -/
theorem end_of_walkW {S : Spot} {G : Guard} {W : List Watch} {key : AS → Nat} {fin : AS → Bool} (hc : keepCheckW S G E W key fin = true) (hE : E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hw : Watched W m) (hk : ∀ j, CleanK G S.store (trace m i j)) :
    ∃ B, watchOK W B = true ∧ endOK G B = true ∧ fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  have hC := keepOKW_of_check hc
  obtain ⟨b, hs⟩ := sim_startK hE h0 hw
  have hw0 : walkK (cfgOfKW S G E W key fin) fuelK (startK G W b) = true := by
    cases b with
    | false => exact hC.s0
    | true => exact hC.s1
  obtain ⟨_, B, h1, h2, h3, _, h4⟩ := frame_of_walkK (C := cfgOfKW S G E W key fin) (F := (m.frame, 2)) hC.table rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hE hw0 hs hk
  exact ⟨B, h1, h2, h3, h4⟩

/-- **One frame in control keeps the watched bits**, for the check with any key and end condition -/
theorem keep_frameW {S : Spot} {G : Guard} {W : List Watch} {key : AS → Nat} {fin : AS → Bool} (hc : keepCheckW S G E W key fin = true) (hE : E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hw : Watched W m) (hk : ∀ j, CleanK G S.store (trace m i j)) : Watched W (frame m i) := by
  obtain ⟨B, h1, _, _, h2⟩ := end_of_walkW hc hE h0 hw hk
  exact watched_of h1 h2

/-- **One frame in control keeps the watched bits.** A frame that starts in the idle loop in control (`FrameStart`) with the watched bits at their values, and whose every instruction
meets `CleanK`, ends with the watched bits at their values. -/
theorem keep_frame {S : Spot} {G : Guard} {W : List Watch} (hc : keepCheck S G E W = true) (hE : E.pad = AB.top) {m : Machine} {i : UInt8}
    (h0 : FrameStart G E m) (hw : Watched W m) (hk : ∀ j, CleanK G S.store (trace m i j)) : Watched W (frame m i) :=
  keep_frameW hc hE h0 hw hk

theorem bit80_all : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0x80 != 0) = true → UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel

/-- a known bit 7 that is 1 -/
theorem ctrl_of_bit {b : AB} {x : UInt8} (h : (b.bit 0x80 == some true) = true) (hm : b.mem x) : x &&& 0x80 = 0x80 := by
  unfold AB.bit at h
  split at h
  · rename_i hk
    simp only [beq_iff_eq, Option.some.injEq] at h hk
    have e : (x &&& b.k) &&& 0x80 = (b.v &&& b.k) &&& 0x80 := by rw [show x &&& b.k = b.v &&& b.k from hm]
    rw [UInt8.and_assoc, UInt8.and_assoc, hk] at e
    rw [e]
    have h1 := bit80_all ⟨b.v.toNat, b.v.toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at h1
    exact h1 (by rw [h])
  · simp at h

/-- **The start of a frame from the state after the frame's end**: `endOK` and the known bytes on the machine give `FrameStart`. `E'` has the program of `E`. -/
theorem start_of_sim {G : Guard} {E' : Env} {B : AS} {m : Machine} (hs : Sim E F B m) (he : endOK G B = true) (hp : E.prg = E'.prg) (hmk : E.mask = E'.mask)
    (hk : ∀ p ∈ G.known, m.ram.get! p.1 = p.2) : FrameStart G E' m := by
  simp only [endOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨hpc, hs0⟩, hdot⟩, hc7⟩, hst⟩ := he
  refine ⟨hs.pc.trans hpc, hs.s.trans hs0, ?_, ctrl_of_bit (by rw [hc7]; rfl) hs.ppuCtrl, hs.s0, hs.strobe.trans hst, hs.halted, hs.trk, hs.prg.trans hp, hs.mask.trans hmk,
    hs.size, hk⟩
  have hlo := hs.lo
  have hhi := hs.hi
  rcases hdot with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · exact Or.inl ⟨by omega, hs.vb.trans h3, hs.nmi.trans h4⟩
  · exact Or.inr ⟨by omega, by omega, hs.vb.trans h3, hs.nmi.trans h4⟩

/-- **One frame in control ends at the start of a frame in control**, for the check with any key and end condition -/
theorem keep_frame_startW {S : Spot} {G : Guard} {W : List Watch} {key : AS → Nat} {fin : AS → Bool} (hc : keepCheckW S G E W key fin = true) (hE : E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hw : Watched W m) (hk : ∀ j, CleanK G S.store (trace m i j)) (hkn : ∀ p ∈ G.known, (frame m i).ram.get! p.1 = p.2) :
    FrameStart G E (frame m i) ∧ Watched W (frame m i) := by
  obtain ⟨B, h1, h2, _, h3⟩ := end_of_walkW hc hE h0 hw hk
  exact ⟨start_of_sim h3 h2 rfl rfl hkn, watched_of h1 h3⟩

/-- **One frame in control ends at the start of a frame in control**, if the frame's end has the known bytes of `G` (for `guardK`: the routine, the mode, the task),
and it keeps the watched bits. -/
theorem keep_frame_start {S : Spot} {G : Guard} {W : List Watch} (hc : keepCheck S G E W = true) (hE : E.pad = AB.top) {m : Machine} {i : UInt8}
    (h0 : FrameStart G E m) (hw : Watched W m) (hk : ∀ j, CleanK G S.store (trace m i j)) (hkn : ∀ p ∈ G.known, (frame m i).ram.get! p.1 = p.2) :
    FrameStart G E (frame m i) ∧ Watched W (frame m i) :=
  keep_frame_startW hc hE h0 hw hk hkn

end

/-! ## The frames before the touch: the stores of the three bytes of control cut

The routine, the mode and the task are in `prot` of `guardK`, so under `CleanK` a store through an index or a pointer does not change them. Only an instruction that names one of them
by its address, zero page or absolute, can (`storesTo`). `walkKC` is `walkK`, but a path stops at such an instruction: the frame does not come there, by hypothesis. At the frame's end it asks that the
known bytes of the guard are still known with their values (`knownAll`). So a frame in control whose instructions do not write the three bytes by their addresses ends in control. -/

/-- the opcodes that write a byte by its zero page address: `STA`, `STX`, `STY`, `INC`, `DEC`, `ASL`, `LSR`, `ROL`, `ROR` -/
def zpWrites : List UInt8 := [0x85, 0x86, 0x84, 0xE6, 0xC6, 0x06, 0x46, 0x26, 0x66]

/-- the opcodes that write a byte by its absolute address: the same instructions -/
def absWrites : List UInt8 := [0x8D, 0x8E, 0x8C, 0xEE, 0xCE, 0x0E, 0x4E, 0x2E, 0x6E]

/-- the instruction at `pc` of the program writes one of the RAM bytes `l` by its address, zero page or absolute -/
def storesTo (l : List Nat) (prg : ByteArray) (mask pc : UInt16) : Bool :=
  (zpWrites.contains (prg.get! (pc &&& mask).toNat) && l.contains (prg.get! ((pc + 1) &&& mask).toNat).toNat) ||
  (absWrites.contains (prg.get! (pc &&& mask).toNat) &&
    (decide (((prg.get! ((pc + 1) &&& mask).toNat).toUInt16 ||| ((prg.get! ((pc + 2) &&& mask).toNat).toUInt16 <<< 8)) < 0x2000) &&
      l.contains ((((prg.get! ((pc + 1) &&& mask).toNat).toUInt16 ||| ((prg.get! ((pc + 2) &&& mask).toNat).toUInt16 <<< 8)) &&& 0x7FF).toNat)))

/-- the three bytes of control: the routine, the mode, the task -/
def ctlI (sy : Syms) : List Nat := [(sy.GameEngineSubroutine &&& 0x7FF).toNat, (sy.OperMode &&& 0x7FF).toNat, (sy.OperMode_Task &&& 0x7FF).toNat]

/-- **The machine's instruction writes the routine, the mode or the task byte by its address** -/
def CtlStore (sy : Syms) (m : Machine) : Bool := storesTo (ctlI sy) m.prg m.prgMask m.pc

/-- the known bytes of the guard are known in `B`, with their values -/
def knownAll (G : Guard) (B : AS) : Bool := G.known.all fun p => decide (p.1 < 2048) && (B.getK p.1).isK && (B.getK p.1).v == p.2

/-- `walkK`, but a path stops at an instruction that writes one of the bytes `l` by its address -/
def walkKC (C : CfgK) (l : List Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => storesTo l C.E.prg C.E.mask A.pc || (preK C.S C.G A).all fun A₁ => (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverK C B) || walkKC C l n B
      else B.k == A.k + 1 && watchOK C.W B && endOK C.G B && C.fin B

/-! ### Finding its table: a search, no part of the proof -/

partial def runKWC (S : Spot) (G : Guard) (E : Env) (key : AS → Nat) (l : List Nat) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    if storesTo l E.prg E.mask cur.pc then break
    let rs := (preK S G cur).flatMap (kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some _ => false
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && !storesTo l E.prg E.mask b.pc &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeKW S G key X b
    break
  return X

partial def searchKWC (S : Spot) (G : Guard) (E : Env) (key : AS → Nat) (l : List Nat) (ops : Array (AM Unit)) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      X := runKWC S G E key l ops X A
  return X

def searchOfKWC (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (l : List Nat) : SG :=
  searchKWC S G E key l (aRows E).toArray ([startK G W false, startK G W true].foldl (routeKW S G key) {})

/-- the table of the walk with the stores cut -/
def cfgOfKWC (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (l : List Nat) (fin : AS → Bool) : CfgK :=
  let q := tableOfKW key (searchOfKWC S G E W key l)
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, fin }

/-- **The check of the walk with the stores of `l` cut** -/
def keepCheckC (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (l : List Nat) (fin : AS → Bool) : Bool :=
  let C := cfgOfKWC S G E W key l fin
  decide (G.late < dotsPerFrame) && W.all (fun w => decide (w.1 < 2048)) &&
    C.t.all (walkKC C l fuelK) && walkKC C l fuelK (startK G W false) && walkKC C l fuelK (startK G W true)

/-! ### The walk covers the frame -/

section
variable {C : CfgK} {l : List Nat} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk with the stores cut from `A` succeeds -/
def LiveKC (C : CfgK) (l : List Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkKC C l n A = true

theorem cover_liveKC (ht : C.t.all (walkKC C l Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverK C B = true) :
    ∃ D, LiveKC C l F D m ∧ D.k = B.k := by
  unfold coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepKC (ht : C.t.all (walkKC C l Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hl : LiveKC C l F A m) (hh : CleanK C.G C.S.store m) (hx : storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveKC C l F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, watchOK C.W B = true ∧ endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkKC] at hw
  | succ n =>
    have hx' : storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := s_kstep hops hT hh hs1
    simp only [walkKC, hx', Bool.false_or, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveKC ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.1.2, hw2.1.2, hw2.2, k1, h1⟩

/-- **One frame, with the stores cut.** A walk from `S` that succeeds covers the frame of every machine of `S`, for every input, if each instruction meets `CleanK` and does not write a
byte of `l` by its address. -/
theorem frame_of_walkKC (ht : C.t.all (walkKC C l Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkKC C l Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, watchOK C.W B = true ∧ endOK C.G B = true ∧ C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveKC C l F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, watchOK C.W B = true ∧ endOK C.G B = true ∧ C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h2'', h3, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rw [e2]
        rcases live_stepKC ht hkl hops hT h1 (hk j) (hx j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a2'', a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', a2'', by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h2'', h3, h4⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h2', h2'', h3, h4⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact ⟨h1, B, h2, h2', h2'', h3, h4⟩

end

section
variable {E : Env} {F : Nat × UInt8}

/-- what the check of the walk with the stores cut says -/
structure KeepOKC (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (l : List Nat) (fin : AS → Bool) : Prop where
  late : G.late < dotsPerFrame
  table : (cfgOfKWC S G E W key l fin).t.all (walkKC (cfgOfKWC S G E W key l fin) l fuelK) = true
  s0 : walkKC (cfgOfKWC S G E W key l fin) l fuelK (startK G W false) = true
  s1 : walkKC (cfgOfKWC S G E W key l fin) l fuelK (startK G W true) = true

theorem keepOKC_of_check {S : Spot} {G : Guard} {W : List Watch} {key : AS → Nat} {l : List Nat} {fin : AS → Bool} (h : keepCheckC S G E W key l fin = true) :
    KeepOKC S G E W key l fin := by
  simp only [keepCheckC, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, _⟩, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- **The frame's end, with the stores cut**: a frame from `FrameStart` with the watched bits, whose instructions meet `CleanK` and do not write a byte of `l` by its address, ends in
a state with the watched bits, the start of a frame (`endOK`), and `fin` -/
theorem end_of_walkKC {S : Spot} {G : Guard} {W : List Watch} {key : AS → Nat} {l : List Nat} {fin : AS → Bool} (hc : keepCheckC S G E W key l fin = true) (hE : E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hw : Watched W m) (hk : ∀ j, CleanK G S.store (trace m i j))
    (hx : ∀ j, storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∃ B, watchOK W B = true ∧ endOK G B = true ∧ fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  have hC := keepOKC_of_check hc
  obtain ⟨b, hs⟩ := sim_startK hE h0 hw
  have hw0 : walkKC (cfgOfKWC S G E W key l fin) l fuelK (startK G W b) = true := by
    cases b with
    | false => exact hC.s0
    | true => exact hC.s1
  obtain ⟨_, B, h1, h2, h3, _, h4⟩ := frame_of_walkKC (C := cfgOfKWC S G E W key l fin) (F := (m.frame, 2)) hC.table rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hE hw0 hs hk hx
  exact ⟨B, h1, h2, h3, h4⟩

/-- the known bytes of the guard, from a state that knows them -/
theorem known_of_all {G : Guard} {B : AS} {m : Machine} (hs : Sim E F B m) (h : knownAll G B = true) : ∀ p ∈ G.known, m.ram.get! p.1 = p.2 := by
  intro p hp
  have h1 := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  obtain ⟨⟨h2, h3⟩, h4⟩ := h1
  rw [PipeEntryRule.known_eq h3 (hs.ram _ h2), h4]

/-- **A frame in control that does not write the three bytes by their addresses ends at the start of a frame in control**, and keeps the watched bits -/
theorem keep_frame_startC {S : Spot} {G : Guard} {W : List Watch} {key : AS → Nat} {l : List Nat} (hc : keepCheckC S G E W key l (knownAll G) = true) (hE : E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hw : Watched W m) (hk : ∀ j, CleanK G S.store (trace m i j))
    (hx : ∀ j, storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    FrameStart G E (frame m i) ∧ Watched W (frame m i) := by
  obtain ⟨B, h1, h2, h3, h4⟩ := end_of_walkKC hc hE h0 hw hk hx
  exact ⟨start_of_sim h4 h2 rfl rfl (known_of_all h4 h3), watched_of h1 h4⟩

end

/-! ## On the ROM -/

/-- the guard: that of `PipeWrites`, with the watched bytes among the bytes a store with a target not known does not touch -/
def guardK (sy : Syms) (m0 : Machine) : Guard :=
  let G := guardOf sy m0
  { G with prot := (sy.StarFlagTaskControl &&& 0x7FF).toNat :: (sy.SprObject_X_MoveForce &&& 0x7FF).toNat :: G.prot }

/-- the watched bits: the castle flag down, the fraction's low 4 bits 0 -/
def watchOf (sy : Syms) : List Watch :=
  [((sy.StarFlagTaskControl &&& 0x7FF).toNat, 0xFF, 0), ((sy.SprObject_X_MoveForce &&& 0x7FF).toNat, 0x0F, 0)]

/-- the move routine: its store of the fraction is its first `STA abs,X`, and its sum adds a zero page byte -/
def spotOf (sy : Syms) (m0 : Machine) : Spot :=
  let sum := findOp m0 sy.MoveObjectHorizontally 0x65 64
  { entry := sy.MoveObjectHorizontally, store := findOp m0 sy.MoveObjectHorizontally 0x9D 64, temps := [(romByte m0 (sum + 1)).toNat] }

/-- the value `v` is not in the byte: a known bit differs -/
def excl (b : AB) (v : UInt8) : Bool := v &&& b.k != b.v &&& b.k

/-- **The frame's end, for the frames of a run**: if the routine is the player's and the task is the core's, then the mode is the game's -/
def endCtl (sy : Syms) (B : AS) : Bool :=
  excl (B.getK (sy.GameEngineSubroutine &&& 0x7FF).toNat) sy.Eng_PlayerCtrl.toUInt8 ||
  excl (B.getK (sy.OperMode_Task &&& 0x7FF).toNat) sy.Task_GameCore.toUInt8 ||
  ((B.getK (sy.OperMode &&& 0x7FF).toNat).isK && (B.getK (sy.OperMode &&& 0x7FF).toNat).v == sy.GameModeValue.toUInt8)

/-- the table's key with the mode and the task: no part of the proof -/
def keyKC (sy : Syms) (S : Spot) (G : Guard) (W : List Watch) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  (keyK S G W A * 65536 + num (A.getK (sy.OperMode &&& 0x7FF).toNat)) * 65536 + num (A.getK (sy.OperMode_Task &&& 0x7FF).toNat)

/-- **The check on the ROM of the frames before the touch**: the walk with the stores of the routine, the mode and the task cut; at each frame's end the three bytes are known with
the values of control. The values fit in a byte. -/
def ctlKeepCheck (sy : Syms) (m0 : Machine) : Bool :=
  decide (sy.Eng_PlayerCtrl < 256) && decide (sy.Task_GameCore < 256) &&
    keepCheckC (spotOf sy m0) (guardK sy m0) (PipeEntryRule.envOf m0) (watchOf sy) (keyK (spotOf sy m0) (guardK sy m0) (watchOf sy)) (ctlI sy) (knownAll (guardK sy m0))

theorem ctlKeepCheck_parts {sy : Syms} {m0 : Machine} (h : ctlKeepCheck sy m0 = true) : sy.Eng_PlayerCtrl < 256 ∧ sy.Task_GameCore < 256 ∧
    keepCheckC (spotOf sy m0) (guardK sy m0) (PipeEntryRule.envOf m0) (watchOf sy) (keyK (spotOf sy m0) (guardK sy m0) (watchOf sy)) (ctlI sy) (knownAll (guardK sy m0)) = true := by
  simp only [ctlKeepCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The check on the ROM**: the walk with the mode and the task in the table's key, and at the frame's end `endCtl` too; and the walk with the stores of the three bytes of
control cut (`ctlKeepCheck`) -/
def keepCheckOf (sy : Syms) (m0 : Machine) : Bool :=
  (decide (sy.GameModeValue < 256) &&
    keepCheckW (spotOf sy m0) (guardK sy m0) (PipeEntryRule.envOf m0) (watchOf sy) (keyKC sy (spotOf sy m0) (guardK sy m0) (watchOf sy)) (endCtl sy)) &&
  ctlKeepCheck sy m0

/-- the walk of the frames of a run, without the end condition `endCtl`: no part of the proof -/
def keepCheckOld (sy : Syms) (m0 : Machine) : Bool := keepCheck (spotOf sy m0) (guardK sy m0) (PipeEntryRule.envOf m0) (watchOf sy)

/-- the routine is the player's and the task the core's: two of the three bytes of `controllable` -/
def ctlRT (sy : Syms) (m : Machine) : Bool :=
  (peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore && (peek m sy.GameEngineSubroutine).toUInt16 == sy.Eng_PlayerCtrl

/-- `Watched` as a check, for a program -/
def watchedB (W : List Watch) (m : Machine) : Bool := W.all fun w => m.ram.get! w.1 &&& w.2.1 == w.2.2 &&& w.2.1

/-- the store is the fraction's -/
def spotCheck (sy : Syms) (m0 : Machine) : Bool :=
  let q := (spotOf sy m0).store
  romByte m0 q == 0x9D && romByte m0 (q + 1) == sy.SprObject_X_MoveForce.toUInt8 && romByte m0 (q + 2) == (sy.SprObject_X_MoveForce >>> 8).toUInt8

/-! ## The castle flag and the fraction -/

section
variable {sy : Syms} {m0 m : Machine}

theorem and_ff (x : UInt8) : x &&& 0xFF = x := by
  apply bt_ext
  intro j hj
  rw [bt_and, TaintRun.bt_ff hj, Bool.and_true]

/-- the watched bits: the castle flag is down -/
theorem castle_of_watched (h : Watched (watchOf sy) m) : CastleWalk.castle sy m = false := by
  have h1 : m.ram.get! (sy.StarFlagTaskControl &&& 0x7FF).toNat &&& 0xFF = (0 : UInt8) &&& 0xFF := h _ List.mem_cons_self
  rw [and_ff, and_ff] at h1
  unfold CastleWalk.castle peek
  rw [h1]
  rfl

/-- the watched bits: the fraction is a multiple of 1/16 px -/
theorem frac_of_watched (h : Watched (watchOf sy) m) : posP sy m % 16 = 0 := by
  have h1 : m.ram.get! (sy.SprObject_X_MoveForce &&& 0x7FF).toNat &&& 0x0F = (0 : UInt8) &&& 0x0F := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have e : (peek m sy.SprObject_X_MoveForce &&& 0x0F).toNat = 0 := by
    unfold peek
    rw [h1]
    rfl
  rw [and0F] at e
  unfold posP
  omega

/-- the castle flag down and the fraction a multiple of 1/16 px are the watched bits -/
theorem watched_of_parts (h1 : CastleWalk.castle sy m = false) (h2 : posP sy m % 16 = 0) : Watched (watchOf sy) m := by
  intro w hw
  simp only [watchOf, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · show m.ram.get! (sy.StarFlagTaskControl &&& 0x7FF).toNat &&& 0xFF = (0 : UInt8) &&& 0xFF
    have e : peek m sy.StarFlagTaskControl = 0 := by
      unfold CastleWalk.castle at h1
      simpa using h1
    unfold peek at e
    rw [e]
  · show m.ram.get! (sy.SprObject_X_MoveForce &&& 0x7FF).toNat &&& 0x0F = (0 : UInt8) &&& 0x0F
    have e := and0F (peek m sy.SprObject_X_MoveForce)
    unfold posP at h2
    have e2 : (peek m sy.SprObject_X_MoveForce &&& 0x0F).toNat = ((0 : UInt8) &&& 0x0F).toNat := by
      rw [e]
      show _ = 0
      omega
    exact UInt8.toNat_inj.1 e2

end

/-! ## The frames of a run -/

/-- the start of a frame in control, as the walk needs it: `FrameStart` of the guard `guardK` -/
abbrev StartK (sy : Syms) (m0 m : Machine) : Prop := FrameStart (guardK sy m0) (PipeEntryRule.envOf m0) m

/-- **The machine at control, as the walk needs it**: the start of a frame in control, with the castle flag down -/
structure AtCtl (sy : Syms) (m0 m : Machine) : Prop where
  start : StartK sy m0 m
  castle : CastleWalk.castle sy m = false

theorem toUInt8_of_toUInt16 {x : UInt8} {v : UInt16} (h : x.toUInt16 = v) : x = v.toUInt8 := by
  subst h
  apply UInt8.toNat_inj.1
  simp

/-- the known bytes of `guardK` on a machine with control: the routine, the mode, the task -/
theorem known_of_ctl {sy : Syms} {m0 m : Machine} (h1 : controllable sy m = true) :
    ∀ p ∈ (guardK sy m0).known, m.ram.get! p.1 = p.2 := by
  have e : (guardK sy m0).known = [((sy.GameEngineSubroutine &&& 0x7FF).toNat, sy.Eng_PlayerCtrl.toUInt8), ((sy.OperMode &&& 0x7FF).toNat, sy.GameModeValue.toUInt8),
      ((sy.OperMode_Task &&& 0x7FF).toNat, sy.Task_GameCore.toUInt8)] := rfl
  rw [e]
  simp only [controllable, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨a1, a2⟩, a3⟩ := h1
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact toUInt8_of_toUInt16 a3
  · exact toUInt8_of_toUInt16 a1
  · exact toUInt8_of_toUInt16 a2

/-- the parts of the check -/
theorem keepCheckOf_parts {sy : Syms} {m0 : Machine} (h : keepCheckOf sy m0 = true) : sy.GameModeValue < 256 ∧
    keepCheckW (spotOf sy m0) (guardK sy m0) (PipeEntryRule.envOf m0) (watchOf sy) (keyKC sy (spotOf sy m0) (guardK sy m0) (watchOf sy)) (endCtl sy) = true := by
  simp only [keepCheckOf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- the walk with the stores cut, from the check -/
theorem keepCheckOf_ctl {sy : Syms} {m0 : Machine} (h : keepCheckOf sy m0 = true) : ctlKeepCheck sy m0 = true := by
  simp only [keepCheckOf, Bool.and_eq_true] at h
  exact h.2

theorem excl_false {b : AB} {x : UInt8} (hm : b.mem x) : excl b x = false := by
  simp only [excl, bne_eq_false_iff_eq]
  exact hm

/-- **`endCtl` on the machine**: a state of the frame's end that meets `endCtl` covers a machine; if the machine has the routine and the task of control, it has control -/
theorem ctl_of_endCtl {sy : Syms} {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} (hg : sy.GameModeValue < 256) (hs : Sim E F B m) (he : endCtl sy B = true)
    (hc : ctlRT sy m = true) : controllable sy m = true := by
  simp only [ctlRT, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨h1, h2⟩ := hc
  have e1 : m.ram.get! (sy.OperMode_Task &&& 0x7FF).toNat = sy.Task_GameCore.toUInt8 := toUInt8_of_toUInt16 h1
  have e2 : m.ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat = sy.Eng_PlayerCtrl.toUInt8 := toUInt8_of_toUInt16 h2
  have m1 := hs.ram _ (PipeTransitionAll.mask_lt sy.OperMode_Task)
  have m2 := hs.ram _ (PipeTransitionAll.mask_lt sy.GameEngineSubroutine)
  have m3 := hs.ram _ (PipeTransitionAll.mask_lt sy.OperMode)
  rw [e1] at m1
  rw [e2] at m2
  simp only [endCtl, excl_false m1, excl_false m2, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨hk, hv⟩ := he
  have e3 : m.ram.get! (sy.OperMode &&& 0x7FF).toNat = sy.GameModeValue.toUInt8 := by rw [PipeEntryRule.known_eq hk m3, hv]
  have hg' : sy.GameModeValue.toNat < 256 := UInt16.lt_iff_toNat_lt.1 hg
  have e4 : (peek m sy.OperMode).toUInt16 = sy.GameModeValue := by
    unfold peek
    rw [e3]
    apply UInt16.toNat_inj.1
    simp
    omega
  simp only [controllable, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨e4, h1⟩, h2⟩

/-- **A frame in control that ends with the routine and the task of control ends in control.** The walk of `keepCheckOf` from the frame's start, with `endCtl` at the frame's end. -/
theorem ctl_of_frame {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : keepCheckOf sy m0 = true) (h0 : StartK sy m0 m) (hw : Watched (watchOf sy) m)
    (hk : ∀ j, CleanK (guardK sy m0) (spotOf sy m0).store (trace m i j)) (h1 : ctlRT sy (frame m i) = true) : controllable sy (frame m i) = true := by
  obtain ⟨hg, hW⟩ := keepCheckOf_parts hc
  obtain ⟨B, _, _, h2, h3⟩ := end_of_walkW hW rfl h0 hw hk
  exact ctl_of_endCtl hg h3 h2 h1

theorem toUInt16_of_lt {x : UInt8} {v : UInt16} (h : x = v.toUInt8) (hv : v < 256) : x.toUInt16 = v := by
  have hv' : v.toNat < 256 := UInt16.lt_iff_toNat_lt.1 hv
  subst h
  apply UInt16.toNat_inj.1
  simp
  omega

/-- **The known bytes of `guardK` give control** -/
theorem ctl_of_known {sy : Syms} {m0 m : Machine} (h1 : sy.GameModeValue < 256) (h2 : sy.Task_GameCore < 256) (h3 : sy.Eng_PlayerCtrl < 256)
    (h : ∀ p ∈ (guardK sy m0).known, m.ram.get! p.1 = p.2) : controllable sy m = true := by
  have e : (guardK sy m0).known = [((sy.GameEngineSubroutine &&& 0x7FF).toNat, sy.Eng_PlayerCtrl.toUInt8), ((sy.OperMode &&& 0x7FF).toNat, sy.GameModeValue.toUInt8),
      ((sy.OperMode_Task &&& 0x7FF).toNat, sy.Task_GameCore.toUInt8)] := rfl
  rw [e] at h
  have a1 := h _ List.mem_cons_self
  have a2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have a3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [controllable, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨toUInt16_of_lt a2 h1, toUInt16_of_lt a3 h2⟩, toUInt16_of_lt a1 h3⟩

/-- **A run of real frames.** `seq n` is the machine when frame `n` begins, counted or not, and `inp n` its input. Each frame is the real frame of the one before.
The parts of the route take their machines from one such run (`Route.Run.base`). -/
structure RealRun where
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (inp n)

/-! ## The counted frames: the frames that end not paused

A frame is counted when it ends with the game not paused. `upTo f n` counts the frames `1, …, n` for which `f` holds, and the counted frame `j` is the first frame
`n` with `j ≤ upTo f n` (`firstLe`). No game data: the pause byte is read through `sy` and the ROM of `m0`, as `CtrlKeep.pauseI`. -/

/-- of the frames `1, …, n`, the number for which `f` holds -/
def upTo (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => upTo f n + (if f (n + 1) then 1 else 0)

/-- the first `n ≤ N` with `p n`, or `N` if there is none -/
def firstLe (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N + 1 => if p (firstLe p N) then firstLe p N else N + 1

theorem upTo_succ (f : Nat → Bool) (n : Nat) : upTo f (n + 1) = upTo f n + (if f (n + 1) then 1 else 0) := rfl

theorem upTo_mono (f : Nat → Bool) {n k : Nat} (h : n ≤ k) : upTo f n ≤ upTo f k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = n + d := ⟨k - n, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    rw [show n + (d + 1) = n + d + 1 by omega, upTo_succ]
    have := ih (by omega)
    omega

theorem upTo_succ_le (f : Nat → Bool) (n : Nat) : upTo f (n + 1) ≤ upTo f n + 1 := by
  rw [upTo_succ]
  split <;> omega

theorem firstLe_le (p : Nat → Bool) : ∀ N, firstLe p N ≤ N
  | 0 => Nat.le_refl _
  | N + 1 => by
    have := firstLe_le p N
    simp only [firstLe]
    split <;> omega

/-- **The first `n ≤ N` with `p n`**: if there is one, `firstLe` is one, and no smaller `n` has `p n` -/
theorem firstLe_spec (p : Nat → Bool) : ∀ N, (∃ n, n ≤ N ∧ p n = true) → p (firstLe p N) = true ∧ ∀ k, k < firstLe p N → p k = false
  | 0, ⟨n, hn, hp⟩ => by
    have e : n = 0 := by omega
    subst e
    exact ⟨hp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | N + 1, ⟨n, hn, hp⟩ => by
    by_cases h : ∃ n, n ≤ N ∧ p n = true
    · obtain ⟨h1, h2⟩ := firstLe_spec p N h
      have e : firstLe p (N + 1) = firstLe p N := by simp only [firstLe, h1, if_true]
      rw [e]
      exact ⟨h1, h2⟩
    · have hno : ∀ k, k ≤ N → p k = false := fun k hk => by
        cases hk' : p k with
        | false => rfl
        | true => exact absurd ⟨k, hk, hk'⟩ h
      have hf := hno _ (firstLe_le p N)
      have e : firstLe p (N + 1) = N + 1 := by simp [firstLe, hf]
      rw [e]
      have hN : n = N + 1 := by
        by_cases e : n ≤ N
        · rw [hno n e] at hp
          cases hp
        · omega
      subst hN
      exact ⟨hp, fun k hk => hno k (by omega)⟩

/-- `firstLe` is `0` when `p 0` holds -/
theorem firstLe_zero (p : Nat → Bool) (h : p 0 = true) : ∀ N, firstLe p N = 0
  | 0 => rfl
  | N + 1 => by
    have e := firstLe_zero p h N
    simp only [firstLe, e, h, if_true]

/-- the `j`-th frame for which `f` holds, among the frames up to `N` -/
def nthUp (f : Nat → Bool) (N j : Nat) : Nat := firstLe (fun n => decide (j ≤ upTo f n)) N

section
variable {f : Nat → Bool} {N : Nat}

theorem nthUp_spec {j : Nat} (h : j ≤ upTo f N) : nthUp f N j ≤ N ∧ j ≤ upTo f (nthUp f N j) ∧ ∀ k, k < nthUp f N j → upTo f k < j := by
  obtain ⟨h1, h2⟩ := firstLe_spec (fun n => decide (j ≤ upTo f n)) N ⟨N, Nat.le_refl _, by simp [h]⟩
  refine ⟨firstLe_le _ N, by simpa using h1, fun k hk => ?_⟩
  have := h2 k hk
  simp only [decide_eq_false_iff_not, Nat.not_le] at this
  exact this

theorem nthUp_zero : nthUp f N 0 = 0 := firstLe_zero _ (by simp) N

/-- **The `j`-th frame for which `f` holds**: `f` holds there, and `j` frames up to it -/
theorem nthUp_at {j : Nat} (h1 : 1 ≤ j) (h : j ≤ upTo f N) : 1 ≤ nthUp f N j ∧ f (nthUp f N j) = true ∧ upTo f (nthUp f N j) = j := by
  obtain ⟨_, a2, a3⟩ := nthUp_spec h
  generalize nthUp f N j = n at a2 a3
  cases n with
  | zero => exact absurd a2 (by simp [upTo]; omega)
  | succ k =>
    have b := a3 k (by omega)
    rw [upTo_succ] at a2 ⊢
    cases hf : f (k + 1) with
    | false =>
      rw [hf] at a2
      simp at a2
      omega
    | true =>
      rw [hf] at a2
      simp at a2
      refine ⟨by omega, rfl, ?_⟩
      simp
      omega

/-- the counted frames come in order -/
theorem nthUp_lt {j : Nat} (h : j + 1 ≤ upTo f N) : nthUp f N j < nthUp f N (j + 1) := by
  have hle : upTo f (nthUp f N j) ≤ j := by
    cases j with
    | zero => rw [nthUp_zero]; simp [upTo]
    | succ j =>
      rw [(nthUp_at (f := f) (N := N) (j := j + 1) (by omega) (by omega)).2.2]
      exact Nat.le_refl _
  obtain ⟨_, a2, _⟩ := nthUp_spec h
  apply Nat.lt_of_not_le
  intro hn
  have := upTo_mono f hn
  omega

/-- **Between two counted frames `f` does not hold** -/
theorem nthUp_between {j n : Nat} (h1 : 1 ≤ j) (h : j ≤ upTo f N) (hn1 : nthUp f N (j - 1) ≤ n) (hn2 : n + 1 < nthUp f N j) : f (n + 1) = false := by
  obtain ⟨_, _, a3⟩ := nthUp_spec h
  obtain ⟨_, b2, _⟩ := nthUp_spec (f := f) (N := N) (j := j - 1) (by omega)
  have c1 := a3 (n + 1) hn2
  have c2 := upTo_mono f hn1
  rw [upTo_succ] at c1
  cases hf : f (n + 1) with
  | false => rfl
  | true =>
    rw [hf] at c1
    simp at c1
    omega

end

/-- **The pause byte**, as `CtrlKeep.pauseI`: the operand of the load just before the NMI's call of the mode's routine. Its low bit is 1 while the game is paused. -/
def pauseI (sy : Syms) (m0 : Machine) : Nat :=
  (((romByte m0 (LagFrames.modeCall sy - 5)).toUInt16 ||| ((romByte m0 (LagFrames.modeCall sy - 4)).toUInt16 <<< 8)) &&& 0x7FF).toNat

/-- **The game is not paused** on the machine `m`: the low bit of the pause byte is 0 (as `CtrlKeep.Unpaused`) -/
def Unpaused (sy : Syms) (m0 m : Machine) : Prop := m.ram.get! (pauseI sy m0) &&& 1 = 0

/-- the frame of the run `S` that ends at `S.seq (a + n)` ends with the game not paused -/
def upAt (sy : Syms) (m0 : Machine) (S : RealRun) (a n : Nat) : Bool := (S.seq (a + n)).ram.get! (pauseI sy m0) &&& 1 == 0

/-- **The counted frame `j`** of the run `S` from frame `a` on: the `j`-th frame that ends with the game not paused, among the frames up to `N`. The counted frame 0 is
frame `a`. -/
abbrev ixOf (sy : Syms) (m0 : Machine) (S : RealRun) (a N j : Nat) : Nat := nthUp (upAt sy m0 S a) N j

/-- **The bytes that no frame of a run writes through an index or a pointer**, besides those of `guardK`: the pause byte, the area's type, the swimming flag, the change of
size (as `CtrlKeep.spareI`) -/
def spareK (sy : Syms) (m0 : Machine) : List Nat :=
  [pauseI sy m0, (sy.AreaType &&& 0x7FF).toNat, (sy.SwimmingFlag &&& 0x7FF).toNat, (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat]

/-- **A guard of the frames of a run**: `guardK`, with the bytes of `spareK` protected too (as `CtrlKeep.guardP` with `CtrlKeep.spareI`). The walks of this file use
`guardK`; the walks of `PrevKeep` and `AfterKeep` use this guard with a few more bytes. The condition on each instruction of the frames of a run is `CleanK` of
`guardE`, which gives `CleanK` of this guard (`Frames.cleanF`). -/
def guardF (sy : Syms) (m0 : Machine) : Guard := { guardK sy m0 with prot := spareK sy m0 ++ (guardK sy m0).prot }

/-- `CleanK` with more bytes protected gives `CleanK` -/
theorem cleanK_weak {G : Guard} {l : List Nat} {q : UInt16} {m : Machine} (h : CleanK { G with prot := l ++ G.prot } q m) : CleanK G q m := by
  refine ⟨fun t ht hq => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht hq with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h1, fun h3 => h2 (List.mem_append_right _ h3)⟩
  · exact Or.inr h1

/-- `CleanK` of `guardF` gives `CleanK` of `guardK` -/
theorem cleanK_of_F {sy : Syms} {m0 : Machine} {q : UInt16} {m : Machine} (h : CleanK (guardF sy m0) q m) : CleanK (guardK sy m0) q m := cleanK_weak h

/-- **Five bytes of the player's routine that no frame of a run writes through an index or a pointer**: A and B, A and B of the frame before, the moving direction,
the running speed, the stored speed (the bytes of `AfterKeep.eI`, of the old field `spareE` of the frames above ground) -/
def spareE (sy : Syms) : List Nat :=
  [(sy.A_B_Buttons &&& 0x7FF).toNat, (sy.PreviousA_B_Buttons &&& 0x7FF).toNat, (sy.Player_MovingDir &&& 0x7FF).toNat, (sy.RunningSpeed &&& 0x7FF).toNat,
    (sy.Player_XSpeedAbsolute &&& 0x7FF).toNat]

/-- **The player's collision bits**, which no frame of a run writes through an index or a pointer (the old field `spareC` of the frames above ground) -/
def collE (sy : Syms) : List Nat := [(sy.Player_CollisionBits &&& 0x7FF).toNat]

/-- **The player's speed**, which no frame of a run writes through an index or a pointer (the old field `spareV` of the frames above ground) -/
def speedE (sy : Syms) : List Nat := [(sy.Player_X_Speed &&& 0x7FF).toNat]

/-- **Three vertical bytes of the player**, which no frame of a run writes through an index or a pointer: the vertical force down, the jump's origin, the jump's halt value
(`VertKeep.kI`: a part of the old field `vAfter` of the frames above ground) -/
def vertE (sy : Syms) : List Nat :=
  [(sy.VerticalForceDown &&& 0x7FF).toNat, (sy.JumpOrigin_Y_Position &&& 0x7FF).toNat, (sy.DiffToHaltJump &&& 0x7FF).toNat]

/-- **The player's facing and subspeed**, which no frame of a run writes through an index or a pointer (`FaceKeep.zI`: the facing of the old field `after` and the
subspeed of the old field `collide` of the frames above ground) -/
def faceE (sy : Syms) : List Nat := [(sy.PlayerFacingDir &&& 0x7FF).toNat, (sy.Player_X_MoveForce &&& 0x7FF).toNat]

/-- **The player's state and the vertical force**, which no frame of a run writes through an index or a pointer (the walk of the vertical force, `FaceKeep.vf_end`:
a part of the old field `vAfter` of the frames above ground) -/
def stateE (sy : Syms) : List Nat := [(sy.Player_State &&& 0x7FF).toNat, (sy.VerticalForce &&& 0x7FF).toNat]

/-- a word of the program, its low byte first (round 26) -/
def romWE (m0 : Machine) (a : UInt16) : UInt16 := (romByte m0 a).toUInt16 ||| ((romByte m0 (a + 1)).toUInt16 <<< 8)

/-- **The screen's left edge, its pixel and its page** (round 26), which no frame of a run writes through an index or a pointer: the operands of the two loads of the
clamp at the screen's edge, found from the scroll handler's call as `ScreenClamp.places` finds them (`EdgeStep.eI`; the walks of `EdgeStep` follow them). Round 27:
and the platforms' force on the scroll (`Platform_X_Scroll`), which the walks of `EdgeStep` follow too (it is 0 at the scroll handler: `SurfaceFrames.OnFrames.platQ`) -/
def edgeE (sy : Syms) (m0 : Machine) : List Nat :=
  let entry := PipeEntryRule.findOp m0 (romWE m0 (sy.PlayerSubs + 1)) 0xB9 256
  let pg := PipeEntryRule.findOp m0 (entry + 1) 0xB9 32
  [(romWE m0 (entry + 1) &&& 0x7FF).toNat, (romWE m0 (pg + 1) &&& 0x7FF).toNat, (sy.Platform_X_Scroll &&& 0x7FF).toNat]

/-- **The area parser's task routine** (round 29): in `UpdScrollVar` its call of the task handler, in the handler its call of the task routine; that routine's
first entry is the column's step (as `PoleParser.places`) -/
def parRt (sy : Syms) (m0 : Machine) : UInt16 :=
  let h := romWE m0 (sy.UpdScrollVar + 0x21)
  let t := romWE m0 (h + 0x0D)
  romWE m0 (t + 3)

/-- **The area parser's four bytes** (round 29), which no frame of a run writes through an index or a pointer: the tasks left, the scroll counter of 32 px, the
parser's column in its page and its page, found from the code of `UpdScrollVar` as `PoleParser.places` finds them (`PoleParser.pI` is this list, `PoleParserRun.pI_eq`):
the operands of its load of the task count and of its load of the scroll counter; its call of the task handler, the handler's call of the task routine, whose first
entry is the column's step, with its two `INC`s -/
def parE (sy : Syms) (m0 : Machine) : List Nat :=
  [romWE m0 (sy.UpdScrollVar + 8), romWE m0 (sy.UpdScrollVar + 13), romWE m0 (parRt sy m0 + 1), romWE m0 (parRt sy m0 + 0x0E)].map fun a => (a &&& 0x7FF).toNat

/-- **The guard of the condition on each instruction of the frames of a run** (`Frames.cleanE`): `guardF`, with the screen's left edge and the platforms' force on the
scroll (`edgeE`, rounds 26 and 27), the area parser's four bytes (`parE`, round 29), the player's
state and the vertical force (`stateE`), the facing and the subspeed (`faceE`), the bytes of `spareE`, the collision bits (`collE`), the speed (`speedE`) and three
vertical bytes (`vertE`) protected too. The walks of this file use `guardK` or `guardF`, and `CleanK` of `guardE` gives both (`cleanK_of_E`, `cleanK_sub`); the walk of
`PhaseFrame` uses `guardE` with two more bytes. -/
def guardE (sy : Syms) (m0 : Machine) : Guard :=
  { guardF sy m0 with prot := edgeE sy m0 ++ (parE sy m0 ++ stateE sy) ++ faceE sy ++ spareE sy ++ collE sy ++ speedE sy ++ vertE sy ++ (guardF sy m0).prot }

/-- `CleanK` of `guardE` gives `CleanK` of `guardF` -/
theorem cleanK_of_E {sy : Syms} {m0 : Machine} {q : UInt16} {m : Machine} (h : CleanK (guardE sy m0) q m) : CleanK (guardF sy m0) q m := cleanK_weak h

/-- **`CleanK` with fewer protected bytes**: a guard that differs only in its protected bytes, each of them protected by `G` -/
theorem cleanK_sub {G G' : Guard} {q : UInt16} {m : Machine} (h : CleanK G q m) (hp : ∀ x ∈ G'.prot, x ∈ G.prot) (hi : G'.idle = G.idle) (hl : G'.late = G.late)
    (hj : G'.je = G.je) (hjs : G'.jumps = G.jumps) : CleanK G' q m := by
  refine ⟨fun t ht hq => ?_, h.read, fun hpc n hn => h.jump (hj ▸ hpc) n (hjs ▸ hn), fun hpc => hl ▸ h.time (hi ▸ hpc)⟩
  rcases h.store t ht hq with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h1, fun h3 => h2 (hp _ h3)⟩
  · exact Or.inr h1

/-- **The frames of a run, as the walk needs them.** They are the frames of the real run `S` from frame `a` on: `all n = S.seq (a + n)` is the machine when frame `n` begins,
counted or not, from the machine at control (`all 0`) on, and `inp n` its input. These are definitions, so `all 0` is `S.seq a`, and each frame is the real frame of
the one before (`Frames.next`). A frame is counted when it ends with the game not paused (`upAt`): the counted frame `j` ends at `all (ix j)`, the `j`-th such end, also by
definition (`ixOf`). So the counted frames come in order (`Frames.order`), each ends not paused (`Frames.up`), and the frames between two counted frames, the `lag` frames,
end paused (`Frames.down`). `seq j` is the machine at the end of the counted frame `j`. Every field is a hypothesis.
That each frame starts in the idle loop in control (`StartK`) is not a field: it follows from the machine at control, `noStore` and `clean` (`Frames.all_start`), and so do the
watched bits of the `lag` frames. That each frame before the touch's frame ends in control is a theorem too (`Frames.ctlAll`): the walk with the stores of the three bytes cut. -/
structure Frames (sy : Syms) (m0 : Machine) (S : RealRun) (a : Nat) (g : Nat) (seq : Nat → Machine) where
  /-- a frame from control by whose end `g` frames have ended not paused: the search for the counted frames looks up to it -/
  top : Nat
  /-- `g` frames end not paused by the end of frame `top` -/
  many : g ≤ upTo (upAt sy m0 S a) top
  /-- the counted frame `j` ends at `seq j` -/
  seqAt : ∀ j, j ≤ g → seq j = S.seq (a + ixOf sy m0 S a top j)
  /-- no instruction of a frame before the touch's frame, counted or not, writes the routine, the mode or the task byte by its address -/
  noStore : ∀ n, n + 1 < ixOf sy m0 S a top g → ∀ k, CtlStore sy (trace (S.seq (a + n)) (S.inp (a + n)) k) = false
  /-- each instruction of each frame up to the touch's frame, counted or not, meets `CleanK` of `guardE`: no store through an index or a pointer writes the bytes of
  `guardK` (but the player's own store of the fraction), the pause byte, the area's type, the swimming flag, the change of size, A and B, A and B of the frame before,
  the moving direction, the running speed, the stored speed, the player's collision bits, the player's speed, the vertical force down, the jump's origin, the jump's
  halt value, the player's facing, the player's subspeed, the player's state, the vertical force, the screen's left edge (round 26) or the area parser's four
  bytes (round 29: `parE`) -/
  cleanE : ∀ n, n < ixOf sy m0 S a top g → ∀ k, CleanK (guardE sy m0) (spotOf sy m0).store (trace (S.seq (a + n)) (S.inp (a + n)) k)

section
variable {sy : Syms} {m0 : Machine} {S : RealRun} {a : Nat} {g : Nat} {seq : Nat → Machine}

/-- the machine when frame `n` begins, counted or not: frame `a + n` of the real run -/
abbrev Frames.all (_K : Frames sy m0 S a g seq) (n : Nat) : Machine := S.seq (a + n)

/-- the input of frame `n` -/
abbrev Frames.inp (_K : Frames sy m0 S a g seq) (n : Nat) : UInt8 := S.inp (a + n)

/-- each frame is the real frame of the one before: from the real run -/
theorem Frames.next (K : Frames sy m0 S a g seq) (n : Nat) : K.all (n + 1) = frame (K.all n) (K.inp n) := S.next (a + n)

/-- **The counted frame `j` ends at `all (ix j)`**: the `j`-th frame from control that ends not paused (a definition, `ixOf`) -/
abbrev Frames.ix (K : Frames sy m0 S a g seq) (j : Nat) : Nat := ixOf sy m0 S a K.top j

/-- the counted frame `j` ends at `seq j` (the field `seqAt`) -/
theorem Frames.at_ix (K : Frames sy m0 S a g seq) : ∀ j, j ≤ g → seq j = S.seq (a + K.ix j) := K.seqAt

/-- the counted frame 0 is control: the field `ix0` of before -/
theorem Frames.ix0 (K : Frames sy m0 S a g seq) : K.ix 0 = 0 := nthUp_zero

/-- **The counted frames come in order**: the field `order` of before, now from the definition -/
theorem Frames.order (K : Frames sy m0 S a g seq) : ∀ j, j < g → K.ix j < K.ix (j + 1) :=
  fun _ hj => nthUp_lt (Nat.le_trans hj K.many)

/-- **A counted frame ends with the game not paused**: by the definition -/
theorem Frames.up (K : Frames sy m0 S a g seq) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ g) : Unpaused sy m0 (seq j) := by
  have h := (nthUp_at (f := upAt sy m0 S a) h1 (Nat.le_trans h2 K.many)).2.1
  rw [K.at_ix j h2]
  simpa [upAt] using h

/-- **A frame between two counted frames, a `lag` frame, ends with the game paused**: by the definition -/
theorem Frames.down (K : Frames sy m0 S a g seq) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ g) {n : Nat} (hn1 : K.ix (j - 1) ≤ n) (hn2 : n + 1 < K.ix j) :
    ¬ Unpaused sy m0 (K.all (n + 1)) := by
  have h := nthUp_between (f := upAt sy m0 S a) h1 (Nat.le_trans h2 K.many) hn1 hn2
  intro hu
  have e : upAt sy m0 S a (n + 1) = true := by
    simp only [upAt, beq_iff_eq]
    exact hu
  rw [e] at h
  cases h

/-- **Each instruction meets `CleanK`** of `guardF`, on each frame up to the touch's frame: from `cleanE` (it was the field `cleanF`) -/
theorem Frames.cleanF (K : Frames sy m0 S a g seq) : ∀ n, n < K.ix g → ∀ k, CleanK (guardF sy m0) (spotOf sy m0).store (trace (S.seq (a + n)) (S.inp (a + n)) k) :=
  fun n hn k => cleanK_of_E (K.cleanE n hn k)

/-- **Each instruction meets `CleanK`** of `guardK`, on each frame up to the touch's frame: from `cleanE` -/
theorem Frames.clean (K : Frames sy m0 S a g seq) : ∀ n, n < K.ix g → ∀ k, CleanK (guardK sy m0) (spotOf sy m0).store (trace (S.seq (a + n)) (S.inp (a + n)) k) :=
  fun n hn k => cleanK_of_F (K.cleanF n hn k)

/-- the machine at control is the real run's frame `a` -/
theorem Frames.seq0 (K : Frames sy m0 S a g seq) : seq 0 = S.seq a := by
  rw [K.at_ix 0 (Nat.zero_le _), K.ix0]
  rfl

/-- the machine when the counted frame `j` begins: `seq (j − 1)`, or later by `lag` frames -/
def Frames.fm (K : Frames sy m0 S a g seq) (j : Nat) : Machine := K.all (K.ix j - 1)

/-- the input of the counted frame `j` -/
def Frames.pad (K : Frames sy m0 S a g seq) (j : Nat) : UInt8 := K.inp (K.ix j - 1)

/-- the counted frames come in order -/
theorem Frames.ix_mono (K : Frames sy m0 S a g seq) : ∀ j k, j ≤ k → k ≤ g → K.ix j + (k - j) ≤ K.ix k := by
  intro j k hjk hk
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := K.order (j + d) (by omega)
    rw [show j + (d + 1) = j + d + 1 by omega]
    omega

/-- the counted frame `j` begins after control -/
theorem Frames.one_le_ix (K : Frames sy m0 S a g seq) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ g) : 1 ≤ K.ix j := by
  have h := K.ix_mono 0 j (by omega) h2
  omega

/-- **The counted frame `j` ends at `seq j`**: the field `ends` of before, now a theorem -/
theorem Frames.ends (K : Frames sy m0 S a g seq) : ∀ j, 1 ≤ j → j ≤ g → seq j = frame (K.fm j) (K.pad j) := by
  intro j h1 h2
  have h := K.one_le_ix h1 h2
  rw [K.at_ix j h2, Frames.fm, Frames.pad, ← K.next]
  congr 1
  omega

/-- **Each instruction of the counted frame `j` meets `CleanK`**: the field `clean` read at the counted frames -/
theorem Frames.cleanAt (K : Frames sy m0 S a g seq) : ∀ j, 1 ≤ j → j ≤ g → ∀ n, CleanK (guardK sy m0) (spotOf sy m0).store (trace (K.fm j) (K.pad j) n) := by
  intro j h1 h2
  have a := K.ix_mono j g h2 (Nat.le_refl g)
  have b := K.one_le_ix h1 h2
  exact K.clean (K.ix j - 1) (by omega)

/-- **Every frame up to the touch's frame starts in the idle loop in control with the watched bits**, counted or not, from the machine at control on. `hc` is the walk's check
on the ROM. -/
theorem Frames.all_start (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ n, n < K.ix g → StartK sy m0 (K.all n) ∧ Watched (watchOf sy) (K.all n) := by
  have e0 : seq 0 = K.all 0 := by rw [K.at_ix 0 (Nat.zero_le _), K.ix0]
  intro n
  induction n with
  | zero => exact fun _ => ⟨e0 ▸ hs0, e0 ▸ h0⟩
  | succ i ih =>
    intro hi
    obtain ⟨a1, a2⟩ := ih (by omega)
    rw [K.next i]
    exact keep_frame_startC (ctlKeepCheck_parts (keepCheckOf_ctl hc)).2.2 rfl a1 a2 (K.clean i (by omega)) (K.noStore i hi)

/-- **Every frame up to the touch's frame ends with the watched bits**, counted or not -/
theorem Frames.all_watched (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ n, n ≤ K.ix g → Watched (watchOf sy) (K.all n) := by
  intro n hn
  cases n with
  | zero =>
    have e0 : seq 0 = K.all 0 := by rw [K.at_ix 0 (Nat.zero_le _), K.ix0]
    exact e0 ▸ h0
  | succ i =>
    obtain ⟨a1, a2⟩ := K.all_start hc hs0 h0 i (by omega)
    rw [K.next i]
    exact keep_frameW (keepCheckOf_parts hc).2 rfl a1 a2 (K.clean i (by omega))

/-- **Every frame before the touch's frame ends in control**, counted or not: the old field `ctl`, now from `noStore` and the walk with the stores cut -/
theorem Frames.ctlAll (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ n, n + 1 < K.ix g → controllable sy (K.all (n + 1)) = true := by
  intro n hn
  obtain ⟨a1, a2⟩ := K.all_start hc hs0 h0 n (by omega)
  rw [K.next n]
  obtain ⟨h1, h2, hW⟩ := ctlKeepCheck_parts (keepCheckOf_ctl hc)
  obtain ⟨B, _, _, hf, hs⟩ := end_of_walkKC hW rfl a1 a2 (K.clean n (by omega)) (K.noStore n hn)
  exact ctl_of_known (keepCheckOf_parts hc).1 h2 h1 (known_of_all hs hf)

/-- **The ends of the frames before `g`** are starts of frames in control with the watched bits, from the machine at control on. `hc` is the walk's check on the ROM. -/
theorem Frames.run (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ j, j < g → StartK sy m0 (seq j) ∧ Watched (watchOf sy) (seq j) := by
  intro j hj
  have h := K.ix_mono j g (by omega) (Nat.le_refl _)
  rw [K.at_ix j (by omega)]
  exact K.all_start hc hs0 h0 (K.ix j) (by omega)

/-- **Each frame up to `g` starts in the idle loop in control** (`StartK`): the field `start` of before, now a theorem -/
theorem Frames.start (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ j, 1 ≤ j → j ≤ g → StartK sy m0 (K.fm j) := by
  intro j h1 h2
  have h := K.ix_mono j g h2 (Nat.le_refl _)
  have h3 := K.one_le_ix h1 h2
  exact (K.all_start hc hs0 h0 (K.ix j - 1) (by omega)).1

/-- **Every frame keeps the watched bits**, from the machine at control on. `hc` is the walk's check on the ROM. -/
theorem Frames.watched (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ j, j ≤ g → Watched (watchOf sy) (seq j) := by
  intro j hj
  have h := K.ix_mono j g hj (Nat.le_refl _)
  rw [K.at_ix j hj]
  exact K.all_watched hc hs0 h0 (K.ix j) (by omega)

/-- no castle flag up to frame `g` -/
theorem Frames.noCastle (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ j, j ≤ g → CastleWalk.castle sy (seq j) = false :=
  fun j hj => castle_of_watched (K.watched hc hs0 h0 j hj)

/-- the fraction is a multiple of 1/16 px up to frame `g` -/
theorem Frames.frac (hc : keepCheckOf sy m0 = true) (K : Frames sy m0 S a g seq) (hs0 : StartK sy m0 (seq 0)) (h0 : Watched (watchOf sy) (seq 0)) :
    ∀ j, j ≤ g → posP sy (seq j) % 16 = 0 :=
  fun j hj => frac_of_watched (K.watched hc hs0 h0 j hj)

end

/-! ## The frames of a run with their ends defined

`Frames` takes the machine at the end of each counted frame as a parameter `seq`, tied to the run up to the touch by the field `seqAt`. `Keep` has no such parameter: the
machine at the end of the counted frame `j` is frame `a + ix j` of the run, by definition (`Keep.seq`), for every `j`, before the touch and after it. It is the end of the
`j`-th frame that ends not paused whenever `j` such frames end by the end of frame `top` (`Keep.up_at`, `Keep.ends_at`). `Keep.toFrames` gives the same frames as `Frames`,
with `seqAt` true by the definition. -/

/-- **The frames of a run from control on**, up to the touch `g`: the fields of `Frames` without `seq` and `seqAt`. The machine at the end of the counted frame `j` is
defined from the run (`Keep.seq`). Every field is a hypothesis. -/
structure Keep (sy : Syms) (m0 : Machine) (S : RealRun) (a : Nat) (g : Nat) where
  /-- a frame from control by whose end `g` frames have ended not paused: the search for the counted frames looks up to it -/
  top : Nat
  /-- `g` frames end not paused by the end of frame `top` -/
  many : g ≤ upTo (upAt sy m0 S a) top
  /-- no instruction of a frame before the touch's frame, counted or not, writes the routine, the mode or the task byte by its address -/
  noStore : ∀ n, n + 1 < ixOf sy m0 S a top g → ∀ k, CtlStore sy (trace (S.seq (a + n)) (S.inp (a + n)) k) = false
  /-- each instruction of each frame up to the touch's frame, counted or not, meets `CleanK` of `guardE` -/
  cleanE : ∀ n, n < ixOf sy m0 S a top g → ∀ k, CleanK (guardE sy m0) (spotOf sy m0).store (trace (S.seq (a + n)) (S.inp (a + n)) k)

section
variable {sy : Syms} {m0 : Machine} {S : RealRun} {a : Nat} {g : Nat}

/-- **The machine at the end of the counted frame `j`**: frame `a + ix j` of the run, a definition for every `j`. When `j` frames end not paused by the end of frame
`top`, it is the end of the `j`-th of them (`Keep.up_at`, `Keep.ends_at`); `seq 0` is frame `a`. -/
abbrev Keep.seq (K : Keep sy m0 S a g) (j : Nat) : Machine := S.seq (a + ixOf sy m0 S a K.top j)

/-- **The same frames as `Frames`**: the field `seqAt` holds by the definition of `Keep.seq` -/
def Keep.toFrames (K : Keep sy m0 S a g) : Frames sy m0 S a g K.seq := ⟨K.top, K.many, fun _ _ => rfl, K.noStore, K.cleanE⟩

/-- where the counted frame `j` begins: as `Frames.fm` -/
abbrev Keep.fm (K : Keep sy m0 S a g) (j : Nat) : Machine := K.toFrames.fm j

/-- the input of the counted frame `j`: as `Frames.pad` -/
abbrev Keep.pad (K : Keep sy m0 S a g) (j : Nat) : UInt8 := K.toFrames.pad j

/-- the machine at control is the run's frame `a` -/
theorem Keep.seq0 (K : Keep sy m0 S a g) : K.seq 0 = S.seq a := K.toFrames.seq0

/-- **A counted frame ends with the game not paused**, before the touch and after it: for every `j` with `j` frames ending not paused by the end of frame `top` -/
theorem Keep.up_at (K : Keep sy m0 S a g) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ upTo (upAt sy m0 S a) K.top) : Unpaused sy m0 (K.seq j) := by
  have h := (nthUp_at (f := upAt sy m0 S a) h1 h2).2.1
  simpa [upAt] using h

/-- **A counted frame is a real frame of the run**, before the touch and after it: it ends at `seq j`, from the machine and the input of frame `a + ix j − 1` -/
theorem Keep.ends_at (K : Keep sy m0 S a g) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ upTo (upAt sy m0 S a) K.top) :
    K.seq j = frame (S.seq (a + (ixOf sy m0 S a K.top j - 1))) (S.inp (a + (ixOf sy m0 S a K.top j - 1))) := by
  have h : 1 ≤ ixOf sy m0 S a K.top j := (nthUp_at (f := upAt sy m0 S a) h1 h2).1
  rw [Keep.seq, ← S.next]
  congr 1
  omega

end

end Smbrta.FrameKeep
