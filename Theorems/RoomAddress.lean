import Theorems.EntryHeight
import Theorems.RoomBlocks
import Std.Tactic.BVDecide

/-!
# The room's block-buffer column routine

A small check of `GetBlockBufferAddr`, for all 32 column/buffer selectors and all
stack bytes. This is a routine lemma, not a proof of the whole landing frame.
Page: `1-1/c-7-5-7-RoomAddress.md`.
-/
namespace Smbrta.RoomAddress
open FrameModel

/-- The buffer and column encoded by the low five selector bits. -/
def target (P : ScreenPage.Places) (a : UInt8) : UInt16 :=
  (P.bufLo + a.toNat / 16 * (P.bufN / 2) + a.toNat % 16).toUInt16

def bytes16 (v : UInt16) : UInt16 := v.toUInt8.toUInt16 ||| ((v >>> 8).toUInt8.toUInt16 <<< 8)

theorem bytes16_eq (v : UInt16) : bytes16 v = v := by
  unfold bytes16
  bv_decide

/-- The byte arithmetic used to combine page parity and the pixel's column. -/
def encoded (page x adder : UInt8) : UInt8 :=
  let sum := x + adder
  let carry := ((x.toUInt16 + adder.toUInt16) >>> 8).toUInt8
  (sum >>> 4) ||| (((page + carry) &&& 1) <<< 4)

/-- The same selector read from the full coordinate, modulo the two-buffer cycle. -/
def selector (page x adder : UInt8) : UInt8 :=
  ((((page.toUInt16 <<< 8) + x.toUInt16 + adder.toUInt16) >>> 4).toUInt8 &&& 31)

theorem encoded_eq_selector (page x adder : UInt8) : encoded page x adder = selector page x adder := by
  unfold encoded selector
  bv_decide

theorem selector_lt (page x adder : UInt8) : (selector page x adder).toNat < 32 := by
  have h : selector page x adder < 32 := by
    unfold selector
    bv_decide
  exact UInt8.lt_iff_toNat_lt.1 h

def start (H : EntryHeight.HP) (S a : UInt8) : Cut :=
  { pc := H.colAt, s := S, K := [], ra := some a }

/-- The cut before RTS, after the routine has restored its stack pointer. -/
def finish (E : Rom) (H : EntryHeight.HP) (z S a : UInt8) : Cut :=
  let v := target H.P a
  { pc := firstRts E 40 (startQ (start H S a)), s := S,
    K := [(I z.toUInt16, v.toUInt8), (I (z + 1).toUInt16, (v >>> 8).toUInt8)] }

def coreCheck (E : Rom) (H : EntryHeight.HP) (z S a : UInt8) : Bool :=
  pieceOK E (start H S a) (finish E H z S a) [] 40

def caseCheck (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) (S a : UInt8) : Bool :=
  let H := EntryHeight.hpOf sy nm m0
  coreCheck (Rom.of m0) H (romByte m0 (H.P.read + 1)) S a

/-- No assumption about the stack byte is required by this check. -/
def check (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) : Bool :=
  let H := EntryHeight.hpOf sy nm m0
  let E := Rom.of m0
  let z := romByte m0 (H.P.read + 1)
  (List.range 256).all fun s => (List.range 32).all fun a => coreCheck E H z s.toUInt8 a.toUInt8

theorem case_of_check {sy : Syms} {nm : PipeTransitionAll.Names} {m0 : Machine} {S a : UInt8}
    (h : check sy nm m0 = true) (ha : a.toNat < 32) : caseCheck sy nm m0 S a = true := by
  have hs := List.all_eq_true.1 h S.toNat (List.mem_range.2 S.toNat_lt)
  have hh := List.all_eq_true.1 hs a.toNat (List.mem_range.2 ha)
  simpa only [UInt8.ofNat_toNat] using hh

/-- A selector known at entry gives the actual pointer at the routine's return.
The input selector's relationship to player coordinates remains a separate obligation. -/
theorem pointer_of_check {sy : Syms} {nm : PipeTransitionAll.Names} {m0 R : Machine} {S a : UInt8}
    (h : check sy nm m0 = true) (ha : a.toNat < 32) (hr : At (Rom.of m0) (start (EntryHeight.hpOf sy nm m0) S a) R) :
    ∃ k, k ≤ 40 ∧ At (Rom.of m0) (finish (Rom.of m0) (EntryHeight.hpOf sy nm m0) (romByte m0 ((EntryHeight.hpOf sy nm m0).P.read + 1)) S a) (stepN k R) ∧
      RoomBlocks.ptrZ (stepN k R) (romByte m0 ((EntryHeight.hpOf sy nm m0).P.read + 1)) =
        target (EntryHeight.hpOf sy nm m0).P a := by
  obtain ⟨k, hk, atR, _, _⟩ := piece_specI (case_of_check h ha) hr
  refine ⟨k, hk, atR, ?_⟩
  have lo := atR.K _ (List.mem_cons_self ..)
  have hi := atR.K _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  change (stepN k R).ram.get! (I (romByte m0 ((EntryHeight.hpOf sy nm m0).P.read + 1)).toUInt16) = _ at lo
  change (stepN k R).ram.get! (I ((romByte m0 ((EntryHeight.hpOf sy nm m0).P.read + 1)) + 1).toUInt16) = _ at hi
  rw [← bytes16_eq (target (EntryHeight.hpOf sy nm m0).P a)]
  unfold RoomBlocks.ptrZ bytes16
  simp only [FrameModel.I] at lo hi
  rw [lo, hi]

end Smbrta.RoomAddress
