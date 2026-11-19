import Theorems.PoleFrame
import Theorems.RoomBlocks

/-! A frame-start tile classification carried through value-aware RAM writes.
This is conditional infrastructure; it does not replace PoleJoin.Run.tiles. -/
namespace Smbrta.PoleTiles
open PoleEntryRule (Spots onCol WriteStep)
open PipeEntryRule (trace)
open PipeTransitionAll (go)

def Tile (Q : Spots) (v : UInt8) : Prop := v = Q.ball ∨ v = Q.shaft
def tileB (Q : Spots) (v : UInt8) : Bool := v == Q.ball || v == Q.shaft

theorem tileB_spec {Q : Spots} {v : UInt8} : tileB Q v = true ↔ Tile Q v := by
  simp only [tileB,Tile,Bool.or_eq_true,beq_iff_eq]

/-- A condition on one machine. Only pole bytes, not all bytes, are classified. -/
def ColumnMap (Q : Spots) (lo hi : Nat) (m : Machine) : Prop :=
  ∀ j, lo ≤ j → j < hi → Tile Q (m.ram.get! j) →
    onCol Q j = true ∧ Q.pg ≤ (m.ram.get! Q.pI).toNat+1

def columnB (Q : Spots) (lo hi : Nat) (m : Machine) : Bool :=
  (List.range (hi-lo)).all fun k =>
    !tileB Q (m.ram.get! (lo+k)) ||
      (onCol Q (lo+k) && decide (Q.pg ≤ (m.ram.get! Q.pI).toNat+1))

theorem columnB_spec {Q : Spots} {lo hi : Nat} {m : Machine}
    (h : columnB Q lo hi m = true) : ColumnMap Q lo hi m := by
  intro j hl hr ht
  have k : j-lo < hi-lo := by omega
  have hh := List.all_eq_true.1 h (j-lo) (List.mem_range.2 k)
  have e : lo+(j-lo) = j := by omega
  rw [e] at hh
  have tt := tileB_spec.2 ht
  simpa only [tt,Bool.not_true,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] using hh

/-- At a write, any resulting pole byte in the interval has the right column
and page. A page-byte write must also preserve the page condition for old
pole bytes. Other RAM bytes may change freely. -/
def WriteOK (Q : Spots) (lo hi : Nat) (m : Machine) : Prop :=
  (∀ j ∈ StepWrites.stepLocs m, lo ≤ j → j < hi →
    Tile Q ((go step m).2.ram.get! j) →
      onCol Q j = true ∧ Q.pg ≤ ((go step m).2.ram.get! Q.pI).toNat+1) ∧
  (Q.pI ∈ StepWrites.stepLocs m → ∀ j, lo ≤ j → j < hi →
    Tile Q ((go step m).2.ram.get! j) →
      Q.pg ≤ ((go step m).2.ram.get! Q.pI).toNat+1)

/-- An executable test of a single instruction's actual write locations and
values, including read-modify-write and stack instructions. -/
def writesB (Q : Spots) (lo hi : Nat) (m : Machine) : Bool :=
  let n := (go step m).2
  let ws := StepWrites.stepLocs m
  ws.all (fun j => !decide (lo ≤ j ∧ j < hi) || !tileB Q (n.ram.get! j) ||
    (onCol Q j && decide (Q.pg ≤ (n.ram.get! Q.pI).toNat+1))) &&
  (!ws.contains Q.pI ||
    !((List.range (hi-lo)).any fun k => tileB Q (n.ram.get! (lo+k))) ||
    decide (Q.pg ≤ (n.ram.get! Q.pI).toNat+1))

theorem writesB_spec {Q : Spots} {lo hi : Nat} {m : Machine}
    (h : writesB Q lo hi m = true) : WriteOK Q lo hi m := by
  simp only [writesB,Bool.and_eq_true] at h
  constructor
  · intro j hj hl hr ht
    have hh := List.all_eq_true.1 h.1 j hj
    have inn : decide (lo ≤ j ∧ j < hi) = true := decide_eq_true ⟨hl,hr⟩
    have tt := tileB_spec.2 ht
    simpa only [inn,tt,Bool.not_true,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] using hh
  · intro hp j hl hr ht
    have k : j-lo < hi-lo := by omega
    have e : lo+(j-lo) = j := by omega
    have any : ((List.range (hi-lo)).any fun k => tileB Q ((go step m).2.ram.get! (lo+k))) = true :=
      List.any_eq_true.2 ⟨j-lo,List.mem_range.2 k,by rw [e]; exact tileB_spec.2 ht⟩
    have mem : (StepWrites.stepLocs m).contains Q.pI = true := List.contains_iff_mem.2 hp
    simpa only [mem,any,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h.2

theorem step_column {Q : Spots} {lo hi : Nat} {m : Machine}
    (h : ColumnMap Q lo hi m) (hw : WriteOK Q lo hi m) :
    ColumnMap Q lo hi (go step m).2 := by
  intro j hl hr ht
  by_cases hj : j ∈ StepWrites.stepLocs m
  · exact hw.1 j hj hl hr ht
  · have eq := StepWrites.step_ram m j hj
    have old : Tile Q (m.ram.get! j) := by rw [eq] at ht; exact ht
    have col := h j hl hr old
    refine ⟨col.1,?_⟩
    by_cases hp : Q.pI ∈ StepWrites.stepLocs m
    · exact hw.2 hp j hl hr ht
    · rw [StepWrites.step_ram m Q.pI hp]
      exact col.2

/-- Non-pole writes are allowed, so coin erasure and a blank block write need
not keep the original buffer byte. -/
theorem writeOK_of_non_tile {Q : Spots} {lo hi : Nat} {m : Machine}
    (hp : Q.pI ∉ StepWrites.stepLocs m)
    (hv : ∀ j ∈ StepWrites.stepLocs m, lo ≤ j → j < hi →
      ¬ Tile Q ((go step m).2.ram.get! j)) : WriteOK Q lo hi m := by
  exact ⟨fun j hj hl hr ht => False.elim (hv j hj hl hr ht),
    fun h => False.elim (hp h)⟩

/-- Carry the frame-start condition to every instruction before the touch's
write, without assuming TileRead on the way. -/
theorem prefix_column {Q : Spots} {lo hi : Nat} {sy : Syms}
    {m : Machine} {i : UInt8} {n : Nat} (touch : WriteStep sy m i n)
    (start : ColumnMap Q lo hi m)
    (writes : ∀ k, k < n → WriteOK Q lo hi (trace m i k)) :
    ∀ j, j ≤ n → ColumnMap Q lo hi (trace m i j) := by
  intro j
  induction j with
  | zero => intro _; exact start
  | succ j ih =>
    intro hj
    rw [PoleEntryRule.step_before touch j (by omega)]
    exact step_column (ih (by omega)) (writes j (by omega))

/-- At a real post-read state, classification of its actual byte implies
TileRead. The caller must still provide the byte/read identity and interval. -/
theorem tile_read_of_column {Q : Spots} {lo hi : Nat} {m : Machine}
    (h : ColumnMap Q lo hi m)
    (hl : lo ≤ PoleFrame.readAt Q m) (hr : PoleFrame.readAt Q m < hi)
    (read : m.a = m.ram.get! (PoleFrame.readAt Q m)) : PoleFrame.TileRead Q m := by
  intro _ _ ht
  apply h _ hl hr
  rw [← read]
  exact ht


/-- Instruction and pointer metadata for the post-read byte identity. -/
def readCheck (E : FrameModel.Rom) (Q : Spots) : Bool :=
  let z := E.b (Q.read+1)
  decide (0x8000 ≤ Q.read) && decide (0x8000 ≤ Q.read+1) &&
    decide (0x8000 ≤ Q.read+1+1) && E.b Q.read == 0xB1 &&
    decide ((z.toUInt16 &&& 0x7FF).toNat = Q.ptrI) &&
    decide (((z+1).toUInt16 &&& 0x7FF).toNat = Q.ptrI+1)

/-- The actual LDA leaves RAM and Y unchanged and reads its post-step address.
The RAM-address premise is explicit; masking a ROM address is not a RAM read. -/
theorem load_result {E : FrameModel.Rom} {Q : Spots} {R : Machine}
    (hc : readCheck E Q = true) (g : FrameModel.Good E R) (pc : R.pc = Q.read)
    (ram : FrameModel.Md.ea E .izy {R with pc := R.pc+1} < 0x2000) :
    let T := (go step R).2
    T.ram = R.ram ∧ T.y = R.y ∧ T.a = T.ram.get! (PoleFrame.readAt Q T) := by
  simp only [readCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hp,hp1⟩,hp2⟩,op⟩,lo⟩,hi⟩ := hc
  let ad := FrameModel.Md.ea E .izy {R with pc := R.pc+1}
  let v := FrameModel.memv E R ad
  have code : E.b R.pc = 0xB1 := by rw [pc]; exact op
  have hd : FrameModel.lookupOp (E.b R.pc) FrameModel.insList = some (.rd .lda .izy) := by
    rw [code]; rfl
  have idle : FrameModel.idleAt E R.pc = false := by simp [FrameModel.idleAt,code]
  have sem := FrameModel.sem_rd (f := .lda) (md := .izy) g
    (by rw [pc]; exact hp1) (by rw [pc]; exact hp2) (Or.inl ram)
  have eq := FrameModel.step_nt g (by rw [pc]; exact hp) hd idle sem
    (FrameModel.rfE_good .lda v (g.pc (FrameModel.Md.adv .izy (R.pc+1))))
  have rr : (go step R).2.ram = R.ram := by
    simpa only [FrameModel.nt,FrameModel.rfE] using congrArg Machine.ram eq
  have yr : (go step R).2.y = R.y := by
    simpa only [FrameModel.nt,FrameModel.rfE] using congrArg Machine.y eq
  have ar : (go step R).2.a = v := by
    simpa only [FrameModel.nt,FrameModel.rfE] using congrArg Machine.a eq
  have addr : FrameModel.I ad = PoleFrame.readAt Q (go step R).2 := by
    simp only [ad,FrameModel.Md.ea,FrameModel.ptrAt,pc,lo,hi,PoleFrame.readAt,rr,yr,FrameModel.I]
  refine ⟨rr,yr,?_⟩
  rw [ar,rr,← addr]
  exact if_pos ram

/-- TileRead for a real load in the classified interval, from the pre-load
classification and checked CPU semantics, rather than a byte-identity field. -/
theorem tile_after_load {E : FrameModel.Rom} {Q : Spots} {R : Machine} {lo hi : Nat}
    (hc : readCheck E Q = true) (g : FrameModel.Good E R) (pc : R.pc = Q.read)
    (ram : FrameModel.Md.ea E .izy {R with pc := R.pc+1} < 0x2000)
    (h : ColumnMap Q lo hi R)
    (hl : lo ≤ PoleFrame.readAt Q (go step R).2)
    (hr : PoleFrame.readAt Q (go step R).2 < hi) :
    PoleFrame.TileRead Q (go step R).2 := by
  obtain ⟨rr,_,a⟩ := load_result hc g pc ram
  apply tile_read_of_column (lo := lo) (hi := hi) _ hl hr a
  intro j hj hk ht
  rw [rr] at ht ⊢
  exact h j hj hk ht


/-- Conditional TileRead along the actual touch frame: the invariant is
transported from frame start, and the actual load supplies its byte identity. -/
theorem prefix_tile_after_load {E : FrameModel.Rom} {Q : Spots} {lo hi : Nat}
    {sy : Syms} {m : Machine} {i : UInt8} {n k : Nat}
    (touch : WriteStep sy m i n) (start : ColumnMap Q lo hi m)
    (writes : ∀ j, j < n → WriteOK Q lo hi (trace m i j)) (hk : k < n)
    (hc : readCheck E Q = true) (g : FrameModel.Good E (trace m i k))
    (pc : (trace m i k).pc = Q.read)
    (ram : FrameModel.Md.ea E .izy {(trace m i k) with pc := (trace m i k).pc+1} < 0x2000)
    (hl : lo ≤ PoleFrame.readAt Q (trace m i (k+1)))
    (hr : PoleFrame.readAt Q (trace m i (k+1)) < hi) :
    PoleFrame.TileRead Q (trace m i (k+1)) := by
  have eq := PoleEntryRule.step_before touch k (by omega)
  have cols := prefix_column touch start writes k (by omega)
  rw [eq] at hl hr ⊢
  exact tile_after_load hc g pc ram cols hl hr

end Smbrta.PoleTiles
