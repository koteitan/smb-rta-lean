import Theorems.PushTimer

/-!
# Above ground: the stores that may reach the side collision's timer, outside the area parser

Round 33 asked the field `OnFrames.sideW` (a store through an index or a pointer does not write the side collision's timer) only at the stores that may
reach the timer (`PushTimer.NearW`): a store to an absolute address plus an index from whose base some index reaches the timer, or a store through a pointer.
Here a walk proves it at each such store outside the area parser's code (from `AreaParserCore` to `GetBlockBufferAddr`) and the code of the head's collision
with a block (from `PlayerHeadCollision` to `BlockObjectsCore`) (`near_side`). So the field is asked only at the stores of `Resid`.

The walk (`walkR`) starts at the scroll handler's call (`PlayerSubs`), in the states of the first walk of `AfterKeep` there, and follows the frame to its end. Its
guard is `FrameKeep.guardE`, whose `CleanK` is the field `cleanE` of `FrameKeep.Frames`; it follows no byte. At a store that may reach the timer and is not in
`Resid` it asks that every target that the walk's state allows misses the timer (`missK`; through a pointer `missP`). To know the index there it has three things that the
walks of `PushTimer` do not have:
* bounds on `X` and `Y` at the states of its table (`bnd`, kept in the state's `log`, which `Sim` does not read): a walk from a table state first splits it into
  its values of `X` and `Y` inside the bounds (`pieces`), and a state is covered by a table state only when its values are inside the bounds (`leB`);
* before some instructions (`TXA`, `INX`, `DEX`, the stores through `X`, `TYA`, `INY`, `DEY`, `STA abs,Y`) a split of `X` or `Y` into its values when at
  most 4 of its bits are not known (`splitR`);
* after a store through an index or a pointer: when the index is not known the abstract step forgets every byte outside the guard, and the walk takes back
  each byte of the zero page that the state before knows and that the store cannot reach (`fixR`, by `StepWrites.keep_step`).

The search that makes the table is no part of the proof (`searchR`); the check is `rCheck`. There is no game data in this file.
Page: `1-1/e-2-10-3-24-SideRange.md`.
-/

namespace Smbrta.SideRange

open TaintRun
open PipeTransitionAll (go ba_get_set_self ba_get_set_ne ba_size_set)
open AfterKeep (walkQ1)

variable {sy : Syms}

/-! ## The values of a byte -/

/-- `x` is a value that the known bits of `b` allow -/
def memB (b : AB) (x : UInt8) : Bool := x &&& b.k == b.v &&& b.k

theorem memB_of {b : AB} {x : UInt8} (h : b.mem x) : memB b x = true := by
  unfold memB
  unfold AB.mem at h
  rw [h]
  exact beq_self_eq_true _

/-- the values from `lo` to `hi` that the known bits of `b` allow -/
def valsIn (b : AB) (lo hi : Nat) : List UInt8 :=
  ((List.range 256).filter fun v => decide (lo ≤ v) && decide (v ≤ hi) && memB b v.toUInt8).map (·.toUInt8)

theorem mem_valsIn {b : AB} {x : UInt8} {lo hi : Nat} (h : b.mem x) (h1 : lo ≤ x.toNat) (h2 : x.toNat ≤ hi) : x ∈ valsIn b lo hi := by
  unfold valsIn
  refine List.mem_map.2 ⟨x.toNat, List.mem_filter.2 ⟨List.mem_range.2 (UInt8.toNat_lt _), ?_⟩, UInt8.ofNat_toNat⟩
  have e : x.toNat.toUInt8 = x := UInt8.ofNat_toNat
  simp only [e, memB_of h, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1, h2⟩

theorem mem_valsAll {b : AB} {x : UInt8} (h : b.mem x) : x ∈ valsIn b 0 255 := mem_valsIn h (Nat.zero_le _) (by have := UInt8.toNat_lt x; omega)

/-- the number of bits of `b` that are not known -/
def nUnk (b : AB) : Nat := (List.range 8).countP fun i => (b.k >>> i.toUInt8) &&& 1 == 0

/-! ## Bounds on `X` and `Y` at the table's states -/

/-- the bounds of a table state on `X` (`j = 0`) and on `Y` (`j = 1`), kept in its `log` as `[xlo, xhi, ylo, yhi]`; with no bounds `0` and `255` -/
def bnd (A : AS) (j : Nat) : Nat × Nat :=
  match A.log with
  | [a, b, c, d] => if j = 0 then (a, b) else (c, d)
  | _ => (0, 255)

/-- what the state knows of `X` (`j = 0`) or `Y` -/
def regB (A : AS) (j : Nat) : AB := if j = 0 then A.x else A.y

/-- `X` (`j = 0`) or `Y` of the machine -/
def regM (m : Machine) (j : Nat) : UInt8 := if j = 0 then m.x else m.y

/-- **The bounds hold** on the machine -/
def BOK (A : AS) (m : Machine) : Prop := ∀ j, j < 2 → (bnd A j).1 ≤ (regM m j).toNat ∧ (regM m j).toNat ≤ (bnd A j).2

/-- the state with `X` (`j = 0`) or `Y` replaced -/
def setR (A : AS) (j : Nat) (b : AB) : AS := if j = 0 then { A with x := b } else { A with y := b }

theorem regB_mem {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (j : Nat) : (regB A j).mem (regM m j) := by
  unfold regB regM
  by_cases e : j = 0
  · rw [if_pos e, if_pos e]; exact hs.x
  · rw [if_neg e, if_neg e]; exact hs.y

theorem sim_setR {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (j : Nat) : Sim E F (setR A j (AB.known (regM m j))) m := by
  unfold setR regM
  by_cases e : j = 0
  · rw [if_pos e, if_pos e]; exact { hs with x := mem_known_self _ }
  · rw [if_neg e, if_neg e]; exact { hs with y := mem_known_self _ }

theorem setR_k (A : AS) (j : Nat) (b : AB) : (setR A j b).k = A.k := by
  unfold setR; split <;> rfl

/-- one split of a table state: `X` (`j = 0`) or `Y` into its values inside the bounds, when there are fewer than `W` of them and the bounds exclude a value
that the known bits allow -/
def cut1 (W : Nat) (A0 : AS) (j : Nat) (ps : List AS) : List AS :=
  let b := regB A0 j
  let vs := valsIn b (bnd A0 j).1 (bnd A0 j).2
  if decide (vs.length < W) && !b.isK && decide (vs.length < (valsIn b 0 255).length) then ps.flatMap fun B => vs.map fun v => setR B j (AB.known v) else ps

/-- **The pieces of a table state**, from which its walks start: its `X`, then its `Y`, split by the bounds; the pieces have no bounds -/
def pieces (W : Nat) (A : AS) : List AS := cut1 W A 1 (cut1 W A 0 [{ A with log := [] }])

theorem cut1_cov {E : Env} {F : Nat × UInt8} {W : Nat} {A0 : AS} {m : Machine} (hs0 : Sim E F A0 m) (hb : BOK A0 m) {j : Nat} (hj : j < 2) {ps : List AS}
    (hps : ∃ B ∈ ps, Sim E F B m ∧ B.k = A0.k) : ∃ B ∈ cut1 W A0 j ps, Sim E F B m ∧ B.k = A0.k := by
  obtain ⟨B, hB, hsB, hkB⟩ := hps
  unfold cut1
  dsimp only
  split
  · refine ⟨setR B j (AB.known (regM m j)), List.mem_flatMap.2 ⟨B, hB, List.mem_map.2 ⟨regM m j, ?_, rfl⟩⟩, sim_setR hsB j, by rw [setR_k]; exact hkB⟩
    exact mem_valsIn (regB_mem hs0 j) (hb j hj).1 (hb j hj).2
  · exact ⟨B, hB, hsB, hkB⟩

theorem pieces_cov {E : Env} {F : Nat × UInt8} (W : Nat) {A : AS} {m : Machine} (hs : Sim E F A m) (hb : BOK A m) :
    ∃ P ∈ pieces W A, Sim E F P m ∧ P.k = A.k :=
  cut1_cov hs hb (by decide) (cut1_cov hs hb (by decide) ⟨{ A with log := [] }, List.mem_singleton_self _, { hs with }, rfl⟩)

/-- the values that the known bits of `b` allow are inside `r` -/
def inB (b : AB) (r : Nat × Nat) : Bool := decide (r.1 ≤ b.minv.toNat) && decide (b.maxv.toNat ≤ r.2)

/-- the values of `X` and `Y` that `B` allows are inside the bounds of `D` -/
def leB (B D : AS) : Bool := inB B.x (bnd D 0) && inB B.y (bnd D 1)

theorem bok_of_leB {E : Env} {F : Nat × UInt8} {B D : AS} {m : Machine} (hs : Sim E F B m) (h : leB B D = true) : BOK D m := by
  unfold leB inB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  intro j hj
  have hx1 := minv_le hs.x
  have hx2 := le_maxv hs.x
  have hy1 := minv_le hs.y
  have hy2 := le_maxv hs.y
  rcases (show j = 0 ∨ j = 1 by omega) with e | e
  · subst e
    show (bnd D 0).1 ≤ m.x.toNat ∧ m.x.toNat ≤ (bnd D 0).2
    exact ⟨by omega, by omega⟩
  · subst e
    show (bnd D 1).1 ≤ m.y.toNat ∧ m.y.toNat ≤ (bnd D 1).2
    exact ⟨by omega, by omega⟩

/-! ## The zero page after a store through an index that the state does not know -/

/-- `A` with byte `d` known to be `v` covers each machine of `A` with that value (a copy of `EraseRange.sim_setK_same`) -/
theorem sim_setK_same {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) {d : Nat} {v : AB} (hv : v.mem (m.ram.get! d)) :
    Sim E F (A.setK d v) m := by
  refine { hs with
    ram := ?_
    szR := ?_
    szK := ?_ }
  · intro i hi
    show AB.mem ⟨(A.ram.set! d v.v).get! i, (A.kn.set! d v.k).get! i⟩ (m.ram.get! i)
    by_cases hdi : d = i
    · subst hdi
      rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hi), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hi)]
      exact hv
    · rw [ba_get_set_ne _ _ _ _ hdi, ba_get_set_ne _ _ _ _ hdi]
      exact hs.ram i hi
  · show (A.ram.set! d _).size = 2048
    rw [ba_size_set]
    exact hs.szR
  · show (A.kn.set! d _).size = 2048
    rw [ba_size_set]
    exact hs.szK

/-- the opcode at the state's `pc` -/
def opA (E : Env) (A : AS) : UInt8 := E.prg.get! (A.pc &&& E.mask).toNat

/-- one byte of the zero page: that of `A₁`, when the step of `A₁` does not write it (`StepWrites.keepOK`) and `A₁` knows a bit of it -/
def takeI (E : Env) (A₁ B : AS) (i : Nat) : AS :=
  if (A₁.getK i).k != 0 && StepWrites.keepOK E (· == i) A₁ then B.setK i (A₁.getK i) else B

/-- **After the step of `A₁`**: when it is a store through an index or a pointer, each byte of the zero page that the store does not write is that of `A₁` -/
def fixR (E : Env) (A₁ B : AS) : AS :=
  if PushTimer.wOps.contains (opA E A₁) then (List.range 256).foldl (takeI E A₁) B else B

theorem takeZ_go {E : Env} {F : Nat × UInt8} {A₁ : AS} {m : Machine} (hs1 : Sim E F A₁ m) :
    ∀ (l : List Nat) (B : AS), (∀ i ∈ l, i < 256) → Sim E F B (go step m).2 → Sim E F (l.foldl (takeI E A₁) B) (go step m).2
  | [], _, _, h => h
  | i :: t, B, hl, h => by
    show Sim E F (t.foldl (takeI E A₁) (takeI E A₁ B i)) (go step m).2
    have hi : i < 256 := hl i List.mem_cons_self
    refine takeZ_go hs1 t _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ?_
    unfold takeI
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      refine sim_setK_same h ?_
      rw [StepWrites.keep_step hs1 hc.2 i (beq_self_eq_true i)]
      exact hs1.ram i (by omega)
    · exact h

theorem fixR_sim {E : Env} {F : Nat × UInt8} {A₁ B : AS} {m : Machine} (hs1 : Sim E F A₁ m) (hB : Sim E F B (go step m).2) :
    Sim E F (fixR E A₁ B) (go step m).2 := by
  unfold fixR
  split
  · exact takeZ_go hs1 _ B (fun i hi => List.mem_range.1 hi) hB
  · exact hB

theorem takeI_k (E : Env) (A₁ B : AS) (i : Nat) : (takeI E A₁ B i).k = B.k := by
  unfold takeI; split <;> rfl

theorem takeZ_k (E : Env) (A₁ : AS) : ∀ (l : List Nat) (B : AS), (l.foldl (takeI E A₁) B).k = B.k
  | [], _ => rfl
  | i :: t, B => (takeZ_k E A₁ t _).trans (takeI_k E A₁ B i)

theorem fixR_k (E : Env) (A₁ B : AS) : (fixR E A₁ B).k = B.k := by
  unfold fixR; split
  · exact takeZ_k _ _ _ _
  · rfl

/-! ## Splits of `X` and `Y` before some instructions -/

/-- **The split**: before an instruction whose opcode is in `xo` (`yo`), `X` (`Y`) is split into its values when at most `u` of its bits are not known -/
def splitR (E : Env) (u : Nat) (xo yo : List UInt8) (A : AS) : List AS :=
  let op := opA E A
  if xo.contains op && !A.x.isK && decide (nUnk A.x ≤ u) then (valsIn A.x 0 255).map fun v => { A with x := AB.known v }
  else if yo.contains op && !A.y.isK && decide (nUnk A.y ≤ u) then (valsIn A.y 0 255).map fun v => { A with y := AB.known v }
  else [A]

theorem cov_splitR {E : Env} {F : Nat × UInt8} (u : Nat) (xo yo : List UInt8) : Cov E F (splitR E u xo yo) := by
  intro A m hs
  unfold splitR
  dsimp only
  split
  · exact ⟨{ A with x := AB.known m.x }, List.mem_map.2 ⟨m.x, mem_valsAll hs.x, rfl⟩, { hs with x := mem_known_self _ }, rfl⟩
  · split
    · exact ⟨{ A with y := AB.known m.y }, List.mem_map.2 ⟨m.y, mem_valsAll hs.y, rfl⟩, { hs with y := mem_known_self _ }, rfl⟩
    · exact ⟨A, List.mem_singleton_self _, hs, rfl⟩

/-- the opcodes before which `X` is split: `TXA`, `INX`, `DEX` and the stores through `X` -/
def xOps : List UInt8 := [0x8A, 0xE8, 0xCA, 0x95, 0x94, 0xD6, 0xF6, 0x9D, 0xDE, 0xFE, 0x7E]

/-- the opcodes before which `Y` is split: `TYA`, `INY`, `DEY`, `STA abs,Y` -/
def yOps : List UInt8 := [0x98, 0xC8, 0x88, 0x99]

/-! ## The condition at a store -/

/-- the operand of the instruction at the state's `pc` -/
def opnd (E : Env) (A : AS) : UInt16 :=
  (E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 ||| ((E.prg.get! ((A.pc + 2) &&& E.mask).toNat).toUInt16 <<< 8)

/-- the store at the state's `pc` may reach the byte `s` (`PushTimer.nearWB` on the state) -/
def nearA (s : Nat) (E : Env) (A : AS) : Bool := (PushTimer.absWOps.contains (opA E A) && !PositionKeep.farB [s] (opnd E A)) || opA E A == 0x91

/-- the zero page operand of the instruction at the state's `pc` -/
def zop (E : Env) (A : AS) : UInt8 := E.prg.get! ((A.pc + 1) &&& E.mask).toNat

/-- **Through a pointer** (`STA (zp),Y`): for each value of the pointer's high byte that the state allows, every address from the high byte's page plus the
smallest of the low byte plus `Y` to the largest misses the byte `s` -/
def missP (s : Nat) (E : Env) (A : AS) : Bool :=
  let lo := A.getK (zop E A).toNat
  let hi := A.getK (zop E A + 1).toNat
  let dmin := lo.minv.toNat + A.y.minv.toNat
  let dmax := lo.maxv.toNat + A.y.maxv.toNat
  (valsIn hi 0 255).all fun h => (List.range (dmax + 1 - dmin)).all fun d => !(StepWrites.ramIdx (h.toNat * 256 + (dmin + d)).toUInt16).contains s

/-- **What the walk asks at a store**: through `X` (`STA`, `DEC`, `INC`, `ROR` absolute with `X`) or through `Y` (`STA` absolute with `Y`), every value of the
index that the state allows misses the byte `s`; through a pointer, `missP` -/
def missK (s : Nat) (E : Env) (A : AS) : Bool :=
  let op := opA E A
  if op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E then (valsIn A.x 0 255).all fun v => !(StepWrites.ramIdx (opnd E A + v.toUInt16)).contains s
  else if op == 0x99 then (valsIn A.y 0 255).all fun v => !(StepWrites.ramIdx (opnd E A + v.toUInt16)).contains s
  else if op == 0x91 then missP s E A
  else false

/-- **The places where the field `OnFrames.sideW` stays asked**, for a program: the area parser's code, from `AreaParserCore` to `GetBlockBufferAddr`,
and the code of the head's collision with a block and of the bumped block's routines that it calls, from `PlayerHeadCollision` to `BlockObjectsCore` -/
def residB (sy : Syms) (pc : UInt16) : Bool :=
  (decide (sy.AreaParserCore ≤ pc) && decide (pc < sy.GetBlockBufferAddr)) || (decide (sy.PlayerHeadCollision ≤ pc) && decide (pc < sy.BlockObjectsCore))

/-- **The places where the field `OnFrames.sideW` stays asked** (round 34): the area parser's code and the code of the head's collision with a block -/
def Resid (sy : Syms) (m : Machine) : Prop := residB sy m.pc = true

/-- **What the walk asks at a state**: at a store through an index or a pointer, no interrupt pending, the instruction and its two next bytes in the program's half of
the address space, and if the store may reach the timer and is not one of `Resid`, `missK` -/
def okR (sy : Syms) (m0 : Machine) (E : Env) (A : AS) : Bool :=
  !PushTimer.wOps.contains (opA E A) ||
    (!A.nmi && decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) &&
      (!nearA (ScrollRule.places sy m0).sideB E A || residB sy A.pc || missK (ScrollRule.places sy m0).sideB E A))

theorem miss_of {s : Nat} {t : UInt16} (h : (StepWrites.ramIdx t).contains s = false) (hlt : t < 0x2000) : (t &&& 0x7FF).toNat ≠ s := by
  intro e
  have : (StepWrites.ramIdx t).contains s = true := by simp [StepWrites.ramIdx, hlt, e]
  rw [h] at this
  cases this

theorem zp_lt (z : UInt8) : z.toUInt16 < 0x2000 := by
  apply UInt16.lt_iff_toNat_lt.2
  have h := z.toNat_lt
  simp
  omega

theorem zp_idx (z : UInt8) : (z.toUInt16 &&& 0x7FF).toNat = z.toNat := by
  have h := PositionWriters.zp_all ⟨z.toNat, z.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

theorem w16 (lo hi y : UInt8) : ((hi.toNat * 256 + (lo.toNat + y.toNat)).toUInt16) = (lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + y.toUInt16 := by
  apply UInt16.toNat_inj.1
  rw [UInt16.toNat_add, SideChangeEnd.ptr_toNat, UInt8.toNat_toUInt16,
    show (hi.toNat * 256 + (lo.toNat + y.toNat)).toUInt16.toNat = (hi.toNat * 256 + (lo.toNat + y.toNat)) % 65536 from UInt16.toNat_ofNat]
  have : (2 : Nat) ^ 16 = 65536 := rfl
  omega

/-- the target of `STA (zp),Y`: the pointer in the zero page plus `Y` -/
theorem izy_t {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) (ht : m.trk = false) :
    (go Smbrta.mIzy { m with pc := m.pc + 1 }).1 =
      ((m.ram.get! (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toNat).toUInt16 |||
        ((m.ram.get! (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat + 1).toNat).toUInt16 <<< 8)) + m.y.toUInt16 := by
  have e : go Smbrta.mIzy { m with pc := m.pc + 1 } = go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun s =>
      pure (b + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind]
  generalize m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = z
  have ht' : ({ { m with pc := m.pc + 1 } with pc := m.pc + 1 + 1 } : Machine).trk = false := ht
  have e2 : go (rd16zp z) { { m with pc := m.pc + 1 } with pc := m.pc + 1 + 1 } =
      ((m.ram.get! (z.toUInt16 &&& 0x7FF).toNat).toUInt16 ||| ((m.ram.get! ((z + 1).toUInt16 &&& 0x7FF).toNat).toUInt16 <<< 8),
        { { m with pc := m.pc + 1 } with pc := m.pc + 1 + 1 }) := by
    show go (rd z.toUInt16 >>= fun lo => rd (z + 1).toUInt16 >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) _ = _
    rw [PipeTransitionAll.go_bind, TaintRun.rd_ram (zp_lt _) ht']
    dsimp only
    rw [PipeTransitionAll.go_bind, TaintRun.rd_ram (zp_lt _) ht']
    rfl
  rw [e2, zp_idx, zp_idx]
  rfl

/-- **`okR` gives `SideW`** at a store that may reach the timer and is not one of `Resid` -/
theorem okR_spec {m0 : Machine} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : okR sy m0 E A = true)
    (hn : PushTimer.NearW sy m0 m) (hr : ¬ Resid sy m) : PushTimer.SideW sy m0 m := by
  intro t ht hlt heq
  have hop : PipeWrites.opAt m = opA E A := by unfold PipeWrites.opAt opA; rw [hs.prg, hs.mask, hs.pc]
  have hoa : PositionKeep.operandAt m.prg m.prgMask m.pc = opnd E A := by unfold PositionKeep.operandAt opnd; rw [hs.prg, hs.mask, hs.pc]
  have hw : PushTimer.wOps.contains (opA E A) = true := by rw [← hop]; exact List.contains_iff_mem.2 (PushTimer.wTarget_ops ht)
  unfold okR at h
  rw [hw] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨_, _⟩, hp1⟩, hp2⟩, hc⟩ := h
  have hp1' : 0x8000 ≤ m.pc + 1 := by rw [hs.pc]; exact hp1
  have hp2' : 0x8000 ≤ m.pc + 1 + 1 := by rw [hs.pc]; exact hp2
  have hnA : nearA (ScrollRule.places sy m0).sideB E A = true := by
    have e : PushTimer.nearWB sy m0 m = true := hn
    unfold PushTimer.nearWB at e
    unfold nearA
    rw [← hop, ← hoa]
    exact e
  have hrA : residB sy A.pc = false := by
    cases e : residB sy A.pc with
    | false => rfl
    | true => exact absurd (show residB sy m.pc = true by rw [hs.pc]; exact e) hr
  rw [hnA, hrA] at hc
  have hmk : missK (ScrollRule.places sy m0).sideB E A = true := by
    rcases hc with (h1 | h1) | h1
    · cases h1
    · cases h1
    · exact h1
  unfold missK at hmk
  unfold PipeWrites.wTarget at ht
  generalize hop2 : opA E A = op at hmk
  rw [hop, hop2] at ht
  dsimp only at hmk
  by_cases c1 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true
  · exfalso
    have hz : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = false ∧ (op == 0x99) = false ∧ (op == 0x91) = false := by
      simp only [Bool.or_eq_true, beq_iff_eq] at c1
      rcases c1 with ((e | e) | e) | e <;> subst e <;> exact ⟨rfl, rfl, rfl⟩
    rw [if_neg (by simp [hz.1]), if_neg (by simp [hz.2.1]), if_neg (by simp [hz.2.2])] at hmk
    cases hmk
  · rw [if_neg c1] at ht
    by_cases c2 : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = true
    · rw [if_pos c2, PushTimer.abx_t hp1' hp2', hoa] at ht
      rw [if_pos c2] at hmk
      have hm := List.all_eq_true.1 hmk m.x (mem_valsAll hs.x)
      have e := Option.some.inj ht
      rw [e] at hm
      exact miss_of (by simpa using hm) hlt heq
    · rw [if_neg c2] at ht
      rw [if_neg c2] at hmk
      by_cases c3 : (op == 0x99) = true
      · rw [if_pos c3, PushTimer.aby_t hp1' hp2', hoa] at ht
        rw [if_pos c3] at hmk
        have hm := List.all_eq_true.1 hmk m.y (mem_valsAll hs.y)
        have e := Option.some.inj ht
        rw [e] at hm
        exact miss_of (by simpa using hm) hlt heq
      · rw [if_neg c3] at hmk
        rw [if_neg c3] at ht
        by_cases c4 : (op == 0x91) = true
        · rw [if_pos c4, izy_t hp1' hs.trk] at ht
          rw [if_pos c4] at hmk
          have hz : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = zop E A := by unfold zop; rw [hs.prg, hs.mask, hs.pc]
          rw [hz] at ht
          have e := Option.some.inj ht
          unfold missP at hmk
          have hl0 : (zop E A).toNat < 2048 := by have := (zop E A).toNat_lt; omega
          have hh0 : (zop E A + 1).toNat < 2048 := by have := (zop E A + 1).toNat_lt; omega
          have hlo := hs.ram _ hl0
          have hhi := hs.ram _ hh0
          have hm1 := List.all_eq_true.1 hmk _ (mem_valsAll hhi)
          have a1 := minv_le hlo
          have a2 := le_maxv hlo
          have a3 := minv_le hs.y
          have a4 := le_maxv hs.y
          have hm2 := List.all_eq_true.1 hm1 ((m.ram.get! (zop E A).toNat).toNat + m.y.toNat - ((A.getK (zop E A).toNat).minv.toNat + A.y.minv.toNat))
            (List.mem_range.2 (by omega))
          rw [show (A.getK (zop E A).toNat).minv.toNat + A.y.minv.toNat + ((m.ram.get! (zop E A).toNat).toNat + m.y.toNat -
              ((A.getK (zop E A).toNat).minv.toNat + A.y.minv.toNat)) = (m.ram.get! (zop E A).toNat).toNat + m.y.toNat by omega, w16, e] at hm2
          exact miss_of (by simpa using hm2) hlt heq
        · rw [if_neg c4] at hmk
          cases hmk

/-! ## The walk -/

/-- the walk's table -/
structure CfgR where
  E : Env
  ops : Array (AM Unit)
  S : FrameKeep.Spot
  G : PipeWrites.Guard
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray
  /-- the table's key of a state: no part of the proof -/
  key : AS → Nat
  /-- the limit of the pieces of a table state -/
  W : Nat
  sp : AS → List AS
  ok : AS → Bool

/-- `B` is covered by a state of the table: its known bits, and its values of `X` and `Y` inside the bounds -/
def coverR (C : CfgR) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => PipeWrites.leK B D l && leB B D
    | _, _ => false

/-- **The walk**: from `A`, step by step, until each path stops at a store to a byte of `l` by its address, comes to a state of the table, or ends the frame; at each
state `ok`. The step is `FrameKeep.kstep` on the pieces of `FrameKeep.preK` and `sp`, followed by `fixR`. -/
def walkR (C : CfgR) (l : List Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || (C.ok A && ((FrameKeep.preK C.S C.G A).flatMap C.sp).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B0 =>
      if (fixR C.E A₁ B0).k == A.k then (C.cut.get! (fixR C.E A₁ B0).pc.toNat != 0 && coverR C (fixR C.E A₁ B0)) || walkR C l n (fixR C.E A₁ B0)
      else true)

/-- the table's check: from each piece of each state, the walk succeeds -/
def tableOK (C : CfgR) (l : List Nat) (Fu : Nat) : Bool := C.t.all fun D => (pieces C.W D).all (walkR C l Fu)

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {C : CfgR} {l : List Nat} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveR (C : CfgR) (l : List Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkR C l n A = true

theorem cover_liveR (ht : tableOK C l Fu = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : coverR C B = true) : ∃ D, LiveR C l F D m ∧ D.k = B.k := by
  unfold coverR at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = PipeWrites.knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    simp only [Bool.and_eq_true] at h2
    have hle := PipeWrites.leK_le h2.1
    have hsD := sim_le hle hs
    have hb := bok_of_leB hs h2.2
    obtain ⟨P, hP, hsP, hkP⟩ := pieces_cov C.W hsD hb
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨P, ⟨hsP, Fu, List.all_eq_true.1 hall P hP⟩, by rw [hkP]; exact (PipeWrites.le_k hle).symm⟩
  · cases h2

/-- one step of the walk -/
theorem live_stepR (hsp : Cov C.E F C.sp) (ht : tableOK C l Fu = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveR C l F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    C.ok A = true ∧
    ((∃ A', LiveR C l F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
      (go step m).2.frame = m.frame + 1) := by
  obtain ⟨hs, n, hw0⟩ := hl
  cases n with
  | zero => simp [walkR] at hw0
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    simp only [walkR, hx', Bool.false_or, Bool.and_eq_true] at hw0
    obtain ⟨hokA, hw1⟩ := hw0
    refine ⟨hokA, ?_⟩
    obtain ⟨A₁, hA, hs1, hk1⟩ := CollKeep.cov_preKX hsp hh hs
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw1
    obtain ⟨hd, hw2⟩ := hw1 A₁ hA
    obtain ⟨r, hr, hB⟩ := AfterKeep.s_kstepL hops hd hh hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      have h1' := fixR_sim hs1 h1
      have hkf := fixR_k C.E A₁ B
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨_, k2⟩
      · left
        have e : (fixR C.E A₁ B).k = A.k := by rw [hkf, k1, hk1]
        rw [if_pos (by simp [e])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
        rcases hw3 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveR ht hkl h1' h3
          exact ⟨D, hD, by rw [hk, e], k2, k3⟩
        · exact ⟨_, ⟨h1', n, h3⟩, e, k2, k3⟩
      · right
        exact k2

/-- **The walk: from `k` to the frame's end, each instruction of the frame meets `ok` in a state that covers it**. `CleanK` of the walk's guard is asked of each
instruction from `k` on, in the frame. -/
theorem okR_all (hsp : Cov C.E F C.sp) (ht : tableOK C l Fu = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkR C l Fu' A = true)
    (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, k ≤ j → (trace m i j).frame = m.frame → FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∀ j, k ≤ j → (trace m i j).frame = m.frame → ∃ B, Sim C.E F B (trace m i j) ∧ C.ok B = true := by
  have key : ∀ d, (∃ A, LiveR C l F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      (trace m i (k + d)).frame = m.frame + 1 := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | h1
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases (live_stepR hsp ht hkl hops h1 (hcl (k + d) (by omega) h2) (hx (k + d))).2 with ⟨A', a1, _, a3, a4⟩ | a1
        · exact Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩
        · exact Or.inr (by rw [a1, h2])
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr h1
  intro j hj hfj
  rcases key (j - k) with ⟨A, h1, h2, _⟩ | h1
  · rw [show k + (j - k) = j by omega] at h1 h2
    exact ⟨A, h1.1, (live_stepR hsp ht hkl hops h1 (hcl j hj hfj) (hx j)).1⟩
  · rw [show k + (j - k) = j by omega] at h1
    omega

end

/-! ## Finding the table: a search, no part of the proof -/

/-- the bounds of a state that is not in the table: those of its known bits -/
def rngOf (b : AB) : Nat × Nat := (b.minv.toNat, b.maxv.toNat)

def withB (A : AS) (x y : Nat × Nat) : AS := { A with log := [x.1, x.2, y.1, y.2] }

def hullB (p q : Nat × Nat) : Nat × Nat := (Nat.min p.1 q.1, Nat.max p.2 q.2)

def subB (p q : Nat × Nat) : Bool := decide (q.1 ≤ p.1) && decide (p.2 ≤ q.2)

/-- the bounds of `A`: its `log`, or those of its known bits -/
def bndS (A : AS) (j : Nat) : Nat × Nat := match A.log with
  | [_, _, _, _] => bnd A j
  | _ => rngOf (regB A j)

/-- the search's step into the table, with the bounds -/
def routeB (S : FrameKeep.Spot) (G : PipeWrites.Guard) (keep : List Nat) (key : AS → Nat) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let B := withB (PrevKeep.normP S G keep B0) (bndS B0 0) (bndS B0 1)
  let K := key B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (PipeWrites.knownOf D)
      let J := withB (PipeWrites.joinK Q B l) (hullB (bndS Q 0) (bndS B 0)) (hullB (bndS Q 1) (bndS B 1))
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (PipeWrites.knownOf D)
      if PipeWrites.leK B D l && subB (bndS B 0) (bndS D 0) && subB (bndS B 1) (bndS D 1) then
        { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) }
      else
      let J0 := withB (PipeWrites.joinK D B l) (hullB (bndS D 0) (bndS B 0)) (hullB (bndS D 1) (bndS B 1))
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

/-- the search from one piece: straight runs, the pieces of a split one by one, the other successors into the table -/
partial def runR (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (ok : AS → Bool)
    (l : List Nat) (keep : List Nat) (P0 : PrevKeep.PS) (k0 : Nat) (A0 : AS) : PrevKeep.PS := Id.run do
  let ⟨X0, pred0, fa0, ch0, st0, dr0⟩ := P0
  let mut X := X0
  let mut pred := pred0
  let mut fa := fa0
  let mut ch := ch0
  let mut work : List (AS × Nat) := [(A0, 0)]
  let mut guardN := 0
  while guardN < 100000 do
    guardN := guardN + 1
    match work with
    | [] => break
    | (c0, r0) :: rest =>
    work := rest
    let mut cur := c0
    let mut run := r0
    while true do
      if FrameKeep.storesTo l E.prg E.mask cur.pc then
        ch := ch.insert cur.pc.toNat (ch.getD cur.pc.toNat 0 + 1)
        break
      if !ok cur then
        fa := fa.push (k0, cur)
        X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
        break
      let pre := FrameKeep.preK S G cur
      let ps := pre.flatMap sp
      if pre.length == 1 && ps.length > 1 then
        work := (ps.map fun p => (p, run)) ++ work
        break
      let dec := ps.any fun A₁ => isRkDec E A₁.pc (LagFrames.opOf E A₁)
      let rs := ps.flatMap fun A₁ => (FrameKeep.kstep S G E ops A₁).map (Option.map (fixR E A₁))
      X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
      if dec || rs.any (·.isNone) then
        fa := fa.push (k0, cur)
        X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
      let good := (rs.filterMap id).filter fun b => b.k == cur.k
      match good with
      | [b] =>
        if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && !FrameKeep.storesTo l E.prg E.mask b.pc &&
            (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
          cur := b
          run := run + 1
          continue
        else pure ()
      | _ => pure ()
      for b in good do
        let K := key (withB (PrevKeep.normP S G keep b) (bndS b 0) (bndS b 1))
        if !(pred.contains K) then pred := pred.insert K (k0, cur.pc)
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeB S G keep key X b
      break
  return ⟨X, pred, fa, ch, st0, dr0⟩

/-- the search: each pending state of the table, in its pieces -/
partial def searchR (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (ok : AS → Bool)
    (l : List Nat) (keep : List Nat) (W : Nat) (P0 : PrevKeep.PS) : PrevKeep.PS := Id.run do
  let mut P := P0
  while true do
    match P.X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      let ⟨X, pr, fa, ch, st, dr⟩ := P
      P := ⟨{ X with pending := X.pending.erase k }, pr, fa, ch, st, dr⟩
      for B in pieces W A do
        P := runR S G E key ops sp ok l keep P k B
  return P

/-- the limit of the pieces of a table state -/
def wLim : Nat := 17

/-- the zero page: the bytes that the search's table keeps besides the guard's -/
def zKeep : List Nat := List.range 256

/-- the search from the states at the scroll handler's call `starts` -/
def searchSide (sy : Syms) (m0 : Machine) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardE sy m0
  let E := PipeEntryRule.envOf m0
  let key := PrevKeep.keyP S G []
  let X := starts.foldl (routeB S G zKeep key) {}
  searchR S G E key (aRows E).toArray (splitR E 4 xOps yOps) (okR sy m0 E) (FrameKeep.ctlI sy) zKeep wLim { X }

/-- **The walk's table**, from the states at the scroll handler's call `starts` -/
def rCfg (sy : Syms) (m0 : Machine) (starts : List AS) : CfgR :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardE sy m0
  let E := PipeEntryRule.envOf m0
  let key := PrevKeep.keyP S G []
  let q := FrameKeep.tableOfKW key (searchSide sy m0 starts).X
  { E, ops := (aRows E).toArray, S, G, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, W := wLim,
    sp := splitR E 4 xOps yOps, ok := okR sy m0 E }

/-- what the first walk asks at the scroll handler's call: the walk of this file succeeds -/
def atR (sy : Syms) (C : CfgR) (B : AS) : Bool := walkR C (FrameKeep.ctlI sy) FrameKeep.fuelK B

/-- the walk of the pause bit up to the cut, then the first walk to the scroll handler's call, then the walk of this file -/
def cfgPR (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 : FrameKeep.CfgK) (C : CfgR) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atR sy C) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check on the ROM**: the walk of the pause bit up to the cut; from there the first walk of `AfterKeep` to the scroll handler's call; from there the walk of
this file to the frame's end -/
def rCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let C := rCfg sy m0 P.stops.toList
  CtrlKeep.ctrlCheck1 (cfgPR sy m0 v q C1 C) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atR sy C) FrameKeep.fuelK) &&
    tableOK C (FrameKeep.ctlI sy) FrameKeep.fuelK

/-- the search's failures and its size, for a program (no part of the proof) -/
def rFails (sy : Syms) (m0 : Machine) (v : UInt8) : Nat × List Nat × Nat × Nat :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let R := searchSide sy m0 P.stops.toList
  (R.X.fails, R.X.failPcs.toList.map (·.1), R.X.done.size, R.X.multi.size)

/-! ## On the ROM: one frame -/

section Frames
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {m0 : Machine}

/-- **A store that may reach the side collision's timer and is not one of `Resid` does not write it**, from the scroll handler's call to the frame's end: with the
hypotheses of `PushTimer.pix_end` but `posW` and `sideW`, the frame comes to the scroll handler at `kq`, and from there each instruction of the frame that is a
store of `PushTimer.NearW` and not of `Resid` meets `PushTimer.SideW`. `hr` is the check on the ROM. -/
theorem near_side {v : UInt8} (hr : rCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hc : CtrlKeep.ctrlCheck sy m0 = true) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ kq, n₀ < kq ∧ (trace m i kq).pc = sy.PlayerSubs ∧ (trace m i kq).frame = m.frame ∧ (∀ j, n₀ < j → j < kq → (trace m i j).pc ≠ sy.PlayerSubs) ∧
      ∀ j, kq ≤ j → (trace m i j).frame = m.frame → PushTimer.NearW sy m0 (trace m i j) → ¬ Resid sy (trace m i j) →
        PushTimer.SideW sy m0 (trace m i j) := by
  simp only [rCheck, Bool.and_eq_true] at hr
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hr
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  rcases CtrlKeep.cut_or_end2 (C := cfgPR sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (rCfg sy m0 P.stops.toList))
      hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := EdgeStep.watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atR sy (rCfg sy m0 P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨kq, hkq, hqq, hfq, hdq, hbq, Bq, hatq, hsq⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA a2 a5 hclF hx'
    refine ⟨kq, hkq, hqq, hfq, hbq, fun j hj hfj hn hres => ?_⟩
    have hw1 : walkR (rCfg sy m0 P.stops.toList) (FrameKeep.ctlI sy) FrameKeep.fuelK Bq = true := hatq
    obtain ⟨B', hsB, hok⟩ := okR_all (C := rCfg sy m0 P.stops.toList) (cov_splitR 4 xOps yOps) hp3 rfl rfl hw1 hsq hfq hdq
      (fun j _ _ => hcl j) hx' j hj hfj
    exact okR_spec hsB hok hn hres
  · exact absurd harr (hno n₀ hf0)

end Frames

end Smbrta.SideRange
