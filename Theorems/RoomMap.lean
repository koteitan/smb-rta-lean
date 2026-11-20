import Theorems.ScreenStart
import Theorems.SideEntryRule
import Theorems.PipeWrites

/-!
# The block map in the room

At the first control in the room the rows of the change into the room (`PipeChangeEnd`) know every byte of the two block buffers. Here the walk of one whole frame in the room of
`ScreenPage` is run again with more known bits: in each byte of the block buffers, the bits that are 0 in the map (`mapRef`: the machine at the first control in the room after the
reference entry into the pipe, with no input). The only write into the block buffers that the walk does not know is the erase of a coin. It writes 0, so it keeps these bits
(`stepT`, `s_eraseT`). So a frame that starts with them ends with them or leaves the player's routine (`room_stepT`), and every frame from the first control to the entry keeps
them (`map_run`).

A byte with these bits is neither of the side pipe's two tiles unless it is in the pipe's column: the walk checks this at each read of the block buffer routine (`tilesB`). So at
every read of every frame from the first control to the entry, the side pipe's tiles are only in the pipe's column: this is `PoleEntryRule.TilesOK` for the side pipe
(`map_of_rows`).

The walk also checks at each state the conditions of `PipeWrites.Clean` that `SiteOK` does not give (`cleanS`): a store through an index or a pointer has a known target
outside the guard's bytes, or it is the erase of a coin; the jump routine's index is known and in its table. So every instruction of these frames is `Clean` (`clean_of_rows`).
And the room's condition at the start of each frame is a `PipeWrites.FrameStart` (`startCheckF`, `start_of_rowsF`). The guard is the room's (`SideFrame.roomG`): the
screen's bytes that the scroll handler reads are known at each frame's start and protected from stores through an index or a pointer. The walk cuts two places (`roomGB`): the
routine of the head's collision with a block (`PipeWrites.headAt`) and the bump of the head on a solid block (`SideFrame.bumpAt`). No state of the walk is at either of them
(`cuts_run`, `head_of_rows`, `bump_of_rows`): `SiteOK` lets a read for the head give only nothing or a coin. So no frame of the room changes the vertical motion by the head's
collision with a block. The walks of the entering frame (`SideEntryEnd`, `SideEntryRest`) use these facts on the entering frame (and `SideFrame` four of them), and
`Route.Run.roomBump` the last one on the frames before it (`RoomJoin.InRoom.bump`); `RoomVert` uses the condition at each frame's start (`cond_of_rows`).

What stays assumed is what `ScreenPage` assumes: `SiteOK` on each instruction of the frames, and that each frame before the entry starts in the player's routine. The condition at
the first control comes from the rows of the time of the change (`start_of_rows`). No game data: the map comes from a reference machine. Page: `1-1/c-7-12-RoomMap.md`.
-/

namespace Smbrta.RoomMap

open PipeTransition (frame)
open PipeTransitionAll (Names go ba_get_set_self ba_get_set_ne ba_size_set go_bind)
open SideChangeBound
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop)
open ScreenPage (Places SiteOK PlacesOK CfgS clampS preS stepS readStep writeStep tilesFor coverS weaken RoomCond startsR startR maskOf MaskOK maskOK maskOK_spec
  endUnder sim_of_room room_of_sim room_of_end writeAddr aPtrW s_ptrW op_91 cyc_91 step_at)
open PoleEntryRule (Spots onCol TilesOK AtRead)

/-! ## The bits of the map -/

/-- the map: the machine at the first control in the room, after the reference entry into the pipe with no input -/
def mapRef (m0 : Machine) : Machine := PipeTransition.run (PipeTransition.entry m0) (PipeTransition.zeros 91)

/-- in each byte of the block buffers, the bits that are 0 in the map -/
def bufK (lo n : Nat) (r : Machine) : List (Nat × UInt8) := (List.range n).map fun j => (lo + j, ~~~ r.ram.get! (lo + j))

/-- the written value is known, and every byte of the block buffers agrees with it on its known bits -/
def bufAgree (P : Places) (A : AS) : Bool :=
  A.a.isK && (List.range P.bufN).all fun j => (A.getK (P.bufLo + j)).v &&& (A.getK (P.bufLo + j)).k == A.a.v &&& (A.getK (P.bufLo + j)).k

/-- the byte, as far as it is known, is not `t` -/
def excl (b : AB) (t : UInt8) : Bool := t &&& b.k != b.v &&& b.k

/-- at a read of the block buffer routine, a byte of the block buffers out of the pipe's column is known to be neither tile -/
def tilesB (Q : Spots) (A : AS) : Bool :=
  A.pc != Q.read || (List.range Q.bufBytes).all fun j => onCol Q (Q.bufLo + j) || (excl (A.getK (Q.bufLo + j)) Q.ball && excl (A.getK (Q.bufLo + j)) Q.shaft)

/-! ## The walk -/

/-- a step: at the erase of a coin, a write through a pointer not known into the block buffers, with the value that agrees with their known bits; else the step of `ScreenPage` -/
def stepT (P : Places) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if !A.nmi && A.pc == P.erase && A.pc != P.read then [if bufAgree P A && !A.rk then writeStep E A else none]
  else stepS P E ops A

/-! ## The conditions of `PipeWrites.Clean` that the walk knows -/

/-- the target of a store through an index or a pointer, as far as the abstract machine knows it; `none` if the instruction is not such a store -/
def storeAd (E : Env) (A : AS) (op : UInt8) : Option (Option AAd) :=
  if op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6 then some ((aZpi E (·.x) { A with pc := A.pc + 1 }).map (·.1))
  else if op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E then some ((aAbi E (·.x) { A with pc := A.pc + 1 }).map (·.1))
  else if op == 0x99 then some ((aAbi E (·.y) { A with pc := A.pc + 1 }).map (·.1))
  else if op == 0x91 then some ((aIzy E { A with pc := A.pc + 1 }).map (·.1))
  else none

/-- such a store has a known target outside the guard's bytes, or it is the erase of a coin -/
def storeOK (G : PipeWrites.Guard) (P : Places) (E : Env) (A : AS) : Bool :=
  A.pc == P.erase || match storeAd E A (E.prg.get! (A.pc &&& E.mask).toNat) with
    | none => true
    | some (some ad) => ad.lo == ad.hi && PipeWrites.plainB G.prot ad.lo
    | some none => false

/-- at the jump routine, the index is known and in its table -/
def jumpOK (G : PipeWrites.Guard) (A : AS) : Bool :=
  A.pc != G.je || (A.a.isK && match ptrOf (A.getK (0x100 + A.s.toNat + 1)) (A.getK (0x100 + A.s.toNat + 2)) with
    | some r => (match G.jumps.lookup (r + 1).toNat with
      | some n => decide (A.a.v.toNat < n)
      | none => true)
    | none => false)

/-- the conditions of `Clean` on the instruction of a state: it is in the ROM, its store and its jump are as `Clean` asks -/
def cleanS (G : PipeWrites.Guard) (P : Places) (E : Env) (A : AS) : Bool := decide (0x8000 ≤ A.pc) && storeOK G P E A && jumpOK G A

/-- at the frame's end: the tiles, `Clean`, and a start state of the condition, or the routine is known and is not the reference's -/
def finT (Q : Spots) (G : PipeWrites.Guard) (E : Env) (P : Places) (r : Machine) (K : List (Nat × UInt8)) (B : AS) : Bool :=
  tilesB Q B && cleanS G P E B && !G.cuts.contains B.pc && (endUnder r K B || (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI))

/-- the walk of `ScreenPage` with `stepT`, and the tiles, `Clean` and no place of the guard's cuts at each state -/
def walkT (Q : Spots) (G : PipeWrites.Guard) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => tilesB Q A && cleanS G C.P C.E A && !G.cuts.contains A.pc && (preS C.P (clampS C.P A)).all fun A₁ => (stepT C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkT Q G C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-! ## The erase covers the machine -/

section
variable {E : Env} {F : Nat × UInt8}

/-- a byte of the RAM may take a value that agrees with its known bits -/
theorem sim_wrv {A : AS} {m : Machine} {i : Nat} {v : UInt8} (hE : E.D = []) (hk : v &&& A.kn.get! i = A.ram.get! i &&& A.kn.get! i) (hr : A.rk = false)
    (hs : Sim E F A m) : Sim E F A { m with ram := m.ram.set! i v } := by
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
      exact hk
    · rw [ba_get_set_ne _ _ _ _ h]
      exact hs.ram j hj
  · intro hd
    have := hs.dg hd
    rw [hE] at this
    exact absurd this (by simp)
  · intro h
    rw [hr] at h
    cases h

/-- `STA (zp),Y` through a pointer not known, with a known `A` that agrees with the known bits of the byte written -/
theorem s_eraseT {A : AS} {m : Machine} {B : AS} (hE : E.D = []) (hs : Sim E F A m) (hn : A.nmi = false) (hp : 0x8000 ≤ A.pc)
    (hop : E.prg.get! (A.pc &&& E.mask).toNat = 0x91) (hr : A.rk = false) (had : writeAddr m < 0x2000) (ha : A.a.isK = true)
    (hag : A.a.v &&& A.kn.get! (writeAddr m &&& 0x7FF).toNat = A.ram.get! (writeAddr m &&& 0x7FF).toNat &&& A.kn.get! (writeAddr m &&& 0x7FF).toNat)
    (hB : writeStep E A = some B) :
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
    -- the state after the operand has the same bytes and the same `A`
    have hA2 : A2.kn = A.kn ∧ A2.rk = A.rk ∧ A2.ram = A.ram ∧ A2.a = A.a := by
      unfold ScreenPage.aPtrW afetch at h1
      simp only [bind, StateT.bind] at h1
      split at h1
      · have h5 := TaintRun.some_pair h1
        rw [← h5.2]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · cases h1
    generalize hm2 : (go mIzy { m with pc := m.pc + 1 }).2 = m2 at s2 a2
    have hv : m2.a = A.a.v := by
      have h6 := s2.a
      rw [hA2.2.2.2] at h6
      exact PipeEntryRule.known_eq ha h6
    have hk2 : m2.a &&& A2.kn.get! (writeAddr m &&& 0x7FF).toNat = A2.ram.get! (writeAddr m &&& 0x7FF).toNat &&& A2.kn.get! (writeAddr m &&& 0x7FF).toNat := by
      rw [hv, hA2.1, hA2.2.2.1]
      exact hag
    have e : go ((opSTA mIzy) >>= fun _ => tick 6) { m with pc := m.pc + 1 } = go (tick 6) (go (wr (writeAddr m) m2.a) m2).2 := by
      rw [go_bind]
      have e2 : go (opSTA mIzy) { m with pc := m.pc + 1 } = go (mIzy >>= fun ad => (MonadState.get : M Machine) >>= fun t => wr ad t.a) { m with pc := m.pc + 1 } := rfl
      rw [e2, go_bind, hm2]
      rfl
    have s3 := sim_wrv (E := E) (F := F) (i := (writeAddr m &&& 0x7FF).toNat) hE hk2 (by rw [hA2.2.1]; exact hr) s2
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

/-! ## One step, and the walk -/

section
variable {E : Env} {F : Nat × UInt8} {P : Places}

theorem s_stepT {ops : Array (AM Unit)} (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK P m) :
    ∃ r ∈ stepT P E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold stepT
  by_cases hc : (!A.nmi && A.pc == P.erase && A.pc != P.read) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨hn, hpc⟩, _⟩ := hc
    have hm : m.pc = P.erase := by rw [hs.pc]; exact hpc
    refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
    split at hB
    · rename_i hc2
      simp only [bufAgree, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, beq_iff_eq] at hc2
      obtain ⟨⟨ha, hall⟩, hr⟩ := hc2
      obtain ⟨g1, g2, g3⟩ := hh.erase hm
      have h5 := hall ((writeAddr m &&& 0x7FF).toNat - P.bufLo) (List.mem_range.2 (by omega))
      have h6 : P.bufLo + ((writeAddr m &&& 0x7FF).toNat - P.bufLo) = (writeAddr m &&& 0x7FF).toNat := by omega
      rw [h6] at h5
      exact s_eraseT hO.noD hs hn (by rw [hpc]; exact hO.erase.1) (by rw [hpc]; exact hO.erase.2) hr g1 ha h5.symm hB
    · cases hB
  · rw [if_neg hc]
    exact ScreenPage.s_stepS hO hops hT hs hh

/-- what `Clean` needs of the places: the idle loop and the time of the guard, and the block buffers outside the guard's bytes -/
structure CleanFacts (G : PipeWrites.Guard) (P : Places) : Prop where
  idle : P.idle = G.idle
  late : P.late ≤ G.late
  buf : ∀ i, P.bufLo ≤ i → i < P.bufLo + P.bufN → i ∉ G.prot

/-- `CleanFacts` as a check -/
def cleanFactsB (G : PipeWrites.Guard) (P : Places) : Bool :=
  P.idle == G.idle && decide (P.late ≤ G.late) && (List.range P.bufN).all fun j => !G.prot.contains (P.bufLo + j)

theorem cleanFacts_of {G : PipeWrites.Guard} {P : Places} (h : cleanFactsB G P = true) : CleanFacts G P := by
  simp only [cleanFactsB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun i a b hm => ?_⟩
  have h4 := h3 (i - P.bufLo) (by omega)
  rw [show P.bufLo + (i - P.bufLo) = i by omega] at h4
  simp [hm] at h4

theorem plain_of_plainB {prot : List Nat} {t : UInt16} (h : PipeWrites.plainB prot t = true) : PipeWrites.Plain prot t := by
  simp only [PipeWrites.plainB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
  · left
    refine ⟨h1, fun hm => ?_⟩
    have e : prot.contains (t &&& 0x7FF).toNat = List.elem (t &&& 0x7FF).toNat prot := rfl
    rw [e, List.elem_eq_true_of_mem hm] at h2
    cases h2
  · exact Or.inr ⟨h1, h2, h3⟩

/-- a store whose abstract target is one known address -/
theorem exact_target {am : AMode} {md : M UInt16} (hsnd : Snd E F AdR am md) {A1 : AS} {m1 : Machine} (hs : Sim E F A1 m1) {prot : List Nat}
    (h : (match some ((am A1).map (·.1)) with
      | none => true
      | some (some ad) => ad.lo == ad.hi && PipeWrites.plainB prot ad.lo
      | some none => false) = true) : PipeWrites.Plain prot (go md m1).1 := by
  cases ha : am A1 with
  | none =>
    rw [ha] at h
    cases h
  | some p =>
    obtain ⟨ad, A'⟩ := p
    rw [ha] at h
    simp only [Option.map_some, Bool.and_eq_true, beq_iff_eq] at h
    rw [adR_same (hsnd A1 m1 hs ad A' ha).1 h.1]
    exact plain_of_plainB h.2

/-- **`Clean` from the walk**: a machine covered by a state that passes `cleanS`, and that meets `SiteOK`, meets `PipeWrites.Clean` -/
theorem clean_of_sim {G : PipeWrites.Guard} (hO : PlacesOK E P) (hG : CleanFacts G P) {A : AS} {m : Machine} (hs : Sim E F A m) (hc : cleanS G P E A = true)
    (hh : SiteOK P m) : PipeWrites.Clean G m := by
  simp only [cleanS, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hp, hst⟩, hj⟩ := hc
  have hop : PipeWrites.opAt m = E.prg.get! (A.pc &&& E.mask).toNat := by
    unfold PipeWrites.opAt
    rw [hs.prg, hs.mask, hs.pc]
  have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with pc := by show m.pc + 1 = A.pc + 1; rw [hs.pc] }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    by_cases herase : A.pc = P.erase
    · have hop2 : PipeWrites.opAt m = 0x91 := by rw [hop, herase]; exact hO.erase.2
      rw [hop2] at ht
      have e : t = writeAddr m := by
        unfold PipeWrites.wTarget at ht
        simp only [show ((0x91 : UInt8) == 0x95 || (0x91 : UInt8) == 0x94 || (0x91 : UInt8) == 0xD6 || (0x91 : UInt8) == 0xF6) = false by decide,
          show ((0x91 : UInt8) == 0x9D || (0x91 : UInt8) == 0xDE || (0x91 : UInt8) == 0xFE || (0x91 : UInt8) == 0x7E) = false by decide,
          show ((0x91 : UInt8) == 0x99) = false by decide, show ((0x91 : UInt8) == 0x91) = true by decide, Bool.false_eq_true, if_false, if_true, Option.some.injEq] at ht
        exact ht.symm
      obtain ⟨g1, g2, g3⟩ := hh.erase (by rw [hs.pc]; exact herase)
      left
      rw [e]
      exact ⟨g1, hG.buf _ g2 g3⟩
    · have hne : (A.pc == P.erase) = false := by simpa using herase
      simp only [storeOK, hne, Bool.false_or] at hst
      rw [hop] at ht
      unfold storeAd at hst
      unfold PipeWrites.wTarget at ht
      generalize E.prg.get! (A.pc &&& E.mask).toNat = op at hst ht
      by_cases c1 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true
      · rw [if_pos c1] at hst ht
        rw [← Option.some.inj ht]
        exact exact_target TaintRun.s_mZpx hs1 hst
      rw [if_neg c1] at hst ht
      by_cases c2 : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = true
      · rw [if_pos c2] at hst ht
        rw [← Option.some.inj ht]
        exact exact_target TaintRun.s_mAbx hs1 hst
      rw [if_neg c2] at hst ht
      by_cases c3 : (op == 0x99) = true
      · rw [if_pos c3] at hst ht
        rw [← Option.some.inj ht]
        exact exact_target TaintRun.s_mAby hs1 hst
      rw [if_neg c3] at hst ht
      by_cases c4 : (op == 0x91) = true
      · rw [if_pos c4] at hst ht
        rw [← Option.some.inj ht]
        exact exact_target TaintRun.s_mIzy hs1 hst
      rw [if_neg c4] at ht
      cases ht
  · intro h0
    exact hh.reads (by rw [hs.pc]; exact hp) h0
  · intro hpc n hn
    have hA : A.pc = G.je := by rw [← hs.pc]; exact hpc
    simp only [jumpOK, hA, bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at hj
    obtain ⟨ha, hj⟩ := hj
    cases hpt : ptrOf (A.getK (0x100 + A.s.toNat + 1)) (A.getK (0x100 + A.s.toNat + 2)) with
    | none =>
      rw [hpt] at hj
      cases hj
    | some r =>
      rw [hpt] at hj
      simp only at hj
      have hsz : A.s.toNat < 256 := A.s.toNat_lt
      have e1 := hs.ram (0x100 + A.s.toNat + 1) (by omega)
      have e2 := hs.ram (0x100 + A.s.toNat + 2) (by omega)
      have e3 := TaintRun.ptrOf_ok hpt e1 e2
      have ht : PipeWrites.tableOf m = r + 1 := by
        unfold PipeWrites.tableOf
        rw [hs.s, e3]
      rw [ht] at hn
      rw [hn] at hj
      simp only [decide_eq_true_eq] at hj
      have hma : m.a = A.a.v := PipeEntryRule.known_eq ha hs.a
      rw [hma]
      exact hj
  · intro hpc
    exact Nat.le_trans (hh.late (by rw [hG.idle]; exact hpc)) hG.late

/-- **The tiles at a read**: a machine at the read of the block buffer routine, covered by a state that passes `tilesB`, has the side pipe's tiles only in the pipe's column -/
theorem tiles_of_sim {Q : Spots} (hQ : Q.pg = 0) (hbuf : Q.bufLo + Q.bufBytes ≤ 2048) {A : AS} {m : Machine} (hs : Sim E F A m) (ht : tilesB Q A = true)
    (hr : AtRead Q m) : TilesOK Q m := by
  intro i h1 h2 h3
  refine ⟨?_, by rw [hQ]; omega⟩
  have hpc : A.pc = Q.read := by rw [← hs.pc]; exact hr
  simp only [tilesB, Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at ht
  rcases ht with ht | ht
  · exact absurd hpc ht
  · have h4 := ht (i - Q.bufLo) (List.mem_range.2 (by omega))
    rw [show Q.bufLo + (i - Q.bufLo) = i by omega] at h4
    simp only [Bool.and_eq_true] at h4
    rcases h4 with h4 | ⟨h4, h5⟩
    · exact h4
    · exfalso
      have hm := hs.ram i (by omega)
      simp only [excl, bne_iff_ne, ne_eq] at h4 h5
      rcases h3 with h3 | h3
      · rw [h3] at hm
        exact h4 hm
      · rw [h3] at hm
        exact h5 hm

end

section
variable {Q : Spots} {G : PipeWrites.Guard} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveT (Q : Spots) (G : PipeWrites.Guard) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkT Q G C n A = true

theorem tiles_of_walkT {n : Nat} {A : AS} (h : walkT Q G C n A = true) : tilesB Q A = true := by
  cases n with
  | zero => simp [walkT] at h
  | succ n =>
    simp only [walkT, Bool.and_eq_true] at h
    exact h.1.1.1

theorem cleanS_of_walkT {n : Nat} {A : AS} (h : walkT Q G C n A = true) : cleanS G C.P C.E A = true := by
  cases n with
  | zero => simp [walkT] at h
  | succ n =>
    simp only [walkT, Bool.and_eq_true] at h
    exact h.1.1.2

theorem cut_of_walkT {n : Nat} {A : AS} (h : walkT Q G C n A = true) : A.pc ∉ G.cuts := by
  cases n with
  | zero => simp [walkT] at h
  | succ n =>
    simp only [walkT, Bool.and_eq_true] at h
    intro hm
    have h2 := h.1.2
    simp at h2
    exact h2 hm

theorem cover_liveT (ht : C.t.all (walkT Q G C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ D, LiveT Q G C F D m ∧ D.k = B.k := by
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

theorem live_stepT (hO : PlacesOK C.E C.P) (ht : C.t.all (walkT Q G C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hl : LiveT Q G C F A m) (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) :
    (∃ A', LiveT Q G C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkT] at hw
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    obtain ⟨A₁, hA, hs1, hk1⟩ := ScreenPage.cov_preS hO hs0 hh
    obtain ⟨r, hr, hB⟩ := s_stepT hO hops hT hs1 hh
    simp only [walkT, List.all_eq_true, Bool.and_eq_true] at hw
    have hw2 := hw.2 A₁ hA r hr
    have hkA : A₁.k = A.k := by rw [hk1, ScreenPage.clamp_k]
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
        · obtain ⟨D, hD, hk⟩ := cover_liveT ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h3
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S`, for every input, if each instruction meets `SiteOK`; and at each read of the block buffer
routine in the frame, the side pipe's tiles are only in the pipe's column; each instruction is `Clean` and at no place of the guard's cuts. -/
theorem frame_of_walkT (hO : PlacesOK C.E C.P) (ht : C.t.all (walkT Q G C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (hfin : ∀ B, C.fin B = true → tilesB Q B = true ∧ cleanS G C.P C.E B = true ∧ B.pc ∉ G.cuts) (hG : CleanFacts G C.P) (hQ : Q.pg = 0) (hbuf : Q.bufLo + Q.bufBytes ≤ 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkT Q G C Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, SiteOK C.P (trace m i j)) :
    ((frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i)) ∧
    (∀ j, AtRead Q (trace m i j) → TilesOK Q (trace m i j)) ∧ (∀ j, PipeWrites.Clean G (trace m i j)) ∧ ∀ j, (trace m i j).pc ∉ G.cuts := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveT Q G C F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
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
        rcases live_stepT hO ht hops hT h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3, h4⟩
  refine ⟨?_, fun j hr => ?_, fun j => ?_, fun j => ?_⟩
  · rw [frame_trace]
    rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h3, h4⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨h1, B, h2, h3, h4⟩
  · rcases key j with ⟨A, ⟨h1, n, h2⟩, _⟩ | ⟨_, B, h2, _, h4⟩
    · exact tiles_of_sim hQ hbuf h1 (tiles_of_walkT h2) hr
    · exact tiles_of_sim hQ hbuf h4 (hfin B h2).1 hr
  · rcases key j with ⟨A, ⟨h1, n, h2⟩, _⟩ | ⟨_, B, h2, _, h4⟩
    · exact clean_of_sim hO hG h1 (cleanS_of_walkT h2) (hk j)
    · exact clean_of_sim hO hG h4 (hfin B h2).2.1 (hk j)
  · rcases key j with ⟨A, ⟨h1, n, h2⟩, _⟩ | ⟨_, B, h2, _, h4⟩
    · rw [h1.pc]
      exact cut_of_walkT h2
    · rw [h4.pc]
      exact (hfin B h2).2.2

end

/-! ## The frames in the room -/

/-- what the check says -/
structure RoomOKT (Q : Spots) (G : PipeWrites.Guard) (E : Env) (P : Places) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) (Fu : Nat) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = finT Q G E P r K
  table : C.t.all (walkT Q G C Fu) = true
  starts : ∀ S ∈ startsR r K, walkT Q G C Fu S = true
  clean : CleanFacts G P
  pg : Q.pg = 0
  buf : Q.bufLo + Q.bufBytes ≤ 2048

section
variable {Q : Spots} {G : PipeWrites.Guard} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat}

/-- **One frame in the room.** A frame that starts in the condition ends in it, or with another routine; and at each read of the block buffer routine the side pipe's tiles are
only in the pipe's column. -/
theorem room_stepT (h : RoomOKT Q G E P r K C Fu) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (RoomCond E r K (frame m i) ∨ (frame m i).ram.get! P.rtI ≠ r.ram.get! P.rtI) ∧ (∀ j, AtRead Q (trace m i j) → TilesOK Q (trace m i j)) ∧
    (∀ j, PipeWrites.Clean G (trace m i j)) ∧ ∀ j, (trace m i j).pc ∉ G.cuts := by
  obtain ⟨S, hS, hs⟩ := sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S hS
  have hs' : Sim C.E (m.frame, 2) S m := by rw [h.env]; exact hs
  have hfin : ∀ B, C.fin B = true → tilesB Q B = true ∧ cleanS G C.P C.E B = true ∧ B.pc ∉ G.cuts := by
    intro B hB
    rw [h.fin] at hB
    simp only [finT, Bool.and_eq_true] at hB
    rw [h.env, h.pl]
    refine ⟨hB.1.1.1, hB.1.1.2, fun hm => ?_⟩
    have h2 := hB.1.2
    simp at h2
    exact h2 hm
  have hG : CleanFacts G C.P := by rw [h.pl]; exact h.clean
  obtain ⟨⟨_, B, h2, _, h4⟩, ht, hcl, hcu⟩ := frame_of_walkT (i := i) hO h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) hfin hG h.pg h.buf hw hs'
    (by rw [h.pl]; exact hk)
  refine ⟨?_, ht, hcl, hcu⟩
  rw [h.env] at h4
  rw [h.fin] at h2
  simp only [finT, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h2
  rcases h2.2 with h3 | ⟨⟨a1, a2⟩, a3⟩
  · left
    exact room_of_end h.mask h4 h3
  · right
    have e := PipeEntryRule.known_eq a2 (h4.ram _ a1)
    rw [e]
    exact a3

/-- **Every frame from the first control in the room to the entry.** The frames before `e` start in the condition and stay in the player's routine. Then each of them starts in the
condition, and at each read of the block buffer routine in each of them the side pipe's tiles are only in the pipe's column. -/
theorem map_run (h : RoomOKT Q G E P r K C Fu) {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat}
    (h0 : RoomCond E r K (seq c))
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK P (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! P.rtI = r.ram.get! P.rtI) :
    (∀ n, c ≤ n → n < e → RoomCond E r K (seq n)) ∧ ∀ n, c ≤ n → n < e → ∀ j, AtRead Q (trace (seq n) (inp n) j) → TilesOK Q (trace (seq n) (inp n) j) := by
  have key : ∀ d, c + d < e → RoomCond E r K (seq (c + d)) := by
    intro d
    induction d with
    | zero => exact fun _ => h0
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := (room_stepT h h1 (hs (c + d) (by omega) (by omega))).1
      rw [← next] at h2
      rcases h2 with h3 | h3
      · exact h3
      · exact absurd (hr (c + d + 1) (by omega) hd) h3
  have hall : ∀ n, c ≤ n → n < e → RoomCond E r K (seq n) := by
    intro n h1 h2
    obtain ⟨d, rfl⟩ : ∃ d, n = c + d := ⟨n - c, by omega⟩
    exact key d h2
  exact ⟨hall, fun n h1 h2 => (room_stepT h (hall n h1 h2) (hs n h1 h2)).2.1⟩

/-- **`Clean` on every instruction of every frame from the first control in the room to the entry**, under the hypotheses of `map_run` -/
theorem clean_run (h : RoomOKT Q G E P r K C Fu) {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat}
    (h0 : RoomCond E r K (seq c))
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK P (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! P.rtI = r.ram.get! P.rtI) :
    ∀ n, c ≤ n → n < e → ∀ j, PipeWrites.Clean G (trace (seq n) (inp n) j) :=
  fun n h1 h2 => (room_stepT h ((map_run h next h0 hs hr).1 n h1 h2) (hs n h1 h2)).2.2.1

/-- **No place of the guard's cuts on any instruction of any frame from the first control in the room to the entry**, under the hypotheses of `map_run` -/
theorem cuts_run (h : RoomOKT Q G E P r K C Fu) {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat}
    (h0 : RoomCond E r K (seq c))
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK P (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! P.rtI = r.ram.get! P.rtI) :
    ∀ n, c ≤ n → n < e → ∀ j, (trace (seq n) (inp n) j).pc ∉ G.cuts :=
  fun n h1 h2 => (room_stepT h ((map_run h next h0 hs hr).1 n h1 h2) (hs n h1 h2)).2.2.2

end

/-! ## Finding the table: a search, no part of the proof -/

open ScreenPage (Aids SearchS routeS) in
partial def runT (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preS P (clampS P cur)).flatMap (stepT P E ops)
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

open ScreenPage (Aids SearchS routeS) in
partial def searchT (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := Z.key E A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runT P Z E ops X A
  return X

open ScreenPage (Aids SearchS routeS) in
def searchOfT (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchT P Z E ops ((startsR r K).foldl (routeS P Z E) {})

open ScreenPage (Aids) in
/-- the configuration from the table found -/
def cfgOfT (Q : Spots) (G : PipeWrites.Guard) (P : Places) (Z : Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOfT P Z E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd]).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin := finT Q G E P r K, t := q.1, key := Z.key E, idx := q.2.1, cut := q.2.2, norm := Z.norm, normAt := at0 }

/-- **The check of the walk.** -/
def walkCheckT (Q : Spots) (G : PipeWrites.Guard) (P : Places) (Z : ScreenPage.Aids) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOfT Q G P Z E r K
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && maskOK r K && C.t.all (walkT Q G C ScreenPage.fuelS) && (startsR r K).all (walkT Q G C ScreenPage.fuelS) &&
    cleanFactsB G P

theorem roomOKT_of_check {Q : Spots} {G : PipeWrites.Guard} {P : Places} {Z : ScreenPage.Aids} {E : Env} {r : Machine} {K : List (Nat × UInt8)} (h : walkCheckT Q G P Z E r K = true)
    (hpg : Q.pg = 0) (hb : Q.bufLo + Q.bufBytes ≤ 2048) : RoomOKT Q G E P r K (cfgOfT Q G P Z E r K) ScreenPage.fuelS := by
  simp only [walkCheckT, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, maskOK_spec h3, rfl, rfl, rfl, rfl, h4, h5, cleanFacts_of h6, hpg, hb⟩

/-! ## The room -/

section
open ScreenPage (placesR placesOf envR envOf refR aidsOf knownOf)

/-- the screen's bytes of the side pipe's walk, all bits known -/
def scrK (sy : Syms) (m0 : Machine) : List (Nat × UInt8) := (SideFrame.screenI sy m0).map fun i => (i, (255 : UInt8))

/-- the known bits: those of `ScreenPage`, the bits of the map, and the screen's bytes -/
def knownT (sy : Syms) (nm : Names) (m0 : Machine) : List (Nat × UInt8) :=
  knownOf nm ++ bufK (placesR sy nm m0).bufLo (placesR sy nm m0).bufN (mapRef m0) ++ scrK sy m0

/-- the side pipe's places, on the machine `m0` -/
abbrev spotsT (sy : Syms) (m0 : Machine) : Spots := SideEntryRule.spots sy m0

/-- the guard of the walk: the room's (`SideFrame.roomG`), with the two places of the head's collision cut: the routine of the head's collision with a block
(`PipeWrites.headAt`) and the bump on a solid block (`SideFrame.bumpAt`). Its conditions on one state are those of `roomG` (`clean_of_GB`). -/
def roomGB (sy : Syms) (m0 : Machine) : PipeWrites.Guard := { SideFrame.roomG sy m0 with cuts := [PipeWrites.headAt sy m0, SideFrame.bumpAt sy m0] }

/-- the conditions of `Clean` do not look at the places cut -/
theorem clean_cuts {G : PipeWrites.Guard} {c : List UInt16} {m : Machine} (h : PipeWrites.Clean { G with cuts := c } m) : PipeWrites.Clean G m :=
  ⟨h.store, h.read, h.jump, h.time⟩

theorem clean_of_GB {sy : Syms} {m0 m : Machine} (h : PipeWrites.Clean (roomGB sy m0) m) : PipeWrites.Clean (SideFrame.roomG sy m0) m := by
  unfold roomGB at h
  exact clean_cuts h

/-- the configuration of the walk -/
abbrev cfgT (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  cfgOfT (spotsT sy m0) (roomGB sy m0) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (knownT sy nm m0)

/-- **The check on the ROM**: the walk, the side pipe's page and the block buffers, and the reference has no bit in the block buffers that the map has not. The machines are
computed once. -/
def mapCheck (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let P := placesR sy nm m0
  let Q := spotsT sy m0
  let r := refR m0
  let mr := mapRef m0
  walkCheckT Q (roomGB sy m0) P (aidsOf sy nm m0) (envOf nm sy r) r (knownOf nm ++ bufK P.bufLo P.bufN mr ++ scrK sy m0) && Q.pg == 0 && decide (Q.bufLo + Q.bufBytes ≤ 2048) &&
    (List.range P.bufN).all fun j => r.ram.get! (P.bufLo + j) &&& ~~~ mr.ram.get! (P.bufLo + j) == 0

/-- what the check gives -/
structure MapFacts (sy : Syms) (nm : Names) (m0 : Machine) : Prop where
  ok : RoomOKT (spotsT sy m0) (roomGB sy m0) (envR sy nm m0) (placesR sy nm m0) (refR m0) (knownT sy nm m0) (cfgT sy nm m0) ScreenPage.fuelS
  sub : ∀ j, j < (placesR sy nm m0).bufN → (refR m0).ram.get! ((placesR sy nm m0).bufLo + j) &&& ~~~ (mapRef m0).ram.get! ((placesR sy nm m0).bufLo + j) = 0

theorem mapFacts_of_check {sy : Syms} {nm : Names} {m0 : Machine} (h : mapCheck sy nm m0 = true) : MapFacts sy nm m0 := by
  simp only [mapCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨roomOKT_of_check h1 h2 h3, h4⟩

/-! ## At the first control: from the rows of the change -/

open PipeChangeEnd (Data timeEnv timeCtx timeRows InRowsT)

/-- **The check on the ROM**: in the rows of the time of the change into the room, a machine with control is in a start state of the condition, with the bits of the map -/
def startCheckT (sy : Syms) (nm : Names) (d : Data) (e : Machine) (nmS : Names) (m0 : Machine) : Bool :=
  let r := refR m0
  let P := placesOf sy nmS m0 r
  let K := knownOf nmS ++ bufK P.bufLo P.bufN (mapRef m0) ++ scrK sy m0
  let E := envOf nmS sy r
  maskOK r K && decide ((timeEnv d e).prg.data = E.prg.data) && (timeEnv d e).mask == E.mask && ScreenStart.rowsR sy r K (timeRows (timeCtx sy nm d e) d e)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **The condition at the first control in the room, with the bits of the map**, for a machine with control in the rows of the time -/
theorem start_of_rows (hc : startCheckT sy nm d e nmS m0 = true) {m : Machine} (h : InRowsT sy nm d e m) (hm : controllable sy m = true) :
    RoomCond (envR sy nmS m0) (refR m0) (knownT sy nmS m0) m := by
  simp only [startCheckT, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have hM := maskOK_spec h1
  have hp := ScreenStart.ba_eq h2
  have hc0 : RoomCond (timeEnv d e) (refR m0) (knownT sy nmS m0) m := ScreenStart.room_of_invL hM h4 h hm
  exact ScreenStart.roomCond_env hc0 hp h3

/-- **The block map and the side pipe's tiles in the room, on the real machines.** `seq` lists the frames of a run; frame `b` is the first control in the room, a machine with
control in the rows of the change; each frame before `a` meets `SiteOK` on each instruction and starts in the player's routine. Then on each frame from `b` to `a`: every bit of
a byte of the block buffers that is 0 in the map is 0, and at each read of the block buffer routine the side pipe's tiles are only in the pipe's column. -/
theorem map_of_rows (hF : MapFacts sy nmS m0) (hc : startCheckT sy nm d e nmS m0 = true) {seq : Nat → Machine} {inp : Nat → UInt8}
    (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    (∀ n, b ≤ n → n < a → ∀ i, i < (placesR sy nmS m0).bufN →
      (seq n).ram.get! ((placesR sy nmS m0).bufLo + i) &&& ~~~ (mapRef m0).ram.get! ((placesR sy nmS m0).bufLo + i) = 0) ∧
    ∀ n, b ≤ n → n < a → ∀ j, AtRead (spotsT sy m0) (trace (seq n) (inp n) j) → TilesOK (spotsT sy m0) (trace (seq n) (inp n) j) := by
  have h0 := start_of_rows hc hin hctl
  obtain ⟨h1, h2⟩ := map_run hF.ok next h0 sites stay
  refine ⟨fun n a1 a2 i hi => ?_, h2⟩
  have hmem : ((placesR sy nmS m0).bufLo + i, ~~~ (mapRef m0).ram.get! ((placesR sy nmS m0).bufLo + i)) ∈ knownT sy nmS m0 :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  have hb := (h1 n a1 a2).bytes _ hmem
  simp only at hb
  rw [hb]
  exact hF.sub i hi


/-- **Every frame from the first control in the room to the entry starts in the room's condition**, under the hypotheses of `map_of_rows` -/
theorem cond_of_rows (hF : MapFacts sy nmS m0) (hc : startCheckT sy nm d e nmS m0 = true) {seq : Nat → Machine} {inp : Nat → UInt8}
    (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → RoomCond (ScreenPage.envR sy nmS m0) (refR m0) (knownT sy nmS m0) (seq n) :=
  (map_run hF.ok next (start_of_rows hc hin hctl) sites stay).1
end

/-! ## Each frame of the room starts in control -/

section
open ScreenPage (placesR envR refR)

/-- **The check on the ROM**: a machine in the room's condition starts a frame as `PipeWrites.FrameStart` asks with the room's guard (`SideFrame.roomG`: the screen's bytes too).
The reference machine is in the idle loop with the guard's stack pointer, the condition knows each byte of the guard whole and with the guard's value, the program is the same, and
the first dots are before the end of vblank. -/
def startCheckF (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let G := SideFrame.roomG sy m0
  let r := refR m0
  let K := knownT sy nm m0
  r.pc == G.idle && r.s == G.s0 && decide (9 < dotVblClr) &&
    G.known.all (fun p => K.contains (p.1, 255) && r.ram.get! p.1 == p.2) &&
    decide ((envR sy nm m0).prg.data = (PipeEntryRule.envOf m0).prg.data) && (envR sy nm m0).mask == (PipeEntryRule.envOf m0).mask

variable {sy : Syms} {nm nmS : Names} {d : PipeChangeEnd.Data} {e m0 : Machine}

/-- a machine in the room's condition starts a frame in control -/
theorem frameStart_of_cond (hc : startCheckF sy nmS m0 = true) {m : Machine} (h : RoomCond (envR sy nmS m0) (refR m0) (knownT sy nmS m0) m) :
    PipeWrites.FrameStart (SideFrame.roomG sy m0) (PipeEntryRule.envOf m0) m := by
  simp only [startCheckF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  have hd := h.dot
  refine ⟨by rw [h.pc]; exact h1, by rw [h.s]; exact h2, ?_, h.ctrl, ?_, h.strobe, h.halted, h.trk, ?_, ?_, h.size, ?_⟩
  · rcases h.flags with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨a, b, c⟩
    · exact Or.inr ⟨a, by omega, b, c⟩
  · rw [h.s0]
    have hl : m.fdot < dotVblClr := by omega
    simp [s0f, hl]
  · rw [h.prg]
    exact ScreenStart.ba_eq h5
  · rw [h.mask]
    exact h6
  · intro p hp
    obtain ⟨hk, hv⟩ := h4 p hp
    have hm : (p.1, (255 : UInt8)) ∈ knownT sy nmS m0 := List.mem_of_elem_eq_true hk
    have hb : (AB.known ((refR m0).ram.get! p.1)).mem (m.ram.get! p.1) := h.bytes _ hm
    rw [TaintRun.known_eq hb]
    exact hv

/-- **Each frame of the room starts in control**, on the real machines: under the conditions of `map_of_rows`, every frame from `b` to `a` starts in the idle loop, in control. -/
theorem start_of_rowsF (hF : MapFacts sy nmS m0) (hc : startCheckT sy nm d e nmS m0 = true) (hs : startCheckF sy nmS m0 = true) {seq : Nat → Machine} {inp : Nat → UInt8}
    (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : PipeChangeEnd.InRowsT sy nm d e (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → PipeWrites.FrameStart (SideFrame.roomG sy m0) (PipeEntryRule.envOf m0) (seq n) := by
  have h0 := start_of_rows hc hin hctl
  obtain ⟨h1, _⟩ := map_run hF.ok next h0 sites stay
  exact fun n a1 a2 => frameStart_of_cond hs (h1 n a1 a2)

/-- **`Clean` on every instruction of every frame of the room**, on the real machines, under the conditions of `map_of_rows`: the walk knows the target of each store through an
index or a pointer, and the index of each jump of the jump routine; `SiteOK` gives the reads through a pointer and the time -/
theorem clean_of_rows (hF : MapFacts sy nmS m0) (hc : startCheckT sy nm d e nmS m0 = true) {seq : Nat → Machine} {inp : Nat → UInt8}
    (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : PipeChangeEnd.InRowsT sy nm d e (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, PipeWrites.Clean (SideFrame.roomG sy m0) (trace (seq n) (inp n) j) :=
  fun n h1 h2 j => clean_of_GB (clean_run hF.ok next (start_of_rows hc hin hctl) sites stay n h1 h2 j)

/-- **No frame of the room comes to the routine of the head's collision with a block**, on the real machines, under the conditions of `map_of_rows`: a read for the head gives
nothing or a coin (`SiteOK`), so the walk never comes there -/
theorem head_of_rows (hF : MapFacts sy nmS m0) (hc : startCheckT sy nm d e nmS m0 = true) {seq : Nat → Machine} {inp : Nat → UInt8}
    (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : PipeChangeEnd.InRowsT sy nm d e (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, (trace (seq n) (inp n) j).pc ≠ PipeWrites.headAt sy m0 := by
  intro n h1 h2 j he
  apply cuts_run hF.ok next (start_of_rows hc hin hctl) sites stay n h1 h2 j
  rw [he]
  exact List.mem_cons_self

/-- **No frame of the room comes to the bump of the head on a solid block**, on the real machines, under the conditions of `map_of_rows`: the store of the vertical speed after the
head's check (`SideFrame.bumpAt`). The head's check comes there only after a read for the head that gives a tile other than nothing or a coin, and `SiteOK` lets such a read give only
these. With `head_of_rows`: no frame of the room changes the vertical motion by the head's collision with a block. -/
theorem bump_of_rows (hF : MapFacts sy nmS m0) (hc : startCheckT sy nm d e nmS m0 = true) {seq : Nat → Machine} {inp : Nat → UInt8}
    (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : PipeChangeEnd.InRowsT sy nm d e (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, (trace (seq n) (inp n) j).pc ≠ SideFrame.bumpAt sy m0 := by
  intro n h1 h2 j he
  apply cuts_run hF.ok next (start_of_rows hc hin hctl) sites stay n h1 h2 j
  rw [he]
  exact List.mem_cons_of_mem _ List.mem_cons_self

end

end Smbrta.RoomMap
