import Theorems.StartRun
import Theorems.PipeFrames
import Theorems.ScreenPage

/-!
# The block buffers, the jumpspring and the player's state on the first frames

The two block buffers hold the tiles that the collision code reads. At control they are those of the machine `m0`, the jumpspring byte is 0 and the player's state is 0:
the title's check knows them in every near state (`titleMapCheck`). A walk of one whole frame keeps them (`mapCheck`): it is the walk of `FrameKeep`, with the two buffers
and the jumpspring byte watched, the player's state known at the frame's start and 0, 1 or 2 at its end, and one more step. At the read of the block buffer routine
(`LDA (zp),Y`) the walk does not know the pointer; if the read is in the buffers, the value is one of their tiles, and the walk follows one path for each tile (`tstep`).
None of the tiles is a jumpspring or a climbing tile, so no path sets the jumpspring byte or the climbing state.

What is asked of each instruction (`MapOK`): a store through an index or a pointer does not write the player's state, the jumpspring byte or the buffers, and the read of the
block buffer routine is in the buffers. With `Clean` of every frame from control on (`PipeFrames.Lags`), every frame up to a bound, counted or not, starts with the buffers of
`m0`, the jumpspring byte 0 and the player's state 0, 1 or 2 (`Lags.mapAt`).

There is no game data in this file. Page: `1-1/a-5-4-3-3-3-OpenMap.md`.
-/

namespace Smbrta.OpenMap

open PipeTransition (frame)
open TaintRun (AS Sim Env AB)
open PipeWrites (Guard Clean FrameStart guardOf)
open PipeEntryRule (trace)
open FrameKeep (Watch Watched keepCheck CfgK Spot CleanK)
open PipeWrites (SG knownOf)
open PipeTransitionAll (go go_bind leaf_ppuRead leaf_padRead leaf_tick)
open TaintRun (StepRel mem_known_self)
open PipeEntryRule (nxt frame_trace)

/-- the RAM indices of the two block buffers (13 rows of 16 tiles each) -/
def bufI (sy : Syms) : List Nat :=
  (List.range 0xD0).map (fun j => (sy.Block_Buffer_1 &&& 0x7FF).toNat + j) ++ (List.range 0xD0).map (fun j => (sy.Block_Buffer_2 &&& 0x7FF).toNat + j)

/-- the watched bytes: every byte of the two block buffers, with its value in `m0` -/
def bufW (sy : Syms) (m0 : Machine) : List Watch := (bufI sy).map fun i => (i, 0xFF, m0.ram.get! i)

/-! ## The walk that knows the tiles

At the read of the block buffer routine (`LDA (zp),Y`) the walk does not know the pointer. If the read is in the block buffers and the walk knows every byte of them, the value
read is one of their tiles. So the walk follows one path for each tile (`tstep`). With this it can follow the jumpspring byte and the player's state through a whole frame. -/

/-- the read of the block buffer routine: its place, the tiles it may give, the bytes of the buffers with their values -/
structure Rd where
  pc : UInt16
  tl : List UInt8
  buf : List (Nat × UInt8)

/-- the walk knows every byte of the buffers, with its value -/
def Rd.known (R : Rd) (A : AS) : Bool := R.buf.all (TaintRun.knownIs A)

/-- the step of the walk: at the read, one path for each tile; elsewhere the step of `FrameKeep` -/
def tstep (R : Rd) (S : Spot) (G : Guard) (E : Env) (ops : Array (TaintRun.AM Unit)) (A : AS) : List (Option AS) :=
  if !A.nmi && A.pc == R.pc then
    if decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1 && R.known A then R.tl.map fun T => ScreenPage.readStep E (AB.known T) A
    else [none]
  else FrameKeep.kstep S G E ops A

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end with the watched bits known, the start of the next frame, and `fin` -/
def walkT (R : Rd) (C : CfgK) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (FrameKeep.preK C.S C.G A).all fun A₁ => (tstep R C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkT R C n B
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B

/-! ### Finding its table: a search, no part of the proof -/

/-- what the search forgets: as `FrameKeep.normK`, but in the places `keepAt` it keeps the bytes `temps` too -/
def normT (keepAt : UInt16 → Bool) (temps : List Nat) (S : Spot) (G : Guard) (A0 : AS) : AS :=
  if keepAt A0.pc then FrameKeep.normK { S with entry := A0.pc, store := A0.pc, temps } G A0 else FrameKeep.normK S G A0

/-- the search's step into the table, with the normalization `normT` -/
def routeT (keepAt : UInt16 → Bool) (temps : List Nat) (S : Spot) (G : Guard) (key : AS → Nat) (X : SG) (B0 : AS) : SG :=
  let B := normT keepAt temps S G B0
  let K := key B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if PipeWrites.leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runT (R : Rd) (keepAt : UInt16 → Bool) (temps : List Nat) (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (ops : Array (TaintRun.AM Unit)) (fin : AS → Bool) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (FrameKeep.preK S G cur).flatMap (tstep R S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !(FrameKeep.watchOK W B && fin B)
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && b.pc != R.pc &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeT keepAt temps S G key X b
    break
  return X

partial def searchT (R : Rd) (keepAt : UInt16 → Bool) (temps : List Nat) (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (ops : Array (TaintRun.AM Unit)) (fin : AS → Bool) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      X := runT R keepAt temps S G E W key ops fin X A
  return X

/-- the table, from a search from the start states `st` -/
def cfgOfT (R : Rd) (keepAt : UInt16 → Bool) (temps : List Nat) (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (fin : AS → Bool) (st : List AS) : CfgK :=
  let ops := (TaintRun.aRows E).toArray
  let q := FrameKeep.tableOfKW key (searchT R keepAt temps S G E W key ops fin (st.foldl (routeT keepAt temps S G key) {}))
  { E, ops, S, G, W, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, fin }

/-- **The check**: every state of the table and every start state walks to the frame's end -/
def checkT (R : Rd) (C : CfgK) (st : List AS) : Bool :=
  decide (C.G.late < dotsPerFrame) && C.W.all (fun w => decide (w.1 < 2048)) && C.t.all (walkT R C FrameKeep.fuelK) && st.all (walkT R C FrameKeep.fuelK)

/-! ## The walk of the first frames -/

/-- the player's state and the jumpspring byte, as RAM indices -/
def stI (sy : Syms) : Nat := (sy.Player_State &&& 0x7FF).toNat
def jI (sy : Syms) : Nat := (sy.JumpspringAnimCtrl &&& 0x7FF).toNat

/-- the bytes that a store through an index or a pointer must not write: the player's state, the jumpspring byte, the block buffers -/
def keepI (sy : Syms) : List Nat := stI sy :: jI sy :: bufI sy

/-- the tiles of the buffers of `m0`: each value once -/
def tilesOf (sy : Syms) (m0 : Machine) : List UInt8 :=
  ((List.range 256).filter fun v => (bufI sy).any fun i => m0.ram.get! i == v.toUInt8).map (·.toUInt8)

/-- the read of the block buffer routine, with the tiles and the buffers of `m0` -/
def rdOf (sy : Syms) (m0 : Machine) : Rd :=
  { pc := PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64, tl := tilesOf sy m0, buf := (bufI sy).map fun i => (i, m0.ram.get! i) }

/-- the watched bits: the block buffers with the values of `m0`, and the jumpspring byte 0 -/
def mapW (sy : Syms) (m0 : Machine) : List Watch := bufW sy m0 ++ [(jI sy, 0xFF, 0)]

/-- the guard: that of a frame in control (`guardOf`), with the player's state, the jumpspring byte and the block buffers among the bytes that a store with a target
not known does not touch -/
def guardM (sy : Syms) (m0 : Machine) : Guard := { guardOf sy m0 with prot := keepI sy ++ (guardOf sy m0).prot }

/-- the player's state is known and is 0, 1 or 2 -/
def stOK (sy : Syms) (B : AS) : Bool := (B.getK (stI sy)).isK && decide ((B.getK (stI sy)).v ≤ 2)

/-- the frame's end: the player's state is 0, 1 or 2, or the frame ends out of control (the routine, the task or the mode is known not to be that of control) -/
def finM (sy : Syms) (B : AS) : Bool :=
  stOK sy B || FrameKeep.excl (B.getK (sy.GameEngineSubroutine &&& 0x7FF).toNat) sy.Eng_PlayerCtrl.toUInt8 ||
    FrameKeep.excl (B.getK (sy.OperMode_Task &&& 0x7FF).toNat) sy.Task_GameCore.toUInt8 ||
    FrameKeep.excl (B.getK (sy.OperMode &&& 0x7FF).toNat) sy.GameModeValue.toUInt8

/-- the start states: those of `FrameKeep` with the watched bits and the player's state 0, 1 or 2 -/
def startsM (G : Guard) (W : List Watch) (s : Nat) : List AS :=
  ([0, 1, 2] : List UInt8).flatMap fun v => [false, true].map fun late => FrameKeep.startK G (W ++ [(s, 0xFF, v)]) late

/-- the collision code of the player and the block buffer routine: there the search keeps the temporaries -/
def inColl (sy : Syms) (pc : UInt16) : Bool :=
  (decide (sy.PlayerBGCollision ≤ pc) && decide (pc < sy.HandleEToBGCollision)) ||
    (decide (sy.BlockBufferCollision - 0x20 ≤ pc) && decide (pc < sy.BlockBufferCollision + 0x60))

/-- the temporaries of the collision code -/
def tempsC : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 0xEB]

/-- the table's key: that of the walk with no bit watched, with the player's state, and in the collision code `A` and the temporaries: no part of the proof -/
def keyM (sy : Syms) (G : Guard) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := FrameKeep.keyK StartRun.noSpot G [] A
  let n := n * 65536 + num (A.getK (stI sy))
  if inColl sy A.pc then tempsC.foldl (fun n i => n * 65536 + num (A.getK i)) (n * 65536 + num A.a) else n

/-- the walk's table for the first frames -/
def cfgM (sy : Syms) (m0 : Machine) : CfgK :=
  let G := guardM sy m0
  let W := mapW sy m0
  cfgOfT (rdOf sy m0) (inColl sy) tempsC StartRun.noSpot G (PipeEntryRule.envOf m0) W (keyM sy G) (finM sy) (startsM G W (stI sy))

/-- **The check on the ROM**: the walk of one whole frame with the tiles, from every start state -/
def mapCheck (sy : Syms) (m0 : Machine) : Bool :=
  let R := rdOf sy m0
  let C := cfgM sy m0
  R.buf.all (fun p => R.tl.contains p.2) && checkT R C (startsM C.G C.W (stI sy))

/-! ## The condition on one instruction -/

/-- **What is asked of one instruction**, besides `Clean` of `guardOf`: a store through an index or a pointer does not write the player's state, the jumpspring byte or the
block buffers, and the read of the block buffer routine is in the block buffers -/
structure MapOK (sy : Syms) (m0 : Machine) (m : Machine) : Prop where
  store : ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ keepI sy
  read : m.pc = (rdOf sy m0).pc → ScreenPage.readAddr m < 0x2000 ∧ (ScreenPage.readAddr m &&& 0x7FF).toNat ∈ bufI sy

/-- `MapOK`, for a program -/
def mapOKB (sy : Syms) (m0 : Machine) (m : Machine) : Bool :=
  (match PipeWrites.wTarget (PipeWrites.opAt m) m with
   | some t => !(decide (t < 0x2000) && (keepI sy).contains (t &&& 0x7FF).toNat)
   | none => true) &&
  (m.pc != (rdOf sy m0).pc || (decide (ScreenPage.readAddr m < 0x2000) && (bufI sy).contains (ScreenPage.readAddr m &&& 0x7FF).toNat))

/-! ## The read of `LDA (zp),Y` -/

/-- a piece of a step that keeps the RAM, and the tracking off -/
def KR {α : Type} (f : M α) : Prop := ∀ m : Machine, m.trk = false → (go f m).2.ram = m.ram ∧ (go f m).2.trk = false

theorem kr_bind {α β : Type} {f : M α} {g : α → M β} (hf : KR f) (hg : ∀ a, KR (g a)) : KR (f >>= g) := by
  intro m ht
  rw [go_bind]
  obtain ⟨a1, a2⟩ := hf m ht
  obtain ⟨b1, b2⟩ := hg (go f m).1 _ a2
  exact ⟨b1.trans a1, b2⟩

theorem kr_pure {α : Type} (a : α) : KR (pure a : M α) := fun _ ht => ⟨rfl, ht⟩

theorem kr_get : KR (get : M Machine) := fun _ ht => ⟨rfl, ht⟩

theorem kr_rd (a : UInt16) : KR (rd a) := by
  intro m ht
  by_cases h1 : a < 0x2000
  · rw [TaintRun.rd_ram h1 ht]; exact ⟨rfl, ht⟩
  · by_cases h2 : a ≥ 0x8000
    · rw [TaintRun.rd_rom _ h1 h2]; exact ⟨rfl, ht⟩
    · by_cases h3 : a < 0x4000
      · rw [TaintRun.rd_ppu h1 h2 h3 ht]
        exact ⟨(leaf_ppuRead _).ram m, by rw [(leaf_ppuRead _).trk m]; exact ht⟩
      · by_cases h4 : (a == 0x4016) = true
        · rw [TaintRun.rd_pad h1 h2 h3 h4 ht]
          exact ⟨leaf_padRead.ram m, by rw [leaf_padRead.trk m]; exact ht⟩
        · by_cases h5 : (a == 0x4017) = true
          · rw [TaintRun.rd_17 _ h1 h2 h3 h4 h5]; exact ⟨rfl, ht⟩
          · rw [TaintRun.rd_else _ h1 h2 h3 h4 h5]; exact ⟨rfl, ht⟩

theorem kr_tick (c : Nat) : KR (tick c) := fun m ht => ⟨(leaf_tick c).ram m, by rw [(leaf_tick c).trk m]; exact ht⟩

theorem kr_fetch : KR fetch := by
  intro m ht
  have e : go fetch m = go (rd m.pc) { m with pc := m.pc + 1 } := rfl
  rw [e]
  exact kr_rd m.pc _ ht

theorem kr_rd16zp (z : UInt8) : KR (rd16zp z) := by
  unfold rd16zp
  exact kr_bind (kr_rd _) fun _ => kr_bind (kr_rd _) fun _ => kr_pure _

theorem kr_penalty (b e : UInt16) : KR (pagePenalty b e) := by
  unfold pagePenalty
  split
  · exact kr_tick 1
  · exact kr_pure ()

theorem kr_izyR : KR mIzyR := by
  unfold mIzyR
  exact kr_bind kr_fetch fun _ => kr_bind (kr_rd16zp _) fun _ => kr_bind kr_get fun _ => kr_bind (kr_penalty _ _) fun _ => kr_pure _

/-- **The byte that `LDA (zp),Y` reads**, at an address in the RAM, is the RAM's byte there -/
theorem readVal_ram {m : Machine} (ht : m.trk = false) (h : ScreenPage.readAddr m < 0x2000) :
    ScreenPage.readVal m = m.ram.get! (ScreenPage.readAddr m &&& 0x7FF).toNat := by
  have hk := kr_izyR { m with pc := m.pc + 1 } ht
  unfold ScreenPage.readVal
  unfold ScreenPage.readAddr at h ⊢
  dsimp only
  rw [TaintRun.rd_ram h hk.2, hk.1]

/-- **The read of the block buffer routine is in the buffers** that `R` knows -/
def RdOK (R : Rd) (m : Machine) : Prop :=
  m.pc = R.pc → ScreenPage.readAddr m < 0x2000 ∧ (ScreenPage.readAddr m &&& 0x7FF).toNat ∈ R.buf.map Prod.fst

section
variable {E : Env} {F : Nat × UInt8}

/-- **A step of the machine**, with the steps of this walk -/
theorem s_tstep {R : Rd} {S : Spot} {G : Guard} {A : AS} {m : Machine} {ops : Array (TaintRun.AM Unit)} (hops : ops = (TaintRun.aRows E).toArray)
    (hT : 2 ≤ F.2.toNat) (hc : CleanK G S.store m) (hs : Sim E F A m) (hr : RdOK R m) (hR : R.buf.all (fun p => R.tl.contains p.2) = true) :
    ∃ r ∈ tstep R S G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold tstep
  by_cases h1 : (!A.nmi && A.pc == R.pc) = true
  · rw [if_pos h1]
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
    obtain ⟨hn, hpc⟩ := h1
    by_cases h2 : (decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1 && R.known A) = true
    · rw [if_pos h2]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
      obtain ⟨⟨g1, g2⟩, g3⟩ := h2
      have hm : m.pc = R.pc := by rw [hs.pc]; exact hpc
      obtain ⟨ha, hi⟩ := hr hm
      obtain ⟨p, hp, hp1⟩ := List.mem_map.1 hi
      have hk : TaintRun.knownIs A p = true := List.all_eq_true.1 g3 p hp
      have hv : ScreenPage.readVal m = p.2 := by
        rw [readVal_ram hs.trk ha, ← hp1]
        exact TaintRun.sim_known hs hk
      have ht : p.2 ∈ R.tl := List.mem_of_elem_eq_true (List.all_eq_true.1 hR p hp)
      refine ⟨_, List.mem_map.2 ⟨p.2, ht, rfl⟩, fun B hB => ?_⟩
      exact ScreenPage.s_readStep hs hn g1 g2 (Or.inl ha) (by rw [hv]; exact mem_known_self _) hB
    · rw [if_neg h2]
      exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  · rw [if_neg h1]
    exact FrameKeep.s_kstep hops hT hc hs

end

/-! ## The walk covers the frame -/

section
variable {R : Rd} {C : CfgK} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveT (R : Rd) (C : CfgK) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkT R C n A = true

theorem cover_liveT (ht : C.t.all (walkT R C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : FrameKeep.coverK C B = true) :
    ∃ D, LiveT R C F D m ∧ D.k = B.k := by
  unfold FrameKeep.coverK at h
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
    exact ⟨D, ⟨TaintRun.sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepT (ht : C.t.all (walkT R C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hR : R.buf.all (fun p => R.tl.contains p.2) = true) {A : AS} {m : Machine} (hl : LiveT R C F A m) (hh : CleanK C.G C.S.store m) (hr : RdOK R m) :
    (∃ A', LiveT R C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkT] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    have hr1 : RdOK R m := hr
    obtain ⟨r, hr, hB⟩ := s_tstep hops hT hh hs1 hr1 hR
    simp only [walkT, List.all_eq_true] at hw
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
        · obtain ⟨D, hD, hk⟩ := cover_liveT ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.1.2, hw2.1.2, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S`, for every input, if each instruction meets `CleanK` and `RdOK`. -/
theorem frame_of_walkT (ht : C.t.all (walkT R C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hp : C.E.pad = AB.top) (hR : R.buf.all (fun p => R.tl.contains p.2) = true)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkT R C Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) (hr : ∀ j, RdOK R (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact TaintRun.mem_top _ }
  have key : ∀ j, (∃ A, LiveT R C F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j)) := by
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
        rcases live_stepT ht hkl hops hT hR h1 (hk j) (hr j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a2'', a3, a4⟩
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


/-! ## One frame -/

theorem excl_mem {b : AB} {x : UInt8} (h1 : FrameKeep.excl b x = true) (h2 : b.mem x) : False := by
  unfold FrameKeep.excl at h1
  have e : x &&& b.k = b.v &&& b.k := h2
  simp [e] at h1

theorem le2 {v : UInt8} (h : v ≤ 2) : v = 0 ∨ v = 1 ∨ v = 2 := by
  have h1 := UInt8.le_iff_toNat_le.1 h
  have h2 : (2 : UInt8).toNat = 2 := rfl
  rw [h2] at h1
  have e : v = UInt8.ofNat v.toNat := by simp
  rcases (show v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 by omega) with h | h | h
  · left; rw [e, h]; rfl
  · right; left; rw [e, h]; rfl
  · right; right; rw [e, h]; rfl

/-- **One frame**: from a start in control with the buffers of `m0`, the jumpspring byte 0 and the player's state 0, 1 or 2, the walk covers the frame's end, if each
instruction meets `CleanK` of `guardM` and the read of the block buffer routine is in the buffers. `hc` is the check on the ROM. -/
theorem map_frame {sy : Syms} {m0 : Machine} (hc : mapCheck sy m0 = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardM sy m0) (PipeEntryRule.envOf m0) m) (hw : Watched (mapW sy m0) m) (hst : m.ram.get! (stI sy) ≤ 2)
    (hk : ∀ j, CleanK (guardM sy m0) StartRun.noSpot.store (trace m i j)) (hr : ∀ j, RdOK (rdOf sy m0) (trace m i j)) :
    ∃ B, FrameKeep.watchOK (mapW sy m0) B = true ∧ FrameKeep.endOK (guardM sy m0) B = true ∧ finM sy B = true ∧
      Sim (PipeEntryRule.envOf m0) (m.frame, 2) B (frame m i) := by
  simp only [mapCheck, checkT, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hR, ⟨⟨⟨_, _⟩, ht⟩, hs⟩⟩ := hc
  have hw' : Watched (mapW sy m0 ++ [(stI sy, 0xFF, m.ram.get! (stI sy))]) m := by
    intro w hw2
    rcases List.mem_append.1 hw2 with h | h
    · exact hw w h
    · rw [List.mem_singleton.1 h]
  obtain ⟨b, hsim⟩ := FrameKeep.sim_startK (E := PipeEntryRule.envOf m0) rfl h0 hw'
  have hmem : FrameKeep.startK (guardM sy m0) (mapW sy m0 ++ [(stI sy, 0xFF, m.ram.get! (stI sy))]) b ∈ startsM (guardM sy m0) (mapW sy m0) (stI sy) := by
    unfold startsM
    refine List.mem_flatMap.2 ⟨m.ram.get! (stI sy), ?_, List.mem_map.2 ⟨b, by cases b <;> simp, rfl⟩⟩
    rcases le2 hst with h | h | h <;> simp [h]
  have hwalk := List.all_eq_true.1 hs _ hmem
  obtain ⟨_, B, h1, h2, h3, _, h4⟩ := frame_of_walkT (C := cfgM sy m0) (R := rdOf sy m0) (F := (m.frame, 2)) ht rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) rfl hR hwalk hsim hk hr
  exact ⟨B, h1, h2, h3, h4⟩

/-- **One frame that ends in control** keeps the buffers, the jumpspring byte 0 and the player's state 0, 1 or 2, and ends at the start of a frame -/
theorem map_frame_start {sy : Syms} {m0 : Machine} (hc : mapCheck sy m0 = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardM sy m0) (PipeEntryRule.envOf m0) m) (hw : Watched (mapW sy m0) m) (hst : m.ram.get! (stI sy) ≤ 2)
    (hk : ∀ j, CleanK (guardM sy m0) StartRun.noSpot.store (trace m i j)) (hr : ∀ j, RdOK (rdOf sy m0) (trace m i j))
    (hkn : ∀ p ∈ (guardM sy m0).known, (frame m i).ram.get! p.1 = p.2) :
    FrameStart (guardM sy m0) (PipeEntryRule.envOf m0) (frame m i) ∧ Watched (mapW sy m0) (frame m i) ∧ (frame m i).ram.get! (stI sy) ≤ 2 := by
  obtain ⟨B, h1, h2, h3, h4⟩ := map_frame hc h0 hw hst hk hr
  refine ⟨FrameKeep.start_of_sim h4 h2 rfl rfl hkn, FrameKeep.watched_of h1 h4, ?_⟩
  have k1 := hkn _ (List.Mem.head _)
  have k2 := hkn _ (List.Mem.tail _ (List.Mem.head _))
  have k3 := hkn _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  unfold finM at h3
  simp only [Bool.or_eq_true] at h3
  rcases h3 with ((h | h) | h) | h
  · unfold stOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [PipeEntryRule.known_eq h.1 (h4.ram _ (PipeTransitionAll.mask_lt _))]
    exact h.2
  · exact absurd (excl_mem h (by have := h4.ram _ (PipeTransitionAll.mask_lt sy.GameEngineSubroutine); rwa [k1] at this)) id
  · exact absurd (excl_mem h (by have := h4.ram _ (PipeTransitionAll.mask_lt sy.OperMode_Task); rwa [k3] at this)) id
  · exact absurd (excl_mem h (by have := h4.ram _ (PipeTransitionAll.mask_lt sy.OperMode); rwa [k2] at this)) id

/-- what the three facts say on one machine -/
def MapAt (sy : Syms) (m0 : Machine) (m : Machine) : Prop := Watched (mapW sy m0) m ∧ m.ram.get! (stI sy) ≤ 2

/-- **The frames of a run keep them**: by induction from `seq a`, every machine up to `seq b` starts a frame in control with the buffers of `m0`, the jumpspring byte 0 and
the player's state 0, 1 or 2, if each frame between meets `CleanK` and `RdOK` on each instruction and, when it starts a frame, ends with the known bytes of the guard -/
theorem map_run {sy : Syms} {m0 : Machine} (hc : mapCheck sy m0 = true) {seq : Nat → Machine} {sin : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (sin n))
    {a b : Nat} (h0 : FrameStart (guardM sy m0) (PipeEntryRule.envOf m0) (seq a)) (hm : MapAt sy m0 (seq a))
    (hk : ∀ n, a ≤ n → n < b → ∀ j, CleanK (guardM sy m0) StartRun.noSpot.store (trace (seq n) (sin n) j))
    (hr : ∀ n, a ≤ n → n < b → ∀ j, RdOK (rdOf sy m0) (trace (seq n) (sin n) j))
    (hkn : ∀ n, a ≤ n → n < b → FrameStart (guardM sy m0) (PipeEntryRule.envOf m0) (seq n) → ∀ p ∈ (guardM sy m0).known, (seq (n + 1)).ram.get! p.1 = p.2) :
    ∀ n, a ≤ n → n ≤ b → FrameStart (guardM sy m0) (PipeEntryRule.envOf m0) (seq n) ∧ MapAt sy m0 (seq n) := by
  have key : ∀ d, a + d ≤ b → FrameStart (guardM sy m0) (PipeEntryRule.envOf m0) (seq (a + d)) ∧ MapAt sy m0 (seq (a + d)) := by
    intro d
    induction d with
    | zero => exact fun _ => ⟨h0, hm⟩
    | succ d ih =>
      intro hd
      obtain ⟨s1, w1, t1⟩ := ih (by omega)
      have hkn' := hkn (a + d) (by omega) (by omega) s1
      rw [show a + (d + 1) = a + d + 1 by omega, next (a + d)]
      rw [next (a + d)] at hkn'
      obtain ⟨r1, r2, r3⟩ := map_frame_start hc s1 w1 t1 (hk (a + d) (by omega) (by omega)) (hr (a + d) (by omega) (by omega)) hkn'
      exact ⟨r1, r2, r3⟩
  intro n h1 h2
  have := key (n - a) (by omega)
  rwa [show a + (n - a) = n by omega] at this

/-! ## At control, from the title -/

section
open TitleStart

/-- **The check on the ROM of the state at control**: frame 0 from each near or held state of the set, with any input, ends with control and the speed 0, the player's
state 0, the jumpspring byte 0 and the two buffers known with the values of `m0`, or without control in a state of the set -/
def titleMapCheck (sy : Syms) (c : Ctx) (m0 : Machine) : Bool :=
  frame0Check sy c (fun B => finNear sy B && ((stI sy, 0) :: (jI sy, 0) :: (bufI sy).map fun i => (i, m0.ram.get! i)).all (TaintRun.knownIs B))

/-- **At control** (the machine after frame 0, from the press of Start on the title) the buffers are those of `m0`, the jumpspring byte is 0 and the player's state 0 -/
theorem Begin.map₁ {c : Ctx} {t0 : Nat} {seq : Nat → Machine} {inp : Nat → UInt8} (hB : check sy c t0 = true) (hc : titleMapCheck sy c m0 = true)
    (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) : MapAt sy m0 (seq 1) ∧ (seq 1).ram.get! (stI sy) = 0 := by
  obtain ⟨Bs, hf, hb⟩ := B.frame0 hB hc hn
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  have hk : ∀ p ∈ (stI sy, (0 : UInt8)) :: (jI sy, (0 : UInt8)) :: (bufI sy).map (fun i => (i, m0.ram.get! i)), (seq 1).ram.get! p.1 = p.2 :=
    fun p hp => TaintRun.sim_known hb (hf.2 p hp)
  have e0 : (seq 1).ram.get! (stI sy) = 0 := hk _ (List.Mem.head _)
  refine ⟨⟨?_, by rw [e0]; decide⟩, e0⟩
  intro w hw
  unfold mapW bufW at hw
  rcases List.mem_append.1 hw with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    show (seq 1).ram.get! i &&& 0xFF = m0.ram.get! i &&& 0xFF
    rw [hk (i, m0.ram.get! i) (List.Mem.tail _ (List.Mem.tail _ (List.mem_map.2 ⟨i, hi, rfl⟩)))]
  · rw [List.mem_singleton.1 h]
    show (seq 1).ram.get! (jI sy) &&& 0xFF = 0 &&& 0xFF
    rw [hk _ (List.Mem.tail _ (List.Mem.head _))]

end

/-! ## The frames from control on -/

/-- `Clean` of a guard and the stores of `MapOK` give `CleanK` of the guard with the bytes of `keepI` protected too -/
theorem cleanK_with {sy : Syms} {m0 m : Machine} {G : Guard} (h : Clean G m) (hm : MapOK sy m0 m) :
    CleanK { G with prot := keepI sy ++ G.prot } StartRun.noSpot.store m := by
  refine ⟨fun t ht _ => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, fun hx => ?_⟩
    rcases List.mem_append.1 hx with h3 | h3
    · exact hm.store t ht h1 h3
    · exact h2 h3
  · exact Or.inr h1

/-- `Clean` of `guardOf` and the stores of `MapOK` give `CleanK` of `guardM` -/
theorem cleanK_of {sy : Syms} {m0 m : Machine} (h : Clean (guardOf sy m0) m) (hm : MapOK sy m0 m) : CleanK (guardM sy m0) StartRun.noSpot.store m :=
  cleanK_with h hm

/-- the read of `MapOK` is `RdOK` of `rdOf` -/
theorem rdOK_of {sy : Syms} {m0 m : Machine} (hm : MapOK sy m0 m) : RdOK (rdOf sy m0) m := by
  intro hp
  obtain ⟨h1, h2⟩ := hm.read hp
  refine ⟨h1, ?_⟩
  show _ ∈ ((bufI sy).map fun i => (i, m0.ram.get! i)).map Prod.fst
  rw [List.map_map]
  simpa using h2

/-- the guard of `guardOf` and of `guardM` ask the same at a frame's start -/
theorem start_M {sy : Syms} {m0 m : Machine} {E : Env} (h : FrameStart (guardOf sy m0) E m) : FrameStart (guardM sy m0) E m :=
  StartRun.start_mono h rfl rfl fun _ hp => hp

theorem start_G {sy : Syms} {m0 m : Machine} {E : Env} (h : FrameStart (guardM sy m0) E m) : FrameStart (guardOf sy m0) E m :=
  StartRun.start_mono h rfl rfl fun _ hp => hp

/-- **Every frame from frame 1 up to `b`, counted or not, starts with the buffers of `m0`, the jumpspring byte 0 and the player's state 0, 1 or 2**: `map_run` on the frames
of `Lags`, from frame 1 (`hs₁`, `hm₁`), with `Clean` (`Lags.clean`) and `MapOK` on each instruction before `b`, and the known bytes at each frame's end
(`Lags.known_end`). `hc`, `hk`, `hp`, `hM` are the checks on the ROM. -/
theorem Lags.mapAt {sy : Syms} {m0 : Machine} {g E : Nat} {S : FrameKeep.RealRun} (hc : LagFrames.lagCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true)
    (hM : mapCheck sy m0 = true) (L : PipeFrames.Lags sy m0 g S E)
    (hs₁ : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (hm₁ : MapAt sy m0 (S.seq 1)) {b : Nat} (hb : b ≤ L.ix E)
    (hmap : ∀ n, 1 ≤ n → n < b → ∀ k, MapOK sy m0 (trace (S.seq n) (S.inp n) k)) :
    ∀ n, 1 ≤ n → n ≤ b → MapAt sy m0 (S.seq n) := fun n h1 h2 =>
  (map_run hM S.next (start_M hs₁) hm₁ (fun n a1 a2 j => cleanK_of (L.cleanG n a1 (Nat.lt_of_lt_of_le a2 hb) j) (hmap n a1 a2 j))
    (fun n a1 a2 j => rdOK_of (hmap n a1 a2 j)) (fun _ a1 a2 hs => L.known_end hc hp a1 (Nat.lt_of_lt_of_le a2 hb) (start_G hs)) n h1 h2).2

end Smbrta.OpenMap
