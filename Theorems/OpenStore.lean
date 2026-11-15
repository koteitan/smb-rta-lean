import Theorems.OpenWalk

/-!
# The opening: a frame in control that ends in control stores neither the routine, nor the mode, nor the task by its address

The frames of the opening asked that no instruction of a counted frame writes the routine, the mode or the task byte by its address (the field `noStore` of
`OpenFrames.RealB`, as `FrameKeep.Frames.noStore` above ground). The walks from the player's routine to the frame's end cut their paths at such an instruction.

Here two walks cover a whole frame that starts in the idle loop in control:

* the first is the walk of `FrameKeep` with the stores cut (`FrameKeep.walkKC`), but at the first instruction that stores to one of the three bytes by its address
  it asks that the second walk succeeds (`walkH`);
* the second goes from that instruction to the frame's end (`walkS`). After a store to one of the three bytes it asks that the routine, the task or the mode is
  known not to be that of control (`OpenFlat.finX`): each such store writes a value that the walk knows. Then it forgets the three bytes. At every other instruction
  it asks that the step does not write the three bytes (`okW`): as far as the abstract state says (`StepWrites.keepOK`), or because the instruction is a store
  through an index or a pointer, which the guard of `CleanK` keeps away from them (`keep_of_cleanK`). So from the first store on the machine is out of control
  (a fact about the machine, outside the abstract states), up to the frame's end.

So (`noStore_of_ctl`): a frame that starts in the idle loop in control and ends in control has no such instruction. A counted frame before the entry ends in control
(`PipeFrames.Lags.ctl`), so the field `noStore` is a theorem (`OpenFrames.Real.noStore`).

The searches are no part of the proof. No game data. Page: `1-1/a-5-4-3-3-5-OpenStore.md`.
-/

namespace Smbrta.OpenStore

open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun (AS Sim Env AB)
open PipeWrites (Guard knownOf SG wTarget opAt)
open FrameKeep (Watch CfgK Spot CleanK)
open PipeEntryRule (trace)

/-! ## The walks -/

/-- the opcodes of a store through an index or a pointer that `PipeWrites.wTarget` knows -/
def wtOps : List UInt8 := [0x95, 0x94, 0xD6, 0xF6, 0x9D, 0xDE, 0xFE, 0x7E, 0x99, 0x91]

/-- **The step of `A` does not write the bytes of `l`**: as far as `A` says (`StepWrites.keepOK`); or it is a store through an index or a pointer of `wtOps`, not the
move routine's own store with the index 0 (then `CleanK` of a guard that protects the bytes of `l` says so) -/
def okW (l : List Nat) (S : Spot) (E : Env) (A : AS) : Bool :=
  StepWrites.keepOK E (fun i => l.contains i) A ||
    (!A.nmi && decide (0x8000 ≤ A.pc) && wtOps.contains (E.prg.get! (A.pc &&& E.mask).toNat) && (A.pc != S.store || FrameKeep.nonZero A.x))

/-- the state with the bytes of `l` forgotten -/
def forgetC (l : List Nat) (A : AS) : AS := l.foldl (fun A i => A.setK i AB.top) A

/-- **The second walk**, from the first store to the frame's end: before each step the pieces of `FrameKeep.preK`; a piece at a store to a byte of `l` by its address
asks `out` of each state after the step; every other piece meets `okW`; the bytes of `l` are forgotten after each step. -/
def walkS (C : CfgK) (l : List Nat) (out : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (FrameKeep.preK C.S C.G A).all fun A₁ =>
    (FrameKeep.storesTo l C.E.prg C.E.mask A₁.pc || okW l C.S C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      (!FrameKeep.storesTo l C.E.prg C.E.mask A₁.pc || out B) &&
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C (forgetC l B)) || walkS C l out n (forgetC l B)
      else B.k == A.k + 1

/-- **The first walk**: `FrameKeep.walkKC`, but at an instruction that stores to a byte of `l` by its address it asks `after`; at the frame's end the instruction is no
such store -/
def walkH (C : CfgK) (l : List Nat) (after : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A =>
    if FrameKeep.storesTo l C.E.prg C.E.mask A.pc then after A else
    (FrameKeep.preK C.S C.G A).all fun A₁ => (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkH C l after n B
      else B.k == A.k + 1 && !FrameKeep.storesTo l C.E.prg C.E.mask B.pc

/-! ## Finding the tables: searches, no part of the proof -/

/-- one path of the search of the second walk -/
partial def runS (l : List Nat) (out : AS → Bool) (S : Spot) (G : Guard) (E : Env) (key : AS → Nat) (ops : Array (TaintRun.AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let ps := FrameKeep.preK S G cur
    let rs := ps.flatMap fun A₁ => (FrameKeep.kstep S G E ops A₁).map fun r => (A₁, r)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := ps.any (fun A₁ => !(FrameKeep.storesTo l E.prg E.mask A₁.pc || okW l S E A₁)) || rs.any fun (A₁, r) =>
      match r with
      | none => true
      | some B => FrameKeep.storesTo l E.prg E.mask A₁.pc && !out B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := ((rs.filterMap (·.2)).filter fun b => b.k == cur.k).map (forgetC l)
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
      X := FrameKeep.routeKW S G key X b
    break
  return X

/-- the search of the second walk: every pending state, until none is left -/
partial def searchS (l : List Nat) (out : AS → Bool) (S : Spot) (G : Guard) (E : Env) (key : AS → Nat) (ops : Array (TaintRun.AM Unit)) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      X := runS l out S G E key ops X A
  return X

/-! ## On the ROM -/

/-- a store to a byte of `l` by its address comes within 8 bytes of `pc`, or a jump or a call there goes to one: where the search keeps the states of different `A`
apart, so that the value that the store writes stays known. No part of the proof. -/
def nearStore (l : List Nat) (E : Env) (pc : UInt16) : Bool :=
  (List.range 8).any fun d =>
    let p := pc + d.toUInt16
    FrameKeep.storesTo l E.prg E.mask p ||
      ((E.prg.get! (p &&& E.mask).toNat == 0x20 || E.prg.get! (p &&& E.mask).toNat == 0x4C) &&
        FrameKeep.storesTo l E.prg E.mask ((E.prg.get! ((p + 1) &&& E.mask).toNat).toUInt16 ||| ((E.prg.get! ((p + 2) &&& E.mask).toNat).toUInt16 <<< 8)))

/-- the table's key: that of `FrameKeep`, with `A` near a store. No part of the proof. -/
def keyS (l : List Nat) (S : Spot) (G : Guard) (E : Env) (A : AS) : Nat :=
  FrameKeep.keyK S G [] A * 65536 + (if nearStore l E A.pc then A.a.k.toNat * 256 + (A.a.v &&& A.a.k).toNat else 0)

/-- the search of the first walk: that of `FrameKeep`, with the stores to the routine, the mode and the task cut -/
def search1 (sy : Syms) (m0 : Machine) : SG :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardF sy m0
  let E := PipeEntryRule.envOf m0
  FrameKeep.searchOfKWC S G E [] (keyS (FrameKeep.ctlI sy) S G E) (FrameKeep.ctlI sy)

/-- the states of the first search at a store to the routine, the mode or the task -/
def stores (sy : Syms) (m0 : Machine) (X : SG) : List AS :=
  let E := PipeEntryRule.envOf m0
  (X.done.toList.map (·.2.1)).filter fun A => FrameKeep.storesTo (FrameKeep.ctlI sy) E.prg E.mask A.pc

/-- the search of the second walk, from the stores of the first -/
def search2 (sy : Syms) (m0 : Machine) (starts : List AS) : SG :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardF sy m0
  let E := PipeEntryRule.envOf m0
  let key := keyS (FrameKeep.ctlI sy) S G E
  searchS (FrameKeep.ctlI sy) (OpenFlat.finX sy) S G E key (TaintRun.aRows E).toArray (starts.foldl (FrameKeep.routeKW S G key) {})

/-- a walk's table from a search -/
def cfgOf (sy : Syms) (m0 : Machine) (X : SG) : CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardF sy m0
  let E := PipeEntryRule.envOf m0
  let key := keyS (FrameKeep.ctlI sy) S G E
  let q := FrameKeep.tableOfKW key X
  { E := E, ops := (TaintRun.aRows E).toArray, S := S, G := G, W := [], t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key := key, fin := fun _ => true }

/-- the check with the two walks `C1`, `C2` -/
def storeCheckWith (sy : Syms) (C1 C2 : CfgK) : Bool :=
  let l := FrameKeep.ctlI sy
  let after := walkS C2 l (OpenFlat.finX sy) FrameKeep.fuelK
  decide (C1.G.late < dotsPerFrame) && C2.t.all after && C1.t.all (walkH C1 l after FrameKeep.fuelK) &&
    walkH C1 l after FrameKeep.fuelK (PipeWrites.startG C1.G false) && walkH C1 l after FrameKeep.fuelK (PipeWrites.startG C1.G true)

/-- **The check on the ROM**: the two walks of a whole frame from its start in control -/
def storeCheck (sy : Syms) (m0 : Machine) : Bool :=
  let X1 := search1 sy m0
  storeCheckWith sy (cfgOf sy m0 X1) (cfgOf sy m0 (search2 sy m0 (stores sy m0 X1)))

/-! ## A store through an index or a pointer keeps a protected byte -/

/-- the store through an index or a pointer of the four opcodes with the zero page indexed by `X`: `wTarget` gives its target, and it is what the step writes -/
theorem wt_zpx {m : Machine} (h : opAt m ∈ [(0x95 : UInt8), 0x94, 0xD6, 0xF6]) :
    wTarget (opAt m) m = some (go mZpx { m with pc := m.pc + 1 }).1 ∧ StepWrites.wOf (opAt m) = StepWrites.wZpx := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩

theorem wt_abx {m : Machine} (h : opAt m ∈ [(0x9D : UInt8), 0xDE, 0xFE, 0x7E]) :
    wTarget (opAt m) m = some (go mAbx { m with pc := m.pc + 1 }).1 ∧ StepWrites.wOf (opAt m) = StepWrites.wAbx := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩

theorem wt_aby {m : Machine} (h : opAt m = 0x99) :
    wTarget (opAt m) m = some (go mAby { m with pc := m.pc + 1 }).1 ∧ StepWrites.wOf (opAt m) = StepWrites.wAby := by
  rw [h]; exact ⟨rfl, rfl⟩

theorem wt_izy {m : Machine} (h : opAt m = 0x91) :
    wTarget (opAt m) m = some (go mIzy { m with pc := m.pc + 1 }).1 ∧ StepWrites.wOf (opAt m) = StepWrites.wIzy := by
  rw [h]; exact ⟨rfl, rfl⟩

/-- **A store through an index or a pointer keeps a protected byte**: one step of the machine at an instruction of `wtOps`, not the move routine's own store with
the index 0, changes no byte that the guard of `CleanK` protects. One step changes RAM only where its instruction stores (`StepWrites.step_ram`), the instruction
stores at the target of `wTarget`, and `CleanK` says that the target is outside the protected bytes, or no RAM. -/
theorem keep_of_cleanK {G : Guard} {q : UInt16} {m : Machine} {i : Nat} (hc : CleanK G q m) (hq : ¬ (m.pc = q ∧ m.x = 0)) (hi : i ∈ G.prot)
    (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hop : opAt m ∈ wtOps) :
    (go step m).2.ram.get! i = m.ram.get! i := by
  apply StepWrites.step_ram
  unfold StepWrites.stepLocs
  rw [if_neg (by simp [hn]), if_neg (by simp [hh]), TaintRun.fetch_rom hp]
  intro hmem
  have key : ∀ t, wTarget (opAt m) m = some t → i ∈ StepWrites.ramIdx t → False := by
    intro t ht hit
    unfold StepWrites.ramIdx at hit
    rcases hc.store t ht hq with ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [if_pos h1, List.mem_singleton] at hit
      exact h2 (hit ▸ hi)
    · have h3 : ¬ t < 0x2000 := by
        intro h4
        have a1 := UInt16.lt_iff_toNat_lt.1 h4
        have a2 := UInt16.le_iff_toNat_le.1 h1
        simp at a1 a2
        omega
      rw [if_neg h3] at hit
      cases hit
  have hop' : m.prg.get! (m.pc &&& m.prgMask).toNat = opAt m := rfl
  simp only [hop'] at hmem
  simp only [wtOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨e1, e2⟩ := wt_zpx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_zpx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_zpx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_zpx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_abx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_abx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_abx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_abx (m := m) (by simp [h]); rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_aby (m := m) h; rw [e2] at hmem; exact key _ e1 hmem
  · obtain ⟨e1, e2⟩ := wt_izy (m := m) h; rw [e2] at hmem; exact key _ e1 hmem


/-! ## The second walk covers the frame from the first store to its end -/

section
variable {C : CfgK} {l : List Nat} {out : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

theorem sim_forgetC {E : Env} (l : List Nat) {A : AS} {m : Machine} (hs : Sim E F A m) : Sim E F (forgetC l A) m := by
  unfold forgetC
  induction l generalizing A with
  | nil => exact hs
  | cons i l ih => exact ih (PipeEntryRule.sim_setK' hs (TaintRun.mem_top _))

theorem forgetC_k (l : List Nat) (A : AS) : (forgetC l A).k = A.k := by
  unfold forgetC
  induction l generalizing A with
  | nil => rfl
  | cons i l ih => exact ih _

/-- **A step that meets `okW` keeps the bytes of `l`**, on a machine that the state covers, if the guard of `CleanK` protects them -/
theorem okW_keep {E : Env} {S : Spot} {G : Guard} {A : AS} {m : Machine} (hs : Sim E F A m) (hc : CleanK G S.store m) (hl : ∀ i ∈ l, i ∈ G.prot)
    (hk : okW l S E A = true) : ∀ i ∈ l, (go step m).2.ram.get! i = m.ram.get! i := by
  intro i hi
  unfold okW at hk
  rcases Bool.or_eq_true_iff.1 hk with h | h
  · exact StepWrites.keep_step hs h i (List.contains_iff_mem.2 hi)
  · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine keep_of_cleanK hc ?_ (hl i hi) (by rw [hs.nmi]; exact h1) hs.halted (by rw [hs.pc]; exact h2) ?_
    · intro ⟨e1, e2⟩
      rcases h4 with h4 | h4
      · exact h4 (hs.pc ▸ e1)
      · exact FrameKeep.ne_of_nonZero h4 hs.x e2
    · show m.prg.get! (m.pc &&& m.prgMask).toNat ∈ wtOps
      rw [hs.prg, hs.mask, hs.pc]
      exact List.contains_iff_mem.1 h3

/-- `A` covers `m`, and a second walk from `A` succeeds -/
def LiveS (C : CfgK) (l : List Nat) (out : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkS C l out n A = true

theorem cover_liveS (ht : C.t.all (walkS C l out Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveS C l out F D m := by
  unfold FrameKeep.coverK at h
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
    exact ⟨D, TaintRun.sim_le hle hs, Fu, hall⟩
  · cases h2

/-- **One step of the second walk.** `P` is a fact about machines that a state after a store gives (`hout`) and that a step keeping the bytes of `l` keeps (`hkeep`).
From a machine at a store, or with `P`: the next machine has `P`, and the walk goes on or the frame ends. -/
theorem live_stepS {P : Machine → Prop} (ht : C.t.all (walkS C l out Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) (hprot : ∀ i ∈ l, i ∈ C.G.prot) (hout : ∀ B x, Sim C.E F B x → out B = true → P x)
    (hkeep : ∀ x x', (∀ i ∈ l, x'.ram.get! i = x.ram.get! i) → P x → P x') {A : AS} {m : Machine} (hl : LiveS C l out F A m) (hh : CleanK C.G C.S.store m)
    (hP : FrameKeep.storesTo l m.prg m.prgMask m.pc = true ∨ P m) :
    P (go step m).2 ∧
      ((∃ A', LiveS C l out F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨ (go step m).2.frame = m.frame + 1) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkS] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkS, List.all_eq_true] at hw
    have hw1 := hw A₁ hA
    rw [Bool.and_eq_true] at hw1
    obtain ⟨hst, hw2⟩ := hw1
    have hw3 := List.all_eq_true.1 hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rw [Bool.and_eq_true] at hw3
      obtain ⟨ho, hw4⟩ := hw3
      have ex : FrameKeep.storesTo l C.E.prg C.E.mask A₁.pc = FrameKeep.storesTo l m.prg m.prgMask m.pc := by rw [hs1.prg, hs1.mask, hs1.pc]
      have hPn : P (go step m).2 := by
        cases hx : FrameKeep.storesTo l C.E.prg C.E.mask A₁.pc with
        | true =>
          rw [hx] at ho
          exact hout B _ h1 (by simpa using ho)
        | false =>
          rw [hx] at hst
          have hk : okW l C.S C.E A₁ = true := by simpa using hst
          rw [ex] at hx
          rcases hP with hP | hP
          · rw [hx] at hP; cases hP
          · exact hkeep _ _ (okW_keep hs1 hh hprot hk) hP
      refine ⟨hPn, ?_⟩
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨_, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw4
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw4
        rcases hw4 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD⟩ := cover_liveS ht hkl (sim_forgetC l h1) h3
          exact ⟨D, hD, k2, k3⟩
        · exact ⟨forgetC l B, ⟨sim_forgetC l h1, n, h3⟩, k2, k3⟩
      · exact Or.inr k2

/-- **The second walk: from the first store to the frame's end.** The machine `k` instructions into the frame of `m`, at a store to a byte of `l` by its address or
with `P`, covered by a state from which the walk succeeds: the frame's end has `P`. -/
theorem endS {P : Machine → Prop} (ht : C.t.all (walkS C l out Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) (hprot : ∀ i ∈ l, i ∈ C.G.prot) (hout : ∀ B x, Sim C.E F B x → out B = true → P x)
    (hkeep : ∀ x x', (∀ i ∈ l, x'.ram.get! i = x.ram.get! i) → P x → P x') {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS}
    (hw : walkS C l out Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, CleanK C.G C.S.store (trace m i j))
    (hP : FrameKeep.storesTo l (trace m i k).prg (trace m i k).prgMask (trace m i k).pc = true ∨ P (trace m i k)) : P (frame m i) := by
  have key : ∀ d, (∃ A, LiveS C l out F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
        (FrameKeep.storesTo l (trace m i (k + d)).prg (trace m i (k + d)).prgMask (trace m i (k + d)).pc = true ∨ P (trace m i (k + d)))) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ P (trace m i (k + d))) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd, hP⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        obtain ⟨hPn, hc⟩ := live_stepS ht hkl hops hT hprot hout hkeep h1 (hcl (k + d)) h4
        rcases hc with ⟨A', a1, a3, a4⟩ | a1
        · exact Or.inl ⟨A', a1, by rw [a3, h2], by omega, Or.inr hPn⟩
        · exact Or.inr ⟨by rw [a1, h2], hPn⟩
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr ⟨h1, h2⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3, _⟩ | ⟨_, h2⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h2
    rw [PipeEntryRule.frame_trace]
    exact h2

end

/-! ## The first walk covers the frame up to the first store -/

section
variable {C : CfgK} {l : List Nat} {after : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a first walk from `A` succeeds -/
def LiveH (C : CfgK) (l : List Nat) (after : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkH C l after n A = true

theorem cover_liveH (ht : C.t.all (walkH C l after Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveH C l after F D m := by
  unfold FrameKeep.coverK at h
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
    exact ⟨D, TaintRun.sim_le hle hs, Fu, hall⟩
  · cases h2

/-- at a store, the first walk asks `after` -/
theorem after_of_liveH {A : AS} {m : Machine} (hl : LiveH C l after F A m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = true) : after A = true := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkH] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = true := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    simp only [walkH, hx', if_true] at hw
    exact hw

/-- **One step of the first walk**, from a machine that is at no store: the walk goes on, or the frame ends at an instruction that is no store -/
theorem live_stepH (ht : C.t.all (walkH C l after Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveH C l after F A m) (hh : CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveH C l after F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ FrameKeep.storesTo l (go step m).2.prg (go step m).2.prgMask (go step m).2.pc = false) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkH] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkH, hx', Bool.false_eq_true, if_false, List.all_eq_true] at hw
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
        · obtain ⟨D, hD⟩ := cover_liveH ht hkl h1 h3
          exact ⟨D, hD, k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw2
        refine ⟨k2, ?_⟩
        rw [h1.prg, h1.mask, h1.pc]
        exact hw2.2

/-- **The first walk: the frame up to its first store.** A walk from `S` that succeeds covers the frame of every machine of `S`: no instruction of the frame stores to
a byte of `l` by its address, or the frame comes to a first such instruction, in a state where `after` holds. -/
theorem runH (ht : C.t.all (walkH C l after Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hp : C.E.pad = AB.top) {S : AS} {m : Machine} {i : UInt8} (hw : walkH C l after Fu S = true) (hs : Sim C.E F S m)
    (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) :
    (∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) ∨
    ∃ j A, (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot ∧
      FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = true ∧ Sim C.E F A (trace m i j) ∧ after A = true := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact TaintRun.mem_top _ }
  have key : ∀ j, (∃ A, LiveH C l after F A (trace m i j) ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot ∧
        ∀ j', j' < j → FrameKeep.storesTo l (trace m i j').prg (trace m i j').prgMask (trace m i j').pc = false) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∀ j', j' ≤ j → FrameKeep.storesTo l (trace m i j').prg (trace m i j').prgMask (trace m i j').pc = false) ∨
      (∃ j₁ A, (trace m i j₁).frame = m.frame ∧ m.fdot + 3 * j₁ ≤ (trace m i j₁).fdot ∧
        FrameKeep.storesTo l (trace m i j₁).prg (trace m i j₁).prgMask (trace m i j₁).pc = true ∧ Sim C.E F A (trace m i j₁) ∧ after A = true) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl, Nat.le_refl _, fun j' h => absurd h (by omega)⟩
    | succ j ih =>
      have e : trace m i (j + 1) = PipeEntryRule.nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h3, h4, h5⟩ | ⟨h1, h2⟩ | h
      · cases hx : FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc with
        | true => exact Or.inr (Or.inr ⟨j, A, h3, h4, hx, h1.1, after_of_liveH h1 hx⟩)
        | false =>
          have hh := h1.1.halted
          have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by simp [h3, hh]
          have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
            rw [e]
            simp only [PipeEntryRule.nxt, if_neg hc]
          have hall : ∀ j', j' < j + 1 → FrameKeep.storesTo l (trace m i j').prg (trace m i j').prgMask (trace m i j').pc = false := by
            intro j' hj
            by_cases hjj : j' < j
            · exact h5 j' hjj
            · rw [show j' = j by omega]; exact hx
          rcases live_stepH ht hkl hops hT h1 (hk j) hx with ⟨A', a1, a3, a4⟩ | ⟨a1, a2⟩
          · rw [← e2] at a1 a3 a4
            exact Or.inl ⟨A', a1, by rw [a3, h3], by omega, hall⟩
          · rw [← e2] at a1 a2
            refine Or.inr (Or.inl ⟨by rw [a1, h3], fun j' hj => ?_⟩)
            by_cases hjj : j' < j + 1
            · exact hall j' hjj
            · rw [show j' = j + 1 by omega]; exact a2
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [PipeEntryRule.nxt, if_pos hc]
        refine Or.inr (Or.inl ⟨by rw [e2]; exact h1, fun j' hj => ?_⟩)
        by_cases hjj : j' ≤ j
        · exact h2 j' hjj
        · rw [show j' = j + 1 by omega, e2]; exact h2 j (Nat.le_refl j)
      · exact Or.inr (Or.inr h)
  by_cases hex : ∃ j A, (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot ∧
      FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = true ∧ Sim C.E F A (trace m i j) ∧ after A = true
  · exact Or.inr hex
  · refine Or.inl fun j => ?_
    rcases key (j + fuelPerFrame) with ⟨A, h1, _, h4, _⟩ | ⟨_, h2⟩ | h
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact h2 j (by omega)
    · exact absurd h hex

end

/-! ## On the ROM: one frame -/

section
variable {sy : Syms} {m0 : Machine}

/-- a state that is out of control covers no machine in control -/
theorem out_of_finX {E : Env} {F : Nat × UInt8} {B : AS} {x : Machine} (hs : Sim E F B x) (h : OpenFlat.finX sy B = true) : controllable sy x = false := by
  cases hc : controllable sy x with
  | false => rfl
  | true =>
    exfalso
    have hk := FrameKeep.known_of_ctl (m0 := x) hc
    have k1 : x.ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat = sy.Eng_PlayerCtrl.toUInt8 := hk (_, _) (List.Mem.head _)
    have k2 : x.ram.get! (sy.OperMode &&& 0x7FF).toNat = sy.GameModeValue.toUInt8 := hk (_, _) (List.Mem.tail _ (List.Mem.head _))
    have k3 : x.ram.get! (sy.OperMode_Task &&& 0x7FF).toNat = sy.Task_GameCore.toUInt8 := hk (_, _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    unfold OpenFlat.finX at h
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact OpenMap.excl_mem h (by have := hs.ram _ (PipeTransitionAll.mask_lt sy.GameEngineSubroutine); rwa [k1] at this)
    · exact OpenMap.excl_mem h (by have := hs.ram _ (PipeTransitionAll.mask_lt sy.OperMode_Task); rwa [k3] at this)
    · exact OpenMap.excl_mem h (by have := hs.ram _ (PipeTransitionAll.mask_lt sy.OperMode); rwa [k2] at this)

/-- a machine with the routine, the mode and the task of another is in control when the other is -/
theorem ctl_congr {x x' : Machine} (h : ∀ i ∈ FrameKeep.ctlI sy, x'.ram.get! i = x.ram.get! i) : controllable sy x' = controllable sy x := by
  have e1 : peek x' sy.OperMode = peek x sy.OperMode := h _ (by simp [FrameKeep.ctlI])
  have e2 : peek x' sy.OperMode_Task = peek x sy.OperMode_Task := h _ (by simp [FrameKeep.ctlI])
  have e3 : peek x' sy.GameEngineSubroutine = peek x sy.GameEngineSubroutine := h _ (by simp [FrameKeep.ctlI])
  unfold controllable
  rw [e1, e2, e3]

/-- what the check says -/
structure StoreOK (sy : Syms) (C1 C2 : CfgK) : Prop where
  late : C1.G.late < dotsPerFrame
  t2 : C2.t.all (walkS C2 (FrameKeep.ctlI sy) (OpenFlat.finX sy) FrameKeep.fuelK) = true
  t1 : C1.t.all (walkH C1 (FrameKeep.ctlI sy) (walkS C2 (FrameKeep.ctlI sy) (OpenFlat.finX sy) FrameKeep.fuelK) FrameKeep.fuelK) = true
  s0 : walkH C1 (FrameKeep.ctlI sy) (walkS C2 (FrameKeep.ctlI sy) (OpenFlat.finX sy) FrameKeep.fuelK) FrameKeep.fuelK (PipeWrites.startG C1.G false) = true
  s1 : walkH C1 (FrameKeep.ctlI sy) (walkS C2 (FrameKeep.ctlI sy) (OpenFlat.finX sy) FrameKeep.fuelK) FrameKeep.fuelK (PipeWrites.startG C1.G true) = true

theorem storeOK_of {C1 C2 : CfgK} (h : storeCheckWith sy C1 C2 = true) : StoreOK sy C1 C2 := by
  simp only [storeCheckWith, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- the guard of the walks protects the routine, the mode and the task -/
theorem ctlI_prot : ∀ x ∈ FrameKeep.ctlI sy, x ∈ (FrameKeep.guardF sy m0).prot := by
  intro x hx
  simp only [FrameKeep.ctlI, List.mem_cons, List.not_mem_nil, or_false] at hx
  refine List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
  show x ∈ (PipeWrites.guardOf sy m0).prot
  simp only [PipeWrites.guardOf, List.mem_cons]
  rcases hx with rfl | rfl | rfl <;> simp

/-- **A frame in control that ends in control stores neither the routine, nor the mode, nor the task by its address**, with the two walks `C1`, `C2` on the machine of
`m0` and the guard `FrameKeep.guardF` -/
theorem noStore_of_ok {C1 C2 : CfgK} (H : StoreOK sy C1 C2) (hE1 : C1.E = PipeEntryRule.envOf m0) (hE2 : C2.E = PipeEntryRule.envOf m0)
    (hG1 : C1.G = FrameKeep.guardF sy m0) (hG2 : C2.G = FrameKeep.guardF sy m0) (hS1 : C1.S = FrameKeep.spotOf sy m0) (hS2 : C2.S = FrameKeep.spotOf sy m0)
    (hk1 : C1.kl = C1.t.map knownOf) (hk2 : C2.kl = C2.t.map knownOf) (ho1 : C1.ops = (TaintRun.aRows C1.E).toArray) (ho2 : C2.ops = (TaintRun.aRows C2.E).toArray)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hctl : controllable sy (frame m i) = true) :
    ∀ n, FrameKeep.CtlStore sy (trace m i n) = false := by
  have hF : PipeWrites.FrameStart C1.G C1.E m := by
    rw [hG1, hE1]
    exact StartRun.start_mono h0 rfl rfl (fun _ hp => hp)
  obtain ⟨b, hs⟩ := PipeWrites.sim_startG (by rw [hE1]; rfl) hF
  have hw0 : walkH C1 (FrameKeep.ctlI sy) (walkS C2 (FrameKeep.ctlI sy) (OpenFlat.finX sy) FrameKeep.fuelK) FrameKeep.fuelK (PipeWrites.startG C1.G b) = true := by
    cases b with
    | false => exact H.s0
    | true => exact H.s1
  have hcl1 : ∀ j, CleanK C1.G C1.S.store (trace m i j) := by rw [hG1, hS1]; exact hcl
  have hcl2 : ∀ j, CleanK C2.G C2.S.store (trace m i j) := by rw [hG2, hS2]; exact hcl
  rcases runH (F := (m.frame, 2)) H.t1 hk1 ho1 (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [hE1]; rfl) hw0 hs hcl1 with h | ⟨j, A, hf, hd, hx, hsA, haf⟩
  · exact h
  · exfalso
    have hsA2 : Sim C2.E (m.frame, 2) A (trace m i j) := by rw [hE2, ← hE1]; exact hsA
    have hend : controllable sy (frame m i) = false :=
      endS (F := (m.frame, 2)) (P := fun x => controllable sy x = false) H.t2 hk2 ho2 (show 2 ≤ (2 : UInt8).toNat by decide)
        (by rw [hG2]; exact ctlI_prot) (fun B x hsB ho => out_of_finX hsB ho) (fun x x' hb hx => (ctl_congr hb).trans hx) haf hsA2 hf hd hcl2 (Or.inl hx)
    rw [hctl] at hend
    cases hend

/-- **A frame in control that ends in control stores neither the routine, nor the mode, nor the task by its address.** The frame starts in the idle loop in
control (`FrameKeep.StartK`) and each instruction meets `CleanK` of `FrameKeep.guardF`. If its end is in control (`controllable`), no instruction of it writes one of
the three bytes by its address. `hk` is the check on the ROM. -/
theorem noStore_of_ctl (hk : storeCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hctl : controllable sy (frame m i) = true) :
    ∀ n, FrameKeep.CtlStore sy (trace m i n) = false :=
  noStore_of_ok (storeOK_of hk) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h0 hcl hctl

end


end Smbrta.OpenStore
