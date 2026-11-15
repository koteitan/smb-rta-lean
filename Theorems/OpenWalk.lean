import Theorems.OpenFlat
import Theorems.StepWrites

/-!
# A walk of a frame with phases

The walk of `OpenFlat` (the steps of `FrameKeep`, and at the read of the block buffer routine the tiles of the first block buffer) with two hooks, as the walks of
`RoomVert` (`RoomVert.Ph`): before each step a state is split into pieces (`PhK.zone`), and each piece is checked (`PhK.ok`). The list `AS.log` of a state carries a
phase: the steps keep it (the walk checks this), and only the pieces change it. A fact `Φ` outside the abstract states, on the machine after `j` instructions and the
phase of the state that covers it, holds along the whole frame if each piece keeps it (`frame_of_walkP`). The walk runs to the frame's end.

There is no game data in this file. Page: `1-1/a-5-7-2-OpenAir.md`.
-/

namespace Smbrta.OpenWalk

open PipeTransition (frame)
open TaintRun (AS Sim Env AB)
open PipeWrites (Guard knownOf leK SG)
open FrameKeep (Watch CfgK Spot CleanK)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open OpenFlat (Rd1 preF fstep RdOK1)

/-! ## The walk -/

/-- a walk's phases: the pieces of a state before a step, and what each piece must meet -/
structure PhK where
  zone : AS → List AS
  ok : AS → Bool

/-- the table has a state that covers `B`, with the same phase -/
def coverP (C : CfgK) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l && B.log == D.log
    | _, _ => false

/-- **The walk**: from `A`, step by step, until every path ends in a state of the table (with the same phase), or at the frame's end with the watched bits known, the
start of the next frame and `fin`. Before each step the state is split by `OpenFlat.preF`, then by `zone`; each piece meets `ok`; the steps keep the phase. -/
def walkP (R : Rd1) (Z : PhK) (C : CfgK) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preF R C.S C.G A).all fun A₁ => A₁.log == A.log && A₁.k == A.k && (Z.zone A₁).all fun A₂ =>
    Z.ok A₂ && A₂.k == A₁.k && (fstep R C.S C.G C.E C.ops A₂).all fun r =>
    match r with
    | none => false
    | some B =>
      B.log == A₂.log &&
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverP C B) || walkP R Z C n B
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B

/-! ## Finding its table: a search, no part of the proof -/

/-- the search's step into the table: `OpenFlat.routeF` (the bytes `extra` kept), with the phase in the key -/
def routeP (keepAt : UInt16 → Bool) (temps extra : List Nat) (S : Spot) (G : Guard) (key : AS → Nat) (X : SG) (B0 : AS) : SG :=
  OpenFlat.routeF keepAt temps extra S G key X B0

/-- one path of the search, as `OpenFlat.runQ` with the pieces of `zone` and the checks of `ok` -/
partial def runP (R : Rd1) (Z : PhK) (route : SG → AS → SG) (S : Spot) (G : Guard) (E : Env) (W : List Watch)
    (ops : Array (TaintRun.AM Unit)) (fin : AS → Bool) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let ps := (preF R S G cur).flatMap Z.zone
    let rs := (ps.filter Z.ok).flatMap fun A => (fstep R S G E ops A).map fun r => r.map fun B => (A, B)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := ps.any (fun A => !Z.ok A) || rs.any fun r => match r with
      | none => true
      | some (A, B) => B.log != A.log || (B.k != cur.k && !(FrameKeep.watchOK W B && FrameKeep.endOK G B && fin B))
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := ((rs.filterMap id).map (·.2)).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && b.pc != R.pc && b.pc != R.adc && b.log == cur.log &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := route X b
    break
  return X

/-- the search: every pending state, until none is left -/
partial def searchP (R : Rd1) (Z : PhK) (route : SG → AS → SG) (S : Spot) (G : Guard) (E : Env) (W : List Watch)
    (ops : Array (TaintRun.AM Unit)) (fin : AS → Bool) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      X := runP R Z route S G E W ops fin X A
  return X

/-! ## The walk covers the frame -/

section
variable {R : Rd1} {Z : PhK} {C : CfgK} {Fu : Nat} {F : Nat × UInt8}

/-- a state of the walk that covers the machine -/
def LiveP (R : Rd1) (Z : PhK) (C : CfgK) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkP R Z C n A = true

theorem cover_liveP (ht : C.t.all (walkP R Z C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : coverP C B = true) : ∃ D, LiveP R Z C F D m ∧ D.k = B.k ∧ D.log = B.log := by
  unfold coverP at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    have hle := PipeWrites.leK_le h2.1
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    have hsD := TaintRun.sim_le hle hs
    exact ⟨D, ⟨hsD, Fu, hall⟩, (PipeWrites.le_k hle).symm, h2.2.symm⟩
  · cases h2

/-- **One step of the walk**: a live state `A` covering `m` has a piece of `preF` covering `m` with the same phase; for every piece of `zone` of it that covers `m`, the
piece meets `ok`, and the step goes on in a live state with the piece's phase, or ends the frame in a state with the watched bits, the start of a frame, `fin` and the
piece's phase -/
theorem live_stepP (ht : C.t.all (walkP R Z C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveP R Z C F A m) (hh : CleanK C.G C.S.store m) (hr : RdOK1 R m) :
    ∃ A₁ ∈ preF R C.S C.G A, Sim C.E F A₁ m ∧ A₁.log = A.log ∧
      ∀ A₂ ∈ Z.zone A₁, Sim C.E F A₂ m → Z.ok A₂ = true ∧
        ((∃ A', LiveP R Z C F A' (go step m).2 ∧ A'.k = A.k ∧ A'.log = A₂.log ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
         ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.log = A₂.log ∧
           Sim C.E F B (go step m).2)) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkP] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := OpenFlat.cov_preF R hh hs
    simp only [walkP, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨hlog1, _⟩, hz⟩ := hw A₁ hA
    refine ⟨A₁, hA, hs1, hlog1, fun A₂ hA₂ hs2 => ?_⟩
    obtain ⟨⟨hok, hk2⟩, hr2⟩ := hz A₂ hA₂
    refine ⟨hok, ?_⟩
    obtain ⟨r, hrm, hB⟩ := OpenFlat.s_fstep hops hT hh hs2 hr
    have hw2 := hr2 r hrm
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      simp only [Bool.and_eq_true, beq_iff_eq] at hw2
      obtain ⟨hlogB, hw3⟩ := hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · rw [hk2, hk1] at k1
        rw [if_pos (by simp [k1])] at hw3
        left
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
        rcases hw3 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk, hlD⟩ := cover_liveP ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], by rw [hlD, hlogB], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, hlogB, k2, k3⟩
      · right
        rw [hk2, hk1] at k1
        rw [if_neg (by simp [k1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact ⟨k2, B, hw3.1.1.2, hw3.1.2, hw3.2, hlogB, h1⟩

/-- **One frame, with a fact `Φ` outside the abstract states.** `Φ j l` speaks of the machine after `j` instructions and the phase `l` of the state that covers it.
The walk starts after the instruction `n₀`, in a state that covers the machine there, with `Φ`. Before each step a piece of `zone` covers the machine, with a fact `Ψ`
that the caller chooses (`hz`); if each such piece that meets `ok` keeps `Φ` (`hstep`), `Φ` holds at every instruction of the frame from `n₀` on and at the frame's
end. Each instruction meets `CleanK` of the guard and `RdOK1`. -/
theorem frame_of_walkP (Φ : Nat → List Nat → Prop) (Ψ : Nat → AS → Prop) (ht : C.t.all (walkP R Z C Fu) = true) (hkl : C.kl = C.t.map knownOf)
    (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {S : AS} {m : Machine} {i : UInt8} {n₀ : Nat} {Fu' : Nat}
    (hw : walkP R Z C Fu' S = true) (hs : Sim C.E F S (trace m i n₀)) (hf : (trace m i n₀).frame = m.frame) (hd : m.fdot + 3 * n₀ ≤ (trace m i n₀).fdot)
    (hcl : ∀ j, CleanK C.G C.S.store (trace m i j)) (hr : ∀ j, (trace m i j).frame = m.frame → RdOK1 R (trace m i j))
    (h0 : Φ n₀ S.log)
    (hz : ∀ j (A₁ : AS), n₀ ≤ j → Φ j A₁.log → Sim C.E F A₁ (trace m i j) → (trace m i j).frame = m.frame →
      ∃ A₂ ∈ Z.zone A₁, Sim C.E F A₂ (trace m i j) ∧ Ψ j A₂)
    (hstep : ∀ j (A₁ A₂ : AS), n₀ ≤ j → Φ j A₁.log → Sim C.E F A₁ (trace m i j) → (trace m i j).frame = m.frame → A₂ ∈ Z.zone A₁ →
      Sim C.E F A₂ (trace m i j) → Ψ j A₂ → Z.ok A₂ = true → Φ (j + 1) A₂.log) :
    (∀ j, n₀ ≤ j → (trace m i j).frame = m.frame → ∃ A, Sim C.E F A (trace m i j) ∧ Φ j A.log) ∧
    ∃ J, n₀ ≤ J ∧ (trace m i J).frame = m.frame + 1 ∧ (∀ j, n₀ ≤ j → j < J → (trace m i j).frame = m.frame) ∧ frame m i = trace m i J ∧
      ∃ B, C.fin B = true ∧ Sim C.E F B (trace m i J) ∧ Φ J B.log := by
  have key : ∀ d, (∃ A, LiveP R Z C F A (trace m i (n₀ + d)) ∧ (∀ j, n₀ ≤ j → j ≤ n₀ + d → (trace m i j).frame = m.frame) ∧
        m.fdot + 3 * (n₀ + d) ≤ (trace m i (n₀ + d)).fdot ∧ Φ (n₀ + d) A.log) ∨
      (∃ J, n₀ ≤ J ∧ J ≤ n₀ + d ∧ (trace m i J).frame = m.frame + 1 ∧ (∀ j, n₀ ≤ j → j < J → (trace m i j).frame = m.frame) ∧
        trace m i (n₀ + d) = trace m i J ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (trace m i J) ∧ Φ J B.log) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨S, ⟨hs, Fu', hw⟩, fun j h1 h2 => by rw [show j = n₀ by omega]; exact hf, by omega, h0⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h4, h5⟩ | ⟨J, h1, h2, h3, h4, h6, B, h7⟩
      · have h3 := h2 (n₀ + d) (by omega) (Nat.le_refl _)
        have hh := h1.1.halted
        have hc : ¬ (((trace m i (n₀ + d)).frame ≥ m.frame + 1 || (trace m i (n₀ + d)).halted) = true) := by simp [h3, hh]
        have e2 : trace m i (n₀ + (d + 1)) = (go step (trace m i (n₀ + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (n₀ + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hc]
        obtain ⟨A₁, _, hs1, hl1, hall⟩ := live_stepP ht hkl hops hT h1 (hcl (n₀ + d)) (hr (n₀ + d) h3)
        have hΦ1 : Φ (n₀ + d) A₁.log := by rw [hl1]; exact h5
        obtain ⟨A₂, hA₂, hs2, hψ⟩ := hz (n₀ + d) A₁ (by omega) hΦ1 hs1 h3
        obtain ⟨hok, hnext⟩ := hall A₂ hA₂ hs2
        have hΦ2 := hstep (n₀ + d) A₁ A₂ (by omega) hΦ1 hs1 h3 hA₂ hs2 hψ hok
        rw [show n₀ + d + 1 = n₀ + (d + 1) by omega] at hΦ2
        rcases hnext with ⟨A', a1, _, a3, a4, a5⟩ | ⟨a1, B, _, _, b3, b4, b5⟩
        · rw [← e2] at a1 a4 a5
          refine Or.inl ⟨A', a1, fun j j1 j2 => ?_, by omega, by rw [a3]; exact hΦ2⟩
          rcases Nat.lt_or_ge j (n₀ + (d + 1)) with hlt | hge
          · exact h2 j j1 (by omega)
          · rw [show j = n₀ + (d + 1) by omega, a4, h3]
        · rw [← e2] at a1 b5
          refine Or.inr ⟨n₀ + (d + 1), by omega, Nat.le_refl _, by rw [a1, h3], fun j j1 j2 => h2 j j1 (by omega), rfl, B, b3, b5, ?_⟩
          rw [b4]; exact hΦ2
      · have hc : ((trace m i (n₀ + d)).frame ≥ m.frame + 1 || (trace m i (n₀ + d)).halted) = true := by
          rw [h6]
          simp [h3]
        have e2 : trace m i (n₀ + (d + 1)) = trace m i (n₀ + d) := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (n₀ + d)) = _
          simp only [PipeEntryRule.nxt, if_pos hc]
        exact Or.inr ⟨J, h1, by omega, h3, h4, by rw [e2, h6], B, h7⟩
  refine ⟨fun j j1 hj => ?_, ?_⟩
  · rcases key (j - n₀) with ⟨A, h1, _, _, h5⟩ | ⟨J, _, h2, h3, _, h6, _⟩
    · rw [show n₀ + (j - n₀) = j by omega] at h1 h5
      exact ⟨A, h1.1, h5⟩
    · rw [show n₀ + (j - n₀) = j by omega] at h6
      rw [h6, h3] at hj
      omega
  · have a1 := hs.hi
    have a2 := hs.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    rcases key (fuelPerFrame - n₀) with ⟨A, h1, _, h4, _⟩ | ⟨J, j1, _, h2, h3, h4, B, h5⟩
    · exfalso
      rw [show n₀ + (fuelPerFrame - n₀) = fuelPerFrame by omega] at h1 h4
      have b1 := h1.1.hi
      have b2 := h1.1.lim
      omega
    · rw [show n₀ + (fuelPerFrame - n₀) = fuelPerFrame by omega] at h4
      exact ⟨J, j1, h2, h3, by rw [PipeEntryRule.frame_trace, h4], B, h5⟩

end

end Smbrta.OpenWalk
