import Theorems.StepPrg
import Theorems.EntryKeep
import Theorems.LagPause
import Theorems.CtrlKeep

/-!
# One condition on each instruction from control to the vertical pipe's entry

Four conditions on the instructions of the frames from control to the entry were fields of `Route.Run`: `chg.upClean₁` (`Clean` of the guard of `EntryKeep`),
`pipe.lags.clean` (`Clean` of `LagPause.guardP`), `pipe.clean` (`Clean` of the guard of `PipeWrites` on the entering frame) and `pipe.opening.cleanK` (`CleanK` of
`FrameKeep.guardE` on the first counted frames). The four guards are the guard of `PipeWrites` with more protected bytes; they have the same idle loop, the same `late`
and the same jump tables. `guardU` protects the bytes of all four lists (`EntryKeep.guardOf`, `LagPause.guardP` with the pause byte of `CtrlKeep.pauseI`, `FrameKeep.guardE`).

The one condition is `CleanK` of `guardU`: `Clean` of it, but the store of the move routine (`FrameKeep.spotOf`) with the index 0 is not asked. That store writes the
player's fraction, which `guardE` protects and the other three guards do not. So `CleanK` of `guardU` gives `CleanK` of each guard (`FrameKeep.cleanK_sub`), and for the
three guards of `Clean` the store of the move routine is `Plain`: on the ROM it is `STA abs,X`, its target with the index 0 is a byte of RAM, none of the three guards
protects it (`qCheck`), and the machine runs the ROM's program (`StepPrg.trace_prg`). This is `at_q`. `qCheck` is a check on the ROM, one of `EntryKeep.Checks`
(round 15); before, the condition was `CleanU`, with an `if` on `qCheck` inside it, because the theorems that use it had no place for the check.

There is no game data in this file. Page: `1-1/a-5-10-UpClean.md`.
-/

namespace Smbrta.UpClean

open PipeWrites (Guard Clean Plain wTarget opAt)
open FrameKeep (CleanK)
open PipeEntryRule (trace)
open PipeTransitionAll (go)

/-! ## The guard and the condition -/

/-- **The union guard**: the guard of `PipeWrites`, with the protected bytes of the guard of `EntryKeep`, of `LagPause.guardP` (the pause byte of `CtrlKeep.pauseI`) and of
`FrameKeep.guardE` -/
def guardU (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Guard :=
  { PipeWrites.guardOf sy m0 with
    prot := (EntryKeep.guardOf sy m0 d e).prot ++ (LagPause.guardP sy m0 (CtrlKeep.pauseI sy m0)).prot ++ (FrameKeep.guardE sy m0).prot }

/- The store of the move routine (`qOf`), the operand of its instruction (`tq`) and the check on the ROM (`qCheck`) are those of `EntryKeep`, which has the check among
its checks (`EntryKeep.Checks.q`). -/
export EntryKeep (qOf tq qCheck)

section
variable {sy : Syms} {m0 : Machine} {d : PipeChangeEnd.Data} {e : Machine} {m : Machine}

/-- `Clean` is `CleanK` with any store set apart -/
theorem cleanK_of_clean {G : Guard} {q : UInt16} (h : Clean G m) : CleanK G q m :=
  ⟨fun t ht _ => h.store t ht, h.read, h.jump, h.time⟩

/-- a guard with the idle loop, `late` and the jump tables of the guard of `PipeWrites` -/
def SameW (sy : Syms) (m0 : Machine) (G : Guard) : Prop :=
  G.idle = (PipeWrites.guardOf sy m0).idle ∧ G.late = (PipeWrites.guardOf sy m0).late ∧ G.je = (PipeWrites.guardOf sy m0).je ∧
    G.jumps = (PipeWrites.guardOf sy m0).jumps

theorem sameW_U : SameW sy m0 (guardU sy m0 d e) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [guardU]

theorem sameW_E : SameW sy m0 (EntryKeep.guardOf sy m0 d e) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [EntryKeep.guardOf]

theorem sameW_P (g : Nat) : SameW sy m0 (LagPause.guardP sy m0 g) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [LagPause.guardP, LagPause.guardWith]

theorem sameW_FE : SameW sy m0 (FrameKeep.guardE sy m0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [FrameKeep.guardE, FrameKeep.guardF, FrameKeep.guardK]

theorem sameW_W : SameW sy m0 (PipeWrites.guardOf sy m0) := ⟨rfl, rfl, rfl, rfl⟩

/-- `CleanK` of a guard gives `CleanK` of a guard with fewer protected bytes, both with the idle loop, `late` and the jump tables of the guard of `PipeWrites` -/
theorem cleanK_sub {G G' : Guard} {q : UInt16} (h : CleanK G q m) (hG : SameW sy m0 G) (hG' : SameW sy m0 G') (hp : ∀ x ∈ G'.prot, x ∈ G.prot) :
    CleanK G' q m :=
  FrameKeep.cleanK_sub h hp (hG'.1.trans hG.1.symm) (hG'.2.1.trans hG.2.1.symm) (hG'.2.2.1.trans hG.2.2.1.symm) (hG'.2.2.2.trans hG.2.2.2.symm)

theorem mem_E {x : Nat} (h : x ∈ (EntryKeep.guardOf sy m0 d e).prot) : x ∈ (guardU sy m0 d e).prot := by
  simp only [guardU, List.mem_append]
  exact Or.inl (Or.inl h)

theorem mem_P {x : Nat} (h : x ∈ (LagPause.guardP sy m0 (CtrlKeep.pauseI sy m0)).prot) : x ∈ (guardU sy m0 d e).prot := by
  simp only [guardU, List.mem_append]
  exact Or.inl (Or.inr h)

theorem mem_FE {x : Nat} (h : x ∈ (FrameKeep.guardE sy m0).prot) : x ∈ (guardU sy m0 d e).prot := by
  simp only [guardU, List.mem_append]
  exact Or.inr h

/-- the bytes of the guard of `PipeWrites` are among those of the guard of `EntryKeep` -/
theorem mem_W_E {x : Nat} (h : x ∈ (PipeWrites.guardOf sy m0).prot) : x ∈ (EntryKeep.guardOf sy m0 d e).prot := by
  simp only [EntryKeep.guardOf, List.mem_append]
  exact Or.inr h

/-- **`CleanK` of `guardE`** (the old field `opening.cleanK`) -/
theorem cleanE_of_U (h : CleanK (guardU sy m0 d e) (qOf sy m0) m) : CleanK (FrameKeep.guardE sy m0) (qOf sy m0) m :=
  cleanK_sub h sameW_U sameW_FE fun _ hx => mem_FE hx

/-! ## The store of the move routine -/

/-- **The target of the store of the move routine with the index 0**: on a machine that runs the ROM's program, at `q` with the index 0, the store goes to `tq` -/
theorem at_q (hc : qCheck sy m0 d e = true) (hp : m.prg = m0.prg) (hm : m.prgMask = m0.prgMask) (hpc : m.pc = qOf sy m0) (hx : m.x = 0) :
    wTarget (opAt m) m = some (tq sy m0) := by
  simp only [qCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩ := hc
  have hop : opAt m = 0x9D := by
    unfold opAt
    rw [hp, hm, hpc]
    exact h1
  have e1 : wTarget 0x9D m = some (go mAbx { m with pc := m.pc + 1 }).1 := by
    unfold wTarget
    simp
  rw [hop, e1]
  have ef : (go mAbx { m with pc := m.pc + 1 }).1 =
      ((go fetch { m with pc := m.pc + 1 }).1.toUInt16 ||| ((go fetch (go fetch { m with pc := m.pc + 1 }).2).1.toUInt16 <<< 8)) +
        (go fetch (go fetch { m with pc := m.pc + 1 }).2).2.x.toUInt16 := rfl
  have f1 : go fetch { m with pc := m.pc + 1 } = (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat, { m with pc := m.pc + 1 + 1 }) := by
    rw [TaintRun.fetch_rom (by rw [hpc]; exact h3)]
  have f2 : go fetch { m with pc := m.pc + 1 + 1 } = (m.prg.get! ((m.pc + 1 + 1) &&& m.prgMask).toNat, { m with pc := m.pc + 1 + 1 + 1 }) := by
    rw [TaintRun.fetch_rom (show m.pc + 1 + 1 ≥ 0x8000 by rw [hpc, UInt16.add_assoc]; exact h4)]
  rw [ef, f1]
  simp only
  rw [f2]
  simp only [hx, hp, hm, hpc, UInt16.add_assoc]
  unfold tq romByte
  simp

/-- **`Plain` for a guard at the store of the move routine**, from the check -/
theorem plainE_q (hc : qCheck sy m0 d e = true) : Plain (EntryKeep.guardOf sy m0 d e).prot (tq sy m0) := by
  simp only [qCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨_, h5⟩, h6⟩, _⟩ := hc
  refine Or.inl ⟨h5, fun hx => ?_⟩
  rw [List.contains_iff_mem.2 hx] at h6
  exact absurd h6 (by decide)

theorem plainP_q (hc : qCheck sy m0 d e = true) : Plain (LagPause.guardP sy m0 (CtrlKeep.pauseI sy m0)).prot (tq sy m0) := by
  have hE := plainE_q hc
  simp only [qCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  have h7 := hc.2
  rcases hE with ⟨h5, h6⟩ | h5
  · refine Or.inl ⟨h5, fun hx => ?_⟩
    simp only [LagPause.guardP, LagPause.guardWith, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact h7 hx
    · exact h6 (mem_W_E hx)
  · exact Or.inr h5

/-- `CleanK` of `guardU` gives `Clean` of a guard with the bytes of `guardU`, if the store of the move routine is `Plain` for it, on a machine that runs the ROM's
program. `hc` is the check on the ROM. -/
theorem clean_of_U {G : Guard} (hc : qCheck sy m0 d e = true) (h : CleanK (guardU sy m0 d e) (qOf sy m0) m) (hG : SameW sy m0 G)
    (hp : ∀ x ∈ G.prot, x ∈ (guardU sy m0 d e).prot) (hq : Plain G.prot (tq sy m0)) (hprg : m.prg = m0.prg) (hmask : m.prgMask = m0.prgMask) : Clean G m := by
  have hk : CleanK G (qOf sy m0) m := cleanK_sub h sameW_U hG hp
  by_cases hqx : m.pc = qOf sy m0 ∧ m.x = 0
  · refine ⟨fun t ht => ?_, hk.read, hk.jump, hk.time⟩
    rw [at_q hc hprg hmask hqx.1 hqx.2] at ht
    cases ht
    exact hq
  · exact FrameKeep.clean_of hk hqx

/-- **`Clean` of the guard of `EntryKeep`** (the old field `upClean₁`) -/
theorem cleanE₁_of_U (hc : qCheck sy m0 d e = true) (h : CleanK (guardU sy m0 d e) (qOf sy m0) m) (hprg : m.prg = m0.prg) (hmask : m.prgMask = m0.prgMask) :
    Clean (EntryKeep.guardOf sy m0 d e) m :=
  clean_of_U hc h sameW_E (fun _ hx => mem_E hx) (plainE_q hc) hprg hmask

/-- **`Clean` of `LagPause.guardP`** with the pause byte `g` that the NMI tests (the old field `pipe.lags.clean`) -/
theorem cleanP_of_U {g : Nat} (hc : qCheck sy m0 d e = true) (hg : CtrlKeep.pauseI sy m0 = g) (h : CleanK (guardU sy m0 d e) (qOf sy m0) m) (hprg : m.prg = m0.prg)
    (hmask : m.prgMask = m0.prgMask) : Clean (LagPause.guardP sy m0 g) m := by
  subst hg
  exact clean_of_U hc h (sameW_P _) (fun _ hx => mem_P hx) (plainP_q hc) hprg hmask

/-- `Clean` of a guard gives `Clean` of a guard with fewer protected bytes, both with the idle loop, `late` and the jump tables of the guard of `PipeWrites` -/
theorem clean_sub {G G' : Guard} (h : Clean G m) (hG : SameW sy m0 G) (hG' : SameW sy m0 G') (hp : ∀ x ∈ G'.prot, x ∈ G.prot) : Clean G' m := by
  have hk := cleanK_sub (q := 0) (cleanK_of_clean h) hG hG' hp
  refine ⟨fun t ht => ?_, hk.read, hk.jump, hk.time⟩
  rcases h.store t ht with ⟨a1, a2⟩ | a1
  · exact Or.inl ⟨a1, fun hx => a2 (hp _ hx)⟩
  · exact Or.inr a1

/-- **`Clean` of the guard of `PipeWrites`** (the old field `pipe.clean`) -/
theorem cleanW_of_U (hc : qCheck sy m0 d e = true) (h : CleanK (guardU sy m0 d e) (qOf sy m0) m) (hprg : m.prg = m0.prg) (hmask : m.prgMask = m0.prgMask) :
    Clean (PipeWrites.guardOf sy m0) m :=
  clean_sub (cleanE₁_of_U hc h hprg hmask) sameW_E sameW_W fun _ hx => mem_W_E hx

end

/-! ## On the frames of a run -/

section
variable {sy : Syms} {m0 : Machine} {d : PipeChangeEnd.Data} {e : Machine}

/-- **Each machine of a frame from frame `a` on runs the ROM's program**, if frame `a` begins with it -/
theorem prg_on {S : FrameKeep.RealRun} {a : Nat} (h : (S.seq a).prg = m0.prg ∧ (S.seq a).prgMask = m0.prgMask) {n : Nat} (hn : a ≤ n) (j : Nat) :
    (trace (S.seq n) (S.inp n) j).prg = m0.prg ∧ (trace (S.seq n) (S.inp n) j).prgMask = m0.prgMask := by
  obtain ⟨k, rfl⟩ : ∃ k, n = a + k := ⟨n - a, by omega⟩
  have h1 := StepPrg.trace_prg (S.seq (a + k)) (S.inp (a + k)) j
  have h2 := StepPrg.run_prg S a k
  exact ⟨h1.1.trans (h2.1.trans h.1), h1.2.trans (h2.2.trans h.2)⟩

/-- the machine of a frame start in control runs the ROM's program -/
theorem prg_of_start {G : Guard} {m : Machine} (h : PipeWrites.FrameStart G (PipeEntryRule.envOf m0) m) : m.prg = m0.prg ∧ m.prgMask = m0.prgMask :=
  ⟨h.prg, h.mask⟩

/-- **`upClean₁` from `CleanK` of `guardU`**: each instruction of the frames from frame 1 to frame `a`, `a` not included, is `Clean` of the guard of `EntryKeep`, when
frame 1 begins with the ROM's program. `hc` is the check on the ROM. -/
theorem upClean₁_of {S : FrameKeep.RealRun} {a : Nat} (hc : qCheck sy m0 d e = true) (h1 : (S.seq 1).prg = m0.prg ∧ (S.seq 1).prgMask = m0.prgMask)
    (hU : ∀ n, 1 ≤ n → n < a → ∀ j, CleanK (guardU sy m0 d e) (qOf sy m0) (trace (S.seq n) (S.inp n) j)) :
    ∀ n, 1 ≤ n → n < a → ∀ j, Clean (EntryKeep.guardOf sy m0 d e) (trace (S.seq n) (S.inp n) j) := fun n a1 a2 j =>
  cleanE₁_of_U hc (hU n a1 a2 j) (prg_on h1 a1 j).1 (prg_on h1 a1 j).2

end

end Smbrta.UpClean
