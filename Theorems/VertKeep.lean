import Theorems.GuardE

/-!
# Above ground: four vertical bytes after the scroll handler

A frame in control comes to the player's routine (the cut of `CtrlKeep`), and from there to the scroll handler (`PlayerSubs`), as in `AfterKeep`. From the scroll
handler to the frame's end, no step writes four of the bytes that the vertical step (`Jump.vstep`) reads: the vertical force down, the jump's origin, the jump's halt
value, A and B (`kI`). The second walk of `AfterKeep` follows each of them, one at a time, as the counter of `TaintRun` (`Env.rkI`): it fails on any write to the
byte, and asks at the frame's end that the byte is still followed. Its guard protects the byte (`AfterKeep.guardH`). `FrameKeep.guardE` protects all four (A and B in
`FrameKeep.spareE`, the other three in `FrameKeep.vertE`), so `CleanK` of `guardE` gives `CleanK` of the walk's guard (`cleanK_of_kI`).

So (`keep_end`): at the frame's end the four bytes are those at the scroll handler. This was a part of the field `vAfter` of the frames above ground
(`PoleJoin.SurfaceFrames.OnFrames`).

The other bytes of `vAfter` stay assumed: the height, its fraction, the vertical speed, the fraction counter, the vertical force and the player's state. The collision
routine writes the state on every frame that starts on the ground and lands him again; the enemies' code, the platforms, the jumpspring and the blocks write them too,
and the walk knows neither the map nor the objects (`vert-after-bytes`).

No game data. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.VertKeep

open TaintRun
open PipeEntryRule (trace)
open PipeTransition (frame)
open AfterKeep (walkQ1 walkKR q1Search q1Cfg q2Cfg atQ rkOn sim_rkOn endKR q1_run guardH cfgPH)

/-- **The four vertical bytes that a frame keeps after the scroll handler**: the vertical force down, the jump's origin, the jump's halt value, A and B -/
def kI (sy : Syms) : List Nat :=
  [(sy.VerticalForceDown &&& 0x7FF).toNat, (sy.JumpOrigin_Y_Position &&& 0x7FF).toNat, (sy.DiffToHaltJump &&& 0x7FF).toNat, (sy.A_B_Buttons &&& 0x7FF).toNat]

/-- **The check**: the walk of the pause bit up to the cut; from there the first walk of `AfterKeep` to the scroll handler; from there, for each byte of `kI`, the second
walk of `AfterKeep` to the frame's end (`AfterKeep.hCheck` with the bytes of `kI`) -/
def kCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := q1Search sy m0 v cuts
  let C1 := q1Cfg sy m0 v P
  let C2 := (kI sy).map fun b => q2Cfg sy m0 b P.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (cfgPH sy m0 v q C1 C2) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQ sy C2) FrameKeep.fuelK) &&
    C2.all fun C => C.t.all (walkKR C (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK)

section
variable {sy : Syms} {m0 : Machine}

/-- the bytes of `kI` are protected by `FrameKeep.guardE`: A and B in `FrameKeep.spareE`, the other three in `FrameKeep.vertE` -/
theorem kI_mem {x : Nat} (hx : x ∈ kI sy) : x ∈ (FrameKeep.guardE sy m0).prot := by
  simp only [kI, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [FrameKeep.guardE, FrameKeep.spareE, FrameKeep.vertE, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- **`CleanK` of `guardE` gives `CleanK` of the guard of the second walk of `AfterKeep` for a byte of `kI`** -/
theorem cleanK_of_kI {q : UInt16} {m : Machine} {x : Nat} (hx : x ∈ kI sy) (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) :
    FrameKeep.CleanK (guardH sy m0 x) q m := by
  refine FrameKeep.cleanK_sub h (fun y hy => ?_) rfl rfl rfl rfl
  simp only [guardH, List.mem_append, List.mem_singleton] at hy
  rcases hy with rfl | hy
  · exact kI_mem hx
  · exact List.mem_append_right _ hy

/-- **A frame in control keeps four vertical bytes from the scroll handler to its end**: the vertical force down, the jump's origin, the jump's halt value, A and B. The
frame starts in the idle loop in control (`FrameKeep.StartK`), each instruction meets `CleanK` of `FrameKeep.guardE` and writes neither the routine, nor the mode, nor
the task by its address; the area's type is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time. Then at each
instruction `k ≥ n₀` at the scroll handler the four bytes are those of the frame's end. `hc`, `hk` are the checks on the ROM. The proof is that of `GuardE.keepHE`, with
the bytes of `kI` for those of `AfterKeep.hI`. -/
theorem keep_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hk : kCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ x ∈ kI sy, (frame m i).ram.get! x = (trace m i k).ram.get! x := by
  simp only [kCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
  obtain ⟨⟨⟨⟨hne1, hne2⟩, hp1⟩, hp2⟩, hp3⟩ := hk
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPH sy m0 v q (q1Cfg sy m0 v P) ((kI sy).map fun b => q2Cfg sy m0 b P.stops.toList)) hp1 rfl rfl rfl
      (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd h1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (h4 n₀ h)
    subst hk0
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (CtrlKeep.valA sy v) (trace m i k₀) := by
      intro w hw
      simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQ sy ((kI sy).map fun b => q2Cfg sy m0 b P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ := q1_run (C := q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclF hx'
    intro k hk hpc x hxI
    have hmem : q2Cfg sy m0 x P.stops.toList ∈ (kI sy).map fun b => q2Cfg sy m0 b P.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
    have hw2 := List.all_eq_true.1 hat _ hmem
    have ht2 := List.all_eq_true.1 hp3 _ hmem
    have hs2 : Sim (q2Cfg sy m0 x P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (rkOn B₁) (trace m i k₁) := sim_rkOn hs₁
    have hclH : ∀ j, FrameKeep.CleanK (q2Cfg sy m0 x P.stops.toList).G (q2Cfg sy m0 x P.stops.toList).S.store (trace m i j) := fun j => cleanK_of_kI hxI (hcl j)
    obtain ⟨⟨B₂, hfin, hs₂⟩, hnoQ⟩ := endKR (C := q2Cfg sy m0 x P.stops.toList) ht2 rfl rfl hne2 hw2 hs2 hf1 hd1 hclH hx'
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [h1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exfalso
        have := hnoQ (k - k₁) (by omega)
        rw [show k₁ + (k - k₁) = k by omega] at this
        exact this hpc
    subst hkk
    change (B₂.rk && !B₂.spent) = true at hfin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
    have e := hs₂.rkv hfin.1
    rw [if_neg (by simp [hfin.2])] at e
    exact e
  · exact absurd harr (hno n₀ hf0)

end

end Smbrta.VertKeep
