import Theorems.VertKeep
import Theorems.OpenFlat

/-!
# The opening: four vertical bytes after the return of the collision routine

`VertKeep.keep_end` (part e) shows that a frame in control keeps four vertical bytes (`VertKeep.kI`: the vertical force down, the jump's origin, the jump's halt value,
A and B) from the scroll handler to its end. The frames of the opening ask these bytes at a later place: the return of the collision routine in the player's routine
(`OpenFlat.collRet`, the field `afterV` of `OpenFrames.RealB`). The walks of `TaintRun` give the frame's end only, not the steps between, so here are the same two
walks of `AfterKeep` with the return in place of the scroll handler:

* the first from the cut of `CtrlKeep` (the player's routine) to the first time the frame comes to the place `Q` (`AfterKeep.walkQ1`);
* the second from there to the frame's end (`AfterKeep.walkKR`), with one byte followed as the counter of `TaintRun` (`Env.rkI`): it fails on any write to the byte, and
  if the frame comes to `Q` again.

`keep_at` is the theorem for any place `Q`; `keep_ret` is `keep_at` at the return of the collision routine. The condition on each instruction is `CleanK` of
`FrameKeep.guardE`, which protects the four bytes (`VertKeep.cleanK_of_kI`), and no store to the routine, the mode or the task by its address.

The searches are no part of the proof. No game data. Page: `1-1/a-5-4-3-3-4-OpenAfter.md`.
-/

namespace Smbrta.OpenAfter

open TaintRun
open PipeEntryRule (trace)
open PipeTransition (frame)
open AfterKeep (walkQ1 walkKR rkOn sim_rkOn endKR q1_run guardH tableBut)

/-- the search from the cut to the place `Q`, from the states at the cut: no part of the proof -/
def search1 (sy : Syms) (m0 : Machine) (v : UInt8) (Q : UInt16) (starts : List AS) : PrevKeep.PS :=
  PrevKeep.searchFrom sy m0 (PipeEntryRule.envOf m0) (CtrlKeep.spareI sy m0) [] (CtrlKeep.watchA sy m0 v) (FrameKeep.ctlI sy) (fun A => A.pc == Q)
    (starts.map (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v)))

/-- **The first walk's table**: `AfterKeep.q1Cfg` with the place `Q` -/
def cfg1 (sy : Syms) (m0 : Machine) (v : UInt8) (Q : UInt16) (P : PrevKeep.PS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardF sy m0
  let E := PipeEntryRule.envOf m0
  let W := CtrlKeep.watchA sy m0 v
  let key := PrevKeep.keyP S G W
  let q := tableBut key Q P.X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- **The second walk's table** for the byte `b`, from the states `starts` at `Q`: `AfterKeep.q2Cfg` with the place `Q` -/
def cfg2 (sy : Syms) (m0 : Machine) (Q : UInt16) (b : Nat) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardH sy m0 b
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let P := PrevKeep.searchFrom sy m0 E (b :: CtrlKeep.spareI sy m0) [] [] (FrameKeep.ctlI sy) (fun A => A.pc == Q) (starts.map rkOn)
  let q := FrameKeep.tableOfKW key P.X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun B => B.rk && !B.spent }

/-- what the first walk asks at `Q`: the second walk succeeds for each byte -/
def atQ (sy : Syms) (Q : UInt16) (C2 : List FrameKeep.CfgK) (B : AS) : Bool := C2.all fun C => walkKR C (FrameKeep.ctlI sy) Q FrameKeep.fuelK (rkOn B)

/-- the walk of the pause bit up to the cut, then the first walk, then the second walks -/
def cfgP (sy : Syms) (m0 : Machine) (v : UInt8) (Q : UInt16) (q : CtrlKeep.Table) (C1 : FrameKeep.CfgK) (C2 : List FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => walkQ1 C1 (FrameKeep.ctlI sy) Q (atQ sy Q C2) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check for the place `Q` and the bytes `bs`**: the walk of the pause bit up to the cut; from there the first walk to `Q`; from there, for each byte of `bs`,
the second walk to the frame's end -/
def checkAt (sy : Syms) (m0 : Machine) (v : UInt8) (Q : UInt16) (bs : List Nat) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := search1 sy m0 v Q cuts
  let C1 := cfg1 sy m0 v Q P
  let C2 := bs.map fun b => cfg2 sy m0 Q b P.stops.toList
  sy.PlayerCtrlRoutine != Q && Q != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (cfgP sy m0 v Q q C1 C2) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) Q (atQ sy Q C2) FrameKeep.fuelK) &&
    C2.all fun C => C.t.all (walkKR C (FrameKeep.ctlI sy) Q FrameKeep.fuelK)

/-- **The check on the ROM**: `checkAt` at the return of the collision routine, with the four bytes of `VertKeep.kI` -/
def retCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool := checkAt sy m0 v (OpenFlat.collRet sy m0) (VertKeep.kI sy)

section
variable {sy : Syms} {m0 : Machine}

/-- **A frame in control keeps the bytes of `bs` from the place `Q` to its end.** The frame starts in the idle loop in control (`FrameKeep.StartK`), each instruction
meets `CleanK` of `FrameKeep.guardF` and of the guard of the second walk for each byte of `bs` (`hH`), and writes neither the routine, nor the mode, nor the task by its
address; the area's type is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time. Then at each instruction `k ≥ n₀`
at `Q` the bytes of `bs` are those of the frame's end. `hc`, `hk` are the checks on the ROM. The proof is that of `VertKeep.keep_end`, with `Q` for the scroll
handler. -/
theorem keep_at (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} {Q : UInt16} {bs : List Nat} (hk : checkAt sy m0 v Q bs = true) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ bs, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = Q → ∀ x ∈ bs, (frame m i).ram.get! x = (trace m i k).ram.get! x := by
  simp only [checkAt, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
  obtain ⟨⟨⟨⟨hne1, hne2⟩, hp1⟩, hp2⟩, hp3⟩ := hk
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize search1 sy m0 v Q cuts = P at hp1 hp2 hp3
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgP sy m0 v Q q (cfg1 sy m0 v Q P) (bs.map fun b => cfg2 sy m0 Q b P.stops.toList)) hp1 rfl rfl rfl
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
    have hw : walkQ1 (cfg1 sy m0 v Q P) (FrameKeep.ctlI sy) Q (atQ sy Q (bs.map fun b => cfg2 sy m0 Q b P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ := q1_run (C := cfg1 sy m0 v Q P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hcl hx'
    intro k hk hpc x hxI
    have hmem : cfg2 sy m0 Q x P.stops.toList ∈ bs.map fun b => cfg2 sy m0 Q b P.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
    have hw2 := List.all_eq_true.1 hat _ hmem
    have ht2 := List.all_eq_true.1 hp3 _ hmem
    have hs2 : Sim (cfg2 sy m0 Q x P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (rkOn B₁) (trace m i k₁) := sim_rkOn hs₁
    have hclH : ∀ j, FrameKeep.CleanK (cfg2 sy m0 Q x P.stops.toList).G (cfg2 sy m0 Q x P.stops.toList).S.store (trace m i j) := fun j => hH x hxI j
    obtain ⟨⟨B₂, hfin, hs₂⟩, hnoQ⟩ := endKR (C := cfg2 sy m0 Q x P.stops.toList) ht2 rfl rfl hne2 hw2 hs2 hf1 hd1 hclH hx'
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

/-- **A frame in control keeps four vertical bytes from the return of the collision routine to its end**: the vertical force down, the jump's origin, the jump's
halt value, A and B (`VertKeep.kI`). `keep_at` at `OpenFlat.collRet`, with the one condition `CleanK` of `FrameKeep.guardE` on each instruction. -/
theorem keep_ret (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hk : retCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = OpenFlat.collRet sy m0 → ∀ x ∈ VertKeep.kI sy, (frame m i).ram.get! x = (trace m i k).ram.get! x :=
  keep_at hc hk h0 (fun n => FrameKeep.cleanK_of_E (hcl n)) (fun _ hx' j => VertKeep.cleanK_of_kI hx' (hcl j)) hx hv harr hf0 hfirst

end

end Smbrta.OpenAfter
