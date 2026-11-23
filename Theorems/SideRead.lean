import Theorems.EraseRange

/-!
# The side pipe's read of the position, only on the entering frame (round 34)

`SiteOK.xbit` asks that the position's low bits are not 0 where the side pipe's code reads the position (`xAt`): with them 0 the code does not set the area
change's timer. Until round 33 the route asked it on every instruction of every frame of the room (`roomXbit`).

The side pipe's code reads the position at `xAt` and goes on, with no branch out of it, to the store of the routine byte (`stAt`, an `STA zp`). With the step
`EraseRange.pstepX` (a fifth piece at `xAt`, the four low bits 0) the room's walks need nothing of the position there. Each state of the walks also passes two
checks (`xChk`):

* `rtOK`: its step keeps the routine byte (it may be the coin's erase, which writes in the block buffers), or it is an `STA zp` of the routine byte with the
  accumulator known and not the reference's routine; the state at `stAt` is such a store;
* `wsetOK`: a state from `xAt` to before `stAt` has every successor of the walk's step from `xAt` to `stAt`;

and the walks' frame ends are not from `xAt` to `stAt` (`finX`). Then on a frame: once an instruction was at `xAt`, the machine stays from `xAt` to `stAt` until
the store, and after it the routine byte is not the reference's (`XInv`, `xinv_step`). A frame that ends with the reference's routine never runs `xAt`
(`no_xAt`). The frames of the room before the entering frame end in the player's routine (the definition of `a₂`), so only the entering frame reads the
position, and the route asks `Xbit` there only.

There is no game data in this file. Page: `1-1/d-2-4-2-9-SideRead.md`.
-/

namespace Smbrta.SideRead

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken coverS startsR writeAddr)
open RoomPause (Reg Ph InCls)

section
open ScreenPage (placesR envR refR)

/-- the store of the routine byte after the side pipe's read of the position: the first `STA zp` of the routine byte from `xAt` on -/
def stAtOf (sy : Syms) (m0 : Machine) (P : Places) : UInt16 := ScreenPage.findOpZ m0 P.xAt 0x85 sy.GameEngineSubroutine.toUInt8 64

/-- **The routine byte's writes**: a step that is not `st` keeps the routine byte (or it is the coin's erase, which writes in the block buffers), or it is an
`STA zp` of the routine byte with the accumulator known and not `v` -/
def rtOK (P : Places) (E : Env) (st : UInt16) (v : UInt8) (A : AS) : Bool :=
  (A.pc != st && (StepWrites.keepOK E (fun i => i == P.rtI) A || (A.pc == P.erase && !A.nmi))) ||
    (EraseRange.opAt E A == 0x85 && RoomBlocks.zI (EraseRange.b1At E A) == P.rtI && !A.nmi && decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) &&
      A.a.isK && A.a.v != v)

/-- **From `xAt` to `st`**: a state from `xAt` to before `st` has every successor of the walk's step from `xAt` to `st` -/
def wsetOK (sp : AS → List AS) (P : Places) (E : Env) (G : Reg) (st : UInt16) (A : AS) : Bool :=
  !(decide (P.xAt ≤ A.pc) && decide (A.pc < st)) ||
    (EraseRange.piecesF sp A).all fun A2 => (EraseRange.pstepX P E (aRows E).toArray G A2).all fun r =>
      match r with
      | some B => decide (P.xAt ≤ B.pc) && decide (B.pc ≤ st)
      | none => false

/-- a frame's end is not from `xAt` to `st` -/
def finX (P : Places) (st : UInt16) (B : AS) : Bool := !(decide (P.xAt ≤ B.pc) && decide (B.pc ≤ st))

/-- **After the side pipe's read of the position** (in frame `m`, `i`, at instruction `j`): if an instruction up to `j` was at `xAt`, the machine is from `xAt` to
`st` or its routine byte is not `v` -/
def XInv (P : Places) (st : UInt16) (v : UInt8) (m : Machine) (i : UInt8) (j : Nat) : Prop :=
  (∃ k, k ≤ j ∧ (trace m i k).pc = P.xAt) → (P.xAt ≤ (trace m i j).pc ∧ (trace m i j).pc ≤ st) ∨ (trace m i j).ram.get! P.rtI ≠ v

section
variable {E : Env} {F : Nat × UInt8} {P : Places} {st : UInt16} {v : UInt8}

set_option maxRecDepth 100000 in
theorem rt_step {A : AS} {m : Machine} (hs : Sim E F A m) (hr : P.rtI < 2048) (hO : PlacesOK E P) (hrb : P.rtI < P.bufLo) (hh : EraseRange.SiteX P m)
    (h : rtOK P E st v A = true) :
    (A.pc ≠ st ∧ (go step m).2.ram.get! P.rtI = m.ram.get! P.rtI) ∨ (go step m).2.ram.get! P.rtI ≠ v := by
  unfold rtOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with ⟨h1, h2 | ⟨he, hn⟩⟩ | ⟨⟨⟨⟨⟨⟨hop, hz⟩, hn⟩, hp⟩, hp1⟩, hak⟩, hav⟩
  · exact Or.inl ⟨h1, StepWrites.keep_step hs h2 P.rtI (by simp)⟩
  · -- the coin's erase writes in the block buffers, above the routine byte
    have hmp : m.pc = P.erase := by rw [hs.pc]; exact he
    obtain ⟨_, g2, _⟩ := hh.erase hmp
    refine Or.inl ⟨h1, RoomBlocks.erase_other (P := EraseRange.movX P (m.pc + 1)) (EraseRange.placesOK_movX hO _) hs hn he
      (EraseRange.siteOK_movX hh) ?_⟩
    intro e
    have : P.bufLo ≤ P.rtI := by rw [e]; exact g2
    omega
  · right
    have hn' : m.nmiPending = false := by rw [hs.nmi]; exact hn
    have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
    have hp1' : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact hp1
    have hop' : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x85 := by rw [hs.prg, hs.mask, hs.pc]; exact hop
    rw [EraseRange.step_rom (f := opSTA mZp) hn' hs.halted hpm hop' (by decide) rfl, EraseRange.tick_ram,
      EraseRange.go_staZp (m := { m with pc := m.pc + 1 }) hp1' hs.trk]
    have hb : ((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 &&& 0x7FF).toNat = P.rtI := by
      rw [hs.prg, hs.mask, hs.pc]
      exact hz
    show (m.ram.set! (((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 &&& 0x7FF).toNat) m.a).get! P.rtI ≠ v
    rw [hb, PipeTransitionAll.ba_get_set_self _ _ _ (by rw [hs.size]; exact hr), isK_eq hak hs.a]
    exact hav

theorem wset_step {sp : AS → List AS} {G : Reg} (hcv : EraseRange.CovF E F sp) (hsk : EraseSplit.SpentKeep sp) (hO : PlacesOK E P) (hT : 2 ≤ F.2.toNat)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine} (hs : Sim E F A m)
    (hf : EraseRange.FOK A.log m) (hh : EraseRange.SiteX P m) (hp : Ph G A m) (h : wsetOK sp P E G st A = true) (hin : P.xAt ≤ A.pc ∧ A.pc < st) :
    P.xAt ≤ (go step m).2.pc ∧ (go step m).2.pc ≤ st := by
  obtain ⟨A2, hA2, r, hr, hB⟩ := EraseRange.succ_of hcv hsk hO rfl hT h0 hg hkb hs hf hh hp
  unfold wsetOK at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.all_eq_true] at h
  rcases h with h | h
  · rcases h with h | h
    · exact absurd hin.1 h
    · exact absurd hin.2 h
  · have h2 := h A2 hA2 r hr
    cases r with
    | none => simp at h2
    | some B =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      have hsB := hB B rfl
      rw [hsB.pc]
      exact h2

theorem xinv_zero {m : Machine} {i : UInt8} (hxs : P.xAt ≤ st) : XInv P st v m i 0 := by
  intro ⟨k, hk, hx⟩
  have : k = 0 := by omega
  subst this
  left
  rw [hx]
  exact ⟨UInt16.le_refl _, hxs⟩

theorem xinv_stop {m : Machine} {i : UInt8} {j : Nat} (e : trace m i (j + 1) = trace m i j) (hJ : XInv P st v m i j) :
    XInv P st v m i (j + 1) := by
  intro ⟨k, hk, hx⟩
  rw [e]
  by_cases hkj : k ≤ j
  · exact hJ ⟨k, hkj, hx⟩
  · have : k = j + 1 := by omega
    subst this
    rw [e] at hx
    exact hJ ⟨j, Nat.le_refl _, hx⟩

theorem xinv_step {sp : AS → List AS} {G : Reg} (hxs : P.xAt ≤ st) (hr : P.rtI < 2048) (hrb : P.rtI < P.bufLo) (hcv : EraseRange.CovF E F sp)
    (hsk : EraseSplit.SpentKeep sp)
    (hO : PlacesOK E P) (hT : 2 ≤ F.2.toNat) (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {m : Machine} {i : UInt8} {j : Nat} {A : AS} (hs : Sim E F A (trace m i j)) (hf : EraseRange.FOK A.log (trace m i j)) (hp : Ph G A (trace m i j))
    (hrt : rtOK P E st v A = true) (hw : wsetOK sp P E G st A = true) (hh : EraseRange.SiteX P (trace m i j))
    (e : trace m i (j + 1) = (go step (trace m i j)).2) (hJ : XInv P st v m i j) : XInv P st v m i (j + 1) := by
  intro ⟨k, hk, hx⟩
  by_cases hkj : k ≤ j
  · rcases hJ ⟨k, hkj, hx⟩ with ⟨h1, h2⟩ | h1
    · rcases Nat.lt_or_ge (trace m i j).pc.toNat st.toNat with h3 | h3
      · have hA : A.pc = (trace m i j).pc := hs.pc.symm
        have hin : P.xAt ≤ A.pc ∧ A.pc < st := ⟨by rw [hA]; exact h1, by rw [hA]; exact UInt16.lt_iff_toNat_lt.2 h3⟩
        left
        rw [e]
        exact wset_step hcv hsk hO hT h0 hg hkb hs hf hh hp hw hin
      · -- at the store
        have hst : (trace m i j).pc = st := by
          apply UInt16.toNat_inj.1
          have := UInt16.le_iff_toNat_le.1 h2
          omega
        right
        rw [e]
        rcases rt_step hs hr hO hrb hh hrt with ⟨h4, _⟩ | h4
        · exact absurd (hs.pc.symm.trans hst) h4
        · exact h4
    · right
      rw [e]
      rcases rt_step hs hr hO hrb hh hrt with ⟨_, h4⟩ | h4
      · rw [h4]
        exact h1
      · exact h4
  · have : k = j + 1 := by omega
    subst this
    left
    rw [hx]
    exact ⟨UInt16.le_refl _, hxs⟩

/-- **A frame that ends with the routine `v`, out of `xAt` to `st`, never runs the side pipe's read of the position** -/
theorem no_xAt {m : Machine} {i : UInt8} (hJ : ∀ j, XInv P st v m i j) (hend : (trace m i fuelPerFrame).frame = m.frame + 1)
    (hpc : ¬ (P.xAt ≤ (frame m i).pc ∧ (frame m i).pc ≤ st)) (hrt : (frame m i).ram.get! P.rtI = v) : ∀ j, (trace m i j).pc ≠ P.xAt := by
  intro j hj
  have hstop : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by simp [hend]
  have hk : ∃ k, k ≤ fuelPerFrame ∧ (trace m i k).pc = P.xAt := by
    rcases Nat.lt_or_ge fuelPerFrame j with h1 | h1
    · refine ⟨fuelPerFrame, Nat.le_refl _, ?_⟩
      have e := PipeEntryRule.trace_stop hstop (j - fuelPerFrame)
      rw [show fuelPerFrame + (j - fuelPerFrame) = j by omega] at e
      rw [← e]
      exact hj
    · exact ⟨j, h1, hj⟩
  rw [PipeEntryRule.frame_trace] at hpc hrt
  rcases hJ fuelPerFrame hk with h1 | h1
  · exact hpc h1
  · exact h1 hrt
end

/-- **The checks of the side pipe's read on one state**: `rtOK` and `wsetOK` (the places are arguments, so that a walk computes them once) -/
def xChk (P : Places) (E : Env) (G : Reg) (sp : AS → List AS) (st : UInt16) (v : UInt8) (A : AS) : Bool := rtOK P E st v A && wsetOK sp P E G st A

/-- the places' facts on the ROM: `xAt ≤ stAt`, and the routine byte is in the RAM, below the block buffers -/
def xFacts (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  decide ((placesR sy nm m0).xAt ≤ stAtOf sy m0 (placesR sy nm m0)) && decide ((placesR sy nm m0).rtI < 2048) &&
    decide ((placesR sy nm m0).rtI < (placesR sy nm m0).bufLo)

end

end Smbrta.SideRead
