import Theorems.EraseRange

/-!
# The block buffer routine reads a tile of the list (round 34)

`SiteParts.Read` asks, at the read `LDA (zp),Y` of the block buffer routine, that the byte read is a tile of the list `P.tiles` (the tiles of the block buffers
of the reference, and the empty tile), and that a read for the head gives the empty tile or a coin. Until round 33 the route asked all of it (`roomRead`).

Here the walks of the room's frames (`LoopTime.recCheckB`) prove the first half:

* **The buffers hold tiles of the list** (`RoomMap.TilesIn`): every byte of the two block buffers is a tile of `P.tiles`. It holds at the room's first control
  (the rows of the change know every byte of the block buffers, `RoomMap.tiles_of_rows`). One step keeps it if the step writes no byte of the block buffers,
  or if it is the coin's erase with the accumulator 0 (`keepOKB`, `tiles_step`): the empty tile is in the list. The walks check this at every state, and the
  frame theorem carries it from instruction to instruction (`frame_of_walkVI`, `frameVI`: `EraseRange.frame_of_walkV` with an invariant), and so from frame to
  frame.
* **The read is in the block buffers** (`ReadIn`): the walks know the pointer's page and the largest value of its low byte, and a bound of `Y` (the row, from the
  height's bound: `EraseRange.xferY`), and check that the address is in the block buffers (`LoopTime.readInOK`).

Then the byte read is a tile of the list (`read_of`). The route asks only the head's half (`ReadH`): a read for the head gives the empty tile or a coin.

There is no game data in this file. Page: `1-1/d-2-4-2-8-ReadTiles.md`.
-/

namespace Smbrta.ReadTiles

open PipeTransition (frame)
open PipeTransitionAll (Names go go_bind ba_get_set_self ba_get_set_ne)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS RoomCond readAddr readVal writeAddr startsR)
open RoomPause (Reg Ph InCls)
open RoomLate (LateS sclamp sim_sclamp sclamp_k sclamp_spent)
open EraseSplit (SpentKeep)
open EraseRange (FOK CovF walkV LiveV live_stepV chkV_of_walk Rules VOK fok_nil sim_log)
open RoomMap (TilesIn)

/-! ## The parts of `Read` -/

/-- **The head's half of `SiteParts.Read`**: a read for the head gives the empty tile or a coin. The route asks this (`roomRead`, round 34) -/
def ReadH (P : Places) (m : Machine) : Prop :=
  m.pc = P.read → m.ram.get! P.saveI ∈ P.heads → readVal m ∈ P.headTiles

/-- **The read is in the block buffers**: the address of the block buffer routine's read is in the RAM, in the two block buffers -/
def ReadIn (P : Places) (m : Machine) : Prop :=
  m.pc = P.read → readAddr m < 0x2000 ∧ P.bufLo ≤ (readAddr m &&& 0x7FF).toNat ∧ (readAddr m &&& 0x7FF).toNat < P.bufLo + P.bufN

/-- **`Read` from its parts**: the block buffers hold tiles of the list, the read is in them, and the head's half -/
theorem read_of {P : Places} {m : Machine} (ht : TilesIn P m) (hi : ReadIn P m) (hh : ReadH P m) : SiteParts.Read P m := by
  intro hpc
  obtain ⟨a1, a2, a3⟩ := hi hpc
  refine ⟨?_, hh hpc⟩
  rw [RoomBlocks.readVal_eq a1]
  exact ht _ a2 a3

/-! ## One step keeps the tiles -/

/-- a RAM index of the block buffers -/
def inBuf (P : Places) (i : Nat) : Bool := decide (P.bufLo ≤ i) && decide (i < P.bufLo + P.bufN)

/-- **The check of one state**: its step writes no byte of the block buffers, or it is the coin's erase (its operand in the ROM) with the accumulator known 0 -/
def keepOKB (P : Places) (E : Env) (A : AS) : Bool :=
  StepWrites.keepOK E (inBuf P) A || (A.pc == P.erase && !A.nmi && decide (0x8000 ≤ A.pc + 1) && A.a.isK && A.a.v == 0)

/-- the empty tile is in the list of the tiles -/
theorem zero_mem_tilesOf (lo n : Nat) (r : Machine) : (0 : UInt8) ∈ ScreenPage.tilesOf lo n r := by
  unfold ScreenPage.tilesOf
  exact List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_singleton_self _))

section
variable {E : Env} {F : Nat × UInt8}

/-- the two reads of the pointer from the zero page keep the machine -/
theorem rd16zp_state {x : Machine} (z : UInt8) (ht : x.trk = false) : (go (rd16zp z) x).2 = x := by
  have e : go (rd16zp z) x = go (rd z.toUInt16 >>= fun lo => rd (z + 1).toUInt16 >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) x := rfl
  rw [e, go_bind, TaintRun.rd_ram (RoomBlocks.zp_lt z) ht]
  simp only []
  rw [go_bind, TaintRun.rd_ram (RoomBlocks.zp_lt (z + 1)) ht]
  rfl

/-- the address of `STA (zp),Y` is made with no change but the program counter -/
theorem mIzy_state {m : Machine} (hp1 : m.pc + 1 ≥ 0x8000) (ht : m.trk = false) :
    (go mIzy { m with pc := m.pc + 1 }).2 = { m with pc := m.pc + 1 + 1 } := by
  have e : go mIzy { m with pc := m.pc + 1 } =
      go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun s => pure (b + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp1, go_bind]
  show (go (get >>= fun s => pure ((go (rd16zp (RoomBlocks.operand m)) { m with pc := m.pc + 1 + 1 }).1 + s.y.toUInt16))
    (go (rd16zp (RoomBlocks.operand m)) { m with pc := m.pc + 1 + 1 }).2).2 = _
  rw [rd16zp_state (x := { m with pc := m.pc + 1 + 1 }) _ ht]
  rfl

/-- **The erase's step on the machine**: `STA (zp),Y` writes the accumulator at its address -/
theorem erase_ram {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91) (had : writeAddr m < 0x2000) (ht : m.trk = false) :
    (go step m).2.ram = m.ram.set! (writeAddr m &&& 0x7FF).toNat m.a := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), ScreenPage.op_91, ScreenPage.cyc_91]
  have hs2 := mIzy_state hp1 ht
  generalize hm2 : (go mIzy { m with pc := m.pc + 1 }).2 = m2 at hs2
  have t2 : m2.trk = false := by rw [hs2]; exact ht
  have a2 : m2.a = m.a := by rw [hs2]
  have r2 : m2.ram = m.ram := by rw [hs2]
  have e : go ((opSTA mIzy) >>= fun _ => tick 6) { m with pc := m.pc + 1 } = go (tick 6) (go (wr (writeAddr m) m2.a) m2).2 := by
    rw [go_bind]
    have e2 : go (opSTA mIzy) { m with pc := m.pc + 1 } =
        go (mIzy >>= fun ad => (MonadState.get : M Machine) >>= fun t => wr ad t.a) { m with pc := m.pc + 1 } := rfl
    rw [e2, go_bind, hm2]
    rfl
  rw [e, TaintRun.wr_ram _ had t2, EraseRange.tick_ram]
  show m2.ram.set! (writeAddr m &&& 0x7FF).toNat m2.a = _
  rw [a2, r2]

/-- **One step keeps the tiles of the block buffers**, if the state's check `keepOKB` holds and the empty tile is in the list -/
theorem tiles_step {P : Places} {A : AS} {m : Machine} (hO : PlacesOK E P) (h0 : (0 : UInt8) ∈ P.tiles) (hs : Sim E F A m)
    (hk : keepOKB P E A = true) (hh : EraseRange.SiteX P m) (ht : TilesIn P m) : TilesIn P (go step m).2 := by
  unfold keepOKB at hk
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hk
  rcases hk with hk | ⟨⟨⟨⟨hpc, hn⟩, h81⟩, hak⟩, hav⟩
  · intro d hd1 hd2
    rw [StepWrites.keep_step hs hk d (by simp [inBuf, hd1, hd2])]
    exact ht d hd1 hd2
  · have hmp : m.pc = P.erase := by rw [hs.pc]; exact hpc
    have hn' : m.nmiPending = false := by rw [hs.nmi]; exact hn
    have hp0 : m.pc ≥ 0x8000 := by rw [hmp]; exact hO.erase.1
    have hp1 : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact h81
    have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91 := by rw [hs.prg, hs.mask, hmp]; exact hO.erase.2
    obtain ⟨g1, _, _⟩ := hh.erase hmp
    have hr := erase_ram hn' hs.halted hp0 hp1 hop g1 hs.trk
    have ha : m.a = 0 := by rw [isK_eq hak hs.a]; exact hav
    intro d hd1 hd2
    rw [hr]
    by_cases hdi : (writeAddr m &&& 0x7FF).toNat = d
    · rw [← hdi, ba_get_set_self _ _ _ (by rw [hs.size]; exact EraseRow.and7FF_lt _), ha]
      exact h0
    · rw [ba_get_set_ne _ _ _ _ hdi]
      exact ht d hd1 hd2
end

/-! ## The frame with an invariant -/

section
variable {G : Reg} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8} {sq : UInt16 → Bool} {D : Nat} {sp : AS → List AS} {Ru : Rules}

/-- **One frame of the walk with bounds, with invariants** (round 34): `EraseRange.frame_of_walkV`, with an invariant `I` of the machine and an invariant `J`
of the instruction's number. At each instruction the check of the walk's state gives `SiteX` (with `I`), `I` after the step (`hI`) and `J` after the step
(`hJ`, from the state's check and `Ph`); when the frame is over, `J` goes on (`hJs`). Then `I` and `J` hold at every instruction -/
theorem frame_of_walkVI (hcv : CovF C.E F sp) (hsk : SpentKeep sp) {R I : Machine → Prop} {J : Nat → Prop}
    (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → FOK A.log m → chk A = true → R m → I m → EraseRange.SiteX C.P m)
    (hI : ∀ {A : AS} {m : Machine}, Sim C.E F A m → FOK A.log m → chk A = true → R m → I m → EraseRange.SiteX C.P m → I (go step m).2)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkV sp Ru G C chk sq D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hp : C.E.pad = AB.top) (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkV sp Ru G C chk sq D Fu S = true) (hs : Sim C.E F S m) (hf : FOK S.log m) (hph : Ph G S m)
    (hk : ∀ j, R (trace m i j)) (hI0 : I (trace m i 0))
    (hJ : ∀ j {A : AS}, Sim C.E F A (trace m i j) → FOK A.log (trace m i j) → Ph G A (trace m i j) → chk A = true → R (trace m i j) →
      I (trace m i j) → EraseRange.SiteX C.P (trace m i j) → (trace m i j).frame = m.frame → trace m i (j + 1) = (go step (trace m i j)).2 → J j → J (j + 1))
    (hJs : ∀ j, trace m i (j + 1) = trace m i j → J j → J (j + 1)) (hJ0 : J 0) :
    (∀ j, EraseRange.SiteX C.P (trace m i j)) ∧ (∃ B, C.fin B = true ∧ Sim C.E F B (frame m i)) ∧ (∀ j, I (trace m i j)) ∧ (∀ j, J j) ∧
      (trace m i fuelPerFrame).frame = m.frame + 1 := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have hf0 : FOK S.log { m with pad := smbToPad i } := hf
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E F A m' → FOK A.log m' → chk A = true → (R m' ∧ I m') → EraseRange.SiteX C.P m' :=
    fun hs1 hf1 hc1 hr => hQ hs1 hf1 hc1 hr.1 hr.2
  have hS' : ∀ {m' : Machine}, (R m' ∧ I m') → LateS sq D m' := fun hr => hS hr.1
  have key : ∀ j, ((∃ A, LiveV sp Ru G C chk sq D F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j) ∧ FOK B.log (trace m i j) ∧
        Ph G B (trace m i j))) ∧ I (trace m i j) ∧ J j := by
    intro j
    induction j with
    | zero => exact ⟨Or.inl ⟨S, ⟨hs0, hf0, hph0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩, hI0, hJ0⟩
    | succ j ih =>
      obtain ⟨ih, hIj, hJj⟩ := ih
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h3, h4, h4', h5⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have h1c := h1
        obtain ⟨hs1, hf1, hp1, n, hw1⟩ := h1c
        have hsc : Sim C.E F (sclamp sq D A) (trace m i j) := sim_sclamp hD hs1 (hS (hk j))
        have hfc : FOK (sclamp sq D A).log (trace m i j) := by unfold sclamp; split <;> exact hf1
        have hpc : Ph G (sclamp sq D A) (trace m i j) := RoomPause.ph_of_spent (sclamp_spent sq D A).symm hp1
        have hcc : chk (sclamp sq D A) = true := chkV_of_walk hw1
        have hsite : EraseRange.SiteX C.P (trace m i j) := hQ hsc hfc hcc (hk j) hIj
        have hJ1 : J (j + 1) := hJ j hsc hfc hpc hcc (hk j) hIj hsite h3 e2 hJj
        have hI1 : I (trace m i (j + 1)) := by rw [e2]; exact hI hsc hfc hcc (hk j) hIj hsite
        have hh2 := hS (hk (j + 1))
        rw [e2] at hh2 hI1 ⊢
        refine ⟨?_, hI1, hJ1⟩
        rcases live_stepV hcv hsk hQ' hS' hD hO ht hops hT h0 hg hkb h1 ⟨hk j, hIj⟩ hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a4', a5⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', by rw [a3, h2], a4, a4', a5⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        have hJ1 := hJs j e2 hJj
        rw [e2]
        exact ⟨Or.inr ⟨h1, B, h2, h2', h3, h4, h4', h5⟩, hIj, hJ1⟩
  have hend : (trace m i fuelPerFrame).frame = m.frame + 1 := by
    rcases (key fuelPerFrame).1 with ⟨A, h1, _, _, h4⟩ | ⟨h1, _⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact h1
  refine ⟨fun j => ?_, ?_, fun j => (key j).2.1, fun j => (key j).2.2, hend⟩
  · obtain ⟨hj, hIj, _⟩ := key j
    rcases hj with ⟨A, ⟨h1, hf1, _, n, h1'⟩, _, _, _⟩ | ⟨_, B, _, h2', _, h4, h4', _⟩
    · have hf1' : FOK (sclamp sq D A).log (trace m i j) := by unfold sclamp; split <;> exact hf1
      exact hQ (sim_sclamp hD h1 (hS (hk j))) hf1' (chkV_of_walk h1') (hk j) hIj
    · exact hQ h4 h4' h2' (hk j) hIj
  · rw [frame_trace]
    rcases (key fuelPerFrame).1 with ⟨A, h1, _, _, h4⟩ | ⟨_, B, h2, _, _, h4, _, _⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨B, h2, h4⟩

end

/-- **One frame of the room from a reference of `RK`, with invariants** (round 34): `EraseRange.frameV`, with `I` and `J` carried through the frame -/
theorem frameVI {sp : AS → List AS} {Ru : Rules} {E : Env} {P : Places} {G : Reg} {RK : List (Machine × List (Nat × UInt8))}
    {C : CfgS} {fin chk : AS → Bool} {sq : UInt16 → Bool} {D : Nat} {R I : Machine → Prop} (hcv : ∀ F : Nat × UInt8, CovF E F sp) (hsk : SpentKeep sp)
    (h : VOK sp Ru E P G RK C fin chk sq D)
    (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → FOK A.log m → chk A = true → R m → I m → EraseRange.SiteX P m)
    (hI : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → FOK A.log m → chk A = true → R m → I m → EraseRange.SiteX P m → I (go step m).2)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) {r : Machine} {K : List (Nat × UInt8)} (hq : (r, K) ∈ RK)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hc : InCls G m) (hk : ∀ j, R (trace m i j)) (hI0 : I (trace m i 0)) {J : Nat → Prop}
    (hJ : ∀ j {A : AS}, Sim E (m.frame, 2) A (trace m i j) → FOK A.log (trace m i j) → Ph G A (trace m i j) → chk A = true → R (trace m i j) →
      I (trace m i j) → EraseRange.SiteX P (trace m i j) → (trace m i j).frame = m.frame → trace m i (j + 1) = (go step (trace m i j)).2 → J j → J (j + 1))
    (hJs : ∀ j, trace m i (j + 1) = trace m i j → J j → J (j + 1)) (hJ0 : J 0) :
    (∀ j, EraseRange.SiteX P (trace m i j)) ∧ (∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i)) ∧ (∀ j, I (trace m i j)) ∧ (∀ j, J j) ∧
      (trace m i fuelPerFrame).frame = m.frame + 1 := by
  obtain ⟨hM, hw0⟩ := h.starts _ hq
  obtain ⟨S0, hS0, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) hM h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := hw0 S0 hS0
  have hs' : Sim C.E (m.frame, 2) { S0 with log := [] } m := by rw [h.env]; exact sim_log _ hs
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → FOK A.log m' → chk A = true → R m' → I m' → EraseRange.SiteX C.P m' := by
    intro A m' hs2 hf2 hc2 hr hi
    rw [h.pl]
    rw [h.env] at hs2
    exact hQ hs2 hf2 hc2 hr hi
  have hI' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → FOK A.log m' → chk A = true → R m' → I m' → EraseRange.SiteX C.P m' →
      I (go step m').2 := by
    intro A m' hs2 hf2 hc2 hr hi hst
    rw [h.env] at hs2
    rw [h.pl] at hst
    exact hI hs2 hf2 hc2 hr hi hst
  have hJ' : ∀ j {A : AS}, Sim C.E (m.frame, 2) A (trace m i j) → FOK A.log (trace m i j) → Ph G A (trace m i j) → chk A = true → R (trace m i j) →
      I (trace m i j) → EraseRange.SiteX C.P (trace m i j) → (trace m i j).frame = m.frame → trace m i (j + 1) = (go step (trace m i j)).2 → J j → J (j + 1) := by
    intro j A hs2 hf2 hp2 hc2 hr hi hst hfr he hj
    rw [h.env] at hs2
    rw [h.pl] at hst
    exact hJ j hs2 hf2 hp2 hc2 hr hi hst hfr he hj
  have hcv' : CovF C.E (m.frame, 2) sp := by rw [h.env]; exact hcv _
  have := frame_of_walkVI (G := G) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) (I := I) (J := J) hcv' hsk hQ' hI' hS h.dD hO h.table h.ops
    (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) h.tab h.gI h.keepI hw hs' (fok_nil _) (Or.inr hc) hk hI0 hJ' hJs hJ0
  rw [h.pl, h.fin, h.env] at this
  exact this

/-- `I` at the frame's end, from `I` at each instruction -/
theorem inv_end {I : Machine → Prop} {m : Machine} {i : UInt8} (h : ∀ j, I (trace m i j)) : I (frame m i) := by
  rw [frame_trace]
  exact h _

end Smbrta.ReadTiles
