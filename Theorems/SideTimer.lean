import Theorems.MoveScroll

/-!
# Above ground: the scroll's bytes from the frame's start to the player's routine

The scroll handler moves the screen only when the scroll lock is 0, the byte of his place on the screen is at least a threshold and the side collision's timer is 0
(`ScrollRule.Allows`). The field `nearA` of the frames above ground (round 28) asked a condition on these bytes where the frame first comes to the player's routine
(`MoveScroll.NearA`). This file moves it to the frame's start (`NearM`), where an induction over the frames can take it up.

From the frame's start to the player's routine the frame runs the screen, the sound, the pad, the pause and the timers. The timer part decrements the side
collision's timer through an index (`DEC abs,X`), once at most. The walks of `CtrlKeep` follow one byte as the counter of `TaintRun` (`Env.rkI`, `AS.rk`,
`AS.spent`), but `TaintRun` follows only the counter's `DEC abs`. Here the step `gsuccX` also follows `DEC abs,X` of the counter when the index is known
(`arkOpX`, `s_rkOpX`): the counter falls by one, at most once. The walk `walkX` is the walk of `CtrlKeep` with this step; at the player's routine it asks only that
the counter is followed. So the timer there is the timer at the frame's start, or one less (`side_at`), and a timer 0 there was at most 1 at the frame's start
(`side_le`).

The place byte, the scroll lock and the edge's two bytes are not written before the player's routine: the walks of `CtrlKeep` show it (`keep_at`, with the table
of `CtrlKeep.cutTable`). The position is in `CtrlKeep.keepA`. So `NearM` at the frame's start gives `NearA` at the arrival (`nearA_of_M`).

The searches of the tables are no part of the proof. No game data: the bytes are the operands of the scroll handler's loads (`ScrollRule.places`).
Page: `1-1/e-2-10-3-17-SideTimer.md`.
-/

namespace Smbrta.SideTimer

open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun
open PipeWrites
open PipeEntryRule (trace)
open LagFrames (preL opOf startL)
open CtrlKeep (CfgR coverR keyR startP cfgOf envR Table)

variable {sy : Syms} {m0 : Machine}

/-! ## `DEC abs,X` of the counter -/

/-- the target of `DEC abs,X` at `A.pc`, with the index of `A` -/
def decTarget (E : Env) (A : AS) : UInt16 :=
  ((E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 ||| ((E.prg.get! ((A.pc + 2) &&& E.mask).toNat).toUInt16 <<< 8)) + A.x.v.toUInt16

/-- the instruction `DEC abs,X` of the counter, with the index known -/
def isRkDecX (E : Env) (A : AS) : Bool :=
  opOf E A == 0xDE && A.x.isK && decide (E.rkI < 2048) && decide (decTarget E A < 0x2000) && ((decTarget E A) &&& 0x7FF).toNat == E.rkI

/-- the flags after `DEC`: Z and N not known -/
def decFlags (p : AB) : AB := ((p.and (AB.known 0x7D)).or (AB.ite none 0x02 0)).or (AB.top.and (AB.known 0x80))

/-- `DEC abs,X` of the counter, with the index known: it falls by one, at most once in a frame -/
def arkOpX (E : Env) : AM Unit :=
  afetch16 E >>= fun ad A =>
    if A.rk && !A.spent && A.x.isK && decide (ad + A.x.v.toUInt16 < 0x2000) && ((ad + A.x.v.toUInt16) &&& 0x7FF).toNat == E.rkI then
      some ((), { A.setK E.rkI AB.top with spent := true, dg := A.dg && !E.D.contains E.rkI, p := decFlags A.p })
    else none

section
variable {E : Env} {F : Nat × UInt8}

open PipeTransitionAll (mask_lt ba_size_set ba_get_set_self ba_get_set_ne) in
/-- `DEC abs,X` of the counter, the index known -/
theorem s_rkOpX : Snd E F TT (arkOpX E) (opDEC mAbx) := by
  refine Snd.congr (g := fetch16 >>= fun ad => (MonadState.get >>= fun (s : Machine) => rd (ad + s.x.toUInt16) >>= fun v => decV v >>= fun r =>
    wr (ad + s.x.toUInt16) r)) (fun _ => rfl) ?_
  refine Snd.bind s_fetch16 fun ad ad2 h => ?_
  subst h
  refine snd_leaf fun A m hs a A' he => ?_
  have he2 : (if A.rk && !A.spent && A.x.isK && decide (ad + A.x.v.toUInt16 < 0x2000) && ((ad + A.x.v.toUInt16) &&& 0x7FF).toNat == E.rkI then
      some ((), { A.setK E.rkI AB.top with spent := true, dg := A.dg && !E.D.contains E.rkI, p := decFlags A.p }) else none) = some (a, A') := he
  split at he2
  · rename_i hc
    obtain ⟨rfl, rfl⟩ := some_pair he2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨hr, hsp⟩, hxk⟩, h1⟩, hi⟩ := hc
    have hx : m.x = A.x.v := CtrlKeep.eq_of_known hxk hs.x
    have eg : go (MonadState.get >>= fun (s : Machine) => rd (ad + s.x.toUInt16) >>= fun v => decV v >>= fun r => wr (ad + s.x.toUInt16) r) m =
        go (rd (ad + A.x.v.toUInt16) >>= fun v => decV v >>= fun r => wr (ad + A.x.v.toUInt16) r) m := by
      rw [← hx]
      rfl
    rw [eg, go_dec h1 hs.trk]
    have hlt : E.rkI < 2048 := by
      rw [← hi]
      exact mask_lt _
    have hv : m.ram.get! ((ad + A.x.v.toUInt16) &&& 0x7FF).toNat = F.2 := by
      rw [hi, hs.rkv hr, hsp]
      rfl
    rw [hv, hi]
    refine ⟨trivial, { hs with
      p := ?_
      size := by show (m.ram.set! E.rkI (F.2 - 1)).size = 2048; rw [ba_size_set]; exact hs.size
      szR := by show (A.ram.set! E.rkI AB.top.v).size = 2048; rw [ba_size_set]; exact hs.szR
      szK := by show (A.kn.set! E.rkI AB.top.k).size = 2048; rw [ba_size_set]; exact hs.szK
      ram := ?_
      dg := ?_
      rkv := ?_ }, rfl, rfl⟩
    · exact mem_or (mem_or (mem_and hs.p (mem_known_self _)) (mem_ite (TR_none _) 0x02 0)) (mem_and (mem_top _) (mem_known_self _))
    · intro j hj
      show AB.mem ⟨(A.ram.set! E.rkI AB.top.v).get! j, (A.kn.set! E.rkI AB.top.k).get! j⟩ ((m.ram.set! E.rkI (F.2 - 1)).get! j)
      by_cases hij : E.rkI = j
      · subst hij
        rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hj), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hj)]
        exact mem_top _
      · rw [ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij]
        exact hs.ram j hj
    · intro hg
      have hg' : A.dg = true ∧ E.D.contains E.rkI = false := by simpa using hg
      have hany := hs.dg hg'.1
      obtain ⟨d, hd, hd2⟩ := List.any_eq_true.1 hany
      refine List.any_eq_true.2 ⟨d, hd, ?_⟩
      have hne2 : E.rkI ≠ d := by
        intro he3
        subst he3
        have : E.D.contains E.rkI = true := by simpa using hd
        rw [this] at hg'
        simp at hg'
      show ((m.ram.set! E.rkI (F.2 - 1)).get! d != 0) = true
      rw [ba_get_set_ne _ _ _ _ hne2]
      exact hd2
    · intro _
      show (m.ram.set! E.rkI (F.2 - 1)).get! E.rkI = (if true = true then F.2 - 1 else F.2)
      rw [ba_get_set_self _ _ _ (by rw [hs.size]; exact hlt)]
      rfl
  · cases he2

set_option maxRecDepth 100000 in
theorem op_DE : opTable[(0xDE : UInt8).toNat]?.getD opJAM = opDEC mAbx := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

set_option maxRecDepth 100000 in
theorem cyc_DE : (cycTable.get! (0xDE : UInt8).toNat).toNat = 7 := by decide

/-- **The abstract successors**: at `DEC abs,X` of the followed counter with the index known, `arkOpX`; else those of `PipeWrites.gsucc` -/
def gsuccX (G : Guard) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if A.rk && !A.nmi && decide (0x8000 ≤ A.pc) && isRkDecX E A then [((arkOpX E >>= fun _ => atick 7 7) { A with pc := A.pc + 1 }).map (·.2)]
  else gsucc G E ops A

/-- a step of the machine with the steps of `gsuccX`, if the instruction is not `DEC abs` of the counter (as `LagFrames.s_gsuccL`) -/
theorem s_gsuccX {G : Guard} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray)
    (hd : isRkDec E A.pc (opOf E A) = false) (hc : Clean G m) (hs : Sim E F A m) :
    ∃ r ∈ gsuccX G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold gsuccX
  by_cases h : (A.rk && !A.nmi && decide (0x8000 ≤ A.pc) && isRkDecX E A) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨⟨_, hn⟩, hp⟩, hx⟩ := h
    have hop : opOf E A = 0xDE := by
      simp only [isRkDecX, Bool.and_eq_true, beq_iff_eq] at hx
      exact hx.1.1.1.1
    refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
    have hn2 : m.nmiPending = false := by rw [hs.nmi]; exact hn
    have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
    rw [step_op hn2 hs.halted hpm]
    have hop2 : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xDE := by
      rw [hs.prg, hs.mask, hs.pc]
      exact hop
    rw [hop2]
    have e4C : ((0xDE : UInt8) == 0x4C) = false := by decide
    have estep : stepK m m.pc 0xDE = ((opTable[(0xDE : UInt8).toNat]?.getD opJAM) >>= fun _ => tick (cycTable.get! (0xDE : UInt8).toNat).toNat) := by
      unfold stepK
      simp only [e4C, Bool.false_and, Bool.false_eq_true, if_false]
    rw [estep, op_DE, cyc_DE]
    cases he : (arkOpX E >>= fun _ => atick 7 7) { A with pc := A.pc + 1 } with
    | none =>
      rw [he] at hB
      cases hB
    | some p =>
      rw [he] at hB
      obtain ⟨u, B1⟩ := p
      have hB1 : B1 = B := Option.some.inj hB
      subst hB1
      have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
        pc := by
          show m.pc + 1 = A.pc + 1
          rw [hs.pc] }
      obtain ⟨g1, g2, g3⟩ := snd_then_tick s_rkOpX hs1 he
      refine ⟨g1, steprel_same hs g1 g2 ?_⟩
      have g3' : m.fdot + 3 * 7 ≤ (go (opDEC mAbx >>= fun _ => tick 7) { m with pc := m.pc + 1 }).2.fdot := g3
      omega
  · rw [if_neg h]
    exact LagFrames.s_gsuccL hops hd hc hs

end

/-! ## The walk -/

/-- **The walk of the counter** from the frame's start to the cut: `CtrlKeep.walkR` with the steps of `gsuccX`. At the cut it asks only that the counter is followed
(it may have fallen by one); at the end of a frame that did not come to the cut, that it is followed and has not fallen (the paused frames skip the timers). No state
is at the move routine's store, and no step is `DEC abs` of the counter. -/
def walkX (C : CfgR) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => A.pc != C.q && (preL C.G A).all fun A₁ => !isRkDec C.E A₁.pc (opOf C.E A₁) && (gsuccX C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then
        (if B.pc == C.cut then B.rk else (C.tc.get! B.pc.toNat != 0 && coverR C B) || walkX C n B)
      else B.k == A.k + 1 && B.rk && !B.spent

/-- **The check of the counter's walk**, as `CtrlKeep.ctrlCheck1` -/
def check1X (C : CfgR) : Bool :=
  decide (C.G.late < dotsPerFrame) && C.cut != C.G.idle && C.t.all (walkX C fuelG) &&
    walkX C fuelG (startP C.G C.pz false false) && walkX C fuelG (startP C.G C.pz false true) &&
    walkX C fuelG (startP C.G C.pz true false) && walkX C fuelG (startP C.G C.pz true true)

section
variable {C : CfgR} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveX (C : CfgR) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkX C n A = true

theorem cover_liveX (ht : C.t.all (walkX C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverR C B = true) : ∃ D, LiveX C F D m := by
  unfold coverR at h
  split at h
  · rename_i i _
    split at h
    · rename_i D l e1 e2
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
      have hl : l = knownOf D := by
        rw [hkl] at e2
        rw [Array.getElem?_map, e1] at e2
        exact (Option.some.inj e2).symm
      rw [hl] at h
      have hle := leK_le h
      have hall := (Array.all_eq_true.1 ht) i hi
      rw [he] at hall
      have hDk : D.k = 0 := by
        have e3 := le_k hle
        omega
      exact ⟨D, sim_le hle hs, hDk, Fu, hall⟩
    · cases h
  · cases h

/-- one step: the walk goes on, or the machine comes to the cut with the counter followed, or the frame ends with the counter followed and not fallen -/
theorem live_stepX (ht : C.t.all (walkX C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveX C F A m) (hc : FrameKeep.CleanK C.G C.q m) :
    (∃ A', LiveX C F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ (go step m).2.pc ≠ C.cut ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame ∧ (go step m).2.pc = C.cut ∧ ∃ B, B.rk = true ∧ Sim C.E F B (go step m).2) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, B.rk = true ∧ B.spent = false ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkX] at hw
  | succ n =>
    simp only [walkX, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hw
    obtain ⟨hq, hw⟩ := hw
    have hc' : Clean C.G m := FrameKeep.clean_of hc (fun h => hq (hs.pc ▸ h.1))
    obtain ⟨A₁, hA, hs1, hk1⟩ := LagFrames.cov_preL hc' hs
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    have hd' : isRkDec C.E A₁.pc (opOf C.E A₁) = false := by simpa using hd
    obtain ⟨r, hr1, hB⟩ := s_gsuccX hops hd' hc' hs1
    have hw3 := hw2 r hr1
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · rw [if_pos (by simp [k1, hk1])] at hw3
        by_cases hcut : B.pc = C.cut
        · rw [if_pos (by simp [hcut])] at hw3
          exact Or.inr (Or.inl ⟨k2, by rw [h1.pc]; exact hcut, B, hw3, h1⟩)
        · rw [if_neg (by simp [hcut])] at hw3
          have hcut' : (go step m).2.pc ≠ C.cut := by rw [h1.pc]; exact hcut
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
          rcases hw3 with ⟨_, h4⟩ | h4
          · obtain ⟨D, hD⟩ := cover_liveX ht hkl h1 (by omega) h4
            exact Or.inl ⟨D, hD, k2, hcut', k3⟩
          · exact Or.inl ⟨B, ⟨h1, by omega, n, h4⟩, k2, hcut', k3⟩
      · rw [if_neg (by simp [k1, hk1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw3
        exact Or.inr (Or.inr ⟨k2, B, hw3.1.2, hw3.2, h1⟩)

/-- the instructions of the frame up to its first arrival at the cut -/
theorem frame_runX (ht : C.t.all (walkX C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) {M : Machine} {i : UInt8}
    (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace M i n)) {k : Nat} (hk : (trace M i k).pc = C.cut) (hf : (trace M i k).frame = M.frame)
    (hfirst : ∀ j, j < k → (trace M i j).pc ≠ C.cut) :
    ∀ (d j : Nat) (A : AS), j + d = k → LiveX C F A (trace M i j) → (trace M i j).frame = M.frame → (trace M i j).pc ≠ C.cut →
      ∃ B, B.rk = true ∧ Sim C.E F B (trace M i k) := by
  intro d
  induction d with
  | zero =>
    intro j A hj _ _ hp
    rw [Nat.add_zero] at hj
    rw [hj] at hp
    exact absurd hk hp
  | succ d ih =>
    intro j A hj hl hfj _
    have hh := hl.1.halted
    have e : trace M i (j + 1) = (go step (trace M i j)).2 := by
      show PipeEntryRule.nxt (M.frame + 1) (trace M i j) = _
      have hn : ¬ ((trace M i j).frame ≥ M.frame + 1 || (trace M i j).halted) = true := by simp [hfj, hh]
      simp only [PipeEntryRule.nxt, if_neg hn]
    rcases live_stepX ht hkl hops hl (hcl j) with ⟨A', h1, h2, h3, _⟩ | ⟨h1, h2, B, h3, h4⟩ | ⟨h1, _⟩
    · rw [← e] at h1 h2 h3
      exact ih (j + 1) A' (by omega) h1 (h2.trans hfj) h3
    · rw [← e] at h1 h2 h4
      have hjk : j + 1 = k := by
        by_cases h5 : j + 1 < k
        · exact absurd h2 (hfirst (j + 1) h5)
        · omega
      rw [← hjk]
      exact ⟨B, h3, h4⟩
    · rw [← e] at h1
      exfalso
      have hst : ((trace M i (j + 1)).frame ≥ M.frame + 1 || (trace M i (j + 1)).halted) = true := by simp [h1, hfj]
      have e2 := PipeEntryRule.trace_stop hst d
      rw [show j + 1 + d = k by omega] at e2
      rw [e2, h1, hfj] at hf
      omega

/-- what the check says -/
structure OKX (C : CfgR) : Prop where
  late : C.G.late < dotsPerFrame
  cutIdle : C.cut ≠ C.G.idle
  table : C.t.all (walkX C fuelG) = true
  s00 : walkX C fuelG (startP C.G C.pz false false) = true
  s01 : walkX C fuelG (startP C.G C.pz false true) = true
  s10 : walkX C fuelG (startP C.G C.pz true false) = true
  s11 : walkX C fuelG (startP C.G C.pz true true) = true

theorem okX_of_check (h : check1X C = true) : OKX C := by
  simp only [check1X, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- the walk starts: the state of the frame's start, with the counter followed and the low bit of the pause byte -/
theorem start_liveX (hO : check1X C = true) (hE : C.E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) :
    ∃ A, LiveX C (m.frame, m.ram.get! C.E.rkI) A (trace m i 0) := by
  have H := okX_of_check hO
  obtain ⟨b, hs⟩ := sim_startG hE h0
  have hs2 := LagFrames.sim_rk hs rfl
  have hs3 : Sim C.E (m.frame, m.ram.get! C.E.rkI) (startL C.G b) (trace m i 0) := { hs2 with pad := by rw [hE]; exact mem_top _ }
  have hs4 : Sim C.E (m.frame, m.ram.get! C.E.rkI) (startP C.G C.pz b (m.ram.get! C.pz &&& 1 != 0)) (trace m i 0) :=
    PipeEntryRule.sim_setK' hs3 (CtrlKeep.low_mem (m.ram.get! C.pz))
  generalize (m.ram.get! C.pz &&& 1 != 0) = p at hs4
  refine ⟨_, hs4, rfl, fuelG, ?_⟩
  cases b <;> cases p
  · exact H.s00
  · exact H.s01
  · exact H.s10
  · exact H.s11

/-- **The counter at the cut.** A frame from the idle loop in control whose instructions meet `CleanK` comes to the cut, the first time, in a state that the walk
covers with the counter followed: the counter is what it was at the frame's start, or one less. -/
theorem at_cutX (hO : check1X C = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hE : C.E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace m i n))
    {k : Nat} (hk : (trace m i k).pc = C.cut) (hf : (trace m i k).frame = m.frame) (hfirst : ∀ j, j < k → (trace m i j).pc ≠ C.cut) :
    (trace m i k).ram.get! C.E.rkI = m.ram.get! C.E.rkI ∨ (trace m i k).ram.get! C.E.rkI = m.ram.get! C.E.rkI - 1 := by
  have H := okX_of_check hO
  obtain ⟨A, hl⟩ := start_liveX hO hE h0 (i := i)
  have hp0 : (trace m i 0).pc ≠ C.cut := by
    show m.pc ≠ C.cut
    rw [h0.pc]
    exact fun h => H.cutIdle h.symm
  obtain ⟨B, hr, hs⟩ := frame_runX H.table hkl hops hcl hk hf hfirst k 0 A (by omega) hl rfl hp0
  have h1 := hs.rkv hr
  cases hsp : B.spent
  · rw [hsp] at h1
    exact Or.inl h1
  · rw [hsp] at h1
    exact Or.inr h1

/-- **A frame that does not come to the cut keeps the counter** (as `CtrlKeep.cut_or_end2`): a frame from the idle loop in control whose instructions meet `CleanK` and
that does not come to the cut ends in a state that the walk covers with the counter followed and not fallen. -/
theorem end_noCutX (hO : check1X C = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hE : C.E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ C.cut) : (frame m i).ram.get! C.E.rkI = m.ram.get! C.E.rkI := by
  have H := okX_of_check hO
  obtain ⟨A0, hl0⟩ := start_liveX hO hE h0 (i := i)
  have key : ∀ j, (∃ A, LiveX C (m.frame, m.ram.get! C.E.rkI) A (trace m i j) ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, B.rk = true ∧ B.spent = false ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (trace m i j)) := by
    intro j
    induction j with
    | zero =>
      refine Or.inl ⟨A0, hl0, rfl, ?_⟩
      show m.fdot + 3 * 0 ≤ m.fdot
      omega
    | succ j ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hn' : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by simp [h2, hh]
        have e : trace m i (j + 1) = (go step (trace m i j)).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i j) = _
          simp only [PipeEntryRule.nxt, if_neg hn']
        rcases live_stepX H.table hkl hops h1 (hcl j) with ⟨A', a1, a2, _, a4⟩ | ⟨a1, a2, _⟩ | ⟨a1, B, b1, b2, b3⟩
        · rw [← e] at a1 a2 a4
          exact Or.inl ⟨A', a1, a2.trans h2, by omega⟩
        · rw [← e] at a1 a2
          exact absurd a2 (hn (j + 1) (a1.trans h2))
        · rw [← e] at a1 b3
          exact Or.inr ⟨by rw [a1, h2], B, b1, b2, b3⟩
      · have hst : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by simp [h1]
        rw [PipeEntryRule.trace_stop hst 1]
        exact Or.inr ⟨h1, B, h2, h3, h4⟩
  rcases key fuelPerFrame with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, h3, h4⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · rw [← PipeEntryRule.frame_trace] at h4
    have h5 := h4.rkv h2
    rw [h3] at h5
    exact h5

end

/-! ## Finding the table: a search, no part of the proof (`CtrlKeep.runR`, `CtrlKeep.searchR` with the steps of `gsuccX`) -/

partial def runX (G : Guard) (E : Env) (ops : Array (AM Unit)) (cut : UInt16) (pz : Nat) (pw : Bool) (X0 : LagFrames.SL) (A0 : AS) : LagFrames.SL := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preL G cur).flatMap (gsuccX G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (fun r => r.isNone) then X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let same := (rs.filterMap id).filter fun b => b.k == cur.k
    X := { X with cuts := X.cuts + (same.filter fun b => b.pc == cut).length, ends := X.ends + ((rs.filterMap id).filter fun b => b.k != cur.k).length }
    let good := same.filter fun b => b.pc != cut
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := CtrlKeep.routeR G pz pw X b
    break
  return X

partial def searchX (G : Guard) (E : Env) (cut : UInt16) (pz : Nat) (pw : Bool) : LagFrames.SL := Id.run do
  let ops := (aRows E).toArray
  let mut X : LagFrames.SL := [startP G pz false false, startP G pz false true, startP G pz true false, startP G pz true true].foldl (CtrlKeep.routeR G pz pw) {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runX G E ops cut pz pw X A
  return X

/-! ## On the ROM -/

/-- the side collision's timer: the operand of the scroll handler's load of it -/
def sideI (sy : Syms) (m0 : Machine) : Nat := (ScrollRule.places sy m0).sideB

/-- the table of the counter's walk: states with other values of the pause byte are not joined (as `CtrlKeep.cutTable` with `pw`), so that a frame that skips the
timers as paused also skips the mode's routine -/
def sideTable (sy : Syms) (m0 : Machine) : Table :=
  let G := FrameKeep.guardK sy m0
  CtrlKeep.tableOfR G (CtrlKeep.pauseI sy m0) true (searchX G (envR m0 (sideI sy m0)) sy.PlayerCtrlRoutine (CtrlKeep.pauseI sy m0) true)

/-- **The check of the timer**: the walk of the counter from the frame's start to the player's routine -/
def sideCheck (sy : Syms) (m0 : Machine) : Bool := check1X (cfgOf sy m0 (sideTable sy m0) (sideI sy m0) true)

/-- the place byte, the scroll lock and the edge's two bytes -/
def startI (sy : Syms) (m0 : Machine) : List Nat :=
  [(ScrollRule.places sy m0).pfs, (ScrollRule.places sy m0).lockB, (ScrollRule.places sy m0).lx, (ScrollRule.places sy m0).lp]

/-- **The check of the four bytes**: a walk of `CtrlKeep` for each, with the table of `CtrlKeep.cutTable` -/
def keepCheck (sy : Syms) (m0 : Machine) : Bool :=
  let q := CtrlKeep.cutTable sy m0 false
  (startI sy m0).all fun b => CtrlKeep.ctrlCheck1 (cfgOf sy m0 q b false)

/-- **The side collision's timer at the player's routine.** A frame from the idle loop in control (`FrameKeep.StartK`) whose instructions meet `FrameKeep.CleanK`
comes to the player's routine at `k`, the first time. There the timer is that of the frame's start, or one less. -/
theorem side_at (hc : sideCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) {k : Nat}
    (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame)
    (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    (trace m i k).ram.get! (sideI sy m0) = m.ram.get! (sideI sy m0) ∨ (trace m i k).ram.get! (sideI sy m0) = m.ram.get! (sideI sy m0) - 1 :=
  at_cutX (C := cfgOf sy m0 (sideTable sy m0) (sideI sy m0) true) hc rfl rfl rfl (CtrlKeep.cfg_start _ _ true h0) hcl hk hf hfirst

theorem dec_le : ∀ n : Fin 256, (UInt8.ofNat n.val - 1 = 0) → UInt8.ofNat n.val ≤ 1 := by decide +kernel

/-- a byte that is 0 after a fall of at most one was at most 1 -/
theorem le_one_of {x y : UInt8} (h : y = x ∨ y = x - 1) (h0 : y = 0) : x ≤ 1 := by
  rcases h with h | h
  · rw [← h, h0]
    decide
  · rw [h0] at h
    have := dec_le ⟨x.toNat, x.toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at this
    exact this h.symm

/-- **A timer 0 at the player's routine was at most 1 at the frame's start** -/
theorem side_le (hc : sideCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) {k : Nat}
    (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame)
    (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) (hz : (trace m i k).ram.get! (sideI sy m0) = 0) :
    m.ram.get! (sideI sy m0) ≤ 1 :=
  le_one_of (side_at hc h0 hcl hk hf hfirst) hz

/-- **The four bytes at the player's routine**: the place byte, the scroll lock and the edge's two bytes are those of the frame's start -/
theorem keep_at (hc : keepCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) {k : Nat}
    (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame)
    (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) : ∀ x ∈ startI sy m0, (trace m i k).ram.get! x = m.ram.get! x := by
  intro b hb
  unfold keepCheck at hc
  obtain ⟨B, hB, hs⟩ := CtrlKeep.at_cut (C := cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) b false) ((List.all_eq_true.1 hc) b hb) rfl rfl rfl
    (CtrlKeep.cfg_start _ _ false h0) hcl hk hf hfirst
  simp only [CtrlKeep.atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB
  have h1 := hs.rkv hB.1.1.1.1.1.1
  rw [if_neg (by simp [hB.1.1.1.1.1.2])] at h1
  exact h1

/-- **A frame in control that does not come to the player's routine keeps the side collision's timer** (the paused frames skip the timers) -/
theorem side_noCut (hc : sideCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) : (frame m i).ram.get! (sideI sy m0) = m.ram.get! (sideI sy m0) :=
  end_noCutX (C := cfgOf sy m0 (sideTable sy m0) (sideI sy m0) true) hc rfl rfl rfl (CtrlKeep.cfg_start _ _ true h0) hcl hn

/-- **A frame in control that does not come to the player's routine keeps the four bytes** -/
theorem keep_noCut (hc : keepCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) : ∀ x ∈ startI sy m0, (frame m i).ram.get! x = m.ram.get! x := by
  intro b hb
  unfold keepCheck at hc
  rcases CtrlKeep.cut_or_end (C := cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) b false) ((List.all_eq_true.1 hc) b hb) rfl rfl rfl
    (CtrlKeep.cfg_start _ _ false h0) hcl with ⟨k, h1, h2, _, _⟩ | ⟨B, hB, hs⟩
  · exact absurd h1 (hn k h2)
  · simp only [CtrlKeep.endR, Bool.and_eq_true, Bool.not_eq_true'] at hB
    have h1 := hs.rkv hB.1.1
    rw [if_neg (by simp [hB.1.2])] at h1
    exact h1

/-- the bytes of `NearM` but the position: the side collision's timer and the four bytes of `startI` -/
def nearI (sy : Syms) (m0 : Machine) : List Nat := sideI sy m0 :: startI sy m0

/-! ## The condition at the frame's start -/

/-- **NearM(M)**, at the frame's start `M`: when the side collision's timer is at most 1, the scroll lock is 0 and his place on the screen is at least the scroll's
threshold, he is at least 2 px right of the screen's left edge -/
def NearM (sy : Syms) (P : ScrollRule.Places) (M : Machine) : Prop :=
  M.ram.get! P.sideB ≤ 1 → M.ram.get! P.lockB = 0 → P.thr1 ≤ M.ram.get! P.pfs → ScrollRule.left16 P M + 2 ≤ EdgeStep.pixel16 sy M

/-- **`NearM` at the frame's start gives `MoveScroll.NearA` at the first arrival at the player's routine**: a timer 0 there was at most 1 at the start (`side_le`), the
place byte, the lock and the edge are those of the start (`keep_at`), and so is the position (`CtrlKeep.ctrl_keep`) -/
theorem nearA_of_M (hs : sideCheck sy m0 = true) (hkc : keepCheck sy m0 = true) (hck : CtrlKeep.ctrlCheck sy m0 = true) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) {k : Nat}
    (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame)
    (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) (hM : NearM sy (ScrollRule.places sy m0) m) :
    MoveScroll.NearA sy (ScrollRule.places sy m0) (trace m i k) := by
  intro hz hl hp
  have kp := keep_at hkc h0 hcl hk hf hfirst
  have A := CtrlKeep.ctrl_keep hck h0 hcl hk hf hfirst
  have k1 : (trace m i k).ram.get! (ScrollRule.places sy m0).pfs = m.ram.get! (ScrollRule.places sy m0).pfs := kp _ (by simp [startI])
  have k2 : (trace m i k).ram.get! (ScrollRule.places sy m0).lockB = m.ram.get! (ScrollRule.places sy m0).lockB := kp _ (by simp [startI])
  have k3 : (trace m i k).ram.get! (ScrollRule.places sy m0).lx = m.ram.get! (ScrollRule.places sy m0).lx := kp _ (by simp [startI])
  have k4 : (trace m i k).ram.get! (ScrollRule.places sy m0).lp = m.ram.get! (ScrollRule.places sy m0).lp := kp _ (by simp [startI])
  have hx : peek (trace m i k) sy.Player_X_Position = peek m sy.Player_X_Position := A.keep _ (by simp [CtrlKeep.keepA])
  have hpg : peek (trace m i k) sy.Player_PageLoc = peek m sy.Player_PageLoc := A.keep _ (by simp [CtrlKeep.keepA])
  have hS := side_le hs h0 hcl hk hf hfirst hz
  have h := hM hS (by rw [← k2]; exact hl) (by rw [← k1]; exact hp)
  have eL : ScrollRule.left16 (ScrollRule.places sy m0) (trace m i k) = ScrollRule.left16 (ScrollRule.places sy m0) m := by
    unfold ScrollRule.left16
    rw [k3, k4]
  have eP : EdgeStep.pixel16 sy (trace m i k) = EdgeStep.pixel16 sy m := by
    unfold EdgeStep.pixel16
    rw [hx, hpg]
  rw [eL, eP]
  exact h

/-- **`NearM` on another machine with the same bytes**: the timer, the four bytes of `startI` and the position -/
theorem nearM_congr {m m' : Machine} (h : ∀ x ∈ nearI sy m0, m'.ram.get! x = m.ram.get! x)
    (hx : peek m' sy.Player_X_Position = peek m sy.Player_X_Position) (hp : peek m' sy.Player_PageLoc = peek m sy.Player_PageLoc)
    (hM : NearM sy (ScrollRule.places sy m0) m) : NearM sy (ScrollRule.places sy m0) m' := by
  intro h1 h2 h3
  have k0 : m'.ram.get! (ScrollRule.places sy m0).sideB = m.ram.get! (ScrollRule.places sy m0).sideB := h _ (by simp [nearI, sideI])
  have k1 : m'.ram.get! (ScrollRule.places sy m0).pfs = m.ram.get! (ScrollRule.places sy m0).pfs := h _ (by simp [nearI, startI])
  have k2 : m'.ram.get! (ScrollRule.places sy m0).lockB = m.ram.get! (ScrollRule.places sy m0).lockB := h _ (by simp [nearI, startI])
  have k3 : m'.ram.get! (ScrollRule.places sy m0).lx = m.ram.get! (ScrollRule.places sy m0).lx := h _ (by simp [nearI, startI])
  have k4 : m'.ram.get! (ScrollRule.places sy m0).lp = m.ram.get! (ScrollRule.places sy m0).lp := h _ (by simp [nearI, startI])
  have e := hM (by rw [← k0]; exact h1) (by rw [← k2]; exact h2) (by rw [← k1]; exact h3)
  have eL : ScrollRule.left16 (ScrollRule.places sy m0) m' = ScrollRule.left16 (ScrollRule.places sy m0) m := by
    unfold ScrollRule.left16
    rw [k3, k4]
  have eP : EdgeStep.pixel16 sy m' = EdgeStep.pixel16 sy m := by
    unfold EdgeStep.pixel16
    rw [hx, hp]
  rw [eL, eP]
  exact e

/-- **`NearM` from the edge and the position**: a machine with the program of `m0` that is at least 2 px and one fraction step right of the screen's left edge as a
position (`SurfaceRead.edgeOf`) meets `NearM`, whatever its other bytes -/
theorem nearM_of_edge {m : Machine} (hp : m.prg = m0.prg) (hk : m.prgMask = m0.prgMask) (h : SurfaceRead.edgeOf sy m + 257 ≤ posP sy m) :
    NearM sy (ScrollRule.places sy m0) m := by
  intro _ _ _
  rw [ScrollRule.edgeOf_left16 hp hk, FrameModel.posP_eq] at h
  unfold FrameModel.posOf at h
  have hf := (peek m sy.SprObject_X_MoveForce).toNat_lt
  unfold EdgeStep.pixel16
  omega

/-! ## A program: where the walk fails, no part of the proof -/

/-- the walk of `walkX`, returning where it fails first, and the path's last `pc`s -/
def whyX (C : CfgR) : Nat → List Nat → AS → Option (String × Nat × List Nat)
  | 0, path, A => some ("fuel", A.pc.toNat, path)
  | n + 1, path, A => Id.run do
    if A.pc == C.q then return some ("store", A.pc.toNat, path)
    for A₁ in preL C.G A do
      if isRkDec C.E A₁.pc (opOf C.E A₁) then return some ("dec", A₁.pc.toNat, path)
      for r in gsuccX C.G C.E C.ops A₁ do
        match r with
        | none => return some ("step", A₁.pc.toNat, path)
        | some B =>
          if A₁.rk && !B.rk then return some (s!"rkdrop x {A₁.x.v}/{A₁.x.k}", A₁.pc.toNat, path)
          if B.k == A.k then
            if B.pc == C.cut then
              if !B.rk then return some ("cut", A₁.pc.toNat, path)
            else if C.tc.get! B.pc.toNat != 0 && coverR C B then pure ()
            else
              match whyX C n ((A₁.pc.toNat :: path).take 40) B with
              | some w => return some w
              | none => pure ()
          else if B.k != A.k + 1 then return some ("end", A₁.pc.toNat, path)
          else if !(B.rk && !B.spent) then
            return some (s!"end rk {B.rk} spent {B.spent} pause {(B.getK C.pz).v}/{(B.getK C.pz).k}", A₁.pc.toNat, path)
    return none

/-- where the check of the timer fails: the table's states and the four starts -/
def whySide (sy : Syms) (m0 : Machine) : List (Nat × String × Nat × List Nat) :=
  let C := cfgOf sy m0 (sideTable sy m0) (sideI sy m0) true
  let starts := [startP C.G C.pz false false, startP C.G C.pz false true, startP C.G C.pz true false, startP C.G C.pz true true]
  let l := (C.t.toList ++ starts).zipIdx
  (l.filterMap fun (A, i) => (whyX C fuelG [] A).map fun w => (i, w)).take 6

end Smbrta.SideTimer
