import Theorems.RoomVert

/-! # The speed after the end of the move, on a frame of the room (round 37)

After the end of the move (`PlayerSubs`) the player's collision routine and the scroll handler's clamp of the screen's edge may set the horizontal speed
`Player_X_Speed` to 0 (`ImpedePlayerMove`, `KeepOnscr`); nothing else writes it. Here a walk of one whole frame of the room (the abstract machine of `RoomMap`, as
`RoomAbsKeep`'s walk) checks that from `PlayerSubs` to the frame's end the speed is that of `PlayerSubs`, or 0.

The walk sets its bit on every state at `PlayerSubs` (`phV`). A state with the bit whose step may write the speed (`mayWriteV`) drops the bit and is marked `[1]`; such a
state must end the frame out of the player's routine, or with the speed known to be 0 (`finV`). The erase of a coin writes in the block buffers, which do not hold the
speed (`apartV`). So a frame of the room that comes to `PlayerSubs` and ends in the player's routine ends with the speed of `PlayerSubs`, or 0 (`after_QV`,
`speed_frame`). `RoomJoin.RoomRun.InRoom.speedAfter` is this on the real machines (`Route.Run.roomSpeed`).

There is no game data in this file. Page: `1-1/c-7-8-6-AirMove.md`.
-/

namespace Smbrta.RoomSpeedKeep

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop)
open ScreenPage (Places SiteOK PlacesOK CfgS RoomCond)
open RoomVert (Ph walkV OKV I sim_bits trace_succ start_of_room frame_of_walkV erase_keep)

/-- at the frame's end: a state whose speed may have been written after `PlayerSubs` ends out of the player's routine (the routine byte is known and is not the
reference's), or with the speed known to be 0 -/
def finV (sy : Syms) (P : Places) (r : Machine) (B : AS) : Bool :=
  B.log != [1] || (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI) ||
    ((B.getK (I sy.Player_X_Speed)).isK && (B.getK (I sy.Player_X_Speed)).v == 0)

/-- the step of `A` may write the speed: not the erase of a coin, which writes in the block buffers -/
def mayWriteV (sy : Syms) (E : Env) (P : Places) (A : AS) : Bool :=
  !(A.pc == P.erase && !A.nmi) && !StepWrites.keepOK E (fun i => i == I sy.Player_X_Speed) A

/-- the bit says that the frame came to the end of the move `PlayerSubs`, and that no step has written the speed since. A step that may write it drops the bit and
marks the state `[1]`. The walk asks that the frame comes to `PlayerSubs` once. -/
def phV (sy : Syms) (E : Env) (P : Places) : Ph where
  zone := fun A =>
    if A.pc == sy.PlayerSubs && !A.spent && A.log.isEmpty then [{ A with spent := true }]
    else if A.spent && mayWriteV sy E P A then [{ A with spent := false, log := [1] }]
    else [A]
  pre := fun A => !(A.pc == sy.PlayerSubs && (A.spent || !A.log.isEmpty))
  ok := fun A => !A.spent || !mayWriteV sy E P A

/-- the speed is not in the block buffers -/
def apartV (sy : Syms) (P : Places) : Bool :=
  decide (I sy.Player_X_Speed < P.bufLo) || decide (P.bufLo + P.bufN ≤ I sy.Player_X_Speed)

section
open ScreenPage (placesR envR refR aidsOf)

/-- the walk from the end of the move, on the room -/
abbrev cfgV (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phV sy (envR sy nm m0) (placesR sy nm m0)) (finV sy (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0)
    (refR m0) (RoomMap.knownT sy nm m0)

/-- the check of the walk from the end of the move -/
def checkV (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  RoomVert.walkCheckV sy (phV sy (envR sy nm m0) (placesR sy nm m0)) (finV sy (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0)
    (refR m0) (RoomMap.knownT sy nm m0)

/-- the search of the walk, for the program: the number of failures, the first failing state's address, the states at the frame's end, those of them marked `[1]`,
and those that `finV` refuses with the address of the first -/
def searchV (sy : Syms) (nm : Names) (m0 : Machine) : Nat × Option UInt16 × Nat × Nat × Nat × Option UInt16 :=
  let X := RoomVert.searchOfV sy (phV sy (envR sy nm m0) (placesR sy nm m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)
  let bad := X.ends.filter fun B => !finV sy (placesR sy nm m0) (refR m0) B
  (X.fails, X.firstFail.map (·.pc), X.ends.size, (X.ends.filter (·.log == [1])).size, bad.size, bad[0]?.map (·.pc))

end

/-- a state with the bit, that meets `ok`, keeps the speed over its step -/
theorem keepV_step {sy : Syms} {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {y : Machine} (hO : PlacesOK E P) (hap : apartV sy P = true)
    (hs : Sim E F A y) (hh : SiteOK P y) (hok : (phV sy E P).ok A = true) (hb : A.spent = true) :
    (go step y).2.ram.get! (I sy.Player_X_Speed) = y.ram.get! (I sy.Player_X_Speed) := by
  have h1 : mayWriteV sy E P A = false := by simpa [phV, hb] using hok
  unfold mayWriteV at h1
  cases hc : (A.pc == P.erase && !A.nmi) with
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    simp only [apartV, Bool.or_eq_true, decide_eq_true_eq] at hap
    exact erase_keep hO hs hc.2 hc.1 hh hap
  | false =>
    rw [hc] at h1
    simp only [Bool.not_false, Bool.true_and, Bool.not_eq_false'] at h1
    exact StepWrites.keep_step hs h1 _ (by simp)

/-- **The frame from the end of the move.** The frame comes to `PlayerSubs` at most once. If it comes there and ends in the player's routine, it ends with the speed of
`PlayerSubs`, or 0. The frame starts in the room's condition, and each instruction meets `SiteOK`. -/
theorem after_QV {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV (phV sy E P) E P r K C Fu)
    (hfin : C.fin = finV sy P r) (hap : apartV sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerSubs → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerSubs) ∧
    (∀ j, (trace m i j).pc = sy.PlayerSubs → (trace m i j).frame = m.frame → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       (frame m i).ram.get! (I sy.Player_X_Speed) = (trace m i j).ram.get! (I sy.Player_X_Speed) ∨ (frame m i).ram.get! (I sy.Player_X_Speed) = 0) := by
  obtain ⟨S, hw, hs, s1, s2, _⟩ := start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  let Φ : Nat → Bool → List Nat → Prop := fun j b l =>
    (∀ j₀, j₀ < j → (trace m i j₀).pc = sy.PlayerSubs → (b = true ∨ l ≠ [])) ∧
    (b = true → l = [] ∧ ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = sy.PlayerSubs ∧
      (trace m i j).ram.get! (I sy.Player_X_Speed) = (trace m i j₀).ram.get! (I sy.Player_X_Speed)) ∧
    (l = [] ∨ l = [1])
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phV sy E P).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    show ∃ A₁ ∈ (if A'.pc == sy.PlayerSubs && !A'.spent && A'.log.isEmpty then [{ A' with spent := true }]
      else if A'.spent && mayWriteV sy E P A' then [{ A' with spent := false, log := [1] }] else [A']), _
    split
    · exact ⟨_, List.mem_singleton.2 rfl, sim_bits hsx hr true A'.log⟩
    · split
      · exact ⟨_, List.mem_singleton.2 rfl, sim_bits hsx hr false [1]⟩
      · exact ⟨A', List.mem_singleton.2 rfl, hsx⟩
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phV sy E P).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phV sy E P).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2, p3⟩ hs' hf _ hA₁ hs₁ hok
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    have keep : A₁.spent = true → (trace m i (j + 1)).ram.get! (I sy.Player_X_Speed) = (trace m i j).ram.get! (I sy.Player_X_Speed) := by
      intro hb
      rw [trace_succ hf hs'.halted]
      have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
      exact keepV_step h.places hap hs₂ (hk j) hok hb
    change A₁ ∈ (if A'.pc == sy.PlayerSubs && !A'.spent && A'.log.isEmpty then [{ A' with spent := true }]
      else if A'.spent && mayWriteV sy E P A' then [{ A' with spent := false, log := [1] }] else [A']) at hA₁
    split at hA₁
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
      obtain ⟨⟨hq, _⟩, hlg⟩ := hc
      obtain rfl := List.mem_singleton.1 hA₁
      refine ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨hlg, j, by omega, by rw [hpc, hq], keep rfl⟩, Or.inl hlg⟩
    · rename_i hc
      split at hA₁
      · obtain rfl := List.mem_singleton.1 hA₁
        exact ⟨fun _ _ _ => Or.inr (by simp), fun h => by simp at h, Or.inr rfl⟩
      · obtain rfl := List.mem_singleton.1 hA₁
        refine ⟨fun j₀ hj₀ hq₀ => ?_, fun hb => ?_, p3⟩
        · rcases Nat.lt_or_ge j₀ j with hlt | hge
          · exact p1 j₀ hlt hq₀
          · rw [show j₀ = j by omega, hpc] at hq₀
            simp only [hq₀, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_and] at hc
            cases hsp : A₁.spent with
            | true => exact Or.inl rfl
            | false => exact Or.inr (hc hsp)
        · obtain ⟨l1, j₀, a1, a2, a3⟩ := p2 hb
          exact ⟨l1, j₀, by omega, a2, by rw [keep hb]; exact a3⟩
  have h0 : Φ 0 S.spent S.log := by
    refine ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun hb => ?_, Or.inl s2⟩
    rw [s1] at hb
    cases hb
  obtain ⟨hall, J, hJ1, hJ2, hJ3, B, hB1, hB2, hB3⟩ := frame_of_walkV (Z := phV sy E P) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0 hstep
  have uniq : ∀ j j', j < j' → (trace m i j).pc = sy.PlayerSubs → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerSubs := by
    intro j j' hlt hq hj' hq'
    obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = sy.PlayerSubs := by rw [← hsA.pc]; exact hq'
    simp only [phV, hApc, beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hpre
    rcases q1 j hlt hq with e | e
    · rw [hpre.1] at e
      cases e
    · exact e hpre.2
  refine ⟨uniq, fun jq hq hf hrt => ?_⟩
  have hjJ : jq < J := by
    rcases Nat.lt_or_ge jq J with h1 | h1
    · exact h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (jq - J)
      rw [show J + (jq - J) = jq by omega] at e
      rw [e, hJ1] at hf
      omega
  obtain ⟨q1, q2, q3⟩ := hB3
  have only : ∀ j₀, j₀ < J → (trace m i j₀).pc = sy.PlayerSubs → j₀ = jq := by
    intro j₀ h1 h2
    rcases Nat.lt_trichotomy j₀ jq with e | e | e
    · exact absurd hq (uniq j₀ jq e h2 hf)
    · exact e
    · exact absurd h2 (uniq jq j₀ e hq (hJ2 j₀ h1))
  rcases q3 with e | e
  · rcases q1 jq hjJ hq with e2 | e2
    · obtain ⟨_, j₀, a1, a2, a3⟩ := q2 e2
      rw [only j₀ a1 a2] at a3
      left
      rw [hJ3]
      exact a3
    · exact absurd e e2
  · -- marked `[1]`: the frame ends in the player's routine, so the walk knows the speed 0 there
    right
    rw [hfin] at hB1
    simp only [finV, e, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at hB1
    rcases hB1 with ⟨⟨a1, a2⟩, a3⟩ | ⟨a1, a2⟩
    · exfalso
      have e' := isK_eq a2 (hB2.ram _ a1)
      rw [← hJ3, hrt] at e'
      exact a3 e'.symm
    · have e' := isK_eq a1 (hB2.ram _ (FrameModel.I_lt _))
      rw [hJ3, e', a2]

/-- **A frame of the room that comes to the end of the move and ends in the player's routine ends with the speed of the end of the move, or 0**, and comes there once.
`after_QV` on the room's walk `checkV`. -/
theorem speed_frame {sy : Syms} {nm : Names} {m0 : Machine} (hcv : checkV sy nm m0 = true) (hap : apartV sy (ScreenPage.placesR sy nm m0) = true) {m : Machine}
    {input : UInt8} (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace m input j)) :
    (frame m input).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI →
      ∀ k, (trace m input k).pc = sy.PlayerSubs → (trace m input k).frame = m.frame →
      (frame m input).ram.get! (I sy.Player_X_Speed) = (trace m input k).ram.get! (I sy.Player_X_Speed) ∨ (frame m input).ram.get! (I sy.Player_X_Speed) = 0 := by
  obtain ⟨_, h2⟩ := after_QV (RoomVert.okV_of_check hcv) RoomVert.cfgOfV_fin hap hm sites
  exact fun hrt k hpc hf => h2 k hpc hf hrt

end Smbrta.RoomSpeedKeep
