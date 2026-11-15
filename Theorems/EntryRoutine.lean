import Theorems.SideEntryRest

/-!
# The routine at the side pipe's entry

`Route.ChangesBase.entry₂` asked the routine byte at the side pipe's entry (`Base.a₂`, the first frame from the room's first control on that has left the player's routine)
to be the side pipe's. Here it is proved from the room's entering frame. The walk of `SideEntryRest` asks at every step that once the routine byte is the side pipe's it stays so
(`SideEntryRest.okT`); `SideEntryRest.rest_end` uses it inside its proof. `rest_rt` is the same induction with that conclusion: a frame of the room that makes the routine
byte the side pipe's ends with it (`rt_of_rows`, on the real machines, with the walk of `SideEntryEnd` for the hypothesis at the write).

There is no game data in this file. Page: `1-1/d-2-5-2-EntryRoutine.md`.
-/

namespace Smbrta.EntryRoutine

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open SideChangeBound
open TaintRun
open PipeEntryRule (trace frame_trace trace_stop nxt)
open ScreenPage (SiteOK PlacesOK RoomCond startsR)
open SideEntryRest (SideP okS HypW LiveP RestOK live_stepP restCheck sidePOf restOK_of_check clean_E start_E)

/-- **The rest of the entering frame keeps the side pipe's routine.** Under the hypotheses of `SideEntryRest.rest_end`: if an instruction makes the routine byte the side
pipe's, the routine byte is the side pipe's at the frame's end. The proof is that of `rest_end`, with the routine byte in place of the position at the end. -/
theorem rest_rt {S : SideP} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : ScreenPage.CfgS} (h : RestOK S E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j))
    (hw : ∀ j, (∀ k, k ≤ j → (trace m i k).ram.get! S.rtI ≠ S.ev) → HypW S (trace m i j))
    (he : ∃ n, (trace m i n).ram.get! S.rtI ≠ S.ev ∧ (trace m i (n + 1)).ram.get! S.rtI = S.ev) :
    (frame m i).ram.get! S.rtI = S.ev := by
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hs0 : Sim C.E (m.frame, 2) S0 { m with pad := smbToPad i } := by
    rw [h.env]
    exact { hs with pad := by rw [h.pad]; exact mem_top _ }
  have hT : 2 ≤ (m.frame, (2 : UInt8)).2.toNat := by show 2 ≤ (2 : UInt8).toNat; decide
  -- the invariant of `rest_end`: covered by a live state in the frame, or the frame has ended in a state that passes `okS`; and the routine byte stays the side pipe's
  have key : ∀ j, ((∃ A, LiveP S C (m.frame, 2) A (trace m i j) ∧ A.k = S0.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, okS S B = true ∧ Sim C.E (m.frame, 2) B (trace m i j))) ∧
      (∀ k, k ≤ j → (trace m i k).ram.get! S.rtI = S.ev → (trace m i j).ram.get! S.rtI = S.ev) := by
    intro j
    induction j with
    | zero =>
      refine ⟨Or.inl ⟨S0, ⟨hs0, ScreenPage.fuelS, h.starts S0 hS⟩, rfl, rfl, Nat.le_refl _⟩, fun k hk0 he0 => ?_⟩
      have : k = 0 := by omega
      subst this
      exact he0
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      have hwj : HypW S (trace m i j) := by
        by_cases hb : ∀ k, k ≤ j → (trace m i k).ram.get! S.rtI ≠ S.ev
        · exact hw j hb
        · intro _ hne
          apply absurd _ hne
          have : ∃ k, k ≤ j ∧ (trace m i k).ram.get! S.rtI = S.ev :=
            Classical.byContradiction fun hn => hb (fun k hk he' => hn ⟨k, hk, he'⟩)
          obtain ⟨k, hk1, hk2⟩ := this
          exact ih2 k hk1 hk2
      rcases ih1 with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hk' (j + 1)
        rw [e2] at hh2 ⊢
        obtain ⟨hst, hper⟩ := live_stepP hO h.pl h.rt h.right h.table h.ops hT h1 (hk' j) hh2 hwj
        refine ⟨?_, fun k hk1 hk2 => ?_⟩
        · rcases hst with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, _, a4⟩
          · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
          · exact Or.inr ⟨by rw [a1, h3], B, a2, a4⟩
        · by_cases hkj : k ≤ j
          · exact hper (ih2 k hkj hk2)
          · have : k = j + 1 := by omega
            subst this
            rw [e2] at hk2
            exact hk2
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        refine ⟨Or.inr ⟨h1, B, h2, h4⟩, fun k hk1 hk2 => ?_⟩
        by_cases hkj : k ≤ j
        · exact ih2 k hkj hk2
        · have : k = j + 1 := by omega
          subst this
          rw [e2] at hk2
          exact hk2
  -- at `fuelPerFrame` the frame has ended
  have hend : (trace m i fuelPerFrame).frame = m.frame + 1 := by
    rcases (key fuelPerFrame).1 with ⟨A, h1, _, _, h4⟩ | ⟨h1, _⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact h1
  obtain ⟨n, _, hn2⟩ := he
  have hstop : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by
    simp [hend]
  have e3 : trace m i (fuelPerFrame + (n + 1)) = trace m i fuelPerFrame := trace_stop hstop (n + 1)
  have hev : (trace m i fuelPerFrame).ram.get! S.rtI = S.ev := by
    rw [← e3]
    exact (key (fuelPerFrame + (n + 1))).2 (n + 1) (by omega) hn2
  rw [frame_trace]
  exact hev

section
open ScreenPage (placesR envR refR)
open PipeChangeEnd (Data InRowsT)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **The routine at the end of the entering frame, on the real machines.** A frame of the room (from `b` to `a`, under the conditions of `RoomMap.map_of_rows`) that writes the
side pipe's routine ends with the side pipe's routine. `SideEntryEnd` gives the position at the first write (the hypothesis of the second walk), `rest_rt` carries the routine
byte to the frame's end. The hypotheses are those of `SideEntryRest.mouth_of_rows`; `hc`, `hs`, `hA`, `hB` and `hF` are checks on the ROM. -/
theorem rt_of_rows (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hs : RoomMap.startCheckF sy nmS m0 = true)
    (hA : SideEntryEnd.sideEntryEndCheck sy m0 = true) (hB : restCheck sy nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    {k : Nat} (h1 : b ≤ k) (h2 : k < a) (hen : SideEntryRule.Enters sy (seq k) (inp k)) :
    (frame (seq k) (inp k)).ram.get! (placesR sy nmS m0).rtI = (placesR sy nmS m0).eng := by
  simp only [SideEntryEnd.sideEntryEndCheck, Bool.and_eq_true] at hA
  -- the first write, by the walk of `SideEntryEnd`
  have hw := SideEntryEnd.write_right_of_left (S := SideEntryEnd.sideOfE sy m0) (E := PipeEntryRule.envOf m0) hA.2 rfl
    (start_E (RoomMap.start_of_rowsF hF hc hs next hin hctl sites stay k h1 h2))
    (fun j => ⟨clean_E (RoomMap.clean_of_rows hF hc next hin hctl sites stay k h1 h2 j),
      (RoomMap.map_of_rows hF hc next hin hctl sites stay).2 k h1 h2 j, by
        show (trace (seq k) (inp k) j).pc ∉ [PipeWrites.headAt sy m0, SideFrame.bumpAt sy m0]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨RoomMap.head_of_rows hF hc next hin hctl sites stay k h1 h2 j, RoomMap.bump_of_rows hF hc next hin hctl sites stay k h1 h2 j⟩⟩)
  -- the rest of the frame, by the walk of the room
  have hcond := (RoomMap.map_run hF.ok next (RoomMap.start_of_rows hc hin hctl) sites stay).1 k h1 h2
  obtain ⟨n, hn⟩ := hen
  exact rest_rt (S := sidePOf sy nmS m0) (restOK_of_check hB) hcond (sites k h1 h2) (fun j hb hpc hne => hw j hb hpc) ⟨n, hn.1, hn.2⟩

end

end Smbrta.EntryRoutine
