import Theorems.PositionWriters

/-!
# Above ground: the order of the calls after the scroll handler

The walk of `PositionWriters` (`writers_end`) also follows whether the call of the scroll handler is open (`PositionWriters.Ph0`): the stack is at least two bytes
below the stack at the scroll handler `Q` (`FrameModel.ctrlStack`, the stack at the player's routine), and the two bytes that the call at `Q` pushed are still those
of its return address. The walk asks, at each of its states and steps (`okW`, `walkKW`, with `phK` and `phN`, what it knows of `Ph0`):

* at the clamp's entry (`ScreenClamp.places`) the call is open, and the stack is two bytes below that at `Q` (`AtW.phC`);
* at the push's entry (`ImpedePlayerMove`) the call is not open (`AtW.phI`);
* a step into a machine where the call is open comes from one where it is open, or from `Q` (`FrameW.ph`).

So the machines of the frame where the call is open come right after `Q`, one after another (`ph_down`). Every clamp's entry comes before every push's entry
(`clamp_before_push`), and once the stack is back two bytes above a clamp's entry (where the clamp returns, `ScreenClamp.clamp_return`), no clamp's entry comes
(`clamp_once`). The number of pushes is not bounded here. No game data. Page: `1-1/e-2-10-3-9-PositionOrder.md`.
-/

namespace Smbrta.PositionOrder

section
variable {sy : Syms} {m0 : Machine}

/-- **The call stays open back to the scroll handler**: if it is open at `n > q`, it is open at every `j` with `q < j ≤ n` -/
theorem ph_down {w : List UInt16} {s0 : UInt8} {T : Nat → Machine} {q f : Nat} (F : PositionWriters.FrameW sy m0 w s0 T q f) :
    ∀ d n, q + d < n → (∀ j, q ≤ j → j ≤ n → (T j).frame = f) → PositionWriters.Ph0 (FrameModel.ctrlStack sy m0) (PositionWriters.phQ sy m0) (T n) →
      PositionWriters.Ph0 (FrameModel.ctrlStack sy m0) (PositionWriters.phQ sy m0) (T (n - d))
  | 0, n, _, _, h => by simpa using h
  | d + 1, n, hd, live, h => by
    have ih := ph_down F d n (by omega) live h
    have e : n - d = (n - (d + 1)) + 1 := by omega
    rw [e] at ih
    rcases F.ph (n - (d + 1)) (by omega) (live _ (by omega) (by omega)) ih with h2 | h2
    · exact h2
    · omega

/-- **Every clamp comes before every push**: in the frame from the scroll handler `q`, an instruction at the clamp's entry comes before an instruction at the
push's entry -/
theorem clamp_before_push {w : List UInt16} {s0 : UInt8} {T : Nat → Machine} {q f : Nat} (F : PositionWriters.FrameW sy m0 w s0 T q f)
    (hq : (T q).pc = sy.PlayerSubs) (hne : sy.PlayerSubs ≠ sy.ImpedePlayerMove) (hic : sy.ImpedePlayerMove ≠ (ScreenClamp.places sy m0).entry)
    {a a' : Nat} (hqa : q ≤ a) (hqa' : q ≤ a') (live : ∀ j, q ≤ j → j ≤ a → (T j).frame = f) (live' : (T a').frame = f)
    (hc : (T a).pc = (ScreenClamp.places sy m0).entry) (hi : (T a').pc = sy.ImpedePlayerMove) : a < a' := by
  rcases Nat.lt_or_ge a a' with h | h
  · exact h
  · exfalso
    have hA := (F.atW a hqa (live a hqa (Nat.le_refl _))).phC hc
    have hB := (F.atW a' hqa' live').phI hi
    rcases Nat.lt_or_ge q a' with h2 | h2
    · have hd := ph_down F (a - a') a (by
        rcases Nat.lt_or_ge a' a with h3 | h3
        · omega
        · exfalso
          have e : a' = a := by omega
          rw [e, hc] at hi
          exact hic hi.symm) live hA.1
      rw [show a - (a - a') = a' by omega] at hd
      exact hB hd
    · have e : a' = q := by omega
      rw [e, hq] at hi
      exact hne hi

theorem two_add_one (x : UInt8) : x + 1 + 1 = x + 2 := by rw [UInt8.add_assoc]; rfl

theorem ph_le_all : ∀ n : Fin 256, ¬ (UInt8.ofNat n.val).toNat + 2 ≤ (UInt8.ofNat n.val).toNat := by decide +kernel

/-- **After the clamp has returned, no clamp comes**: a clamp's entry at `a`, and at `b' > a` the stack two bytes above that of `a` (where the clamp returns); then no
instruction of the frame from `b'` on is at the clamp's entry -/
theorem clamp_once {w : List UInt16} {s0 : UInt8} {T : Nat → Machine} {q f : Nat} (F : PositionWriters.FrameW sy m0 w s0 T q f)
    {a b' a₂ : Nat} (hqa : q ≤ a) (hab : a < b') (live : ∀ j, q ≤ j → j ≤ a₂ → (T j).frame = f)
    (hc : (T a).pc = (ScreenClamp.places sy m0).entry) (hs : (T b').s = (T a).s + 1 + 1) (hb2 : b' ≤ a₂) :
    (T a₂).pc ≠ (ScreenClamp.places sy m0).entry := by
  intro hc2
  have hA := (F.atW a hqa (live a hqa (by omega))).phC hc
  have hA2 := (F.atW a₂ (by omega) (live a₂ (by omega) (Nat.le_refl _))).phC hc2
  have hd := ph_down F (a₂ - b') a₂ (by omega) live hA2.1
  rw [show a₂ - (a₂ - b') = b' by omega] at hd
  have h1 := hd.1
  rw [hs, two_add_one, hA.2] at h1
  exact ph_le_all ⟨(FrameModel.ctrlStack sy m0).toNat, (FrameModel.ctrlStack sy m0).toNat_lt⟩ (by simpa using h1)


/-- a piece that starts at the clamp's entry is a clamp: it ends with the stack two bytes up -/
theorem edge_clamp_ret {T : Nat → Machine} {a c : Nat} {e : Int} (h : PositionDispatch.Edge sy m0 T a c e) (hc : (T a).pc = (ScreenClamp.places sy m0).entry)
    (hic : sy.ImpedePlayerMove ≠ (ScreenClamp.places sy m0).entry) : (T c).s = (T a).s + 1 + 1 := by
  cases h with
  | ordinary _ nc _ _ => exact absurd hc nc
  | impede _ en _ _ _ => rw [hc] at en; exact absurd en.symm hic
  | clamp _ _ _ st _ => exact st

/-- **In a chain of pieces from the scroll handler, one clamp at most, and every push after it**: the cuts of a chain (`PositionDispatch.Chain.cuts`) from a cut
`a ≥ q` to the frame's end `b`; a cut at the clamp's entry comes before every cut at the push's entry, and it is the only cut at the clamp's entry -/
theorem chain_order {w : List UInt16} {s0 : UInt8} {T : Nat → Machine} {q b f : Nat} (F : PositionWriters.FrameW sy m0 w s0 T q f)
    (hq : (T q).pc = sy.PlayerSubs) (hne : sy.PlayerSubs ≠ sy.ImpedePlayerMove) (hic : sy.ImpedePlayerMove ≠ (ScreenClamp.places sy m0).entry)
    (live : ∀ j, q ≤ j → j < b → (T j).frame = f) {a : Nat} {es : List Int} (ch : PositionDispatch.Chain sy m0 T a b es) (hqa : q ≤ a) :
    ∃ cuts : Nat → Nat, cuts 0 = a ∧ cuts es.length = b ∧ (∀ j, j < es.length → PositionDispatch.Edge sy m0 T (cuts j) (cuts (j + 1)) es[j]!) ∧
      ∀ i j, i < es.length → j < es.length → (T (cuts i)).pc = (ScreenClamp.places sy m0).entry →
        ((T (cuts j)).pc = sy.ImpedePlayerMove → i < j) ∧ ((T (cuts j)).pc = (ScreenClamp.places sy m0).entry → i = j) := by
  obtain ⟨cuts, h0, hn, he⟩ := ch.cuts
  have step : ∀ j, j < es.length → cuts j < cuts (j + 1) := fun j hj => (he j hj).forward
  have mono : ∀ i j, i < j → j ≤ es.length → cuts i < cuts j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_or_ge i j with h | h
      · have := ih h (by omega)
        have := step j (by omega)
        omega
      · have e : i = j := by omega
        subst e
        exact step i (by omega)
  have ge : ∀ i, i ≤ es.length → a ≤ cuts i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with e | e
    · rw [e, h0]
      exact Nat.le_refl a
    · have := mono 0 i e hi
      omega
  have lt : ∀ i, i < es.length → cuts i < b := by
    intro i hi
    have := mono i es.length hi (Nat.le_refl _)
    omega
  -- a cut at the clamp's entry: its piece is a clamp, which returns with the stack two bytes up
  have ret : ∀ i, i < es.length → (T (cuts i)).pc = (ScreenClamp.places sy m0).entry → (T (cuts (i + 1))).s = (T (cuts i)).s + 1 + 1 := by
    intro i hi hc
    exact edge_clamp_ret (he i hi) hc hic
  refine ⟨cuts, h0, hn, he, fun i j hi hj hc => ⟨fun hp => ?_, fun hc2 => ?_⟩⟩
  · have := clamp_before_push F hq hne hic (by have := ge i (by omega); omega) (by have := ge j (by omega); omega)
      (fun k h1 h2 => live k h1 (by have := lt i hi; omega)) (live _ (by have := ge j (by omega); omega) (lt j hj)) hc hp
    rcases Nat.lt_or_ge i j with h | h
    · exact h
    · rcases Nat.lt_or_ge j i with h2 | h2
      · have := mono j i h2 (by omega); omega
      · have e : i = j := by omega
        subst e
        rw [hc] at hp
        exact absurd hp.symm hic
  · rcases Nat.lt_trichotomy i j with h | h | h
    · exfalso
      have hle : i + 1 ≤ j := h
      have h3 : cuts (i + 1) ≤ cuts j := by
        rcases Nat.lt_or_ge (i + 1) j with h4 | h4
        · exact Nat.le_of_lt (mono (i + 1) j h4 (by omega))
        · have e : i + 1 = j := by omega
          rw [e]
          exact Nat.le_refl _
      exact clamp_once F (by have := ge i (by omega); omega) (step i hi)
        (fun k h1 h2 => live k h1 (by have := lt j hj; omega)) hc (ret i hi hc) h3 hc2
    · exact h
    · exfalso
      have h3 : cuts (j + 1) ≤ cuts i := by
        rcases Nat.lt_or_ge (j + 1) i with h4 | h4
        · exact Nat.le_of_lt (mono (j + 1) i h4 (by omega))
        · have e : j + 1 = i := by omega
          rw [e]
          exact Nat.le_refl _
      exact clamp_once F (by have := ge j (by omega); omega) (step j hj)
        (fun k h1 h2 => live k h1 (by have := lt i hi; omega)) hc2 (ret j hj hc2) h3 hc

end

end Smbrta.PositionOrder
