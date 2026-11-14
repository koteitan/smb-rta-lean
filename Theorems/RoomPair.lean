import Theorems.RoomVert
import Theorems.RoomFall
import Theorems.RoomStart

/-!
# Two pairs of bytes through the room's frames

`RoomVert.air_frame` asks two things of the machine at the start of a frame: in a jump (the player's state 1) the jump's halt value is 1, and bit 7 of A of the frame
before is bit 7 of A. They were the fields `halt` and `prevA` of `RoomJoin.RoomRun`. Here they are theorems on every frame of the room before the entry.

Each is a relation `R x y` of two bytes. A walk of one whole frame of the room (the abstract machine of `RoomMap`, through `RoomVert.walkV`) marks each state: the mark `[]`
says that the relation holds on the machine, the mark `[1]` that it may not (`markP`). A step keeps the mark `[]` when it writes neither byte (`keepXY`); a step after which
every state that it gives knows enough bits of the two bytes to show the relation (`nextOK`) gets the mark `[]`; any other step from a state marked `[]` gets `[1]`.
At the frame's end the mark is `[]`, or the frame leaves the player's routine (`finP`). So a frame that starts with the relation and ends in the player's routine ends with it
(`pair_frame`).
* `halt`: the player's state and the jump's halt value. The jump stores the state 1 and then the halt value 1; the walk knows both values (`knHalt`).
* `prevA`: A of the frame before, and A. The game engine copies A there at its end with a load of A and a store. Before a load of A the walk splits the state on bit 7 of A
  (`splitLda`), so the store gives a known bit 7 to both (`knPrev`).

At the first control in the room the rows of the change know both pairs (`rowsCheck`, `pair_of_rows`). Then every frame of the room before the entry keeps them
(`pair_run`), with what `RoomMap` gives: each frame starts in the room's condition. No game data. Page: `1-1/c-7-5-2-RoomPair.md`.
-/

namespace Smbrta.RoomPair

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK PlacesOK CfgS RoomCond)
open RoomVert (Ph walkV OKV withBit I)

/-! ## The walk -/

/-- the step of `A` keeps the bytes `x` and `y`: the erase of a coin (it writes in the block buffers), or a step that does not store to them -/
def keepXY (E : Env) (P : Places) (x y : Nat) (A : AS) : Bool :=
  (A.pc == P.erase && !A.nmi) || StepWrites.keepOK E (fun i => i == x || i == y) A

/-- every state that the step of `A` gives knows enough bits of `x` and `y` to show the relation (`kn`) -/
def nextOK (E : Env) (P : Places) (ops : Array (AM Unit)) (kn : AB → AB → Bool) (x y : Nat) (A : AS) : Bool :=
  (RoomMap.stepT P E ops A).all fun r => match r with
    | some B => kn (B.getK x) (B.getK y)
    | none => false

/-- the mark of a piece before its step: `[]` the relation holds, `[1]` it may not -/
def markP (E : Env) (P : Places) (ops : Array (AM Unit)) (kn : AB → AB → Bool) (x y : Nat) (A : AS) : AS :=
  if nextOK E P ops kn x y A then { A with log := [], spent := false }
  else if A.log.isEmpty && !keepXY E P x y A then { A with log := [1] }
  else A

/-- the walk's pieces: those of `split`, marked -/
def phP (E : Env) (P : Places) (ops : Array (AM Unit)) (kn : AB → AB → Bool) (x y : Nat) (split : AS → List AS) : Ph where
  zone := fun A => (split A).map (markP E P ops kn x y)
  pre := fun _ => true
  ok := fun _ => true

/-- at the frame's end: the mark `[]`, or the routine byte is known and is not the reference's -/
def finP (P : Places) (r : Machine) (B : AS) : Bool :=
  B.log.isEmpty || (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI)

/-! ## The two relations -/

/-- the player's state is known not to be 1, or the jump's halt value is known to be 1 -/
def knHalt (bs bd : AB) : Bool := (1 &&& bs.k != bs.v &&& bs.k) || (bd.k == 0xFF && bd.v == 1)

/-- bit 7 of both bytes is known, and it is the same -/
def knPrev (bp ba : AB) : Bool := bp.k &&& 0x80 == 0x80 && ba.k &&& 0x80 == 0x80 && bp.v &&& 0x80 == ba.v &&& 0x80

/-- at a load of `y` from the zero page (`LDA zp`) followed by a store to `x` (`STA zp`), in a state marked `[1]` that does not know bit 7 of `y`: the two pieces with
that bit known. The bit `spent` is that bit, so that the search keeps the two pieces apart up to the store -/
def splitLda (E : Env) (x y : Nat) (A : AS) : List AS :=
  if !A.log.isEmpty && (A.getK y).k &&& 0x80 != 0x80 && E.prg.get! (A.pc &&& E.mask).toNat == 0xA5 &&
      (E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toNat == y && E.prg.get! ((A.pc + 2) &&& E.mask).toNat == 0x85 &&
      (E.prg.get! ((A.pc + 3) &&& E.mask).toNat).toNat == x then
    [{ A.setK y (withBit (A.getK y) 0x80 true) with spent := true }, { A.setK y (withBit (A.getK y) 0x80 false) with spent := false }]
  else [A]

theorem knHalt_spec {bs bd : AB} {s d : UInt8} (h : knHalt bs bd = true) (hs : bs.mem s) (hd : bd.mem d) : s = 1 → d = 1 := by
  intro e
  subst e
  simp only [knHalt, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact absurd hs h
  · have hk : bd.isK = true := by simp [AB.isK, h1]
    rw [isK_eq hk hd, h2]

theorem bit7_cases : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 ∨ UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel

theorem knPrev_spec {bp ba : AB} {p a : UInt8} (h : knPrev bp ba = true) (hp : bp.mem p) (ha : ba.mem a) : p &&& 0x80 = a &&& 0x80 := by
  simp only [knPrev, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [bit_eq hp h1, bit_eq ha h2, h3]

/-- the pieces of `splitLda` cover the state, with its mark and its counter -/
theorem splitLda_cover {E : Env} {F : Nat × UInt8} {x y : Nat} {A : AS} {m : Machine} (hy : y < 2048) (hr : A.rk = false) (hs : Sim E F A m) :
    ∃ A₁ ∈ splitLda E x y A, Sim E F A₁ m := by
  unfold splitLda
  split
  · have hm := hs.ram y hy
    rcases (RoomVert.u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) bit7_cases) (m.ram.get! y) with e | e
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl),
        RoomVert.sim_bits (PipeEntryRule.sim_setK' hs (RoomVert.withBit_false_of hm e)) hr false _⟩
    · exact ⟨_, List.mem_cons_self, RoomVert.sim_bits (PipeEntryRule.sim_setK' hs (RoomVert.withBit_true_of (by decide) hm e)) hr true _⟩
  · exact ⟨A, List.mem_singleton.2 rfl, hs⟩

theorem splitLda_keep {E : Env} {x y : Nat} {A A₁ : AS} (h : A₁ ∈ splitLda E x y A) : A₁.log = A.log ∧ A₁.rk = A.rk := by
  unfold splitLda at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · rw [List.mem_singleton.1 h]
    exact ⟨rfl, rfl⟩

/-! ## One frame -/

section
variable {E : Env} {P : Places} {ops : Array (AM Unit)} {kn : AB → AB → Bool} {x y : Nat} {split : AS → List AS} {R : UInt8 → UInt8 → Prop}
  {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat}

theorem markP_eq (A : AS) : markP E P ops kn x y A = { A with spent := (markP E P ops kn x y A).spent, log := (markP E P ops kn x y A).log } := by
  unfold markP
  split
  · rfl
  · split <;> rfl

theorem markP_rk (A : AS) : (markP E P ops kn x y A).rk = A.rk := by
  unfold markP
  split
  · rfl
  · split <;> rfl

/-- a step that `keepXY` allows keeps both bytes -/
theorem keepXY_step {F : Nat × UInt8} {A : AS} {m : Machine} (hO : PlacesOK E P) (hs : Sim E F A m) (hh : SiteOK P m) (hk : keepXY E P x y A = true)
    (hx : x < P.bufLo ∨ P.bufLo + P.bufN ≤ x) (hy : y < P.bufLo ∨ P.bufLo + P.bufN ≤ y) :
    (go step m).2.ram.get! x = m.ram.get! x ∧ (go step m).2.ram.get! y = m.ram.get! y := by
  unfold keepXY at hk
  cases hc : (A.pc == P.erase && !A.nmi) with
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    exact ⟨RoomVert.erase_keep hO hs hc.2 hc.1 hh hx, RoomVert.erase_keep hO hs hc.2 hc.1 hh hy⟩
  | false =>
    rw [hc, Bool.false_or] at hk
    exact ⟨StepWrites.keep_step hs hk x (by simp), StepWrites.keep_step hs hk y (by simp)⟩

/-- **One frame of the room keeps the relation.** The frame starts in the room's condition with the relation `R` of the bytes `x` and `y`, each instruction meets
`SiteOK`, and it ends in the player's routine. Then it ends with the relation. `h` is what the check of the walk gives, `hkn` says that `kn` shows `R`, the pieces of
`split` cover the state and keep its mark and counter, and `x`, `y` are out of the block buffers. -/
theorem pair_frame (h : OKV (phP E P ops kn x y split) E P r K C Fu) (hfin : C.fin = finP P r) (hops : ops = (aRows E).toArray)
    (hkn : ∀ (bx bw : AB) (u v : UInt8), kn bx bw = true → bx.mem u → bw.mem v → R u v)
    (hsp : ∀ (F : Nat × UInt8) (A : AS) (m : Machine), A.rk = false → Sim E F A m → ∃ A₁ ∈ split A, Sim E F A₁ m)
    (hsk : ∀ A A₁, A₁ ∈ split A → A₁.log = A.log ∧ A₁.rk = A.rk)
    (hx2 : x < 2048) (hy2 : y < 2048) (hx : x < P.bufLo ∨ P.bufLo + P.bufN ≤ x) (hy : y < P.bufLo ∨ P.bufLo + P.bufN ≤ y)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j))
    (h0 : R (m.ram.get! x) (m.ram.get! y)) (hrt : (frame m i).ram.get! P.rtI = r.ram.get! P.rtI) :
    R ((frame m i).ram.get! x) ((frame m i).ram.get! y) := by
  obtain ⟨S, hw, hs, _, s2, _⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hO' : PlacesOK E P := h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  let Φ : Nat → Bool → List Nat → Prop := fun j _ l => l.isEmpty = true → R ((trace m i j).ram.get! x) ((trace m i j).ram.get! y)
  have hz : ∀ (A' : AS) (z : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' z → ∃ A₁ ∈ (phP E P ops kn x y split).zone A', Sim C.E (m.frame, 2) A₁ z := by
    intro A' z hr hsz
    rw [h.env] at hsz ⊢
    obtain ⟨A₂, hA₂, hs₂⟩ := hsp _ A' z hr hsz
    have hr₂ : A₂.rk = false := by rw [(hsk A' A₂ hA₂).2]; exact hr
    refine ⟨markP E P ops kn x y A₂, List.mem_map.2 ⟨A₂, hA₂, rfl⟩, ?_⟩
    rw [markP_eq A₂]
    exact RoomVert.sim_bits hs₂ hr₂ _ _
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phP E P ops kn x y split).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phP E P ops kn x y split).ok A₁ = true →
      Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ hΦ hs' hf hr hA₁ hs₁ _ hl
    rw [h.env] at hs' hs₁
    obtain ⟨A₂, hA₂, rfl⟩ := List.mem_map.1 hA₁
    obtain ⟨hlg, hrk⟩ := hsk A' A₂ hA₂
    have hr₂ : A₂.rk = false := by rw [hrk]; exact hr
    -- the piece before its mark covers the machine
    have hs₂ : Sim E (m.frame, 2) A₂ (trace m i j) := by
      have e : A₂ = { markP E P ops kn x y A₂ with spent := A₂.spent, log := A₂.log } := by
        rw [markP_eq A₂]
      rw [e]
      exact RoomVert.sim_bits hs₁ (by rw [markP_rk]; exact hr₂) _ _
    have e2 := RoomVert.trace_succ hf hs'.halted
    show R ((trace m i (j + 1)).ram.get! x) ((trace m i (j + 1)).ram.get! y)
    rw [e2]
    by_cases hn : nextOK E P ops kn x y A₂ = true
    · obtain ⟨q, hq, hB⟩ := RoomMap.s_stepT hO' hops (by show 2 ≤ (2 : UInt8).toNat; decide) hs₂ (hk j)
      unfold nextOK at hn
      have hq2 := (List.all_eq_true.1 hn) q hq
      cases q with
      | none => cases hq2
      | some B =>
        obtain ⟨b1, _⟩ := hB B rfl
        exact hkn _ _ _ _ hq2 (b1.ram x hx2) (b1.ram y hy2)
    · have hn' : nextOK E P ops kn x y A₂ = false := by simpa using hn
      unfold markP at hl
      rw [if_neg (by rw [hn']; decide)] at hl
      by_cases hc : (A₂.log.isEmpty && !keepXY E P x y A₂) = true
      · rw [if_pos hc] at hl
        cases hl
      · rw [if_neg hc] at hl
        have hkp : keepXY E P x y A₂ = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          cases hk2 : keepXY E P x y A₂ with
          | true => rfl
          | false => exact absurd ⟨hl, hk2⟩ hc
        obtain ⟨k1, k2⟩ := keepXY_step hO' hs₂ (hk j) hkp hx hy
        rw [k1, k2]
        exact hΦ (by rw [← hlg]; exact hl)
  obtain ⟨_, J, _, _, hfr, B, hB, hsB, hΦB⟩ := RoomVert.frame_of_walkV (Z := phP E P ops kn x y split) Φ hO h.table h.ops
    (by show 2 ≤ (2 : UInt8).toNat; decide) (by rw [h.env]; exact h.pad) hz hw hs hk' (fun _ => by exact h0) hstep
  rw [hfin] at hB
  rw [h.env] at hsB
  rw [hfr]
  apply hΦB
  simp only [finP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB
  rcases hB with hB | ⟨⟨hlt, hK⟩, hne⟩
  · exact hB
  · exfalso
    have e := isK_eq hK (hsB.ram _ hlt)
    rw [← hfr, hrt] at e
    exact hne e.symm
end

/-! ## On the room -/

section
open ScreenPage (placesR envR refR aidsOf)

/-- the pieces of the halt walk: none -/
def phH (sy : Syms) (E : Env) (P : Places) (ops : Array (AM Unit)) : Ph := phP E P ops knHalt (I sy.Player_State) (I sy.DiffToHaltJump) (fun A => [A])

/-- the pieces of the walk of A: split at a load of A -/
def phA (sy : Syms) (E : Env) (P : Places) (ops : Array (AM Unit)) : Ph :=
  phP E P ops knPrev (I sy.PreviousA_B_Buttons) (I sy.A_B_Buttons) (splitLda E (I sy.PreviousA_B_Buttons) (I sy.A_B_Buttons))

/-- the configuration of the halt walk -/
abbrev cfgH (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phH sy (envR sy nm m0) (placesR sy nm m0) (aRows (envR sy nm m0)).toArray) (finP (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0)
    (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

/-- the configuration of the walk of A -/
abbrev cfgA (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phA sy (envR sy nm m0) (placesR sy nm m0) (aRows (envR sy nm m0)).toArray) (finP (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0)
    (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

/-- **The check on the ROM** of the halt walk -/
def checkH (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let E := envR sy nm m0
  let P := placesR sy nm m0
  RoomVert.walkCheckV sy (phH sy E P (aRows E).toArray) (finP P (refR m0)) P (aidsOf sy nm m0) E (refR m0) (RoomMap.knownT sy nm m0)

/-- **The check on the ROM** of the walk of A -/
def checkA (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let E := envR sy nm m0
  let P := placesR sy nm m0
  RoomVert.walkCheckV sy (phA sy E P (aRows E).toArray) (finP P (refR m0)) P (aidsOf sy nm m0) E (refR m0) (RoomMap.knownT sy nm m0)

/-- the four bytes are out of the block buffers -/
def apartP (sy : Syms) (P : Places) : Bool :=
  [I sy.Player_State, I sy.DiffToHaltJump, I sy.PreviousA_B_Buttons, I sy.A_B_Buttons].all fun x => decide (x < P.bufLo) || decide (P.bufLo + P.bufN ≤ x)

/-- the two relations on a machine -/
structure Pair (sy : Syms) (m : Machine) : Prop where
  halt : peek m sy.Player_State = 1 → peek m sy.DiffToHaltJump = 1
  prevA : peek m sy.PreviousA_B_Buttons &&& 0x80 = peek m sy.A_B_Buttons &&& 0x80

/-- the checks of the two walks -/
structure WalkChecks (sy : Syms) (nm : Names) (m0 : Machine) : Prop where
  halt : checkH sy nm m0 = true
  prev : checkA sy nm m0 = true
  apart : apartP sy (placesR sy nm m0) = true

variable {sy : Syms} {nm : Names} {m0 : Machine}

theorem apart_of (h : apartP sy (placesR sy nm m0) = true) :
    ∀ x ∈ [I sy.Player_State, I sy.DiffToHaltJump, I sy.PreviousA_B_Buttons, I sy.A_B_Buttons],
      x < (placesR sy nm m0).bufLo ∨ (placesR sy nm m0).bufLo + (placesR sy nm m0).bufN ≤ x := by
  intro x hx
  simp only [apartP, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h x hx

/-- **One frame of the room keeps both relations.** The frame starts in the room's condition with them, each instruction meets `SiteOK`, and it ends in the player's
routine. -/
theorem pair_step (hW : WalkChecks sy nm m0) {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0) m)
    (hk : ∀ j, SiteOK (placesR sy nm m0) (trace m i j)) (h0 : Pair sy m)
    (hrt : (frame m i).ram.get! (placesR sy nm m0).rtI = (refR m0).ram.get! (placesR sy nm m0).rtI) : Pair sy (frame m i) := by
  have ha := apart_of hW.apart
  have l1 : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have l2 : I sy.DiffToHaltJump < 2048 := PipeTransitionAll.mask_lt _
  have l3 : I sy.PreviousA_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  have l4 : I sy.A_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  refine ⟨?_, ?_⟩
  · exact pair_frame (R := fun s d => s = 1 → d = 1) (RoomVert.okV_of_check hW.halt) rfl rfl
      (fun _ _ _ _ hh a b => knHalt_spec hh a b)
      (fun _ A _ _ hs => ⟨A, List.mem_singleton.2 rfl, hs⟩)
      (fun _ _ hA => by rw [List.mem_singleton.1 hA]; exact ⟨rfl, rfl⟩)
      l1 l2 (ha _ (by simp)) (ha _ (by simp)) hm hk h0.halt hrt
  · exact pair_frame (R := fun p a => p &&& 0x80 = a &&& 0x80) (RoomVert.okV_of_check hW.prev) rfl rfl
      (fun _ _ _ _ hh a b => knPrev_spec hh a b)
      (fun _ _ _ hr hs => splitLda_cover l4 hr hs)
      (fun _ _ hA => splitLda_keep hA)
      l3 l4 (ha _ (by simp)) (ha _ (by simp)) hm hk h0.prevA hrt

end

/-! ## Two bytes, each on its own

The player's routine needs two more facts of the machine at its start: the player's state is 0, 1 or 2, and the change of size is 0. Each is a relation of one byte
(`x = y` in `pair_frame`), with its own walk. -/

/-- the player's state is known to be 0, 1 or 2: the bits above the low two are known 0, and one of the low two is known 0 -/
def knSt (b _ : AB) : Bool :=
  b.k &&& 0xFC == 0xFC && b.v &&& 0xFC == 0 && ((b.k &&& 1 == 1 && b.v &&& 1 == 0) || (b.k &&& 2 == 2 && b.v &&& 2 == 0))

/-- the byte is known to be 0 -/
def knZero (b _ : AB) : Bool := b.isK && b.v == 0

theorem st_low : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0xFC = 0 → (UInt8.ofNat n.val &&& 1 = 0 ∨ UInt8.ofNat n.val &&& 2 = 0) →
    UInt8.ofNat n.val = 0 ∨ UInt8.ofNat n.val = 1 ∨ UInt8.ofNat n.val = 2 := by decide +kernel

theorem knSt_spec {b b' : AB} {s : UInt8} (h : knSt b b' = true) (hs : b.mem s) : s = 0 ∨ s = 1 ∨ s = 2 := by
  simp only [knSt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e1 : s &&& 0xFC = 0 := by rw [bit_eq hs h1, h2]
  have e2 : s &&& 1 = 0 ∨ s &&& 2 = 0 := by
    rcases h3 with ⟨a, b2⟩ | ⟨a, b2⟩
    · exact Or.inl (by rw [bit_eq hs a, b2])
    · exact Or.inr (by rw [bit_eq hs a, b2])
  have := RoomVert.u8_all (P := fun t => t &&& 0xFC = 0 → (t &&& 1 = 0 ∨ t &&& 2 = 0) → t = 0 ∨ t = 1 ∨ t = 2) st_low s
  exact this e1 e2

theorem knZero_spec {b b' : AB} {s : UInt8} (h : knZero b b' = true) (hs : b.mem s) : s = 0 := by
  simp only [knZero, Bool.and_eq_true, beq_iff_eq] at h
  rw [isK_eq h.1 hs, h.2]

section
open ScreenPage (placesR envR refR aidsOf)

/-- the walk of the player's state -/
def phSt (sy : Syms) (E : Env) (P : Places) (ops : Array (AM Unit)) : Ph := phP E P ops knSt (I sy.Player_State) (I sy.Player_State) (fun A => [A])
/-- the walk of the change of size -/
def phSz (sy : Syms) (E : Env) (P : Places) (ops : Array (AM Unit)) : Ph :=
  phP E P ops knZero (I sy.PlayerChangeSizeFlag) (I sy.PlayerChangeSizeFlag) (fun A => [A])

/-- **The check on the ROM** of a walk with the pieces `Z` -/
def checkOf (sy : Syms) (nm : Names) (m0 : Machine) (Z : Env → Places → Array (AM Unit) → Ph) : Bool :=
  let E := envR sy nm m0
  let P := placesR sy nm m0
  RoomVert.walkCheckV sy (Z E P (aRows E).toArray) (finP P (refR m0)) P (aidsOf sy nm m0) E (refR m0) (RoomMap.knownT sy nm m0)

def checkSt (sy : Syms) (nm : Names) (m0 : Machine) : Bool := checkOf sy nm m0 (phSt sy)
def checkSz (sy : Syms) (nm : Names) (m0 : Machine) : Bool := checkOf sy nm m0 (phSz sy)

/-- the two bytes are out of the block buffers -/
def apartQ (sy : Syms) (P : Places) : Bool :=
  [I sy.Player_State, I sy.PlayerChangeSizeFlag].all fun x => decide (x < P.bufLo) || decide (P.bufLo + P.bufN ≤ x)

end

/-- the two facts on a machine -/
structure Quad (sy : Syms) (m : Machine) : Prop where
  st : peek m sy.Player_State = 0 ∨ peek m sy.Player_State = 1 ∨ peek m sy.Player_State = 2
  size : peek m sy.PlayerChangeSizeFlag = 0

/-- the checks of the two walks -/
structure QuadWalks (sy : Syms) (nm : Names) (m0 : Machine) : Prop where
  st : checkSt sy nm m0 = true
  size : checkSz sy nm m0 = true
  apart : apartQ sy (ScreenPage.placesR sy nm m0) = true

section
open ScreenPage (placesR envR refR)
variable {sy : Syms} {nm : Names} {m0 : Machine}

/-- **One frame of the room keeps both facts.** The frame starts in the room's condition with them, each instruction meets `SiteOK`, and it ends in the player's
routine. -/
theorem quad_step (hW : QuadWalks sy nm m0) {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0) m)
    (hk : ∀ j, SiteOK (placesR sy nm m0) (trace m i j)) (h0 : Quad sy m)
    (hrt : (frame m i).ram.get! (placesR sy nm m0).rtI = (refR m0).ram.get! (placesR sy nm m0).rtI) : Quad sy (frame m i) := by
  have ha : ∀ x ∈ [I sy.Player_State, I sy.PlayerChangeSizeFlag], x < (placesR sy nm m0).bufLo ∨ (placesR sy nm m0).bufLo + (placesR sy nm m0).bufN ≤ x := by
    intro x hx
    have h := hW.apart
    simp only [apartQ, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    exact h x hx
  have l1 : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have l2 : I sy.PlayerChangeSizeFlag < 2048 := PipeTransitionAll.mask_lt _
  refine ⟨?_, ?_⟩
  · exact pair_frame (R := fun s _ => s = 0 ∨ s = 1 ∨ s = 2) (RoomVert.okV_of_check hW.st) rfl rfl
      (fun _ _ _ _ hh a _ => knSt_spec hh a)
      (fun _ A _ _ hs => ⟨A, List.mem_singleton.2 rfl, hs⟩)
      (fun _ _ hA => by rw [List.mem_singleton.1 hA]; exact ⟨rfl, rfl⟩)
      l1 l1 (ha _ (by simp)) (ha _ (by simp)) hm hk h0.st hrt
  · exact pair_frame (R := fun z _ => z = 0) (RoomVert.okV_of_check hW.size) rfl rfl
      (fun _ _ _ _ hh a _ => knZero_spec hh a)
      (fun _ A _ _ hs => ⟨A, List.mem_singleton.2 rfl, hs⟩)
      (fun _ _ hA => by rw [List.mem_singleton.1 hA]; exact ⟨rfl, rfl⟩)
      l2 l2 (ha _ (by simp)) (ha _ (by simp)) hm hk h0.size hrt

end

/-! ## At the first control: from the rows of the change -/

section
open SideChangeEnd (Row Ctx InvL knowsAd mOf)
open PipeChangeEnd (Data timeCtx timeRows InRowsT)

/-- a state of a row: it says whether it has control, and if it has, it knows enough bits of the two pairs of bytes to show both relations -/
def rowP (sy : Syms) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || (knHalt (S.getK (I sy.Player_State)) (S.getK (I sy.DiffToHaltJump)) &&
      knPrev (S.getK (I sy.PreviousA_B_Buttons)) (S.getK (I sy.A_B_Buttons))))

/-- a state of a row: it says whether it has control, and if it has, it knows the player's state and the change of size enough to show `Quad` -/
def rowQ (sy : Syms) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || (knSt (S.getK (I sy.Player_State)) AB.top && knZero (S.getK (I sy.PlayerChangeSizeFlag)) AB.top))

/-- **The check on the ROM**: in the rows of the time of the change into the room, a machine with control has both relations, and the two facts of `Quad` -/
def rowsCheck (sy : Syms) (nm : Names) (d : Data) (e : Machine) : Bool :=
  (timeRows (timeCtx sy nm d e) d e).all fun w => w.R.all fun S => rowP sy S && rowQ sy S

variable {sy : Syms}

theorem pair_of_state {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowP sy S = true) (h : controllable sy m = true) : Pair sy m := by
  simp only [rowP, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨h1, h2⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · exact ⟨knHalt_spec h1 (hs.ram _ (PipeTransitionAll.mask_lt _)) (hs.ram _ (PipeTransitionAll.mask_lt _)),
      knPrev_spec h2 (hs.ram _ (PipeTransitionAll.mask_lt _)) (hs.ram _ (PipeTransitionAll.mask_lt _))⟩

theorem pair_of_invL {C : Ctx} : ∀ {l : List Row}, (l.all fun w => w.R.all fun S => rowP sy S && rowQ sy S) = true → ∀ {m : Machine}, InvL C l m →
    controllable sy m = true → Pair sy m
  | [], _, _, h, _ => by cases h
  | w :: t, hl, _, h, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact pair_of_state hs (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hl.1 S hS).1 hc
    · exact pair_of_invL hl.2 h hc

/-- **Both relations at the first control in the room**, for a machine with control in the rows of the time -/
theorem pair_of_rows {nm : Names} {d : Data} {e : Machine} (hc : rowsCheck sy nm d e = true) {m : Machine} (h : InRowsT sy nm d e m) (hm : controllable sy m = true) :
    Pair sy m :=
  pair_of_invL hc h hm

theorem quad_of_state {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowQ sy S = true) (h : controllable sy m = true) : Quad sy m := by
  simp only [rowQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨h1, h2⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · exact ⟨knSt_spec h1 (hs.ram _ (PipeTransitionAll.mask_lt _)), knZero_spec h2 (hs.ram _ (PipeTransitionAll.mask_lt _))⟩

theorem quad_of_invL {C : Ctx} : ∀ {l : List Row}, (l.all fun w => w.R.all fun S => rowP sy S && rowQ sy S) = true → ∀ {m : Machine}, InvL C l m →
    controllable sy m = true → Quad sy m
  | [], _, _, h, _ => by cases h
  | w :: t, hl, _, h, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact quad_of_state hs (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hl.1 S hS).2 hc
    · exact quad_of_invL hl.2 h hc

/-- **Both facts at the first control in the room**, for a machine with control in the rows of the time -/
theorem quad_of_rows {nm : Names} {d : Data} {e : Machine} (hc : rowsCheck sy nm d e = true) {m : Machine} (h : InRowsT sy nm d e m) (hm : controllable sy m = true) :
    Quad sy m :=
  quad_of_invL hc h hm

end

/-! ## Every frame of the room -/

section
open ScreenPage (placesR envR refR)
open PipeChangeEnd (Data InRowsT)

/-- what the room needs: the two walks and the rows -/
structure Checks (sy : Syms) (nmS : Names) (m0 : Machine) (nm : Names) (d : Data) : Prop where
  walks : WalkChecks sy nmS m0
  rows : rowsCheck sy nm d (PipeTransition.entry m0) = true

variable {sy : Syms} {nm nmS : Names} {d : Data} {m0 : Machine}

/-- **Both relations at the start of every frame of the room before the entry.** `seq` lists the frames of a run; frame `b` is the first control in the room, a machine
with control in the rows of the change; each frame before `a` meets `SiteOK` on each instruction and starts in the player's routine. The machine at the end of each frame
from `b` to `a` has both relations: in a jump the jump's halt value is 1, and bit 7 of A of the frame before is bit 7 of A. -/
theorem pair_run (hP : Checks sy nmS m0 nm d) (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → Pair sy (seq n) := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay
  have key : ∀ k, b + k < a → Pair sy (seq (b + k)) := by
    intro k
    induction k with
    | zero => exact fun _ => pair_of_rows hP.rows hin hctl
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hst := stay (b + k + 1) (by omega) hk
      rw [next] at hst
      rw [show b + (k + 1) = b + k + 1 by omega, next]
      exact pair_step hP.walks (hcond (b + k) (by omega) (by omega)) (sites (b + k) (by omega) (by omega)) h1 hst
  intro n h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, n = b + k := ⟨n - b, by omega⟩
  exact key k h2

/-- **The player's state is 0, 1 or 2 and the change of size is 0 at the start of every frame of the room before the entry**, under the conditions of `pair_run`.
`hQ` are the two walks, `hP` gives the rows -/
theorem quad_run (hQ : QuadWalks sy nmS m0) (hP : Checks sy nmS m0 nm d) (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → Quad sy (seq n) := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay
  have key : ∀ k, b + k < a → Quad sy (seq (b + k)) := by
    intro k
    induction k with
    | zero => exact fun _ => quad_of_rows hP.rows hin hctl
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hst := stay (b + k + 1) (by omega) hk
      rw [next] at hst
      rw [show b + (k + 1) = b + k + 1 by omega, next]
      exact quad_step hQ (hcond (b + k) (by omega) (by omega)) (sites (b + k) (by omega) (by omega)) h1 hst
  intro n h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, n = b + k := ⟨n - b, by omega⟩
  exact key k h2

/-- the checks of the room's walks: those of `RoomVert` and those of this file, and that the room's idle loop is a `JMP` to itself -/
structure RoomWalks (sy : Syms) (nmS : Names) (m0 : Machine) (h k : Nat) (nm : Names) (d : Data) : Prop where
  vert : RoomVert.VChecks sy nmS m0 h k
  /-- the walk from the scroll handler falling, and every state of the jumps from the floor (`RoomFall`) -/
  fall : RoomFall.FChecks sy nmS m0 h
  pair : Checks sy nmS m0 nm d
  quad : QuadWalks sy nmS m0
  idle : FrameModel.idleAt (FrameModel.Rom.of m0) (placesR sy nmS m0).idle = true

end

end Smbrta.RoomPair
