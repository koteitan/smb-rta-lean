import Theorems.EraseSplit

/-!
# The row of the coin's erase: the player's height split in the collision routine

Round 31 (`EraseSplit`) split the state before the add of the block buffer's low byte, so that at the coin's erase (`STA (zp),Y`) the walk knows the pointer's
low byte. For a pointer into the first block buffer every `Y` keeps the erase inside the block buffers. For a pointer into the second block buffer the erase needs
`Y` (the row's offset, `(y + adder) & 0xF0 − 32`) at most 192; the walk did not know `Y`, since it did not know the player's height `y`.

The player's collision routine tests `y` before each call of the block buffer routine (at the start, before the head's call, before the feet's, before each side's).
Here the walk (`splitR2`)

* splits the state where the routine first loads `y` (`yAt`) into nine pieces of `y` whose known bits decide every test (`splitY`, `ySteps`), by bit 0 of the
  size and by the crouch byte's lowest set bit (`zsplitL`), so that the head's upper extent (read from a table by the size and the crouch) is known;
* splits the accumulator (that is, `y`) before the add of the row's adder (`adcY`, the `ADC abs,Y` of the block buffer routine; `EraseSplit.splitK`), so that the
  row's offset is known;
* keeps round 31's split before the add of the buffer's low byte (`EraseSplit.adcAt`).

The walk with any split function `sp` that covers every machine (`Cov`) and keeps the flag of the counter's fall (`SpentKeep`) is `walkG`; `frameG` is its frame
theorem, with the same conclusions as `EraseSplit.frameK`. The search that finds the table (no part of the proof: the walk checks it) keeps the pieces apart while
`y`'s high bits are known (`rowKey`), keeps the block buffer routine's adder offset through the routine's checks (`aidsR`), forgets `y` at the routine's return and
after the erase and the size and the crouch byte after the head's test (`forgetAt`, `normR`), and runs the pieces of the row's add on to the place where they meet
(`passAt`, `advR`). `LoopTime` gives the walks the size's bits 1 to 7 at each frame's start.

There is no game data in this file. Page: `1-1/d-2-4-2-6-EraseRow.md`.
-/

namespace Smbrta.EraseRow

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken coverS startsR)
open RoomPause (Reg pstep Ph InCls)
open RoomLate (LateS sclamp sim_sclamp sclamp_k sclamp_spent)
open EraseSplit (SpentKeep splitK cov_splitK spent_splitK spent_allBits)

/-! ## The split -/

theorem spent_splitBit (d : Nat) (b : UInt8) : SpentKeep (splitBit d b) := by
  intro A B hB
  unfold splitBit at hB
  split at hB
  · rw [List.mem_singleton.1 hB]
  · rcases List.mem_cons.1 hB with e | e
    · subst e; rfl
    · rw [List.mem_singleton.1 e]; rfl

/-- **The byte `d` by its lowest set bit** among `bs`: a piece for each bit of `bs` that may be the lowest set one (the bits before it 0), and a piece with all bits
of `bs` 0. So in each piece it is known whether the byte is 0 (if `bs` holds all eight bits) -/
def zsplitL (d : Nat) : List UInt8 → AS → List AS
  | [], A => [A]
  | b :: bs, A =>
    match (A.getK d).bit b with
    | some true => [A]
    | some false => zsplitL d bs A
    | none => A.setK d ((A.getK d).or (AB.known b)) :: zsplitL d bs (A.setK d ((A.getK d).and (AB.known (~~~b))))

theorem cov_zsplitL {E : Env} {F : Nat × UInt8} {d : Nat} (hd : d < 2048) : ∀ (bs : List UInt8), (∀ b ∈ bs, b ∈ bitList) → Cov E F (zsplitL d bs)
  | [], _ => fun A _ hs => ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | b :: bs, hb => by
    intro A m hs
    have hbs : ∀ x ∈ bs, x ∈ bitList := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hbit := cov_bit (E := E) (F := F) hd (hb b List.mem_cons_self) A m hs
    unfold splitBit at hbit
    cases e : (A.getK d).bit b with
    | some t =>
      cases t with
      | true =>
        simp only [zsplitL, e]
        exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
      | false =>
        simp only [zsplitL, e]
        exact cov_zsplitL hd bs hbs A m hs
    | none =>
      rw [e] at hbit
      simp only [zsplitL, e]
      obtain ⟨B, hB, h1, h2⟩ := hbit
      rcases List.mem_cons.1 hB with e1 | e1
      · subst e1
        exact ⟨_, List.mem_cons_self, h1, h2⟩
      · rw [List.mem_singleton.1 e1] at h1 h2
        obtain ⟨C, hC, h3, h4⟩ := cov_zsplitL hd bs hbs _ m h1
        exact ⟨C, List.mem_cons_of_mem _ hC, h3, h4.trans h2⟩

theorem spent_zsplitL (d : Nat) : ∀ (bs : List UInt8), SpentKeep (zsplitL d bs)
  | [] => fun A B hB => by rw [List.mem_singleton.1 hB]
  | b :: bs => by
    intro A B hB
    cases e : (A.getK d).bit b with
    | some t =>
      cases t with
      | true =>
        simp only [zsplitL, e] at hB
        rw [List.mem_singleton.1 hB]
      | false =>
        simp only [zsplitL, e] at hB
        exact spent_zsplitL d bs A B hB
    | none =>
      simp only [zsplitL, e] at hB
      rcases List.mem_cons.1 hB with e1 | e1
      · subst e1; rfl
      · exact (spent_zsplitL d bs _ B e1).trans rfl

/-- the byte `d` by its bit `b`, when its bits `mask` are known with the values `val` -/
def splitIf (d : Nat) (mask val b : UInt8) (A : AS) : List AS :=
  if (A.getK d).k &&& mask == mask && (A.getK d).v &&& mask == val then splitBit d b A else [A]

/-- the steps of the height's split: bits 7 and 6; bit 5 when they are 00 or 11; bit 4 when bits 7 to 5 are 000 or 110; bit 3 when bits 7 to 4 are 0000. So the
pieces are the heights 0–7, 8–15, 16–31, 32–63, 64–127, 128–191, 192–207, 208–223, 224–255 -/
def ySteps : List (UInt8 × UInt8 × UInt8) :=
  [(0, 0, 0x80), (0, 0, 0x40), (0xC0, 0x00, 0x20), (0xC0, 0xC0, 0x20), (0xE0, 0x00, 0x10), (0xE0, 0xC0, 0x10), (0xF0, 0x00, 0x08)]

/-- **The height's split** -/
def splitY (d : Nat) (A : AS) : List AS := ySteps.foldl (fun l q => l.flatMap (splitIf d q.1 q.2.1 q.2.2)) [A]

theorem cov_splitIf {E : Env} {F : Nat × UInt8} {d : Nat} (hd : d < 2048) {mask val b : UInt8} (hb : b ∈ bitList) : Cov E F (splitIf d mask val b) := by
  intro A m hs
  unfold splitIf
  split
  · exact cov_bit hd hb A m hs
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem spent_splitIf (d : Nat) (mask val b : UInt8) : SpentKeep (splitIf d mask val b) := by
  intro A B hB
  unfold splitIf at hB
  split at hB
  · exact spent_splitBit d b A B hB
  · rw [List.mem_singleton.1 hB]

theorem cov_splitY {E : Env} {F : Nat × UInt8} {d : Nat} (hd : d < 2048) : Cov E F (splitY d) := by
  intro A m hs
  unfold splitY
  have key : ∀ (L : List (UInt8 × UInt8 × UInt8)) (l : List AS), (∀ q ∈ L, q.2.2 ∈ bitList) → (∃ B ∈ l, Sim E F B m ∧ B.k = A.k) →
      ∃ B ∈ L.foldl (fun l q => l.flatMap (splitIf d q.1 q.2.1 q.2.2)) l, Sim E F B m ∧ B.k = A.k := by
    intro L
    induction L with
    | nil => exact fun l _ h => h
    | cons q L ih =>
      intro l hL h
      exact ih _ (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (cov_flat (cov_splitIf hd (hL q List.mem_cons_self)) h)
  exact key _ _ (by decide) ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem spent_splitY (d : Nat) : SpentKeep (splitY d) := by
  intro A
  unfold splitY
  have key : ∀ (L : List (UInt8 × UInt8 × UInt8)) (l : List AS), (∀ C ∈ l, C.spent = A.spent) →
      ∀ B ∈ L.foldl (fun l q => l.flatMap (splitIf d q.1 q.2.1 q.2.2)) l, B.spent = A.spent := by
    intro L
    induction L with
    | nil => exact fun l h => h
    | cons q L ih =>
      intro l hl
      apply ih
      intro C hC
      obtain ⟨C0, h0, h1⟩ := List.mem_flatMap.1 hC
      rw [spent_splitIf d _ _ _ C0 C h1]
      exact hl C0 h0
  exact key _ [A] (fun C hC => by rw [List.mem_singleton.1 hC])

/-- **The split** (round 32, second form): at `pcY` the height `yI` (`splitY`), bit 0 of the size byte `sI`, and the crouch byte `cI` by its lowest set bit; at
`pcA` and at `pc0` the accumulator and `Y` by their bits (`EraseSplit.splitK`) -/
def splitR2 (pcY : UInt16) (yI sI cI : Nat) (pcA pc0 : UInt16) (A : AS) : List AS :=
  ((if A.pc == pcY then ((splitY yI A).flatMap (splitBit sI 1)).flatMap (zsplitL cI bitList) else [A]).flatMap (splitK pcA)).flatMap (splitK pc0)

theorem cov_splitR2 {E : Env} {F : Nat × UInt8} {pcY pcA pc0 : UInt16} {yI sI cI : Nat} (hy : yI < 2048) (hs : sI < 2048) (hc : cI < 2048) :
    Cov E F (splitR2 pcY yI sI cI pcA pc0) := by
  intro A m hm
  unfold splitR2
  have h1 : ∃ B ∈ (if A.pc == pcY then ((splitY yI A).flatMap (splitBit sI 1)).flatMap (zsplitL cI bitList) else [A]), Sim E F B m ∧ B.k = A.k := by
    split
    · exact cov_flat (cov_zsplitL hc bitList (fun b hb => hb)) (cov_flat (cov_bit hs (by decide)) (cov_splitY hy A m hm))
    · exact ⟨A, List.mem_singleton.2 rfl, hm, rfl⟩
  exact cov_flat (cov_splitK pc0) (cov_flat (cov_splitK pcA) h1)

theorem spent_splitR2 (pcY : UInt16) (yI sI cI : Nat) (pcA pc0 : UInt16) : SpentKeep (splitR2 pcY yI sI cI pcA pc0) := by
  intro A B hB
  unfold splitR2 at hB
  obtain ⟨C1, h1, h2⟩ := List.mem_flatMap.1 hB
  obtain ⟨C0, h0, h3⟩ := List.mem_flatMap.1 h1
  rw [spent_splitK pc0 C1 B h2, spent_splitK pcA C0 C1 h3]
  split at h0
  · obtain ⟨D1, h4, h5⟩ := List.mem_flatMap.1 h0
    obtain ⟨D0, h6, h7⟩ := List.mem_flatMap.1 h4
    rw [spent_zsplitL cI bitList D1 C0 h5, spent_splitBit sI 1 D0 D1 h7, spent_splitY yI A D0 h6]
  · rw [List.mem_singleton.1 h0]

/-! ## The walk with a split before each step -/

section
variable {G : Reg} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8} {sq : UInt16 → Bool} {D : Nat} {sp : AS → List AS}

/-- `EraseSplit.walkK` with any split `sp` before each step -/
def walkG (sp : AS → List AS) (G : Reg) (C : CfgS) (chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => chk (sclamp sq D A) && ((sp (sclamp sq D A)).flatMap (pstep C.P C.E C.ops G)).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (sclamp sq D (weaken C B))) || walkG sp G C chk sq D n (weaken C B)
      else B.k == A.k + 1 && C.fin B && chk B

/-- `A` covers `m` with `Ph`, and a walk from `A` succeeds -/
def LiveG (sp : AS → List AS) (G : Reg) (C : CfgS) (chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ Ph G A m ∧ ∃ n, walkG sp G C chk sq D n A = true

theorem chkG_of_walk {n : Nat} {A : AS} (h : walkG sp G C chk sq D n A = true) : chk (sclamp sq D A) = true := by
  cases n with
  | zero => simp [walkG] at h
  | succ n =>
    simp only [walkG, Bool.and_eq_true] at h
    exact h.1

theorem cover_liveG (ht : C.t.all (walkG sp G C chk sq D Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph G B m) (h : coverS C B = true) :
    ∃ D', LiveG sp G C chk sq D F D' m ∧ D'.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D' e
    have hle : B.le D' = true := h2
    have hk : D'.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D', ⟨sim_le hle hs, RoomPause.ph_of_spent (StepWrites.le_pc_spent hle).2 hp, Fu, hall⟩, hk⟩
  · cases h2

/-- **One step of the walk**, as `EraseSplit.live_stepK`, for a split that covers and keeps the counter's flag -/
theorem live_stepG (hcv : Cov C.E F sp) (hsk : SpentKeep sp) {R : Machine → Prop}
    (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkG sp G C chk sq D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine} (hl : LiveG sp G C chk sq D F A m)
    (hr : R m) (hl2 : LateS sq D (go step m).2) :
    (∃ A', LiveG sp G C chk sq D F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph G B (go step m).2) := by
  obtain ⟨hs, hp, n, hw⟩ := hl
  cases n with
  | zero => simp [walkG] at hw
  | succ n =>
    have hs1 : Sim C.E F (sclamp sq D A) m := sim_sclamp hD hs (hS hr)
    have hp1 : Ph G (sclamp sq D A) m := RoomPause.ph_of_spent (sclamp_spent sq D A).symm hp
    have hh : SiteOK C.P m := hQ hs1 (chkG_of_walk hw) hr
    obtain ⟨A2, hA2, hs2, hk2⟩ := hcv _ m hs1
    have hp2 : Ph G A2 m := RoomPause.ph_of_spent (hsk _ A2 hA2).symm hp1
    obtain ⟨r, hr', hB⟩ := RoomPause.s_pstep hO hops hT h0 hg hkb hs2 hh hp2
    simp only [walkG, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 r (List.mem_flatMap.2 ⟨A2, hA2, hr'⟩)
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨g1, g2, g3⟩ := hB B rfl
      dsimp only at hw2
      rcases g2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk2, sclamp_k] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        obtain ⟨n1, n2, n3⟩ := RoomPause.weaken_of (C := C) g1
        have hpW : Ph G (weaken C B) (go step m).2 := RoomPause.ph_of_spent n3.symm g3
        rcases hw2 with ⟨_, h3⟩ | h3
        · have hpC : Ph G (sclamp sq D (weaken C B)) (go step m).2 := RoomPause.ph_of_spent (sclamp_spent sq D _).symm hpW
          obtain ⟨D', hD', hk⟩ := cover_liveG ht (sim_sclamp hD n1 hl2) hpC h3
          exact ⟨D', hD', by rw [hk, sclamp_k, n2, k1], k2, k3⟩
        · exact ⟨_, ⟨n1, hpW, n, h3⟩, by rw [n2, k1], k2, k3⟩
      · right
        rw [hk2, sclamp_k] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.2, hw2.2, k1, g1, g3⟩

/-- **One frame**, as `EraseSplit.frame_of_walkK`, for the walk with the split `sp` -/
theorem frame_of_walkG (hcv : Cov C.E F sp) (hsk : SpentKeep sp) {R : Machine → Prop}
    (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkG sp G C chk sq D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkG sp G C chk sq D Fu S = true) (hs : Sim C.E F S m) (hph : Ph G S m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteOK C.P (trace m i j)) ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have key : ∀ j, (∃ A, LiveG sp G C chk sq D F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j) ∧ Ph G B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, hph0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h3, h4, h5⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hS (hk (j + 1))
        rw [e2] at hh2 ⊢
        rcases live_stepG hcv hsk hQ hS hD hO ht hops hT h0 hg hkb h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a5⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', by rw [a3, h2], a4, a5⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h3, h4, h5⟩
  refine ⟨fun j => ?_, ?_⟩
  · rcases key j with ⟨A, ⟨h1, _, n, h1'⟩, _, _, _⟩ | ⟨_, B, _, h2', _, h4, _⟩
    · exact hQ (sim_sclamp hD h1 (hS (hk j))) (chkG_of_walk h1') (hk j)
    · exact hQ h4 h2' (hk j)
  · rw [frame_trace]
    rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨_, B, h2, _, _, h4, _⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨B, h2, h4⟩

end

/-! ## Finding the table: a search with the split, the key and the forgetting, no part of the proof, and the check -/

section
open ScreenPage (SearchS)

/-- the search's key: `RoomPause.keyP`, and what `kb` picks -/
def keyR (Z : Aids) (E : Env) (kb : AS → Nat) (A : AS) : Nat := RoomPause.keyP Z E A * 4294967296 + kb A

/-- what the search forgets: that of `Z`, and at each program counter of `fy` its bytes -/
def normR (Z : Aids) (fy : List (UInt16 × List Nat)) (A : AS) : AS :=
  (fy.filter (·.1 == A.pc)).foldl (fun C q => q.2.foldl (fun C i => C.setK i AB.top) C) (Z.norm A)

/-- `EraseSplit.routeK` with `normR` and `keyR` -/
def routeR (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (E : Env) (kb : AS → Nat) (sq : UInt16 → Bool) (D : Nat) (X : SearchS) (B0 : AS) :
    SearchS :=
  let B := sclamp sq D (clampS P (normR Z fy B0))
  let K := keyR Z E kb B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D' =>
    if B.le D' then X else
    let J := D'.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 && sq J.pc then { J with hi := D } else J
    RoomPause.putP { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => RoomPause.putP { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

/-- a piece after a split, run on while it is at one of the program counters `ad` and has one successor (at most `n` steps): so the pieces are put into the
table only where they meet again -/
partial def advR (sp : AS → List AS) (P : Places) (E : Env) (ops : Array (AM Unit)) (G : Reg) (sq : UInt16 → Bool) (D : Nat) (ad : List UInt16) (n : Nat)
    (b : AS) : AS :=
  if n == 0 || !ad.contains b.pc then b else
  match ((sp (sclamp sq D b)).flatMap (pstep P E ops G)).filterMap id with
  | [c] => if c.k == b.k then advR sp P E ops G sq D ad (n - 1) c else b
  | _ => b

/-- `EraseSplit.runK` with the split `sp`; a run also stops at the program counters `fy`; a piece at a program counter of `ad` is run on (`advR`) -/
partial def runR (sp : AS → List AS) (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16) (E : Env) (kb : AS → Nat) (ops : Array (AM Unit))
    (G : Reg) (sq : UInt16 → Bool) (D : Nat) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (sp (sclamp sq D cur)).flatMap (pstep P E ops G)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (Z.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          !fy.any (·.1 == b.pc) && (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b0 in good do
      if b0.k != cur.k then X := { X with ends := X.ends.push b0 }
      else
        let b := if good.length ≥ 2 then advR sp P E ops G sq D ad 8 b0 else b0
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeR P Z fy E kb sq D X b
    break
  return X

/-- `EraseSplit.searchK` with `runR` -/
partial def searchR (sp : AS → List AS) (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16) (E : Env) (kb : AS → Nat)
    (ops : Array (AM Unit)) (G : Reg) (sq : UInt16 → Bool) (D : Nat) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := keyR Z E kb A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runR sp P Z fy ad E kb ops G sq D X A
  return X

/-- `EraseSplit.searchBK` with `searchR` -/
def searchBR (sp : AS → List AS) (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16) (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16)
    (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (sq : UInt16 → Bool) (D : Nat) : SearchS :=
  let Z := RoomPause.aidsP Z G
  let ops := (aRows E).toArray
  let S0 := RK.flatMap fun q => startsR q.1 q.2
  let S := match pre with
    | some fpc => (S0.flatMap (BufferRecords.preWalk P E ops G fpc)).map (BufferRecords.forgetL fz)
    | none => S0
  searchR sp P Z fy ad E kb ops G sq D (S.foldl (routeR P Z fy E kb sq D) {})

/-- the table of `searchBR`, as `EraseSplit.cfgBK`, with the key `keyR` and the forgetting `normR` -/
def cfgBR (sp : AS → List AS) (P : Places) (Z0 : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16) (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16)
    (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin : AS → Bool) (sq : UInt16 → Bool) (D : Nat) : CfgS :=
  let Z := RoomPause.aidsP Z0 G
  let X := searchBR sp P Z0 fy ad E kb G pre fz RK sq D
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      match acc with
      | (arr, hm, ba) =>
        let i := arr.size
        let l := hm.getD e.1 []
        (arr.push e.2, hm.insert e.1 (i :: l), ba.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ pre.toList ++ fy.map (·.1)).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin, t := q.1, key := keyR Z E kb, idx := q.2.1, cut := q.2.2,
    norm := fun A => if pre == some A.pc then BufferRecords.forgetL fz (normR Z fy A) else normR Z fy A, normAt := at0 }

/-- **The check of the walk with the split `sp`**, as `EraseSplit.walkCheckK` -/
def walkCheckR (sp : AS → List AS) (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16) (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16)
    (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) : Bool :=
  let C := cfgBR sp P Z fy ad E kb G pre fz RK fin sq D
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && StepWrites.tabOK G.SB G.T && decide (G.gI < 2048) &&
    G.keepB.all (fun p => decide (p.1 < 2048)) && decide (D < dotsPerFrame) && C.t.all (walkG sp G C chk sq D ScreenPage.fuelS) &&
    RK.all (fun q => ScreenPage.maskOK q.1 q.2 && (startsR q.1 q.2).all (walkG sp G C chk sq D ScreenPage.fuelS))

/-- what the check says -/
structure GOK (sp : AS → List AS) (E : Env) (P : Places) (G : Reg) (RK : List (Machine × List (Nat × UInt8))) (C : CfgS) (fin chk : AS → Bool)
    (sq : UInt16 → Bool) (D : Nat) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = fin
  tab : StepWrites.tabOK G.SB G.T = true
  gI : G.gI < 2048
  keepI : ∀ p ∈ G.keepB, p.1 < 2048
  dD : D < dotsPerFrame
  table : C.t.all (walkG sp G C chk sq D ScreenPage.fuelS) = true
  starts : ∀ q ∈ RK, ScreenPage.MaskOK q.1 q.2 ∧ ∀ S ∈ startsR q.1 q.2, walkG sp G C chk sq D ScreenPage.fuelS S = true

theorem gok_of_check {sp : AS → List AS} {P : Places} {Z : Aids} {fy : List (UInt16 × List Nat)} {ad : List UInt16} {E : Env} {kb : AS → Nat} {G : Reg}
    {pre : Option UInt16} {fz : List Nat} {RK : List (Machine × List (Nat × UInt8))} {fin chk : AS → Bool} {sq : UInt16 → Bool} {D : Nat}
    (h : walkCheckR sp P Z fy ad E kb G pre fz RK fin chk sq D = true) :
    GOK sp E P G RK (cfgBR sp P Z fy ad E kb G pre fz RK fin sq D) fin chk sq D := by
  simp only [walkCheckR, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h4⟩, h5⟩, hkb⟩, hD⟩, h6⟩, h7⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  refine ⟨ScreenPage.placesOK_spec h1, hp, rfl, rfl, rfl, rfl, h4, h5, fun p hp => hkb p hp, hD, h6, ?_⟩
  intro q hq
  have := h7 q hq
  exact ⟨ScreenPage.maskOK_spec this.1, fun S hS => this.2 S hS⟩

end

/-- **One frame of the room from a reference of `RK`**, as `EraseSplit.frameK`, for the walk with a split `sp` that covers every machine and keeps the counter's
flag -/
theorem frameG {sp : AS → List AS} {E : Env} {P : Places} {G : Reg} {RK : List (Machine × List (Nat × UInt8))} {C : CfgS} {fin chk : AS → Bool}
    {sq : UInt16 → Bool} {D : Nat} {R : Machine → Prop} (hcv : ∀ F : Nat × UInt8, Cov E F sp) (hsk : SpentKeep sp) (h : GOK sp E P G RK C fin chk sq D)
    (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → chk A = true → R m → SiteOK P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) {r : Machine} {K : List (Nat × UInt8)} (hq : (r, K) ∈ RK)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hc : InCls G m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteOK P (trace m i j)) ∧ ∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  obtain ⟨hM, hw0⟩ := h.starts _ hq
  obtain ⟨S0, hS0, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) hM h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := hw0 S0 hS0
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → chk A = true → R m' → SiteOK C.P m' := by
    intro A m' hs2 hc2 hr
    rw [h.pl]
    rw [h.env] at hs2
    exact hQ hs2 hc2 hr
  have hcv' : Cov C.E (m.frame, 2) sp := by rw [h.env]; exact hcv _
  have := frame_of_walkG (G := G) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) hcv' hsk hQ' hS h.dD hO h.table h.ops
    (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) h.tab h.gI h.keepI hw hs' (Or.inr hc) hk
  rw [h.pl, h.fin, h.env] at this
  exact this

/-! ## The places of the split on the ROM -/

/-- the player's height, as a RAM index -/
def yIdx (sy : Syms) : Nat := (sy.Player_Y_Position &&& 0x7FF).toNat

/-- **The place of the height's split**: the collision routine's first load of the player's height (`LDA zp`) -/
def yAt (sy : Syms) (m0 : Machine) : UInt16 := ScreenPage.findOpZ m0 sy.PlayerBGCollision 0xA5 sy.Player_Y_Position.toUInt8 64

/-- **The place of the accumulator's split**: the block buffer routine's add of the row's adder (`ADC abs,Y`) -/
def adcY (sy : Syms) (m0 : Machine) : UInt16 := PipeEntryRule.findOp m0 sy.BlockBufferCollision 0x79 64

/-- the RAM index of the absolute operand of the instruction at `a` -/
def absIdx (m0 : Machine) (a : UInt16) : Nat := (((romByte m0 (a + 1)).toUInt16 ||| ((romByte m0 (a + 2)).toUInt16 <<< 8)) &&& 0x7FF).toNat

/-- the crouch byte: the operand of the collision routine's first `LDA abs` after the height's load -/
def crouchIdx (sy : Syms) (m0 : Machine) : Nat := absIdx m0 (PipeEntryRule.findOp m0 (yAt sy m0 + 2) 0xAD 16)

/-- the player's size, as a RAM index -/
def sizeIdx (sy : Syms) : Nat := (sy.PlayerSize &&& 0x7FF).toNat

/-- the head's test: the collision routine's `CMP abs,X` of the height with the upper extent -/
def hcAt (sy : Syms) (m0 : Machine) : UInt16 := PipeEntryRule.findOp m0 (yAt sy m0 + 2) 0xDD 48

theorem and7FF_lt (a : UInt16) : (a &&& 0x7FF).toNat < 2048 := by
  rw [UInt16.toNat_and]
  have : (a.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
  have e : (0x7FF : UInt16).toNat = 2047 := rfl
  omega

theorem yIdx_lt (sy : Syms) : yIdx sy < 2048 := and7FF_lt _
theorem sizeIdx_lt (sy : Syms) : sizeIdx sy < 2048 := and7FF_lt _
theorem crouchIdx_lt (sy : Syms) (m0 : Machine) : crouchIdx sy m0 < 2048 := and7FF_lt _

/-- **The split on the ROM** -/
def splitRom (sy : Syms) (m0 : Machine) : AS → List AS :=
  splitR2 (yAt sy m0) (yIdx sy) (sizeIdx sy) (crouchIdx sy m0) (adcY sy m0) (EraseSplit.adcAt sy m0)

theorem cov_splitRom (sy : Syms) (m0 : Machine) (E : Env) (F : Nat × UInt8) : Cov E F (splitRom sy m0) :=
  cov_splitR2 (yIdx_lt sy) (sizeIdx_lt sy) (crouchIdx_lt sy m0)

theorem spent_splitRom (sy : Syms) (m0 : Machine) : SpentKeep (splitRom sy m0) := spent_splitR2 _ _ _ _ _ _

/-- the row's offset: the zero page byte that the block buffer routine stores before its read -/
def rowIdx (sy : Syms) (m0 : Machine) : Nat := (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 - 2)).toNat

/-- the block buffer routine's adder offset, which the collision routine keeps: the operand of its first load at the feet's check -/
def sideIdx (sy : Syms) (m0 : Machine) : Nat := (romByte m0 (sy.DoFootCheck + 1)).toNat

/-- a bit's class: not known, known 0, known 1 -/
def bitC (b : AB) (mask : UInt8) : Nat := if b.k &&& mask == 0 then 0 else if b.v &&& mask == 0 then 1 else 2

/-- the class of a byte split by its lowest set bit (`zsplitL`): its lowest bit known set with the bits below known 0, all known 0, or neither -/
def lowC (b : AB) : Nat := (bitList.findIdx? fun m => b.k &&& m == 0 || b.v &&& m != 0).elim 9 fun i =>
  if b.k &&& bitList[i]! != 0 && b.v &&& bitList[i]! != 0 then i else 9

/-- **The key's part on the ROM**: round 31's `EraseSplit.ptrKey`; a state whose first dot is below 10 (a frame's start, which knows the size's bits) apart from
the others; and, while bits 7 and 6 of the height are known (in the collision routine), the height's known
bits from bit 3 up, the row's offset's two high bits when the pointer's low byte is known at or past 128 (the second block buffer), and the classes of the crouch
byte and of the size's bit 0 -/
def rowKey (sy : Syms) (m0 : Machine) : AS → Nat :=
  let pk := EraseSplit.ptrKey sy m0
  let yI := yIdx sy
  let zI := rowIdx sy m0
  let cI := crouchIdx sy m0
  let sI := sizeIdx sy
  let zP := (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 + 1)).toNat
  fun A =>
    let y := A.getK yI
    let st := if A.lo < 10 then 2147483648 else 0
    st + if y.k &&& 0xC0 == 0xC0 then
      let z := A.getK zI
      let yc := (y.k >>> 3).toNat * 32 + ((y.v &&& y.k) >>> 3).toNat
      let p := A.getK zP
      let rc := if z.k &&& 0xC0 == 0xC0 && p.k &&& p.v &&& 0x80 != 0 then 1 + (z.v >>> 6).toNat else 0
      let c := A.getK cI
      let cc := if c.k == 0xFF && c.v == 0 then 10 else lowC c
      pk A + 16 * (yc + 1024 * (rc + 5 * (cc + 11 * bitC (A.getK sI) 1)))
    else pk A

/-- the aids on the ROM: `Z` without the adder offset among the bytes forgotten at the collision routine's checks -/
def aidsR (sy : Syms) (m0 : Machine) (Z : Aids) : Aids :=
  { Z with temps := Z.temps.filter (· != sideIdx sy m0), aAt := Z.aAt ++ [adcY sy m0 + 6] }

/-- where the search runs the pieces of the row's add on: the `AND #` and the `SEC` after it; they meet at the `SBC #`, where the search keys the accumulator -/
def passAt (sy : Syms) (m0 : Machine) : List UInt16 := [adcY sy m0 + 3, adcY sy m0 + 5]

/-- **What the search forgets, and where**: the height, the adder offset and the row at the collision routine's return and after the erase; the crouch byte and
the size after the head's test -/
def forgetAt (sy : Syms) (m0 : Machine) (Z : Aids) (P : Places) : List (UInt16 × List Nat) :=
  let l := [yIdx sy, sideIdx sy m0, rowIdx sy m0]
  [(Z.colEnd, l), (P.erase + 2, l), (hcAt sy m0 + 3, [crouchIdx sy m0, sizeIdx sy])]

end Smbrta.EraseRow
