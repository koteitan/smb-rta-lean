import Theorems.BufferControl
import Theorems.RoomBlocks

/-!
# The parts of `SiteOK`, the screen buffer's offset and the reads through a pointer in the room

`Route.ChangesBase.roomSites` asked `ScreenPage.SiteOK` on every instruction of every frame of the room, as one condition. Here its six parts are conditions of
their own (`Late`, `Reads`, `Read`, `Erase`, `Off`, `Xbit`; `siteOK_of`), with no change of content, so that each part can be proved or assumed alone.

Then two parts are proved on most instructions, by a walk of the room's frame with a check at every state it reaches:

* `Off`, that the first screen buffer's offset is below 64 where the code uses it as an index, on the frames that start with the control of the screen's
  buffers at 0: the screen update at the start of such a frame sets the offset to 0, and the code of the frame adds known lengths to it (`offOK`).
* `Reads`, that an `LDA (zp),Y` reads RAM or ROM, at every such read whose pointer is not the screen update's pointer into the buffer (`ptrS`): there the state
  knows the pointer's high byte at most `0x1E` or at least `0x80` (`readsOK`, `reads_of_ok`, with `SideChangeEnd.ptrHiOK`).

The walk that the route uses is that of `RoomMusic` (`RoomPause.pstep`: at the call of the sound routine the music bytes are split by the states of its table, so
the music's pointer is known), with the control known and the offset kept apart in the search (`walkPC`, `frame_of_walkPC`, `walkCheckPC`, `musicCheck`,
`music_frame0`, `music_frame6`). A first version on the walk of `BufferControl` (`walkC`, `frame_of_walkC`, `siteCheck`, `site_frame0`, `site_frame6`,
`sites_of_rows`) proves the same but for the reads through the music's pointer (`ptrsOf`); the route does not use it.

Over the room's frames the induction takes a frame's parts only from the frames before it (`music_sites_of_rows`): the room's condition, the control at 0 or 6,
and the music bytes in a state of the table at a frame's start come from the frames before (`RoomMap.cond_of_rows`, `BufferControl.ctl_run`,
`RoomPause.pause_step`).

What stays assumed: `Late`, `Read`, `Erase`, `Xbit`; `Reads` through the screen update's pointer; `Off` on the frames that start with the control at 6. Such a
frame draws the second buffer and does not reset the first buffer's offset. A coin frame adds 14 bytes to the first buffer (the coins' two digits and the score's
six, each with a header of three bytes), and coin frames can follow each other, so a bound needs the number of coins in a row, which the walk does not know. The
screen update's pointer moves through the buffer by the lengths of its records, which the walk does not know.

There is no game data in this file. Page: `1-1/d-2-4-2-1-SiteParts.md`.
-/

namespace Smbrta.SiteParts

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken coverS startsR readAddr readVal writeAddr RamRom placesR envR refR aidsOf)
open EntryHeight (HP preY stepY cov_preY s_stepY Opts)
open EntryBuffer (ctlI hpB knownB optsB)

/-! ## The six parts of `SiteOK` -/

/-- the handler is done before the frame's end -/
def Late (P : Places) (m : Machine) : Prop := m.pc ≠ P.idle → m.fdot ≤ P.late

/-- an `LDA (zp),Y` reads RAM or ROM -/
def Reads (m : Machine) : Prop := 0x8000 ≤ m.pc → m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 → RamRom (readAddr m)

/-- the block buffer routine reads a tile of the list -/
def Read (P : Places) (m : Machine) : Prop :=
  m.pc = P.read → readVal m ∈ P.tiles ∧ (m.ram.get! P.saveI ∈ P.heads → readVal m ∈ P.headTiles)

/-- the coin is erased in the block buffers -/
def Erase (P : Places) (m : Machine) : Prop :=
  m.pc = P.erase → writeAddr m < 0x2000 ∧ P.bufLo ≤ (writeAddr m &&& 0x7FF).toNat ∧ (writeAddr m &&& 0x7FF).toNat < P.bufLo + P.bufN

/-- the screen's buffer is not full -/
def Off (P : Places) (m : Machine) : Prop := m.pc ∈ P.offAt → (m.ram.get! P.offI).toNat < 64

/-- the position's low bits are not zero when the side pipe's code reads them -/
def Xbit (P : Places) (m : Machine) : Prop := m.pc = P.xAt → m.ram.get! P.xI &&& 0x0F ≠ 0

/-- `Reads` only at the reads through the zero page pointers `Z`: an `LDA (zp),Y` whose operand is in `Z` reads RAM or ROM -/
def ReadsAt (Z : List UInt8) (m : Machine) : Prop :=
  0x8000 ≤ m.pc → m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 → RoomBlocks.operand m ∈ Z → RamRom (readAddr m)

/-- **`SiteOK` is its six parts** -/
theorem siteOK_of {P : Places} {m : Machine} (h1 : Late P m) (h2 : Reads m) (h3 : Read P m) (h4 : Erase P m) (h5 : Off P m) (h6 : Xbit P m) : SiteOK P m :=
  ⟨h1, h2, h3, h4, h5, h6⟩

theorem late_of {P : Places} {m : Machine} (h : SiteOK P m) : Late P m := h.late
theorem reads_of {P : Places} {m : Machine} (h : SiteOK P m) : Reads m := h.reads
theorem read_of {P : Places} {m : Machine} (h : SiteOK P m) : Read P m := h.read
theorem erase_of {P : Places} {m : Machine} (h : SiteOK P m) : Erase P m := h.erase
theorem off_of {P : Places} {m : Machine} (h : SiteOK P m) : Off P m := h.off
theorem xbit_of {P : Places} {m : Machine} (h : SiteOK P m) : Xbit P m := h.xbit

/-- what the route still asks on every instruction of the room: four parts, and `Reads` only through the pointers `Z` -/
structure Rest (P : Places) (Z : List UInt8) (m : Machine) : Prop where
  late : Late P m
  reads : ReadsAt Z m
  read : Read P m
  erase : Erase P m
  xbit : Xbit P m

theorem siteOK_of_rest {P : Places} {Z : List UInt8} {m : Machine} (h : Rest P Z m) (hr : Reads m) (ho : Off P m) : SiteOK P m :=
  ⟨h.late, hr, h.read, h.erase, ho, h.xbit⟩

/-! ## A walk that checks a condition at each state -/

/-- from `A`, step by step, as `EntryHeight.walkY`, and `chk` holds at every state of the way and at the frame's end -/
def walkC (S : HP) (C : CfgS) (chk : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => chk A && (preY S (clampS C.P A)).all fun A₁ => (stepY C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkC S C chk n (weaken C B)
      else B.k == A.k + 1 && C.fin B && chk B

/-- **The offset's check**: where the code uses the first buffer's offset as an index, the state knows it below 64 -/
def offOK (P : Places) (A : AS) : Bool := !(P.offAt.contains A.pc) || decide ((A.getK P.offI).maxv.toNat < 64)

theorem off_of_ok {E : Env} {F : Nat × UInt8} {P : Places} (hI : P.offI < 2048) {A : AS} {m : Machine} (hs : Sim E F A m) (h : offOK P A = true) : Off P m := by
  intro hm
  simp only [offOK, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with h | h
  · have hm' : A.pc ∈ P.offAt := by rw [← hs.pc]; exact hm
    rw [List.contains_iff_mem.2 hm'] at h
    cases h
  · exact Nat.lt_of_le_of_lt (le_maxv (hs.ram _ hI)) h

/-- the high byte of the pointer of the `LDA (zp),Y` at `A.pc` meets `SideChangeEnd.ptrHiOK` (at most `0x1E`, or at least `0x80`) -/
def hiOK (E : Env) (A : AS) : Bool :=
  let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
  decide (0x8000 ≤ A.pc + 1) && SideChangeEnd.ptrHiOK (A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat)

/-- **The read's check**: at an `LDA (zp),Y` whose pointer is not one of `Z`, the pointer's high byte is known well enough -/
def readsOK (E : Env) (Z : List UInt8) (A : AS) : Bool :=
  !(decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1) || Z.contains (E.prg.get! ((A.pc + 1) &&& E.mask).toNat) || hiOK E A

theorem wide_ramRom {a : UInt16} (h : TaintRun.AdR SideChangeEnd.ptrWide a) : RamRom a := by
  rcases h with ⟨h1, _, _⟩ | ⟨_, h2 | h2⟩
  · exact absurd h1 (by decide)
  · exact Or.inr h2
  · left
    apply UInt16.lt_iff_toNat_lt.2
    have := UInt16.le_iff_toNat_le.1 h2
    have e : (SideChangeEnd.ptrWide.hi).toNat = 8191 := rfl
    rw [e] at this
    show a.toNat < 8192
    omega

theorem reads_of_ok {E : Env} {F : Nat × UInt8} {Z : List UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : readsOK E Z A = true) (hz : ReadsAt Z m) :
    Reads m := by
  intro h1 h2
  have g1 : 0x8000 ≤ A.pc := by rw [← hs.pc]; exact h1
  have g2 : E.prg.get! (A.pc &&& E.mask).toNat = 0xB1 := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact h2
  have hop : RoomBlocks.operand m = E.prg.get! ((A.pc + 1) &&& E.mask).toNat := by
    unfold RoomBlocks.operand
    rw [hs.prg, hs.mask, hs.pc]
  have hn : (decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1) = true := by rw [g2]; simp [g1]
  unfold readsOK at h
  rw [hn] at h
  cases hc : Z.contains (E.prg.get! ((A.pc + 1) &&& E.mask).toNat) with
  | true => exact hz h1 h2 (by rw [hop]; exact List.contains_iff_mem.1 hc)
  | false =>
    rw [hc] at h
    have hh : hiOK E A = true := by simpa using h
    simp only [hiOK, Bool.and_eq_true, decide_eq_true_eq] at hh
    obtain ⟨hp, hk⟩ := hh
    have hp' : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact hp
    rw [RoomBlocks.readAddr_eq hp']
    apply wide_ramRom
    unfold RoomBlocks.ptrZ
    have hlt : (((RoomBlocks.operand m) + 1).toUInt16 &&& 0x7FF).toNat < 2048 := by
      rw [UInt16.toNat_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hmem := hs.ram _ hlt
    rw [← hop] at hk
    exact SideChangeEnd.wide_ok hk hmem

section
variable {S : HP} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveC (S : HP) (C : CfgS) (chk : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkC S C chk n A = true

theorem chk_of_walk {n : Nat} {A : AS} (h : walkC S C chk n A = true) : chk A = true := by
  cases n with
  | zero => simp [walkC] at h
  | succ n =>
    simp only [walkC, Bool.and_eq_true] at h
    exact h.1

theorem cover_liveC (ht : C.t.all (walkC S C chk Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ D, LiveC S C chk F D m ∧ D.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

/-- **One step of the walk**, as `EntryHeight.live_stepY`: `SiteOK` at the machine comes from `R` and the check at the state (`hQ`), and the next machine needs
only its `Late` -/
theorem live_stepC {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (ht : C.t.all (walkC S C chk Fu) = true)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveC S C chk F A m)
    (hr : R m) (hl2 : Late C.P (go step m).2) :
    (∃ A', LiveC S C chk F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkC] at hw
  | succ n =>
    have hh : SiteOK C.P m := hQ hs (chk_of_walk hw) hr
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    have hhS : SiteOK S.P m := by rw [← hP]; exact hh
    have hOS : PlacesOK C.E S.P := by rw [← hP]; exact hO
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preY hOS hy htl hs0 hhS
    obtain ⟨r, hr', hB⟩ := s_stepY hO hops hT hs1 hh
    simp only [walkC, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 A₁ hA r hr'
    have hkA : A₁.k = A.k := by rw [hk1, ScreenPage.clamp_k]
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hkA] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        have hN : Sim C.E F (weaken C B) (go step m).2 ∧ (weaken C B).k = B.k := by
          unfold weaken
          split
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            have h5 := sim_le hc.2 h1
            refine ⟨h5, ?_⟩
            have hle := hc.2
            simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
            exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
          · exact ⟨h1, rfl⟩
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveC ht (ScreenPage.sim_clamp hO.late hN.1 hl2) h3
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.2, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `A₀` that succeeds covers the frame of every machine of `A₀`, for every input, if each instruction meets `R`; and then each
instruction meets `SiteOK`. `R` must give `Late` (`hL`), and `R` with the check at a state that covers the machine must give `SiteOK` (`hQ`). -/
theorem frame_of_walkC {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hL : ∀ {m : Machine}, R m → Late C.P m)
    (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (ht : C.t.all (walkC S C chk Fu) = true)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {A₀ : AS} {m : Machine} {i : UInt8} (hw : walkC S C chk Fu A₀ = true) (hs : Sim C.E F A₀ m) (hk : ∀ j, R (trace m i j)) :
    ((frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (frame m i)) ∧ ∀ j, SiteOK C.P (trace m i j) := by
  have hs0 : Sim C.E F A₀ { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveC S C chk F A (trace m i j) ∧ A.k = A₀.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨A₀, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h3, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hL (hk (j + 1))
        rw [e2] at hh2 ⊢
        rcases live_stepC hQ hO hP hy htl ht hops hT h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h3, h4⟩
  refine ⟨?_, fun j => ?_⟩
  · rw [frame_trace]
    rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, _, h3, h4⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨h1, B, h2, h3, h4⟩
  · rcases key j with ⟨A, ⟨h1, n, h1'⟩, _, _, _⟩ | ⟨_, B, _, h2', _, h4⟩
    · exact hQ h1 (chk_of_walk h1') (hk j)
    · exact hQ h4 h2' (hk j)

end

/-! ## The check of a walk -/

/-- **The check of a walk with a check at each state**: the table of `EntryHeight`'s search, and the walk `walkC` from it and from the start states -/
def walkCheckC (S : HP) (Z : Aids) (O : Opts) (fin : AS → Bool) (chk : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := EntryHeight.cfgOf S Z O fin E r K
  ScreenPage.placesOK E S.P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K &&
    decide (S.rtI < 2048) && decide (S.yI < 2048) && decide (S.tileI < 2048) &&
    C.t.all (walkC S C chk ScreenPage.fuelS) && (startsR r K).all (walkC S C chk ScreenPage.fuelS)

/-- what the check says -/
structure WalkOKC (S : HP) (fin chk : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) : Prop where
  places : PlacesOK E S.P
  pad : E.pad = AB.top
  mask : ScreenPage.MaskOK r K
  env : C.E = E
  pl : C.P = S.P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = fin
  rt : S.rtI < 2048
  yI : S.yI < 2048
  tileI : S.tileI < 2048
  table : C.t.all (walkC S C chk ScreenPage.fuelS) = true
  starts : ∀ A ∈ startsR r K, walkC S C chk ScreenPage.fuelS A = true

theorem walkOKC_of_check {S : HP} {Z : Aids} {O : Opts} {fin chk : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)}
    (h : walkCheckC S Z O fin chk E r K = true) : WalkOKC S fin chk E r K (EntryHeight.cfgOf S Z O fin E r K) := by
  simp only [walkCheckC, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, rfl, h4, h5, h6, h7, h8⟩

/-- **One frame of the room, all six parts.** A frame that starts in the room's condition with the bits `K`, with `R` on each instruction, meets `SiteOK` on
each instruction, if the walk with the check `chk` succeeds and `R` with the check at a state gives `SiteOK` -/
theorem sites_frame {S : HP} {fin chk : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {R : Machine → Prop}
    (h : WalkOKC S fin chk E r K C) (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → chk A = true → R m → SiteOK S.P m)
    (hL : ∀ {m : Machine}, R m → Late S.P m)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, R (trace m i j)) : ∀ j, SiteOK S.P (trace m i j) := by
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → chk A = true → R m' → SiteOK C.P m' := by
    intro A m' hs2 hc hr
    rw [h.pl]
    rw [h.env] at hs2
    exact hQ hs2 hc hr
  have hL' : ∀ {m' : Machine}, R m' → Late C.P m' := by
    intro m' hr
    rw [h.pl]
    exact hL hr
  have := (frame_of_walkC (S := S) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) hQ' hL'
    hO h.pl h.yI h.tileI h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) hw hs' hk).2
  rw [h.pl] at this
  exact this

/-! ## On the ROM -/

section
variable {sy : Syms} {nmS : Names} {m0 : Machine}

/-- **The two pointers whose reads stay assumed**: the zero page operands of the first `LDA (zp),Y` of the screen update (its pointer into the screen's buffer)
and of square 1's music data (the music's pointer); found in the ROM from the two symbols -/
def ptrsOf (sy : Syms) (m0 : Machine) : List UInt8 :=
  [romByte m0 (PipeEntryRule.findOp m0 sy.UpdateScreen 0xB1 16 + 1), romByte m0 (PipeEntryRule.findOp m0 sy.FetchSqu1MusicData 0xB1 16 + 1)]

/-- the check at each state of a frame that starts with the control at 0: the offset's and the read's -/
def chk0 (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := offOK P A && readsOK E Z A

/-- the walk of `BufferControl` from the reference `r`, with the check `chk` at each state -/
def walkS (sy : Syms) (nm : Names) (m0 : Machine) (chk : AS → Bool) (r : Machine) : Bool :=
  walkCheckC (hpB sy nm m0) (aidsOf sy nm m0) (optsB (hpB sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (ctlI nm) (EntryBuffer.bufIdx nm))
    (BufferControl.finK (ctlI nm)) chk (envR sy nm m0) r (knownB sy nm m0)

/-- **The check on the ROM**: the room's walk with the control known (that of `BufferControl`) from the control at 0 knows the first buffer's offset below 64
where the code uses it, and the high byte of each pointer of an `LDA (zp),Y` other than those of `ptrsOf`; from the control at 6, the high bytes -/
def siteCheck (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  walkS sy nm m0 (chk0 (placesR sy nm m0) (envR sy nm m0) (ptrsOf sy m0)) (refR m0) && walkS sy nm m0 (readsOK (envR sy nm m0) (ptrsOf sy m0)) (BufferControl.ref6 (ctlI nm) (refR m0))

theorem site_parts (h : siteCheck sy nmS m0 = true) :
    walkS sy nmS m0 (chk0 (placesR sy nmS m0) (envR sy nmS m0) (ptrsOf sy m0)) (refR m0) = true ∧ walkS sy nmS m0 (readsOK (envR sy nmS m0) (ptrsOf sy m0)) (BufferControl.ref6 (ctlI nmS) (refR m0)) = true := by
  simp only [siteCheck, Bool.and_eq_true] at h
  exact h

/-- **One frame of the room that starts with the control at 0**: the four parts and `Reads` through the two pointers on each instruction give all six -/
theorem site_frame0 (hK : BufferControl.keepCheck sy nmS m0 = true) (hO : siteCheck sy nmS m0 = true) {m : Machine} {i : UInt8}
    (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMap.knownT sy nmS m0) m) (hv : m.ram.get! (ctlI nmS) = 0)
    (hk : ∀ j, Rest (placesR sy nmS m0) (ptrsOf sy m0) (trace m i j)) : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  have hI : (placesR sy nmS m0).offI < 2048 := (walkOKC_of_check (site_parts hO).1).places.offI
  refine sites_frame (S := hpB sy nmS m0) (R := Rest (placesR sy nmS m0) (ptrsOf sy m0)) (walkOKC_of_check (site_parts hO).1) ?_ (fun hr => hr.late)
    (BufferControl.cond0 hm (hv.trans h2.symm)) hk
  intro F A m' hs hc hr
  simp only [chk0, Bool.and_eq_true] at hc
  exact siteOK_of_rest hr (reads_of_ok hs hc.2 hr.reads) (off_of_ok hI hs hc.1)

/-- **One frame of the room that starts with the control at 6**: with `Off` too on each instruction, all six -/
theorem site_frame6 (hK : BufferControl.keepCheck sy nmS m0 = true) (hO : siteCheck sy nmS m0 = true) {m : Machine} {i : UInt8}
    (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMap.knownT sy nmS m0) m) (hv : m.ram.get! (ctlI nmS) = 6)
    (hk : ∀ j, Rest (placesR sy nmS m0) (ptrsOf sy m0) (trace m i j)) (ho : ∀ j, Off (placesR sy nmS m0) (trace m i j)) :
    ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨h1, _, h3, _, _⟩ := BufferControl.keep_parts hK
  have w := walkOKC_of_check (site_parts hO).2
  have hsz : ((refR m0).ram.set! (ctlI nmS) 6).size = 2048 := w.mask.szR
  rw [PipeTransitionAll.ba_size_set] at hsz
  have hc6 := BufferControl.cond6 hm h1 (by rw [hsz]; exact h3) hv
  refine sites_frame (S := hpB sy nmS m0) (R := fun m' => Rest (placesR sy nmS m0) (ptrsOf sy m0) m' ∧ Off (placesR sy nmS m0) m') w ?_
    (fun hr => hr.1.late) hc6 (fun j => ⟨hk j, ho j⟩)
  intro F A m' hs hc hr
  exact siteOK_of_rest hr.1 (reads_of_ok hs hc hr.1.reads) hr.2

end

/-! ## The walk of `RoomMusic` with a check at each state

The walk of `RoomMusic` (`RoomPause.pstep`: at the call of the sound routine the music bytes are split by the states of the table `T`) knows the music's pointer
at every read through it. With the control of the screen's buffers known and the first buffer's offset kept apart in the search, it also knows the offset from the
control at 0. So this walk, with the check at each state, gives `Reads` at every read but those through the screen update's pointer (`ptrS`). -/

section
open RoomPause (Reg pstep Ph InCls)
variable {G : Reg} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

/-- from `A`, step by step with `RoomPause.pstep`, as `RoomPause.walkP`, and `chk` holds at every state of the way and at the frame's end -/
def walkPC (G : Reg) (C : CfgS) (chk : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => chk A && (pstep C.P C.E C.ops G A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkPC G C chk n (weaken C B)
      else B.k == A.k + 1 && C.fin B && chk B

/-- `A` covers `m` with `Ph`, and a walk from `A` succeeds -/
def LivePC (G : Reg) (C : CfgS) (chk : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ Ph G A m ∧ ∃ n, walkPC G C chk n A = true

theorem chkP_of_walk {n : Nat} {A : AS} (h : walkPC G C chk n A = true) : chk A = true := by
  cases n with
  | zero => simp [walkPC] at h
  | succ n =>
    simp only [walkPC, Bool.and_eq_true] at h
    exact h.1

theorem cover_livePC (ht : C.t.all (walkPC G C chk Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph G B m) (h : coverS C B = true) :
    ∃ D, LivePC G C chk F D m ∧ D.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, RoomPause.ph_of_spent (StepWrites.le_pc_spent hle).2 hp, Fu, hall⟩, hk⟩
  · cases h2

/-- **One step of the walk**, as `RoomPause.live_stepP`, with `SiteOK` at the machine from `R` and the check (`hQ`), and only `Late` at the next machine -/
theorem live_stepPC {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkPC G C chk Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine} (hl : LivePC G C chk F A m)
    (hr : R m) (hl2 : Late C.P (go step m).2) :
    (∃ A', LivePC G C chk F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph G B (go step m).2) := by
  obtain ⟨hs, hp, n, hw⟩ := hl
  cases n with
  | zero => simp [walkPC] at hw
  | succ n =>
    have hh : SiteOK C.P m := hQ hs (chkP_of_walk hw) hr
    obtain ⟨r, hr', hB⟩ := RoomPause.s_pstep hO hops hT h0 hg hkb hs hh hp
    simp only [walkPC, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 r hr'
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨g1, g2, g3⟩ := hB B rfl
      dsimp only at hw2
      rcases g2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        obtain ⟨n1, n2, n3⟩ := RoomPause.weaken_of (C := C) g1
        have hpW : Ph G (weaken C B) (go step m).2 := RoomPause.ph_of_spent n3.symm g3
        rcases hw2 with ⟨_, h3⟩ | h3
        · have hpC : Ph G (clampS C.P (weaken C B)) (go step m).2 := RoomPause.ph_of_spent (RoomPause.clamp_spent _).symm hpW
          obtain ⟨D, hD, hk⟩ := cover_livePC ht (ScreenPage.sim_clamp hO.late n1 hl2) hpC h3
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, n2, k1], k2, k3⟩
        · exact ⟨_, ⟨n1, hpW, n, h3⟩, by rw [n2, k1], k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.2, hw2.2, k1, g1, g3⟩

/-- **One frame.** A walk from `S` that succeeds, with `Ph` at the start, covers the frame of every machine of `S`, if each instruction meets `R`; and then each
instruction meets `SiteOK` -/
theorem frame_of_walkPC {R : Machine → Prop} (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → chk A = true → R m → SiteOK C.P m)
    (hL : ∀ {m : Machine}, R m → Late C.P m)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkPC G C chk Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkPC G C chk Fu S = true) (hs : Sim C.E F S m) (hph : Ph G S m) (hk : ∀ j, R (trace m i j)) :
    ∀ j, SiteOK C.P (trace m i j) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have key : ∀ j, (∃ A, LivePC G C chk F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
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
        have hh2 := hL (hk (j + 1))
        rw [e2] at hh2 ⊢
        rcases live_stepPC hQ hO ht hops hT h0 hg hkb h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a5⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', by rw [a3, h2], a4, a5⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h3, h4, h5⟩
  intro j
  rcases key j with ⟨A, ⟨h1, _, n, h1'⟩, _, _, _⟩ | ⟨_, B, _, h2', _, h4, _⟩
  · exact hQ h1 (chkP_of_walk h1') (hk j)
  · exact hQ h4 h2' (hk j)

/-- the table of `RoomPause`'s search, with no condition at the frame's end: the frame theorem here gives only `SiteOK` on each instruction, and a frame may
end with the control at 0 or 6 -/
def cfgPC (P : Places) (Z : Aids) (E : Env) (G : Reg) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  { RoomPause.cfgOfP P Z E G r K with fin := fun _ => true }

/-- **The check of the walk with a check at each state**, as `RoomPause.walkCheck` -/
def walkCheckPC (P : Places) (Z : Aids) (E : Env) (G : Reg) (r : Machine) (K : List (Nat × UInt8)) (chk : AS → Bool) : Bool :=
  let C := cfgPC P Z E G r K
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K && StepWrites.tabOK G.SB G.T && decide (G.gI < 2048) &&
    G.keepB.all (fun p => decide (p.1 < 2048)) && C.t.all (walkPC G C chk ScreenPage.fuelS) && (startsR r K).all (walkPC G C chk ScreenPage.fuelS)

/-- what the check says -/
structure PauseOKC (E : Env) (P : Places) (r : Machine) (K : List (Nat × UInt8)) (G : Reg) (C : CfgS) (chk : AS → Bool) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  mask : ScreenPage.MaskOK r K
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  tab : StepWrites.tabOK G.SB G.T = true
  gI : G.gI < 2048
  keepI : ∀ p ∈ G.keepB, p.1 < 2048
  table : C.t.all (walkPC G C chk ScreenPage.fuelS) = true
  starts : ∀ S ∈ startsR r K, walkPC G C chk ScreenPage.fuelS S = true

theorem pauseOKC_of_check {P : Places} {Z : Aids} {E : Env} {G : Reg} {r : Machine} {K : List (Nat × UInt8)} {chk : AS → Bool}
    (h : walkCheckPC P Z E G r K chk = true) : PauseOKC E P r K G (cfgPC P Z E G r K) chk := by
  simp only [walkCheckPC, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, hkb⟩, h6⟩, h7⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, h4, h5, fun p hp => by simpa using hkb p hp, h6, h7⟩

/-- **One frame of the room with the music bytes in a class**: with `R` on each instruction, `SiteOK` on each instruction, if the walk with the check succeeds -/
theorem music_frame {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {R : Machine → Prop} (h : PauseOKC E P r K G C chk)
    (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → chk A = true → R m → SiteOK P m) (hL : ∀ {m : Machine}, R m → Late P m)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hc : InCls G m) (hk : ∀ j, R (trace m i j)) : ∀ j, SiteOK P (trace m i j) := by
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → chk A = true → R m' → SiteOK C.P m' := by
    intro A m' hs2 hc2 hr
    rw [h.pl]
    rw [h.env] at hs2
    exact hQ hs2 hc2 hr
  have hL' : ∀ {m' : Machine}, R m' → Late C.P m' := by
    intro m' hr
    rw [h.pl]
    exact hL hr
  have := frame_of_walkPC (G := G) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) hQ' hL' hO h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide)
    (by rw [h.env]; exact h.pad) h.tab h.gI h.keepI hw hs' (Or.inr hc) hk
  rw [h.pl] at this
  exact this

end

/-! ## The music walk on the ROM -/

section
open RoomPause (InCls)
variable {sy : Syms} {nmS : Names} {m0 : Machine} {T : List StepWrites.SState}

/-- **The pointer whose reads stay assumed**: the zero page operand of the first `LDA (zp),Y` of the screen update (its pointer into the screen's buffer) -/
def ptrS (sy : Syms) (m0 : Machine) : List UInt8 := [romByte m0 (PipeEntryRule.findOp m0 sy.UpdateScreen 0xB1 16 + 1)]

/-- the room's known bits of `RoomMusic` and the control -/
def knownMC (nm : Names) : List (Nat × UInt8) := RoomMusic.knownM nm ++ [(ctlI nm, 0xFF)]

/-- the search keeps the first buffer's offset apart (no part of the proof: the walk checks the table) -/
def keepOff (Z : Aids) (i : Nat) : Aids := { Z with keep := Z.keep ++ [i] }

/-- **The check on the ROM**: the walk of `RoomMusic` with the table `T` and the control known, from the control at 0 with the offset's and the read's checks
(but the reads through the screen update's pointer), and from 6 with the read's check; and `knownM` does not list the control -/
def musicCheck (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) : Bool :=
  (RoomMusic.knownM nm).all (fun p => p.1 != ctlI nm) &&
  walkCheckPC (placesR sy nm m0) (keepOff (aidsOf sy nm m0) (placesR sy nm m0).offI) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (refR m0) (knownMC nm)
    (chk0 (placesR sy nm m0) (envR sy nm m0) (ptrS sy m0)) &&
  walkCheckPC (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (BufferControl.ref6 (ctlI nm) (refR m0)) (knownMC nm)
    (readsOK (envR sy nm m0) (ptrS sy m0))

theorem music_parts (h : musicCheck sy nmS m0 T = true) :
    (RoomMusic.knownM nmS).all (fun p => p.1 != ctlI nmS) = true ∧
    walkCheckPC (placesR sy nmS m0) (keepOff (aidsOf sy nmS m0) (placesR sy nmS m0).offI) (envR sy nmS m0) (RoomMusic.regM sy m0 nmS T) (refR m0) (knownMC nmS)
      (chk0 (placesR sy nmS m0) (envR sy nmS m0) (ptrS sy m0)) = true ∧
    walkCheckPC (placesR sy nmS m0) (aidsOf sy nmS m0) (envR sy nmS m0) (RoomMusic.regM sy m0 nmS T) (BufferControl.ref6 (ctlI nmS) (refR m0)) (knownMC nmS)
      (readsOK (envR sy nmS m0) (ptrS sy m0)) = true := by
  simp only [musicCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **One frame of the room that starts with the control at 0**, in the condition of `RoomMusic` and with the music bytes in a class: the four parts and `Reads`
through the screen update's pointer on each instruction give all six -/
theorem music_frame0 (hK : BufferControl.keepCheck sy nmS m0 = true) (hO : musicCheck sy nmS m0 T = true) {m : Machine} {i : UInt8}
    (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m) (hv : m.ram.get! (ctlI nmS) = 0)
    (hk : ∀ j, Rest (placesR sy nmS m0) (ptrS sy m0) (trace m i j)) : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  have w := pauseOKC_of_check (music_parts hO).2.1
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  refine music_frame (R := Rest (placesR sy nmS m0) (ptrS sy m0)) w ?_ (fun hr => hr.late) (BufferControl.cond0 hm (hv.trans h2.symm)) hc hk
  intro F A m' hs hc2 hr
  simp only [chk0, Bool.and_eq_true] at hc2
  exact siteOK_of_rest hr (reads_of_ok hs hc2.2 hr.reads) (off_of_ok hI hs hc2.1)

/-- **One frame of the room that starts with the control at 6**, as `music_frame0`, with `Off` too on each instruction -/
theorem music_frame6 (hK : BufferControl.keepCheck sy nmS m0 = true) (hO : musicCheck sy nmS m0 T = true) {m : Machine} {i : UInt8}
    (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m) (hv : m.ram.get! (ctlI nmS) = 6)
    (hk : ∀ j, Rest (placesR sy nmS m0) (ptrS sy m0) (trace m i j)) (ho : ∀ j, Off (placesR sy nmS m0) (trace m i j)) :
    ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, h6⟩ := music_parts hO
  have w := pauseOKC_of_check h6
  have hsz : ((refR m0).ram.set! (ctlI nmS) 6).size = 2048 := w.mask.szR
  rw [PipeTransitionAll.ba_size_set] at hsz
  have hc6 := BufferControl.cond6 hm hk1 (by rw [hsz]; exact h3) hv
  refine music_frame (R := fun m' => Rest (placesR sy nmS m0) (ptrS sy m0) m' ∧ Off (placesR sy nmS m0) m') w ?_ (fun hr => hr.1.late) hc6 hc
    (fun j => ⟨hk j, ho j⟩)
  intro F A m' hs hc2 hr
  exact siteOK_of_rest hr.1 (reads_of_ok hs hc2 hr.1.reads) hr.2

end

/-! ## The room's frames -/

section
open PipeChangeEnd (Data InRowsT)
variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **The room's condition at a frame's start from the frames before it**: under the conditions of `RoomMap.map_of_rows`, with `SiteOK` only on the frames
before `n` -/
theorem cond_at (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b n : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true) (hbn : b ≤ n)
    (sites : ∀ k, b ≤ k → k < n → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq k) (inp k) j))
    (stay : ∀ k, b ≤ k → k ≤ n → (seq k).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    RoomCond (envR sy nmS m0) (refR m0) (RoomMap.knownT sy nmS m0) (seq n) := by
  rcases Nat.eq_or_lt_of_le hbn with h | h
  · rw [← h]
    exact RoomMap.start_of_rows hc hin hctl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := RoomMap.cond_of_rows hF hc next hin hctl (a := k + 1) sites (fun q a1 a2 => stay q a1 (by omega)) k (by omega) (by omega)
    have h2 := (RoomMap.room_stepT hF.ok h1 (sites k (by omega) (by omega))).1
    rw [← next] at h2
    rcases h2 with h3 | h3
    · exact h3
    · exact absurd (stay (k + 1) (by omega) (Nat.le_refl _)) h3

/-- **`SiteOK` on every instruction of every frame of the room**, from four parts and `Reads` through the two pointers of `ptrsOf` on every frame, and `Off`
on the frames that start with the control at 6: under the conditions of `RoomMap.map_of_rows`, with the checks of `BufferControl` and `siteCheck`. The frames
are taken in order: the room's condition and the control at 0 or 6 at the start of a frame come from the frames before it. -/
theorem sites_of_rows (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hK : BufferControl.keepCheck sy nmS m0 = true)
    (hs : BufferControl.startCheckC sy nm d e nmS m0 = true) (hO : siteCheck sy nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (rest : ∀ n, b ≤ n → n < a → ∀ j, Rest (placesR sy nmS m0) (ptrsOf sy m0) (trace (seq n) (inp n) j))
    (off6 : ∀ n, b ≤ n → n < a → (seq n).ram.get! (ctlI nmS) = 6 → ∀ j, Off (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j) := by
  have key : ∀ k, ∀ n, b ≤ n → n < b + k → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j) := by
    intro k
    induction k with
    | zero => intro n h1 h2; omega
    | succ k ih =>
      intro n h1 h2 h3
      rcases Nat.lt_or_ge n (b + k) with h4 | h4
      · exact ih n h1 h4 h3
      · have hn : n = b + k := by omega
        subst hn
        have sites : ∀ q, b ≤ q → q < b + k → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq q) (inp q) j) := fun q a1 a2 => ih q a1 a2 (by omega)
        have hcond := cond_at hF hc next hin hctl (n := b + k) (by omega) sites (fun q a1 a2 => stay q a1 (by omega))
        have hctl06 := BufferControl.ctl_of_rows hF hc hK hs next hin hctl (a := b + k) sites (fun q a1 a2 => stay q a1 (by omega)) (b + k) h1 (Nat.le_refl _)
        rcases hctl06 with h0 | h6
        · exact site_frame0 hK hO hcond h0 (rest (b + k) h1 h3)
        · exact site_frame6 hK hO hcond h6 (rest (b + k) h1 h3) (off6 (b + k) h1 h3 h6)
  intro n h1 h2
  exact key (n + 1 - b) n h1 (by omega) h2

/-- **`SiteOK` on every instruction of every frame of the room, with the music walk**: from four parts and `Reads` through the screen update's pointer
(`ptrS`) on every frame, and `Off` on the frames that start with the control at 6; under the conditions of `RoomMap.map_of_rows`, with the checks of
`BufferControl`, of `RoomMusic` (`hM`, with its table `T`) and `musicCheck` with the same table. The frames are taken in order: at a frame's start the room's
condition (`cond_at`), the control at 0 or 6 (`BufferControl.ctl_of_rows`), and the condition of `RoomMusic` with the music bytes in a class (one step of
`RoomPause.pause_step` from the frame before) come from the frames before it. -/
theorem music_sites_of_rows {V : List (Machine × List Nat)} {T : List StepWrites.SState}
    (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true) (hK : BufferControl.keepCheck sy nmS m0 = true)
    (hs : BufferControl.startCheckC sy nm d (PipeTransition.entry m0) nmS m0 = true) (hM : RoomMusic.Facts sy m0 nm d V nmS T) (hO : musicCheck sy nmS m0 T = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true) (h0 : ScreenPage.Room sy nmS m0 (seq b))
    (rest : ∀ n, b ≤ n → n < a → ∀ j, Rest (placesR sy nmS m0) (ptrS sy m0) (trace (seq n) (inp n) j))
    (off6 : ∀ n, b ≤ n → n < a → (seq n).ram.get! (ctlI nmS) = 6 → ∀ j, Off (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j) := by
  have hq : RoomMusic.emq nmS < 2048 := by
    have : RoomMusic.emq nmS ≤ 0x7FF := Nat.and_le_right
    omega
  obtain ⟨hx, ht⟩ := RoomMusic.start_of_invL hq hM.bit hM.start hin hctl
  have hm0 : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq b) := RoomMusic.roomCond_append h0 hx
  have key : ∀ k, b + k ≤ a → (∀ n, b ≤ n → n < b + k → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j)) ∧
      (b + k < a → RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq (b + k)) ∧ RoomPause.InCls (RoomMusic.regM sy m0 nmS T) (seq (b + k))) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun n h1 h2 => by omega, fun _ => ⟨hm0, ht⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨sites, hmk⟩ := ih (by omega)
      obtain ⟨hmc, hcls⟩ := hmk (by omega)
      have hcond := cond_at hF hc next hin hctl (n := b + k) (by omega) sites (fun q a1 a2 => stay q a1 (by omega))
      have hctl06 := BufferControl.ctl_of_rows hF hc hK hs next hin hctl (a := b + k) sites (fun q a1 a2 => stay q a1 (by omega)) (b + k) (by omega) (Nat.le_refl _)
      have hnow : ∀ j, SiteOK (placesR sy nmS m0) (trace (seq (b + k)) (inp (b + k)) j) := by
        rcases hctl06 with h0' | h6
        · exact music_frame0 hK hO hmc hcls h0' (rest (b + k) (by omega) (by omega))
        · exact music_frame6 hK hO hmc hcls h6 (rest (b + k) (by omega) (by omega)) (off6 (b + k) (by omega) (by omega) h6)
      refine ⟨fun n h1 h2 => ?_, fun hlt => ?_⟩
      · rcases Nat.lt_or_ge n (b + k) with h3 | h3
        · exact sites n h1 h3
        · have e : n = b + k := by omega
          rw [e]
          exact hnow
      · have hstep := RoomPause.pause_step hM.walk hmc hnow hcls
        have e1 : b + (k + 1) = b + k + 1 := rfl
        rw [e1, next]
        refine ⟨?_, hstep.1⟩
        rcases hstep.2 with h3 | ⟨h3, _⟩
        · exact h3
        · exfalso
          apply h3
          rw [← next]
          exact stay (b + k + 1) (by omega) (by omega)
  intro n h1 h2
  exact (key (n + 1 - b) (by omega)).1 n h1 (by omega)

end

end Smbrta.SiteParts
