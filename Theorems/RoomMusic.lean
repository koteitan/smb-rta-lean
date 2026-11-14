import Theorems.RoomPause

/-!
# The music bytes through the room's frames

`ScreenPage.EntryRest` (the field `entry₂` of the route) asks 16 bytes at the side pipe's entry to have the values of a reference. Eight of them are bytes of the music.
Here the walk of one frame in the room of `RoomPause` carries the music bytes in a table outside the abstract state, as it carries the six bytes of the pause: at the
call of the sound routine the state is split by the table, the routine is walked with the bytes known, and after the pause routine they must be in a state of the table and
are forgotten (but for the bits that the room's condition knows, `RoomPause.Reg.keepB`). The room's condition is taken with one more byte, the noise effect's queue.
The event music's queue is a byte of the table, not of the room's condition: the code of a fall into a hole stores it with a value that the walk does not know. The table
has 62 states: the music of the room, the hurry-up music, and songs read from that queue.

From the room's first control, where the rows of the time of the change into the room know these bytes, the bytes at the side pipe's entry are in a state of the table
(`music_run`). Every state of the table that admits the reference's `AreaMusicBuffer` knows five other bytes with the reference's values (`deriveCheck`). So `entry₂`
needs 11 bytes, not 16: `EntryRestM`, and `entryRest_of` gives `EntryRest` from it.

There is no game data in this file. Page: `1-1/d-2-5-1-RoomMusic.md`.
-/

namespace Smbrta.RoomMusic

open TaintRun (AS Env AB Sim bt bt_and bt_ext)
open ScreenPage (Places SiteOK RoomCond placesR envR refR knownOf Room)
open StepWrites (SState SIn soundLe)
open PipeTransitionAll (Names)
open PipeEntryRule (trace)
open PipeTransition (frame)

/-! ## The bytes -/

/-- a RAM index from a name and an offset -/
def ix (nm : Names) (n : String) (off : Nat := 0) : Nat := ((nm.ad n).toNat + off) &&& 0x7FF

/-- the area music's buffer -/
def amb (nm : Names) : Nat := ix nm "AreaMusicBuffer"

/-- the event music's queue -/
def emq (nm : Names) : Nat := ix nm "EventMusicQueue"

/-- the bit of the hurry-up music in the event music's queue -/
def hurryBit (nm : Names) : UInt8 := nm.vl "TimeRunningOutMusic"

/-- the bytes of the table: the event music's buffer, the song's pointer, square 1's offset, the noise effect's buffer, the added note length, the area music's buffer and
its copy, and the event music's queue -/
def tabIdx (nm : Names) : List Nat :=
  [ix nm "EventMusicBuffer", ix nm "MusicData", ix nm "MusicData" 1, ix nm "MusicOffset_Square1", ix nm "NoiseSoundBuffer", ix nm "NoteLengthTblAdder", amb nm,
   ix nm "AreaMusicBuffer_Alt", emq nm]

/-- the bytes of `EntryRest` that follow from the table and the area music's buffer -/
def derivedIdx (nm : Names) : List Nat :=
  [ix nm "EventMusicBuffer", ix nm "MusicData", ix nm "MusicData" 1, ix nm "MusicOffset_Square1", ix nm "NoiseSoundBuffer"]

/-- the byte added to the room's known bits: the noise effect's queue -/
def extraOf (nm : Names) : List (Nat × UInt8) := [(ix nm "NoiseSoundQueue", 0xFF)]

/-- the room's known bits with the noise effect's queue -/
def knownM (nm : Names) : List (Nat × UInt8) := knownOf nm ++ extraOf nm

/-- **the region and the table**: the region of `RoomPause` (the sound routine, the pads, the pause routine), the music bytes, the bits of them that the room's condition
knows, and no condition on the pause byte at a frame that leaves the room -/
def regM (sy : Syms) (m0 : Machine) (nm : Names) (T : List SState) : RoomPause.Reg :=
  let call := ScreenPage.findJsr m0 sy.NonMaskableInterrupt sy.SoundEngine 256
  { call, ret := call + 9, SB := tabIdx nm, gI := ix nm "GamePauseStatus", T,
    keepB := (knownM nm).filter (fun p => (tabIdx nm).contains p.1), needG := false }

/-- the configuration of the walk -/
abbrev cfgM (sy : Syms) (nm : Names) (m0 : Machine) (T : List SState) : ScreenPage.CfgS :=
  RoomPause.cfgOfP (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (regM sy m0 nm T) (refR m0) (knownM nm)

/-! ## The checks -/

/-- **The check of the walk on the ROM**, with the table `T` -/
def roomCheckM (sy : Syms) (nm : Names) (m0 : Machine) (T : List SState) : Bool :=
  RoomPause.walkCheck (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (regM sy m0 nm T) (refR m0) (knownM nm)

/-- the state knows the bits `msk` of byte `i` with the values of `v` -/
def knowsMasked (S : AS) (i : Nat) (msk v : UInt8) : Bool :=
  decide (i < 2048) && (S.getK i).k &&& msk == msk && (S.getK i).v &&& msk == v &&& msk

/-- a state of a row: it knows the bytes of control, and if it has control, it knows the bytes `X` as `r` has them, and each of its two pieces by the bit `b` of byte `q`
has its music bytes under a state of the table -/
def rowM (sy : Syms) (X : List (Nat × UInt8)) (q : Nat) (b : UInt8) (r : Machine) (T : List SState) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (SideChangeEnd.knowsAd S) && (!controllable sy (SideChangeEnd.mOf S) ||
    (X.all (fun p => knowsMasked S p.1 p.2 (r.ram.get! p.1)) && (TaintRun.splitBit q b S).all fun S' => T.any (soundLe S')))

/-- **The check at the room's first control**: in the rows of the time of the change into the room, every state with control knows the noise effect's queue, and each of
its two pieces by the bit of the hurry-up music in the event music's queue has its music bytes under a state of the table -/
def startCheckM (sy : Syms) (nm₁ : Names) (d : PipeChangeEnd.Data) (e : Machine) (nm : Names) (r : Machine) (T : List SState) : Bool :=
  (PipeChangeEnd.timeRows (PipeChangeEnd.timeCtx sy nm₁ d e) d e).all fun w => w.R.all (rowM sy (extraOf nm) (emq nm) (hurryBit nm) r T)

/-- the two checks at the room's first control, `RoomPause.startCheck` and `startCheckM`, with the rows made once -/
def startBoth (sy : Syms) (nm₁ : Names) (d : PipeChangeEnd.Data) (e : Machine) (nx nm : Names) (r : Machine) (T : List SState) : Bool :=
  let l := PipeChangeEnd.timeRows (PipeChangeEnd.timeCtx sy nm₁ d e) d e
  (l.all fun w => w.R.all (RoomPause.rowP sy (SideChangeSound.pauseIdx nx) (SidePause.pauseBytesOf nx))) &&
    (l.all fun w => w.R.all (rowM sy (extraOf nm) (emq nm) (hurryBit nm) r T))

theorem startBoth_parts {sy : Syms} {nm₁ : Names} {d : PipeChangeEnd.Data} {e : Machine} {nx nm : Names} {r : Machine} {T : List SState}
    (h : startBoth sy nm₁ d e nx nm r T = true) : RoomPause.startCheck sy nm₁ d e nx = true ∧ startCheckM sy nm₁ d e nm r T = true := by
  simp only [startBoth, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

/-- **The check of the table**: every state of the table that admits the value of the area music's buffer in `r` knows each byte of `derivedIdx` with the value in `r` -/
def deriveCheck (nm : Names) (r : Machine) (T : List SState) : Bool :=
  T.all fun t => !(t.all fun p => p.1 != amb nm || r.ram.get! p.1 &&& p.2.k == p.2.v &&& p.2.k) ||
    (derivedIdx nm).all fun i => t.any fun p => p.1 == i && p.2.v == r.ram.get! i && p.2.k == 0xFF

/-- the bytes of `EntryRest` without those that follow -/
def restIdxM (nm : Names) : List Nat := (ScreenPage.restIdx nm).filter fun i => !(derivedIdx nm).contains i

/-- **The condition on 11 bytes at the entry**: `EntryRest` on the bytes of `restIdxM` -/
def EntryRestM (nm : Names) (V : List (Machine × List Nat)) (m : Machine) : Prop :=
  ∃ v ∈ V, ∀ i ∈ v.2, i ∈ restIdxM nm → m.ram.get! i = v.1.ram.get! i

/-- **The check of the references**: each reference of the entry lists the area music's buffer, and has the values of `r` on it and on the bytes that follow; the area
music's buffer is a byte of `restIdxM` -/
def refsCheck (nm : Names) (r : Machine) (V : List (Machine × List Nat)) : Bool :=
  (restIdxM nm).contains (amb nm) &&
    V.all fun v => v.2.contains (amb nm) && (amb nm :: derivedIdx nm).all fun i => v.1.ram.get! i == r.ram.get! i

/-! ## The proofs -/

section
variable {E : Env} {F : Nat × UInt8}

theorem masked_of {a : AB} {x msk v : UInt8} (h : a.mem x) (hk : a.k &&& msk = msk) (hv : a.v &&& msk = v &&& msk) : x &&& msk = v &&& msk := by
  apply bt_ext
  intro i hi
  have m1 := TaintRun.mem_iff.1 h i hi
  have k1 := congrArg (fun y => bt y i) hk
  have v1 := congrArg (fun y => bt y i) hv
  simp only [bt_and] at k1 v1 ⊢
  revert m1 k1 v1
  generalize bt x i = p, bt a.k i = q, bt a.v i = s, bt msk i = u, bt v i = w
  revert p q s u w
  decide

theorem masked_of_knows {S : AS} {m : Machine} (hs : Sim E F S m) {i : Nat} {msk v : UInt8} (h : knowsMasked S i msk v = true) :
    m.ram.get! i &&& msk = v &&& msk := by
  simp only [knowsMasked, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact masked_of (hs.ram i h.1.1) h.1.2 h.2

theorem roomCond_append {r : Machine} {K X : List (Nat × UInt8)} {m : Machine} (h : RoomCond E r K m)
    (hx : ∀ p ∈ X, m.ram.get! p.1 &&& p.2 = r.ram.get! p.1 &&& p.2) : RoomCond E r (K ++ X) m :=
  { h with bytes := fun p hp => (List.mem_append.1 hp).elim (h.bytes p) (hx p) }

end

section
variable {sy : Syms}

theorem start_of_invL {c : SideChangeEnd.Ctx} {X : List (Nat × UInt8)} {q : Nat} {b : UInt8} {r : Machine} {T : List SState} (hq : q < 2048)
    (hb : b ∈ TaintRun.bitList) :
    ∀ {l : List SideChangeEnd.Row}, (l.all fun w => w.R.all (rowM sy X q b r T)) = true → ∀ {m : Machine},
    SideChangeEnd.InvL c l m → controllable sy m = true → (∀ p ∈ X, m.ram.get! p.1 &&& p.2 = r.ram.get! p.1 &&& p.2) ∧ ∃ t ∈ T, SIn t m
  | [], _, _, h, _ => by cases h
  | w :: l, hl, _, h, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · have hr := List.all_eq_true.1 hl.1 S hS
      simp only [rowM, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
      obtain ⟨hk, hr⟩ := hr
      rcases hr with h1 | ⟨hx, ht⟩
      · have := SurfaceFrames.controllable_of_known hs hk hc
        rw [this] at h1
        cases h1
      · refine ⟨fun p hp => masked_of_knows hs (List.all_eq_true.1 hx p hp), ?_⟩
        obtain ⟨S', hS', hs', _⟩ := TaintRun.cov_bit hq hb S _ hs
        obtain ⟨t, ht, hle⟩ := List.any_eq_true.1 (List.all_eq_true.1 ht S' hS')
        exact ⟨t, ht, StepWrites.sIn_of_le hs' hle⟩
    · exact start_of_invL hq hb hl.2 h hc

/-- **The bytes that follow**: a machine in a state of the table with the reference's area music buffer has the reference's values on the bytes of `derivedIdx` -/
theorem derive_spec {nm : Names} {r : Machine} {T : List SState} (h : deriveCheck nm r T = true) {t : SState} (ht : t ∈ T) {m : Machine} (hm : SIn t m)
    (ha : m.ram.get! (amb nm) = r.ram.get! (amb nm)) : ∀ i ∈ derivedIdx nm, m.ram.get! i = r.ram.get! i := by
  have h1 := List.all_eq_true.1 h t ht
  have hadm : (t.all fun p => p.1 != amb nm || r.ram.get! p.1 &&& p.2.k == p.2.v &&& p.2.k) = true := by
    refine List.all_eq_true.2 fun p hp => ?_
    rw [Bool.or_eq_true]
    by_cases hpa : p.1 = amb nm
    · right
      have hmem : m.ram.get! p.1 &&& p.2.k = p.2.v &&& p.2.k := hm p hp
      have e : r.ram.get! p.1 = m.ram.get! p.1 := by
        rw [hpa]
        exact ha.symm
      rw [e, hmem]
      exact beq_self_eq_true _
    · left
      simp [hpa]
  rw [hadm] at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
  intro i hi
  obtain ⟨p, hp, ⟨hp1, hp2⟩, hp3⟩ := h1 i hi
  have hmem := hm p hp
  rw [hp1] at hmem
  have hab : p.2 = AB.known (r.ram.get! i) := by
    cases hq : p.2
    rw [hq] at hp2 hp3
    simp only at hp2 hp3
    rw [hp2, hp3]
    rfl
  rw [hab] at hmem
  exact SidePause.eq_of_mem_known hmem

theorem refs_spec {nm : Names} {r : Machine} {V : List (Machine × List Nat)} (h : refsCheck nm r V = true) :
    amb nm ∈ restIdxM nm ∧ ∀ v ∈ V, amb nm ∈ v.2 ∧ ∀ i ∈ amb nm :: derivedIdx nm, v.1.ram.get! i = r.ram.get! i := by
  simp only [refsCheck, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun v hv => ⟨(h.2 v hv).1, (h.2 v hv).2⟩⟩

end

/-! ## For the route -/

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {V : List (Machine × List Nat)} {nmS : Names} {T : List SState}

/-- what the checks on the ROM give for the music in the room, with the table `T` -/
structure Facts (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (V : List (Machine × List Nat)) (nmS : Names) (T : List SState) : Prop where
  walk : RoomPause.PauseOK (envR sy nmS m0) (placesR sy nmS m0) (refR m0) (knownM nmS) (regM sy m0 nmS T) (cfgM sy nmS m0 T) ScreenPage.fuelS
  start : startCheckM sy nm₁ d₁ (PipeTransition.entry m0) nmS (refR m0) T = true
  derive : deriveCheck nmS (refR m0) T = true
  refs : refsCheck nmS (refR m0) V = true
  /-- the routine's byte is not among the bytes that follow -/
  rt : (derivedIdx nmS).contains (placesR sy nmS m0).rtI = false
  /-- the hurry-up music's value is one bit -/
  bit : hurryBit nmS ∈ TaintRun.bitList

theorem factsOf (h1 : roomCheckM sy nmS m0 T = true) (h2 : startCheckM sy nm₁ d₁ (PipeTransition.entry m0) nmS (refR m0) T = true)
    (h3 : deriveCheck nmS (refR m0) T = true) (h4 : refsCheck nmS (refR m0) V = true) (h5 : (derivedIdx nmS).contains (placesR sy nmS m0).rtI = false)
    (h6 : TaintRun.bitList.contains (hurryBit nmS) = true) : Facts sy m0 nm₁ d₁ V nmS T :=
  ⟨RoomPause.pauseOK_of_check h1, h2, h3, h4, h5, List.contains_iff_mem.1 h6⟩

/-- **The music bytes at the side pipe's entry are in a state of the table.** The room's first control `c` is in the room's condition and has control in the rows of
the time of the change into the room. Each frame from `c` to `e` meets `SiteOK` and starts in the player's routine, and `e` has another routine. -/
theorem music_run (hF : Facts sy m0 nm₁ d₁ V nmS T) (hrt : ((placesR sy nmS m0).rtI, (0xFF : UInt8)) ∈ knownOf nmS)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (hce : c ≤ e)
    (h0 : Room sy nmS m0 (seq c)) (hin : PipeChangeEnd.InRowsT sy nm₁ d₁ (PipeTransition.entry m0) (seq c)) (hctl : controllable sy (seq c) = true)
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    (he : (seq e).ram.get! (placesR sy nmS m0).rtI ≠ (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∃ t ∈ T, SIn t (seq e) := by
  have hq : emq nmS < 2048 := by
    have : emq nmS ≤ 0x7FF := Nat.and_le_right
    omega
  obtain ⟨hx, ht⟩ := start_of_invL hq hF.bit hF.start hin hctl
  have h0' : RoomCond (envR sy nmS m0) (refR m0) (knownM nmS) (seq c) := roomCond_append h0 hx
  exact (RoomPause.pause_run hF.walk (List.mem_append_left _ hrt) next hce h0' ht hs hr he).1

/-- **`EntryRest` from 11 bytes**, at a machine whose music bytes are in a state of the table -/
theorem entryRest_of (hF : Facts sy m0 nm₁ d₁ V nmS T) {m : Machine} (ht : ∃ t ∈ T, SIn t m) (hR : EntryRestM nmS V m) : ScreenPage.EntryRest nmS V m := by
  obtain ⟨v, hv, hb⟩ := hR
  obtain ⟨t, htT, hm⟩ := ht
  obtain ⟨hA, hrefs⟩ := refs_spec hF.refs
  obtain ⟨hav, hvr⟩ := hrefs v hv
  have hamb : m.ram.get! (amb nmS) = (refR m0).ram.get! (amb nmS) := by
    rw [hb _ hav hA]
    exact hvr _ List.mem_cons_self
  have hd := derive_spec hF.derive htT hm hamb
  refine ⟨v, hv, fun i hi1 hi2 => ?_⟩
  by_cases hdi : i ∈ derivedIdx nmS
  · rw [hd i hdi, hvr i (List.mem_cons_of_mem _ hdi)]
  · exact hb i hi1 (List.mem_filter.2 ⟨hi2, by simpa using hdi⟩)

/-- the routine's byte is a byte of the 11 when it is a byte of the 16 -/
theorem rt_mem (hF : Facts sy m0 nm₁ d₁ V nmS T) (h : (placesR sy nmS m0).rtI ∈ ScreenPage.restIdx nmS) : (placesR sy nmS m0).rtI ∈ restIdxM nmS :=
  List.mem_filter.2 ⟨h, by rw [hF.rt]; rfl⟩

end

end Smbrta.RoomMusic
