import Theorems.ScreenStart
import Theorems.SidePause

/-!
# The pause in the room, from the first control to the side pipe's entry

`SidePause` asks a condition on the pause at the side pipe's entry (`PauseE`): the pause is silent, or the unpause sound plays with the pause timer one more than its
counter, or the unpause was pressed on that frame. Here it is proved from the room's first control, by the room's frames, for any input, Start included.

The six bytes of the pause (`SidePause.pauseKeep`: the queue, the buffer, the flag and the counter of the pause sound, the pause timer, the pause byte) are written only
by the sound routine and by the pause routine. The handler calls the sound routine, the reading of the pads and the pause routine one after another. The walk of one
frame in the room (`ScreenPage`) is taken with a table of states of the six bytes carried outside the abstract state: the classes of `SidePause.classesP`. At the call of
the sound routine the state is split by the classes and marked (`spent`); the three routines are walked with the six bytes known; at the return of the pause routine the
bytes must be in a class, and they are forgotten, but for bit 0 of the pause byte (paused or not). Outside the three routines every step keeps the six bytes (`keepP`).
So a frame that starts with the bytes in a class ends with them in a class (`pause_step`; the walk checks that no other step writes them). At the frame that enters the side pipe the game's routine has run, so the frame
is not paused, and the class is one of `PauseE` (`pause_run`).

The state at the room's first control is in a class: the rows of the change into the room know there that the pause is silent and not paused (`startCheck`), and
with bits 1 to 6 of the pause byte 0, which those rows do not know, the pause byte is 0 or has only bit 7 (`class_of_rows`).

There is no game data in this file. Page: `1-1/d-3-4-4-RoomPause.md`.
-/

namespace Smbrta.RoomPause

open TaintRun (AS Env AB Sim AM aRows StepRel sim_le mem_top bt bt_and bt_ext)
open ScreenPage (Places SiteOK PlacesOK clampS preS stepS CfgS coverS weaken startsR endUnder RoomCond MaskOK)
open StepWrites (SState SIn soundLe refineAll agrees forgetAll retag keepOK tabOK)
open PipeEntryRule (trace nxt frame_trace)
open PipeTransition (frame)
open PipeTransitionAll (go Names)

/-! ## The step -/

/-- the region of the walk: the call of the sound routine, the place after the call of the pause routine, the six bytes, the pause byte, and the table -/
structure Reg where
  call : UInt16
  ret : UInt16
  SB : List Nat
  gI : Nat
  T : List SState

/-- `B` with bit 0 of the pause byte as `B0` knows it, and no other bit of it -/
def keep0 (gI : Nat) (B0 B : AS) : AS := B.setK gI ⟨(B0.getK gI).v &&& 1, (B0.getK gI).k &&& 1⟩

/-- the step of `ScreenPage`: the pieces of `preS` after the clamp of the time, then `stepS` -/
def baseS (P : Places) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) := (preS P (clampS P A)).flatMap (stepS P E ops)

/-- the write that erases a coin does not reach the six bytes: they are outside the block buffers -/
def eraseKeeps (P : Places) (SB : List Nat) : Bool := SB.all fun i => decide (i < P.bufLo) || decide (P.bufLo + P.bufN ≤ i)

/-- the step of `A` keeps the six bytes: it is the erase of a coin (into the block buffers, by `SiteOK`), or `keepOK` -/
def keepP (P : Places) (E : Env) (SB : List Nat) (A : AS) : Bool :=
  (!A.nmi && A.pc == P.erase && eraseKeeps P SB) || keepOK E (fun i => SB.contains i) A

/-- a successor in the three routines: at the place after them, the bytes are in a class and are forgotten, but for bit 0 of the pause byte -/
def inP (G : Reg) (A B : AS) : Option AS :=
  if B.pc == G.ret && B.k == A.k then (if G.T.any (soundLe B) then some (keep0 G.gI B (retag false (forgetAll G.SB B))) else none)
  else some (retag true B)

/-- **The step with the region split.** In the region (`spent`): the step of `ScreenPage`, and at its end the check and the forgetting. At the call: the pieces of the
table, marked. Elsewhere: the step of `ScreenPage` from the pieces that keep the six bytes. -/
def pstep (P : Places) (E : Env) (ops : Array (AM Unit)) (G : Reg) (A : AS) : List (Option AS) :=
  if A.spent then (baseS P E ops A).map fun o => o.bind (inP G A)
  else if A.pc == G.call then
    G.T.flatMap fun t => if agrees t A then (baseS P E ops (refineAll t A)).map fun o => o.map (retag true) else []
  else (preS P (clampS P A)).flatMap fun A₁ => if keepP P E G.SB A₁ then stepS P E ops A₁ else [none]

/-- outside the region the six bytes are in a class -/
def Ph (G : Reg) (A : AS) (m : Machine) : Prop := A.spent = true ∨ ∃ t ∈ G.T, SIn t m

/-! ## The walk -/

/-- at the frame's end: out of the region, and a start state of the room's condition, or the routine is known and is not the reference's and the pause byte's bit 0 is
known to be 0 -/
def finP (P : Places) (r : Machine) (K : List (Nat × UInt8)) (gI : Nat) (B : AS) : Bool :=
  !B.spent && (endUnder r K B ||
    (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI && (B.getK gI).k &&& 1 == 1 && (B.getK gI).v &&& 1 == 0))

/-- from `A`, step by step with `pstep`, until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def walkP (G : Reg) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (pstep C.P C.E C.ops G A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkP G C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-! ## Finding the table: a search, no part of the proof -/

section
open ScreenPage (Aids SearchS)

/-- `SearchS.put` with the whole key in the order: the keys here are longer than 200 bits (and shorter than 640 with `keyP`) -/
def putP (X : SearchS) (K : Nat) (B : AS) : SearchS :=
  let q := B.lo * (1 <<< 640) + K
  let pend := match X.pendKey[K]? with
    | some r => X.pending.erase r
    | none => X.pending
  { X with pending := pend.insert q B, pendKey := X.pendKey.insert K q }

/-- the key of `Z` with all its bits mixed into the low 64: a `Nat` is hashed by its low 64 bits -/
def keyP (Z : Aids) (E : Env) (A : AS) : Nat :=
  let K := Z.key E A
  K * 18446744073709551616 + K % 18446744073709551557

/-- `ScreenPage.routeS` with `putP` and `keyP` -/
def routeP (P : Places) (Z : Aids) (E : Env) (X : SearchS) (B0 : AS) : SearchS :=
  let B := clampS P (Z.norm B0)
  let K := keyP Z E B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D =>
    if B.le D then X else
    let J := D.join B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 then { J with hi := P.late } else J
    putP { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => putP { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

partial def runP (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (G : Reg) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := pstep P E ops G cur
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (Z.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeP P Z E X b
    break
  return X

partial def searchP (P : Places) (Z : Aids) (E : Env) (ops : Array (AM Unit)) (G : Reg) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := keyP Z E A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runP P Z E ops G X A
  return X

/-- the aids of the search, with the six bytes among the bytes that keep states apart -/
def aidsP (Z : Aids) (G : Reg) : Aids := { Z with keep := Z.keep ++ G.SB }

def searchOfP (P : Places) (Z : Aids) (E : Env) (G : Reg) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let Z := aidsP Z G
  searchP P Z E (aRows E).toArray G ((startsR r K).foldl (routeP P Z E) {})

/-- the configuration from the table found -/
def cfgOfP (P : Places) (Z : Aids) (E : Env) (G : Reg) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOfP P Z E G r K
  let Z := aidsP Z G
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd]).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin := finP P r K G.gI, t := q.1, key := keyP Z E, idx := q.2.1, cut := q.2.2, norm := Z.norm, normAt := at0 }

end

/-! ## The check -/

/-- **The check of the walk.** -/
def walkCheck (P : Places) (Z : ScreenPage.Aids) (E : Env) (G : Reg) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOfP P Z E G r K
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K && tabOK G.SB G.T && decide (G.gI < 2048) &&
    C.t.all (walkP G C ScreenPage.fuelS) && (startsR r K).all (walkP G C ScreenPage.fuelS)

/-! ## The region and the room, from the symbols -/

/-- the region: the call of the sound routine in the handler, and the place after the next two calls (the pads and the pause); the six bytes and the classes -/
def regOf (sy : Syms) (m0 : Machine) (nx : Names) : Reg :=
  let call := ScreenPage.findJsr m0 sy.NonMaskableInterrupt sy.SoundEngine 256
  let ix := SideChangeSound.pauseIdx nx
  let pb := SidePause.pauseBytesOf nx
  { call, ret := call + 9, SB := SidePause.pauseKeep ix pb, gI := pb.g, T := SidePause.classesP sy ix pb }

/-- the configuration of the room's walk -/
abbrev cfgR (sy : Syms) (nm nx : Names) (m0 : Machine) : CfgS :=
  cfgOfP (ScreenPage.placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (ScreenPage.envR sy nm m0) (regOf sy m0 nx) (ScreenPage.refR m0) (ScreenPage.knownOf nm)

/-- **The check on the ROM**: the walk of one frame in the room with the pause's region, and the length of the pause sound below 255 -/
def roomCheck (sy : Syms) (nm nx : Names) (m0 : Machine) : Bool :=
  walkCheck (ScreenPage.placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (ScreenPage.envR sy nm m0) (regOf sy m0 nx) (ScreenPage.refR m0) (ScreenPage.knownOf nm) &&
    decide (sy.PauseSfxLength.toNat + 1 < 256)

/-! ## At the first control: from the rows of the change into the room -/

/-- a state of a row: it says whether it has control, and if it has, the queue and the buffer of the pause sound are known to be 0 and bit 0 of the pause byte is known to
be 0 -/
def rowP (sy : Syms) (ix : SideChangeSound.PauseIdx) (pb : SidePause.PauseBytes) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (SideChangeEnd.knowsAd S) && (!controllable sy (SideChangeEnd.mOf S) ||
    (TaintRun.knownIs S (ix.q, 0) && TaintRun.knownIs S (ix.b, 0) && decide (pb.g < 2048) && (S.getK pb.g).k &&& 1 == 1 && (S.getK pb.g).v &&& 1 == 0))

/-- **The check on the ROM**: in the rows of the time of the change into the room, a state with control knows that the pause is silent and not paused -/
def startCheck (sy : Syms) (nm : Names) (d : PipeChangeEnd.Data) (e : Machine) (nx : Names) : Bool :=
  (PipeChangeEnd.timeRows (PipeChangeEnd.timeCtx sy nm d e) d e).all fun w => w.R.all (rowP sy (SideChangeSound.pauseIdx nx) (SidePause.pauseBytesOf nx))

/-! ## The step follows the machine -/

section
variable {E : Env} {F : Nat × UInt8} {P : Places} {ops : Array (AM Unit)} {G : Reg}

/-- a byte with only its bit 0 known holds the byte -/
theorem mem_low {a : AB} {x : UInt8} (h : a.mem x) : (⟨a.v &&& 1, a.k &&& 1⟩ : AB).mem x := by
  refine TaintRun.mem_iff.2 fun i hi => ?_
  have a1 := TaintRun.mem_iff.1 h i hi
  show (bt x i && bt (a.k &&& 1) i) = (bt (a.v &&& 1) i && bt (a.k &&& 1) i)
  rw [bt_and, bt_and]
  revert a1
  generalize bt x i = p, bt a.v i = q, bt a.k i = s, bt 1 i = u
  revert p q s u
  decide

/-- bit 0 known to be 0 -/
theorem low_of_mem {a : AB} {x : UInt8} (h : a.mem x) (hk : a.k &&& 1 = 1) (hv : a.v &&& 1 = 0) : x &&& 1 = 0 := by
  have m0 := TaintRun.mem_iff.1 h 0 (by decide)
  have k0 : bt a.k 0 = true := by
    have h1 := congrArg (fun y => bt y 0) hk
    simp only [bt_and, TaintRun.bt_one (show 0 < 8 by decide)] at h1
    simpa using h1
  have v0 : bt a.v 0 = false := by
    have h1 := congrArg (fun y => bt y 0) hv
    simp only [bt_and, TaintRun.bt_one (show 0 < 8 by decide), TaintRun.bt_zero (show 0 < 8 by decide)] at h1
    simpa using h1
  apply bt_ext
  intro j hj
  rw [bt_and, TaintRun.bt_one hj, TaintRun.bt_zero hj]
  by_cases h0 : j = 0
  · subst h0
    rw [k0, v0] at m0
    simpa using m0
  · simp [h0]

theorem sim_keep0 {B0 B : AS} {m : Machine} {gI : Nat} (hs0 : Sim E F B0 m) (hs : Sim E F B m) (hg : gI < 2048) : Sim E F (keep0 gI B0 B) m :=
  SideChangeEnd.sim_refine hs (mem_low (hs0.ram gI hg))

theorem clamp_spent (A : AS) : (clampS P A).spent = A.spent := by
  unfold clampS
  split <;> rfl

/-- **The step of `ScreenPage` follows the machine**, from the pieces after the clamp -/
theorem s_baseS (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK P m) :
    ∃ r ∈ baseS P E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
  obtain ⟨A₁, hA, hs1, hk1⟩ := ScreenPage.cov_preS hO hs0 hh
  obtain ⟨r, hr, hB⟩ := ScreenPage.s_stepS hO hops hT hs1 hh
  refine ⟨r, List.mem_flatMap.2 ⟨A₁, hA, hr⟩, fun B hB' => ?_⟩
  obtain ⟨g1, g2⟩ := hB B hB'
  exact ⟨g1, StepWrites.stepRel_k (by rw [hk1, ScreenPage.clamp_k]) rfl g2⟩

/-- **A step that `keepP` allows keeps the six bytes** -/
theorem keepP_ok (hO : PlacesOK E P) {SB : List Nat} {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK P m) (hk : keepP P E SB A = true) :
    ∀ i, SB.contains i = true → (go step m).2.ram.get! i = m.ram.get! i := by
  unfold keepP at hk
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hk
  rcases hk with ⟨⟨hn, hpc⟩, hek⟩ | hk
  · intro i hi
    apply StepWrites.step_ram
    intro hm
    unfold StepWrites.stepLocs at hm
    have hn' : m.nmiPending = false := by rw [hs.nmi]; exact hn
    have hpm : m.pc = P.erase := by rw [hs.pc]; exact hpc
    rw [if_neg (by simp [hn']), if_neg (by simp [hs.halted])] at hm
    have hge : m.pc ≥ 0x8000 := by rw [hpm]; exact hO.erase.1
    rw [TaintRun.fetch_rom hge] at hm
    have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91 := by rw [hs.prg, hs.mask, hpm]; exact hO.erase.2
    rw [hop] at hm
    have hw : StepWrites.wOf 0x91 = StepWrites.wIzy := rfl
    rw [hw] at hm
    simp only [StepWrites.Wr.locs] at hm
    obtain ⟨g1, g2, g3⟩ := hh.erase hpm
    have e1 : (go mIzy { m with pc := m.pc + 1 }).1 = ScreenPage.writeAddr m := rfl
    rw [e1] at hm
    unfold StepWrites.ramIdx at hm
    rw [if_pos g1] at hm
    simp only [List.mem_singleton] at hm
    have h2 := List.all_eq_true.1 hek i (by simpa using hi)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
    omega
  · exact StepWrites.keep_step hs hk

/-- **One step**: `pstep` follows the machine, and `Ph` goes on -/
theorem s_pstep (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (h0 : tabOK G.SB G.T = true) (hg : G.gI < 2048)
    {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK P m) (hph : Ph G A m) :
    ∃ r ∈ pstep P E ops G A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 ∧ Ph G B (go step m).2 := by
  have tab : ∀ t ∈ G.T, ∀ p ∈ t, G.SB.contains p.1 = true ∧ p.1 < 2048 := by
    intro t ht p hp
    simp only [tabOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h0
    exact h0 t ht p hp
  unfold pstep
  by_cases hsp : A.spent = true
  · rw [if_pos hsp]
    obtain ⟨r, hr, hB⟩ := s_baseS hO hops hT hs hh
    refine ⟨r.bind (inP G A), List.mem_map.2 ⟨r, hr, rfl⟩, fun B hB' => ?_⟩
    cases r with
    | none => cases hB'
    | some B0 =>
      obtain ⟨g1, g2⟩ := hB B0 rfl
      simp only [Option.bind_some, inP] at hB'
      split at hB'
      · split at hB'
        · rename_i _ hany
          simp only [Option.some.injEq] at hB'
          subst hB'
          obtain ⟨t, ht, hle⟩ := List.any_eq_true.1 hany
          exact ⟨sim_keep0 g1 (StepWrites.sim_retag _ (StepWrites.sim_forgetAll _ g1)) hg,
            StepWrites.stepRel_k rfl (StepWrites.forgetAll_k _ _) g2, Or.inr ⟨t, ht, StepWrites.sIn_of_le g1 hle⟩⟩
        · cases hB'
      · simp only [Option.some.injEq] at hB'
        subst hB'
        exact ⟨StepWrites.sim_retag _ g1, StepWrites.stepRel_k rfl rfl g2, Or.inl rfl⟩
  · rw [if_neg hsp]
    obtain ⟨t, ht, htm⟩ : ∃ t ∈ G.T, SIn t m := by
      rcases hph with h | h
      · exact absurd h hsp
      · exact h
    by_cases hc : (A.pc == G.call) = true
    · rw [if_pos hc]
      have hag : agrees t A = true := StepWrites.agrees_of hs (fun p hp => (tab t ht p hp).2) htm
      obtain ⟨r, hr, hB⟩ := s_baseS hO hops hT (StepWrites.sim_refineAll t hs htm) hh
      refine ⟨r.map (retag true), List.mem_flatMap.2 ⟨t, ht, by rw [if_pos hag]; exact List.mem_map.2 ⟨r, hr, rfl⟩⟩, fun B hB' => ?_⟩
      cases r with
      | none => cases hB'
      | some B0 =>
        simp only [Option.map_some, Option.some.injEq] at hB'
        subst hB'
        obtain ⟨g1, g2⟩ := hB B0 rfl
        exact ⟨StepWrites.sim_retag _ g1, StepWrites.stepRel_k (StepWrites.refineAll_k t A).symm rfl g2, Or.inl rfl⟩
    · rw [if_neg hc]
      have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
      obtain ⟨A₁, hA, hs1, hk1⟩ := ScreenPage.cov_preS hO hs0 hh
      by_cases hk : keepP P E G.SB A₁ = true
      · obtain ⟨r, hr, hB⟩ := ScreenPage.s_stepS hO hops hT hs1 hh
        refine ⟨r, List.mem_flatMap.2 ⟨A₁, hA, by rw [if_pos hk]; exact hr⟩, fun B hB' => ?_⟩
        obtain ⟨g1, g2⟩ := hB B hB'
        exact ⟨g1, StepWrites.stepRel_k (by rw [hk1, ScreenPage.clamp_k]) rfl g2,
          Or.inr ⟨t, ht, StepWrites.sIn_keep (fun p hp => (tab t ht p hp).1) htm (keepP_ok hO hs1 hh hk)⟩⟩
      · refine ⟨none, List.mem_flatMap.2 ⟨A₁, hA, by rw [if_neg hk]; exact List.mem_singleton.2 rfl⟩, fun B hB => by cases hB⟩

end

/-! ## The walk covers the frame -/

section
variable {G : Reg} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` with `Ph`, and a walk from `A` succeeds -/
def LiveP (G : Reg) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ Ph G A m ∧ ∃ n, walkP G C n A = true

theorem ph_of_spent {A B : AS} {m : Machine} (he : A.spent = B.spent) (h : Ph G A m) : Ph G B m := by
  unfold Ph at h ⊢
  rw [← he]
  exact h

theorem cover_liveP (ht : C.t.all (walkP G C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph G B m) (h : coverS C B = true) :
    ∃ D, LiveP G C F D m ∧ D.k = B.k := by
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
    exact ⟨D, ⟨sim_le hle hs, ph_of_spent (StepWrites.le_pc_spent hle).2 hp, Fu, hall⟩, hk⟩
  · cases h2

theorem weaken_of {B : AS} {m : Machine} (hs : Sim C.E F B m) :
    Sim C.E F (weaken C B) m ∧ (weaken C B).k = B.k ∧ (weaken C B).spent = B.spent := by
  unfold weaken
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    refine ⟨sim_le hc.2 hs, ?_, (StepWrites.le_pc_spent hc.2).2.symm⟩
    have hle := hc.2
    simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
    exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
  · exact ⟨hs, rfl, rfl⟩

theorem live_stepP (hO : PlacesOK C.E C.P) (ht : C.t.all (walkP G C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : tabOK G.SB G.T = true) (hg : G.gI < 2048) {A : AS} {m : Machine} (hl : LiveP G C F A m)
    (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) :
    (∃ A', LiveP G C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph G B (go step m).2) := by
  obtain ⟨hs, hp, n, hw⟩ := hl
  cases n with
  | zero => simp [walkP] at hw
  | succ n =>
    obtain ⟨r, hr, hB⟩ := s_pstep hO hops hT h0 hg hs hh hp
    simp only [walkP, List.all_eq_true] at hw
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨g1, g2, g3⟩ := hB B rfl
      dsimp only at hw2
      rcases g2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        obtain ⟨n1, n2, n3⟩ := weaken_of (C := C) g1
        have hpW : Ph G (weaken C B) (go step m).2 := ph_of_spent n3.symm g3
        rcases hw2 with ⟨_, h3⟩ | h3
        · have hpC : Ph G (clampS C.P (weaken C B)) (go step m).2 := ph_of_spent (clamp_spent _).symm hpW
          obtain ⟨D, hD, hk⟩ := cover_liveP ht (ScreenPage.sim_clamp hO.late n1 hh2.late) hpC h3
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, n2, k1], k2, k3⟩
        · exact ⟨_, ⟨n1, hpW, n, h3⟩, by rw [n2, k1], k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, g1, g3⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S` for every input, if each instruction meets `SiteOK`, and `Ph` holds at its end. -/
theorem frame_of_walkP (hO : PlacesOK C.E C.P) (ht : C.t.all (walkP G C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (h0 : tabOK G.SB G.T = true) (hg : G.gI < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkP G C Fu S = true) (hs : Sim C.E F S m) (hph : Ph G S m) (hk : ∀ j, SiteOK C.P (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) ∧ Ph G B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have key : ∀ j, (∃ A, LiveP G C F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j) ∧ Ph G B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, hph0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4, h5⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hk (j + 1)
        rw [e2] at hh2 ⊢
        rcases live_stepP hO ht hops hT h0 hg h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4, a5⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4, a5⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3, h4, h5⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h3, h4, h5⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact ⟨h1, B, h2, h3, h4, h5⟩

end

/-! ## The room's frames -/

/-- the six bytes are in a class -/
def InCls (G : Reg) (m : Machine) : Prop := ∃ t ∈ G.T, SIn t m

/-- what the check says -/
structure PauseOK (E : Env) (P : Places) (r : Machine) (K : List (Nat × UInt8)) (G : Reg) (C : CfgS) (Fu : Nat) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = finP P r K G.gI
  tab : tabOK G.SB G.T = true
  gI : G.gI < 2048
  table : C.t.all (walkP G C Fu) = true
  starts : ∀ S ∈ startsR r K, walkP G C Fu S = true

theorem pauseOK_of_check {P : Places} {Z : ScreenPage.Aids} {E : Env} {G : Reg} {r : Machine} {K : List (Nat × UInt8)} (h : walkCheck P Z E G r K = true) :
    PauseOK E P r K G (cfgOfP P Z E G r K) ScreenPage.fuelS := by
  simp only [walkCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, rfl, h4, h5, h6, h7⟩

/-- **One frame in the room.** A frame that starts in the room's condition with the six bytes in a class ends with them in a class, and in the condition, or with
another routine and not paused. -/
theorem pause_step {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {G : Reg} {C : CfgS} {Fu : Nat} (h : PauseOK E P r K G C Fu)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) (hc : InCls G m) :
    InCls G (frame m i) ∧ (RoomCond E r K (frame m i) ∨ ((frame m i).ram.get! P.rtI ≠ r.ram.get! P.rtI ∧ (frame m i).ram.get! G.gI &&& 1 = 0)) := by
  obtain ⟨S, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S hS
  have hs' : Sim C.E (m.frame, 2) S m := by rw [h.env]; exact hs
  obtain ⟨_, B, h2, _, h4, h5⟩ := frame_of_walkP (i := i) hO h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) h.tab h.gI hw hs'
    (Or.inr hc) (by rw [h.pl]; exact hk)
  rw [h.env] at h4
  rw [h.fin] at h2
  unfold finP at h2
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq, beq_iff_eq] at h2
  obtain ⟨hsp, h2⟩ := h2
  have hcls : InCls G (frame m i) := by
    rcases h5 with h5 | h5
    · rw [hsp] at h5; cases h5
    · exact h5
  refine ⟨hcls, ?_⟩
  rcases h2 with h2 | ⟨⟨⟨⟨a3, a4⟩, a5⟩, a6⟩, a7⟩
  · exact Or.inl (ScreenPage.room_of_end h.mask h4 h2)
  · right
    have e := PipeEntryRule.known_eq a4 (h4.ram _ a3)
    refine ⟨by rw [e]; exact a5, low_of_mem (h4.ram G.gI h.gI) a6 a7⟩

/-- **The room's frames.** From the first control `c` with the six bytes in a class, up to the first machine `e` with another routine: each frame meets `SiteOK`
and starts in the player's routine. Then at `e` the six bytes are in a class and the frame before `e` was not paused. -/
theorem pause_run {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {G : Reg} {C : CfgS} {Fu : Nat} (h : PauseOK E P r K G C Fu)
    (hrt : (P.rtI, (0xFF : UInt8)) ∈ K)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (hce : c ≤ e)
    (h0 : RoomCond E r K (seq c)) (hc0 : InCls G (seq c))
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK P (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! P.rtI = r.ram.get! P.rtI)
    (he : (seq e).ram.get! P.rtI ≠ r.ram.get! P.rtI) :
    InCls G (seq e) ∧ (seq e).ram.get! G.gI &&& 1 = 0 := by
  have rtOf : ∀ {m : Machine}, RoomCond E r K m → m.ram.get! P.rtI = r.ram.get! P.rtI := by
    intro m hm
    exact ScreenPage.byte_of_ff (hm.bytes _ hrt)
  have key : ∀ d, c + d ≤ e → InCls G (seq (c + d)) ∧
      (RoomCond E r K (seq (c + d)) ∨ ((seq (c + d)).ram.get! P.rtI ≠ r.ram.get! P.rtI ∧ (seq (c + d)).ram.get! G.gI &&& 1 = 0)) := by
    intro d
    induction d with
    | zero => exact fun _ => ⟨hc0, Or.inl h0⟩
    | succ d ih =>
      intro hd
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hm : RoomCond E r K (seq (c + d)) := by
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd (hr (c + d) (by omega) (by omega)) h2.1
      have e1 : c + (d + 1) = c + d + 1 := rfl
      rw [e1, next]
      exact pause_step h hm (hs (c + d) (by omega) (by omega)) h1
  obtain ⟨d, rfl⟩ : ∃ d, e = c + d := ⟨e - c, by omega⟩
  obtain ⟨h1, h2⟩ := key d (Nat.le_refl _)
  rcases h2 with h2 | h2
  · exact absurd (rtOf h2) he
  · exact ⟨h1, h2.2⟩

/-! ## The classes that are not paused -/

section
variable {sy : Syms} {ix : SideChangeSound.PauseIdx} {pb : SidePause.PauseBytes}

theorem eq_of_sIn {t : SState} {m : Machine} (h : SIn t m) {i : Nat} {v : UInt8} (hp : (i, AB.known v) ∈ t) : m.ram.get! i = v :=
  SidePause.eq_of_mem_known (h _ hp)

/-- **A machine in a class whose pause byte has bit 0 clear meets `PauseE`** (the length of the sound is below 255) -/
theorem pauseE_of_class (hL : sy.PauseSfxLength.toNat + 1 < 256) {t : SState} (ht : t ∈ SidePause.classesP sy ix pb) {m : Machine} (hm : SIn t m)
    (hg : m.ram.get! pb.g &&& 1 = 0) : SidePause.PauseE sy ix pb m := by
  unfold SidePause.classesP at ht
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.mem_range] at ht
  rcases ht with ((((((rfl | rfl) | ⟨j, hj, rfl⟩) | rfl) | rfl) | ⟨j, hj, rfl⟩) | (rfl | rfl | rfl))
  · exact Or.inl ⟨Or.inl (eq_of_sIn hm (by simp)), eq_of_sIn hm (by simp), eq_of_sIn hm (by simp)⟩
  · exact Or.inl ⟨Or.inr (eq_of_sIn hm (by simp)), eq_of_sIn hm (by simp), eq_of_sIn hm (by simp)⟩
  · have hc : m.ram.get! ix.c = (j + 1).toUInt8 := eq_of_sIn hm (by simp)
    have htt : m.ram.get! pb.t = (j + 2).toUInt8 := eq_of_sIn hm (by simp)
    have hc' := SidePause.toNat_of_toUInt8 hc (by omega)
    have ht' := SidePause.toNat_of_toUInt8 htt (by omega)
    exact Or.inr (Or.inl ⟨eq_of_sIn hm (by simp), eq_of_sIn hm (by simp), eq_of_sIn hm (by simp), eq_of_sIn hm (by simp), by omega, by omega, by omega⟩)
  · have htt : m.ram.get! pb.t = (sy.PauseSfxLength.toNat + 1).toUInt8 := eq_of_sIn hm (by simp)
    exact Or.inr (Or.inr ⟨eq_of_sIn hm (by simp), eq_of_sIn hm (by simp), eq_of_sIn hm (by simp), eq_of_sIn hm (by simp),
      SidePause.toNat_of_toUInt8 htt (by omega)⟩)
  · have := eq_of_sIn (i := pb.g) (v := 0x81) hm (by simp)
    rw [this] at hg
    exact absurd hg (by decide)
  · have := eq_of_sIn (i := pb.g) (v := 0x81) hm (by simp)
    rw [this] at hg
    exact absurd hg (by decide)
  · have := eq_of_sIn (i := pb.g) (v := 0x81) hm (by simp)
    rw [this] at hg
    exact absurd hg (by decide)
  · have := eq_of_sIn (i := pb.g) (v := 0x81) hm (by simp)
    rw [this] at hg
    exact absurd hg (by decide)
  · have := eq_of_sIn (i := pb.g) (v := 1) hm (by simp)
    rw [this] at hg
    exact absurd hg (by decide)

end

/-! ## At the first control -/

section
variable {sy : Syms} {nm nx : Names} {d : PipeChangeEnd.Data} {e : Machine}

set_option maxRecDepth 100000 in
theorem bits_all : ((List.range 256).all fun n => !(n.toUInt8 &&& 1 == 0 && n.toUInt8 &&& 0x7E == 0) || n.toUInt8 == 0 || n.toUInt8 == 0x80) = true := by decide

theorem bits_of_low (x : UInt8) (h1 : x &&& 1 = 0) (h2 : x &&& 0x7E = 0) : x = 0 ∨ x = 0x80 := by
  have h := List.all_eq_true.1 bits_all x.toNat (List.mem_range.2 x.toNat_lt)
  have e : x.toNat.toUInt8 = x := by simp
  rw [e, h1, h2] at h
  simpa using h

/-- the queue and the buffer of the pause sound are 0, and the pause byte is 0 or has only bit 7: the first two classes -/
theorem class_of_silent {ix : SideChangeSound.PauseIdx} {pb : SidePause.PauseBytes} {m : Machine} (hq : m.ram.get! ix.q = 0) (hb : m.ram.get! ix.b = 0)
    (hg : m.ram.get! pb.g &&& 1 = 0) (hg2 : m.ram.get! pb.g &&& 0x7E = 0) : ∃ t ∈ SidePause.classesP sy ix pb, SIn t m := by
  rcases bits_of_low _ hg hg2 with h | h
  · refine ⟨[(ix.q, AB.known 0), (ix.b, AB.known 0), (pb.g, AB.known 0)], by simp [SidePause.classesP], ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact SidePause.mem_known_of_eq hq
    · exact SidePause.mem_known_of_eq hb
    · exact SidePause.mem_known_of_eq h
  · refine ⟨[(ix.q, AB.known 0), (ix.b, AB.known 0), (pb.g, AB.known 0x80)], by simp [SidePause.classesP], ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact SidePause.mem_known_of_eq hq
    · exact SidePause.mem_known_of_eq hb
    · exact SidePause.mem_known_of_eq h

theorem class_of_invL {c : SideChangeEnd.Ctx} {ix : SideChangeSound.PauseIdx} {pb : SidePause.PauseBytes} :
    ∀ {l : List SideChangeEnd.Row}, (l.all fun w => w.R.all (rowP sy ix pb)) = true → ∀ {m : Machine},
    SideChangeEnd.InvL c l m → controllable sy m = true → m.ram.get! pb.g &&& 0x7E = 0 → ∃ t ∈ SidePause.classesP sy ix pb, SIn t m
  | [], _, _, h, _, _ => by cases h
  | w :: l, hl, _, h, hc, hg2 => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · have hr := List.all_eq_true.1 hl.1 S hS
      simp only [rowP, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq, decide_eq_true_eq] at hr
      obtain ⟨hk, hr⟩ := hr
      rcases hr with h1 | ⟨⟨⟨⟨hq, hb⟩, hgi⟩, hgk⟩, hgv⟩
      · have := SurfaceFrames.controllable_of_known hs hk hc
        rw [this] at h1
        cases h1
      · exact class_of_silent (TaintRun.sim_known hs hq) (TaintRun.sim_known hs hb) (low_of_mem (hs.ram _ hgi) hgk hgv) hg2
    · exact class_of_invL hl.2 h hc hg2

/-- **The six bytes at the first control in the room are in a class**, for a machine with control in the rows of the time whose pause byte has bits 1 to 6 clear -/
theorem class_of_rows (hc : startCheck sy nm d e nx = true) {m : Machine} (h : PipeChangeEnd.InRowsT sy nm d e m) (hm : controllable sy m = true)
    (hg : m.ram.get! (SidePause.pauseBytesOf nx).g &&& 0x7E = 0) :
    ∃ t ∈ SidePause.classesP sy (SideChangeSound.pauseIdx nx) (SidePause.pauseBytesOf nx), SIn t m :=
  class_of_invL hc h hm hg

end

/-! ## For the route -/

section
open ScreenPage (placesR envR refR knownOf Room)
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nx₂ nmS : Names}

/-- what the checks on the ROM give for the pause in the room -/
structure Facts (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nx₂ nmS : Names) : Prop where
  walk : PauseOK (envR sy nmS m0) (placesR sy nmS m0) (refR m0) (knownOf nmS) (regOf sy m0 nx₂) (cfgR sy nmS nx₂ m0) ScreenPage.fuelS
  start : startCheck sy nm₁ d₁ (PipeTransition.entry m0) nx₂ = true
  len : sy.PauseSfxLength.toNat + 1 < 256

theorem factsOf (h1 : roomCheck sy nmS nx₂ m0 = true) (h2 : startCheck sy nm₁ d₁ (PipeTransition.entry m0) nx₂ = true) : Facts sy m0 nm₁ d₁ nx₂ nmS := by
  simp only [roomCheck, Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨pauseOK_of_check h1.1, h2, h1.2⟩

/-- **The condition on the pause at the side pipe's entry.** The room's first control `c` is in the room's condition, has control in the rows of the time of the
change into the room, and its pause byte has bits 1 to 6 clear. Each frame from `c` to `e` meets `SiteOK` and starts in the player's routine, and `e` has another
routine. Then at `e` the pause is silent, or the unpause sound plays with the pause timer one more than its counter, or the unpause was pressed (`PauseE`). -/
theorem pauseE_run (hF : Facts sy m0 nm₁ d₁ nx₂ nmS) (hrt : ((placesR sy nmS m0).rtI, (0xFF : UInt8)) ∈ knownOf nmS)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat} (hce : c ≤ e)
    (h0 : Room sy nmS m0 (seq c)) (hin : PipeChangeEnd.InRowsT sy nm₁ d₁ (PipeTransition.entry m0) (seq c)) (hctl : controllable sy (seq c) = true)
    (hg : (seq c).ram.get! (SidePause.pauseBytesOf nx₂).g &&& 0x7E = 0)
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    (he : (seq e).ram.get! (placesR sy nmS m0).rtI ≠ (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    SidePause.PauseE sy (SideChangeSound.pauseIdx nx₂) (SidePause.pauseBytesOf nx₂) (seq e) := by
  obtain ⟨⟨t, ht, hm⟩, h2⟩ := pause_run hF.walk hrt next hce h0 (class_of_rows hF.start hin hctl hg) hs hr he
  exact pauseE_of_class hF.len ht hm h2

end

end Smbrta.RoomPause
