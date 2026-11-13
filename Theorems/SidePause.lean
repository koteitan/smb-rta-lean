import Theorems.SideChangeSound

/-!
# The pause through the side pipe's frames

Start may be pressed on the frames of the side pipe. The pause then plays its sound, and the unpause plays another. `SideChangeSound` asks how the pause sound
is at the exit (`QuietK`). Here this is proved from a condition at the entry, by the frames of the pipe for any input.

The pause has a timer (`GamePauseTimer`): a press of Start counts only when it is 0, and a press sets it one more than the length of the pause sound. So while a
pause sound plays, Start does nothing, and the timer is one more than the sound's counter. The pipe's frames are split by classes of the six bytes of the pause
(`classesP`): the queue, the buffer, the flag and the counter of the pause sound, the timer, and the pause byte. Each class is a start state of the pipe's frames with
these bytes. The check walks every frame from every class and ends in a class, or at the exit in one of the kinds of `QuietK` (`kindsX`).

There is no game data in this file. Page: `1-1/d-3-4-3-SidePause.md`.
-/

namespace Smbrta.SidePause

open TaintRun (AS Env AB Sim InvAt ExitAt sim_le toOne tm)
open StepWrites (Rt SState SIn soundLe sIn_of_le)
open SideChangeSound (PauseIdx pauseIdx QuietK InRowsK EndStatementK endCheckK)
open SideChangeEnd (adI Entry2 During2 refs2 refExit exitSplits keep2 duringCheck TimerOK Paused)
open SideChangeBound (startsOf exitBytes keepOf sideEnv Statement leftAt)
open PipeTransition (frame)
open PipeTransitionAll (Names)

/-! ## The classes of the pause -/

/-- the pause byte and the pause timer, as RAM indices -/
structure PauseBytes where
  g : Nat
  t : Nat

/-- the pause byte and the timer, from the names -/
def pauseBytesOf (nx : Names) : PauseBytes := ⟨adI nx "GamePauseStatus", adI nx "GamePauseTimer"⟩

/-- **The classes of the pause state at a frame's end in the game core.** Not paused: silent (the queue and the buffer 0; the flag, the counter and the timer any;
the pause byte 0 or with bit 7); the sound of the unpause with the counter `c` from 1 to the length and the timer `c + 1`; the unpause pressed on this frame
(the timer one more than the length). Paused: the pause pressed on this frame; the pause sound with the counter `c` and the timer `c + 1`; the pause sound over
(the timer 1, then 0). Bit 7 of the pause byte is set by a press and cleared when the timer is 0 and Start is not pressed; its bits 1 to 6 are 0. -/
def classesP (sy : Syms) (ix : PauseIdx) (pb : PauseBytes) : List SState :=
  let U := AB.known sy.UnpauseSfxValue.toUInt8
  let P := AB.known sy.PauseSfxValue.toUInt8
  let L := sy.PauseSfxLength.toNat
  let z := AB.known 0
  let gv := fun (v : UInt8) => (pb.g, AB.known v)
  [[(ix.q, z), (ix.b, z), gv 0], [(ix.q, z), (ix.b, z), gv 0x80]] ++
    ((List.range L).map fun j => [(ix.q, z), (ix.b, U), (ix.f, U), (ix.c, AB.known (j + 1).toUInt8), (pb.t, AB.known (j + 2).toUInt8), gv 0x80]) ++
    [[(ix.q, U), (ix.b, z), (ix.f, P), (pb.t, AB.known (L + 1).toUInt8), gv 0x80]] ++
    [[(ix.q, P), (ix.b, z), (pb.t, AB.known (L + 1).toUInt8), gv 0x81]] ++
    ((List.range (L - 1)).map fun j => [(ix.q, z), (ix.b, P), (ix.f, P), (ix.c, AB.known (j + 1).toUInt8), (pb.t, AB.known (j + 2).toUInt8), gv 0x81]) ++
    [[(ix.q, z), (ix.b, z), (ix.f, P), (ix.c, z), (pb.t, AB.known 1), gv 0x81], [(ix.q, z), (ix.b, z), (ix.f, P), (ix.c, z), (pb.t, z), gv 0x81],
     [(ix.q, z), (ix.b, z), (ix.f, P), (ix.c, z), (pb.t, z), gv 1]]

/-- **The condition at the entry**: the classes that are not paused. Silent: the queue and the buffer 0, the pause byte 0 or `0x80`. Or the sound of the unpause plays:
the buffer and the flag hold the unpause sound's value, the counter is from 1 to the length, the timer is one more than the counter, the pause byte is `0x80`. Or the
unpause was pressed on this frame: the queue holds the unpause sound's value, the buffer 0, the flag the pause sound's value, the timer one more than the length, the
pause byte `0x80`. -/
def PauseE (sy : Syms) (ix : PauseIdx) (pb : PauseBytes) (m : Machine) : Prop :=
  ((m.ram.get! pb.g = 0 ∨ m.ram.get! pb.g = 0x80) ∧ m.ram.get! ix.q = 0 ∧ m.ram.get! ix.b = 0) ∨
  (m.ram.get! pb.g = 0x80 ∧ m.ram.get! ix.q = 0 ∧ m.ram.get! ix.b = sy.UnpauseSfxValue.toUInt8 ∧ m.ram.get! ix.f = sy.UnpauseSfxValue.toUInt8 ∧
    1 ≤ (m.ram.get! ix.c).toNat ∧ (m.ram.get! ix.c).toNat ≤ sy.PauseSfxLength.toNat ∧ (m.ram.get! pb.t).toNat = (m.ram.get! ix.c).toNat + 1) ∨
  (m.ram.get! pb.g = 0x80 ∧ m.ram.get! ix.q = sy.UnpauseSfxValue.toUInt8 ∧ m.ram.get! ix.b = 0 ∧ m.ram.get! ix.f = sy.PauseSfxValue.toUInt8 ∧
    (m.ram.get! pb.t).toNat = sy.PauseSfxLength.toNat + 1)

/-- the kinds of `QuietK` as states of the bytes: silent; the sound of the unpause at each count; the unpause pressed -/
def kindsX (sy : Syms) (ix : PauseIdx) (x : Machine) : List SState :=
  let q0 := (ix.q, AB.known (x.ram.get! ix.q))
  let b0 := (ix.b, AB.known (x.ram.get! ix.b))
  let U := AB.known sy.UnpauseSfxValue.toUInt8
  [[q0, b0]] ++ ((List.range sy.PauseSfxLength.toNat).map fun j => [q0, (ix.b, U), (ix.f, U), (ix.c, AB.known (j + 1).toUInt8)]) ++
    [[(ix.q, U), b0, (ix.f, AB.known sy.PauseSfxValue.toUInt8)]]

/-- the state with the bytes of a class -/
def withClass (t : SState) (S : AS) : AS := t.foldl (fun A p => A.setK p.1 p.2) S

/-- the bytes of the pause, kept apart by the searches -/
def pauseKeep (ix : PauseIdx) (pb : PauseBytes) : List Nat := [ix.q, ix.b, ix.f, ix.c, pb.t, pb.g]

/-- the start states of the pipe's frames, split by the classes -/
def startsC (sy : Syms) (ix : PauseIdx) (pb : PauseBytes) (starts : List AS) : List AS :=
  starts.flatMap fun S => (classesP sy ix pb).map fun t => withClass t S

/-- the states at the exit, split by the kinds -/
def baseX (sy : Syms) (ix : PauseIdx) (x : Machine) (base : List AS) : List AS :=
  base.flatMap fun S => (kindsX sy ix x).map fun t => withClass t S

/-- **The state during the pipe, with the pause in a class** -/
abbrev During2C (sy : Syms) (nm nx : Names) (e : Machine) : Machine → Prop :=
  InvAt (sideEnv nm e) (startsC sy (pauseIdx nx) (pauseBytesOf nx) (startsOf (refs2 nm nx e)))

/-- **the check on the ROM**: the pipe's frames from every class end in a class, or at the exit in a kind; a class and a kind only add known bytes -/
def pipeCheck (sy : Syms) (nm nx : Names) (e : Machine) (A : Nat) : Bool :=
  let ix := pauseIdx nx
  let pb := pauseBytesOf nx
  let x := refExit e A
  let st0 := startsOf (refs2 nm nx e)
  let base := SideChangeSound.baseK nx e A
  let E := sideEnv nm e
  decide (2 ≤ A) && decide (sy.PauseSfxLength.toNat < 256) && SideChangeBound.startsOK (refs2 nm nx e) &&
    st0.all (fun S => (classesP sy ix pb).all fun t => (withClass t S).le S && (toOne E (withClass t S)).le (toOne E S)) &&
    base.all (fun S => (kindsX sy ix x).all fun t => (withClass t S).le S && soundLe (withClass t S) t) &&
    duringCheck E (exitSplits nm nx e) sy (keepOf nm ++ pauseKeep ix pb) (keep2 nm nx ++ pauseKeep ix pb) (startsC sy ix pb st0) (baseX sy ix x base) [] (exitBytes sy nm x)

/-! ## The classes and the kinds of real machines -/

section

theorem and_ff (x : UInt8) : x &&& 0xFF = x := by
  apply UInt8.toNat_inj.1
  rw [UInt8.toNat_and]
  have : (0xFF : UInt8).toNat = 2 ^ 8 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt

theorem eq_of_mem_known {v x : UInt8} (h : (AB.known v).mem x) : x = v := by
  have h' : x &&& 0xFF = v &&& 0xFF := h
  rwa [and_ff, and_ff] at h'

theorem mem_known_of_eq {v x : UInt8} (h : x = v) : (AB.known v).mem x := by
  rw [h]
  exact TaintRun.mem_known_self v

theorem toUInt8_of_toNat {x : UInt8} {n : Nat} (h : x.toNat = n) : x = n.toUInt8 := by
  rw [← h]
  exact (UInt8.ofNat_toNat).symm

theorem toNat_of_toUInt8 {x : UInt8} {n : Nat} (h : x = n.toUInt8) (hn : n < 256) : x.toNat = n := by
  rw [h]
  exact Nat.mod_eq_of_lt hn

variable {sy : Syms} {ix : PauseIdx} {pb : PauseBytes}

/-- **A machine with the condition at the entry has the bytes of one of the classes** -/
theorem class_of_pauseE {m : Machine} (h : PauseE sy ix pb m) : ∃ t ∈ classesP sy ix pb, SIn t m := by
  rcases h with ⟨hg, hq, hb⟩ | ⟨hg, hq, hb, hf, hc1, hc2, ht⟩ | ⟨hg, hq, hb, hf, ht⟩
  · rcases hg with hg | hg
    · refine ⟨[(ix.q, AB.known 0), (ix.b, AB.known 0), (pb.g, AB.known 0)], by simp [classesP], ?_⟩
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_known_of_eq hq
      · exact mem_known_of_eq hb
      · exact mem_known_of_eq hg
    · refine ⟨[(ix.q, AB.known 0), (ix.b, AB.known 0), (pb.g, AB.known 0x80)], by simp [classesP], ?_⟩
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_known_of_eq hq
      · exact mem_known_of_eq hb
      · exact mem_known_of_eq hg
  · have hj : (m.ram.get! ix.c).toNat - 1 < sy.PauseSfxLength.toNat := by omega
    refine ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (List.mem_map.2 ⟨(m.ram.get! ix.c).toNat - 1, List.mem_range.2 hj, rfl⟩)))))))))), ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_known_of_eq hq
    · exact mem_known_of_eq hb
    · exact mem_known_of_eq hf
    · exact mem_known_of_eq (x := m.ram.get! ix.c) (toUInt8_of_toNat (by omega))
    · exact mem_known_of_eq (x := m.ram.get! pb.t) (toUInt8_of_toNat (by omega))
    · exact mem_known_of_eq hg
  · refine ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr List.mem_cons_self))))))), ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact mem_known_of_eq hq
    · exact mem_known_of_eq hb
    · exact mem_known_of_eq hf
    · exact mem_known_of_eq (x := m.ram.get! pb.t) (toUInt8_of_toNat ht)
    · exact mem_known_of_eq hg

/-- **A machine with the bytes of a kind has the pause sound as `QuietK` says** (the length of the sound is below 256, as the check says) -/
theorem quietK_of_kind (hL : sy.PauseSfxLength.toNat < 256) {x m : Machine} {t : SState} (ht : t ∈ kindsX sy ix x) (hm : SIn t m) : QuietK sy ix x m := by
  unfold kindsX at ht
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.mem_range] at ht
  rcases ht with (rfl | ⟨j, hj, rfl⟩) | rfl
  · exact Or.inl ⟨eq_of_mem_known (hm (ix.q, AB.known (x.ram.get! ix.q)) (by simp)), eq_of_mem_known (hm (ix.b, AB.known (x.ram.get! ix.b)) (by simp))⟩
  · have hc : m.ram.get! ix.c = (j + 1).toUInt8 := eq_of_mem_known (hm (ix.c, AB.known (j + 1).toUInt8) (by simp))
    have hc' := toNat_of_toUInt8 hc (by omega)
    exact Or.inr (Or.inl ⟨eq_of_mem_known (hm (ix.q, AB.known (x.ram.get! ix.q)) (by simp)),
      eq_of_mem_known (hm (ix.b, AB.known sy.UnpauseSfxValue.toUInt8) (by simp)), eq_of_mem_known (hm (ix.f, AB.known sy.UnpauseSfxValue.toUInt8) (by simp)),
      by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨eq_of_mem_known (hm (ix.q, AB.known sy.UnpauseSfxValue.toUInt8) (by simp)),
      eq_of_mem_known (hm (ix.b, AB.known (x.ram.get! ix.b)) (by simp)), eq_of_mem_known (hm (ix.f, AB.known sy.PauseSfxValue.toUInt8) (by simp))⟩)

theorem sim_withClass {E : Env} {F : Nat × UInt8} {m : Machine} : ∀ (t : SState) {A : AS}, Sim E F A m → SIn t m → Sim E F (withClass t A) m := by
  intro t
  induction t with
  | nil => intro A hs _; exact hs
  | cons p l ih =>
    intro A hs ht
    exact ih (SideChangeEnd.sim_refine hs (ht p List.mem_cons_self)) (fun q hq => ht q (List.mem_cons_of_mem _ hq))

end

/-! ## The pipe's frames -/

section
variable {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} {R : Rt}

/-- what the check gives on the pipe's frames, with the rows of `SideChangeSound` after them -/
structure PipeQ (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) : Prop where
  /-- an entry with the condition on the pause is in a class -/
  during : ∀ M, Entry2 nm nx e A M → PauseE sy (pauseIdx nx) (pauseBytesOf nx) M → During2C sy nm nx e M
  /-- a class is in the state during the pipe of `SideChangeEnd` -/
  toDuring2 : ∀ m, During2C sy nm nx e m → During2 nm nx e m
  /-- **one frame of the pipe, for any input**: the machine stays in a class, or this is the exit; there the pause sound is as `QuietK` says, and with the timer not
  000 the machine is in the rows -/
  step : ∀ m, During2C sy nm nx e m → ∀ i, During2C sy nm nx e (frame m i) ∨
    (ExitAt (exitBytes sy nm (refExit e A)) (frame m i) ∧ QuietK sy (pauseIdx nx) (refExit e A) (frame m i) ∧
      (TimerOK nx (frame m i) → InRowsK sy nm nx e A B R (frame m i)))

/-- the start of the rows from a state at the exit, as in `SideChangeSound.endStatementK_of_check` -/
theorem inRows_of_base (hk : endCheckK sy nm nx e A B R = true) {D : AS} (hD : D ∈ SideChangeSound.baseK nx e A) {m : Machine}
    (hs : Sim (sideEnv nm e) (m.frame, 2) D m) (hq : QuietK sy (pauseIdx nx) (refExit e A) m) (ht : TimerOK nx m) : InRowsK sy nm nx e A B R m := by
  simp only [endCheckK, SideChangeSound.endCheckL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hb⟩, _⟩, _⟩, _⟩, hh⟩, _⟩, _⟩, _⟩, _⟩ := hk
  have hbD := hb D hD
  have hs2 : Sim (SideChangeEnd.timeEnv nm nx e) (m.frame, 2) D m :=
    SideChangeEnd.sim_splits' (l := exitSplits nm nx e) (SideChangeEnd.sim_D (D := SideChangeEnd.digitsOf nx) hs hbD.1)
  have hdg : (SideChangeEnd.timeEnv nm nx e).D.any (fun j => m.ram.get! j != 0) = true := by
    obtain ⟨j, hj, hne⟩ := ht
    exact List.any_eq_true.2 ⟨j, hj, by simpa using hne⟩
  have hs3 : Sim (SideChangeEnd.timeEnv nm nx e) (m.frame, 2) (StepWrites.retag false ({ StepWrites.forgetAll R.SB D with dg := true } : AS)) m :=
    StepWrites.sim_retag false { StepWrites.sim_forgetAll R.SB hs2 with dg := fun _ => hdg }
  obtain ⟨kd, hkd, hkm⟩ := SideChangeSound.kinds_of_quiet hq
  exact SideChangeSound.inv_headS B _ _ hh (List.mem_map.2 ⟨D, hD, rfl⟩) hs3 rfl (List.mem_map.2 ⟨kd, hkd, rfl⟩)
    (SideChangeSound.sIn_append (sIn_of_le hs hbD.2) hkm)

theorem pipeQ_of_check (hp : pipeCheck sy nm nx e A = true) (hk : endCheckK sy nm nx e A B R = true) : PipeQ sy nm nx e A B R := by
  simp only [pipeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨hA, hL⟩, hV⟩, hC⟩, hX⟩, hD⟩ := hp
  have hDOK := SideChangeEnd.duringOK_of_check hD
  have hE : (sideEnv nm e).pad = AB.top := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro M hM hP
    obtain ⟨S, hS, hcase⟩ := SideChangeBound.inv_of_entry hV hE hA hM
    obtain ⟨t, ht, htm⟩ := class_of_pauseE hP
    have hS' : withClass t S ∈ startsC sy (pauseIdx nx) (pauseBytesOf nx) (startsOf (refs2 nm nx e)) :=
      List.mem_flatMap.2 ⟨S, hS, List.mem_map.2 ⟨t, ht, rfl⟩⟩
    rcases hcase with ⟨h2, hs⟩ | ⟨h1, _⟩
    · exact ⟨_, hS', Or.inl ⟨h2, sim_withClass t hs htm⟩⟩
    · exfalso
      have := hM.timer
      have h1' : (tm (sideEnv nm e) M).toNat = 1 := by rw [h1]; rfl
      have : A ≤ (tm (sideEnv nm e) M).toNat := this
      omega
  · intro m hm
    obtain ⟨S', hS', hcase⟩ := hm
    obtain ⟨S, hS, hS2⟩ := List.mem_flatMap.1 hS'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hS2
    have hle := hC S hS t ht
    rcases hcase with ⟨h2, hs⟩ | ⟨h1, hs⟩
    · exact ⟨S, hS, Or.inl ⟨h2, sim_le hle.1 hs⟩⟩
    · exact ⟨S, hS, Or.inr ⟨h1, sim_le hle.2 hs⟩⟩
  · intro m hm i
    rcases SideChangeEnd.during_step hDOK hE hm i with g | ⟨_, g1, g2⟩
    · exact Or.inl g
    · obtain ⟨D, hD1, hs⟩ := g2 (fun q hq => by cases hq)
      obtain ⟨S, hS, hS2⟩ := List.mem_flatMap.1 hD1
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hS2
      have hle := hX S hS t ht
      have hq := quietK_of_kind hL ht (sIn_of_le hs hle.2)
      exact Or.inr ⟨g1, hq, fun hT => inRows_of_base hk hS (sim_le hle.1 hs) hq hT⟩

end

/-! ## A run -/

section
variable {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} {R : Rt} {es : List Machine}

/-- **The change of a run.** The fields of `SideChangeSound.EndRunK`, with the condition on the pause at the entry (`pause`) in place of the condition at the exit. -/
structure EndRunQ (sy : Syms) (nm nx : Names) (e : Machine) (A : Nat) where
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (inp n)
  lag : Nat → Prop
  dec : DecidablePred lag
  cnt : Nat → Nat
  hcnt : ∀ n, cnt (n + 1) = cnt n + (@ite _ (lag n) (dec n) 0 1)
  a : Nat
  b : Nat
  order : a ≤ b
  /-- the condition on the state at the entry -/
  entry : Entry2 nm nx e A (seq a)
  /-- the condition on the pause at the entry -/
  pause : PauseE sy (pauseIdx nx) (pauseBytesOf nx) (seq a)
  /-- control at `b` -/
  atCtl : controllable sy (seq b) = true
  /-- a lag frame ends paused -/
  lagPaused : ∀ n, a ≤ n → n < b → lag n → Paused nx (seq (n + 1))
  /-- no Start on the frames of the game core after the pipe -/
  noStart : ∀ n, a ≤ n → n < b → SideChangeEnd.coreFrame sy sy.EngSidePipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- at the exit, the game timer is not 000 -/
  time : ∀ n, a ≤ n → n ≤ b → ExitAt (exitBytes sy nm (refExit e A)) (seq n) → TimerOK nx (seq n)

/-- in a class during the pipe, or in the rows -/
def StQ (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (R : Rt) (m : Machine) : Prop := During2C sy nm nx e m ∨ InRowsK sy nm nx e A B R m

/-- one frame -/
theorem st_stepQ (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R) {m : Machine} {i : UInt8}
    (h : StQ sy nm nx e A B R m) (hi : SideChangeEnd.coreFrame sy sy.EngSidePipe m = true → SideChangeEnd.noStart i = true)
    (ht : ExitAt (exitBytes sy nm (refExit e A)) (frame m i) → TimerOK nx (frame m i)) :
    leftAt sy nm e A B m = 0 ∨ (StQ sy nm nx e A B R (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i) + 1) := by
  rcases h with h | h
  · right
    refine ⟨?_, S.fall _ (T.toDuring _ (Q.toDuring2 _ h)) _⟩
    rcases Q.step m h i with g | ⟨g1, _, g3⟩
    · exact Or.inl g
    · exact Or.inr (g3 (ht g1))
  · rcases T.rows m h i hi with g | ⟨g1, g2⟩
    · exact Or.inl g
    · exact Or.inr ⟨Or.inr g1, g2⟩

/-- one frame that ends paused: it takes nothing off `left` -/
theorem st_step_pausedQ (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R) {m : Machine} {i : UInt8} (h : StQ sy nm nx e A B R m)
    (hi : SideChangeEnd.coreFrame sy sy.EngSidePipe m = true → SideChangeEnd.noStart i = true)
    (ht : ExitAt (exitBytes sy nm (refExit e A)) (frame m i) → TimerOK nx (frame m i)) (hp : Paused nx (frame m i)) :
    leftAt sy nm e A B m = 0 ∨ (StQ sy nm nx e A B R (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i)) := by
  rcases h with h | h
  · rcases Q.step m h i with g | ⟨g1, _, g3⟩
    · exact Or.inr ⟨Or.inl g, T.pauseKeeps m (Q.toDuring2 _ h) i hp (Q.toDuring2 _ g)⟩
    · exact absurd hp (T.rowsNotPaused _ (g3 (ht g1)))
  · rcases T.rows m h i hi with g | ⟨g1, _⟩
    · exact Or.inl g
    · exact absurd hp (T.rowsNotPaused _ g1)

theorem EndRunQ.cnt_mono (R' : EndRunQ sy nm nx e A) (n : Nat) : R'.cnt n ≤ R'.cnt (n + 1) := by
  rw [R'.hcnt n]
  omega

/-- the timer at the exit of a run, on the frame after `n` -/
theorem EndRunQ.timeAt (R' : EndRunQ sy nm nx e A) {n : Nat} (h1 : R'.a ≤ n) (h2 : n < R'.b) :
    ExitAt (exitBytes sy nm (refExit e A)) (frame (R'.seq n) (R'.inp n)) → TimerOK nx (frame (R'.seq n) (R'.inp n)) := by
  intro hx
  rw [← R'.next n] at hx ⊢
  exact R'.time _ (by omega) (by omega) hx

/-- **The bound on the change**: `change₂` of `Route`, with `A + B = 282`. -/
theorem EndRunQ.bound (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R) (R' : EndRunQ sy nm nx e A) :
    R'.cnt R'.a + (A + B) ≤ R'.cnt R'.b := by
  have key : ∀ d, R'.a + d ≤ R'.b → R'.cnt R'.a + (A + B) ≤ R'.cnt (R'.a + d) ∨
      (StQ sy nm nx e A B R (R'.seq (R'.a + d)) ∧ R'.cnt R'.a + (A + B) ≤ R'.cnt (R'.a + d) + leftAt sy nm e A B (R'.seq (R'.a + d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      right
      refine ⟨Or.inl (Q.during _ R'.entry R'.pause), ?_⟩
      have := S.atEntry _ (T.entry _ R'.entry)
      simp only [Nat.add_zero]
      omega
    | succ d ih =>
      intro hd
      have e1 : R'.a + (d + 1) = R'.a + d + 1 := rfl
      rw [e1]
      have hn := R'.next (R'.a + d)
      rcases ih (by omega) with h | ⟨h1, h2⟩
      · left
        have := R'.cnt_mono (R'.a + d)
        omega
      · have hi := R'.noStart (R'.a + d) (by omega) (by omega)
        have ht := R'.timeAt (n := R'.a + d) (by omega) (by omega)
        have hc := R'.hcnt (R'.a + d)
        by_cases hl : R'.lag (R'.a + d)
        · rw [@if_pos _ (R'.dec _) hl] at hc
          have hp := R'.lagPaused (R'.a + d) (by omega) (by omega) hl
          rw [hn] at hp
          rcases st_step_pausedQ T Q h1 hi ht hp with g | ⟨g1, g2⟩
          · left
            omega
          · right
            rw [hn]
            exact ⟨g1, by omega⟩
        · rw [@if_neg _ (R'.dec _) hl] at hc
          rcases st_stepQ S T Q h1 hi ht with g | ⟨g1, g2⟩
          · left
            omega
          · right
            rw [hn]
            exact ⟨g1, by omega⟩
  have hb := R'.order
  have e2 : R'.a + (R'.b - R'.a) = R'.b := by omega
  rcases key (R'.b - R'.a) (by omega) with h | ⟨_, h⟩
  · rw [e2] at h
    exact h
  · rw [e2, S.atControl _ R'.atCtl] at h
    omega

/-- **Each machine from the entry up to the first control is in a class during the pipe or in the rows**, when `b` is the first control after the entry -/
theorem EndRunQ.way (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R) (R' : EndRunQ sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : ∀ d, R'.a + d ≤ R'.b → StQ sy nm nx e A B R (R'.seq (R'.a + d)) := by
  intro d
  induction d with
  | zero => exact fun _ => Or.inl (Q.during _ R'.entry R'.pause)
  | succ d ih =>
    intro hd
    have e1 : R'.a + (d + 1) = R'.a + d + 1 := rfl
    rw [e1, R'.next (R'.a + d)]
    rcases st_stepQ S T Q (ih (by omega)) (R'.noStart (R'.a + d) (by omega) (by omega)) (R'.timeAt (n := R'.a + d) (by omega) (by omega)) with g | ⟨g1, _⟩
    · rcases ih (by omega) with h | h
      · exact absurd g (T.duringLeft _ (Q.toDuring2 _ h))
      · have := T.zero _ h g
        rw [hc _ (by omega) (by omega)] at this
        cases this
    · exact g1

/-- **`left` is not 0 before control**, on a run of the change, if `b` is the first control after the entry -/
theorem EndRunQ.first (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R) (R' : EndRunQ sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : ∀ n, R'.a ≤ n → n < R'.b → leftAt sy nm e A B (R'.seq n) ≠ 0 := by
  intro n h1 h2 h0
  obtain ⟨d, rfl⟩ : ∃ d, n = R'.a + d := ⟨n - R'.a, by omega⟩
  rcases EndRunQ.way S T Q R' hc d (by omega) with h | h
  · exact T.duringLeft _ (Q.toDuring2 _ h) h0
  · have := T.zero _ h h0
    rw [hc _ h1 h2] at this
    cases this

/-- **The machine at control is in the rows**, if `b` is the first control after the entry -/
theorem EndRunQ.inRows (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R) (R' : EndRunQ sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) : InRowsK sy nm nx e A B R (R'.seq R'.b) := by
  have hb := R'.order
  have e2 : R'.a + (R'.b - R'.a) = R'.b := by omega
  have h := EndRunQ.way S T Q R' hc (R'.b - R'.a) (by omega)
  rw [e2] at h
  rcases h with h | h
  · exact absurd (S.atControl _ R'.atCtl) (T.duringLeft _ (Q.toDuring2 _ h))
  · exact h

/-- **The last frame before control is in the rows, with `left` 1**, if `b` is the first control after the entry, as `SideChangeSound.EndRunK.last` -/
theorem EndRunQ.last (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R) (R' : EndRunQ sy nm nx e A)
    (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    R'.a + 1 ≤ R'.b ∧ SideChangeEnd.InvL (SideChangeSound.ctxOf sy nm nx e A B R) ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row)) (R'.seq (R'.b - 1)) ∧
      leftAt sy nm e A B (R'.seq (R'.b - 1)) = 1 := by
  have h0 := S.atControl _ R'.atCtl
  have hab : R'.a + 1 ≤ R'.b := by
    refine Nat.lt_of_le_of_ne R'.order fun heq => ?_
    have hd := T.duringLeft _ (Q.toDuring2 _ (Q.during _ R'.entry R'.pause))
    rw [heq] at hd
    exact hd h0
  have e1 : R'.a + (R'.b - 1 - R'.a) = R'.b - 1 := by omega
  have hw := EndRunQ.way S T Q R' hc (R'.b - 1 - R'.a) (by omega)
  rw [e1] at hw
  have hn := R'.next (R'.b - 1)
  rw [show R'.b - 1 + 1 = R'.b by omega] at hn
  have hf1 := EndRunQ.first S T Q R' hc (R'.b - 1) (by omega) (by omega)
  rcases hw with h | h
  · exfalso
    rcases Q.step _ h (R'.inp (R'.b - 1)) with g | ⟨g1, _, _⟩
    · rw [← hn] at g
      exact T.duringLeft _ (Q.toDuring2 _ g) h0
    · rw [← hn] at g1
      have := T.exitOff _ g1
      rw [R'.atCtl] at this
      cases this
  · rcases T.rows _ h (R'.inp (R'.b - 1)) (R'.noStart _ (by omega) (by omega)) with g | ⟨g1, g2⟩
    · exact absurd g hf1
    · rw [← hn, h0] at g2
      exact ⟨hab, SideChangeSound.invL_of_invS h, by omega⟩

/-- **The state at control, on a real run**, from the rows of `SideChangeSound` -/
theorem EndRunQ.start {c : PoleJoin.Box} (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R)
    (hk : SideChangeSound.startCheckK sy nm nx e A B R c = true) (R' : EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    SurfaceFrames.Start sy c (R'.seq R'.b) := by
  unfold SideChangeSound.startCheckK at hk
  exact SurfaceFrames.start_of_invL hk (SideChangeSound.invL_of_invS (EndRunQ.inRows S T Q R' hc)) R'.atCtl

/-- **The machine at control is as `FrameKeep` needs it**, on a real run, from the rows of `SideChangeSound` -/
theorem EndRunQ.atCtl' {m0 : Machine} (S : Statement sy nm e es A B) (T : EndStatementK sy nm nx e A B R) (Q : PipeQ sy nm nx e A B R)
    (hk : SideChangeSound.ctlCheckK sy m0 nm nx e A B R = true) (R' : EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    FrameKeep.AtCtl sy m0 (R'.seq R'.b) := by
  simp only [SideChangeSound.ctlCheckK, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨hp, hmk⟩, h0⟩ := hk
  exact ControlStart.ctl_of_invL hp hmk h0 (SideChangeSound.invL_of_invS (EndRunQ.inRows S T Q R' hc)) R'.atCtl

end

end Smbrta.SidePause
