import Theorems.FrameKeep
import Theorems.TitleStart

/-!
# The frames of a run start in the idle loop, from the machine at control

`FrameKeep.keep_frame_start` says: a frame that starts in the idle loop in control (`FrameStart`), whose every instruction meets `CleanK`, and that ends in control, ends at the
start of a frame in control. Here this is put in a sequence of real machines, and the first machine comes from the press of Start on the title.

* `starts`: by induction along a sequence of machines, from one machine that starts a frame, every machine up to `b` starts a frame, if each frame between meets `CleanK` on
  each instruction and ends with the known bytes of the guard (for the guards of the game: in control). It is general in the guard, the watched bits and the walk's check.
  `starts_dep` asks the known bytes at the end of a frame only when it starts a frame, so that they may come from a walk of that frame (`LagFrames.keeps_frame`).
* `Begin.start₁`: the machine at control (the machine after frame 0) starts a frame in the idle loop in control. `TitleStart` proves that frame 0 begins in a state of the
  near group of its set. A check on the ROM (`titleCheck`) walks each frame from those states again and asks that it ends at the start of a frame (`FrameKeep.endOK`).
* `walkCheck`: the walk of `FrameKeep` with the guard of `PipeWrites` (`guardOf`), no bit watched, and no spot of the move routine, so that its condition on one
  instruction is `PipeWrites.Clean` itself (`cleanK_of_clean`).

There is no game data in this file. Page: `1-1/a-5-5-3-2-StartRun.md`.
-/

namespace Smbrta.StartRun

open PipeTransition (frame)
open TaintRun (AS Sim Env AB)
open PipeWrites (Guard Clean FrameStart guardOf)
open PipeEntryRule (trace)
open FrameKeep (Spot CleanK Watch Watched keepCheck)

section
variable {E : Env}

/-- `FrameStart` asks of the guard only its idle loop, its stack pointer and its known bytes -/
theorem start_mono {G G' : Guard} {m : Machine} (h : FrameStart G E m) (hi : G'.idle = G.idle) (hs : G'.s0 = G.s0)
    (hk : ∀ p ∈ G'.known, p ∈ G.known) : FrameStart G' E m :=
  ⟨h.pc.trans hi.symm, h.s.trans hs.symm, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, fun p hp => h.known p (hk p hp)⟩

/-- no bit watched -/
theorem watched_nil (m : Machine) : Watched [] m := fun _ hw => absurd hw List.not_mem_nil

/-- `Clean` gives `CleanK` at any place -/
theorem cleanK_of_clean {G : Guard} {q : UInt16} {m : Machine} (h : Clean G m) : CleanK G q m :=
  ⟨fun t ht _ => h.store t ht, h.read, h.jump, h.time⟩

/-- **The frames of a run start in the idle loop**, when the known bytes at the end of a frame may come from its start. `seq n` is the machine when frame `n` begins.
From `seq a`, which starts a frame with the watched bits, every machine up to `seq b` does, if each frame from `a` to `b` meets `CleanK` on each of its instructions and,
when it starts a frame, ends with the known bytes of the guard. `hc` is the walk's check on the ROM. -/
theorem starts_dep {S : Spot} {G : Guard} {W : List Watch} (hc : keepCheck S G E W = true) (hE : E.pad = AB.top)
    {seq : Nat → Machine} {sin : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (sin n)) {a b : Nat}
    (h0 : FrameStart G E (seq a)) (hw : Watched W (seq a))
    (hk : ∀ n, a ≤ n → n < b → ∀ j, CleanK G S.store (trace (seq n) (sin n) j))
    (hkn : ∀ n, a ≤ n → n < b → FrameStart G E (seq n) → ∀ p ∈ G.known, (seq (n + 1)).ram.get! p.1 = p.2) :
    ∀ n, a ≤ n → n ≤ b → FrameStart G E (seq n) ∧ Watched W (seq n) := by
  have key : ∀ d, a + d ≤ b → FrameStart G E (seq (a + d)) ∧ Watched W (seq (a + d)) := by
    intro d
    induction d with
    | zero => exact fun _ => ⟨h0, hw⟩
    | succ d ih =>
      intro hd
      obtain ⟨s1, w1⟩ := ih (by omega)
      have hkn' := hkn (a + d) (by omega) (by omega) s1
      rw [show a + (d + 1) = a + d + 1 by omega, next (a + d)]
      rw [next (a + d)] at hkn'
      exact FrameKeep.keep_frame_start hc hE s1 w1 (hk (a + d) (by omega) (by omega)) hkn'
  intro n h1 h2
  have := key (n - a) (by omega)
  rwa [show a + (n - a) = n by omega] at this

/-- **The frames of a run start in the idle loop.** `seq n` is the machine when frame `n` begins. From `seq a`, which starts a frame with the watched bits, every machine up to
`seq b` does, if each frame from `a` to `b` meets `CleanK` on each of its instructions and ends with the known bytes of the guard. `hc` is the walk's check on the ROM. -/
theorem starts {S : Spot} {G : Guard} {W : List Watch} (hc : keepCheck S G E W = true) (hE : E.pad = AB.top)
    {seq : Nat → Machine} {sin : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (sin n)) {a b : Nat}
    (h0 : FrameStart G E (seq a)) (hw : Watched W (seq a))
    (hk : ∀ n, a ≤ n → n < b → ∀ j, CleanK G S.store (trace (seq n) (sin n) j))
    (hkn : ∀ n, a ≤ n → n < b → ∀ p ∈ G.known, (seq (n + 1)).ram.get! p.1 = p.2) :
    ∀ n, a ≤ n → n ≤ b → FrameStart G E (seq n) ∧ Watched W (seq n) :=
  starts_dep hc hE next h0 hw hk fun n h1 h2 _ => hkn n h1 h2

/-- **The same as `starts_dep`, with no bit watched and `Clean` on each instruction.** -/
theorem starts_clean_dep {S : Spot} {G : Guard} (hc : keepCheck S G E [] = true) (hE : E.pad = AB.top)
    {seq : Nat → Machine} {sin : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (sin n)) {a b : Nat}
    (h0 : FrameStart G E (seq a))
    (hk : ∀ n, a ≤ n → n < b → ∀ j, Clean G (trace (seq n) (sin n) j))
    (hkn : ∀ n, a ≤ n → n < b → FrameStart G E (seq n) → ∀ p ∈ G.known, (seq (n + 1)).ram.get! p.1 = p.2) :
    ∀ n, a ≤ n → n ≤ b → FrameStart G E (seq n) :=
  fun n h1 h2 => (starts_dep hc hE next h0 (watched_nil _) (fun n h1 h2 j => cleanK_of_clean (hk n h1 h2 j)) (fun n h1 h2 hs => hkn n h1 h2 hs) n h1 h2).1

/-- **The same, with no bit watched and `Clean` on each instruction.** -/
theorem starts_clean {S : Spot} {G : Guard} (hc : keepCheck S G E [] = true) (hE : E.pad = AB.top)
    {seq : Nat → Machine} {sin : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (sin n)) {a b : Nat}
    (h0 : FrameStart G E (seq a))
    (hk : ∀ n, a ≤ n → n < b → ∀ j, Clean G (trace (seq n) (sin n) j))
    (hkn : ∀ n, a ≤ n → n < b → ∀ p ∈ G.known, (seq (n + 1)).ram.get! p.1 = p.2) :
    ∀ n, a ≤ n → n ≤ b → FrameStart G E (seq n) :=
  fun n h1 h2 => (starts hc hE next h0 (watched_nil _) (fun n h1 h2 j => cleanK_of_clean (hk n h1 h2 j)) hkn n h1 h2).1

end

/-- the known bytes of `PipeWrites.guardOf` on a machine with control: the routine, the mode, the task -/
theorem known_ctl {sy : Syms} {m0 m : Machine} (h : controllable sy m = true) : ∀ p ∈ (guardOf sy m0).known, m.ram.get! p.1 = p.2 :=
  FrameKeep.known_of_ctl (m0 := m0) h

/-- no place of the move routine: the walk's condition on one instruction is `Clean` -/
def noSpot : Spot := { entry := 0, store := 0, temps := [] }

/-- **The walk of one whole frame on the ROM**: the guard of `PipeWrites`, no bit watched -/
def walkCheck (sy : Syms) (m0 : Machine) : Bool := keepCheck noSpot (guardOf sy m0) (PipeEntryRule.envOf m0) []

/-! ## The machine at control, from the title -/

section
open TitleStart

variable {sy : Syms} {c : Ctx} {t0 : Nat} {G : Guard} {m0 : Machine} {seq : Nat → Machine} {inp : Nat → UInt8}

/-- **The check on the ROM**: the title's environment has the program of `m0`, and frame 0 from each near or held state of the set, with any input, ends at the start
of a frame (`FrameKeep.endOK`) with control and the speed 0, or without control in a state of the set (`TitleStart.frame0Check`) -/
def titleCheck (sy : Syms) (c : Ctx) (G : Guard) (m0 : Machine) : Bool :=
  decide (c.E.prg = m0.prg) && decide (c.E.mask = m0.prgMask) &&
    frame0Check sy c (fun B => finNear sy B && FrameKeep.endOK G B)

/-- **The machine at control starts a frame in the idle loop**, with the known bytes of `G` there: from the press of Start on the title (`Begin`). `hB` and `hc` are checks
on the ROM. -/
theorem Begin.start₁ (hB : check sy c t0 = true) (hc : titleCheck sy c G m0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0))
    (hk : ∀ p ∈ G.known, (seq 1).ram.get! p.1 = p.2) : FrameStart G (PipeEntryRule.envOf m0) (seq 1) := by
  simp only [titleCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hp, hm⟩, hg⟩ := hc
  obtain ⟨Bs, hf, hb⟩ := B.frame0 hB hg hn
  simp only [Bool.and_eq_true] at hf
  exact FrameKeep.start_of_sim hb hf.2 hp hm hk

/-- the RAM indices of the position's bytes: the page, the pixel, the fraction -/
def posI (sy : Syms) : List Nat := [(sy.Player_PageLoc &&& 0x7FF).toNat, (sy.Player_X_Position &&& 0x7FF).toNat, (sy.SprObject_X_MoveForce &&& 0x7FF).toNat]

/-- the RAM indices of the horizontal state's bytes (`Potential.startHS`): the speed, the subspeed, the facing and moving directions, the running speed -/
def hsI (sy : Syms) : List Nat := [(sy.Player_X_Speed &&& 0x7FF).toNat, (sy.Player_X_MoveForce &&& 0x7FF).toNat, (sy.PlayerFacingDir &&& 0x7FF).toNat,
  (sy.Player_MovingDir &&& 0x7FF).toNat, (sy.RunningSpeed &&& 0x7FF).toNat]

/-- **The check on the ROM of the state at control**: frame 0 from each near or held state of the set, with any input, ends with control and the speed 0 and with the
position's bytes and the horizontal state's bytes known, with the values of `m0`, or without control in a state of the set -/
def titlePosCheck (sy : Syms) (c : Ctx) (m0 : Machine) : Bool :=
  frame0Check sy c (fun B => finNear sy B && (posI sy ++ hsI sy).all fun i => TaintRun.knownIs B (i, m0.ram.get! i))

/-- the bytes of the check at control have the values of `m0` -/
theorem Begin.bytes₁ (hB : check sy c t0 = true) (hc : titlePosCheck sy c m0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    ∀ i ∈ posI sy ++ hsI sy, (seq 1).ram.get! i = m0.ram.get! i := by
  obtain ⟨Bs, hf, hb⟩ := B.frame0 hB hc hn
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  exact fun i hi => TaintRun.sim_known hb (hf.2 i hi)

/-- **The position at control is that of `m0`**, with any input: from the press of Start on the title (`Begin`). `hB` and `hc` are checks on the ROM. -/
theorem Begin.pos₁ (hB : check sy c t0 = true) (hc : titlePosCheck sy c m0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    posP sy (seq 1) = posP sy m0 := by
  have hk := fun i hi => Begin.bytes₁ hB hc B hn i (List.mem_append_left _ hi)
  have e1 : peek (seq 1) sy.Player_PageLoc = peek m0 sy.Player_PageLoc := hk _ (List.Mem.head _)
  have e2 : peek (seq 1) sy.Player_X_Position = peek m0 sy.Player_X_Position := hk _ (List.Mem.tail _ (List.Mem.head _))
  have e3 : peek (seq 1) sy.SprObject_X_MoveForce = peek m0 sy.SprObject_X_MoveForce := hk _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  unfold posP
  rw [e1, e2, e3]

/-- **The horizontal state at control is that of `m0`**, with any input: from the press of Start on the title. `hB` and `hc` are checks on the ROM. -/
theorem Begin.hs₁ (hB : check sy c t0 = true) (hc : titlePosCheck sy c m0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    Potential.startHS sy (seq 1) = Potential.startHS sy m0 := by
  have hk := fun i hi => Begin.bytes₁ hB hc B hn i (List.mem_append_right _ hi)
  have e1 : peek (seq 1) sy.Player_X_Speed = peek m0 sy.Player_X_Speed := hk _ (List.Mem.head _)
  have e2 : peek (seq 1) sy.Player_X_MoveForce = peek m0 sy.Player_X_MoveForce := hk _ (List.Mem.tail _ (List.Mem.head _))
  have e3 : peek (seq 1) sy.PlayerFacingDir = peek m0 sy.PlayerFacingDir := hk _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have e4 : peek (seq 1) sy.Player_MovingDir = peek m0 sy.Player_MovingDir :=
    hk _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have e5 : peek (seq 1) sy.RunningSpeed = peek m0 sy.RunningSpeed :=
    hk _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  unfold Potential.startHS PState.read
  rw [e1, e2, e3, e4, e5]

/-- **The machine at control starts a frame in the idle loop in control**, for the guard of `PipeWrites` -/
theorem Begin.start₁G (hB : check sy c t0 = true) (hc : titleCheck sy c (guardOf sy m0) m0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (seq 1) :=
  Begin.start₁ hB hc B hn (known_ctl B.ctl)

end

end Smbrta.StartRun
