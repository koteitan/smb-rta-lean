import Theorems.SideChangeBound

/-!
# The last frames of the change out of the side pipe

`SideChangeBound` proves the first frames of the change, and keeps a hypothesis `fallAfter` on the frames after the pipe. Here that hypothesis is proved for a stated set of states at the exit,
for inputs with no Start on the frames of the game core. The frame after the pipe clears RAM, and the frame ends inside that loop. So this file adds to the abstract machine a tick that crosses the
end of a frame (`xtick`), and a walk with it (`xwalk`). After the clear most bytes are known, and an abstract run goes from row to row (`Row`, `chainOK`). There is no game data in this file.
Two more parts: rows that know that the game timer is not 000 (`timeRows`), whose last row has control only, so that `left` is not 0 before control (`EndRun.first`);
and a walk of the pipe's frames with the pause bit in pieces, so that a frame that ends paused takes nothing off `left` (`pause_keeps`, `EndRun.lagPaused`).
The step `xstep1` also reads through a pointer that is not known when its high byte puts the address in the RAM or the ROM (`aIzyHi`, `s_aIzyHi`); it uses this only where its other rules fail.
Page: `1-1/d-2-3-SideChangeEnd.md`.
-/

namespace Smbrta.SideChangeEnd

open PipeTransition (frame run zeros)
open PipeTransitionAll (go Names)
open SideChangeBound

/-! ## A tick that crosses the end of a frame -/

/-- the tick where `atick` does not go: the first dot of a frame, the frame's end, the clear of the vblank flag -/
def xtickOwn (c : Nat) (A : AS) : List (Option AS) :=
  if c == 0 || decide (dotVblClr ≤ 3 * c) then [none]
  else if A.hi == 0 then
    match A.ppuCtrl.bit 0x80 with
    | some b => [some { A with lo := 3 * c, hi := 3 * c, vb := true, nmi := A.nmi || b }]
    | none => [none]
  else if decide (dotSpr0 ≤ A.lo) && decide (dotsPerFrame - 1 ≤ A.hi + 3 * c) then
    match A.ppuCtrl.bit 0x80 with
    | some b =>
      (if A.lo + 3 * c ≤ dotsPerFrame - 1 then [some { A with lo := A.lo + 3 * c, hi := dotsPerFrame - 1 }] else []) ++
      [some { A with lo := 0, hi := 0, k := A.k + 1 }] ++
      (if dotsPerFrame ≤ A.hi + 3 * c then [some { A with lo := 1, hi := A.hi + 3 * c - (dotsPerFrame - 1), vb := true, nmi := A.nmi || b, k := A.k + 1 }] else [])
    | none => [none]
  else if decide (dotVblSet ≤ A.lo) && A.vb && decide (A.hi < dotVblClr) && decide (A.lo + 3 * c < dotVblClr) && decide (dotVblClr ≤ A.hi + 3 * c) && decide (A.hi + 3 * c < dotsPerFrame - 1) then
    [some { A with lo := A.lo + 3 * c, hi := dotVblClr - 1 }, some { A with lo := dotVblClr, hi := A.hi + 3 * c, vb := false }]
  else [none]

/-- `tick c`: `atick` where it goes -/
def xtick (c : Nat) (A : AS) : List (Option AS) :=
  match atick c c A with
  | some (_, B) => [some B]
  | none => xtickOwn c A

/-- a branch that may cross the end of a frame: `A.pc` is at the offset. The frame ends at most once. -/
def xbr (E : Env) (mask : UInt8) (neg : Bool) (A : AS) : List (Option AS) :=
  match afetch E A with
  | none => [none]
  | some (off, A1) =>
    match A1.p.bit mask with
    | none => [none]
    | some b =>
      if b == neg then
        let t := A1.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0))
        let c := if (A1.pc ^^^ t) &&& 0xFF00 != 0 then 2 else 1
        (xtick c { A1 with pc := t }).flatMap fun r =>
          match r with
          | none => [none]
          | some B => (xtick 2 B).map fun r2 => r2.bind fun D => if D.k ≤ A.k + 1 then some D else none
      else xtick 2 A1

/-! ## A read through a pointer that is not known

An `LDA (zp),Y` through a pointer that the state does not know fails in `astep1`. If the pointer's high byte is known well enough, every address `p + y` is in the RAM or the ROM,
not at a register: the read gives a byte that is not known and changes nothing else (`aIzyHi`, `s_aIzyHi`). `xstep1` uses this rule only where the old rules fail. -/

/-- every address `p + y`, with `p` a pointer of this high byte and `y` a byte, is in the RAM or the ROM: the high byte is at most `0x1E`, or at least `0x80` (past the end of memory
the address goes round to the zero page and the stack) -/
def ptrHiOK (hi : TaintRun.AB) : Bool := decide (hi.maxv.toNat ≤ 0x1E) || decide (0x80 ≤ hi.minv.toNat)

/-- the RAM and the ROM, as an interval that goes round the end of memory -/
def ptrWide : TaintRun.AAd := ⟨0x8000, 0x1FFF⟩

/-- `(zp),Y` through a pointer whose high byte is known well enough: the address is in `ptrWide`, and a page penalty may come -/
def aIzyHi (E : Env) : AMode :=
  afetch E >>= fun z => ard16zp E z >>= fun p =>
    if ptrHiOK p.2 then (MonadState.get : AM AS) >>= fun _ => atick 0 1 >>= fun _ => Pure.pure ptrWide else failure

/-- a step: `astep1` if it goes, else the rules above, and the read through a pointer not known -/
def xstep1 (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  let rs := astep1 E ops A
  if rs.all (·.isSome) then rs
  else if A.nmi || decide (A.pc < 0x8000) then rs
  else
    let op := E.prg.get! (A.pc &&& E.mask).toNat
    if isIdle E A.pc op || (A.rk && isRkDec E A.pc op) then rs
    else if op == 0xD0 then xbr E 0x02 false { A with pc := A.pc + 1 }
    else if op == 0xB0 then xbr E 0x01 true { A with pc := A.pc + 1 }
    else if op == 0x10 then xbr E 0x80 false { A with pc := A.pc + 1 }
    else if cycOf op == 0 then [none]
    else
      match (ops[op.toNat]?.getD aJAM) { A with pc := A.pc + 1 } with
      | none =>
        if op == 0xB1 then
          match aLDA E (aIzyHi E) { A with pc := A.pc + 1 } with
          | none => [none]
          | some (_, B) => xtick (cycOf op) B
        else [none]
      | some (_, B) => xtick (cycOf op) B

def xsuccs (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  (pieces E A).flatMap (xstep1 E ops)

/-! ## The tick follows the machine -/

section
variable {E : Env} {F : Nat × UInt8}

/-- what a tick does to the frame and the dot -/
def TickRel (c : Nat) (A B : AS) (m m' : Machine) : Prop :=
  (B.k = A.k ∧ m'.frame = m.frame ∧ m'.fdot = m.fdot + 3 * c) ∨ (B.k = A.k + 1 ∧ m'.frame = m.frame + 1)

theorem tick_firstX (c : Nat) (m : Machine) (h1 : m.fdot = 0) (h2 : 1 ≤ c) (h3 : 3 * c < dotVblClr) :
    (go (tick c) m).2 = { m with
      cyc := m.cyc + c
      fdot := 3 * c
      vblank := true
      nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) } := by
  have hc := vc
  have hs0 := vs
  have hd := vd
  have h1' := v1
  have hlen : ∀ n : Machine, 3 * c < PipeTransitionAll.tickLen n := by
    intro n
    unfold PipeTransitionAll.tickLen
    split <;> omega
  have h4 : ∀ (new len : Nat) (n : Machine), new < len → PipeTransitionAll.tick4 new len n = { n with fdot := new } := by
    intro new len n hl
    unfold PipeTransitionAll.tick4
    rw [if_neg (by omega)]
  rw [PipeTransitionAll.tick_eq]
  dsimp only
  rw [h1]
  simp only [Nat.zero_add]
  rw [h4 _ _ _ (hlen _)]
  have a1 : (decide (0 < dotVblSet) && decide (dotVblSet ≤ 3 * c)) = true := by
    simp only [v1]
    simp
    omega
  have a2 : (decide (0 < dotVblClr) && decide (dotVblClr ≤ 3 * c)) = false := by
    have : ¬ dotVblClr ≤ 3 * c := by omega
    simp [this]
  have a3 : (decide (0 < dotSpr0) && decide (dotSpr0 ≤ 3 * c)) = false := by
    have : ¬ dotSpr0 ≤ 3 * c := by omega
    simp [this]
  rw [a1, a2, a3]
  rfl

/-- near the end of a frame: the frame goes on, or it ends at a small dot -/
theorem tick_end (c : Nat) (m : Machine) (h1 : dotSpr0 ≤ m.fdot) :
    (m.fdot + 3 * c ≤ dotsPerFrame - 1 ∧ (go (tick c) m).2 = { m with cyc := m.cyc + c, fdot := m.fdot + 3 * c }) ∨
    (dotsPerFrame - 1 ≤ m.fdot + 3 * c ∧ (go (tick c) m).2 = { m with cyc := m.cyc + c, frame := m.frame + 1, fdot := 0 }) ∨
    (dotsPerFrame ≤ m.fdot + 3 * c ∧ ∃ d, 1 ≤ d ∧ d ≤ m.fdot + 3 * c - (dotsPerFrame - 1) ∧
      (go (tick c) m).2 = { m with cyc := m.cyc + c, frame := m.frame + 1, fdot := d, vblank := true, nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) }) := by
  have hc := vc
  have hs0 := vs
  have hv1 := v1
  have hd := vd
  have a1 : (decide (m.fdot < dotVblSet) && decide (dotVblSet ≤ m.fdot + 3 * c)) = false := by
    have : ¬ m.fdot < dotVblSet := by omega
    simp [this]
  have a2 : (decide (m.fdot < dotVblClr) && decide (dotVblClr ≤ m.fdot + 3 * c)) = false := by
    have : ¬ m.fdot < dotVblClr := by omega
    simp [this]
  have a3 : (decide (m.fdot < dotSpr0) && decide (dotSpr0 ≤ m.fdot + 3 * c)) = false := by
    have : ¬ m.fdot < dotSpr0 := by omega
    simp [this]
  have e0 : go (tick c) m = ((), PipeTransitionAll.tick4 (m.fdot + 3 * c) (PipeTransitionAll.tickLen { m with cyc := m.cyc + c }) { m with cyc := m.cyc + c }) := by
    rw [PipeTransitionAll.tick_eq]
    dsimp only
    rw [a1, a2, a3]
    rfl
  rw [e0]
  generalize hL : PipeTransitionAll.tickLen { m with cyc := m.cyc + c } = L
  have hL2 : L = dotsPerFrame ∨ L = dotsPerFrame - 1 := by
    rw [← hL]
    unfold PipeTransitionAll.tickLen
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases hge : L ≤ m.fdot + 3 * c
  · by_cases hdd : dotVblSet ≤ m.fdot + 3 * c - L
    · right; right
      refine ⟨by omega, m.fdot + 3 * c - L, by omega, by omega, ?_⟩
      simp only [PipeTransitionAll.tick4]
      rw [if_pos hge, if_pos hdd]
    · right; left
      refine ⟨by omega, ?_⟩
      simp only [PipeTransitionAll.tick4]
      rw [if_pos hge, if_neg hdd]
      have : m.fdot + 3 * c - L = 0 := by omega
      rw [this]
  · left
    refine ⟨by omega, ?_⟩
    simp only [PipeTransitionAll.tick4]
    rw [if_neg hge]

theorem s0f_lt {d : Nat} (h : d < dotVblClr) : s0f d = true := by
  simp [s0f, h]

theorem s0f_ge {d : Nat} (h : dotSpr0 ≤ d) : s0f d = true := by
  simp [s0f, h]

/-- the tick where `atick` does not go -/
theorem s_xtickOwn {A : AS} {m : Machine} (hs : Sim E F A m) (c : Nat) :
    ∃ r ∈ xtickOwn c A, ∀ B, r = some B → Sim E F B (go (tick c) m).2 ∧ TickRel c A B m (go (tick c) m).2 := by
  have hlo := hs.lo
  have hhi := hs.hi
  have hlim := hs.lim
  have hc := vc
  have hsp := vs
  have hv1 := v1
  have hd := vd
  unfold xtickOwn
  by_cases g0 : (c == 0 || decide (dotVblClr ≤ 3 * c)) = true
  · rw [if_pos g0]
    exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  rw [if_neg g0]
  have g0' : c ≠ 0 ∧ ¬ dotVblClr ≤ 3 * c := by simpa using g0
  obtain ⟨gc, gv⟩ := g0'
  have hb : ∀ {b : Bool}, A.ppuCtrl.bit 0x80 = some b → b = (m.ppuCtrl &&& 0x80 != 0) := by
    intro b he
    have t := TaintRun.TR_bit 0x80 hs.ppuCtrl
    rw [he] at t
    rcases t with t | t
    · cases t
    · exact Option.some.inj t
  by_cases g1 : (A.hi == 0) = true
  · rw [if_pos g1]
    have g1' : A.hi = 0 := by simpa using g1
    have hd0 : m.fdot = 0 := by omega
    cases e : A.ppuCtrl.bit 0x80 with
    | none => exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
    | some b =>
      have hb' : b = (m.ppuCtrl &&& 0x80 != 0) := hb e
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      obtain rfl := Option.some.inj hB
      rw [tick_firstX c m hd0 (by omega) (by omega)]
      refine ⟨{ hs with
        vb := rfl
        nmi := ?_
        s0 := ?_
        lo := Nat.le_refl _
        hi := Nat.le_refl _
        lim := ?_ }, Or.inl ⟨rfl, rfl, ?_⟩⟩
      · show (m.nmiPending || (m.ppuCtrl &&& 0x80 != 0)) = (A.nmi || b)
        rw [hs.nmi, hb']
      · show m.sprite0 = s0f (3 * c)
        rw [hs.s0, hd0, s0f_lt (by omega), s0f_lt (by omega)]
      · show 3 * c < dotsPerFrame
        omega
      · show 3 * c = m.fdot + 3 * c
        omega
  rw [if_neg g1]
  by_cases g2 : (decide (dotSpr0 ≤ A.lo) && decide (dotsPerFrame - 1 ≤ A.hi + 3 * c)) = true
  · rw [if_pos g2]
    have g2' : dotSpr0 ≤ A.lo ∧ dotsPerFrame - 1 ≤ A.hi + 3 * c := by simpa using g2
    obtain ⟨g3, g4⟩ := g2'
    cases e : A.ppuCtrl.bit 0x80 with
    | none => exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
    | some b =>
      have hb' : b = (m.ppuCtrl &&& 0x80 != 0) := hb e
      have hs1 : m.sprite0 = true := by
        rw [hs.s0]
        exact s0f_ge (by omega)
      rcases tick_end c m (by omega) with ⟨t1, t2⟩ | ⟨t1, t2⟩ | ⟨t1, d, t2, t3, t4⟩
      · refine ⟨some { A with lo := A.lo + 3 * c, hi := dotsPerFrame - 1 }, ?_, fun B hB => ?_⟩
        · simp only [List.mem_append]
          left; left
          rw [if_pos (by omega)]
          exact List.mem_singleton.2 rfl
        · obtain rfl := Option.some.inj hB
          rw [t2]
          refine ⟨{ hs with
            s0 := ?_
            lo := ?_
            hi := ?_
            lim := ?_ }, Or.inl ⟨rfl, rfl, rfl⟩⟩
          · show m.sprite0 = s0f (m.fdot + 3 * c)
            rw [hs1, s0f_ge (by omega)]
          · show A.lo + 3 * c ≤ m.fdot + 3 * c
            omega
          · exact t1
          · show dotsPerFrame - 1 < dotsPerFrame
            omega
      · refine ⟨some { A with lo := 0, hi := 0, k := A.k + 1 }, ?_, fun B hB => ?_⟩
        · simp only [List.mem_append]
          left; right
          exact List.mem_singleton.2 rfl
        · obtain rfl := Option.some.inj hB
          rw [t2]
          refine ⟨{ hs with
            s0 := ?_
            lo := Nat.le_refl _
            hi := Nat.le_refl _
            lim := ?_
            fr := ?_ }, Or.inr ⟨rfl, rfl⟩⟩
          · show m.sprite0 = s0f 0
            rw [hs1, s0f_lt (by omega)]
          · show 0 < dotsPerFrame
            omega
          · show m.frame + 1 = F.1 + (A.k + 1)
            have := hs.fr
            omega
      · refine ⟨some { A with lo := 1, hi := A.hi + 3 * c - (dotsPerFrame - 1), vb := true, nmi := A.nmi || b, k := A.k + 1 }, ?_, fun B hB => ?_⟩
        · simp only [List.mem_append]
          right
          rw [if_pos (by omega)]
          exact List.mem_singleton.2 rfl
        · obtain rfl := Option.some.inj hB
          rw [t4]
          refine ⟨{ hs with
            vb := rfl
            nmi := ?_
            s0 := ?_
            lo := t2
            hi := ?_
            lim := ?_
            fr := ?_ }, Or.inr ⟨rfl, rfl⟩⟩
          · show (m.nmiPending || (m.ppuCtrl &&& 0x80 != 0)) = (A.nmi || b)
            rw [hs.nmi, hb']
          · show m.sprite0 = s0f d
            rw [hs1, s0f_lt (by omega)]
          · show d ≤ A.hi + 3 * c - (dotsPerFrame - 1)
            omega
          · show A.hi + 3 * c - (dotsPerFrame - 1) < dotsPerFrame
            omega
          · show m.frame + 1 = F.1 + (A.k + 1)
            have := hs.fr
            omega
  rw [if_neg g2]
  by_cases g3 : (decide (dotVblSet ≤ A.lo) && A.vb && decide (A.hi < dotVblClr) && decide (A.lo + 3 * c < dotVblClr) && decide (dotVblClr ≤ A.hi + 3 * c) && decide (A.hi + 3 * c < dotsPerFrame - 1)) = true
  · rw [if_pos g3]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at g3
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := g3
    have ht := tick_mid c m (by omega) (by omega)
    by_cases hn : m.fdot + 3 * c < dotVblClr
    · refine ⟨_, List.mem_cons_self, fun B hB => ?_⟩
      obtain rfl := Option.some.inj hB
      rw [ht]
      refine ⟨{ hs with
        vb := ?_
        s0 := s0f_step _ _ (by omega) _ hs.s0
        lo := ?_
        hi := ?_
        lim := ?_ }, Or.inl ⟨rfl, rfl, rfl⟩⟩
      · show (if m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c then false else m.vblank) = A.vb
        rw [if_neg (by omega)]
        exact hs.vb
      · show A.lo + 3 * c ≤ m.fdot + 3 * c
        omega
      · show m.fdot + 3 * c ≤ dotVblClr - 1
        omega
      · show dotVblClr - 1 < dotsPerFrame
        omega
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun B hB => ?_⟩
      obtain rfl := Option.some.inj hB
      rw [ht]
      refine ⟨{ hs with
        vb := ?_
        s0 := s0f_step _ _ (by omega) _ hs.s0
        lo := ?_
        hi := ?_
        lim := ?_ }, Or.inl ⟨rfl, rfl, rfl⟩⟩
      · show (if m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c then false else m.vblank) = false
        rw [if_pos ⟨by omega, by omega⟩]
      · show dotVblClr ≤ m.fdot + 3 * c
        omega
      · show m.fdot + 3 * c ≤ A.hi + 3 * c
        omega
      · show A.hi + 3 * c < dotsPerFrame
        omega
  · rw [if_neg g3]
    exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩

/-- `xtick` follows `tick` -/
theorem s_xtick {A : AS} {m : Machine} (hs : Sim E F A m) (c : Nat) :
    ∃ r ∈ xtick c A, ∀ B, r = some B → Sim E F B (go (tick c) m).2 ∧ TickRel c A B m (go (tick c) m).2 := by
  unfold xtick
  cases e : atick c c A with
  | some p =>
    obtain ⟨u, B0⟩ := p
    refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
    obtain rfl := Option.some.inj hB
    obtain ⟨_, h2, h3⟩ := s_tick (E := E) (F := F) (Nat.le_refl c) (Nat.le_refl c) A m hs u B0 e
    refine ⟨h2, Or.inl ⟨?_, h3.1, tick_adv hs e⟩⟩
    have a1 := hs.fr
    have a2 := h2.fr
    have a3 := h3.1
    omega
  | none => exact s_xtickOwn hs c

end

/-! ## A step follows the machine -/

section
variable {E : Env} {F : Nat × UInt8}

/-- the rest of a branch, after the offset -/
theorem branch_after (cond : Machine → Bool) (off : UInt8) (m : Machine) :
    (go ((get >>= fun (n : Machine) => if cond n = true then
        (setPC (n.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0))) >>= fun _ =>
          tick (if (n.pc ^^^ (n.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0)))) &&& 0xFF00 != 0 then 2 else 1))
      else (pure () : M Unit)) : M Unit) m).2 =
    if cond m = true then
      (go (tick (if (m.pc ^^^ (m.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0)))) &&& 0xFF00 != 0 then 2 else 1))
        { m with pc := m.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0)) }).2
    else m := by
  by_cases h : cond m = true
  · rw [if_pos h]
    show (go (if cond m = true then _ else _) m).2 = _
    rw [if_pos h]
    rfl
  · rw [if_neg h]
    show (go (if cond m = true then _ else _) m).2 = _
    rw [if_neg h]
    rfl

/-- a branch of the machine, by its parts -/
theorem go_branch (cond : Machine → Bool) (m : Machine) : (go (branch cond >>= fun _ => tick 2) m).2 =
    if cond (go fetch m).2 = true then
      (go (tick 2) (go (tick (if ((go fetch m).2.pc ^^^ ((go fetch m).2.pc + ((go fetch m).1.toUInt16 ||| (if (go fetch m).1 ≥ 0x80 then 0xFF00 else 0)))) &&& 0xFF00 != 0 then 2 else 1))
        { (go fetch m).2 with pc := (go fetch m).2.pc + ((go fetch m).1.toUInt16 ||| (if (go fetch m).1 ≥ 0x80 then 0xFF00 else 0)) }).2).2
    else (go (tick 2) (go fetch m).2).2 := by
  have e : (go (branch cond) m).2 = _ := branch_after cond (go fetch m).1 (go fetch m).2
  rw [PipeTransitionAll.go_bind, e]
  split <;> rfl

/-- the relation of a step, from a tick -/
theorem steprel_of_tick {c : Nat} {A0 A B : AS} {m0 m m' : Machine} (hk : A.k = A0.k) (hf : m.frame = m0.frame) (hd : m0.fdot ≤ m.fdot) (hc : 1 ≤ c)
    (h : TickRel c A B m m') : StepRel A0 B m0 m' := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.trans hk, h2.trans hf, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- a branch that may cross the end of a frame -/
theorem s_xbr (mask : UInt8) (neg : Bool) {cond : Machine → Bool} (hc : ∀ m, cond m = ((m.p &&& mask != 0) == neg)) {A : AS} {m : Machine} (hs : Sim E F A m) :
    ∃ r ∈ xbr E mask neg A, ∀ B, r = some B → Sim E F B (go (branch cond >>= fun _ => tick 2) m).2 ∧ StepRel A B m (go (branch cond >>= fun _ => tick 2) m).2 := by
  unfold xbr
  cases e1 : afetch E A with
  | none => exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  | some p =>
    obtain ⟨off, A1⟩ := p
    dsimp only
    obtain ⟨h1, hs1, ha1⟩ := s_fetch A m hs off A1 e1
    rw [go_branch]
    generalize hm1 : (go fetch m).2 = m1 at hs1 ha1 ⊢
    rw [← h1]
    have hk1 : A1.k = A.k := by
      have a1 := hs.fr
      have a2 := hs1.fr
      have a3 := ha1.1
      omega
    cases e2 : A1.p.bit mask with
    | none => exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
    | some b =>
      dsimp only
      have t := TaintRun.TR_bit mask hs1.p
      rw [e2] at t
      have hb : b = (m1.p &&& mask != 0) := by
        rcases t with t | t
        · cases t
        · exact Option.some.inj t
      have hcond : cond m1 = (b == neg) := by rw [hc, hb]
      rw [hcond]
      by_cases hn : (b == neg) = true
      · rw [if_pos hn, if_pos hn]
        rw [← hs1.pc]
        generalize ht : m1.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0)) = t2
        generalize hcc : (if (m1.pc ^^^ t2) &&& 0xFF00 != 0 then 2 else 1) = c1
        have hc1 : 1 ≤ c1 := by
          rw [← hcc]
          split <;> omega
        have hs2 : Sim E F { A1 with pc := t2 } { m1 with pc := t2 } := { hs1 with pc := rfl }
        obtain ⟨r1, hr1, g1⟩ := s_xtick hs2 c1
        cases r1 with
        | none => exact ⟨none, List.mem_flatMap.2 ⟨none, hr1, List.mem_singleton.2 rfl⟩, fun B hB => by cases hB⟩
        | some B1 =>
          obtain ⟨g2, g3⟩ := g1 B1 rfl
          obtain ⟨r2, hr2, g4⟩ := s_xtick g2 2
          refine ⟨_, List.mem_flatMap.2 ⟨some B1, hr1, List.mem_map.2 ⟨r2, hr2, rfl⟩⟩, fun B hB => ?_⟩
          cases r2 with
          | none => cases hB
          | some B2 =>
            simp only [Option.bind_some] at hB
            split at hB
            · rename_i hle
              obtain rfl := Option.some.inj hB
              obtain ⟨g5, g6⟩ := g4 B2 rfl
              refine ⟨g5, ?_⟩
              rcases g3 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩ <;> rcases g6 with ⟨k4, k5, k6⟩ | ⟨k4, k5⟩
              · refine Or.inl ⟨by simp only at k1; omega, ?_, ?_⟩
                · rw [k5, k2]
                  exact ha1.1
                · rw [k6, k3]
                  have := ha1.2
                  show m.fdot + 3 ≤ _
                  have e0 : ({ m1 with pc := t2 } : Machine).fdot = m1.fdot := rfl
                  rw [e0]
                  omega
              · refine Or.inr ⟨by simp only at k1; omega, ?_⟩
                rw [k5, k2]
                exact congrArg (· + 1) ha1.1
              · refine Or.inr ⟨by simp only at k1; omega, ?_⟩
                rw [k5, k2]
                exact congrArg (· + 1) ha1.1
              · exfalso
                simp only at k1
                omega
            · cases hB
      · rw [if_neg hn, if_neg hn]
        obtain ⟨r1, hr1, g1⟩ := s_xtick hs1 2
        refine ⟨r1, hr1, fun B hB => ?_⟩
        obtain ⟨g2, g3⟩ := g1 B hB
        exact ⟨g2, steprel_of_tick hk1 ha1.1 ha1.2 (by omega) g3⟩

set_option maxRecDepth 100000 in
theorem op_D0 : opTable[(0xD0 : UInt8).toNat]?.getD opJAM = opBNE := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

set_option maxRecDepth 100000 in
theorem op_B0 : opTable[(0xB0 : UInt8).toNat]?.getD opJAM = opBCS := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

set_option maxRecDepth 100000 in
theorem op_10 : opTable[(0x10 : UInt8).toNat]?.getD opJAM = opBPL := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

set_option maxRecDepth 100000 in
theorem cyc_D0 : (cycTable.get! (0xD0 : UInt8).toNat).toNat = 2 := by decide
set_option maxRecDepth 100000 in
theorem cyc_B0 : (cycTable.get! (0xB0 : UInt8).toNat).toNat = 2 := by decide
set_option maxRecDepth 100000 in
theorem cyc_10 : (cycTable.get! (0x10 : UInt8).toNat).toNat = 2 := by decide

/-- a step that is not the idle loop and no NMI: the action and the tick -/
theorem step_plain {A : AS} {m : Machine} (hs : Sim E F A m) (hn : A.nmi = false) (hp : 0x8000 ≤ A.pc) (hi : isIdle E A.pc (E.prg.get! (A.pc &&& E.mask).toNat) = false) :
    go step m = go ((opTable[(E.prg.get! (A.pc &&& E.mask).toNat).toNat]?.getD opJAM) >>= fun _ => tick (cycTable.get! (E.prg.get! (A.pc &&& E.mask).toNat).toNat).toNat) { m with pc := m.pc + 1 } := by
  have hn2 : m.nmiPending = false := by rw [hs.nmi]; exact hn
  have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
  rw [step_op hn2 hs.halted hpm]
  have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = E.prg.get! (A.pc &&& E.mask).toNat := by
    rw [hs.prg, hs.mask, hs.pc]
  rw [hop]
  generalize hopp : E.prg.get! (A.pc &&& E.mask).toNat = op at hi
  have hidle : (op == 0x4C && m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat == m.pc.toUInt8
      && m.prg.get! ((m.pc + 2) &&& m.prgMask).toNat == (m.pc >>> 8).toUInt8 && decide (m.pc ≥ 0x8000)) = isIdle E A.pc op := by
    simp only [isIdle, hs.prg, hs.mask, hs.pc]
  unfold stepK
  simp only [hidle, hi, Bool.false_eq_true, if_false]

set_option maxRecDepth 100000 in
theorem op_B1x : opTable[(0xB1 : UInt8).toNat]?.getD opJAM = opLDA mIzyR := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

/-- the page penalty, which may come or not -/
theorem s_tick01x (b e : UInt16) : Snd E F TT (atick 0 1) (pagePenalty b e) := by
  unfold pagePenalty
  split
  · exact s_tick (Nat.zero_le _) (Nat.le_refl _)
  · exact s_tick0

/-- the number of a pointer from its two bytes -/
theorem ptr_toNat (u v : UInt8) : (u.toUInt16 ||| (v.toUInt16 <<< 8)).toNat = u.toNat + 256 * v.toNat := by
  have hu := UInt8.toNat_lt u
  have hv := UInt8.toNat_lt v
  rw [UInt16.toNat_or, UInt16.toNat_shiftLeft]
  simp only [UInt8.toNat_toUInt16]
  have e1 : (8 : UInt16).toNat % 16 = 8 := by decide
  rw [e1, Nat.shiftLeft_eq]
  have e2 : v.toNat * 2 ^ 8 % 65536 = v.toNat * 2 ^ 8 := Nat.mod_eq_of_lt (by omega)
  rw [e2, Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hu, Nat.shiftLeft_eq]
  omega

/-- **The address is in the RAM or the ROM**, when the high byte of the pointer meets `ptrHiOK` -/
theorem wide_ok {hi : TaintRun.AB} {u v y : UInt8} (hk : ptrHiOK hi = true) (h : hi.mem v) :
    AdR ptrWide ((u.toUInt16 ||| (v.toUInt16 <<< 8)) + y.toUInt16) := by
  right
  refine ⟨by decide, ?_⟩
  have e1 := ptr_toNat u v
  have hu := UInt8.toNat_lt u
  have hv := UInt8.toNat_lt v
  have hy := UInt8.toNat_lt y
  have hy2 : y.toUInt16.toNat = y.toNat := by simp
  have hsum : ((u.toUInt16 ||| (v.toUInt16 <<< 8)) + y.toUInt16).toNat = (u.toNat + 256 * v.toNat + y.toNat) % 65536 := by
    rw [UInt16.toNat_add, e1, hy2]
  have g1 := TaintRun.minv_le h
  have g2 := TaintRun.le_maxv h
  simp only [ptrHiOK, Bool.or_eq_true, decide_eq_true_eq] at hk
  have lo8 : (ptrWide.lo).toNat = 32768 := rfl
  have hi8 : (ptrWide.hi).toNat = 8191 := rfl
  rcases hk with hk | hk
  · right
    apply UInt16.le_iff_toNat_le.2
    rw [hsum, hi8]
    omega
  · by_cases hlt : u.toNat + 256 * v.toNat + y.toNat < 65536
    · left
      apply UInt16.le_iff_toNat_le.2
      rw [hsum, lo8]
      omega
    · right
      apply UInt16.le_iff_toNat_le.2
      rw [hsum, hi8]
      omega

/-- **The read through a pointer whose high byte is known well enough** follows the machine's addressing mode -/
theorem s_aIzyHi : Snd E F AdR (aIzyHi E) mIzyR :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    refine Snd.bind (s_rd16zp _) fun p q hr => ?_
    obtain ⟨lo, hi⟩ := p
    obtain ⟨u, v, rfl, _, h2⟩ := hr
    by_cases hk : ptrHiOK hi = true
    · simp only [hk, if_true]
      exact Snd.get fun _ _ hs => Snd.bind (s_tick01x _ _) fun _ _ _ => Snd.pure (wide_ok hk h2)
    · simp only [hk, Bool.false_eq_true, if_false]
      exact Snd.fail

/-- a step of the machine is followed by `xstep1` -/
theorem s_xstep1 {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hs : Sim E F A m) :
    ∃ r ∈ xstep1 E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold xstep1
  dsimp only
  have base := s_astep1 hops hT hs
  by_cases h1 : (astep1 E ops A).all (·.isSome) = true
  · rw [if_pos h1]
    exact base
  rw [if_neg h1]
  by_cases h2 : (A.nmi || decide (A.pc < 0x8000)) = true
  · rw [if_pos h2]
    exact base
  rw [if_neg h2]
  have h2' : A.nmi = false ∧ ¬ A.pc < 0x8000 := by simpa using h2
  obtain ⟨hn, hp0⟩ := h2'
  have hp : 0x8000 ≤ A.pc := by
    have a1 : ¬ A.pc.toNat < (0x8000 : UInt16).toNat := fun h => hp0 (UInt16.lt_iff_toNat_lt.2 h)
    exact UInt16.le_iff_toNat_le.2 (by omega)
  by_cases h3 : (isIdle E A.pc (E.prg.get! (A.pc &&& E.mask).toNat) || (A.rk && isRkDec E A.pc (E.prg.get! (A.pc &&& E.mask).toNat))) = true
  · rw [if_pos h3]
    exact base
  rw [if_neg h3]
  have h3' : isIdle E A.pc (E.prg.get! (A.pc &&& E.mask).toNat) = false := by
    simp only [Bool.or_eq_true, not_or] at h3
    simpa using h3.1
  rw [step_plain hs hn hp h3']
  have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
    pc := by
      show m.pc + 1 = A.pc + 1
      rw [hs.pc] }
  generalize E.prg.get! (A.pc &&& E.mask).toNat = op
  have relbr : ∀ (x : Machine) (B : AS), StepRel { A with pc := A.pc + 1 } B { m with pc := m.pc + 1 } x → StepRel A B m x := fun _ _ h => h
  by_cases o1 : (op == 0xD0) = true
  · rw [if_pos o1]
    have o1' : op = 0xD0 := by simpa using o1
    subst o1'
    rw [op_D0, cyc_D0]
    obtain ⟨r, hr, g⟩ := s_xbr (E := E) (F := F) 0x02 false (cond := fun m => m.p &&& 0x02 == 0) (fun m => by cases h : (m.p &&& 0x02 == 0) <;> simp [bne, h]) hs1
    exact ⟨r, hr, g⟩
  rw [if_neg o1]
  by_cases o2 : (op == 0xB0) = true
  · rw [if_pos o2]
    have o2' : op = 0xB0 := by simpa using o2
    subst o2'
    rw [op_B0, cyc_B0]
    obtain ⟨r, hr, g⟩ := s_xbr (E := E) (F := F) 0x01 true (cond := fun m => m.p &&& 0x01 != 0) (fun m => by simp) hs1
    exact ⟨r, hr, g⟩
  rw [if_neg o2]
  by_cases o3 : (op == 0x10) = true
  · rw [if_pos o3]
    have o3' : op = 0x10 := by simpa using o3
    subst o3'
    rw [op_10, cyc_10]
    obtain ⟨r, hr, g⟩ := s_xbr (E := E) (F := F) 0x80 false (cond := fun m => m.p &&& 0x80 == 0) (fun m => by cases h : (m.p &&& 0x80 == 0) <;> simp [bne, h]) hs1
    exact ⟨r, hr, g⟩
  rw [if_neg o3]
  by_cases o4 : (cycOf op == 0) = true
  · rw [if_pos o4]
    exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  rw [if_neg o4]
  have hc1 : 1 ≤ cycOf op := by
    have : cycOf op ≠ 0 := by simpa using o4
    omega
  cases e : (ops[op.toNat]?.getD aJAM) { A with pc := A.pc + 1 } with
  | none =>
    dsimp only
    by_cases ob : (op == 0xB1) = true
    · rw [if_pos ob]
      have ob' : op = 0xB1 := by simpa using ob
      subst ob'
      cases e2 : aLDA E (aIzyHi E) { A with pc := A.pc + 1 } with
      | none => exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
      | some p =>
        obtain ⟨u, B0⟩ := p
        dsimp only
        obtain ⟨_, g1, g2⟩ := TaintRun.s_LDA (E := E) (F := F) s_aIzyHi _ _ hs1 u B0 e2
        rw [op_B1x, PipeTransitionAll.go_bind]
        have ee : (cycTable.get! (0xB1 : UInt8).toNat).toNat = cycOf 0xB1 := rfl
        rw [ee]
        obtain ⟨r, hr, g3⟩ := s_xtick g1 (cycOf 0xB1)
        refine ⟨r, hr, fun B hB => ?_⟩
        obtain ⟨g4, g5⟩ := g3 B hB
        refine ⟨g4, steprel_of_tick (A0 := A) (m0 := m) ?_ g2.1 g2.2 hc1 g5⟩
        have a2 := g1.fr
        rw [g2.1] at a2
        have a4 := hs.fr
        have a5 : ({ m with pc := m.pc + 1 } : Machine).frame = m.frame := rfl
        rw [a5] at a2
        omega
    · rw [if_neg ob]
      exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  | some p =>
    obtain ⟨u, B0⟩ := p
    dsimp only
    rw [hops] at e
    obtain ⟨_, g1, g2⟩ := s_op (E := E) (F := F) op.toNat _ _ hs1 u B0 e
    rw [PipeTransitionAll.go_bind]
    have ee : (cycTable.get! op.toNat).toNat = cycOf op := rfl
    rw [ee]
    obtain ⟨r, hr, g3⟩ := s_xtick g1 (cycOf op)
    refine ⟨r, hr, fun B hB => ?_⟩
    obtain ⟨g4, g5⟩ := g3 B hB
    refine ⟨g4, steprel_of_tick (A0 := A) (m0 := m) ?_ g2.1 g2.2 hc1 g5⟩
    have a2 := g1.fr
    rw [g2.1] at a2
    have a4 := hs.fr
    have a5 : ({ m with pc := m.pc + 1 } : Machine).frame = m.frame := rfl
    rw [a5] at a2
    omega

/-- a step of the machine, with the pieces -/
theorem s_xsuccs {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hs : Sim E F A m) :
    ∃ r ∈ xsuccs E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  obtain ⟨P, hP, h1, h2⟩ := cov_pieces A m hs
  obtain ⟨r, hr, h3⟩ := s_xstep1 hops hT h1
  refine ⟨r, List.mem_flatMap.2 ⟨P, hP, hr⟩, fun B hB => ?_⟩
  obtain ⟨h4, h5⟩ := h3 B hB
  refine ⟨h4, ?_⟩
  unfold StepRel at h5 ⊢
  rw [h2] at h5
  exact h5

end

/-! ## One frame, from a table -/

/-- from `A`, step by step until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def xwalk (C : Cfg) (fin : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (xsuccs C.E C.ops A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverIn C B) || xwalk C fin n B
      else B.k == A.k + 1 && fin B

section
variable {C : Cfg} {Fu : Nat} {F : Nat × UInt8} {fin : AS → Bool}

def XLive (C : Cfg) (fin : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, xwalk C fin n A = true

theorem cover_xlive (ht : C.t.all (xwalk C fin Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverIn C B = true) :
    ∃ D, XLive C fin F D m ∧ D.k = B.k := by
  unfold coverIn at h
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

theorem xlive_step (ht : C.t.all (xwalk C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : XLive C fin F A m) :
    (∃ A', XLive C fin F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [xwalk] at hw
  | succ n =>
    obtain ⟨r, hr, hB⟩ := s_xsuccs hops hT hs
    simp only [xwalk, List.all_eq_true] at hw
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_xlive ht h1 h3
          exact ⟨D, hD, hk.trans k1, k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

theorem xframe_run (ht : C.t.all (xwalk C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {f : Nat} :
    ∀ (n : Nat) (A : AS) (m : Machine), XLive C fin F A m → m.frame = f → dotsPerFrame ≤ m.fdot + 3 * n →
      (go (runUntilFrame (f + 1) n) m).2.frame = f + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go (runUntilFrame (f + 1) n) m).2 := by
  intro n
  induction n with
  | zero =>
    intro A m hl _ hd
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ n ih =>
    intro A m hl hf hd
    have hh := hl.1.halted
    rw [PipeTransitionAll.ruf_eq, if_neg (by simp [hf, hh])]
    rcases xlive_step ht hops hT hl with ⟨A', h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
    · have := ih A' _ h1 (h3.trans hf) (by omega)
      rw [h2] at this
      exact this
    · rw [ruf_doneF (by rw [h1, hf]; exact Nat.le_refl _) n]
      exact ⟨by rw [h1, hf], B, h2, h3, h4⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of a machine of `S`, when `S` covers the machine with this frame's pad. The frame may start and end anywhere. -/
theorem xframe_of_walk (ht : C.t.all (xwalk C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {S : AS} {m : Machine} {i : UInt8} (hw : xwalk C fin Fu S = true) (hs : Sim C.E F S { m with pad := smbToPad i }) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  rw [PipeTransitionAll.frame_eq]
  have hf : dotsPerFrame ≤ ({ m with pad := smbToPad i } : Machine).fdot + 3 * fuelPerFrame := by
    have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
    omega
  exact xframe_run ht hops hT (f := m.frame) fuelPerFrame S _ ⟨hs, Fu, hw⟩ rfl hf

end

/-! ## The search for the tables: no part of the proof -/

/-- the order of the search: a loop that counts `x` and `y` down goes in the order of its turns, so that paths join -/
def xprio (A : AS) : Nat :=
  (if A.x.isK then 255 - A.x.v.toNat else 0) * 256 + (if A.y.isK then 255 - A.y.v.toNat else 0)

def xkey (E : Env) (keep : List Nat) (A : AS) : Nat := xprio A * (2 ^ 800) + keyOf E keep A

def xroute (E : Env) (keep : List Nat) (X : Search) (B : AS) : Search :=
  let K := xkey E keep B
  match X.pending[K]? with
  | some P => { X with pending := X.pending.insert K (P.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
  | none => { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

/-- the search for a frame that starts at many places of a loop: one step at a time, in the order of `xprio` -/
partial def xsearchTurns (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (limit : Nat) (X0 : Search) : Search := Id.run do
  let mut X := X0
  let mut c := 0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      c := c + 1
      if n ≥ 2 || c % 64 == 0 then X := { X with out := X.out.push A }
      let rs := xsuccs E ops A
      X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
      if rs.any (·.isNone) then
        X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A }
      for b in rs.filterMap id do
        if b.k != A.k then X := { X with ends := X.ends.push b }
        else X := xroute E keep X b
  return X

/-- follow one waiting state as far as no other path can join -/
partial def xrunChain (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (X0 : Search) (A0 : AS) : Search := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := xsuccs E ops cur
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 128 &&
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
        X := route E keep X b
    break
  return X

/-- the search with chains, for a frame that starts at few places -/
partial def xsearchChains (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (limit : Nat) (X0 : Search) : Search := Id.run do
  let mut X := X0
  let mut c := 0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      c := c + 1
      if n ≥ 2 || c % 16 == 0 then X := { X with out := X.out.push A }
      if isSpin E A then X := { X with done := X.done.insert key A }
      X := xrunChain E ops keep X A
  return X

/-- the search stops after `limit` steps, with a failure -/
def xsearch (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (starts : List AS) (limit : Nat := 1000000) : Search :=
  if starts.length > 8 then xsearchTurns E ops keep limit (starts.foldl (xroute E keep) {})
  else xsearchChains E ops keep limit (starts.foldl (route E keep) {})

/-! ## Rows: the frames after the pipe, one state or a few for each frame -/

/-- the pad of a frame with no Start -/
def noStartPad : TaintRun.AB := ⟨0, 0x08⟩

/-- the input has no Start -/
def noStart (i : UInt8) : Bool := smbToPad i &&& 0x08 == 0

/-- what the rows have in common. `E` has a pad that is not known. -/
structure Ctx where
  E : Env
  sy : Syms
  nm : Names
  /-- the pipe's routine -/
  eng : UInt16
  /-- the table of `left` -/
  tbl : List (List UInt8 × Nat)
  B : Nat
  keep : List Nat

/-- the number `left` -/
def Ctx.left (c : Ctx) (m : Machine) : Nat := PipeChangeBound.leftOf c.sy c.nm c.eng c.tbl c.B m

/-- a state of the game core with a routine other than the pipe's: the only frames where Start pauses after the pipe -/
def coreFrame (sy : Syms) (eng : UInt16) (m : Machine) : Bool :=
  (peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore && (peek m sy.GameEngineSubroutine).toUInt16 != eng

/-- the states after `v` frames from the control's side, and the table of the frame from them -/
structure Row where
  /-- the frame's input has no Start -/
  core : Bool
  R : List AS
  /-- `left` on these states -/
  v : Nat
  t : Array AS
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray

def rowEnv (c : Ctx) (r : Row) : Env := if r.core then { c.E with pad := noStartPad } else c.E

def rowCfg (c : Ctx) (r : Row) : Cfg :=
  { E := rowEnv c r, ops := (aRows (rowEnv c r)).toArray, sy := c.sy, K := 1, keep := c.keep, t := r.t, idx := r.idx, cut := r.cut }

/-- the state knows the byte -/
def knowsAd (S : AS) (a : UInt16) : Bool := (S.getK (a &&& 0x7FF).toNat).isK

/-- the bytes of a state as a machine -/
def mOf (S : AS) : Machine := { ram := S.ram }

/-- the state knows the bytes of the key -/
def keyKnown (c : Ctx) (S : AS) : Bool :=
  knowsAd S c.sy.OperMode_Task && knowsAd S (c.nm.ad "ScreenRoutineTask") && knowsAd S c.sy.GameEngineSubroutine && knowsAd S (c.nm.ad "DisableScreenFlag") &&
  (if (peek (mOf S) c.sy.OperMode_Task).toUInt16 == c.sy.Task_GameCore then
    knowsAd S c.sy.Player_State && knowsAd S c.sy.Player_Y_Position && knowsAd S c.sy.Player_Y_MoveForce && knowsAd S c.sy.Player_YMF_Dummy && knowsAd S c.sy.Player_Y_Speed
  else true)

/-- at the frame's end: a state of the next row -/
def finOf (R' : List AS) (B : AS) : Bool := !B.rk && R'.any fun D => ({ B with k := 0 } : AS).le D

/-- the states of a row: `left` is known, and if the row asks for no Start, Start would pause -/
def statesOK (c : Ctx) (r : Row) : Bool :=
  r.R.all fun S => S.k == 0 && !S.rk && keyKnown c S && !PipeChangeBound.inPipe c.sy c.eng (mOf S) && c.left (mOf S) == r.v && (!r.core || coreFrame c.sy c.eng (mOf S))

/-- a frame from a row to the next -/
def linkOK (c : Ctx) (r r' : Row) : Bool :=
  statesOK c r && statesOK c r' && decide (r.v ≤ r'.v + 1) &&
    (rowCfg c r).t.all (xwalk (rowCfg c r) (finOf r'.R) TaintRun.walkFuel) && r.R.all (xwalk (rowCfg c r) (finOf r'.R) TaintRun.walkFuel)

/-- all the frames: `left` is 0 at the last row -/
def chainOK (c : Ctx) : List Row → Bool
  | [] => true
  | [r] => statesOK c r && r.v == 0
  | r :: r' :: t => linkOK c r r' && chainOK c (r' :: t)

/-- the frame's ends as the next states: at the idle loop only the bytes matter, and two kinds of dots -/
def canon (B : AS) : AS :=
  { B with k := 0, spent := false, a := TaintRun.AB.top, x := TaintRun.AB.top, y := TaintRun.AB.top, p := TaintRun.AB.top, padShift := TaintRun.AB.top, log := [] }

def joinDots (l : List AS) : List AS :=
  let j : List AS → List AS := fun xs => match xs with
    | [] => []
    | y :: ys => [ys.foldl AS.join y]
  j (l.filter (·.lo == 0)) ++ j (l.filter (·.lo != 0))

/-- the next states from the ends of a frame -/
def nextStates (E : Env) (last : Bool) (ends : List AS) : List AS :=
  if !last && ends.all (fun b => isIdle E b.pc (E.prg.get! (b.pc &&& E.mask).toNat)) then joinDots (ends.map canon)
  else ends.map fun b => { b with k := 0, spent := false, log := [] }

/-- the rows from the states `R`, for `n` frames -/
def rowsFrom (c : Ctx) : Nat → List AS → List Row
  | 0, R => [{ core := false, R, v := (R.head?.map (fun S => c.left (mOf S))).getD 0, t := #[], idx := {}, cut := ByteArray.empty }]
  | n + 1, R =>
    let core := R.any fun S => coreFrame c.sy c.eng (mOf S)
    let e : Env := if core then { c.E with pad := noStartPad } else c.E
    let X := xsearch e (aRows e).toArray c.keep R
    let P := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
        let k := keyOf e c.keep A
        (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
      (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
    { core, R, v := (R.head?.map (fun S => c.left (mOf S))).getD 0, t := X.out, idx := P.1, cut := P.2.1 } :: rowsFrom c n (nextStates c.E (n == 0) X.ends.toList)

section
variable {c : Ctx} {F : Nat × UInt8}

open PipeTransitionAll (mask_lt)

theorem peek_of_known {E : Env} {S : AS} {m : Machine} (hs : Sim E F S m) {a : UInt16} (h : knowsAd S a = true) : peek m a = peek (mOf S) a := by
  have hm := hs.ram _ (mask_lt a)
  exact TaintRun.isK_eq h hm

/-- `left` on a state that knows its key -/
theorem left_of_known {E : Env} {S : AS} {m : Machine} (hs : Sim E F S m) (hk : keyKnown c S = true) (hp : PipeChangeBound.inPipe c.sy c.eng (mOf S) = false) :
    c.left m = c.left (mOf S) := by
  unfold keyKnown at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hk
  have e1 := peek_of_known hs h1
  have e2 := peek_of_known hs h2
  have e3 := peek_of_known hs h3
  have e4 := peek_of_known hs h4
  have hp2 : PipeChangeBound.inPipe c.sy c.eng m = false := by
    rw [← hp]
    simp only [PipeChangeBound.inPipe, e1, e3]
  have hkey : PipeChangeBound.keyOf c.sy c.nm m = PipeChangeBound.keyOf c.sy c.nm (mOf S) := by
    unfold PipeChangeBound.keyOf
    simp only [e1, e2, e3, e4]
    split
    · rename_i hc
      simp only [hc, if_true] at h5
      simp only [Bool.and_eq_true] at h5
      obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩ := h5
      rw [peek_of_known hs g1, peek_of_known hs g2, peek_of_known hs g3, peek_of_known hs g4, peek_of_known hs g5]
    · rfl
  simp only [Ctx.left, PipeChangeBound.leftOf, hp, hp2, hkey]
  simp

theorem core_of_known {E : Env} {S : AS} {m : Machine} (hs : Sim E F S m) (hk : keyKnown c S = true) (h : coreFrame c.sy c.eng (mOf S) = true) : coreFrame c.sy c.eng m = true := by
  unfold keyKnown at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨h1, _⟩, h3⟩, _⟩, _⟩ := hk
  simp only [coreFrame, peek_of_known hs h1, peek_of_known hs h3] at h ⊢
  exact h

/-- the same machine with this frame's pad, in an environment with a smaller pad -/
theorem sim_pad {E : Env} {q : TaintRun.AB} {S : AS} {m : Machine} {p : UInt8} (hs : Sim E F S m) (hq : q.mem p) : Sim { E with pad := q } F S { m with pad := p } :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, hq, hs.padShift, hs.strobe, hs.halted, hs.trk, hs.size, hs.ram, hs.dg, hs.szR, hs.szK, hs.fr, hs.rkv⟩

/-- back from the smaller pad -/
theorem sim_unpad {E : Env} {q : TaintRun.AB} {S : AS} {m : Machine} (hE : E.pad = TaintRun.AB.top) (hs : Sim { E with pad := q } F S m) : Sim E F S m :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, by rw [hE]; exact TaintRun.mem_top _, hs.padShift, hs.strobe, hs.halted, hs.trk, hs.size, hs.ram, hs.dg, hs.szR, hs.szK, hs.fr, hs.rkv⟩

theorem two_le : 2 ≤ (2 : UInt8).toNat := by decide

/-- a machine is in a row -/
def Covered (c : Ctx) (r : Row) (m : Machine) : Prop := ∃ S ∈ r.R, Sim c.E (m.frame, 2) S m

theorem left_of_covered {r : Row} {m : Machine} (hr : statesOK c r = true) (h : Covered c r m) : c.left m = r.v := by
  obtain ⟨S, hS, hs⟩ := h
  simp only [statesOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hr
  obtain ⟨⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, h5⟩, _⟩ := hr S hS
  rw [left_of_known hs h3 h4, h5]

/-- **A frame from a row to the next.** -/
theorem link_frame (hE : c.E.pad = TaintRun.AB.top) {r r' : Row} (h : linkOK c r r' = true) {m : Machine} (hc : Covered c r m) {i : UInt8}
    (hi : coreFrame c.sy c.eng m = true → noStart i = true) : Covered c r' (frame m i) := by
  simp only [linkOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, _⟩, _⟩, h4⟩, h5⟩ := h
  obtain ⟨S, hS, hs⟩ := hc
  have h1' := h1
  simp only [statesOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true] at h1'
  obtain ⟨⟨⟨⟨⟨k0, _⟩, a3⟩, _⟩, _⟩, a6⟩ := h1' S hS
  have hs1 : Sim (rowCfg c r).E (m.frame, 2) S { m with pad := smbToPad i } := by
    show Sim (rowEnv c r) (m.frame, 2) S { m with pad := smbToPad i }
    unfold rowEnv
    split
    · rename_i hcore
      apply sim_pad hs
      have hcf : coreFrame c.sy c.eng (mOf S) = true := by
        rcases a6 with a6 | a6
        · rw [hcore] at a6
          cases a6
        · exact a6
      have hn := hi (core_of_known hs a3 hcf)
      have e : smbToPad i &&& 0x08 = 0 := by simpa [noStart] using hn
      show smbToPad i &&& 0x08 = 0 &&& 0x08
      rw [e]
      rfl
    · exact { hs with pad := by rw [hE]; exact TaintRun.mem_top _ }
  obtain ⟨g1, B, g2, g3, g4⟩ := xframe_of_walk (C := rowCfg c r) (F := (m.frame, 2)) h4 rfl two_le (List.all_eq_true.1 h5 S hS) hs1
  have g4' : Sim c.E (m.frame, 2) B (frame m i) := by
    have e4 : Sim (rowEnv c r) (m.frame, 2) B (frame m i) := g4
    unfold rowEnv at e4
    split at e4
    · exact sim_unpad hE e4
    · exact e4
  simp only [finOf, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at g2
  obtain ⟨hrk, D, hD, hle⟩ := g2
  have hbase : Sim c.E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
    refine { g4' with fr := ?_, rkv := ?_ }
    · show (frame m i).frame = (frame m i).frame + 0
      rfl
    · intro hr2
      have : B.rk = true := hr2
      rw [hrk] at this
      cases this
  exact ⟨D, hD, sim_le hle hbase⟩

/-- a machine is in one of the rows -/
def InvL (c : Ctx) : List Row → Machine → Prop
  | [], _ => False
  | r :: t, m => Covered c r m ∨ InvL c t m

/-- **A frame in the rows.** `left` is 0 already, or the machine stays in the rows and `left` falls by at most one. -/
theorem chain_step (hE : c.E.pad = TaintRun.AB.top) : ∀ (l : List Row), chainOK c l = true → ∀ {m : Machine}, InvL c l m → ∀ {i : UInt8},
    (coreFrame c.sy c.eng m = true → noStart i = true) → c.left m = 0 ∨ (InvL c l (frame m i) ∧ c.left m ≤ c.left (frame m i) + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ m h
    cases h
  | cons r t ih =>
    intro hl m h i hi
    cases t with
    | nil =>
      simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hl
      rcases h with h | h
      · left
        rw [left_of_covered hl.1 h, hl.2]
      · cases h
    | cons r2 t2 =>
      simp only [chainOK, Bool.and_eq_true] at hl
      obtain ⟨h1, h2⟩ := hl
      rcases h with h | h
      · right
        have hn := link_frame hE h1 h hi
        refine ⟨Or.inr (Or.inl hn), ?_⟩
        simp only [linkOK, Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, _⟩ := h1
        rw [left_of_covered a1 h, left_of_covered a2 hn]
        exact a3
      · rcases ih h2 h hi with h3 | ⟨h3, h4⟩
        · exact Or.inl h3
        · exact Or.inr ⟨Or.inr h3, h4⟩

/-- a machine of the first states is in the rows -/
theorem inv_head (n : Nat) (R : List AS) {m : Machine} (h : ∃ S ∈ R, Sim c.E (m.frame, 2) S m) : InvL c (rowsFrom c n R) m := by
  cases n with
  | zero => exact Or.inl h
  | succ n => exact Or.inl h

/-! ### Rows that keep `dg`

A state that knows a bit 1 in a byte of `D` gets `dg` (`normD`). At the frame's end the states with `dg` and those without it are not put together (`joinDotsD`). -/

/-- `dg` from a known bit 1 in a byte of `D` -/
def normD (D : List Nat) (B : AS) : AS :=
  if D.any (fun i => decide (i < 2048) && ((B.getK i).v &&& (B.getK i).k != 0)) then { B with dg := true } else B

theorem sim_normD {E : Env} {B : AS} {m : Machine} (hs : Sim E F B m) : Sim E F (normD E.D B) m := by
  unfold normD
  split
  · rename_i h
    obtain ⟨i, hi, h1⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
    have hm := hs.ram i h1.1
    have hne : m.ram.get! i ≠ 0 := by
      intro h0
      rw [h0] at hm
      simp only [TaintRun.AB.mem] at hm
      apply h1.2
      rw [← hm]
      exact UInt8.zero_and
    exact { hs with dg := fun _ => List.any_eq_true.2 ⟨i, hi, by simpa using hne⟩ }
  · exact hs

/-- the frame's ends as the next states, as `joinDots`, but states with `dg` and states without it are not put together -/
def joinDotsD (l : List AS) : List AS :=
  joinDots (l.filter (·.dg)) ++ joinDots (l.filter (!·.dg))

/-- the next states from the ends of a frame, with `normD` and `joinDotsD` -/
def nextStatesD (E : Env) (last : Bool) (ends : List AS) : List AS :=
  if !last && ends.all (fun b => isIdle E b.pc (E.prg.get! (b.pc &&& E.mask).toNat)) then joinDotsD (ends.map fun b => normD E.D (canon b))
  else ends.map fun b => { b with k := 0, spent := false, log := [] }

/-- at the frame's end: a state of the next row, after `normD` -/
def finOfD (D : List Nat) (R' : List AS) (B : AS) : Bool := !B.rk && R'.any fun S => (normD D ({ B with k := 0 } : AS)).le S

/-- a frame from a row to the next, with `finOfD` -/
def linkOKD (c : Ctx) (r r' : Row) : Bool :=
  statesOK c r && statesOK c r' && decide (r.v ≤ r'.v + 1) &&
    (rowCfg c r).t.all (xwalk (rowCfg c r) (finOfD c.E.D r'.R) TaintRun.walkFuel) && r.R.all (xwalk (rowCfg c r) (finOfD c.E.D r'.R) TaintRun.walkFuel)

/-- all the frames, with `linkOKD`: `left` is 0 at the last row -/
def chainOKD (c : Ctx) : List Row → Bool
  | [] => true
  | [r] => statesOK c r && r.v == 0
  | r :: r' :: t => linkOKD c r r' && chainOKD c (r' :: t)

/-- **A frame from a row to the next**, with `finOfD` -/
theorem link_frameD (hE : c.E.pad = TaintRun.AB.top) {r r' : Row} (h : linkOKD c r r' = true) {m : Machine} (hc : Covered c r m) {i : UInt8}
    (hi : coreFrame c.sy c.eng m = true → noStart i = true) : Covered c r' (frame m i) := by
  simp only [linkOKD, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, _⟩, _⟩, h4⟩, h5⟩ := h
  obtain ⟨S, hS, hs⟩ := hc
  have h1' := h1
  simp only [statesOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true] at h1'
  obtain ⟨⟨⟨⟨⟨k0, _⟩, a3⟩, _⟩, _⟩, a6⟩ := h1' S hS
  have hs1 : Sim (rowCfg c r).E (m.frame, 2) S { m with pad := smbToPad i } := by
    show Sim (rowEnv c r) (m.frame, 2) S { m with pad := smbToPad i }
    unfold rowEnv
    split
    · rename_i hcore
      apply sim_pad hs
      have hcf : coreFrame c.sy c.eng (mOf S) = true := by
        rcases a6 with a6 | a6
        · rw [hcore] at a6
          cases a6
        · exact a6
      have hn := hi (core_of_known hs a3 hcf)
      have e : smbToPad i &&& 0x08 = 0 := by simpa [noStart] using hn
      show smbToPad i &&& 0x08 = 0 &&& 0x08
      rw [e]
      rfl
    · exact { hs with pad := by rw [hE]; exact TaintRun.mem_top _ }
  obtain ⟨g1, B, g2, g3, g4⟩ := xframe_of_walk (C := rowCfg c r) (F := (m.frame, 2)) h4 rfl two_le (List.all_eq_true.1 h5 S hS) hs1
  have g4' : Sim c.E (m.frame, 2) B (frame m i) := by
    have e4 : Sim (rowEnv c r) (m.frame, 2) B (frame m i) := g4
    unfold rowEnv at e4
    split at e4
    · exact sim_unpad hE e4
    · exact e4
  simp only [finOfD, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at g2
  obtain ⟨hrk, D, hD, hle⟩ := g2
  have hbase : Sim c.E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
    refine { g4' with fr := ?_, rkv := ?_ }
    · show (frame m i).frame = (frame m i).frame + 0
      rfl
    · intro hr2
      have : B.rk = true := hr2
      rw [hrk] at this
      cases this
  exact ⟨D, hD, sim_le hle (sim_normD hbase)⟩

/-- **A frame in the rows**, with `chainOKD` -/
theorem chain_stepD (hE : c.E.pad = TaintRun.AB.top) : ∀ (l : List Row), chainOKD c l = true → ∀ {m : Machine}, InvL c l m → ∀ {i : UInt8},
    (coreFrame c.sy c.eng m = true → noStart i = true) → c.left m = 0 ∨ (InvL c l (frame m i) ∧ c.left m ≤ c.left (frame m i) + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ m h
    cases h
  | cons r t ih =>
    intro hl m h i hi
    cases t with
    | nil =>
      simp only [chainOKD, Bool.and_eq_true, beq_iff_eq] at hl
      rcases h with h | h
      · left
        rw [left_of_covered hl.1 h, hl.2]
      · cases h
    | cons r2 t2 =>
      simp only [chainOKD, Bool.and_eq_true] at hl
      obtain ⟨h1, h2⟩ := hl
      rcases h with h | h
      · right
        have hn := link_frameD hE h1 h hi
        refine ⟨Or.inr (Or.inl hn), ?_⟩
        simp only [linkOKD, Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, _⟩ := h1
        rw [left_of_covered a1 h, left_of_covered a2 hn]
        exact a3
      · rcases ih h2 h hi with h3 | ⟨h3, h4⟩
        · exact Or.inl h3
        · exact Or.inr ⟨Or.inr h3, h4⟩

theorem states_of_chainD : ∀ (l : List Row), chainOKD c l = true → ∀ r ∈ l, statesOK c r = true
  | [], _, r, hr => by cases hr
  | [r0], h, r, hr => by
    simp only [chainOKD, Bool.and_eq_true] at h
    rw [List.mem_singleton] at hr
    rw [hr]
    exact h.1
  | r0 :: r1 :: t, h, r, hr => by
    simp only [chainOKD, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hr with e | hr
    · rw [e]
      simp only [linkOKD, Bool.and_eq_true] at h1
      obtain ⟨⟨⟨⟨a1, _⟩, _⟩, _⟩, _⟩ := h1
      exact a1
    · exact states_of_chainD (r1 :: t) h2 r hr

/-- the rows from the states `R`, for `n` frames, as `rowsFrom`, with `nextStatesD` -/
def rowsFromD (c : Ctx) : Nat → List AS → List Row
  | 0, R => [{ core := false, R, v := (R.head?.map (fun S => c.left (mOf S))).getD 0, t := #[], idx := {}, cut := ByteArray.empty }]
  | n + 1, R =>
    let core := R.any fun S => coreFrame c.sy c.eng (mOf S)
    let e : Env := if core then { c.E with pad := noStartPad } else c.E
    let X := xsearch e (aRows e).toArray c.keep R
    let P := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
        let k := keyOf e c.keep A
        (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
      (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
    { core, R, v := (R.head?.map (fun S => c.left (mOf S))).getD 0, t := X.out, idx := P.1, cut := P.2.1 } :: rowsFromD c n (nextStatesD c.E (n == 0) X.ends.toList)

theorem inv_headD (n : Nat) (R : List AS) {m : Machine} (h : ∃ S ∈ R, Sim c.E (m.frame, 2) S m) : InvL c (rowsFromD c n R) m := by
  cases n with
  | zero => exact Or.inl h
  | succ n => exact Or.inl h

/-! ### Control where `left` is 0 -/

/-- the state knows the bytes of control, and they give control -/
def ctlKnown (sy : Syms) (S : AS) : Bool :=
  knowsAd S sy.OperMode && knowsAd S sy.OperMode_Task && knowsAd S sy.GameEngineSubroutine && controllable sy (mOf S)

/-- every row where `left` is 0 has only states with control -/
def zeroCtl (sy : Syms) (l : List Row) : Bool := l.all fun r => r.v != 0 || r.R.all (ctlKnown sy)

theorem ctl_of_known {sy : Syms} {E : Env} {S : AS} {m : Machine} (hs : Sim E F S m) (h : ctlKnown sy S = true) : controllable sy m = true := by
  simp only [ctlKnown, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold controllable at h4 ⊢
  rw [peek_of_known hs h1, peek_of_known hs h2, peek_of_known hs h3]
  exact h4

theorem covered_of_invL : ∀ {l : List Row} {m : Machine}, InvL c l m → ∃ r ∈ l, Covered c r m
  | [], _, h => by cases h
  | r :: t, m, h => by
    rcases h with h | h
    · exact ⟨r, List.mem_cons_self, h⟩
    · obtain ⟨r', hr', h'⟩ := covered_of_invL h
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

/-- **Control where `left` is 0.** In rows that pass `zeroCtl`, a machine with `left` 0 has control. -/
theorem ctl_of_zero {sy : Syms} {l : List Row} (hl : ∀ r ∈ l, statesOK c r = true) (hz : zeroCtl sy l = true) {m : Machine} (h : InvL c l m) (h0 : c.left m = 0) :
    controllable sy m = true := by
  obtain ⟨r, hr, S, hS, hs⟩ := covered_of_invL h
  have hv : c.left m = r.v := left_of_covered (hl r hr) ⟨S, hS, hs⟩
  simp only [zeroCtl, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hz
  rcases hz r hr with h1 | h1
  · exact absurd (hv.symm.trans h0) h1
  · exact ctl_of_known hs (h1 S hS)

end

/-! ## The state at the exit -/

/-- the start states of the rows: from the machine `x` when the timer has run out, for dot 0 or dots `1..9`. The bytes `K` are known, and the low bit of the pause status byte `gps` is 0. -/
def exitStarts (x : Machine) (K : List Nat) (gps : Nat) : List AS :=
  [true, false].map fun low => ({ startOf x K low with rk := false } : AS).setK gps ⟨0, 1⟩

/-- **The condition on the state at the exit.** The frame has ended in the idle loop; the bytes `K` are those of `x`; the game is not paused. All other bytes are free. -/
structure ExitCond (E : Env) (x : Machine) (K : List Nat) (gps : Nat) (m : Machine) : Prop where
  dot : m.fdot < 10
  flags : (m.fdot = 0 ∧ m.vblank = false ∧ m.nmiPending = false) ∨ (1 ≤ m.fdot ∧ m.vblank = true ∧ m.nmiPending = true)
  s0 : m.sprite0 = true
  ctrl : m.ppuCtrl &&& 0x80 = 0x80
  strobe : m.padStrobe = false
  halted : m.halted = false
  trk : m.trk = false
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  size : m.ram.size = 2048
  pc : m.pc = x.pc
  s : m.s = x.s
  bytes : ∀ i ∈ K, m.ram.get! i = x.ram.get! i
  notPaused : m.ram.get! gps &&& 1 = 0

/-- `ExitCond` as a check, for a program -/
def exitOK (E : Env) (x : Machine) (K : List Nat) (gps : Nat) (m : Machine) : Bool :=
  decide (m.fdot < 10) && ((m.fdot == 0 && !m.vblank && !m.nmiPending) || (decide (1 ≤ m.fdot) && m.vblank && m.nmiPending)) && m.sprite0 &&
  m.ppuCtrl &&& 0x80 == 0x80 && !m.padStrobe && !m.halted && !m.trk && decide (m.prg.data = E.prg.data) && m.prgMask == E.mask && m.ram.size == 2048 &&
  m.pc == x.pc && m.s == x.s && K.all (fun i => m.ram.get! i == x.ram.get! i) && m.ram.get! gps &&& 1 == 0

section
variable {E : Env} {F : Nat × UInt8}

open PipeTransitionAll (ba_size_set ba_get_set_self ba_get_set_ne)

/-- what is known of a byte of the machine can be put into the state -/
theorem sim_refine {A : AS} {m : Machine} (hs : Sim E F A m) {i : Nat} {v : TaintRun.AB} (hv : v.mem (m.ram.get! i)) : Sim E F (A.setK i v) m := by
  refine { hs with
    ram := ?_
    szR := ?_
    szK := ?_ }
  · intro j hj
    show TaintRun.AB.mem ⟨(A.ram.set! i v.v).get! j, (A.kn.set! i v.k).get! j⟩ (m.ram.get! j)
    by_cases hij : i = j
    · subst hij
      rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hj), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hj)]
      exact hv
    · rw [ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij]
      exact hs.ram j hj
  · show (A.ram.set! i _).size = 2048
    rw [ba_size_set]
    exact hs.szR
  · show (A.kn.set! i _).size = 2048
    rw [ba_size_set]
    exact hs.szK

/-- the check on the known bytes -/
def exitStartsOK (x : Machine) (K : List Nat) : Bool := startsOK [(x, K)]

/-- a machine with the condition is in a start state -/
theorem exit_cover {x : Machine} {K : List Nat} {gps : Nat} (hV : exitStartsOK x K = true) (hp : E.pad = TaintRun.AB.top) {m : Machine} (h : ExitCond E x K gps m) :
    ∃ S ∈ exitStarts x K gps, Sim E (m.frame, 2) S m := by
  simp only [exitStartsOK, startsOK, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hV
  obtain ⟨⟨s1, s2⟩, s3⟩ := hV
  have key : ∀ low : Bool, (low = true ↔ m.fdot = 0) → Sim E (m.frame, 2) ({ startOf x K low with rk := false } : AS) m := by
    intro low hl
    have hvb : m.vblank = !low ∧ m.nmiPending = !low := by
      rcases h.flags with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
      · have : low = true := hl.2 a1
        subst this
        exact ⟨a2, a3⟩
      · have : low = false := by
          cases low with
          | false => rfl
          | true =>
            have := hl.1 rfl
            omega
        subst this
        exact ⟨a2, a3⟩
    have hlo : (if low = true then 0 else 1) ≤ m.fdot := by
      cases low with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have : m.fdot ≠ 0 := fun h0 => by
          have := hl.2 h0
          cases this
        omega
    have hhi : m.fdot ≤ (if low = true then 0 else 9) := by
      have hd := h.dot
      cases low with
      | true =>
        have := hl.1 rfl
        simp only [if_true]
        omega
      | false =>
        simp only [Bool.false_eq_true, if_false]
        omega
    refine ⟨TaintRun.mem_top _, TaintRun.mem_top _, TaintRun.mem_top _, TaintRun.mem_top _, h.s, h.pc, h.prg, h.mask, ?_, TaintRun.mem_top _, hvb.1, hvb.2, ?_, hlo, hhi, ?_, by rw [hp]; exact TaintRun.mem_top _, TaintRun.mem_top _, h.strobe, h.halted, h.trk, h.size, ?_, ?_, s1, s2, ?_, ?_⟩
    · show m.ppuCtrl &&& 0x80 = (0x80 : UInt8) &&& 0x80
      rw [h.ctrl]
      decide
    · rw [h.s0]
      have : m.fdot ≤ 9 := by have := h.dot; omega
      exact (s0f_small this).symm
    · show (if low = true then 0 else 9) < dotsPerFrame
      split <;> decide
    · intro i hi
      show TaintRun.AB.mem ⟨x.ram.get! i, (knOf K).get! i⟩ (m.ram.get! i)
      have h5 := s3 i (List.mem_range.2 hi)
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h5
      rcases h5 with h5 | ⟨h5, h6⟩
      · apply TaintRun.bt_ext
        intro j hj
        simp [h5, TaintRun.bt_zero hj]
      · rw [h.bytes i (by simpa using h6)]
        exact rfl
    · intro hd
      cases hd
    · show m.frame = m.frame + 0
      rfl
    · intro hr
      cases hr
  have hg2 : (⟨0, 1⟩ : TaintRun.AB).mem (m.ram.get! gps) := by
    show m.ram.get! gps &&& 1 = 0 &&& 1
    rw [h.notPaused]
    rfl
  by_cases hd : m.fdot = 0
  · exact ⟨_, List.mem_cons_self, sim_refine (key true ⟨fun _ => hd, fun _ => rfl⟩) hg2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), sim_refine (key false ⟨fun h0 => (by cases h0), fun h0 => absurd h0 hd⟩) hg2⟩

/-- the same state in an environment with other bytes `D`, when the state does not use them -/
theorem sim_D {S : AS} {m : Machine} {D : List Nat} (hs : Sim E F S m) (hd : S.dg = false) : Sim { E with D := D } F S m :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, hs.pad, hs.padShift, hs.strobe, hs.halted, hs.trk, hs.size, hs.ram,
    (fun h => by rw [hd] at h; cases h), hs.szR, hs.szK, hs.fr, hs.rkv⟩

end

/-! ## The two cases of the sound's pause flag

If the flag is not 0, the sound routines do not run. The clear of RAM does not touch the flag. -/

def flagZero (pm : Nat) (l : List AS) : List AS := l.map (·.setK pm (TaintRun.AB.known 0))
def flagNotZero (l : List AS) : List AS := l.map fun S => { S with dg := true }

/-! ## The frames of the pipe, and how their last frame meets the exit -/

/-- `B` with these bytes known -/
def refine (qs : List (Nat × UInt8)) (B : AS) : AS := qs.foldl (fun A q => A.setK q.1 (TaintRun.AB.known q.2)) B

/-- the machine has these bytes -/
def Quiet (qs : List (Nat × UInt8)) (m : Machine) : Prop := ∀ q ∈ qs, m.ram.get! q.1 = q.2

/-- at the frame's end, with the counter at 1 before it: the counter has not moved, or this is the exit: with the bytes `qs`, the state is in `base` -/
def finX (ones base : List AS) (qs : List (Nat × UInt8)) (xb : List (Nat × UInt8)) (B : AS) : Bool :=
  !B.rk && (ones.any (fun S => ({ B with k := 0 } : AS).le S) ||
    (xb.all (knownIs B) && base.any fun D => (refine qs ({ B with k := 0 } : AS)).le D))

/-- what the check of the pipe's frames says. The frame of the exit reads more bytes in pieces (`l`), and keeps them apart (`keepO`). -/
structure DuringOK (E : Env) (l : List (Nat × UInt8)) (sy : Syms) (keep keepO : List Nat) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Prop where
  ti : E.rkI < 2048
  rkStarts : ∀ S ∈ starts, S.k = 0 ∧ S.rk = true ∧ S.spent = false
  tr : (cfgR E sy keep starts).t.all (walkF (cfgR E sy keep starts) (finRk starts) TaintRun.walkFuel) = true
  sr : ∀ S ∈ starts, walkF (cfgR E sy keep starts) (finRk starts) TaintRun.walkFuel S = true
  to : (cfgO { E with splits := l } sy keepO starts).t.all (walkF (cfgO { E with splits := l } sy keepO starts) (finX (starts.map (toOne E)) base qs xb) TaintRun.walkFuel) = true
  so : ∀ S ∈ starts, walkF (cfgO { E with splits := l } sy keepO starts) (finX (starts.map (toOne E)) base qs xb) TaintRun.walkFuel (toOne E S) = true

def duringCheck (E : Env) (l : List (Nat × UInt8)) (sy : Syms) (keep keepO : List Nat) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Bool :=
  let ones := starts.map (toOne E)
  let Cr := cfgR E sy keep starts
  let Co := cfgO { E with splits := l } sy keepO starts
  let fr := finRk starts
  let fo := finX ones base qs xb
  decide (E.rkI < 2048) && starts.all (fun S => S.k == 0 && S.rk && !S.spent) &&
    Cr.t.all (walkF Cr fr TaintRun.walkFuel) && starts.all (walkF Cr fr TaintRun.walkFuel) &&
    Co.t.all (walkF Co fo TaintRun.walkFuel) && starts.all (fun S => walkF Co fo TaintRun.walkFuel (toOne E S))

theorem duringOK_of_check {E : Env} {l : List (Nat × UInt8)} {sy : Syms} {keep keepO : List Nat} {starts base : List AS} {qs xb : List (Nat × UInt8)} (h : duringCheck E l sy keep keepO starts base qs xb = true) :
    DuringOK E l sy keep keepO starts base qs xb := by
  simp only [duringCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, fun S hS => ?_, h4, h5, h6, h7⟩
  have := h2 S hS
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- the environments differ in what the proof does not read -/
theorem sim_splits {E : Env} {l : List (Nat × UInt8)} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim { E with splits := l } F S m) : Sim E F S m :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, hs.pad, hs.padShift, hs.strobe, hs.halted, hs.trk, hs.size, hs.ram, hs.dg, hs.szR, hs.szK, hs.fr, hs.rkv⟩

theorem sim_splits' {E : Env} {l : List (Nat × UInt8)} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) : Sim { E with splits := l } F S m :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, hs.pad, hs.padShift, hs.strobe, hs.halted, hs.trk, hs.size, hs.ram, hs.dg, hs.szR, hs.szK, hs.fr, hs.rkv⟩

section
variable {E : Env} {F : Nat × UInt8} {sy : Syms} {keep keepO : List Nat} {l : List (Nat × UInt8)} {starts base : List AS} {qs xb : List (Nat × UInt8)}

theorem sim_refines {m : Machine} (hq : Quiet qs m) : ∀ {A : AS}, Sim E F A m → Sim E F (refine qs A) m := by
  induction qs with
  | nil =>
    intro A hs
    exact hs
  | cons q t ih =>
    intro A hs
    have h1 := hq q List.mem_cons_self
    have h2 := sim_refine hs (v := TaintRun.AB.known q.2) (by rw [h1]; exact TaintRun.mem_known_self _)
    exact ih (fun p hp => hq p (List.mem_cons_of_mem _ hp)) h2

/-- **One frame of the pipe, for any input.** Like `SideChangeBound.inv_step`, and when the frame leaves the pipe, the state with the bytes `qs` is in `base`. -/
theorem during_step (hc : DuringOK E l sy keep keepO starts base qs xb) (hp : E.pad = TaintRun.AB.top) {m : Machine} (h : InvAt E starts m) (i : UInt8) :
    InvAt E starts (frame m i) ∨ (tm E m = 1 ∧ ExitAt xb (frame m i) ∧ (Quiet qs (frame m i) → ∃ D ∈ base, Sim E ((frame m i).frame, 2) D (frame m i))) := by
  obtain ⟨S, hS, (⟨h2, hs⟩ | ⟨h1, hs⟩)⟩ := h
  · obtain ⟨k0, _, _⟩ := hc.rkStarts S hS
    obtain ⟨g1, B, g2, g3, g4⟩ := frame_of_walk (C := cfgR E sy keep starts) (F := (m.frame, tm E m)) hc.tr rfl h2 hp (hc.sr S hS) hs i
    simp only [finRk, Bool.and_eq_true, List.any_eq_true] at g2
    obtain ⟨hr, S', hS', hle⟩ := g2
    have hv : (frame m i).ram.get! E.rkI = if B.spent then tm E m - 1 else tm E m := g4.rkv hr
    have hbase : Sim E ((frame m i).frame, tm E (frame m i)) ({ B with k := 0, spent := false } : AS) (frame m i) := by
      refine { g4 with fr := ?_, rkv := ?_ }
      · show (frame m i).frame = (frame m i).frame + 0
        rfl
      · intro _
        rfl
    have hs' := sim_le hle hbase
    have hle2 : (tm E m).toNat ≤ (tm E (frame m i)).toNat + 1 := by
      show (tm E m).toNat ≤ ((frame m i).ram.get! E.rkI).toNat + 1
      rw [hv]
      split
      · rw [u8_sub_one h2]
        omega
      · omega
    left
    refine ⟨S', hS', ?_⟩
    have hge : 1 ≤ (tm E (frame m i)).toNat := by omega
    by_cases h3 : 2 ≤ (tm E (frame m i)).toNat
    · exact Or.inl ⟨h3, hs'⟩
    · have he : tm E (frame m i) = 1 := by
        apply UInt8.toNat_inj.1
        have : (1 : UInt8).toNat = 1 := rfl
        omega
      exact Or.inr ⟨he, sim_toOne hc.ti hs' he _ rfl⟩
  · obtain ⟨g1, B, g2, g3, g5⟩ := frame_of_walk (C := cfgO { E with splits := l } sy keepO starts) (F := (m.frame, 2)) hc.to rfl (Nat.le_refl _) hp (hc.so S hS) (sim_splits' hs) i
    have g4 : Sim E (m.frame, 2) B (frame m i) := sim_splits g5
    simp only [finX, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at g2
    obtain ⟨hr, (⟨S', hS', hle⟩ | ⟨hx, D, hD, hle⟩)⟩ := g2
    · obtain ⟨S2, hS2, rfl⟩ := List.mem_map.1 hS'
      have hbase : Sim E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
        refine { g4 with fr := ?_, rkv := ?_ }
        · show (frame m i).frame = (frame m i).frame + 0
          rfl
        · intro hr2
          have : B.rk = true := hr2
          rw [hr] at this
          cases this
      have hs' := sim_le hle hbase
      have he := one_of_sim hc.ti hs'
      left
      exact ⟨S2, hS2, Or.inr ⟨he, hs'⟩⟩
    · right
      refine ⟨h1, fun p hq => sim_known g4 (hx p hq), fun hq => ⟨D, hD, ?_⟩⟩
      have hbase : Sim E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
        refine { g4 with fr := ?_, rkv := ?_ }
        · show (frame m i).frame = (frame m i).frame + 0
          rfl
        · intro hr2
          have : B.rk = true := hr2
          rw [hr] at this
          cases this
      exact sim_le hle (sim_refines hq hbase)

end

/-! ## The statement for the side pipe -/

section
open PipeChangeBound (leftOf)

/-- the bytes that the state at the entry knows, besides those of `SideChangeBound`. Nothing in the pipe's frames writes them; the frames after the pipe read them. -/
def extraNames : List (String × Nat × Nat) :=
  [("AreaPointer", 0, 1), ("EntrancePage", 0, 1), ("CurrentPlayer", 0, 1), ("JoypadOverride", 0, 1), ("GameTimerExpiredFlag", 0, 1), ("AreaNumber", 0, 1), ("PrimaryHardMode", 0, 1), ("NoteLengthTblAdder", 0, 1)]

/-- the bytes that the state at the exit knows. The values come from the reference machine when the timer has run out. -/
def exitNames : List (String × Nat × Nat) :=
  [("OperMode", 0, 1), ("OperMode_Task", 0, 1), ("GameEngineSubroutine", 0, 1), ("ScreenRoutineTask", 0, 1), ("DisableScreenFlag", 0, 1), ("WorldNumber", 0, 1), ("AreaNumber", 0, 1), ("AreaPointer", 0, 1),
   ("EntrancePage", 0, 1), ("AltEntranceControl", 0, 1), ("CurrentPlayer", 0, 1), ("JoypadOverride", 0, 1), ("GameTimerExpiredFlag", 0, 1), ("PrimaryHardMode", 0, 1), ("Sprite0HitDetectFlag", 0, 1),
   ("VRAM_Buffer1", 0, 1), ("VRAM_Buffer_AddrCtrl", 0, 1), ("NoiseSoundBuffer", 0, 1), ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1), ("MusicData", 0, 2), ("MusicOffset_Square1", 0, 1),
   ("NoteLengthTblAdder", 0, 1), ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1)]

/-- the bytes of the sound's pause: at the exit they have the reference machine's values -/
def quietNames : List (String × Nat × Nat) := [("PauseSoundBuffer", 0, 1), ("PauseSoundQueue", 0, 1)]

/-- the names this file needs -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  let l := ((extraNames ++ exitNames ++ quietNames).map (·.1)) ++ ["GamePauseStatus", "PauseModeFlag", "VRAM_Buffer1_Offset", "ScreenRoutineTask", "DisableScreenFlag", "GameTimerDisplay", "FetchNewGameTimerFlag"]
  SideChangeBound.namesOf text ++ (l.eraseDups.filterMap fun n => (PipeTransitionAll.asmValue ls n).map (n, ·))

/-- a name as a RAM index -/
def adI (nm : Names) (n : String) : Nat := ((nm.ad n) &&& 0x7FF).toNat

/-- the bytes the exit's frame reads in pieces: the pause byte too -/
def exitSplits (nm nx : Names) (e : Machine) : List (Nat × UInt8) := (sideEnv nm e).splits ++ [(adI nx "GamePauseStatus", 1)]

/-- the environment of the rows: `dg` says that the sound's pause flag is not 0 -/
def rowsEnv (nm nx : Names) (e : Machine) : Env := { sideEnv nm e with splits := exitSplits nm nx e, D := [adI nx "PauseModeFlag"] }

/-- the reference machines, with the bytes `extraNames` known too -/
def refs2 (nm nx : Names) (e : Machine) : List (Machine × List Nat) :=
  (refsOf nm e).map fun v => (v.1, v.2 ++ bytesOf nx extraNames)

/-- **The condition on the entry here.** `SideChangeBound.Entry` with the bytes `extraNames`. -/
abbrev Entry2 (nm nx : Names) (e : Machine) (A : Nat) (m : Machine) : Prop := EntryCond (sideEnv nm e) (refs2 nm nx e) A m

/-- the state during the pipe, with these bytes -/
abbrev During2 (nm nx : Names) (e : Machine) : Machine → Prop := InvAt (sideEnv nm e) (startsOf (refs2 nm nx e))

/-- the bytes of the condition at the exit -/
def exitKnown (nx : Names) : List Nat := bytesOf nx exitNames ++ bytesOf nx quietNames

/-- the reference machine at the exit -/
abbrev refExit (e : Machine) (A : Nat) : Machine := run e (zeros A)

/-- **The condition on the state at the exit.** -/
abbrev Exit2 (nm nx : Names) (e : Machine) (A : Nat) (m : Machine) : Prop :=
  ExitCond (rowsEnv nm nx e) (refExit e A) (exitKnown nx) (adI nx "GamePauseStatus") m

/-- the start states of the rows -/
def endBase (nx : Names) (e : Machine) (A : Nat) : List AS :=
  exitStarts (refExit e A) (exitKnown nx) (adI nx "GamePauseStatus")

/-- the sound's pause bytes with the values of the reference machine -/
def quietBytes (nx : Names) (e : Machine) (A : Nat) : List (Nat × UInt8) :=
  (bytesOf nx quietNames).map fun i => (i, (refExit e A).ram.get! i)

/-- what the rows have in common -/
def rowCtx (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) : Ctx :=
  { E := rowsEnv nm nx e, sy, nm, eng := sy.EngSidePipe, tbl := tableFrom sy nm B (refExit e A), B, keep := [adI nx "VRAM_Buffer1_Offset"] }

/-- the search keeps these bytes apart on the frame of the exit -/
def keep2 (nm nx : Names) : List Nat := keepOf nm ++ [adI nx "GamePauseStatus"]

/-- the rows of the two cases of the flag -/
def rows0 (c : Ctx) (nx : Names) (e : Machine) (A B : Nat) : List Row := rowsFrom c B (flagZero (adI nx "PauseModeFlag") (endBase nx e A))
def rows1 (c : Ctx) (nx : Names) (e : Machine) (A B : Nat) : List Row := rowsFrom c B (flagNotZero (endBase nx e A))

/-! ## The time at the exit

The last row of `rows0` and of `rows1` holds the states with control and the states where the time is up, because the game timer's digits are free.
If at the exit the sound's pause flag is 0 and the game timer is not 000, the machine is in the rows `timeRows`, whose last row has only states with control.
There `dg` says that the timer is not 000. The entrance's setup may load the timer from the level's header, on the flag `FetchNewGameTimerFlag`: the search keeps
this flag apart, and the frame's ends keep `dg` apart. -/

/-- the game timer's three digits, as RAM indices -/
def digitsOf (nx : Names) : List Nat := bytesOf nx [("GameTimerDisplay", 0, 3)]

/-- **The time at the exit.** The sound's pause flag is 0, and the game timer is not 000. -/
structure TimeOK (nx : Names) (m : Machine) : Prop where
  flag : m.ram.get! (adI nx "PauseModeFlag") = 0
  timer : ∃ i ∈ digitsOf nx, m.ram.get! i ≠ 0

/-- the value that the game timer's three digits show -/
def timerVal (nx : Names) (m : Machine) : Nat := (digitsOf nx).foldl (fun a i => 10 * a + (m.ram.get! i).toNat) 0

theorem fold_digit (m : Machine) : ∀ (l : List Nat) (a : Nat), l.foldl (fun a i => 10 * a + (m.ram.get! i).toNat) a ≠ 0 → a ≠ 0 ∨ ∃ i ∈ l, m.ram.get! i ≠ 0
  | [], a, h => Or.inl h
  | x :: l, a, h => by
    rcases fold_digit m l (10 * a + (m.ram.get! x).toNat) h with h1 | ⟨i, hi, h2⟩
    · by_cases hx : (m.ram.get! x).toNat = 0
      · left
        omega
      · right
        refine ⟨x, List.mem_cons_self, fun h0 => hx ?_⟩
        rw [h0]
        rfl
    · exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, h2⟩

/-- a timer that does not show 0 has a digit that is not 0 -/
theorem digit_of_timerVal {nx : Names} {m : Machine} (h : timerVal nx m ≠ 0) : ∃ i ∈ digitsOf nx, m.ram.get! i ≠ 0 := by
  rcases fold_digit m (digitsOf nx) 0 h with h1 | h1
  · exact absurd rfl h1
  · exact h1

/-- **The time at the exit from its two parts**: the sound's pause flag, and a timer that does not show 0 -/
theorem timeOK_of {nx : Names} {m : Machine} (hf : m.ram.get! (adI nx "PauseModeFlag") = 0) (ht : timerVal nx m ≠ 0) : TimeOK nx m :=
  ⟨hf, digit_of_timerVal ht⟩

/-- the environment of these rows: `dg` says that the timer is not 000 -/
def timeEnv (nm nx : Names) (e : Machine) : Env := { rowsEnv nm nx e with D := digitsOf nx }

/-- what these rows have in common -/
def timeCtx (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) : Ctx :=
  { rowCtx sy nm nx e A B with E := timeEnv nm nx e, keep := (rowCtx sy nm nx e A B).keep ++ [adI nx "FetchNewGameTimerFlag"] }

/-- the start states: those of `rows0`, with `dg` -/
def timeBase (nx : Names) (e : Machine) (A : Nat) : List AS :=
  (flagZero (adI nx "PauseModeFlag") (endBase nx e A)).map fun S => { S with dg := true }

/-- the rows of the time -/
def timeRows (c : Ctx) (nx : Names) (e : Machine) (A B : Nat) : List Row := rowsFromD c B (timeBase nx e A)

/-- a machine is in the rows of the time -/
def InRowsT (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (m : Machine) : Prop :=
  InvL (timeCtx sy nm nx e A B) (timeRows (timeCtx sy nm nx e A B) nx e A B) m

/-- the check of the rows of the time, and of `left` during the pipe -/
def timeCheck (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) : Bool :=
  let c := timeCtx sy nm nx e A B
  let l := timeRows c nx e A B
  decide (0 < B) && leftCheck (sideEnv nm e) sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B (startsOf (refsOf nm e)) (refExit e A) &&
    chainOKD c l && zeroCtl sy l

/-! ## Frames that end paused

A frame that ends paused skips the timers and the mode's routine. In the pipe's frames it does not move the counter: in a walk that reads the pause bit in pieces and keeps
the pause byte apart, a frame whose counter falls ends knowing that the bit is 0 (`finRkP`). In the rows every state knows that the bit is 0. -/

/-- **The frame ends paused**: the low bit of `GamePauseStatus` is 1 -/
def Paused (nx : Names) (m : Machine) : Prop := m.ram.get! (adI nx "GamePauseStatus") &&& 1 = 1

/-- the state knows that the low bit of the byte `g` is 0 -/
def notPausedK (g : Nat) (B : AS) : Bool := decide (g < 2048) && (B.getK g).k &&& 1 == 1 && (B.getK g).v &&& 1 == 0

theorem not_paused_of {E : Env} {F : Nat × UInt8} {g : Nat} {B : AS} {m : Machine} (hs : Sim E F B m) (h : notPausedK g B = true) : m.ram.get! g &&& 1 ≠ 1 := by
  simp only [notPausedK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hg, hk⟩, hv⟩ := h
  have e := TaintRun.bit_eq (hs.ram g hg) hk
  rw [e, hv]
  decide

/-- the environment of the pipe's frames, with the pause bit read in pieces -/
def pauseEnv (nm nx : Names) (e : Machine) : Env := { sideEnv nm e with splits := (sideEnv nm e).splits ++ [(adI nx "GamePauseStatus", 1)] }

/-- at the frame's end, with the counter followed: a start state; if the counter has fallen, the state knows that the game is not paused -/
def finRkP (g : Nat) (starts : List AS) (B : AS) : Bool := finRk starts B && (!B.spent || notPausedK g B)

/-- the table of the pipe's frames with the counter followed, the pause byte kept apart -/
def cfgP (sy : Syms) (nm nx : Names) (e : Machine) : Cfg := cfgR (pauseEnv nm nx e) sy (keepOf nm ++ [adI nx "GamePauseStatus"]) (startsOf (refs2 nm nx e))

/-- the check of the paused frames of the pipe -/
def pauseCheck (sy : Syms) (nm nx : Names) (e : Machine) : Bool :=
  let C := cfgP sy nm nx e
  let fin := finRkP (adI nx "GamePauseStatus") (startsOf (refs2 nm nx e))
  C.t.all (walkF C fin TaintRun.walkFuel) && (startsOf (refs2 nm nx e)).all (walkF C fin TaintRun.walkFuel)

/-- every state of the rows knows that the game is not paused -/
def notPausedRows (g : Nat) (l : List Row) : Bool := l.all fun r => r.R.all (notPausedK g)

theorem not_paused_rows {c : Ctx} {g : Nat} {l : List Row} (h : notPausedRows g l = true) {m : Machine} (hm : InvL c l m) : m.ram.get! g &&& 1 ≠ 1 := by
  obtain ⟨r, hr, S, hS, hs⟩ := covered_of_invL hm
  simp only [notPausedRows, List.all_eq_true] at h
  exact not_paused_of hs (h r hr S hS)

/-- **A paused frame of the pipe keeps the counter.** -/
theorem pause_keeps {sy : Syms} {nm nx : Names} {e : Machine} (hP : pauseCheck sy nm nx e = true) {m : Machine} (h : During2 nm nx e m) (i : UInt8)
    (hp : Paused nx (frame m i)) (h' : During2 nm nx e (frame m i)) : (tm (sideEnv nm e) m).toNat ≤ (tm (sideEnv nm e) (frame m i)).toNat := by
  simp only [pauseCheck, Bool.and_eq_true, List.all_eq_true] at hP
  obtain ⟨ht, hs0⟩ := hP
  obtain ⟨S, hS, (⟨h2, hs⟩ | ⟨h1, _⟩)⟩ := h
  · have hs' : Sim (pauseEnv nm nx e) (m.frame, tm (sideEnv nm e) m) S m := sim_splits' hs
    obtain ⟨_, B, g2, _, g4⟩ := frame_of_walk (C := cfgP sy nm nx e) (F := (m.frame, tm (sideEnv nm e) m)) ht rfl h2 rfl (hs0 S hS) hs' i
    simp only [finRkP, finRk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at g2
    obtain ⟨⟨hrk, _⟩, hsp⟩ := g2
    have hns : B.spent = false := by
      rcases hsp with hsp | hsp
      · exact hsp
      · exact absurd hp (not_paused_of g4 hsp)
    have hv : (frame m i).ram.get! (pauseEnv nm nx e).rkI = if B.spent then tm (sideEnv nm e) m - 1 else tm (sideEnv nm e) m := g4.rkv hrk
    rw [hns] at hv
    show (tm (sideEnv nm e) m).toNat ≤ ((frame m i).ram.get! (sideEnv nm e).rkI).toNat
    have e1 : (frame m i).ram.get! (sideEnv nm e).rkI = tm (sideEnv nm e) m := hv
    rw [e1]
    exact Nat.le_refl _
  · obtain ⟨S', _, (⟨g2, _⟩ | ⟨g1, _⟩)⟩ := h'
    · rw [h1]
      have : (1 : UInt8).toNat = 1 := rfl
      omega
    · rw [h1, g1]
      exact Nat.le_refl _

/-- a state of the pipe's frames here is one of `SideChangeBound` -/
def duringLe (nm nx : Names) (e : Machine) : Bool :=
  (startsOf (refs2 nm nx e)).all fun S2 => (startsOf (refsOf nm e)).any fun S =>
    S2.le S && (toOne (sideEnv nm e) S2).le (toOne (sideEnv nm e) S)

/-- the whole check on the ROM -/
def endCheck (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) : Bool :=
  let c := rowCtx sy nm nx e A B
  let base := endBase nx e A
  let r0 := rows0 c nx e A B
  let r1 := rows1 c nx e A B
  startsOK (refs2 nm nx e) && duringLe nm nx e && exitStartsOK (refExit e A) (exitKnown nx) &&
    base.all (fun S => !S.dg && keyKnown c S && !PipeChangeBound.inPipe c.sy c.eng (mOf S) && c.left (mOf S) == B) && decide (2 ≤ A) &&
    duringCheck (sideEnv nm e) (exitSplits nm nx e) sy (keepOf nm) (keep2 nm nx) (startsOf (refs2 nm nx e)) base (quietBytes nx e A) (exitBytes sy nm (refExit e A)) &&
    chainOK c r0 && chainOK c r1 && timeCheck sy nm nx e A B &&
    pauseCheck sy nm nx e && notPausedRows (adI nx "GamePauseStatus") r0 && notPausedRows (adI nx "GamePauseStatus") r1

/-- a machine is in the rows of one of the two cases -/
def InRows (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (m : Machine) : Prop :=
  InvL (rowCtx sy nm nx e A B) (rows0 (rowCtx sy nm nx e A B) nx e A B) m ∨ InvL (rowCtx sy nm nx e A B) (rows1 (rowCtx sy nm nx e A B) nx e A B) m

/-- **The statement.** -/
structure EndStatement (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) : Prop where
  /-- the condition here gives the condition of `SideChangeBound` -/
  entry : ∀ M, Entry2 nm nx e A M → Entry nm e A M
  /-- an entry is in the state during the pipe -/
  during : ∀ M, Entry2 nm nx e A M → During2 nm nx e M
  /-- this state is the state during the pipe of `SideChangeBound` -/
  toDuring : ∀ m, During2 nm nx e m → During nm e m
  /-- one frame of the pipe, for any input. A frame that leaves the pipe has the exit's bytes. If the sound's pause bytes have the reference's values, the machine is in the rows. -/
  step : ∀ m, During2 nm nx e m → ∀ i, During2 nm nx e (frame m i) ∨
    (ExitAt (exitBytes sy nm (refExit e A)) (frame m i) ∧ (Quiet (quietBytes nx e A) (frame m i) → InRows sy nm nx e A B (frame m i)))
  /-- a state with the condition at the exit is in the rows -/
  atExit : ∀ m, Exit2 nm nx e A m → InRows sy nm nx e A B m
  /-- `left` at the exit -/
  leftExit : ∀ m, Exit2 nm nx e A m → leftAt sy nm e A B m = B
  /-- a frame in the rows: `left` is 0 already, or the machine stays in the rows and `left` falls by at most one -/
  rows : ∀ m, InRows sy nm nx e A B m → ∀ i, (coreFrame sy sy.EngSidePipe m = true → noStart i = true) →
    leftAt sy nm e A B m = 0 ∨ (InRows sy nm nx e A B (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i) + 1)
  /-- `left` is not 0 during the pipe -/
  duringLeft : ∀ m, During2 nm nx e m → leftAt sy nm e A B m ≠ 0
  /-- one frame of the pipe: a frame that leaves the pipe, with the sound's pause bytes and the time at the exit, is in the rows of the time -/
  stepT : ∀ m, During2 nm nx e m → ∀ i, During2 nm nx e (frame m i) ∨
    (ExitAt (exitBytes sy nm (refExit e A)) (frame m i) ∧ (Quiet (quietBytes nx e A) (frame m i) → TimeOK nx (frame m i) → InRowsT sy nm nx e A B (frame m i)))
  /-- a frame in the rows of the time: `left` is 0 already, or the machine stays in these rows -/
  rowsT : ∀ m, InRowsT sy nm nx e A B m → ∀ i, (coreFrame sy sy.EngSidePipe m = true → noStart i = true) →
    leftAt sy nm e A B m = 0 ∨ InRowsT sy nm nx e A B (frame m i)
  /-- in the rows of the time, `left` is 0 only with control -/
  zeroT : ∀ m, InRowsT sy nm nx e A B m → leftAt sy nm e A B m = 0 → controllable sy m = true
  /-- a frame of the pipe that ends paused takes nothing off `left` -/
  pauseKeeps : ∀ m, During2 nm nx e m → ∀ i, Paused nx (frame m i) → During2 nm nx e (frame m i) → leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i)
  /-- no machine of the rows is paused -/
  rowsNotPaused : ∀ m, InRows sy nm nx e A B m → ¬ Paused nx m

theorem during_le {nm nx : Names} {e : Machine} (h : duringLe nm nx e = true) {m : Machine} (hm : During2 nm nx e m) : During nm e m := by
  obtain ⟨S2, hS2, hc⟩ := hm
  simp only [duringLe, List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨S, hS, h1, h2⟩ := h S2 hS2
  rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · exact ⟨S, hS, Or.inl ⟨c1, sim_le h1 c2⟩⟩
  · exact ⟨S, hS, Or.inr ⟨c1, sim_le h2 c2⟩⟩

/-- the rows from a machine of the start states -/
theorem in_rows {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} {m : Machine}
    (h : ∃ D ∈ endBase nx e A, Sim (rowsEnv nm nx e) (m.frame, 2) D m) : InRows sy nm nx e A B m := by
  obtain ⟨D, hD, hs⟩ := h
  by_cases h0 : m.ram.get! (adI nx "PauseModeFlag") = 0
  · left
    refine inv_head B _ ⟨_, List.mem_map.2 ⟨D, hD, rfl⟩, sim_refine hs ?_⟩
    rw [h0]
    exact TaintRun.mem_known_self _
  · right
    refine inv_head B _ ⟨_, List.mem_map.2 ⟨D, hD, rfl⟩, { hs with dg := fun _ => ?_ }⟩
    show ([adI nx "PauseModeFlag"].any fun i => m.ram.get! i != 0) = true
    simp [h0]

theorem timeCheck_parts {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} (h : timeCheck sy nm nx e A B = true) :
    0 < B ∧ LeftOK (sideEnv nm e) sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B (startsOf (refsOf nm e)) (refExit e A) ∧
    chainOKD (timeCtx sy nm nx e A B) (timeRows (timeCtx sy nm nx e A B) nx e A B) = true ∧ zeroCtl sy (timeRows (timeCtx sy nm nx e A B) nx e A B) = true := by
  simp only [timeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, leftOK_of_check h2, h3, h4⟩

theorem endStatement_of_check {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} (h : endCheck sy nm nx e A B = true) : EndStatement sy nm nx e A B := by
  simp only [endCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  obtain ⟨hB, hL, hTc, hTz⟩ := timeCheck_parts h10
  have hE4 : (timeCtx sy nm nx e A B).E.pad = TaintRun.AB.top := rfl
  have hD := duringOK_of_check h7
  have hE2 : (sideEnv nm e).pad = TaintRun.AB.top := rfl
  have hE3 : (rowCtx sy nm nx e A B).E.pad = TaintRun.AB.top := rfl
  have hent : ∀ M, Entry2 nm nx e A M → Entry nm e A M := by
    intro M hM
    refine ⟨hM.dot, hM.flags, hM.s0, hM.ctrl, hM.strobe, hM.halted, hM.trk, hM.prg, hM.mask, hM.size, ?_, hM.timer⟩
    obtain ⟨v, hv, a1, a2, a3⟩ := hM.ref
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.1 hv
    exact ⟨v0, hv0, a1, a2, fun i hi => a3 i (List.mem_append_left _ hi)⟩
  refine ⟨hent, fun M hM => inv_of_entry h1 hE2 h6 hM, fun m hm => during_le h2 hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm i
    rcases during_step hD hE2 hm i with g | ⟨_, g1, g2⟩
    · exact Or.inl g
    · refine Or.inr ⟨g1, fun hq => ?_⟩
      obtain ⟨D, hD1, hs⟩ := g2 hq
      have hs2 : Sim (rowsEnv nm nx e) ((frame m i).frame, 2) D (frame m i) := sim_splits' (l := exitSplits nm nx e) (sim_D (D := [adI nx "PauseModeFlag"]) hs (h5 D hD1).1.1.1)
      exact in_rows ⟨D, hD1, hs2⟩
  · intro m hm
    exact in_rows (exit_cover h3 rfl hm)
  · intro m hm
    obtain ⟨D, hD1, hs⟩ := exit_cover h3 rfl hm
    obtain ⟨⟨⟨_, a2⟩, a3⟩, a4⟩ := h5 D hD1
    have : (rowCtx sy nm nx e A B).left m = B := by
      rw [left_of_known hs a2 a3, a4]
    exact this
  · intro m hm i hi
    rcases hm with hm | hm
    · rcases chain_step hE3 _ h8 hm hi with g | ⟨g1, g2⟩
      · exact Or.inl g
      · exact Or.inr ⟨Or.inl g1, g2⟩
    · rcases chain_step hE3 _ h9 hm hi with g | ⟨g1, g2⟩
      · exact Or.inl g
      · exact Or.inr ⟨Or.inr g1, g2⟩
  · intro m hm
    have h0 := left_of_inv hL (during_le h2 hm)
    show leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B m ≠ 0
    rw [h0]
    omega
  · intro m hm i
    rcases during_step hD hE2 hm i with g | ⟨_, g1, g2⟩
    · exact Or.inl g
    · refine Or.inr ⟨g1, fun hq ht => ?_⟩
      obtain ⟨D, hD1, hs⟩ := g2 hq
      have hs2 : Sim (timeEnv nm nx e) ((frame m i).frame, 2) D (frame m i) :=
        sim_splits' (l := exitSplits nm nx e) (sim_D (D := digitsOf nx) hs (h5 D hD1).1.1.1)
      have hs3 := sim_refine hs2 (i := adI nx "PauseModeFlag") (v := TaintRun.AB.known 0) (by rw [ht.flag]; exact TaintRun.mem_known_self _)
      have hdg : (timeEnv nm nx e).D.any (fun j => (frame m i).ram.get! j != 0) = true := by
        obtain ⟨j, hj, hne⟩ := ht.timer
        exact List.any_eq_true.2 ⟨j, hj, by simpa using hne⟩
      have hs4 : Sim (timeEnv nm nx e) ((frame m i).frame, 2) ({ D.setK (adI nx "PauseModeFlag") (TaintRun.AB.known 0) with dg := true } : AS) (frame m i) :=
        { hs3 with dg := fun _ => hdg }
      exact inv_headD B _ ⟨_, List.mem_map.2 ⟨_, List.mem_map.2 ⟨D, hD1, rfl⟩, rfl⟩, hs4⟩
  · intro m hm i hi
    rcases chain_stepD hE4 _ hTc hm hi with g | ⟨g1, _⟩
    · exact Or.inl g
    · exact Or.inr g1
  · intro m hm h0
    exact ctl_of_zero (states_of_chainD _ hTc) hTz hm h0
  · intro m hm i hp hm'
    have e1 := left_of_inv hL (during_le h2 hm)
    have e2 := left_of_inv hL (during_le h2 hm')
    show leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B m ≤ leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (refExit e A)) B (frame m i)
    rw [e1, e2]
    have := pause_keeps h11 hm i hp hm'
    omega
  · intro m hm hp
    rcases hm with hm | hm
    · exact not_paused_rows h12 hm hp
    · exact not_paused_rows h13 hm hp

end

/-! ## A run -/

section
open PipeChangeBound (leftOf)
open PipeTransitionAll (Names)

/-- **The change of a run, without `fallAfter`.** The fields of `SideChangeBound.ChangeRun`, with the entry's condition here, no Start on the frames of the game core after the pipe, and the sound's pause bytes at the exit. -/
structure EndRun (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) where
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
  /-- control at `b` -/
  atCtl : controllable sy (seq b) = true
  /-- a lag frame ends paused -/
  lagPaused : ∀ n, a ≤ n → n < b → lag n → Paused nx (seq (n + 1))
  /-- no Start on the frames of the game core after the pipe -/
  noStart : ∀ n, a ≤ n → n < b → coreFrame sy sy.EngSidePipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- at the exit, the sound's pause bytes have the reference's values -/
  quiet : ∀ n, a ≤ n → n ≤ b → ExitAt (exitBytes sy nm (refExit e A)) (seq n) → Quiet (quietBytes nx e A) (seq n)

variable {sy : Syms} {nm nx : Names} {e : Machine} {A B : Nat} {es : List Machine}

/-- during the pipe or in the rows -/
def St (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (m : Machine) : Prop := During2 nm nx e m ∨ InRows sy nm nx e A B m

/-- one frame -/
theorem st_step (S : Statement sy nm e es A B) (T : EndStatement sy nm nx e A B) {m : Machine} {i : UInt8} (h : St sy nm nx e A B m)
    (hi : coreFrame sy sy.EngSidePipe m = true → noStart i = true)
    (hq : ExitAt (exitBytes sy nm (refExit e A)) (frame m i) → Quiet (quietBytes nx e A) (frame m i)) :
    leftAt sy nm e A B m = 0 ∨ (St sy nm nx e A B (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i) + 1) := by
  rcases h with h | h
  · right
    refine ⟨?_, S.fall _ (T.toDuring _ h) _⟩
    rcases T.step m h i with g | ⟨g1, g2⟩
    · exact Or.inl g
    · exact Or.inr (g2 (hq g1))
  · rcases T.rows m h i hi with g | ⟨g1, g2⟩
    · exact Or.inl g
    · exact Or.inr ⟨Or.inr g1, g2⟩

/-- one frame that ends paused: it takes nothing off `left` -/
theorem st_step_paused (T : EndStatement sy nm nx e A B) {m : Machine} {i : UInt8} (h : St sy nm nx e A B m)
    (hi : coreFrame sy sy.EngSidePipe m = true → noStart i = true)
    (hq : ExitAt (exitBytes sy nm (refExit e A)) (frame m i) → Quiet (quietBytes nx e A) (frame m i)) (hp : Paused nx (frame m i)) :
    leftAt sy nm e A B m = 0 ∨ (St sy nm nx e A B (frame m i) ∧ leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i)) := by
  rcases h with h | h
  · rcases T.step m h i with g | ⟨g1, g2⟩
    · exact Or.inr ⟨Or.inl g, T.pauseKeeps m h i hp g⟩
    · exact absurd hp (T.rowsNotPaused _ (g2 (hq g1)))
  · rcases T.rows m h i hi with g | ⟨g1, _⟩
    · exact Or.inl g
    · exact absurd hp (T.rowsNotPaused _ g1)

theorem cnt_mono (R : EndRun sy nm nx e A B) (n : Nat) : R.cnt n ≤ R.cnt (n + 1) := by
  rw [R.hcnt n]
  omega

/-- **The bound on the change.** This is `change₂` of `Route`, with `A + B = 282`. -/
theorem EndRun.bound (S : Statement sy nm e es A B) (T : EndStatement sy nm nx e A B) (R : EndRun sy nm nx e A B) : R.cnt R.a + (A + B) ≤ R.cnt R.b := by
  have key : ∀ d, R.a + d ≤ R.b → R.cnt R.a + (A + B) ≤ R.cnt (R.a + d) ∨
      (St sy nm nx e A B (R.seq (R.a + d)) ∧ R.cnt R.a + (A + B) ≤ R.cnt (R.a + d) + leftAt sy nm e A B (R.seq (R.a + d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      right
      refine ⟨Or.inl (T.during _ R.entry), ?_⟩
      have := S.atEntry _ (T.entry _ R.entry)
      simp only [Nat.add_zero]
      omega
    | succ d ih =>
      intro hd
      have e1 : R.a + (d + 1) = R.a + d + 1 := rfl
      rw [e1]
      have hn := R.next (R.a + d)
      rcases ih (by omega) with h | ⟨h1, h2⟩
      · left
        have := cnt_mono R (R.a + d)
        omega
      · have hi := R.noStart (R.a + d) (by omega) (by omega)
        have hq : ExitAt (exitBytes sy nm (refExit e A)) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) → Quiet (quietBytes nx e A) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) := by
          intro hx
          rw [← hn] at hx ⊢
          exact R.quiet _ (by omega) (by omega) hx
        have hc := R.hcnt (R.a + d)
        by_cases hl : R.lag (R.a + d)
        · rw [@if_pos _ (R.dec _) hl] at hc
          have hp := R.lagPaused (R.a + d) (by omega) (by omega) hl
          rw [hn] at hp
          rcases st_step_paused T h1 hi hq hp with g | ⟨g1, g2⟩
          · left
            omega
          · right
            rw [hn]
            exact ⟨g1, by omega⟩
        · rw [@if_neg _ (R.dec _) hl] at hc
          rcases st_step S T h1 hi hq with g | ⟨g1, g2⟩
          · left
            omega
          · right
            rw [hn]
            exact ⟨g1, by omega⟩
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  rcases key (R.b - R.a) (by omega) with h | ⟨_, h⟩
  · rw [e2] at h
    exact h
  · rw [e2, S.atControl _ R.atCtl] at h
    omega

/-- **What `fallAfter` becomes.** On a run, as long as `left` has not been 0, every frame takes at most one off `left`. -/
theorem EndRun.fall (S : Statement sy nm e es A B) (T : EndStatement sy nm nx e A B) (R : EndRun sy nm nx e A B) :
    ∀ d, R.a + d < R.b → (∀ k, k ≤ d → leftAt sy nm e A B (R.seq (R.a + k)) ≠ 0) →
      leftAt sy nm e A B (R.seq (R.a + d)) ≤ leftAt sy nm e A B (R.seq (R.a + d + 1)) + 1 := by
  have key : ∀ d, R.a + d ≤ R.b → (∀ k, k < d → leftAt sy nm e A B (R.seq (R.a + k)) ≠ 0) → St sy nm nx e A B (R.seq (R.a + d)) := by
    intro d
    induction d with
    | zero => exact fun _ _ => Or.inl (T.during _ R.entry)
    | succ d ih =>
      intro hd hk
      have e1 : R.a + (d + 1) = R.a + d + 1 := rfl
      rw [e1, R.next (R.a + d)]
      have h1 := ih (by omega) (fun k h => hk k (by omega))
      have hn := R.next (R.a + d)
      have hq : ExitAt (exitBytes sy nm (refExit e A)) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) → Quiet (quietBytes nx e A) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) := by
        intro hx
        rw [← hn] at hx ⊢
        exact R.quiet _ (by omega) (by omega) hx
      rcases st_step S T h1 (R.noStart (R.a + d) (by omega) (by omega)) hq with g | ⟨g1, _⟩
      · exact absurd g (hk d (by omega))
      · exact g1
  intro d hd hk
  have h1 := key d (by omega) (fun k h => hk k (by omega))
  have hn := R.next (R.a + d)
  have hq : ExitAt (exitBytes sy nm (refExit e A)) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) → Quiet (quietBytes nx e A) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) := by
    intro hx
    rw [← hn] at hx ⊢
    exact R.quiet _ (by omega) (by omega) hx
  rw [hn]
  rcases st_step S T h1 (R.noStart (R.a + d) (by omega) (by omega)) hq with g | ⟨_, g2⟩
  · exact absurd g (hk d (by omega))
  · exact g2

/-- **`left` is not 0 before control**, on a run of the change: if the time is not up at the exit (`TimeOK`), and `b` is the first control after the entry. -/
theorem EndRun.first (T : EndStatement sy nm nx e A B) (R : EndRun sy nm nx e A B)
    (ht : ∀ n, R.a ≤ n → n ≤ R.b → ExitAt (exitBytes sy nm (refExit e A)) (R.seq n) → TimeOK nx (R.seq n))
    (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) :
    ∀ n, R.a ≤ n → n < R.b → leftAt sy nm e A B (R.seq n) ≠ 0 := by
  have key : ∀ d, R.a + d ≤ R.b → During2 nm nx e (R.seq (R.a + d)) ∨ InRowsT sy nm nx e A B (R.seq (R.a + d)) := by
    intro d
    induction d with
    | zero => exact fun _ => Or.inl (T.during _ R.entry)
    | succ d ih =>
      intro hd
      have e1 : R.a + (d + 1) = R.a + d + 1 := rfl
      have hn := R.next (R.a + d)
      rw [e1]
      rcases ih (by omega) with h | h
      · rcases T.stepT _ h (R.inp (R.a + d)) with g | ⟨g1, g2⟩
        · rw [hn]
          exact Or.inl g
        · right
          have g1' : ExitAt (exitBytes sy nm (refExit e A)) (R.seq (R.a + d + 1)) := by
            rw [hn]
            exact g1
          have q := R.quiet _ (by omega) (by omega) g1'
          have t := ht _ (by omega) (by omega) g1'
          rw [hn] at q t ⊢
          exact g2 q t
      · rcases T.rowsT _ h (R.inp (R.a + d)) (R.noStart (R.a + d) (by omega) (by omega)) with g | g
        · have := T.zeroT _ h g
          rw [hc _ (by omega) (by omega)] at this
          cases this
        · rw [hn]
          exact Or.inr g
  intro n h1 h2 h0
  obtain ⟨d, rfl⟩ : ∃ d, n = R.a + d := ⟨n - R.a, by omega⟩
  rcases key d (by omega) with h | h
  · exact T.duringLeft _ h h0
  · have := T.zeroT _ h h0
    rw [hc _ h1 h2] at this
    cases this

/-- **No control, from a state at the exit.** From a state with the condition at the exit, with no Start on the frames of the game core, there is no control on the next `B - 1` frames. -/
theorem no_control_exit (S : Statement sy nm e es A B) (T : EndStatement sy nm nx e A B) {seq : Nat → Machine} {inp : Nat → UInt8} (hn : ∀ n, seq (n + 1) = frame (seq n) (inp n))
    (hx : Exit2 nm nx e A (seq 0)) (hi : ∀ n, coreFrame sy sy.EngSidePipe (seq n) = true → noStart (inp n) = true) :
    ∀ j, j < B → controllable sy (seq j) = false := by
  have key : ∀ d, B ≤ d + leftAt sy nm e A B (seq d) ∧ InRows sy nm nx e A B (seq d) ∨ B ≤ d := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨by rw [T.leftExit _ hx]; omega, T.atExit _ hx⟩
    | succ d ih =>
      rcases ih with ⟨h1, h2⟩ | h1
      · rw [hn d]
        rcases T.rows _ h2 (inp d) (hi d) with g | ⟨g1, g2⟩
        · right
          omega
        · left
          exact ⟨by omega, g1⟩
      · right
        omega
  intro j hj
  cases hc : controllable sy (seq j) with
  | false => rfl
  | true =>
    exfalso
    have hz := S.atControl _ hc
    rcases key j with ⟨h1, _⟩ | h1
    · omega
    · omega

end

end Smbrta.SideChangeEnd
