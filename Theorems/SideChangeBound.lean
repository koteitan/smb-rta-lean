import Theorems.TaintRun
import Theorems.PipeChangeBound
import Theorems.SideTransition

/-!
# The first frames of the change out of the side pipe, from one frame

`Route` proves `change₂ : room.E + 282 ≤ Cs` with this file and `SideChangeEnd.lean`. The change has `A` frames of the pipe's timer and `B` frames after it. Here the first `A` frames are proved for every entry state that meets
a condition on one state (`EntryCond`), for any inputs. The proof looks at one frame only: the abstract machine of `TaintRun.lean` follows one frame with the pad not known and the timer free, and the table of
abstract states closes (`inv_step`). A number `left` is the timer and `B` during the pipe. So a frame of the pipe takes at most one off `left` (`fall_of_inv`). The frames after the pipe are not
proved here: `no_control_all` and `ChangeRun` keep a hypothesis on them, and `SideChangeEnd.lean` proves them.

There is no game data in this file: the known bytes are given by their names, and their values come from a reference machine. Page: `1-1/d-2-2-SideChangeBound.md`.
-/

namespace Smbrta.SideChangeBound

open PipeTransition (frame run zeros)
open PipeTransitionAll (go)
open TaintRun

-- the abstract machine is in `TaintRun.lean`: its names also resolve in this namespace
export TaintRun (
  Env AS AM AS.getK AS.setK s0f atick s0tri appuRead apadRead AS.note ardK peekK rangeJoin ard appuWrite apadWrite awr afetch afetch16 ard16zp addIdx
  apenalty AMode ptrOf aImm aZp aZpi aAbs aAbi aAbiR aIzx aIzy aIzyR asetZN asetFlag asetA asetX asetY apush apull asetPC aadc aoraV aandV aeorV
  ageTri aeqTri acmpV aaslV alsrV arolV arorV aincV adecV aLDA aLDX aLDY aLAX aSTA aSTX aSTY aSAX aADC aSBC aORA aAND aEOR aCMP aCPX aCPY aBIT armw
  armw2 aNOPm aASL aLSR aROL aROR aINC aDEC aSLO aRLA aSRE aRRA aDCP aISB aaccOp aPLP aPHP aPLA aTXS aTSX aJMP aJMPi aJSR aRTS aRTI ainterrupt aBRK
  anmi abranch aJAM aNOP aPHA aTAX aTAY aTXA aTYA aINX aINY aDEX aDEY arow0 arow1 arow2 arow3 arow4 arow5 arow6 arow7 arow8 arow9 arowA arowB arowC
  arowD arowE arowF aRows nextEvent aidle isIdle cycOf isRkDec rkFlags arkOp astep1 splitDot splitFlag bitList splitDg branchMask readsPPU readsDg
  splitBit ldaAddr splitRead pieces succs ramLeFrom AS.le eqTri tri3 actl stackHash keyOf Cfg coverIn isSpin widen ramJoin AS.join Search route
  runFrom searchLoop search Cfg.of Sim Adv Adv.refl Adv.tr Snd TT abind_some Snd.bind Snd.pure Snd.get Snd.fail Snd.congr snd_leaf some_pair s_setZN
  s_setFlag s_modA s_modX s_modY s_setA s_setX s_setY vc vs v1 vd tick_mid s0f_step s_tick s_tick0 rd_ram rd_rom rd_ppu rd_pad rd_17 rd_else TR_s0
  s_ppuRead s_padRead sim_note s_ardK AdR adR_exact adR_same rd_ramrom rangeJoin_mem offset_of_le s_ard wr_ram s_ppuWrite and1 s_padWrite sim_setK
  s_wr s_fetch s_fetch16 s_rd16zp toUInt16_le addIdx_ok s_mImm s_mZp zpi_ok s_mZpx s_mZpy s_mAbs s_mAbx s_mAby s_penalty s_mAbxR s_mAbyR ptrOf_ok
  s_mIzx s_mIzy s_mIzyR s_setPC mem_iteN s_push s_pull s_adc s_oraV s_andV s_eorV s_cmpV s_aslV s_lsrV s_rolV s_rorV s_incV s_decV s_LDA s_LDX s_LDY
  s_modAX s_LAX s_STA s_STX s_STY s_SAX s_ADC s_SBC s_ORA s_AND s_EOR s_CMP s_CPX s_CPY s_bitFlags s_BIT s_rmw s_rmw2 s_ASL s_LSR s_ROL s_ROR s_INC
  s_DEC s_SLO s_RLA s_SRE s_RRA s_DCP s_ISB s_NOPm s_NOP s_JAM s_accOp s_branch s_BPL s_BMI s_BVC s_BVS s_BCC s_BCS s_BNE s_BEQ s_flag s_CLC s_SEC
  s_CLI s_SEI s_CLV s_CLD s_SED s_TAX s_TAY s_TXA s_TYA s_TSX s_TXS s_INX s_INY s_DEX s_DEY s_PHA s_PHP s_PLA s_modP s_PLP s_JMP s_ptrPC s_JMPi s_JSR
  s_RTS s_RTI s_interrupt s_BRK s_nmi AllS AllS.append AllS.get s_row0 s_row1 s_row2 s_row3 s_row4 s_row5 s_row6 s_row7 s_row8 s_row9 s_rowA s_rowB
  s_rowC s_rowD s_rowE s_rowF s_all s_op tick_adv StepRel step_nmi fetch_rom stepK step_op nextEvent_cases nextEvent_same cyc_range tick_first
  tick_wrap s0f_small s_idle snd_then_tick steprel_same go_dec u8_sub_one s_rkOp op_CE cyc_CE s_astep1 Cov cov_flat cov_dot or_self_of bit_of_ne
  and_not_self_of cov_flag bits_80 bits_40 bits_01 bits_02 bit_list cov_dg bit_of_list cov_bit cov_read branchMask_cases cov_pieces s_succs
  ramLeFrom_spec sim_le TR_eqTri tri3_ok actl_ok walkF LiveF cover_liveF live_stepF ruf_doneF frame_runF frame_of_walk tm toOne finRk knownIs finOne
  InvAt ExitAt cfgR cfgO FrameOK frameCheck frameOK_of_check sim_known sim_toOne one_of_sim inv_step)

/-! ## Many frames, for any inputs -/

section
variable {E : Env} {sy : Syms} {keep : List Nat} {starts : List AS} {xb : List (Nat × UInt8)}

open PipeChangeBound (seqOf seqOf_succ)

theorem seq_zero (M : Machine) (w : List UInt8) : seqOf M w 0 = M := by
  simp [seqOf, PipeTransition.run]

/-- while the counter has not had time to run out, the state is the state during the pipe, and the counter has fallen by at most the number of frames -/
theorem inv_seq (hc : FrameOK E sy keep starts xb) (hp : E.pad = AB.top) {M : Machine} (hM : InvAt E starts M) (w : List UInt8) :
    ∀ j, j ≤ w.length → j < (tm E M).toNat → InvAt E starts (seqOf M w j) ∧ (tm E M).toNat ≤ (tm E (seqOf M w j)).toNat + j := by
  intro j
  induction j with
  | zero =>
    intro _ _
    rw [seq_zero]
    exact ⟨hM, by omega⟩
  | succ j ih =>
    intro h1 h2
    obtain ⟨i1, i2⟩ := ih (by omega) (by omega)
    have hj : j < w.length := by omega
    rw [seqOf_succ M w hj]
    rcases inv_step (sy := sy) (keep := keep) hc hp i1 w[j] with ⟨h3, h4⟩ | ⟨h3, _⟩
    · exact ⟨h3, by omega⟩
    · exfalso
      have : (tm E (seqOf M w j)).toNat = 1 := by rw [h3]; rfl
      omega

/-- **The first frames, for any inputs.** Up to the frame on which the counter can first run out, the state is during the pipe or after it. -/
theorem state_seq (hc : FrameOK E sy keep starts xb) (hp : E.pad = AB.top) {M : Machine} (hM : InvAt E starts M) (w : List UInt8) :
    ∀ j, j ≤ w.length → j ≤ (tm E M).toNat → InvAt E starts (seqOf M w j) ∨ ExitAt xb (seqOf M w j) := by
  intro j h1 h2
  by_cases h3 : j < (tm E M).toNat
  · exact Or.inl (inv_seq hc hp hM w j h1 h3).1
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := by
      cases j with
      | zero =>
        exfalso
        have : 0 < (tm E M).toNat := by
          obtain ⟨S, _, (⟨h, _⟩ | ⟨h, _⟩)⟩ := hM
          · omega
          · rw [h]; decide
        omega
      | succ n => exact ⟨n, rfl⟩
    have hj : n < w.length := by omega
    obtain ⟨i1, _⟩ := inv_seq hc hp hM w n (by omega) (by omega)
    rw [seqOf_succ M w hj]
    rcases inv_step (sy := sy) (keep := keep) hc hp i1 w[n] with ⟨h4, _⟩ | ⟨_, h4⟩
    · exact Or.inl h4
    · exact Or.inr h4

end

/-! ## The number of frames left -/

section
open PipeChangeBound (inPipe leftOf keysOK)
open PipeTransitionAll (Names)

/-- the bytes that say where the change is, with the values in the reference machine `x` -/
def exitBytes (sy : Syms) (nm : Names) (x : Machine) : List (Nat × UInt8) :=
  [sy.OperMode_Task, nm.ad "ScreenRoutineTask", sy.GameEngineSubroutine, nm.ad "DisableScreenFlag"].map fun a => ((a &&& 0x7FF).toNat, peek x a)

/-- the state `A` knows that the pipe's routine `eng` runs in the game core -/
def pipeOK (sy : Syms) (eng : UInt16) (A : AS) : Bool :=
  knownIs A ((sy.OperMode_Task &&& 0x7FF).toNat, sy.Task_GameCore.toUInt8) && sy.Task_GameCore.toUInt8.toUInt16 == sy.Task_GameCore &&
  knownIs A ((sy.GameEngineSubroutine &&& 0x7FF).toNat, eng.toUInt8) && eng.toUInt8.toUInt16 == eng

/-- what links the frames to the number `left`. `x` is the reference machine when the timer has run out. -/
def leftCheck (E : Env) (sy : Syms) (nm : Names) (eng : UInt16) (tbl : List (List UInt8 × Nat)) (B : Nat) (starts : List AS) (x : Machine) : Bool :=
  E.rkI == ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat && keysOK sy eng tbl &&
  starts.all (pipeOK sy eng) && (starts.map (toOne E)).all (pipeOK sy eng) &&
  (peek x sy.OperMode_Task).toUInt16 != sy.Task_GameCore && tbl.lookup (PipeChangeBound.keyOf sy nm x) == some B

variable {E : Env} {sy : Syms} {nm : Names} {eng : UInt16} {tbl : List (List UInt8 × Nat)} {B : Nat} {keep : List Nat} {starts : List AS} {x : Machine}

structure LeftOK (E : Env) (sy : Syms) (nm : Names) (eng : UInt16) (tbl : List (List UInt8 × Nat)) (B : Nat) (starts : List AS) (x : Machine) : Prop where
  timer : E.rkI = ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat
  keys : keysOK sy eng tbl = true
  s1 : ∀ S ∈ starts, pipeOK sy eng S = true
  s2 : ∀ S ∈ starts, pipeOK sy eng (toOne E S) = true
  notCore : (peek x sy.OperMode_Task).toUInt16 ≠ sy.Task_GameCore
  look : tbl.lookup (PipeChangeBound.keyOf sy nm x) = some B

theorem leftOK_of_check (h : leftCheck E sy nm eng tbl B starts x = true) : LeftOK E sy nm eng tbl B starts x := by
  simp only [leftCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, fun S hS => h4 _ (List.mem_map.2 ⟨S, hS, rfl⟩), h5, h6⟩

theorem inPipe_of_sim {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : pipeOK sy eng A = true) : inPipe sy eng m = true := by
  simp only [pipeOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := sim_known hs h1
  have e2 := sim_known hs h3
  simp only [inPipe, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · show (m.ram.get! (sy.OperMode_Task &&& 0x7FF).toNat).toUInt16 = _
    rw [e1]
    exact h2
  · show (m.ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat).toUInt16 = _
    rw [e2]
    exact h4

theorem inPipe_of_inv (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : InvAt E starts m) : inPipe sy eng m = true := by
  obtain ⟨S, hS, (⟨_, hs⟩ | ⟨_, hs⟩)⟩ := h
  · exact inPipe_of_sim hs (hl.s1 S hS)
  · exact inPipe_of_sim hs (hl.s2 S hS)

/-- during the pipe, `left` is the counter and `B` -/
theorem left_of_inv (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : InvAt E starts m) :
    leftOf sy nm eng tbl B m = (tm E m).toNat + B := by
  simp only [leftOf, inPipe_of_inv hl h, if_true]
  have : peek m (nm.ad "ChangeAreaTimer") = tm E m := by
    show m.ram.get! _ = m.ram.get! E.rkI
    rw [hl.timer]
  rw [this]

theorem key_of_exit (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : ExitAt (exitBytes sy nm x) m) :
    PipeChangeBound.keyOf sy nm m = PipeChangeBound.keyOf sy nm x := by
  have e : ∀ a, a ∈ [sy.OperMode_Task, nm.ad "ScreenRoutineTask", sy.GameEngineSubroutine, nm.ad "DisableScreenFlag"] → peek m a = peek x a := by
    intro a ha
    exact h ((a &&& 0x7FF).toNat, peek x a) (List.mem_map.2 ⟨a, ha, rfl⟩)
  have e1 := e _ List.mem_cons_self
  have e2 := e _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have e3 := e _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have e4 := e _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hn : ((peek x sy.OperMode_Task).toUInt16 == sy.Task_GameCore) = false := beq_eq_false_iff_ne.2 hl.notCore
  have hn2 : ((peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore) = false := by rw [e1]; exact hn
  unfold PipeChangeBound.keyOf
  simp only [hn, hn2, Bool.false_eq_true, if_false]
  rw [e1, e2, e3, e4]

/-- after the pipe, `left` is `B` -/
theorem left_of_exit (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : ExitAt (exitBytes sy nm x) m) :
    leftOf sy nm eng tbl B m = B := by
  have e1 : peek m sy.OperMode_Task = peek x sy.OperMode_Task := h ((sy.OperMode_Task &&& 0x7FF).toNat, peek x sy.OperMode_Task) (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  have hnp : inPipe sy eng m = false := by
    cases hq : inPipe sy eng m with
    | false => rfl
    | true =>
      exfalso
      simp only [inPipe, Bool.and_eq_true, beq_iff_eq] at hq
      rw [e1] at hq
      exact hl.notCore hq.1
  simp only [leftOf, hnp, if_false]
  rw [key_of_exit hl h, hl.look]
  rfl

/-- **A frame of the pipe takes at most one off `left`, for any input.** -/
theorem fall_of_inv (hc : FrameOK E sy keep starts (exitBytes sy nm x)) (hp : E.pad = AB.top) (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine}
    (h : InvAt E starts m) (i : UInt8) : leftOf sy nm eng tbl B m ≤ leftOf sy nm eng tbl B (frame m i) + 1 := by
  rw [left_of_inv hl h]
  rcases inv_step hc hp h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [left_of_inv hl h1]
    omega
  · rw [left_of_exit hl h2, h1]
    have : (1 : UInt8).toNat = 1 := rfl
    omega

theorem ctl_of_inPipe {m : Machine} (hk : keysOK sy eng tbl = true) (h : inPipe sy eng m = true) : controllable sy m = false := by
  simp only [keysOK, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hk
  simp only [inPipe, Bool.and_eq_true, beq_iff_eq] at h
  cases hc : controllable sy m with
  | false => rfl
  | true =>
    exfalso
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
    exact hk.1 (h.2.symm.trans hc.2)

theorem ctl_of_exit (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : ExitAt (exitBytes sy nm x) m) : controllable sy m = false := by
  have e1 : peek m sy.OperMode_Task = peek x sy.OperMode_Task := h ((sy.OperMode_Task &&& 0x7FF).toNat, peek x sy.OperMode_Task) (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  cases hc : controllable sy m with
  | false => rfl
  | true =>
    exfalso
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
    rw [e1] at hc
    exact hl.notCore hc.1.2

open PipeChangeBound (seqOf seqOf_succ)

/-- **No control on the first frames, for any inputs.** The whole statement comes from the state `M` alone. `c` is at most the counter's value in `M`. -/
theorem no_control_first (hc : FrameOK E sy keep starts (exitBytes sy nm x)) (hp : E.pad = AB.top) (hl : LeftOK E sy nm eng tbl B starts x) {M : Machine}
    (hM : InvAt E starts M) {c : Nat} (hT : c ≤ (tm E M).toNat) (w : List UInt8) : ∀ j, j ≤ w.length → j ≤ c → controllable sy (seqOf M w j) = false := by
  intro j h1 h2
  rcases state_seq hc hp hM w j h1 (by omega) with h3 | h3
  · exact ctl_of_inPipe hl.keys (inPipe_of_inv hl h3)
  · exact ctl_of_exit hl h3

/-- **No control on the whole change, for any inputs.** The frames in the state during the pipe are proved. The other frames keep the hypothesis `hf`: `left` falls by at most one on them. -/
theorem no_control_all (hc : FrameOK E sy keep starts (exitBytes sy nm x)) (hp : E.pad = AB.top) (hl : LeftOK E sy nm eng tbl B starts x) {M : Machine}
    (hM : InvAt E starts M) (w : List UInt8)
    (hf : ∀ j (h : j < w.length), ¬ InvAt E starts (seqOf M w j) → leftOf sy nm eng tbl B (seqOf M w j) ≤ leftOf sy nm eng tbl B (frame (seqOf M w j) w[j]) + 1) :
    ∀ j, j ≤ w.length → j < (tm E M).toNat + B → controllable sy (seqOf M w j) = false := by
  intro j h1 h2
  refine PipeChangeBound.no_control (controllable sy) (left := leftOf sy nm eng tbl B) M w ?_ (fun i _ hq => PipeChangeBound.left_zero_of_ctl hl.keys hq) j h1 ?_
  · intro i hi
    by_cases hin : InvAt E starts (seqOf M w i)
    · exact fall_of_inv hc hp hl hin _
    · exact hf i hi hin
  · rw [left_of_inv hl hM]
    exact h2

/-- **The bound on the change, counted.** `seq` lists all the frames of a run, `cnt` counts the frames that are not lag frames. Each counted frame takes at most one off `left`, a lag frame takes nothing off.
Then the change from `a` to `b` has at least `left (seq a)` counted frames, if `left` is 0 at `b`. -/
theorem change_counted {left : Machine → Nat} {seq : Nat → Machine} {cnt : Nat → Nat} {lag : Nat → Prop} [DecidablePred lag]
    (hc : ∀ n, cnt (n + 1) = cnt n + (if lag n then 0 else 1)) {a b : Nat} (hab : a ≤ b)
    (hf : ∀ n, a ≤ n → n < b → left (seq n) ≤ left (seq (n + 1)) + (if lag n then 0 else 1)) (hb : left (seq b) = 0) :
    cnt a + left (seq a) ≤ cnt b := by
  have key : ∀ d, a + d ≤ b → cnt a + left (seq a) ≤ cnt (a + d) + left (seq (a + d)) := by
    intro d
    induction d with
    | zero => intro _; exact Nat.le_refl _
    | succ d ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hf (a + d) (by omega) (by omega)
      have h3 := hc (a + d)
      have e : a + (d + 1) = a + d + 1 := rfl
      rw [e, h3]
      omega
  have := key (b - a) (by omega)
  have e : a + (b - a) = b := by omega
  rw [e, hb] at this
  omega

end

/-! ## The state at the entry -/

/-- the known bytes as a mask -/
def knOf (K : List Nat) : ByteArray := K.foldl (fun b i => b.set! i 0xFF) (ByteArray.mk (Array.replicate 2048 0))

/-- the abstract start state from the reference machine `r`, for dot 0 (`low`) or dots `1..9`. Only the bytes `K` are known. The registers are not known. The counter is followed. -/
def startOf (r : Machine) (K : List Nat) (low : Bool) : AS :=
  { a := AB.top, x := AB.top, y := AB.top, s := r.s, p := AB.top, pc := r.pc, ram := r.ram, kn := knOf K, ppuCtrl := ⟨0x80, 0x80⟩, ppuMask := AB.top,
    vb := !low, nmi := !low, lo := if low then 0 else 1, hi := if low then 0 else 9, padShift := AB.top, strobe := false, dg := false, k := 0, rk := true, spent := false }

/-- the start states: each reference machine with its known bytes, two kinds of dots -/
def startsOf (V : List (Machine × List Nat)) : List AS :=
  V.flatMap fun v => [startOf v.1 v.2 true, startOf v.1 v.2 false]

/-- **The condition on the state at the end of the entry frame.** It is on one state. All bytes that are not listed are free. -/
structure EntryCond (E : Env) (V : List (Machine × List Nat)) (c : Nat) (m : Machine) : Prop where
  /-- the frame has ended in the idle loop, with the next NMI to come or pending -/
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
  /-- the program counter, the stack pointer and the listed bytes are those of a reference machine -/
  ref : ∃ v ∈ V, m.pc = v.1.pc ∧ m.s = v.1.s ∧ ∀ i ∈ v.2, m.ram.get! i = v.1.ram.get! i
  /-- the counter -/
  timer : c ≤ (m.ram.get! E.rkI).toNat

/-- `EntryCond` as a check, for a program -/
def entryOK (E : Env) (V : List (Machine × List Nat)) (c : Nat) (m : Machine) : Bool :=
  decide (m.fdot < 10) && ((m.fdot == 0 && !m.vblank && !m.nmiPending) || (decide (1 ≤ m.fdot) && m.vblank && m.nmiPending)) && m.sprite0 &&
  m.ppuCtrl &&& 0x80 == 0x80 && !m.padStrobe && !m.halted && !m.trk && decide (m.prg.data = E.prg.data) && m.prgMask == E.mask && m.ram.size == 2048 &&
  V.any (fun v => m.pc == v.1.pc && m.s == v.1.s && v.2.all fun i => m.ram.get! i == v.1.ram.get! i) && decide (c ≤ (m.ram.get! E.rkI).toNat)

theorem entryCond_of_ok {E : Env} {V : List (Machine × List Nat)} {c : Nat} {m : Machine} (h : entryOK E V c m = true) : EntryCond E V c m := by
  simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, SideTransition.byteArray_eq h8, h9, h10, ?_, h12⟩
  · rcases h2 with ⟨⟨a1, a2⟩, a3⟩ | ⟨⟨a1, a2⟩, a3⟩
    · exact Or.inl ⟨a1, a2, a3⟩
    · exact Or.inr ⟨a1, a2, a3⟩
  · obtain ⟨v, hv, ⟨a1, a2⟩, a3⟩ := h11
    exact ⟨v, hv, a1, a2, a3⟩

/-- the masks of the start states are what the list says -/
def startsOK (V : List (Machine × List Nat)) : Bool :=
  V.all fun v => v.1.ram.size == 2048 && (knOf v.2).size == 2048 && (List.range 2048).all fun i => (knOf v.2).get! i == 0 || ((knOf v.2).get! i == 0xFF && v.2.contains i)

section
variable {E : Env} {V : List (Machine × List Nat)} {c : Nat}

theorem inv_of_entry (hV : startsOK V = true) (hp : E.pad = AB.top) (hc : 2 ≤ c) {m : Machine} (h : EntryCond E V c m) : InvAt E (startsOf V) m := by
  obtain ⟨v, hv, h1, h2, h3⟩ := h.ref
  simp only [startsOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hV
  obtain ⟨⟨s1, s2⟩, s3⟩ := hV v hv
  have hT : 2 ≤ (tm E m).toNat := Nat.le_trans hc h.timer
  have key : ∀ low : Bool, (low = true ↔ m.fdot = 0) → Sim E (m.frame, tm E m) (startOf v.1 v.2 low) m := by
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
    refine ⟨mem_top _, mem_top _, mem_top _, mem_top _, h2, h1, h.prg, h.mask, ?_, mem_top _, hvb.1, hvb.2, ?_, hlo, hhi, ?_, by rw [hp]; exact mem_top _, mem_top _, h.strobe, h.halted, h.trk, h.size, ?_, ?_, s1, s2, ?_, ?_⟩
    · show m.ppuCtrl &&& 0x80 = (0x80 : UInt8) &&& 0x80
      rw [h.ctrl]
      decide
    · rw [h.s0]
      have : m.fdot ≤ 9 := by have := h.dot; omega
      exact (s0f_small this).symm
    · show (if low = true then 0 else 9) < dotsPerFrame
      split <;> decide
    · intro i hi
      show AB.mem ⟨v.1.ram.get! i, (knOf v.2).get! i⟩ (m.ram.get! i)
      have h5 := s3 i (List.mem_range.2 hi)
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h5
      rcases h5 with h5 | ⟨h5, h6⟩
      · apply bt_ext
        intro j hj
        simp [bt_and, h5, bt_zero hj]
      · rw [h3 i (by simpa using h6)]
        exact rfl
    · intro hd
      cases hd
    · show m.frame = m.frame + 0
      rfl
    · intro _
      rfl
  by_cases hd : m.fdot = 0
  · exact ⟨_, List.mem_flatMap.2 ⟨v, hv, List.mem_cons_self⟩, Or.inl ⟨hT, key true ⟨fun _ => hd, fun _ => rfl⟩⟩⟩
  · refine ⟨_, List.mem_flatMap.2 ⟨v, hv, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩, Or.inl ⟨hT, key false ⟨fun h0 => (by cases h0), fun h0 => absurd h0 hd⟩⟩⟩

end

/-! ## The statement for the side pipe -/

section
open PipeTransitionAll (Names asmValue)
open PipeChangeBound (leftOf seqOf)

/-- the table of `left`: `n` frames with no input from `m`, each key with the frames left -/
def tableFrom (sy : Syms) (nm : Names) : Nat → Machine → List (List UInt8 × Nat)
  | 0, _ => []
  | n + 1, m => (PipeChangeBound.keyOf sy nm m, n + 1) :: tableFrom sy nm n (frame m 0)

/-- the bytes that the state at the entry knows: a name, an offset and a number of bytes. The values come from the reference machine. -/
def knownNames : List (String × Nat × Nat) :=
  [("OperMode", 0, 1), ("OperMode_Task", 0, 1), ("GameEngineSubroutine", 0, 1), ("ScreenRoutineTask", 0, 1), ("DisableScreenFlag", 0, 1), ("WorldNumber", 0, 1),
   ("AreaType", 0, 1), ("SecondaryHardMode", 0, 1),
   ("Player_State", 0, 1), ("Player_Y_HighPos", 0, 1), ("Player_Y_Position", 0, 1), ("Player_SprDataOffset", 0, 1), ("JumpspringAnimCtrl", 0, 1),
   ("Enemy_Flag", 0, 6), ("Enemy_ID", 5, 1), ("Fireball_State", 0, 2), ("Block_State", 0, 2), ("Block_RepFlag", 0, 2), ("Misc_State", 0, 9), ("FloateyNum_Timer", 0, 6),
   ("VineFlagOffset", 0, 1), ("Cannon_PageLoc", 0, 6), ("Cannon_X_Position", 0, 6), ("Cannon_Y_Position", 0, 4),
   ("EnemyData", 0, 2), ("EnemyDataOffset", 0, 1), ("EnemyObjectPageLoc", 0, 1), ("EnemyFrenzyBuffer", 0, 1), ("EnemyFrenzyQueue", 0, 1), ("StarInvincibleTimer", 0, 1),
   ("ScreenRight_PageLoc", 0, 1), ("ScreenRight_X_Pos", 0, 1), ("ScrollLock", 0, 1), ("ScrollThirtyTwo", 0, 1), ("AreaParserTaskNum", 0, 1), ("VRAM_Buffer_AddrCtrl", 0, 1),
   ("VRAM_Buffer1_Offset", 0, 1), ("VRAM_Buffer1", 0, 1),
   ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1), ("MusicData", 0, 2), ("MusicOffset_Square1", 0, 1), ("NoiseSoundBuffer", 0, 1), ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1)]

/-- the bytes that the state knows besides, when the buffer of the screen holds a record -/
def recordNames : List (String × Nat × Nat) := [("VRAM_Buffer1", 1, 2), ("VRAM_Buffer1", 7, 1)]

/-- the names this file needs -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  let l := (knownNames ++ recordNames).map (·.1) ++ ["ChangeAreaTimer", "FrameCounter"]
  l.eraseDups.filterMap fun n => (asmValue ls n).map (n, ·)

/-- the list of bytes of a list of names, as RAM indices -/
def bytesOf (nm : Names) (l : List (String × Nat × Nat)) : List Nat :=
  l.flatMap fun p => (List.range p.2.2).map fun j => ((nm.ad p.1).toNat + p.2.1 + j) &&& 0x7FF

/-- the environment of the abstract run: the pad is not known; the counter is the pipe's timer; the frame counter is read in pieces by its low bits -/
def sideEnv (nm : Names) (e : Machine) : Env :=
  { prg := e.prg, mask := e.prgMask, pad := AB.top, D := [], rkI := ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat, splits := [(((nm.ad "FrameCounter") &&& 0x7FF).toNat, 7)] }

/-- the reference machines from the entry `e`: one frame with the buffer of the screen empty, one with a record in it -/
def refsOf (nm : Names) (e : Machine) : List (Machine × List Nat) :=
  let ms := (List.range 9).map fun j => run e (zeros j)
  let off := fun (m : Machine) => peek m (nm.ad "VRAM_Buffer1_Offset")
  [((ms.find? (off · == 0)).getD e, bytesOf nm knownNames), ((ms.find? (off · != 0)).getD e, bytesOf nm (knownNames ++ recordNames))]

/-- the bytes whose values are kept apart in the search -/
def keepOf (nm : Names) : List Nat := [((nm.ad "VRAM_Buffer1_Offset") &&& 0x7FF).toNat, ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat]

/-- `EntryCond` for the entry `e`, with the timer at least `A` -/
abbrev Entry (nm : Names) (e : Machine) (A : Nat) (m : Machine) : Prop := EntryCond (sideEnv nm e) (refsOf nm e) A m

/-- the number of frames left, with the table from `e` from frame `A` on -/
abbrev leftAt (sy : Syms) (nm : Names) (e : Machine) (A B : Nat) : Machine → Nat :=
  leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (run e (zeros A))) B

/-- the state during the pipe -/
abbrev During (nm : Names) (e : Machine) : Machine → Prop := InvAt (sideEnv nm e) (startsOf (refsOf nm e))

/-- the whole check on the ROM -/
def allCheck (sy : Syms) (nm : Names) (e : Machine) (es : List Machine) (A B : Nat) : Bool :=
  let E := sideEnv nm e
  let V := refsOf nm e
  let st := startsOf V
  let x := run e (zeros A)
  decide (2 ≤ A) && startsOK V && frameCheck E sy (keepOf nm) st (exitBytes sy nm x) &&
    leftCheck E sy nm sy.EngSidePipe (tableFrom sy nm B x) B st x && es.all (entryOK E V A)

/-- **The statement.** `A` is the pipe's timer and `B` the frames after it. -/
structure Statement (sy : Syms) (nm : Names) (e : Machine) (es : List Machine) (A B : Nat) : Prop where
  /-- the entries that were run meet the condition -/
  entries : ∀ m ∈ es, Entry nm e A m
  /-- an entry is in the state during the pipe -/
  during : ∀ M, Entry nm e A M → During nm e M
  /-- one frame of the pipe, for any input -/
  step : ∀ m, During nm e m → ∀ i, (During nm e (frame m i) ∧ (tm (sideEnv nm e) m).toNat ≤ (tm (sideEnv nm e) (frame m i)).toNat + 1) ∨
    (tm (sideEnv nm e) m = 1 ∧ ExitAt (exitBytes sy nm (run e (zeros A))) (frame m i))
  /-- one frame of the pipe takes at most one off `left`, for any input -/
  fall : ∀ m, During nm e m → ∀ i, leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i) + 1
  /-- `left` at an entry -/
  atEntry : ∀ M, Entry nm e A M → A + B ≤ leftAt sy nm e A B M
  /-- control only where `left` is 0 -/
  atControl : ∀ m, controllable sy m = true → leftAt sy nm e A B m = 0
  /-- no control on the first `A` frames, for any inputs, from the condition on the entry alone -/
  noFirst : ∀ M, Entry nm e A M → ∀ w, ∀ j, j ≤ w.length → j ≤ A → controllable sy (seqOf M w j) = false
  /-- no control on the whole change, for any inputs, if `left` falls by at most one on the frames out of the state during the pipe -/
  noAll : ∀ M, Entry nm e A M → ∀ w, (∀ j (h : j < w.length), ¬ During nm e (seqOf M w j) → leftAt sy nm e A B (seqOf M w j) ≤ leftAt sy nm e A B (frame (seqOf M w j) w[j]) + 1) →
    ∀ j, j ≤ w.length → j < A + B → controllable sy (seqOf M w j) = false

theorem statement_of_check {sy : Syms} {nm : Names} {e : Machine} {es : List Machine} {A B : Nat} (h : allCheck sy nm e es A B = true) : Statement sy nm e es A B := by
  simp only [allCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hV⟩, hf⟩, hl⟩, hes⟩ := h
  have hF := frameOK_of_check hf
  have hL := leftOK_of_check hl
  have hp : (sideEnv nm e).pad = AB.top := rfl
  have hd : ∀ M, Entry nm e A M → During nm e M := fun M hM => inv_of_entry hV hp hA hM
  refine ⟨fun m hm => entryCond_of_ok (hes m hm), hd, fun m hm i => inv_step hF hp hm i, fun m hm i => fall_of_inv hF hp hL hm i, ?_, fun m hc => PipeChangeBound.left_zero_of_ctl hL.keys hc, ?_, ?_⟩
  · intro M hM
    show A + B ≤ leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (run e (zeros A))) B M
    rw [left_of_inv hL (hd M hM)]
    have := hM.timer
    show A + B ≤ ((sideEnv nm e).rkI |> M.ram.get!).toNat + B
    omega
  · intro M hM w j h1 h2
    exact no_control_first hF hp hL (hd M hM) hM.timer w j h1 h2
  · intro M hM w hff j h1 h2
    have := hM.timer
    exact no_control_all hF hp hL (hd M hM) w hff j h1 (by
      show j < ((sideEnv nm e).rkI |> M.ram.get!).toNat + B
      omega)

/-! ## A run -/

/-- with no input, the frames of `seqOf` are the frames of `run` -/
theorem seq_zeros (M : Machine) {n k : Nat} (h : k ≤ n) : seqOf M (zeros n) k = run M (zeros k) := by
  simp only [seqOf, zeros]
  rw [List.take_replicate, Nat.min_eq_left h]

/-- `(H1)` of `SideTransitionAll.every_entry` follows from the condition on the entry -/
theorem Statement.no_input {sy : Syms} {nm : Names} {e : Machine} {es : List Machine} {A B : Nat} (S : Statement sy nm e es A B) {M : Machine} (hM : Entry nm e A M) :
    ∀ k, 1 ≤ k → k ≤ A → controllable sy (run M (zeros k)) = false := by
  intro k _ h2
  have := S.noFirst M hM (zeros A) k (by simpa [zeros] using h2) h2
  rwa [seq_zeros M h2] at this

/-- **The change of a run.** `seq` lists all the frames of a run, `a` is the entry, `b` is control. `cnt` counts the frames that are not lag frames. -/
structure ChangeRun (sy : Syms) (nm : Names) (e : Machine) (A B : Nat) where
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (inp n)
  lag : Nat → Prop
  dec : DecidablePred lag
  cnt : Nat → Nat
  hcnt : ∀ n, cnt (n + 1) = cnt n + (if lag n then 0 else 1)
  a : Nat
  b : Nat
  order : a ≤ b
  /-- the condition on the state at the entry -/
  entry : Entry nm e A (seq a)
  /-- control at `b` -/
  atCtl : controllable sy (seq b) = true
  /-- a lag frame takes nothing off `left` -/
  lagKeeps : ∀ n, a ≤ n → n < b → lag n → leftAt sy nm e A B (seq n) ≤ leftAt sy nm e A B (seq (n + 1))
  /-- out of the state during the pipe, a frame takes at most one off `left` -/
  fallAfter : ∀ n, a ≤ n → n < b → ¬ During nm e (seq n) → leftAt sy nm e A B (seq n) ≤ leftAt sy nm e A B (seq (n + 1)) + 1

/-- **The bound on the change follows**, under `fallAfter`. `SideChangeEnd.EndRun.bound` gives it without that field. -/
theorem ChangeRun.bound {sy : Syms} {nm : Names} {e : Machine} {es : List Machine} {A B : Nat} (S : Statement sy nm e es A B) (R : ChangeRun sy nm e A B) :
    R.cnt R.a + (A + B) ≤ R.cnt R.b := by
  have hf : ∀ n, R.a ≤ n → n < R.b → leftAt sy nm e A B (R.seq n) ≤ leftAt sy nm e A B (R.seq (n + 1)) + (@ite _ (R.lag n) (R.dec n) 0 1) := by
    intro n h1 h2
    by_cases hl : R.lag n
    · rw [if_pos hl]
      exact R.lagKeeps n h1 h2 hl
    · rw [if_neg hl]
      by_cases hd : During nm e (R.seq n)
      · rw [R.next n]
        exact S.fall _ hd _
      · exact R.fallAfter n h1 h2 hd
  have h := @change_counted (leftAt sy nm e A B) R.seq R.cnt R.lag R.dec R.hcnt R.a R.b R.order hf (S.atControl _ R.atCtl)
  have h2 := S.atEntry _ R.entry
  omega

end

end Smbrta.SideChangeBound
