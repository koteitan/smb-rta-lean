import Theorems.CastleToLevel
import Theorems.TitleStart
import Theorems.HurryFrame
import Theorems.HurryStart

/-!
# Runs with the hurry-up music

The game queues the hurry-up music on the frame on which the timer shows 100. A run in which this music plays fails the condition at the side pipe's entry
(`Route.ChangesBase.entry₂`: the music bytes and `NoteLengthTblAdder`), so it is outside `Route.Run`. Here it gets its own bound. By the rule of `CastleToLevel.Frames`
on single frames, the timer shows `u` or less only after at least `q · (t0 − u) − 3q` frames (`CastleToLevel.Frames.late`), so the castle entry and the level change
come long after frame 1748. The link from the music to the timer is a walk of the one frame that starts the music (`HurryFrame.frame_music`): it ends with the timer at `u` or
less, if it is a frame in control as the walk needs it (`HurryFrame.Start`, `Run.clean`). That it begins so is a theorem (`Run.startAt`): the same walk shows that a frame
in control that ends with control and without the music ends at the start of a frame in control (`HurryFrame.frame_startC`), so by induction every frame from `Run.b` on
begins so. That such a frame ends with control is a theorem too: the walk with the stores of the routine, the mode and the task cut (`HurryFrame.frame_ctl`), when no
instruction of the frame writes these bytes by their address (`Run.noStore`). Frame `Run.b` is frame 1, whose start comes from the press of Start on the title
(`Begin.start₁`), or the last frame of a change of area, whose start comes from the last rows with tables of the change (`HurryStart`, `Run.startB`). The run's machines are
those of `Route.Base`, and the conditions of the changes those of `Route.ChangesK`, as in `Route.Run` (for the first change alone, its fields of `Route.ChangesK`). The timer and the music when frame 0 begins come from the press of Start on
the title (`TitleStart.Begin`). Page: `1-1/0-6-4-HurryMusic.md`.

No value of the game appears here: the names are read from the disassembly, and `q`, `t0`, `u` are parameters.
-/

namespace Smbrta.HurryMusic

open CastleToLevel (Frames Segs timerOf)
open PipeTransitionAll (Names asmValue)

/-- the names this file reads -/
def nameList : List String := ["GameTimerDisplay", "EventMusicQueue", "EventMusicBuffer", "NoteLengthTblAdder", "TimeRunningOutMusic", "PlayerStatus", "DeathMusicLoaded", "DigitModifier", "DisplayDigits"]

/-- a value of the disassembly written in binary (`%`) -/
def binValue (lines : List String) (n : String) : Option Nat :=
  lines.findSome? fun l =>
    match (l.splitOn "=").map (fun x => (x.splitOn ";").headD "") with
    | a :: b :: _ =>
      if a.trimAscii.toString == n then
        match b.trimAscii.toString.toList with
        | '%' :: ds => some (ds.foldl (fun v c => 2 * v + (if c == '1' then 1 else 0)) 0)
        | _ => none
      else none
    | _ => none

/-- the names above, from the text of the disassembly -/
def namesFrom (text : String) : Names :=
  let ls := text.splitOn "\n"
  nameList.filterMap fun n => ((asmValue ls n).orElse fun _ => binValue ls n).map (n, ·)

/-- the hurry-up music: queued, playing, or the faster tempo it leaves for the song after it. The queue and its buffer are read by the music's bit. -/
def hurryOn (nm : Names) (m : Machine) : Bool :=
  peek m (nm.ad "EventMusicQueue") &&& nm.vl "TimeRunningOutMusic" != 0 || peek m (nm.ad "EventMusicBuffer") &&& nm.vl "TimeRunningOutMusic" != 0 ||
    peek m (nm.ad "NoteLengthTblAdder") != 0

/-- a property of the machines that is false when frame 0 begins and true when frame `k` begins turns true on some frame before `k` -/
theorem first_on {seq : Nat → Machine} {P : Machine → Bool} (h0 : P (seq 0) = false) :
    ∀ k, P (seq k) = true → ∃ n, n < k ∧ P (seq n) = false ∧ P (seq (n + 1)) = true
  | 0, h => by rw [h0] at h; exact absurd h (by decide)
  | k + 1, h => by
    cases hk : P (seq k) with
    | true =>
      obtain ⟨n, h1, h2, h3⟩ := first_on h0 k hk
      exact ⟨n, by omega, h2, h3⟩
    | false => exact ⟨k, by omega, hk, h⟩

/-- no hurry-up music in a machine with the bytes of `TitleStart.zeroBytes` -/
theorem quiet_of {nm : Names} {t0 : Nat} {m : Machine} (h : ∀ p ∈ TitleStart.zeroBytes nm t0, m.ram.get! p.1 = p.2) :
    hurryOn nm m = false := by
  have h5 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have h6 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  have h7 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
  simp only [hurryOn, peek]
  simp only [TitleStart.adI] at h5 h6 h7
  rw [h5, h6, h7]
  simp

/-- no hurry-up music: the music bits of the walk are off -/
theorem watched_of_off {sy : Syms} {nm : Names} {m0 m : Machine} (h : hurryOn nm m = false) : FrameKeep.Watched (HurryFrame.watchOf (HurryFrame.placesOf sy nm m0)) m := by
  simp only [hurryOn, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro w hw
  simp only [HurryFrame.watchOf, HurryFrame.placesOf, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · show m.ram.get! _ &&& _ = 0 &&& _
    rw [UInt8.zero_and]
    exact h1
  · show m.ram.get! _ &&& _ = 0 &&& _
    rw [UInt8.zero_and]
    exact h2
  · show m.ram.get! _ &&& 0xFF = 0 &&& 0xFF
    rw [FrameKeep.and_ff]
    exact h3

/-- the music bits of the walk off: no hurry-up music -/
theorem off_of_watched {sy : Syms} {nm : Names} {m0 m : Machine} (h : FrameKeep.Watched (HurryFrame.watchOf (HurryFrame.placesOf sy nm m0)) m) : hurryOn nm m = false := by
  have h1 := h _ List.mem_cons_self
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [HurryFrame.placesOf, UInt8.zero_and, FrameKeep.and_ff] at h1 h2 h3
  simp only [hurryOn, peek, Bool.or_eq_false_iff, bne_eq_false_iff_eq]
  exact ⟨⟨h1, h2⟩, h3⟩

/-- frame `n` is the first frame that starts the hurry-up music: no music when frames `0` to `n` begin, the music when frame `n + 1` begins -/
def First (nm : Names) (seq : Nat → Machine) (n : Nat) : Prop :=
  (∀ m, m ≤ n → hurryOn nm (seq m) = false) ∧ hurryOn nm (seq (n + 1)) = true

/-- a property that is false when frame 0 begins and true when frame `k` begins turns true first on some frame before `k` -/
theorem first_turn {seq : Nat → Machine} {P : Machine → Bool} (h0 : P (seq 0) = false) (k : Nat) (hk : P (seq k) = true) :
    ∃ n, n < k ∧ (∀ m, m ≤ n → P (seq m) = false) ∧ P (seq (n + 1)) = true := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => rw [h0] at hk; exact absurd hk (by decide)
    | succ k =>
      cases hb : (List.range (k + 1)).any (fun m => P (seq m)) with
      | false =>
        refine ⟨k, by omega, fun m hm => ?_, hk⟩
        have := List.any_eq_false.1 hb m (List.mem_range.2 (by omega))
        simpa using this
      | true =>
        obtain ⟨m, hm, hP⟩ := List.any_eq_true.1 hb
        have hm' := List.mem_range.1 hm
        obtain ⟨n, h1, h2, h3⟩ := ih m (by omega) hP
        exact ⟨n, by omega, h2, h3⟩

/-- **The check of frame 0**: from each near or held state of `TitleStart`, with any input, the frame ends with control and the speed 0, at the start of a frame in control
(`FrameKeep.endOK`), with the bytes that the digits routine adds 0 and the music bits off; or it ends without control in a state of `TitleStart`'s set
(`TitleStart.frame0Check`). `TitleStart`'s machine has the program of `m0`. -/
def nearCheck (sy : Syms) (m0 : Machine) (c : TitleStart.Ctx) : Bool :=
  let P := HurryFrame.placesOf sy c.nm m0
  decide (c.E.prg.data = (PipeEntryRule.envOf m0).prg.data) && c.E.mask == (PipeEntryRule.envOf m0).mask &&
    TitleStart.frame0Check sy c
      (fun B => TitleStart.finNear sy B && FrameKeep.watchOK (HurryFrame.modsW P ++ HurryFrame.watchOf P) B && FrameKeep.endOK (HurryFrame.guardOf sy c.nm m0) B)

/-- **Frame 1 begins in control as the walk needs it**, with the music bits off: the end of frame 0, with any input (`TitleStart.Begin.frame0`). Start is allowed on every frame.
`hB` and `hN` are checks on the ROM. -/
theorem Begin.start₁ {sy : Syms} {m0 : Machine} {c : TitleStart.Ctx} {t0 : Nat} {seq : Nat → Machine} {inp : Nat → UInt8} (hB : TitleStart.check sy c t0 = true)
    (hN : nearCheck sy m0 c = true) (B : TitleStart.Begin sy c seq inp) (hn : seq 1 = PipeTransition.frame (seq 0) (inp 0)) :
    PipeWrites.FrameStart (HurryFrame.guardOf sy c.nm m0) (PipeEntryRule.envOf m0) (seq 1) ∧
      FrameKeep.Watched (HurryFrame.watchOf (HurryFrame.placesOf sy c.nm m0)) (seq 1) := by
  unfold nearCheck at hN
  rw [Bool.and_eq_true, Bool.and_eq_true] at hN
  obtain ⟨⟨hp, hm⟩, hN'⟩ := hN
  obtain ⟨B', h1, h2⟩ := B.frame0 hB hN' hn
  simp only [Bool.and_eq_true] at h1
  have hw := FrameKeep.watched_of h1.1.2 h2
  have hmo : FrameKeep.Watched (HurryFrame.modsW (HurryFrame.placesOf sy c.nm m0)) (seq 1) :=
    fun w hw' => hw w (List.mem_append_left _ hw')
  have hwm : FrameKeep.Watched (HurryFrame.watchOf (HurryFrame.placesOf sy c.nm m0)) (seq 1) :=
    fun w hw' => hw w (List.mem_append_right _ hw')
  have hc := B.ctl
  exact ⟨FrameKeep.start_of_sim h2 h1.2 (SideTransition.byteArray_eq (of_decide_eq_true hp)) (beq_iff_eq.1 hm) (HurryFrame.known_of hc hmo), hwm⟩

/-- A run in which the hurry-up music plays at frame `k`, up to the castle entry `E`. `clock` is as `Route.Run.clock`; `base` holds the real frames of the run, as `Route.Run.base`:
`base.seq n` is the machine when frame `n` begins. The names are those of `tc`; `m0` is the reference machine at control of the walk. The fields on frames are asked of the first
frame `n` that starts the music (`First`), and of the frames before it, from frame `b` on. -/
structure Run (sy : Syms) (m0 : Machine) (tc : TitleStart.Ctx) (q t0 u E : Nat) (S : Segs) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) where
  /-- every frame up to the castle entry: its kind and its counters, by the rule on one frame -/
  clock : Frames q E S
  /-- the segments of `plan` are in order -/
  order : S.Ok
  /-- the real frames of the run, numbered as `clock` numbers them, and the bounds of the searches of the two changes (`Route.Base`) -/
  base : Route.Base
  /-- from the press of Start on the title to frame 0: one condition on the machine after the press -/
  title : TitleStart.Begin sy tc base.seq base.inp
  /-- the digits of `clock` before frame 0 are those of the machine when frame 0 begins -/
  read₀ : (clock.s 0).t = timerOf tc.nm (base.seq 0)
  /-- the frame with the hurry-up music -/
  k : Nat
  hk : k ≤ E + 1
  on : hurryOn tc.nm (base.seq k) = true
  /-- the frame from which the frames before the music are in control -/
  b : Nat
  /-- frame `b` is frame 1 (its start is `Begin.start₁`); or the last frame of the first change, `b₁ − 1`, with the conditions of the first change (`HurryStart.Chg₁`: the
  fields of `Route.ChangesK` on it, `HurryStart.chg₁_of_changes`); or the last frame of the second change, `b₂ − 1`, with the conditions of both changes as `Route.Run` asks
  them (`Route.ChangesK`). Its start comes from the rows with tables of the change (`Run.startB`). -/
  start : b = 1 ∨ (b + 1 = base.b₁ sy ∧ HurryStart.Chg₁ sy m0 nm₁ d₁ base clock.kind) ∨
    (b + 1 = base.b₂ sy nmS m0 ∧ Route.ChangesK sy m0 nm₁ d₁ nm₂ nx₂ nmS base clock.kind S.e₁ S.c₂ S.e₂ S.c₃)
  /-- the first frame that starts the hurry-up music is not before `b` -/
  bLe : ∀ n, n < k → First tc.nm base.seq n → b ≤ n
  /-- **one instruction at a time**: no instruction of a frame from `b` up to the first frame that starts the music (that frame not counted) that begins with control writes the
  routine, the mode or the task by its address (`FrameKeep.CtlStore`). So each of these frames ends with control (`Run.startAt`, `HurryFrame.frame_ctl`). -/
  noStore : ∀ n, n < k → First tc.nm base.seq n → ∀ j, b ≤ j → j < n → controllable sy (base.seq j) = true →
    ∀ i, FrameKeep.CtlStore sy (PipeEntryRule.trace (base.seq j) (base.inp j) i) = false
  /-- **one frame at a time**: each instruction of these frames and of the music's frame meets `HurryFrame.CleanM` -/
  clean : ∀ n, n < k → First tc.nm base.seq n → ∀ j, b ≤ j → j ≤ n → ∀ i, HurryFrame.CleanAt sy tc.nm m0 (PipeEntryRule.trace (base.seq j) (base.inp j) i)
  /-- **one frame**: the digits of `clock` when the frame after the music's frame begins are not above those of the machine. A routine that runs over lowers the digits after the
  frame's start. -/
  below : ∀ n, n < k → First tc.nm base.seq n → (clock.s (n + 1)).t ≤ timerOf tc.nm (base.seq (n + 1))
  /-- the level change, after the castle entry -/
  L : Nat
  after : E < L

/-- **The checks on the ROM** that the theorem takes: the start from the title (`title`, `near`), the walk of the music's frame (`music`), the walk of a frame in control with the
stores of the routine, the mode and the task cut (`ctl`), the frames from control to the vertical pipe (`entry`), the two changes (`side`, `sideEnd`: the rows of
`SideChangeSound`, with the sound routine at `rt`, as `route_1_1` takes them; `room`, which holds the check of the first change), and the last rows with tables of the two
changes (`rows₁`, `rows₂`) -/
structure Checks (sy : Syms) (m0 : Machine) (tc : TitleStart.Ctx) (t0 u : Nat) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nm₂ nx₂ nmS : Names) (rt : StepWrites.Rt) : Prop where
  title : TitleStart.check sy tc t0 = true
  music : HurryFrame.checkOf sy tc.nm m0 u = true
  ctl : HurryFrame.ctlCheckOf sy tc.nm m0 = true
  near : nearCheck sy m0 tc = true
  entry : EntryKeep.Checks sy m0 d₁ tc
  side : ∃ es, SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122
  sideEnd : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt
  pause : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt
  room : Route.RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS
  rows₁ : HurryStart.rowsCheck₁ sy tc.nm m0 nm₁ d₁ (PipeTransition.entry m0) = true
  rows₂ : HurryStart.rowsCheck₂ sy tc.nm m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true

variable {sy : Syms} {m0 : Machine} {tc : TitleStart.Ctx} {q t0 u E : Nat} {S : Segs} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names}
  {rt : StepWrites.Rt}

/-- the machine when frame 0 begins: the timer shows `t0`, from the press of Start on the title. `hB` is the check on the ROM. -/
theorem Run.zero (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) : timerOf tc.nm (H.base.seq 0) = t0 :=
  (H.title.timer hB (H.base.next 0)).1

/-- no hurry-up music when frame 0 begins, from the press of Start on the title -/
theorem Run.quiet₀ (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) : hurryOn tc.nm (H.base.seq 0) = false :=
  quiet_of (H.title.zero hB (H.base.next 0))

/-- **Frame `b` begins in control as the walk needs it**: the old field `start`. Frame 1 from the press of Start on the title (`Begin.start₁`); the last frame of a change from
the rows of the change (`HurryStart.Chg₁.startLast`, `HurryStart.changes_startLast`). `hC` holds the checks on the ROM. -/
theorem Run.startB (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hC : Checks sy m0 tc t0 u nm₁ d₁ nm₂ nx₂ nmS rt) : HurryFrame.Start sy tc.nm m0 (H.base.seq H.b) := by
  rcases H.start with h | ⟨h, C⟩ | ⟨h, C⟩
  · rw [h]
    exact Or.inl (Begin.start₁ hC.title hC.near H.title (H.base.next 0)).1
  · have g := (C.startLast hC.room.pipe hC.title hC.entry hC.rows₁ H.title).2
    rwa [show H.base.b₁ sy - 1 = H.b by omega] at g
  · obtain ⟨_, hS⟩ := hC.side
    have g := (HurryStart.changes_startLast hS hC.sideEnd hC.pause hC.room hC.title hC.entry hC.rows₂ H.title C).2
    rwa [show H.base.b₂ sy nmS m0 - 1 = H.b by omega] at g

/-- **Frame `b` begins in control, or it ends with control**: frame 1 begins in control (`Begin.start₁`); the last frame of a change ends at the change's first control, by the
choice of `b₁` and `b₂` (`Route.firstWith_at`, `Route.ChangesBase.ctl₂`). `hC` holds the checks on the ROM. -/
theorem Run.startOrCtl (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hC : Checks sy m0 tc t0 u nm₁ d₁ nm₂ nx₂ nmS rt) :
    PipeWrites.FrameStart (HurryFrame.guardOf sy tc.nm m0) (PipeEntryRule.envOf m0) (H.base.seq H.b) ∨ controllable sy (H.base.seq (H.b + 1)) = true := by
  rcases H.start with h | ⟨h, C⟩ | ⟨h, C⟩
  · left
    rw [h]
    exact (Begin.start₁ hC.title hC.near H.title (H.base.next 0)).1
  · right
    rw [h]
    exact Route.firstWith_at (fun n => controllable sy (H.base.seq n)) _ H.base.dB C.ctlBy₁
  · right
    rw [h]
    exact C.ctl₂

/-- **The first frame that starts the hurry-up music begins in control as the walk needs it**: by induction from frame `b` over the frames before it. Each of them ends with
control: frame `b` by `Run.startOrCtl`, a frame that begins in control by the walk with the stores cut (`HurryFrame.frame_ctl`, with `noStore`). Then it ends at the start of a
frame in control (`HurryFrame.frame_startC`). `hC` holds the checks on the ROM. -/
theorem Run.startAt (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hC : Checks sy m0 tc t0 u nm₁ d₁ nm₂ nx₂ nmS rt) :
    ∀ n, n < H.k → First tc.nm H.base.seq n → HurryFrame.Start sy tc.nm m0 (H.base.seq n) := by
  intro n hn hF
  have hsn := H.bLe n hn hF
  have key : ∀ d, H.b + d ≤ n → HurryFrame.Start sy tc.nm m0 (H.base.seq (H.b + d)) ∧
      (PipeWrites.FrameStart (HurryFrame.guardOf sy tc.nm m0) (PipeEntryRule.envOf m0) (H.base.seq (H.b + d)) ∨
        controllable sy (H.base.seq (H.b + d + 1)) = true) := by
    intro d
    induction d with
    | zero => intro _; exact ⟨H.startB hC, H.startOrCtl hC⟩
    | succ d ih =>
      intro hd
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hw : FrameKeep.Watched (HurryFrame.watchOf (HurryFrame.placesOf sy tc.nm m0)) (H.base.seq (H.b + d)) := watched_of_off (hF.1 _ (by omega))
      have hk := H.clean n hn hF (H.b + d) (by omega) (by omega)
      have hctl : controllable sy (H.base.seq (H.b + d + 1)) = true := by
        rcases h2 with h2 | h2
        · rw [H.base.next]
          exact HurryFrame.frame_ctl hC.ctl h2 hw hk (H.noStore n hn hF (H.b + d) (by omega) (by omega) (HurryFrame.ctl_of_start hC.ctl h2))
        · exact h2
      rw [H.base.next] at hctl
      have e : H.base.seq (H.b + (d + 1)) = PipeTransition.frame (H.base.seq (H.b + d)) (H.base.inp (H.b + d)) := by
        rw [show H.b + (d + 1) = H.b + d + 1 by omega]
        exact H.base.next _
      rw [e]
      rcases HurryFrame.frame_startC hC.music h1 hw hk hctl with h | ⟨h, _⟩
      · exfalso
        apply h
        rw [← e]
        exact watched_of_off (hF.1 _ (by omega))
      · exact ⟨Or.inl h, Or.inl h⟩
  have := (key (n - H.b) (by omega)).1
  rwa [show H.b + (n - H.b) = n by omega] at this

/-- **The frame that starts the hurry-up music ends with the timer at `u` or less**: the old field `music`, from the walk of that frame (`HurryFrame.frame_music`).
`hC` holds the checks on the ROM. -/
theorem Run.music (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hC : Checks sy m0 tc t0 u nm₁ d₁ nm₂ nx₂ nmS rt) :
    ∀ n, n < H.k → First tc.nm H.base.seq n → timerOf tc.nm (H.base.seq (n + 1)) ≤ u := by
  intro n h1 hF
  have e := H.base.next n
  have h3 := hF.2
  rcases HurryFrame.frame_music hC.music (H.startAt hC n h1 hF) (watched_of_off (hF.1 n (Nat.le_refl _)))
      (H.clean n h1 hF n (H.bLe n h1 hF) (Nat.le_refl _)) with h | h
  · rw [← e] at h
    rw [off_of_watched h] at h3
    cases h3
  · rw [← e] at h
    exact h

/-- **The hurry-up music comes late**: the castle entry is at least `q · (t0 − u) − 3q` frames into the run -/
theorem Run.late (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hC : Checks sy m0 tc t0 u nm₁ d₁ nm₂ nx₂ nmS rt) (hq : 1 ≤ q) : q * (t0 - u) ≤ E + 3 * q := by
  obtain ⟨n, h1, h2, h3⟩ := first_turn (H.quiet₀ hC.title) H.k H.on
  have hF : First tc.nm H.base.seq n := ⟨h2, h3⟩
  have h4 := H.music hC n h1 hF
  have h5 := H.below n h1 hF
  have hk := H.hk
  exact H.clock.late hq H.order (H.read₀.trans (H.zero hC.title)) (n := n + 1) (by omega) (by omega)

/-- **1-2 does not start before frame 1748** in a run with the hurry-up music, when `q · (t0 − u)` is at least `1748 + 3q` -/
theorem Run.level_ge (H : Run sy m0 tc q t0 u E S nm₁ d₁ nm₂ nx₂ nmS) (hC : Checks sy m0 tc t0 u nm₁ d₁ nm₂ nx₂ nmS rt)
    (hq : 1 ≤ q) (hn : 1748 + 3 * q ≤ q * (t0 - u)) : 1748 ≤ H.L := by
  have h1 := H.late hC hq
  have h2 := H.after
  omega

end Smbrta.HurryMusic
