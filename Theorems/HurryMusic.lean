import Theorems.CastleToLevel
import Theorems.TitleStart
import Theorems.HurryFrame

/-!
# Runs with the hurry-up music

The game queues the hurry-up music on the frame on which the timer shows 100. A run in which this music plays fails the condition at the side pipe's entry
(`Route.Changes.entry₂`: the music bytes and `NoteLengthTblAdder`), so it is outside `Route.Run`. Here it gets its own bound. By the rule of `CastleToLevel.Frames`
on single frames, the timer shows `u` or less only after at least `q · (t0 − u) − 3q` frames (`CastleToLevel.Frames.late`), so the castle entry and the level change
come long after frame 1748. The link from the music to the timer is a walk of the one frame that starts the music (`HurryFrame.frame_music`): it ends with the timer at `u` or
less, if it is a frame in control as the walk needs it (`Run.start`, `Run.clean`). The timer and the music when frame 0 begins come from the press of Start on the title
(`TitleStart.Begin`). Page: `1-1/0-6-4-HurryMusic.md`.

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

/-- A run in which the hurry-up music plays at frame `k`, up to the castle entry `E`. `clock` is as `Route.Run.clock`; `seq n` is the machine when frame `n` begins.
The names are those of `tc`; `m0` is the reference machine at control of the walk. -/
structure Run (sy : Syms) (m0 : Machine) (tc : TitleStart.Ctx) (q t0 u E : Nat) (S : Segs) where
  /-- every frame up to the castle entry: its kind and its counters, by the rule on one frame -/
  clock : Frames q E S
  /-- the segments of `plan` are in order -/
  order : S.Ok
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = PipeTransition.frame (seq n) (inp n)
  /-- from the press of Start on the title to frame 0: one condition on the machine after the press -/
  title : TitleStart.Begin sy tc seq inp
  /-- the digits of `clock` before frame 0 are those of the machine when frame 0 begins -/
  read₀ : (clock.s 0).t = timerOf tc.nm (seq 0)
  /-- the frame with the hurry-up music -/
  k : Nat
  hk : k ≤ E + 1
  on : hurryOn tc.nm (seq k) = true
  /-- **one frame**: a frame that starts the hurry-up music begins in the idle loop, with the routine of control or of the entrance and the bytes that the digits routine adds 0 -/
  start : ∀ n, n < k → hurryOn tc.nm (seq n) = false → hurryOn tc.nm (seq (n + 1)) = true → HurryFrame.Start sy tc.nm m0 (seq n)
  /-- **one frame**: each instruction of that frame meets `HurryFrame.CleanM` -/
  clean : ∀ n, n < k → hurryOn tc.nm (seq n) = false → hurryOn tc.nm (seq (n + 1)) = true → ∀ j, HurryFrame.CleanAt sy tc.nm m0 (PipeEntryRule.trace (seq n) (inp n) j)
  /-- **one frame**: the digits of `clock` when the frame after it begins are not above those of the machine. A routine that runs over lowers the digits after the frame's start. -/
  below : ∀ n, n < k → hurryOn tc.nm (seq n) = false → hurryOn tc.nm (seq (n + 1)) = true → (clock.s (n + 1)).t ≤ timerOf tc.nm (seq (n + 1))
  /-- the level change, after the castle entry -/
  L : Nat
  after : E < L

variable {sy : Syms} {m0 : Machine} {tc : TitleStart.Ctx} {q t0 u E : Nat} {S : Segs}

/-- the machine when frame 0 begins: the timer shows `t0`, from the press of Start on the title. `hB` is the check on the ROM. -/
theorem Run.zero (H : Run sy m0 tc q t0 u E S) (hB : TitleStart.check sy tc t0 = true) : timerOf tc.nm (H.seq 0) = t0 :=
  (H.title.timer hB (H.next 0)).1

/-- no hurry-up music when frame 0 begins, from the press of Start on the title -/
theorem Run.quiet₀ (H : Run sy m0 tc q t0 u E S) (hB : TitleStart.check sy tc t0 = true) : hurryOn tc.nm (H.seq 0) = false :=
  quiet_of (H.title.zero hB (H.next 0))

/-- **The frame that starts the hurry-up music ends with the timer at `u` or less**: the old field `music`, from the walk of that frame (`HurryFrame.frame_music`).
`hM` is the walk's check on the ROM. -/
theorem Run.music (H : Run sy m0 tc q t0 u E S) (hM : HurryFrame.checkOf sy tc.nm m0 u = true) :
    ∀ n, n < H.k → hurryOn tc.nm (H.seq n) = false → hurryOn tc.nm (H.seq (n + 1)) = true → timerOf tc.nm (H.seq (n + 1)) ≤ u := by
  intro n h1 h2 h3
  have e := H.next n
  rcases HurryFrame.frame_music hM (H.start n h1 h2 h3) (watched_of_off h2) (H.clean n h1 h2 h3) with h | h
  · rw [← e] at h
    rw [off_of_watched h] at h3
    cases h3
  · rw [← e] at h
    exact h

/-- **The hurry-up music comes late**: the castle entry is at least `q · (t0 − u) − 3q` frames into the run -/
theorem Run.late (H : Run sy m0 tc q t0 u E S) (hB : TitleStart.check sy tc t0 = true) (hM : HurryFrame.checkOf sy tc.nm m0 u = true) (hq : 1 ≤ q) :
    q * (t0 - u) ≤ E + 3 * q := by
  obtain ⟨n, h1, h2, h3⟩ := first_on (H.quiet₀ hB) H.k H.on
  have h4 := H.music hM n h1 h2 h3
  have h5 := H.below n h1 h2 h3
  have hk := H.hk
  exact H.clock.late hq H.order (H.read₀.trans (H.zero hB)) (n := n + 1) (by omega) (by omega)

/-- **1-2 does not start before frame 1748** in a run with the hurry-up music, when `q · (t0 − u)` is at least `1748 + 3q` -/
theorem Run.level_ge (H : Run sy m0 tc q t0 u E S) (hB : TitleStart.check sy tc t0 = true) (hM : HurryFrame.checkOf sy tc.nm m0 u = true) (hq : 1 ≤ q)
    (hn : 1748 + 3 * q ≤ q * (t0 - u)) : 1748 ≤ H.L := by
  have h1 := H.late hB hM hq
  have h2 := H.after
  omega

end Smbrta.HurryMusic
