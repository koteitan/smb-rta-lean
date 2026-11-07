import Theorems.PipeTransitionAll
import Theorems.SideTransition

/-!
# What decides the length of the change out of the side pipe

The change takes `A + B` frames: `A` frames of the pipe's timer and `B` more. The generic part is in `PipeTransitionAll.lean`: a tracked
run decides what every machine with the same registers and the same values on the bytes it read does, whatever its other bytes are
(`decided_of_check`, `end_of_check`). This file applies it from the state `T` when the timer has run out.

`Statement` and `every_entry` of `PipeTransitionAll.lean` are about the vertical pipe's entry, so this file has its own. Frames `1..A` are not
proved for every entry: `every_entry` takes them as hypotheses, and the check runs a list of entry states. Page: `1-1/d-2-1-SideTransitionAll.md`.
-/

namespace Smbrta.SideTransitionAll

open PipeTransition (frame run zeros Change applyChange)
open PipeTransitionAll (Names asmValue namesFrom enemies fill fireballs allDigits timeOne timeUp atPhase phaseOf norm SameCore
  decideCheck decided_of_check end_of_check EntryFacts entryCheck entryFacts_of_check ctlAt ctlAt_spec noneThen noneThen_none fixedOf
  overlay fold_size fold_in fold_out pattern_join track readSet unionOf ctlBytes lengthOf)
open SideTransition (onBlock toPipe walkIn pre entry entersAt routes runIn stand stepIn ExactNoInput)

/-! ## Names from the disassembly -/

/-- the names this file uses beyond those of `PipeTransitionAll.nameList` -/
def moreNames : List String := ["ScreenRight_PageLoc", "ChangeAreaTimer"]

/-- the names, from the text of the disassembly -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  namesFrom text ++ moreNames.filterMap fun n => (asmValue ls n).map (n, ·)

/-! ## Entry states -/

/-- entry states overwritten from the real one `e`. Each is run for the whole change, so there are fewer than for the vertical pipe, and most change
several bytes at once. -/
def scenes (sy : Syms) (nm : Names) (e : Machine) : List Change :=
  let g := "Goomba"
  let timers := fun (v : UInt8) => (List.range (sy.FrameTimersLast.toNat + 1)).map (fun i => (sy.Timers + i.toUInt16, v))
  [enemies sy nm e (List.replicate 5 g) 8,
   enemies sy nm e [g, g, g, g, g, "PowerUpObject"] 24,
   [(sy.PlayerSize, 0), (nm.ad "PlayerStatus", 2), (nm.ad "StarInvincibleTimer", 0xFF)],
   fireballs sy nm e ++ fill nm "Block_State" 2 0x11 ++ fill nm "Misc_State" 5 1,
   [(nm.ad "ScreenLeft_X_Pos", 0x50), (nm.ad "HorizontalScroll", 0x50), (nm.ad "ScrollLock", 0), (nm.ad "Player_Pos_ForScroll", 0x70),
    (nm.ad "Player_X_Scroll", 2)],
   timers 0xFF ++ [(sy.TimerControl, 0xFF), (nm.ad "IntervalTimerControl", 20), (nm.ad "FrameCounter", 0xFF)],
   timers 0 ++ [(nm.ad "IntervalTimerControl", 0), (nm.ad "FrameCounter", 0)],
   allDigits nm 9 ++ [(nm.ad "CoinTally", 99)],
   allDigits nm 0 ++ timeOne nm,
   fill nm "PseudoRandomBitReg" 7 0,
   fill nm "PseudoRandomBitReg" 7 0xFF,
   [(nm.ad "AreaMusicBuffer", 0), (nm.ad "EventMusicBuffer", 0), (nm.ad "Square1SoundBuffer", 0), (nm.ad "Square2SoundBuffer", 0),
    (nm.ad "NoiseSoundBuffer", 0), (nm.ad "AreaMusicQueue", 8), (nm.ad "Square2SoundQueue", 0x10), (nm.ad "NoiseSoundQueue", 1)],
   [(nm.ad "HalfwayPage", 1), (nm.ad "WarpZoneControl", 1)]]

/-- standing `step · j` more frames on the floor, then walking in, for `j < n`: the machine before the entry frame and its input -/
def standEntries (step : Nat) : Nat → Machine → List (Machine × UInt8)
  | 0, _ => []
  | n + 1, s => (run s stepIn, walkIn) :: standEntries step n (run s (zeros step))

def realStep : Nat := 5
def realCount : Nat := 4

/-- real entries, from the machine `o` on the block: the machine before the entry frame and its input -/
def realEntries (o : Machine) : List (Machine × UInt8) :=
  routes.map (fun r => (run o r.1, runIn)) ++ standEntries realStep realCount (run o stand)

/-- all the entries the check runs: the real one, the overwritten ones, the other real ones -/
def entries (sy : Syms) (nm : Names) (o e : Machine) : List Machine :=
  e :: ((scenes sy nm e).map (applyChange e) ++ (realEntries o).map (fun p => frame p.1 p.2))

/-- the screen not on the first page, written on the frame before the entry, so that the entry frame really runs: the screen and Mario on
another page of the same parity, and the screen's byte alone -/
def pageBefore (sy : Syms) (nm : Names) : List Change :=
  [[(nm.ad "ScreenLeft_PageLoc", 2), (nm.ad "ScreenRight_PageLoc", 3), (sy.Player_PageLoc, 2)],
   [(nm.ad "ScreenLeft_PageLoc", 0xFF)]]

/-- the entry from `p` overwritten by `c` -/
def entryWith (p : Machine) (c : Change) : Machine := frame (applyChange p c) walkIn

/-- overwritten states that frames take longer on: six objects close together -/
def lagScenes (sy : Syms) (nm : Names) (e : Machine) : List Change :=
  [enemies sy nm e (List.replicate 6 "Goomba") 0,
   enemies sy nm e (List.replicate 6 "HammerBro") 4]

/-- the entry `e` with the change's timer overwritten at the end of the entry frame -/
def timerAt (nm : Names) (e : Machine) (v : Nat) : Machine := poke e (nm.ad "ChangeAreaTimer") v.toUInt8

/-- the time-up flag: a longer change -/
def expired (nm : Names) : Change := [(nm.ad "GameTimerExpiredFlag", 1)]

/-! ## The state when the timer has run out -/

/-- the places in the frame that the runs start from: a dot at the frame boundary and two parities. Unlike above ground, the increment bit is off:
the room writes no column of the level. -/
def places (T : Machine) (nm : Names) : List Machine :=
  (List.range 10).flatMap fun fd => (List.range 2).flatMap fun c => (List.range 2).map fun f => atPhase T nm fd c f false

/-- the numbers of the check: `A`, `B`; `S` the frames the shorter timer takes; `X` the length with the time-up flag; `lagL` the lengths of `lagScenes`;
`timerL` the values of the overwritten timer. They come from the generated proof. -/
structure Nums where
  A : Nat
  B : Nat
  S : Nat
  X : Nat
  lagL : List Nat
  timerL : List Nat

/-- how many frames the state with the game timer at 0 is followed -/
def timeUpFrames : Nat := 300

/-- the whole check, on the machines `o` (on the block), `p` (the frame before the entry), `e` (the entry), `T` (when the timer has run out). -/
def checkOn (sy : Syms) (nm : Names) (R Rvar RE : List Nat) (n : Nums) (o p e T : Machine) : Bool :=
  let Rfix := fixedOf R Rvar
  entersAt sy p walkIn &&
  decideCheck sy RE (n.A + n.B) (norm e) &&
  (places T nm).all (decideCheck sy R n.B) &&
  (entries sy nm o e).all (entryCheck sy nm R Rfix n.B T n.A) &&
  (realEntries o).all (fun q => entersAt sy q.1 q.2 && peek q.1 (nm.ad "ScreenLeft_PageLoc") == 0) &&
  peek p (nm.ad "ScreenLeft_PageLoc") == 0 &&
  (pageBefore sy nm).all (fun c => entersAt sy (applyChange p c) walkIn && ctlAt sy (fun _ => true) (n.S + n.B) (entryWith p c)) &&
  n.timerL.all (fun v => ctlAt sy (fun _ => true) (n.B + v) (timerAt nm e v)) &&
  (lagScenes sy nm e).length == n.lagL.length &&
  ((lagScenes sy nm e).zip n.lagL).all (fun q => decide (n.A + n.B < q.2) && ctlAt sy (fun _ => true) q.2 (applyChange e q.1)) &&
  ctlAt sy (fun _ => true) n.X (applyChange e (expired nm)) &&
  noneThen sy (fun _ => true) timeUpFrames (applyChange e (timeUp nm))

/-- the check from the 1-1 start. The run up to the entry is shared. -/
def allCheck (sy : Syms) (m0 : Machine) (nm : Names) (R Rvar RE : List Nat) (n : Nums) : Bool :=
  let o := run m0 onBlock
  let p := run o toPipe
  let e := frame p walkIn
  checkOn sy nm R Rvar RE n o p e (run e (zeros n.A))

/-- the state of the real entry when the timer has run out -/
def cutOf (m0 : Machine) (A : Nat) : Machine := run (entry m0) (zeros A)

/-- what the theorem says -/
structure Statement (sy : Syms) (m0 : Machine) (nm : Names) (R Rvar RE : List Nat) (n : Nums) : Prop where
  /-- the real entry enters, with the screen on the first page -/
  entered : entersAt sy (pre m0) walkIn = true ∧ peek (pre m0) (nm.ad "ScreenLeft_PageLoc") = 0
  /-- From the real entry: every machine with its registers and its values on `RE` gets control on frame `A + B`, not before. -/
  atEntry : ∀ M, SameCore (norm (entry m0)) M → (∀ i ∈ RE, i < 2048 → M.ram.get! i = (norm (entry m0)).ram.get! i) →
    ExactNoInput sy M (n.A + n.B)
  /-- **Decided by `R`**: for each place in the frame, every machine with the registers of the state when the timer has run out and the same
  values on `R` gets control `B` frames later, not before. The other bytes of RAM are arbitrary. -/
  decided : ∀ fd c f, fd < 10 → c < 2 → f < 2 → ∀ M, SameCore (atPhase (cutOf m0 n.A) nm fd c f false) M →
    (∀ i ∈ R, i < 2048 → M.ram.get! i = (atPhase (cutOf m0 n.A) nm fd c f false).ram.get! i) →
    ExactNoInput sy M n.B
  /-- and when control comes, it has the value of the reference in every byte of `R` and in every byte the reference's run wrote -/
  ends : ∀ fd c f, fd < 10 → c < 2 → f < 2 → ∀ M, SameCore (atPhase (cutOf m0 n.A) nm fd c f false) M →
    (∀ i ∈ R, i < 2048 → M.ram.get! i = (atPhase (cutOf m0 n.A) nm fd c f false).ram.get! i) →
    ∀ i, i < 2048 → (i ∈ R ∨ (run (track (atPhase (cutOf m0 n.A) nm fd c f false)) (zeros n.B)).trkWrite.get! i ≠ 0) →
      (run M (zeros n.B)).ram.get! i = (run (track (atPhase (cutOf m0 n.A) nm fd c f false)) (zeros n.B)).ram.get! i
  /-- each entry that was run: control exactly on frame `A + B`, and the state when the timer has run out is of the form that `decided` needs -/
  entryStates : ∀ m ∈ entries sy nm (run m0 onBlock) (entry m0), EntryFacts sy nm R (fixedOf R Rvar) (cutOf m0 n.A) n.A n.B m
  /-- the other real entries are real: the input enters the pipe, with the screen on the first page -/
  real : ∀ q ∈ realEntries (run m0 onBlock), entersAt sy q.1 q.2 = true ∧ peek q.1 (nm.ad "ScreenLeft_PageLoc") = 0
  /-- **A shorter change.** The screen not on the first page, written on the frame before the entry: it enters, and control comes exactly on frame
  `S + B`. -/
  shorter : ∀ c ∈ pageBefore sy nm, entersAt sy (applyChange (pre m0) c) walkIn = true ∧
    ExactNoInput sy (entryWith (pre m0) c) (n.S + n.B)
  /-- the timer overwritten at the end of the entry frame: control comes `B` frames after it runs out -/
  timer : ∀ v ∈ n.timerL, ExactNoInput sy (timerAt nm (entry m0) v) (n.B + v)
  /-- six objects close together: frames run over, control comes later -/
  lag : ∀ q ∈ (lagScenes sy nm (entry m0)).zip n.lagL, n.A + n.B < q.2 ∧ ExactNoInput sy (applyChange (entry m0) q.1) q.2
  /-- the time-up flag: control exactly on frame `X` -/
  flag : ExactNoInput sy (applyChange (entry m0) (expired nm)) n.X
  /-- the game timer at 0: no control -/
  died : ∀ k, 1 ≤ k → k ≤ timeUpFrames → controllable sy (run (applyChange (entry m0) (timeUp nm)) (zeros k)) = false

theorem statement_of_check {sy : Syms} {m0 : Machine} {nm : Names} {R Rvar RE : List Nat} {n : Nums} (hB : 1 ≤ n.B)
    (h : allCheck sy m0 nm R Rvar RE n = true) : Statement sy m0 nm R Rvar RE n := by
  have h' : checkOn sy nm R Rvar RE n (run m0 onBlock) (pre m0) (entry m0) (cutOf m0 n.A) = true := h
  simp only [checkOn, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h5'⟩, h6⟩, h7⟩, _⟩, h9⟩, h10⟩, h11⟩ := h'
  have hplace : ∀ fd c f, fd < 10 → c < 2 → f < 2 → decideCheck sy R n.B (atPhase (cutOf m0 n.A) nm fd c f false) = true := by
    intro fd c f hfd hc hf
    refine h3 _ ?_
    simp only [places, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨fd, hfd, c, hc, f, hf, rfl⟩
  refine ⟨⟨h1, h5'⟩, fun M hs ha => decided_of_check h2 hs ha, ?_, ?_, ?_, h5, ?_, ?_, ?_, ctlAt_spec _ _ h10, noneThen_none _ _ h11⟩
  · intro fd c f hfd hc hf M hs ha
    exact decided_of_check (hplace fd c f hfd hc hf) hs ha
  · intro fd c f hfd hc hf M hs ha
    exact end_of_check (hplace fd c f hfd hc hf) hs ha
  · intro m hm
    exact entryFacts_of_check hB (h4 m hm)
  · intro c hc
    obtain ⟨a, b⟩ := h6 c hc
    exact ⟨a, ctlAt_spec _ _ b⟩
  · intro v hv
    exact ctlAt_spec _ _ (h7 v hv)
  · intro q hq
    have := h9 q hq
    simp only [decide_eq_true_eq] at this
    exact ⟨this.1, ctlAt_spec _ _ this.2⟩

/-! ## Every entry, under assumptions -/

theorem phaseOf_off {T t : Machine} {nm : Names} (hb : (t.a &&& 4 != 0) = false) :
    phaseOf T nm t = atPhase T nm t.fdot (t.cyc % 2) (t.frame % 2) false := by
  simp only [phaseOf, hb]

/-- **Every entry, under assumptions.** Let `M` be any machine, `t` its state `A` frames later. If `M` has no control in those frames (`hA`), if `t`
has the registers of `T` at some place in the frame with the increment bit off (`hd`, `hb`, `hc`), if `t` has `T`'s values in the bytes `Rfix` (`hf`), and if putting
`T`'s values into the bytes `Rvar` changes nothing about control (`hv`), then `M` gets control exactly on frame `A + B`. -/
theorem every_entry {sy : Syms} {m0 : Machine} {nm : Names} {R Rvar RE : List Nat} {n : Nums} (hB : 1 ≤ n.B)
    (S : Statement sy m0 nm R Rvar RE n) (M : Machine)
    (hA : ∀ k, 1 ≤ k → k ≤ n.A → controllable sy (run M (zeros k)) = false)
    (hd : (run M (zeros n.A)).fdot < 10)
    (hb : ((run M (zeros n.A)).a &&& 4 != 0) = false)
    (hc : SameCore (phaseOf (cutOf m0 n.A) nm (run M (zeros n.A))) (run M (zeros n.A)))
    (hf : ∀ i ∈ fixedOf R Rvar, (run M (zeros n.A)).ram.get! i = (phaseOf (cutOf m0 n.A) nm (run M (zeros n.A))).ram.get! i)
    (hv : ∀ k, 1 ≤ k → k ≤ n.B → controllable sy (run (run M (zeros n.A)) (zeros k)) =
      controllable sy (run (overlay Rvar (phaseOf (cutOf m0 n.A) nm (run M (zeros n.A))) (run M (zeros n.A))) (zeros k))) :
    ExactNoInput sy M (n.A + n.B) := by
  refine pattern_join hB hA ?_
  intro k h1 h2
  rw [hv k h1 h2]
  generalize hT : run M (zeros n.A) = t at hd hb hc hf
  rw [phaseOf_off hb] at hc hf ⊢
  have hcs : t.cyc % 2 < 2 := Nat.mod_lt _ (by decide)
  have hfs : t.frame % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsize : (overlay Rvar (atPhase (cutOf m0 n.A) nm t.fdot (t.cyc % 2) (t.frame % 2) false) t).ram.size = 2048 := by
    show (Rvar.foldl _ t.ram).size = 2048
    rw [fold_size]
    exact hc.size
  refine S.decided t.fdot (t.cyc % 2) (t.frame % 2) hd hcs hfs _ ?_ ?_ k h1 h2
  · exact ⟨hc.a, hc.x, hc.y, hc.s, hc.p, hc.pc, hc.prg, hc.prgMask, hc.ppuCtrl, hc.ppuMask, hc.vblank, hc.sprite0,
      hc.nmiPending, hc.fdot, hc.padShift, hc.padStrobe, hc.halted, hc.cycLe, hc.cycEven, hc.frameLe, hc.frameEven, hc.trk, hsize⟩
  · intro i hi hs
    show (Rvar.foldl _ t.ram).get! i = (atPhase (cutOf m0 n.A) nm t.fdot (t.cyc % 2) (t.frame % 2) false).ram.get! i
    by_cases hin : i ∈ Rvar
    · exact fold_in Rvar _ i hin hs _ hc.size
    · rw [fold_out Rvar _ i hin]
      refine hf i ?_
      simp only [fixedOf, List.mem_filter]
      refine ⟨hi, ?_⟩
      simpa using hin

/-- the assumptions of `every_entry` on a machine, as a check for a program: no control for `A` frames, then the form that `every_entry` needs, and control after `B`
frames with the state's own values and with `T`'s values on `Rvar` -/
def assumptionsHold (sy : Syms) (nm : Names) (R Rvar : List Nat) (T : Machine) (A B : Nat) (M : Machine) : Bool :=
  noneThen sy (fun t =>
    PipeTransitionAll.cutOK nm (fixedOf R Rvar) T t && !(t.a &&& 4 != 0) && ctlAt sy (fun _ => true) B t &&
      ctlAt sy (fun _ => true) B (overlay Rvar (phaseOf T nm t) t)) A M

/-- what the bound on the route needs: no control before frame `N` -/
theorem no_control_before {sy : Syms} {M : Machine} {N : Nat} (h : ExactNoInput sy M N) :
    ∀ k, 1 ≤ k → k < N → controllable sy (run M (zeros k)) = false := by
  intro k h1 h2
  rw [h k h1 (Nat.le_of_lt h2)]
  simp [Nat.ne_of_lt h2]

/-! ## Finding the sets, for the generated proof -/

/-- `R`: everything the runs read, and the bytes of `controllable` -/
def computeR (sy : Syms) (nm : Names) (m0 : Machine) (A B : Nat) : List Nat :=
  let o := run m0 onBlock
  let e := frame (run o toPipe) walkIn
  let T := run e (zeros A)
  let cuts := (entries sy nm o e).map fun m => norm (run m (zeros A))
  unionOf (ctlBytes sy :: (places T nm ++ cuts).map (readSet B))

/-- `Rvar`: the bytes of `R` in which the state of some entry differs from `T` when the timer has run out -/
def computeRvar (sy : Syms) (nm : Names) (m0 : Machine) (R : List Nat) (A : Nat) : List Nat :=
  let o := run m0 onBlock
  let e := frame (run o toPipe) walkIn
  let T := run e (zeros A)
  unionOf ((entries sy nm o e).map fun m =>
    let t := run m (zeros A)
    R.filter fun i => t.ram.get! i != (phaseOf T nm t).ram.get! i)

/-- `RE`: everything the run from the real entry reads, and the bytes of `controllable` -/
def computeRE (sy : Syms) (m0 : Machine) (N : Nat) : List Nat :=
  unionOf [ctlBytes sy, readSet N (norm (entry m0))]

/-- the numbers of the check, found by running: `S` is what is left of the change with the screen not on the first page, without `B`. The two values of
the overwritten timer are the smallest and `S`. -/
def numsOf (sy : Syms) (nm : Names) (m0 : Machine) (A B : Nat) : Nums :=
  let e := entry m0
  let len := fun (m : Machine) => lengthOf sy m 800 0
  let S := len (entryWith (pre m0) ((pageBefore sy nm).headD [])) - B
  { A, B, S, X := len (applyChange e (expired nm)), lagL := (lagScenes sy nm e).map (fun c => len (applyChange e c)), timerL := [1, S] }

end Smbrta.SideTransitionAll
