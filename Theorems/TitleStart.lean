import Theorems.SideChangeEnd
import Theorems.CastleToLevel
import Theorems.SurfaceFrames

/-!
# From Start on the title screen to control

Frame 0 of the route is the frame before the first control of 1-1. `Route.Run` asked of the machine when frame 0 begins that the timer shows `t0` and that the interval timers'
phase is 2, and `HurryMusic.Run` that the hurry-up music is not on. `Route.Pipe` asked that the speed is 0 at control. Here these come from one condition on the machine after the frame
on which Start is pressed on the title screen (`Begin.press`). The bytes that the run from there reads before it writes them are those of a reference machine; the bytes that differ
from run to run are free (`freeNames`: the frame counter, the interval timers' phase, the random bytes, the timers, the top score, the number of players, ...).

The game then clears RAM, draws the screens and waits on a timer that ticks with the phase, so that the phase at control does not depend on the phase at the press. An abstract
machine (`TaintRun`, with the tick across the frame's end of `SideChangeEnd`) follows every machine of the condition. A search finds a set of frame-start states closed under one frame
(`closure`). Its states come in two groups: the far ones, whose frames end in a state of the set without control, and the near ones, whose frames end with control and the speed 0.
The near states know the timer, the phase and the music bytes. No frame of the game core before control has Start (`Begin.noPause`): Start there would pause the game.

The search is no part of the proof: `check` walks every state of the set and of its tables, and `Begin.zero` and `Begin.still` follow from it. There is no game data in this file.
Page: `1-1/0-5-3-TitleStart.md`.
-/

namespace Smbrta.TitleStart

open PipeTransition (frame)
open PipeTransitionAll (Names asmValue)
open TaintRun
open SideChangeEnd (xwalk xsearch noStartPad noStart mOf knowsAd ExitCond exitStarts exitStartsOK canon)

/-! ## The names -/

/-- the names this file reads -/
def nameList : List String :=
  ["GameTimerDisplay", "IntervalTimerControl", "EventMusicQueue", "EventMusicBuffer", "NoteLengthTblAdder", "TimeRunningOutMusic", "FrameCounter", "GamePauseStatus",
   "GamePauseTimer", "ScreenRoutineTask", "ScreenTimer", "DisableScreenFlag", "AreaParserTaskNum", "VRAM_Buffer1_Offset", "PseudoRandomBitReg", "NumberOfPlayers",
   "TopScoreDisplay", "ScoreAndCoinDisplay", "Timers", "JoypadBitMask", "HorizontalScroll", "VerticalScroll", "SprShuffleAmtOffset", "SprDataOffset",
   "Mirror_PPU_CTRL_REG1"]

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

/-- a RAM index of a name -/
def adI (nm : Names) (n : String) : Nat := ((nm.ad n) &&& 0x7FF).toNat

/-- the bytes that differ between real runs at the press: a name, an offset and a number of bytes. The frame counter, the phase, the random bytes, the timers and the sprites'
shuffle depend on the frame of the press; the number of players, the timers and the screen's control byte on the buttons pressed on the title; the top score and the bytes after the
scores on a reset; the scroll and the pad's mask on the title's frames. -/
def freeNames : List (String × Nat × Nat) :=
  [("FrameCounter", 0, 1), ("IntervalTimerControl", 0, 1), ("PseudoRandomBitReg", 0, 7), ("NumberOfPlayers", 0, 1), ("TopScoreDisplay", 0, 6),
   ("ScoreAndCoinDisplay", 24, 3), ("Timers", 0, 36), ("JoypadBitMask", 0, 2), ("HorizontalScroll", 0, 1), ("VerticalScroll", 0, 1),
   ("SprShuffleAmtOffset", 0, 1), ("SprDataOffset", 0, 15), ("Mirror_PPU_CTRL_REG1", 0, 1)]

def freeOf (nm : Names) : List Nat := SideChangeBound.bytesOf nm freeNames

/-- the bytes the search keeps apart -/
def keepOf (sy : Syms) (nm : Names) : List Nat :=
  [(sy.OperMode &&& 0x7FF).toNat, (sy.OperMode_Task &&& 0x7FF).toNat, (sy.GameEngineSubroutine &&& 0x7FF).toNat] ++
    ["ScreenRoutineTask", "ScreenTimer", "IntervalTimerControl", "DisableScreenFlag", "AreaParserTaskNum", "VRAM_Buffer1_Offset", "GamePauseStatus", "GamePauseTimer"].map (adI nm)

/-! ## The reference machine and the known bytes -/

/-- from power-on, Start on frame `kk`: the machine after that frame -/
def pressAt (cart : Machine) (kk : Nat) : Machine := Id.run do
  let mut m := powerOn cart 0
  for _ in [0:kk] do m := runFrame m 0
  return runFrame m 0x08

/-- the bytes that the run from `x` with no input reads before it writes them, up to control or `n` frames -/
def readsOf (sy : Syms) (x : Machine) (n : Nat) : List Nat := Id.run do
  let z := ByteArray.mk (Array.replicate 2048 0)
  let mut m := { x with trk := true, trkRead := z, trkWrite := z, trkIO := false }
  for _ in [0:n] do
    if controllable sy m then break
    m := runFrame m 0
  return (List.range 2048).filter fun i => m.trkRead.get! i != 0

/-- the bytes that the condition at the press knows: those read before written, but the free ones -/
def knownOf (sy : Syms) (nm : Names) (x : Machine) : List Nat :=
  let f := freeOf nm
  (readsOf sy x 400).filter fun i => !f.contains i

/-- the state just before control: the timer shows `t0`, the phase is 2, the music queue, its buffer and the tempo's adder are 0 -/
def zeroBytes (nm : Names) (t0 : Nat) : List (Nat × UInt8) :=
  let a := nm.ad "GameTimerDisplay"
  [((a &&& 0x7FF).toNat, (t0 / 100).toUInt8), (((a + 1) &&& 0x7FF).toNat, (t0 / 10 % 10).toUInt8), (((a + 2) &&& 0x7FF).toNat, (t0 % 10).toUInt8), (adI nm "IntervalTimerControl", 2),
   (adI nm "EventMusicQueue", 0), (adI nm "EventMusicBuffer", 0), (adI nm "NoteLengthTblAdder", 0)]

/-- what the check is told -/
structure Ctx where
  nm : Names
  /-- the machine after the press, and the bytes known of it -/
  x : Machine
  K : List Nat

/-- the environment: the pad is not known, and the frame counter is read in pieces by its low bits -/
def Ctx.E (c : Ctx) : Env :=
  { prg := c.x.prg, mask := c.x.prgMask, pad := AB.top, D := [], splits := [(adI c.nm "FrameCounter", 7)] }

def Ctx.gps (c : Ctx) : Nat := adI c.nm "GamePauseStatus"
/-- the speed, as a RAM index -/
def vI (sy : Syms) : Nat := (sy.Player_X_Speed &&& 0x7FF).toNat

/-- the context from the ROM: the reference press on frame `kk` of the title -/
def ctxOf (sy : Syms) (nm : Names) (cart : Machine) (kk : Nat) : Ctx :=
  let x := pressAt cart kk
  { nm, x, K := knownOf sy nm x }

/-! ## The condition at the press -/

/-- the game core: the only frames on which Start pauses before control -/
def inCore (sy : Syms) (m : Machine) : Bool := (peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore

/-- a state that knows it is in the game core -/
def coreK (sy : Syms) (S : AS) : Bool := knowsAd S sy.OperMode_Task && inCore sy (mOf S)

/-- the environment of a group: no Start in the game core -/
def envOf (c : Ctx) (core : Bool) : Env := if core then { c.E with pad := noStartPad } else c.E

/-! ## The search: no part of the proof -/

/-- a frame's end as a frame-start state: at the idle loop only the bytes matter -/
def toStart (E : Env) (B : AS) : AS :=
  if isIdle E B.pc (E.prg.get! (B.pc &&& E.mask).toNat) then canon B else { B with k := 0, spent := false, log := [] }

/-- what the search finds: the set, and for each state whether its frame can end with control, and the states of its frame for the tables -/
structure Found where
  set : Array AS := #[]
  keys : Std.HashMap Nat Nat := {}
  near : Array Bool := #[]
  /-- the states that the last search of each state's frame went through -/
  outs : Array (Array AS) := #[]
  walks : Nat := 0
  deriving Inhabited

/-- a frame's end goes into the set: joined into the state of the same key -/
def Found.add (sy : Syms) (c : Ctx) (f : Found) (queue : Array Nat) (B' : AS) : Found × Array Nat :=
  let k := keyOf c.E (keepOf sy c.nm) B'
  match f.keys[k]? with
  | some j =>
    if B'.le f.set[j]! then (f, queue)
    else ({ f with set := f.set.set! j (f.set[j]!.join B') }, if queue.contains j then queue else queue.push j)
  | none => ({ f with keys := f.keys.insert k f.set.size, set := f.set.push B', near := f.near.push false, outs := f.outs.push #[] }, queue.push f.set.size)

/-- the search for the set: each state's frame, its ends joined into the state of the same key -/
partial def closure (sy : Syms) (c : Ctx) : Found := Id.run do
  let E := c.E
  let mut f : Found := {}
  let mut queue : Array Nat := #[]
  for S in exitStarts c.x c.K c.gps do
    (f, queue) := f.add sy c queue S
  while !queue.isEmpty && f.walks < 20000 do
    let i := queue[0]!
    queue := queue.extract 1 queue.size
    let S := f.set[i]!
    let e := envOf c (coreK sy S)
    let X := xsearch e (aRows e).toArray (keepOf sy c.nm) [S]
    let nr := X.ends.any fun B => actl sy B != some false
    f := { f with near := f.near.set! i nr, outs := f.outs.set! i X.out, walks := f.walks + 1 }
    for B in X.ends do
      if actl sy B == some false then
        (f, queue) := f.add sy c queue (toStart E B)
  return f

/-! ## The groups and the check -/

/-- states of the set that share an environment and an end, with the table of their frames -/
structure Grp where
  core : Bool
  R : List AS
  t : Array AS
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray

def grpCfg (sy : Syms) (c : Ctx) (g : Grp) : Cfg :=
  { E := envOf c g.core, ops := (aRows (envOf c g.core)).toArray, sy, K := 1, keep := keepOf sy c.nm, t := g.t, idx := g.idx, cut := g.cut }

/-- a group and its table, from the states the search went through -/
def grpOf (sy : Syms) (c : Ctx) (core : Bool) (R : List AS) (t : Array AS) : Grp :=
  let e := envOf c core
  let P := t.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyOf e (keepOf sy c.nm) A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { core, R, t, idx := P.1, cut := P.2.1 }

/-- all the states of the set, with candidates by key -/
structure All where
  a : Array AS
  idx : Std.HashMap Nat (List Nat)

def allOf (sy : Syms) (c : Ctx) (l : List AS) : All :=
  let a := l.toArray
  { a, idx := (List.range a.size).foldl (fun (h : Std.HashMap Nat (List Nat)) i => let k := keyOf c.E (keepOf sy c.nm) a[i]!; h.insert k (i :: h.getD k [])) {} }

/-- a state of the set covers `B` -/
def All.covers (sy : Syms) (c : Ctx) (A : All) (B : AS) : Bool :=
  (A.idx.getD (keyOf c.E (keepOf sy c.nm) B) []).any fun i =>
    match A.a[i]? with
    | some D => B.le D
    | none => false

/-- at the end of a far frame: no control, and a state of the set -/
def finFar (sy : Syms) (c : Ctx) (A : All) (B : AS) : Bool := actl sy B == some false && !B.rk && A.covers sy c ({ B with k := 0 } : AS)

/-- at the end of a near frame: control, and the speed is 0 -/
def finNear (sy : Syms) (B : AS) : Bool := actl sy B == some true && knownIs B (vI sy, 0)

/-- a group passes: its states start a frame, they know the game core if the group asks for no Start, and every walk of its states and its table succeeds -/
def grpOK (sy : Syms) (c : Ctx) (g : Grp) (fin : AS → Bool) : Bool :=
  g.R.all (fun S => S.k == 0 && !S.rk && (!g.core || coreK sy S)) && g.t.all (xwalk (grpCfg sy c g) fin walkFuel) && g.R.all (xwalk (grpCfg sy c g) fin walkFuel)

/-- the set, in three groups: far and not in the game core, far and in the game core, near -/
structure Sets where
  farP : Grp
  farC : Grp
  near : Grp

def setsOf (sy : Syms) (c : Ctx) : Sets :=
  let f := closure sy c
  let all := (List.range f.set.size).map fun i => (f.set[i]!, f.near[i]!, f.outs[i]!)
  let pick := fun (nr core : Bool) => all.filter fun p => p.2.1 == nr && coreK sy p.1 == core
  let grp := fun (nr core : Bool) => grpOf sy c core ((pick nr core).map (·.1)) ((pick nr core).foldl (fun t p => t ++ p.2.2) #[])
  { farP := grp false false, farC := grp false true, near := grp true true }

def Sets.all (s : Sets) : List AS := s.farP.R ++ s.farC.R ++ s.near.R

/-- **The check.** The start states are in the set; each group passes; the near states know the bytes of `zeroBytes`. -/
def checkOf (sy : Syms) (c : Ctx) (t0 : Nat) (s : Sets) : Bool :=
  let A := allOf sy c s.all
  decide (t0 < 1000) && decide (c.gps < 2048) && decide (vI sy < 2048) && exitStartsOK c.x c.K &&
    (exitStarts c.x c.K c.gps).all (fun S => s.all.any fun D => S.le D) &&
    grpOK sy c s.farP (finFar sy c A) && grpOK sy c s.farC (finFar sy c A) && grpOK sy c s.near (finNear sy) &&
    s.near.R.all (fun S => (zeroBytes c.nm t0).all (knownIs S))

/-- **The check**, with the set that the search finds -/
def check (sy : Syms) (c : Ctx) (t0 : Nat) : Bool := checkOf sy c t0 (setsOf sy c)

/-! ## What the check gives -/

/-- **The run from the press to frame 0.** `tm n` is the machine `n` frames after the press, and `tm pre` the machine when frame 0 of the route begins, so that the next frame
ends with the first control. -/
structure Begin (sy : Syms) (c : Ctx) (seq : Nat → Machine) (inp : Nat → UInt8) where
  /-- the frames from the press to frame 0 -/
  pre : Nat
  tm : Nat → Machine
  ti : Nat → UInt8
  next : ∀ n, tm (n + 1) = frame (tm n) (ti n)
  /-- **one state**: the machine after the frame of the press, in the idle loop, with the bytes `K` of the reference machine -/
  press : ExitCond c.E c.x c.K c.gps (tm 0)
  /-- frame 0 of the route -/
  atZero : tm pre = seq 0 ∧ ti pre = inp 0
  /-- no Start on the frames of the game core before control -/
  noPause : ∀ n, n ≤ pre → inCore sy (tm n) = true → noStart (ti n) = true
  /-- frame 0 is the frame before the first control after the press -/
  first : ∀ n, n ≤ pre → controllable sy (tm n) = false
  ctl : controllable sy (seq 1) = true

section
variable {sy : Syms} {c : Ctx} {t0 : Nat} {s : Sets}

open SideChangeEnd (sim_pad sim_unpad two_le peek_of_known exit_cover xframe_of_walk)

/-- a machine is in a state of the list, when its frame begins -/
def In (c : Ctx) (R : List AS) (m : Machine) : Prop := ∃ S ∈ R, Sim c.E (m.frame, 2) S m

theorem E_pad (c : Ctx) : c.E.pad = AB.top := rfl

/-- **One frame from a state of a group.** -/
theorem grp_frame {g : Grp} {fin : AS → Bool} (h : grpOK sy c g fin = true) {S : AS} (hS : S ∈ g.R) {m : Machine}
    (hs : Sim c.E (m.frame, 2) S m) {i : UInt8} (hi : g.core = true → noStart i = true) :
    ∃ B, fin B = true ∧ Sim c.E (m.frame, 2) B (frame m i) := by
  simp only [grpOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs1 : Sim (grpCfg sy c g).E (m.frame, 2) S { m with pad := smbToPad i } := by
    show Sim (envOf c g.core) (m.frame, 2) S { m with pad := smbToPad i }
    unfold envOf
    split
    · rename_i hcore
      apply sim_pad hs
      have hn := hi hcore
      have e : smbToPad i &&& 0x08 = 0 := by simpa [noStart] using hn
      show smbToPad i &&& 0x08 = 0 &&& 0x08
      rw [e]
      rfl
    · exact { hs with pad := by rw [E_pad c]; exact mem_top _ }
  have hk : S.k = 0 := by
    have := List.all_eq_true.1 h1 S hS
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1
  obtain ⟨_, B, g2, _, g4⟩ := xframe_of_walk (C := grpCfg sy c g) (F := (m.frame, 2)) h2 rfl two_le (List.all_eq_true.1 h3 S hS) hs1
  have g4' : Sim c.E (m.frame, 2) B (frame m i) := by
    have e4 : Sim (envOf c g.core) (m.frame, 2) B (frame m i) := g4
    unfold envOf at e4
    split at e4
    · exact sim_unpad (E_pad c) e4
    · exact e4
  exact ⟨B, g2, g4'⟩

/-- a group in the game core: its machines are in the game core -/
theorem core_of_K {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (h : coreK sy S = true) : inCore sy m = true := by
  simp only [coreK, Bool.and_eq_true] at h
  simp only [inCore] at h ⊢
  rw [peek_of_known hs h.1]
  exact h.2

/-- the pad of a group: no Start where the group is in the game core -/
theorem grp_pad {g : Grp} {fin : AS → Bool} (h : grpOK sy c g fin = true) {S : AS} (hS : S ∈ g.R) {m : Machine} {F : Nat × UInt8}
    (hs : Sim c.E F S m) {i : UInt8} (hn : inCore sy m = true → noStart i = true) : g.core = true → noStart i = true := by
  intro hc
  simp only [grpOK, Bool.and_eq_true] at h
  have := List.all_eq_true.1 h.1.1 S hS
  simp only [Bool.and_eq_true, hc, Bool.not_true, Bool.false_or] at this
  exact hn (core_of_K hs this.2)

theorem covers_ok {A : All} {B : AS} (h : A.covers sy c B = true) : ∃ D ∈ A.a, B.le D = true := by
  unfold All.covers at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    exact ⟨D, he ▸ Array.getElem_mem hi, h2⟩
  · cases h2

/-- a far frame ends without control, in a state of the set -/
theorem far_frame {g : Grp} (h : grpOK sy c g (finFar sy c (allOf sy c s.all)) = true) {S : AS} (hS : S ∈ g.R) {m : Machine}
    (hs : Sim c.E (m.frame, 2) S m) {i : UInt8} (hi : g.core = true → noStart i = true) :
    controllable sy (frame m i) = false ∧ In c s.all (frame m i) := by
  obtain ⟨B, hf, hb⟩ := grp_frame h hS hs hi
  simp only [finFar, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hf
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨actl_ok sy hb h1, ?_⟩
  obtain ⟨D, hD, hle⟩ := covers_ok h3
  have hbase : Sim c.E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
    refine { hb with fr := ?_, rkv := ?_ }
    · show (frame m i).frame = (frame m i).frame + 0
      rfl
    · intro hr2
      have : B.rk = true := hr2
      rw [h2] at this
      cases this
  have hD' : D ∈ s.all := by simpa [allOf] using hD
  exact ⟨D, hD', sim_le hle hbase⟩

/-- a near frame ends with control and the speed 0 -/
theorem near_frame {g : Grp} (h : grpOK sy c g (finNear sy) = true) {S : AS} (hS : S ∈ g.R) {m : Machine}
    (hs : Sim c.E (m.frame, 2) S m) {i : UInt8} (hi : g.core = true → noStart i = true) :
    controllable sy (frame m i) = true ∧ (frame m i).ram.get! (vI sy) = 0 := by
  obtain ⟨B, hf, hb⟩ := grp_frame h hS hs hi
  simp only [finNear, Bool.and_eq_true, beq_iff_eq] at hf
  exact ⟨actl_ok sy hb hf.1, sim_known hb hf.2⟩

/-- the parts of the check -/
structure Parts (sy : Syms) (c : Ctx) (t0 : Nat) (s : Sets) : Prop where
  small : t0 < 1000
  starts : exitStartsOK c.x c.K = true
  inSet : ∀ S ∈ exitStarts c.x c.K c.gps, ∃ D ∈ s.all, S.le D = true
  farP : grpOK sy c s.farP (finFar sy c (allOf sy c s.all)) = true
  farC : grpOK sy c s.farC (finFar sy c (allOf sy c s.all)) = true
  near : grpOK sy c s.near (finNear sy) = true
  zero : ∀ S ∈ s.near.R, ∀ p ∈ zeroBytes c.nm t0, knownIs S p = true

theorem parts_of_check (h : checkOf sy c t0 s = true) : Parts sy c t0 s := by
  simp only [checkOf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, _⟩, _⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h4, h5, h6, h7, h8, h9⟩

/-- the machine after the press is in the set -/
theorem in_press (P : Parts sy c t0 s) {m : Machine} (h : ExitCond c.E c.x c.K c.gps m) : In c s.all m := by
  obtain ⟨S, hS, hs⟩ := exit_cover P.starts (E_pad c) h
  obtain ⟨D, hD, hle⟩ := P.inSet S hS
  exact ⟨D, hD, sim_le hle hs⟩

/-- **One frame in the set.** A frame from a far state ends in the set without control. A frame from a near state ends with control and the speed 0. -/
theorem step (P : Parts sy c t0 s) {m : Machine} (h : In c s.all m) {i : UInt8} (hn : inCore sy m = true → noStart i = true) :
    (controllable sy (frame m i) = false ∧ In c s.all (frame m i)) ∨
    (In c s.near.R m ∧ controllable sy (frame m i) = true ∧ (frame m i).ram.get! (vI sy) = 0) := by
  obtain ⟨S, hS, hs⟩ := h
  simp only [Sets.all, List.mem_append] at hS
  rcases hS with (hS | hS) | hS
  · exact Or.inl (far_frame P.farP hS hs (grp_pad P.farP hS hs hn))
  · exact Or.inl (far_frame P.farC hS hs (grp_pad P.farC hS hs hn))
  · exact Or.inr ⟨⟨S, hS, hs⟩, near_frame P.near hS hs (grp_pad P.near hS hs hn)⟩

variable {seq : Nat → Machine} {inp : Nat → UInt8}

/-- every machine from the press to frame 0 is in the set -/
theorem Begin.inSet (P : Parts sy c t0 s) (B : Begin sy c seq inp) : ∀ n, n ≤ B.pre → In c s.all (B.tm n)
  | 0, _ => in_press P B.press
  | n + 1, h => by
    rcases step P (Begin.inSet P B n (by omega)) (B.noPause n (by omega)) with ⟨_, h2⟩ | ⟨_, h2, _⟩
    · rw [B.next]
      exact h2
    · have := B.first (n + 1) h
      rw [B.next, h2] at this
      cases this

/-- frame 0 begins in a near state, and frame 1 with the speed 0 -/
theorem Begin.near (P : Parts sy c t0 s) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    In c s.near.R (seq 0) ∧ (seq 1).ram.get! (vI sy) = 0 := by
  have h0 := B.inSet P B.pre (Nat.le_refl _)
  have hc := B.ctl
  rw [hn, ← B.atZero.1, ← B.atZero.2] at hc ⊢
  rcases step P h0 (B.noPause B.pre (Nat.le_refl _)) with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · rw [h1] at hc
    cases hc
  · exact ⟨h1, h3⟩

/-- **The machine when frame 0 begins**: the bytes of `zeroBytes` -/
theorem Begin.zero (hc : check sy c t0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    ∀ p ∈ zeroBytes c.nm t0, (seq 0).ram.get! p.1 = p.2 := by
  have P := parts_of_check hc
  obtain ⟨⟨S, hS, hs⟩, _⟩ := B.near P hn
  intro p hp
  exact sim_known hs (P.zero S hS p hp)

/-- **The speed at control is 0** -/
theorem Begin.still (hc : check sy c t0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    SurfaceFrames.vOf sy (seq 1) = 0 := by
  have h := (B.near (parts_of_check hc) hn).2
  unfold SurfaceFrames.vOf peek
  rw [show ((sy.Player_X_Speed &&& 0x7FF).toNat) = vI sy from rfl, h]
  decide

theorem u8 (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8]
  omega

/-- the timer of a machine with the bytes of `zeroBytes` -/
theorem timer_of {nm : Names} {m : Machine} (ht : t0 < 1000) (h : ∀ p ∈ zeroBytes nm t0, m.ram.get! p.1 = p.2) : CastleToLevel.timerOf nm m = t0 := by
  have h1 := h _ (List.mem_cons_self)
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [CastleToLevel.timerOf, peek]
  rw [h1, h2, h3, u8 _ (by omega), u8 _ (by omega), u8 _ (by omega)]
  omega

/-- the phase of a machine with the bytes of `zeroBytes` -/
theorem phase_of {nm : Names} {m : Machine} (h : ∀ p ∈ zeroBytes nm t0, m.ram.get! p.1 = p.2) : CastleToLevel.phaseOf nm m = 2 := by
  have h4 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  simp only [CastleToLevel.phaseOf, peek]
  exact (congrArg UInt8.toNat h4).trans rfl

/-- **The timer and the phase when frame 0 begins** -/
theorem Begin.timer (hc : check sy c t0 = true) (B : Begin sy c seq inp) (hn : seq 1 = frame (seq 0) (inp 0)) :
    CastleToLevel.timerOf c.nm (seq 0) = t0 ∧ CastleToLevel.phaseOf c.nm (seq 0) = 2 :=
  ⟨timer_of (parts_of_check hc).small (B.zero hc hn), phase_of (B.zero hc hn)⟩

end

end Smbrta.TitleStart
