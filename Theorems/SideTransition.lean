import Theorems.PipeTransition
import Theorems.SidePipe

/-!
# The length of the change from the side pipe to control above ground

From the machine at the frame Mario enters the side pipe, every input of `inputs` gives one state per
frame, not controllable until frame `N`, controllable on frame `N`. The states are compared as in
`PipeTransition.lean`; that equal keys go on to equal keys is the hypothesis `GMerge`.

With no input and no hypothesis: other pixels of the mouth (written on the frame before the entry, so the
entry frame really runs), other fractions and speeds, a big Mario, real entries at other pixels, and real entries
on `D` consecutive frames. The one pixel with low nybble zero takes longer. Page: `SideTransition.md`.
-/

namespace Smbrta.SideTransition

open PipeTransition (frame run zeros expand inputs gchain GMerge no_input_of_chain first_control
  zero_mem_inputs run_append run_zeros_cons applyChange Change withSpeed speeds)

/-- Mario's `x` in pixels -/
def xOf (sy : Syms) (m : Machine) : Nat := (peek m sy.Player_X_Position).toNat

/-! ## The entry -/

/-- from the 1-1 start: the vertical pipe of the other theorem, a few frames of Left, Right to the floor, a jump onto the block -/
def onBlock : List UInt8 := PipeTransition.witness ++ expand [(0x00, 91), (0x02, 3), (0x01, 31), (0x81, 16)]

/-- walking off the block and against the pipe, up to the frame before the entry -/
def toPipe : List UInt8 := expand [(0x01, 118)]

/-- the input of the entry frame -/
def walkIn : UInt8 := 0x01

/-- the machine on the frame before the entry -/
def pre (m0 : Machine) : Machine := run (run m0 onBlock) toPipe

/-- the machine at the entry frame -/
def entry (m0 : Machine) : Machine := frame (pre m0) walkIn

/-- the input `i` on `m` enters the side pipe: control before, the pipe's routine after -/
def entersAt (sy : Syms) (m : Machine) (i : UInt8) : Bool :=
  controllable sy m && (peek (frame m i) sy.GameEngineSubroutine).toUInt16 == sy.EngSidePipe

/-! ## Equal machines stay equal -/

theorem byteArray_eq {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a; cases b; simp_all

/-- every field of the machine is equal -/
def sameM (a b : Machine) : Bool :=
  decide (a.a = b.a ∧ a.x = b.x ∧ a.y = b.y ∧ a.s = b.s ∧ a.p = b.p ∧ a.pc = b.pc ∧ a.cyc = b.cyc ∧
    a.ram.data = b.ram.data ∧ a.prg.data = b.prg.data ∧ a.prgMask = b.prgMask ∧ a.ppuCtrl = b.ppuCtrl ∧
    a.ppuMask = b.ppuMask ∧ a.vblank = b.vblank ∧ a.sprite0 = b.sprite0 ∧ a.nmiPending = b.nmiPending ∧
    a.fdot = b.fdot ∧ a.frame = b.frame ∧ a.pad = b.pad ∧ a.padShift = b.padShift ∧
    a.padStrobe = b.padStrobe ∧ a.halted = b.halted ∧ a.trk = b.trk ∧ a.trkRead.data = b.trkRead.data ∧
    a.trkWrite.data = b.trkWrite.data ∧ a.trkIO = b.trkIO)

theorem eq_of_sameM {a b : Machine} (h : sameM a b = true) : a = b := by
  have h' := of_decide_eq_true h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25⟩ := h'
  have e1 := byteArray_eq h8
  have e2 := byteArray_eq h9
  have e3 := byteArray_eq h23
  have e4 := byteArray_eq h24
  cases a
  cases b
  simp_all

/-- `n` frames of no input: not controllable on any of them, and the machine `b` at the end -/
def mergeTo (sy : Syms) (b : Machine) : Nat → Machine → Bool
  | 0, m => sameM m b
  | n + 1, m => !controllable sy (frame m 0) && mergeTo sy b n (frame m 0)

theorem mergeTo_run (sy : Syms) (b : Machine) :
    ∀ (n : Nat) (m : Machine), mergeTo sy b n m = true → run m (zeros n) = b
  | 0, _, h => eq_of_sameM h
  | n + 1, m, h => by
    simp only [mergeTo, Bool.and_eq_true] at h
    rw [run_zeros_cons]
    exact mergeTo_run sy b n (frame m 0) h.2

theorem mergeTo_none (sy : Syms) (b : Machine) :
    ∀ (n : Nat) (m : Machine), mergeTo sy b n m = true → ∀ k, 1 ≤ k → k ≤ n →
      controllable sy (run m (zeros k)) = false
  | 0, _, _, k, h1, h2 => by omega
  | n + 1, m, h, k, h1, h2 => by
    simp only [mergeTo, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [run_zeros_cons]
    cases j with
    | zero => exact h.1
    | succ i => exact mergeTo_none sy b n (frame m 0) h.2 (i + 1) (by omega) (by omega)

theorem run_zeros_add (m : Machine) (a b : Nat) :
    run m (zeros (a + b)) = run (run m (zeros a)) (zeros b) := by
  induction a generalizing m with
  | zero => simp [zeros, run]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, run_zeros_cons, ih, run_zeros_cons]

/-- what the merge gives: from the frame of the merge on, the machine is the machine of `e`, so control comes
when it comes from `e`, and the two machines are the same on frame `N` -/
theorem merged {sy : Syms} {e m : Machine} {T N : Nat} (hT : T < N)
    (h0 : ∀ k, 1 ≤ k → k ≤ N → controllable sy (run e (zeros k)) = decide (k = N))
    (h : mergeTo sy (run e (zeros T)) T m = true) :
    (∀ k, 1 ≤ k → k ≤ N → controllable sy (run m (zeros k)) = decide (k = N)) ∧
      run m (zeros N) = run e (zeros N) := by
  have h1 := mergeTo_run sy _ T m h
  have h2 := mergeTo_none sy _ T m h
  have hs : ∀ k, T ≤ k → run m (zeros k) = run e (zeros k) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [run_zeros_add, h1, ← run_zeros_add]
  refine ⟨fun k k1 k2 => ?_, hs N (by omega)⟩
  by_cases hk : k ≤ T
  · have hne : k ≠ N := by omega
    rw [h2 k k1 hk]
    simp [hne]
  · rw [hs k (by omega)]
    exact h0 k k1 k2

/-! ## Other entry states -/

/-- the pixel of the mouth whose low nybble is zero -/
def zeroX (sy : Syms) : Nat := 16 * SidePipe.column sy

/-- the mouth's other pixels: `x` with the right side in the mouth, without `zeroX` -/
def otherXs (sy : Syms) : List Nat :=
  ((List.range 16).map (SidePipe.xLo sy + ·)).filter (· != zeroX sy)

/-- the frame before the entry, overwritten so that the entry frame ends at the pixel `x` -/
def atX (sy : Syms) (p : Machine) (x : Nat) : Machine := poke p sy.Player_X_Position (x - 1).toUInt8

/-- the position's fractions tried -/
def fracs : List UInt8 := [80, 128, 240, 255]

/-- overwritten at the end of the entry frame: the fraction, the speed (with the moving direction, the facing and the stored
absolute speed), the speed's fraction, the running bytes -/
def moved (sy : Syms) : List Change :=
  fracs.map (fun f => [(sy.SprObject_X_MoveForce, f)]) ++
  (speeds sy).map (withSpeed sy) ++
  [[(sy.Player_X_MoveForce, 0xFF)], [(sy.RunningSpeed, 0)], [(sy.RunningTimer, 0)]]

/-- a big Mario, written on the frame before the entry -/
def bigBefore (sy : Syms) (p : Machine) : Machine := poke p sy.PlayerSize 0

/-! ## Real entries -/

/-- the input of the last frame of `routes` -/
def runIn : UInt8 := 0x41

/-- real runs from `onBlock`, up to the frame before the entry: Right with B, a jump, Left in the air to brake, Right with B
again. Each comes with the `d` of the pixel it enters at, `x₀ + d`. -/
def routes : List (List UInt8 × Nat) :=
  [(expand [(0x41, 40), (0xC1, 12), (0x02, 12), (0x00, 18), (0x41, 6)], 1),
   (expand [(0x41, 52), (0xC1, 3), (0x02, 15), (0x00, 7), (0x41, 10)], 2)]

/-- standing on the floor at the pipe's mouth, facing it -/
def stand : List UInt8 := expand [(0x01, 112), (0x00, 4)]

/-- from standing, up to the frame before the entry -/
def stepIn : List UInt8 := expand [(0x01, 4)]

def standing (m0 : Machine) : Machine := run (run m0 onBlock) stand

/-- `D` real runs: standing `d < D` more frames, then walking in. Each enters, and with no input control comes exactly `N`
frames after that. The entry falls on `D` consecutive frames. -/
def gridCheck (sy : Syms) (N : Nat) : Nat → Machine → Bool
  | 0, _ => true
  | d + 1, m =>
    let q := run m stepIn
    entersAt sy q walkIn && gchain (controllable sy) sy [] (fun _ => true) N (frame q walkIn) &&
      gridCheck sy N d (frame m 0)

theorem gridCheck_spec (sy : Syms) (N : Nat) :
    ∀ (D : Nat) (m : Machine), gridCheck sy N D m = true → ∀ d, d < D →
      entersAt sy (run (run m (zeros d)) stepIn) walkIn = true ∧
        gchain (controllable sy) sy [] (fun _ => true) N (frame (run (run m (zeros d)) stepIn) walkIn) = true
  | 0, _, _, d, hd => absurd hd (Nat.not_lt_zero d)
  | D + 1, m, h, d, hd => by
    simp only [gridCheck, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases d with
    | zero => exact ⟨h1, h2⟩
    | succ j =>
      rw [run_zeros_cons]
      exact gridCheck_spec sy N D (frame m 0) h3 j (Nat.lt_of_succ_lt_succ hd)

/-! ## All of it -/

/-- everything on the machines `o` (on the block), `s` (standing) and `p` (the frame before the entry). `N`: the length, `D`: the entry
frames, `T`: the frame all the overwritten runs have merged by, `Z`: the length at `zeroX`. -/
def checkOn (sy : Syms) (o s p : Machine) (N D T Z : Nat) : Bool :=
  let e := frame p walkIn
  let b := run e (zeros T)
  let z := frame (atX sy p (zeroX sy)) walkIn
  let g := frame (bigBefore sy p) walkIn
  entersAt sy p walkIn && xOf sy e == SidePipe.xLo sy &&
    gchain (controllable sy) sy inputs (fun _ => true) N e &&
    (otherXs sy).all (fun x =>
      let q := frame (atX sy p x) walkIn
      entersAt sy (atX sy p x) walkIn && xOf sy q == x && mergeTo sy b T q) &&
    entersAt sy (atX sy p (zeroX sy)) walkIn && xOf sy z == zeroX sy &&
      gchain (controllable sy) sy [] (fun _ => true) Z z &&
    (moved sy).all (fun c => mergeTo sy b T (applyChange e c)) &&
    entersAt sy (bigBefore sy p) walkIn && gchain (controllable sy) sy [] (fun _ => true) N g &&
    routes.all (fun r =>
      let q := run o r.1
      entersAt sy q runIn && xOf sy (frame q runIn) == SidePipe.xLo sy + r.2 &&
        gchain (controllable sy) sy [] (fun _ => true) N (frame q runIn)) &&
    gridCheck sy N D s

/-- the whole check from the 1-1 start. The run up to the block is shared. -/
def allCheck (sy : Syms) (m0 : Machine) (N D T Z : Nat) : Bool :=
  let o := run m0 onBlock
  checkOn sy o (run o stand) (run o toPipe) N D T Z

/-- control comes exactly on frame `n` after `m`, with no input -/
def ExactNoInput (sy : Syms) (m : Machine) (n : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → controllable sy (run m (zeros k)) = decide (k = n)

/-- What the theorem says. `N` is the length of the change, `D` the entry frames in `grid`, `Z` the length at `zeroX`. -/
structure Statement (sy : Syms) (m0 : Machine) (N D Z : Nat) : Prop where
  /-- the run enters the side pipe on its last frame, at the mouth's first pixel -/
  entered : entersAt sy (pre m0) walkIn = true ∧ xOf sy (entry m0) = SidePipe.xLo sy
  /-- every input of `inputs`, on every frame: control on frame `N`, not before. Hypothesis: `GMerge`. -/
  allInputs : GMerge (controllable sy) sy inputs N (entry m0) →
    ∀ w : List UInt8, (∀ i ∈ w, i ∈ inputs) → w.length = N →
      controllable sy (run (entry m0) w) = true ∧
        ∀ k, 1 ≤ k → k < N → controllable sy (run (entry m0) (w.take k)) = false
  /-- no input: control on frame `N`, not before. No hypothesis. -/
  noInput : ExactNoInput sy (entry m0) N
  /-- the other pixels of the mouth, written on the frame before the entry: it enters there, control on the same frame, and
  the machine on that frame is the same as from `entry` -/
  otherPixels : ∀ x ∈ otherXs sy,
    entersAt sy (atX sy (pre m0) x) walkIn = true ∧ xOf sy (frame (atX sy (pre m0) x) walkIn) = x ∧
      ExactNoInput sy (frame (atX sy (pre m0) x) walkIn) N ∧
      run (frame (atX sy (pre m0) x) walkIn) (zeros N) = run (entry m0) (zeros N)
  /-- the pixel with low nybble zero, written on the frame before the entry: it enters there, control exactly on frame `Z` -/
  zeroPixel : entersAt sy (atX sy (pre m0) (zeroX sy)) walkIn = true ∧
    xOf sy (frame (atX sy (pre m0) (zeroX sy)) walkIn) = zeroX sy ∧
    ExactNoInput sy (frame (atX sy (pre m0) (zeroX sy)) walkIn) Z
  /-- other fractions, speeds and running bytes at the end of the entry frame: control on the same frame, the same machine -/
  otherMoved : ∀ c ∈ moved sy, ExactNoInput sy (applyChange (entry m0) c) N ∧
    run (applyChange (entry m0) c) (zeros N) = run (entry m0) (zeros N)
  /-- a big Mario, written on the frame before the entry: control on the same frame -/
  otherBig : entersAt sy (bigBefore sy (pre m0)) walkIn = true ∧
    ExactNoInput sy (frame (bigBefore sy (pre m0)) walkIn) N
  /-- real runs entering at other pixels: control on the same frame -/
  otherRoutes : ∀ r ∈ routes,
    entersAt sy (run (run m0 onBlock) r.1) runIn = true ∧
      xOf sy (frame (run (run m0 onBlock) r.1) runIn) = SidePipe.xLo sy + r.2 ∧
      ExactNoInput sy (frame (run (run m0 onBlock) r.1) runIn) N
  /-- real runs: standing `d` more frames, then walking in, then no input: the same frame -/
  grid : ∀ d, d < D →
    entersAt sy (run (run (standing m0) (zeros d)) stepIn) walkIn = true ∧
      ExactNoInput sy (frame (run (run (standing m0) (zeros d)) stepIn) walkIn) N

theorem statement_of_check {sy : Syms} {m0 : Machine} {N D T Z : Nat} (hN : 1 ≤ N) (hT : T < N)
    (h : allCheck sy m0 N D T Z = true) : Statement sy m0 N D Z := by
  simp only [allCheck, checkOn, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have hE : ExactNoInput sy (entry m0) N := no_input_of_chain h3
  refine ⟨⟨h1, h2⟩, ?_, hE, ?_, ⟨h5, h6, no_input_of_chain h7⟩, ?_, ⟨h9, no_input_of_chain h10⟩, ?_, ?_⟩
  · intro hM w hw hl
    exact first_control h3 zero_mem_inputs hM w hw hl hN
  · intro x hx
    obtain ⟨⟨a, b⟩, c⟩ := h4 x hx
    obtain ⟨d, f⟩ := merged hT hE c
    exact ⟨a, b, d, f⟩
  · intro c hc
    exact merged hT hE (h8 c hc)
  · intro r hr
    obtain ⟨⟨a, b⟩, c⟩ := h11 r hr
    exact ⟨a, b, no_input_of_chain c⟩
  · intro d hd
    obtain ⟨a, c⟩ := gridCheck_spec sy N D _ h12 d hd
    exact ⟨a, no_input_of_chain c⟩

/-- frames of no input until control -/
def framesToControl (sy : Syms) (m : Machine) (limit : Nat := 600) : Option Nat := Id.run do
  let mut x := m
  for k in [0:limit] do
    x := frame x 0
    if controllable sy x then return some (k + 1)
  return none

end Smbrta.SideTransition
