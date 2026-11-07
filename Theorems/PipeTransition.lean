import Smbrta.Segment

/-!
# The length of the change from the vertical pipe to the bonus room

From the machine at the frame Mario enters the pipe, every input of a set (`inputs`: all buttons
except Start and Select) gives one state per frame, not controllable until frame `N`, controllable
on frame `N`. The states are compared by `key`. That equal keys go on to equal keys (`Merge`) is a
hypothesis of the theorem, not checked here. Page: `PipeTransition.md`.
-/

namespace Smbrta.PipeTransition

/-! ## Frames -/

/-- one real frame, the input in the game layout (A B Sel St U D L R = bit7..0) -/
def frame (m : Machine) (i : UInt8) : Machine := runFrame m (smbToPad i)

/-- real frames, one per input -/
def run (m : Machine) (w : List UInt8) : Machine := w.foldl frame m

/-- every subset of A, B, Up, Down, Left, Right (opposite directions included); no Start, no Select -/
def inputs : List UInt8 := (List.range 64).map fun (n : Nat) =>
  let i : UInt8 := n.toUInt8
  ((i &&& 0x30) <<< 2) ||| (i &&& 0x0F)

/-- RAM without `SavedJoypadBits` and without the bits of `JoypadBitMask` other than Start and Select.
These two bytes are the only ones that differ between the inputs during the change. Equal values here
give equal `ramKey`, which also blanks other bytes that echo the buttons. -/
def ramEcho (sy : Syms) (m : Machine) : Array UInt8 :=
  let r := m.ram.data
  let a := (sy.SavedJoypadBits &&& 0x7FF).toNat
  let b := (sy.JoypadBitMask &&& 0x7FF).toNat
  (r.set! a 0).set! b (r[b]! &&& 0x30)

/-- the fields of the machine other than RAM. Left out: `pad` (`runFrame` overwrites it), the ROM
(`prg`, `prgMask`, no instruction writes them), the tracking fields (off in real frames). -/
def regs (m : Machine) : List Nat :=
  [m.a.toNat, m.x.toNat, m.y.toNat, m.s.toNat, m.p.toNat, m.pc.toNat, m.cyc, m.fdot, m.frame,
    m.ppuCtrl.toNat, m.ppuMask.toNat, m.padShift.toNat,
    if m.vblank then 1 else 0, if m.sprite0 then 1 else 0, if m.nmiPending then 1 else 0,
    if m.padStrobe then 1 else 0, if m.halted then 1 else 0]

/-- what the check compares; `done` is the event the check waits for -/
def gkey (done : Machine → Bool) (sy : Syms) (m : Machine) : Array UInt8 × List Nat × Bool :=
  (ramEcho sy m, regs m, done m)

/-! ## The check: one state per frame -/

/-- `gchain done sy ins goal n m`: for `n` frames from `m`, each input of `ins` gives the key that no input
gives; the state after no input is controllable only on the last frame; `goal` holds at the end.
With `ins = []` it only follows no input. -/
def gchain (done : Machine → Bool) (sy : Syms) (ins : List UInt8) (goal : Machine → Bool) : Nat → Machine → Bool
  | 0, m => goal m
  | n + 1, m =>
    let m' := frame m 0
    let k := gkey done sy m'
    ins.all (fun i => decide (gkey done sy (frame m i) = k)) &&
      done m' == (n == 0) && gchain done sy ins goal n m'

/-- `k` frames of no input -/
def zeros (k : Nat) : List UInt8 := List.replicate k 0

theorem run_append (m : Machine) (a b : List UInt8) : run m (a ++ b) = run (run m a) b := by
  simp [run, List.foldl_append]

theorem run_zeros_succ (m : Machine) (k : Nat) : run m (zeros (k + 1)) = frame (run m (zeros k)) 0 := by
  rw [zeros, List.replicate_succ', run_append]
  rfl

theorem run_zeros_cons (m : Machine) (k : Nat) : run m (zeros (k + 1)) = run (frame m 0) (zeros k) := by
  simp [run, zeros, List.replicate_succ]

/-- what `chain` says: along no input, on frame `k + 1`, every input gives the key of no input, and
control comes exactly on the last frame -/
theorem chain_spec {done : Machine → Bool} (sy : Syms) (ins : List UInt8) (goal : Machine → Bool) :
    ∀ (n : Nat) (m : Machine), gchain done sy ins goal n m = true → ∀ k, k < n →
      (∀ i ∈ ins, gkey done sy (frame (run m (zeros k)) i) = gkey done sy (run m (zeros (k + 1)))) ∧
        done (run m (zeros (k + 1))) = decide (k + 1 = n)
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, m, h, k, hk => by
    simp only [gchain, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases k with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [run_zeros_succ]
        exact h1 i hi
      · rw [run_zeros_succ]
        show done (frame m 0) = _
        rw [h2]
        by_cases hn : n = 0 <;> simp [hn]
    | succ j =>
      have hj : j < n := Nat.lt_of_succ_lt_succ hk
      have h4 := chain_spec sy ins goal n (frame m 0) h3 j hj
      rw [run_zeros_cons m j, run_zeros_cons m (j + 1)]
      refine ⟨h4.1, ?_⟩
      rw [h4.2]
      simp

/-- the goal holds after `n` frames of no input -/
theorem chain_goal {done : Machine → Bool} (sy : Syms) (ins : List UInt8) (goal : Machine → Bool) :
    ∀ (n : Nat) (m : Machine), gchain done sy ins goal n m = true → goal (run m (zeros n)) = true
  | 0, _, h => h
  | n + 1, m, h => by
    simp only [gchain, Bool.and_eq_true] at h
    rw [run_zeros_cons]
    exact chain_goal sy ins goal n (frame m 0) h.2

/-- With no input nothing else is needed: control comes exactly on frame `n`. -/
theorem no_input_of_chain {done : Machine → Bool} {sy : Syms} {ins : List UInt8} {goal : Machine → Bool} {n : Nat} {m : Machine}
    (h : gchain done sy ins goal n m = true) :
    ∀ k, 1 ≤ k → k ≤ n → done (run m (zeros k)) = decide (k = n) := by
  intro k h1 h2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (chain_spec sy ins goal n m h j (by omega)).2

/-! ## The hypothesis, and what the check gives with it -/

/-- The hypothesis: two states reached from `m` after the same number of frames, with equal keys, go
on to equal keys under the same input. Such states differ only in `SavedJoypadBits`, in the bits of
`JoypadBitMask` other than Start and Select, and in `pad`. The check does not prove this. -/
def GMerge (done : Machine → Bool) (sy : Syms) (ins : List UInt8) (n : Nat) (m : Machine) : Prop :=
  ∀ a b : List UInt8, (∀ i ∈ a, i ∈ ins) → (∀ i ∈ b, i ∈ ins) → a.length = b.length → a.length < n →
    gkey done sy (run m a) = gkey done sy (run m b) →
      ∀ i ∈ ins, gkey done sy (frame (run m a) i) = gkey done sy (frame (run m b) i)

section
variable {done : Machine → Bool} {sy : Syms} {ins : List UInt8} {goal : Machine → Bool} {n : Nat} {m : Machine}

/-- every input sequence of at most `n` frames ends at the key of no input -/
theorem key_of_chain (hc : gchain done sy ins goal n m = true) (h0 : (0 : UInt8) ∈ ins)
    (hM : GMerge done sy ins n m) :
    ∀ w : List UInt8, (∀ i ∈ w, i ∈ ins) → w.length ≤ n →
      gkey done sy (run m w) = gkey done sy (run m (zeros w.length)) := by
  suffices h : ∀ (L : Nat) (w : List UInt8), w.length = L → (∀ i ∈ w, i ∈ ins) → w.length ≤ n →
      gkey done sy (run m w) = gkey done sy (run m (zeros w.length)) from fun w => h w.length w rfl
  intro L
  induction L with
  | zero =>
    intro w hL _ _
    rw [List.length_eq_zero_iff.1 hL]
    rfl
  | succ L ih =>
    intro w hL hw hl
    obtain ⟨v, i, rfl⟩ : ∃ v i, w = v ++ [i] := by
      rcases List.eq_nil_or_concat w with h | ⟨v, i, h⟩
      · simp [h] at hL
      · exact ⟨v, i, by simpa using h⟩
    have hv : ∀ j ∈ v, j ∈ ins := fun j hj => hw j (by simp [hj])
    have hi : i ∈ ins := hw i (by simp)
    have hvL : v.length = L := by simpa using hL
    have hl' : v.length < n := by simp at hl; omega
    have hz : ∀ j ∈ zeros v.length, j ∈ ins := by
      intro j hj
      rw [zeros, List.mem_replicate] at hj
      rw [hj.2]
      exact h0
    have h1 := hM v (zeros v.length) hv hz (by simp [zeros]) hl' (ih v hvL hv (Nat.le_of_lt hl')) i hi
    have h2 := (chain_spec sy ins goal n m hc v.length hl').1 i hi
    rw [run_append, List.length_append, List.length_singleton]
    exact h1.trans h2

/-- control comes exactly on frame `n`, for every input sequence of `ins` -/
theorem control_of_chain (hc : gchain done sy ins goal n m = true) (h0 : (0 : UInt8) ∈ ins)
    (hM : GMerge done sy ins n m) (w : List UInt8) (hw : ∀ i ∈ w, i ∈ ins) (h1 : 1 ≤ w.length)
    (h2 : w.length ≤ n) :
    done (run m w) = decide (w.length = n) := by
  have hk := key_of_chain hc h0 hM w hw h2
  have hc' : done (run m w) = done (run m (zeros w.length)) :=
    congrArg (fun x : Array UInt8 × List Nat × Bool => x.2.2) hk
  rw [hc']
  exact no_input_of_chain hc w.length h1 h2 |>.trans (by simp)

/-- the same for a sequence of exactly `n` frames: not on its proper prefixes, on the whole of it -/
theorem first_control (hc : gchain done sy ins goal n m = true) (h0 : (0 : UInt8) ∈ ins)
    (hM : GMerge done sy ins n m) (w : List UInt8) (hw : ∀ i ∈ w, i ∈ ins) (hl : w.length = n)
    (hn : 1 ≤ n) :
    done (run m w) = true ∧
      ∀ k, 1 ≤ k → k < n → done (run m (w.take k)) = false := by
  refine ⟨?_, ?_⟩
  · rw [control_of_chain hc h0 hM w hw (by omega) (by omega), hl]
    simp
  · intro k h1 h2
    have hlen : (w.take k).length = k := by
      rw [List.length_take]
      omega
    have ht : ∀ i ∈ w.take k, i ∈ ins := fun i hi => hw i (List.mem_of_mem_take hi)
    rw [control_of_chain hc h0 hM (w.take k) ht (by omega) (by omega), hlen]
    simp
    omega

end

/-- the change into the room waits for control -/
abbrev key (sy : Syms) := gkey (controllable sy) sy
abbrev chain (sy : Syms) := gchain (controllable sy) sy
abbrev Merge (sy : Syms) := GMerge (controllable sy) sy

theorem zero_mem_inputs : (0 : UInt8) ∈ inputs :=
  List.mem_map.2 ⟨0, List.mem_range.2 (by decide), by decide⟩

/-! ## The entry -/

/-- runs of equal inputs -/
def expand (l : List (UInt8 × Nat)) : List UInt8 := l.flatMap fun (b, n) => List.replicate n b

/-- from the 1-1 start: right with B held, A over each obstacle, up to the takeoff for the fourth pipe -/
def approach : List UInt8 :=
  expand [(0x41, 129), (0xC1, 6), (0x41, 45), (0xC1, 30), (0x41, 68), (0xC1, 30), (0x41, 38), (0xC1, 12),
    (0x41, 57)]

/-- the jump onto the pipe, with Down held from the top of the jump on -/
def fall : List UInt8 := expand [(0xC1, 16), (0x45, 8)]

/-- the input of the frame he lands on the pipe's top: Right, B and Down -/
def landIn : UInt8 := 0x45

/-- the witness: he enters at top speed, on the landing frame -/
def witness : List UInt8 := approach ++ fall ++ [landIn]

/-- the machine at the entry frame -/
def entry (m0 : Machine) : Machine := run m0 witness

/-- the input `i` on `m` enters the pipe: control before, the pipe's routine after -/
def entersAt (sy : Syms) (m : Machine) (i : UInt8) : Bool :=
  controllable sy m &&
    (peek (frame m i) sy.GameEngineSubroutine).toUInt16 == sy.EngVerticalPipe

/-! ## Other entry states -/

/-- a jump onto the pipe with Left in the air, then stopped in the pipe's window: he stands there -/
def stop : List UInt8 := expand [(0x41, 4), (0xC1, 30), (0x41, 8), (0x02, 8), (0x00, 2)]

/-- standing in the window after the run -/
def standing (m0 : Machine) : Machine := run m0 (approach ++ stop)

/-- Down alone -/
def downIn : UInt8 := 0x04

/-- `D` real runs: standing `d < D` more frames and then pressing Down enters the pipe, and with no input
control comes exactly `N` frames after that. The entry falls on `D` different frames. -/
def standCheck (sy : Syms) (N : Nat) : Nat → Machine → Bool
  | 0, _ => true
  | d + 1, m =>
    entersAt sy m downIn && chain sy [] (fun _ => true) N (frame m downIn) &&
      standCheck sy N d (frame m 0)

theorem standCheck_spec (sy : Syms) (N : Nat) :
    ∀ (D : Nat) (m : Machine), standCheck sy N D m = true → ∀ d, d < D →
      entersAt sy (run m (zeros d)) downIn = true ∧
        chain sy [] (fun _ => true) N (frame (run m (zeros d)) downIn) = true
  | 0, _, _, d, hd => absurd hd (Nat.not_lt_zero d)
  | D + 1, m, h, d, hd => by
    simp only [standCheck, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases d with
    | zero => exact ⟨h1, h2⟩
    | succ j =>
      rw [run_zeros_cons]
      exact standCheck_spec sy N D (frame m 0) h3 j (Nat.lt_of_succ_lt_succ hd)

/-- bytes to overwrite -/
abbrev Change := List (UInt16 × UInt8)

def applyChange (m : Machine) (c : Change) : Machine := c.foldl (fun m p => poke m p.1 p.2) m

/-- the left end of the column of the pipe's left half, in pixels -/
def pipeX (sy : Syms) : Nat := 16 * (sy.PipeColumnByte.toNat / 16)

/-- the pipe's window: one foot on each half of the pipe -/
def windowXs (sy : Syms) : List UInt8 :=
  (List.range (2 * sy.FeetAdderX.toNat - 16 + 1)).map fun d =>
    (pipeX sy + 16 - sy.FeetAdderX.toNat + d).toUInt8

/-- Mario moving at the speed byte `v`: speed, stored absolute speed, moving direction, facing -/
def withSpeed (sy : Syms) (v : UInt8) : Change :=
  let right := v < 0x80
  let dir : UInt8 := if right then 1 else 2
  [(sy.Player_X_Speed, v), (sy.Player_XSpeedAbsolute, if right then v else 0 - v),
    (sy.Player_MovingDir, dir), (sy.PlayerFacingDir, dir)]

/-- half and all of the running top speed, both ways, and 0 -/
def speeds (sy : Syms) : List UInt8 :=
  let t := sy.RunTopSpeed.toNat
  let h : UInt8 := (t / 2).toUInt8
  let f : UInt8 := t.toUInt8
  [h, 0 - h, f, 0 - f, 0]

/-- other positions and speeds on the pipe: every pixel of the window, speeds, the fractions, the
running bytes -/
def moved (sy : Syms) : List Change :=
  (windowXs sy).map (fun x => [(sy.Player_X_Position, x)]) ++
  (speeds sy).map (withSpeed sy) ++
  [[(sy.SprObject_X_MoveForce, 0xFF)], [(sy.Player_X_MoveForce, 0xFF)],
   [(sy.RunningSpeed, 0)], [(sy.RunningTimer, 0)]]

/-- a big Mario -/
def big (sy : Syms) : Change := [(sy.PlayerSize, 0)]

/-- with no input: from each changed entry state, control comes exactly on frame `N`; for the moved
ones the state then has the key of the unchanged run -/
def changesCheck (sy : Syms) (N : Nat) (e : Machine) : Bool :=
  let b := key sy (run e (zeros N))
  (moved sy).all (fun c => chain sy [] (fun m => decide (key sy m = b)) N (applyChange e c)) &&
    chain sy [] (fun _ => true) N (applyChange e (big sy))

/-! ## All of it -/

/-- the whole check. The run up to the takeoff is shared. -/
def allCheck (sy : Syms) (m0 : Machine) (N D : Nat) : Bool :=
  let a := run m0 approach
  let p := run a fall
  let e := frame p landIn
  entersAt sy p landIn && chain sy inputs (fun _ => true) N e && changesCheck sy N e &&
    standCheck sy N D (run a stop)

/-- What the theorem says. `N` is the length of the change. -/
structure Statement (sy : Syms) (m0 : Machine) (N D : Nat) : Prop where
  /-- the witness enters the pipe on its last frame -/
  entered : entersAt sy (run m0 (approach ++ fall)) landIn = true
  /-- every input of `inputs`, on every frame: control on frame `N`, not before. Hypothesis: `Merge`. -/
  allInputs : Merge sy inputs N (entry m0) →
    ∀ w : List UInt8, (∀ i ∈ w, i ∈ inputs) → w.length = N →
      controllable sy (run (entry m0) w) = true ∧
        ∀ k, 1 ≤ k → k < N → controllable sy (run (entry m0) (w.take k)) = false
  /-- no input: control on frame `N`, not before. No hypothesis. -/
  noInput : ∀ k, 1 ≤ k → k ≤ N → controllable sy (run (entry m0) (zeros k)) = decide (k = N)
  /-- other positions and speeds, no input: the same frame, and the same key at that frame -/
  otherMoved : ∀ c ∈ moved sy,
    (∀ k, 1 ≤ k → k ≤ N → controllable sy (run (applyChange (entry m0) c) (zeros k)) = decide (k = N)) ∧
      key sy (run (applyChange (entry m0) c) (zeros N)) = key sy (run (entry m0) (zeros N))
  /-- a big Mario, no input: the same frame -/
  otherBig : ∀ k, 1 ≤ k → k ≤ N →
    controllable sy (run (applyChange (entry m0) (big sy)) (zeros k)) = decide (k = N)
  /-- real runs: standing `d` more frames, then Down, then no input: the same frame -/
  stand : ∀ d, d < D →
    entersAt sy (run (standing m0) (zeros d)) downIn = true ∧
      ∀ k, 1 ≤ k → k ≤ N →
        controllable sy (run (frame (run (standing m0) (zeros d)) downIn) (zeros k)) = decide (k = N)

theorem entry_eq (m0 : Machine) : entry m0 = frame (run (run m0 approach) fall) landIn := by
  simp only [entry, witness, run_append]
  rfl

theorem statement_of_check {sy : Syms} {m0 : Machine} {N D : Nat} (hN : 1 ≤ N)
    (h : allCheck sy m0 N D = true) : Statement sy m0 N D := by
  simp only [allCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [changesCheck, Bool.and_eq_true, List.all_eq_true] at h3
  obtain ⟨h5, h6⟩ := h3
  rw [← entry_eq] at h2 h5 h6
  refine ⟨?_, ?_, no_input_of_chain h2, ?_, no_input_of_chain h6, ?_⟩
  · rw [run_append]
    exact h1
  · intro hM w hw hl
    exact first_control h2 zero_mem_inputs hM w hw hl hN
  · intro c hc
    have h7 := h5 c hc
    refine ⟨no_input_of_chain h7, ?_⟩
    exact of_decide_eq_true (chain_goal sy [] _ N _ h7)
  · intro d hd
    have h7 : run (run m0 approach) stop = standing m0 := by
      simp only [standing, run_append]
    rw [h7] at h4
    obtain ⟨h8, h9⟩ := standCheck_spec sy N D _ h4 d hd
    exact ⟨h8, no_input_of_chain h9⟩

end Smbrta.PipeTransition
