import Smbrta

/-!
# Fast accel: fewest frames to the running top speed, with jumps

From the first controllable frame of 1-1 (`ctx = smb11Start sy cart`).
* `Upper`: on the full emulator (no model), the input sequence `w` reaches the top speed.
* `Lower`: in the relaxed model (`stepRelax`: horizontal state + ground/air flag, landing
  chosen freely), no sequence of at most `n` frames reaches it.
Real controller: `Bounds sy ctx padInputsA relaxInputs 33 34`. With Left+Right
(`Theorems/TasFastAccel.lean`): `Bounds sy ctx lrInputsA relaxInputsLR 30 32`.
Page: `Theorems/FastAccel.md`.
-/

namespace Smbrta.FastAccel

def start (sy : Syms) (ctx : Machine) : RState := { h := dropPos (PState.read sy ctx), air := false }
def top (sy : Syms) : Int := sy.RunTopSpeed.toNat

/-- in the relaxed model, nothing over `rins` of at most `n` frames reaches the top speed -/
def Lower (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) (n : Nat) : Prop :=
  ∀ seq : List (UInt8 × Bool), (∀ c ∈ seq, c ∈ rins) → seq.length ≤ n →
    (Cert.run (stepRelax sy ctx) (start sy ctx) seq).h.speedInt < top sy

/-- on the full emulator, `w` (inputs from `eins`) reaches the top speed -/
def Upper (sy : Syms) (ctx : Machine) (eins : List UInt8) (w : List UInt8) : Prop :=
  (∀ i ∈ w, i ∈ eins) ∧ (PState.read sy (playFull ctx w)).speedInt ≥ top sy

/-- relaxed lower bound `lo` and an emulator witness of `n` frames -/
def Bounds (sy : Syms) (ctx : Machine) (eins : List UInt8) (rins : List (UInt8 × Bool))
    (lo n : Nat) : Prop :=
  Lower sy ctx rins lo ∧ ∃ w, w.length = n ∧ Upper sy ctx eins w

instance (sy : Syms) (ctx : Machine) (eins w : List UInt8) : Decidable (Upper sy ctx eins w) := by
  unfold Upper; infer_instance

def lowerCheck (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) (n : Nat) : Bool :=
  Cert.checkUpTo (stepRelax sy ctx) rins (fun s => decide (s.h.speedInt < top sy)) n [start sy ctx]

theorem lower_of_check (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) (n : Nat)
    (h : lowerCheck sy ctx rins n = true) : Lower sy ctx rins n := by
  intro seq h1 h2
  have := Cert.lower_bound (stepRelax sy ctx) rins (fun s => decide (s.h.speedInt < top sy))
    (start sy ctx) n h seq h1 h2
  simpa using this

/-- 34 frames, real controller: two backward jumps (found by the pruned exact search) -/
def witness : List UInt8 := [0x02, 0x04, 0x81, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x41, 0x01, 0x02, 0x81,
  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01]

end Smbrta.FastAccel
