import Theorems.PoleSlot

/-!
# The pole's tiles: the parser stores a column at its own place in the ring of the block buffers

Round 33 made the field `PoleJoin.Run.bufAll` ask, at each store that changes a byte of the block buffers to a pole's tile, that the area parser's column at the
frame's start has come to the pole's (`PoleSlot.NoTileC`). Here that part asks less: such a store is in the column of the ring of the block buffers that the
parser's column of the frame's start has, or the parser's column has come to the pole's (`NoTileM`). The rest is proved:

* The block buffers are a ring of 32 columns (two buffers of 16 columns, the rows of 16 bytes). `ringCol Q i` is the column of the ring of the byte `i`.
* `RingOK Q` (from the check `ringCheck` on the places): every byte of the pole's column is in the ring's column `colP mod 32`.
* `BufV` (asked by `bufAll` since round 26) puts a pole's tile only in the pole's column. So a store of a pole's tile in the ring's column of the parser's column
  `c` has `c ≡ colP (mod 32)`. With `colP < c + 32` that is `colP ≤ c` (`noTileC_of_M`).
* `colP < c + 32` holds at control (a check on the rows of the change out of the side pipe, `PoleParserRun.low₀`) and the parser's column does not go back from
  frame to frame (`PoleParserRun.colMono_run`), so it holds at every frame's start up to the touch's frame (`PoleJoin.Run.slotStart`).

There is no game data in this file. Page: `1-1/f-6-17-16-PoleRing.md`.
-/

namespace Smbrta.PoleRing

open PoleFrame
open PoleEntryRule (Spots onCol)
open PipeTransitionAll (go)
open PipeWrites (wTarget opAt)
open PoleTileWalk (NoTile BufAt)
open PoleTiles (Tile)
open PoleSlot (colP NoTileC BufVS BufC)

/-- **The column of the ring of the block buffers** of the RAM index `i`: 16 for each buffer before it, and its place in the row -/
def ringCol (Q : Spots) (i : Nat) : Nat := 16 * ((i - Q.bufLo) / (16 * Q.rows)) + (i - Q.bufLo) % 16

/-- **Every byte of the pole's column is in the ring's column of the pole's column** -/
def RingOK (Q : Spots) : Prop := ∀ i, onCol Q i = true → ringCol Q i = colP Q % 32

/-- the check of `RingOK`: the rows of the pole's column, one by one -/
def ringCheck (Q : Spots) : Bool := (List.range Q.rows).all fun r => ringCol Q (Q.dC + 16 * r) == colP Q % 32

theorem ringOK_of_check {Q : Spots} (h : ringCheck Q = true) : RingOK Q := by
  intro i hi
  simp only [onCol, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi
  obtain ⟨⟨h1, h2⟩, h3⟩ := hi
  have hr : (i - Q.dC) / 16 < Q.rows := by
    have : i - Q.dC < 16 * Q.rows := by omega
    omega
  have hm := List.all_eq_true.1 h ((i - Q.dC) / 16) (List.mem_range.2 hr)
  have e : Q.dC + 16 * ((i - Q.dC) / 16) = i := by omega
  rw [e] at hm
  exact beq_iff_eq.1 hm

/-- **What a store asks for the slot from round 34**, on a frame whose start has the parser's column `c`: it changes a byte of the block buffers to a pole's tile
only when the parser's column has come to the pole's, or in the ring's column of the parser's column -/
def NoTileM (Q : Spots) (c : Nat) (m : Machine) : Prop :=
  ∀ i, Q.bufLo ≤ i → i < Q.bufLo + Q.bufBytes → (go step m).2.ram.get! i ≠ m.ram.get! i → Tile Q ((go step m).2.ram.get! i) →
    colP Q ≤ c ∨ ringCol Q i = c % 32

/-- **What the field `bufAll` asks of one instruction from round 34**, with `c` the parser's column at the frame's start: `PoleKeepFar.BufV`, and at the same
stores `NoTileM` (round 33 asked `PoleSlot.NoTileC` there) -/
def BufVM (Q : Spots) (c : Nat) (m : Machine) : Prop :=
  PoleKeepFar.farBuf Q m = false → (m.nmiPending = false → m.halted = false → 0x8000 ≤ m.pc → 0x8000 ≤ m.pc + 1 → 0x8000 ≤ m.pc + 1 + 1 →
    PoleKeepFar.staOps.contains (opAt m) = true → Tile Q m.a) → (wTarget (opAt m) m).isSome = true → NoTile Q m ∧ NoTileM Q c m

/-- `NoTileC` gives `NoTileM`: the round 33 condition asks more -/
theorem noTileM_of_C {Q : Spots} {c : Nat} {m : Machine} (h : NoTileC Q c m) : NoTileM Q c m :=
  fun i h1 h2 hch ht => Or.inl (h i h1 h2 hch ht)

/-- `BufVS` gives `BufVM`: the round 33 field asks more -/
theorem bufVM_of_VS {Q : Spots} {c : Nat} {m : Machine} (h : BufVS Q c m) : BufVM Q c m :=
  fun hf ht hs => ⟨(h hf ht hs).1, noTileM_of_C (h hf ht hs).2⟩

theorem bufV_of_VM {Q : Spots} {c : Nat} {m : Machine} (h : BufVM Q c m) : PoleKeepFar.BufV Q m := fun hf ht hs => (h hf ht hs).1

/-- `BufAt` from `BufVM` (`PoleKeepFar.bufAt_of_V`) -/
theorem bufAt_of_VM {Q : Spots} {c : Nat} {m : Machine} (h : BufVM Q c m) : BufAt Q m := PoleKeepFar.bufAt_of_V (bufV_of_VM h)

/-- **`NoTileC` from `NoTileM`**: a pole's tile goes only into the pole's column (`NoTile`), which is the ring's column `colP mod 32` (`RingOK`); if that is also
the ring's column of `c`, then `c ≡ colP (mod 32)`, and with `colP < c + 32` the parser's column has come to the pole's -/
theorem noTileC_of_M {Q : Spots} {c : Nat} {m : Machine} (hn : NoTile Q m) (h : NoTileM Q c m) (hr : RingOK Q) (hc : colP Q < c + 32) : NoTileC Q c m := by
  intro i h1 h2 hch ht
  rcases h i h1 h2 hch ht with h3 | h3
  · exact h3
  · have h4 := hr i (hn i h1 h2 hch ht)
    rw [h4] at h3
    omega

/-- **`BufVS` from `BufVM`**, with `RingOK` and `colP < c + 32` -/
theorem bufVS_of_VM {Q : Spots} {c : Nat} {m : Machine} (h : BufVM Q c m) (hr : RingOK Q) (hc : colP Q < c + 32) : BufVS Q c m :=
  fun hf ht hs => ⟨(h hf ht hs).1, noTileC_of_M (h hf ht hs).1 (h hf ht hs).2 hr hc⟩

/-- **`BufC` from `BufVM`** (`PoleSlot.bufC_of_VS`) -/
theorem bufC_of_VM {Q : Spots} {c : Nat} {m : Machine} (h : BufVM Q c m) (hr : RingOK Q) (hc : colP Q < c + 32) : BufC Q c m :=
  PoleSlot.bufC_of_VS (bufVS_of_VM h hr hc)

/-- **What the field `bufAll` asks of one instruction from round 35** (`1-1/f-6-17-18-PoleBcol.md`): `BufVM`, but `NoTileM` only away from the place `st`, the
area parser's store of a column (there the walk of `PoleBcol` proves it) -/
def BufVR (Q : Spots) (c : Nat) (st : UInt16) (m : Machine) : Prop :=
  PoleKeepFar.farBuf Q m = false → (m.nmiPending = false → m.halted = false → 0x8000 ≤ m.pc → 0x8000 ≤ m.pc + 1 → 0x8000 ≤ m.pc + 1 + 1 →
    PoleKeepFar.staOps.contains (opAt m) = true → Tile Q m.a) → (wTarget (opAt m) m).isSome = true → NoTile Q m ∧ (m.pc ≠ st → NoTileM Q c m)

/-- `BufVM` gives `BufVR`: the round 34 field asks more -/
theorem bufVR_of_VM {Q : Spots} {c : Nat} {st : UInt16} {m : Machine} (h : BufVM Q c m) : BufVR Q c st m :=
  fun hf ht hs => ⟨(h hf ht hs).1, fun _ => (h hf ht hs).2⟩

/-- **`BufVM` from `BufVR`** and `NoTileM` at the place `st` -/
theorem bufVM_of_R {Q : Spots} {c : Nat} {st : UInt16} {m : Machine} (h : BufVR Q c st m) (hs : m.pc = st → NoTileM Q c m) : BufVM Q c m :=
  fun hf ht hw => ⟨(h hf ht hw).1, if e : m.pc = st then hs e else (h hf ht hw).2 e⟩

/-- `BufAt` from `BufVR` (`PoleKeepFar.bufAt_of_V`) -/
theorem bufAt_of_VR {Q : Spots} {c : Nat} {st : UInt16} {m : Machine} (h : BufVR Q c st m) : BufAt Q m :=
  PoleKeepFar.bufAt_of_V fun hf ht hs => (h hf ht hs).1

/-- the bound `colP < c + 32` from the bound at the first frame, along columns that do not go back -/
theorem low_mono {Q : Spots} {c : Nat → Nat} {K : Nat} (h0 : colP Q < c 0 + 32) (hm : ∀ n, n + 1 < K → c n ≤ c (n + 1)) :
    ∀ n, n < K → colP Q < c n + 32
  | 0, _ => h0
  | n + 1, hn => by
    have := low_mono h0 hm n (by omega)
    have := hm n hn
    omega

end Smbrta.PoleRing
