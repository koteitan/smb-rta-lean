import Theorems.PoleWrap
/-!
# The pole's tiles: a frame with the screen buffers' control byte 6 keeps `JV` when the parser is not late

`PoleJoin.Run.ctlU` (round 31) asked, on each frame before the touch's frame that comes to the player's routine, at `UpdScrollVar`: the screen buffers' control
byte is not 6. With it the frame follows the strict rule and keeps `JV` (`N ≤ 7 ∧ S + 3·N < 32`, `PoleWrap.JV`; `PoleStrict.step_strict`).

Where the code sets the byte (the community disassembly's names): the screen update at the start of each frame sets it to 0. In the game's core, before
`UpdScrollVar`, only `RemoveCoin_Axe` sets it to 6: he takes a coin (with his head, a foot or a side: `HandleCoinMetatile`), he touches the axe
(`HandleAxeMetatile`), or a block he bumps has a coin on top (`CheckTopOfBlock`). After `UpdScrollVar` the parser's tasks set it to 6 for the next frame's
screen update. So the byte is 6 at `UpdScrollVar` only on a frame where he takes a coin, and then `UpdScrollVar` runs no task: `N` and the counter `S` stay.

Round 32: such a frame keeps `JV` too when the parser is not late there, `S + 3·N < 32` at `UpdScrollVar` (`S` already has the scroll's amount): the weak forms
of `PoleParser.frame_six` keep `N` or take one off and keep `S` (`jv_weak`, with `colEnd_n` for the column's step), or start a new column, which needs
`S ≥ 32`.
So `ctlU` asks the control byte not 6 only where `S + 3·N ≥ 32` at `UpdScrollVar` (`PoleStrict.step_strict`, `PoleStrict.invJ_onFrames`).

What is not proved: that he takes no coin above ground on a frame where the parser is late. A proof needs the block buffers' contents at his reads on every
frame (no coin's tile there), as the rest of `tilesCol` does.

There is no game data in this file. Page: `1-1/f-6-17-13-PoleLate.md`.
-/

namespace Smbrta.PoleLate

open PoleParser

variable {sy : Syms} {m0 : Machine}

/-- **The column's step keeps `N` or takes one off** (`PoleParser.ColEnd`), when the column is below 16 -/
theorem colEnd_n {u e : Machine} (h : ColEnd sy m0 u e) (hc : (u.ram.get! (cIdx sy m0)).toNat < 16) :
    e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) ∨ e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) - 1 := by
  by_cases h15 : (u.ram.get! (cIdx sy m0)).toNat < 15
  · rcases (h.1 h15).2 with ⟨a, _⟩ | ⟨a, _⟩
    · exact Or.inl a
    · exact Or.inr a
  · have e15 : u.ram.get! (cIdx sy m0) = 15 := UInt8.toNat_inj.1 (by have : (15 : UInt8).toNat = 15 := rfl; rw [this]; omega)
    rcases h.2 e15 with ⟨a, _⟩ | ⟨a, _⟩
    · exact Or.inl a
    · exact Or.inr a

/-- **`JV` after the parser's weak part**: `N` at most 7 and `S + 3·N` below 32 at `UpdScrollVar`, and at the end `N` kept or less and `S` kept. (The other
weak case, a new column, needs `S ≥ 32`, which `S + 3·N < 32` excludes.) -/
theorem jv_weak {n s n' s' : Nat} (hn : n ≤ 7) (hl : s + 3 * n < 32) (h : n' ≤ n) (hs : s' = s) : n' ≤ 7 ∧ s' + 3 * n' < 32 := by
  omega

end Smbrta.PoleLate
