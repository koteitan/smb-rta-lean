[← Back](README.md) | [English](f-6-17-7-PoleKeepFar.md) | [Japanese](f-6-17-7-PoleKeepFar-ja.md)

# The pole's tiles: the stores that `keepB` and `bufAll` still speak of

Two fields of `PoleJoin.Run` are conditions on every store through an index or a pointer, on every frame up to the touch:

* `keepB`: such a store writes neither the block objects' offset nor the player's number (`PoleTileKeep.KeepB`, [The height kept inside the collision routine](f-6-17-6-PoleTileKeep.md));
* `bufAll`: such a store puts a pole's tile into the block buffers only in the pole's column (`PoleTileWalk.BufAt`, [The pole's tiles at the touch](f-6-17-2-PoleTileWalk.md)).

Most of these stores cannot do what the conditions forbid, whatever their index. Now this is proved for them, and the two fields ask only of the other stores. For one instruction the new conditions say the same as the old ones (`keepB_of_R`, `bufAt_of_V`; the other direction is plain). What is new is that the fields now state which stores they still speak of. On the measured real frames these are 66 places for `keepB` and 7 places for `bufAll`.

## The stores that the program settles

Write `op` for the instruction's opcode, `b` for its operand (the base address), `P` for a list of RAM indices. `farStore P m` holds when the instruction at `m.pc` and its operand bytes are in the ROM, and

* `op` is a store through an absolute address and `X` or `Y`, and no index 0 to 255 brings `b` onto a byte of `P` (`PositionKeep.absFarAt`, from part e): `∀ x < 256, (b + x) mod 2¹⁶ < 0x2000 ⇒ (b + x) mod 2048 ∉ P`; or
* `op` is a store through the zero page and `X` (`STA`, `STY`, `INC`, `DEC`), and every byte of `P` is at 256 or more: the target is `(b + X) mod 256`, in the zero page.

`far_target` proves: `farStore P m ⇒ ∀ t, wTarget(op, m) = t ∧ t < 0x2000 ⇒ t mod 2048 ∉ P`. Only the ROM's bytes are read; no index is known.

For the block buffers, `farBuf Q m` is `farStore` of all bytes of the two buffers, and the buffers are past the stack (`far_locs`: such a step, an NMI's pushes too, changes no byte of the buffers). So `farBuf Q m ⇒ NoTile Q m` (`noTile_of_far`).

## The stores of A

An `STA abs,X`, `STA abs,Y` or `STA (zp),Y` run from the ROM with no NMI pending changes a byte of the RAM only to A (`sta_step`, from `wr_val`, `sta_val` and the three addressing modes `abx_state`, `aby_state`, `izy_state`, which keep the RAM and A). So if A is not one of the pole's two tiles, the step puts no pole's tile anywhere.

## The fields

```
KeepR(m) :=  farStore(bI, m) = false  ⇒  KeepB(m)
BufV(m)  :=  farBuf(Q, m) = false  ⇒  (no NMI ∧ not halted ∧ pc, pc+1, pc+2 ≥ 0x8000 ∧ op ∈ {STA abs,X, STA abs,Y, STA (zp),Y}  ⇒  A ∈ {ball, shaft})  ⇒  BufAt(Q, m)
```

where `bI` is the two bytes of `PoleTileKeep`, `Q` the places of the pole, and `ball`, `shaft` the pole's two tiles.

* `keepB : ∀ n < ix(g), ∀ k, KeepR(trace(all n, inp n, k))` (was `KeepB`);
* `bufAll : ∀ n < ix(g), ∀ k, BufV(trace(all n, inp n, k))` (was `BufAt`).

`keepB_of_R : KeepR(m) ⇒ KeepB(m)` and `bufAt_of_V : BufV(m) ⇒ BufAt(m)`. `Run.tilesStart`, `Run.keepB₁` and `Run.bufAt₁` use them; no other theorem changed, and `route_1_1` still concludes `1748 + j ≤ L`.

## Measured

`pole-keep check FM2 96` (every instruction of every frame from the first control; the counts are on the frames that start in control, which are the frames the fields speak of):

| | stores settled | stores still asked | places still asked | the condition false |
|---|---|---|---|---|
| `keepB` (`farStore`) | 4,769,204 at 177 places | 1,331,301 | 66 | 0 |
| `bufAll` (`farBuf`, then the byte of an `STA`) | 5,867,858 + 231,685 | 962 | 7 | 0 |

The runs are those of [The height kept inside the collision routine](f-6-17-6-PoleTileKeep.md) with `N = 96`: the TAS, the TAS from frame 1089 with other inputs, and own random inputs: 41,021 frames that start in control, 167,758,026 instructions in all. The same check with `N = 16` gave 66 and 5 places. For `bufAll` "false" counts the real steps that put a pole's tile into the block buffers off the pole's column.

The places where `bufAll` still asks are the area parser's store of a metatile into the block buffers, and six stores into the objects' and the bounding boxes' tables, where A happened to have the value of a pole's tile; their targets are off the block buffers. The places where `keepB` still asks are stores into the screen's buffers, the metatile buffer, the block objects', the enemies' and the sprite objects' tables, the joypad's saved bits, the block buffers through a pointer, and the digits of a number.

What a walk would have to know there, measured (the largest index seen, over the same runs): the screen's first buffer up to 65, its second buffer up to 29, the sprites' data offsets up to 14, the metatile buffer up to 12, the area objects' tables up to 2, the block objects' tables and the joypad's saved bits up to 1, the enemies' tables up to 5, the sprite objects' tables up to 6, the digits of a number up to 42; at the four stores through a pointer the pointer's high byte is always the block buffers' page. At the six stores of `bufAll` into the objects' and the bounding boxes' tables the index is at most 0 and 69.

**Tried and not done.** A walk of the frames that knows the index at these stores. The walk of `PoleTileKeep.keepCheckOfY` knows `X` at almost none of them: an `INX` or `DEX` of an `X` that is only partly known gives an unknown `X`, and the index often comes from a byte that the walk does not keep (the cannons' offset, the screen buffers' offsets). In that walk the test "the step writes no byte of the block buffers" fails at 38 places, and the test "the store writes neither of the two bytes" at 111 places; of the 66 real places of `keepB`, it settles only 12. With the objects' offset protected and watched with its value at control (5), the table grows from 46,486 to 183,335 states, the offset is known exactly at many places, but `X` is still unknown at the stores, and protecting the offset itself needs 361 more places. So this is not done.

## What is not proved

* `keepB` at its 66 places: no store there writes the block objects' offset or the player's number.
* `bufAll` at its 7 places: the area parser draws the pole's tiles only in the pole's column, and the other six stores do not reach the block buffers. Round 33: at the same stores `bufAll` also asks that a pole's tile goes into the block buffers only once the parser's column at the frame's start has come to the pole's (`PoleSlot.BufVS`, [the slot of the area parser is a theorem](f-6-17-14-PoleSlot.md)). Round 34: that part asks only that the parser's column has come to the pole's or the store is in the ring's column of the parser's column (`PoleRing.BufVM`, [the parser stores a column at its own place in the ring](f-6-17-16-PoleRing.md)).
* `tilesCol` is unchanged.

**Files.** `Theorems/PoleKeepFar.lean`; `Theorems/PoleJoin.lean` (the two fields); `pole-keep check` in `Main.lean`.
