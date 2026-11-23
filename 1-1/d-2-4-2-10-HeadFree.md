[← Back](README.md) | [English](d-2-4-2-10-HeadFree.md) | [Japanese](d-2-4-2-10-HeadFree-ja.md)

# The head's read from the head's cell in the map

**Claim.** On every frame of the room, a read of the block buffer routine for the head gives the empty tile or a coin, if the cell that it reads is the empty
tile or a coin in the map. So the field `roomRead` no longer asks the byte that the machine reads. It asks only where the head's read is: its cell is free in the
map (`HeadFree`).

This is proved, with one more check on the ROM in a private proof that already exists (walk (i) of `LoopTime.recCheckB`, `Proof.SiteMusic1`; no new private
file). The field `roomRead` is changed: it asks a condition on the read's address in place of the byte read. No field is added.

`B` is the set of the 416 bytes of the two block buffers, `M` the map (`RoomMap.mapRef`: the machine at the first control in the room after the reference entry,
with no input for 91 frames), `m(d)` the byte `d` of the RAM of `m`. `T` is the list of tiles (`P.tiles`, 12 tiles), `H` the head's tiles (`P.headTiles`: the
empty tile and the coin). `read` is the routine's `LDA (zp),Y`, `addr(m)` its address, `val(m)` the byte it reads, `save` the routine's offset byte, `heads`
the head's offsets. `tr_n(j)` is the machine after `j` instructions of frame `n`. `x & y` and `~x` are bitwise.

## The statement

```
ZeroIn(m)     :=  ∀ d ∈ B,  m(d) & ~M(d) = 0                                  (the bits that are 0 in the map are 0)
HeadFree(m)   :=  pc(m) = read  →  m(save) ∈ heads  →  M(addr(m) & 0x7FF) ∈ H   (the head's cell is free in the map)
ReadH(m)      :=  pc(m) = read  →  m(save) ∈ heads  →  val(m) ∈ H                (round 34: the field)
headSub       :=  ∀ t ∈ T,  ∀ c ∈ H,  t & ~c = 0  →  t ∈ H                      (a check on the ROM)

readH_of_free :  headSub,  TilesIn(m),  ZeroIn(m),  ReadIn(m),  HeadFree(m)   →   ReadH(m)
zero_step     :  Sim(A, m),  keepOKB(A),  SiteX(m),  ZeroIn(m)                →   ZeroIn(step(m))
zero_of_rows  :  MapFacts,  startCheckT,  InRowsT(m),  control(m)            →   ZeroIn(m)
```

`TilesIn` and `ReadIn` are those of [the block buffers' tiles at the read](d-2-4-2-8-ReadTiles.md): every byte of `B` is a tile of `T`, and the read's address
is in `B`.

In `Route.ChangesBase` the field changes:

```
before   roomRead : ∀ n ∈ [b₁, a₂),  ∀ j,  ReadH(tr_n(j))
now      roomRead : ∀ n ∈ [b₁, a₂),  ∀ j,  HeadFree(tr_n(j))
```

The new field does not imply the old one by itself. With `ZeroIn`, `TilesIn` and `ReadIn` on each instruction, which the room's walks prove, it does
(`readH_of_free`). The old field does not imply the new one either: a machine whose block buffer holds 0 at a cell that is a brick, the block, a pipe or the floor in
the map has `ZeroIn` and `ReadH` there, but not `HeadFree`. So on such states the new field asks more. On the measured runs both hold at every head read (below).

## How it works

**The map's bits.** The walks of the room's frames (`LoopTime.recCheckB`) already check at every state that its step writes no byte of `B`, or that it is the
coin's erase with the accumulator 0 (`ReadTiles.keepOKB`). Such a step keeps each byte of `B` or makes it 0 (`buf_step`). A byte that becomes 0 has no bit at
all. So `ZeroIn` is kept by every step (`zero_step`). The walks carry it with `TilesIn` as one invariant (`LoopTime.MapIn`) through every instruction of every
frame (`ReadTiles.frameVI`), from the room's first control on. There it holds: the rows of the change into the room give the room's condition with the map's bits
(`RoomMap.start_of_rows`), and the reference has no bit outside the map (`RoomMap.MapFacts.sub`).

**The read for the head.** At a read for the head, the byte read is a byte of `B` (`ReadIn`), a tile of `T` (`TilesIn`), with no bit outside the map's byte
(`ZeroIn`). If the map's byte is a head tile, the check `headSub` gives that the byte read is a head tile too. On this ROM the coin is the only tile of the list
other than the empty one whose bits all lie in the coin's bits.

**On the ROM.** `headSub` is part of walk (i) (`LoopTime.walk1B`), next to `SideRead.xFacts`.

## Measured

`buffer-ctl-check FM2 100 headfree` (exit 0, 120 s): the movie's frames in the room, and own runs from them (100 runs of per-frame random inputs, 100 runs of
inputs held for several frames), each with a small and a big player, instruction by instruction.

| player | runs | frames | head reads | `HeadFree` false | `ReadH` false | frame starts without `ZeroIn` |
|---|---|---|---|---|---|---|
| small | 201 | 65,076 | 65,076 | 0 | 0 | 0 |
| big | 201 | 71,395 | 71,395 | 0 | 0 | 0 |

`headSub` is true. The head's reads were in rows 1 to 10 of the first block buffer, never in the top row (the least height at a head read 45 px). Every head read
of these runs was in a cell that is free in the map.

## What is not proved

* `HeadFree`: where the head is. The cells that are not free in the map are the left wall, the bricks of the top row over the block, the block, the side pipe, the
  vertical pipe and the floor. To keep the head out of them, the position has to be bounded over frames: the left wall and the pipes as walls, and the height
  of a jump below the top row. The facts of part c about the room's frames cannot be used here: they are proved with `SiteOK`, whose head clause is this field.

## Uses from other parts

* Part c: `RoomMap.start_of_rows`, `RoomMap.MapFacts` (`sub`), `RoomMap.startCheckT`, `RoomMap.knownT`, `RoomMap.mapRef`, `RoomMap.TilesIn`,
  `RoomBlocks.readVal_eq`.
* Part d: `ReadTiles` (round 34), `LoopTime`, `EraseRange`, `StepWrites.keep_step`.
* No cycle: `ZeroIn` at frame `n` comes from the rows at the first control and from the steps of the frames before `n` and of the instructions before.
