[← Back](README.md) | [English](c-7-5-11-RoomFootCut.md) | [Japanese](c-7-5-11-RoomFootCut-ja.md)

# A small landing cut

`RoomFootCut` builds its cut from the actual movement-end state Q. Twelve sampled bytes supply the controls, size and coordinates. One map cell supplies the head read; the second-foot cut also supplies the left-foot cell. Their addresses are computed from Q and the ROM indices. `Solid`, buffer bounds and exclusion of coins prove that the map entries hold at Q.

A cut depends only on these sampled values and the stack pointer. A finite family check therefore applies to every machine with those values, regardless of its other bytes. On a reference slice at 180 pixels, map geometry selects 80 horizontal coordinates. Both foot checks pass for all 160 cases. This slice comes from the reference room machine and uses no input movie. The head and both foot cells have proved buffer bounds and are not coins. Membership in this slice is still required for an actual landing.

The existing `RoomMap` walk supplies six control bytes at the actual `PlayerSubs` instruction: the routine and five screen bytes. `controls_at_subs` uses the old room condition, `MapFacts` and `SiteOK`, plus a checked observation on the same walk table. It does not assume those bytes at Q or add a `Run` field. The other three bytes, collision disable, vertical page and player size, remain open.

After the second foot returns, `landing_stores` proves a local caller branch reaches the side checks with the player standing. It needs a floor tile in A and on the stack, the saved height nibble, a nonnegative vertical speed and no spring. Preservation from the side checks to frame end remains open.

In 100 TAS room frames and 1,600 frames from 20 new random runs, the six controls matched at all 1,700 Q states. The other three bytes had constant values at the starts and Q. The vertical page was nevertheless written by the gravity routine. The 21 measured landing frames passed both foot cuts, all 21 right-foot return states met the caller condition, and all 21 reached the side checks standing. There were no map-cut mismatches. These measurements are not a proof of the three missing byte invariants.

An unrestricted check of all 256 horizontal coordinates fails in 272 of 512 foot cases. It is not the theorem. `land_at` remains. The fall's coordinates still need to imply membership in the finite slice, the caller condition needs to follow from the two actual returns, and standing must survive to frame end. No result uses `floor_at_of` to prove landing.
