[← Back](README.md) | [English](g-2-2-2-TouchRows.md) | [Japanese](g-2-2-2-TouchRows-ja.md)

# Rows from the touch's end to the castle (measured)

**Claim.** This is a measurement, not a proof. From the machine at the end of the movie's touch of the pole, rows of abstract states reach the castle entry with any input, Start included. They do so also when 350 bytes are not known at the start. But the rows take 10 s without Start and 295 s with Start, and their start still knows 1698 bytes of the movie's machine. So the fields `flag.entry`, `flag.task_E` and `flag.y_E` of `Route.Run` stay. The four things a proof needs are at the end.

## What the game does

* The touch's frame runs `FlagpoleCollision`. The routine becomes 4 (the slide). Mario climbs, his speed is 0, and his `x` is set from the pole's column. The number of the score is set from the height. The music is asked to stop, and the scroll is locked.
* Routine 4 (`FlagpoleSlide`) moves him down. `FlagpoleRoutine` moves the flag down. When the flag or Mario is low enough, it gives the score and sets routine 5. A grab low on the pole, as in the movie, reaches routine 5 in the touch's frame.
* Routine 5 (`PlayerEndLevel`) walks him right. When he is off the pole it asks for the music of the level's end. When his right side meets the castle's wall, the wall clears bit 0 of his collision bits, and the routine sets the star flag's task to 1. The star flag's routine runs later in the same frame and sets task 2. So the first frame with the castle flag ends with task 2.
* The game timer does not run in routines 4 and 5. A frame that ends paused does not run the game.

## The rows

`row(j)` holds states at a frame's start after `j` frames that end not paused since the touch's end. This is how `pole` counts its frames. A frame that ends paused leads back into the same row.

```
the touch's end            ∈  row(0)
S ∈ row(j),  any input i:  frame(S, i) ends paused      →  frame(S, i) ∈ row(j)
                           frame(S, i) ends not paused  →  frame(S, i) ∈ row(j + 1),  or the castle flag is up
```

Each state's frame is searched alone, from the idle loop to the frame's end, with the pad not known. In a row the ends are joined when they have the same dots and the same known values of the pause status, the screen buffer's offset and first byte, the music's queues and buffers, the music's pointer, and the pause sound's bytes. The search keeps these bytes apart as well. Reads of the music's queues and of the pause sound's bytes are split by their values (`Env.splits`). Square 1's place in the music is split as in [The star flag's rule after the castle entry](g-2-1-FlagRule.md).

## Measurements

The start is the movie's machine at the end of its touch's frame: the machine when frame 1093 (`b₂ + 240`) begins. The castle flag is up when frame 1219 (`b₂ + 366`) begins, after frame 1218, so after 126 frames that end not paused. Each measurement was run once, with the machine nearly idle.

```
bytes not known at the start      Start   castle flag   states in a row        searches   steps     time
none                              no      row 126       2                      251        1.6 M     3.6 s
350                               no      row 126       4                      537        4.1 M     10.4 s
none                              yes     row 126       36, from row 66: 108   11455      55.9 M    119 s
350                               yes     row 126       54, from row 66: 162   16553      123 M     295 s
350, the music's places and       yes     the first row did not end in 10 minutes
the sound effects
```

The 350 bytes are the temporary bytes, the top of the stack, the sprites, the random bytes, the frame counter, the phase and 4 other counting timers, the pad's bytes, the game timer's digits, the score and the coins.

The music of the level's end starts on row 66. From then on a pause can delay the music, and the states of a row differ in the music's place. This is why the rows grow from row 66.

## What a proof needs

1. **A condition at the touch's end.** On the 31 real runs of [A wider condition at the castle entry](g-2-2-1-FlagWide.md), the machine at the touch's end differs from the movie's in 289 bytes on some run: the height of the touch, Mario's vertical state, the screen, the sound, other slots. On the movie and its 12 runs with pauses, 26 bytes differ: the sound, the pause, the random bytes. The rows above know 1698 bytes. A condition that is true on the other touches needs rows with more bytes not known. These were not measured.
2. **The pause.** The pause multiplies the states of a row (2 → 108 with all bytes known). The time grows from 3.6 s to 119 s. When the music's places are not known, each frame splits Square 1's place, and the first row does not end.
3. **The counters at `E + 1`.** `Good` asks that the timer's digits be those of some `t ≤ tmax`. With the digits not known at the start, more walks have to keep the 3 digit bytes through each frame, as the keeps of the star flag's check do. Each is as long as the main walk.
4. **Which frame `E` is.** `flag` reads `seq(E + 1)`. `LagUp` gives `seq(E + 1) = pole.seq(c)` (`Run.castle_join`), and `pole.atCastle` says the castle flag is up there. Nothing says that `c` is the first counted frame with the castle flag. `task_E` holds only on the frames of task 2. The rows show that the first frame after the touch's end with the castle flag ends with task 2. To use this, `flag` needs a condition on single frames that puts `E` there, for example:

```
∀ n,  touch's end ≤ n ≤ E  →  ¬castle(seq n),        castle(seq(E + 1))
```

## What is not proved

* Nothing on this page is proved. `flag.entry`, `flag.task_E` and `flag.y_E` stay hypotheses (1-1-g-2-2).
* The rows start from the movie's own machine. The movie is used only by the program, to make the start; nothing of it is in a Lean file.
* The phase rule after the touch's frame (`hA` of `Run.lagUp_of`) and the lengths after the touch (`flagAny`, `flagTight`, `other` of part f) could be read off such rows. This was not measured.

## Files

Program only, in `Main.lean`: `touchRowsPaused`, `touchRowsProbe` (`touch-rows-check`), `touchRunOf`, `touchEndProbe` (`touch-end-check`).

```
.lake/build/bin/smbrta touch-rows-check FM2 ns-pad     # all bytes known, no Start
.lake/build/bin/smbrta touch-rows-check FM2 ns-real0   # 350 bytes not known, no Start
.lake/build/bin/smbrta touch-rows-check FM2 pad        # all bytes known, any input
.lake/build/bin/smbrta touch-rows-check FM2 real0      # 350 bytes not known, any input
.lake/build/bin/smbrta touch-rows-check FM2 real       # also the music's places and the sound effects (does not end)
.lake/build/bin/smbrta touch-end-check FM2 [N]         # the touch's end and the castle entry on real runs
```
