import Theorems.PoleJoin

/-!
# Above ground: `SideAcross.FactsAt` on the frames of part f's run

`SideAcross.FactsAt` asks, of a frame, that it starts with the block buffer's column below 32 and the block objects' offset 0 or 1, and that no store through an
index or a pointer writes either byte. On the frames of `PoleJoin.Run` (which are those of `SurfaceFrames.OnFrames`, `PoleJoin.Run.frames`) it follows from
part f: the fields `bKeep` (`PoleBcol.BcR` where round 36's `PoleNear` leaves it; with `PoleNear.near_frames` no such store writes the column, `PoleJoin.Run.bNoW`), `keepB` (`PoleTileKeep.KeepB`: none writes the offset) and `bufAll`, and the
column and the offset at control, by the walks of whole frames `PoleBcol.frames_bcol` (the column is the parser's column mod 32 at each frame's start) and
`PoleTileKeep.frames_keepY` (bits 1 to 7 of the offset stay 0) (`Run.factsAll`). The two pairs of RAM indices (the symbols of `SideAcross`, the operands that part
f reads from the code) are the same: the checks `he1`, `he2` on the ROM.

So on the route's frames the old field `OnFrames.sideW`, which round 36 asked only on a frame without `FactsAt`, asked nothing: there is no such frame. Round 37:
the route passes `Run.factsK` (every frame of `keep` up to the touch's frame) to part e as the hypothesis `hF` of `SurfaceFrames.OnFrames.areaRun` (the field
`SurfaceFrames.AreaRun.facts`), and the field `sideW` is gone. The theorems of `PoleJoin` and `PoleParserRun` that build an `AreaRun` take `hF`; the private proof
of the route makes it from the facts at control (`PoleParserRun.bInv₀`, `PoleTileCtl.colMap₀`, `PoleTileCtl.watch₀`) and `he1`, `he2` on the ROM.
Page: `1-1/e-2-10-3-26-SideAcross.md`.
-/

namespace Smbrta.SideAcross

open PipeEntryRule (trace)

variable {sy : Syms} {m0 : Machine}

theorem lt32_all : ∀ n : Fin 256, n.val < 32 → UInt8.ofNat n.val &&& 0xE0 = 0 := by decide +kernel

theorem and_e0 {x : UInt8} (h : x.toNat < 32) : x &&& 0xE0 = 0 := by
  have := lt32_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h

/-- **`FactsAt` on every frame of a run of frames in control**, from part f's conditions on each instruction (`hct`: `PoleBcol.NoW` of the column away from the
parser's store, as `PoleJoin.Run.bNoW` gives it since round 36; at the store `frames_bcol` gives it; `hkb`:
`PoleTileKeep.KeepB`; `hb`: `PoleTileWalk.BufAt`) and the two bytes at control (`hI0`, `hw0`, with the map `hm0`), by `PoleBcol.frames_bcol` and
`PoleTileKeep.frames_keepY`. `he1`, `he2` say that the two pairs of indices are the same (checks on the ROM). -/
theorem factsAt_frames {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 Sr a g seq)
    (hcK : FrameKeep.keepCheckOf sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hcY : PoleTileKeep.keepCheckOfY sy m0 = true)
    (hs0 : FrameKeep.StartK sy m0 (seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0)) (hI0 : PoleBcol.BInv (PoleBcol.bcOf sy m0) (seq 0))
    (hw0 : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (seq 0)) (hm0 : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (seq 0))
    (hct : ∀ n, n < K.ix g → ∀ k, (trace (K.all n) (K.inp n) k).frame = (K.all n).frame → (trace (K.all n) (K.inp n) k).pc ≠ (PoleBcol.bcOf sy m0).store →
      PoleBcol.NoW (PoleBcol.bcOf sy m0).bI (trace (K.all n) (K.inp n) k))
    (hkb : ∀ n, n < K.ix g → ∀ k, PoleTileKeep.KeepB sy m0 (trace (K.all n) (K.inp n) k))
    (hb : ∀ n, n + 1 < K.ix g → ∀ k, PoleTileWalk.BufAt (PoleFrame.spotsF sy m0) (trace (K.all n) (K.inp n) k))
    (he1 : (PoleBcol.bcOf sy m0).bI = bcpI sy) (he2 : PoleTileKeep.sprI sy m0 = sdoI sy) :
    ∀ n, n < K.ix g → FactsAt sy (K.all n) (K.inp n) := by
  intro n hn
  have hBc := PoleBcol.frames_bcol hcK hcB K hs0 h0 hI0 hct n hn
  have hB := hBc.1
  have hY := (PoleTileKeep.frames_keepY hcK hcY K hs0 h0 hw0 hm0 (fun n' hn' k => hkb n' (by omega) k) hb n hn).2
  refine ⟨⟨?_, ?_⟩, fun k hfk => ?_⟩
  · rw [← he1]
    apply and_e0
    rw [hB.1]
    exact Nat.mod_lt _ (by decide)
  · have e := hY (PoleTileKeep.sprI sy m0, 0xFE, 0) (by simp [PoleTileKeep.watchB])
    rw [← he2]
    dsimp only at e
    rw [e]
    rfl
  · intro t ht hlt hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with e | e
    · by_cases hpc : (trace (K.all n) (K.inp n) k).pc = (PoleBcol.bcOf sy m0).store
      · exact (hBc.2 k hpc).2.1 t ht hlt (by rw [e, he1])
      · exact hct n hn k hfk hpc t ht hlt (by rw [e, he1])
    · exact hkb n hn k t ht hlt (by rw [e, ← he2]; simp [PoleTileKeep.bI])

set_option maxRecDepth 100000 in
/-- **`FactsAt` on every frame of `PoleJoin.Run` up to the touch's frame** (counted or not: the frames of `keep`, as `SurfaceFrames.AreaRun.facts` asks it), from
its fields `bKeep` (through `Run.bNoW` and the check `hcN`), `keepB`, `bufAll` and the two bytes at control (`hIB`: `PoleParserRun.bInv₀`; `hwb`:
`PoleTileCtl.watch₀`; with the map `hmap`: `PoleTileCtl.colMap₀`), as `Run.tilesStart`. Round 37: the route passes it to part e (`SurfaceFrames.OnFrames.areaRun`), so
the field `OnFrames.sideW` is gone. -/
theorem Run.factsK {b : Machine} {vs : List Jump.VS} {B : PoleJoin.Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat}
    (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar)
    (hc : PoleTileKeep.poleCheckZ sy m0 = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true)
    (hcN : PoleNear.nCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : PoleJoin.fracCheck sy B.m = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))
    (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0))
    (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0))
    (he1 : (PoleBcol.bcOf sy m0).bI = bcpI sy) (he2 : PoleTileKeep.sprI sy m0 = sdoI sy) :
    ∀ n, n < R.keep.toFrames.ix R.g → FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n) := by
  have e : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  exact factsAt_frames R.keep.toFrames hk hcB (PoleTileKeep.keepY_of_Z hc) hc0.start (R.watched₀ st hq hc0.castle) hIB hwb hmap
    (R.bNoW hk hcN hc0.start (R.watched₀ st hq hc0.castle)) (fun n hn k => PoleKeepFar.keepB_of_R (R.keepB n (by omega) k))
    (fun n hn k => PoleRing.bufAt_of_VR (R.bufAll n (by omega) k)) he1 he2

/-- `Run.factsK` with the box written `⟨M, dx, dy, rows⟩`, as `PoleJoin.touch_castle` writes it, so that the private proof's facts on its machine `M` match
without unfolding it -/
theorem Run.factsKM {b : Machine} {vs : List Jump.VS} {M : Machine} {dx dy rows T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat}
    (R : PoleJoin.Run sy m0 b vs ⟨M, dx, dy, rows⟩ T J Nc F Sr ar)
    (hc : PoleTileKeep.poleCheckZ sy m0 = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true)
    (hcN : PoleNear.nCheck sy m0 = true)
    (st : SurfaceFrames.Start sy ⟨M, dx, dy, rows⟩ (R.seq 0)) (hq : PoleJoin.fracCheck sy M = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))
    (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0))
    (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0))
    (he1 : (PoleBcol.bcOf sy m0).bI = bcpI sy) (he2 : PoleTileKeep.sprI sy m0 = sdoI sy) :
    ∀ n, n < R.keep.toFrames.ix R.g → FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n) :=
  Run.factsK R hc hk hcB hcN st hq hc0 hIB hmap hwb he1 he2

/-- **`FactsAt` on every counted frame of `PoleJoin.Run` up to the touch** (the frames of `OnFrames`: `Run.frames`): `Run.factsK` at the counted frames -/
theorem Run.factsAll {b : Machine} {vs : List Jump.VS} {B : PoleJoin.Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat}
    (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar)
    (hc : PoleTileKeep.poleCheckZ sy m0 = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true)
    (hcN : PoleNear.nCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : PoleJoin.fracCheck sy B.m = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))
    (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0))
    (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0))
    (he1 : (PoleBcol.bcOf sy m0).bI = bcpI sy) (he2 : PoleTileKeep.sprI sy m0 = sdoI sy) :
    ∀ j, 1 ≤ j → j ≤ R.g → FactsAt sy (R.keep.fm j) (R.keep.pad j) := by
  intro j h1 h2
  have h3 := R.keep.toFrames.one_le_ix h1 h2
  have h4 := R.keep.toFrames.ix_mono j R.g h2 (Nat.le_refl _)
  exact Run.factsK R hc hk hcB hcN st hq hc0 hIB hmap hwb he1 he2 (R.keep.toFrames.ix j - 1) (by omega)

end Smbrta.SideAcross
