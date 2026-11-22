import Theorems.PoleKeepFar

/-!
# The pole's tiles at the touch: the slot of the area parser

Round 29 asked, as the part (`slot`) of the field `PoleJoin.Run.tilesCol` (`PoleTileFar.TileSlot`): right after a read of the side check far from the pole, at the
pole's column, if the byte read is one of the pole's tiles, the area parser's column at the start of the touch's frame had come to the pole's column. Here that part
is a theorem. What is asked in its place is a condition on the stores, at the same stores that the field `bufAll` already speaks of. And the other two parts
(`near`, `read`) are needed only where the parser's column has come to the pole's, so `tilesCol` now asks only that it has not, at such a read (`TileSlotC`).

* The pole's column is `colP Q = 16·pg + c`, counted as the parser's column (16 a page).
* `SlotMap Q c m`: the parser's column `c` has come to the pole's (`colP Q ≤ c`), or no byte of the block buffers holds a pole's tile. The second part is the map
  `PoleTileWalk.ColMap` of the places `noCol Q`, which are `Q` with the pole's column moved past the RAM (`onCol_noCol`). The walks with the test `okSK` look at the places
  only through the block buffers' bytes, so the walk of the frames of `PoleTileKeep` is also the walk for `noCol Q` (`keepCheckS_noCol`).
* `BufVS Q c m` (the field `bufAll` from round 33): `PoleKeepFar.BufV`, and at the same stores (`NoTileC`): a byte of the block buffers that the step changes to
  a pole's tile only when the parser's column `c` of the frame's start has come to the pole's. It asks more than `BufV`. It gives `BufAt` (`bufAt_of_VS`) and `BufC`
  on every instruction (`bufC_of_VS`: a store that `farBuf` settles writes no byte of the block buffers, an `STA` of another byte writes no pole's tile).
* A frame keeps the slot's map (`frame_slot`), and with the parser's column not going back from frame to frame (the weak rule, `PoleParserRun.colMono_run`) so
  do all the frames from control to the touch's frame (`frames_slot`). At control the block buffers hold no pole's tile (`PoleParser.inv₀`).
* The touch's frame (`no_write_frameZS`, the walk of `PoleTileKeep.no_write_frameZ`): the slot's map goes on from step to step. Right after a far read at the pole's
  column, by `TileSlotC` the parser's column has not come to the pole's, so no pole's tile is in the block buffers, and the byte read is a byte of the block
  buffers (`PoleTileFar.tileRead_afterF` on the places `noCol`: `noTile_after`). So `TileCol` holds there, and the walk goes on as before.
* `TileSlotC` is weaker than the round 30 parts (`near`) and (`read`) with the parser's invariant `16·c₀ ≤ e₀ + 384`, which the route proves
  (`tileSlotC_of_N`: the arithmetic of `PoleTileFar.tileCol_of_slot`).

There is no game data in this file. Page: `1-1/f-6-17-14-PoleSlot.md`.
-/

namespace Smbrta.PoleSlot

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeTransition (frame)
open PipeWrites (Guard FrameStart okRt fuelG knownOf wTarget opAt)
open FrameKeep (CleanK Watch Watched)
open TaintRun (AS Env Sim AB AM aRows)
open PoleTileWalk (ColMap BufAt NoTile HypR okS pairOK walkKS keepCheckS okSK)
open PoleTileRead (TR)
open PoleTileHeight (HP hpOf ZoneH)
open PoleTileFar (TileCol TileSlot)
open PoleTiles (Tile)

/-! ## The conditions -/

/-- **The pole's column**, 16 a page, as the parser's column is counted (`PoleJoin.parColOf`) -/
def colP (Q : Spots) : Nat := 16 * Q.pg + Q.col.toNat

/-- the places `Q` with the pole's column moved past the RAM: no index of the RAM is in that column (`onCol_noCol`), and the block buffers are the same,
so `ColMap (noCol Q) m` holds when no byte of the block buffers holds a pole's tile -/
def noCol (Q : Spots) : Spots := { Q with dC := 2048 }

theorem onCol_noCol (Q : Spots) {i : Nat} (h : i < 2048) : onCol (noCol Q) i = false := by
  unfold onCol
  have e : (noCol Q).dC = 2048 := rfl
  rw [e]
  have h2 : ¬ (2048 ≤ i) := by omega
  simp [h2]

/-- the place of a read is in the RAM -/
theorem readAt_lt (Q : Spots) (m : Machine) : readAt Q m < 2048 := by
  unfold readAt
  rw [UInt16.toNat_and]
  have e7 : (0x7FF : UInt16).toNat = 2 ^ 11 - 1 := by decide
  rw [e7, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

/-- **The slot's map** for the parser's column `c` (16 a page): the parser's column has come to the pole's, or no byte of the block buffers holds a pole's tile -/
def SlotMap (Q : Spots) (c : Nat) (m : Machine) : Prop := colP Q ≤ c ∨ ColMap (noCol Q) m

theorem slotMap_mono {Q : Spots} {c c' : Nat} {m : Machine} (h : SlotMap Q c m) (hc : c ≤ c') : SlotMap Q c' m := by
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- no byte of the block buffers holds a pole's tile: the slot's map for every column -/
theorem slotMap_of_none {Q : Spots} {c : Nat} {m : Machine} (h : ∀ i, Q.bufLo ≤ i → i < Q.bufLo + Q.bufBytes → ¬ Tile Q (m.ram.get! i)) :
    SlotMap Q c m :=
  Or.inr fun i h1 h2 ht => absurd ht (h i h1 h2)

/-- **What a store asks for the slot**, on a frame whose start has the parser's column `c`: it changes a byte of the block buffers to a pole's tile only when the
parser's column has come to the pole's -/
def NoTileC (Q : Spots) (c : Nat) (m : Machine) : Prop :=
  ∀ i, Q.bufLo ≤ i → i < Q.bufLo + Q.bufBytes → (go step m).2.ram.get! i ≠ m.ram.get! i → Tile Q ((go step m).2.ram.get! i) → colP Q ≤ c

/-- `NoTileC` of a store through an index or a pointer -/
def BufC (Q : Spots) (c : Nat) (m : Machine) : Prop := (wTarget (opAt m) m).isSome = true → NoTileC Q c m

/-- **What the field `bufAll` asks of one instruction from round 33**, with `c` the parser's column at the frame's start: `PoleKeepFar.BufV`, and at the same
stores `NoTileC`: a store that `farBuf` does not settle, through an index or a pointer, and for an `STA` only when A holds one of the pole's tiles, writes a pole's
tile into the block buffers only in the pole's column and only when the parser's column of the frame's start has come to the pole's -/
def BufVS (Q : Spots) (c : Nat) (m : Machine) : Prop :=
  PoleKeepFar.farBuf Q m = false → (m.nmiPending = false → m.halted = false → 0x8000 ≤ m.pc → 0x8000 ≤ m.pc + 1 → 0x8000 ≤ m.pc + 1 + 1 →
    PoleKeepFar.staOps.contains (opAt m) = true → Tile Q m.a) → (wTarget (opAt m) m).isSome = true → NoTile Q m ∧ NoTileC Q c m

theorem bufV_of_VS {Q : Spots} {c : Nat} {m : Machine} (h : BufVS Q c m) : PoleKeepFar.BufV Q m := fun hf ht hs => (h hf ht hs).1

/-- `BufAt` from `BufVS` (`PoleKeepFar.bufAt_of_V`) -/
theorem bufAt_of_VS {Q : Spots} {c : Nat} {m : Machine} (h : BufVS Q c m) : BufAt Q m := PoleKeepFar.bufAt_of_V (bufV_of_VS h)

/-- a step that `farBuf` settles changes no byte of the block buffers (`PoleKeepFar.far_locs`) -/
theorem noTileC_of_far {Q : Spots} {c : Nat} {m : Machine} (h : PoleKeepFar.farBuf Q m = true) : NoTileC Q c m := by
  simp only [PoleKeepFar.farBuf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro i h1 h2 hch _
  have hm : i ∈ PoleKeepFar.bufL Q := by
    simp only [PoleKeepFar.bufL, List.mem_range'_1]
    exact ⟨h1, h2⟩
  exact absurd (StepWrites.step_ram m i (PoleKeepFar.far_locs h.1 h.2 i hm)) hch

/-- **`BufC` of every instruction from `BufVS`**: a store that `farBuf` settles writes no byte of the block buffers; an `STA` of a byte that is not one of the
pole's tiles writes no pole's tile (`PoleKeepFar.sta_step`) -/
theorem bufC_of_VS {Q : Spots} {c : Nat} {m : Machine} (h : BufVS Q c m) : BufC Q c m := by
  cases hf : PoleKeepFar.farBuf Q m with
  | true => exact fun _ => noTileC_of_far hf
  | false =>
    by_cases hc : m.nmiPending = false ∧ m.halted = false ∧ 0x8000 ≤ m.pc ∧ 0x8000 ≤ m.pc + 1 ∧ 0x8000 ≤ m.pc + 1 + 1 ∧
        PoleKeepFar.staOps.contains (opAt m) = true ∧ ¬ Tile Q m.a
    · obtain ⟨hn, hh, hp, hp1, hp2, hop, ht⟩ := hc
      intro _ i _ _ hch htile
      rw [PoleKeepFar.sta_step hn hh hp hp1 hp2 hop i hch] at htile
      exact absurd htile ht
    · intro hs
      refine (h hf ?_ hs).2
      intro hn hh hp hp1 hp2 hop
      by_cases ht : Tile Q m.a
      · exact ht
      · exact absurd ⟨hn, hh, hp, hp1, hp2, hop, ht⟩ hc

/-- with the parser's column before the pole's, `BufC` says that the step writes no pole's tile into the block buffers: `BufAt` of the places `noCol` -/
theorem bufAt_noCol {Q : Spots} {c : Nat} {m : Machine} (h : BufC Q c m) (hc : ¬ colP Q ≤ c) : BufAt (noCol Q) m :=
  fun hs i h1 h2 hch ht => absurd (h hs i h1 h2 hch ht) hc

/-! ## The frames before the touch's frame -/

theorem okSK_noCol (E : Env) (Q : Spots) (A : AS) : okSK E (noCol Q) A = okSK E Q A := rfl

/-- the walk with the test `okSK` looks at the places only through the block buffers' bytes -/
theorem walkKS_noCol (C : FrameKeep.CfgK) (Q : Spots) : ∀ (n : Nat) (A : AS), walkKS C (noCol Q) n A = walkKS C Q n A
  | 0, _ => rfl
  | n + 1, A => by
    simp only [walkKS, okSK_noCol, walkKS_noCol C Q n]

/-- **The check of the frames is the check for the places `noCol`** -/
theorem keepCheckS_noCol {S : FrameKeep.Spot} {G : Guard} {E : Env} {W : List Watch} {key : AS → Nat} {fin : AS → Bool} {Q : Spots} :
    keepCheckS S G E W key fin (noCol Q) = keepCheckS S G E W key fin Q := by
  have e : walkKS (FrameKeep.cfgOfKW S G E W key fin) (noCol Q) = walkKS (FrameKeep.cfgOfKW S G E W key fin) Q :=
    funext fun n => funext fun A => walkKS_noCol _ Q n A
  simp only [keepCheckS, e]

/-- **One frame keeps the slot's map**: it starts as `FrameStart` asks, with the watched bits, its instructions meet `CleanK` and `BufC`. With the parser's
column before the pole's, no step writes a pole's tile into the block buffers (`bufAt_noCol`), and the walk of the frame keeps the map of the places `noCol`
(`PoleTileWalk.frame_colMap`) -/
theorem frame_slot {S : FrameKeep.Spot} {G : Guard} {E : Env} {W : List Watch} {key : AS → Nat} {fin : AS → Bool} {Q : Spots} {c : Nat}
    (hc : keepCheckS S G E W key fin Q = true) (hE : E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hw : Watched W m)
    (hk : ∀ j, CleanK G S.store (trace m i j)) (hb : ∀ j, BufC Q c (trace m i j)) (hm : SlotMap Q c m) : SlotMap Q c (frame m i) := by
  by_cases hD : colP Q ≤ c
  · exact Or.inl hD
  · rcases hm with h | h
    · exact absurd h hD
    · exact Or.inr (PoleTileWalk.frame_colMap (keepCheckS_noCol.trans hc) hE h0 hw hk (fun j => bufAt_noCol (hb j) hD) h)

/-- **The slot's map at every frame's start up to the touch's frame**: from the map at control (`hz0`), with `BufC` on each instruction of each frame for the
column `c n` of its start, and the column not going back (`hcm`). The watched bits of the walk come from `PoleTileKeep.frames_keepY`. -/
theorem frames_slot {sy : Syms} {m0 : Machine} {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hc : FrameKeep.keepCheckOf sy m0 = true)
    (hcY : PoleTileKeep.keepCheckOfY sy m0 = true) (K : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0))
    (h0 : Watched (FrameKeep.watchOf sy) (seq 0)) (hw0 : Watched (PoleTileKeep.watchB sy m0) (seq 0)) (hm0 : ColMap (spotsF sy m0) (seq 0))
    (hkb : ∀ n, n + 1 < K.ix g → ∀ k, PoleTileKeep.KeepB sy m0 (trace (K.all n) (K.inp n) k))
    (hb : ∀ n, n + 1 < K.ix g → ∀ k, BufAt (spotsF sy m0) (trace (K.all n) (K.inp n) k))
    (c : Nat → Nat) (hcm : ∀ n, n + 1 < K.ix g → c n ≤ c (n + 1))
    (hbc : ∀ n, n + 1 < K.ix g → ∀ k, BufC (spotsF sy m0) (c n) (trace (K.all n) (K.inp n) k))
    (hz0 : SlotMap (spotsF sy m0) (c 0) (K.all 0)) :
    ∀ n, n < K.ix g → SlotMap (spotsF sy m0) (c n) (K.all n) := by
  have hY := PoleTileKeep.frames_keepY hc hcY K hs0 h0 hw0 hm0 hkb hb
  intro n
  induction n with
  | zero => exact fun _ => hz0
  | succ i ih =>
    intro hi
    have hzi := ih (by omega)
    obtain ⟨a1, a2⟩ := K.all_start hc hs0 h0 i (by omega)
    have a1' : FrameStart (PoleTileKeep.GK sy m0) (PipeEntryRule.envOf m0) (K.all i) := PoleTileKeep.start_prot a1
    have a2' : Watched (PoleTileKeep.watchY sy m0) (K.all i) := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact a2 w hw
      · exact (hY i (by omega)).2 w hw
    have hcl : ∀ k, CleanK (PoleTileKeep.GK sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all i) (K.inp i) k) :=
      fun k => PoleTileKeep.cleanK_GK (K.clean i (by omega) k) (hkb i hi k)
    rw [K.next i]
    exact slotMap_mono (frame_slot hcY rfl a1' a2' hcl (hbc i hi) hzi) (hcm i hi)

/-! ## The touch's frame -/

/-- **What stays assumed of a read far from the pole at the pole's column** (round 33, the field `PoleJoin.Run.tilesCol`): `PoleTileFar.TileSlot` without its
part (`slot`): (`near`) his pixel is at most 112 px left of the edge `e₀` of the frame's start; (`read`) with his page two before the pole's, the read is in the
column of his pixel plus less than 16 px, mod 32 -/
def TileSlotN (Q : Spots) (e₀ : Nat) (m : Machine) : Prop :=
  m.pc = Q.read + 2 → m.ram.get! Q.saveI ∈ Q.idx → (m.ram.get! Q.pI).toNat + 1 < Q.pg → onCol Q (readAt Q m) = true →
    e₀ ≤ (m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat + 112 ∧
    ((m.ram.get! Q.pI).toNat + 2 = Q.pg →
      ∃ a, a < 16 ∧ ((m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat + a) / 16 % 32 = (16 * Q.pg + Q.col.toNat) % 32)

/-- the round 30 condition gives the round 33 one (it asks less) -/
theorem tileSlotN_of {Q : Spots} {c₀ e₀ : Nat} {m : Machine} (h : TileSlot Q c₀ e₀ m) : TileSlotN Q e₀ m := fun a b c d => (h a b c d).2

/-- with the parser's column at the pole's, `TileSlotN` is `TileSlot` -/
theorem tileSlot_of_N {Q : Spots} {c₀ e₀ : Nat} {m : Machine} (h : TileSlotN Q e₀ m) (hD : colP Q ≤ c₀) : TileSlot Q c₀ e₀ m :=
  fun a b c d => ⟨fun _ => hD, h a b c d⟩

/-- **What is assumed of a read far from the pole at the pole's column from round 33, part two** (the field `PoleJoin.Run.tilesCol`): right after a read of the side
check with his page two or more before the pole's, at the pole's column, the parser's column `c₀` at the start of the touch's frame has not come to the pole's -/
def TileSlotC (Q : Spots) (c₀ : Nat) (m : Machine) : Prop :=
  m.pc = Q.read + 2 → m.ram.get! Q.saveI ∈ Q.idx → (m.ram.get! Q.pI).toNat + 1 < Q.pg → onCol Q (readAt Q m) = true → c₀ < colP Q

/-- **`TileSlotC` from (`near`) and (`read`)** and the parser's column at most 384 px past the edge `e₀` (`16·c₀ ≤ e₀ + 384`, the parser's invariant): the arithmetic of
`PoleTileFar.tileCol_of_slot`. So on the route, where the invariant is proved, `TileSlotC` asks less than `TileSlotN` -/
theorem tileSlotC_of_N {Q : Spots} {c₀ e₀ : Nat} {m : Machine} (h : TileSlotN Q e₀ m) (hc : 16 * c₀ ≤ e₀ + 384) : TileSlotC Q c₀ m := by
  intro h1 h2 hpg hon
  obtain ⟨hn, hr⟩ := h h1 h2 hpg hon
  have hx : (m.ram.get! Q.xI).toNat < 256 := (m.ram.get! Q.xI).toNat_lt
  unfold colP
  by_cases h2p : (m.ram.get! Q.pI).toNat + 2 = Q.pg
  · obtain ⟨a, ha, hm⟩ := hr h2p
    omega
  · omega

/-- the round 30 condition gives `TileSlotC`, with the parser's invariant -/
theorem tileSlotC_of_slot {Q : Spots} {c₀ e₀ : Nat} {m : Machine} (h : TileSlot Q c₀ e₀ m) (hc : 16 * c₀ ≤ e₀ + 384) : TileSlotC Q c₀ m :=
  tileSlotC_of_N (tileSlotN_of h) hc

/-- the pole with the places `noCol` -/
def noColT (T : Pole) : Pole := { T with Q := noCol T.Q }

theorem onCol_noColT (T : Pole) {i : Nat} (h : i < 2048) : onCol (noColT T).Q i = false := onCol_noCol T.Q h

theorem zone_noCol {T : Pole} (hb : ZoneOK T) : ZoneOK (noColT T) :=
  ⟨⟨hb.pre.xI, hb.pre.pI, hb.pre.saveI, hb.pre.left, hb.pre.lo, hb.pre.pg1, hb.pre.pg2, hb.pre.posP, hb.pre.posL, hb.pre.cover⟩, hb.ptr⟩

theorem read_noCol {T : Pole} {E : Env} (hR : PoleTileWalk.ReadFacts T E) : PoleTileWalk.ReadFacts (noColT T) E :=
  ⟨hR.r0, hR.r1, hR.op, hR.z1, hR.z2, hR.idle⟩

/-- **The byte read is not a pole's tile**, right after a read of the side check that the walk knows (the tests `pairOK` and `PoleTileFar.readPF`), when no byte of
the block buffers holds a pole's tile before it: `PoleTileFar.tileRead_afterF` on the places `noCol` -/
theorem noTile_after {T : Pole} {E : Env} {F : Nat × UInt8} {A₁ B : AS} {m : Machine} (hb : ZoneOK T) (hR : PoleTileWalk.ReadFacts T E) (hs : Sim E F A₁ m)
    (hpair : pairOK T.Q A₁ B = true) (hrp : PoleTileFar.readPF T.Q A₁ B = true) (hBpc : B.pc = T.Q.read + 2) (hsn : SideFrame.sideNow T.Q B = true)
    (hm : ColMap (noCol T.Q) m) :
    (go step m).2.pc = T.Q.read + 2 → (go step m).2.ram.get! T.Q.saveI ∈ T.Q.idx → ¬ ((go step m).2.a = T.Q.ball ∨ (go step m).2.a = T.Q.shaft) := by
  intro hpc hsv ht
  have hcol : TileCol (noColT T).Q (go step m).2 := fun _ _ _ h => by
    rw [onCol_noColT T (readAt_lt _ _)] at h
    cases h
  have h := PoleTileFar.tileRead_afterF (T := noColT T) (zone_noCol hb) (read_noCol hR) hs hpair hrp hBpc hsn hm hcol hpc hsv ht
  have h1 := h.1
  rw [onCol_noColT T (readAt_lt _ _)] at h1
  cases h1

/-- **The frame.** As `PoleTileKeep.no_write_frameZ`, with the slot's map at the frame's start for the parser's column `c`, and on each instruction `BufC` and
`TileSlotC` in place of `TileCol`: right after each read of the side check that the walk knows, `TileCol` is proved: at a far read at the pole's column the
parser's column has not come to the pole's (`TileSlotC`), so by the map no byte of the block buffers holds a pole's tile (`noTile_after`). The slot's map goes on
from step to step as the map does. -/
theorem no_write_frameZS {T : Pole} {H : HP} {R : List (UInt16 × UInt16)} {Z : List Nat} {E : Env} {W : List Watch} (hp : T.Q.ptrI + 1 < 2048)
    (hc : PoleTileKeep.frameCheckZ T H R Z E W = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat} {c : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart T.G E (s 0)) (hw0 : Watched W (s 0))
    (hm0 : ColMap T.Q (s 0)) (hz0 : SlotMap T.Q c (s 0))
    (hh : ∀ j, j ≤ n → CleanK T.G T.K.store (s j) ∧ PosAt T.Q T.ps (s j) ∧ HypR T (s j) ∧ BufAt T.Q (s j) ∧ BufC T.Q c (s j) ∧ TileSlotC T.Q c (s j)) :
    (s (n + 1)).ram.get! T.G.rtI ≠ T.G.ev := by
  have hC := PoleTileKeep.frameOKZ_of_check hp hc
  obtain ⟨b, hsim⟩ := FrameKeep.sim_startK hE h0 hw0
  have hkl : (PoleTileKeep.cfgOfZ T H R Z E W).kl = (PoleTileKeep.cfgOfZ T H R Z E W).t.map knownOf := rfl
  have hT2 : 2 ≤ (2 : UInt8).toNat := by decide
  have hstart : ∃ A, PoleTileKeep.LiveZ (PoleTileKeep.cfgOfZ T H R Z E W) H R Z ((s 0).frame, 2) A (s 0) ∧ TR T.Q A (s 0) := by
    have hT0 : ∀ A : AS, Sim E ((s 0).frame, 2) A (s 0) → TR T.Q A (s 0) := by
      intro A hA hpc
      rw [← hA.pc, h0.pc] at hpc
      exact absurd hpc hC.read.idle
    cases b with
    | false => exact ⟨_, ⟨hsim, PoleTileKeep.startY_k T W false, fuelG, hC.s0⟩, hT0 _ hsim⟩
    | true => exact ⟨_, ⟨hsim, PoleTileKeep.startY_k T W true, fuelG, hC.s1⟩, hT0 _ hsim⟩
  have live : ∀ j, j ≤ n → (∃ A, PoleTileKeep.LiveZ (PoleTileKeep.cfgOfZ T H R Z E W) H R Z ((s 0).frame, 2) A (s j) ∧ TR T.Q A (s j)) ∧
      ColMap T.Q (s j) ∧ SlotMap T.Q c (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hstart, hm0, hz0⟩
    | succ j ih =>
      intro hj
      obtain ⟨⟨A, hA, hTA⟩, hmj, hzj⟩ := ih (by omega)
      obtain ⟨hh1, hp1, hr1, hb1, hbc1, _⟩ := hh j (by omega)
      obtain ⟨A₁, B, hs1, hok, _, hpair, hrp, _, h2⟩ :=
        PoleTileKeep.live_stepZ hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hr1 hTA
      have hsl : TileSlotC T.Q c (go step (s j)).2 := by
        rw [← hs j (by omega)]
        exact (hh (j + 1) hj).2.2.2.2.2
      have hmj1 := PoleTileWalk.colMap_step hs1 hok hb1 hmj
      have hzj1 : SlotMap T.Q c (go step (s j)).2 := by
        by_cases hD : colP T.Q ≤ c
        · exact Or.inl hD
        · rcases hzj with h | h
          · exact absurd h hD
          · exact Or.inr (PoleTileWalk.colMap_step (T := noColT T) hs1 hok (bufAt_noCol hbc1 hD) h)
      rw [← hs j (by omega)] at hmj1 hzj1
      refine ⟨?_, hmj1, hzj1⟩
      rcases h2 with h2 | ⟨A', hA', hAB⟩
      · have h3 := hf (j + 1) hj
        have h4 : (s 0).frame < (s (j + 1)).frame := by rw [hs j (by omega)]; exact h2
        omega
      · refine ⟨A', by rw [hs j (by omega)]; exact hA', fun hpc hsn => ?_⟩
        have e := hAB hpc
        subst e
        have hcol : TileCol T.Q (go step (s j)).2 := by
          rcases hzj with hD | hM
          · exact fun h1 h2 hpg hon _ => absurd (hsl h1 h2 hpg hon) (Nat.not_lt.2 hD)
          · exact fun h1 h2 _ _ ht => noTile_after hC.zone hC.read hs1 hpair hrp hpc hsn hM h1 h2 ht
        rw [hs j (by omega)]
        exact PoleTileFar.tileRead_afterF hC.zone hC.read hs1 hpair hrp hpc hsn hmj hcol
  obtain ⟨⟨A, hA, hTA⟩, _, _⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hp1, hr1, _, _, _⟩ := hh n (Nat.le_refl n)
  obtain ⟨_, _, _, _, _, _, _, h1, _⟩ := PoleTileKeep.live_stepZ hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hr1 hTA
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-- **The touch on a real frame, at the end of the move**: as `PoleTileKeep.touch_right_of_leftZ`, with the slot's map at the frame's start, and up to the
write `BufC` and `TileSlotC` in place of `TileCol` -/
theorem touch_right_of_leftZS {sy : Syms} {m0 m : Machine} {i : UInt8} {c : Nat} (hc : PoleTileKeep.poleCheckZ sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hw : Watched (PoleTileKeep.watchB sy m0) m)
    (hk : ∀ j, CleanK (PoleTileKeep.GK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m) (hz : SlotMap (spotsF sy m0) c m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hbc : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufC (spotsF sy m0) c (trace m i j))
    (hsl : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileSlotC (spotsF sy m0) c (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k)) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) := by
  simp only [PoleTileKeep.poleCheckZ, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp, hc⟩, _⟩, _⟩ := hc
  have hp' : (spotsF sy m0).ptrI + 1 < 2048 := by simpa [ptrOK] using hp
  obtain ⟨n, hw'⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw', a, b, c⟩
  · exfalso
    have hn := no_write_frameZS (T := PoleTileKeep.poleY sy m0) (H := hpOf sy m0) (s := trace m i) (n := n) hp' hc rfl
      (fun j hj => PoleEntryRule.step_before hw' j hj) (fun j hj => frame_before hw' j hj)
      (by rw [PoleTileKeep.poleY_G]; exact start_with (PoleTileKeep.start_prot (h0.pad _))) hw hm hz
      (fun j hj => ⟨by rw [PoleTileKeep.poleY_G]; exact cleanK_with (hk j), hpk n hw' j hj, ⟨fun hs => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd ⟨j, hj, hs, hl⟩ hx
        · exact Nat.lt_of_not_le hl, fun ha => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd (hag n hw' j hj ha hl) hx
        · exact Nat.lt_of_not_le hl, by
        show (trace m i j).pc ∉ ([] : List UInt16)
        simp⟩, hbuf n hw' j hj, hbc n hw' j hj, hsl n hw' j hj⟩)
    exact hn hw'.2

/-- **In the pole's range, from one whole frame**: as `PoleTileKeep.inRange_of_frameZ`, with the slot's map and `TileSlotC` in place of `TileCol` -/
theorem inRange_of_frameZS {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} {c : Nat} (hc : PoleTileKeep.poleCheckZ sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hw : Watched (PoleTileKeep.watchB sy m0) m)
    (hk : ∀ j, CleanK (PoleTileKeep.GK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m) (hz : SlotMap (spotsF sy m0) c m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hbc : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufC (spotsF sy m0) c (trace m i j))
    (hsl : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileSlotC (spotsF sy m0) c (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k))
    (hmoved : ∀ n j, WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SurfaceRun.poleP sy m0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := touch_right_of_leftZS hc he h0 hw hk hpk hm hz hbuf hbc hsl hag
  rw [hmoved n j h1 h2 h3]
  have h5 : (spotsF sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  have h7 : (spotsF sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (spotsF sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h5, h7, h8] at h4
  unfold SurfaceRun.poleP posP peek
  omega

end Smbrta.PoleSlot
