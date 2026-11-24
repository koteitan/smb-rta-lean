import Theorems.PoleStrict
/-!
# The area parser on the route's frames up to the touch, and the reads far from the pole

Rounds 27 and 28 proved the area parser's invariant `Inv` (`16·col + 16·p(N) + S = edge + 384`, `N ≤ 8`) at control and the rule of one frame that keeps it, and
`PoleParser.inv_onFrames` carried it over the frames of a run under conditions on each frame. Here those conditions come from the route (`PoleJoin.Run`):

* no store through an index or a pointer writes the parser's four bytes: `FrameKeep.guardE` protects them (`FrameKeep.parE`, the same bytes as `PoleParser.pI`:
  `pI_eq`), so the field `cleanE` of the frames gives `CleanK` of `PoleParser.guardPI` (`cleanPI_of_E`);
* the area's type, the swimming flag and the change of size: `SurfaceFrames.AreaRun`;
* the field `posW` of the counted frames from the scroll handler on: a frame before the touch's frame that comes to the player's routine is a counted frame
  (`counted_of`: a frame that is not counted does not come there, `SurfaceFrames.OnFrames.lagNo`), and its first arrival is not before `CtrlKeep.arrAt` (`arrAt_le`);
* no wrap of the scroll counter (round 29: the field `PoleJoin.Run.parWrap`; round 31: not a field, `PoleStrict.invJ_onFrames` keeps `JV` with the field
  `ctlU`, the scroll's amount at most 3 (`amount_run`) and `JV` at control) and the edge below 64,896 px (`noWrap_of`). The edge's bound is a theorem (`edgeLow_run`): part
  e bounds the edge at the end of each counted frame by the position's range when the touch is not later than `farN` frames after control
  (`SurfaceFrames.OnFrames.readAllB`), the frames not counted keep the edge (`lag_edge`), and one number on the ROM, `posP(B.m) + 16·top·farN < 64896·256`, closes it.

So the invariant holds at every frame's start up to the touch's frame (`inv_run`), and with it the parser's column at the start of the touch's frame is at most 384 px
past the screen's left edge. That and the field `PoleJoin.Run.tilesCol` (`PoleTileFar.TileSlot`) give `PoleTileFar.TileCol` on the touch's frame (`tilesCol_run`),
which was the old field `tilesCol`; on the route, with the invariant and the column at control from the rows of the change (`PoleParser.inv₀`, `PoleParser.col₀`):
`tilesCol_route`. Round 33 (`PoleSlot`, `1-1/f-6-17-14-PoleSlot.md`): `tilesCol_run` gives what the touch's frame needs of the parser
(`PoleJoin.Run.TileColAll`): the bound at the start of the touch's frame, the parser's column not going back from frame to frame (`colMono_run`, from the weak
rule of each frame: `PoleStrict.ruleW_onFrames`), and no pole's tile in the block buffers at control; the part (`slot`) of `TileSlot` is then a theorem of the walk
of the touch's frame (`PoleSlot.no_write_frameZS`).

There is no game data in this file. Page: `1-1/f-6-17-10-PoleParserRun.md`.
-/

namespace Smbrta.PoleParserRun

open PoleParser
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-! ## The bytes -/

/-- the parser's four bytes of `PoleParser` are those that `FrameKeep.guardE` protects as `FrameKeep.parE` -/
theorem pI_eq : pI sy m0 = FrameKeep.parE sy m0 := rfl

/-- the parser's column of `PoleJoin` is that of `PoleParser` -/
theorem parCol_eq (m : Machine) : PoleJoin.parColOf sy m0 m = colOf (places sy m0) m := rfl

/-- the screen's left edge of the scroll's rule is that of `PoleParser` -/
theorem edge_eq (m : Machine) : ScrollRule.left16 (ScrollRule.places sy m0) m = edgeOf (places sy m0) m := rfl

/-- **`FrameKeep.guardE` protects the parser's four bytes** -/
theorem par_mem {x : Nat} (hx : x ∈ FrameKeep.parE sy m0) : x ∈ (FrameKeep.guardE sy m0).prot :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_append_left _ hx)))))))

/-- **`CleanK` of `guardE` gives `CleanK` of `PoleParser.guardPI`**: each byte that `guardPI` protects, `guardE` protects -/
theorem cleanPI_of_E {q : UInt16} {m : Machine} (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) : FrameKeep.CleanK (guardPI sy m0) q m :=
  FrameKeep.cleanK_sub h (fun x hx => by
    rcases List.mem_append.1 hx with h1 | h1
    · exact par_mem (pI_eq (sy := sy) (m0 := m0) ▸ h1)
    · exact List.mem_append_right _ h1) rfl rfl rfl rfl

/-- **No wrap of the scroll** (`PoleParser.NoWrap`) from no wrap of the counter (`PoleJoin.NoWrapP`) and the edge below `65280 − 384` px -/
theorem noWrap_of {m u : Machine} (h : PoleJoin.NoWrapP sy m0 m u) (he : ScrollRule.left16 (ScrollRule.places sy m0) m + 384 < 65280) : NoWrap sy m0 m u := by
  intro Y hY
  have hy : Y.toNat < 256 := Y.toNat_lt
  exact ⟨h Y hY, by
    have e : ScrollRule.left16 (placesS sy m0) m = ScrollRule.left16 (ScrollRule.places sy m0) m := rfl
    rw [e]
    omega⟩

/-! ## The frames that come to the player's routine -/

section Counted
variable {B : PoleJoin.Box} {T J g : Nat} {seq : Nat → Machine} {S : FrameKeep.RealRun} {a : Nat} {K : FrameKeep.Frames sy m0 S a g seq}

/-- for a frame `n` before the touch's frame, the counted frame in which it ends or before whose end it ends -/
theorem frame_between (K : FrameKeep.Frames sy m0 S a g seq) {n : Nat} :
    ∀ j, j ≤ g → n + 1 ≤ K.ix j → ∃ j', 1 ≤ j' ∧ j' ≤ j ∧ K.ix (j' - 1) ≤ n ∧ n + 1 ≤ K.ix j' := by
  intro j
  induction j with
  | zero =>
    intro _ h
    rw [K.ix0] at h
    omega
  | succ j ih =>
    intro hj h
    by_cases h2 : n + 1 ≤ K.ix j
    · obtain ⟨j', a1, a2, a3, a4⟩ := ih (by omega) h2
      exact ⟨j', a1, by omega, a3, a4⟩
    · exact ⟨j + 1, by omega, Nat.le_refl _, by rw [Nat.add_sub_cancel]; omega, h⟩

/-- **A frame before the touch's frame that comes to the player's routine is a counted frame**: a frame that is not counted ends paused and does not come there
(`SurfaceFrames.OnFrames.lagNo`) -/
theorem counted_of (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (Ar : SurfaceFrames.AreaRun sy m0 K v) (O : SurfaceFrames.OnFrames sy m0 B T J g seq K)
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {n : Nat} (hn : n + 1 < K.ix g) {n₀ : Nat}
    (h1 : (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine) (h2 : (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame) :
    ∃ j, 1 ≤ j ∧ j < g ∧ K.ix j = n + 1 := by
  obtain ⟨j, a1, a2, a3, a4⟩ := frame_between K g (Nat.le_refl g) (Nat.le_of_lt hn)
  rcases Nat.lt_or_eq_of_le a4 with h5 | h5
  · exact absurd h1 (O.lagNo hck Ar hst j a1 a2 n a3 h5 n₀ h2)
  · refine ⟨j, a1, ?_, h5.symm⟩
    rcases Nat.lt_or_eq_of_le a2 with h6 | h6
    · exact h6
    · subst h6
      omega

/-- **The first arrival at the player's routine is not before `CtrlKeep.arrAt`** -/
theorem arrAt_le {M : Machine} {i : UInt8} {n₀ : Nat} (h1 : (trace M i n₀).pc = sy.PlayerCtrlRoutine) : CtrlKeep.arrAt sy M i ≤ n₀ := by
  have key : ∀ (f : Nat → Bool) (L : Nat), f n₀ = true → CtrlKeep.firstUpTo f L ≤ n₀ := by
    intro f L hf
    have hs := (CtrlKeep.firstUpTo_spec f L).2.1
    by_cases h : n₀ < CtrlKeep.firstUpTo f L
    · have e := hs n₀ h
      rw [hf] at e
      cases e
    · omega
  unfold CtrlKeep.arrAt
  exact key _ _ (by simp only [h1, beq_self_eq_true])

/-- **`posW` on every frame before the touch's frame that comes to the player's routine**, from its first arrival there: the frame is a counted frame (`counted_of`),
whose field `posW` holds from `CtrlKeep.arrAt` on (`arrAt_le`); no instruction from the scroll handler to the frame's end is a store of the position by its address
outside the push and the clamp (`EdgeStep.cutPos`) -/
theorem cut_of_posW (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (Ar : SurfaceFrames.AreaRun sy m0 K v) (O : SurfaceFrames.OnFrames sy m0 B T J g seq K)
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {n : Nat} (hn : n + 1 < K.ix g) {n₀ : Nat}
    (h1 : (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine) (h2 : (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame)
    {k : Nat} (hk : n₀ ≤ k) (hpc : (trace (K.all n) (K.inp n) k).pc = sy.PlayerSubs) {j : Nat} (hj : k ≤ j)
    (hf : (trace (K.all n) (K.inp n) j).frame = (K.all n).frame) : EdgeStep.cutPos sy m0 (trace (K.all n) (K.inp n) j).pc = false := by
  obtain ⟨c, c1, c2, c3⟩ := counted_of hck Ar O hst hn h1 h2
  have efm : K.fm c = K.all n := by
    show K.all (K.ix c - 1) = K.all n
    rw [c3, Nat.add_sub_cancel]
  have epad : K.pad c = K.inp n := by
    show K.inp (K.ix c - 1) = K.inp n
    rw [c3, Nat.add_sub_cancel]
  have ha := arrAt_le h1
  have W := (O.posW c c1 c2 k j (by rw [efm, epad]; omega) hj (by rw [efm, epad]; exact hpc) (by rw [efm, epad]; exact hf)).1
  rw [efm, epad] at W
  have h0 := hst n (by omega)
  have hpg := StepPrg.trace_prg (K.all n) (K.inp n) j
  have e1 : (trace (K.all n) (K.inp n) j).prg = m0.prg := hpg.1.trans h0.prg
  have e2 : (trace (K.all n) (K.inp n) j).prgMask = m0.prgMask := hpg.2.trans h0.mask
  rw [e1, e2] at W
  unfold EdgeStep.cutPos
  cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (trace (K.all n) (K.inp n) j).pc with
  | false => rfl
  | true => rw [W hs]; rfl

/-- **The frames not counted between two counted frames keep the edge's two bytes**: as `SurfaceFrames.OnFrames.edgeLag`, for each frame from the end of the
counted frame `j − 1` up to the start of the counted frame `j` -/
theorem lag_edge (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (Ar : SurfaceFrames.AreaRun sy m0 K v) (O : SurfaceFrames.OnFrames sy m0 B T J g seq K)
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) :
    ∀ d, K.ix (j - 1) + d + 1 ≤ K.ix j → ∀ x ∈ EdgeStep.eI sy m0, (K.all (K.ix (j - 1) + d)).ram.get! x = (K.all (K.ix (j - 1))).ram.get! x := by
  have hg := K.ix_mono j g (by omega) (Nat.le_refl g)
  intro d
  induction d with
  | zero => exact fun _ _ _ => rfl
  | succ d ih =>
    intro hd x hx
    have hn := K.next (K.ix (j - 1) + d)
    rw [show K.ix (j - 1) + (d + 1) = K.ix (j - 1) + d + 1 by omega, hn]
    rw [EdgeStep.keep_noCut Ar.eq (hst _ (by omega)) (K.clean _ (by omega)) (O.lagNo hck Ar hst j h1 h3 _ (by omega) (by omega)) x hx]
    exact ih (by omega) x hx

end Counted

/-! ## The edge below 64,896 px on the frames before the touch

Part e bounds the position and the edge on the counted frames up to the touch, when the touch is not later than `farN` frames after control (`OnFrames.readAllB`): the
larger of the position and the edge at the end of the counted frame `d` is at most `posP(B.m) + 16·top·d` (in 1/256 px). The frames not counted keep the edge's
bytes (`lag_edge`). So one number on the ROM, `posP(B.m) + 16·top·farN < 64896·256`, puts the edge below 64,896 px at every frame's start before the touch's frame. -/

/-- `SurfaceRead.edgeOf` (in 1/256 px, with the places from the machine's own program) and the edge of the scroll's rule -/
theorem surf_edge {m : Machine} (hp : m.prg = m0.prg) (hk : m.prgMask = m0.prgMask) :
    SurfaceRead.edgeOf sy m = (ScrollRule.left16 (ScrollRule.places sy m0) m : Int) * 256 + 255 := by
  have e1 : ScrollRule.left16 (ScrollRule.places sy m0) m =
      (peek m (ScreenClamp.places sy m0).edgeP).toNat * 256 + (peek m (ScreenClamp.places sy m0).edgeX).toNat := rfl
  unfold SurfaceRead.edgeOf
  rw [SurfaceRead.places_congr hp hk, e1]
  omega

/-- the bytes of the edge of the scroll's rule are those of `EdgeStep.eI` -/
theorem left16_of_eI {m m' : Machine} (h : ∀ x ∈ EdgeStep.eI sy m0, m.ram.get! x = m'.ram.get! x) :
    ScrollRule.left16 (ScrollRule.places sy m0) m = ScrollRule.left16 (ScrollRule.places sy m0) m' := by
  have hx : ∀ x ∈ EdgeStep.eI sy m0, m.ram.get! x = m'.ram.get! x := h
  have a := hx _ (List.mem_cons_self (a := ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat))
  have b := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self (a := ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat)))
  show (m.ram.get! ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat).toNat * 256 + (m.ram.get! ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat).toNat =
    (m'.ram.get! ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat).toNat * 256 + (m'.ram.get! ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat).toNat
  rw [a, b]

/-! ## On the route's frames up to the touch -/

section Run
variable {b : Machine} {vs : List Jump.VS} {B : PoleJoin.Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat}

/-- **The edge below 64,896 px at every frame's start before the touch's frame**: the frame starts with the edge of the end of a counted
frame `d < g` (`lag_edge`), and there the edge is at most `posP(B.m) + 16·top·d` (`SurfaceFrames.OnFrames.readAllB`, with `g ≤ farN`); `hb` is the number on the ROM -/
theorem edgeLow_run (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hfq : PoleJoin.fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hF : ∀ n, n < R.keep.toFrames.ix R.g → SideAcross.FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n))
    (hg : R.g ≤ SurfaceFrames.farN sy B.m)
    (hb : posP sy B.m + 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy B.m : Int) < 64896 * 256) :
    ∀ n, n + 1 < R.keep.toFrames.ix R.g → ScrollRule.left16 (ScrollRule.places sy m0) (R.keep.toFrames.all n) + 384 < 65280 := by
  have Nm := SurfaceFrames.numbers_of_check hN
  have hw0 := R.watched₀ st hfq hc0.castle
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start hw0 n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst hF
  have h16 : (16 : Int) ≤ (TopSpeed.top sy : Int) := by
    have := (FrameModel.facts_of Nm.model).top16
    show (16 : Int) ≤ (TopSpeed.top sy : Int)
    omega
  intro n hn
  obtain ⟨j, a1, a2, a3, a4⟩ := frame_between R.keep.toFrames R.g (Nat.le_refl _) (Nat.le_of_lt hn)
  have hL := lag_edge Nm.ctrl Ar R.frames hst a1 a2 (n - R.keep.toFrames.ix (j - 1)) (by omega)
  rw [show R.keep.toFrames.ix (j - 1) + (n - R.keep.toFrames.ix (j - 1)) = n by omega] at hL
  have e1 := left16_of_eI hL
  have hs : R.keep.toFrames.all (R.keep.toFrames.ix (j - 1)) = R.keep.seq (j - 1) := (R.keep.toFrames.at_ix (j - 1) (by omega)).symm
  rw [e1, hs]
  obtain ⟨_, hr⟩ := R.frames.readAllB Nm.ctrl Nm.model hfr Nm.idle hst Ar (SurfaceFrames.start_v0 hN st) st.P hg (j - 1) (by omega)
  have hb2 := (hr (by omega)).2
  have hst' := hst (R.keep.toFrames.ix (j - 1)) (by have := R.keep.toFrames.ix_mono (j - 1) R.g (by omega) (Nat.le_refl _); omega)
  rw [hs] at hst'
  have he := surf_edge (sy := sy) (m0 := m0) hst'.prg hst'.mask
  have hle : SurfaceRead.edgeOf sy (R.keep.seq (j - 1)) ≤ SurfaceRead.baseOf sy (R.keep.seq (j - 1)) := Int.le_max_right _ _
  have hmul : 16 * (TopSpeed.top sy : Int) * ((j - 1 : Nat) : Int) ≤ 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy B.m : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega

/-- **The scroll's amount at most 3** (round 31): on each frame before the touch's frame that comes to the player's routine, at each call
of the player's subroutines from an arrival there on, the scroll's amount, when it is in 1 ‥ 128, is at most 3. The frame is a counted frame `c` (`counted_of`);
part e reads it up to the scroll handler (`SurfaceFrames.OnFrames.readH`, with the speed and the position of the frame before from `OnFrames.readAll`); there the
byte the move stores is his pixel's move from the arrival when it is in 1 ‥ 128 (`MoveScroll.move_xs`), the position moved by `16·v₂` with `|v₂| ≤ top`
(`SurfaceRead.read_move`), and the platforms' force is 0 (`OnFrames.scrollAt`, `OnFrames.platPrev`). With `top ≤ 48` (`htop`, on the ROM), `256·X ≤ 16·48 + 255`,
so `X ≤ 3`. The frame comes to the scroll handler once (`GuardE.subs_onceE`). -/
theorem amount_run (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hfq : PoleJoin.fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hF : ∀ n, n < R.keep.toFrames.ix R.g → SideAcross.FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n))
    (hg : R.g ≤ SurfaceFrames.farN sy B.m) (htop : TopSpeed.top sy ≤ 48) :
    ∀ n, n + 1 < R.keep.toFrames.ix R.g → ∀ n₀, (trace (R.keep.toFrames.all n) (R.keep.toFrames.inp n) n₀).pc = sy.PlayerCtrlRoutine →
      (trace (R.keep.toFrames.all n) (R.keep.toFrames.inp n) n₀).frame = (R.keep.toFrames.all n).frame →
      ∀ k, n₀ ≤ k → (trace (R.keep.toFrames.all n) (R.keep.toFrames.inp n) k).pc = sy.PlayerSubs →
      (trace (R.keep.toFrames.all n) (R.keep.toFrames.inp n) k).frame = (R.keep.toFrames.all n).frame →
      ScrollRule.xOK (ScrollRule.amountOf (ScrollRule.places sy m0) (trace (R.keep.toFrames.all n) (R.keep.toFrames.inp n) k)) = true →
      (ScrollRule.amountOf (ScrollRule.places sy m0) (trace (R.keep.toFrames.all n) (R.keep.toFrames.inp n) k)).toNat ≤ 3 := by
  have Nm := SurfaceFrames.numbers_of_check hN
  have hw0 := R.watched₀ st hfq hc0.castle
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start hw0 n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst hF
  intro n hn n₀ a1 a2 k hk0 hpk _ hxo
  obtain ⟨c, c1, c2, c3⟩ := counted_of Nm.ctrl Ar R.frames hst hn a1 a2
  have efm : R.keep.toFrames.fm c = R.keep.toFrames.all n := by
    show R.keep.toFrames.all (R.keep.toFrames.ix c - 1) = R.keep.toFrames.all n
    rw [c3, Nat.add_sub_cancel]
  have epad : R.keep.toFrames.pad c = R.keep.toFrames.inp n := by
    show R.keep.toFrames.inp (R.keep.toFrames.ix c - 1) = R.keep.toFrames.inp n
    rw [c3, Nat.add_sub_cancel]
  rw [← efm, ← epad] at a1 hpk hxo ⊢
  have hix : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  have hgc := R.keep.toFrames.ix_mono c R.g (by omega) (Nat.le_refl _)
  have hc1 := R.keep.toFrames.one_le_ix c1 (by omega)
  -- the frame before: the speed in range, and the position far from the ends
  obtain ⟨hsp, hr⟩ := R.frames.readAll Nm.ctrl Nm.model hfr Nm.idle hst Ar (SurfaceFrames.start_v0 hN st) st.P hg (c - 1) (by omega)
  have hn1 : c - 1 < SurfaceFrames.farN sy B.m := by omega
  have hfar := SurfaceFrames.far_of_range hn1 (hr hn1)
  obtain ⟨hR, hSame⟩ := R.frames.readH Nm.ctrl Nm.model hfr Nm.idle hst Ar c1 (by omega) hsp hfar
  have harr := R.frames.arrive Nm.ctrl hst c1 (by omega)
  have hAf : CtrlKeep.AreaOK sy (peek B.m sy.AreaType) (R.keep.toFrames.fm c) := Ar.all _ (by omega)
  have h0 := SurfaceFrames.start_fm hst c1 (by omega)
  have hclE := R.keep.toFrames.cleanE (R.keep.toFrames.ix c - 1) (by show R.keep.toFrames.ix c - 1 < R.keep.toFrames.ix R.g; omega)
  have hxs := R.keep.toFrames.noStore (R.keep.toFrames.ix c - 1) (by show R.keep.toFrames.ix c - 1 + 1 < R.keep.toFrames.ix R.g; omega)
  have honce := GuardE.subs_onceE Nm.ctrl Ar.keep h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
  have hle := arrAt_le a1
  have harrE : R.frames.arr c = CtrlKeep.arrAt sy (R.keep.toFrames.fm c) (R.keep.toFrames.pad c) := rfl
  -- the byte the move stores, and the move
  obtain ⟨k1, hk1, hpk1, hmv⟩ := MoveScroll.move_xs hR Ar.xs honce
  have e1 : k1 = k := honce k1 k hk1 (by omega) hpk1 hpk
  subst e1
  obtain ⟨f, k2, hk2, hpk2, hfv, _, hfP, hv2, _, hP2, _, _, _⟩ := SurfaceRead.read_move hR
  have e2 : k2 = k1 := honce k2 k1 hk2 (by omega) hpk2 hpk
  subst e2
  -- the platforms' force at the scroll handler
  obtain ⟨kq, _, hk3, hpk3, _, _, _, hpq, _, _⟩ := R.frames.scrollAt Nm.ctrl hst Ar c1 c2
  have e3 : kq = k2 := honce kq k2 (by omega) (by omega) hpk3 hpk
  subst e3
  have hp0 : (trace (R.keep.toFrames.fm c) (R.keep.toFrames.pad c) kq).ram.get! (ScrollRule.places sy m0).plat = 0 := by
    rw [Ar.platP, hpq]
    exact R.frames.platPrev Nm.ctrl hst Ar c1 c2
  -- the amount is the byte the move stores
  have ham : ScrollRule.amountOf (ScrollRule.places sy m0) (trace (R.keep.toFrames.fm c) (R.keep.toFrames.pad c) kq) =
      (trace (R.keep.toFrames.fm c) (R.keep.toFrames.pad c) kq).ram.get! (ScrollRule.places sy m0).xs := by
    unfold ScrollRule.amountOf
    rw [hp0]
    exact UInt8.add_zero _
  rw [ham] at hxo ⊢
  have hm := hmv hxo
  have hb1 := hR.before sy.Player_X_Position (by simp [FrameModel.hBytes])
  have hb2 := hR.before sy.Player_PageLoc (by simp [FrameModel.hBytes])
  unfold EdgeStep.pixel16 at hm
  rw [hb1, hb2] at hm
  have hmove := f.move
  rw [hP2, hfP] at hmove
  unfold posP at hmove
  have hv1 : -(TopSpeed.top sy : Int) ≤ f.v₁ ∧ f.v₁ ≤ (TopSpeed.top sy : Int) := by
    have hsp' := hsp
    simp only [TopSpeed.inSpeed, decide_eq_true_eq] at hsp'
    have e := hSame.v
    have hvv : -(TopSpeed.top sy : Int) ≤ f.v ∧ f.v ≤ (TopSpeed.top sy : Int) := by
      rw [hfv, e]
      rcases Int.natAbs_eq (sbyte (peek (R.keep.seq (c - 1)) sy.Player_X_Speed)) with h | h <;> omega
    rcases f.anim with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  have hv2b := f.friction hv1
  have ht48 : (TopSpeed.top sy : Int) ≤ 48 := by exact_mod_cast htop
  have hfr1 := (peek (trace (R.keep.toFrames.fm c) (R.keep.toFrames.pad c) kq) sy.SprObject_X_MoveForce).toNat_lt
  have hfr2 := (peek (R.keep.toFrames.fm c) sy.SprObject_X_MoveForce).toNat_lt
  omega

/-- **The parser's invariant, its column below 16 and `JV` at every frame's start up to the touch's frame**, on the frames of `PoleJoin.Run`
(round 31: `PoleStrict.invJ_onFrames`): from their values at control (`h0`, `hJ`), the checks on the ROM (`hN` the numbers of the machine at control, `hk` that of
`FrameKeep`, `hq`, `he`, `hs` those of the parser's walks for the area's type `v` of the machine at control), the fields `keep.cleanE` (`cleanPI_of_E`),
`frames.posW` (`cut_of_posW`), the control byte not 6 at `UpdScrollVar` (round 35: `PoleJoin.Run.ctl6` from the coin's map and the walk of `PoleCoin`, `hcC`, `hmK`; it was the field `ctlU`), the scroll's amount (`amount_run`, with the check of the scroll's rule `hsc` and `htop`), and the edge's bound (`edgeLow_run`: `hfr`, `hg` the touch not later than `farN` frames after control, `hb`
the number on the ROM) -/
theorem invJ_run (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0))
    (hfq : PoleJoin.fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hF : ∀ n, n < R.keep.toFrames.ix R.g → SideAcross.FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n)) (hg : R.g ≤ SurfaceFrames.farN sy B.m)
    (hb : posP sy B.m + 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy B.m : Int) < 64896 * 256) {v : UInt8} (hv : peek B.m sy.AreaType = v)
    (hq : qCheckP sy m0 v = true) (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true) (htop : TopSpeed.top sy ≤ 48)
    (h0 : Inv (places sy m0) 384 (R.seq 0) ∧ ColOK sy m0 (R.seq 0)) (hJ : PoleWrap.JV (valsOf (places sy m0) (R.seq 0)))
    (hcC : PoleCoin.coinCheck sy m0 = true) (hmK : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))
    (hcN : PoleNear.nCheck sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) :
    ∀ n, n < R.keep.toFrames.ix R.g →
      (Inv (places sy m0) 384 (R.keep.toFrames.all n) ∧ ColOK sy m0 (R.keep.toFrames.all n)) ∧ PoleLag.JY (valsOf (places sy m0) (R.keep.toFrames.all n)) := by
  subst hv
  have hE := edgeLow_run R hN hfr st hfq hk hc0 hF hg hb
  have Nm := SurfaceFrames.numbers_of_check hN
  have hw0 := R.watched₀ st hfq hc0.castle
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start hw0 n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst hF
  have e0 : R.keep.toFrames.all 0 = R.seq 0 := R.keep.toFrames.seq0.symm
  have hix : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  refine PoleStrict.invJ_onFrames R.keep.toFrames hk hc0.start hw0 Nm.ctrl hq Ar.eq he hs hsc Nm.idle (by rw [e0]; exact h0) (by rw [e0]; exact PoleLag.jy_of_jv hJ)
    (fun n hn k => cleanPI_of_E (R.keep.cleanE n (by omega) k)) (fun n hn => Ar.all n (by omega))
    (fun n hn n₀ a1 a2 _ k hk hpc j hj hf => cut_of_posW Nm.ctrl Ar R.frames hst hn a1 a2 hk hpc hj hf)
    (fun n hn n₀ a1 a2 k hpu hf => Or.inl (R.ctl6 hk hcC hc0.start hw0 hmK hcN hcB hIB n (by omega) k hpu hf))
    (fun n hn n₀ a1 a2 k hk0 hkp hf => amount_run R hN hfr st hfq hk hc0 hF hg htop n hn n₀ a1 a2 k hk0 hkp hf)
    (fun n hn => by rw [← edge_eq]; exact hE n hn)

/-- **The parser's invariant and its column below 16 at every frame's start up to the touch's frame** (`invJ_run`) -/
theorem inv_run (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0))
    (hfq : PoleJoin.fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hF : ∀ n, n < R.keep.toFrames.ix R.g → SideAcross.FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n)) (hg : R.g ≤ SurfaceFrames.farN sy B.m)
    (hb : posP sy B.m + 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy B.m : Int) < 64896 * 256) {v : UInt8} (hv : peek B.m sy.AreaType = v)
    (hq : qCheckP sy m0 v = true) (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true) (htop : TopSpeed.top sy ≤ 48)
    (h0 : Inv (places sy m0) 384 (R.seq 0) ∧ ColOK sy m0 (R.seq 0)) (hJ : PoleWrap.JV (valsOf (places sy m0) (R.seq 0)))
    (hcC : PoleCoin.coinCheck sy m0 = true) (hmK : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))
    (hcN : PoleNear.nCheck sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) :
    ∀ n, n < R.keep.toFrames.ix R.g → Inv (places sy m0) 384 (R.keep.toFrames.all n) ∧ ColOK sy m0 (R.keep.toFrames.all n) :=
  fun n hn => (invJ_run R hN hfr st hfq hk hc0 hF hg hb hv hq he hs hsc htop h0 hJ hcC hmK hcN hcB hIB n hn).1

/-- **The parser's column does not go back** from a frame's start to the next one up to the touch's frame (round 33): the weak rule of each frame
(`PoleStrict.ruleW_onFrames`, under the conditions of `invJ_run`) keeps the column or adds one (`PoleStrict.col_of_ruleW`) -/
theorem colMono_run (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0))
    (hfq : PoleJoin.fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hF : ∀ n, n < R.keep.toFrames.ix R.g → SideAcross.FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n)) (hg : R.g ≤ SurfaceFrames.farN sy B.m)
    (hb : posP sy B.m + 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy B.m : Int) < 64896 * 256) {v : UInt8} (hv : peek B.m sy.AreaType = v)
    (hq : qCheckP sy m0 v = true) (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true) (htop : TopSpeed.top sy ≤ 48)
    (h0 : Inv (places sy m0) 384 (R.seq 0) ∧ ColOK sy m0 (R.seq 0)) (hJ : PoleWrap.JV (valsOf (places sy m0) (R.seq 0)))
    (hcC : PoleCoin.coinCheck sy m0 = true) (hmK : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))
    (hcN : PoleNear.nCheck sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) :
    ∀ n, n + 1 < R.keep.toFrames.ix R.g →
      PoleJoin.parColOf sy m0 (R.keep.toFrames.all n) ≤ PoleJoin.parColOf sy m0 (R.keep.toFrames.all (n + 1)) := by
  subst hv
  have hE := edgeLow_run R hN hfr st hfq hk hc0 hF hg hb
  have Nm := SurfaceFrames.numbers_of_check hN
  have hw0 := R.watched₀ st hfq hc0.castle
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start hw0 n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst hF
  have e0 : R.keep.toFrames.all 0 = R.seq 0 := R.keep.toFrames.seq0.symm
  have hix : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  intro n hn
  exact PoleStrict.col_of_ruleW (PoleStrict.ruleW_onFrames R.keep.toFrames hk hc0.start hw0 Nm.ctrl hq Ar.eq he hs hsc Nm.idle (by rw [e0]; exact h0)
    (by rw [e0]; exact PoleLag.jy_of_jv hJ)
    (fun n hn k => cleanPI_of_E (R.keep.cleanE n (by omega) k)) (fun n hn => Ar.all n (by omega))
    (fun n hn n₀ a1 a2 _ k hk hpc j hj hf => cut_of_posW Nm.ctrl Ar R.frames hst hn a1 a2 hk hpc hj hf)
    (fun n hn n₀ a1 a2 k hpu hf => Or.inl (R.ctl6 hk hcC hc0.start hw0 hmK hcN hcB hIB n (by omega) k hpu hf))
    (fun n hn n₀ a1 a2 k hk0 hkp hf => amount_run R hN hfr st hfq hk hc0 hF hg htop n hn n₀ a1 a2 k hk0 hkp hf)
    (fun n hn => by rw [← edge_eq]; exact hE n hn) n hn)

/-- **What the touch's frame needs of the parser** (`PoleJoin.Run.TileColAll`, round 33; up to round 32 it was `TileCol` on the touch's frame, from the field
`tilesCol` and the parser's invariant there): the column does not go back from frame to frame (`colMono_run`); and at control no byte of the block buffers holds
a pole's tile (`hNT`, from the rows of the change: `PoleParser.inv₀`), so the slot's map holds there (`PoleSlot.slotMap_of_none`). Round 34: the parser's column
at control less than 32 columns before the pole's (`hL`, from the rows: `low₀`), and the ring's facts of the pole's column (`hRg`, a check on the places) -/
theorem tilesCol_run (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0))
    (hfq : PoleJoin.fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hF : ∀ n, n < R.keep.toFrames.ix R.g → SideAcross.FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n)) (hg : R.g ≤ SurfaceFrames.farN sy B.m)
    (hb : posP sy B.m + 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy B.m : Int) < 64896 * 256) {v : UInt8} (hv : peek B.m sy.AreaType = v)
    (hq : qCheckP sy m0 v = true) (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true) (htop : TopSpeed.top sy ≤ 48)
    (h0 : Inv (places sy m0) 384 (R.seq 0) ∧ ColOK sy m0 (R.seq 0)) (hJ : PoleWrap.JV (valsOf (places sy m0) (R.seq 0)))
    (hcC : PoleCoin.coinCheck sy m0 = true) (hmK : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0)) (hcN : PoleNear.nCheck sy m0 = true)
    (hNT : NoTiles (PoleFrame.spotsF sy m0) (R.seq 0))
    (hL : PoleSlot.colP (PoleFrame.spotsF sy m0) < PoleJoin.parColOf sy m0 (R.seq 0) + 32) (hRg : PoleRing.RingOK (PoleFrame.spotsF sy m0))
    (hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) : R.TileColAll := by
  have e0 : R.keep.toFrames.all 0 = R.seq 0 := R.keep.toFrames.seq0.symm
  refine ⟨colMono_run R hN hfr st hfq hk hc0 hF hg hb hv hq he hs hsc htop h0 hJ hcC hmK hcN hcB hIB, ?_, ?_, hRg, ?_⟩
  · rw [e0]
    exact PoleSlot.slotMap_of_none hNT
  · rw [e0]
    exact hL
  · intro n hn k hpc
    have hw0 := R.watched₀ st hfq hc0.castle
    obtain ⟨hI, hS⟩ := PoleBcol.frames_bcol hk hcB R.keep.toFrames hc0.start hw0 hIB (R.bNoW hk hcN hc0.start hw0) n hn
    have e : ((R.keep.toFrames.all n).ram.get! (PoleBcol.bcOf sy m0).bI).toNat = PoleJoin.parColOf sy m0 (R.keep.toFrames.all n) % 32 := hI.1
    exact PoleBcol.noTileM_of_ring (e ▸ (hS k hpc).1)

/-- **The parser's column at the start of the touch's frame is at most 384 px past the edge there** (`inv_run`, `PoleParser.col_le`): with it the round 30 parts
(`near`) and (`read`) of the far reads give the field `tilesCol` of round 33 (`PoleSlot.tileSlotC_of_N`) -/
theorem colEdge_run (R : PoleJoin.Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0))
    (hfq : PoleJoin.fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hF : ∀ n, n < R.keep.toFrames.ix R.g → SideAcross.FactsAt sy (R.keep.toFrames.all n) (R.keep.toFrames.inp n)) (hg : R.g ≤ SurfaceFrames.farN sy B.m)
    (hb : posP sy B.m + 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy B.m : Int) < 64896 * 256) {v : UInt8} (hv : peek B.m sy.AreaType = v)
    (hq : qCheckP sy m0 v = true) (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true) (htop : TopSpeed.top sy ≤ 48)
    (h0 : Inv (places sy m0) 384 (R.seq 0) ∧ ColOK sy m0 (R.seq 0)) (hJ : PoleWrap.JV (valsOf (places sy m0) (R.seq 0)))
    (hcC : PoleCoin.coinCheck sy m0 = true) (hmK : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))
    (hcN : PoleNear.nCheck sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0)) :
    16 * PoleJoin.parColOf sy m0 (R.keep.fm R.g) ≤ ScrollRule.left16 (ScrollRule.places sy m0) (R.keep.fm R.g) + 384 := by
  have h1 := R.keep.toFrames.one_le_ix R.one_le (Nat.le_refl _)
  have hI := inv_run R hN hfr st hfq hk hc0 hF hg hb hv hq he hs hsc htop h0 hJ hcC hmK hcN hcB hIB (R.keep.toFrames.ix R.g - 1) (by omega)
  rw [parCol_eq, edge_eq]
  exact col_le hI.1

end Run

/-! ## Round 34: the parser's column at control is less than 32 columns before the pole's

At control above ground the parser's column `c(0)` has `colP < c(0) + 32`: a check on the rows of the change out of the side pipe, as `PoleParser.col₀`. With the
column not going back (`colMono_run`) it holds at every frame's start up to the touch's frame (`PoleJoin.Run.low`), which is what `PoleRing.noTileC_of_M` needs. -/

/-- a state of a row: it knows the bytes of control, and if it has control, it knows the parser's column and its page, and the column is less than 32 columns before
the pole's -/
def rowLow (sy : Syms) (m0 : Machine) (S : TaintRun.AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (SideChangeEnd.knowsAd S) &&
    (!controllable sy (SideChangeEnd.mOf S) || (SideChangeEnd.knowsAd S (places sy m0).page && SideChangeEnd.knowsAd S (places sy m0).col &&
      decide (PoleSlot.colP (PoleFrame.spotsF sy m0) < colOf (places sy m0) (SideChangeEnd.mOf S) + 32)))

/-- **The check on the ROM** (round 34): the ring's facts of the pole's column (`PoleRing.ringCheck`), and in every state with control of the rows of the change
out of the side pipe the parser's column is less than 32 columns before the pole's -/
def lowCheckK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  PoleRing.ringCheck (PoleFrame.spotsF sy m0) && ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row)).all fun r => r.R.all (rowLow sy m0)

theorem low_of_state {E : TaintRun.Env} {Fr : Nat × UInt8} {S : TaintRun.AS} {m : Machine} (hs : TaintRun.Sim E Fr S m) (hr : rowLow sy m0 S = true)
    (h : controllable sy m = true) : PoleSlot.colP (PoleFrame.spotsF sy m0) < PoleJoin.parColOf sy m0 m + 32 := by
  simp only [rowLow, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨⟨h1, h2⟩, h3⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · have e1 := peek_of_known hs h1
    have e2 := peek_of_known hs h2
    rw [parCol_eq]
    unfold colOf at h3 ⊢
    rw [e1, e2]
    exact h3

theorem low_of_invL {C : SideChangeEnd.Ctx} :
    ∀ {l : List SideChangeEnd.Row}, (l.all fun r => r.R.all (rowLow sy m0)) = true → ∀ {m : Machine}, SideChangeEnd.InvL C l m → controllable sy m = true →
      PoleSlot.colP (PoleFrame.spotsF sy m0) < PoleJoin.parColOf sy m0 m + 32
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact low_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact low_of_invL hl.2 h hc

/-- **The parser's column at control is less than 32 columns before the pole's**, on a real run of the change (as `PoleParser.EndRunQ.col`) -/
theorem EndRunQ.low {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine}
    (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : lowCheckK sy m0 nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    PoleSlot.colP (PoleFrame.spotsF sy m0) < PoleJoin.parColOf sy m0 (R'.seq R'.b) + 32 := by
  simp only [lowCheckK, Bool.and_eq_true] at hk
  exact low_of_invL hk.2 (SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)) R'.atCtl

/-- the ring's facts from the check -/
theorem ring_of_low {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} (hk : lowCheckK sy m0 nm nx e A B R = true) :
    PoleRing.RingOK (PoleFrame.spotsF sy m0) := by
  simp only [lowCheckK, Bool.and_eq_true] at hk
  exact PoleRing.ringOK_of_check hk.1

/-! ## Round 35: no coin's tile in the block buffers at control

`PoleJoin.Run.ctl6` needs the coin's map at control: no byte of the block buffers holds a coin's tile. In every state with control of the rows of the change out of
the side pipe every byte of the block buffers is known (as for `PoleTileCtl.mapCheckK`), and none is a coin's tile: the check `coinMapK`, with the coin's places of
`PoleCoin` in place of the pole's (they have no column, so `PoleTileCtl.rowsMap` asks that no byte is a coin's tile). -/

/-- **The check on the ROM** (round 35): no coin's tile in the block buffers in every state with control of the rows of the change out of the side pipe -/
def coinMapK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  decide ((PoleCoin.coinOf sy m0).Q.bufLo + (PoleCoin.coinOf sy m0).Q.bufBytes ≤ 2048) &&
    PoleTileCtl.rowsMap sy (PoleCoin.coinOf sy m0).Q ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row))

/-- **No coin's tile in the block buffers at control**, on a real run of the change (as `PoleTileCtl.EndRunQ.colMap`) -/
theorem EndRunQ.coinMap {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine}
    (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : coinMapK sy m0 nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R'.seq R'.b) := by
  simp only [coinMapK, Bool.and_eq_true, decide_eq_true_eq] at hk
  exact PoleTileCtl.map_of_invL hk.1 hk.2 (SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)) R'.atCtl

/-! ## Round 35: the block buffer's column at control

`PoleBcol.frames_bcol` needs `PoleBcol.BInv` at control: the block buffer's column `B` is the parser's column mod 32, with the column in its page below 16. In
every state with control of the rows of the change out of the side pipe the three bytes are known and meet it (`bInvK`). -/

/-- a state of a row: it knows the bytes of control, and if it has control, it knows `B`, the parser's column and its page, with `BInv` -/
def rowB (sy : Syms) (m0 : Machine) (S : TaintRun.AS) : Bool :=
  let rt := FrameKeep.parRt sy m0
  let bA := FrameKeep.romWE m0 (rt + 0x11)
  let cA := FrameKeep.romWE m0 (rt + 1)
  let pA := FrameKeep.romWE m0 (rt + 0x0E)
  (SurfaceFrames.ctlBytes sy).all (SideChangeEnd.knowsAd S) &&
    (!controllable sy (SideChangeEnd.mOf S) || (SideChangeEnd.knowsAd S bA && SideChangeEnd.knowsAd S cA && SideChangeEnd.knowsAd S pA &&
      (peek (SideChangeEnd.mOf S) bA).toNat == ((peek (SideChangeEnd.mOf S) pA).toNat * 16 + (peek (SideChangeEnd.mOf S) cA).toNat) % 32 &&
      decide ((peek (SideChangeEnd.mOf S) cA).toNat < 16)))

/-- **The check on the ROM** (round 35): `BInv` in every state with control of the rows of the change out of the side pipe -/
def bInvK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row)).all fun r => r.R.all (rowB sy m0)

theorem bInv_of_state {E : TaintRun.Env} {Fr : Nat × UInt8} {S : TaintRun.AS} {m : Machine} (hs : TaintRun.Sim E Fr S m) (hr : rowB sy m0 S = true)
    (h : controllable sy m = true) : PoleBcol.BInv (PoleBcol.bcOf sy m0) m := by
  simp only [rowB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, beq_iff_eq] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · have e1 := peek_of_known hs h1
    have e2 := peek_of_known hs h2
    have e3 := peek_of_known hs h3
    refine ⟨?_, ?_⟩
    · show (peek m _).toNat = ((peek m _).toNat * 16 + (peek m _).toNat) % 32
      rw [e1, e2, e3]
      exact h4
    · show (peek m _).toNat < 16
      rw [e2]
      exact h5

theorem bInv_of_invL {C : SideChangeEnd.Ctx} :
    ∀ {l : List SideChangeEnd.Row}, (l.all fun r => r.R.all (rowB sy m0)) = true → ∀ {m : Machine}, SideChangeEnd.InvL C l m → controllable sy m = true →
      PoleBcol.BInv (PoleBcol.bcOf sy m0) m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact bInv_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact bInv_of_invL hl.2 h hc

/-- **`BInv` at control**, on a real run of the change -/
theorem EndRunQ.bInv {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine}
    (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : bInvK sy m0 nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    PoleBcol.BInv (PoleBcol.bcOf sy m0) (R'.seq R'.b) :=
  bInv_of_invL hk (SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)) R'.atCtl

section Route
open Route

variable {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : PipeTransitionAll.Names} {d₁ : PipeChangeEnd.Data}
  {nm₂ nx₂ nmS : PipeTransitionAll.Names} {fc : FlagRule.Ctx} {tc : TitleStart.Ctx}

/-- **The parser's column at control above ground is less than 32 columns before the pole's** (round 34), on the real machines (as `PoleParser.col₀`). `hm` is the
check on the ROM. -/
theorem low₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : lowCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) {PA : PoleJoin.Box}
    (R : Route.Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    PoleSlot.colP (PoleFrame.spotsF sy m0) < PoleJoin.parColOf sy m0 (R.pole.seq 0) + 32 := by
  rw [R.atCtl]
  exact EndRunQ.low hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

/-- **`BInv` at control above ground** (round 35), on the real machines (as `low₀`). `hm` is the check on the ROM. -/
theorem bInv₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : bInvK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) {PA : PoleJoin.Box}
    (R : Route.Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.pole.seq 0) := by
  rw [R.atCtl]
  exact EndRunQ.bInv hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

/-- **No coin's tile in the block buffers at control above ground** (round 35), on the real machines (as `PoleTileCtl.colMap₀`). `hm` is the check on the ROM. -/
theorem coinMap₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : coinMapK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) {PA : PoleJoin.Box}
    (R : Route.Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.pole.seq 0) := by
  rw [R.atCtl]
  exact EndRunQ.coinMap hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

/-- **What the touch's frame of the route needs of the parser** (`PoleJoin.Run.TileColAll`): `tilesCol_run` on `R.pole`, with the invariant, no pole's tile in
the block buffers and the column at control from the rows of the change out of the side pipe (`PoleParser.inv₀`, `PoleParser.col₀`; the checks `hmI`, `hmC` on the ROM). The box is written `⟨M, dx, dy, rows⟩`, as in `PoleJoin.touch_castle`, so that
the private proof's facts on its machine `M` match without unfolding it -/
theorem tilesCol_route {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hmI : invCheckK sy m0 384 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true) (hmC : colCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hmJ : PoleStrict.jvCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hmL : lowCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hmK : coinMapK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true) (hcC : PoleCoin.coinCheck sy m0 = true)
    (hmB : bInvK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hcN : PoleNear.nCheck sy m0 = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) {M : Machine} {dx dy rows : Nat}
    (R : Route.Run sy m0 N D rN b vs ⟨M, dx, dy, rows⟩ Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    (st : SurfaceFrames.Start sy ⟨M, dx, dy, rows⟩ (R.pole.seq 0)) (hN : SurfaceFrames.numbersCheck sy m0 ⟨M, dx, dy, rows⟩ J = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hfq : PoleJoin.fracCheck sy M = true)
    (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.pole.seq 0)) (hF : ∀ n, n < R.pole.keep.toFrames.ix R.pole.g → SideAcross.FactsAt sy (R.pole.keep.toFrames.all n) (R.pole.keep.toFrames.inp n)) (hg : R.pole.g ≤ SurfaceFrames.farN sy M)
    (hb : posP sy M + 16 * (TopSpeed.top sy : Int) * (SurfaceFrames.farN sy M : Int) < 64896 * 256) {v : UInt8} (hv : peek M sy.AreaType = v)
    (hq : qCheckP sy m0 v = true) (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true)
    (htop : TopSpeed.top sy ≤ 48) : R.pole.TileColAll :=
  tilesCol_run R.pole hN hfr st hfq hk hc0 hF hg hb hv hq he hs hsc htop ⟨(inv₀ hS hT hQ hR hmI hB hK R).1, col₀ hS hT hQ hR hmC hB hK R⟩ (PoleStrict.jv₀ hS hT hQ hR hmJ hB hK R)
    hcC (coinMap₀ hS hT hQ hR hmK hB hK R) hcN (inv₀ hS hT hQ hR hmI hB hK R).2 (low₀ hS hT hQ hR hmL hB hK R) (ring_of_low hmL) hcB
    (bInv₀ hS hT hQ hR hmB hB hK R)

end Route

end Smbrta.PoleParserRun
