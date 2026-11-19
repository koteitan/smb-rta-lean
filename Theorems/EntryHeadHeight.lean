import Theorems.EntryCollisionNear

/-! A small head/side address incompatibility table. It does not add a Run field
or enlarge EntryHeight's frame walk. -/
namespace Smbrta.EntryHeadHeight
open FrameModel

def cell (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places)
    (pg x y index : UInt8) : Nat :=
  I (RoomAddress.target B (RoomAddress.selector pg x (RoomCollision.xadd E P index)) +
    (RoomCollision.rowOf P y (RoomCollision.yadd E P index)).toUInt16)

theorem cell_eq {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places} (R : Machine) :
    cell E B P (R.ram.get! P.pg) (R.ram.get! P.x) (R.ram.get! P.y) R.y =
      I (RoomCollision.readAddress E B P R) := rfl

/-- If a side cell at the candidate landed height contains the pipe, every
head cell in the preceding landing-depth band is a noncoin outside the allowed
head class. No path search is used. -/
def core (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places)
    (M : Machine) (cs : List UInt8) (head side height tile : UInt8) (depth : Nat) : Bool :=
  (List.range 256).all fun pg => (List.range 256).all fun x =>
    if M.ram.get! (cell E B P pg.toUInt8 x.toUInt8 height side) == tile then
      (List.range depth).all fun dy =>
        let j := cell E B P pg.toUInt8 x.toUInt8 (height+dy.toUInt8) head
        decide (B.bufLo ≤ j) && decide (j < B.bufLo+B.bufN) &&
          !cs.contains (M.ram.get! j) && !B.headTiles.contains (M.ram.get! j)
    else true

def check (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) : Bool :=
  let E := Rom.of m0
  let B := ScreenPage.placesR sy nm m0
  let P := RoomCollision.places sy m0
  let M := RoomMap.mapRef m0
  let head := E.b sy.BlockBufferAdderData
  let height := (EntryHeight.hpOf sy nm m0).yv+16
  B.heads.contains head &&
    core E B P M (RoomBlocks.coinsOf B) head (head+3) height sy.SidePipeTile.toUInt8 sy.LandDepth.toNat

/-- The checked instance is the big, non-swimming head and its first upper
side offset; its candidate landed height is one metatile below the reference. -/
theorem core_of_check {sy : Syms} {nm : PipeTransitionAll.Names} {m0 : Machine}
    (h : check sy nm m0 = true) :
    (Rom.of m0).b sy.BlockBufferAdderData ∈ (ScreenPage.placesR sy nm m0).heads ∧
      core (Rom.of m0) (ScreenPage.placesR sy nm m0) (RoomCollision.places sy m0)
        (RoomMap.mapRef m0) (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0))
        ((Rom.of m0).b sy.BlockBufferAdderData) ((Rom.of m0).b sy.BlockBufferAdderData+3)
        ((EntryHeight.hpOf sy nm m0).yv+16) sy.SidePipeTile.toUInt8 sy.LandDepth.toNat = true := by
  change (_ && _) = true at h
  simp only [Bool.and_eq_true] at h
  exact ⟨List.contains_iff_mem.1 h.1,h.2⟩

theorem core_at {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places}
    {M : Machine} {cs : List UInt8} {head side height tile pg x : UInt8} {depth dy : Nat}
    (hc : core E B P M cs head side height tile depth = true)
    (hd : dy < depth) (ht : M.ram.get! (cell E B P pg x height side) = tile) :
    let j := cell E B P pg x (height+dy.toUInt8) head
    B.bufLo ≤ j ∧ j < B.bufLo+B.bufN ∧
      M.ram.get! j ∉ cs ∧ M.ram.get! j ∉ B.headTiles := by
  unfold core at hc
  have hp := List.all_eq_true.1 hc pg.toNat (List.mem_range.2 pg.toNat_lt)
  have hx := List.all_eq_true.1 hp x.toNat (List.mem_range.2 x.toNat_lt)
  simp only [UInt8.ofNat_toNat] at hx
  simp only [ht,beq_self_eq_true,if_true] at hx
  have hy := List.all_eq_true.1 hx dy (List.mem_range.2 hd)
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hy
  refine ⟨hy.1.1.1,hy.1.1.2,?_,?_⟩
  · intro h
    have e := List.contains_iff_mem.2 h
    rw [hy.1.2] at e
    cases e
  · intro h
    have e := List.contains_iff_mem.2 h
    rw [hy.2] at e
    cases e

/-- A real head read with SiteOK and Solid is incompatible with a side-pipe
reference cell at the same horizontal coordinates in this landing band.
Reaching both calls and their coordinate relation are still explicit. -/
theorem excludes_head {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places}
    {R T W M : Machine} {cs : List UInt8} {head side height tile : UInt8} {depth dy : Nat}
    (hc : core E B P M cs head side height tile depth = true)
    (F : RoomCollision.Facts E B P) (H : RoomCollision.ReadAt E B P R T)
    (site : ScreenPage.SiteOK B T) (hmeta : P.read = B.read ∧ P.saved = B.saveI)
    (headMem : head ∈ B.heads) (hi : R.y = head) (si : W.y = side)
    (hx : R.ram.get! P.x = W.ram.get! P.x)
    (hp : R.ram.get! P.pg = W.ram.get! P.pg)
    (hy : R.ram.get! P.y = height+dy.toUInt8)
    (wy : W.ram.get! P.y = height) (hd : dy < depth)
    (pipe : M.ram.get! (I (RoomCollision.readAddress E B P W)) = tile)
    (solid : RoomBlocks.Solid B cs M T) : False := by
  have pipe' : M.ram.get! (cell E B P (W.ram.get! P.pg) (W.ram.get! P.x) height side) = tile := by
    rw [← wy,← si,cell_eq]; exact pipe
  obtain ⟨hl,hr,nc,nh⟩ := core_at hc hd pipe'
  have addr : cell E B P (W.ram.get! P.pg) (W.ram.get! P.x) (height+dy.toUInt8) head =
      I (RoomCollision.readAddress E B P R) := by
    rw [← hp,← hx,← hy,← hi,cell_eq]
  rw [addr] at hl hr nc nh
  exact nh (RoomCollision.head_reference_allowed F H site hmeta.1 hmeta.2
    (by rw [hi]; exact headMem) solid hl hr nc)

end Smbrta.EntryHeadHeight
