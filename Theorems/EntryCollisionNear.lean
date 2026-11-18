import Theorems.RoomCollisionMap
import Theorems.EntryBufferNear

/-! Actual collision reads and the existing coin gap, without new Run fields. -/
namespace Smbrta.EntryBufferNear
open FrameModel
open ScreenPage
open PipeTransitionAll (Names)
variable {sy : Syms} {nm : Names} {m0 R T U : Machine} {gap : Nat}

def callIndex (sy : Syms) (nm : Names) (m0 R : Machine) : Nat :=
  I (RoomCollision.readAddress (Rom.of m0) (placesR sy nm m0) (RoomCollision.places sy m0) R)

/-- A computed read in a column closer to the mouth than any map coin is not a coin. -/
theorem map_noncoin_near_read (hg : gapCheck sy nm m0 gap = true)
    (hl : (placesR sy nm m0).bufLo ≤ callIndex sy nm m0 R)
    (hr : callIndex sy nm m0 R < (placesR sy nm m0).bufLo+(placesR sy nm m0).bufN)
    (hn : SidePipe.column sy < column (placesR sy nm m0)
      (callIndex sy nm m0 R-(placesR sy nm m0).bufLo)+gap) :
    (RoomMap.mapRef m0).ram.get! (callIndex sy nm m0 R) ∉ RoomBlocks.coinsOf (placesR sy nm m0) := by
  intro hc
  have eq : (placesR sy nm m0).bufLo+
      (callIndex sy nm m0 R-(placesR sy nm m0).bufLo) = callIndex sy nm m0 R := by omega
  have h := gap_of_check hg (j := callIndex sy nm m0 R-(placesR sy nm m0).bufLo)
    (by omega) (by rw [eq]; exact hc)
  omega

/-- The routine returns the map byte and cannot return a coin near the mouth;
the noncoin premise of returned_map is derived from the existing gap. -/
theorem returned_near_read (hg : gapCheck sy nm m0 gap = true)
    (ret : RoomCollision.Returned (Rom.of m0) (placesR sy nm m0) (RoomCollision.places sy m0) R T U)
    (solid : RoomBlocks.SolidR sy nm m0 T)
    (hl : (placesR sy nm m0).bufLo ≤ callIndex sy nm m0 R)
    (hr : callIndex sy nm m0 R < (placesR sy nm m0).bufLo+(placesR sy nm m0).bufN)
    (hn : SidePipe.column sy < column (placesR sy nm m0)
      (callIndex sy nm m0 R-(placesR sy nm m0).bufLo)+gap) :
    U.a = (RoomMap.mapRef m0).ram.get! (callIndex sy nm m0 R) ∧
      U.a ∉ RoomBlocks.coinsOf (placesR sy nm m0) := by
  have nc := map_noncoin_near_read hg hl hr hn
  have val := RoomCollision.returned_map ret solid hl hr nc
  exact ⟨val,by rw [val]; exact nc⟩

/-- A coin returned by an actual call inherits the map's column-gap bound. -/
theorem returned_coin_gap (hg : gapCheck sy nm m0 gap = true)
    (ret : RoomCollision.Returned (Rom.of m0) (placesR sy nm m0) (RoomCollision.places sy m0) R T U)
    (solid : RoomBlocks.SolidR sy nm m0 T)
    (hl : (placesR sy nm m0).bufLo ≤ callIndex sy nm m0 R)
    (hr : callIndex sy nm m0 R < (placesR sy nm m0).bufLo+(placesR sy nm m0).bufN)
    (coin : U.a ∈ RoomBlocks.coinsOf (placesR sy nm m0)) :
    column (placesR sy nm m0) (callIndex sy nm m0 R-(placesR sy nm m0).bufLo)+gap ≤ SidePipe.column sy := by
  have hc : T.ram.get! (callIndex sy nm m0 R) ∈ RoomBlocks.coinsOf (placesR sy nm m0) := by
    unfold callIndex
    rw [← ret.a]; exact coin
  have mc := map_coin solid hl hr hc
  have eq : (placesR sy nm m0).bufLo+
      (callIndex sy nm m0 R-(placesR sy nm m0).bufLo) = callIndex sy nm m0 R := by omega
  exact gap_of_check hg (by omega) (by rw [eq]; exact mc)
end Smbrta.EntryBufferNear

namespace Smbrta.RoomCollision
open FrameModel
/-- At an actual head read, a noncoin reference byte must meet SiteOK's head
classification. In particular, an incompatible floor cell rules out that read. -/
theorem head_reference_allowed {E : Rom} {B : ScreenPage.Places} {P : Places} {R T M : Machine} {cs : List UInt8}
    (F : Facts E B P) (H : ReadAt E B P R T)
    (site : ScreenPage.SiteOK B T) (hpc : P.read = B.read) (hsaved : P.saved = B.saveI)
    (head : R.y ∈ B.heads) (solid : RoomBlocks.Solid B cs M T)
    (hl : B.bufLo ≤ I (readAddress E B P R))
    (hr : I (readAddress E B P R) < B.bufLo+B.bufN)
    (nc : M.ram.get! (I (readAddress E B P R)) ∉ cs) :
    M.ram.get! (I (readAddress E B P R)) ∈ B.headTiles := by
  have pc : T.pc = B.read := H.cut.pc.trans hpc
  have hd : T.ram.get! B.saveI ∈ B.heads := by rw [← hsaved,H.saved]; exact head
  have ok := (site.read pc).2 hd
  have val := (read_value F H).trans (solid _ hl hr nc)
  rw [val] at ok
  exact ok
end Smbrta.RoomCollision
