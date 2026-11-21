import Theorems.Route
import Theorems.RoomCollision

/-! Room map agreement at instruction cuts, and the tile returned by actual
player collision calls. No new Run field is introduced. -/
namespace Smbrta.Route
open PipeTransitionAll (Names)
open FrameModel (Good Rom idleAt I)

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {fc : FlagRule.Ctx}
  {tc : TitleStart.Ctx}

/- The Run-level companion of Run.roomBlocks, with the same hypotheses. -/
theorem Run.roomBlocksTrace {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hW : RoomBlocks.BChecks sy nmS m0) (hRw : RoomBlocks.rowsCheckR sy nm₁ d₁ nmS m0 rN.vStart = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ∀ n, R.base.b₁ sy ≤ n → n < R.base.a₂ sy nmS m0 → ∀ j, (PipeEntryRule.trace (R.base.seq n) (R.base.inp n) j).frame = (R.base.seq n).frame →
      RoomBlocks.SolidR sy nmS m0 (PipeEntryRule.trace (R.base.seq n) (R.base.inp n) j) :=
  RoomBlocks.blocks_run_trace hW hRw hM hS R.base.next ((R.chg.run₁ (R.entry₁ hB hK)).inRowsT hT₁ R.chg.ctlFirst₁) R.chg.ctl₁ (R.roomSites hR hB hK) R.chg.roomStay


/-- On every actual player call inside a room frame, a non-coin map cell is returned to the original caller. -/
theorem Run.roomCollisionMap {es₁ : List Machine} (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0) (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hW : RoomBlocks.BChecks sy nmS m0) (hRw : RoomBlocks.rowsCheckR sy nm₁ d₁ nmS m0 rN.vStart = true)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) {k n : Nat}
    (hk0 : R.base.b₁ sy ≤ k) (hk1 : k < R.base.a₂ sy nmS m0)
    (hc : RoomCollision.check sy nmS m0 = true)
    (g : Good (Rom.of m0) (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n))
    (pc : (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n).pc = sy.BlockBufferCollision) (x : (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n).x = 0)
    (hf : (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n).frame = (R.base.seq k).frame)
    (loop : idleAt (Rom.of m0) (ScreenPage.placesR sy nmS m0).idle = true)
    (hl : (ScreenPage.placesR sy nmS m0).bufLo ≤ I (RoomCollision.readAddress (Rom.of m0) (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0) (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n)))
    (hr : I (RoomCollision.readAddress (Rom.of m0) (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0) (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n)) < (ScreenPage.placesR sy nmS m0).bufLo+(ScreenPage.placesR sy nmS m0).bufN)
    (nc : (RoomMap.mapRef m0).ram.get! (I (RoomCollision.readAddress (Rom.of m0) (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0) (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n))) ∉ RoomBlocks.coinsOf (ScreenPage.placesR sy nmS m0)) :
    ∃ nr nt, nr ≤ 93 ∧ nt ≤ 25 ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+nr+nt)).pc = RoomCollision.returnPc (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n) ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+nr+nt)).a = (RoomMap.mapRef m0).ram.get! (I (RoomCollision.readAddress (Rom.of m0) (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0) (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n))) ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+nr+nt)).frame = (R.base.seq k).frame := by
  apply RoomCollision.frame_returned_map hc g pc x hf loop ?_ ?_ hl hr nc
  · intro j hj
    apply Nat.le_trans (R.chg.roomLate k hk0 hk1 j hj)
    change dotsPerFrame-6000 ≤ dotsPerFrame-64
    decide
  · exact R.roomBlocksTrace hT₁ hM hS hW hRw hR hB hK k hk0 hk1

end Smbrta.Route
