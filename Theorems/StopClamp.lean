import Theorems.RightEdge

/-!
# Above ground: a frame that the clamp stops ends at the screen's left edge

Round 33. At the scroll handler's call the frame comes, by the scroll's part (`RightEdge.scroll_rel`), to the routine of the offscreen bits (`ChkPOffscr`) at a
machine `C`, where the right edge is the left edge plus 255 px, modulo 2¹⁶ (`RightEdge.Rel`). The routine and the clamp bring it to the scroll handler's return
instruction at `R`; there his pixel is that of the clamp's choice (`ClampSide.pixAfter`), and when nothing is chosen his speed is that of `C`
(`ClampSide.clamp_end`). `stop_clamp`: if at the frame's end `b` his pixel and his speed are those of `R`, his pixel is that of `C`, the left edge is that of `C`,
and his speed is not that of `C`, then he ends at the left edge. With nothing chosen the speed would be kept. The clamp at the right edge leaves him its amount
left of the right edge, and at that place the choice is not the clamp at the right edge (`ClampSide.rightAmt`, a check on the ROM); but his pixel at `C` is the
one at the end, so the choice at `C` would be made at that place. So the clamp at the left edge was chosen, whose amount is 0. No game data. Page:
`1-1/e-2-10-3-23-StopClamp.md`.
-/

namespace Smbrta.StopClamp
open FrameModel

/-- **A frame that the clamp stops ends at the screen's left edge** (round 33; `SurfaceFrames.OnFrames.stopRight`). `C` is the machine at the routine of the
offscreen bits, `R` at the scroll handler's return instruction, `b` at the frame's end. -/
theorem stop_clamp {sy : Syms} {m0 : Machine} (hc : ClampSide.checkAll sy m0 = true) {C R b : Machine}
    (hrel : RightEdge.Rel (ClampSide.places sy m0) C)
    (hp : ClampSide.pix16 (ClampSide.places sy m0) R =
      ClampSide.pixAfter (Rom.of m0) (ClampSide.places sy m0) (ClampSide.selM (Rom.of m0) (ClampSide.places sy m0) C) C)
    (hv : ClampSide.selM (Rom.of m0) (ClampSide.places sy m0) C = none →
      R.ram.get! (ClampSide.places sy m0).speed = C.ram.get! (ClampSide.places sy m0).speed)
    (hpb : ClampSide.pix16 (ClampSide.places sy m0) b = ClampSide.pix16 (ClampSide.places sy m0) R)
    (hvb : b.ram.get! (ClampSide.places sy m0).speed = R.ram.get! (ClampSide.places sy m0).speed)
    (hpc : ClampSide.pix16 (ClampSide.places sy m0) C = ClampSide.pix16 (ClampSide.places sy m0) b)
    (hed : ClampSide.edge16 (ClampSide.places sy m0) 0 b = ClampSide.edge16 (ClampSide.places sy m0) 0 C)
    (hne : b.ram.get! (ClampSide.places sy m0).speed ≠ C.ram.get! (ClampSide.places sy m0).speed) :
    ClampSide.pix16 (ClampSide.places sy m0) b = ClampSide.edge16 (ClampSide.places sy m0) 0 b := by
  have hamt := ClampSide.amt_facts hc
  rw [hed]
  cases hs : ClampSide.selM (Rom.of m0) (ClampSide.places sy m0) C with
  | none => exact absurd (hvb.trans (hv hs)) hne
  | some t =>
    rw [hs, ClampSide.pixAfter_some] at hp
    rcases ClampSide.selM_mem hs with rfl | rfl
    · -- the clamp at the left edge: its amount is 0
      rw [hpb, hp, hamt.1, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (ClampSide.edge16_lt _ 0 C)]
    · -- the clamp at the right edge: the choice at his pixel is not the clamp at the right edge
      exfalso
      rw [ClampSide.selM_rel C hrel] at hs
      have hl1 := ClampSide.edge16_lt (ClampSide.places sy m0) 1 C
      have ha := ((Rom.of m0).b ((ClampSide.places sy m0).table + (1 : UInt8).toUInt16)).toNat_lt
      have ea : ClampSide.amt (Rom.of m0) (ClampSide.places sy m0) 1 =
          ((Rom.of m0).b ((ClampSide.places sy m0).table + (1 : UInt8).toUInt16)).toNat := rfl
      have hd : (ClampSide.edge16 (ClampSide.places sy m0) 1 C + 65536 - ClampSide.pix16 (ClampSide.places sy m0) C) % 65536 =
          ClampSide.amt (Rom.of m0) (ClampSide.places sy m0) 1 := by
        rw [hpc, hpb, hp]
        omega
      rw [hd] at hs
      exact hamt.2 hs

end Smbrta.StopClamp
