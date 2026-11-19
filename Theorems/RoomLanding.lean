import Theorems.RoomCollisionMap

/-! Non-circular facts before landing and the exact coordinate link needed at a foot call. -/
namespace Smbrta.RoomJoin
open Jump (VS)
namespace RoomRun
variable {sy : Syms} {m : Machine} {N : Nums} {S : FrameKeep.RealRun} {b lim : Nat}
variable (r : RoomRun sy m N S b lim)

/-- With no wall there is no stand strictly before the landing frame.
Uses stand_wall and fall_first, and never land_at/floor_at_of. -/
theorem no_stand_before_land (H : Checks sy m N) (hr : r.InRoom)
    (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) :
    ∀ j, r.C < j → j < r.C+N.fall → (r.fr.vs j).st ≠ 0 := by
  obtain ⟨_,_,_,_⟩ := fall_ok H.first
  have hhit := H.nums.hit_ge
  intro j h1 h2 h3
  obtain ⟨i, i1, i2, i3, i4⟩ := first_of (P := fun j => (r.fr.vs j).st = 0) (r.C + N.fall) ⟨j, h1, h2, h3⟩
  have h5 := r.fall_first H hr st (n := i) (by omega) i2 (fun k a b => i4 k a b)
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  exact r.stand_wall i' (by omega) (by omega) i3 h5 (hw i' (by omega) (by omega))

/-- The last prelanding vertical state belongs to the existing fall layer,
without using the missing landing-state field. -/
theorem before_land_mem (H : Checks sy m N) (hr : r.InRoom)
    (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) :
    r.fr.vs (r.C+(N.fall-1)) ∈ fallLayer sy m N.vStart (N.fall-1) := by
  obtain ⟨hf,hfs,_,_⟩ := fall_ok H.first
  apply r.fall_mem H hr st (N.fall-1) (by omega)
  intro j hj hk
  exact r.no_stand_before_land H hr st hw j hj (by omega)

/-- The final fall step still has two alternatives; choosing the actual landing
requires the foot call and its caller's branch, not floor_at_of. -/
theorem before_land_step (H : Checks sy m N) (hr : r.InRoom)
    (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) :
    let v := vstepR sy m (r.fr.vs (r.C+(N.fall-1))) (r.fr.a (r.C+N.fall))
    r.fr.vs (r.C+N.fall) = v ∨
      Jump.falling v = true ∧ r.fr.vs (r.C+N.fall) = VertAir.land v := by
  obtain ⟨hf,hfs,_,_⟩ := fall_ok H.first
  obtain ⟨_,h⟩ := r.fall_next H hr st (d := N.fall-1) (by omega)
    (fun j hj hk => r.no_stand_before_land H hr st hw j hj (by omega))
  have eq : r.C+(N.fall-1)+1 = r.C+N.fall := by omega
  simpa only [eq] using h

end RoomRun
end Smbrta.RoomJoin

namespace Smbrta.RoomCollision
open FrameModel
/-- If the movement-end and call-entry coordinate bytes agree, the computed
cell can be read at the movement end with the actual call's offset index.
This is a local transport lemma, not a new Run field or a proof of agreement. -/
theorem readAddress_from_coords {E : Rom} {B : ScreenPage.Places} {P : Places} {R Q : Machine}
    (hc : ∀ j ∈ coords P, R.ram.get! j = Q.ram.get! j) :
    readAddress E B P R = readAddress E B P {Q with y := R.y} := by
  unfold readAddress
  rw [hc P.pg (by simp [coords]),hc P.x (by simp [coords]),hc P.y (by simp [coords])]

/-- The map-return result expressed using movement-end coordinates, provided
the actual instruction prefix preserves them. No call or preservation is assumed globally. -/
theorem returned_map_from_coords {E : Rom} {B : ScreenPage.Places} {P : Places} {R Q T U M : Machine} {cs : List UInt8}
    (ret : Returned E B P R T U) (solid : RoomBlocks.Solid B cs M T)
    (hc : ∀ j ∈ coords P, R.ram.get! j = Q.ram.get! j)
    (hl : B.bufLo ≤ I (readAddress E B P {Q with y := R.y}))
    (hr : I (readAddress E B P {Q with y := R.y}) < B.bufLo+B.bufN)
    (nc : M.ram.get! (I (readAddress E B P {Q with y := R.y})) ∉ cs) :
    U.a = M.ram.get! (I (readAddress E B P {Q with y := R.y})) := by
  have eq := readAddress_from_coords (E := E) (B := B) hc
  rw [← eq] at hl hr nc ⊢
  exact returned_map ret solid hl hr nc
end Smbrta.RoomCollision

namespace Smbrta.RoomCollision
set_option maxRecDepth 100000 in
/-- The BIT used to skip the overlapping side-load in the head/feet wrapper
keeps all RAM. FrameWalk also supports the full BIT transition. -/
theorem bit_abs_ram {R : Machine} (hn : R.nmiPending = false) (hh : R.halted = false)
    (hp : 0x8000 ≤ R.pc) (op : R.prg.get! (R.pc &&& R.prgMask).toNat = 0x2C) :
    (PipeTransitionAll.go step R).2.ram = R.ram := by
  have table : opTable[(0x2C : UInt8).toNat]?.getD opJAM = opBIT mAbs := by
    rw [PipeTransitionAll.opTable_eq]
    rfl
  rw [ScreenPage.step_at hn hh hp op (by decide),table,PipeTransitionAll.go_bind]
  rw [(PipeTransitionAll.leaf_tick _).ram,StepWrites.nw_opBIT StepWrites.nw_mAbs]
end Smbrta.RoomCollision
