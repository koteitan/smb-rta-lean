import Theorems.RoomStand
import Theorems.RoomJump

/-!
# The vertical bytes of the frame that enters the side pipe

The walks of the room's frames (`RoomVert`'s walk from the scroll handler `Q` rising, `RoomFall`'s from `Q` falling, `RoomStand`'s from the player's routine `R` standing)
follow a frame to its end. A state on which a step may write a vertical byte where the walk's list does not allow it must end the frame out of the player's routine (the
frame's end condition). Up to round 35 that was all: so they said nothing of the frame that enters the side pipe, which ends in the side pipe's routine. Since round 36 the
frame's end condition asks that such a state ends neither in the player's routine nor in the side pipe's (`RoomVert.outE`), and in walk B that a state that came to `Q`
rising with no such write since knows the routine byte not to be the side pipe's (`RoomVert.notEng`). The three walks pass with these conditions, with no other change.

So on a frame of the room that ends in the side pipe's routine:
* if it starts in the air, he falls at `Q`, and the vertical bytes at the frame's end are those of `vstep` or its landing (`air_frame`, `air_room`);
* if it starts standing with no new press of A, the vertical bytes at its end are as `RoomJoin.StandNext` allows (`stand_frame`, `stand_room`);
* it does not start standing with a new press of A (`jump_frame`, `jump_room`): the takeoff rises at `Q`, and a frame that comes to `Q` rising does not end in the side
  pipe's routine (`RoomVert.after_QE`).

There is no game data in this file. Page: `1-1/c-7-8-5-EntryVert.md`.
-/

namespace Smbrta.EntryVert

open PipeTransition (frame)
open PipeTransitionAll (Names)
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK CfgS RoomCond)
open RoomVert (OKV phA phB finB apartB I vKeep vKeepA before_R Rising vsOf_eq_of)
open VertAir (AtV)
open FrameModel (Rom)

/-- **A frame of the room in the air that ends in the side pipe's routine.** As `RoomFall.jump_frame`, with the frame's end in the side pipe's routine `P.eng` in place of
the player's routine: `vstep` on the machine of the player's routine falls (a frame that comes to `Q` rising does not end so, `RoomVert.after_QE`), and the vertical bytes
at the frame's end are those of `vstep` or its landing (`RoomFall.after_QHE`) -/
theorem air_frame {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CB CC : CfgS}
    {Fa Fb Fc : Nat} (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hB : OKV (phB sy E P) E P r K CB Fb) (hfB : CB.fin = finB P r) (hC : OKV (RoomFall.phC sy E P) E P r K CC Fc) (hfC : CC.fin = RoomFall.finC P r)
    (hap : RoomFall.apartC sy P = true) (hV : VertAir.vertAirOK sy m0 S = true) {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true)
    {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (heng : (frame M i).ram.get! P.rtI = P.eng) :
    Jump.falling (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0) = true ∧
    (VertModel.vsOf sy (frame M i) = VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∨
     VertModel.vsOf sy (frame M i) = VertAir.land (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0)) := by
  obtain ⟨j, hq, hf, hv, hst2⟩ := RoomFall.at_Q hpz hA hfA hV hidle hm hk hR ht hst hd hp
  generalize VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 = t at hv hst2 ⊢
  have hapB : RoomVert.apartB sy P = true := by
    simp only [RoomFall.apartC, Bool.and_eq_true] at hap
    exact hap.1.1.1
  have e1 : (VertModel.vsOf sy (trace M i j)).st = (trace M i j).ram.get! (I sy.Player_State) := rfl
  have e2 : (VertModel.vsOf sy (trace M i j)).vy = (trace M i j).ram.get! (I sy.Player_Y_Speed) := rfl
  rcases RoomFall.vy_cases t.vy with h0 | h80
  · -- falling at the scroll handler: kept, or the landing
    have hF : RoomFall.Falling sy (trace M i j) := by
      unfold RoomFall.Falling
      rw [← e1, ← e2, hv]
      exact ⟨hst2, h0⟩
    refine ⟨RoomFall.falling_of h0, ?_⟩
    rcases ((RoomFall.after_QHE hC hfC hap hm hk).2 j hq hf hF (Or.inr heng)).2 with ⟨e, _⟩ | ⟨f1, f2, f3, f4, f5⟩
    · exact Or.inl (by rw [vsOf_eq_of e, hv])
    · exact Or.inr (by rw [RoomFall.vsOf_land f1 f2 f3 f4 f5, hv])
  · -- rising at the scroll handler: the frame does not end in the side pipe's routine
    exfalso
    have hRi : Rising sy (trace M i j) := by
      unfold Rising
      rw [← e1, ← e2, hv]
      exact ⟨hst2, h80⟩
    exact ((RoomVert.after_QE hB hfB hapB hm hk).2 j hq hf hRi).1 heng

/-- **A frame of the room that starts standing with no new press of A and ends in the side pipe's routine.** As `RoomStand.stand_frame`, with the frame's end in the side
pipe's routine `P.eng` (`RoomStand.after_RSE`): the vertical state at the frame's end is one that `RoomJoin.StandNext` allows -/
theorem stand_frame {sy : Syms} {S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CS : CfgS} {Fa Fs : Nat}
    (hpz : pz < 2048) (hA : OKV (RoomVert.phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hS : OKV (RoomStand.phS sy E P) E P r K CS Fs) (hfS : CS.fin = RoomStand.finS sy P r) (hap : RoomStand.apartS sy P = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : (trace M i k).pc = sy.PlayerCtrlRoutine) (hst : peek M sy.Player_State = 0)
    (hn : (FrameModel.readIn sy (trace M i k)).jump = false)
    (heng : (frame M i).ram.get! P.rtI = P.eng) :
    RoomJoin.StandNext (VertModel.vsOf sy M) (VertModel.vsOf sy (frame M i)) := by
  obtain ⟨a1, a2, _, a4⟩ := RoomVert.before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, I a ∈ vKeep sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ (List.mem_append_left _ ha)
  have hs0 : peek (trace M i k) sy.Player_State = 0 := by rw [eq sy.Player_State (by simp [vKeep])]; exact hst
  have hstd : RoomStand.StandAt sy (trace M i k) := ⟨hs0, RoomStand.nopress_of hs0 hn⟩
  obtain ⟨e1, e2⟩ := (RoomStand.after_RSE hS hfS hap hm hk).2 k hR hfk hstd (Or.inr heng)
  have f : ∀ a : UInt16, I a ∈ RoomStand.vRestS sy → peek (frame M i) a = peek M a := fun a ha => by
    show (frame M i).ram.get! (I a) = M.ram.get! (I a)
    rw [← hkeep _ (RoomStand.vRestS_sub sy _ ha)]
    exact e1 _ ha
  refine ⟨f sy.Player_YMF_Dummy (by simp [RoomStand.vRestS]), f sy.VerticalForce (by simp [RoomStand.vRestS]), f sy.VerticalForceDown (by simp [RoomStand.vRestS]),
    f sy.JumpOrigin_Y_Position (by simp [RoomStand.vRestS]), ?_⟩
  rcases e2 with ⟨g1, g2, _⟩ | ⟨g1, g2, g3, g4⟩
  · have g : ∀ a : UInt16, I a ∈ RoomStand.vLand3 sy → peek (frame M i) a = peek M a := fun a ha => by
      rw [← eq a (RoomStand.vLand3_sub sy _ ha)]
      exact g1 _ ha
    exact Or.inl ⟨g sy.Player_Y_Position (by simp [RoomStand.vLand3]), g sy.Player_Y_Speed (by simp [RoomStand.vLand3]),
      g sy.Player_Y_MoveForce (by simp [RoomStand.vLand3]), g2⟩
  · refine Or.inr ⟨g1, g2, g3, ?_⟩
    show peek (frame M i) sy.Player_Y_Position = peek M sy.Player_Y_Position &&& 0xF0
    rw [← eq sy.Player_Y_Position (by simp [vKeep])]
    exact g4

/-- **A frame of the room that starts a jump does not end in the side pipe's routine.** As `RoomJump.jump_frame`: at the scroll handler he is in a jump and rising
(`VertJump.vert_jump`), and a frame that comes there rising does not end in the side pipe's routine (`RoomVert.after_QE`) -/
theorem jump_frame {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CB : CfgS} {Fa Fb : Nat}
    (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine) (hB : OKV (phB sy E P) E P r K CB Fb)
    (hfin : CB.fin = finB P r) (hap : apartB sy P = true) (hV : VertModel.vertOK sy m0 S = true) (hJ : VertJump.jumpOK sy m0 S = true) {idle : UInt16}
    (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hj : (FrameModel.readIn sy (trace M i k)).jump = true)
    (heng : (frame M i).ram.get! P.rtI = P.eng) : False := by
  obtain ⟨_, _, _, a4⟩ := before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR.pc
  obtain ⟨p1, p2, p3⟩ := RoomJump.press_of hj
  obtain ⟨kk, _, _, hpc, _, _, hs1, hvy, hIn⟩ := VertJump.vert_jump hV hJ hR p1 p2 p3
  obtain ⟨htr, hfq⟩ := FrameModel.trace_inFrame hidle hfk hIn ht kk (Nat.le_refl kk)
  rw [← htr] at hpc hs1 hvy
  have hrs : Rising sy (trace M i (k + kk)) := ⟨Or.inl hs1, hvy⟩
  exact ((RoomVert.after_QE hB hfin hap hm hk).2 (k + kk) hpc hfq hrs).1 heng

/-! ## On the room -/

/-- **A frame of the room in the air that ends in the side pipe's routine**, on the room: `air_frame` with the checks of `RoomVert` and `RoomFall` -/
theorem air_room {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk) (hF : RoomFall.FChecks sy nm m0 h) {idle : UInt16}
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i k))
    (htm : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (heng : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.placesR sy nm m0).eng) :
    Jump.falling (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0) = true ∧
    (VertModel.vsOf sy (frame M i) = VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∨
     VertModel.vsOf sy (frame M i) =
       VertAir.land (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0)) :=
  air_frame (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB) (RoomVert.okV_of_check hV.b) rfl
    (RoomVert.okV_of_check hF.c) rfl hF.apart hV.air hidle hm hs hR htm hst hd hp heng

/-- **A frame of the room that starts standing with no new press of A and ends in the side pipe's routine**, on the room: `stand_frame` with the checks of `RoomVert`
and `RoomStand` -/
theorem stand_room {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk) (hS : RoomStand.SChecks sy nm m0) {M : Machine} {i : UInt8}
    {k : Nat} (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : (trace M i k).pc = sy.PlayerCtrlRoutine) (hst : peek M sy.Player_State = 0)
    (hn : (FrameModel.readIn sy (trace M i k)).jump = false)
    (heng : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.placesR sy nm m0).eng) :
    RoomJoin.StandNext (VertModel.vsOf sy M) (VertModel.vsOf sy (frame M i)) :=
  stand_frame (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB) (RoomVert.okV_of_check hS.c) rfl hS.apart hm hs hR hst hn heng

/-- **A frame of the room that starts a jump does not end in the side pipe's routine**, on the room: `jump_frame` with the checks of `RoomVert` and the takeoff's walk -/
theorem jump_room {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk)
    (hJ : VertJump.jumpOK sy m0 (FrameModel.ctrlStack sy m0) = true) {idle : UInt16} (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) idle = true)
    {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i k))
    (htm : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hj : (FrameModel.readIn sy (trace M i k)).jump = true)
    (heng : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.placesR sy nm m0).eng) : False := by
  have hair := hV.air
  simp only [VertAir.vertAirOK, Bool.and_eq_true] at hair
  exact jump_frame (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB) (RoomVert.okV_of_check hV.b) rfl hV.apart hair.1 hJ
    hidle hm hs hR htm hj heng

end Smbrta.EntryVert
