import Theorems.RoomVert
import Theorems.VertJump

/-!
# The vertical bytes of a frame in the room that starts a jump

`RoomStand` follows a frame of the room that comes to the player's routine standing with no new press of A. Here the frame comes there standing with a new press: the input
that the model reads has a jump. Then the movement routine starts a jump, and the vertical bytes at the scroll handler are those of `VertJump.jumpOff` of the height and the
stored speed (`VertJump.vert_jump`: the walk of two machines on a takeoff); there he is in a jump and rising, so the walk of `RoomVert` from the scroll handler says that
no step up to the frame's end writes them (`RoomVert.after_Q`). So the vertical state at the frame's end is `jumpOff` of the height at the frame's start and the stored
speed at the player's routine (`jump_frame`, `jump_room`).

No new walk of the room's frames is needed: the walks to the player's routine and from the scroll handler are those of `RoomVert`.

There is no game data in this file. Page: `1-1/c-7-5-6-RoomJump.md`.
-/

namespace Smbrta.RoomJump

open PipeTransition (frame)
open PipeTransitionAll (Names)
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK CfgS RoomCond)
open RoomVert (OKV phA phB finB apartB I vKeep vKeepA before_R after_Q Rising vsOf_eq_of)
open VertAir (AtV)
open FrameModel (Rom stepN)

theorem b80_cases : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 ∨ UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel

/-- **A jump in the input that the model reads** is a new press of A, standing: the state 0, bit 7 of the joypad's bits 1, bit 7 of A of the frame before 0 -/
theorem press_of {sy : Syms} {x : Machine} (hj : (FrameModel.readIn sy x).jump = true) :
    peek x sy.Player_State = 0 ∧ peek x sy.SavedJoypadBits &&& 0x80 = 0x80 ∧ peek x sy.PreviousA_B_Buttons &&& 0x80 = 0 := by
  have e : (FrameModel.readIn sy x).jump = (peek x sy.Player_State == 0 && peek x sy.SavedJoypadBits &&& 0x80 != 0 &&
      peek x sy.PreviousA_B_Buttons &&& 0x80 == 0) := rfl
  rw [e] at hj
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hj
  obtain ⟨⟨h1, h2⟩, h3⟩ := hj
  refine ⟨h1, ?_, h3⟩
  have c := b80_cases ⟨(peek x sy.SavedJoypadBits).toNat, (peek x sy.SavedJoypadBits).toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at c
  rcases c with c | c
  · exact absurd c h2
  · exact c

/-- **One frame of the room that starts a jump.** The frame starts in the room's condition `M`, each instruction meets `SiteOK`, the frame comes to the player's routine at
instruction `k` in the state `AtV` with a jump in the input that the model reads there (standing, a new press of A), and it ends in the player's routine. Then the vertical
bytes at the frame's end are `VertJump.jumpOff` of the height at the frame's start and the stored speed at the player's routine. The checks: the two walks of the room of
`RoomVert`, `apartB`, `vertOK`, and the takeoff's walk of two machines (`VertJump.jumpOK`). Each instruction of the frame that is not at the idle loop `idle` runs at least
64 dots before the frame's end (`ht`): so the frame does not end during the movement. -/
theorem jump_frame {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CB : CfgS} {Fa Fb : Nat}
    (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine) (hB : OKV (phB sy E P) E P r K CB Fb) (hfin : CB.fin = finB P r)
    (hap : apartB sy P = true) (hV : VertModel.vertOK sy m0 S = true) (hJ : VertJump.jumpOK sy m0 S = true) {idle : UInt16}
    (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hj : (FrameModel.readIn sy (trace M i k)).jump = true)
    (hrt : (frame M i).ram.get! P.rtI = r.ram.get! P.rtI) :
    VertModel.vsOf sy (frame M i) = VertJump.jumpOff sy m0 S (peek M sy.Player_Y_Position) (peek (trace M i k) sy.Player_XSpeedAbsolute) := by
  obtain ⟨a1, a2, _, a4⟩ := before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR.pc
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR.pc
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, I a ∈ vKeepA sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ ha
  obtain ⟨p1, p2, p3⟩ := press_of hj
  obtain ⟨kk, _, _, hpc, _, hv, hs1, hvy, hIn⟩ := VertJump.vert_jump hV hJ hR p1 p2 p3
  rw [eq sy.Player_Y_Position (by simp [vKeepA, vKeep])] at hv
  obtain ⟨htr, hfq⟩ := FrameModel.trace_inFrame hidle hfk hIn ht kk (Nat.le_refl kk)
  rw [← htr] at hpc hv hs1 hvy
  obtain ⟨_, b2⟩ := after_Q hB hfin hap hm hk
  have hrs : Rising sy (trace M i (k + kk)) := ⟨Or.inl hs1, hvy⟩
  rw [vsOf_eq_of (b2 (k + kk) hpc hfq hrs hrt), hv]

/-- **A frame of the room that starts a jump**, on the room: `jump_frame` with the checks of `RoomVert` and the takeoff's walk of two machines -/
theorem jump_room {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk)
    (hJ : VertJump.jumpOK sy m0 (FrameModel.ctrlStack sy m0) = true) {idle : UInt16} (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) idle = true)
    {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i k))
    (htm : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hj : (FrameModel.readIn sy (trace M i k)).jump = true)
    (hrt : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    VertModel.vsOf sy (frame M i) =
      VertJump.jumpOff sy m0 (FrameModel.ctrlStack sy m0) (peek M sy.Player_Y_Position) (peek (trace M i k) sy.Player_XSpeedAbsolute) := by
  have hair := hV.air
  simp only [VertAir.vertAirOK, Bool.and_eq_true] at hair
  exact jump_frame (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB) (RoomVert.okV_of_check hV.b) rfl hV.apart hair.1 hJ hidle hm hs hR
    htm hj hrt

end Smbrta.RoomJump
