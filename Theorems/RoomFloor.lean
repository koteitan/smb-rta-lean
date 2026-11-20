import Theorems.RoomStand
import Theorems.VertStand

/-!
# A frame of the room that starts standing on the floor

`RoomStand.stand_frame` follows a frame of the room that comes to the player's routine standing with no new press of A: he stands or falls off with the height kept, or
lands. Which one, the walk of the room's frames cannot tell: it does not know the floor's cells. Here the frame comes to the end of its move `Q` (the scroll handler) with the
stack of the player's routine and with the vertical bytes of its start (`VertStand.vert_stand`). If from `Q` on some step of the frame comes to the side check in the state
0 (`RoomLand.stand_at` says so on the floor's height, from the map's cells), the frame lands: the walk standing says that a frame that has not landed is not in the state 0
at the side check (`RoomStand.after_RS`). So the state, the vertical speed and its fraction are 0 at the frame's end, the height is that of the start with its low four bits 0,
and the vertical page is kept (`floor_frame`).

There is no game data in this file. Page: `1-1/c-7-5-14-FloorFrames.md`.
-/

namespace Smbrta.RoomFloor

open PipeTransition (frame)
open PipeTransitionAll (Names)
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK CfgS RoomCond)
open RoomVert (OKV phA I vKeep vKeepA before_R)
open VertAir (AtV)
open FrameModel (Rom stepN Good)

theorem standKeep_sub (sy : Syms) : ∀ x ∈ VertStand.standKeep sy, x ∈ vKeepA sy := by
  intro x hx
  have e : ∀ a, FrameModel.I a = I a := fun _ => rfl
  simp only [VertStand.standKeep, e, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [vKeepA, vKeep]

/-- **One frame of the room that starts standing with no new press of A.** The frame starts in the room's condition `M` standing with the vertical page 1, each instruction
meets `SiteOK`, the frame comes to the player's routine at instruction `k` in the state `AtV` with no jump in the input that the model reads there, A of the frame before
is the A that the machine holds, the frame does not end during the movement (`ht`), and it ends in the player's routine. Then it comes to the end of its move `j`, `Good`,
with the stack of the player's routine and the five bytes of `VertStand.standKeep` of its start; and if from `j` on a step of the frame comes to the side check in the state
0, the frame lands: at its end the state, the vertical speed and its fraction are 0, the height is the start's with its low four bits 0, and the vertical page is the
start's. The checks: the walk to the player's routine (`walkA`), the walk standing (`walkS`) with `apartS`, and the movement routine standing (`VertStand.standOK`, with
`OpenVert.vertAirHOK`). -/
theorem floor_frame {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CS : CfgS} {Fa Fs : Nat}
    (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hS : OKV (RoomStand.phS sy E P) E P r K CS Fs) (hfS : CS.fin = RoomStand.finS sy P r) (hap : RoomStand.apartS sy P = true)
    (hH : OpenVert.vertAirHOK sy m0 S = true) (hV : VertStand.standOK sy m0 S = true) {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 0) (hn : (FrameModel.readIn sy (trace M i k)).jump = false)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80) (hhi : peek M sy.Player_Y_HighPos = 1)
    (hrt : (frame M i).ram.get! P.rtI = r.ram.get! P.rtI) :
    ∃ j, k ≤ j ∧ (trace M i j).pc = sy.PlayerSubs ∧ (trace M i j).frame = M.frame ∧ Good (Rom.of m0) (trace M i j) ∧ (trace M i j).s = S ∧
      (∀ x ∈ VertStand.standKeep sy, (trace M i j).ram.get! x = M.ram.get! x) ∧
      ((∃ k', j ≤ k' ∧ (trace M i k').frame = M.frame ∧ (trace M i k').pc = sy.DoPlayerSideCheck ∧ (trace M i k').ram.get! (I sy.Player_State) = 0) →
        (frame M i).ram.get! (I sy.Player_State) = 0 ∧ (frame M i).ram.get! (I sy.Player_Y_Speed) = 0 ∧ (frame M i).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
        (frame M i).ram.get! (I sy.Player_Y_Position) = M.ram.get! (I sy.Player_Y_Position) &&& 0xF0 ∧
        (frame M i).ram.get! (I sy.Player_Y_HighPos) = M.ram.get! (I sy.Player_Y_HighPos)) := by
  obtain ⟨a1, a2, _, a4⟩ := before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR.pc
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR.pc
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, I a ∈ vKeepA sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ ha
  have hs0 : peek (trace M i k) sy.Player_State = 0 := by rw [eq _ (by simp [vKeepA, vKeep])]; exact hst
  have hn' := RoomStand.nopress_of hs0 hn
  obtain ⟨kk, _, hg, hpc, hss, hIn, h5⟩ := VertStand.vert_stand hH hV hR (by rw [eq _ (by simp [vKeepA])]; exact hhi) hs0 hn'
    (by rw [eq sy.PreviousA_B_Buttons (by simp [vKeepA]), eq sy.A_B_Buttons (by simp [vKeepA, vKeep])]; exact hp)
  obtain ⟨htr, hfq⟩ := FrameModel.trace_inFrame hidle hfk hIn ht kk (Nat.le_refl kk)
  rw [← htr] at hpc hg hss h5
  refine ⟨k + kk, by omega, hpc, hfq, hg, hss, fun x hx => (h5 x hx).trans (hkeep x (standKeep_sub sy x hx)), fun ⟨k', hk1, hk2, hk3, hk4⟩ => ?_⟩
  -- the walk standing: the frame lands, or it is not in the state 0 at the side check
  have hstd : RoomStand.StandAt sy (trace M i k) := ⟨hs0, hn'⟩
  obtain ⟨e1, e2⟩ := (RoomStand.after_RS hS hfS hap hm hk).2 k hR.pc hfk hstd hrt
  rcases e2 with ⟨_, _, hside⟩ | ⟨g1, g2, g3, g4⟩
  · exact absurd hk4 (hside k' (by omega) hk2 hk3)
  · refine ⟨g1, g2, g3, ?_, ?_⟩
    · rw [g4, hkeep (I sy.Player_Y_Position) (by simp [vKeepA, vKeep])]
    · rw [e1 (I sy.Player_Y_HighPos) (by simp [RoomStand.vRestS]), hkeep (I sy.Player_Y_HighPos) (by simp [vKeepA])]

end Smbrta.RoomFloor
