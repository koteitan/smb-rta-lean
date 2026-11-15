import Theorems.RoomFall
import Theorems.RoomJoin

/-!
# The vertical bytes of a frame in the room that starts standing

`RoomFall` follows a frame of the room in the air. Here a fourth walk of one whole frame of the room (`walkS`) follows a frame that comes to the player's routine `R`
standing (the state 0) with no new press of A: A not pressed, or pressed on the frame before too. Then the frame does not jump. From `R` to the frame's end no step writes
the height's fraction, the two forces and the jump's origin (`vRestS`); and the height, the vertical speed and its fraction (`vLand3`) stay and the state is 0 or 2 at the
end (he stands, or falls off), or he lands: the state 0, the speed and its fraction 0, the height with its low four bits 0 (`after_RS`).

At `R` the walk splits a state by the player's state (0 or not) and, in the state 0, by bit 7 of the joypad's bits and of A of the frame before. A state standing with no new
press gets the bit and the list `[7, 1]` (A not pressed) or `[7, 2]` (pressed on the frame before too), kept apart up to the jump's check; at the scroll handler `Q` both
become `[7, 7]`. The collision routine stores the state 2 (he may fall) before the foot check: the lists `[7, _]` allow a store to the state. As in
`RoomFall` the state is split by the height's high four bits at the landing's `AND` with the height (`[5, h]`), the landing's stores mark it `[1, h, 0]`, and a state that knows
the landing's four bytes gets `[6]`.

There is no game data in this file. Page: `1-1/c-7-5-5-RoomStand.md`.
-/

namespace Smbrta.RoomStand

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop)
open ScreenPage (Places SiteOK PlacesOK CfgS clampS preS weaken coverS RoomCond startsR MaskOK Aids SearchS routeS)
open RoomVert (Ph walkV I vKeep withBit canBe canBit knIs knP hiP OKV)
open RoomFall (vLand vRest withHi canHi his yPieces isAndY mayWrite landed)

/-! ## The bytes -/

/-- the bytes a frame that starts standing keeps from `R` on: the height's fraction, the two forces, the jump's origin -/
def vRestS (sy : Syms) : List Nat := [I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position]

/-- the bytes of the landing but the state: the height, the vertical speed, its fraction -/
def vLand3 (sy : Syms) : List Nat := [I sy.Player_Y_Position, I sy.Player_Y_Speed, I sy.Player_Y_MoveForce]

/-- **Standing with no new press of A**: the state 0, and bit 7 of the joypad's bits 0, or bit 7 of A of the frame before 1 -/
def StandAt (sy : Syms) (m : Machine) : Prop :=
  m.ram.get! (I sy.Player_State) = 0 ∧
    (m.ram.get! (I sy.SavedJoypadBits) &&& 0x80 = 0 ∨ m.ram.get! (I sy.PreviousA_B_Buttons) &&& 0x80 = 0x80)

/-! ## The walk from the player's routine, standing -/

/-- standing, A not pressed: with the bit set and marked `[7, 1]` -/
def standP0 (sy : Syms) (A : AS) : List AS :=
  if canBe (A.getK (I sy.Player_State)) 0 && canBit (A.getK (I sy.SavedJoypadBits)) 0x80 false then
    [{ (A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false) with spent := true, log := [7, 1] }]
  else []

/-- standing, A pressed on this frame and on the frame before: with the bit set and marked `[7, 2]` -/
def standP1 (sy : Syms) (A : AS) : List AS :=
  if canBe (A.getK (I sy.Player_State)) 0 && canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true && canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true then
    [{ ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons)
        (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true) with spent := true, log := [7, 2] }]
  else []

/-- standing, A newly pressed: marked `[2]` -/
def newP (sy : Syms) (A : AS) : List AS :=
  if canBe (A.getK (I sy.Player_State)) 0 && canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true && canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false then
    [{ ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons)
        (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false) with log := [2] }]
  else []

/-- the pieces at the player's routine: standing with no new press, with the bit set; and the other states, marked `[2]`: standing with a new press, the state 1, 2, 3,
or a state with a bit above bit 1 -/
def piecesS (sy : Syms) (A : AS) : List AS :=
  standP0 sy A ++ standP1 sy A ++ newP sy A ++ knP sy A 1 ++ knP sy A 2 ++ knP sy A 3 ++ hiP sy A

/-- the bit says that the frame came to the player's routine `R` standing with no new press, and that no step since has written the bytes of `vRestS`. The list says what
happened to the bytes of the landing: `[7, _]` the height, the speed and its fraction not written (the state may be; `[7, 1]`, `[7, 2]` up to `Q`, `[7, 7]` after); `[5, h]` the same, the height's high bits known to be
`h` (split at the landing's `AND` with the height); `[1, h, 0]` written since; `[6]` landed: the four known (the state, the speed and its fraction 0, the height `h`), then the
height forgotten, and no byte of the landing written since. A step that may write a byte where the list does not allow it drops the bit and marks the state `[4, 4, 4]`;
such a state must end the frame out of the player's routine (`finS`). The other states at `R` are marked `[2]`. The walk asks that the frame comes to `R` once. -/
def phS (sy : Syms) (E : Env) (P : Places) : Ph where
  zone := fun A =>
    if A.pc == sy.PlayerCtrlRoutine && !A.spent && A.log.isEmpty then piecesS sy A
    else if A.spent && A.pc == sy.PlayerSubs && (A.log == [7, 1] || A.log == [7, 2]) then [{ A with log := [7, 7] }]
    else if A.spent && mayWrite E P (vRestS sy) A then [{ A with spent := false, log := [4, 4, 4] }]
    else if A.spent && A.log.head? == some 7 && isAndY sy E A then yPieces sy A
    else if A.spent && A.log.head? == some 7 && mayWrite E P (vLand3 sy) A then [{ A with spent := false, log := [4, 4, 4] }]
    else if A.spent && A.log == [6] && mayWrite E P (vLand sy) A then [{ A with spent := false, log := [4, 4, 4] }]
    else if A.spent && A.log.head? == some 5 && mayWrite E P (vLand3 sy) A then [{ A with log := [1, A.log.getD 1 0, 0] }]
    else if A.spent && A.log.head? == some 1 && landed sy A then [{ A.setK (I sy.Player_Y_Position) AB.top with log := [6] }]
    else [A]
  pre := fun A => !(A.pc == sy.PlayerCtrlRoutine && (A.spent || !A.log.isEmpty))
  ok := fun A => !A.spent || (!mayWrite E P (vRestS sy) A &&
    (A.log.head? == some 1 || (A.log == [6] && !mayWrite E P (vLand sy) A) || (A.log != [6] && !mayWrite E P (vLand3 sy) A)))

/-- the routine byte is known at the frame's end and is not the reference's: the frame leaves the player's routine -/
def outR (P : Places) (r : Machine) (B : AS) : Bool :=
  decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI

/-- at the frame's end: a state marked `[4, 4, 4]` or `[1, h, 0]` ends out of the player's routine; a state marked `[7, _]` or `[5, h]` knows the player's state to be 0 or
2, or ends out of the player's routine -/
def finS (sy : Syms) (P : Places) (r : Machine) (B : AS) : Bool :=
  match B.log with
  | [4, 4, 4] => outR P r B
  | [1, _, 0] => outR P r B
  | [7, _] => outR P r B || (knIs (B.getK (I sy.Player_State)) 0 || knIs (B.getK (I sy.Player_State)) 2)
  | [5, _] => outR P r B || (knIs (B.getK (I sy.Player_State)) 0 || knIs (B.getK (I sy.Player_State)) 2)
  | _ => true

section
open ScreenPage (placesR envR refR)

/-- the walk from the player's routine, standing, on the room -/
abbrev cfgS (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phS sy (envR sy nm m0) (placesR sy nm m0)) (finS sy (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (envR sy nm m0)
    (refR m0) (RoomMap.knownT sy nm m0)

/-- the check of the walk from the player's routine, standing -/
def checkS (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  RoomVert.walkCheckV sy (phS sy (envR sy nm m0) (placesR sy nm m0)) (finS sy (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0)
    (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

end

/-! ## The pieces -/

section
variable {E : Env} {F : Nat × UInt8}
open RoomVert (getK_setK_self getK_setK_ne setK_ram_size setK_kn_size u8_all withBit_true_mem withBit_false_mem withBit_true_of withBit_false_of
  canBe_of canBit_of mem_known sim_bits vy_cases st_cases getK_one)

theorem getK3 {A : AS} {i j k : Nat} {u v w : AB} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) (hi : i < 2048)
    (hj : j < 2048) (hk : k < 2048) :
    (((A.setK i u).setK j v).setK k w).getK i = u ∧ (((A.setK i u).setK j v).setK k w).getK j = v ∧ (((A.setK i u).setK j v).setK k w).getK k = w := by
  refine ⟨?_, ?_, ?_⟩
  · rw [getK_setK_ne (Ne.symm hik), getK_setK_ne (Ne.symm hij), getK_setK_self (by rw [hsz.1]; exact hi) (by rw [hsz.2]; exact hi)]
  · rw [getK_setK_ne (Ne.symm hjk), getK_setK_self (by rw [setK_ram_size, hsz.1]; exact hj) (by rw [setK_kn_size, hsz.2]; exact hj)]
  · rw [getK_setK_self (by rw [setK_ram_size, setK_ram_size, hsz.1]; exact hk) (by rw [setK_kn_size, setK_kn_size, hsz.2]; exact hk)]

theorem b80_mem : (0x80 : UInt8) ∈ ([4, 8, 16, 32, 64, 128] : List UInt8) := by decide

theorem hi_not0 : ∀ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), (0 : UInt8) &&& b ≠ b := by decide

/-- every piece at the player's routine is standing with no new press, with the bit set and marked `[7, 1]` or `[7, 2]`, or not so, marked `[2]` -/
theorem piecesS_class {sy : Syms} {A A₁ : AS} {x : Machine} (h12 : I sy.Player_State ≠ I sy.SavedJoypadBits) (h13 : I sy.Player_State ≠ I sy.PreviousA_B_Buttons)
    (h23 : I sy.SavedJoypadBits ≠ I sy.PreviousA_B_Buttons) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048)
    (h : A₁ ∈ piecesS sy A) (hs : Sim E F A₁ x) :
    (A₁.spent = true ∧ (A₁.log = [7, 1] ∨ A₁.log = [7, 2]) ∧ StandAt sy x) ∨ (A₁.spent = A.spent ∧ A₁.log = [2] ∧ ¬ StandAt sy x) := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hjl : I sy.SavedJoypadBits < 2048 := PipeTransitionAll.mask_lt _
  have hpl : I sy.PreviousA_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  have notS : ∀ c, c ≠ 0 → x.ram.get! (I sy.Player_State) = c → ¬ StandAt sy x := fun c h1 h2 hr => h1 (h2.symm.trans hr.1)
  simp only [piecesS, List.mem_append] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · unfold standP0 at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have g1 : ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)).getK
          (I sy.Player_State) = AB.known 0 := by
        rw [getK_setK_ne (Ne.symm h12), getK_setK_self (by rw [hsz.1]; exact hsl) (by rw [hsz.2]; exact hsl)]
      have g2 : ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)).getK
          (I sy.SavedJoypadBits) = withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false := by
        rw [getK_setK_self (by rw [setK_ram_size, hsz.1]; exact hjl) (by rw [setK_kn_size, hsz.2]; exact hjl)]
      have m1 : (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)).getK
          (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have m2 : (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)).getK
          (I sy.SavedJoypadBits)).mem (x.ram.get! (I sy.SavedJoypadBits)) := hs.ram _ hjl
      rw [g1] at m1
      rw [g2] at m2
      exact Or.inl ⟨rfl, Or.inl rfl, mem_known m1, Or.inl (withBit_false_mem m2)⟩
    · cases h
  · unfold standP1 at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, _, g3⟩ := getK3 (A := A) (u := AB.known 0) (v := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)
        (w := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true) h12 h13 h23 hsz hsl hjl hpl
      have m1 : ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK
          (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) :=
        hs.ram _ hsl
      have m3 : ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK
          (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true)).getK (I sy.PreviousA_B_Buttons)).mem
          (x.ram.get! (I sy.PreviousA_B_Buttons)) := hs.ram _ hpl
      rw [g1] at m1
      rw [g3] at m3
      exact Or.inl ⟨rfl, Or.inr rfl, mem_known m1, Or.inr (withBit_true_mem b80_mem m3)⟩
    · cases h
  · unfold newP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, g2, g3⟩ := getK3 (A := A) (u := AB.known 0) (v := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)
        (w := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false) h12 h13 h23 hsz hsl hjl hpl
      have m2 : ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK
          (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false)).getK (I sy.SavedJoypadBits)).mem
          (x.ram.get! (I sy.SavedJoypadBits)) := hs.ram _ hjl
      have m3 : ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK
          (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false)).getK (I sy.PreviousA_B_Buttons)).mem
          (x.ram.get! (I sy.PreviousA_B_Buttons)) := hs.ram _ hpl
      rw [g2] at m2
      rw [g3] at m3
      have e2 := withBit_true_mem b80_mem m2
      have e3 := withBit_false_mem m3
      refine Or.inr ⟨rfl, rfl, fun hr => ?_⟩
      rcases hr.2 with e | e
      · rw [e] at e2
        exact absurd e2 (by decide)
      · rw [e] at e3
        exact absurd e3 (by decide)
    · cases h
  all_goals first
    | (unfold knP at h
       split at h
       · obtain rfl := List.mem_singleton.1 h
         have h1 : ((A.setK (I sy.Player_State) (AB.known _)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
         rw [getK_one hsz hsl] at h1
         exact Or.inr ⟨rfl, rfl, notS _ (by decide) (mem_known h1)⟩
       · cases h)
    | (unfold RoomVert.hiP at h
       obtain ⟨b, hb, h⟩ := List.mem_flatMap.1 h
       split at h
       · obtain rfl := List.mem_singleton.1 h
         have h1 : ((A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true)).getK (I sy.Player_State)).mem
           (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
         rw [getK_one hsz hsl] at h1
         have h3 := withBit_true_mem hb h1
         refine Or.inr ⟨rfl, rfl, fun hr => ?_⟩
         rw [hr.1] at h3
         exact hi_not0 b hb h3
       · cases h)

/-- the pieces at the player's routine cover every machine of the state -/
theorem piecesS_cover {sy : Syms} {A : AS} {x : Machine} (hr : A.rk = false) (hs : Sim E F A x) : ∃ A₁ ∈ piecesS sy A, Sim E F A₁ x := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hjl : I sy.SavedJoypadBits < 2048 := PipeTransitionAll.mask_lt _
  have hpl : I sy.PreviousA_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  have ms := hs.ram _ hsl
  have mj := hs.ram _ hjl
  have mp := hs.ram _ hpl
  generalize hst : x.ram.get! (I sy.Player_State) = st at ms
  generalize hj : x.ram.get! (I sy.SavedJoypadBits) = jv at mj
  generalize hp : x.ram.get! (I sy.PreviousA_B_Buttons) = pv at mp
  have L : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₁ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_left _ h
  have R : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₂ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_right _ h
  have kn : ∀ c, st = c → canBe (A.getK (I sy.Player_State)) c = true ∧ Sim E F (A.setK (I sy.Player_State) (AB.known c)) x := fun c e => by
    subst e
    exact ⟨canBe_of ms, PipeEntryRule.sim_setK' hs (by rw [hst]; exact mem_known_self st)⟩
  have knp : ∀ c, st = c → ∃ A₁ ∈ knP sy A c, Sim E F A₁ x := fun c e => by
    obtain ⟨c1, c2⟩ := kn c e
    unfold knP
    rw [if_pos c1]
    exact ⟨_, List.mem_singleton.2 rfl, sim_bits c2 hr _ _⟩
  rcases (u8_all (P := fun t => t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ ∃ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), t &&& b = b) st_cases) st with
    e | e | e | e | ⟨b, hb, e⟩
  · obtain ⟨c1, s1⟩ := kn 0 e
    rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) jv with hv | hv
    · have c2 : canBit (A.getK (I sy.SavedJoypadBits)) 0x80 false = true := canBit_of mj false (by rw [hv]; decide)
      have s2 := PipeEntryRule.sim_setK' s1 (d := I sy.SavedJoypadBits) (v := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)
        (by rw [hj]; exact withBit_false_of mj hv)
      refine ⟨_, L (L (L (L (L (L (?_ : _ ∈ standP0 sy A)))))), sim_bits s2 hr true [7, 1]⟩
      unfold standP0
      rw [if_pos (by rw [c1, c2]; rfl)]
      exact List.mem_singleton.2 rfl
    · have c2 : canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true = true := canBit_of mj true (by rw [hv]; decide)
      have s2 := PipeEntryRule.sim_setK' s1 (d := I sy.SavedJoypadBits) (v := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)
        (by rw [hj]; exact withBit_true_of b80_mem mj hv)
      rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) pv with hq | hq
      · have c3 : canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false = true := canBit_of mp false (by rw [hq]; decide)
        have s3 := PipeEntryRule.sim_setK' s2 (d := I sy.PreviousA_B_Buttons) (v := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false)
          (by rw [hp]; exact withBit_false_of mp hq)
        refine ⟨_, L (L (L (L (R (?_ : _ ∈ newP sy A))))), sim_bits s3 hr A.spent [2]⟩
        unfold newP
        rw [if_pos (by rw [c1, c2, c3]; rfl)]
        exact List.mem_singleton.2 rfl
      · have c3 : canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true = true := canBit_of mp true (by rw [hq]; decide)
        have s3 := PipeEntryRule.sim_setK' s2 (d := I sy.PreviousA_B_Buttons) (v := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true)
          (by rw [hp]; exact withBit_true_of b80_mem mp hq)
        refine ⟨_, L (L (L (L (L (R (?_ : _ ∈ standP1 sy A)))))), sim_bits s3 hr true [7, 2]⟩
        unfold standP1
        rw [if_pos (by rw [c1, c2, c3]; rfl)]
        exact List.mem_singleton.2 rfl
  · obtain ⟨A₁, h1, h2⟩ := knp 1 e
    exact ⟨A₁, L (L (L (R h1))), h2⟩
  · obtain ⟨A₁, h1, h2⟩ := knp 2 e
    exact ⟨A₁, L (L (R h1)), h2⟩
  · obtain ⟨A₁, h1, h2⟩ := knp 3 e
    exact ⟨A₁, L (R h1), h2⟩
  · have c1 : canBit (A.getK (I sy.Player_State)) b true = true := canBit_of ms true (by
      rw [e]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hm : ({ A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true) with log := [2] } : AS) ∈ hiP sy A := by
      unfold hiP
      exact List.mem_flatMap.2 ⟨b, hb, by rw [if_pos c1]; exact List.mem_singleton.2 rfl⟩
    exact ⟨_, R hm, sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst]; exact withBit_true_of hb ms e)) hr _ _⟩
end

/-! ## The frame from the player's routine, standing -/

/-- the bytes apart: those of `RoomFall.apartC`, and the state, the joypad's bits and A of the frame before are three bytes -/
def apartS (sy : Syms) (P : Places) : Bool :=
  RoomFall.apartC sy P && I sy.Player_State != I sy.SavedJoypadBits && I sy.Player_State != I sy.PreviousA_B_Buttons &&
    I sy.SavedJoypadBits != I sy.PreviousA_B_Buttons

theorem vRestS_sub (sy : Syms) : ∀ x ∈ vRestS sy, x ∈ vKeep sy := by
  intro x hx
  simp only [vRestS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [vKeep]

theorem vLand3_sub (sy : Syms) : ∀ x ∈ vLand3 sy, x ∈ vKeep sy := by
  intro x hx
  simp only [vLand3, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [vKeep]

theorem vLand_sub (sy : Syms) : ∀ x ∈ vLand sy, x ∈ vKeep sy := RoomFall.vLand_sub sy

theorem l77_2 : ([7, 7] : List Nat) ≠ [2] := by decide

set_option maxHeartbeats 1000000 in
/-- **The frame from the player's routine, standing.** The frame comes to the player's routine at most once. If it comes there standing with no new press of A, and ends in
the player's routine, then from there to its end no step writes the height's fraction, the forces and the jump's origin; and the height, the vertical speed and its fraction
stay and the state is 0 or 2 at the end, or he lands: the state, the vertical speed and its fraction are 0, and the height is the one at the player's routine with the low
four bits 0. The frame starts in the room's condition, and each instruction meets `SiteOK`. -/
theorem after_RS {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV (phS sy E P) E P r K C Fu)
    (hfin : C.fin = finS sy P r) (hap : apartS sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerCtrlRoutine) ∧
    (∀ j, (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j).frame = m.frame → StandAt sy (trace m i j) → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       (∀ x ∈ vRestS sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) ∧
       (((∀ x ∈ vLand3 sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) ∧
         ((frame m i).ram.get! (I sy.Player_State) = 0 ∨ (frame m i).ram.get! (I sy.Player_State) = 2)) ∨
        ((frame m i).ram.get! (I sy.Player_State) = 0 ∧ (frame m i).ram.get! (I sy.Player_Y_Speed) = 0 ∧
         (frame m i).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
         (frame m i).ram.get! (I sy.Player_Y_Position) = (trace m i j).ram.get! (I sy.Player_Y_Position) &&& 0xF0))) := by
  obtain ⟨S, hw, hs, s1, s2, s3⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  have hsz : ∀ (A : AS) (y : Machine), Sim C.E (m.frame, 2) A y → A.ram.size = 2048 ∧ A.kn.size = 2048 := fun _ _ hs => ⟨hs.szR, hs.szK⟩
  simp only [apartS, RoomFall.apartC, Bool.and_eq_true, bne_iff_ne, ne_eq] at hap
  obtain ⟨⟨⟨⟨⟨hapB, _⟩, _⟩, h12⟩, h13⟩, h23⟩ := hap
  have hout : ∀ x ∈ vKeep sy, x < P.bufLo ∨ P.bufLo + P.bufN ≤ x := by
    simp only [RoomVert.apartB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hapB
    exact hapB.1
  have hyL : I sy.Player_Y_Position ∈ vLand sy := by simp [vLand]
  have hvL : I sy.Player_Y_Speed ∈ vLand sy := by simp [vLand]
  have hmL : I sy.Player_Y_MoveForce ∈ vLand sy := by simp [vLand]
  have hsL : I sy.Player_State ∈ vLand sy := by simp [vLand]
  have hy3 : I sy.Player_Y_Position ∈ vLand3 sy := by simp [vLand3]
  let R := sy.PlayerCtrlRoutine
  let Vs : List Nat → Nat → Nat → Prop := fun L j j₀ => ∀ x ∈ L, (trace m i j).ram.get! x = (trace m i j₀).ram.get! x
  let yQ : Nat → Nat := fun j₀ => ((trace m i j₀).ram.get! (I sy.Player_Y_Position) &&& 0xF0).toNat
  let Φ : Nat → Bool → List Nat → Prop := fun j b l =>
    (∀ j₀, j₀ < j → (trace m i j₀).pc = R → (b = true ∨ l ≠ [])) ∧
    (b = true → ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = R ∧ StandAt sy (trace m i j₀) ∧ Vs (vRestS sy) j j₀ ∧
      (((l = [7, 1] ∨ l = [7, 2] ∨ l = [7, 7]) ∧ Vs (vLand3 sy) j j₀) ∨ (l = [5, yQ j₀] ∧ Vs (vLand3 sy) j j₀) ∨ l = [1, yQ j₀, 0] ∨
       (l = [6] ∧ (trace m i j).ram.get! (I sy.Player_Y_Position) = (trace m i j₀).ram.get! (I sy.Player_Y_Position) &&& 0xF0 ∧
        (trace m i j).ram.get! (I sy.Player_Y_Speed) = 0 ∧ (trace m i j).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
        (trace m i j).ram.get! (I sy.Player_State) = 0))) ∧
    (l = [2] → ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = R ∧ ¬ StandAt sy (trace m i j₀)) ∧
    (b = false → l = [] ∨ l = [2] ∨ l = [4, 4, 4])
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phS sy E P).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    show ∃ A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent && A'.log.isEmpty then piecesS sy A'
      else if A'.spent && A'.pc == sy.PlayerSubs && (A'.log == [7, 1] || A'.log == [7, 2]) then [{ A' with log := [7, 7] }]
      else if A'.spent && mayWrite E P (vRestS sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log.head? == some 7 && isAndY sy E A' then yPieces sy A'
      else if A'.spent && A'.log.head? == some 7 && mayWrite E P (vLand3 sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log == [6] && mayWrite E P (vLand sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log.head? == some 5 && mayWrite E P (vLand3 sy) A' then [{ A' with log := [1, A'.log.getD 1 0, 0] }]
      else if A'.spent && A'.log.head? == some 1 && landed sy A' then [{ A'.setK (I sy.Player_Y_Position) AB.top with log := [6] }]
      else [A']), _
    split
    · exact piecesS_cover hr hsx
    · split
      · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr A'.spent [7, 7]⟩
      · split
        · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr false [4, 4, 4]⟩
        · split
          · exact RoomFall.yPieces_cover hr hsx
          · split
            · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr false [4, 4, 4]⟩
            · split
              · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr false [4, 4, 4]⟩
              · split
                · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr A'.spent [1, A'.log.getD 1 0, 0]⟩
                · split
                  · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits (PipeEntryRule.sim_setK' hsx (mem_top _)) hr A'.spent [6]⟩
                  · exact ⟨A', List.mem_singleton.2 rfl, hsx⟩
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phS sy E P).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phS sy E P).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2, p3, p4⟩ hs' hf hr hA₁ hs₁ hok
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
    have hnext : trace m i (j + 1) = (go step (trace m i j)).2 := RoomVert.trace_succ hf hs'.halted
    have okS : A₁.spent = true → mayWrite E P (vRestS sy) A₁ = false ∧ (A₁.log.head? = some 1 ∨ (A₁.log = [6] ∧ mayWrite E P (vLand sy) A₁ = false) ∨
        (A₁.log ≠ [6] ∧ mayWrite E P (vLand3 sy) A₁ = false)) := by
      intro hb
      have hok' : (!A₁.spent || (!mayWrite E P (vRestS sy) A₁ &&
          (A₁.log.head? == some 1 || (A₁.log == [6] && !mayWrite E P (vLand sy) A₁) || (A₁.log != [6] && !mayWrite E P (vLand3 sy) A₁)))) = true := hok
      simp only [hb, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok'
      obtain ⟨o1, o2⟩ := hok'
      refine ⟨o1, ?_⟩
      rcases o2 with (o | o) | o
      · exact Or.inl o
      · exact Or.inr (Or.inl o)
      · exact Or.inr (Or.inr o)
    have keepR : A₁.spent = true → Vs (vRestS sy) (j + 1) j := by
      intro hb x hx
      rw [hnext]
      exact RoomFall.keep_of_may h.places (fun x hx => hout x (vRestS_sub sy x hx)) hs₂ (hk j) (okS hb).1 x hx
    have keep3 : A₁.spent = true → A₁.log.head? ≠ some 1 → A₁.log ≠ [6] → Vs (vLand3 sy) (j + 1) j := by
      intro hb h1 h6 x hx
      have h3 : mayWrite E P (vLand3 sy) A₁ = false := by
        rcases (okS hb).2 with e | e | e
        · exact absurd e h1
        · exact absurd e.1 h6
        · exact e.2
      rw [hnext]
      exact RoomFall.keep_of_may h.places (fun x hx => hout x (vLand3_sub sy x hx)) hs₂ (hk j) h3 x hx
    have keepL : A₁.spent = true → A₁.log = [6] → Vs (vLand sy) (j + 1) j := by
      intro hb h6 x hx
      have h3 : mayWrite E P (vLand sy) A₁ = false := by
        rcases (okS hb).2 with e | e | e
        · rw [h6] at e
          simp at e
        · exact e.2
        · exact absurd h6 e.1
      rw [hnext]
      exact RoomFall.keep_of_may h.places (fun x hx => hout x (vLand_sub sy x hx)) hs₂ (hk j) h3 x hx
    have tr : ∀ {L : List Nat} {j₀ : Nat}, Vs L (j + 1) j → Vs L j j₀ → Vs L (j + 1) j₀ := fun h1 h2 x hx => by rw [h1 x hx]; exact h2 x hx
    have out : A₁.spent = false → A₁.log = [4, 4, 4] → Φ (j + 1) A₁.spent A₁.log := by
      intro hb hl
      rw [hb, hl]
      exact ⟨fun _ _ _ => Or.inr (by simp), fun h => absurd h (by decide), fun h => by simp at h, fun _ => Or.inr (Or.inr rfl)⟩
    -- the list of a state with the bit
    have cases7 : ∀ {j₀ : Nat} {l : List Nat}, (((l = [7, 1] ∨ l = [7, 2] ∨ l = [7, 7]) ∧ Vs (vLand3 sy) j j₀) ∨ (l = [5, yQ j₀] ∧ Vs (vLand3 sy) j j₀) ∨
        l = [1, yQ j₀, 0] ∨ (l = [6] ∧ (trace m i j).ram.get! (I sy.Player_Y_Position) = (trace m i j₀).ram.get! (I sy.Player_Y_Position) &&& 0xF0 ∧
        (trace m i j).ram.get! (I sy.Player_Y_Speed) = 0 ∧ (trace m i j).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
        (trace m i j).ram.get! (I sy.Player_State) = 0)) → l.head? = some 7 → ((l = [7, 1] ∨ l = [7, 2] ∨ l = [7, 7]) ∧ Vs (vLand3 sy) j j₀) := by
      intro j₀ l a5 hl
      rcases a5 with e | ⟨e, _⟩ | e | ⟨e, _⟩
      · exact e
      · rw [e] at hl; simp at hl
      · rw [e] at hl; simp at hl
      · rw [e] at hl; simp at hl
    change A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent && A'.log.isEmpty then piecesS sy A'
      else if A'.spent && A'.pc == sy.PlayerSubs && (A'.log == [7, 1] || A'.log == [7, 2]) then [{ A' with log := [7, 7] }]
      else if A'.spent && mayWrite E P (vRestS sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log.head? == some 7 && isAndY sy E A' then yPieces sy A'
      else if A'.spent && A'.log.head? == some 7 && mayWrite E P (vLand3 sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log == [6] && mayWrite E P (vLand sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log.head? == some 5 && mayWrite E P (vLand3 sy) A' then [{ A' with log := [1, A'.log.getD 1 0, 0] }]
      else if A'.spent && A'.log.head? == some 1 && landed sy A' then [{ A'.setK (I sy.Player_Y_Position) AB.top with log := [6] }]
      else [A']) at hA₁
    split at hA₁
    · -- at the player's routine
      rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
      obtain ⟨⟨hq, hsp⟩, hlg⟩ := hc
      have hqj : (trace m i j).pc = R := by rw [hpc, hq]
      rcases piecesS_class h12 h13 h23 (hsz A' _ hs') hA₁ hs₁ with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
      · have n1 : A₁.log.head? ≠ some 1 := by rcases c2 with e | e <;> rw [e] <;> simp
        have n6 : A₁.log ≠ [6] := by rcases c2 with e | e <;> rw [e] <;> simp
        have n2 : A₁.log ≠ [2] := by rcases c2 with e | e <;> rw [e] <;> simp
        rw [c1]
        exact ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨j, by omega, hqj, c3, keepR c1, Or.inl ⟨by rcases c2 with e | e <;> simp [e], keep3 c1 n1 n6⟩⟩,
          fun h => absurd h n2, fun h => absurd h (by decide)⟩
      · rw [c1, c2, hsp]
        exact ⟨fun _ _ _ => Or.inr (by simp), fun h => absurd h (by decide), fun _ => ⟨j, by omega, hqj, c3⟩, fun _ => Or.inr (Or.inl rfl)⟩
    · rename_i hc
      split at hA₁
      · -- at the scroll handler: one list for both pieces
        rename_i hc2
        obtain rfl := List.mem_singleton.1 hA₁
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc2
        obtain ⟨⟨hb, _⟩, hl⟩ := hc2
        obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
        have hL := (cases7 a5 (by rcases hl with e | e <;> rw [e] <;> rfl)).2
        have hb' : ({ A' with log := [7, 7] } : AS).spent = true := hb
        exact ⟨fun _ _ _ => Or.inl hb, fun _ => ⟨j₀, by omega, a2, a3, tr (keepR hb') a4,
          Or.inl ⟨Or.inr (Or.inr rfl), tr (keep3 hb' (by show ([7, 7] : List Nat).head? ≠ some 1; decide) (by show ([7, 7] : List Nat) ≠ [6]; decide)) hL⟩⟩,
          fun h => absurd h l77_2, fun h => absurd (h.symm.trans hb) (by decide)⟩
      · split at hA₁
        · obtain rfl := List.mem_singleton.1 hA₁
          exact out rfl rfl
        · split at hA₁
          · -- the split by the height's high bits
            rename_i hc3 hc4
            simp only [Bool.and_eq_true, beq_iff_eq] at hc4
            obtain ⟨⟨hb, hl⟩, _⟩ := hc4
            obtain ⟨c1, c2⟩ := RoomFall.yPieces_class (hsz A' _ hs') hA₁ hs₁
            obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
            have hL := (cases7 a5 hl).2
            have hb1 : A₁.spent = true := by rw [c1, hb]
            rw [c1, c2, hb]
            refine ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨j₀, by omega, a2, a3, tr (keepR hb1) a4,
              Or.inr (Or.inl ⟨?_, tr (keep3 hb1 (by rw [c2]; simp) (by rw [c2]; simp)) hL⟩)⟩, fun h => by simp at h, fun h => absurd h (by decide)⟩
            show [5, ((trace m i j).ram.get! (I sy.Player_Y_Position) &&& 0xF0).toNat] = [5, yQ j₀]
            rw [hL _ hy3]
          · split at hA₁
            · obtain rfl := List.mem_singleton.1 hA₁
              exact out rfl rfl
            · split at hA₁
              · obtain rfl := List.mem_singleton.1 hA₁
                exact out rfl rfl
              · split at hA₁
                · -- a write of the landing's bytes after the split
                  rename_i hc7
                  obtain rfl := List.mem_singleton.1 hA₁
                  simp only [Bool.and_eq_true, beq_iff_eq] at hc7
                  obtain ⟨⟨hb, hl⟩, _⟩ := hc7
                  obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
                  have e5 : A'.log = [5, yQ j₀] := by
                    rcases a5 with ⟨e, _⟩ | ⟨e, _⟩ | e | ⟨e, _⟩
                    · rcases e with e | e | e <;> rw [e] at hl <;> simp at hl
                    · exact e
                    · rw [e] at hl; simp at hl
                    · rw [e] at hl; simp at hl
                  have hb' : ({ A' with log := [1, A'.log.getD 1 0, 0] } : AS).spent = true := hb
                  refine ⟨fun _ _ _ => Or.inl hb, fun _ => ⟨j₀, by omega, a2, a3, tr (keepR hb') a4, Or.inr (Or.inr (Or.inl ?_))⟩, fun h => by simp at h,
                    fun h => absurd (h.symm.trans hb) (by decide)⟩
                  show [1, A'.log.getD 1 0, 0] = [1, yQ j₀, 0]
                  rw [e5]
                  rfl
                · split at hA₁
                  · -- landed: the four bytes known, the height forgotten
                    rename_i hc8
                    obtain rfl := List.mem_singleton.1 hA₁
                    simp only [Bool.and_eq_true, beq_iff_eq] at hc8
                    obtain ⟨⟨hb, hl⟩, hland⟩ := hc8
                    obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
                    have e1 : A'.log = [1, yQ j₀, 0] := by
                      rcases a5 with ⟨e, _⟩ | ⟨e, _⟩ | e | ⟨e, _⟩
                      · rcases e with e | e | e <;> rw [e] at hl <;> simp at hl
                      · rw [e] at hl; simp at hl
                      · exact e
                      · rw [e] at hl; simp at hl
                    have hb' : ({ A'.setK (I sy.Player_Y_Position) AB.top with log := [6] } : AS).spent = true := hb
                    simp only [landed, Bool.and_eq_true] at hland
                    obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hland
                    have v1 := RoomVert.knIs_spec k1 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                    have v2 := RoomVert.knIs_spec k2 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                    have v3 := RoomVert.knIs_spec k3 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                    have v4 := RoomVert.knIs_spec k4 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                    rw [e1] at v4
                    have hkL := keepL hb' rfl
                    refine ⟨fun _ _ _ => Or.inl hb, fun _ => ⟨j₀, by omega, a2, a3, tr (keepR hb') a4, Or.inr (Or.inr (Or.inr ⟨rfl, ?_, ?_, ?_, ?_⟩))⟩,
                      fun h => by simp at h, fun h => absurd (h.symm.trans hb) (by decide)⟩
                    · rw [hkL _ hyL, v4]
                      exact RoomFall.toUInt8_toNat _
                    · rw [hkL _ hvL, v2]
                    · rw [hkL _ hmL, v3]
                    · rw [hkL _ hsL, v1]
                  · -- the state stays
                    obtain rfl := List.mem_singleton.1 hA₁
                    refine ⟨fun j₀ hj₀ hq₀ => ?_, fun hb => ?_, fun hl => ?_, p4⟩
                    · rcases Nat.lt_or_ge j₀ j with hlt | hge
                      · exact p1 j₀ hlt hq₀
                      · rw [show j₀ = j by omega, hpc] at hq₀
                        have hq' : A₁.pc = sy.PlayerCtrlRoutine := hq₀
                        simp only [hq', beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_and] at hc
                        cases hsp : A₁.spent with
                        | true => exact Or.inl rfl
                        | false => exact Or.inr (hc hsp)
                    · obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
                      refine ⟨j₀, by omega, a2, a3, tr (keepR hb) a4, ?_⟩
                      rcases a5 with ⟨e, f⟩ | ⟨e, f⟩ | e | ⟨e, f1, f2, f3, f4⟩
                      · exact Or.inl ⟨e, tr (keep3 hb (by rcases e with e | e | e <;> rw [e] <;> simp) (by rcases e with e | e | e <;> rw [e] <;> simp)) f⟩
                      · exact Or.inr (Or.inl ⟨e, tr (keep3 hb (by rw [e]; simp) (by rw [e]; simp)) f⟩)
                      · exact Or.inr (Or.inr (Or.inl e))
                      · have hkL := keepL hb e
                        exact Or.inr (Or.inr (Or.inr ⟨e, by rw [hkL _ hyL]; exact f1, by rw [hkL _ hvL]; exact f2, by rw [hkL _ hmL]; exact f3,
                          by rw [hkL _ hsL]; exact f4⟩))
                    · obtain ⟨j₀, a1, a2, a3⟩ := p3 hl
                      exact ⟨j₀, by omega, a2, a3⟩
  have h0 : Φ 0 S.spent S.log := by
    refine ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun hb => ?_, fun hl => ?_, fun _ => Or.inl s2⟩
    · rw [s1] at hb
      cases hb
    · rw [s2] at hl
      cases hl
  obtain ⟨hall, J, hJ1, hJ2, hJ3, B, hB1, hB2, hB3⟩ := RoomVert.frame_of_walkV (Z := phS sy E P) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0 hstep
  have uniq : ∀ j j', j < j' → (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerCtrlRoutine := by
    intro j j' hlt hq hj' hq'
    obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = sy.PlayerCtrlRoutine := by rw [← hsA.pc]; exact hq'
    simp only [phS, hApc, beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hpre
    rcases q1 j hlt hq with e | e
    · rw [hpre.1] at e
      cases e
    · exact e hpre.2
  refine ⟨uniq, fun jq hq hf hstand hrt => ?_⟩
  have hjJ : jq < J := by
    rcases Nat.lt_or_ge jq J with h1 | h1
    · exact h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (jq - J)
      rw [show J + (jq - J) = jq by omega] at e
      rw [e, hJ1] at hf
      omega
  have hfinB : finS sy P r B = true := by rw [← hfin]; exact hB1
  -- the frame does not end out of the player's routine
  have outF : outR P r B ≠ true := by
    intro e
    simp only [outR, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at e
    obtain ⟨⟨a1, a2⟩, a3⟩ := e
    have e2 := isK_eq a2 (hB2.ram _ a1)
    rw [← hJ3, hrt] at e2
    exact a3 e2.symm
  have notOut : ∀ l, (l = [4, 4, 4] ∨ ∃ a, l = [1, a, 0]) → B.log ≠ l := by
    intro l hl e
    apply outF
    rcases hl with rfl | ⟨a, rfl⟩ <;> simpa [finS, e] using hfinB
  -- a state that stands at the end knows the state 0 or 2
  have stK : (B.log = [7, 1] ∨ B.log = [7, 2] ∨ B.log = [7, 7] ∨ ∃ a, B.log = [5, a]) →
      (frame m i).ram.get! (I sy.Player_State) = 0 ∨ (frame m i).ram.get! (I sy.Player_State) = 2 := by
    intro hl
    have h1 : outR P r B = true ∨ (knIs (B.getK (I sy.Player_State)) 0 = true ∨ knIs (B.getK (I sy.Player_State)) 2 = true) := by
      rcases hl with e | e | e | ⟨a, e⟩ <;> simpa [finS, e] using hfinB
    rw [hJ3]
    rcases h1 with e | e | e
    · exact absurd e outF
    · exact Or.inl (RoomVert.knIs_spec e (hB2.ram _ (PipeTransitionAll.mask_lt _)))
    · exact Or.inr (RoomVert.knIs_spec e (hB2.ram _ (PipeTransitionAll.mask_lt _)))
  obtain ⟨q1, q2, q3, q4⟩ := hB3
  have only : ∀ j₀, j₀ < J → (trace m i j₀).pc = sy.PlayerCtrlRoutine → j₀ = jq := by
    intro j₀ h1 h2
    rcases Nat.lt_trichotomy j₀ jq with e | e | e
    · exact absurd hq (uniq j₀ jq e h2 hf)
    · exact e
    · exact absurd h2 (uniq jq j₀ e hq (hJ2 j₀ h1))
  cases hb : B.spent with
  | true =>
    obtain ⟨j₀, a1, a2, _, a4, a5⟩ := q2 hb
    have e0 := only j₀ a1 a2
    subst e0
    rcases a5 with ⟨e, f⟩ | ⟨e, f⟩ | e | ⟨_, f1, f2, f3, f4⟩
    · have hst := stK (by rcases e with e | e | e <;> simp [e])
      rw [hJ3] at hst ⊢
      exact ⟨a4, Or.inl ⟨f, hst⟩⟩
    · have hst := stK (Or.inr (Or.inr (Or.inr ⟨_, e⟩)))
      rw [hJ3] at hst ⊢
      exact ⟨a4, Or.inl ⟨f, hst⟩⟩
    · exact absurd e (notOut _ (Or.inr ⟨_, rfl⟩))
    · rw [hJ3]
      exact ⟨a4, Or.inr ⟨f4, f2, f3, f1⟩⟩
  | false =>
    rcases q4 hb with e | e | e
    · rcases q1 jq hjJ hq with e2 | e2
      · rw [hb] at e2
        cases e2
      · exact absurd e e2
    · obtain ⟨j₀, a1, a2, a3⟩ := q3 e
      rw [only j₀ a1 a2] at a3
      exact absurd hstand a3
    · exact absurd e (notOut _ (Or.inl rfl))

/-! ## One frame of the room that starts standing -/

theorem b80_cases : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 ∨ UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel

/-- standing, the jump bit of the input that the model reads is 0 only with no new press of A -/
theorem nopress_of {sy : Syms} {x : Machine} (h0 : peek x sy.Player_State = 0) (hn : (FrameModel.readIn sy x).jump = false) :
    x.ram.get! (I sy.SavedJoypadBits) &&& 0x80 = 0 ∨ x.ram.get! (I sy.PreviousA_B_Buttons) &&& 0x80 = 0x80 := by
  have e : (FrameModel.readIn sy x).jump = (peek x sy.Player_State == 0 && peek x sy.SavedJoypadBits &&& 0x80 != 0 &&
      peek x sy.PreviousA_B_Buttons &&& 0x80 == 0) := rfl
  rw [e, h0] at hn
  have c1 := b80_cases ⟨(peek x sy.SavedJoypadBits).toNat, (peek x sy.SavedJoypadBits).toNat_lt⟩
  have c2 := b80_cases ⟨(peek x sy.PreviousA_B_Buttons).toNat, (peek x sy.PreviousA_B_Buttons).toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at c1 c2
  show peek x sy.SavedJoypadBits &&& 0x80 = 0 ∨ peek x sy.PreviousA_B_Buttons &&& 0x80 = 0x80
  rcases c1 with e1 | e1
  · exact Or.inl e1
  · rcases c2 with e2 | e2
    · rw [e1, e2] at hn
      exact absurd hn (by decide)
    · exact Or.inr e2

section
open RoomVert (vKeepA)

/-- **A frame of the room that starts standing with no new press of A.** The frame starts in the room's condition `M` standing (the state 0), each instruction meets
`SiteOK`, the frame comes to the player's routine at instruction `k` with no jump in the input that the model reads there (`FrameModel.readIn`: no new press of A), and
the frame ends in the player's routine. Then the vertical state at the frame's end is one that `RoomJoin.StandNext` allows: he stands or falls off with the height and the speed kept, or lands. The checks:
the walk to the player's routine (`walkA`) and the walk from there standing (`walkS`), and `apartS`. -/
theorem stand_frame {sy : Syms} {S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CS : CfgS} {Fa Fs : Nat}
    (hpz : pz < 2048) (hA : OKV (RoomVert.phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hS : OKV (phS sy E P) E P r K CS Fs) (hfS : CS.fin = finS sy P r) (hap : apartS sy P = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : (trace M i k).pc = sy.PlayerCtrlRoutine) (hst : peek M sy.Player_State = 0)
    (hn : (FrameModel.readIn sy (trace M i k)).jump = false)
    (hrt : (frame M i).ram.get! P.rtI = r.ram.get! P.rtI) :
    RoomJoin.StandNext (VertModel.vsOf sy M) (VertModel.vsOf sy (frame M i)) := by
  obtain ⟨a1, a2, _, a4⟩ := RoomVert.before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, I a ∈ vKeep sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ (List.mem_append_left _ ha)
  have hs0 : peek (trace M i k) sy.Player_State = 0 := by rw [eq sy.Player_State (by simp [vKeep])]; exact hst
  have hstd : StandAt sy (trace M i k) := ⟨hs0, nopress_of hs0 hn⟩
  obtain ⟨e1, e2⟩ := (after_RS hS hfS hap hm hk).2 k hR hfk hstd hrt
  have f : ∀ a : UInt16, I a ∈ vRestS sy → peek (frame M i) a = peek M a := fun a ha => by
    rw [← eq a (vRestS_sub sy _ ha)]
    exact e1 _ ha
  refine ⟨f sy.Player_YMF_Dummy (by simp [vRestS]), f sy.VerticalForce (by simp [vRestS]), f sy.VerticalForceDown (by simp [vRestS]),
    f sy.JumpOrigin_Y_Position (by simp [vRestS]), ?_⟩
  rcases e2 with ⟨g1, g2⟩ | ⟨g1, g2, g3, g4⟩
  · have g : ∀ a : UInt16, I a ∈ vLand3 sy → peek (frame M i) a = peek M a := fun a ha => by
      rw [← eq a (vLand3_sub sy _ ha)]
      exact g1 _ ha
    exact Or.inl ⟨g sy.Player_Y_Position (by simp [vLand3]), g sy.Player_Y_Speed (by simp [vLand3]), g sy.Player_Y_MoveForce (by simp [vLand3]), g2⟩
  · refine Or.inr ⟨g1, g2, g3, ?_⟩
    show peek (frame M i) sy.Player_Y_Position = peek M sy.Player_Y_Position &&& 0xF0
    rw [← eq sy.Player_Y_Position (by simp [vKeep])]
    exact g4

end

/-! ## On the room -/

/-- **The checks on the ROM** of this file: the walk from the player's routine standing, and the bytes apart -/
structure SChecks (sy : Syms) (nm : Names) (m0 : Machine) : Prop where
  c : checkS sy nm m0 = true
  apart : apartS sy (ScreenPage.placesR sy nm m0) = true

/-- **A frame of the room that starts standing with no new press of A**, on the room: `stand_frame` with the checks of `RoomVert` and of this file -/
theorem stand_room {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk) (hS : SChecks sy nm m0) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : (trace M i k).pc = sy.PlayerCtrlRoutine) (hst : peek M sy.Player_State = 0)
    (hn : (FrameModel.readIn sy (trace M i k)).jump = false)
    (hrt : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    RoomJoin.StandNext (VertModel.vsOf sy M) (VertModel.vsOf sy (frame M i)) :=
  stand_frame (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB) (RoomVert.okV_of_check hS.c) rfl hS.apart hm hs hR hst hn hrt

end Smbrta.RoomStand
