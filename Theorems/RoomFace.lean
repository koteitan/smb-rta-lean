import Theorems.RoomVert

/-! # The facing on a frame of the room in the air, or on a jump frame

A frame of the room writes the facing direction in the player's routine only on the ground with Left or Right and no jump (`OnGroundStateSub`), while swimming, and
in the climbing routine; and in the collision routine at a flagpole or a vine. Here a walk of one whole frame of the room (the abstract machine of `RoomMap`, as
`RoomVert.walkB`) follows the facing from the player's routine on.

At the player's routine the walk splits the state by the player's state and by bit 7 of the joypad's A and of A of the frame before (`piecesF`): in the air (the state 1
or 2), or on the ground with a new press of A (the state 0, A pressed now and not on the frame before: the jump starts), the piece carries the bit `spent`; the other pieces
are marked `[2]`. A step of a piece with the bit that may write the facing drops the bit and marks the state `[1]`; such a state must end the frame out of the player's
routine (`finF`). The walk asks that the frame comes to the player's routine once.

So a frame of the room that comes to the player's routine in the air or with a new press of A on the ground, and ends in the player's routine, ends with the facing it had
there (`after_F`, `face_frame`). `RoomJoin.RoomRun.InRoom.face` is this on the real machines (`Route.Run.roomFace`).

There is no game data in this file. Page: `1-1/c-7-13-2-FaceWalk.md`.
-/

namespace Smbrta.RoomFace

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop)
open ScreenPage (Places SiteOK PlacesOK CfgS RoomCond)
open RoomVert (Ph walkV OKV I withBit canBe canBit knP hiP knIs)

/-! ## The bytes and the pieces -/

/-- the byte the walk follows: the facing -/
def fdW (sy : Syms) : List Nat := [I sy.PlayerFacingDir]

/-- **What the walk follows at the player's routine**: in the air (the state 1 or 2), or the state 0 with A pressed now and not on the frame before -/
def FaceIn (sy : Syms) (m : Machine) : Prop :=
  m.ram.get! (I sy.Player_State) = 1 ∨ m.ram.get! (I sy.Player_State) = 2 ∨
    (m.ram.get! (I sy.Player_State) = 0 ∧ m.ram.get! (I sy.SavedJoypadBits) &&& 0x80 = 0x80 ∧ m.ram.get! (I sy.PreviousA_B_Buttons) &&& 0x80 = 0)

/-- a piece in the air with the state `c`, with the bit set -/
def airP (sy : Syms) (A : AS) (c : UInt8) : List AS :=
  if canBe (A.getK (I sy.Player_State)) c then [{ A.setK (I sy.Player_State) (AB.known c) with spent := true }] else []

/-- the state 0 with the bit 7 of the joypad `a` and of A of the frame before `p` -/
def zeroS (sy : Syms) (A : AS) (a p : Bool) : AS :=
  ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 a)).setK (I sy.PreviousA_B_Buttons)
    (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 p)

/-- a piece on the ground with a new press of A, with the bit set -/
def jumpP (sy : Syms) (A : AS) : List AS :=
  if canBe (A.getK (I sy.Player_State)) 0 && canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true && canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false then
    [{ zeroS sy A true false with spent := true }]
  else []

/-- a piece on the ground with A not pressed, marked `[2]` -/
def noAP (sy : Syms) (A : AS) : List AS :=
  if canBe (A.getK (I sy.Player_State)) 0 && canBit (A.getK (I sy.SavedJoypadBits)) 0x80 false then
    [{ (A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false) with log := [2] }]
  else []

/-- a piece on the ground with A held from the frame before, marked `[2]` -/
def heldP (sy : Syms) (A : AS) : List AS :=
  if canBe (A.getK (I sy.Player_State)) 0 && canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true && canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true then
    [{ zeroS sy A true true with log := [2] }]
  else []

/-- the pieces at the player's routine: in the air (the state 1 or 2) or on the ground with a new press of A, with the bit set; and the other states, which together
cover the rest, marked `[2]`: the state 0 with A not pressed or held, the state 3, or a state with a bit above bit 1 -/
def piecesF (sy : Syms) (A : AS) : List AS :=
  airP sy A 1 ++ airP sy A 2 ++ jumpP sy A ++ noAP sy A ++ heldP sy A ++ knP sy A 3 ++ hiP sy A

/-- the step of `A` may write the facing: not the erase of a coin, which writes in the block buffers -/
def mayWriteF (sy : Syms) (E : Env) (P : Places) (A : AS) : Bool :=
  !(A.pc == P.erase && !A.nmi) && !StepWrites.keepOK E (fun i => (fdW sy).contains i) A

/-- the bit says that the frame came to the player's routine in the air or with a new press of A on the ground, and that no step has written the facing since. A step that
may write it drops the bit and marks the state `[1]`; such a state must end the frame out of the player's routine (`finF`). The other states at the player's routine are
marked `[2]`. The walk asks that the frame comes to the player's routine once. -/
def phF (sy : Syms) (E : Env) (P : Places) : Ph where
  zone := fun A =>
    if A.pc == sy.PlayerCtrlRoutine && !A.spent && A.log.isEmpty then piecesF sy A
    else if A.spent && mayWriteF sy E P A then [{ A with spent := false, log := [1] }]
    else [A]
  pre := fun A => !(A.pc == sy.PlayerCtrlRoutine && (A.spent || !A.log.isEmpty))
  ok := fun A => !A.spent || !mayWriteF sy E P A

/-- at the frame's end: a state whose facing may have been written after the player's routine ends out of the player's routine: the routine byte is known and is not the
reference's -/
def finF (P : Places) (r : Machine) (B : AS) : Bool :=
  B.log != [1] || (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI)

/-- the facing is out of the block buffers, and the state, the joypad and A of the frame before are three bytes -/
def apartF (sy : Syms) (P : Places) : Bool :=
  (fdW sy).all (fun x => decide (x < P.bufLo) || decide (P.bufLo + P.bufN ≤ x)) && I sy.Player_State != I sy.SavedJoypadBits &&
    I sy.Player_State != I sy.PreviousA_B_Buttons && I sy.SavedJoypadBits != I sy.PreviousA_B_Buttons

section
open ScreenPage (placesR envR refR aidsOf)

/-- the walk from the player's routine, on the room -/
abbrev cfgF (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phF sy (envR sy nm m0) (placesR sy nm m0)) (finF (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0)
    (RoomMap.knownT sy nm m0)

/-- the check of the walk from the player's routine -/
def checkF (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  RoomVert.walkCheckV sy (phF sy (envR sy nm m0) (placesR sy nm m0)) (finF (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0)
    (refR m0) (RoomMap.knownT sy nm m0)

end

/-! ## The pieces at the player's routine -/

section
variable {E : Env} {F : Nat × UInt8}
open RoomVert (getK_setK_self getK_setK_ne setK_ram_size setK_kn_size u8_all withBit_true_mem withBit_false_mem withBit_true_of withBit_false_of
  canBe_of canBit_of mem_known sim_bits vy_cases st_cases hi_not12 getK_one)

theorem getK2F {A : AS} {i j : Nat} {u w : AB} (hij : i ≠ j) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) (hi : i < 2048) (hj : j < 2048) :
    ((A.setK i u).setK j w).getK i = u ∧ ((A.setK i u).setK j w).getK j = w := by
  constructor
  · rw [getK_setK_ne (Ne.symm hij), getK_setK_self (by rw [hsz.1]; exact hi) (by rw [hsz.2]; exact hi)]
  · rw [getK_setK_self (by rw [setK_ram_size, hsz.1]; exact hj) (by rw [setK_kn_size, hsz.2]; exact hj)]

theorem getK3F {A : AS} {i j k : Nat} {u v w : AB} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048)
    (hi : i < 2048) (hj : j < 2048) (hk : k < 2048) :
    (((A.setK i u).setK j v).setK k w).getK i = u ∧ (((A.setK i u).setK j v).setK k w).getK j = v ∧ (((A.setK i u).setK j v).setK k w).getK k = w := by
  refine ⟨?_, ?_, ?_⟩
  · rw [getK_setK_ne (Ne.symm hik), getK_setK_ne (Ne.symm hij), getK_setK_self (by rw [hsz.1]; exact hi) (by rw [hsz.2]; exact hi)]
  · rw [getK_setK_ne (Ne.symm hjk), getK_setK_self (by rw [setK_ram_size, hsz.1]; exact hj) (by rw [setK_kn_size, hsz.2]; exact hj)]
  · rw [getK_setK_self (by rw [setK_ram_size, setK_ram_size, hsz.1]; exact hk) (by rw [setK_kn_size, setK_kn_size, hsz.2]; exact hk)]

theorem hi_not0 : ∀ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), (0 : UInt8) &&& b ≠ b := by decide

theorem b80_mem : (0x80 : UInt8) ∈ ([4, 8, 16, 32, 64, 128] : List UInt8) := by decide

/-- every piece is followed (in the air, or a new press of A on the ground) with the bit set, or not followed, marked `[2]` -/
theorem piecesF_class {sy : Syms} {A A₁ : AS} {x : Machine} (h12 : I sy.Player_State ≠ I sy.SavedJoypadBits) (h13 : I sy.Player_State ≠ I sy.PreviousA_B_Buttons)
    (h23 : I sy.SavedJoypadBits ≠ I sy.PreviousA_B_Buttons) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048)
    (h : A₁ ∈ piecesF sy A) (hs : Sim E F A₁ x) :
    (A₁.spent = true ∧ A₁.log = A.log ∧ FaceIn sy x) ∨ (A₁.spent = A.spent ∧ A₁.log = [2] ∧ ¬ FaceIn sy x) := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hal : I sy.SavedJoypadBits < 2048 := PipeTransitionAll.mask_lt _
  have hpl : I sy.PreviousA_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  have notS : ∀ c, c ≠ 0 → c ≠ 1 → c ≠ 2 → x.ram.get! (I sy.Player_State) = c → ¬ FaceIn sy x := by
    intro c h0 h1 h2 h3 hf
    rcases hf with e | e | ⟨e, _⟩ <;> rw [h3] at e
    · exact h1 e
    · exact h2 e
    · exact h0 e
  have air : ∀ c, (c = 1 ∨ c = 2) → A₁ ∈ airP sy A c → (A₁.spent = true ∧ A₁.log = A.log ∧ FaceIn sy x) := by
    intro c hc hm
    unfold airP at hm
    split at hm
    · obtain rfl := List.mem_singleton.1 hm
      have h1 : ((A.setK (I sy.Player_State) (AB.known c)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      refine ⟨rfl, rfl, ?_⟩
      rcases hc with e | e
      · exact Or.inl (by rw [mem_known h1, e])
      · exact Or.inr (Or.inl (by rw [mem_known h1, e]))
    · cases hm
  simp only [piecesF, List.mem_append] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · exact Or.inl (air 1 (Or.inl rfl) h)
  · exact Or.inl (air 2 (Or.inr rfl) h)
  · unfold jumpP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, g2, g3⟩ := getK3F (u := AB.known 0) (v := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)
        (w := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false) h12 h13 h23 hsz hsl hal hpl
      have m1 : ((zeroS sy A true false).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have m2 : ((zeroS sy A true false).getK (I sy.SavedJoypadBits)).mem (x.ram.get! (I sy.SavedJoypadBits)) := hs.ram _ hal
      have m3 : ((zeroS sy A true false).getK (I sy.PreviousA_B_Buttons)).mem (x.ram.get! (I sy.PreviousA_B_Buttons)) := hs.ram _ hpl
      unfold zeroS at m1 m2 m3
      rw [g1] at m1
      rw [g2] at m2
      rw [g3] at m3
      exact Or.inl ⟨rfl, rfl, Or.inr (Or.inr ⟨mem_known m1, withBit_true_mem b80_mem m2, withBit_false_mem m3⟩)⟩
    · cases h
  · unfold noAP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, g2⟩ := getK2F (u := AB.known 0) (w := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false) h12 hsz hsl hal
      have m1 : (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)).getK
        (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have m2 : (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)).getK
        (I sy.SavedJoypadBits)).mem (x.ram.get! (I sy.SavedJoypadBits)) := hs.ram _ hal
      rw [g1] at m1
      rw [g2] at m2
      have e1 := mem_known m1
      have e2 := withBit_false_mem m2
      refine Or.inr ⟨rfl, rfl, fun hf => ?_⟩
      rcases hf with e | e | ⟨_, e, _⟩
      · rw [e1] at e; exact absurd e (by decide)
      · rw [e1] at e; exact absurd e (by decide)
      · rw [e2] at e; exact absurd e (by decide)
    · cases h
  · unfold heldP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, _, g3⟩ := getK3F (u := AB.known 0) (v := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)
        (w := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true) h12 h13 h23 hsz hsl hal hpl
      have m1 : ((zeroS sy A true true).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have m3 : ((zeroS sy A true true).getK (I sy.PreviousA_B_Buttons)).mem (x.ram.get! (I sy.PreviousA_B_Buttons)) := hs.ram _ hpl
      unfold zeroS at m1 m3
      rw [g1] at m1
      rw [g3] at m3
      have e1 := mem_known m1
      have e3 := withBit_true_mem b80_mem m3
      refine Or.inr ⟨rfl, rfl, fun hf => ?_⟩
      rcases hf with e | e | ⟨_, _, e⟩
      · rw [e1] at e; exact absurd e (by decide)
      · rw [e1] at e; exact absurd e (by decide)
      · rw [e3] at e; exact absurd e (by decide)
    · cases h
  · unfold knP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (AB.known 3)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      exact Or.inr ⟨rfl, rfl, notS 3 (by decide) (by decide) (by decide) (mem_known h1)⟩
    · cases h
  · unfold hiP at h
    obtain ⟨b, hb, h⟩ := List.mem_flatMap.1 h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true)).getK (I sy.Player_State)).mem
        (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      have h3 := withBit_true_mem hb h1
      refine Or.inr ⟨rfl, rfl, fun hf => ?_⟩
      have hn := hi_not12 b hb
      have hn0 := hi_not0 b hb
      rcases hf with e | e | ⟨e, _⟩ <;> rw [e] at h3
      · exact hn.1 h3
      · exact hn.2 h3
      · exact hn0 h3
    · cases h

/-- the pieces cover every machine of the state -/
theorem piecesF_cover {sy : Syms} {A : AS} {x : Machine} (hr : A.rk = false) (hs : Sim E F A x) : ∃ A₁ ∈ piecesF sy A, Sim E F A₁ x := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hal : I sy.SavedJoypadBits < 2048 := PipeTransitionAll.mask_lt _
  have hpl : I sy.PreviousA_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  have ms := hs.ram _ hsl
  have ma := hs.ram _ hal
  have mp := hs.ram _ hpl
  generalize hst : x.ram.get! (I sy.Player_State) = st at ms
  generalize hsa : x.ram.get! (I sy.SavedJoypadBits) = sa at ma
  generalize hpa : x.ram.get! (I sy.PreviousA_B_Buttons) = pa at mp
  have L : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₁ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_left _ h
  have R : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₂ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_right _ h
  have airC : ∀ c, st = c → ∃ A₁ ∈ airP sy A c, Sim E F A₁ x := by
    intro c hc
    subst hc
    have c1 : canBe (A.getK (I sy.Player_State)) st = true := canBe_of ms
    unfold airP
    rw [if_pos c1]
    exact ⟨_, List.mem_singleton.2 rfl, sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst]; exact mem_known_self st)) hr true _⟩
  rcases (u8_all (P := fun t => t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ ∃ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), t &&& b = b) st_cases) st with
    e | e | e | e | ⟨b, hb, e⟩
  · have c1 : canBe (A.getK (I sy.Player_State)) 0 = true := by rw [← e]; exact canBe_of ms
    have s1 : Sim E F (A.setK (I sy.Player_State) (AB.known 0)) x := PipeEntryRule.sim_setK' hs (by rw [hst, e]; exact mem_known_self 0)
    rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) sa with ha | ha
    · have c2 : canBit (A.getK (I sy.SavedJoypadBits)) 0x80 false = true := canBit_of ma false (by rw [ha]; decide)
      have hm : ({ (A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false) with log := [2] } : AS) ∈
          noAP sy A := by
        unfold noAP
        rw [if_pos (by rw [c1, c2]; rfl)]
        exact List.mem_singleton.2 rfl
      exact ⟨_, L (L (L (R hm))), sim_bits (PipeEntryRule.sim_setK' s1 (by rw [hsa]; exact withBit_false_of ma ha)) hr _ _⟩
    · have c2 : canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true = true := canBit_of ma true (by rw [ha]; decide)
      have s2 : Sim E F ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.SavedJoypadBits) (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)) x :=
        PipeEntryRule.sim_setK' s1 (by rw [hsa]; exact withBit_true_of b80_mem ma ha)
      rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) pa with hp | hp
      · have c3 : canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false = true := canBit_of mp false (by rw [hp]; decide)
        have hm : ({ zeroS sy A true false with spent := true } : AS) ∈ jumpP sy A := by
          unfold jumpP
          rw [if_pos (by rw [c1, c2, c3]; rfl)]
          exact List.mem_singleton.2 rfl
        exact ⟨_, L (L (L (L (R hm)))), sim_bits (PipeEntryRule.sim_setK' s2 (by rw [hpa]; exact withBit_false_of mp hp)) hr true _⟩
      · have c3 : canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true = true := canBit_of mp true (by rw [hp]; decide)
        have hm : ({ zeroS sy A true true with log := [2] } : AS) ∈ heldP sy A := by
          unfold heldP
          rw [if_pos (by rw [c1, c2, c3]; rfl)]
          exact List.mem_singleton.2 rfl
        exact ⟨_, L (L (R hm)), sim_bits (PipeEntryRule.sim_setK' s2 (by rw [hpa]; exact withBit_true_of b80_mem mp hp)) hr _ _⟩
  · obtain ⟨A₁, h1, h2⟩ := airC 1 e
    exact ⟨A₁, L (L (L (L (L (L h1))))), h2⟩
  · obtain ⟨A₁, h1, h2⟩ := airC 2 e
    exact ⟨A₁, L (L (L (L (L (R h1))))), h2⟩
  · have c1 : canBe (A.getK (I sy.Player_State)) 3 = true := by rw [← e]; exact canBe_of ms
    have hm : ({ A.setK (I sy.Player_State) (AB.known 3) with log := [2] } : AS) ∈ knP sy A 3 := by
      unfold knP
      rw [if_pos c1]
      exact List.mem_singleton.2 rfl
    exact ⟨_, L (R hm), sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst, e]; exact mem_known_self 3)) hr _ _⟩
  · have c1 : canBit (A.getK (I sy.Player_State)) b true = true := canBit_of ms true (by
      rw [e]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hm : ({ A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true) with log := [2] } : AS) ∈ hiP sy A := by
      unfold hiP
      exact List.mem_flatMap.2 ⟨b, hb, by rw [if_pos c1]; exact List.mem_singleton.2 rfl⟩
    exact ⟨_, R hm, sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst]; exact withBit_true_of hb ms e)) hr _ _⟩
end

/-! ## The frame from the player's routine -/

/-- a piece with the bit, that meets `ok`, keeps the facing over its step -/
theorem keepF_step {sy : Syms} {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {y : Machine} (hO : PlacesOK E P) (hap : apartF sy P = true)
    (hs : Sim E F A y) (hh : SiteOK P y) (hok : (phF sy E P).ok A = true) (hb : A.spent = true) :
    ∀ x ∈ fdW sy, (go step y).2.ram.get! x = y.ram.get! x := by
  intro x hx
  have h1 : mayWriteF sy E P A = false := by simpa [phF, hb] using hok
  unfold mayWriteF at h1
  cases hc : (A.pc == P.erase && !A.nmi) with
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    simp only [apartF, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hap
    exact RoomVert.erase_keep hO hs hc.2 hc.1 hh (hap.1.1.1 x hx)
  | false =>
    rw [hc] at h1
    simp only [Bool.not_false, Bool.true_and, Bool.not_eq_false'] at h1
    exact StepWrites.keep_step hs h1 x (List.contains_iff_mem.2 hx)

/-- **The frame from the player's routine.** The frame comes to the player's routine at most once. If it comes there in the air or with a new press of A on the ground
(`FaceIn`), and ends in the player's routine, no step from there to its end writes the facing. The frame starts in the room's condition, and each instruction meets
`SiteOK`. -/
theorem after_F {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV (phF sy E P) E P r K C Fu)
    (hfin : C.fin = finF P r) (hap : apartF sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerCtrlRoutine) ∧
    (∀ j, (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j).frame = m.frame → FaceIn sy (trace m i j) → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       ∀ x ∈ fdW sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) := by
  obtain ⟨S, hw, hs, s1, s2, s3⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  have hsz : ∀ (A : AS) (y : Machine), Sim C.E (m.frame, 2) A y → A.ram.size = 2048 ∧ A.kn.size = 2048 := fun _ _ hs => ⟨hs.szR, hs.szK⟩
  have hap' := hap
  simp only [apartF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hap'
  obtain ⟨⟨⟨_, h12⟩, h13⟩, h23⟩ := hap'
  let Φ : Nat → Bool → List Nat → Prop := fun j b l =>
    (∀ j₀, j₀ < j → (trace m i j₀).pc = sy.PlayerCtrlRoutine → (b = true ∨ l ≠ [])) ∧
    (b = true → l = [] ∧ ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = sy.PlayerCtrlRoutine ∧ ∀ x ∈ fdW sy, (trace m i j).ram.get! x = (trace m i j₀).ram.get! x) ∧
    (l = [2] → ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = sy.PlayerCtrlRoutine ∧ ¬ FaceIn sy (trace m i j₀)) ∧
    (l = [] ∨ l = [1] ∨ l = [2])
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phF sy E P).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    show ∃ A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent && A'.log.isEmpty then piecesF sy A'
      else if A'.spent && mayWriteF sy E P A' then [{ A' with spent := false, log := [1] }] else [A']), _
    split
    · exact piecesF_cover hr hsx
    · split
      · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr false [1]⟩
      · exact ⟨A', List.mem_singleton.2 rfl, hsx⟩
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phF sy E P).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phF sy E P).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2, p3, p4⟩ hs' hf hr hA₁ hs₁ hok
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    have keep : A₁.spent = true → ∀ x ∈ fdW sy, (trace m i (j + 1)).ram.get! x = (trace m i j).ram.get! x := by
      intro hb x hx
      rw [RoomVert.trace_succ hf hs'.halted]
      have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
      exact keepF_step h.places hap hs₂ (hk j) hok hb x hx
    change A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent && A'.log.isEmpty then piecesF sy A'
      else if A'.spent && mayWriteF sy E P A' then [{ A' with spent := false, log := [1] }] else [A']) at hA₁
    split at hA₁
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
      obtain ⟨⟨hq, hsp⟩, hlg⟩ := hc
      rcases piecesF_class h12 h13 h23 (hsz A' _ hs') hA₁ hs₁ with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
      · rw [c1, c2, hlg]
        refine ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨rfl, j, by omega, by rw [hpc, hq], keep c1⟩, fun h => by simp at h, Or.inl rfl⟩
      · rw [c1, c2, hsp]
        refine ⟨fun _ _ _ => Or.inr (by simp), fun h => by simp at h, fun _ => ⟨j, by omega, by rw [hpc, hq], c3⟩, Or.inr (Or.inr rfl)⟩
    · rename_i hc
      split at hA₁
      · obtain rfl := List.mem_singleton.1 hA₁
        exact ⟨fun _ _ _ => Or.inr (by simp), fun h => by simp at h, fun h => by simp at h, Or.inr (Or.inl rfl)⟩
      · obtain rfl := List.mem_singleton.1 hA₁
        refine ⟨fun j₀ hj₀ hq₀ => ?_, fun hb => ?_, fun hl => ?_, p4⟩
        · rcases Nat.lt_or_ge j₀ j with hlt | hge
          · exact p1 j₀ hlt hq₀
          · rw [show j₀ = j by omega, hpc] at hq₀
            simp only [hq₀, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_and] at hc
            cases hsp : A₁.spent with
            | true => exact Or.inl rfl
            | false => exact Or.inr (hc hsp)
        · obtain ⟨l1, j₀, a1, a2, a3⟩ := p2 hb
          exact ⟨l1, j₀, by omega, a2, fun x hx => by rw [keep hb x hx]; exact a3 x hx⟩
        · obtain ⟨j₀, a1, a2, a3⟩ := p3 hl
          exact ⟨j₀, by omega, a2, a3⟩
  have h0 : Φ 0 S.spent S.log := by
    refine ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun hb => ?_, fun hl => ?_, Or.inl s2⟩
    · rw [s1] at hb
      cases hb
    · rw [s2] at hl
      cases hl
  obtain ⟨hall, J, hJ1, hJ2, hJ3, B, hB1, hB2, hB3⟩ := RoomVert.frame_of_walkV (Z := phF sy E P) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0 hstep
  have uniq : ∀ j j', j < j' → (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerCtrlRoutine := by
    intro j j' hlt hq hj' hq'
    obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = sy.PlayerCtrlRoutine := by rw [← hsA.pc]; exact hq'
    simp only [phF, hApc, beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hpre
    rcases q1 j hlt hq with e | e
    · rw [hpre.1] at e
      cases e
    · exact e hpre.2
  refine ⟨uniq, fun jq hq hf hin hrt x hx => ?_⟩
  have hjJ : jq < J := by
    rcases Nat.lt_or_ge jq J with h1 | h1
    · exact h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (jq - J)
      rw [show J + (jq - J) = jq by omega] at e
      rw [e, hJ1] at hf
      omega
  have hl1 : B.log ≠ [1] := by
    intro hl
    rw [hfin] at hB1
    simp only [finF, hl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB1
    obtain ⟨⟨a1, a2⟩, a3⟩ := hB1
    have e := isK_eq a2 (hB2.ram _ a1)
    rw [← hJ3, hrt] at e
    exact a3 e.symm
  obtain ⟨q1, q2, q3, q4⟩ := hB3
  have only : ∀ j₀, j₀ < J → (trace m i j₀).pc = sy.PlayerCtrlRoutine → j₀ = jq := by
    intro j₀ h1 h2
    rcases Nat.lt_trichotomy j₀ jq with e | e | e
    · exact absurd hq (uniq j₀ jq e h2 hf)
    · exact e
    · exact absurd h2 (uniq jq j₀ e hq (hJ2 j₀ h1))
  rcases q4 with e | e | e
  · rcases q1 jq hjJ hq with e2 | e2
    · obtain ⟨_, j₀, a1, a2, a3⟩ := q2 e2
      rw [only j₀ a1 a2] at a3
      rw [hJ3]
      exact a3 x hx
    · exact absurd e e2
  · exact absurd e hl1
  · obtain ⟨j₀, a1, a2, a3⟩ := q3 e
    rw [only j₀ a1 a2] at a3
    exact absurd hin a3

/-- **A frame of the room that comes to the player's routine in the air or with a new press of A on the ground, and ends in the player's routine, ends with the facing
it had there.** `after_F` on the room's walk `checkF`. -/
theorem face_frame {sy : Syms} {nm : Names} {m0 : Machine} (hcf : checkF sy nm m0 = true) (hap : apartF sy (ScreenPage.placesR sy nm m0) = true) {m : Machine}
    {input : UInt8} (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace m input j))
    (hrt : (frame m input).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI)
    {k : Nat} (hpc : (trace m input k).pc = sy.PlayerCtrlRoutine) (hf : (trace m input k).frame = m.frame) (hin : FaceIn sy (trace m input k)) :
    (frame m input).ram.get! (I sy.PlayerFacingDir) = (trace m input k).ram.get! (I sy.PlayerFacingDir) :=
  (after_F (RoomVert.okV_of_check hcf) RoomVert.cfgOfV_fin hap hm sites).2 k hpc hf hin hrt _ (List.mem_singleton.2 rfl)

end Smbrta.RoomFace
