import Theorems.RoomFace

/-! # `RunningSpeed` on a frame of the room

A frame of the room writes `RunningSpeed` only in `GetPlayerAnimSpeed`, which the player's routine calls on the ground (`OnGroundStateSub`) and while swimming. There it
stores the stored speed `Player_XSpeedAbsolute` when that is at least the running threshold `RunSpeedMin` (the byte that the routine compares with), and 0 otherwise or
nothing. The stored speed is written only in `ImposeFriction`, after that call. Here a walk of one whole frame of the room (the abstract machine of `RoomMap`, as
`RoomFace`) follows `RunningSpeed` from the player's routine on.

At the player's routine the walk splits the state (`piecesR`): `RunningSpeed` 0 and in the air (the state 1 or 2), or `RunningSpeed` 0, the state 0 and the stored speed
in one of the blocks of bits below the threshold (`lowB`), or `RunningSpeed` 0, the state 0 and a new press of A (the jump starts before the movement routine, which then
does not call `GetPlayerAnimSpeed`), carry the bit `spent`; the other pieces are marked `[2]`: `RunningSpeed` with a bit set, the state 0 with the stored speed in a block
at or above the threshold (`highB`) and A not pressed or held, the state 3, or a state with a bit above bit 1. On a block below the threshold the routine's compare is
decided (the block's largest byte is below the threshold), so the store of the stored speed is not reached. A state with the bit must end the frame with `RunningSpeed`
known to be 0, or out of the player's routine (`finRS`). Each piece with the bit carries its block in its list, so that the search does not join two blocks.

So a frame of the room that comes to the player's routine with `RunningSpeed` 0, in the air, or on the ground with the stored speed below the threshold or a new press of
A (`RunIn`), and ends in the player's routine, ends with `RunningSpeed` 0 (`after_RS`, `run_frame`). `RoomJoin.RoomRun.InRoom.run` is this on the real machines (`Route.Run.roomRun`).

There is no game data in this file. Page: `1-1/c-7-4-2-RunWalk.md`.
-/

namespace Smbrta.RoomRunSpeed

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop)
open ScreenPage (Places SiteOK PlacesOK CfgS RoomCond)
open RoomVert (Ph walkV OKV I canBe knP hiP knIs)

/-! ## The blocks of the stored speed -/

/-- the eight bits of a byte -/
def bits8 : List UInt8 := [1, 2, 4, 8, 16, 32, 64, 128]

/-- the blocks of the bytes below `R`: for each bit `b` set in `R`, the bytes whose bits above `b` are those of `R`, with the bit `b` clear -/
def lowB (R : UInt8) : List AB :=
  bits8.filterMap fun c => if R &&& c != 0 then some ⟨R &&& ~~~(c ||| (c - 1)), ~~~(c - 1)⟩ else none

/-- the blocks of the bytes at or above `R`: `R` itself, and for each bit `b` clear in `R`, the bytes whose bits above `b` are those of `R`, with the bit `b` set -/
def highB (R : UInt8) : List AB :=
  AB.known R :: bits8.filterMap fun c => if R &&& c == 0 then some ⟨(R &&& ~~~(c ||| (c - 1))) ||| c, ~~~(c - 1)⟩ else none

/-- the blocks below `R` hold only bytes below `R`, those of `highB` only bytes at or above `R`, and each byte is in one of them -/
def blocksCheck (R : UInt8) : Bool :=
  (List.range 256).all fun n =>
    ((lowB R).all fun b => !(n.toUInt8 &&& b.k == b.v &&& b.k) || decide (n.toUInt8 < R)) &&
    ((highB R).all fun b => !(n.toUInt8 &&& b.k == b.v &&& b.k) || decide (R ≤ n.toUInt8)) &&
    ((lowB R).any (fun b => n.toUInt8 &&& b.k == b.v &&& b.k) || (highB R).any fun b => n.toUInt8 &&& b.k == b.v &&& b.k)

theorem blocks_of {R : UInt8} (h : blocksCheck R = true) (x : UInt8) :
    ((∀ b ∈ lowB R, b.mem x → x < R) ∧ (∀ b ∈ highB R, b.mem x → R ≤ x)) ∧ ((∃ b ∈ lowB R, b.mem x) ∨ ∃ b ∈ highB R, b.mem x) := by
  unfold blocksCheck at h
  have h1 := List.all_eq_true.1 h x.toNat (List.mem_range.2 x.toNat_lt)
  simp only [UInt8.ofNat_toNat, Nat.toUInt8_eq, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq, decide_eq_true_eq, List.any_eq_true] at h1
  obtain ⟨⟨h2, h3⟩, h4⟩ := h1
  refine ⟨⟨fun b hb hm => ?_, fun b hb hm => ?_⟩, h4⟩
  · rcases h2 b hb with e | e
    · exact absurd hm e
    · exact e
  · rcases h3 b hb with e | e
    · exact absurd hm e
    · exact e

/-! ## The pieces -/

/-- **What the walk follows at the player's routine**: `RunningSpeed` 0, and the state 1 or 2, or the state 0 with the stored speed below `R` or a new press of A
(bit 7 of the joypad set, bit 7 of A of the frame before clear) -/
def RunIn (sy : Syms) (R : UInt8) (m : Machine) : Prop :=
  m.ram.get! (I sy.RunningSpeed) = 0 ∧
    (m.ram.get! (I sy.Player_State) = 1 ∨ m.ram.get! (I sy.Player_State) = 2 ∨
      (m.ram.get! (I sy.Player_State) = 0 ∧ (m.ram.get! (I sy.Player_XSpeedAbsolute) < R ∨
        (m.ram.get! (I sy.SavedJoypadBits) &&& 0x80 = 0x80 ∧ m.ram.get! (I sy.PreviousA_B_Buttons) &&& 0x80 = 0))))

/-- a piece in the air with the state `c` and `RunningSpeed` 0, with the bit set -/
def airR (sy : Syms) (A : AS) (c : UInt8) : List AS :=
  if canBe (A.getK (I sy.Player_State)) c && canBe (A.getK (I sy.RunningSpeed)) 0 then
    [{ (A.setK (I sy.Player_State) (AB.known c)).setK (I sy.RunningSpeed) (AB.known 0) with spent := true, log := [3, c.toNat] }]
  else []

/-- the pieces on the ground with `RunningSpeed` 0 and the stored speed in a block below `R`, with the bit set and the block in the list -/
def lowR (sy : Syms) (R : UInt8) (A : AS) : List AS :=
  (lowB R).flatMap fun b =>
    if canBe (A.getK (I sy.Player_State)) 0 && canBe (A.getK (I sy.RunningSpeed)) 0 then
      [{ ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b with
          spent := true, log := [3, b.k.toNat] }]
    else []

/-- the piece on the ground with `RunningSpeed` 0 and a new press of A, with the bit set -/
def jumpR (sy : Syms) (A : AS) : List AS :=
  if canBe (A.getK (I sy.Player_State)) 0 && canBe (A.getK (I sy.RunningSpeed)) 0 && RoomVert.canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true &&
      RoomVert.canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false then
    [{ (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.SavedJoypadBits)
        (RoomVert.withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons) (RoomVert.withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false) with
        spent := true, log := [3, 3] }]
  else []

/-- the pieces on the ground with the stored speed in a block at or above `R` and A not pressed, marked `[2]` -/
def highR (sy : Syms) (R : UInt8) (A : AS) : List AS :=
  (highB R).flatMap fun b =>
    if canBe (A.getK (I sy.Player_State)) 0 && RoomVert.canBit (A.getK (I sy.SavedJoypadBits)) 0x80 false then
      [{ ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).setK (I sy.SavedJoypadBits)
          (RoomVert.withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false) with log := [2] }]
    else []

/-- the pieces on the ground with the stored speed in a block at or above `R` and A held from the frame before, marked `[2]` -/
def heldR (sy : Syms) (R : UInt8) (A : AS) : List AS :=
  (highB R).flatMap fun b =>
    if canBe (A.getK (I sy.Player_State)) 0 && RoomVert.canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true &&
        RoomVert.canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true then
      [{ (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).setK (I sy.SavedJoypadBits)
          (RoomVert.withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons)
          (RoomVert.withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true) with log := [2] }]
    else []

/-- the pieces with a bit of `RunningSpeed` set, marked `[2]` -/
def rsHiR (sy : Syms) (A : AS) : List AS :=
  bits8.map fun c => { A.setK (I sy.RunningSpeed) ⟨c, c⟩ with log := [2] }

/-- the pieces at the player's routine: `RunIn` with the bit set, and the other states, which together cover the rest, marked `[2]` -/
def piecesR (sy : Syms) (R : UInt8) (A : AS) : List AS :=
  airR sy A 1 ++ airR sy A 2 ++ lowR sy R A ++ jumpR sy A ++ highR sy R A ++ heldR sy R A ++ rsHiR sy A ++ knP sy A 3 ++ hiP sy A

/-- the bit says that the frame came to the player's routine in the state `RunIn`. The walk asks that the frame comes to the player's routine once; the abstract machine
follows the value of `RunningSpeed` from there -/
def phR (sy : Syms) (R : UInt8) : Ph where
  zone := fun A => if A.pc == sy.PlayerCtrlRoutine && !A.spent && A.log.isEmpty then piecesR sy R A else [A]
  pre := fun A => !(A.pc == sy.PlayerCtrlRoutine && (A.spent || !A.log.isEmpty))
  ok := fun _ => true

/-- at the frame's end: a state with the bit knows `RunningSpeed` 0, or ends out of the player's routine: the routine byte is known and is not the reference's -/
def finRS (sy : Syms) (P : Places) (r : Machine) (B : AS) : Bool :=
  !B.spent || knIs (B.getK (I sy.RunningSpeed)) 0 || (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI)

/-- the five bytes of `RunIn` are apart, and the blocks of `RunSpeedMin` meet `blocksCheck` -/
def apartR (sy : Syms) : Bool :=
  decide [I sy.Player_State, I sy.RunningSpeed, I sy.Player_XSpeedAbsolute, I sy.SavedJoypadBits, I sy.PreviousA_B_Buttons].Nodup &&
    blocksCheck sy.RunSpeedMin.toUInt8

section
open ScreenPage (placesR envR refR aidsOf)

/-- the walk from the player's routine, on the room -/
abbrev cfgR (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phR sy sy.RunSpeedMin.toUInt8) (finRS sy (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0)
    (RoomMap.knownT sy nm m0)

/-- the check of the walk from the player's routine -/
def checkR (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  RoomVert.walkCheckV sy (phR sy sy.RunSpeedMin.toUInt8) (finRS sy (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0)
    (refR m0) (RoomMap.knownT sy nm m0)

/-- the search of the walk, for the program: the number of failures, the first failing state's address, the states at the frame's end, those of them with the bit,
and those that `finRS` refuses with the address of the first -/
def searchR (sy : Syms) (nm : Names) (m0 : Machine) : Nat × Option UInt16 × Nat × Nat × Nat × Option UInt16 :=
  let X := RoomVert.searchOfV sy (phR sy sy.RunSpeedMin.toUInt8) (placesR sy nm m0) (aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)
  let bad := X.ends.filter fun B => !finRS sy (placesR sy nm m0) (refR m0) B
  (X.fails, X.firstFail.map (·.pc), X.ends.size, (X.ends.filter (·.spent)).size, bad.size, bad[0]?.map (·.pc))

end

/-! ## The pieces at the player's routine -/

section
variable {E : Env} {F : Nat × UInt8}
open RoomVert (getK_setK_self getK_setK_ne setK_ram_size setK_kn_size u8_all canBe_of mem_known sim_bits st_cases vy_cases hi_not12 getK_one
  withBit withBit_true_mem withBit_false_mem withBit_true_of withBit_false_of canBit canBit_of)
open RoomFace (getK2F getK3F hi_not0 b80_mem)

/-- the five bytes apart, and the blocks -/
structure Apart (sy : Syms) : Prop where
  sr : I sy.Player_State ≠ I sy.RunningSpeed
  sx : I sy.Player_State ≠ I sy.Player_XSpeedAbsolute
  ss : I sy.Player_State ≠ I sy.SavedJoypadBits
  sp : I sy.Player_State ≠ I sy.PreviousA_B_Buttons
  rx : I sy.RunningSpeed ≠ I sy.Player_XSpeedAbsolute
  rs : I sy.RunningSpeed ≠ I sy.SavedJoypadBits
  rp : I sy.RunningSpeed ≠ I sy.PreviousA_B_Buttons
  xs : I sy.Player_XSpeedAbsolute ≠ I sy.SavedJoypadBits
  xp : I sy.Player_XSpeedAbsolute ≠ I sy.PreviousA_B_Buttons
  sa : I sy.SavedJoypadBits ≠ I sy.PreviousA_B_Buttons
  blocks : blocksCheck sy.RunSpeedMin.toUInt8 = true

theorem apart_of {sy : Syms} (h : apartR sy = true) : Apart sy := by
  simp only [apartR, Bool.and_eq_true, decide_eq_true_eq, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at h
  obtain ⟨⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩, hb⟩ := h
  exact ⟨h12, h13, h14, h15, h23, h24, h25, h34, h35, h45.1, hb⟩

theorem getK4 {A : AS} {i j k l : Nat} {u v w x : AB} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) (hi : i < 2048) (hj : j < 2048) (hk : k < 2048) (hl : l < 2048) :
    ((((A.setK i u).setK j v).setK k w).setK l x).getK i = u ∧ ((((A.setK i u).setK j v).setK k w).setK l x).getK j = v ∧
      ((((A.setK i u).setK j v).setK k w).setK l x).getK k = w ∧ ((((A.setK i u).setK j v).setK k w).setK l x).getK l = x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getK_setK_ne (Ne.symm hil), getK_setK_ne (Ne.symm hik), getK_setK_ne (Ne.symm hij), getK_setK_self (by rw [hsz.1]; exact hi) (by rw [hsz.2]; exact hi)]
  · rw [getK_setK_ne (Ne.symm hjl), getK_setK_ne (Ne.symm hjk), getK_setK_self (by rw [setK_ram_size, hsz.1]; exact hj) (by rw [setK_kn_size, hsz.2]; exact hj)]
  · rw [getK_setK_ne (Ne.symm hkl), getK_setK_self (by rw [setK_ram_size, setK_ram_size, hsz.1]; exact hk)
      (by rw [setK_kn_size, setK_kn_size, hsz.2]; exact hk)]
  · rw [getK_setK_self (by rw [setK_ram_size, setK_ram_size, setK_ram_size, hsz.1]; exact hl) (by rw [setK_kn_size, setK_kn_size, setK_kn_size, hsz.2]; exact hl)]

theorem bits8_cover : ∀ n : Fin 256, UInt8.ofNat n.val = 0 ∨ ∃ c ∈ bits8, UInt8.ofNat n.val &&& c = c := by decide +kernel

theorem bits8_self : ∀ c ∈ bits8, c &&& c = c := by decide

theorem bits8_ne0 : ∀ c ∈ bits8, (0 : UInt8) &&& c ≠ c := by decide

theorem mem_bitAB {c x : UInt8} (hc : c ∈ bits8) (h : x &&& c = c) : (⟨c, c⟩ : AB).mem x := by
  show x &&& c = c &&& c
  rw [bits8_self c hc]
  exact h

theorem ne0_of_bitAB {c x : UInt8} (hc : c ∈ bits8) (h : (⟨c, c⟩ : AB).mem x) : x ≠ 0 := by
  intro e
  have h' : x &&& c = c &&& c := h
  rw [e, bits8_self c hc] at h'
  exact bits8_ne0 c hc h'

theorem b80_ne : (0 : UInt8) ≠ 0x80 := by decide

/-- every piece is followed (`RunIn`) with the bit set and a list that is not `[2]`, or not followed, marked `[2]` -/
theorem piecesR_class {sy : Syms} {A A₁ : AS} {x : Machine} (hd : Apart sy)
    (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) (h : A₁ ∈ piecesR sy sy.RunSpeedMin.toUInt8 A) (hs : Sim E F A₁ x) :
    (A₁.spent = true ∧ A₁.log ≠ [2] ∧ RunIn sy sy.RunSpeedMin.toUInt8 x) ∨ (A₁.spent = A.spent ∧ A₁.log = [2] ∧ ¬ RunIn sy sy.RunSpeedMin.toUInt8 x) := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hrl : I sy.RunningSpeed < 2048 := PipeTransitionAll.mask_lt _
  have hxl : I sy.Player_XSpeedAbsolute < 2048 := PipeTransitionAll.mask_lt _
  have hal : I sy.SavedJoypadBits < 2048 := PipeTransitionAll.mask_lt _
  have hpl : I sy.PreviousA_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  have hR := hd.blocks
  have notS : ∀ c, c ≠ 0 → c ≠ 1 → c ≠ 2 → x.ram.get! (I sy.Player_State) = c → ¬ RunIn sy sy.RunSpeedMin.toUInt8 x := by
    intro c h0 h1 h2 h3 ⟨_, hf⟩
    rcases hf with e | e | ⟨e, _⟩ <;> rw [h3] at e
    · exact h1 e
    · exact h2 e
    · exact h0 e
  have air : ∀ c, (c = 1 ∨ c = 2) → A₁ ∈ airR sy A c → (A₁.spent = true ∧ A₁.log ≠ [2] ∧ RunIn sy sy.RunSpeedMin.toUInt8 x) := by
    intro c hc hm
    unfold airR at hm
    split at hm
    · obtain rfl := List.mem_singleton.1 hm
      obtain ⟨g1, g2⟩ := getK2F (u := AB.known c) (w := AB.known 0) hd.sr hsz hsl hrl
      have m1 : (((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.RunningSpeed) (AB.known 0)).getK (I sy.Player_State)).mem
        (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have m2 : (((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.RunningSpeed) (AB.known 0)).getK (I sy.RunningSpeed)).mem
        (x.ram.get! (I sy.RunningSpeed)) := hs.ram _ hrl
      rw [g1] at m1
      rw [g2] at m2
      refine ⟨rfl, by simp, mem_known m2, ?_⟩
      rcases hc with e | e
      · exact Or.inl (by rw [mem_known m1, e])
      · exact Or.inr (Or.inl (by rw [mem_known m1, e]))
    · cases hm
  simp only [piecesR, List.mem_append] at h
  rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
  · exact Or.inl (air 1 (Or.inl rfl) h)
  · exact Or.inl (air 2 (Or.inr rfl) h)
  · unfold lowR at h
    obtain ⟨b, hb, h⟩ := List.mem_flatMap.1 h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, g2, g3⟩ := getK3F (u := AB.known 0) (v := AB.known 0) (w := b) hd.sr hd.sx hd.rx hsz hsl hrl hxl
      have m1 : ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).getK
        (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have m2 : ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).getK
        (I sy.RunningSpeed)).mem (x.ram.get! (I sy.RunningSpeed)) := hs.ram _ hrl
      have m3 : ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).getK
        (I sy.Player_XSpeedAbsolute)).mem (x.ram.get! (I sy.Player_XSpeedAbsolute)) := hs.ram _ hxl
      rw [g1] at m1
      rw [g2] at m2
      rw [g3] at m3
      exact Or.inl ⟨rfl, by simp, mem_known m2, Or.inr (Or.inr ⟨mem_known m1, Or.inl ((blocks_of hR _).1.1 b hb m3)⟩)⟩
    · cases h
  · unfold jumpR at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, g2, g3, g4⟩ := getK4 (A := A) (u := AB.known 0) (v := AB.known 0) (w := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)
        (x := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false) hd.sr hd.ss hd.sp hd.rs hd.rp hd.sa hsz hsl hrl hal hpl
      have m1 := hs.ram _ hsl
      have m2 := hs.ram _ hrl
      have m3 := hs.ram _ hal
      have m4 := hs.ram _ hpl
      simp only [AS.getK] at m1 m2 m3 m4 g1 g2 g3 g4
      rw [g1] at m1
      rw [g2] at m2
      rw [g3] at m3
      rw [g4] at m4
      exact Or.inl ⟨rfl, by simp, mem_known m2, Or.inr (Or.inr ⟨mem_known m1, Or.inr ⟨withBit_true_mem b80_mem m3, withBit_false_mem m4⟩⟩)⟩
    · cases h
  · unfold highR at h
    obtain ⟨b, hb, h⟩ := List.mem_flatMap.1 h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, g2, g3⟩ := getK3F (A := A) (u := AB.known 0) (v := b) (w := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false) hd.sx hd.ss hd.xs hsz hsl
        hxl hal
      have m1 := hs.ram _ hsl
      have m2 := hs.ram _ hxl
      have m3 := hs.ram _ hal
      simp only [AS.getK] at m1 m2 m3 g1 g2 g3
      rw [g1] at m1
      rw [g2] at m2
      rw [g3] at m3
      have e1 := mem_known m1
      have e2 := (blocks_of hR _).1.2 b hb m2
      have e3 := withBit_false_mem m3
      refine Or.inr ⟨rfl, rfl, fun ⟨_, hf⟩ => ?_⟩
      rcases hf with e | e | ⟨_, e | ⟨e, _⟩⟩
      · rw [e1] at e; exact absurd e (by decide)
      · rw [e1] at e; exact absurd e (by decide)
      · exact absurd e2 (UInt8.not_le.2 e)
      · rw [e3] at e; exact b80_ne e
    · cases h
  · unfold heldR at h
    obtain ⟨b, hb, h⟩ := List.mem_flatMap.1 h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      obtain ⟨g1, g2, g3, g4⟩ := getK4 (A := A) (u := AB.known 0) (v := b) (w := withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)
        (x := withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true) hd.sx hd.ss hd.sp hd.xs hd.xp hd.sa hsz hsl hxl hal hpl
      have m1 := hs.ram _ hsl
      have m2 := hs.ram _ hxl
      have m4 := hs.ram _ hpl
      simp only [AS.getK] at m1 m2 m4 g1 g2 g4
      rw [g1] at m1
      rw [g2] at m2
      rw [g4] at m4
      have e1 := mem_known m1
      have e2 := (blocks_of hR _).1.2 b hb m2
      have e4 := withBit_true_mem b80_mem m4
      refine Or.inr ⟨rfl, rfl, fun ⟨_, hf⟩ => ?_⟩
      rcases hf with e | e | ⟨_, e | ⟨_, e⟩⟩
      · rw [e1] at e; exact absurd e (by decide)
      · rw [e1] at e; exact absurd e (by decide)
      · exact absurd e2 (UInt8.not_le.2 e)
      · rw [e4] at e; exact absurd e (by decide)
    · cases h
  · unfold rsHiR at h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    have m2 : ((A.setK (I sy.RunningSpeed) ⟨c, c⟩).getK (I sy.RunningSpeed)).mem (x.ram.get! (I sy.RunningSpeed)) := hs.ram _ hrl
    rw [getK_one hsz hrl] at m2
    exact Or.inr ⟨rfl, rfl, fun ⟨e, _⟩ => ne0_of_bitAB hc m2 e⟩
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
      refine Or.inr ⟨rfl, rfl, fun ⟨_, hf⟩ => ?_⟩
      have hn := hi_not12 b hb
      have hn0 := hi_not0 b hb
      rcases hf with e | e | ⟨e, _⟩ <;> rw [e] at h3
      · exact hn.1 h3
      · exact hn.2 h3
      · exact hn0 h3
    · cases h

/-- the pieces cover every machine of the state -/
theorem piecesR_cover {sy : Syms} {A : AS} {x : Machine} (hd : Apart sy) (hr : A.rk = false) (hs : Sim E F A x) :
    ∃ A₁ ∈ piecesR sy sy.RunSpeedMin.toUInt8 A, Sim E F A₁ x := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hrl : I sy.RunningSpeed < 2048 := PipeTransitionAll.mask_lt _
  have hal : I sy.SavedJoypadBits < 2048 := PipeTransitionAll.mask_lt _
  have hpl : I sy.PreviousA_B_Buttons < 2048 := PipeTransitionAll.mask_lt _
  have hR := hd.blocks
  have ms := hs.ram _ hsl
  have mr := hs.ram _ hrl
  have ma := hs.ram _ hal
  have mp := hs.ram _ hpl
  generalize hst : x.ram.get! (I sy.Player_State) = st at ms
  generalize hrs : x.ram.get! (I sy.RunningSpeed) = rs at mr
  generalize hsa : x.ram.get! (I sy.SavedJoypadBits) = sa at ma
  generalize hpa : x.ram.get! (I sy.PreviousA_B_Buttons) = pa at mp
  have L : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₁ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_left _ h
  have R' : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₂ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_right _ h
  rcases (u8_all (P := fun t => t = 0 ∨ ∃ c ∈ bits8, t &&& c = c) bits8_cover) rs with e0 | ⟨c, hc, ec⟩
  · subst e0
    have c2 : canBe (A.getK (I sy.RunningSpeed)) 0 = true := canBe_of mr
    have airC : ∀ c, st = c → ∃ A₁ ∈ airR sy A c, Sim E F A₁ x := by
      intro c hcs
      subst hcs
      have c1 : canBe (A.getK (I sy.Player_State)) st = true := canBe_of ms
      have s1 : Sim E F (A.setK (I sy.Player_State) (AB.known st)) x := PipeEntryRule.sim_setK' hs (by rw [hst]; exact mem_known_self st)
      have s2 : Sim E F ((A.setK (I sy.Player_State) (AB.known st)).setK (I sy.RunningSpeed) (AB.known 0)) x :=
        PipeEntryRule.sim_setK' s1 (by rw [hrs]; exact mem_known_self 0)
      unfold airR
      rw [if_pos (by rw [c1, c2]; rfl)]
      exact ⟨_, List.mem_singleton.2 rfl, sim_bits s2 hr true _⟩
    rcases (u8_all (P := fun t => t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ ∃ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), t &&& b = b) st_cases) st with
      e | e | e | e | ⟨b, hb, e⟩
    · subst e
      have c1 : canBe (A.getK (I sy.Player_State)) 0 = true := canBe_of ms
      have s1 : Sim E F (A.setK (I sy.Player_State) (AB.known 0)) x := PipeEntryRule.sim_setK' hs (by rw [hst]; exact mem_known_self 0)
      rcases (blocks_of hR (x.ram.get! (I sy.Player_XSpeedAbsolute))).2 with ⟨b, hb, hm⟩ | ⟨b, hb, hm⟩
      · have s2 : Sim E F ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)) x :=
          PipeEntryRule.sim_setK' s1 (by rw [hrs]; exact mem_known_self 0)
        have s3 : Sim E F (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b) x :=
          PipeEntryRule.sim_setK' s2 hm
        have hmem : ({ ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b with
            spent := true, log := [3, b.k.toNat] } : AS) ∈ lowR sy sy.RunSpeedMin.toUInt8 A := by
          unfold lowR
          exact List.mem_flatMap.2 ⟨b, hb, by rw [if_pos (by rw [c1, c2]; rfl)]; exact List.mem_singleton.2 rfl⟩
        exact ⟨_, L (L (L (L (L (L (R' hmem)))))), sim_bits s3 hr true _⟩
      · have s3 : Sim E F ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b) x := PipeEntryRule.sim_setK' s1 hm
        rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) sa with ha | ha
        · have c3 : canBit (A.getK (I sy.SavedJoypadBits)) 0x80 false = true := canBit_of ma false (by rw [ha]; decide)
          have s4 : Sim E F (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).setK (I sy.SavedJoypadBits)
              (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false)) x := PipeEntryRule.sim_setK' s3 (by rw [hsa]; exact withBit_false_of ma ha)
          have hmem : ({ ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).setK (I sy.SavedJoypadBits)
              (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 false) with log := [2] } : AS) ∈ highR sy sy.RunSpeedMin.toUInt8 A := by
            unfold highR
            exact List.mem_flatMap.2 ⟨b, hb, by rw [if_pos (by rw [c1, c3]; rfl)]; exact List.mem_singleton.2 rfl⟩
          exact ⟨_, L (L (L (L (R' hmem)))), sim_bits s4 hr _ _⟩
        · have c3 : canBit (A.getK (I sy.SavedJoypadBits)) 0x80 true = true := canBit_of ma true (by rw [ha]; decide)
          rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) pa with hp | hp
          · have c4 : canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false = true := canBit_of mp false (by rw [hp]; decide)
            have s2 : Sim E F ((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)) x :=
              PipeEntryRule.sim_setK' s1 (by rw [hrs]; exact mem_known_self 0)
            have s5 : Sim E F (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.SavedJoypadBits)
                (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)) x := PipeEntryRule.sim_setK' s2 (by rw [hsa]; exact withBit_true_of b80_mem ma ha)
            have s6 : Sim E F ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.SavedJoypadBits)
                (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false)) x :=
              PipeEntryRule.sim_setK' s5 (by rw [hpa]; exact withBit_false_of mp hp)
            have hmem : ({ (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.RunningSpeed) (AB.known 0)).setK (I sy.SavedJoypadBits)
                (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 false) with
                spent := true, log := [3, 3] } : AS) ∈ jumpR sy A := by
              unfold jumpR
              rw [if_pos (by rw [c1, c2, c3, c4]; rfl)]
              exact List.mem_singleton.2 rfl
            exact ⟨_, L (L (L (L (L (R' hmem))))), sim_bits s6 hr true _⟩
          · have c4 : canBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true = true := canBit_of mp true (by rw [hp]; decide)
            have s5 : Sim E F (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).setK (I sy.SavedJoypadBits)
                (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)) x := PipeEntryRule.sim_setK' s3 (by rw [hsa]; exact withBit_true_of b80_mem ma ha)
            have s6 : Sim E F ((((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).setK (I sy.SavedJoypadBits)
                (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true)) x :=
              PipeEntryRule.sim_setK' s5 (by rw [hpa]; exact withBit_true_of b80_mem mp hp)
            have hmem : ({ (((A.setK (I sy.Player_State) (AB.known 0)).setK (I sy.Player_XSpeedAbsolute) b).setK (I sy.SavedJoypadBits)
                (withBit (A.getK (I sy.SavedJoypadBits)) 0x80 true)).setK (I sy.PreviousA_B_Buttons) (withBit (A.getK (I sy.PreviousA_B_Buttons)) 0x80 true) with
                log := [2] } : AS) ∈ heldR sy sy.RunSpeedMin.toUInt8 A := by
              unfold heldR
              exact List.mem_flatMap.2 ⟨b, hb, by rw [if_pos (by rw [c1, c3, c4]; rfl)]; exact List.mem_singleton.2 rfl⟩
            exact ⟨_, L (L (L (R' hmem))), sim_bits s6 hr _ _⟩
    · obtain ⟨A₁, h1, h2⟩ := airC 1 e
      exact ⟨A₁, L (L (L (L (L (L (L (L h1))))))), h2⟩
    · obtain ⟨A₁, h1, h2⟩ := airC 2 e
      exact ⟨A₁, L (L (L (L (L (L (L (R' h1))))))), h2⟩
    · have c1 : canBe (A.getK (I sy.Player_State)) 3 = true := by rw [← e]; exact canBe_of ms
      have hm : ({ A.setK (I sy.Player_State) (AB.known 3) with log := [2] } : AS) ∈ knP sy A 3 := by
        unfold knP
        rw [if_pos c1]
        exact List.mem_singleton.2 rfl
      exact ⟨_, L (R' hm), sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst, e]; exact mem_known_self 3)) hr _ _⟩
    · have c1 : canBit (A.getK (I sy.Player_State)) b true = true := canBit_of ms true (by
        rw [e]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      have hm : ({ A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true) with log := [2] } : AS) ∈ hiP sy A := by
        unfold hiP
        exact List.mem_flatMap.2 ⟨b, hb, by rw [if_pos c1]; exact List.mem_singleton.2 rfl⟩
      exact ⟨_, R' hm, sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst]; exact withBit_true_of hb ms e)) hr _ _⟩
  · have hmem : ({ A.setK (I sy.RunningSpeed) ⟨c, c⟩ with log := [2] } : AS) ∈ rsHiR sy A := by
      unfold rsHiR
      exact List.mem_map.2 ⟨c, hc, rfl⟩
    exact ⟨_, L (L (R' hmem)), sim_bits (PipeEntryRule.sim_setK' hs (by rw [hrs]; exact mem_bitAB hc ec)) hr _ _⟩
end

/-! ## The frame from the player's routine -/

/-- **The frame from the player's routine.** The frame comes to the player's routine at most once. If it comes there in the state `RunIn`, and ends in the player's
routine, it ends with `RunningSpeed` 0. The frame starts in the room's condition, and each instruction meets `SiteOK`. -/
theorem after_RS {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat}
    (h : OKV (phR sy sy.RunSpeedMin.toUInt8) E P r K C Fu) (hfin : C.fin = finRS sy P r) (hd : Apart sy) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerCtrlRoutine) ∧
    (∀ j, (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j).frame = m.frame → RunIn sy sy.RunSpeedMin.toUInt8 (trace m i j) → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       (frame m i).ram.get! (I sy.RunningSpeed) = 0) := by
  obtain ⟨S, hw, hs, s1, s2, _⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  have hsz : ∀ (A : AS) (y : Machine), Sim C.E (m.frame, 2) A y → A.ram.size = 2048 ∧ A.kn.size = 2048 := fun _ _ hs => ⟨hs.szR, hs.szK⟩
  let Φ : Nat → Bool → List Nat → Prop := fun j b l =>
    (∀ j₀, j₀ < j → (trace m i j₀).pc = sy.PlayerCtrlRoutine → (b = true ∨ l = [2])) ∧
    (l = [2] → ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = sy.PlayerCtrlRoutine ∧ ¬ RunIn sy sy.RunSpeedMin.toUInt8 (trace m i j₀)) ∧
    (b = false → l = [] ∨ l = [2])
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phR sy sy.RunSpeedMin.toUInt8).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    show ∃ A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent && A'.log.isEmpty then piecesR sy sy.RunSpeedMin.toUInt8 A' else [A']), _
    split
    · exact piecesR_cover hd hr hsx
    · exact ⟨A', List.mem_singleton.2 rfl, hsx⟩
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phR sy sy.RunSpeedMin.toUInt8).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phR sy sy.RunSpeedMin.toUInt8).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2, p3⟩ hs' _ _ hA₁ hs₁ _
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    change A₁ ∈ (if A'.pc == sy.PlayerCtrlRoutine && !A'.spent && A'.log.isEmpty then piecesR sy sy.RunSpeedMin.toUInt8 A' else [A']) at hA₁
    split at hA₁
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
      obtain ⟨⟨hq, hsp⟩, _⟩ := hc
      rcases piecesR_class hd (hsz A' _ hs') hA₁ hs₁ with ⟨c1, c2, _⟩ | ⟨c1, c2, c3⟩
      · rw [c1]
        exact ⟨fun _ _ _ => Or.inl rfl, fun hl => absurd hl c2, fun h => by simp at h⟩
      · rw [c1, c2, hsp]
        exact ⟨fun _ _ _ => Or.inr rfl, fun _ => ⟨j, by omega, by rw [hpc, hq], c3⟩, fun _ => Or.inr rfl⟩
    · rename_i hc
      obtain rfl := List.mem_singleton.1 hA₁
      refine ⟨fun j₀ hj₀ hq₀ => ?_, fun hl => ?_, p3⟩
      · rcases Nat.lt_or_ge j₀ j with hlt | hge
        · exact p1 j₀ hlt hq₀
        · rw [show j₀ = j by omega, hpc] at hq₀
          simp only [hq₀, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_and] at hc
          cases hsp : A₁.spent with
          | true => exact Or.inl rfl
          | false =>
            rcases p3 hsp with e | e
            · exact absurd e (hc hsp)
            · exact Or.inr e
      · obtain ⟨j₀, a1, a2, a3⟩ := p2 hl
        exact ⟨j₀, by omega, a2, a3⟩
  have h0 : Φ 0 S.spent S.log := by
    refine ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun hl => ?_, fun _ => Or.inl s2⟩
    rw [s2] at hl
    cases hl
  obtain ⟨hall, J, hJ1, hJ2, hJ3, B, hB1, hB2, hB3⟩ := RoomVert.frame_of_walkV (Z := phR sy sy.RunSpeedMin.toUInt8) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0 hstep
  have uniq : ∀ j j', j < j' → (trace m i j).pc = sy.PlayerCtrlRoutine → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerCtrlRoutine := by
    intro j j' hlt hq hj' hq'
    obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = sy.PlayerCtrlRoutine := by rw [← hsA.pc]; exact hq'
    simp only [phR, hApc, beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hpre
    rcases q1 j hlt hq with e | e
    · rw [hpre.1] at e
      cases e
    · rw [hpre.2] at e
      cases e
  refine ⟨uniq, fun jq hq hf hin hrt => ?_⟩
  have hjJ : jq < J := by
    rcases Nat.lt_or_ge jq J with h1 | h1
    · exact h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (jq - J)
      rw [show J + (jq - J) = jq by omega] at e
      rw [e, hJ1] at hf
      omega
  obtain ⟨q1, q2, _⟩ := hB3
  have only : ∀ j₀, j₀ < J → (trace m i j₀).pc = sy.PlayerCtrlRoutine → j₀ = jq := by
    intro j₀ h1 h2
    rcases Nat.lt_trichotomy j₀ jq with e | e | e
    · exact absurd hq (uniq j₀ jq e h2 hf)
    · exact e
    · exact absurd h2 (uniq jq j₀ e hq (hJ2 j₀ h1))
  rcases q1 jq hjJ hq with e | e
  · rw [hfin] at hB1
    simp only [finRS, e, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB1
    rcases hB1 with h0 | ⟨⟨a1, a2⟩, a3⟩
    · rw [hJ3]
      exact RoomVert.knIs_spec h0 (hB2.ram _ (PipeTransitionAll.mask_lt _))
    · exfalso
      have e2 := isK_eq a2 (hB2.ram _ a1)
      rw [← hJ3, hrt] at e2
      exact a3 e2.symm
  · obtain ⟨j₀, a1, a2, a3⟩ := q2 e
    rw [only j₀ a1 a2] at a3
    exact absurd hin a3

/-- **A frame of the room that comes to the player's routine with `RunningSpeed` 0, in the air, or on the ground with the stored speed below `RunSpeedMin` or a new
press of A, and ends in the player's routine, ends with `RunningSpeed` 0.** `after_RS` on the room's walk `checkR`. -/
theorem run_frame {sy : Syms} {nm : Names} {m0 : Machine} (hcr : checkR sy nm m0 = true) (hap : apartR sy = true) {m : Machine}
    {input : UInt8} (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace m input j))
    (hrt : (frame m input).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI)
    {k : Nat} (hpc : (trace m input k).pc = sy.PlayerCtrlRoutine) (hf : (trace m input k).frame = m.frame)
    (hin : RunIn sy sy.RunSpeedMin.toUInt8 (trace m input k)) :
    (frame m input).ram.get! (I sy.RunningSpeed) = 0 := by
  exact (after_RS (RoomVert.okV_of_check hcr) RoomVert.cfgOfV_fin (apart_of hap) hm sites).2 k hpc hf hin hrt

end Smbrta.RoomRunSpeed
