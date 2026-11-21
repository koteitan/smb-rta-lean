import Theorems.AreaKeep
import Theorems.EntryHeightBig
import Theorems.RoomPair

/-!
# The player's size through the room's frames

`Route.Run.y₂` proves the height at the side pipe's entry from the frame that enters the side pipe, when that frame starts with a small player (the reference's size,
`EntryHeight`) or a big one (the size byte 0, `EntryHeightBig`). Until round 21 the field `height₂` asked that the frame starts with one of these two sizes, or that
the height at the entry is the reference entry's.

Only three places of the game store to the size byte by its address (read from the disassembly): the setup of a new game and the continue store the small value,
and the change of size stores the old value with its low bit flipped. In the room there is no power-up and no enemy. Here the room's frames keep the byte: the walk
of `RoomPause` with the byte in a table of one state (`AreaKeep.roomCheckA`, the walk that keeps the level's number), once with the reference's value and once with
0 (`roomCheckS`). Each frame of the room starts in the room's condition (`ScreenPage.Room`) and meets `SiteOK` on each instruction; so a frame that starts with the
byte at one of the two values ends with it at the same value (`RoomPause.pause_step`), and every frame of the room starts with it (`byte_all`, `size_run`).

So the size at the start of the frame that enters the side pipe is the reference's or 0 when it is so at the room's first control (`Route.Run.size₂`). At the room's
first control it is so (`Route.Run.size₁`): since round 22 the vertical pipe's entry and the exit's list know bits 1 to 7 of the size (`PipeChangeEnd.entryMasks`,
`exitMasks`), so every state of the rows of the first change knows them (`rowsCheckS`, `size_of_rows`). The change of size flips only bit 0, so the frames from
control to the vertical pipe keep these bits (`EntryKeep`), and the condition at the press of Start on the title knows them.

There is no game data in this file. Page: `1-1/d-2-5-4-4-SizeKeep.md`.
-/

namespace Smbrta.SizeKeep

open TaintRun
open PipeTransition (frame)
open PipeTransitionAll (Names)
open PipeEntryRule (trace)
open ScreenPage (SiteOK placesR envR refR knownOf Room)
open StepWrites (SState SIn)

/-! ## The byte and the checks -/

/-- the player's size, as a RAM index -/
abbrev sizeI (sy : Syms) : Nat := EntryHeight.sizeI sy

/-- the reference's size (small) -/
abbrev refSize (sy : Syms) (m0 : Machine) : UInt8 := (refR m0).ram.get! (sizeI sy)

/-- **The check of the room's frames with the size byte at the value `v`**: the walk of `AreaKeep` with this byte -/
def roomCheckS (sy : Syms) (nm : Names) (m0 : Machine) (v : UInt8) : Bool := AreaKeep.roomCheckA sy nm m0 (sizeI sy) v

/-- what the walk with the byte at the value `v` gives -/
abbrev KeepOK (sy : Syms) (nmS : Names) (m0 : Machine) (i : Nat) (v : UInt8) : Prop :=
  RoomPause.PauseOK (envR sy nmS m0) (placesR sy nmS m0) (refR m0) (knownOf nmS) (AreaKeep.regA sy m0 nmS i v) (AreaKeep.cfgA sy nmS m0 i v) ScreenPage.fuelS

/-! ## Every frame of the room -/

section
variable {sy : Syms} {m0 : Machine} {nmS : Names} {i : Nat} {v : UInt8}

/-- **The byte at every frame of the room.** The room's first control `c` is in the room's condition and has the byte with the value `v`. Each frame from `c` before
`e` meets `SiteOK` and starts in the player's routine. Then every machine from `c` to `e` has the byte with the value `v`. -/
theorem byte_all (hF : KeepOK sy nmS m0 i v) {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat}
    (h0 : Room sy nmS m0 (seq c)) (hv : (seq c).ram.get! i = v)
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, c ≤ n → n ≤ e → (seq n).ram.get! i = v := by
  have hc0 : RoomPause.InCls (AreaKeep.regA sy m0 nmS i v) (seq c) := by
    refine ⟨[(i, AB.known v)], List.mem_singleton_self _, fun p hp => ?_⟩
    rw [List.mem_singleton] at hp
    subst hp
    exact SidePause.mem_known_of_eq hv
  have key : ∀ d, c + d ≤ e → RoomPause.InCls (AreaKeep.regA sy m0 nmS i v) (seq (c + d)) ∧
      (Room sy nmS m0 (seq (c + d)) ∨ (seq (c + d)).ram.get! (placesR sy nmS m0).rtI ≠ (refR m0).ram.get! (placesR sy nmS m0).rtI) := by
    intro d
    induction d with
    | zero => exact fun _ => ⟨hc0, Or.inl h0⟩
    | succ d ih =>
      intro hd
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hm : Room sy nmS m0 (seq (c + d)) := by
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd (hr (c + d) (by omega) (by omega)) h2
      have e1 : c + (d + 1) = c + d + 1 := rfl
      rw [e1, next]
      obtain ⟨g1, g2⟩ := RoomPause.pause_step hF hm (hs (c + d) (by omega) (by omega)) h1
      refine ⟨g1, ?_⟩
      rcases g2 with g2 | g2
      · exact Or.inl g2
      · exact Or.inr g2.1
  intro n h1 h2
  obtain ⟨d, rfl⟩ : ∃ d, n = c + d := ⟨n - c, by omega⟩
  obtain ⟨t, ht, hm⟩ := (key d h2).1
  have ht' : t = [(i, AB.known v)] := List.mem_singleton.1 ht
  subst ht'
  exact SidePause.eq_of_mem_known (hm _ (List.mem_singleton_self _))

end

/-! ## At the room's first control: from the rows of the first change

Since round 22 the vertical pipe's entry knows bits 1 to 7 of the size byte (`PipeChangeEnd.entryMasks`, with the reference's value 0 there), so the walk of the
pipe's frames knows them, and the exit's list has them too (`PipeChangeEnd.exitMasks`). Then the rows of the first change know them (`rowsCheckS`). The press of Start
on the title and the frames from control give them at the vertical pipe's entry (`EntryKeep`: the size is one of the kept bytes, under its mask; the change of size
flips only bit 0). -/

section
open PipeChangeEnd (Data timeCtx timeRows InRowsT)

/-- a state knows bits 1 to 7 of the size byte to be 0 -/
def rowS (sy : Syms) (S : AS) : Bool :=
  (S.getK (sizeI sy)).k &&& 0xFE == 0xFE && (S.getK (sizeI sy)).v &&& 0xFE == 0

/-- **The check on the ROM**: every state of the rows of the time of the first change knows bits 1 to 7 of the size byte to be 0; the reference's size has them 0
and is not 0 -/
def rowsCheckS (sy : Syms) (nm : Names) (d : Data) (e m0 : Machine) : Bool :=
  (timeRows (timeCtx sy nm d e) d e).all (fun w => w.R.all (rowS sy)) && refSize sy m0 &&& 0xFE == 0 && refSize sy m0 != 0

theorem low_one : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0xFE = 0 → UInt8.ofNat n.val = 0 ∨ UInt8.ofNat n.val = 1 := by decide +kernel

/-- a byte with bits 1 to 7 clear is 0 or 1 -/
theorem zero_or_one {x : UInt8} (h : x &&& 0xFE = 0) : x = 0 ∨ x = 1 :=
  RoomVert.u8_all (P := fun t => t &&& 0xFE = 0 → t = 0 ∨ t = 1) low_one x h

variable {sy : Syms}

theorem size_of_state {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowS sy S = true) :
    m.ram.get! (sizeI sy) &&& 0xFE = 0 := by
  simp only [rowS, Bool.and_eq_true, beq_iff_eq] at hr
  have h := bit_eq (hs.ram (sizeI sy) (PipeTransitionAll.mask_lt _)) hr.1
  rw [h, hr.2]

/-- **The size at the room's first control is the reference's or 0**: a machine with control in the rows of the time of the first change -/
theorem size_of_rows {nm : Names} {d : Data} {e m0 : Machine} (hc : rowsCheckS sy nm d e m0 = true) {m : Machine} (h : InRowsT sy nm d e m)
    (hm : controllable sy m = true) : m.ram.get! (sizeI sy) = refSize sy m0 ∨ m.ram.get! (sizeI sy) = 0 := by
  simp only [rowsCheckS, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have hl : m.ram.get! (sizeI sy) &&& 0xFE = 0 :=
    RoomPair.of_invL (sy := sy) (Q := rowS sy) (R := fun m => m.ram.get! (sizeI sy) &&& 0xFE = 0) (fun hs hq _ => size_of_state hs hq) h1 h hm
  rcases zero_or_one hl with e1 | e1
  · exact Or.inr e1
  · rcases zero_or_one h2 with e2 | e2
    · exact absurd e2 h3
    · exact Or.inl (e1.trans e2.symm)

end

/-! ## For the route -/

/-- **What the checks on the ROM give for the height and the size**: those of `EntryHeightBig`, the room's walk with the size byte at the reference's value and
at 0, and the rows of the first change with bits 1 to 7 of the size -/
structure Facts (sy : Syms) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nmS : Names) (m0 : Machine) (V : List (Machine × List Nat)) : Prop
    extends toBig : EntryHeightBig.Facts sy nm₁ d₁ nmS m0 V where
  keepR : KeepOK sy nmS m0 (sizeI sy) (refSize sy m0)
  keep0 : KeepOK sy nmS m0 (sizeI sy) 0
  rowsS : rowsCheckS sy nm₁ d₁ (PipeTransition.entry m0) m0 = true

theorem factsOf {sy : Syms} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nmS : Names} {m0 : Machine} {V : List (Machine × List Nat)}
    (h : EntryHeightBig.Facts sy nm₁ d₁ nmS m0 V) (h1 : roomCheckS sy nmS m0 (refSize sy m0) = true) (h2 : roomCheckS sy nmS m0 0 = true)
    (h3 : rowsCheckS sy nm₁ d₁ (PipeTransition.entry m0) m0 = true) : Facts sy nm₁ d₁ nmS m0 V :=
  { h with keepR := AreaKeep.roomOK_of_check h1, keep0 := AreaKeep.roomOK_of_check h2, rowsS := h3 }

section
variable {sy : Syms} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nmS : Names} {m0 : Machine} {V : List (Machine × List Nat)}

/-- **The size at every frame of the room is the reference's or 0** when it is so at the room's first control `c`, under the conditions of `byte_all` -/
theorem size_run (hF : Facts sy nm₁ d₁ nmS m0 V) {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {c e : Nat}
    (h0 : Room sy nmS m0 (seq c)) (hv : (seq c).ram.get! (sizeI sy) = refSize sy m0 ∨ (seq c).ram.get! (sizeI sy) = 0)
    (hs : ∀ n, c ≤ n → n < e → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (hr : ∀ n, c ≤ n → n < e → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, c ≤ n → n ≤ e → (seq n).ram.get! (sizeI sy) = refSize sy m0 ∨ (seq n).ram.get! (sizeI sy) = 0 := by
  intro n h1 h2
  rcases hv with hv | hv
  · exact Or.inl (byte_all hF.keepR next h0 hv hs hr n h1 h2)
  · exact Or.inr (byte_all hF.keep0 next h0 hv hs hr n h1 h2)

end

end Smbrta.SizeKeep
