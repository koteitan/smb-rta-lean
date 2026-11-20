import Theorems.RoomVert

/-!
# The vertical bytes of a frame in the room, falling

`RoomVert` follows a frame of the room in the air while he rises: from the scroll handler `Q` to the frame's end nothing writes the vertical bytes. Here a third walk of one
whole frame of the room (`walkC`) follows a frame in which he falls at `Q`: from `Q` to the frame's end nothing writes the vertical bytes, or he lands: the state, the height,
the vertical speed and its fraction are written, the height keeps its high four bits and gets the low four bits 0, the speed and its fraction are 0, the state is 0, and
the other vertical bytes stay (`after_QC`).

At `Q` the walk splits a falling state in the air by the state (1 or 2) and by the high four bits of the height (16 values), and marks it with these bits; so it knows the
height when it lands. The bit `spent` says that no step since `Q` has written the vertical bytes but the four of the landing (`vLand`); the list says whether these four
have been written (`[3, c]`: not written, `[1, c, 0]`: written, `c` the high bits). A step that may write another vertical byte drops the bit and marks the state `[4, 4, 4]`;
such a state must end the frame out of the room's routine.

There is no game data in this file. Page: `1-1/c-7-11-RoomFall.md`.
-/

namespace Smbrta.RoomFall

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop)
open ScreenPage (Places SiteOK PlacesOK CfgS clampS preS weaken coverS RoomCond startsR MaskOK Aids SearchS routeS)
open RoomVert (Ph walkV I vKeep withBit canBe canBit knIs knP hiP OKV)

/-! ## The bytes -/

/-- the four bytes a landing writes: the height, the vertical speed, its fraction, the state -/
def vLand (sy : Syms) : List Nat := [I sy.Player_Y_Position, I sy.Player_Y_Speed, I sy.Player_Y_MoveForce, I sy.Player_State]

/-- the other bytes that `VertModel.vsOf` reads: the height's fraction, the two forces, the jump's origin, A and B -/
def vRest (sy : Syms) : List Nat := [I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position, I sy.A_B_Buttons]

/-- **Falling in the air**: the state 1 or 2, and the vertical speed not negative -/
def Falling (sy : Syms) (m : Machine) : Prop :=
  (m.ram.get! (I sy.Player_State) = 1 ∨ m.ram.get! (I sy.Player_State) = 2) ∧ m.ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0

/-! ## The high four bits of a byte -/

/-- the byte with its high four bits known to be those of `c` -/
def withHi (x : AB) (c : UInt8) : AB := ⟨(x.v &&& ~~~0xF0) ||| (c &&& 0xF0), x.k ||| 0xF0⟩

/-- the byte can have the high four bits of `c` -/
def canHi (x : AB) (c : UInt8) : Bool := (x.v ^^^ c) &&& x.k &&& 0xF0 == 0

/-- the high four bits that the pieces take -/
def his : List UInt8 := [0x00, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0, 0xF0]

/-! ## The walk from the scroll handler, falling -/

/-- a piece falling in the air with the state `c`, with the bit set and marked `[3]` -/
def downP (sy : Syms) (A : AS) (c : UInt8) : List AS :=
  if canBe (A.getK (I sy.Player_State)) c && canBit (A.getK (I sy.Player_Y_Speed)) 0x80 false then
    [{ (A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false) with spent := true, log := [3] }]
  else []

/-- a piece in the air with the state `c` and rising, marked `[2]` -/
def riseP (sy : Syms) (A : AS) (c : UInt8) : List AS :=
  if canBe (A.getK (I sy.Player_State)) c && canBit (A.getK (I sy.Player_Y_Speed)) 0x80 true then
    [{ (A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true) with log := [2] }]
  else []

/-- the pieces at the scroll handler: falling in the air, by the state, with the bit set; and the other states, marked `[2]`: rising in the air, the state 0, the state 3,
or a state with a bit above bit 1 -/
def piecesC (sy : Syms) (A : AS) : List AS :=
  downP sy A 1 ++ downP sy A 2 ++ riseP sy A 1 ++ riseP sy A 2 ++ knP sy A 0 ++ knP sy A 3 ++ hiP sy A

/-- the pieces by the high four bits `h` of the height, marked `[5, h]` -/
def yPieces (sy : Syms) (A : AS) : List AS :=
  his.flatMap fun h =>
    if canHi (A.getK (I sy.Player_Y_Position)) h then [{ A.setK (I sy.Player_Y_Position) (withHi (A.getK (I sy.Player_Y_Position)) h) with log := [5, h.toNat] }] else []

/-- the step of `A` is an `AND` with the height (zero page or absolute): the landing takes the height's high bits so -/
def isAndY (sy : Syms) (E : Env) (A : AS) : Bool :=
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let lo := (E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16
  let hi := (E.prg.get! ((A.pc + 2) &&& E.mask).toNat).toUInt16
  (op == 0x25 && lo == sy.Player_Y_Position) || (op == 0x2D && (lo ||| (hi <<< 8)) == sy.Player_Y_Position)

/-- the step of `A` may write a byte of `L`: not the erase of a coin, which writes in the block buffers -/
def mayWrite (E : Env) (P : Places) (L : List Nat) (A : AS) : Bool :=
  !(A.pc == P.erase && !A.nmi) && !StepWrites.keepOK E (fun i => L.contains i) A

/-- the state knows that he has landed with the height `h`: the state, the vertical speed and its fraction 0, the height `h` -/
def landed (sy : Syms) (A : AS) : Bool :=
  knIs (A.getK (I sy.Player_State)) 0 && knIs (A.getK (I sy.Player_Y_Speed)) 0 && knIs (A.getK (I sy.Player_Y_MoveForce)) 0 &&
    knIs (A.getK (I sy.Player_Y_Position)) (A.log.getD 1 0).toUInt8

/-- the bit says that the frame came to the scroll handler `Q` falling in the air, and that no step since has written the bytes of `vRest`. The list says what happened to
the four bytes of the landing (`vLand`): `[3]` not written; `[5, h]` not written, the height's high bits known to be `h` (split at the landing's `AND` with the height);
`[1, h, 0]` written since; `[6]` landed: the four known (the state, the speed and its fraction 0, the height `h`), then the height forgotten, and no vertical byte written
since. A step that may write a vertical byte where the list does not allow it drops the bit and marks the state `[4, 4, 4]`; such a state must end the frame out of the
player's routine (`finC`). The other states at `Q` are marked `[2]`. The walk asks that the frame comes to `Q` once. -/
def phC (sy : Syms) (E : Env) (P : Places) : Ph where
  zone := fun A =>
    if A.pc == sy.PlayerSubs && !A.spent && A.log.isEmpty then piecesC sy A
    else if A.spent && mayWrite E P (vRest sy) A then [{ A with spent := false, log := [4, 4, 4] }]
    else if A.spent && A.log == [3] && isAndY sy E A then yPieces sy A
    else if A.spent && (A.log == [3] || A.log == [6]) && mayWrite E P (vLand sy) A then [{ A with spent := false, log := [4, 4, 4] }]
    else if A.spent && A.log.head? == some 5 && mayWrite E P (vLand sy) A then [{ A with log := [1, A.log.getD 1 0, 0] }]
    else if A.spent && A.log.head? == some 1 && landed sy A then [{ A.setK (I sy.Player_Y_Position) AB.top with log := [6] }]
    else [A]
  pre := fun A => !(A.pc == sy.PlayerSubs && (A.spent || !A.log.isEmpty))
  ok := fun A => !A.spent || (!mayWrite E P (vRest sy) A && (A.log.head? == some 1 || !mayWrite E P (vLand sy) A))

/-- at the frame's end: a state marked `[4, 4, 4]` or `[1, h, 0]` ends out of the player's routine: the routine byte is known and is not the reference's -/
def finC (P : Places) (r : Machine) (B : AS) : Bool :=
  match B.log with
  | [4, 4, 4] => decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI
  | [1, _, 0] => decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI
  | _ => true

section
open ScreenPage (placesR envR refR)

/-- the walk from the scroll handler, falling, on the room -/
abbrev cfgC (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phC sy (envR sy nm m0) (placesR sy nm m0)) (finC (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (refR m0)
    (RoomMap.knownT sy nm m0)

/-- the check of the walk from the scroll handler, falling -/
def checkC (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  RoomVert.walkCheckV sy (phC sy (envR sy nm m0) (placesR sy nm m0)) (finC (placesR sy nm m0) (refR m0)) (placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (refR m0)
    (RoomMap.knownT sy nm m0)

end

/-! ## The high bits, as bits -/

theorem withHi_of {x : AB} {y : UInt8} (hm : x.mem y) : (withHi x (y &&& 0xF0)).mem y := by
  refine mem_iff.2 fun i hi => ?_
  have a1 := mem_iff.1 hm i hi
  simp only [withHi, bt_and, bt_or, bt_not _ _ hi]
  revert a1
  generalize bt y i = p, bt x.v i = r, bt x.k i = s, bt 0xF0 i = f
  revert p r s f
  decide

theorem withHi_hi {x : AB} {y c : UInt8} (hm : (withHi x c).mem y) : y &&& 0xF0 = c &&& 0xF0 := by
  apply bt_ext
  intro i hi
  have a1 := mem_iff.1 hm i hi
  simp only [withHi, bt_and, bt_or, bt_not _ _ hi] at a1 ⊢
  revert a1
  generalize bt y i = p, bt x.v i = r, bt x.k i = s, bt 0xF0 i = f, bt c i = q
  revert p r s f q
  decide

theorem canHi_of {x : AB} {y : UInt8} (hm : x.mem y) : canHi x (y &&& 0xF0) = true := by
  simp only [canHi, beq_iff_eq]
  apply bt_ext
  intro i hi
  have a1 := mem_iff.1 hm i hi
  simp only [bt_and, bt_xor, bt_zero hi]
  revert a1
  generalize bt y i = p, bt x.v i = r, bt x.k i = s, bt 0xF0 i = f
  revert p r s f
  decide

theorem his_mem : ∀ y : UInt8, y &&& 0xF0 ∈ his :=
  RoomVert.u8_all (P := fun t => t &&& 0xF0 ∈ his) (by decide +kernel)

theorem his_hi : ∀ h ∈ his, h &&& 0xF0 = h := by decide

theorem toUInt8_toNat (c : UInt8) : c.toNat.toUInt8 = c := by simp

/-! ## The pieces -/

section
variable {E : Env} {F : Nat × UInt8}
open RoomVert (getK_setK_self getK_setK_ne setK_ram_size setK_kn_size u8_all withBit_true_mem withBit_false_mem withBit_true_of withBit_false_of
  canBe_of canBit_of mem_known sim_bits vy_cases st_cases hi_not12 getK_one)

theorem getK2 {A : AS} {i j : Nat} {u w : AB} (hij : i ≠ j) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) (hi : i < 2048) (hj : j < 2048) :
    ((A.setK i u).setK j w).getK i = u ∧ ((A.setK i u).setK j w).getK j = w := by
  constructor
  · rw [getK_setK_ne (Ne.symm hij), getK_setK_self (by rw [hsz.1]; exact hi) (by rw [hsz.2]; exact hi)]
  · rw [getK_setK_self (by rw [setK_ram_size, hsz.1]; exact hj) (by rw [setK_kn_size, hsz.2]; exact hj)]

/-- every piece at the scroll handler is falling in the air with the bit set and marked `[3]`, or not falling in the air, marked `[2]` -/
theorem piecesC_class {sy : Syms} {A A₁ : AS} {x : Machine} (hap : I sy.Player_State ≠ I sy.Player_Y_Speed) (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048)
    (h : A₁ ∈ piecesC sy A) (hs : Sim E F A₁ x) :
    (A₁.spent = true ∧ A₁.log = [3] ∧ Falling sy x) ∨ (A₁.spent = A.spent ∧ A₁.log = [2] ∧ ¬ Falling sy x) := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hvl : I sy.Player_Y_Speed < 2048 := PipeTransitionAll.mask_lt _
  have notF : ∀ c, c ≠ 1 → c ≠ 2 → x.ram.get! (I sy.Player_State) = c → ¬ Falling sy x := by
    intro c h1 h2 h3 hr
    rcases hr.1 with e | e <;> rw [h3] at e
    · exact h1 e
    · exact h2 e
  have down : ∀ c, (c = 1 ∨ c = 2) → A₁ ∈ downP sy A c → (A₁.spent = true ∧ A₁.log = [3] ∧ Falling sy x) := by
    intro c hc hm
    unfold downP at hm
    split at hm
    · obtain rfl := List.mem_singleton.1 hm
      have g := getK2 (u := AB.known c) (w := withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false) hap hsz hsl hvl
      have h1 : (((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).getK
        (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      have h2 : (((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 false)).getK
        (I sy.Player_Y_Speed)).mem (x.ram.get! (I sy.Player_Y_Speed)) := hs.ram _ hvl
      rw [g.1] at h1
      rw [g.2] at h2
      refine ⟨rfl, rfl, ?_, withBit_false_mem h2⟩
      rw [mem_known h1]
      exact hc
    · cases hm
  have rise : ∀ c, A₁ ∈ riseP sy A c → (A₁.spent = A.spent ∧ A₁.log = [2] ∧ ¬ Falling sy x) := by
    intro c hm
    unfold riseP at hm
    split at hm
    · obtain rfl := List.mem_singleton.1 hm
      have g := getK2 (u := AB.known c) (w := withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true) hap hsz hsl hvl
      have h2 : (((A.setK (I sy.Player_State) (AB.known c)).setK (I sy.Player_Y_Speed) (withBit (A.getK (I sy.Player_Y_Speed)) 0x80 true)).getK
        (I sy.Player_Y_Speed)).mem (x.ram.get! (I sy.Player_Y_Speed)) := hs.ram _ hvl
      rw [g.2] at h2
      have h3 := withBit_true_mem (by decide) h2
      refine ⟨rfl, rfl, fun hr => ?_⟩
      rw [hr.2] at h3
      exact absurd h3 (by decide)
    · cases hm
  simp only [piecesC, List.mem_append] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · exact Or.inl (down 1 (Or.inl rfl) h)
  · exact Or.inl (down 2 (Or.inr rfl) h)
  · exact Or.inr (rise 1 h)
  · exact Or.inr (rise 2 h)
  · unfold knP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (AB.known 0)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      exact Or.inr ⟨rfl, rfl, notF 0 (by decide) (by decide) (mem_known h1)⟩
    · cases h
  · unfold knP at h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (AB.known 3)).getK (I sy.Player_State)).mem (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      exact Or.inr ⟨rfl, rfl, notF 3 (by decide) (by decide) (mem_known h1)⟩
    · cases h
  · unfold hiP at h
    obtain ⟨b, hb, h⟩ := List.mem_flatMap.1 h
    split at h
    · obtain rfl := List.mem_singleton.1 h
      have h1 : ((A.setK (I sy.Player_State) (withBit (A.getK (I sy.Player_State)) b true)).getK (I sy.Player_State)).mem
        (x.ram.get! (I sy.Player_State)) := hs.ram _ hsl
      rw [getK_one hsz hsl] at h1
      have h3 := withBit_true_mem hb h1
      refine Or.inr ⟨rfl, rfl, fun hr => ?_⟩
      have hn := hi_not12 b hb
      rcases hr.1 with e | e <;> rw [e] at h3
      · exact hn.1 h3
      · exact hn.2 h3
    · cases h

/-- the pieces at the scroll handler cover every machine of the state -/
theorem piecesC_cover {sy : Syms} {A : AS} {x : Machine} (hr : A.rk = false) (hs : Sim E F A x) : ∃ A₁ ∈ piecesC sy A, Sim E F A₁ x := by
  have hsl : I sy.Player_State < 2048 := PipeTransitionAll.mask_lt _
  have hvl : I sy.Player_Y_Speed < 2048 := PipeTransitionAll.mask_lt _
  have ms := hs.ram _ hsl
  have mv := hs.ram _ hvl
  generalize hst : x.ram.get! (I sy.Player_State) = st at ms
  generalize hvy : x.ram.get! (I sy.Player_Y_Speed) = vy at mv
  have upC : ∀ c, st = c → vy &&& 0x80 = 0x80 → ∃ A₁ ∈ riseP sy A c, Sim E F A₁ x := by
    intro c hc hv
    subst hc
    have c1 : canBe (A.getK (I sy.Player_State)) st = true := canBe_of ms
    have c2 : canBit (A.getK (I sy.Player_Y_Speed)) 0x80 true = true := canBit_of mv true (by rw [hv]; decide)
    unfold riseP
    rw [if_pos (by rw [c1, c2]; rfl)]
    exact ⟨_, List.mem_singleton.2 rfl, sim_bits (PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hs (by rw [hst]; exact mem_known_self st))
        (by rw [hvy]; exact withBit_true_of (by decide) mv hv)) hr _ _⟩
  have dnC : ∀ c, st = c → vy &&& 0x80 = 0 → ∃ A₁ ∈ downP sy A c, Sim E F A₁ x := by
    intro c hc hv
    subst hc
    have c1 : canBe (A.getK (I sy.Player_State)) st = true := canBe_of ms
    have c2 : canBit (A.getK (I sy.Player_Y_Speed)) 0x80 false = true := canBit_of mv false (by rw [hv]; decide)
    unfold downP
    rw [if_pos (by rw [c1, c2]; rfl)]
    exact ⟨_, List.mem_singleton.2 rfl, sim_bits (PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hs (by rw [hst]; exact mem_known_self st))
        (by rw [hvy]; exact withBit_false_of mv hv)) hr _ _⟩
  have L : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₁ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_left _ h
  have R : ∀ {a : AS} {l₁ l₂ : List AS}, a ∈ l₂ → a ∈ l₁ ++ l₂ := fun h => List.mem_append_right _ h
  rcases (u8_all (P := fun t => t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ ∃ b ∈ ([4, 8, 16, 32, 64, 128] : List UInt8), t &&& b = b) st_cases) st with
    e | e | e | e | ⟨b, hb, e⟩
  · have c1 : canBe (A.getK (I sy.Player_State)) 0 = true := by rw [← e]; exact canBe_of ms
    have hm : ({ A.setK (I sy.Player_State) (AB.known 0) with log := [2] } : AS) ∈ knP sy A 0 := by
      unfold knP
      rw [if_pos c1]
      exact List.mem_singleton.2 rfl
    exact ⟨_, L (L (R hm)), sim_bits (PipeEntryRule.sim_setK' hs (by rw [hst, e]; exact mem_known_self 0)) hr _ _⟩
  · rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) vy with hv | hv
    · obtain ⟨A₁, h1, h2⟩ := dnC 1 e hv
      exact ⟨A₁, L (L (L (L (L (L h1))))), h2⟩
    · obtain ⟨A₁, h1, h2⟩ := upC 1 e hv
      exact ⟨A₁, L (L (L (L (R h1)))), h2⟩
  · rcases (u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) vy_cases) vy with hv | hv
    · obtain ⟨A₁, h1, h2⟩ := dnC 2 e hv
      exact ⟨A₁, L (L (L (L (L (R h1))))), h2⟩
    · obtain ⟨A₁, h1, h2⟩ := upC 2 e hv
      exact ⟨A₁, L (L (L (R h1))), h2⟩
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

/-- the pieces by the height's high bits cover every machine of the state -/
theorem yPieces_cover {sy : Syms} {A : AS} {x : Machine} (hr : A.rk = false) (hs : Sim E F A x) : ∃ A₁ ∈ yPieces sy A, Sim E F A₁ x := by
  have hyl : I sy.Player_Y_Position < 2048 := PipeTransitionAll.mask_lt _
  have my := hs.ram _ hyl
  refine ⟨_, List.mem_flatMap.2 ⟨_, his_mem (x.ram.get! (I sy.Player_Y_Position)), by rw [if_pos (canHi_of my)]; exact List.mem_singleton.2 rfl⟩,
    sim_bits (PipeEntryRule.sim_setK' hs (withHi_of my)) hr _ _⟩

/-- a piece by the height's high bits keeps the bit, and its list holds the high bits of the machine's height -/
theorem yPieces_class {sy : Syms} {A A₁ : AS} {x : Machine} (hsz : A.ram.size = 2048 ∧ A.kn.size = 2048) (h : A₁ ∈ yPieces sy A) (hs : Sim E F A₁ x) :
    A₁.spent = A.spent ∧ A₁.log = [5, (x.ram.get! (I sy.Player_Y_Position) &&& 0xF0).toNat] := by
  have hyl : I sy.Player_Y_Position < 2048 := PipeTransitionAll.mask_lt _
  obtain ⟨hh, hm, h⟩ := List.mem_flatMap.1 h
  split at h
  · obtain rfl := List.mem_singleton.1 h
    have h1 : ((A.setK (I sy.Player_Y_Position) (withHi (A.getK (I sy.Player_Y_Position)) hh)).getK (I sy.Player_Y_Position)).mem
      (x.ram.get! (I sy.Player_Y_Position)) := hs.ram _ hyl
    rw [getK_one hsz hyl] at h1
    rw [withHi_hi h1, his_hi hh hm]
    exact ⟨rfl, rfl⟩
  · cases h
end

/-! ## The frame from the scroll handler, falling -/

/-- the bytes of `vKeep` are out of the block buffers, and the state, the vertical speed and the height are three bytes -/
def apartC (sy : Syms) (P : Places) : Bool :=
  RoomVert.apartB sy P && I sy.Player_State != I sy.Player_Y_Position && I sy.Player_Y_Speed != I sy.Player_Y_Position

theorem vLand_sub (sy : Syms) : ∀ x ∈ vLand sy, x ∈ vKeep sy := by
  intro x hx
  simp only [vLand, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [vKeep]

theorem vRest_sub (sy : Syms) : ∀ x ∈ vRest sy, x ∈ vKeep sy := by
  intro x hx
  simp only [vRest, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [vKeep]

theorem vKeep_split (sy : Syms) : ∀ x ∈ vKeep sy, x ∈ vLand sy ∨ x ∈ vRest sy := by
  intro x hx
  simp only [vKeep, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vLand, vRest]

/-- a step that `mayWrite` clears keeps the bytes of `L`, if they are out of the block buffers -/
theorem keep_of_may {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {y : Machine} {L : List Nat} (hO : PlacesOK E P)
    (hL : ∀ x ∈ L, x < P.bufLo ∨ P.bufLo + P.bufN ≤ x) (hs : Sim E F A y) (hh : SiteOK P y) (hm : mayWrite E P L A = false) :
    ∀ x ∈ L, (go step y).2.ram.get! x = y.ram.get! x := by
  intro x hx
  unfold mayWrite at hm
  cases hc : (A.pc == P.erase && !A.nmi) with
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    exact RoomVert.erase_keep hO hs hc.2 hc.1 hh (hL x hx)
  | false =>
    rw [hc] at hm
    simp only [Bool.not_false, Bool.true_and, Bool.not_eq_false'] at hm
    exact StepWrites.keep_step hs hm x (List.contains_iff_mem.2 hx)

/-- **The frame from the scroll handler, falling.** The frame comes to the scroll handler at most once. If it comes there falling in the air, and ends in the player's
routine, then from there to its end no step writes the bytes of `vKeep`, or he lands: the state, the vertical speed and its fraction are 0 at the end, the height is the one
at the scroll handler with the low four bits 0, and the other bytes of `vKeep` (`vRest`) are those at the scroll handler. The frame starts in the room's condition, and each
instruction meets `SiteOK`. In the first case every instruction of the frame from the scroll handler on has the four bytes of the landing of the scroll
handler (`after_QC` drops this history). -/
theorem after_QH {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV (phC sy E P) E P r K C Fu)
    (hfin : C.fin = finC P r) (hap : apartC sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerSubs → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerSubs) ∧
    (∀ j, (trace m i j).pc = sy.PlayerSubs → (trace m i j).frame = m.frame → Falling sy (trace m i j) → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       ((∀ x ∈ vKeep sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) ∧
        ∀ j', j ≤ j' → (trace m i j').frame = m.frame → ∀ x ∈ vLand sy, (trace m i j').ram.get! x = (trace m i j).ram.get! x) ∨
       ((∀ x ∈ vRest sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) ∧ (frame m i).ram.get! (I sy.Player_State) = 0 ∧
        (frame m i).ram.get! (I sy.Player_Y_Speed) = 0 ∧ (frame m i).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
        (frame m i).ram.get! (I sy.Player_Y_Position) = (trace m i j).ram.get! (I sy.Player_Y_Position) &&& 0xF0)) := by
  obtain ⟨S, hw, hs, s1, s2, s3⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  have hsz : ∀ (A : AS) (y : Machine), Sim C.E (m.frame, 2) A y → A.ram.size = 2048 ∧ A.kn.size = 2048 := fun _ _ hs => ⟨hs.szR, hs.szK⟩
  simp only [apartC, Bool.and_eq_true, bne_iff_ne, ne_eq] at hap
  obtain ⟨⟨hapB, hsy⟩, hvy⟩ := hap
  have hap2 : I sy.Player_State ≠ I sy.Player_Y_Speed := by
    simp only [RoomVert.apartB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hapB
    exact hapB.2
  have hout : ∀ x ∈ vKeep sy, x < P.bufLo ∨ P.bufLo + P.bufN ≤ x := by
    simp only [RoomVert.apartB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hapB
    exact hapB.1
  have hyL : I sy.Player_Y_Position ∈ vLand sy := by simp [vLand]
  have hvL : I sy.Player_Y_Speed ∈ vLand sy := by simp [vLand]
  have hmL : I sy.Player_Y_MoveForce ∈ vLand sy := by simp [vLand]
  have hsL : I sy.Player_State ∈ vLand sy := by simp [vLand]
  let Q := sy.PlayerSubs
  let Vs : List Nat → Nat → Nat → Prop := fun L j j₀ => ∀ x ∈ L, (trace m i j).ram.get! x = (trace m i j₀).ram.get! x
  let Hs : List Nat → Nat → Nat → Prop := fun L j j₀ => ∀ j', j₀ ≤ j' → j' ≤ j → Vs L j' j₀
  let yQ : Nat → Nat := fun j₀ => ((trace m i j₀).ram.get! (I sy.Player_Y_Position) &&& 0xF0).toNat
  let Φ : Nat → Bool → List Nat → Prop := fun j b l =>
    (∀ j₀, j₀ < j → (trace m i j₀).pc = Q → (b = true ∨ l ≠ [])) ∧
    (b = true → ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = Q ∧ Falling sy (trace m i j₀) ∧ Vs (vRest sy) j j₀ ∧
      ((l = [3] ∧ Hs (vLand sy) j j₀) ∨ (l = [5, yQ j₀] ∧ Hs (vLand sy) j j₀) ∨ l = [1, yQ j₀, 0] ∨
       (l = [6] ∧ (trace m i j).ram.get! (I sy.Player_Y_Position) = (trace m i j₀).ram.get! (I sy.Player_Y_Position) &&& 0xF0 ∧
        (trace m i j).ram.get! (I sy.Player_Y_Speed) = 0 ∧ (trace m i j).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
        (trace m i j).ram.get! (I sy.Player_State) = 0))) ∧
    (l = [2] → ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = Q ∧ ¬ Falling sy (trace m i j₀)) ∧
    (b = false → l = [] ∨ l = [2] ∨ l = [4, 4, 4])
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phC sy E P).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    show ∃ A₁ ∈ (if A'.pc == sy.PlayerSubs && !A'.spent && A'.log.isEmpty then piecesC sy A'
      else if A'.spent && mayWrite E P (vRest sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log == [3] && isAndY sy E A' then yPieces sy A'
      else if A'.spent && (A'.log == [3] || A'.log == [6]) && mayWrite E P (vLand sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log.head? == some 5 && mayWrite E P (vLand sy) A' then [{ A' with log := [1, A'.log.getD 1 0, 0] }]
      else if A'.spent && A'.log.head? == some 1 && landed sy A' then [{ A'.setK (I sy.Player_Y_Position) AB.top with log := [6] }]
      else [A']), _
    split
    · exact piecesC_cover hr hsx
    · split
      · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr false [4, 4, 4]⟩
      · split
        · exact yPieces_cover hr hsx
        · split
          · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr false [4, 4, 4]⟩
          · split
            · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr A'.spent [1, A'.log.getD 1 0, 0]⟩
            · split
              · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits (PipeEntryRule.sim_setK' hsx (mem_top _)) hr A'.spent [6]⟩
              · exact ⟨A', List.mem_singleton.2 rfl, hsx⟩
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phC sy E P).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phC sy E P).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2, p3, p4⟩ hs' hf hr hA₁ hs₁ hok
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
    have hnext : trace m i (j + 1) = (go step (trace m i j)).2 := RoomVert.trace_succ hf hs'.halted
    have keepR : A₁.spent = true → Vs (vRest sy) (j + 1) j := by
      intro hb x hx
      have h1 : mayWrite E P (vRest sy) A₁ = false := by
        simp only [phC, hb, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hok
        exact hok.1
      rw [hnext]
      exact keep_of_may h.places (fun x hx => hout x (vRest_sub sy x hx)) hs₂ (hk j) h1 x hx
    have keepL : A₁.spent = true → A₁.log.head? ≠ some 1 → Vs (vLand sy) (j + 1) j := by
      intro hb hl x hx
      have h1 : mayWrite E P (vLand sy) A₁ = false := by
        simp only [phC, hb, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hok
        rcases hok.2 with e | e
        · exact absurd e hl
        · exact e
      rw [hnext]
      exact keep_of_may h.places (fun x hx => hout x (vLand_sub sy x hx)) hs₂ (hk j) h1 x hx
    have tr : ∀ {L : List Nat} {j₀ : Nat}, Vs L (j + 1) j → Vs L j j₀ → Vs L (j + 1) j₀ := fun h1 h2 x hx => by rw [h1 x hx]; exact h2 x hx
    have ext : ∀ {L : List Nat} {j₀ : Nat}, j₀ ≤ j → Vs L (j + 1) j → Hs L j j₀ → Hs L (j + 1) j₀ := by
      intro L j₀ hj h1 h2 j' a b
      rcases Nat.lt_or_ge j' (j + 1) with c | c
      · exact h2 j' a (by omega)
      · rw [show j' = j + 1 by omega]
        exact tr h1 (h2 j hj (Nat.le_refl _))
    have start : ∀ {L : List Nat}, Vs L (j + 1) j → Hs L (j + 1) j := by
      intro L h1 j' a b
      rcases Nat.lt_or_ge j' (j + 1) with c | c
      · rw [show j' = j by omega]
        exact fun _ _ => rfl
      · rw [show j' = j + 1 by omega]
        exact h1
    -- the bytes of the landing at `j + 1`
    have atL : A₁.spent = true → A₁.log.head? ≠ some 1 → ∀ x ∈ vLand sy, (trace m i (j + 1)).ram.get! x = (trace m i j).ram.get! x := keepL
    change A₁ ∈ (if A'.pc == sy.PlayerSubs && !A'.spent && A'.log.isEmpty then piecesC sy A'
      else if A'.spent && mayWrite E P (vRest sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log == [3] && isAndY sy E A' then yPieces sy A'
      else if A'.spent && (A'.log == [3] || A'.log == [6]) && mayWrite E P (vLand sy) A' then [{ A' with spent := false, log := [4, 4, 4] }]
      else if A'.spent && A'.log.head? == some 5 && mayWrite E P (vLand sy) A' then [{ A' with log := [1, A'.log.getD 1 0, 0] }]
      else if A'.spent && A'.log.head? == some 1 && landed sy A' then [{ A'.setK (I sy.Player_Y_Position) AB.top with log := [6] }]
      else [A']) at hA₁
    have mark : A₁.log ≠ [] → Φ (j + 1) A₁.spent A₁.log → Φ (j + 1) A₁.spent A₁.log := fun _ h => h
    -- the state marked `[4, 4, 4]`
    have out : A₁.spent = false → A₁.log = [4, 4, 4] → Φ (j + 1) A₁.spent A₁.log := by
      intro hb hl
      rw [hb, hl]
      exact ⟨fun _ _ _ => Or.inr (by simp), fun h => absurd h (by decide), fun h => by simp at h, fun _ => Or.inr (Or.inr rfl)⟩
    split at hA₁
    · -- at the scroll handler
      rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
      obtain ⟨⟨hq, hsp⟩, hlg⟩ := hc
      have hqj : (trace m i j).pc = Q := by rw [hpc, hq]
      rcases piecesC_class hap2 (hsz A' _ hs') hA₁ hs₁ with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
      · rw [c1, c2]
        refine ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨j, by omega, hqj, c3, keepR c1, Or.inl ⟨rfl, start (keepL c1 (by rw [c2]; simp))⟩⟩, fun h => by simp at h,
          fun h => absurd h (by decide)⟩
      · rw [c1, c2, hsp]
        exact ⟨fun _ _ _ => Or.inr (by simp), fun h => absurd h (by decide), fun _ => ⟨j, by omega, hqj, c3⟩, fun _ => Or.inr (Or.inl rfl)⟩
    · rename_i hc
      split at hA₁
      · obtain rfl := List.mem_singleton.1 hA₁
        exact out rfl rfl
      · split at hA₁
        · -- the split by the height's high bits
          rename_i hc3
          simp only [Bool.and_eq_true, beq_iff_eq] at hc3
          obtain ⟨⟨hb, hl⟩, _⟩ := hc3
          obtain ⟨c1, c2⟩ := yPieces_class (hsz A' _ hs') hA₁ hs₁
          obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
          rw [hl] at a5
          have hH : Hs (vLand sy) j j₀ := by
            rcases a5 with ⟨_, e⟩ | ⟨e, _⟩ | e | ⟨e, _⟩
            · exact e
            · simp at e
            · simp at e
            · simp at e
          have hL : Vs (vLand sy) j j₀ := hH j (by omega) (Nat.le_refl _)
          have hb1 : A₁.spent = true := by rw [c1, hb]
          rw [c1, c2, hb]
          refine ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨j₀, by omega, a2, a3, tr (keepR hb1) a4, Or.inr (Or.inl ⟨?_, ext (by omega) (keepL hb1 (by rw [c2]; simp)) hH⟩)⟩,
            fun h => by simp at h, fun h => absurd h (by decide)⟩
          show [5, ((trace m i j).ram.get! (I sy.Player_Y_Position) &&& 0xF0).toNat] = [5, yQ j₀]
          rw [hL _ hyL]
        · split at hA₁
          · obtain rfl := List.mem_singleton.1 hA₁
            exact out rfl rfl
          · split at hA₁
            · -- a write of the landing's bytes after the split
              rename_i hc5
              obtain rfl := List.mem_singleton.1 hA₁
              simp only [Bool.and_eq_true, beq_iff_eq] at hc5
              obtain ⟨⟨hb, hl⟩, _⟩ := hc5
              obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
              have e5 : A'.log = [5, yQ j₀] := by
                rcases a5 with ⟨e, _⟩ | ⟨e, _⟩ | e | ⟨e, _⟩ <;> rw [e] at hl <;> simp at hl
                · exact e
              refine ⟨fun _ _ _ => Or.inl hb, fun _ => ⟨j₀, by omega, a2, a3, tr (keepR hb) a4, Or.inr (Or.inr (Or.inl ?_))⟩, fun h => by simp at h,
                fun h => absurd (h.symm.trans hb) (by decide)⟩
              show [1, A'.log.getD 1 0, 0] = [1, yQ j₀, 0]
              rw [e5]
              rfl
            · split at hA₁
              · -- landed: the four bytes known, the height forgotten
                rename_i hc6
                obtain rfl := List.mem_singleton.1 hA₁
                simp only [Bool.and_eq_true, beq_iff_eq] at hc6
                obtain ⟨⟨hb, hl⟩, hland⟩ := hc6
                obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
                have e1 : A'.log = [1, yQ j₀, 0] := by
                  rcases a5 with ⟨e, _⟩ | ⟨e, _⟩ | e | ⟨e, _⟩ <;> rw [e] at hl <;> simp at hl
                  · exact e
                have hb' : ({ A'.setK (I sy.Player_Y_Position) AB.top with log := [6] } : AS).spent = true := hb
                simp only [landed, Bool.and_eq_true] at hland
                obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hland
                have v1 := RoomVert.knIs_spec k1 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                have v2 := RoomVert.knIs_spec k2 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                have v3 := RoomVert.knIs_spec k3 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                have v4 := RoomVert.knIs_spec k4 (hs'.ram _ (PipeTransitionAll.mask_lt _))
                rw [e1] at v4
                have hkL := keepL hb' (by simp)
                refine ⟨fun _ _ _ => Or.inl hb, fun _ => ⟨j₀, by omega, a2, a3, tr (keepR hb') a4, Or.inr (Or.inr (Or.inr ⟨rfl, ?_, ?_, ?_, ?_⟩))⟩,
                  fun h => by simp at h, fun h => absurd (h.symm.trans hb) (by decide)⟩
                · rw [hkL _ hyL, v4]
                  exact toUInt8_toNat _
                · rw [hkL _ hvL, v2]
                · rw [hkL _ hmL, v3]
                · rw [hkL _ hsL, v1]
              · -- the state stays
                obtain rfl := List.mem_singleton.1 hA₁
                rename_i hc4 hc5 hc6
                refine ⟨fun j₀ hj₀ hq₀ => ?_, fun hb => ?_, fun hl => ?_, p4⟩
                · rcases Nat.lt_or_ge j₀ j with hlt | hge
                  · exact p1 j₀ hlt hq₀
                  · rw [show j₀ = j by omega, hpc] at hq₀
                    have hq' : A₁.pc = sy.PlayerSubs := hq₀
                    simp only [hq', beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_and] at hc
                    cases hsp : A₁.spent with
                    | true => exact Or.inl rfl
                    | false => exact Or.inr (hc hsp)
                · obtain ⟨j₀, a1, a2, a3, a4, a5⟩ := p2 hb
                  refine ⟨j₀, by omega, a2, a3, tr (keepR hb) a4, ?_⟩
                  rcases a5 with ⟨e, f⟩ | ⟨e, f⟩ | e | ⟨e, f1, f2, f3, f4⟩
                  · exact Or.inl ⟨e, ext (by omega) (keepL hb (by rw [e]; simp)) f⟩
                  · exact Or.inr (Or.inl ⟨e, ext (by omega) (keepL hb (by rw [e]; simp)) f⟩)
                  · exact Or.inr (Or.inr (Or.inl e))
                  · have hkL := keepL hb (by rw [e]; simp)
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
  obtain ⟨hall, J, hJ1, hJ2, hJ3, B, hB1, hB2, hB3⟩ := RoomVert.frame_of_walkV (Z := phC sy E P) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0 hstep
  have uniq : ∀ j j', j < j' → (trace m i j).pc = sy.PlayerSubs → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerSubs := by
    intro j j' hlt hq hj' hq'
    obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = sy.PlayerSubs := by rw [← hsA.pc]; exact hq'
    simp only [phC, hApc, beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hpre
    rcases q1 j hlt hq with e | e
    · rw [hpre.1] at e
      cases e
    · exact e hpre.2
  refine ⟨uniq, fun jq hq hf hfall hrt => ?_⟩
  have hjJ : jq < J := by
    rcases Nat.lt_or_ge jq J with h1 | h1
    · exact h1
    · exfalso
      have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (jq - J)
      rw [show J + (jq - J) = jq by omega] at e
      rw [e, hJ1] at hf
      omega
  -- a state that must end out of the player's routine does not end so
  have notOut : ∀ l, (l = [4, 4, 4] ∨ ∃ a, l = [1, a, 0]) → B.log ≠ l := by
    intro l hl e
    rw [hfin] at hB1
    have hB1' : (decide (P.rtI < 2048) && (B.getK P.rtI).isK && ((B.getK P.rtI).v != r.ram.get! P.rtI)) = true := by
      rcases hl with rfl | ⟨a, rfl⟩ <;> simpa [finC, e] using hB1
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB1'
    obtain ⟨⟨a1, a2⟩, a3⟩ := hB1'
    have e2 := isK_eq a2 (hB2.ram _ a1)
    rw [← hJ3, hrt] at e2
    exact a3 e2.symm
  obtain ⟨q1, q2, q3, q4⟩ := hB3
  have only : ∀ j₀, j₀ < J → (trace m i j₀).pc = sy.PlayerSubs → j₀ = jq := by
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
    rw [hJ3]
    have past : ∀ j', j₀ ≤ j' → (trace m i j').frame = m.frame → j' ≤ J := by
      intro j' _ hj'
      rcases Nat.lt_or_ge J j' with h1 | h1
      · exfalso
        have e := PipeEntryRule.trace_stop (m := m) (i := i) (j := J) (by simp [hJ1]) (j' - J)
        rw [show J + (j' - J) = j' by omega] at e
        rw [e, hJ1] at hj'
        omega
      · exact h1
    rcases a5 with ⟨_, f⟩ | ⟨_, f⟩ | e | ⟨_, f1, f2, f3, f4⟩
    · exact Or.inl ⟨fun x hx => by
        rcases vKeep_split sy x hx with h1 | h1
        · exact f J (by omega) (Nat.le_refl _) x h1
        · exact a4 x h1, fun j' h1 h2 => f j' h1 (past j' h1 h2)⟩
    · exact Or.inl ⟨fun x hx => by
        rcases vKeep_split sy x hx with h1 | h1
        · exact f J (by omega) (Nat.le_refl _) x h1
        · exact a4 x h1, fun j' h1 h2 => f j' h1 (past j' h1 h2)⟩
    · exact absurd e (notOut _ (Or.inr ⟨_, rfl⟩))
    · exact Or.inr ⟨a4, f4, f2, f3, f1⟩
  | false =>
    rcases q4 hb with e | e | e
    · rcases q1 jq hjJ hq with e2 | e2
      · rw [hb] at e2
        cases e2
      · exact absurd e e2
    · obtain ⟨j₀, a1, a2, a3⟩ := q3 e
      rw [only j₀ a1 a2] at a3
      exact absurd hfall a3
    · exact absurd e (notOut _ (Or.inl rfl))

/-- **The frame from the scroll handler, falling** (`after_QH` without the history) -/
theorem after_QC {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV (phC sy E P) E P r K C Fu)
    (hfin : C.fin = finC P r) (hap : apartC sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    (∀ j j', j < j' → (trace m i j).pc = sy.PlayerSubs → (trace m i j').frame = m.frame → (trace m i j').pc ≠ sy.PlayerSubs) ∧
    (∀ j, (trace m i j).pc = sy.PlayerSubs → (trace m i j).frame = m.frame → Falling sy (trace m i j) → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       (∀ x ∈ vKeep sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) ∨
       ((∀ x ∈ vRest sy, (frame m i).ram.get! x = (trace m i j).ram.get! x) ∧ (frame m i).ram.get! (I sy.Player_State) = 0 ∧
        (frame m i).ram.get! (I sy.Player_Y_Speed) = 0 ∧ (frame m i).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
        (frame m i).ram.get! (I sy.Player_Y_Position) = (trace m i j).ram.get! (I sy.Player_Y_Position) &&& 0xF0)) := by
  obtain ⟨u, H⟩ := after_QH h hfin hap hm hk
  exact ⟨u, fun j hq hf hF hrt => (H j hq hf hF hrt).imp (fun e => e.1) id⟩

/-- **A frame falling at `Q` that writes the state 0 later in the frame ends landed**: the other vertical bytes stay, the state, the speed and its fraction are 0, and the
height is that of `Q` with the low four bits 0 -/
theorem landed_of_write {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} (h : OKV (phC sy E P) E P r K C Fu)
    (hfin : C.fin = finC P r) (hap : apartC sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j))
    {jq k : Nat} (hq : (trace m i jq).pc = sy.PlayerSubs) (hf : (trace m i jq).frame = m.frame) (hF : Falling sy (trace m i jq))
    (hrt : (frame m i).ram.get! P.rtI = r.ram.get! P.rtI) (hjk : jq ≤ k) (hfk : (trace m i k).frame = m.frame)
    (h0 : (trace m i k).ram.get! (I sy.Player_State) = 0) :
    (∀ x ∈ vRest sy, (frame m i).ram.get! x = (trace m i jq).ram.get! x) ∧ (frame m i).ram.get! (I sy.Player_State) = 0 ∧
      (frame m i).ram.get! (I sy.Player_Y_Speed) = 0 ∧ (frame m i).ram.get! (I sy.Player_Y_MoveForce) = 0 ∧
      (frame m i).ram.get! (I sy.Player_Y_Position) = (trace m i jq).ram.get! (I sy.Player_Y_Position) &&& 0xF0 := by
  rcases (after_QH h hfin hap hm hk).2 jq hq hf hF hrt with ⟨_, hist⟩ | e
  · exfalso
    have e := hist k hjk hfk (I sy.Player_State) (by simp [vLand])
    rw [h0] at e
    rcases hF.1 with e1 | e1
    · change (trace m i jq).ram.get! (I sy.Player_State) = 1 at e1
      rw [e1] at e
      exact absurd e (by decide)
    · change (trace m i jq).ram.get! (I sy.Player_State) = 2 at e1
      rw [e1] at e
      exact absurd e (by decide)
  · exact e

/-! ## One frame of the room in the air -/

/-- a machine whose vertical bytes are the landing of those of another -/
theorem vsOf_land {sy : Syms} {m m' : Machine} (hr : ∀ x ∈ vRest sy, m'.ram.get! x = m.ram.get! x) (h1 : m'.ram.get! (I sy.Player_State) = 0)
    (h2 : m'.ram.get! (I sy.Player_Y_Speed) = 0) (h3 : m'.ram.get! (I sy.Player_Y_MoveForce) = 0)
    (h4 : m'.ram.get! (I sy.Player_Y_Position) = m.ram.get! (I sy.Player_Y_Position) &&& 0xF0) :
    VertModel.vsOf sy m' = VertAir.land (VertModel.vsOf sy m) := by
  have e : ∀ a : UInt16, I a ∈ vRest sy → peek m' a = peek m a := fun a ha => hr _ ha
  unfold VertModel.vsOf VertAir.land
  rw [e sy.Player_YMF_Dummy (by simp [vRest]), e sy.VerticalForce (by simp [vRest]), e sy.VerticalForceDown (by simp [vRest]),
    e sy.JumpOrigin_Y_Position (by simp [vRest]), e sy.A_B_Buttons (by simp [vRest])]
  show Jump.VS.mk (m'.ram.get! (I sy.Player_Y_Position)) (m'.ram.get! (I sy.Player_Y_MoveForce)) (m'.ram.get! (I sy.Player_Y_Speed)) _ _ _ _
    (m'.ram.get! (I sy.Player_State)) _ = _
  rw [h1, h2, h3, h4]
  rfl

section
open VertAir (AtV vertAirOK vert_air)
open FrameModel (Rom stepN)
open RoomVert (phA before_R vsOf_eq_of vKeepA Rising)

/-- **A frame of the room in the air comes to the scroll handler with the vertical bytes of `vstep`.** The frame starts in the room's condition `M` in the air (the state
1 or 2), each instruction meets `SiteOK`, the frame comes to the player's routine at instruction `k` in the state `AtV`; at its start the jump's halt value is 1 if the
state is 1, and A of the frame before is A. Then at an instruction `j` of the frame it is at the scroll handler, with the vertical bytes of `vstep` on `vmach` with A of
the frame and the stored speed 0, and that state is 1 or 2. Each instruction of the frame that is not at the idle loop `idle` runs at least 64 dots before the frame's end. -/
theorem at_Q {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA : CfgS} {Fa : Nat}
    (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hV : vertAirOK sy m0 S = true) {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80) :
    ∃ j, (trace M i j).pc = sy.PlayerSubs ∧ (trace M i j).frame = M.frame ∧
      VertModel.vsOf sy (trace M i j) = VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧
      ((VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 1 ∨
       (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 2) := by
  obtain ⟨a1, a2, _, a4⟩ := before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR.pc
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR.pc
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, I a ∈ vKeepA sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ ha
  have hvs : VertModel.vsOf sy (trace M i k) = VertModel.vsOf sy M :=
    vsOf_eq_of (fun x hx => hkeep x (List.mem_append_left _ hx))
  have est : peek (trace M i k) sy.Player_State = peek M sy.Player_State := eq _ (by simp [vKeepA, vKeep])
  obtain ⟨kk, _, _, hpc, _, hv, hst2, hIn⟩ := vert_air hV hR (by rw [est]; exact hst)
    (by rw [est, eq sy.DiffToHaltJump (by simp [vKeepA])]; exact hd)
    (by rw [eq sy.PreviousA_B_Buttons (by simp [vKeepA]), eq sy.A_B_Buttons (by simp [vKeepA, vKeep])]; exact hp)
  rw [hvs] at hv hst2
  obtain ⟨htr, hfq⟩ := FrameModel.trace_inFrame hidle hfk hIn ht kk (Nat.le_refl kk)
  rw [← htr] at hpc hv
  exact ⟨k + kk, hpc, hfq, hv, hst2⟩

/-- **`at_Q` with the machine at the scroll handler `Good` and its stack pointer that of the player's routine** -/
theorem at_QG {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA : CfgS} {Fa : Nat}
    (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hV : vertAirOK sy m0 S = true) {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80) :
    ∃ j, k ≤ j ∧ (trace M i j).pc = sy.PlayerSubs ∧ (trace M i j).frame = M.frame ∧ FrameModel.Good (Rom.of m0) (trace M i j) ∧ (trace M i j).s = S ∧
      VertModel.vsOf sy (trace M i j) = VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧
      ((VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 1 ∨
       (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 2) := by
  obtain ⟨a1, a2, _, a4⟩ := before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR.pc
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR.pc
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, I a ∈ vKeepA sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ ha
  have hvs : VertModel.vsOf sy (trace M i k) = VertModel.vsOf sy M :=
    vsOf_eq_of (fun x hx => hkeep x (List.mem_append_left _ hx))
  have est : peek (trace M i k) sy.Player_State = peek M sy.Player_State := eq _ (by simp [vKeepA, vKeep])
  obtain ⟨kk, _, hg, hpc, hs, hv, hst2, hIn⟩ := vert_air hV hR (by rw [est]; exact hst)
    (by rw [est, eq sy.DiffToHaltJump (by simp [vKeepA])]; exact hd)
    (by rw [eq sy.PreviousA_B_Buttons (by simp [vKeepA]), eq sy.A_B_Buttons (by simp [vKeepA, vKeep])]; exact hp)
  rw [hvs] at hv hst2
  obtain ⟨htr, hfq⟩ := FrameModel.trace_inFrame hidle hfk hIn ht kk (Nat.le_refl kk)
  rw [← htr] at hpc hv hg hs
  exact ⟨k + kk, Nat.le_add_right _ _, hpc, hfq, hg, hs, hv, hst2⟩

theorem vy_cases (x : UInt8) : x &&& 0x80 = 0 ∨ x &&& 0x80 = 0x80 :=
  RoomVert.u8_all (P := fun t => t &&& 0x80 = 0 ∨ t &&& 0x80 = 0x80) RoomVert.vy_cases x

theorem falling_of {s : Jump.VS} (h : s.vy &&& 0x80 = 0) : Jump.falling s = true := by
  have a : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 → decide (UInt8.ofNat n.val < 0x80) = true := by decide +kernel
  have := a ⟨s.vy.toNat, s.vy.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  simpa [Jump.falling] using this h

/-- **Every frame of the room in the air follows `vstep`, up to the landing.** The frame starts in the room's condition `M` in the air (the state 1 or 2), each instruction
meets `SiteOK`, the frame comes to the player's routine at instruction `k` in the state `AtV`, each instruction away from the idle loop runs at least 64 dots before the
frame's end, at its start the jump's halt value is 1 if the state is 1 and A of the frame before is A, and the frame ends in the player's routine. Let `t` be `vstep` on
`vmach` of the vertical bytes at the start, with A of the frame and the stored speed 0. Then `t` is in the air, and the vertical bytes at the frame's end are `t`, or `t`
is falling and they are the landing of `t`. The checks: the three walks of the room (`walkA`, `walkB`, `walkC`), `apartB`, `apartC`, `vertAirOK`. -/
theorem jump_frame {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CB CC : CfgS}
    {Fa Fb Fc : Nat} (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hB : OKV (RoomVert.phB sy E P) E P r K CB Fb) (hfB : CB.fin = RoomVert.finB P r) (hC : OKV (phC sy E P) E P r K CC Fc) (hfC : CC.fin = finC P r)
    (hap : apartC sy P = true) (hV : vertAirOK sy m0 S = true) {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (hrt : (frame M i).ram.get! P.rtI = r.ram.get! P.rtI) :
    ((VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 1 ∨
     (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 2) ∧
    (VertModel.vsOf sy (frame M i) = VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∨
     (Jump.falling (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0) = true ∧
      VertModel.vsOf sy (frame M i) = VertAir.land (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0))) := by
  obtain ⟨j, hq, hf, hv, hst2⟩ := at_Q hpz hA hfA hV hidle hm hk hR ht hst hd hp
  generalize VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 = t at hv hst2 ⊢
  have hapB : RoomVert.apartB sy P = true := by
    simp only [apartC, Bool.and_eq_true] at hap
    exact hap.1.1
  have e1 : (VertModel.vsOf sy (trace M i j)).st = (trace M i j).ram.get! (I sy.Player_State) := rfl
  have e2 : (VertModel.vsOf sy (trace M i j)).vy = (trace M i j).ram.get! (I sy.Player_Y_Speed) := rfl
  refine ⟨hst2, ?_⟩
  rcases vy_cases t.vy with h0 | h80
  · -- falling at the scroll handler
    have hF : Falling sy (trace M i j) := by
      unfold Falling
      rw [← e1, ← e2, hv]
      exact ⟨hst2, h0⟩
    rcases (after_QC hC hfC hap hm hk).2 j hq hf hF hrt with e | ⟨f1, f2, f3, f4, f5⟩
    · exact Or.inl (by rw [vsOf_eq_of e, hv])
    · exact Or.inr ⟨falling_of h0, by rw [vsOf_land f1 f2 f3 f4 f5, hv]⟩
  · -- rising at the scroll handler
    have hRi : Rising sy (trace M i j) := by
      unfold Rising
      rw [← e1, ← e2, hv]
      exact ⟨hst2, h80⟩
    exact Or.inl (by rw [vsOf_eq_of ((RoomVert.after_Q hB hfB hapB hm hk).2 j hq hf hRi hrt), hv])

/-- **A frame of the room in the air that writes the state 0 after the scroll handler lands.** As `jump_frame`: the frame comes to the scroll handler `j` with the
vertical bytes of `vstep`, the machine there `Good` with the stack of the player's routine. If `vstep` does not rise and some instruction of the frame from `j` on has the
state 0, the vertical bytes at the frame's end are the landing of `vstep` (`landed_of_write`). Which frames write the state 0 is not said here. -/
theorem land_frame {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CC : CfgS}
    {Fa Fc : Nat} (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hC : OKV (phC sy E P) E P r K CC Fc) (hfC : CC.fin = finC P r)
    (hap : apartC sy P = true) (hV : vertAirOK sy m0 S = true) {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (hrt : (frame M i).ram.get! P.rtI = r.ram.get! P.rtI) :
    ∃ j, k ≤ j ∧ (trace M i j).pc = sy.PlayerSubs ∧ (trace M i j).frame = M.frame ∧ FrameModel.Good (Rom.of m0) (trace M i j) ∧ (trace M i j).s = S ∧
      VertModel.vsOf sy (trace M i j) = VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧
      ((VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&& 0x80 = 0 →
        (∃ k', j ≤ k' ∧ (trace M i k').frame = M.frame ∧ (trace M i k').ram.get! (I sy.Player_State) = 0) →
        VertModel.vsOf sy (frame M i) = VertAir.land (VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0)) := by
  obtain ⟨j, hkj, hq, hf, hg, hs, hv, hst2⟩ := at_QG hpz hA hfA hV hidle hm hk hR ht hst hd hp
  refine ⟨j, hkj, hq, hf, hg, hs, hv, fun h0 ⟨k', hk1, hk2, hk3⟩ => ?_⟩
  generalize VertModel.vstepV sy m0 S (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 = t at hv hst2 h0 ⊢
  have e1 : (VertModel.vsOf sy (trace M i j)).st = (trace M i j).ram.get! (I sy.Player_State) := rfl
  have e2 : (VertModel.vsOf sy (trace M i j)).vy = (trace M i j).ram.get! (I sy.Player_Y_Speed) := rfl
  have hF : Falling sy (trace M i j) := by
    unfold Falling
    rw [← e1, ← e2, hv]
    exact ⟨hst2, h0⟩
  obtain ⟨f1, f2, f3, f4, f5⟩ := landed_of_write hC hfC hap hm hk hq hf hF hrt hk1 hk2 hk3
  rw [vsOf_land f1 f2 f3 f4 f5, hv]

end

/-! ## On the room -/

/-- **The checks on the ROM** of this file: the walk from the scroll handler falling, the bytes apart, and every state of the jumps from the floor (`VertAir.bridgeAll`) -/
structure FChecks (sy : Syms) (nm : Names) (m0 : Machine) (h : Nat) : Prop where
  c : checkC sy nm m0 = true
  apart : apartC sy (ScreenPage.placesR sy nm m0) = true
  bridge : VertAir.bridgeAll sy m0 (FrameModel.ctrlStack sy m0) (Jump.groundY sy) h = true

/-- **Every frame of the room in the air follows `vstep`, up to the landing**, on the room: `jump_frame` with the checks of `RoomVert` and of this file -/
theorem jump_room {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk) (hF : FChecks sy nm m0 h) {idle : UInt16}
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : VertAir.AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i k))
    (htm : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (hrt : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    ((VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 1 ∨
     (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 2) ∧
    (VertModel.vsOf sy (frame M i) = VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∨
     (Jump.falling (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0) = true ∧
      VertModel.vsOf sy (frame M i) =
        VertAir.land (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (VertModel.vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0))) :=
  jump_frame (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB) (RoomVert.okV_of_check hV.b) rfl
    (RoomVert.okV_of_check hF.c) rfl hF.apart hV.air hidle hm hs hR htm hst hd hp hrt

end Smbrta.RoomFall
