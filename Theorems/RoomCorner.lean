import Theorems.RoomWall

/-! # The block's left side in the room, from the end of the move

On a frame of the room the player's collision routine runs after the end of the move `Q` (the first `PlayerSubs` of the frame). Near the block's left side, with his
horizontal coordinate from `cornerX` (his right side check reaches the block's left column) to `cornerX + 4`, two walks follow it from `Q` back to `PlayerSubs`, to the
instruction after its call of the collision routine (`RoomWall.retBG`).

* The first walk (`check1C`) starts at a cut that samples the bytes of `RoomLand.keys` and the player's state, knows the sign bit of the vertical speed, and takes the head,
  foot and side cells of the three adder offsets from the reference map (`RoomWall.cellsW`). The horizontal speed is not sampled. Two kinds of `Q` are walked (`clsC`): he
  stands at the floor's height (the state 0, not moving up), or he moves up in the state 1 with his height from `ylo` to the floor's. The private proof takes `ylo` one
  row below the corner's height (`Jump.cornerY`): higher, with the size not known, a cell holds a coin and the walk fails. The walk stops at `retBG`, where it asks the
  height above the corner's, or at `ImpedePlayerMove`, called by the side check with the side byte 1 (the block on his right), where it asks the coordinate and the page
  of `Q` and the speed not written.
* The second walk (`check2C`) starts there, for every coordinate and every speed, and goes back to `retBG`. A speed from 0 to 127 becomes 0 and the coordinate one less;
  a negative speed is kept, and the coordinate too (`endC`).

So at `retBG` the height is above the corner's, or the page is 0 and he was pushed back one pixel with the speed 0, or he moves left as at `Q` (`corner_at`). `RoomWall`'s walk
of the room's whole frame from `retBG` (`RoomWall.checkW`, `RoomWall.after_G`) carries this to the frame's end (`corner_frame`).

`RoomJoin.cornerX`, `RoomJoin.xsC` and `RoomJoin.CornerEnd` are defined in `RoomJoin`, which states the field `InRoom.corner` with them. There is no game data in this
file. Page: `1-1/c-7-5-17-RoomCorner.md`. -/
namespace Smbrta.RoomCorner
open FrameModel
open RoomWall (retBG retImp sideI knIs cellsW keysW cutW variantW variantW_s floorY cutW_eq coords_sub_keys cells_of_familyW refCheckW)
open RoomJoin (cornerX xsC CornerEnd)

/-- the heights of a move up: from `ylo` to the floor's -/
def ysUp (sy : Syms) (ylo : Nat) : List UInt8 :=
  (List.range (Jump.groundY sy + 1 - ylo)).map fun k => (ylo + k).toUInt8

/-- the two kinds of `Q`: (the state, the sign bit of the vertical speed, the heights). Standing at the floor's height, not moving up; moving up in the state 1 with the
height from `ylo` to the floor's -/
def clsC (sy : Syms) (ylo : Nat) : List (UInt8 × UInt8 × List UInt8) := [(0, 0, [floorY sy]), (1, 0x80, ysUp sy ylo)]

/-- the cut at `Q` with the sign bit `b` of the vertical speed: `RoomWall.cutW` with that bit -/
def cutC (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine) (b : UInt8) : Cut :=
  {cutW sy E B P screen M Q with B := [(I sy.Player_Y_Speed, ⟨b, 0x80⟩)]}

/-- the height is known and above the corner's height `cy` -/
def knHigh (t : Tag) (cy : Nat) : Bool :=
  match t.same with
  | some v => decide (v.toNat < cy)
  | none => false

/-- the cut at the entry of `ImpedePlayerMove` from the side check: the side byte 1 (the block on his right), the two return addresses on the stack, the coordinate `x`
and the page 0 -/
def impCutC0 (sy : Syms) (E : Rom) (s0 x : UInt8) : Cut :=
  let rb := retBG sy E - 1
  let ri := retImp sy E - 1
  {pc := sy.ImpedePlayerMove, s := s0 - 4,
   K := [(sideI sy E, 1), (stkI s0, (rb >>> 8).toUInt8), (stkI (s0 - 1), rb.toUInt8),
         (stkI (s0 - 2), (ri >>> 8).toUInt8), (stkI (s0 - 3), ri.toUInt8), (I sy.Player_X_Position, x), (I sy.Player_PageLoc, 0)]}

/-- the same with the speed `v` -/
def impCutC (sy : Syms) (E : Rom) (s0 x v : UInt8) : Cut :=
  {impCutC0 sy E s0 x with K := (impCutC0 sy E s0 x).K ++ [(I sy.Player_X_Speed, v)]}

/-- where the first walk stops: at `retBG`, or at `ImpedePlayerMove` -/
def stop1C (sy : Syms) (E : Rom) (T : TS) : Bool := T.pc == retBG sy E || T.pc == sy.ImpedePlayerMove

/-- what the first walk asks where it stops: at `retBG` the stack of `Q` and the height above `cy`; at `ImpedePlayerMove` the cut `impCutC0` with the coordinate `x` of
`Q`, and the speed not written since `Q` -/
def goal1C (sy : Syms) (E : Rom) (cy : Nat) (s0 x : UInt8) (T : TS) : Bool :=
  if T.pc == retBG sy E then T.s == some s0 && knHigh (T.ram (I sy.Player_Y_Position)) cy
  else goalC (impCutC0 sy E s0 x) [] T && !T.w (I sy.Player_X_Speed)

/-- what the second walk asks back at `retBG`, from the coordinate `x` and the speed `v`: the stack of `Q`, the page 0; from 0 to 127 the speed 0 and the coordinate
`x − 1`; a negative speed and the coordinate as they were -/
def endC (sy : Syms) (s0 x v : UInt8) (T : TS) : Bool :=
  T.s == some s0 && knIs (T.ram (I sy.Player_PageLoc)) 0 &&
    (if v < 0x80 then knIs (T.ram (I sy.Player_X_Speed)) 0 && knIs (T.ram (I sy.Player_X_Position)) (x - 1)
     else knIs (T.ram (I sy.Player_X_Speed)) v && knIs (T.ram (I sy.Player_X_Position)) x)

/-- the first walk, from the cut at `Q` -/
def check1C (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (cy : Nat) (M Q : Machine) (b : UInt8) (fuel : Nat) : Bool :=
  walkT E (stop1C sy E) (goal1C sy E cy Q.s (Q.ram.get! P.x)) fuel (startQ (cutC sy E B P screen M Q b))

/-- the second walk, from `ImpedePlayerMove` with the coordinate `x` and the speed `v` -/
def check2C (sy : Syms) (E : Rom) (s0 x v : UInt8) (fuel : Nat) : Bool :=
  walkT E (fun T => T.pc == retBG sy E) (endC sy s0 x v) fuel (startQ (impCutC sy E s0 x v))

/-- the first walk for every coordinate of `xs` and every kind of `cls` -/
def family1C (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (cy : Nat) (M Q : Machine)
    (xs : List UInt8) (cls : List (UInt8 × UInt8 × List UInt8)) (fuel : Nat) : Bool :=
  cls.all fun c => c.2.2.all fun y => xs.all fun x => check1C sy E B P screen cy M (variantW sy P Q x y c.1) c.2.1 fuel

/-- the second walk for every coordinate of `xs` and every speed -/
def family2C (sy : Syms) (E : Rom) (s0 : UInt8) (xs : List UInt8) (fuel : Nat) : Bool :=
  xs.all fun x => (List.range 256).all fun v => check2C sy E s0 x v.toUInt8 fuel

/-- the cells of every machine of the family lie in the block buffers and are not coins on `M` -/
def cellsOKC (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (M Q : Machine) (cs : List UInt8) (xs : List UInt8)
    (cls : List (UInt8 × UInt8 × List UInt8)) : Bool :=
  cls.all fun c => c.2.2.all fun y => xs.all fun x => (cellsW sy E B P (variantW sy P Q x y 0)).all fun j =>
    decide (B.bufLo ≤ j ∧ j < B.bufLo + B.bufN) && !cs.contains (M.ram.get! j)

/-! ## From the walks to the machine -/

section
variable {sy : Syms} {E : Rom}

theorem knIs_spec {t : Tag} {v x y : UInt8} (h : knIs t v = true) (hr : t.R x y) : x = v := by
  simp only [knIs, beq_iff_eq] at h
  exact (Tag.same_spec h hr).1

theorem knHigh_spec {t : Tag} {cy : Nat} {x y : UInt8} (h : knHigh t cy = true) (hr : t.R x y) : x.toNat < cy := by
  unfold knHigh at h
  cases hm : t.same with
  | none => rw [hm] at h; cases h
  | some v =>
    rw [hm] at h
    rw [(Tag.same_spec hm hr).1]
    simpa using h

/-- what `endC` says of the machine -/
theorem endC_spec {s0 x v : UInt8} {T : TS} {m₀ n₀ m n : Machine} (h : endC sy s0 x v T = true) (hl : Lk E m₀ n₀ T m n) :
    m.s = s0 ∧ m.ram.get! (I sy.Player_PageLoc) = 0 ∧
      (if v < 0x80 then m.ram.get! (I sy.Player_X_Speed) = 0 ∧ m.ram.get! (I sy.Player_X_Position) = x - 1
       else m.ram.get! (I sy.Player_X_Speed) = v ∧ m.ram.get! (I sy.Player_X_Position) = x) := by
  unfold endC at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, hv⟩ := h
  refine ⟨(hl.s _ hs).1, knIs_spec hp (hl.ram _ (I_lt _)), ?_⟩
  split
  · rename_i hc
    rw [if_pos hc] at hv
    simp only [Bool.and_eq_true] at hv
    exact ⟨knIs_spec hv.1 (hl.ram _ (I_lt _)), knIs_spec hv.2 (hl.ram _ (I_lt _))⟩
  · rename_i hc
    rw [if_neg hc] at hv
    simp only [Bool.and_eq_true] at hv
    exact ⟨knIs_spec hv.1 (hl.ram _ (I_lt _)), knIs_spec hv.2 (hl.ram _ (I_lt _))⟩

/-- the cut at `ImpedePlayerMove` with the speed, from the cut without it and the speed -/
theorem at_impCutC {s0 x v : UInt8} {m : Machine} (h : At E (impCutC0 sy E s0 x) m) (hv : m.ram.get! (I sy.Player_X_Speed) = v) : At E (impCutC sy E s0 x v) m := by
  refine {good := h.good, pc := h.pc, s := h.s, K := ?_, B := h.B, ra := h.ra, x := h.x, cf := h.cf}
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h.K p hp
  · simp only [List.mem_singleton] at hp
    subst hp
    exact hv

/-- **From a cut at `Q` that passes both walks, back at `retBG`**: within the frame, at `retBG` with the stack pointer of `Q`, the machine is `CornerEnd` of the
coordinate and the speed at `Q`. The second walk is asked for every speed -/
theorem corner_end {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {cy : Nat} {M R : Machine} {b : UInt8} {f1 f2 : Nat}
    (h1 : check1C sy E B P screen cy M R b f1 = true) (h2 : ∀ v : UInt8, check2C sy E R.s (R.ram.get! P.x) v f2 = true)
    (hat : At E (cutC sy E B P screen M R b) R) (ePx : P.x = I sy.Player_X_Position) :
    ∃ k, k ≤ f1 + f2 ∧ (stepN k R).pc = retBG sy E ∧ (stepN k R).s = R.s ∧ InFrameN E R k ∧
      CornerEnd sy cy (R.ram.get! (I sy.Player_X_Position)) (R.ram.get! (I sy.Player_X_Speed)) (stepN k R) := by
  obtain ⟨k, T, hk, hs, hg, hl, hj⟩ := walkT_spec f1 _ R R h1 (lk_self hat)
  have hin : InFrameN E R k := fun j hj' => by obtain ⟨_, _, _, _, hi, _⟩ := hj j hj'; exact hi
  unfold goal1C at hg
  split at hg
  · rename_i hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨e1, e2⟩ := hg
    exact ⟨k, by omega, by rw [hl.pcl]; simpa using hp, (hl.s _ e1).1, hin, Or.inl (knHigh_spec e2 (hl.ram _ (I_lt _)))⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨hg, hw⟩ := hg
    obtain ⟨ha, _, _⟩ := at_of_goal hg hl
    have hx : (stepN k R).ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := hl.fixl _ (I_lt _) hw
    have ha2 := at_impCutC ha hx
    obtain ⟨k2, T2, hk2, hs2', hg2, hl2, hj2⟩ := walkT_spec f2 _ (stepN k R) (stepN k R) (h2 _) (lk_self ha2)
    have hin2 : InFrameN E (stepN k R) k2 := fun j hj' => by obtain ⟨_, _, _, _, hi, _⟩ := hj2 j hj'; exact hi
    obtain ⟨e1, e2, e3⟩ := endC_spec hg2 hl2
    rw [← stepN_add] at e1 e2 e3
    rw [ePx] at e3
    refine ⟨k + k2, by omega, ?_, e1, InFrameN.add hin hin2, Or.inr ⟨e2, e3⟩⟩
    rw [stepN_add, hl2.pcl]
    simpa using hs2'

/-- the first walk applies to every machine with the same sampled bytes and stack pointer -/
theorem check1C_eq {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {cy : Nat} {M Q R : Machine} {b : UInt8} {fuel : Nat}
    (sp : Q.s = R.s) (same : ∀ j ∈ keysW sy E P screen, Q.ram.get! j = R.ram.get! j) :
    check1C sy E B P screen cy M Q b fuel = check1C sy E B P screen cy M R b fuel := by
  have hx : Q.ram.get! P.x = R.ram.get! P.x := same _ (by simp [keysW, RoomLand.keys])
  unfold check1C cutC
  rw [cutW_eq sp same, sp, hx]

/-- **The machine at `Q` meets the cut**: the sampled entries hold by construction; the cells need the solid map at `Q`, their bounds and no coin; the sign bit -/
theorem at_cutC {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M Q : Machine} {cs : List UInt8} {b : UInt8}
    (hg : Good E Q) (hp : Q.pc = sy.PlayerSubs) (hs : RoomBlocks.Solid B cs M Q)
    (hb : ∀ j ∈ cellsW sy E B P Q, B.bufLo ≤ j ∧ j < B.bufLo + B.bufN)
    (hn : ∀ j ∈ cellsW sy E B P Q, M.ram.get! j ∉ cs)
    (hv : Q.ram.get! (I sy.Player_Y_Speed) &&& 0x80 = b &&& 0x80) :
    At E (cutC sy E B P screen M Q b) Q := by
  refine {good := hg, pc := hp, s := rfl, K := ?_, B := ?_, ra := ?_, x := ?_, cf := ?_}
  · intro p hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
      rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
      exact hs j (hb j hj).1 (hb j hj).2 (hn j hj)
  · intro p hm
    simp only [cutC, List.mem_singleton] at hm
    subst hm
    exact hv
  · simp [cutC, cutW]
  · simp [cutC, cutW]
  · simp [cutC, cutW]

/-- the cells of the family: bounds and no coin, for every machine with the same coordinates as one of its machines -/
theorem cells_of_familyC {B : ScreenPage.Places} {P : RoomCollision.Places} {M Q R : Machine} {cs xs : List UInt8} {cls : List (UInt8 × UInt8 × List UInt8)}
    {c : UInt8 × UInt8 × List UInt8} {x y : UInt8}
    (hc : cellsOKC sy E B P M Q cs xs cls = true) (hcm : c ∈ cls) (hx : x ∈ xs) (hy : y ∈ c.2.2)
    (hk : ∀ j ∈ RoomCollision.coords P, R.ram.get! j = (variantW sy P Q x y 0).ram.get! j) :
    ∀ j ∈ cellsW sy E B P R, (B.bufLo ≤ j ∧ j < B.bufLo + B.bufN) ∧ M.ram.get! j ∉ cs := by
  intro j hj
  rw [RoomWall.cellsW_eq hk] at hj
  have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc c hcm) y hy) x hx) j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1, fun hm => by
    have e := List.contains_iff_mem.mpr hm
    rw [h.2] at e
    cases e⟩

end

/-! ## The checks on the ROM, and a frame of the room -/

/-- **The checks on the ROM**: the first walk for every coordinate of `xsC` and every kind of `clsC` from the reference machine of `RoomLand`; the second for every
coordinate and speed; the cells; the room's walk that knows the control bytes at `PlayerSubs`; the reference of `RoomWall` -/
structure Checks (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) (h ylo : Nat) : Prop where
  family1 : family1C sy (Rom.of m0) (ScreenPage.placesR sy nm m0) (RoomCollision.places sy m0) (SideFrame.screenI sy m0) (Jump.cornerY sy h) (RoomMap.mapRef m0)
    (RoomLand.refQ sy m0 0) (xsC sy) (clsC sy ylo) 3000 = true
  family2 : family2C sy (Rom.of m0) (RoomLand.refQ sy m0 0).s (xsC sy) 200 = true
  cells : cellsOKC sy (Rom.of m0) (ScreenPage.placesR sy nm m0) (RoomCollision.places sy m0) (RoomMap.mapRef m0) (RoomLand.refQ sy m0 0)
    (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) (xsC sy) (clsC sy ylo) = true
  control : RoomLand.controlCheck sy nm m0 = true
  ref : refCheckW sy m0 = true

theorem toUInt8_toNat (v : UInt8) : v.toNat.toUInt8 = v := by simp

/-- **At the end of the move of a frame of the room, with the vertical page 1, the page 0, a coordinate of `xsC`, and the state, the sign bit of the vertical speed and the
height of a kind of `clsC`, the collision routine returns to `PlayerSubs`, and there the machine is `CornerEnd`**: the height above the corner's, or pushed back one pixel
with the speed 0, or moving left as at `Q`. The routine, the screen bytes, the jump spring and the collision-disable flag come from the room's walk; the cells from the
solid map at `Q`; the stack and `Good` are hypotheses. -/
theorem corner_at {sy : Syms} {nm : PipeTransitionAll.Names} {m0 m : Machine} {h ylo : Nat} (H : Checks sy nm m0 h ylo)
    (hM : RoomMap.MapFacts sy nm m0) {input : UInt8} {n : Nat}
    (hm : ScreenPage.RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nm m0) (PipeEntryRule.trace m input j))
    (hf : (PipeEntryRule.trace m input n).frame = m.frame) (pc : (PipeEntryRule.trace m input n).pc = sy.PlayerSubs)
    (hg : Good (Rom.of m0) (PipeEntryRule.trace m input n)) (hs : (PipeEntryRule.trace m input n).s = ctrlStack sy m0)
    (hsolid : RoomBlocks.Solid (ScreenPage.placesR sy nm m0) (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) (RoomMap.mapRef m0) (PipeEntryRule.trace m input n))
    (hhi : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_HighPos) = 1)
    (hpg : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_PageLoc) = 0)
    (hx : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Position) ∈ xsC sy)
    {c : UInt8 × UInt8 × List UInt8} (hc : c ∈ clsC sy ylo)
    (hst : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_State) = c.1)
    (hvy : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Speed) &&& 0x80 = c.2.1 &&& 0x80)
    (hy : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Position) ∈ c.2.2) :
    ∃ k, k ≤ 3200 ∧ (stepN k (PipeEntryRule.trace m input n)).pc = retBG sy (Rom.of m0) ∧
      (stepN k (PipeEntryRule.trace m input n)).s = (PipeEntryRule.trace m input n).s ∧ InFrameN (Rom.of m0) (PipeEntryRule.trace m input n) k ∧
      CornerEnd sy (Jump.cornerY sy h) ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Position))
        ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Speed)) (stepN k (PipeEntryRule.trace m input n)) := by
  have hr := H.ref
  simp only [refCheckW, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsz, ePx⟩, ePg⟩, ePy⟩, r1⟩, r2⟩, rc⟩, rx⟩, nxy⟩, nxs⟩, nys⟩, rs⟩ := hr
  let R := PipeEntryRule.trace m input n
  let Q := RoomLand.refQ sy m0 0
  let P := RoomCollision.places sy m0
  let x := R.ram.get! (I sy.Player_X_Position)
  let y := R.ram.get! (I sy.Player_Y_Position)
  let V := variantW sy P Q x y c.1
  have hlt : ∀ j, j < 2048 → j < Q.ram.size := fun j hj => by rw [hsz]; exact hj
  have hPx : P.x < 2048 := by rw [ePx]; exact I_lt _
  have hPy : P.y < 2048 := by rw [ePy]; exact I_lt _
  have hvar : ∀ j, j ≠ P.x → j ≠ P.y → j ≠ I sy.Player_State → V.ram.get! j = Q.ram.get! j := fun j h1 h2 h3 => by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) c.1).get! j = Q.ram.get! j
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h3 e.symm), PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h2 e.symm),
      PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h1 e.symm)]
  have hvst : V.ram.get! (I sy.Player_State) = c.1 := by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) c.1).get! (I sy.Player_State) = c.1
    apply PipeTransitionAll.ba_get_set_self
    rw [PipeTransitionAll.ba_size_set, PipeTransitionAll.ba_size_set]
    exact hlt _ (I_lt _)
  have hvy' : V.ram.get! P.y = y := by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) c.1).get! P.y = y
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => nys e.symm)]
    apply PipeTransitionAll.ba_get_set_self
    rw [PipeTransitionAll.ba_size_set]
    exact hlt _ hPy
  have hvx : V.ram.get! P.x = x := by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) c.1).get! P.x = x
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => nxs e.symm), PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => nxy e.symm)]
    exact PipeTransitionAll.ba_get_set_self _ _ _ (hlt _ hPx)
  have ctl := RoomLand.controls_at_subs hM H.control hm sites hf pc
  have hcK : ∀ j ∈ RoomLand.controlKeys sy m0, R.ram.get! j = V.ram.get! j := by
    intro j hj
    have ne := rx j (List.mem_append_right _ hj)
    rw [hvar j ne.1.1 ne.1.2 ne.2, (rc j hj).2, ctl j hj (rc j hj).1]
  have hk : ∀ j ∈ keysW sy (Rom.of m0) P (SideFrame.screenI sy m0), R.ram.get! j = V.ram.get! j := by
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · unfold RoomLand.keys at hj
      rcases List.mem_append.mp hj with hj | hj
      · rcases List.mem_append.mp hj with hj | hj
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with e | e | e | e | e | e
          · exact hcK j (by rw [e]; simp [RoomLand.controlKeys])
          · subst e
            have ne := rx (I sy.Player_Y_HighPos) (by simp)
            rw [hvar _ ne.1.1 ne.1.2 ne.2, r1]
            exact hhi
          · exact hcK j (by rw [e]; simp [RoomLand.controlKeys])
          · subst e
            rw [hvx]
            exact congrArg R.ram.get! ePx
          · subst e
            have ne := rx P.pg (by simp [P])
            rw [hvar _ ne.1.1 ne.1.2 ne.2, r2, ePg]
            exact hpg
          · subst e
            rw [hvy']
            exact congrArg R.ram.get! ePy
        · apply hcK j
          unfold RoomLand.controlKeys
          exact List.mem_cons_of_mem _ (List.mem_append_left _ hj)
      · apply hcK j
        rw [List.mem_singleton.mp hj]
        simp [RoomLand.controlKeys]
    · simp only [List.mem_singleton] at hj
      subst hj
      rw [hvst]
      exact hst
  have hVs : V.s = Q.s := variantW_s
  have hsQ : R.s = V.s := hs.trans (rs.symm.trans hVs.symm)
  have h1 : check1C sy (Rom.of m0) (ScreenPage.placesR sy nm m0) P (SideFrame.screenI sy m0) (Jump.cornerY sy h) (RoomMap.mapRef m0) R c.2.1 3000 = true := by
    rw [check1C_eq hsQ hk]
    exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp H.family1 c hc) y hy) x hx
  have h2 : ∀ v : UInt8, check2C sy (Rom.of m0) R.s (R.ram.get! P.x) v 200 = true := by
    intro v
    rw [hs, ← rs, ePx]
    have e := List.all_eq_true.mp (List.all_eq_true.mp H.family2 x hx) v.toNat (List.mem_range.2 v.toNat_lt)
    rwa [toUInt8_toNat] at e
  have hcoords : ∀ j ∈ RoomCollision.coords P, R.ram.get! j = (variantW sy P Q x y 0).ram.get! j := by
    intro j hj
    have e := hk j (coords_sub_keys j hj)
    rw [e]
    simp only [RoomCollision.coords, List.mem_cons, List.not_mem_nil, or_false] at hj
    have hne : j ≠ I sy.Player_State := by
      rcases hj with rfl | rfl | rfl
      · exact nxs
      · exact (rx P.pg (by simp [P])).2
      · exact nys
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) c.1).get! j = (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) 0).get! j
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => hne e.symm), PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => hne e.symm)]
  have hcell := cells_of_familyC H.cells hc hx hy hcoords
  have hat : At (Rom.of m0) (cutC sy (Rom.of m0) (ScreenPage.placesR sy nm m0) P (SideFrame.screenI sy m0) (RoomMap.mapRef m0) R c.2.1) R :=
    at_cutC hg pc hsolid (fun j hj => (hcell j hj).1) (fun j hj => (hcell j hj).2) hvy
  obtain ⟨k, hk', a1, a2, a3, a4⟩ := corner_end h1 h2 hat ePx
  exact ⟨k, by omega, a1, a2, a3, a4⟩

/-- **A frame of the room whose end of the move meets the conditions of `corner_at`, and that ends in the player's routine, ends `CornerEnd`**: the height above the
corner's, or pushed back one pixel with the speed 0 and the page 0, or moving left as at `Q` with the page 0. `corner_at` up to `retBG`, and `RoomWall`'s walk of the whole
frame from there (`RoomWall.after_G`: no step writes the speed, the coordinate, the page, the state or the height) to the frame's end. -/
theorem corner_frame {sy : Syms} {nm : PipeTransitionAll.Names} {m0 m : Machine} {h ylo : Nat} (H : Checks sy nm m0 h ylo) (hcw : RoomWall.checkW sy nm m0 = true)
    (hap : RoomWall.apartW sy (ScreenPage.placesR sy nm m0) = true) (hM : RoomMap.MapFacts sy nm m0) {input : UInt8} {n : Nat}
    (hm : ScreenPage.RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nm m0) (PipeEntryRule.trace m input j))
    {idle : UInt16} (hidle : idleAt (Rom.of m0) idle = true)
    (htime : ∀ j, (PipeEntryRule.trace m input j).pc ≠ idle → (PipeEntryRule.trace m input j).fdot ≤ dotsPerFrame - 64)
    (hf : (PipeEntryRule.trace m input n).frame = m.frame) (pc : (PipeEntryRule.trace m input n).pc = sy.PlayerSubs)
    (hg : Good (Rom.of m0) (PipeEntryRule.trace m input n)) (hs : (PipeEntryRule.trace m input n).s = ctrlStack sy m0)
    (hsolid : RoomBlocks.Solid (ScreenPage.placesR sy nm m0) (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) (RoomMap.mapRef m0) (PipeEntryRule.trace m input n))
    (hhi : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_HighPos) = 1)
    (hpg : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_PageLoc) = 0)
    (hx : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Position) ∈ xsC sy)
    {c : UInt8 × UInt8 × List UInt8} (hc : c ∈ clsC sy ylo)
    (hst : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_State) = c.1)
    (hvy : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Speed) &&& 0x80 = c.2.1 &&& 0x80)
    (hy : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Position) ∈ c.2.2)
    (hrt : (PipeTransition.frame m input).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    CornerEnd sy (Jump.cornerY sy h) ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Position))
      ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Speed)) (PipeTransition.frame m input) := by
  obtain ⟨k, _, hpc, _, hin, hend⟩ := corner_at H hM hm sites hf pc hg hs hsolid hhi hpg hx hc hst hvy hy
  obtain ⟨htr, hfr⟩ := FrameModel.trace_inFrame hidle hf hin htime k (Nat.le_refl k)
  have hO := RoomVert.okV_of_check hcw
  have hkeep := RoomWall.after_G hO RoomVert.cfgOfV_fin hap hm sites (n + k) (by rw [htr]; exact hpc) hfr hrt
  have e : ∀ x ∈ RoomWall.hW sy, (PipeTransition.frame m input).ram.get! x = (stepN k (PipeEntryRule.trace m input n)).ram.get! x := fun x hx => by
    rw [hkeep x hx, htr]
  unfold CornerEnd at hend ⊢
  rw [e (I sy.Player_Y_Position) (by simp [RoomWall.hW]), e (I sy.Player_PageLoc) (by simp [RoomWall.hW]),
    e (I sy.Player_X_Speed) (by simp [RoomWall.hW]), e (I sy.Player_X_Position) (by simp [RoomWall.hW])]
  exact hend


end Smbrta.RoomCorner
