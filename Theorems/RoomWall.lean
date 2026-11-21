import Theorems.RoomLand

/-! # A stand away from the floor in the room, from the end of the move

On a frame of the room the player's collision routine runs after the end of the move `Q` (the first `PlayerSubs` of the frame). Two walks follow it from `Q` back to
`PlayerSubs`, to the instruction after its call of the collision routine (`retBG`).

* The first walk (`check1`) starts at a cut that samples the bytes of `RoomLand.keys` and the player's state, and takes the head, foot and side cells of the three adder
  offsets from the reference map. The horizontal speed is not sampled. The walk stops at `retBG`, or at `ImpedePlayerMove` when the state is known to be 0 there and the
  height is not the floor's: a stand away from the floor that comes to the routine that pushes him out of a side.
* The second walk (`check2`) starts there, at `ImpedePlayerMove`, with the side byte 2 (a left side), the state 0, the return addresses on the stack and the speed sampled,
  and goes back to `retBG`.

At `retBG` both ask the same (`endOK`): the state is not 0, or he stands with the floor's height, or the horizontal speed is 0. So a frame whose `Q` meets the cut and has a
speed that is 0 or negative (but not −128) stands away from the floor at `retBG` only with the speed 0 (`wall_end`, `wall_at`).

A third walk, of the room's whole frame (`checkW`, `after_G`), marks the state at `retBG`: no step after it writes the speed, the position, the state or the height, or
the frame ends out of the player's routine. So the frame ends as it was at `retBG` (`wall_frame`).

`neg_of_check` checks one frame of `hstep` from a state that moves left fast, and `not_follow_of` joins them to `hstep` before the end of the fall: with the fields
`stand_fast` and `clean`, a stand away from the floor whose end of the move gives the speed 0 at the frame's end (what `wall_frame` gives) is on a frame that does not
follow `hstep`. `RoomJoin.RoomRun.stand_first` proves the conditions of `wall_at` at the end of the move of the first stand of the fall on the real machines (`InRoom.wall`,
`Route.Run.roomWall`); the field `RoomJoin.RoomFields.stand_wall` asks only the later stands (page `1-1/c-7-5-16-FirstStand.md`). There is no game data in this file. Page: `1-1/c-7-5-15-RoomWall.md`. -/
namespace Smbrta.RoomWall
open FrameModel

/-- the address after the first `JSR target` from `a` on, within `n` bytes -/
def afterJsr (E : Rom) (a target : UInt16) : Nat → UInt16
  | 0 => a
  | n + 1 => if E.b a == 0x20 && E.w (a + 1) == target then a + 3 else afterJsr E (a + 1) target n

/-- the instruction of `PlayerSubs` after its call of the collision routine -/
def retBG (sy : Syms) (E : Rom) : UInt16 := afterJsr E sy.PlayerSubs sy.PlayerBGCollision 32

/-- the instruction after the side check's call of `ImpedePlayerMove` -/
def retImp (sy : Syms) (E : Rom) : UInt16 := afterJsr E sy.DoPlayerSideCheck sy.ImpedePlayerMove 255

/-- the byte that tells `ImpedePlayerMove` which side: the operand of its third instruction, a `LDX` zero page -/
def sideI (sy : Syms) (E : Rom) : Nat := (E.b (sy.ImpedePlayerMove + 5)).toNat

/-- the floor's height as a byte -/
def floorY (sy : Syms) : UInt8 := (Jump.groundY sy).toUInt8

/-- the head, foot and side cells of each of the three adder offsets, computed from `Q` -/
def cellsW (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (Q : Machine) : List Nat :=
  ([0, 1, 2] : List UInt16).flatMap fun o =>
    let e := E.b (sy.BlockBufferAdderData + o)
    ([0, 1, 2, 3, 4, 5, 6] : List UInt8).map fun d => RoomLand.cell E B P Q (e + d)

/-- the bytes the cut samples at `Q`: those of `RoomLand.keys`, and the player's state -/
def keysW (sy : Syms) (E : Rom) (P : RoomCollision.Places) (screen : List Nat) : List Nat :=
  RoomLand.keys sy E P screen ++ [I sy.Player_State]

/-- the cut at `Q`: the sampled bytes from `Q`, the cells from `M`, and the vertical speed not negative -/
def cutW (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine) : Cut :=
  {pc := sy.PlayerSubs, s := Q.s,
   K := (keysW sy E P screen).map (fun j => (j, Q.ram.get! j)) ++ (cellsW sy E B P Q).map (fun j => (j, M.ram.get! j)),
   B := [(I sy.Player_Y_Speed, ⟨0, 0x80⟩)]}

/-- the tag is known to be `v` -/
def knIs (t : Tag) (v : UInt8) : Bool := t.same == some v

/-- the tag is known, and not 0 -/
def knNe0 (t : Tag) : Bool :=
  match t.same with
  | some v => v != 0
  | none => false

/-- what both walks ask back at `retBG`, with the stack pointer `s0` of `Q`: the state is not 0, or the state is 0 with the floor's height, or the speed is 0 -/
def endOK (sy : Syms) (s0 : UInt8) (T : TS) : Bool :=
  T.s == some s0 &&
    (knNe0 (T.ram (I sy.Player_State)) ||
     (knIs (T.ram (I sy.Player_State)) 0 && knIs (T.ram (I sy.Player_Y_Position)) (floorY sy)) ||
     knIs (T.ram (I sy.Player_X_Speed)) 0)

/-- the cut at the entry of `ImpedePlayerMove` from the side check, without the speed: the side byte 2, the state 0, and the two return addresses on the stack -/
def impCut0 (sy : Syms) (E : Rom) (s0 : UInt8) : Cut :=
  let rb := retBG sy E - 1
  let ri := retImp sy E - 1
  {pc := sy.ImpedePlayerMove, s := s0 - 4,
   K := [(sideI sy E, 2), (I sy.Player_State, 0), (stkI s0, (rb >>> 8).toUInt8), (stkI (s0 - 1), rb.toUInt8),
         (stkI (s0 - 2), (ri >>> 8).toUInt8), (stkI (s0 - 3), ri.toUInt8)]}

/-- the same with the speed `v` -/
def impCut (sy : Syms) (E : Rom) (s0 v : UInt8) : Cut :=
  {impCut0 sy E s0 with K := (impCut0 sy E s0).K ++ [(I sy.Player_X_Speed, v)]}

/-- where the first walk stops: at `retBG`, or at `ImpedePlayerMove` standing away from the floor -/
def stop1 (sy : Syms) (E : Rom) (T : TS) : Bool :=
  T.pc == retBG sy E ||
    (T.pc == sy.ImpedePlayerMove && knIs (T.ram (I sy.Player_State)) 0 && !knIs (T.ram (I sy.Player_Y_Position)) (floorY sy))

/-- what the first walk asks where it stops: `endOK` at `retBG`; at `ImpedePlayerMove` the cut `impCut0`, with the speed not written since `Q` or known to be 0
(the screen's left edge, in `ScrollHandler`, may stop him) -/
def goal1 (sy : Syms) (E : Rom) (s0 : UInt8) (T : TS) : Bool :=
  if T.pc == retBG sy E then endOK sy s0 T
  else goalC (impCut0 sy E s0) [] T && (!T.w (I sy.Player_X_Speed) || knIs (T.ram (I sy.Player_X_Speed)) 0)

/-- the first walk, from the cut at `Q` -/
def check1 (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine) (fuel : Nat) : Bool :=
  walkT E (stop1 sy E) (goal1 sy E Q.s) fuel (startQ (cutW sy E B P screen M Q))

/-- the second walk, from `ImpedePlayerMove` with the speed `v` -/
def check2 (sy : Syms) (E : Rom) (s0 v : UInt8) (fuel : Nat) : Bool :=
  walkT E (fun T => T.pc == retBG sy E) (endOK sy s0) fuel (startQ (impCut sy E s0 v))

/-- the speeds of the second walk: 0, and the negative bytes but −128 -/
def speeds : List UInt8 := 0 :: ((List.range 127).map fun k => (129 + k).toUInt8)

/-- the byte 0 and the bytes from 129 on are the speeds of the second walk (`RoomJoin.WallQ.v`) -/
theorem speeds_of {v : UInt8} (h : v = 0 ∨ 129 ≤ v.toNat) : v ∈ speeds := by
  rcases h with h | h
  · rw [h]
    exact List.mem_cons_self
  · have hv := v.toNat_lt
    exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨v.toNat - 129, List.mem_range.2 (by omega), by
      rw [show 129 + (v.toNat - 129) = v.toNat by omega]; simp⟩)

/-- `Q` with the horizontal coordinate `x`, the height `y` and the state `st` -/
def variantW (sy : Syms) (P : RoomCollision.Places) (Q : Machine) (x y st : UInt8) : Machine :=
  {Q with ram := ((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) st}

theorem variantW_s {sy : Syms} {P : RoomCollision.Places} {Q : Machine} {x y st : UInt8} : (variantW sy P Q x y st).s = Q.s := rfl

/-- the first walk for every horizontal coordinate of `xs`, every height of `ys` and the states 0, 1, 2 -/
def family1 (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine)
    (xs ys : List UInt8) (fuel : Nat) : Bool :=
  ys.all fun y => xs.all fun x => ([0, 1, 2] : List UInt8).all fun st => check1 sy E B P screen M (variantW sy P Q x y st) fuel

/-- the second walk for every speed of `speeds` -/
def family2 (sy : Syms) (E : Rom) (s0 : UInt8) (fuel : Nat) : Bool :=
  speeds.all fun v => check2 sy E s0 v fuel

/-- the cells of every machine of the family lie in the block buffers and are not coins on `M` -/
def cellsOKW (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (M Q : Machine) (cs : List UInt8) (xs ys : List UInt8) : Bool :=
  ys.all fun y => xs.all fun x => (cellsW sy E B P (variantW sy P Q x y 0)).all fun j =>
    decide (B.bufLo ≤ j ∧ j < B.bufLo + B.bufN) && !cs.contains (M.ram.get! j)

/-! ## From the walks to the machine -/

section
variable {sy : Syms} {E : Rom}

/-- what `endOK` says of the machine -/
theorem endOK_spec {s0 : UInt8} {T : TS} {m₀ n₀ m n : Machine} (h : endOK sy s0 T = true) (hl : Lk E m₀ n₀ T m n) :
    m.s = s0 ∧ (m.ram.get! (I sy.Player_State) ≠ 0 ∨
      (m.ram.get! (I sy.Player_State) = 0 ∧ m.ram.get! (I sy.Player_Y_Position) = floorY sy) ∨ m.ram.get! (I sy.Player_X_Speed) = 0) := by
  simp only [endOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hs, h⟩ := h
  refine ⟨(hl.s _ hs).1, ?_⟩
  rcases h with (h | ⟨h1, h2⟩) | h
  · left
    unfold knNe0 at h
    cases hm : (T.ram (I sy.Player_State)).same with
    | none => rw [hm] at h; cases h
    | some v =>
      rw [hm] at h
      have e := (Tag.same_spec hm (hl.ram _ (I_lt _))).1
      rw [e]
      simpa using h
  · right; left
    simp only [knIs, beq_iff_eq] at h1 h2
    exact ⟨(Tag.same_spec h1 (hl.ram _ (I_lt _))).1, (Tag.same_spec h2 (hl.ram _ (I_lt _))).1⟩
  · right; right
    simp only [knIs, beq_iff_eq] at h
    exact (Tag.same_spec h (hl.ram _ (I_lt _))).1

/-- the cut at `ImpedePlayerMove` with the speed, from the cut without it and the speed -/
theorem at_impCut {s0 v : UInt8} {m : Machine} (h : At E (impCut0 sy E s0) m) (hv : m.ram.get! (I sy.Player_X_Speed) = v) : At E (impCut sy E s0 v) m := by
  refine {good := h.good, pc := h.pc, s := h.s, K := ?_, B := h.B, ra := h.ra, x := h.x, cf := h.cf}
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h.K p hp
  · simp only [List.mem_singleton] at hp
    subst hp
    exact hv

/-- **From a cut at `Q` that passes both walks, back at `retBG`**: within the frame, at `retBG` with the stack pointer of `Q`, the state is not 0, or he stands at the
floor's height, or the speed is 0. The speed at `Q` is one of `speeds`; the second walk is asked for each of them -/
theorem wall_end {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M R : Machine} {f1 f2 : Nat}
    (h1 : check1 sy E B P screen M R f1 = true) (h2 : ∀ v ∈ speeds, check2 sy E R.s v f2 = true)
    (hat : At E (cutW sy E B P screen M R) R) (hv : R.ram.get! (I sy.Player_X_Speed) ∈ speeds) :
    ∃ k, k ≤ f1 + f2 ∧ (stepN k R).pc = retBG sy E ∧ (stepN k R).s = R.s ∧ InFrameN E R k ∧
      ((stepN k R).ram.get! (I sy.Player_State) ≠ 0 ∨
       ((stepN k R).ram.get! (I sy.Player_State) = 0 ∧ (stepN k R).ram.get! (I sy.Player_Y_Position) = floorY sy) ∨
       (stepN k R).ram.get! (I sy.Player_X_Speed) = 0) := by
  obtain ⟨k, T, hk, hs, hg, hl, hj⟩ := walkT_spec f1 _ R R h1 (lk_self hat)
  have hin : InFrameN E R k := fun j hj' => by obtain ⟨_, _, _, _, hi, _⟩ := hj j hj'; exact hi
  unfold goal1 at hg
  split at hg
  · rename_i hp
    obtain ⟨e1, e2⟩ := endOK_spec hg hl
    exact ⟨k, by omega, by rw [hl.pcl]; simpa using hp, e1, hin, e2⟩
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨hg, hw⟩ := hg
    obtain ⟨ha, _, _⟩ := at_of_goal hg hl
    have hx : (stepN k R).ram.get! (I sy.Player_X_Speed) ∈ speeds := by
      rcases hw with hw | hw
      · rw [hl.fixl _ (I_lt _) hw]
        exact hv
      · simp only [knIs, beq_iff_eq] at hw
        rw [(Tag.same_spec hw (hl.ram _ (I_lt _))).1]
        exact List.mem_cons_self
    have ha2 := at_impCut ha rfl
    obtain ⟨k2, T2, hk2, hs2', hg2, hl2, hj2⟩ :=
      walkT_spec f2 _ (stepN k R) (stepN k R) (h2 _ hx) (lk_self ha2)
    have hin2 : InFrameN E (stepN k R) k2 := fun j hj' => by obtain ⟨_, _, _, _, hi, _⟩ := hj2 j hj'; exact hi
    obtain ⟨e1, e2⟩ := endOK_spec hg2 hl2
    rw [← stepN_add] at e1 e2
    refine ⟨k + k2, by omega, ?_, e1, InFrameN.add hin hin2, e2⟩
    rw [stepN_add, hl2.pcl]
    simpa using hs2'

/-- the cells depend only on the coordinates -/
theorem cellsW_eq {B : ScreenPage.Places} {P : RoomCollision.Places} {Q R : Machine}
    (coords : ∀ j ∈ RoomCollision.coords P, Q.ram.get! j = R.ram.get! j) :
    cellsW sy E B P Q = cellsW sy E B P R := by
  have ce : ∀ index, RoomLand.cell E B P Q index = RoomLand.cell E B P R index := by
    intro index
    unfold RoomLand.cell
    exact congrArg I (RoomCollision.readAddress_from_coords (E := E) (B := B) (R := {Q with y := index}) (Q := R) coords)
  simp only [cellsW, ce]

theorem coords_sub_keys {P : RoomCollision.Places} {screen : List Nat} : ∀ j ∈ RoomCollision.coords P, j ∈ keysW sy E P screen := by
  intro j hj
  simp only [RoomCollision.coords, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> simp [keysW, RoomLand.keys]

/-- the cut depends only on its sampled bytes and the stack pointer -/
theorem cutW_eq {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M Q R : Machine}
    (sp : Q.s = R.s) (same : ∀ j ∈ keysW sy E P screen, Q.ram.get! j = R.ram.get! j) :
    cutW sy E B P screen M Q = cutW sy E B P screen M R := by
  have coords : ∀ j ∈ RoomCollision.coords P, Q.ram.get! j = R.ram.get! j := fun j hj => same j (coords_sub_keys j hj)
  have ks : (keysW sy E P screen).map (fun j => (j, Q.ram.get! j)) = (keysW sy E P screen).map (fun j => (j, R.ram.get! j)) := by
    apply List.map_congr_left
    intro j hj
    rw [same j hj]
  simp only [cutW, sp, ks, cellsW_eq (sy := sy) (E := E) (B := B) coords]

/-- the first walk applies to every machine with the same sampled bytes and stack pointer -/
theorem check1_eq {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M Q R : Machine} {fuel : Nat}
    (sp : Q.s = R.s) (same : ∀ j ∈ keysW sy E P screen, Q.ram.get! j = R.ram.get! j) :
    check1 sy E B P screen M Q fuel = check1 sy E B P screen M R fuel := by
  unfold check1
  rw [cutW_eq sp same, sp]

/-- **The machine at `Q` meets the cut**: the sampled entries hold by construction; the cells need the solid map at `Q`, their bounds and no coin. -/
theorem at_cutW {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M Q : Machine} {cs : List UInt8}
    (hg : Good E Q) (hp : Q.pc = sy.PlayerSubs) (hs : RoomBlocks.Solid B cs M Q)
    (hb : ∀ j ∈ cellsW sy E B P Q, B.bufLo ≤ j ∧ j < B.bufLo + B.bufN)
    (hn : ∀ j ∈ cellsW sy E B P Q, M.ram.get! j ∉ cs)
    (hv : Q.ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0) :
    At E (cutW sy E B P screen M Q) Q := by
  refine {good := hg, pc := hp, s := rfl, K := ?_, B := ?_, ra := ?_, x := ?_, cf := ?_}
  · intro p hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
      rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
      exact hs j (hb j hj).1 (hb j hj).2 (hn j hj)
  · intro p hm
    simp only [cutW, List.mem_singleton] at hm
    subst hm
    show Q.ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0 &&& 0x80
    rw [hv]
    rfl
  · simp [cutW]
  · simp [cutW]
  · simp [cutW]

/-- the cells of the family: bounds and no coin, for every machine with the same coordinates as one of its machines -/
theorem cells_of_familyW {B : ScreenPage.Places} {P : RoomCollision.Places} {M Q R : Machine} {cs xs ys : List UInt8} {x y : UInt8}
    (hc : cellsOKW sy E B P M Q cs xs ys = true) (hx : x ∈ xs) (hy : y ∈ ys)
    (hk : ∀ j ∈ RoomCollision.coords P, R.ram.get! j = (variantW sy P Q x y 0).ram.get! j) :
    ∀ j ∈ cellsW sy E B P R, (B.bufLo ≤ j ∧ j < B.bufLo + B.bufN) ∧ M.ram.get! j ∉ cs := by
  intro j hj
  rw [cellsW_eq hk] at hj
  have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc y hy) x hx) j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1, fun hm => by
    have e := List.contains_iff_mem.mpr hm
    rw [h.2] at e
    cases e⟩

end

/-! ## The checks on the ROM, and a frame of the room -/

/-- what the reference machine has: the size of the RAM, the coordinates' places, the vertical page 1, the page 0, the reference's control bytes, the stack of the player's
routine; and the coordinates and the state apart from each other and from the other sampled bytes -/
def refCheckW (sy : Syms) (m0 : Machine) : Bool :=
  let E := Rom.of m0
  let P := RoomCollision.places sy m0
  let Q := RoomLand.refQ sy m0 0
  let ref := ScreenPage.refR m0
  Q.ram.size == 2048 && P.x == I sy.Player_X_Position && P.pg == I sy.Player_PageLoc && P.y == I sy.Player_Y_Position &&
  Q.ram.get! (I sy.Player_Y_HighPos) == 1 && Q.ram.get! P.pg == 0 &&
  (RoomLand.controlKeys sy m0).all (fun j => decide (j < 2048) && Q.ram.get! j == ref.ram.get! j) &&
  ([RoomLand.disable sy E, I sy.Player_Y_HighPos, P.pg] ++ RoomLand.controlKeys sy m0).all (fun j => j != P.x && j != P.y && j != I sy.Player_State) &&
  P.x != P.y && P.x != I sy.Player_State && P.y != I sy.Player_State &&
  Q.s == ctrlStack sy m0

/-- the horizontal coordinates and the heights of the checks: x below 16, the height from 32 to 206 -/
def xsW : List UInt8 := (List.range 16).map Nat.toUInt8
def ysW : List UInt8 := (List.range 175).map fun k => (32 + k).toUInt8

/-- **The checks on the ROM**: the first walk for every coordinate of `xsW`, height of `ysW` and state 0, 1, 2 from the reference machine; the second for every speed of
`speeds`; the cells; the room's walk that knows the control bytes at `PlayerSubs`; the reference -/
structure Checks (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) : Prop where
  family1 : family1 sy (Rom.of m0) (ScreenPage.placesR sy nm m0) (RoomCollision.places sy m0) (SideFrame.screenI sy m0) (RoomMap.mapRef m0) (RoomLand.refQ sy m0 0)
    xsW ysW 3000 = true
  family2 : family2 sy (Rom.of m0) (RoomLand.refQ sy m0 0).s 200 = true
  cells : cellsOKW sy (Rom.of m0) (ScreenPage.placesR sy nm m0) (RoomCollision.places sy m0) (RoomMap.mapRef m0) (RoomLand.refQ sy m0 0)
    (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) xsW ysW = true
  control : RoomLand.controlCheck sy nm m0 = true
  ref : refCheckW sy m0 = true

theorem mem_xsW {x : UInt8} (h : x.toNat < 16) : x ∈ xsW := List.mem_map.2 ⟨x.toNat, List.mem_range.2 h, by simp⟩

theorem mem_ysW {y : UInt8} (h1 : 32 ≤ y.toNat) (h2 : y.toNat < 207) : y ∈ ysW :=
  List.mem_map.2 ⟨y.toNat - 32, List.mem_range.2 (by omega), by rw [show 32 + (y.toNat - 32) = y.toNat by omega]; simp⟩

/-- **At the end of the move of a frame of the room, with the vertical page 1, the page 0, x below 16, the height from 32 to 206, the state 0, 1 or 2, the vertical speed
not negative and the speed 0 or negative (not −128), the collision routine returns to `PlayerSubs`, and there the state is not 0, or he stands at the floor's height, or
the speed is 0**. The routine, the screen bytes, the jump spring and the collision-disable flag come from the room's walk; the cells from the solid map at `Q`; the stack
and `Good` are hypotheses. -/
theorem wall_at {sy : Syms} {nm : PipeTransitionAll.Names} {m0 m : Machine} (H : Checks sy nm m0)
    (hM : RoomMap.MapFacts sy nm m0) {input : UInt8} {n : Nat}
    (hm : ScreenPage.RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nm m0) (PipeEntryRule.trace m input j))
    (hf : (PipeEntryRule.trace m input n).frame = m.frame) (pc : (PipeEntryRule.trace m input n).pc = sy.PlayerSubs)
    (hg : Good (Rom.of m0) (PipeEntryRule.trace m input n)) (hs : (PipeEntryRule.trace m input n).s = ctrlStack sy m0)
    (hsolid : RoomBlocks.Solid (ScreenPage.placesR sy nm m0) (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) (RoomMap.mapRef m0) (PipeEntryRule.trace m input n))
    (hhi : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_HighPos) = 1)
    (hpg : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_PageLoc) = 0)
    (hx : ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Position)).toNat < 16)
    (hy1 : 32 ≤ ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Position)).toNat)
    (hy2 : ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Position)).toNat < 207)
    (hst : ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_State)).toNat ≤ 2)
    (hv : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0)
    (hxs : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Speed) ∈ speeds) :
    ∃ k, k ≤ 3200 ∧ (stepN k (PipeEntryRule.trace m input n)).pc = retBG sy (Rom.of m0) ∧
      (stepN k (PipeEntryRule.trace m input n)).s = (PipeEntryRule.trace m input n).s ∧ InFrameN (Rom.of m0) (PipeEntryRule.trace m input n) k ∧
      ((stepN k (PipeEntryRule.trace m input n)).ram.get! (I sy.Player_State) ≠ 0 ∨
       ((stepN k (PipeEntryRule.trace m input n)).ram.get! (I sy.Player_State) = 0 ∧
        (stepN k (PipeEntryRule.trace m input n)).ram.get! (I sy.Player_Y_Position) = floorY sy) ∨
       (stepN k (PipeEntryRule.trace m input n)).ram.get! (I sy.Player_X_Speed) = 0) := by
  have hr := H.ref
  simp only [refCheckW, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsz, ePx⟩, ePg⟩, ePy⟩, r1⟩, r2⟩, rc⟩, rx⟩, nxy⟩, nxs⟩, nys⟩, rs⟩ := hr
  let R := PipeEntryRule.trace m input n
  let Q := RoomLand.refQ sy m0 0
  let P := RoomCollision.places sy m0
  let x := R.ram.get! (I sy.Player_X_Position)
  let y := R.ram.get! (I sy.Player_Y_Position)
  let st := R.ram.get! (I sy.Player_State)
  let V := variantW sy P Q x y st
  have hlt : ∀ j, j < 2048 → j < Q.ram.size := fun j hj => by rw [hsz]; exact hj
  have hPx : P.x < 2048 := by rw [ePx]; exact I_lt _
  have hPy : P.y < 2048 := by rw [ePy]; exact I_lt _
  have hvar : ∀ j, j ≠ P.x → j ≠ P.y → j ≠ I sy.Player_State → V.ram.get! j = Q.ram.get! j := fun j h1 h2 h3 => by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) st).get! j = Q.ram.get! j
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h3 e.symm), PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h2 e.symm),
      PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h1 e.symm)]
  have hvst : V.ram.get! (I sy.Player_State) = st := by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) st).get! (I sy.Player_State) = st
    apply PipeTransitionAll.ba_get_set_self
    rw [PipeTransitionAll.ba_size_set, PipeTransitionAll.ba_size_set]
    exact hlt _ (I_lt _)
  have hvy : V.ram.get! P.y = y := by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) st).get! P.y = y
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => nys e.symm)]
    apply PipeTransitionAll.ba_get_set_self
    rw [PipeTransitionAll.ba_size_set]
    exact hlt _ hPy
  have hvx : V.ram.get! P.x = x := by
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) st).get! P.x = x
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => nxs e.symm), PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => nxy e.symm)]
    exact PipeTransitionAll.ba_get_set_self _ _ _ (hlt _ hPx)
  have ctl := RoomLand.controls_at_subs hM H.control hm sites hf pc
  have hc : ∀ j ∈ RoomLand.controlKeys sy m0, R.ram.get! j = V.ram.get! j := by
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
          · exact hc j (by rw [e]; simp [RoomLand.controlKeys])
          · subst e
            have ne := rx (I sy.Player_Y_HighPos) (by simp)
            rw [hvar _ ne.1.1 ne.1.2 ne.2, r1]
            exact hhi
          · exact hc j (by rw [e]; simp [RoomLand.controlKeys])
          · subst e
            rw [hvx]
            exact congrArg R.ram.get! ePx
          · subst e
            have ne := rx P.pg (by simp [P])
            rw [hvar _ ne.1.1 ne.1.2 ne.2, r2, ePg]
            exact hpg
          · subst e
            rw [hvy]
            exact congrArg R.ram.get! ePy
        · apply hc j
          unfold RoomLand.controlKeys
          exact List.mem_cons_of_mem _ (List.mem_append_left _ hj)
      · apply hc j
        rw [List.mem_singleton.mp hj]
        simp [RoomLand.controlKeys]
    · simp only [List.mem_singleton] at hj
      subst hj
      rw [hvst]
  have hVs : V.s = Q.s := variantW_s
  have hsQ : R.s = V.s := hs.trans (rs.symm.trans hVs.symm)
  have hxs' : x ∈ xsW := mem_xsW hx
  have hys' : y ∈ ysW := mem_ysW hy1 hy2
  have hsts : st ∈ ([0, 1, 2] : List UInt8) := by
    have h3 : st.toNat ≤ 2 := hst
    have : st = 0 ∨ st = 1 ∨ st = 2 := by
      rcases Nat.lt_or_ge st.toNat 1 with h | h
      · left; exact UInt8.toNat_inj.mp (by simp; omega)
      · rcases Nat.lt_or_ge st.toNat 2 with h' | h'
        · right; left; exact UInt8.toNat_inj.mp (by simp; omega)
        · right; right; exact UInt8.toNat_inj.mp (by simp; omega)
    rcases this with e | e | e <;> simp [e]
  have h1 : check1 sy (Rom.of m0) (ScreenPage.placesR sy nm m0) P (SideFrame.screenI sy m0) (RoomMap.mapRef m0) R 3000 = true := by
    rw [check1_eq hsQ hk]
    exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp H.family1 y hys') x hxs') st hsts
  have h2 : ∀ v ∈ speeds, check2 sy (Rom.of m0) R.s v 200 = true := by
    intro v hv'
    rw [hs, ← rs]
    exact List.all_eq_true.mp H.family2 v hv'
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
    show (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) st).get! j = (((Q.ram.set! P.x x).set! P.y y).set! (I sy.Player_State) 0).get! j
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => hne e.symm), PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => hne e.symm)]
  have hcell := cells_of_familyW H.cells hxs' hys' hcoords
  have hat : At (Rom.of m0) (cutW sy (Rom.of m0) (ScreenPage.placesR sy nm m0) P (SideFrame.screenI sy m0) (RoomMap.mapRef m0) R) R :=
    at_cutW hg pc hsolid (fun j hj => (hcell j hj).1) (fun j hj => (hcell j hj).2) hv
  exact wall_end h1 h2 hat hxs

/-! ## From `retBG` to the frame's end: a walk of the whole frame of the room -/

section
open PipeTransition (frame)
open PipeTransitionAll (Names)
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK PlacesOK CfgS RoomCond)
open RoomVert (Ph walkV OKV)

/-- the bytes that the rest of the frame keeps after `retBG`: the speed, the horizontal position and page, the state and the height -/
def hW (sy : Syms) : List Nat := [I sy.Player_X_Speed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.Player_State, I sy.Player_Y_Position]

/-- the step of `A` may write a byte of `hW`: not the erase of a coin, which writes in the block buffers -/
def mayWriteW (sy : Syms) (E : Env) (P : Places) (A : AS) : Bool :=
  !(A.pc == P.erase && !A.nmi) && !StepWrites.keepOK E (fun i => (hW sy).contains i) A

/-- the bit says that the frame came to `rb` and that no step has written the bytes of `hW` since. A step that may write them drops the bit and marks the state `[1]`; such a
state must end the frame out of the player's routine (`finW`). The walk asks that the frame comes to `rb` once. -/
def phW (sy : Syms) (E : Env) (P : Places) (rb : UInt16) : Ph where
  zone := fun A =>
    if A.pc == rb && !A.spent && A.log.isEmpty then [{ A with spent := true }]
    else if A.spent && mayWriteW sy E P A then [{ A with spent := false, log := [1] }]
    else [A]
  pre := fun A => !(A.pc == rb && (A.spent || !A.log.isEmpty))
  ok := fun A => !A.spent || !mayWriteW sy E P A

/-- at the frame's end: a state whose bytes of `hW` may have been written after `rb` ends out of the player's routine: the routine byte is known and is not the reference's -/
def finW (P : Places) (r : Machine) (B : AS) : Bool :=
  B.log != [1] || (decide (P.rtI < 2048) && (B.getK P.rtI).isK && (B.getK P.rtI).v != r.ram.get! P.rtI)

/-- the bytes of `hW` are out of the block buffers -/
def apartW (sy : Syms) (P : Places) : Bool :=
  (hW sy).all (fun x => decide (x < P.bufLo) || decide (P.bufLo + P.bufN ≤ x))

/-- a piece with the bit, that meets `ok`, keeps the bytes of `hW` over its step -/
theorem keepW_step {sy : Syms} {E : Env} {F : Nat × UInt8} {P : Places} {rb : UInt16} {A : AS} {y : Machine} (hO : PlacesOK E P) (hap : apartW sy P = true)
    (hs : Sim E F A y) (hh : SiteOK P y) (hok : (phW sy E P rb).ok A = true) (hb : A.spent = true) :
    ∀ x ∈ hW sy, (PipeTransitionAll.go step y).2.ram.get! x = y.ram.get! x := by
  intro x hx
  have h1 : mayWriteW sy E P A = false := by simpa [phW, hb] using hok
  unfold mayWriteW at h1
  cases hc : (A.pc == P.erase && !A.nmi) with
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    simp only [apartW, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hap
    exact RoomVert.erase_keep hO hs hc.2 hc.1 hh (hap x hx)
  | false =>
    rw [hc] at h1
    simp only [Bool.not_false, Bool.true_and, Bool.not_eq_false'] at h1
    exact StepWrites.keep_step hs h1 x (List.contains_iff_mem.2 hx)

/-- **The frame from `rb` to its end.** If the frame comes to `rb` and ends in the player's routine, no step from there to its end writes the bytes of `hW`. The frame starts
in the room's condition, and each instruction meets `SiteOK`. -/
theorem after_G {sy : Syms} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat} {rb : UInt16} (h : OKV (phW sy E P rb) E P r K C Fu)
    (hfin : C.fin = finW P r) (hap : apartW sy P = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK P (trace m i j)) :
    ∀ j, (trace m i j).pc = rb → (trace m i j).frame = m.frame → (frame m i).ram.get! P.rtI = r.ram.get! P.rtI →
       ∀ x ∈ hW sy, (frame m i).ram.get! x = (trace m i j).ram.get! x := by
  obtain ⟨S, hw, hs, s1, s2, s3⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  let Φ : Nat → Bool → List Nat → Prop := fun j b l =>
    (∀ j₀, j₀ < j → (trace m i j₀).pc = rb → (b = true ∨ l ≠ [])) ∧
    (b = true → l = [] ∧ ∃ j₀, j₀ < j ∧ (trace m i j₀).pc = rb ∧ ∀ x ∈ hW sy, (trace m i j).ram.get! x = (trace m i j₀).ram.get! x) ∧
    (l = [] ∨ l = [1])
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phW sy E P rb).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    show ∃ A₁ ∈ (if A'.pc == rb && !A'.spent && A'.log.isEmpty then [{ A' with spent := true }]
      else if A'.spent && mayWriteW sy E P A' then [{ A' with spent := false, log := [1] }] else [A']), _
    split
    · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr true A'.log⟩
    · split
      · exact ⟨_, List.mem_singleton.2 rfl, RoomVert.sim_bits hsx hr false [1]⟩
      · exact ⟨A', List.mem_singleton.2 rfl, hsx⟩
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phW sy E P rb).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phW sy E P rb).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p1, p2, p4⟩ hs' hf hr hA₁ hs₁ hok
    have hpc : (trace m i j).pc = A'.pc := hs'.pc
    have keep : A₁.spent = true → ∀ x ∈ hW sy, (trace m i (j + 1)).ram.get! x = (trace m i j).ram.get! x := by
      intro hb x hx
      rw [RoomVert.trace_succ hf hs'.halted]
      have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
      exact keepW_step h.places hap hs₂ (hk j) hok hb x hx
    change A₁ ∈ (if A'.pc == rb && !A'.spent && A'.log.isEmpty then [{ A' with spent := true }]
      else if A'.spent && mayWriteW sy E P A' then [{ A' with spent := false, log := [1] }] else [A']) at hA₁
    split at hA₁
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
      obtain ⟨⟨hq, _⟩, hlg⟩ := hc
      obtain rfl := List.mem_singleton.1 hA₁
      have c1 : ({ A' with spent := true } : AS).spent = true := rfl
      refine ⟨fun _ _ _ => Or.inl rfl, fun _ => ⟨hlg, j, by omega, by rw [hpc, hq], keep c1⟩, Or.inl hlg⟩
    · rename_i hc
      split at hA₁
      · obtain rfl := List.mem_singleton.1 hA₁
        exact ⟨fun _ _ _ => Or.inr (by simp), fun h => by simp at h, Or.inr rfl⟩
      · obtain rfl := List.mem_singleton.1 hA₁
        refine ⟨fun j₀ hj₀ hq₀ => ?_, fun hb => ?_, p4⟩
        · rcases Nat.lt_or_ge j₀ j with hlt | hge
          · exact p1 j₀ hlt hq₀
          · rw [show j₀ = j by omega, hpc] at hq₀
            simp only [hq₀, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_and] at hc
            cases hsp : A₁.spent with
            | true => exact Or.inl rfl
            | false => exact Or.inr (hc hsp)
        · obtain ⟨l1, j₀, a1, a2, a3⟩ := p2 hb
          exact ⟨l1, j₀, by omega, a2, fun x hx => by rw [keep hb x hx]; exact a3 x hx⟩
  have h0 : Φ 0 S.spent S.log := by
    refine ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun hb => ?_, Or.inl s2⟩
    rw [s1] at hb
    cases hb
  obtain ⟨hall, J, hJ1, hJ2, hJ3, B, hB1, hB2, hB3⟩ := RoomVert.frame_of_walkV (Z := phW sy E P rb) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0 hstep
  have uniq : ∀ j j', j < j' → (trace m i j).pc = rb → (trace m i j').frame = m.frame → (trace m i j').pc ≠ rb := by
    intro j j' hlt hq hj' hq'
    obtain ⟨A, hsA, hpre, q1, _⟩ := hall j' hj'
    have hApc : A.pc = rb := by rw [← hsA.pc]; exact hq'
    simp only [phW, hApc, beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hpre
    rcases q1 j hlt hq with e | e
    · rw [hpre.1] at e
      cases e
    · exact e hpre.2
  intro jq hq hf hrt x hx
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
    simp only [finW, hl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB1
    obtain ⟨⟨a1, a2⟩, a3⟩ := hB1
    have e := isK_eq a2 (hB2.ram _ a1)
    rw [← hJ3, hrt] at e
    exact a3 e.symm
  obtain ⟨q1, q2, q4⟩ := hB3
  have only : ∀ j₀, j₀ < J → (trace m i j₀).pc = rb → j₀ = jq := by
    intro j₀ h1 h2
    rcases Nat.lt_trichotomy j₀ jq with e | e | e
    · exact absurd hq (uniq j₀ jq e h2 hf)
    · exact e
    · exact absurd h2 (uniq jq j₀ e hq (hJ2 j₀ h1))
  rcases q4 with e | e
  · rcases q1 jq hjJ hq with e2 | e2
    · obtain ⟨_, j₀, a1, a2, a3⟩ := q2 e2
      rw [only j₀ a1 a2] at a3
      rw [hJ3]
      exact a3 x hx
    · exact absurd e e2
  · exact absurd e hl1

/-- the walk from `retBG`, on the room -/
abbrev cfgW (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phW sy (ScreenPage.envR sy nm m0) (ScreenPage.placesR sy nm m0) (retBG sy (Rom.of m0))) (finW (ScreenPage.placesR sy nm m0) (ScreenPage.refR m0))
    (ScreenPage.placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0)

/-- the check of the walk from `retBG` -/
def checkW (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  RoomVert.walkCheckV sy (phW sy (ScreenPage.envR sy nm m0) (ScreenPage.placesR sy nm m0) (retBG sy (Rom.of m0))) (finW (ScreenPage.placesR sy nm m0) (ScreenPage.refR m0))
    (ScreenPage.placesR sy nm m0) (ScreenPage.aidsOf sy nm m0) (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0)

end

/-- **A frame of the room whose end of the move meets the conditions of `wall_at`, and that ends in the player's routine, ends with the state not 0, or with the state 0 at
the floor's height, or with the speed 0.** `wall_at` up to `retBG`, and the walk of the whole frame from there (`after_G`) to the frame's end. -/
theorem wall_frame {sy : Syms} {nm : PipeTransitionAll.Names} {m0 m : Machine} (H : Checks sy nm m0) (hcw : checkW sy nm m0 = true)
    (hap : apartW sy (ScreenPage.placesR sy nm m0) = true) (hM : RoomMap.MapFacts sy nm m0) {input : UInt8} {n : Nat}
    (hm : ScreenPage.RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nm m0) (PipeEntryRule.trace m input j))
    {idle : UInt16} (hidle : idleAt (Rom.of m0) idle = true)
    (htime : ∀ j, (PipeEntryRule.trace m input j).pc ≠ idle → (PipeEntryRule.trace m input j).fdot ≤ dotsPerFrame - 64)
    (hf : (PipeEntryRule.trace m input n).frame = m.frame) (pc : (PipeEntryRule.trace m input n).pc = sy.PlayerSubs)
    (hg : Good (Rom.of m0) (PipeEntryRule.trace m input n)) (hs : (PipeEntryRule.trace m input n).s = ctrlStack sy m0)
    (hsolid : RoomBlocks.Solid (ScreenPage.placesR sy nm m0) (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) (RoomMap.mapRef m0) (PipeEntryRule.trace m input n))
    (hhi : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_HighPos) = 1)
    (hpg : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_PageLoc) = 0)
    (hx : ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Position)).toNat < 16)
    (hy1 : 32 ≤ ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Position)).toNat)
    (hy2 : ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Position)).toNat < 207)
    (hst : ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_State)).toNat ≤ 2)
    (hv : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0)
    (hxs : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Speed) ∈ speeds)
    (hrt : (PipeTransition.frame m input).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    (PipeTransition.frame m input).ram.get! (I sy.Player_State) ≠ 0 ∨
      ((PipeTransition.frame m input).ram.get! (I sy.Player_State) = 0 ∧ (PipeTransition.frame m input).ram.get! (I sy.Player_Y_Position) = floorY sy) ∨
      (PipeTransition.frame m input).ram.get! (I sy.Player_X_Speed) = 0 := by
  obtain ⟨k, _, hpc, _, hin, hend⟩ := wall_at H hM hm sites hf pc hg hs hsolid hhi hpg hx hy1 hy2 hst hv hxs
  obtain ⟨htr, hfr⟩ := FrameModel.trace_inFrame hidle hf hin htime k (Nat.le_refl k)
  have hO := RoomVert.okV_of_check hcw
  have hkeep := after_G hO RoomVert.cfgOfV_fin hap hm sites (n + k) (by rw [htr]; exact hpc) hfr hrt
  have e : ∀ x ∈ hW sy, (PipeTransition.frame m input).ram.get! x = (stepN k (PipeEntryRule.trace m input n)).ram.get! x := fun x hx => by
    rw [hkeep x hx, htr]
  rw [e _ (by simp [hW]), e _ (by simp [hW]), e _ (by simp [hW])]
  exact hend

/-! ## One frame of `hstep` from a state that moves left fast -/

section
open Potential (HS HIn hstep inD inputs inputsN statesFd norm normIdem speedsComplete V mem_bytes)

/-- from every state with the facing `fd` and `V ≤ −w`, one frame of `hstep` with every normalized input leaves the speed negative and in `speeds` -/
def negCheck (sy : Syms) (m : Machine) (w : Int) (fd : UInt8) : Bool :=
  (statesFd sy fd).all fun s => !decide (V s ≤ -w) || inputsN.all fun i =>
    decide (sbyte (hstep sy m s i).v < 0) && speeds.contains (hstep sy m s i).v

/-- **From a state of the domain that moves left at `w` or more (`V ≤ −w`), one frame of `hstep` with any input leaves the speed negative and one of `speeds`**. With
`w = standV` this is what the field `stand_fast` gives on the frame before a stand in the fall. -/
theorem neg_of_check {sy : Syms} {m : Machine} {w : Int} (hsp : speedsComplete sy = true) (hn : normIdem = true)
    (h1 : negCheck sy m w 1 = true) (h2 : negCheck sy m w 2 = true) (h3 : negCheck sy m w 3 = true) :
    ∀ s, inD sy s = true → V s ≤ -w → ∀ i ∈ inputs, sbyte (hstep sy m s i).v < 0 ∧ (hstep sy m s i).v ∈ speeds := by
  intro s hD hV i hi
  obtain ⟨v, f, fd, md, rs⟩ := s
  simp only [Potential.inD, Bool.and_eq_true, List.contains_iff_mem] at hD
  obtain ⟨⟨⟨hv, hfd⟩, hmd⟩, hrs⟩ := hD
  have hvs : v ∈ TopSpeed.speedsB sy := by
    simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_iff_mem] at hsp
    rcases hsp v (mem_bytes v) with h | h
    · rw [h] at hv; exact absurd hv (by decide)
    · exact h
  have hmem : ({ v, f, fd, md, rs } : HS) ∈ statesFd sy fd :=
    List.mem_flatMap.2 ⟨v, hvs, List.mem_flatMap.2 ⟨f, mem_bytes f,
      List.mem_flatMap.2 ⟨md, hmd, List.mem_map.2 ⟨rs, hrs, rfl⟩⟩⟩⟩
  have hall : negCheck sy m w fd = true := by
    simp only [Potential.facings, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with h | h | h <;> subst h
    · exact h1
    · exact h2
    · exact h3
  simp only [negCheck, List.all_eq_true] at hall
  have hc := hall _ hmem
  have hin : norm i ∈ inputsN := List.mem_eraseDups.2 (List.mem_map.2 ⟨i, hi, rfl⟩)
  have hid : norm (norm i) = norm i := by
    simp only [normIdem, List.all_eq_true, beq_iff_eq] at hn
    exact hn i hi
  have e : hstep sy m { v, f, fd, md, rs } (norm i) = hstep sy m { v, f, fd, md, rs } i := by
    unfold Potential.hstep
    rw [hid]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true] at hc
  rcases hc with hc | hc
  · exact absurd hV hc
  · have h4 := hc _ hin
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h4
    rw [e] at h4
    exact h4

end

/-! ## The link to `hstep`, for a stand before the end of the fall -/

section
open RoomJoin

/-- **Before `C + fall`, a frame of the room that ends standing does not follow `hstep`, if its end of the move with a speed of `speeds` gives the speed 0 at the frame's
end** (`hq`: what `wall_frame` gives where the other conditions of `wall_at` hold). Under `Follow` the speed at the frame's end is that of `hstep`. The field `stand_fast`
puts the frame before a stand in the fall at `V ≤ −standV`, so `neg` (`neg_of_check`) makes that speed negative and one of `speeds`. The field `clean` makes the speed at
the frame's end the speed at the end of the move, or 0; it is not 0, so it is the speed at the end of the move, and `hq` gives 0 at the end: a contradiction. Uses the fields
`stand_fast`, `clean`, `read_hs`, `farNear` (through `far_inD`), not `stand_wall`. -/
theorem not_follow_of {sy : Syms} {m : Machine} {N : Nums} {S : FrameKeep.RealRun} {b lim : Nat} (r : RoomRun sy m N S b lim) (H : RoomJoin.Checks sy m N)
    (hr : r.InRoom) (st : StartAt sy N (r.fe r.C))
    (neg : ∀ s, Potential.inD sy s = true → Potential.V s ≤ -N.standV → ∀ i ∈ Potential.inputs,
      sbyte (Potential.hstep sy m s i).v < 0 ∧ (Potential.hstep sy m s i).v ∈ speeds)
    {n : Nat} (hC : r.C ≤ n) (h1 : n + 1 < r.C + N.fall) (h0 : (r.fr.vs (n + 1)).st = 0)
    (hQ : ∃ j, r.arr n ≤ j ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs)
    (hq : ∀ j, r.arr n ≤ j → (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs →
      peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_X_Speed ∈ speeds →
      peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Speed = 0) :
    ¬Follow sy m r.fr n := by
  intro hf
  have hle := H.nums.fall_le
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have ht : n < r.t0 := by omega
  have hsf := r.stand_fast n hC h1 h0
  have hD : Potential.inD sy (r.fr.hs n) = true := by
    have h := (r.far_inD H hr st (n - r.C) (by omega)).2
    rwa [show r.C + (n - r.C) = n by omega] at h
  have hn := neg (r.fr.hs n) hD (by omega) (r.fr.inp (n + 1)) hf.1
  rw [← hf.2.1] at hn
  have hv : (r.fr.hs (n + 1)).v = peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Speed := by
    rw [r.hs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
    rfl
  rw [hv] at hn
  obtain ⟨hneg, hsp⟩ := hn
  have hne : peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Speed ≠ 0 := fun e => by
    rw [e] at hneg
    exact absurd hneg (by decide)
  obtain ⟨j, hj1, hj2⟩ := hQ
  have heq : peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Speed = peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_X_Speed := by
    rcases r.clean n hC ht with hc | ⟨_, hc⟩
    · exact hc.after j hj1 hj2 _ (by simp [FrameModel.hBytes])
    · rcases (hc.collide j hj1 hj2).v with e | e
      · exact e
      · exact absurd e hne
  have hin : peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_X_Speed ∈ speeds := by
    rw [← heq]
    exact hsp
  exact hne (hq j hj1 hj2 hin)

end

end Smbrta.RoomWall
