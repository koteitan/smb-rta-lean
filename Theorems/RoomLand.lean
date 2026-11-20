import Theorems.RoomBlocks
import Theorems.RoomCollision

/-! # The landing frame of the room's first fall, from the end of the move

A cut at the end of the move `Q` (the first `PlayerSubs` of the frame) samples the collision-disable flag, the vertical page, the routine, the three coordinates,
the five screen bytes and the jump spring from `Q`, and takes the head and foot cells of the three adder offsets from the reference map. The player's size and the
crouching flag are not sampled: the walk follows both of their branches. A walk from the cut that ends at the side check with the state 0 and the landed height is a
local check (`check`); a finite family of such checks covers every machine with the same sampled values (`check_of_family`), and a successful check gives the actual
machine standing at the side check (`land`). Which machines meet the cut at the actual landing frame is not proved here. There is no game data in this file.
Page: `1-1/c-7-5-12-RoomLand.md`. -/
namespace Smbrta.RoomLand
open FrameModel

/-- the collision-disable flag: the operand of the first load of the player's collision routine -/
def disable (sy : Syms) (E : Rom) : Nat := I (E.w (sy.PlayerBGCollision + 1))

/-- the cell that the collision routine reads with the offset index `index`, from the coordinates of `Q` -/
def cell (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (Q : Machine) (index : UInt8) : Nat :=
  I (RoomCollision.readAddress E B P {Q with y := index})

/-- `Q` with the horizontal coordinate `x` -/
def variant (P : RoomCollision.Places) (Q : Machine) (x : UInt8) : Machine :=
  {Q with ram := Q.ram.set! P.x x}

/-- the bytes the cut samples at `Q` -/
def keys (sy : Syms) (E : Rom) (P : RoomCollision.Places) (screen : List Nat) : List Nat :=
  [disable sy E, I sy.Player_Y_HighPos, I sy.GameEngineSubroutine, P.x, P.pg, P.y] ++ screen ++ [I sy.JumpspringAnimCtrl]

/-- the head cell and the two foot cells of each of the three adder offsets, computed from `Q` -/
def cells (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (Q : Machine) : List Nat :=
  ([0, 1, 2] : List UInt16).flatMap fun o =>
    let e := E.b (sy.BlockBufferAdderData + o)
    [cell E B P Q e, cell E B P Q (e + 1), cell E B P Q (e + 2)]

/-- the cut at `Q`: the sampled bytes from `Q`, the cells from `M`, and the vertical speed not negative -/
def cut (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine) : Cut :=
  {pc := sy.PlayerSubs, s := Q.s,
   K := (keys sy E P screen).map (fun j => (j, Q.ram.get! j)) ++ (cells sy E B P Q).map (fun j => (j, M.ram.get! j)),
   B := [(I sy.Player_Y_Speed, ⟨0, 0x80⟩)]}

/-- the goal: the side check, with the state 0 and the height `y` -/
def goal (sy : Syms) (sp y : UInt8) : Cut :=
  {pc := sy.DoPlayerSideCheck, s := sp, K := [(I sy.Player_State, 0), (I sy.Player_Y_Position, y)]}

/-- the walk from the cut to the side check -/
def check (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine)
    (sp y : UInt8) (fuel : Nat) : Bool :=
  walkT E (fun T => T.pc == sy.DoPlayerSideCheck) (goalC (goal sy sp y) []) fuel (startQ (cut sy E B P screen M Q))

/-- the walk for every horizontal coordinate of a list, from one machine -/
def family (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine)
    (xs : List UInt8) (sp y : UInt8) (fuel : Nat) : Bool :=
  xs.all fun x => check sy E B P screen M (variant P Q x) sp y fuel

/-- the cells of every machine of the family lie in the block buffers and are not coins on `M` -/
def cellsOK (sy : Syms) (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places) (M Q : Machine) (cs : List UInt8) (xs : List UInt8) : Bool :=
  xs.all fun x => (cells sy E B P (variant P Q x)).all fun j =>
    decide (B.bufLo ≤ j ∧ j < B.bufLo + B.bufN) && !cs.contains (M.ram.get! j)

/-- **The machine at `Q` meets the cut**: the sampled entries hold by construction; the cells need the solid map at `Q`, their bounds and no coin. -/
theorem at_cut {sy : Syms} {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M Q : Machine} {cs : List UInt8}
    (hg : Good E Q) (hp : Q.pc = sy.PlayerSubs) (hs : RoomBlocks.Solid B cs M Q)
    (hb : ∀ j ∈ cells sy E B P Q, B.bufLo ≤ j ∧ j < B.bufLo + B.bufN)
    (hn : ∀ j ∈ cells sy E B P Q, M.ram.get! j ∉ cs)
    (hv : Q.ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0) :
    At E (cut sy E B P screen M Q) Q := by
  refine {good := hg, pc := hp, s := rfl, K := ?_, B := ?_, ra := ?_, x := ?_, cf := ?_}
  · intro p hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
      rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
      exact hs j (hb j hj).1 (hb j hj).2 (hn j hj)
  · intro p hm
    simp only [cut, List.mem_singleton] at hm
    subst hm
    show Q.ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0 &&& 0x80
    rw [hv]
    rfl
  · simp [cut]
  · simp [cut]
  · simp [cut]

/-- the cells depend only on the coordinates -/
theorem cells_eq {sy : Syms} {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places} {Q R : Machine}
    (coords : ∀ j ∈ RoomCollision.coords P, Q.ram.get! j = R.ram.get! j) :
    cells sy E B P Q = cells sy E B P R := by
  have ce : ∀ index, cell E B P Q index = cell E B P R index := by
    intro index
    unfold cell
    exact congrArg I (RoomCollision.readAddress_from_coords (E := E) (B := B) (R := {Q with y := index}) (Q := R) coords)
  simp only [cells, ce]

/-- the cut depends only on its sampled bytes and the stack pointer -/
theorem cut_eq {sy : Syms} {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M Q R : Machine}
    (sp : Q.s = R.s) (same : ∀ j ∈ keys sy E P screen, Q.ram.get! j = R.ram.get! j) :
    cut sy E B P screen M Q = cut sy E B P screen M R := by
  have coords : ∀ j ∈ RoomCollision.coords P, Q.ram.get! j = R.ram.get! j := by
    intro j hj
    apply same j
    simp only [RoomCollision.coords, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [keys]
  have ks : (keys sy E P screen).map (fun j => (j, Q.ram.get! j)) = (keys sy E P screen).map (fun j => (j, R.ram.get! j)) := by
    apply List.map_congr_left
    intro j hj
    rw [same j hj]
  simp only [cut, sp, ks, cells_eq (sy := sy) (E := E) (B := B) coords]

/-- a family check applies to every machine with the same sampled bytes and stack pointer as one of its machines -/
theorem check_of_family {sy : Syms} {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M Q R : Machine}
    {xs : List UInt8} {x : UInt8} {sp y : UInt8} {fuel : Nat}
    (hc : family sy E B P screen M Q xs sp y fuel = true) (hx : x ∈ xs) (hs : R.s = Q.s)
    (hk : ∀ j ∈ keys sy E P screen, R.ram.get! j = (variant P Q x).ram.get! j) :
    check sy E B P screen M R sp y fuel = true := by
  have he := cut_eq (B := B) (M := M) (Q := R) (R := variant P Q x) hs hk
  unfold check
  rw [he]
  exact (List.all_eq_true.mp hc) x hx

/-- the cells of a family check: bounds and no coin, for every machine with the same coordinates -/
theorem cells_of_family {sy : Syms} {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places} {M Q R : Machine} {cs xs : List UInt8} {x : UInt8}
    (hc : cellsOK sy E B P M Q cs xs = true) (hx : x ∈ xs)
    (hk : ∀ j ∈ RoomCollision.coords P, R.ram.get! j = (variant P Q x).ram.get! j) :
    ∀ j ∈ cells sy E B P R, (B.bufLo ≤ j ∧ j < B.bufLo + B.bufN) ∧ M.ram.get! j ∉ cs := by
  intro j hj
  rw [cells_eq hk] at hj
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc x hx) j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1, fun hm => by
    have e := List.contains_iff_mem.mpr hm
    rw [h.2] at e
    cases e⟩

/-- **A successful check lands the actual machine**: from `Q` it comes to the side check within `fuel` steps, in its frame, with the state 0 and the height `y`. -/
theorem land {sy : Syms} {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places} {screen : List Nat} {M R : Machine} {sp y : UInt8} {fuel : Nat}
    (hc : check sy E B P screen M R sp y fuel = true) (hr : At E (cut sy E B P screen M R) R) :
    ∃ k, k ≤ fuel ∧ (stepN k R).pc = sy.DoPlayerSideCheck ∧ (stepN k R).s = sp ∧
      (stepN k R).ram.get! (I sy.Player_State) = 0 ∧ (stepN k R).ram.get! (I sy.Player_Y_Position) = y ∧ InFrameN E R k := by
  obtain ⟨k, T, hk, _, hg, H, hh⟩ := walkT_spec fuel _ R R hc (lk_self hr)
  obtain ⟨ha, _, _⟩ := at_of_goal hg H
  exact ⟨k, hk, ha.pc, ha.s, ha.K _ (List.mem_cons_self ..), ha.K _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
    fun j hj => by obtain ⟨_, _, _, _, hi, _⟩ := hh j hj; exact hi⟩

/-! ## The values at `Q` from the room's walk -/

/-- the bytes of the cut that the room's walk knows: the routine, the five screen bytes and the jump spring -/
def controlKeys (sy : Syms) (m0 : Machine) : List Nat := I sy.GameEngineSubroutine :: SideFrame.screenI sy m0 ++ [I sy.JumpspringAnimCtrl]

/-- the room's walk, watching these bytes at `PlayerSubs` -/
def controlPh (sy : Syms) (m0 : Machine) : RoomVert.Ph :=
  let ks := controlKeys sy m0
  let ref := ScreenPage.refR m0
  {zone := fun A => [A], ok := fun _ => true,
   pre := fun A => A.pc != sy.PlayerSubs || ks.all (fun j => RoomVert.knIs (A.getK j) (ref.ram.get! j))}

/-- the existing table of `RoomMap`, walked again with that watch; the search, the starts and the steps are those of `RoomMap` -/
def controlCheck (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) : Bool :=
  let C := RoomMap.cfgT sy nm m0
  let Z := controlPh sy m0
  C.t.all (RoomVert.walkV Z C ScreenPage.fuelS) &&
    (ScreenPage.startsR (ScreenPage.refR m0) (RoomMap.knownT sy nm m0)).all (RoomVert.walkV Z C ScreenPage.fuelS)

/-- **The routine, the screen bytes and the jump spring at an actual `PlayerSubs`** of a frame of the room: those of the reference, from the room's walk. No condition
at `Q` is assumed. -/
theorem controls_at_subs {sy : Syms} {nm : PipeTransitionAll.Names} {m0 m : Machine} {input : UInt8} {n : Nat}
    (H : RoomMap.MapFacts sy nm m0) (hc : controlCheck sy nm m0 = true)
    (hm : ScreenPage.RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nm m0) (PipeEntryRule.trace m input j))
    (hf : (PipeEntryRule.trace m input n).frame = m.frame)
    (pc : (PipeEntryRule.trace m input n).pc = sy.PlayerSubs) :
    ∀ j ∈ controlKeys sy m0, j < 2048 →
      (PipeEntryRule.trace m input n).ram.get! j = (ScreenPage.refR m0).ram.get! j := by
  have checks := hc
  simp only [controlCheck, Bool.and_eq_true] at checks
  let C := RoomMap.cfgT sy nm m0
  let Z := controlPh sy m0
  have h : RoomVert.OKV Z (ScreenPage.envR sy nm m0) (ScreenPage.placesR sy nm m0)
      (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) C ScreenPage.fuelS :=
    ⟨H.ok.places, H.ok.pad, H.ok.mask, H.ok.env, H.ok.pl, H.ok.ops, checks.1,
      fun S hs => List.all_eq_true.mp checks.2 S hs⟩
  obtain ⟨S, hw, hs, _, _, _⟩ := RoomVert.start_of_room h hm
  have cov := RoomVert.frame_of_walkV (fun _ _ _ => True)
    (by rw [h.env, h.pl]; exact h.places) h.table h.ops
    (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad)
    (fun A x _ hx => ⟨A, List.mem_singleton_self _, hx⟩) hw hs sites
    True.intro (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
  obtain ⟨A, ha, hpre, _⟩ := cov.1 n hf
  have ap : A.pc = sy.PlayerSubs := ha.pc.symm.trans pc
  have all : (controlKeys sy m0).all
      (fun j => RoomVert.knIs (A.getK j) ((ScreenPage.refR m0).ram.get! j)) = true := by
    simpa only [Z, controlPh, ap, bne_self_eq_false, Bool.false_or] using hpre
  intro j hj lt
  have kj := List.all_eq_true.mp all j hj
  simp only [RoomVert.knIs, Bool.and_eq_true, beq_iff_eq] at kj
  exact (TaintRun.isK_eq kj.1 (ha.ram j lt)).trans kj.2

/-! ## The reference machine and the checks -/

/-- the reference machine: the first `PlayerSubs` from the room's map machine with no input, with the height `y`; from the ROM alone, no input movie -/
def refQ (sy : Syms) (m0 : Machine) (y : UInt8) : Machine :=
  let M := RoomMap.mapRef m0
  let Q := (PipeEntryRule.firstAt sy.PlayerSubs 100000 {M with pad := 0}).getD M
  {Q with ram := Q.ram.set! (I sy.Player_Y_Position) y}

/-- what the reference machine has: the collision-disable flag 0, the vertical page 1, the page 0, the height `y`, the reference's routine, screen bytes and jump
spring, the stack of the player's routine; and the horizontal coordinate apart from the other sampled bytes -/
def refCheck (sy : Syms) (m0 : Machine) (y : UInt8) : Bool :=
  let E := Rom.of m0
  let P := RoomCollision.places sy m0
  let Q := refQ sy m0 y
  let ref := ScreenPage.refR m0
  Q.ram.size == 2048 && P.x == I sy.Player_X_Position && P.pg == I sy.Player_PageLoc && P.y == I sy.Player_Y_Position &&
  Q.ram.get! (disable sy E) == 0 && Q.ram.get! (I sy.Player_Y_HighPos) == 1 && Q.ram.get! P.pg == 0 && Q.ram.get! P.y == y &&
  (controlKeys sy m0).all (fun j => decide (j < 2048) && Q.ram.get! j == ref.ram.get! j) &&
  ([disable sy E, I sy.Player_Y_HighPos, P.pg, P.y] ++ controlKeys sy m0).all (fun j => j != P.x) &&
  Q.s == ctrlStack sy m0

/-- **The checks on the ROM**: the family of walks for the horizontal coordinates below `xB` at the height `y`, the cells, the room's walk with the watch, the reference -/
structure Checks (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) (xB : Nat) (y : UInt8) : Prop where
  family : family sy (Rom.of m0) (ScreenPage.placesR sy nm m0) (RoomCollision.places sy m0) (SideFrame.screenI sy m0) (RoomMap.mapRef m0) (refQ sy m0 y)
    ((List.range xB).map Nat.toUInt8) ((refQ sy m0 y).s - 2) (y &&& 0xF0) 2000 = true
  cells : cellsOK sy (Rom.of m0) (ScreenPage.placesR sy nm m0) (RoomCollision.places sy m0) (RoomMap.mapRef m0) (refQ sy m0 y)
    (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) ((List.range xB).map Nat.toUInt8) = true
  control : controlCheck sy nm m0 = true
  ref : refCheck sy m0 y = true
  xB : xB ≤ 256

/-- **At the end of the move of a frame of the room, with the collision-disable flag 0, the vertical page 1, the page 0, the horizontal coordinate below `xB`, the
height `y` and the vertical speed not negative, the player stands at the side check**, with the height `y` with its low four bits 0. The routine, the screen bytes and
the jump spring come from the room's walk; the cells from the solid map at `Q`; the stack and `Good` are hypotheses. -/
theorem stand_at {sy : Syms} {nm : PipeTransitionAll.Names} {m0 m : Machine} {xB : Nat} {y : UInt8} (H : Checks sy nm m0 xB y)
    (hM : RoomMap.MapFacts sy nm m0) {input : UInt8} {n : Nat}
    (hm : ScreenPage.RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nm m0) (PipeEntryRule.trace m input j))
    (hf : (PipeEntryRule.trace m input n).frame = m.frame) (pc : (PipeEntryRule.trace m input n).pc = sy.PlayerSubs)
    (hg : Good (Rom.of m0) (PipeEntryRule.trace m input n)) (hs : (PipeEntryRule.trace m input n).s = ctrlStack sy m0)
    (hsolid : RoomBlocks.Solid (ScreenPage.placesR sy nm m0) (RoomBlocks.coinsOf (ScreenPage.placesR sy nm m0)) (RoomMap.mapRef m0) (PipeEntryRule.trace m input n))
    (hdis : (PipeEntryRule.trace m input n).ram.get! (disable sy (Rom.of m0)) = 0)
    (hhi : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_HighPos) = 1)
    (hpg : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_PageLoc) = 0)
    (hx : ((PipeEntryRule.trace m input n).ram.get! (I sy.Player_X_Position)).toNat < xB)
    (hy : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Position) = y)
    (hv : (PipeEntryRule.trace m input n).ram.get! (I sy.Player_Y_Speed) &&& 0x80 = 0) :
    ∃ k, k ≤ 2000 ∧ (stepN k (PipeEntryRule.trace m input n)).pc = sy.DoPlayerSideCheck ∧
      (stepN k (PipeEntryRule.trace m input n)).ram.get! (I sy.Player_State) = 0 ∧
      (stepN k (PipeEntryRule.trace m input n)).ram.get! (I sy.Player_Y_Position) = y &&& 0xF0 ∧
      InFrameN (Rom.of m0) (PipeEntryRule.trace m input n) k := by
  have hr := H.ref
  simp only [refCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsz, ePx⟩, ePg⟩, ePy⟩, r0⟩, r1⟩, r2⟩, r3⟩, rc⟩, rx⟩, rs⟩ := hr
  let R := PipeEntryRule.trace m input n
  let Q := refQ sy m0 y
  let x := (R.ram.get! (I sy.Player_X_Position))
  let P := RoomCollision.places sy m0
  have hxs : x ∈ (List.range xB).map Nat.toUInt8 := by
    refine List.mem_map.2 ⟨x.toNat, List.mem_range.2 hx, ?_⟩
    simp
  have hvar : ∀ j, j ≠ P.x → (variant P Q x).ram.get! j = Q.ram.get! j := fun j hj =>
    PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => hj e.symm)
  have hvx : (variant P Q x).ram.get! P.x = x := by
    show (Q.ram.set! P.x x).get! P.x = x
    apply PipeTransitionAll.ba_get_set_self
    rw [hsz, ePx]
    exact PipeTransitionAll.mask_lt _
  have ctl := controls_at_subs hM H.control hm sites hf pc
  have hk : ∀ j ∈ keys sy (Rom.of m0) P (SideFrame.screenI sy m0), R.ram.get! j = (variant P Q x).ram.get! j := by
    intro j hj
    have hc : ∀ j ∈ controlKeys sy m0, R.ram.get! j = (variant P Q x).ram.get! j := by
      intro j hj
      have ne := rx j (List.mem_append_right _ hj)
      rw [hvar j ne, (rc j hj).2, ctl j hj (rc j hj).1]
    simp only [keys, List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hj
    rcases hj with e | e | e | e | e | e | e | e
    · subst e
      rw [hvar _ (rx _ (by simp)), r0]
      exact hdis
    · subst e
      rw [hvar _ (rx _ (by simp)), r1]
      exact hhi
    · exact hc j (by subst e; simp [controlKeys])
    · subst e
      rw [hvx]
      exact congrArg R.ram.get! ePx
    · subst e
      rw [hvar _ (rx _ (by simp [P])), r2, ePg]
      exact hpg
    · subst e
      rw [hvar _ (rx _ (by simp [P])), r3, ePy]
      exact hy
    · exact hc j (by simp [controlKeys, e])
    · exact hc j (by subst e; simp [controlKeys])
  have hsQ : R.s = Q.s := by rw [hs, rs]
  have hcheck := check_of_family H.family hxs hsQ hk
  have hcoords : ∀ j ∈ RoomCollision.coords P, R.ram.get! j = (variant P Q x).ram.get! j := by
    intro j hj
    apply hk j
    simp only [RoomCollision.coords, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [keys]
  have hcell := cells_of_family H.cells hxs hcoords
  have hat : At (Rom.of m0) (cut sy (Rom.of m0) (ScreenPage.placesR sy nm m0) P (SideFrame.screenI sy m0) (RoomMap.mapRef m0) R) R :=
    at_cut hg pc hsolid (fun j hj => (hcell j hj).1) (fun j hj => (hcell j hj).2) hv
  obtain ⟨k, hk1, hk2, _, hk4, hk5, hk6⟩ := land hcheck hat
  exact ⟨k, hk1, hk2, hk4, hk5, hk6⟩

end Smbrta.RoomLand
