import Theorems.RoomFootPrefix

/-! A small foot-prefix cut sampled at the movement end.
Only the two dynamically addressed map cells use reference values. -/
namespace Smbrta.RoomFootCut
open FrameModel

/-- The collision-disable operand is decoded from the first absolute load.
The prefix check itself validates the executed instructions. -/
def disable (sy : Syms) (E : Rom) : Nat := I (E.w (sy.PlayerBGCollision+1))

def keys (sy : Syms) (E : Rom) (P : RoomCollision.Places) (screen : List Nat) : List Nat :=
  [disable sy E,I sy.Player_Y_HighPos,I sy.GameEngineSubroutine,
   P.x,P.pg,P.y,I sy.PlayerSize] ++ screen

/-- The head index for the small-player branch. Its applicability remains
an obligation on the sampled size and control bytes, checked by the prefix. -/
def headIndex (sy : Syms) (E : Rom) : UInt8 := E.b (sy.BlockBufferAdderData+2)

def cell (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places)
    (Q : Machine) (index : UInt8) : Nat :=
  I (RoomCollision.readAddress E B P {Q with y := index})

def cells (sy : Syms) (E : Rom) (B : ScreenPage.Places)
    (P : RoomCollision.Places) (Q : Machine) (right : Bool) : List Nat :=
  let h := cell E B P Q (headIndex sy E)
  if right then [h,cell E B P Q (headIndex sy E+1)] else [h]

/-- Twelve sampled bytes and one or two map bytes, with no literal game data. -/
def cutQ (sy : Syms) (E : Rom) (B : ScreenPage.Places)
    (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine) (right : Bool) : Cut :=
  {pc := sy.PlayerSubs,s := Q.s,
   K := (keys sy E P screen).map (fun j => (j,Q.ram.get! j)) ++
        (cells sy E B P Q right).map (fun j => (j,M.ram.get! j))}

/-- All sampled entries hold by construction. Only the addressed map cells
need the existing solid-map invariant, bounds, and exclusion of coins. -/
theorem at_cutQ {sy : Syms} {E : Rom} {B : ScreenPage.Places}
    {P : RoomCollision.Places} {screen : List Nat} {M Q : Machine} {cs : List UInt8} {right : Bool}
    (hg : Good E Q) (hp : Q.pc = sy.PlayerSubs)
    (hs : RoomBlocks.Solid B cs M Q)
    (hb : ∀ j ∈ cells sy E B P Q right, B.bufLo ≤ j ∧ j < B.bufLo+B.bufN)
    (hn : ∀ j ∈ cells sy E B P Q right, M.ram.get! j ∉ cs) :
    At E (cutQ sy E B P screen M Q right) Q := by
  refine {good := hg,pc := hp,s := rfl,K := ?_,B := ?_,ra := ?_,x := ?_,cf := ?_}
  · intro p hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
      rfl
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      exact hs j (hb j hj).1 (hb j hj).2 (hn j hj)
  · simp [cutQ]
  · simp [cutQ]
  · simp [cutQ]
  · simp [cutQ]

/-- A full abstract byte at any exported walk state gives its concrete value.
This projects control bytes at Q, rather than reusing the frame-start condition. -/
theorem byte_of_sim {E : TaintRun.Env} {F : Nat × UInt8}
    {A : TaintRun.AS} {Q : Machine} {j : Nat} {v : UInt8}
    (hs : TaintRun.Sim E F A Q) (hj : j < 2048)
    (hk : (A.getK j).k = 255) (hv : (A.getK j).v = v) :
    Q.ram.get! j = v := by
  have h := TaintRun.isK_eq (by simp [TaintRun.AB.isK,hk]) (hs.ram j hj)
  exact h.trans hv

/-- A cut depends on its sampled keys and stack pointer, not other RAM. -/
theorem cutQ_eq {sy : Syms} {E : Rom} {B : ScreenPage.Places}
    {P : RoomCollision.Places} {screen : List Nat} {M Q R : Machine} {right : Bool}
    (sp : Q.s = R.s)
    (same : ∀ j ∈ keys sy E P screen, Q.ram.get! j = R.ram.get! j) :
    cutQ sy E B P screen M Q right = cutQ sy E B P screen M R right := by
  have coords : ∀ j ∈ RoomCollision.coords P, Q.ram.get! j = R.ram.get! j := by
    intro j hj
    apply same j
    simp only [RoomCollision.coords, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [keys]
  have ce : ∀ index, cell E B P Q index = cell E B P R index := by
    intro index
    unfold cell
    exact congrArg I (RoomCollision.readAddress_from_coords (E := E) (B := B) (R := {Q with y := index}) (Q := R) coords)
  have ks : (keys sy E P screen).map (fun j => (j,Q.ram.get! j)) =
      (keys sy E P screen).map (fun j => (j,R.ram.get! j)) := by
    apply List.map_congr_left
    intro j hj
    rw [same j hj]
  simp only [cutQ,sp,ks,cells,ce]

/-- Enumerate one varying coordinate without fixing unrelated machine bytes. -/
def variant (P : RoomCollision.Places) (Q : Machine) (x : UInt8) : Machine :=
  {Q with ram := Q.ram.set! P.x x}

def familyCheck (sy : Syms) (E : Rom) (B : ScreenPage.Places)
    (P : RoomCollision.Places) (screen : List Nat) (M Q : Machine)
    (xs : List UInt8) (right : Bool) (ret : UInt16) (sp index : UInt8) (fuel : Nat) : Bool :=
  xs.all fun x => RoomFootPrefix.check E P
    (cutQ sy E B P screen M (variant P Q x) right) ret sp index fuel

/-- A finite certificate applies to any state with the same sampled values.
The stack, controls and coordinates remain explicit pointwise obligations. -/
theorem check_of_family {sy : Syms} {E : Rom} {B : ScreenPage.Places}
    {P : RoomCollision.Places} {screen : List Nat} {M Q R : Machine}
    {xs : List UInt8} {x : UInt8} {right : Bool} {ret : UInt16} {sp index : UInt8} {fuel : Nat}
    (hc : familyCheck sy E B P screen M Q xs right ret sp index fuel = true)
    (hx : x ∈ xs) (hs : R.s = Q.s)
    (hk : ∀ j ∈ keys sy E P screen, R.ram.get! j = (variant P Q x).ram.get! j) :
    RoomFootPrefix.check E P (cutQ sy E B P screen M R right) ret sp index fuel = true := by
  have he := cutQ_eq (B := B) (M := M) (Q := R) (R := variant P Q x) (right := right) hs hk
  rw [he]
  exact (List.all_eq_true.mp hc) x hx

/-- A reproducible reference slice, independent of any input movie. -/
def referenceQ (sy : Syms) (m0 : Machine) (height : UInt8) : Machine :=
  let M := RoomMap.mapRef m0
  let Q := (PipeEntryRule.firstAt sy.PlayerSubs 100000 {M with pad := 0}).getD M
  {Q with ram := Q.ram.set! (I sy.Player_Y_Position) height}

/-- Select coordinates by map geometry: empty head, floor under both feet. -/
def floorXs (sy : Syms) (E : Rom) (B : ScreenPage.Places)
    (P : RoomCollision.Places) (M Q : Machine) (empty floor : UInt8) : List UInt8 :=
  (List.range 256).filterMap fun x =>
    let R := variant P Q x.toUInt8
    if M.ram.get! (cell E B P R (headIndex sy E)) == empty &&
       M.ram.get! (cell E B P R (headIndex sy E+1)) == floor &&
       M.ram.get! (cell E B P R (headIndex sy E+2)) == floor
    then some x.toUInt8 else none

/-- Validate both foot prefixes on the selected finite reference slice.
This does not assert that every actual landing belongs to the slice. -/
def referenceCheck (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine)
    (height empty floor : UInt8) (fuel : Nat) : Bool :=
  let E := Rom.of m0
  let P := RoomCollision.places sy m0
  let B := ScreenPage.placesR sy nm m0
  let M := RoomMap.mapRef m0
  let Q := referenceQ sy m0 height
  let xs := floorXs sy E B P M Q empty floor
  let first := PipeEntryRule.findOp m0 sy.DoFootCheck 0x20 20
  let second := ScreenPage.findJsr m0 (first+3) (E.w (first+1)) 64
  familyCheck sy E B P (SideFrame.screenI sy m0) M Q xs false (first+3) (Q.s-4) (headIndex sy E+1) fuel &&
  familyCheck sy E B P (SideFrame.screenI sy m0) M Q xs true (second+3) (Q.s-5) (headIndex sy E+2) fuel

/-- The routine byte and the five screen bytes already carried by RoomMap. -/
def controlKeys (sy : Syms) (m0 : Machine) : List Nat :=
  I sy.GameEngineSubroutine :: SideFrame.screenI sy m0

def controlPh (sy : Syms) (m0 : Machine) : RoomVert.Ph :=
  let ks := controlKeys sy m0
  let ref := ScreenPage.refR m0
  {zone := fun A => [A],ok := fun _ => true,
   pre := fun A => A.pc != sy.PlayerSubs ||
     ks.all (fun j => RoomVert.knIs (A.getK j) (ref.ram.get! j))}

/-- Recheck the existing RoomMap table with a pointwise observation at Q.
The search, start states, instruction guards and transition are unchanged. -/
def controlCheck (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) : Bool :=
  let C := RoomMap.cfgT sy nm m0
  let Z := controlPh sy m0
  C.t.all (RoomVert.walkV Z C ScreenPage.fuelS) &&
    (ScreenPage.startsR (ScreenPage.refR m0) (RoomMap.knownT sy nm m0)).all
      (RoomVert.walkV Z C ScreenPage.fuelS)

/-- Six control bytes at the actual PlayerSubs instruction, from the room's
existing walk and SiteOK. No condition at Q is assumed. -/
theorem controls_at_subs {sy : Syms} {nm : PipeTransitionAll.Names} {m0 m : Machine}
    {input : UInt8} {n : Nat}
    (H : RoomMap.MapFacts sy nm m0) (hc : controlCheck sy nm m0 = true)
    (hm : ScreenPage.RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) m)
    (sites : ∀ j, ScreenPage.SiteOK (ScreenPage.placesR sy nm m0) (PipeEntryRule.trace m input j))
    (hf : (PipeEntryRule.trace m input n).frame = m.frame)
    (pc : (PipeEntryRule.trace m input n).pc = sy.PlayerSubs) :
    ∀ j ∈ controlKeys sy m0, j < 2048 →
      (PipeEntryRule.trace m input n).ram.get! j = (ScreenPage.refR m0).ram.get! j := by
  have checks := hc
  simp only [controlCheck,Bool.and_eq_true] at checks
  let C := RoomMap.cfgT sy nm m0
  let Z := controlPh sy m0
  have h : RoomVert.OKV Z (ScreenPage.envR sy nm m0) (ScreenPage.placesR sy nm m0)
      (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) C ScreenPage.fuelS :=
    ⟨H.ok.places,H.ok.pad,H.ok.mask,H.ok.env,H.ok.pl,H.ok.ops,checks.1,
      fun S hs => List.all_eq_true.mp checks.2 S hs⟩
  obtain ⟨S,hw,hs,_,_,_⟩ := RoomVert.start_of_room h hm
  have cov := RoomVert.frame_of_walkV (fun _ _ _ => True)
    (by rw [h.env,h.pl]; exact h.places) h.table h.ops
    (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad)
    (fun A x _ hx => ⟨A,List.mem_singleton_self _,hx⟩) hw hs sites
    True.intro (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
  obtain ⟨A,ha,hpre,_⟩ := cov.1 n hf
  have ap : A.pc = sy.PlayerSubs := ha.pc.symm.trans pc
  have all : (controlKeys sy m0).all
      (fun j => RoomVert.knIs (A.getK j) ((ScreenPage.refR m0).ram.get! j)) = true := by
    simpa only [Z,controlPh,ap,bne_self_eq_false,Bool.false_or] using hpre
  intro j hj lt
  have kj := List.all_eq_true.mp all j hj
  simp only [RoomVert.knIs,Bool.and_eq_true,beq_iff_eq] at kj
  exact (TaintRun.isK_eq kj.1 (ha.ram j lt)).trans kj.2

/-- Geometry selected by floorXs supplies both actual reference foot bytes. -/
theorem floorXs_spec {sy : Syms} {E : Rom} {B : ScreenPage.Places}
    {P : RoomCollision.Places} {M Q : Machine} {empty floor x : UInt8}
    (hx : x ∈ floorXs sy E B P M Q empty floor) :
    M.ram.get! (cell E B P (variant P Q x) (headIndex sy E)) = empty ∧
    M.ram.get! (cell E B P (variant P Q x) (headIndex sy E+1)) = floor ∧
    M.ram.get! (cell E B P (variant P Q x) (headIndex sy E+2)) = floor := by
  obtain ⟨n,_,hn⟩ := List.mem_filterMap.mp hx
  dsimp only at hn
  split at hn
  · rename_i h
    have eq := Option.some.inj hn
    subst x
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using h
  · cases hn

/-- State immediately after the right-foot return: left tile on the stack,
right tile in A, coordinate nibble, nonnegative falling speed, no spring. -/
def landingCut (sy : Syms) (P : RoomCollision.Places) (ret : UInt16)
    (sp height floor : UInt8) : Cut :=
  {pc := ret,s := sp,ra := some floor,
   K := [(stkI (sp+1),floor),(P.saved,height &&& P.lowMask),
     (I sy.Player_Y_Position,height),(I sy.JumpspringAnimCtrl,0)],
   B := [(I sy.Player_Y_Speed,⟨0,128⟩)]}

def landingGoal (sy : Syms) (sp : UInt8) : Cut :=
  {pc := sy.DoPlayerSideCheck,s := sp+1,K := [(I sy.Player_State,0)]}

def landingCheck (sy : Syms) (E : Rom) (P : RoomCollision.Places)
    (ret : UInt16) (sp height floor : UInt8) (fuel : Nat) : Bool :=
  walkT E (fun T => T.pc == sy.DoPlayerSideCheck)
    (goalC (landingGoal sy sp) []) fuel (startQ (landingCut sy P ret sp height floor))

/-- The checked caller branch really writes standing before the side checks.
Later instructions and the local entry conditions remain separate obligations. -/
theorem landing_stores {sy : Syms} {E : Rom} {P : RoomCollision.Places}
    {ret : UInt16} {sp height floor : UInt8} {fuel : Nat} {R : Machine}
    (hc : landingCheck sy E P ret sp height floor fuel = true)
    (hr : At E (landingCut sy P ret sp height floor) R) :
    ∃ k, k ≤ fuel ∧ (stepN k R).pc = sy.DoPlayerSideCheck ∧
      (stepN k R).ram.get! (I sy.Player_State) = 0 ∧ InFrameN E R k := by
  obtain ⟨k,T,hk,_,hg,H,hh⟩ := walkT_spec fuel _ R R hc (lk_self hr)
  obtain ⟨ha,_,_⟩ := at_of_goal hg H
  exact ⟨k,hk,ha.pc,ha.K _ (List.mem_cons_self ..),
    fun j hj => by obtain ⟨_,_,_,_,hi,_⟩ := hh j hj; exact hi⟩

/-- Bounds and noncoin classification for a finite set of computed reads. -/
def cellsCheck (E : Rom) (B : ScreenPage.Places) (P : RoomCollision.Places)
    (M Q : Machine) (cs indices : List UInt8) : Bool :=
  indices.all fun index =>
    let j := cell E B P Q index
    decide (B.bufLo ≤ j ∧ j < B.bufLo+B.bufN) && !cs.contains (M.ram.get! j)

theorem cellsCheck_spec {E : Rom} {B : ScreenPage.Places} {P : RoomCollision.Places}
    {M Q : Machine} {cs indices : List UInt8} (hc : cellsCheck E B P M Q cs indices = true)
    {index : UInt8} (hi : index ∈ indices) :
    B.bufLo ≤ cell E B P Q index ∧ cell E B P Q index < B.bufLo+B.bufN ∧
      M.ram.get! (cell E B P Q index) ∉ cs := by
  have h := List.all_eq_true.mp hc index hi
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  exact ⟨h.1.1,h.1.2,fun hm => by
    have e := List.contains_iff_mem.mpr hm
    rw [h.2] at e
    cases e⟩

def referenceCellsCheck (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine)
    (height empty floor : UInt8) : Bool :=
  let E := Rom.of m0
  let P := RoomCollision.places sy m0
  let B := ScreenPage.placesR sy nm m0
  let M := RoomMap.mapRef m0
  let Q := referenceQ sy m0 height
  let h := headIndex sy E
  (floorXs sy E B P M Q empty floor).all fun x =>
    cellsCheck E B P M (variant P Q x) (RoomBlocks.coinsOf B) [h,h+1,h+2]

end Smbrta.RoomFootCut
