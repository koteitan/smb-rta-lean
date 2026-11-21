import Theorems.PoleTileFar

/-!
# The pole's tiles at the touch: the height kept inside the collision routine, from two bytes the frames keep

`PoleTileHeight` protects the height inside the collision routine, and for that it assumes `YAt` on each instruction of the touch's frame up to the write: inside the
routine, a store through an index or a pointer does not write the height. The walk could not show it at 20 stores: 16 stores of the block objects through the index `X`,
which is the block objects' offset; 3 stores through the block buffer's pointer, whose high byte the walk forgot; the store of a score digit through `Y`, which comes from
the player's number.

Here the walk knows these values:
* two bytes are watched from control to the touch's frame (`watchB`): the block objects' offset has its bits 1 to 7 at 0 (the game only flips its bit 0), and the
  player's number is 0. They are known at control (the rows of the change, `PoleTileCtl.watchCheckK`, `PoleTileCtl.watch₀`), and every frame in control keeps them (the walk of the frames,
  `keepCheckOfY`), when no store through an index or a pointer writes them (`KeepB`, a condition on single instructions of the kind of `FrameKeep.CleanK`);
* the walk of the touch's frame starts with them and protects them (`poleY`);
* inside the collision routine, the walk protects the pointer's high byte and the objects' offset too (`zoneB`, `GZ`), and it tests each store through an index or
  a pointer there (`zoneTest`): its target, from what the walk knows of the index or the pointer (`rangeW`), is none of these bytes nor the height.

So `YAt` is proved on the way: the field `yKeep` is gone. What is assumed in its place is `KeepB` on each instruction of the frames up to the touch.

There is no game data in this file. Page: `1-1/f-6-17-6-PoleTileKeep.md`.
-/

namespace Smbrta.PoleTileKeep

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeWrites (Guard FrameStart okRt startG fuelG knownOf wTarget opAt)
open FrameKeep (CleanK Watch Watched)
open TaintRun (AS Env Sim AB AM aRows)
open PoleTileWalk (ColMap BufAt HypR inBufB okS pairOK)
open PoleTileRead (TR)
open PoleTileHeight (HP GY YAt InZone hpOf ZoneH)
open PoleTileFar (TileCol preF readPF normF isCutF)

/-! ## The two bytes -/

/-- a word of the ROM -/
def romW (m0 : Machine) (a : UInt16) : UInt16 := (romByte m0 a).toUInt16 ||| ((romByte m0 (a + 1)).toUInt16 <<< 8)

/-- the block objects' offset: the operand of the first `LDX abs` of the floatey numbers' routine -/
def sprI (sy : Syms) (m0 : Machine) : Nat := (romW m0 (PipeEntryRule.findOp m0 sy.FloateyNumbersRoutine 0xAE 128 + 1) &&& 0x7FF).toNat

/-- the player's number: the operand of the `LDY abs` six bytes before the routine that prints a number -/
def curI (sy : Syms) (m0 : Machine) : Nat := (romW m0 (sy.UpdateNumber - 5) &&& 0x7FF).toNat

/-- the two bytes -/
def bI (sy : Syms) (m0 : Machine) : List Nat := [sprI sy m0, curI sy m0]

/-- **The watched bits of the two bytes**: bits 1 to 7 of the block objects' offset are 0, the player's number is 0 -/
def watchB (sy : Syms) (m0 : Machine) : List Watch := [(sprI sy m0, 0xFE, 0), (curI sy m0, 0xFF, 0)]

/-! ## The ranges of a store's target -/

/-- the targets that a store through an index or a pointer may have, from what the piece knows: `STA`/`STY`/`DEC`/`INC` zero page with `X` when the sum does not go
round the zero page, `STA (zp),Y` -/
def rangeW (E : Env) (A : AS) : Option (Nat × Nat) :=
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
  if op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6 then
    if z.toNat + A.x.maxv.toNat < 256 then some (z.toNat + A.x.minv.toNat, z.toNat + A.x.maxv.toNat) else none
  else if op == 0x91 then
    let lo := A.getK z.toNat
    let hi := A.getK (z + 1).toNat
    some (lo.minv.toNat + 256 * hi.minv.toNat + A.y.minv.toNat, lo.maxv.toNat + 256 * hi.maxv.toNat + A.y.maxv.toNat)
  else none

/-- every address of the range is past the RAM, or in one copy of the RAM with its RAM index none of `P` -/
def avoidR (P : List Nat) (r : Nat × Nat) : Bool :=
  decide (r.2 < 65536) && (decide (0x2000 ≤ r.1) || (decide (r.1 / 2048 = r.2 / 2048) && P.all fun i => decide (i < r.1 % 2048) || decide (r.2 % 2048 < i)))

/-- the store's target is none of `P`, by the range -/
def rangeOK (E : Env) (P : List Nat) (A : AS) : Bool :=
  decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && match rangeW E A with
    | some r => avoidR P r
    | none => false

/-! ## The walk of the touch's frame -/

/-- the pole with the two bytes protected -/
def poleY (sy : Syms) (m0 : Machine) : Pole :=
  let T := poleOf sy m0
  { T with G := { T.G with prot := bI sy m0 ++ T.G.prot } }

/-- the objects' offset: the operand of the `LDX zp` at the end of the routine that prints a number -/
def objI (sy : Syms) (m0 : Machine) : Nat := (romByte m0 (sy.NoZSup + 1)).toNat

/-- **The bytes protected inside the collision routine besides the height**: the high byte of the block buffer's pointer, the objects' offset -/
def zoneB (sy : Syms) (m0 : Machine) : List Nat := [(spotsF sy m0).ptrI + 1, objI sy m0]

/-- **The guard inside the collision routine**: `PoleTileHeight.GY` with the bytes `Z` protected too -/
def GZ (T : Pole) (H : HP) (Z : List Nat) : Guard := { GY T H with prot := Z ++ (GY T H).prot }

/-- the bytes that the test keeps off: the height and the bytes `Z` -/
def zP (H : HP) (Z : List Nat) : List Nat := H.R.yI :: Z

/-- **The test inside the collision routine**: a store through an index or a pointer writes neither the height nor a byte of `Z`, as far as the piece says -/
def zoneTest (T : Pole) (H : HP) (Z : List Nat) (E : Env) (A : AS) : Bool :=
  !PipeWrites.inZone T.G A || !PoleTileWalk.idxOps.contains (E.prg.get! (A.pc &&& E.mask).toNat) ||
    (!A.nmi && StepWrites.keepOK E (fun i => (zP H Z).contains i) A) || rangeOK E (zP H Z) A

/-- **The steps of the walk**: those of `PoleTileHeight.kstepH`, with the guard `GZ` inside the collision routine -/
def kstepZ (T : Pole) (H : HP) (Z : List Nat) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if T.ps.contains A.pc then kstepT T E ops A
  else if PipeWrites.inZone T.G A then FrameKeep.kstep T.K (GZ T H Z) E ops A
  else FrameKeep.kstep T.K T.GP E ops A

/-! ## Finding the table: a search, no part of the proof -/

/-- what the search forgets: as `PoleTileFar.normF`, but inside the collision routine it keeps the bytes `Z`, and it forgets the registers and the flags in the places `R` (the
routines that print a number: with the player's number known they would make a state for each digit) -/
def normZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (A0 : AS) : AS :=
  let B := normF T H A0
  let B := if PipeWrites.inZone T.G A0 then Z.foldl (fun B i => B.setK i (A0.getK i)) B else B
  if PipeWrites.inZone T.G B && R.any (fun r => decide (r.1 ≤ B.pc) && decide (B.pc ≤ r.2)) then { B with a := AB.top, x := AB.top, y := AB.top, p := AB.top } else B

def routeZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let G := T.G
  let B := normZ T H R Z B0
  let K := keyT T B
  let X := if isCutF T B.pc then { X with multi := X.multi.insert K () } else X
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if PipeWrites.leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (A0 : AS) : PipeWrites.SG := Id.run do
  let G := T.G
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let ps := preF T H cur
    for A₁ in ps do
      if !zoneTest T H Z E A₁ then
        X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A₁, failPcs := X.failPcs.insert (A₁.pc.toNat + 196608) (X.failPcs.getD (A₁.pc.toNat + 196608) 0 + 1) }
      for r in kstepZ T H Z E ops A₁ do
        match r with
        | some B =>
          if !readPF T.Q A₁ B || !pairOK T.Q A₁ B || !okS T E A₁ then
            X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A₁, failPcs := X.failPcs.insert (A₁.pc.toNat + 65536) (X.failPcs.getD (A₁.pc.toNat + 65536) 0 + 1) }
        | none => pure ()
    let rs := ps.flatMap (kstepZ T H Z E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => !okRt G B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutF T b.pc && b.pc != G.je && b.pc != G.subs && b.pc != T.K.entry && b.pc != H.band &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeZ T H R Z X b
    break
  return X

partial def searchZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (E : Env) (ops : Array (AM Unit)) (cap : Nat) (X0 : PipeWrites.SG) : PipeWrites.SG := Id.run do
  let mut X := X0
  while true do
    if cap ≤ X.steps then break
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runZ T H R Z E ops X A
  return X

/-- the start of the touch's frame: the guard's bytes, and the watched bits of the two bytes -/
def startY (T : Pole) (W : List Watch) (late : Bool) : AS := FrameKeep.startK T.G W late

/-- the places where the search forgets the registers -/
def rangesZ (sy : Syms) : List (UInt16 × UInt16) := [(sy.OutputNumbers - 16, sy.ExitOutputN), (sy.UpdateNumber, sy.NoZSup)]

def searchOfZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (E : Env) (W : List Watch) (cap : Nat) : PipeWrites.SG :=
  let ops := (aRows E).toArray
  searchZ T H R Z E ops cap ([startY T W false, startY T W true].foldl (routeZ T H R Z) {})

/-- what the search finds: no part of the proof -/
def searchReportZ (sy : Syms) (m0 : Machine) (cap : Nat) : String :=
  let T := poleY sy m0
  let H := hpOf sy m0
  let E := PipeEntryRule.envOf m0
  let X := searchOfZ T H (rangesZ sy) (zoneB sy m0) E (watchB sy m0) cap
  let fp := (X.failPcs.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 24
  let byPc := X.done.fold (fun (h : Std.HashMap Nat Nat) _ (A, _) => h.insert A.pc.toNat (h.getD A.pc.toNat 0 + 1)) {}
  let topPc := (byPc.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 16
  s!"one frame: {X.steps} steps, {X.forks} forks, {X.fails} failures {fp}, table {X.multi.size}, states {X.done.size}; two bytes {bI sy m0}, zone {zoneB sy m0}; states by place {topPc}"

end Smbrta.PoleTileKeep

/-! ## The targets of the stores -/

namespace Smbrta.PoleTileKeep

open PipeTransitionAll (go go_bind)
open PipeWrites (wTarget opAt)
open TaintRun (AS Env Sim AB AM aRows)
open PoleFrame
open PoleTileHeight (HP)

section
variable {E : Env} {F : Nat × UInt8}

theorem idx_mod (a : UInt16) : (a &&& 0x7FF).toNat = a.toNat % 2048 := by
  rw [UInt16.toNat_and]
  have e7 : (0x7FF : UInt16).toNat = 2 ^ 11 - 1 := by decide
  rw [e7, Nat.and_two_pow_sub_one_eq_mod]

theorem zp_idx (z : UInt8) : (z.toUInt16 &&& 0x7FF).toNat = z.toNat := by
  rw [idx_mod, UInt8.toNat_toUInt16]
  have := z.toNat_lt
  omega

/-- the target of a store `zp,X` -/
theorem zpx_eq {m : Machine} (hp : m.pc + 1 ≥ 0x8000) : (go mZpx { m with pc := m.pc + 1 }).1 = (RoomBlocks.operand m + m.x).toUInt16 := by
  have e : go mZpx { m with pc := m.pc + 1 } = go (fetch >>= fun b => get >>= fun s => pure (b + s.x).toUInt16) { m with pc := m.pc + 1 } := rfl
  rw [e, go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp]
  rfl

/-- a store through an index or a pointer has an opcode of `PoleTileWalk.idxOps` -/
theorem idx_of_target {op : UInt8} {m : Machine} {t : UInt16} (h : wTarget op m = some t) : PoleTileWalk.idxOps.contains op = true := by
  unfold wTarget at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with ((e | e) | e) | e <;> subst e <;> decide
  · split at h
    · rename_i _ hc
      simp only [Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with ((e | e) | e) | e <;> subst e <;> decide
    · split at h
      · rename_i _ _ hc
        simp only [beq_iff_eq] at hc
        subst hc
        decide
      · split at h
        · rename_i _ _ _ hc
          simp only [beq_iff_eq] at hc
          subst hc
          decide
        · cases h

/-- **The range of a store's target**: a machine that the piece covers stores at an address of `rangeW` -/
theorem range_spec {A : AS} {m : Machine} {r : Nat × Nat} (hs : Sim E F A m) (hp1 : 0x8000 ≤ A.pc + 1) (hr : rangeW E A = some r) (hr2 : r.2 < 65536) :
    ∀ t, wTarget (opAt m) m = some t → r.1 ≤ t.toNat ∧ t.toNat ≤ r.2 := by
  intro t ht
  have hop : E.prg.get! (A.pc &&& E.mask).toNat = opAt m := by unfold opAt; rw [hs.prg, hs.mask, hs.pc]
  have hz : E.prg.get! ((A.pc + 1) &&& E.mask).toNat = RoomBlocks.operand m := by unfold RoomBlocks.operand; rw [hs.prg, hs.mask, hs.pc]
  have hmp : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact hp1
  unfold rangeW at hr
  dsimp only at hr
  rw [hop, hz] at hr
  by_cases h1 : (opAt m == 0x95 || opAt m == 0x94 || opAt m == 0xD6 || opAt m == 0xF6) = true
  · rw [if_pos h1] at hr
    split at hr
    · rename_i hb
      cases hr
      have e1 : wTarget (opAt m) m = some (go mZpx { m with pc := m.pc + 1 }).1 := by
        unfold wTarget
        dsimp only
        rw [if_pos h1]
      rw [e1] at ht
      have e2 := Option.some.inj ht
      rw [zpx_eq hmp] at e2
      subst e2
      have a1 := TaintRun.minv_le hs.x
      have a2 := TaintRun.le_maxv hs.x
      rw [UInt8.toNat_toUInt16, UInt8.toNat_add]
      dsimp only
      omega
    · cases hr
  · rw [if_neg h1] at hr
    by_cases h2 : (opAt m == 0x91) = true
    · rw [if_pos h2] at hr
      cases hr
      have h91 : opAt m = 0x91 := by simpa using h2
      have e1 : wTarget (opAt m) m = some (ScreenPage.writeAddr m) := by
        rw [h91]
        rfl
      rw [e1] at ht
      have e2 := Option.some.inj ht
      rw [RoomBlocks.writeAddr_eq hmp] at e2
      subst e2
      dsimp only at hr2 ⊢
      unfold RoomBlocks.ptrZ
      rw [zp_idx, zp_idx, UInt16.toNat_add, SideChangeEnd.ptr_toNat, UInt8.toNat_toUInt16]
      have hz1 := (RoomBlocks.operand m).toNat_lt
      have hz2 := (RoomBlocks.operand m + 1).toNat_lt
      have s1 := hs.ram (RoomBlocks.operand m).toNat (by omega)
      have s2 := hs.ram (RoomBlocks.operand m + 1).toNat (by omega)
      have a1 := TaintRun.minv_le s1
      have a2 := TaintRun.le_maxv s1
      have a3 := TaintRun.minv_le s2
      have a4 := TaintRun.le_maxv s2
      have a5 := TaintRun.minv_le hs.y
      have a6 := TaintRun.le_maxv hs.y
      have e65 : (2 : Nat) ^ 16 = 65536 := by decide
      rw [e65]
      omega
    · rw [if_neg h2] at hr
      cases hr

/-- **A store's target that `rangeOK` allows** is none of `P` -/
theorem target_of_range {P : List Nat} {A : AS} {m : Machine} (hs : Sim E F A m) (h : rangeOK E P A = true) :
    ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ P := by
  intro t ht hlt hP
  unfold rangeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, hp1⟩, h⟩ := h
  split at h
  · rename_i r hr
    unfold avoidR at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hr2, h⟩ := h
    obtain ⟨b1, b2⟩ := range_spec hs hp1 hr (by omega) t ht
    have hl : t.toNat < 0x2000 := by
      have := UInt16.lt_iff_toNat_lt.1 hlt
      simpa using this
    rcases h with h | ⟨hb, h⟩
    · omega
    · have hi := h _ hP
      rw [idx_mod] at hi
      omega
  · cases h

/-- the table of the writes has, for a store through an index or a pointer, the mode of its target -/
theorem wOf_of_target {op : UInt8} {m : Machine} {t : UInt16} (h : wTarget op m = some t) :
    ∃ c a, StepWrites.wOf op = .md c a ∧ (go c { m with pc := m.pc + 1 }).1 = t := by
  unfold wTarget at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    have e := Option.some.inj h
    rcases hc with ((e1 | e1) | e1) | e1 <;> subst e1 <;> exact ⟨_, _, rfl, e⟩
  · split at h
    · rename_i _ hc
      simp only [Bool.or_eq_true, beq_iff_eq] at hc
      have e := Option.some.inj h
      rcases hc with ((e1 | e1) | e1) | e1 <;> subst e1 <;> exact ⟨_, _, rfl, e⟩
    · split at h
      · rename_i _ _ hc
        simp only [beq_iff_eq] at hc
        subst hc
        exact ⟨_, _, rfl, Option.some.inj h⟩
      · split at h
        · rename_i _ _ _ hc
          simp only [beq_iff_eq] at hc
          subst hc
          exact ⟨_, _, rfl, Option.some.inj h⟩
        · cases h

/-- **A store's target that `StepWrites.keepOK` allows** is not in `P` -/
theorem keep_target {P : Nat → Bool} {A : AS} {m : Machine} (hs : Sim E F A m) (hn : A.nmi = false) (hk : StepWrites.keepOK E P A = true) :
    ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → P ((t &&& 0x7FF).toNat) = false := by
  intro t ht hlt
  unfold StepWrites.keepOK at hk
  rw [if_neg (by simp [hn])] at hk
  by_cases hp : A.pc < 0x8000
  · rw [if_pos hp] at hk
    cases hk
  rw [if_neg hp] at hk
  have hop : E.prg.get! (A.pc &&& E.mask).toNat = opAt m := by unfold opAt; rw [hs.prg, hs.mask, hs.pc]
  rw [hop] at hk
  obtain ⟨c, a, hw, hc⟩ := wOf_of_target ht
  have hok := (StepWrites.w_op (opAt m)).2
  rw [hw] at hk hok
  simp only at hk
  have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
    pc := by
      show m.pc + 1 = A.pc + 1
      rw [hs.pc] }
  cases ha : a E { A with pc := A.pc + 1 } with
  | none =>
    rw [ha] at hk
    cases hk
  | some p =>
    obtain ⟨ad, A'⟩ := p
    rw [ha] at hk
    obtain ⟨hr, _, _⟩ := hok E F _ _ hs1 ad A' ha
    have h2 := StepWrites.adAvoid_ok hk hr
    rw [hc] at h2
    exact h2 _ (by simp [StepWrites.ramIdx, hlt])

/-- **The zone's test**: inside the collision routine, a store through an index or a pointer of a machine that the piece covers writes neither the height nor a byte
of `Z` -/
theorem zone_of_test {T : Pole} {H : HP} {Z : List Nat} {A : AS} {m : Machine} (hs : Sim E F A m) (h : zoneTest T H Z E A = true)
    (hz : PipeWrites.inZone T.G A = true) : ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ zP H Z := by
  have hop : E.prg.get! (A.pc &&& E.mask).toNat = opAt m := by unfold opAt; rw [hs.prg, hs.mask, hs.pc]
  unfold zoneTest at h
  rw [hop, hz] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
  intro t ht hlt hm
  rcases h with (h1 | ⟨h1, h2⟩) | h1
  · rw [idx_of_target ht] at h1
    cases h1
  · have e := keep_target hs h1 h2 t ht hlt
    have e2 : (zP H Z).contains ((t &&& 0x7FF).toNat) = true := List.elem_eq_true_of_mem hm
    rw [e2] at e
    cases e
  · exact target_of_range hs h1 t ht hlt hm

/-- `Plain` with more bytes protected, that the store does not write -/
theorem plain_app {Z prot : List Nat} {t : UInt16} (h : PipeWrites.Plain prot t) (hz : t < 0x2000 → (t &&& 0x7FF).toNat ∉ Z) : PipeWrites.Plain (Z ++ prot) t := by
  rcases h with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, ?_⟩
    simp only [List.mem_append, not_or]
    exact ⟨hz h1, h2⟩
  · exact Or.inr h1

/-- **`CleanK` of the guard inside the collision routine**, away from the move routine's stores of the position: from `CleanK`, `PosAt` and the zone's test -/
theorem cleanK_GZ {T : Pole} {H : HP} {Z : List Nat} {q : UInt16} {m : Machine} (h : FrameKeep.CleanK T.G q m) (hp : PosAt T.Q T.ps m)
    (hz : ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ zP H Z) (hn : m.pc ∉ T.ps) : FrameKeep.CleanK (GZ T H Z) q m :=
  ⟨fun t ht hq => plain_app (PoleTileHeight.plain_y (plain_pos (h.store t ht hq) (fun hlt => ⟨fun e => hn (hp t ht hlt (Or.inl e)).1, fun e => hn (hp t ht hlt (Or.inr e)).1⟩))
    (fun hlt e => hz t ht hlt (by rw [e]; exact List.mem_cons_self))) (fun hlt e => hz t ht hlt (List.mem_cons_of_mem _ e)), h.read, h.jump, h.time⟩

/-- **A step of the machine**, with the steps of this walk -/
theorem s_kstepZ {T : Pole} {H : HP} {Z : List Nat} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat)
    (hc : FrameKeep.CleanK T.G T.K.store m) (hp : PosAt T.Q T.ps m)
    (hz : PipeWrites.inZone T.G A = true → ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ zP H Z) (hs : Sim E F A m) :
    ∃ r ∈ kstepZ T H Z E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold kstepZ
  by_cases h1 : T.ps.contains A.pc = true
  · rw [if_pos h1]
    exact s_kstepT hops hT hc hp hs
  · rw [if_neg h1]
    have hn : m.pc ∉ T.ps := by
      rw [hs.pc]
      intro h
      exact h1 (List.elem_eq_true_of_mem h)
    by_cases h2 : PipeWrites.inZone T.G A = true
    · rw [if_pos h2]
      exact FrameKeep.s_kstep hops hT (cleanK_GZ hc hp (hz h2) hn) hs
    · rw [if_neg h2]
      exact FrameKeep.s_kstep hops hT (cleanK_GP hc hp hn) hs

end

end Smbrta.PoleTileKeep

/-! ## The walk -/

namespace Smbrta.PoleTileKeep

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeWrites (Guard FrameStart okRt fuelG knownOf wTarget opAt)
open FrameKeep (CleanK Watch Watched)
open TaintRun (AS Env Sim AB AM aRows)
open PoleTileWalk (ColMap BufAt HypR okS pairOK)
open PoleTileRead (TR yPieces)
open PoleTileHeight (HP hpOf ZoneH bandPieces coverN)
open PoleTileFar (TileCol preF readPF isCutF cov_preF)

/-- a state of the table covers the state, by the key of `normZ` -/
def coverZ (C : CfgT) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (B : AS) : Bool :=
  match C.idx[keyT C.T (normZ C.T H R Z B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => PipeWrites.leK B D l
    | _, _ => false
  | none => false

/-- `PoleTileFar.walkF` with the steps `kstepZ` and the zone's test on every piece -/
def walkZ (C : CfgT) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preF C.T H A).all fun A₁ => okS C.T C.E A₁ && zoneTest C.T H Z C.E A₁ && (kstepZ C.T H Z C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.T.G B && pairOK C.T.Q A₁ B && readPF C.T.Q A₁ B &&
      (B.k != A.k || (B.pc != C.T.Q.read + 2 && C.cut.get! B.pc.toNat != 0 && coverZ C H R Z B) || walkZ C H R Z n B)

/-- the table of the search -/
def cfgOfZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (E : Env) (W : List Watch) : CfgT :=
  let q := PipeWrites.tableOfS (searchOfZ T H R Z E W 1000000000)
  { E, ops := (aRows E).toArray, T, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-- **The check**: as `PoleTileFar.frameCheckF`, with this walk from the starts with the watched bits `W` -/
def frameCheckZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (E : Env) (W : List Watch) : Bool :=
  let C := cfgOfZ T H R Z E W
  PoleTileWalk.frameBase T && coverN (bandPieces H.R) 256 && coverN (yPieces H.R) (PoleTileRead.hiR H.R) && decide (H.R.yI < 2048) &&
    C.t.all (walkZ C H R Z fuelG) && walkZ C H R Z fuelG (startY T W false) && walkZ C H R Z fuelG (startY T W true) && PoleTileWalk.readOK T E

/-- what the check says -/
structure FrameOKZ (T : Pole) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (E : Env) (W : List Watch) : Prop where
  rt : T.G.rtI < 2048
  zone : ZoneOK T
  zh : ZoneH H
  table : (cfgOfZ T H R Z E W).t.all (walkZ (cfgOfZ T H R Z E W) H R Z fuelG) = true
  s0 : walkZ (cfgOfZ T H R Z E W) H R Z fuelG (startY T W false) = true
  s1 : walkZ (cfgOfZ T H R Z E W) H R Z fuelG (startY T W true) = true
  read : PoleTileWalk.ReadFacts T E

theorem frameOKZ_of_check {T : Pole} {H : HP} {R : List (UInt16 × UInt16)} {Z : List Nat} {E : Env} {W : List Watch} (hp : T.Q.ptrI + 1 < 2048)
    (h : frameCheckZ T H R Z E W = true) : FrameOKZ T H R Z E W := by
  simp only [frameCheckZ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hB, hY1⟩, hY2⟩, hyI⟩, ht⟩, h0⟩, h1⟩, hr⟩ := h
  simp only [PoleTileWalk.frameBase, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, _⟩, _⟩, _⟩ := hB
  exact ⟨b1, ⟨⟨b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩, hp⟩, ⟨hY1, hY2, hyI⟩, ht, h0, h1, PoleTileWalk.readFacts_of hr⟩

/-! ## One step -/

section
variable {C : CfgT} {H : HP} {R : List (UInt16 × UInt16)} {Z : List Nat} {Fu : Nat} {F : Nat × UInt8}

def LiveZ (C : CfgT) (H : HP) (R : List (UInt16 × UInt16)) (Z : List Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkZ C H R Z n A = true

theorem cover_liveZ (ht : C.t.all (walkZ C H R Z Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverZ C H R Z B = true) : ∃ D, LiveZ C H R Z F D m := by
  unfold coverZ at h
  split at h
  · rename_i i _
    split at h
    · rename_i D l e1 e2
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
      have hl : l = knownOf D := by
        rw [hkl] at e2
        rw [Array.getElem?_map, e1] at e2
        exact (Option.some.inj e2).symm
      rw [hl] at h
      have hle := PipeWrites.leK_le h
      have hall := (Array.all_eq_true.1 ht) i hi
      rw [he] at hall
      have hDk : D.k = 0 := by
        have e3 := PipeWrites.le_k hle
        omega
      exact ⟨D, TaintRun.sim_le hle hs, hDk, Fu, hall⟩
    · cases h
  · cases h

/-- one step of the machine from a live state: the piece before the step, the state after it, and the tests -/
theorem live_stepZ (ht : C.t.all (walkZ C H R Z Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : ZoneOK C.T) (hz : ZoneH H) (hr : C.T.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveZ C H R Z F A m) (hc : CleanK C.T.G C.T.K.store m)
    (hp : PosAt C.T.Q C.T.ps m) (hh : HypR C.T m) (hTR : TR C.T.Q A m) :
    ∃ A₁ B, Sim C.E F A₁ m ∧ okS C.T C.E A₁ = true ∧ Sim C.E F B (go step m).2 ∧ pairOK C.T.Q A₁ B = true ∧ readPF C.T.Q A₁ B = true ∧
      (go step m).2.ram.get! C.T.G.rtI ≠ C.T.G.ev ∧
      (F.1 < (go step m).2.frame ∨ ∃ A', LiveZ C H R Z F A' (go step m).2 ∧ (A'.pc = C.T.Q.read + 2 → A' = B)) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkZ] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preF hb hz hc hh hTR hs
    simp only [walkZ, List.all_eq_true] at hw
    have hw1 := hw A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at hw1
    obtain ⟨⟨hok, hzt⟩, hw1⟩ := hw1
    obtain ⟨r, hr1, hB⟩ := s_kstepZ (H := H) (Z := Z) hops hT hc hp (fun hzz => zone_of_test hs1 hzt hzz) hs1
    have hw2 := hw1 r hr1
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, _⟩ := hB B rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hw2
      obtain ⟨⟨⟨h2, hpair⟩, hrp⟩, h3⟩ := hw2
      refine ⟨A₁, B, hs1, hok, h1, hpair, hrp, PipeWrites.ne_of_okRt h2 (h1.ram _ hr), ?_⟩
      by_cases hk2 : B.k = 0
      · right
        rcases h3 with (h4 | ⟨⟨h5, _⟩, h4⟩) | h4
        · rw [hk, hk2] at h4
          exact absurd rfl h4
        · obtain ⟨D, hD⟩ := cover_liveZ ht hkl h1 hk2 h4
          refine ⟨D, hD, fun hDp => absurd ?_ h5⟩
          rw [← h1.pc, hD.1.pc]
          exact hDp
        · exact ⟨B, ⟨h1, hk2, n, h4⟩, fun _ => rfl⟩
      · left
        rw [h1.fr]
        omega

end

/-! ## The frame -/

theorem foldK : ∀ (l : List Watch) (A : AS), A.k = 0 → (l.foldl (fun A w => A.setK w.1 ⟨w.2.2 &&& w.2.1, w.2.1⟩) A).k = 0
  | [], _, h => h
  | _ :: t, A, h => foldK t _ h

theorem startY_k (T : Pole) (W : List Watch) (b : Bool) : (startY T W b).k = 0 := foldK W _ rfl

/-- **The frame.** From a `FrameStart` with the watched bits `W` and the map `ColMap`, while each instruction is `CleanK`, meets `PosAt`, `HypR`, `BufAt` and `TileCol`,
the routine byte does not become the pole's. `YAt` is not assumed: the zone's test proves it on the way. -/
theorem no_write_frameZ {T : Pole} {H : HP} {R : List (UInt16 × UInt16)} {Z : List Nat} {E : Env} {W : List Watch} (hp : T.Q.ptrI + 1 < 2048)
    (hc : frameCheckZ T H R Z E W = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart T.G E (s 0)) (hw0 : Watched W (s 0))
    (hm0 : ColMap T.Q (s 0))
    (hh : ∀ j, j ≤ n → CleanK T.G T.K.store (s j) ∧ PosAt T.Q T.ps (s j) ∧ HypR T (s j) ∧ BufAt T.Q (s j) ∧ TileCol T.Q (s j)) :
    (s (n + 1)).ram.get! T.G.rtI ≠ T.G.ev := by
  have hC := frameOKZ_of_check hp hc
  obtain ⟨b, hsim⟩ := FrameKeep.sim_startK hE h0 hw0
  have hkl : (cfgOfZ T H R Z E W).kl = (cfgOfZ T H R Z E W).t.map knownOf := rfl
  have hT2 : 2 ≤ (2 : UInt8).toNat := by decide
  have hstart : ∃ A, LiveZ (cfgOfZ T H R Z E W) H R Z ((s 0).frame, 2) A (s 0) ∧ TR T.Q A (s 0) := by
    have hT0 : ∀ A : AS, Sim E ((s 0).frame, 2) A (s 0) → TR T.Q A (s 0) := by
      intro A hA hpc
      rw [← hA.pc, h0.pc] at hpc
      exact absurd hpc hC.read.idle
    cases b with
    | false => exact ⟨_, ⟨hsim, startY_k T W false, fuelG, hC.s0⟩, hT0 _ hsim⟩
    | true => exact ⟨_, ⟨hsim, startY_k T W true, fuelG, hC.s1⟩, hT0 _ hsim⟩
  have live : ∀ j, j ≤ n → (∃ A, LiveZ (cfgOfZ T H R Z E W) H R Z ((s 0).frame, 2) A (s j) ∧ TR T.Q A (s j)) ∧ ColMap T.Q (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hstart, hm0⟩
    | succ j ih =>
      intro hj
      obtain ⟨⟨A, hA, hTA⟩, hmj⟩ := ih (by omega)
      obtain ⟨hh1, hp1, hr1, hb1, _⟩ := hh j (by omega)
      obtain ⟨A₁, B, hs1, hok, _, hpair, hrp, _, h2⟩ :=
        live_stepZ hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hr1 hTA
      have hcol : TileCol T.Q (go step (s j)).2 := by
        rw [← hs j (by omega)]
        exact (hh (j + 1) hj).2.2.2.2
      have hmj1 := PoleTileWalk.colMap_step hs1 hok hb1 hmj
      rw [← hs j (by omega)] at hmj1
      refine ⟨?_, hmj1⟩
      rcases h2 with h2 | ⟨A', hA', hAB⟩
      · have h3 := hf (j + 1) hj
        have h4 : (s 0).frame < (s (j + 1)).frame := by rw [hs j (by omega)]; exact h2
        omega
      · refine ⟨A', by rw [hs j (by omega)]; exact hA', fun hpc hsn => ?_⟩
        have e := hAB hpc
        subst e
        rw [hs j (by omega)]
        exact PoleTileFar.tileRead_afterF hC.zone hC.read hs1 hpair hrp hpc hsn hmj hcol
  obtain ⟨⟨A, hA, hTA⟩, _⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hp1, hr1, _, _⟩ := hh n (Nat.le_refl n)
  obtain ⟨_, _, _, _, _, _, _, h1, _⟩ := live_stepZ hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hr1 hTA
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

end Smbrta.PoleTileKeep

/-! ## The frames up to the touch keep the two bytes -/

namespace Smbrta.PoleTileKeep

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeTransition (frame)
open PipeWrites (Guard FrameStart okRt fuelG knownOf wTarget opAt)
open FrameKeep (CleanK Watch Watched CfgK preK kstep coverK cfgOfKW startK fuelK watchOK endOK)
open TaintRun (AS Env Sim AB AM aRows)
open PoleTileWalk (ColMap BufAt HypR okS pairOK walkKS keepCheckS)
open PoleTileFar (TileCol)
open PoleTileHeight (hpOf)

/-- **What is assumed of one instruction of the frames up to the touch, besides `FrameKeep.CleanK`**: a store through an index or a pointer writes neither of the two
bytes -/
def KeepB (sy : Syms) (m0 : Machine) (m : Machine) : Prop :=
  ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ bI sy m0

/-- the guard of the frames, with the two bytes protected -/
def GK (sy : Syms) (m0 : Machine) : Guard := { FrameKeep.guardK sy m0 with prot := bI sy m0 ++ (FrameKeep.guardK sy m0).prot }

/-- the watched bits of the frames: those of `FrameKeep` and those of the two bytes -/
def watchY (sy : Syms) (m0 : Machine) : List Watch := FrameKeep.watchOf sy ++ watchB sy m0

/-- `CleanK` with more bytes protected, that no store through an index or a pointer writes -/
theorem cleanK_add {G : Guard} {l : List Nat} {q : UInt16} {m : Machine} (h : CleanK G q m)
    (hb : ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ l) : CleanK { G with prot := l ++ G.prot } q m :=
  ⟨fun t ht hq => plain_app (h.store t ht hq) (hb t ht), h.read, h.jump, h.time⟩

theorem cleanK_GK {sy : Syms} {m0 : Machine} {q : UInt16} {m : Machine} (h : CleanK (FrameKeep.guardK sy m0) q m) (hb : KeepB sy m0 m) : CleanK (GK sy m0) q m :=
  cleanK_add h hb

/-- the guard of the touch's walk is that of the frames, as `PoleFrame.guardT` is that of `FrameKeep` -/
theorem poleY_G (sy : Syms) (m0 : Machine) : (poleY sy m0).G = { GK sy m0 with ev := PoleEntryRule.vf sy, subs := sy.PlayerSubs, cuts := [] } := rfl

theorem start_prot {G : Guard} {l : List Nat} {E : Env} {m : Machine} (h : FrameStart G E m) : FrameStart { G with prot := l } E m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- the walk with the test `okSK` is the walk of `FrameKeep` -/
theorem walkK_of_KS {C : CfgK} {Q : Spots} : ∀ {n : Nat} {A : AS}, walkKS C Q n A = true → FrameKeep.walkK C n A = true
  | 0, _, h => by simp [walkKS] at h
  | n + 1, A, h => by
    simp only [walkKS, FrameKeep.walkK, List.all_eq_true] at h ⊢
    intro A₁ hA r hr
    have h1 := h A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at h1
    have h2 := h1.2 r hr
    cases r with
    | none => simp at h2
    | some B =>
      dsimp only at h2 ⊢
      split
      · rename_i hk
        rw [if_pos hk] at h2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h2 ⊢
        rcases h2 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (walkK_of_KS h3)
      · rename_i hk
        rw [if_neg hk] at h2
        exact h2

theorem keepW_of_S {S : FrameKeep.Spot} {G : Guard} {E : Env} {W : List Watch} {key : AS → Nat} {fin : AS → Bool} {Q : Spots}
    (h : keepCheckS S G E W key fin Q = true) : FrameKeep.keepCheckW S G E W key fin = true := by
  simp only [keepCheckS, FrameKeep.keepCheckW, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨⟨⟨⟨h1, h2⟩, Array.all_eq_true.2 fun i hi => walkK_of_KS (Array.all_eq_true.1 h3 i hi)⟩, walkK_of_KS h4⟩, walkK_of_KS h5⟩

/-- **The check on the ROM of the frames**: the walk of `PoleTileWalk.keepCheckOfS` with the two bytes protected and watched -/
def keepCheckOfY (sy : Syms) (m0 : Machine) : Bool :=
  keepCheckS (FrameKeep.spotOf sy m0) (GK sy m0) (PipeEntryRule.envOf m0) (watchY sy m0)
    (FrameKeep.keyKC sy (FrameKeep.spotOf sy m0) (GK sy m0) (watchY sy m0)) (FrameKeep.endCtl sy) (spotsF sy m0)

/-- **Every frame up to the touch's frame keeps the map and the watched bits**: from the map and the bits at control, `CleanK` and `KeepB` and `BufAt` on each
instruction (`PoleTileWalk.frame_colMap`, `FrameKeep.keep_frameW`) -/
theorem frames_keepY {sy : Syms} {m0 : Machine} {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hc : FrameKeep.keepCheckOf sy m0 = true)
    (hcY : keepCheckOfY sy m0 = true) (K : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (h0 : Watched (FrameKeep.watchOf sy) (seq 0))
    (hw0 : Watched (watchB sy m0) (seq 0)) (hm0 : ColMap (spotsF sy m0) (seq 0))
    (hkb : ∀ n, n + 1 < K.ix g → ∀ k, KeepB sy m0 (trace (K.all n) (K.inp n) k))
    (hb : ∀ n, n + 1 < K.ix g → ∀ k, BufAt (spotsF sy m0) (trace (K.all n) (K.inp n) k)) :
    ∀ n, n < K.ix g → ColMap (spotsF sy m0) (K.all n) ∧ Watched (watchB sy m0) (K.all n) := by
  have e0 : seq 0 = K.all 0 := by rw [K.at_ix 0 (Nat.zero_le _), K.ix0]
  intro n
  induction n with
  | zero => exact fun _ => ⟨e0 ▸ hm0, e0 ▸ hw0⟩
  | succ i ih =>
    intro hi
    obtain ⟨hmi, hwi⟩ := ih (by omega)
    obtain ⟨a1, a2⟩ := K.all_start hc hs0 h0 i (by omega)
    have a1' : FrameStart (GK sy m0) (PipeEntryRule.envOf m0) (K.all i) := start_prot a1
    have a2' : Watched (watchY sy m0) (K.all i) := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact a2 w hw
      · exact hwi w hw
    have hcl : ∀ k, CleanK (GK sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all i) (K.inp i) k) :=
      fun k => cleanK_GK (K.clean i (by omega) k) (hkb i hi k)
    rw [K.next i]
    refine ⟨PoleTileWalk.frame_colMap hcY rfl a1' a2' hcl (hb i hi) hmi, ?_⟩
    have hW := FrameKeep.keep_frameW (keepW_of_S hcY) rfl a1' a2' hcl
    intro w hw
    exact hW w (List.mem_append_right _ hw)

/-! ## The touch -/

/-- **The check on the ROM**: as `PoleTileFar.poleCheckF`, with the walk of this file in place of the walk of `PoleTileFar`, and the walk of the frames with the two bytes -/
def poleCheckZ (sy : Syms) (m0 : Machine) : Bool :=
  ptrOK sy m0 && frameCheckZ (poleY sy m0) (hpOf sy m0) (rangesZ sy) (zoneB sy m0) (PipeEntryRule.envOf m0) (watchB sy m0) && SubsOnce.subsCheck sy m0 &&
    keepCheckOfY sy m0

theorem subs_of_Z {sy : Syms} {m0 : Machine} (h : poleCheckZ sy m0 = true) : SubsOnce.subsCheck sy m0 = true := by
  simp only [poleCheckZ, Bool.and_eq_true] at h
  exact h.1.2

theorem keepY_of_Z {sy : Syms} {m0 : Machine} (h : poleCheckZ sy m0 = true) : keepCheckOfY sy m0 = true := by
  simp only [poleCheckZ, Bool.and_eq_true] at h
  exact h.2

/-- **The touch on a real frame, at the end of the move**: as `PoleTileFar.touch_right_of_leftF`, with the two bytes' watched bits at the frame's start and `KeepB` on
each instruction in place of `YKeep` -/
theorem touch_right_of_leftZ {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : poleCheckZ sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hw : Watched (watchB sy m0) m) (hk : ∀ j, CleanK (GK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hcol : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileCol (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k)) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) := by
  simp only [poleCheckZ, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp, hc⟩, _⟩, _⟩ := hc
  have hp' : (spotsF sy m0).ptrI + 1 < 2048 := by simpa [ptrOK] using hp
  obtain ⟨n, hw'⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw', a, b, c⟩
  · exfalso
    have hn := no_write_frameZ (T := poleY sy m0) (H := hpOf sy m0) (s := trace m i) (n := n) hp' hc rfl (fun j hj => PoleEntryRule.step_before hw' j hj)
      (fun j hj => frame_before hw' j hj) (by rw [poleY_G]; exact start_with (start_prot (h0.pad _))) hw hm
      (fun j hj => ⟨by rw [poleY_G]; exact cleanK_with (hk j), hpk n hw' j hj, ⟨fun hs => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd ⟨j, hj, hs, hl⟩ hx
        · exact Nat.lt_of_not_le hl, fun ha => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd (hag n hw' j hj ha hl) hx
        · exact Nat.lt_of_not_le hl, by
        show (trace m i j).pc ∉ ([] : List UInt16)
        simp⟩, hbuf n hw' j hj, hcol n hw' j hj⟩)
    exact hn hw'.2

/-- **In the pole's range, from one whole frame**: as `PoleTileFar.inRange_of_frameF`, without `YKeep` -/
theorem inRange_of_frameZ {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} (hc : poleCheckZ sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hw : Watched (watchB sy m0) m) (hk : ∀ j, CleanK (GK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hcol : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileCol (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k))
    (hmoved : ∀ n j, WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SurfaceRun.poleP sy m0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := touch_right_of_leftZ hc he h0 hw hk hpk hm hbuf hcol hag
  rw [hmoved n j h1 h2 h3]
  have h5 : (spotsF sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  have h7 : (spotsF sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (spotsF sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h5, h7, h8] at h4
  unfold SurfaceRun.poleP posP peek
  omega

end Smbrta.PoleTileKeep
