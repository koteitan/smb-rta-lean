import Theorems.CollideKeep
import Theorems.VertKeep

/-!
# Above ground: the facing, the subspeed, the collision bits and the vertical force after the scroll handler

A frame in control comes to the player's routine (the cut of `CtrlKeep`), and from there to the scroll handler (`PlayerSubs`), as in `AfterKeep`. Three things about the
frame from the scroll handler to its end are proved here by walks.

**The facing and the subspeed** (`keepZ_end`). After the scroll handler the facing is written by its address at the flagpole (a path that then writes the routine,
which `FrameKeep.Frames.noStore` cuts) and in the climbing routine, which first sets the speed and the subspeed to 0; the subspeed is written only there. A walk follows
the byte as the counter of `TaintRun` (`Env.rkI`), stops following it before a store to it by its address (`CollideKeep.rkOff`), and asks at the frame's end (`finZ`)
that the byte is still followed, or that the speed and the subspeed are known to be 0. So at the frame's end the facing and the subspeed are those at the scroll
handler, or the frame ends with the speed 0 and the subspeed 0. A walk cannot say more: it knows neither the map nor the objects, and a climbing tile is in the map.

**The collision bits on a frame that moves right or not at all at the scroll handler** (`bits_end`). The collision routine sets the bits to `FF`, and
`ImpedePlayerMove` clears the bit of a side. On the side of a block of Right it sets the speed to 0 unless he moves left; on the side of a block of Left it does so
unless he moves right. So if the speed's sign bit is 0 at the scroll handler, the frame ends with the bits `FF` or those of a block of Left, or with the speed 0. The
first walk carries the collision bits from the cut to the scroll handler (they are `FF` or those of a block of Left at the frame's start), so that a frame that leaves
the collision routine early keeps this. At the scroll handler the speed's sign bit is set to 0 (`toSign`). The second walk splits `X` at the `DEX` of
`ImpedePlayerMove` (as `CollKeep`) and `Y`, the speed, at its two `CPY #` (`splitYAt`: one piece for each value that the known bits allow), so that the side and the
speed's sign are known where the routine branches on them. At the frame's end it asks (`finB`) the bits under the mask of a block of Left, or the speed known to be 0.

**The vertical force** (`vf_end`). After the scroll handler only the landing on a jumpspring stores it by its address. The landing then sets the player's state to 0,
and the only later stores to the state by its address that the walk meets write 0 (a platform's collision) or 3 (the climbing routine). The walk follows the vertical
force, stops following it before that store, and asks at the frame's end (`finVF`) that it is still followed, or that it is known to be `c` and the player's state is
known to be 0 or 3. `c` is the stored value; it is a parameter, and `vfC` reads it from the search. So a frame keeps the vertical force, or ends with the vertical
force `c` and the state 0 or 3. The table's key has the known bits of the state once the vertical force is no longer followed, so that 0 and 3 are not joined.

The guards protect the bytes the walks follow or read: `FrameKeep.guardE` protects them all (`FrameKeep.faceE` and `FrameKeep.stateE` are new), so `CleanK` of
`guardE` gives `CleanK` of each walk's guard (`cleanZ_of`, `cleanB_of`, `cleanVF_of`, `CollKeep.cleanC_of`).

The searches are no part of the proof. No game data. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.FaceKeep

open TaintRun
open PipeWrites (SG)

/-! ## The facing and the subspeed -/

/-- the facing -/
def fdI (sy : Syms) : Nat := (sy.PlayerFacingDir &&& 0x7FF).toNat

/-- **The two bytes that a frame keeps after the scroll handler unless it ends with the speed and the subspeed 0**: the facing, the subspeed -/
def zI (sy : Syms) : List Nat := [fdI sy, CollideKeep.sfI sy]

/-- what the walk of the byte `b` protects besides the bytes of `FrameKeep.guardF`: `b`, the speed, the subspeed -/
def protZ (sy : Syms) (b : Nat) : List Nat := [b, CollideKeep.spI sy, CollideKeep.sfI sy]

/-- the guard of the walk of the byte `b` -/
def guardZ (sy : Syms) (m0 : Machine) (b : Nat) : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := protZ sy b ++ (FrameKeep.guardF sy m0).prot }

/-- **What the walk asks at the frame's end**: the byte is still followed, or the speed and the subspeed are known to be 0 -/
def finZ (sy : Syms) (B : AS) : Bool :=
  (B.rk && !B.spent) || (CollideKeep.zeroAt (CollideKeep.spI sy) B && CollideKeep.zeroAt (CollideKeep.sfI sy) B)

/-- the search of the walk of the byte `b` from the states at the scroll handler `starts`: no part of the proof -/
def zSearch (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : PrevKeep.PS := CollideKeep.searchWith sy m0 (protZ sy b) (finZ sy) b starts

/-- **The walk's table** for the byte `b`, from the states at the scroll handler `starts` -/
def zCfg (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardZ sy m0 b
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let q := FrameKeep.tableOfKW key (zSearch sy m0 b starts).X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := finZ sy }

/-- what the first walk asks at the scroll handler: the walk of each byte succeeds -/
def atQZ (sy : Syms) (C2 : List FrameKeep.CfgK) (B : AS) : Bool :=
  C2.all fun C => CollideKeep.walkKV C (CollideKeep.rkOff C.E) (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK (AfterKeep.rkOn B)

/-- the walk of the pause bit up to the cut, then the first walk of `AfterKeep`, then the walks of the two bytes -/
def cfgPZ (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 : FrameKeep.CfgK) (C2 : List FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQZ sy C2) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check**: the walk of the pause bit up to the cut; from there the first walk of `AfterKeep` to the scroll handler; from there, for the facing and for the
subspeed, the walk to the frame's end -/
def zCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let C2 := (zI sy).map fun b => zCfg sy m0 b P.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (cfgPZ sy m0 v q C1 C2) && C1.t.all (AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQZ sy C2) FrameKeep.fuelK) &&
    C2.all fun C => C.t.all (CollideKeep.walkKV C (CollideKeep.rkOff C.E) (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK)

/-! ## The collision bits on a frame that moves right at the scroll handler -/

/-- **`Y` in its values at the instruction at `p`**, if it is not known: one piece for each value that its known bits allow -/
def splitYAt (p : UInt16) (A : AS) : List AS :=
  if A.pc == p && !A.y.isK then
    ((List.range 256).filter fun v => v.toUInt8 &&& A.y.k == A.y.v &&& A.y.k).map fun v => { A with y := AB.known v.toUInt8 }
  else [A]

/-- the collision bits under the mask of a block of Left: all the other bits are 1 -/
def nlW (sy : Syms) : FrameKeep.Watch := (CollKeep.bitsI sy, sy.noLeft, sy.noLeft)

/-- what the first walk sets at the cut: the area's values of `CtrlKeep.valA`, and the collision bits under the mask of a block of Left -/
def valB (sy : Syms) (v : UInt8) : List FrameKeep.Watch := CtrlKeep.valA sy v ++ [nlW sy]

/-- what the first walk watches -/
def watchB (sy : Syms) (m0 : Machine) (v : UInt8) : List FrameKeep.Watch := CtrlKeep.watchA sy m0 v ++ [nlW sy]

/-- the search from the cut to the scroll handler with the collision bits protected and watched: no part of the proof -/
def b1Search (sy : Syms) (m0 : Machine) (v : UInt8) (starts : List AS) : PrevKeep.PS :=
  PrevKeep.searchFrom sy m0 (PipeEntryRule.envOf m0) (CollKeep.bitsI sy :: CtrlKeep.spareI sy m0) [] (watchB sy m0 v) (FrameKeep.ctlI sy) (fun A => A.pc == sy.PlayerSubs)
    (starts.map (CtrlKeep.toA (watchB sy m0 v) (valB sy v)))

/-- **The first walk's table**, with the collision bits protected -/
def b1Cfg (sy : Syms) (m0 : Machine) (v : UInt8) (P : PrevKeep.PS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := CollKeep.guardC sy m0
  let E := PipeEntryRule.envOf m0
  let W := watchB sy m0 v
  let key := PrevKeep.keyP S G W
  let q := AfterKeep.tableBut key sy.PlayerSubs P.X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- the speed's sign bit 0 -/
def signW (sy : Syms) : List FrameKeep.Watch := [(CollideKeep.spI sy, 0x80, 0)]

/-- the state at the scroll handler, with the speed's sign bit 0 -/
def toSign (sy : Syms) (B : AS) : AS := (signW sy).foldl (fun A w => A.setK w.1 ⟨w.2.2 &&& w.2.1, w.2.1⟩) B

/-- the guard of the second walk: that of `FrameKeep.guardF`, with the collision bits and the speed protected too -/
def guardB (sy : Syms) (m0 : Machine) : PipeWrites.Guard :=
  { FrameKeep.guardF sy m0 with prot := [CollKeep.bitsI sy, CollideKeep.spI sy] ++ (FrameKeep.guardF sy m0).prot }

/-- the two bytes whose known bits are a part of the table's key: the speed, the collision bits (masks 0: nothing is asked of them at the frame's end) -/
def keyW (sy : Syms) : List FrameKeep.Watch := [(CollideKeep.spI sy, 0, 0)]

/-- **What the second walk asks at the frame's end**: the collision bits are known under the mask of a block of Left, or the speed is known to be 0 -/
def finB (sy : Syms) (B : AS) : Bool := FrameKeep.watchOK [nlW sy] B || CollideKeep.zeroAt (CollideKeep.spI sy) B

/-- where the walk splits `Y`: the two `CPY #` of `ImpedePlayerMove` -/
def cpy1 (sy : Syms) (m0 : Machine) : UInt16 := PipeEntryRule.findOp m0 sy.ImpedePlayerMove 0xC0 32
def cpy2 (sy : Syms) (m0 : Machine) : UInt16 := PipeEntryRule.findOp m0 (cpy1 sy m0 + 1) 0xC0 32

/-- **The pieces of the second walk**: `X` at the `DEX` of `ImpedePlayerMove` (`CollKeep.spOf`), `Y` at its two `CPY #` -/
def spB (sy : Syms) (m0 : Machine) (A : AS) : List AS :=
  (CollKeep.spOf sy m0 A).flatMap fun A₁ => (splitYAt (cpy1 sy m0) A₁).flatMap (splitYAt (cpy2 sy m0))

/-- the table's key: that of `PrevKeep.keyP` with the speed and the collision bits, and `X` and `Y` inside `ImpedePlayerMove`. No part of the proof. -/
def keyB (sy : Syms) (m0 : Machine) (S : FrameKeep.Spot) (G : PipeWrites.Guard) (A : AS) : Nat :=
  let p := CollKeep.splitPc sy m0
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  PrevKeep.keyP S G (keyW sy) A * 4294967296 + (if p ≤ A.pc && A.pc < p + 64 then num A.x * 65536 + num A.y else 0)

/-- the search of the second walk from the states at the scroll handler `starts`: no part of the proof -/
def b2Search (sy : Syms) (m0 : Machine) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := guardB sy m0
  let E := PipeEntryRule.envOf m0
  let key := keyB sy m0 S G
  let X := (starts.map (toSign sy)).foldl (PrevKeep.routeP S G [] key) {}
  CollideKeep.searchV S G E key (aRows E).toArray (spB sy m0) (finB sy) (FrameKeep.ctlI sy) sy.PlayerSubs { X }

/-- **The second walk's table** -/
def b2Cfg (sy : Syms) (m0 : Machine) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardB sy m0
  let E := PipeEntryRule.envOf m0
  let key := keyB sy m0 S G
  let q := FrameKeep.tableOfKW key (b2Search sy m0 starts).X
  { E, ops := (aRows E).toArray, S, G, W := keyW sy, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := finB sy }

/-- what the first walk asks at the scroll handler: the second walk succeeds from the state with the speed's sign bit 0 -/
def atQB (sy : Syms) (m0 : Machine) (C2 : FrameKeep.CfgK) (B : AS) : Bool :=
  CollideKeep.walkKV C2 (spB sy m0) (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK (toSign sy B)

/-- the walk of the pause bit up to the cut, then the first walk with the collision bits, then the second walk -/
def cfgPB (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 C2 : FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQB sy m0 C2) FrameKeep.fuelK (CtrlKeep.toA (watchB sy m0 v) (valB sy v) B) }

/-- the bytes under the mask of a block of Left are `FF` and the block of Left -/
def noLeftOK (sy : Syms) : Bool := (List.range 256).all fun n => n.toUInt8 &&& sy.noLeft != sy.noLeft || n.toUInt8 == 0xFF || n.toUInt8 == sy.noLeft

/-- **The check of the collision bits on a frame that moves right at the scroll handler** -/
def bCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := b1Search sy m0 v cuts
  let C1 := b1Cfg sy m0 v P
  let C2 := b2Cfg sy m0 P.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop && noLeftOK sy &&
    CtrlKeep.ctrlCheck1 (cfgPB sy m0 v q C1 C2) && C1.t.all (AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQB sy m0 C2) FrameKeep.fuelK) &&
    C2.t.all (CollideKeep.walkKV C2 (spB sy m0) (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK)

/-! ## The vertical force -/

/-- the vertical force -/
def vfI (sy : Syms) : Nat := (sy.VerticalForce &&& 0x7FF).toNat

/-- the guard of the walk of the vertical force: that of `FrameKeep.guardF`, with the vertical force and the player's state protected too -/
def guardVF (sy : Syms) (m0 : Machine) : PipeWrites.Guard :=
  { FrameKeep.guardF sy m0 with prot := [vfI sy, CollideKeep.stI sy] ++ (FrameKeep.guardF sy m0).prot }

/-- **What the walk of the vertical force asks at the frame's end**: it is still followed, or it is known to be `c` and the player's state is known to be 0 or 3 -/
def finVF (sy : Syms) (c : UInt8) (B : AS) : Bool :=
  (B.rk && !B.spent) || ((B.getK (vfI sy)).isK && (B.getK (vfI sy)).v == c && (B.getK (CollideKeep.stI sy)).isK &&
    ((B.getK (CollideKeep.stI sy)).v == 0 || (B.getK (CollideKeep.stI sy)).v == 3))

/-- the table's key: that of `PrevKeep.keyP`, and the known bits of the player's state once the vertical force is no longer followed. No part of the proof. -/
def keyVF (sy : Syms) (S : FrameKeep.Spot) (G : PipeWrites.Guard) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  PrevKeep.keyP S G [] A * 65536 + (if A.rk then 0 else num (A.getK (CollideKeep.stI sy)))

/-- the search of the walk of the vertical force from the states at the scroll handler `starts`: no part of the proof -/
def vfSearch (sy : Syms) (m0 : Machine) (c : UInt8) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := guardVF sy m0
  let E := { PipeEntryRule.envOf m0 with rkI := vfI sy }
  let key := keyVF sy S G
  let X := (starts.map AfterKeep.rkOn).foldl (PrevKeep.routeP S G [] key) {}
  CollideKeep.searchV S G E key (aRows E).toArray (CollideKeep.rkOff E) (finVF sy c) (FrameKeep.ctlI sy) sy.PlayerSubs { X }

/-- **The value that the frame's part after the scroll handler stores to the vertical force**, read from the search: the vertical force in the first state where the
walk has stopped following it. It is a parameter of the check and of the theorem, so nothing is assumed of it. -/
def vfC (sy : Syms) (m0 : Machine) (v : UInt8) : UInt8 :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  match (vfSearch sy m0 0 P.stops.toList).stops.toList with
  | b :: _ => (b.getK (vfI sy)).v
  | [] => 0

/-- **The table of the walk of the vertical force**, from the states at the scroll handler `starts` -/
def vfCfg (sy : Syms) (m0 : Machine) (c : UInt8) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardVF sy m0
  let E := { PipeEntryRule.envOf m0 with rkI := vfI sy }
  let key := keyVF sy S G
  let q := FrameKeep.tableOfKW key (vfSearch sy m0 c starts).X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := finVF sy c }

/-- **The check of the vertical force**: the walk of the pause bit up to the cut; from there the first walk of `AfterKeep` to the scroll handler; from there the walk
of the vertical force to the frame's end -/
def vfCheck (sy : Syms) (m0 : Machine) (v c : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let C2 := vfCfg sy m0 c P.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (CollideKeep.cfgPV sy m0 v q C1 C2) && C1.t.all (AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (CollideKeep.atQV sy C2) FrameKeep.fuelK) &&
    C2.t.all (CollideKeep.walkKV C2 (CollideKeep.rkOff C2.E) (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK)

/-! ## The pieces cover the machines -/

section
variable {E : Env} {F : Nat × UInt8}

/-- **The pieces of `Y` cover every machine**: the piece of its own value, which the known bits of `Y` allow -/
theorem cov_splitYAt (p : UInt16) : Cov E F (splitYAt p) := by
  intro B m hs
  unfold splitYAt
  split
  · have e4 : m.y.toNat.toUInt8 = m.y := by simp
    refine ⟨{ B with y := AB.known m.y.toNat.toUInt8 }, List.mem_map.2 ⟨m.y.toNat, List.mem_filter.2 ⟨List.mem_range.2 m.y.toNat_lt, ?_⟩, rfl⟩, { hs with y := ?_ }, rfl⟩
    · rw [e4]
      exact beq_iff_eq.2 hs.y
    · show (AB.known m.y.toNat.toUInt8).mem m.y
      rw [e4]
      exact mem_known_self _
  · exact ⟨B, List.mem_singleton.2 rfl, hs, rfl⟩

/-- pieces after pieces cover every machine -/
theorem cov_comp {f g : AS → List AS} (hf : Cov E F f) (hg : Cov E F g) : Cov E F (fun A => (f A).flatMap g) := by
  intro A m hs
  obtain ⟨B, hB, h1, h2⟩ := hf A m hs
  obtain ⟨D, hD, h3, h4⟩ := hg B m h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

end

/-! ## On the ROM: one frame -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-- the facing is protected by `FrameKeep.guardE` (`FrameKeep.faceE`) -/
theorem fdI_mem : fdI sy ∈ (FrameKeep.guardE sy m0).prot := by
  simp [FrameKeep.guardE, FrameKeep.faceE, fdI]

/-- the subspeed is protected by `FrameKeep.guardE` (`FrameKeep.faceE`) -/
theorem sfI_mem : CollideKeep.sfI sy ∈ (FrameKeep.guardE sy m0).prot := by
  simp [FrameKeep.guardE, FrameKeep.faceE, CollideKeep.sfI]

/-- **`CleanK` of the walk's guard for a byte of `zI` from `CleanK` of `FrameKeep.guardE`** -/
theorem cleanZ_of {q : UInt16} {m : Machine} {x : Nat} (hx : x ∈ zI sy) (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) :
    FrameKeep.CleanK (guardZ sy m0 x) q m := by
  refine FrameKeep.cleanK_sub h (fun y hy => ?_) rfl rfl rfl rfl
  simp only [guardZ, protZ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [zI, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hy with (rfl | rfl | rfl) | hy
  · rcases hx with rfl | rfl
    · exact fdI_mem
    · exact sfI_mem
  · exact CollideKeep.spI_mem
  · exact sfI_mem
  · exact List.mem_append_right _ hy

/-- **`CleanK` of the guard of the second walk of the collision bits from `CleanK` of `FrameKeep.guardE`** -/
theorem cleanB_of {q : UInt16} {m : Machine} (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) : FrameKeep.CleanK (guardB sy m0) q m := by
  refine FrameKeep.cleanK_sub h (fun y hy => ?_) rfl rfl rfl rfl
  simp only [guardB, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with (rfl | rfl) | hy
  · exact CollKeep.bitsI_mem
  · exact CollideKeep.spI_mem
  · exact List.mem_append_right _ hy

/-- **A frame in control keeps the facing and the subspeed from the scroll handler to its end, or it ends with the speed 0 and the subspeed 0.** The frame starts in the
idle loop in control (`FrameKeep.StartK`), each instruction meets `CleanK` of `FrameKeep.guardE` and writes neither the routine, nor the mode, nor the task by its
address; the area's type is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time. Then at each instruction `k ≥ n₀`
at the scroll handler, each of the two bytes is that of the frame's end, or the frame's end has the speed 0 and the subspeed 0. `hc`, `hk` are the checks on the ROM.
The proof is that of `CollideKeep.speed_end`, with the bytes of `zI` for the speed. -/
theorem keepZ_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hk : zCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ x ∈ zI sy, (frame m i).ram.get! x = (trace m i k).ram.get! x ∨
      (peek (frame m i) sy.Player_X_Speed = 0 ∧ peek (frame m i) sy.Player_X_MoveForce = 0) := by
  simp only [zCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
  obtain ⟨⟨⟨⟨hne1, hne2⟩, hp1⟩, hp2⟩, hp3⟩ := hk
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPZ sy m0 v q (AfterKeep.q1Cfg sy m0 v P) ((zI sy).map fun b => zCfg sy m0 b P.stops.toList)) hp1 rfl rfl rfl
      (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd h1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (h4 n₀ h)
    subst hk0
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (CtrlKeep.valA sy v) (trace m i k₀) := by
      intro w hw
      simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : AfterKeep.walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQZ sy ((zI sy).map fun b => zCfg sy m0 b P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclF hx'
    intro k hk hpc x hxI
    have hmem : zCfg sy m0 x P.stops.toList ∈ (zI sy).map fun b => zCfg sy m0 b P.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
    have hw2 := List.all_eq_true.1 hat _ hmem
    have ht2 := List.all_eq_true.1 hp3 _ hmem
    have hs2 : Sim (zCfg sy m0 x P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (AfterKeep.rkOn B₁) (trace m i k₁) := AfterKeep.sim_rkOn hs₁
    have hclZ : ∀ j, FrameKeep.CleanK (zCfg sy m0 x P.stops.toList).G (zCfg sy m0 x P.stops.toList).S.store (trace m i j) := fun j => cleanZ_of hxI (hcl j)
    obtain ⟨⟨B₂, hfin, hs₂⟩, hnoQ⟩ := CollideKeep.endKV (C := zCfg sy m0 x P.stops.toList) CollideKeep.cov_rkOff ht2 rfl rfl hne2 hw2 hs2 hf1 hd1 hclZ hx'
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [h1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exfalso
        have := hnoQ (k - k₁) (by omega)
        rw [show k₁ + (k - k₁) = k by omega] at this
        exact this hpc
    subst hkk
    change ((B₂.rk && !B₂.spent) || (CollideKeep.zeroAt (CollideKeep.spI sy) B₂ && CollideKeep.zeroAt (CollideKeep.sfI sy) B₂)) = true at hfin
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hfin
    rcases hfin with ⟨hr, hsp⟩ | ⟨hz1, hz2⟩
    · left
      have e := hs₂.rkv hr
      rw [if_neg (by simp [hsp])] at e
      exact e
    · right
      simp only [CollideKeep.zeroAt, Bool.and_eq_true, beq_iff_eq] at hz1 hz2
      exact ⟨(isK_eq hz1.1 (hs₂.ram (CollideKeep.spI sy) (PipeTransitionAll.mask_lt _))).trans hz1.2,
        (isK_eq hz2.1 (hs₂.ram (CollideKeep.sfI sy) (PipeTransitionAll.mask_lt _))).trans hz2.2⟩
  · exact absurd harr (hno n₀ hf0)

/-- the watched bytes of the first walk of the collision bits are RAM indices -/
theorem watchB_lt (v : UInt8) : ∀ w ∈ watchB sy m0 v, w.1 < 2048 := by
  intro w hw
  simp only [watchB, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact CtrlKeep.watchA_lt v w hw
  · exact PipeTransitionAll.mask_lt _

/-- a byte under the mask of a block of Left is `FF` or the block of Left -/
theorem noLeft_of (h : noLeftOK sy = true) {x : UInt8} (hx : x &&& sy.noLeft = sy.noLeft) : x = 0xFF ∨ x = sy.noLeft := by
  have h1 := List.all_eq_true.1 h x.toNat (List.mem_range.2 x.toNat_lt)
  have e : x.toNat.toUInt8 = x := by simp
  rw [e] at h1
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact absurd hx h1
  · exact Or.inl h1
  · exact Or.inr h1

/-- **A frame in control that moves right or not at all at the scroll handler ends with the collision bits `FF` or those of a block of Left, or with the speed 0.**
The frame starts in the idle loop in control with the collision bits `FF` or those of a block of Left (`hbits`: under the mask of a block of Left), each instruction
meets `CleanK` of `FrameKeep.guardE` and writes neither the routine, nor the mode, nor the task by its address; the area's type is `v`, the swimming flag 0, the
change of size 0. It comes to the player's routine at `n₀`, the first time, and once to the scroll handler after that (`honce`: `GuardE.subs_onceE`). Then at an
instruction `k ≥ n₀` at the scroll handler where the speed's sign bit is 0, the frame's end has the collision bits `FF` or those of a block of Left, or the speed 0.
`hc`, `hb` are the checks on the ROM. The first walk carries the collision bits from the cut to the scroll handler; the second splits `X` and `Y` in
`ImpedePlayerMove`, so that the side and the sign of the speed are known there. -/
theorem bits_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hb : bCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m)
    (hbits : peek m sy.Player_CollisionBits &&& sy.noLeft = sy.noLeft) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (honce : ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace m i k).pc = sy.PlayerSubs → (trace m i k').pc = sy.PlayerSubs → k = k') :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → peek (trace m i k) sy.Player_X_Speed &&& 0x80 = 0 →
      (peek (frame m i) sy.Player_CollisionBits = 0xFF ∨ peek (frame m i) sy.Player_CollisionBits = sy.noLeft) ∨ peek (frame m i) sy.Player_X_Speed = 0 := by
  simp only [bCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  obtain ⟨⟨⟨⟨⟨hne1, hne2⟩, hnl⟩, hp1⟩, hp2⟩, hp3⟩ := hb
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize b1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (FrameKeep.cleanK_of_E (hcl n))
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPB sy m0 v q (b1Cfg sy m0 v P) (b2Cfg sy m0 P.stops.toList)) hp1 rfl rfl rfl
      (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd h1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (h4 n₀ h)
    subst hk0
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (valB sy v) (trace m i k₀) := by
      intro w hw
      simp only [valB, CtrlKeep.valA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
      · show peek (trace m i k₀) sy.Player_CollisionBits &&& sy.noLeft = sy.noLeft &&& sy.noLeft
        rw [A.keep _ (by simp [CtrlKeep.keepA]), hbits, UInt8.and_self]
    have hsA := CtrlKeep.sim_toA (W := watchB sy m0 v) hs (watchB_lt v) hV
    have hw : AfterKeep.walkQ1 (b1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQB sy m0 (b2Cfg sy m0 P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (watchB sy m0 v) (valB sy v) B) = true := hB2
    have hclC : ∀ j, FrameKeep.CleanK (b1Cfg sy m0 v P).G (b1Cfg sy m0 v P).S.store (trace m i j) := fun j => CollKeep.cleanC_of (hcl j)
    obtain ⟨k₁, hk1, hq1, hf1, hd1, _, B₁, hat, hs₁⟩ :=
      AfterKeep.q1_run (C := b1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclC hx'
    intro k hk hpc hsign
    have hkk : k = k₁ := honce k k₁ hk (by omega) hpc hq1
    subst hkk
    have hW : FrameKeep.Watched (signW sy) (trace m i k) := by
      intro w hw'
      simp only [signW, List.mem_singleton] at hw'
      subst hw'
      show peek (trace m i k) sy.Player_X_Speed &&& 0x80 = 0 &&& 0x80
      rw [hsign]
      rfl
    have hs2 : Sim (b2Cfg sy m0 P.stops.toList).E (m.frame, (2 : UInt8)) (toSign sy B₁) (trace m i k) := FrameKeep.sim_watch hW (signW sy) (fun _ h => h) _ hs₁
    have hclB : ∀ j, FrameKeep.CleanK (b2Cfg sy m0 P.stops.toList).G (b2Cfg sy m0 P.stops.toList).S.store (trace m i j) := fun j => cleanB_of (hcl j)
    have hcov : Cov (b2Cfg sy m0 P.stops.toList).E (m.frame, (2 : UInt8)) (spB sy m0) :=
      cov_comp (CollKeep.cov_splitXAt _) (cov_comp (cov_splitYAt _) (cov_splitYAt _))
    obtain ⟨⟨B₂, hfin, hs₂⟩, _⟩ := CollideKeep.endKV (C := b2Cfg sy m0 P.stops.toList) hcov hp3 rfl rfl hne2 hat hs2 hf1 hd1 hclB hx'
    change (FrameKeep.watchOK [nlW sy] B₂ || CollideKeep.zeroAt (CollideKeep.spI sy) B₂) = true at hfin
    simp only [Bool.or_eq_true] at hfin
    rcases hfin with hwk | hz
    · left
      have hWd := FrameKeep.watched_of hwk hs₂ (nlW sy) (List.mem_singleton.2 rfl)
      have e : peek (frame m i) sy.Player_CollisionBits &&& sy.noLeft = sy.noLeft := by
        have e2 : peek (frame m i) sy.Player_CollisionBits &&& sy.noLeft = sy.noLeft &&& sy.noLeft := hWd
        rw [e2, UInt8.and_self]
      exact noLeft_of hnl e
    · right
      simp only [CollideKeep.zeroAt, Bool.and_eq_true, beq_iff_eq] at hz
      exact (isK_eq hz.1 (hs₂.ram (CollideKeep.spI sy) (PipeTransitionAll.mask_lt _))).trans hz.2
  · exact absurd harr (hno n₀ hf0)

/-- **`CleanK` of the guard of the walk of the vertical force from `CleanK` of `FrameKeep.guardE`** (`FrameKeep.stateE`) -/
theorem cleanVF_of {q : UInt16} {m : Machine} (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) : FrameKeep.CleanK (guardVF sy m0) q m := by
  refine FrameKeep.cleanK_sub h (fun y hy => ?_) rfl rfl rfl rfl
  simp only [guardVF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with (rfl | rfl) | hy
  · simp [FrameKeep.guardE, FrameKeep.stateE, vfI]
  · simp [FrameKeep.guardE, FrameKeep.stateE, CollideKeep.stI]
  · exact List.mem_append_right _ hy

/-- **A frame in control keeps the vertical force from the scroll handler to its end, or it ends with the vertical force `c` and the player's state 0 or 3.** The
frame starts in the idle loop in control (`FrameKeep.StartK`), each instruction meets `CleanK` of `FrameKeep.guardE` and writes neither the routine, nor the mode, nor
the task by its address; the area's type is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time. After the scroll
handler only the landing on a jumpspring stores the vertical force (the value `c`), and that landing sets the player's state to 0; the only later store to the state
by its address that the walk meets writes 0, or 3 in the climbing routine. `hc`, `hh` are the checks on the ROM. The proof is that of `CollideKeep.speed_end`. -/
theorem vf_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v c : UInt8} (hh : vfCheck sy m0 v c = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs →
      peek (frame m i) sy.VerticalForce = peek (trace m i k) sy.VerticalForce ∨
      (peek (frame m i) sy.VerticalForce = c ∧ (peek (frame m i) sy.Player_State = 0 ∨ peek (frame m i) sy.Player_State = 3)) := by
  simp only [vfCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨⟨⟨hne1, hne2⟩, hp1⟩, hp2⟩, hp3⟩ := hh
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := CollideKeep.cfgPV sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (vfCfg sy m0 c P.stops.toList)) hp1 rfl rfl rfl
      (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd h1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (h4 n₀ h)
    subst hk0
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (CtrlKeep.valA sy v) (trace m i k₀) := by
      intro w hw
      simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : AfterKeep.walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (CollideKeep.atQV sy (vfCfg sy m0 c P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclF hx'
    have hs2 : Sim (vfCfg sy m0 c P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! (vfI sy)) (AfterKeep.rkOn B₁) (trace m i k₁) :=
      AfterKeep.sim_rkOn hs₁
    have hclV : ∀ j, FrameKeep.CleanK (vfCfg sy m0 c P.stops.toList).G (vfCfg sy m0 c P.stops.toList).S.store (trace m i j) := fun j => cleanVF_of (hcl j)
    obtain ⟨⟨B₂, hfin, hs₂⟩, hnoQ⟩ := CollideKeep.endKV (C := vfCfg sy m0 c P.stops.toList) CollideKeep.cov_rkOff hp3 rfl rfl hne2 hat hs2 hf1 hd1 hclV hx'
    intro k hk hpc
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [h1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exfalso
        have := hnoQ (k - k₁) (by omega)
        rw [show k₁ + (k - k₁) = k by omega] at this
        exact this hpc
    subst hkk
    change ((B₂.rk && !B₂.spent) || ((B₂.getK (vfI sy)).isK && (B₂.getK (vfI sy)).v == c && (B₂.getK (CollideKeep.stI sy)).isK &&
      ((B₂.getK (CollideKeep.stI sy)).v == 0 || (B₂.getK (CollideKeep.stI sy)).v == 3))) = true at hfin
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hfin
    rcases hfin with ⟨hr, hsp⟩ | ⟨⟨⟨hk1', hc1⟩, hk2⟩, hst⟩
    · left
      have e := hs₂.rkv hr
      rw [if_neg (by simp [hsp])] at e
      exact e
    · right
      have e1 := isK_eq hk1' (hs₂.ram (vfI sy) (PipeTransitionAll.mask_lt _))
      have e2 := isK_eq hk2 (hs₂.ram (CollideKeep.stI sy) (PipeTransitionAll.mask_lt _))
      refine ⟨e1.trans hc1, ?_⟩
      rcases hst with h | h
      · exact Or.inl (e2.trans h)
      · exact Or.inr (e2.trans h)
  · exact absurd harr (hno n₀ hf0)

end

end Smbrta.FaceKeep
