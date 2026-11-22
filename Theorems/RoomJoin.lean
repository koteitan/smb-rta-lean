import Theorems.FastTakeoff
import Theorems.AirCap
import Theorems.LandDist
import Theorems.SidePipe
import Theorems.SideEntryRule
import Theorems.SideFrame
import Theorems.FrameModel
import Theorems.FrameTime
import Theorems.SurfaceFrames
import Theorems.VertAir
import Theorems.VertJump

/-!
# Joining the bonus room

`RoomRun` is what a real run in the room gives: real machines, frames of which `FrameModel.clean_frameR` proves that they follow `hstep` (with the frame's time, the horizontal bytes
at the player's routine and the position's range from `InRoom` and `far`: `FrameTime`), or that leave him stopped, the takeoff before the first frame
past the block's right end, the jump's frames in the vertical routine, how he leaves the block, and the entry frame. `entry_ge`
proves, from it and the checks of the earlier theorems, that the entry comes at least `goalF + aboveF` frames after first control.
Page: `1-1/c-5-RoomJoin.md`.

The arcs are hypotheses: that real frames follow `vstep` is not proved. What follows from them is proved
here, with the theorems of `AirCap`, `FastTakeoff` and `Jump`. Most fields are about one frame: the input and the height of a frame, standing, what the
left wall does to a frame, the stored speed, the entry. From these and small checks: before `hitF` he is left of the corner (`corner_late`), his feet are
low by the earliest jump (`low_by`), with no wall hit he stays on the floor up to an early takeoff (`floor_low`), `RunningSpeed` is 0 at a stop by `runF` or
he is far back (`run_short`). The room's frames are the frames of the real run from first control on that end not paused (`RoomRun.fe`, `RoomRun.fm`); the frames
that end paused in between keep what the model reads (`InRoom.keep`), so a run that pauses in the room is in it. The entry frame is defined on the real machines, `P(E)` is read at its end (`read_PE`), and the walks of the entering frame put it at the
mouth (`RoomRun.mouth_of`, `InRoom.mouthE`: `SideEntryEnd`, `SideEntryRest`).
The heights of the floor frames after the fall are proved (`RoomRun.vfloor_of`, once the field `vfloor`): with a jump in its input a frame takes off (`InRoom.jump`,
`offCheck`), with none it stays on the floor (`InRoom.floor`: the walk of `RoomFloor`, and `RoomLand.stand_at` on the floor's height), with the vertical page and the
vertical speed carried from the end of the fall (`RoomRun.floor_run`). `RoomMap` proves that no frame of the room before the entry comes to the head's collision with a
block (`InRoom.bump`). The frames of a jump's first frames follow `vstep` (`RoomCore.varc`, `RoomRun.varc_of`): the walks of `RoomVert`
give it on the real machines (`InRoom.vert`), with two relations on the machine at each frame's end that `RoomPair` proves (`InRoom.pair`): in a jump the jump's halt value
is 1, and A of the frame before is A. A on a frame is read from the vertical state (`Frames.a`). Every frame in the air follows `vstep` up to the landing (`InRoom.air`,
`RoomRun.vair_of`, `RoomRun.varc_all`: the walk of `RoomFall`), and so a landing is on a whole row with no speed (`RoomRun.stand_row_of`, once the field `stand_row`).
The vertical state at first control is one of `Nums.vStart` (`InRoom.vstart`), so up to the first stand the fall is a finite set of `vstepR` states (`fallLayer`,
`fallCheck`): `floor_at` is proved there (`RoomRun.floor_at_of`; page `1-1/c-7-5-4-FirstFall.md`). A frame that starts standing with no new press of A keeps the height and
the speed, or lands (`InRoom.stand`, `RoomRun.vstand_of`: the walk of `RoomStand`); so with no jump since first control the vertical states are again a finite set
(`noJumpCheck`), and `vfall` (now asked only with no jump since first control) and `fall_long` with no jump are proved (`RoomRun.vfall_of`, `RoomRun.fall_nojump`,
`RoomRun.fall_long_of`; page `1-1/c-7-5-5-RoomStand.md`). The input of a frame that does not follow the model is read from the machine (the field `read_stop`). A frame
that starts standing with a new press of A ends on the takeoff of its height and stored speed (`InRoom.jump`, `RoomRun.vjump_of`: `RoomJump.jump_room`). The vertical bytes
alone do not keep him off the floor after a jump: the landing that the walks give is at any height. The first stand of the fall does not follow `hstep` (`RoomRun.stand_first`, from `InRoom.wall`:
`RoomWall.wall_frame`; the field `stand_wall` asks only the later stands, `RoomRun.stand_off_of`); with the field `wall` the first stand away from the
floor is at frame `C + wallF` or later (`RoomRun.stand_late`), and from the landings of the first fall at these frames the vertical states with any input are a finite set
with no state on the floor before `C + fall` (`anyCheck`, `RoomRun.fall_any`): the old field `fall_jump` (page `1-1/c-7-5-6-RoomJump.md`). That he stands at the end of
the fall is proved too (`RoomRun.land_at_of`, `RoomRun.land_end_of`; once the field `land_at`). With no wall, a frame from `hitF` on that ends on the floor is `LowAt`
(`RoomRun.low_floor_of`, `low_floor_at`): at the block's left side the collision routine pushes him back (`InRoom.corner`: `RoomCorner.corner_frame`; page
`1-1/c-7-5-17-RoomCorner.md`). So is a frame of a jump from the floor that ends at `cornerY + 16` or below (`RoomRun.low_jump_of`, `RoomCore.low_jump`, `arc_down`): the
vertical page stays 1 through the takeoff and the rising frames, and they end `CornerEnd` there (`InRoom.highJ`, `InRoom.highA`; page `1-1/c-7-5-18-RoomHigh.md`).
`low_by` gives each frame its own bound `lowB`, one frame at the top speed per frame after `hitF − 1` or after `runF` (page `1-1/c-7-5-20-LowBound.md`). The frames
above `cornerY + 16` after `runF` when every frame from `runF` on is at or past the corner were the field `low_at`; since round 28 it is gone (page
`1-1/c-7-5-21-PushOne.md`): the frames of `low_floor` and `low_jump` are within the least slack `lowT = 16·top − 257` of the corner (`LowS`, `SlackOK`), after such a
frame at or past the corner (stopped or moving left) a frame in the air moves him at most one pixel right (`RoomCore.push_one`, `RoomRun.push_one_of`, `gainCheck`), so
the first frame above `cornerY + 16` after `runF` is within `16·top − 1` of the corner and the frames after it within one frame at the top speed more each; and frame
`runF` itself ends at `cornerY + 16` or below: the takeoff frame reads the stored speed (`RoomCore.off_ab`), right after the fall it is below the air threshold, and
the jumps rise slowly (`riseCheck`).

The case split, all by `cases` and `by_cases`:
* over the block in one jump (no landing): impossible, `no_landing`;
* onto the block, with a stop from `hitF` on (a hit at the corner on the floor or in the air, a fast jump with a stale speed after a
  hit, a jump from the side of the block): short of the goal, `stop_short`;
* with no such stop, after a wall hit before `hitF`: short of the goal, whatever he does, `wall_short`. It looks at no jump, so a run that stands on the wall
  and never touches the floor is in it;
* with no such stop and no wall hit, onto the block: a takeoff after the last one searched (top speed), or a slow takeoff (air speed cap), or a fast
  takeoff (the search of `FastTakeoff`), `landed_short`. A big player's last low frame may be past the corner (`Approach.low`: a coin above the block's left
  column takes the side check on that frame; asked only at or past the corner and off the frames that `low_jump` proves, page `1-1/c-7-14-3-ApproachJump.md`); then a fast takeoff is the search with one low air frame less (`fast_short`, `roomB`), a slow one after the first
  frame after the fall is the bound from the frame before with the landing one frame later (`slowBigOk`, page `1-1/c-7-14-1-BigApproach.md`), and a slow
  one on that frame is the search of `LandDist` from the room's first frame with the table of the frames after the landing (`Checks.slowLand`, page
  `1-1/c-7-14-2-LandDist.md`);
* then off the block by a fast jump, a slow jump or stepping off, `entry_ge`.
-/


namespace Smbrta.FrameModel
open PipeTransition (frame)
open PipeEntryRule (trace)


/-- **`FrameModel.frame_readR` with the end of the move**: the frame is a `TopSpeed.Frame`, and its `P₂`, `v₂`, `f₂` are the position, the speed and its fraction at an
instruction `n₀ + k` of the frame at `PlayerSubs`. The proof is that of `frame_readR`. -/
theorem frame_readQ {sy : Syms} {m0 : Machine} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} {idle : UInt16} (hOK : modelOK sy m0 S = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true)
    (h : ReadR sy (Rom.of m0) S M i n₀) (hbef : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a) (hT : InTime (Rom.of m0) idle M i n₀)
    (hfar : 2048 ≤ posP sy M ∧ posP sy M + 2048 < 0x1000000) :
    ∃ (f : TopSpeed.Frame (TopSpeed.top sy : Int) (amax sy m0)) (k : Nat), f.v = sbyte (peek M sy.Player_X_Speed) ∧
      f.f = ((peek M sy.Player_X_MoveForce).toNat : Int) ∧ f.P = posP sy M ∧
      f.v' = sbyte (peek (frame M i) sy.Player_X_Speed) ∧ f.f' = ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int) ∧ f.P' = posP sy (frame M i) ∧
      (trace M i (n₀ + k)).pc = sy.PlayerSubs ∧ (trace M i (n₀ + k)).frame = M.frame ∧ f.P₂ = posP sy (trace M i (n₀ + k)) ∧
      f.v₂ = sbyte (peek (trace M i (n₀ + k)) sy.Player_X_Speed) ∧ f.f₂ = ((peek (trace M i (n₀ + k)) sy.Player_X_MoveForce).toNat : Int) := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  obtain ⟨k1, v₁, f₁, b1, A1, an, G1, S1, I1⟩ := frame_pathI hb hfr hF h.at_frame
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h.at_frame)
  have e4 : t = (planOf sy m0 S (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, b2, g2, p2, v2, ff2, d2, r2, m2, q2, I2⟩ := tail_spec htl hF.digits A1
  obtain ⟨e0, e0f⟩ := trace_inFrame hT.loop hT.start (InFrameN.add' I1 rfl I2) hT.time (k1 + k2) (Nat.le_refl _)
  rw [stepN_add] at e0
  generalize hB : stepN k2 (stepN k1 (trace M i n₀)) = B at e0 v2 ff2 q2 p2
  have hco := h.collide (n₀ + (k1 + k2)) (by omega) (by rw [e0]; exact p2)
  rw [e0] at hco
  have ev : peek (trace M i n₀) sy.Player_X_Speed = peek M sy.Player_X_Speed := hbef _ (by simp [hBytes])
  have ef : peek (trace M i n₀) sy.Player_X_MoveForce = peek M sy.Player_X_MoveForce := hbef _ (by simp [hBytes])
  have eP : posP sy (trace M i n₀) = posP sy M := posP_congr hbef
  obtain ⟨g1, g2'⟩ := G1
  have ePk : posP sy (stepN k1 (trace M i n₀)) = posP sy (trace M i n₀) := by
    rw [posP_eq, posP_eq]
    obtain ⟨s1, s2, s3⟩ := S1
    show posOf ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_PageLoc)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Position)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.SprObject_X_MoveForce)) =
      posOf ((trace M i n₀).ram.get! (I sy.Player_PageLoc)) ((trace M i n₀).ram.get! (I sy.Player_X_Position)) ((trace M i n₀).ram.get! (I sy.SprObject_X_MoveForce))
    rw [s1, s2, s3]
  have hv2 : B.ram.get! (I sy.Player_X_Speed) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed) := v2
  have hf2 : B.ram.get! (I sy.Player_X_MoveForce) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce) := ff2
  have hr1 := speed_int g1
  have hmove : posP sy B = posP sy M + 16 * sbyte (B.ram.get! (I sy.Player_X_Speed)) := by
    rw [hv2]
    obtain ⟨a1, a2⟩ := posOf_range (peek B sy.Player_PageLoc) (peek B sy.Player_X_Position) (peek B sy.SprObject_X_MoveForce)
    rw [← posP_eq] at a1 a2
    have a3 := sbyte_range ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed))
    have a4 := hfar
    rw [ePk, eP] at q2
    omega
  have hfr1 := ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce)).toNat_lt
  refine ⟨{ v := sbyte (peek M sy.Player_X_Speed), f := ((peek M sy.Player_X_MoveForce).toNat : Int), P := posP sy M,
            v₁ := sbyte v₁, f₁ := (f₁.toNat : Int),
            v₂ := sbyte (B.ram.get! (I sy.Player_X_Speed)), f₂ := ((B.ram.get! (I sy.Player_X_MoveForce)).toNat : Int), P₂ := posP sy B,
            v' := sbyte (peek (frame M i) sy.Player_X_Speed), f' := ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int), P' := posP sy (frame M i),
            anim := ?_, friction := ?_, friction_gain := ?_, frac := ?_, move := hmove, impedeV := ?_, impedeF := ?_, impedeP := ?_ },
          k1 + k2, rfl, rfl, rfl, rfl, rfl, rfl, by rw [e0]; exact p2, e0f, by rw [e0], by rw [e0]; rfl, by rw [e0]; rfl⟩
  · rcases an with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [a1]
        exact congrArg sbyte ev
      · rw [a2]
        exact congrArg (fun x : UInt8 => (x.toNat : Int)) ef
    · right
      rw [a1, a2]
      exact ⟨rfl, rfl⟩
  · intro _
    rw [hv2]
    exact hr1
  · rw [hv2, hf2]
    exact g2'
  · rw [hf2]
    omega
  · rcases hco.v with e | e
    · left
      rw [e]
      rfl
    · right
      rw [e]
      rfl
  · rw [hco.f]
    rfl
  · have e := hco.P
    rcases e with e | e | ⟨e, e2⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · refine Or.inr (Or.inr ⟨?_, e2⟩)
      have hm := hmove
      have e3 : sbyte (B.ram.get! (I sy.Player_X_Speed)) ≤ 0 := e2
      omega

/-! ### The lower bound of the friction (round 30)

`TopSpeed.frictionCheck` bounds the speed after `ImposeFriction` from above. `frictionLowCheck` is the other side on the same machines: the speed with its fraction is at
least `min(V, 0)` less the adder. With a press to the left the routine takes the adder off, and the left cap only raises the speed; with no press or a press to the right it
adds the adder to a negative speed, and the right cap is not negative. `fric_readL`, `frame_pathL` and `frame_readQL` are `fric_readI`, `frame_pathI` and `frame_readQ`
with this bound in their conclusions; the proofs are theirs. -/

/-- **`ImposeFriction` lowers the speed with its fraction by at most the adder below `min(V, 0)`**, on the machines of `TopSpeed.frictionCheck` -/
def frictionLowCheck (sy : Syms) (m0 : Machine) : Bool :=
  (TopSpeed.speedsB sy).all fun v => TopSpeed.bytes.all fun fr => (adders sy m0).all fun (lo, hi) =>
  (maxRs sy m0).all fun mr => (maxLs sy m0).all fun ml => (TopSpeed.upTo 3).all fun a => (TopSpeed.collBits sy).all fun cb =>
    let m := poke m0 sy.Player_X_Speed v
    let m := poke m sy.Player_X_MoveForce fr
    let m := poke m sy.FrictionAdderLow lo
    let m := poke m sy.FrictionAdderHigh hi
    let m := poke m sy.MaximumRightSpeed mr
    let m := poke m sy.MaximumLeftSpeed ml
    let m := poke m sy.Player_CollisionBits cb
    let m := runSub m sy.ImposeFriction a 0 0
    let V := 256 * sbyte v + fr.toNat
    let V' := 256 * sbyte (peek m sy.Player_X_Speed) + (peek m sy.Player_X_MoveForce).toNat
    decide (min V 0 - (256 * hi.toNat + lo.toNat : Int) ≤ V')

/-- the speed with its fraction is at least `min(V₁, 0) − amax` -/
def lowOK (sy : Syms) (m0 r : Machine) (v₁ f₁ : UInt8) : Prop :=
  min (256 * sbyte v₁ + (f₁.toNat : Int)) 0 - amax sy m0 ≤ 256 * sbyte (r.ram.get! (I sy.Player_X_Speed)) + ((r.ram.get! (I sy.Player_X_MoveForce)).toNat : Int)

section lowF
variable {sy : Syms} {E : Rom}

/-- `FrameTime`'s `fric_readI` with the lower bound of `frictionLowCheck` (round 30) -/
theorem fric_readL {m0 : Machine} {c3 c4 : Cut} {r3 : UInt16} {lr : UInt8} {R : Machine} {mr ml lo hi : UInt8}
    (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hlow : frictionLowCheck sy m0 = true) (hnd : nodupB (fricIdx sy) = true) (hsp : (TopSpeed.speedsB sy).contains (R.ram.get! (I sy.Player_X_Speed)) = true)
    (h1 : leafAll (Rom.of m0) m0.s sy.ImposeFriction r3 (Tag.kn lr lr) (tagsFr sy) [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq)]
      ([I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ c3.ids) = true)
    (h2 : pieceOK (Rom.of m0) (afterLeaf c3 r3) c4 (watchM sy) fuelS = true) (hra : c3.ra = some lr) (hpc : c3.pc = sy.ImposeFriction) (hlr : (TopSpeed.upTo 3).contains lr = true)
    (hA : At (Rom.of m0) c3 R) (hK3 : ∀ p ∈ c3.K, p.1 < 2048)
    (e1 : R.ram.get! (I sy.MaximumRightSpeed) = mr) (e2 : R.ram.get! (I sy.MaximumLeftSpeed) = ml) (e3 : R.ram.get! (I sy.FrictionAdderLow) = lo) (e4 : R.ram.get! (I sy.FrictionAdderHigh) = hi)
    (m1 : mr ∈ maxRs sy m0) (m2 : ml ∈ maxLs sy m0) (m3 : (lo, hi) ∈ adders sy m0) (hcb : R.ram.get! (I sy.Player_CollisionBits) ∈ TopSpeed.collBits sy) :
    ∃ k, k ≤ 2 * fuelS ∧ At (Rom.of m0) c4 (stepN k R) ∧ gainOK sy m0 (stepN k R) (R.ram.get! (I sy.Player_X_Speed)) (R.ram.get! (I sy.Player_X_MoveForce)) ∧
      lowOK sy m0 (stepN k R) (R.ram.get! (I sy.Player_X_Speed)) (R.ram.get! (I sy.Player_X_MoveForce)) ∧ Same3 sy (stepN k R) R ∧ InFrameN (Rom.of m0) R k := by
  generalize hv0 : R.ram.get! (I sy.Player_X_Speed) = v at hsp
  generalize hf0 : R.ram.get! (I sy.Player_X_MoveForce) = f
  generalize hc0 : R.ram.get! (I sy.Player_CollisionBits) = cb at hcb
  have hH := pokeL_good (fricL sy v f lo hi mr ml cb) hb
  have hHs : (pokeL m0 (fricL sy v f lo hi mr ml cb)).s = m0.s := pokeL_s _ _
  have hget : ∀ q ∈ fricL sy v f lo hi mr ml cb, (pokeL m0 (fricL sy v f lo hi mr ml cb)).ram.get! (I q.1) = q.2 := pokeL_get _ _ hb hnd
  have hrel : ∀ p ∈ tagsFr sy, p.2.R (R.ram.get! p.1) ((pokeL m0 (fricL sy v f lo hi mr ml cb)).ram.get! p.1) := by
    intro p hp
    simp only [tagsFr, fricIdx, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show _ = _
      rw [hget (sy.Player_X_Speed, v) (by simp [fricL])]
      exact hv0
    · show _ = _
      rw [hget (sy.Player_X_MoveForce, f) (by simp [fricL])]
      exact hf0
    · show _ = _
      rw [hget (sy.FrictionAdderLow, lo) (by simp [fricL])]
      exact e3
    · show _ = _
      rw [hget (sy.FrictionAdderHigh, hi) (by simp [fricL])]
      exact e4
    · show _ = _
      rw [hget (sy.MaximumRightSpeed, mr) (by simp [fricL])]
      exact e1
    · show _ = _
      rw [hget (sy.MaximumLeftSpeed, ml) (by simp [fricL])]
      exact e2
    · show _ = _
      rw [hget (sy.Player_CollisionBits, cb) (by simp [fricL])]
      exact hc0
  have hae : R.a = lr := hA.ra lr hra
  obtain ⟨k1, f1, g1, p1, s1, o1, w1, _, _, _, I1⟩ := leaf_app h1 hA.good (by rw [hA.pc, hpc]) (by rw [hae]; exact Tag.R_kn _ _) hH hHs hrel
  have hAf := at_after (r := r3) hA g1 p1 s1 (fun p hp => w1 _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (hK3 p hp))
  obtain ⟨k2, f2, A2, W2, _, I2⟩ := piece_spec h2 hAf
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  have oV : (stepN k1 R).ram.get! (I sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := o1 (I sy.Player_X_Speed, .eq) (by simp)
  have oF : (stepN k1 R).ram.get! (I sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := o1 (I sy.Player_X_MoveForce, .eq) (by simp)
  -- what `frictionCheck` says
  have hC := hfr
  simp only [TopSpeed.frictionCheck, List.all_eq_true] at hC
  have hq := hC v (List.contains_iff_mem.1 hsp) f (Potential.mem_bytes f) (lo, hi) m3 mr m1 ml m2 lr (List.contains_iff_mem.1 hlr) cb hcb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  have hk : pokeL m0 (fricL sy v f lo hi mr ml cb) = poke (poke (poke (poke (poke (poke (poke m0 sy.Player_X_Speed v) sy.Player_X_MoveForce f) sy.FrictionAdderLow lo) sy.FrictionAdderHigh hi) sy.MaximumRightSpeed mr) sy.MaximumLeftSpeed ml) sy.Player_CollisionBits cb := by
    simp only [fricL, pokeL]
  rw [← hk] at hq
  have hL := hlow
  simp only [frictionLowCheck, List.all_eq_true] at hL
  have hq2 := hL v (List.contains_iff_mem.1 hsp) f (Potential.mem_bytes f) (lo, hi) m3 mr m1 ml m2 lr (List.contains_iff_mem.1 hlr) cb hcb
  simp only [decide_eq_true_eq] at hq2
  rw [← hk] at hq2
  have hal := adder_le m3
  have w1' : ∀ i, i ∈ [I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] → (stepN k1 R).ram.get! i = R.ram.get! i := by
    intro i hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl
    · exact w1 _ (by simp) (I_lt _)
    · exact w1 _ (by simp) (I_lt _)
    · exact w1 _ (by simp) (I_lt _)
  have e5 : (stepN k2 (stepN k1 R)).ram.get! (I sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := by
    rw [W2 _ (by simp [watchM]) (I_lt _)]
    exact oV
  have e6 : (stepN k2 (stepN k1 R)).ram.get! (I sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := by
    rw [W2 _ (by simp [watchM]) (I_lt _)]
    exact oF
  refine ⟨k1 + k2, by omega, by rw [e]; exact A2, ?_, ?_, ?_, InFrameN.add' I1 rfl I2⟩
  · rw [e]
    refine ⟨?_, ?_⟩
    · rw [e5]
      exact hq.1.1
    · rw [e5, e6]
      have h7 := hq.2
      have h8 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := rfl
      have h9 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := rfl
      rw [h8, h9] at h7
      omega
  · rw [e]
    unfold lowOK
    rw [e5, e6]
    have h7 := hq2
    have h8 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := rfl
    have h9 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := rfl
    rw [h8, h9] at h7
    omega
  · rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]

/-- `FrameTime`'s `frame_pathI` with the lower bound of `frictionLowCheck` at the mover (round 30) -/
theorem frame_pathL {m0 : Machine} {S : UInt8} {R : Machine} (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hlow : frictionLowCheck sy m0 = true) (hF : ModelFacts sy m0 S)
    (h : AtFrame sy (Rom.of m0) S R) :
    ∃ k v₁ f₁, k ≤ fuelW + 6 * fuelS ∧ At (Rom.of m0) (planOf sy m0 S (caseOf sy R)).c4 (stepN k R) ∧
      ((v₁ = R.ram.get! (I sy.Player_X_Speed) ∧ f₁ = R.ram.get! (I sy.Player_X_MoveForce)) ∨ (v₁ = 0 ∧ f₁ = 0)) ∧
      gainOK sy m0 (stepN k R) v₁ f₁ ∧ lowOK sy m0 (stepN k R) v₁ f₁ ∧ Same3 sy (stepN k R) R ∧ InFrameN (Rom.of m0) R k := by
  have hmem := caseOf_memF h
  have hA := at_startF h
  obtain ⟨hc, hc2⟩ := hF.cases _ hmem
  generalize hcc : caseOf sy R = c at hmem hA hc hc2 ⊢
  simp only [caseOK, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [frameCaseOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hc2
  generalize planOf sy m0 S c = P at hc hc2 ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, a9⟩, _⟩, _⟩ := hc
  obtain ⟨⟨⟨hlr, x1⟩, x2⟩, x3⟩ := hc2
  have hzero : TopSpeed.inSpeed sy (0 : UInt8) = true := by
    simp only [TopSpeed.inSpeed, decide_eq_true_eq]
    show ((0 : Int)).natAbs ≤ _
    simp
  have hsp : TopSpeed.inSpeed sy (R.ram.get! (I sy.Player_X_Speed)) = true := h.speed
  have hco : R.ram.get! (I sy.Player_CollisionBits) ∈ TopSpeed.collBits sy := h.coll
  obtain ⟨k1, f1, A1, W1, B1, I1⟩ := piece_spec a1 hA
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have wG : ∀ j ∈ I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy, j < 2048 → R1.ram.get! j = R.ram.get! j := W1
  obtain ⟨k2, Q2, f2, A2, W2, _, cg, L2, I2⟩ := piece_specX (c' := afterLeaf P.c1 P.r1) (watch := I sy.SavedJoypadBits :: watchH sy) (extra := capsGood sy m0) x1 A1
  generalize hR2 : stepN k2 R1 = R2 at A2 W2 L2
  obtain ⟨mr, ml, lo, hi, c1, c2, c3, c4, m1, m2, m3⟩ := capsGood_spec cg L2
  have wX : ∀ j ∈ I sy.SavedJoypadBits :: watchH sy, j < 2048 → R2.ram.get! j = R1.ram.get! j := W2
  have hk : ∀ j ∈ watchH sy, j < 2048 → R2.ram.get! j = R.ram.get! j := fun j hj hl => by
    rw [wX j (List.mem_cons_of_mem _ hj) hl, wG j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hl]
  have hS2 : Same3 sy R2 R := ⟨hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)⟩
  have spL := fun {v : UInt8} (e : TopSpeed.inSpeed sy v = true) => speed_list hF.scomp e
  by_cases h0 : stOf c.n = 0
  · -- on the ground
    simp only [if_pos h0, Bool.and_eq_true] at a9
    obtain ⟨g, fc⟩ := a9
    simp only [groundOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at g
    obtain ⟨⟨⟨⟨b1, b2⟩, _⟩, b4⟩, b5⟩ := g
    simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
    obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
    obtain ⟨k3, f3, A3, W3, B3, I3⟩ := piece_spec b2 A2
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have x2' : walkT (Rom.of m0) (fun Q => Q.pc == P.r2) (fun Q => goalC (afterLeaf P.c2 P.r2) ([I sy.PlayerFacingDir, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy) Q && animGood sy Q) fuelS (startQ P.c2) = true := by
      rcases x2 with x2 | x2
      · exact absurd h0 x2
      · exact x2
    obtain ⟨k4, Q4, f4, A4, W4, _, ag, L4, I4⟩ := piece_specX (c' := afterLeaf P.c2 P.r2) (extra := animGood sy) x2' A3
    generalize hR4 : stepN k4 R3 = R4 at A4 W4 L4
    have an := animGood_spec ag L4
    obtain ⟨k5, f5, A5, W5, B5, I5⟩ := piece_spec b4 A4
    generalize hR5 : stepN k5 R4 = R5 at A5 W5
    have wf : ∀ j ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy,
        j < 2048 → R5.ram.get! j = R4.ram.get! j := fun j hj hl => W5 j (List.mem_append_left _ hj) hl
    have hCaps : ∀ j ∈ capsL sy, R5.ram.get! j = R2.ram.get! j := fun j hj => by
      have hl : j < 2048 := by
        simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
      rw [wf j (List.mem_append_right _ hj) hl, W4 j (List.mem_append_right _ hj) hl, W3 j (by
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl]
    have hcoll5 : R5.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
      rw [wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
    have hsp5 : TopSpeed.inSpeed sy (R5.ram.get! (I sy.Player_X_Speed)) = true := by
      rw [wf _ (by simp) (I_lt _)]
      rcases an with an | an
      · rw [an.1, W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
        exact hsp
      · rw [an.1]
        exact hzero
    obtain ⟨k6, f6, A6, G6, L6, S6, I6⟩ := fric_readL hb hfr hlow hF.fnd (spL hsp5) (x3.resolve_left (fun e => e.1 h0)) d4 d1 d2 hlr A5 B5
      (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
      m1 m2 m3 (by rw [hcoll5]; exact hco)
    have hfin : stepN (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) R = stepN k6 R5 := by
      rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3, stepN_add, hR4, stepN_add, hR5]
    refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + k6)))), R5.ram.get! (I sy.Player_X_Speed), R5.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A6, ?_, by rw [hfin]; exact G6, by rw [hfin]; exact L6, ?_,
      InFrameN.add' I1 hR1 (InFrameN.add' I2 hR2 (InFrameN.add' I3 hR3 (InFrameN.add' I4 hR4 (InFrameN.add' I5 hR5 I6))))⟩
    · rw [wf _ (by simp) (I_lt _), wf _ (by simp) (I_lt _)]
      rcases an with an | an
      · left
        rw [an.1, an.2, W3 _ (by simp [watchA, watchH]) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
        exact ⟨rfl, rfl⟩
      · exact Or.inr an
    · rw [hfin]
      obtain ⟨s1, s2, s3⟩ := S6
      obtain ⟨t1, t2, t3⟩ := hS2
      refine ⟨?_, ?_, ?_⟩
      · rw [s1, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
      · rw [s2, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
      · rw [s3, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
  · simp only [if_neg h0] at a9
    by_cases hl : (lrOf c.n != 0) = true
    · -- in the air, with Left or Right
      rw [if_pos hl] at a9
      simp only [Bool.and_eq_true] at a9
      obtain ⟨g, fc⟩ := a9
      simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
      obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
      obtain ⟨k3, f3, A3, W3, B3, I3⟩ := piece_spec g A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hCaps : ∀ j ∈ capsL sy, R3.ram.get! j = R2.ram.get! j := fun j hj => by
        have hl : j < 2048 := by
          simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
        exact W3 j (List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_X_MoveForce) = R.ram.get! (I sy.Player_X_MoveForce) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e3 : R3.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have hne : lrOf c.n ≠ 0 := by simpa using hl
      obtain ⟨k6, f6, A6, G6, L6, S6, I6⟩ := fric_readL hb hfr hlow hF.fnd (spL (by rw [e1]; exact hsp)) (x3.resolve_left (fun e => hne e.2)) d4 d1 d2 hlr A3 B3
        (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
        m1 m2 m3 (by rw [e3]; exact hco)
      have hfin : stepN (k1 + (k2 + (k3 + k6))) R = stepN k6 R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3]
      refine ⟨k1 + (k2 + (k3 + k6)), R3.ram.get! (I sy.Player_X_Speed), R3.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A6, Or.inl ⟨e1, e2⟩, by rw [hfin]; exact G6, by rw [hfin]; exact L6, ?_,
        InFrameN.add' I1 hR1 (InFrameN.add' I2 hR2 (InFrameN.add' I3 hR3 I6))⟩
      rw [hfin]
      obtain ⟨s1, s2, s3⟩ := S6
      obtain ⟨t1, t2, t3⟩ := hS2
      refine ⟨?_, ?_, ?_⟩
      · rw [s1, W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
      · rw [s2, W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
      · rw [s3, W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
    · -- in the air, with neither
      rw [if_neg hl] at a9
      obtain ⟨k3, f3, A3, W3, _, I3⟩ := piece_spec a9 A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hfin : stepN (k1 + (k2 + k3)) R = R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, hR3]
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_X_MoveForce) = R.ram.get! (I sy.Player_X_MoveForce) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      refine ⟨k1 + (k2 + k3), R.ram.get! (I sy.Player_X_Speed), R.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A3, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_,
        InFrameN.add' I1 hR1 (InFrameN.add' I2 hR2 I3)⟩
      · rw [hfin]
        refine ⟨by rw [e1]; exact hsp, ?_⟩
        rw [e1, e2]
        have := FastAccel.amax_nonneg sy m0
        omega
      · rw [hfin]
        unfold lowOK
        rw [e1, e2]
        have := FastAccel.amax_nonneg sy m0
        omega
      · rw [hfin]
        obtain ⟨t1, t2, t3⟩ := hS2
        refine ⟨?_, ?_, ?_⟩
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t3]

end lowF

/-- **`frame_readQ` with the lower bound of the friction** (round 30): with `frictionLowCheck`, the speed with its fraction at the end of the move is at least `min(V₁, 0) − amax`,
where `V₁` is the speed with its fraction after the animation routine (`TopSpeed.Frame.v₁`, `f₁`). The proof is that of `frame_readQ`. -/
theorem frame_readQL {sy : Syms} {m0 : Machine} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} {idle : UInt16} (hOK : modelOK sy m0 S = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hlow : frictionLowCheck sy m0 = true)
    (h : ReadR sy (Rom.of m0) S M i n₀) (hbef : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a) (hT : InTime (Rom.of m0) idle M i n₀)
    (hfar : 2048 ≤ posP sy M ∧ posP sy M + 2048 < 0x1000000) :
    ∃ (f : TopSpeed.Frame (TopSpeed.top sy : Int) (amax sy m0)) (k : Nat), f.v = sbyte (peek M sy.Player_X_Speed) ∧
      f.f = ((peek M sy.Player_X_MoveForce).toNat : Int) ∧ f.P = posP sy M ∧
      f.v' = sbyte (peek (frame M i) sy.Player_X_Speed) ∧ f.f' = ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int) ∧ f.P' = posP sy (frame M i) ∧
      (trace M i (n₀ + k)).pc = sy.PlayerSubs ∧ (trace M i (n₀ + k)).frame = M.frame ∧ f.P₂ = posP sy (trace M i (n₀ + k)) ∧
      f.v₂ = sbyte (peek (trace M i (n₀ + k)) sy.Player_X_Speed) ∧ f.f₂ = ((peek (trace M i (n₀ + k)) sy.Player_X_MoveForce).toNat : Int) ∧
      min (256 * f.v₁ + f.f₁) 0 - amax sy m0 ≤ 256 * f.v₂ + f.f₂ := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  obtain ⟨k1, v₁, f₁, b1, A1, an, G1, L1, S1, I1⟩ := frame_pathL hb hfr hlow hF h.at_frame
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h.at_frame)
  have e4 : t = (planOf sy m0 S (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, b2, g2, p2, v2, ff2, d2, r2, m2, q2, I2⟩ := tail_spec htl hF.digits A1
  obtain ⟨e0, e0f⟩ := trace_inFrame hT.loop hT.start (InFrameN.add' I1 rfl I2) hT.time (k1 + k2) (Nat.le_refl _)
  rw [stepN_add] at e0
  generalize hB : stepN k2 (stepN k1 (trace M i n₀)) = B at e0 v2 ff2 q2 p2
  have hco := h.collide (n₀ + (k1 + k2)) (by omega) (by rw [e0]; exact p2)
  rw [e0] at hco
  have ev : peek (trace M i n₀) sy.Player_X_Speed = peek M sy.Player_X_Speed := hbef _ (by simp [hBytes])
  have ef : peek (trace M i n₀) sy.Player_X_MoveForce = peek M sy.Player_X_MoveForce := hbef _ (by simp [hBytes])
  have eP : posP sy (trace M i n₀) = posP sy M := posP_congr hbef
  obtain ⟨g1, g2'⟩ := G1
  have ePk : posP sy (stepN k1 (trace M i n₀)) = posP sy (trace M i n₀) := by
    rw [posP_eq, posP_eq]
    obtain ⟨s1, s2, s3⟩ := S1
    show posOf ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_PageLoc)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Position)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.SprObject_X_MoveForce)) =
      posOf ((trace M i n₀).ram.get! (I sy.Player_PageLoc)) ((trace M i n₀).ram.get! (I sy.Player_X_Position)) ((trace M i n₀).ram.get! (I sy.SprObject_X_MoveForce))
    rw [s1, s2, s3]
  have hv2 : B.ram.get! (I sy.Player_X_Speed) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed) := v2
  have hf2 : B.ram.get! (I sy.Player_X_MoveForce) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce) := ff2
  have hr1 := speed_int g1
  have hmove : posP sy B = posP sy M + 16 * sbyte (B.ram.get! (I sy.Player_X_Speed)) := by
    rw [hv2]
    obtain ⟨a1, a2⟩ := posOf_range (peek B sy.Player_PageLoc) (peek B sy.Player_X_Position) (peek B sy.SprObject_X_MoveForce)
    rw [← posP_eq] at a1 a2
    have a3 := sbyte_range ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed))
    have a4 := hfar
    rw [ePk, eP] at q2
    omega
  have hfr1 := ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce)).toNat_lt
  refine ⟨{ v := sbyte (peek M sy.Player_X_Speed), f := ((peek M sy.Player_X_MoveForce).toNat : Int), P := posP sy M,
            v₁ := sbyte v₁, f₁ := (f₁.toNat : Int),
            v₂ := sbyte (B.ram.get! (I sy.Player_X_Speed)), f₂ := ((B.ram.get! (I sy.Player_X_MoveForce)).toNat : Int), P₂ := posP sy B,
            v' := sbyte (peek (frame M i) sy.Player_X_Speed), f' := ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int), P' := posP sy (frame M i),
            anim := ?_, friction := ?_, friction_gain := ?_, frac := ?_, move := hmove, impedeV := ?_, impedeF := ?_, impedeP := ?_ },
          k1 + k2, rfl, rfl, rfl, rfl, rfl, rfl, by rw [e0]; exact p2, e0f, by rw [e0], by rw [e0]; rfl, by rw [e0]; rfl, ?_⟩
  · rcases an with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [a1]
        exact congrArg sbyte ev
      · rw [a2]
        exact congrArg (fun x : UInt8 => (x.toNat : Int)) ef
    · right
      rw [a1, a2]
      exact ⟨rfl, rfl⟩
  · intro _
    rw [hv2]
    exact hr1
  · rw [hv2, hf2]
    exact g2'
  · rw [hf2]
    omega
  · rcases hco.v with e | e
    · left
      rw [e]
      rfl
    · right
      rw [e]
      rfl
  · rw [hco.f]
    rfl
  · have e := hco.P
    rcases e with e | e | ⟨e, e2⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · refine Or.inr (Or.inr ⟨?_, e2⟩)
      have hm := hmove
      have e3 : sbyte (B.ram.get! (I sy.Player_X_Speed)) ≤ 0 := e2
      omega
  · show min (256 * sbyte v₁ + (f₁.toNat : Int)) 0 - amax sy m0 ≤ 256 * sbyte (B.ram.get! (I sy.Player_X_Speed)) + ((B.ram.get! (I sy.Player_X_MoveForce)).toNat : Int)
    rw [hv2, hf2]
    exact L1

end Smbrta.FrameModel

namespace Smbrta.RoomJoin

open Potential
open TopSpeed (top speedsB bytes)
open FastTakeoff (Room bonusRoom cornerP goalP roomCheck rightOk leftOk Takeoff AirIn GndIn JmpIn TFacts Pos Ent Cov Low go adv airI)
open AirCap (capped isAir CFacts capDist step_cap landing_bound landing_later)
open Jump (Arc VS vstep arcStart arcSucc arcCheck arc_spec arc_k arcStart_k groundY standY cornerY windowOk dropOk walkOk walkFrames
  forces falling arcFrames)

/-! ## The numbers -/

/-- the numbers of a room, in frames from first control -/
structure Nums where
  /-- the fall: this many air frames, the last one lands on the floor -/
  fall : Nat
  /-- the search of `FastTakeoff` covers takeoffs up to this many ground frames after the fall -/
  lastG : Nat
  /-- the frames after the takeoff frame with the feet low, in every jump from the floor -/
  rise : Nat
  /-- the frame at which he must be past the block's right end for an earlier entry -/
  goalF : Nat
  /-- before this frame he is not at the corner -/
  hitF : Nat
  /-- `RunningSpeed` is 0 up to this frame -/
  runF : Nat
  /-- what a frame that does not follow `hstep` leaves: the bound on `Φ`, and how far past the corner `P` can be -/
  stopPhi : Int
  stopSlack : Int
  /-- how far past the corner `P` can be while his feet are low -/
  lowSlack : Int
  /-- rows of the block above the floor -/
  h : Nat
  /-- the heights a jump can start from below the block's top: the floor, and the side of the block -/
  heights : List Nat
  /-- onto the block: (last low frame, frame on it), from the takeoff frame -/
  slow : List (Nat × Nat)
  fast : List (Nat × Nat)
  /-- off the block: frames to the floor after the last frame above it, slow and fast; air frames of a slow jump; stepping off -/
  aboveS : Nat
  aboveF : Nat
  airS : Nat
  walk : Nat
  /-- the longest jump from the floor, slow and fast; from any of those heights; from the block -/
  lenS : Nat
  lenF : Nat
  lenA : Nat
  lenB : Nat
  /-- a frame stopped at the left wall starts and ends at or left of `wallP`; the state after the first one is at or after frame `wallF` -/
  wallP : Int
  wallF : Nat
  /-- at the end of the fall, a state with `Φ ≤ safeP` does not reach the running threshold by frame `runF - 1` -/
  safeP : Int
  /-- frames counted back from the end of the fall, when he moves left fast then -/
  backK : Nat
  /-- with `RunningSpeed` not 0 at a stop by frame `runF`, the position is at most this -/
  backP : Int
  /-- after a wall hit, from the last frame stopped by the wall: from frame `wallD` on, the potential alone is enough. Before it, at the end of
  the fall: `Φ ≤ fastQ`, or he moves left and `wallK` air frames took him back -/
  wallD : Nat
  fastQ : Int
  wallK : Nat
  /-- the frames about standing are stated up to here -/
  standF : Nat
  /-- two stands in the fall are at least this many frames apart: before a stand he moves left at `standV` or more, and he is at or left of `standP` -/
  gapF : Nat
  standV : Int
  standP : Int
  /-- at first control: the height and the downward speed are at most these, and the force of the fall -/
  startY : Int
  startW : Int
  fallF : Nat
  /-- `(j, k)`: after a stand on frame `j` with no jump, he is not on the floor for `k` more frames -/
  gaps : List (Nat × Nat)
  /-- the vertical states at first control: `RoomPair.rowsCheck` proves that the rows of the change have no other (`InRoom.vstart`) -/
  vStart : List VS
  /-- the landing at the end of the first fall is checked for the horizontal coordinates below this (`InRoom.land`) -/
  landX : Nat := 0
  deriving Repr, Inhabited

/-- the room of `FastTakeoff`, with these numbers -/
def room (sy : Syms) (N : Nums) : Room := bonusRoom sy N.fall N.lastG N.rise (N.goalF - N.fall)

/-- the same with one low air frame less: a big player may pass the corner on the last low frame (`Approach.low`) -/
def roomB (sy : Syms) (N : Nums) : Room := bonusRoom sy N.fall N.lastG (N.rise - 1) (N.goalF - N.fall)

/-- the slow pairs with one more air frame from the frame before the last low frame and the landing one frame later: short of the goal. A big player's slow takeoff
after the first frame after the fall (`landed_short`) -/
def slowBigOk (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  N.slow.all fun q => decide (cornerP sy - 1 + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((q.2 + 1 - q.1 : Nat) : Int) +
    capDist sy m (N.goalF - (N.fall + 2 + q.2)) < goalP sy)

/-! ## The frames of a run -/

/-- position, horizontal state and input by frame: `inp (n + 1)` is the input of frame `n + 1`, and `hs (n + 1)`, `P (n + 1)` are
the state and the position at its end -/
structure Frames where
  hs : Nat → HS
  inp : Nat → HIn
  P : Nat → Int
  /-- the vertical state at the end of frame `n` -/
  vs : Nat → VS
  /-- `Player_XSpeedAbsolute` when frame `n + 1` comes to the player's routine: the stored speed, which a jump on that frame reads -/
  ab : Nat → Nat

/-- A on frame `n`: the vertical state at the end of the frame holds it (`Jump.vstep` sets `prevA` to the A it was given) -/
abbrev Frames.a (fr : Frames) (n : Nat) : Bool := (fr.vs n).prevA

/-- frame `n + 1` follows `hstep` in the open area -/
def Follow (sy : Syms) (m : Machine) (fr : Frames) (n : Nat) : Prop :=
  fr.inp (n + 1) ∈ inputs ∧ fr.hs (n + 1) = hstep sy m (fr.hs n) (fr.inp (n + 1)) ∧
    fr.P (n + 1) = fr.P n + 16 * sbyte (fr.hs (n + 1)).v

/-- at the end of frame `n` he is slow, and not far past the corner. This is what a hit leaves (the speed is 0), and also the
frames right after a hit that do not follow `hstep`: the stored speed is stale, or the side is masked -/
def Stop (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (n : Nat) : Prop :=
  inD sy (fr.hs n) = true ∧ phi sy m (fr.hs n) ≤ N.stopPhi ∧ fr.P n ≤ cornerP sy + N.stopSlack

/-- what the collision routine gives at a frame with the feet low: not far past the corner; and he is stopped, or left of the corner,
or moving left (then the routine does not stop him) -/
def LowAt (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (n : Nat) : Prop :=
  fr.P n ≤ cornerP sy + N.lowSlack ∧ (Stop sy m N fr n ∨ fr.P n < cornerP sy ∨ sbyte (fr.hs n).v < 0)

/-- `LowAt` with the slack `s` in place of `lowSlack` (round 28) -/
def LowS (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (s : Int) (n : Nat) : Prop :=
  fr.P n ≤ cornerP sy + s ∧ (Stop sy m N fr n ∨ fr.P n < cornerP sy ∨ sbyte (fr.hs n).v < 0)

theorem lowS_iff {sy : Syms} {m : Machine} {N : Nums} {fr : Frames} {n : Nat} : LowAt sy m N fr n ↔ LowS sy m N fr N.lowSlack n := Iff.rfl

/-- what the step at the block's left side needs of a slack (`RoomRun.low_step`): at least one pixel less one 256th, at least one frame at the top speed less a
pixel, and with one frame at the top speed below five pixels -/
def SlackOK (sy : Syms) (s : Int) : Prop := 255 ≤ s ∧ 16 * (top sy : Int) - 257 ≤ s ∧ s + 16 * (top sy : Int) < 1280

/-- the least slack of `SlackOK`: from left of the corner one frame at the top speed, pushed back one pixel. With no wall the frames that `low_floor` and `low_jump`
prove are this close to the corner, and one more pixel is one frame at the top speed less a 256th -/
def lowT (sy : Syms) : Int := 16 * (top sy : Int) - 257

/-- frame `i + 1` of a slow jump that does not follow `hstep`: he still moves at most the air speed. A hit from the block's right
side pushes him 1 px, only if he is moving left or stopped -/
def Moved (sy : Syms) (fr : Frames) (i : Nat) : Prop :=
  capped sy (fr.hs (i + 1)) = true ∧ inD sy (fr.hs (i + 1)) = true ∧
    fr.P (i + 1) ≤ fr.P i + 16 * ((sy.AirFastSpeed.toNat : Int) - 1)

/-- how he gets past the block's right end at frame `t0`, ending on the floor at frame `F` if nothing stops him. A stop or a landing
on the way only delays the floor, so `F` is at or before the entry frame `E` -/
inductive Off (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 E : Nat) : Type where
  /-- a jump from the block: frame `T1 + 1` is the takeoff frame, `n` frames later he reaches the floor. At `t0 - 1` he is above
  the block, or standing on it right before the jump -/
  | jump (T1 n F : Nat) (x u : Arc)
      (T1_ge : C ≤ T1)
      (x_mem : x ∈ arcStart sy m (standY sy N.h) N.h)
      (reach : Cert.Reach (arcSucc sy m N.h) x n u)
      (floor : falling u.s = true ∧ groundY sy ≤ u.s.y.toNat)
      (hF : F = T1 + 1 + n)
      (F_le : F ≤ E)
      (above : t0 + u.above ≤ F + 1)
      (slowJ : x.fast = false → F = E → capped sy (fr.hs T1) = true ∧
        ∀ i, T1 ≤ i → i < F → (Follow sy m fr i ∧ isAir (fr.inp (i + 1)) = true) ∨ Moved sy fr i) :
      Off sy m N fr C t0 E
  /-- stepping off: `t0` is the frame that walks past the end; then he falls with the fall force `f` and the carried fraction `d` -/
  | step (F : Nat) (f d : UInt8)
      (f_mem : f ∈ forces sy m)
      (hF : t0 + walkFrames sy m N.h f d ≤ F)
      (F_le : F ≤ E) :
      Off sy m N fr C t0 E

/-- he passes over the block in one jump, from the floor or from the side of the block: the jump still runs at frame `t0` -/
structure Over (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 : Nat) : Type where
  /-- the takeoff frame is `T1 + 1` -/
  T1 : Nat
  y0 : Nat
  x : Arc
  u : Arc
  T1_ge : C ≤ T1
  T1_lt : T1 < t0
  y0_mem : y0 ∈ N.heights
  x_mem : x ∈ arcStart sy m y0 N.h
  reach : Cert.Reach (arcSucc sy m N.h) x (t0 - (T1 + 1)) u
  /-- he stays in the air, except for stops -/
  air : ∀ n, T1 ≤ n → n < t0 → isAir (fr.inp (n + 1)) = true ∨ Stop sy m N fr (n + 1)
  /-- a slow jump reads a stored speed below the threshold, and the stored speed is at least `|v|` -/
  slowC : x.fast = false → capped sy (fr.hs T1) = true
  /-- at the takeoff he is not far past the corner -/
  start : fr.P T1 ≤ cornerP sy + N.stopSlack
  /-- at the threshold or more he took off from the floor: his feet stay low -/
  low : capped sy (fr.hs T1) = false → y0 = groundY sy ∧
    ∀ n, T1 + 1 ≤ n → n ≤ T1 + 1 + N.rise → n ≤ t0 → fr.P n ≤ cornerP sy + N.lowSlack

/-- he stands on the floor -/
def OnFloor (sy : Syms) (s : VS) : Prop := s.st = 0 ∧ s.y.toNat = groundY sy

/-- no frame before `hitF` is stopped -/
def NoWall (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C : Nat) : Prop :=
  ∀ n, C ≤ n → n + 1 < C + N.hitF → Follow sy m fr n

/-- frame `n + 1` is stopped at the left wall: he is near it before and after the frame, and `RunningSpeed` is 0 -/
structure WallAt (N : Nums) (fr : Frames) (n : Nat) : Prop where
  before : fr.P n ≤ N.wallP
  after : fr.P (n + 1) ≤ N.wallP
  run : (fr.hs (n + 1)).rs = 0

/-- the height with its fraction -/
def VY (s : VS) : Int := 256 * (s.y.toNat : Int) + (s.dummy.toNat : Int)
/-- the downward speed with its fraction -/
def VW (s : VS) : Int := 256 * (s.vy.toNat : Int) + (s.mf.toNat : Int)

/-- what a frame with no jump does to the height, from a state that is not in a jump: the speed is added to the height, the force to the
speed. A landing only lowers them -/
structure VDrop (s t : VS) : Prop where
  st : t.st ≠ 1
  y_le : VY t ≤ VY s + VW s
  w_le : VW t ≤ VW s + (s.vfd.toNat : Int)
  vfd : t.vfd = s.vfd

/-- what a frame that starts standing with no new press of A does to the vertical state (`RoomStand.stand_frame`): the height's fraction, the two forces and the jump's
origin stay; the height, the vertical speed and its fraction stay and the state is 0 or 2 (he stands, or falls off), or he lands: the state 0, the speed and its fraction 0,
the height with its low four bits 0 -/
def StandNext (s t : VS) : Prop :=
  t.dummy = s.dummy ∧ t.vf = s.vf ∧ t.vfd = s.vfd ∧ t.origin = s.origin ∧
    ((t.y = s.y ∧ t.vy = s.vy ∧ t.mf = s.mf ∧ (t.st = 0 ∨ t.st = 2)) ∨ (t.st = 0 ∧ t.vy = 0 ∧ t.mf = 0 ∧ t.y = s.y &&& 0xF0))

theorem hiF0_le : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0xF0).toNat ≤ (UInt8.ofNat n.val).toNat := by decide +kernel

/-- a frame that starts standing with no new press is `VDrop`: he does not go down, and the speed does not grow -/
theorem StandNext.vdrop {s t : VS} (h : StandNext s t) : VDrop s t := by
  obtain ⟨h1, _, h3, _, h5⟩ := h
  have hw : (0 : Int) ≤ VW s := by unfold VW; omega
  rcases h5 with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
  · refine ⟨by rcases e4 with e | e <;> rw [e] <;> decide, ?_, ?_, h3⟩
    · unfold VY; rw [e1, h1]; omega
    · unfold VW; rw [e2, e3]; omega
  · refine ⟨by rw [e1]; decide, ?_, ?_, h3⟩
    · have hy := hiF0_le ⟨s.y.toNat, s.y.toNat_lt⟩
      simp only [UInt8.ofNat_toNat] at hy
      unfold VY; rw [e4, h1]; omega
    · unfold VW; rw [e2, e3]; simp; omega

/-- what frame `n + 1` does to the height. Standing on the floor he stays or takes off; in the air, the frame is the vertical routine's,
unless he is falling (then it may land). The last case is standing anywhere else -/
inductive VFrame (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (n : Nat) : Prop where
  | stay (h1 : OnFloor sy (fr.vs n)) (h2 : OnFloor sy (fr.vs (n + 1))) (hi : GndIn (fr.inp (n + 1))) : VFrame sy m N fr n
  | takeoff (h1 : OnFloor sy (fr.vs n)) (x : Arc) (hx : x ∈ arcStart sy m (groundY sy) N.h) (h2 : fr.vs (n + 1) = x.s)
      (hi : JmpIn (fr.inp (n + 1))) : VFrame sy m N fr n
  | air (h1 : (fr.vs n).st ≠ 0) (h2 : fr.vs (n + 1) = vstep sy m (fr.vs n) (fr.a (n + 1)) 0) (hi : AirIn (fr.inp (n + 1))) :
      VFrame sy m N fr n
  | fall (h1 : (fr.vs n).st ≠ 0) (h2 : falling (vstep sy m (fr.vs n) (fr.a (n + 1)) 0) = true) : VFrame sy m N fr n
  | other (h1 : ¬OnFloor sy (fr.vs n)) (h2 : (fr.vs n).st = 0) : VFrame sy m N fr n

/-- a fast takeoff by the last frame searched, with no wall hit: the frames up to it are those of `FastTakeoff`. `early_of` proves it -/
structure Early (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C T1 : Nat) : Prop where
  /-- no frame before `hitF` is stopped -/
  follow : ∀ n, C ≤ n → n + 1 < C + N.hitF → Follow sy m fr n
  fall_in : ∀ n, C ≤ n → n < C + N.fall → AirIn (fr.inp (n + 1))
  gnd_in : ∀ n, C + N.fall ≤ n → n < T1 → GndIn (fr.inp (n + 1))
  jump_in : JmpIn (fr.inp (T1 + 1))
  air_in : ∀ n, T1 + 1 ≤ n → n < T1 + 1 + N.rise → AirIn (fr.inp (n + 1))

/-- with no wall hit, no stop from `hitF` on, and a landing on the block before `t0`: the last takeoff from the floor and its landing. `sz` is the player's size byte at
first control (0: big) -/
structure Approach (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 : Nat) (sz : UInt8) : Type where
  /-- the takeoff frame is `T1 + 1`. A takeoff needs the floor, so it comes after the fall -/
  T1 : Nat
  T1_ge : C + N.fall ≤ T1
  T1_lt : T1 < t0
  T1_floor : OnFloor sy (fr.vs T1)
  /-- its first frame in the vertical routine; `x.fast` says whether the stored speed is at the threshold -/
  x : Arc
  x_mem : x ∈ arcStart sy m (groundY sy) N.h
  x_vs : fr.vs (T1 + 1) = x.s
  /-- the jump reads the stored speed -/
  x_ab : x.fast = decide (sy.AirFastSpeed.toNat ≤ fr.ab T1)
  /-- he lands on the block on frame `L`, at the arc's state `u`. Frame `T1 + 1 + u.low` is the last low frame -/
  L : Nat
  u : Arc
  L_gt : T1 < L
  L_le : L ≤ t0
  reach : Cert.Reach (arcSucc sy m N.h) x (L - (T1 + 1)) u
  window : falling u.s = true ∧ standY sy N.h ≤ u.s.y.toNat ∧ u.s.y.toNat < standY sy N.h + sy.LandDepth.toNat
  air : ∀ n, T1 ≤ n → n < L → isAir (fr.inp (n + 1)) = true
  /-- the low frames are `LowAt`. For a big player (`sz = 0`) the last low frame may be only not far past the corner: there the upper point of his side check can be at a
  coin above the block's left column, the routine takes the coin and leaves the side check, and that frame does not push him back. Until round 25 `LowAt` was asked on
  every low frame, which is false on measured runs of a big player. Since round 27 (page `1-1/c-7-14-3-ApproachJump.md`) asked only on a frame at or past the corner
  (left of it the frame is `LowAt`), after a takeoff after `C + fall + lastG`, after `C + fall + 1 + rise`, or after a frame of the jump that ends above `cornerY + 16`:
  the other low frames end at `cornerY + 16` or below on the jump from the floor since the end of the fall, and `RoomCore.low_jump` makes them `LowAt` (`landed_short`) -/
  low : ∀ n, T1 + 1 ≤ n → n ≤ T1 + 1 + u.low → cornerP sy ≤ fr.P n →
    (C + N.fall + N.lastG < T1 ∨ C + N.fall + 1 + N.rise < n ∨ ∃ j, T1 < j ∧ j ≤ n ∧ (fr.vs j).y.toNat < cornerY sy N.h + 16) →
    LowAt sy m N fr n ∨ (sz = 0 ∧ n = T1 + 1 + u.low ∧ fr.P n ≤ cornerP sy + N.lowSlack)

/-- over the block in one jump, or onto it and off it. Only a run with no wall hit and no stop needs its takeoff from the floor. `sz` is the player's size byte at
first control (0: big), for `Approach` -/
inductive Way (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 E : Nat) (sz : UInt8) : Type where
  | over (o : Over sy m N fr C t0) : Way sy m N fr C t0 E sz
  | onto (a : NoWall sy m N fr C → (∀ n, C + N.hitF ≤ n → n ≤ t0 → ¬Stop sy m N fr n) → Approach sy m N fr C t0 sz)
      (off : Off sy m N fr C t0 E) : Way sy m N fr C t0 E sz

/-- frame `n` is in a jump from the floor with the takeoff frame `T + 1` -/
def OnArc (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (T n : Nat) : Prop :=
  T + 1 ≤ n ∧ ∃ x u, x ∈ arcStart sy m (groundY sy) N.h ∧ Cert.Reach (arcSucc sy m N.h) x (n - (T + 1)) u ∧ fr.vs n = u.s

/-- `vstep` on the machine of the player's routine in the room (`VertModel.vmach`: the jump's halt value 1), with the stored speed 0: what a frame in the air does to
the vertical bytes up to the landing (`InRoom.air`). On the jumps from the floor it is `vstep` on `m` (`VertAir.bridgeAll`) -/
abbrev vstepR (sy : Syms) (m : Machine) (s : VS) (a : Bool) : VS := VertModel.vstepV sy m (FrameModel.ctrlStack sy m) s a 0

/-- the machine of `vstepR` after the movement routine (`VertModel.vRun`): a frame in the air ends its move with its vertical page (`InRoom.high`) -/
abbrev vRunR (sy : Syms) (m : Machine) (s : VS) (a : Bool) : Machine := VertModel.vRun sy m (FrameModel.ctrlStack sy m) s a 0

/-- the height at the end of the move of the landing frame: the ground with one frame of the largest fall speed -/
def landY (sy : Syms) : UInt8 := (groundY sy + sy.MaxFallSpeed.toNat).toUInt8

/-- **What the landing asks at the end of its move, besides the vertical bytes and the bytes that the room's walk gives**: the vertical page 1, the page 0, the
horizontal coordinate below `N.landX`. The collision-disable flag is one of the walk's bytes (`RoomLand.controlKeys`). All three are proved on the first fall's landing
frame (`RoomRun.land_at_of`) -/
structure LandQ (sy : Syms) (N : Nums) (q : Machine) : Prop where
  high : q.ram.get! (FrameModel.I sy.Player_Y_HighPos) = 1
  page : q.ram.get! (FrameModel.I sy.Player_PageLoc) = 0
  x : (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat < N.landX

/-- **What a stand away from the floor asks at the end of its move** (`RoomWall.wall_frame`): the vertical page 1, the page 0, x below 16, the height from 32 to 206, the
state 0, 1 or 2, the vertical speed not negative, and the speed 0 or a byte from 129 on (negative, not −128). On the first stand of the fall they are proved
(`RoomRun.stand_first`) -/
structure WallQ (sy : Syms) (q : Machine) : Prop where
  high : q.ram.get! (FrameModel.I sy.Player_Y_HighPos) = 1
  page : q.ram.get! (FrameModel.I sy.Player_PageLoc) = 0
  x : (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat < 16
  y1 : 32 ≤ (q.ram.get! (FrameModel.I sy.Player_Y_Position)).toNat
  y2 : (q.ram.get! (FrameModel.I sy.Player_Y_Position)).toNat < 207
  st : (q.ram.get! (FrameModel.I sy.Player_State)).toNat ≤ 2
  vy : q.ram.get! (FrameModel.I sy.Player_Y_Speed) &&& 0x80 = 0
  v : q.ram.get! (FrameModel.I sy.Player_X_Speed) = 0 ∨ 129 ≤ (q.ram.get! (FrameModel.I sy.Player_X_Speed)).toNat

/-- **What a frame in the air asks at the end of its move for no stand** (round 30, `RoomWall.wall_frameX`): the vertical page 1, the page 0, x from 13 to 16, the height
from 32 to one above the floor's, the state 1 or 2, the vertical speed not negative. Then no foot is in a solid cell, and the frame ends with the state not 0 -/
structure WallX (sy : Syms) (q : Machine) : Prop where
  high : q.ram.get! (FrameModel.I sy.Player_Y_HighPos) = 1
  page : q.ram.get! (FrameModel.I sy.Player_PageLoc) = 0
  x1 : 13 ≤ (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat
  x2 : (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat < 17
  y1 : 32 ≤ (q.ram.get! (FrameModel.I sy.Player_Y_Position)).toNat
  y2 : (q.ram.get! (FrameModel.I sy.Player_Y_Position)).toNat < groundY sy
  st : q.ram.get! (FrameModel.I sy.Player_State) = 1 ∨ q.ram.get! (FrameModel.I sy.Player_State) = 2
  vy : q.ram.get! (FrameModel.I sy.Player_Y_Speed) &&& 0x80 = 0

/-- the horizontal coordinate from which his right side check is in the block's left column -/
def cornerX (sy : Syms) : Nat := 16 * (sy.RoomBlockLeftByte.toNat / 16 + 1) - sy.SideAdderX.toNat

/-- **What a frame of the first fall asks at the end of its move for no stand** (round 30, `RoomWall.wall_frameF`): the vertical page 1, the page 0, x from 13 to the
one before `cornerX` (his right side check left of the block's left column), a height of `ys` (the route takes `ysFall`), the state 2, the vertical speed not negative.
Then no foot is in a solid cell, and the frame ends with the state not 0 -/
structure WallF (sy : Syms) (ys : List UInt8) (q : Machine) : Prop where
  high : q.ram.get! (FrameModel.I sy.Player_Y_HighPos) = 1
  page : q.ram.get! (FrameModel.I sy.Player_PageLoc) = 0
  x1 : 13 ≤ (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat
  x2 : (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat < cornerX sy
  y : q.ram.get! (FrameModel.I sy.Player_Y_Position) ∈ ys
  st : q.ram.get! (FrameModel.I sy.Player_State) = 2
  vy : q.ram.get! (FrameModel.I sy.Player_Y_Speed) &&& 0x80 = 0

/-- the coordinates of the checks: from `cornerX` on, five pixels -/
def xsC (sy : Syms) : List UInt8 := (List.range 5).map fun k => (cornerX sy + k).toUInt8


/-- **What a frame's end at the block's left side is**, from the coordinate `x` and the speed `v` at its end of the move: the height above the corner's `cy`, or the page
0 and, with `v` from 0 to 127, the speed 0 and the coordinate `x − 1` (pushed back one pixel), with a negative `v` the speed `v` and the coordinate `x` -/
def CornerEnd (sy : Syms) (cy : Nat) (x v : UInt8) (G : Machine) : Prop :=
  (G.ram.get! (FrameModel.I sy.Player_Y_Position)).toNat < cy ∨
    (G.ram.get! (FrameModel.I sy.Player_PageLoc) = 0 ∧
      (if v < 0x80 then G.ram.get! (FrameModel.I sy.Player_X_Speed) = 0 ∧ G.ram.get! (FrameModel.I sy.Player_X_Position) = x - 1
       else G.ram.get! (FrameModel.I sy.Player_X_Speed) = v ∧ G.ram.get! (FrameModel.I sy.Player_X_Position) = x))

/-- **On a jump's first frames from the floor the height does not grow**: on each state of `VertAir.arcSet` before its last frame, `vstep` with A or not leaves the
height's byte at most what it was -/
def arcDown (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  (VertAir.arcSet sy m N.h N.rise).all fun u => decide (N.rise ≤ u.k) || [true, false].all fun a => decide ((vstep sy m u.s a 0).y.toNat ≤ u.s.y.toNat)

/-- what a real run in the room gives, apart from the frames' link to `hstep`. `sz` is the player's size byte at first control (`RoomRun` sets it from the machine) -/
structure RoomFields (sy : Syms) (m : Machine) (N : Nums) (sz : UInt8) where
  fr : Frames
  /-- first control -/
  C : Nat
  /-- the entry frame: `RoomRun.enters` defines it on the real machines -/
  E : Nat
  /-- the first frame past the block's right end -/
  t0 : Nat
  t0_ge : C ≤ t0
  past : goalP sy ≤ fr.P t0
  first : ∀ n, C ≤ n → n < t0 → fr.P n < goalP sy
  /-- a frame before `hitF` that does not follow `hstep` is stopped by the left wall -/
  wall : ∀ n, C ≤ n → n + 1 < C + N.hitF → ¬Follow sy m fr n → WallAt N fr n
  /-- from `hitF` to `runF + 1`, by the left wall, or he is at the corner. Since round 30 (page `1-1/c-7-4-1-StopRun.md`) asked only after an earlier frame that does
  not follow `hstep` before `hitF`: `anchor_at`, the only user, has one (the first hit) -/
  late : ∀ n, C + N.hitF ≤ n + 1 → n ≤ C + N.runF → (∃ h, C ≤ h ∧ h < n ∧ h + 1 < C + N.hitF ∧ ¬Follow sy m fr h) → ¬Follow sy m fr n →
    WallAt N fr n ∨ cornerP sy ≤ fr.P n + 16 * (top sy : Int)
  /-- from `hitF` to `runF`, a frame on the ground with no jump that does not follow `hstep`, with `RunningSpeed` 0 at its start, and whose stored speed is not the size
  of its speed at the start (it was stored before a stop), reads a stored speed below the running threshold. Since round 31 (page `1-1/c-7-4-2-RunWalk.md`) in place of
  the field `stop_run`, which `RoomRun.stop_run_of` now proves from it, from `ab_early` before `hitF`, and from the walk of `InRoom.run`. On such a frame
  `GetPlayerAnimSpeed` stores a stored speed from the threshold on into `RunningSpeed`, so by this reading of the code (not proved) the old `stop_run` gave this too -/
  ab_run : ∀ n, C + N.hitF ≤ n + 1 → n < C + N.runF → (fr.hs n).rs = 0 → ¬Follow sy m fr n → (fr.vs n).st = 0 → (fr.inp (n + 1)).jump = false →
    fr.ab n ≠ (sbyte (fr.hs n).v).natAbs → fr.ab n < sy.RunSpeedMin.toNat
  /-- he stands away from the floor only at the end of a frame that does not follow `hstep`: a side stops him on that frame. Asked only after an earlier frame that ends
  in the state 0: the first stand of the fall is proved (`RoomRun.stand_first`), and the theorems use no other frame (`RoomRun.stand_off_of`, `RoomCore.stand_off`). Since
  round 29 asked from the end of the fall on only with no jump since such a frame (page `1-1/c-7-5-22-StandNoJump.md`): `wall_turn`, the only user there, has none, and a
  landing on the block needs a jump -/
  stand_wall : ∀ n, C ≤ n → n + 1 < C + N.standF → (∃ j, C < j ∧ j ≤ n ∧ (fr.vs j).st = 0) →
    (n + 1 < C + N.fall ∨ ∃ j, C < j ∧ j ≤ n ∧ (fr.vs j).st = 0 ∧ ∀ l, j ≤ l → l ≤ n → (fr.inp (l + 1)).jump = false) →
    (fr.vs (n + 1)).st = 0 → ¬OnFloor sy (fr.vs (n + 1)) → ¬Follow sy m fr n
  /-- before a stand in the fall he moves left fast. Since round 30 (page `1-1/c-7-13-4-StandHit.md`) asked only on a stand whose frame follows `hstep`
  (`stand_first`, `RoomWall.not_follow_of`) or after an earlier stand (`stand_gap`). The field `stand_P` (near the wall on the frame before) is gone since round 30:
  `stand_first` takes the position from `fall_left` and the walks of `InRoom.wall` (`WallX`, `WallF`), `wall_turn` from `RoomCore.stand_hit` -/
  stand_fast : ∀ n, C ≤ n → n + 1 < C + N.fall → (Follow sy m fr n ∨ ∃ j, C < j ∧ j ≤ n ∧ (fr.vs j).st = 0) → (fr.vs (n + 1)).st = 0 → N.standV ≤ -V (fr.hs n)
  way : Way sy m N fr C t0 E sz

/-- the frames as numbers: what the theorems below use. `RoomRun.toCore` makes them from real machines -/
structure RoomCore (sy : Syms) (m : Machine) (N : Nums) (sz : UInt8) extends RoomFields sy m N sz where
  /-- from the end of the fall to `runF`, a frame that does not follow `hstep`, with `RunningSpeed` 0 and the speed below the running threshold at its start, leaves
  `RunningSpeed` 0. Once a field of `RoomFields` (since round 30 from the end of the fall on, with `RunningSpeed` 0 at the start); since round 31 (page
  `1-1/c-7-4-2-RunWalk.md`) `RoomRun.stop_run_of` proves it: the stored speed it reads is the size of the speed at its start, or below the air threshold (`ab_early`),
  or the field `ab_run`; then the walk of `InRoom.run` says that the frame leaves `RunningSpeed` 0. `rs_of_safe` and `no_wall_back`, the only users, know the speed
  below the threshold (`safeFrom`) -/
  stop_run : ∀ n, C + N.fall ≤ n → n < C + N.runF → (fr.hs n).rs = 0 → (sbyte (fr.hs n).v).natAbs < sy.RunSpeedMin.toNat → ¬Follow sy m fr n →
    (fr.hs (n + 1)).rs = 0
  /-- he stands away from the floor before `standF`, before the end of the fall or after an earlier frame that ends in the state 0, only at the end of a frame that does
  not follow `hstep`. `RoomRun.stand_off_of` proves it from the field `stand_wall` and the first stand of the fall (`RoomRun.stand_first`) -/
  stand_off : ∀ n, C ≤ n → n + 1 < C + N.standF →
    (n + 1 < C + N.fall ∨ ∃ j, C < j ∧ j ≤ n ∧ (fr.vs j).st = 0 ∧ ∀ l, j ≤ l → l ≤ n → (fr.inp (l + 1)).jump = false) → (fr.vs (n + 1)).st = 0 →
    ¬OnFloor sy (fr.vs (n + 1)) → ¬Follow sy m fr n
  /-- the first stand of the fall before `C + wallF + 1`, when it is the first frame that does not follow `hstep`: the frame before is at or left of `standP` (round 30).
  `RoomRun.stand_hit_of` proves it: at the end of the move x is at most 12 (`InRoom.wall` with `WallX`), and the frame moves him left by at most the speed of the start's
  potential and one adder (`FrameModel.frame_readQL`). Before round 30 the field `stand_P` gave it; `wall_turn` uses it -/
  stand_hit : ∀ n, C ≤ n → n + 1 < C + N.fall → n < C + N.wallF → (∀ j, C ≤ j → j < n → Follow sy m fr j) → ¬Follow sy m fr n →
    (∀ j, C < j → j ≤ n → (fr.vs j).st ≠ 0) → (fr.vs (n + 1)).st = 0 → fr.P n ≤ N.standP
  /-- a frame in the air and a jump frame keep the facing direction. Once a field of `RoomFields` (since round 28 only on the frames that do not follow `hstep`); since
  round 29 (page `1-1/c-7-13-2-FaceWalk.md`) `RoomRun.facing_of` proves it on every such frame: at the player's routine the frame is in the air or starts a jump, and the walk
  of the room's whole frame that follows the facing from there (`InRoom.face`) keeps it to the frame's end. `wall_turn` uses it on every frame of its chain -/
  facing : ∀ n, C ≤ n → n < C + N.fall → (fr.inp (n + 1)).st ≠ 0 ∨ (fr.inp (n + 1)).jump = true → (fr.hs (n + 1)).fd = (fr.hs n).fd
  /-- with no wall, a frame from `hitF` to the end of the low frames that ends on the floor, on the floor since the end of the fall, after a frame that is `LowAt`, is
  `LowAt`. `RoomRun.low_floor_of` proves it: at its end of the move he is at or past the corner only at the block's left side, where the collision routine pushes him back
  one pixel with the speed 0 or he moves left (`InRoom.corner`). Since round 28 for `LowS` with any slack of `SlackOK` (`LowAt` is `LowS` with `lowSlack`; `low_by` uses
  also the least slack `lowT`) -/
  low_floor : NoWall sy m N fr C → ∀ n, C + N.hitF ≤ n + 1 → n + 1 ≤ C + N.fall + 1 + N.rise → n < t0 →
    (∀ j, C + N.fall ≤ j → j ≤ n + 1 → OnFloor sy (fr.vs j)) → ∀ s, SlackOK sy s → LowS sy m N fr s n → LowS sy m N fr s (n + 1)
  /-- with no wall, the frames of a jump from the floor after the fall up to the end of the low frames, after a takeoff frame `T + 1` that is `LowAt`'s successor, are
  `LowAt` while every frame of the jump ends at `cornerY + 16` or below. `RoomRun.low_jump_of` proves it: the takeoff and the frames in the air keep the vertical page 1
  (`InRoom.highJ`, `InRoom.highA`), and at the block's left side they end `CornerEnd`. Since round 28 for `LowS` with any slack of `SlackOK` -/
  low_jump : NoWall sy m N fr C → ∀ T n, C + N.fall ≤ T → T < n → n ≤ C + N.fall + 1 + N.rise → n ≤ t0 →
    (∀ j, C + N.fall ≤ j → j ≤ T → OnFloor sy (fr.vs j)) → (∀ j, T < j → j ≤ n → OnArc sy m N fr T j) →
    (∀ j, T < j → j ≤ n → cornerY sy N.h + 16 ≤ (fr.vs j).y.toNat) → ∀ s, SlackOK sy s → LowS sy m N fr s T → LowS sy m N fr s n
  /-- after a frame that is stopped or moves left, a frame that starts in the air moves him at most one pixel right (round 28). `RoomRun.push_one_of` proves it: a frame
  that follows `hstep` gains at most `gFast` of potential (`Potential.stepOk`), or from moving left at most `gFast` of speed (`gainCheck`); a frame that does not is a
  `TopSpeed.Frame`, whose speed after the move is at most 16 and whose collision moves him at most one pixel right of the frame's start -/
  push_one : ∀ n, C ≤ n → n < t0 → n < C + N.standF → (fr.vs n).st ≠ 0 → (Stop sy m N fr n ∨ sbyte (fr.hs n).v < 0) → fr.P (n + 1) ≤ fr.P n + 256
  /-- a frame with a jump in its input ends on the takeoff of its height for the stored speed it reads (round 28). `RoomRun.off_ab_of` proves it: `InRoom.jump`
  (`vjump_of`) with the stored speed read at the player's routine (`read_ab`) -/
  off_ab : ∀ n, C ≤ n → n < t0 → n + 1 < E → (fr.inp (n + 1)).jump = true →
    fr.vs (n + 1) = VertJump.jumpOff sy m (FrameModel.ctrlStack sy m) (fr.vs n).y (fr.ab n).toUInt8 ∧ fr.ab n < 256
  /-- a frame that starts in the air has an air input. Once a field of `RoomRun`; now `RoomRun.air_in_of` proves it: the input is read from the machine (`read_in`,
  `read_stop`), and at the player's routine the player's state is that of the frame's start (`InRoom.stR`) -/
  air_in : ∀ n, C ≤ n → n < C + N.standF → (fr.vs n).st ≠ 0 → AirIn (fr.inp (n + 1))
  /-- with no wall, the heights of the frames after the fall that start on the floor before the entry, when he has stood on the floor since the end of the fall -/
  vfloor : NoWall sy m N fr C → ∀ n, C + N.fall ≤ n → n < C + N.fall + N.lastG + 1 + N.rise → n < E → (∀ j, C + N.fall ≤ j → j ≤ n → OnFloor sy (fr.vs j)) →
    VFrame sy m N fr n
  /-- a frame on the first frames of a jump from the floor follows `vstep` -/
  varc : ∀ T n, C ≤ n → n < t0 → n + 1 < E → OnArc sy m N fr T n → n + 1 - (T + 1) ≤ N.rise → fr.vs (n + 1) = vstep sy m (fr.vs n) (fr.a (n + 1)) 0
  /-- landing: on a whole row, with no speed. Once a field of `RoomRun` (before `standF`); now `RoomRun.stand_row_of` proves it before `t0` from the room's walks -/
  stand_row : ∀ n, C ≤ n → n + 1 < t0 → (fr.vs n).st ≠ 0 → (fr.vs (n + 1)).st = 0 →
    (fr.vs (n + 1)).y.toNat % 16 = 0 ∧ VW (fr.vs (n + 1)) = 0
  /-- he is not on the floor during the fall. Once a field of `RoomRun`; now `RoomRun.fall_long_of` proves it: with no jump from the finite set of the states with no
  jump (`noJumpCheck`), after a jump from the set of the states with any input from the first stand on (`anyCheck`, `RoomRun.fall_any`: with `stand_wall` and `wall`) -/
  fall_long : ∀ n, C ≤ n → n < C + N.fall → ¬OnFloor sy (fr.vs n)
  /-- a frame with no jump, from a state that is not in a jump, with no jump since first control. Once a field of `RoomRun` (without the frames before); now
  `RoomRun.vfall_of` proves it: with no jump since first control the states are those of a finite set (`noJumpCheck`) -/
  vfall : ∀ n, C ≤ n → n + 1 < C + N.standF → (fr.vs n).st ≠ 1 → (∀ j, C ≤ j → j ≤ n → (fr.inp (j + 1)).jump = false) → VDrop (fr.vs n) (fr.vs (n + 1))
  /-- with no wall, the fall ends on the floor. Once a field of `RoomRun`; now `RoomRun.floor_at_of` proves it: with no wall there is no stand before the end of the
  fall, so the first fall gives the floor's height there, and the field `land_at` says that he stands -/
  floor_at : NoWall sy m N fr C → OnFloor sy (fr.vs (C + N.fall))
  /-- the state at first control -/
  start : fr.hs C = (room sy N).s0
  startP0 : (room sy N).P0 ≤ fr.P C
  startP1 : fr.P C ≤ (room sy N).P1
  /-- he starts in the air -/
  v_start : (fr.vs C).st = 2 ∧ VY (fr.vs C) ≤ N.startY ∧ VW (fr.vs C) ≤ N.startW ∧ (fr.vs C).vfd.toNat = N.fallF
  /-- every frame up to `t0` follows `hstep` or leaves him stopped -/
  frames : ∀ n, C ≤ n → n < t0 → Follow sy m fr n ∨ Stop sy m N fr (n + 1)
  /-- every frame moves him at most the top speed -/
  move_top : ∀ n, C ≤ n → n < t0 → fr.P (n + 1) ≤ fr.P n + 16 * (top sy : Int)
  /-- on the entry frame he is at the mouth, or past its left end -/
  mouth : SidePipe.mouthP sy 0 ≤ fr.P E
  /-- the stored speed that frame `n + 1` reads is `|v|`; or that frame leaves him stopped, and before `hitF` the stored speed is below the threshold -/
  ab_of : ∀ n, C ≤ n → n < t0 → fr.ab n = (sbyte (fr.hs n).v).natAbs ∨
    (Stop sy m N fr (n + 1) ∧ (n + 1 < C + N.hitF → fr.ab n < sy.AirFastSpeed.toNat))

/-- **The state at first control**, on the machine: the horizontal state of the room's start, the position of its pixel, in the air with the start's height and fall, and the stored speed 0.
`RoomStart.PipeRun.start` proves it from the change into the room. -/
structure StartAt (sy : Syms) (N : Nums) (m : Machine) : Prop where
  hs : FrameModel.readHS sy m = (room sy N).s0
  P0 : (room sy N).P0 ≤ posP sy m
  P1 : posP sy m ≤ (room sy N).P1
  v : (SurfaceFrames.vsOf sy m).st = 2 ∧ VY (SurfaceFrames.vsOf sy m) ≤ N.startY ∧ VW (SurfaceFrames.vsOf sy m) ≤ N.startW ∧ (SurfaceFrames.vsOf sy m).vfd.toNat = N.fallF
  ab : peek m sy.Player_XSpeedAbsolute = 0
  /-- the vertical page 1 -/
  high : peek m sy.Player_Y_HighPos = 1

/-- **What a frame that follows the model still asks**, at the player's routine (instruction `n₀`): the stored speed is `|v|`, and the side he presses is not masked;
and from the scroll handler on nothing writes the horizontal bytes. `FrameModel.CleanR` without what the room's walks give at the player's routine (`VertAir.AtV`:
`RoomVert.cut_R`, `RoomPair.quad_run`) -/
structure CleanW (sy : Syms) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  abs : peek (PipeEntryRule.trace M i n₀) sy.Player_XSpeedAbsolute = TopSpeed.absB (peek (PipeEntryRule.trace M i n₀) sy.Player_X_Speed)
  coll : peek (PipeEntryRule.trace M i n₀) sy.Player_CollisionBits &&& FrameModel.lrOf (Potential.norm (FrameModel.readIn sy (PipeEntryRule.trace M i n₀))) =
    FrameModel.lrOf (Potential.norm (FrameModel.readIn sy (PipeEntryRule.trace M i n₀)))
  after : ∀ j, n₀ ≤ j → (PipeEntryRule.trace M i j).pc = sy.PlayerSubs → ∀ a ∈ FrameModel.hBytes sy,
    peek (PipeTransition.frame M i) a = peek (PipeEntryRule.trace M i j) a

/-- **What a frame that stops him still asks**: at the player's routine the collision bits are a value of `TopSpeed.collBits`, and what the collision routine and the rest
of the frame do (`FrameModel.Collide`). `FrameModel.ReadR` without `AtV` and without the speed's range, which the frames before give (`RoomRun.far_inD`) -/
structure ReadW (sy : Syms) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  coll : peek (PipeEntryRule.trace M i n₀) sy.Player_CollisionBits ∈ TopSpeed.collBits sy
  collide : ∀ j, n₀ ≤ j → (PipeEntryRule.trace M i j).pc = sy.PlayerSubs → FrameModel.Collide sy (PipeEntryRule.trace M i j) (PipeTransition.frame M i)

theorem CleanW.toR {E : FrameModel.Rom} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} (h : CleanW sy M i n₀)
    (hv : VertAir.AtV sy E S (PipeEntryRule.trace M i n₀)) : FrameModel.CleanR sy E S M i n₀ :=
  ⟨⟨hv.good, hv.pc, hv.s, hv.eng, hv.area, hv.st, hv.spring, hv.swim, hv.size, h.abs, h.coll⟩, h.after⟩

theorem ReadW.toR {E : FrameModel.Rom} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} (h : ReadW sy M i n₀)
    (hv : VertAir.AtV sy E S (PipeEntryRule.trace M i n₀)) (hs : TopSpeed.inSpeed sy (peek (PipeEntryRule.trace M i n₀) sy.Player_X_Speed) = true) :
    FrameModel.ReadR sy E S M i n₀ :=
  ⟨⟨hv.good, hv.pc, hv.s, hv.eng, hv.area, hv.st, hv.spring, hv.swim, hv.size, h.coll, hs⟩, h.collide⟩

/-! ## The room's frames on the real run

The room's frame `n` (from first control `C` on) is a counted frame of the real run `S` from frame `b` on: the `(n − C)`-th frame that ends with the game not paused
(`FrameKeep.ixOf`, the search looking up to frame `b + lim`). So the room's frame `n` ends at `S.seq (b + ixR (n − C))` (`endAt`), and the real frame that is the room's
frame `n + 1` begins one frame before the end of the room's frame `n + 1` (`startAt`). The frames between them end paused: they do not call the mode's routine, and keep what
the model reads (`InRoom.keep`). These are definitions; a run that pauses in the room is a run of this kind. -/

/-- the counted frame `k` of the room: the `k`-th frame of `S` from frame `b` on that ends not paused, among the frames up to `b + lim`. The counted frame 0 is frame `b` -/
abbrev ixR (sy : Syms) (m : Machine) (S : FrameKeep.RealRun) (b lim k : Nat) : Nat := FrameKeep.ixOf sy m S b lim k

/-- the machine at the end of the room's frame `n` (for `C ≤ n`): frame `b + ixR (n − C)` of the run -/
abbrev endAt (sy : Syms) (m : Machine) (S : FrameKeep.RealRun) (b lim C n : Nat) : Machine := S.seq (b + ixR sy m S b lim (n - C))

/-- the machine when the room's frame `n + 1` begins (for `C ≤ n`): the frame of the run just before the end of the room's frame `n + 1` -/
abbrev startAt (sy : Syms) (m : Machine) (S : FrameKeep.RealRun) (b lim C n : Nat) : Machine := S.seq (b + (ixR sy m S b lim (n + 1 - C) - 1))

/-- the input of the room's frame `n + 1` -/
abbrev inpAt (sy : Syms) (m : Machine) (S : FrameKeep.RealRun) (b lim C n : Nat) : UInt8 := S.inp (b + (ixR sy m S b lim (n + 1 - C) - 1))

/-- what a real run in the room gives, on real machines. The machines are those of the real run `S`: the room's frame `n` ends at `endAt … n` (`RoomRun.fe`), the end of
the `(n − C)`-th frame from frame `b` on that ends not paused, and the room's frame `n + 1` is the real frame from `startAt … n` (`RoomRun.fm`) with its input (`RoomRun.inAt`,
`RoomRun.pad`). So the machine at first control is `S.seq b` (`RoomRun.fe_C`). These are definitions; that the room's frame `n + 1` is the real frame of the machine where
it begins is `RoomRun.next`, that it ends not paused is `RoomRun.up`. The frames that end paused in between are not frames of the room. The size byte of `RoomFields` is
that of `S.seq b`, the machine at first control -/
structure RoomRun (sy : Syms) (m : Machine) (N : Nums) (S : FrameKeep.RealRun) (b lim : Nat) extends
    RoomFields sy m N ((S.seq b).ram.get! (FrameModel.I sy.PlayerSize)) where
  /-- the state and the position at the end of each frame up to `t0` are those of the machine -/
  read_hs : ∀ n, C ≤ n → n ≤ t0 → fr.hs n = FrameModel.readHS sy (endAt sy m S b lim C n)
  read_P : ∀ n, C ≤ n → n ≤ t0 → fr.P n = posP sy (endAt sy m S b lim C n)
  /-- the vertical state is that of the machine -/
  read_vs : ∀ n, C ≤ n → n ≤ t0 → fr.vs n = SurfaceFrames.vsOf sy (endAt sy m S b lim C n)
  /-- the stored speed of frame `n` is what frame `n + 1` reads when it comes to the player's routine -/
  read_ab : ∀ n, C ≤ n → n < t0 → fr.ab n = (peek (PipeEntryRule.trace (startAt sy m S b lim C n) (inpAt sy m S b lim C n)
    (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n))) sy.Player_XSpeedAbsolute).toNat
  /-- a frame that follows the model has the input read from the machine -/
  read_in : ∀ n, C ≤ n → n < t0 → FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (startAt sy m S b lim C n) (inpAt sy m S b lim C n)
      (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n)) →
    fr.inp (n + 1) = FrameModel.readIn sy (PipeEntryRule.trace (startAt sy m S b lim C n) (inpAt sy m S b lim C n) (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n)))
  /-- each frame up to `t0` is one that follows the model; or it leaves him stopped, and it is a `TopSpeed.Frame`. What they ask at the player's routine but the values
  that decide which (the stored speed, the mask, the collision bits) comes from the room's walks (`InRoom.cut`); that the frame does not end during the movement (the old
  part `longer`) from the frame's time (`InRoom.time`, `InRoom.arrive`) -/
  clean : ∀ n, C ≤ n → n < t0 → CleanW sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n) (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n)) ∨
    (Stop sy m N fr (n + 1) ∧ ReadW sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n) (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n)))
  /-- a frame up to `t0` that starts at most `16·top + 256` right of 8 px (and at 8 px or more) ends at 8 px or more: the left wall keeps him there. The frames that start
  further right end there by the bound on one frame's move (`RoomRun.far_inD`). The old field `far` (every frame starts at 8 px or more) -/
  farNear : ∀ n, C ≤ n → n + 1 < t0 → 2048 ≤ posP sy (startAt sy m S b lim C n) → posP sy (startAt sy m S b lim C n) < 2048 + 16 * (top sy : Int) + 256 →
    2048 ≤ posP sy (PipeTransition.frame (startAt sy m S b lim C n) (inpAt sy m S b lim C n))
  /-- a frame before `hitF` that does not follow the model reads a stored speed below the air threshold -/
  ab_early : ∀ n, C ≤ n → n + 1 < C + N.hitF → n < t0 →
    ¬FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (startAt sy m S b lim C n) (inpAt sy m S b lim C n)
      (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n)) → fr.ab n < sy.AirFastSpeed.toNat
  /-- frame `E` enters the side pipe: an instruction of it, from the machine where it begins with its input, writes the side pipe's routine -/
  enters : SideEntryRule.Enters sy (startAt sy m S b lim C (E - 1)) (inpAt sy m S b lim C (E - 1))
  /-- `P(E)` is read at the end of frame `E`, as the other frames are read (`read_P`): the position of the machine when the frame that enters ends -/
  read_PE : fr.P E = posP sy (PipeTransition.frame (startAt sy m S b lim C (E - 1)) (inpAt sy m S b lim C (E - 1)))
  /-- a frame up to `t0` that does not follow the model (a side stops him) has the input read from the machine at the player's routine, as `read_in` reads the input of a
  frame that follows the model -/
  read_stop : ∀ n, C ≤ n → n < t0 → ¬FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (startAt sy m S b lim C n) (inpAt sy m S b lim C n)
      (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n)) →
    fr.inp (n + 1) = FrameModel.readIn sy (PipeEntryRule.trace (startAt sy m S b lim C n) (inpAt sy m S b lim C n) (CtrlKeep.arrAt sy (startAt sy m S b lim C n) (inpAt sy m S b lim C n)))

section
variable {sy : Syms} {m : Machine} {N : Nums} {S : FrameKeep.RealRun} {b lim : Nat}

/-- the counted frame `k` of the room -/
abbrev RoomRun.ix (_r : RoomRun sy m N S b lim) (k : Nat) : Nat := ixR sy m S b lim k

/-- the machine at the end of the room's frame `n`: frame `b + ix (n − C)` of the run -/
abbrev RoomRun.fe (r : RoomRun sy m N S b lim) (n : Nat) : Machine := endAt sy m S b lim r.C n

/-- the machine when the room's frame `n + 1` begins: frame `b + ix (n + 1 − C) − 1` of the run. When frame `n` ends not paused (no pause between), it is `fe n` -/
abbrev RoomRun.fm (r : RoomRun sy m N S b lim) (n : Nat) : Machine := startAt sy m S b lim r.C n

/-- the input of the frame that begins with `fm n`: the input of the room's frame `n + 1` -/
abbrev RoomRun.inAt (r : RoomRun sy m N S b lim) (n : Nat) : UInt8 := inpAt sy m S b lim r.C n

/-- the input of the room's frame `n` -/
abbrev RoomRun.pad (r : RoomRun sy m N S b lim) (n : Nat) : UInt8 := r.inAt (n - 1)

/-- the instruction at which the frame that begins with `fm n` first comes to the player's routine (`CtrlKeep.arrAt`). The old field `arr` -/
abbrev RoomRun.arr (r : RoomRun sy m N S b lim) (n : Nat) : Nat := CtrlKeep.arrAt sy (r.fm n) (r.inAt n)

/-- the frames from frame `b` on that end not paused, up to frame `b + lim` -/
abbrev RoomRun.ups (_r : RoomRun sy m N S b lim) : Nat := FrameKeep.upTo (FrameKeep.upAt sy m S b) lim

/-- the counted frame `k` of the room, for `1 ≤ k` up to `ups`, is a frame after `b`, it ends not paused, and it is within `b + lim` -/
theorem RoomRun.ix_at (r : RoomRun sy m N S b lim) {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ r.ups) :
    1 ≤ r.ix k ∧ r.ix k ≤ lim ∧ FrameKeep.Unpaused sy m (S.seq (b + r.ix k)) := by
  obtain ⟨a1, a2, _⟩ := FrameKeep.nthUp_at (f := FrameKeep.upAt sy m S b) h1 h2
  refine ⟨a1, (FrameKeep.nthUp_spec h2).1, ?_⟩
  simpa [FrameKeep.upAt] using a2

/-- **The room's frame `n + 1` is the real frame from `fm n`**: it ends at `fe (n + 1)`, when `n + 1 − C` frames from `b` on end not paused by `b + lim` -/
theorem RoomRun.next (r : RoomRun sy m N S b lim) {n : Nat} (hC : r.C ≤ n) (h : n + 1 - r.C ≤ r.ups) :
    r.fe (n + 1) = PipeTransition.frame (r.fm n) (r.inAt n) := by
  have h1 := (r.ix_at (k := n + 1 - r.C) (by omega) h).1
  show S.seq (b + r.ix (n + 1 - r.C)) = PipeTransition.frame (S.seq (b + (r.ix (n + 1 - r.C) - 1))) (S.inp (b + (r.ix (n + 1 - r.C) - 1)))
  rw [← S.next]
  congr 1
  omega

/-- **The room's frame `n + 1` ends with the game not paused**: by the definition of the counted frames -/
theorem RoomRun.up (r : RoomRun sy m N S b lim) {n : Nat} (hC : r.C ≤ n) (h : n + 1 - r.C ≤ r.ups) : CtrlKeep.Unpaused sy m (PipeTransition.frame (r.fm n) (r.inAt n)) := by
  rw [← r.next hC h]
  exact (r.ix_at (k := n + 1 - r.C) (by omega) h).2.2

/-- **The machine at first control is the real run's frame `b`** (the old link `Route.Run.roomCtl`) -/
theorem RoomRun.fe_C (r : RoomRun sy m N S b lim) : r.fe r.C = S.seq b := by
  show S.seq (b + FrameKeep.nthUp (FrameKeep.upAt sy m S b) lim (r.C - r.C)) = S.seq b
  rw [Nat.sub_self, FrameKeep.nthUp_zero, Nat.add_zero]

/-- the counted frames come in order, one after the other -/
theorem RoomRun.ix_lt (r : RoomRun sy m N S b lim) {k : Nat} (h : k + 1 ≤ r.ups) : r.ix k < r.ix (k + 1) :=
  FrameKeep.nthUp_lt (f := FrameKeep.upAt sy m S b) (N := lim) (j := k) h

/-- the counted frames come in order -/
theorem RoomRun.ix_mono (r : RoomRun sy m N S b lim) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ r.ups) : r.ix j ≤ r.ix k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 : r.ix (j + d) < r.ix (j + d + 1) := FrameKeep.nthUp_lt (f := FrameKeep.upAt sy m S b) (N := lim) (j := j + d) (by omega)
    show r.ix j ≤ r.ix (j + d + 1)
    omega

/-- **The frames between the end of the room's frame `n` and the start of its frame `n + 1` end paused**: frame `b + k` of the run for `ix (n − C) ≤ k` and
`k + 1 < ix (n + 1 − C)` -/
theorem RoomRun.between (r : RoomRun sy m N S b lim) {n k : Nat} (hC : r.C ≤ n) (h : n + 1 - r.C ≤ r.ups) (hk1 : r.ix (n - r.C) ≤ k) (hk2 : k + 1 < r.ix (n + 1 - r.C)) :
    ¬ FrameKeep.Unpaused sy m (S.seq (b + (k + 1))) := by
  have e : n + 1 - r.C - 1 = n - r.C := by omega
  have hb := FrameKeep.nthUp_between (f := FrameKeep.upAt sy m S b) (N := lim) (j := n + 1 - r.C) (n := k) (by omega) h (by rw [e]; exact hk1) hk2
  intro hu
  have e2 : FrameKeep.upAt sy m S b (k + 1) = true := by
    simp only [FrameKeep.upAt, beq_iff_eq]
    exact hu
  rw [e2] at hb
  cases hb

end

/-! ## What the computation provides -/

/-- the bound on the distance from `Φ ≤ p`, with `g_fast` on every frame: it needs no condition on the running speed -/
def fastDist (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * min (top sy : Int) ((p + gFast sy m) / 256) + fastDist sy m (p + gFast sy m) n

/-- on every frame of an arc, its length is at most the given number -/
def lenOk (ks kf : Nat) (x : Arc) : Bool := decide (x.k ≤ if x.fast then kf else ks)

/-- a jump from the floor: on the first `low` frames after the takeoff frame the feet are low, he is rising and in the air state, and a jump
that comes back to the floor lasts at least `hop` frames -/
def floorArcOk (sy : Syms) (h low hop : Nat) (x : Arc) : Bool :=
  (decide (low < x.k) || (decide (Jump.cornerY sy h ≤ x.s.y.toNat) && !falling x.s && x.s.st != 0)) &&
    (!(falling x.s && decide (groundY sy ≤ x.s.y.toNat)) || decide (hop ≤ x.k))

/-- `Φ` counted only to the right: on an air frame facing right it grows by at most `a₁`. Moving left, the adder is doubled, so a state just
below 0 is worth what its reversal gives: the three cases are one, one and two more frames of the doubled adder -/
def psiP (sy : Syms) (m : Machine) (s : HS) : Int :=
  if 0 ≤ V s then V s + w sy m s
  else max 0 (if 256 - gSlow sy m ≤ V s then V s + a1 sy m
    else if -gSlow sy m ≤ V s then V s + gSlow sy m
    else if -gSlow sy m - a1 sy m ≤ V s then V s + gSlow sy m + a1 sy m else 0)

/-- on an air frame facing right: the facing stays, `Ψ` grows by at most `a₁`, `V` falls by at most `g_slow` -/
def airOk (sy : Syms) (m : Machine) (s : HS) (i : HIn) : Bool :=
  let t := hstep sy m s i
  t.fd == s.fd && decide (psiP sy m t ≤ psiP sy m s + a1 sy m) && decide (V s - V t ≤ gSlow sy m)

/-- the states of the fall: below the air threshold, facing right, `RunningSpeed` 0 -/
def fallStates (sy : Syms) : List HS :=
  ((speedsB sy).filter fun v => decide ((sbyte v).natAbs < sy.AirFastSpeed.toNat)).flatMap fun v =>
    bytes.flatMap fun f => (mds v).map fun md => { v, f, fd := 1, md, rs := 0 }

def airCheck (sy : Syms) (m : Machine) : Bool := (fallStates sy).all fun s => airI.all (airOk sy m s)

/-- how far an air frame after `j` frames moves him at most, from `Ψ ≤ p` -/
def airDist (sy : Syms) (m : Machine) (p : Int) : Nat → Int
  | 0 => 0
  | j + 1 => airDist sy m p j + 16 * ((p + a1 sy m * ((j + 1 : Nat) : Int)) / 256)

/-- how far he moves left at least, when `-V` is at least `u` at the end of `k` air frames -/
def backD (sy : Syms) (m : Machine) (u : Int) : Nat → Int
  | 0 => 0
  | k + 1 => 16 * (u / 256) + backD sy m (u - gSlow sy m) k

/-- how far he moves left at most, from `Φ ≤ p` -/
def leftDist (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * ((nxt sy m p + 255) / 256) + leftDist sy m (nxt sy m p) n

/-- below this `|V|` the speed is below the running threshold -/
def runTheta (sy : Syms) : Int := 256 * (sy.RunSpeedMin.toNat : Int) - 255

/-- for `k` more frames `|v|` stays below the running threshold. Most states are decided by the bound on `Φ` -/
def safeFrom (sy : Syms) (m : Machine) : Nat → HS → Bool
  | 0, s => decide ((sbyte s.v).natAbs < sy.RunSpeedMin.toNat)
  | k + 1, s => decide ((sbyte s.v).natAbs < sy.RunSpeedMin.toNat) &&
      (decide (iterN sy m (phi sy m s) (k + 1) < runTheta sy) || inputsN.all fun i => safeFrom sy m k (hstep sy m s i))

/-- moving right at the end of the fall, with `Φ ≤ p` -/
def safeStates (sy : Syms) : List HS :=
  ((speedsB sy).filter fun v => decide (0 ≤ sbyte v) && decide ((sbyte v).natAbs < sy.AirFastSpeed.toNat)).flatMap fun v =>
    bytes.flatMap fun f => (mds v).map fun md => { v, f, fd := 1, md, rs := 0 }

def safeCheck (sy : Syms) (m : Machine) (p : Int) (k : Nat) : Bool :=
  (safeStates sy).all fun s => !decide (phi sy m s ≤ p) || safeFrom sy m k s

/-- the height added in `n` frames, from the speed `w` and the force `f` -/
def fallSum (w f : Int) : Nat → Int
  | 0 => 0
  | n + 1 => fallSum w f n + w + f * (n : Int)

/-- the height with its fraction on a stand `j` frames after first control, at most: a whole row -/
def standB (N : Nums) (j : Nat) : Int := 4096 * ((N.startY + fallSum N.startW (N.fallF : Int) j) / 4096) + 255

/-- how far he moves at most from `Φ ≤ p` in `n` frames below the air threshold -/
def capRamp (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * min ((sy.AirFastSpeed.toNat : Int) - 1) (nxt sy m p / 256) + capRamp sy m (nxt sy m p) n

/-! ### The first fall

From first control up to the first stand every frame is in the air, so it follows `vstepR` (`RoomRun.vair_of`), or he lands and stands. So up to the first stand the
vertical state `d` frames after first control is a state of `fallLayer d`: from the states at first control (`Nums.vStart`), `vstepR` with A pressed or not. -/

/-- the states one frame later in the air: `vstepR` with A pressed or not -/
def fallNext (sy : Syms) (m : Machine) (L : List VS) : List VS :=
  (L.flatMap fun s => [vstepR sy m s true, vstepR sy m s false]).eraseDups

/-- the states of the first fall `d` frames after first control, before any stand -/
def fallLayer (sy : Syms) (m : Machine) (L : List VS) : Nat → List VS
  | 0 => L
  | d + 1 => fallNext sy m (fallLayer sy m L d)

/-- **The heights at the end of the move of the first fall before its last frame** (round 30): `vstepR` with A or not from each state of `fallLayer` at `d < fall − 1` -/
def ysFall (sy : Syms) (m : Machine) (N : Nums) : List UInt8 :=
  ((List.range (N.fall - 1)).flatMap fun d => (fallLayer sy m N.vStart d).flatMap fun s => [true, false].map fun a => (vstepR sy m s a).y).eraseDups

theorem mem_ysFall {sy : Syms} {m : Machine} {N : Nums} {d : Nat} (hd : d < N.fall - 1) {s : VS} (hs : s ∈ fallLayer sy m N.vStart d) (a : Bool) :
    (vstepR sy m s a).y ∈ ysFall sy m N := by
  unfold ysFall
  refine List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨d, List.mem_range.2 hd, List.mem_flatMap.2 ⟨s, hs, ?_⟩⟩)
  cases a <;> simp

/-- `VDrop` as a check -/
def vdropB (s t : VS) : Bool :=
  t.st != 1 && decide (VY t ≤ VY s + VW s) && decide (VW t ≤ VW s + (s.vfd.toNat : Int)) && t.vfd == s.vfd

/-- the frame after a state `s` of the first fall `d` frames after first control, with A or not: `t = vstepR s a` is in the state 2; `VDrop` from `s` to `t` and to
its landing; a landing before `fall` is not on the floor, and at `fall` he falls and the landing is on the floor -/
def fallStep (sy : Syms) (m : Machine) (N : Nums) (d : Nat) (s : VS) (a : Bool) : Bool :=
  let t := vstepR sy m s a
  t.st == 2 && vdropB s t && (!falling t || vdropB s (VertAir.land t)) &&
    (decide (N.fall ≤ d + 1) || !falling t || decide ((VertAir.land t).y.toNat ≠ groundY sy)) &&
    (decide (d + 1 ≠ N.fall) || (falling t && decide ((VertAir.land t).y.toNat = groundY sy)))

/-- a state of the first fall: in the state 2, and both next frames -/
def fallOk (sy : Syms) (m : Machine) (N : Nums) (d : Nat) (s : VS) : Bool :=
  s.st == 2 && fallStep sy m N d s true && fallStep sy m N d s false

/-- the layers `d, d + 1, …, d + k − 1` from `L` -/
def fallRun (sy : Syms) (m : Machine) (N : Nums) : Nat → Nat → List VS → Bool
  | 0, _, _ => true
  | k + 1, d, L => L.all (fallOk sy m N d) && fallRun sy m N k (d + 1) (fallNext sy m L)

/-- **The check on the ROM of the first fall**: the fall is not empty and ends before `standF`; at the top speed from the start he is not past the block's right end by
`standF`; and every state of the first fall before `standF` -/
def fallCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  decide (0 < N.fall) && decide (N.fall < N.standF) && decide ((room sy N).P1 + 16 * (top sy : Int) * (N.standF : Int) < goalP sy) &&
    fallRun sy m N N.standF 0 N.vStart

/-- **The check on the ROM of the landing frame**: from every state of the first fall one frame before its end, `vstepR` with A or not is at the height `landY`
and does not rise -/
def landCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  (fallLayer sy m N.vStart (N.fall - 1)).all fun s => [true, false].all fun a =>
    (vstepR sy m s a).y == landY sy && (vstepR sy m s a).vy &&& 0x80 == 0

/-- **The check on the ROM of the vertical page in the first fall**: from every state of the first fall before its end, `vstepR` with A or not does not rise, and the
machine of `vstep` after the movement routine has the vertical page 1 -/
def highCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  (List.range N.fall).all fun d => (fallLayer sy m N.vStart d).all fun s => [true, false].all fun a =>
    (vstepR sy m s a).vy &&& 0x80 == 0 && peek (vRunR sy m s a) sy.Player_Y_HighPos == 1

theorem highCheck_spec {sy : Syms} {m : Machine} {N : Nums} (h : highCheck sy m N = true) {d : Nat} (hd : d < N.fall) {s : VS}
    (hs : s ∈ fallLayer sy m N.vStart d) (a : Bool) :
    (vstepR sy m s a).vy &&& 0x80 = 0 ∧ peek (vRunR sy m s a) sy.Player_Y_HighPos = 1 := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.2 hd)) s hs
  have h2 := List.all_eq_true.mp h1 a (by cases a <;> simp)
  simpa only [Bool.and_eq_true, beq_iff_eq] using h2

/-- **The check on the ROM of the heights in the first fall**: from every state of the first fall before its end, `vstepR` with A or not is at a height from 32 to 206 -/
def wallYCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  (List.range N.fall).all fun d => (fallLayer sy m N.vStart d).all fun s => [true, false].all fun a =>
    decide (32 ≤ (vstepR sy m s a).y.toNat) && decide ((vstepR sy m s a).y.toNat < 207)

theorem wallYCheck_spec {sy : Syms} {m : Machine} {N : Nums} (h : wallYCheck sy m N = true) {d : Nat} (hd : d < N.fall) {s : VS}
    (hs : s ∈ fallLayer sy m N.vStart d) (a : Bool) :
    32 ≤ (vstepR sy m s a).y.toNat ∧ (vstepR sy m s a).y.toNat < 207 := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.2 hd)) s hs
  have h2 := List.all_eq_true.mp h1 a (by cases a <;> simp)
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h2

/-- **The heights of the first fall before its last frame are above the floor's** (round 30): from every state of the first fall at a frame `d < fall − 1`, `vstepR`
with A or not is above the floor's height -/
def wallYCheckX (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  (List.range (N.fall - 1)).all fun d => (fallLayer sy m N.vStart d).all fun s => [true, false].all fun a =>
    decide ((vstepR sy m s a).y.toNat < groundY sy)

theorem wallYCheckX_spec {sy : Syms} {m : Machine} {N : Nums} (h : wallYCheckX sy m N = true) {d : Nat} (hd : d < N.fall - 1) {s : VS}
    (hs : s ∈ fallLayer sy m N.vStart d) (a : Bool) : (vstepR sy m s a).y.toNat < groundY sy := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h d (List.mem_range.2 hd)) s hs
  have h2 := List.all_eq_true.mp h1 a (by cases a <;> simp)
  simpa only [decide_eq_true_eq] using h2

/-- from every state with the facing `fd` and `V ≤ −w`, one frame of `hstep` with every normalized input leaves a speed byte from 129 on: negative, and not −128 -/
def negCheckJ (sy : Syms) (m : Machine) (w : Int) (fd : UInt8) : Bool :=
  (statesFd sy fd).all fun s => !decide (V s ≤ -w) || inputsN.all fun i => decide (129 ≤ (hstep sy m s i).v.toNat)

/-- **From a state of the domain that moves left at `w` or more (`V ≤ −w`), one frame of `hstep` with any input leaves a speed byte from 129 on** (as
`RoomWall.neg_of_check`) -/
theorem negJ_of_check {sy : Syms} {m : Machine} {w : Int} (hsp : speedsComplete sy = true) (hn : normIdem = true)
    (h1 : negCheckJ sy m w 1 = true) (h2 : negCheckJ sy m w 2 = true) (h3 : negCheckJ sy m w 3 = true) :
    ∀ s, inD sy s = true → V s ≤ -w → ∀ i ∈ inputs, 129 ≤ (hstep sy m s i).v.toNat := by
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
  have hall : negCheckJ sy m w fd = true := by
    simp only [Potential.facings, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with h | h | h <;> subst h
    · exact h1
    · exact h2
    · exact h3
  simp only [negCheckJ, List.all_eq_true] at hall
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
    simp only [decide_eq_true_eq] at h4
    rw [e] at h4
    exact h4

/-- from a state that moves left, one frame of `hstep` in the air with every normalized input gains at most `gFast`: `V' ≤ gFast` (round 28, for `push_one`) -/
def gainCheck (sy : Syms) (m : Machine) (fd : UInt8) : Bool :=
  (statesFd sy fd).all fun s => decide (0 ≤ sbyte s.v) || inputsN.all fun i => i.st == 0 || decide (V (hstep sy m s i) ≤ gFast sy m)

theorem norm_st (i : HIn) : (norm i).st = i.st := by
  unfold norm
  split <;> rfl

/-- **From a state of the domain that moves left, one frame of `hstep` in the air gains at most `gFast`** -/
theorem gain_of_check {sy : Syms} {m : Machine} (hsp : speedsComplete sy = true) (hn : normIdem = true)
    (h1 : gainCheck sy m 1 = true) (h2 : gainCheck sy m 2 = true) (h3 : gainCheck sy m 3 = true) :
    ∀ s, inD sy s = true → sbyte s.v < 0 → ∀ i ∈ inputs, i.st ≠ 0 → V (hstep sy m s i) ≤ gFast sy m := by
  intro s hD hV i hi hst
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
  have hall : gainCheck sy m fd = true := by
    simp only [Potential.facings, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with h | h | h <;> subst h
    · exact h1
    · exact h2
    · exact h3
  simp only [gainCheck, List.all_eq_true] at hall
  have hc := hall _ hmem
  have hin : norm i ∈ inputsN := List.mem_eraseDups.2 (List.mem_map.2 ⟨i, hi, rfl⟩)
  have hid : norm (norm i) = norm i := by
    simp only [normIdem, List.all_eq_true, beq_iff_eq] at hn
    exact hn i hi
  have e : hstep sy m { v, f, fd, md, rs } (norm i) = hstep sy m { v, f, fd, md, rs } i := by
    unfold Potential.hstep
    rw [hid]
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
  rcases hc with hc | hc
  · have hV' : sbyte v < 0 := hV
    exact absurd hc (by omega)
  · rcases hc _ hin with h4 | h4
    · rw [norm_st] at h4
      exact absurd h4 hst
    · rw [e] at h4
      exact h4

/-- one frame of `hstep` in the air or with a jump keeps the facing direction (round 28, for `facing`). Not used by the route since round 29: `RoomCore.facing`
holds on every frame (`RoomRun.facing_of`), so `WallFacts` no longer checks it -/
def faceCheck (sy : Syms) (m : Machine) (fd : UInt8) : Bool :=
  (statesFd sy fd).all fun s => inputsN.all fun i => (i.st == 0 && !i.jump) || (hstep sy m s i).fd == s.fd

theorem norm_jump (i : HIn) : (norm i).jump = i.jump := by
  unfold norm
  split <;> rfl

/-- **From a state of the domain, one frame of `hstep` in the air or with a jump keeps the facing** -/
theorem face_of_check {sy : Syms} {m : Machine} (hsp : speedsComplete sy = true) (hn : normIdem = true)
    (h1 : faceCheck sy m 1 = true) (h2 : faceCheck sy m 2 = true) (h3 : faceCheck sy m 3 = true) :
    ∀ s, inD sy s = true → ∀ i ∈ inputs, (i.st ≠ 0 ∨ i.jump = true) → (hstep sy m s i).fd = s.fd := by
  intro s hD i hi hsj
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
  have hall : faceCheck sy m fd = true := by
    simp only [Potential.facings, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with h | h | h <;> subst h
    · exact h1
    · exact h2
    · exact h3
  simp only [faceCheck, List.all_eq_true] at hall
  have hc := hall _ hmem
  have hin : norm i ∈ inputsN := List.mem_eraseDups.2 (List.mem_map.2 ⟨i, hi, rfl⟩)
  have hid : norm (norm i) = norm i := by
    simp only [normIdem, List.all_eq_true, beq_iff_eq] at hn
    exact hn i hi
  have e : hstep sy m { v, f, fd, md, rs } (norm i) = hstep sy m { v, f, fd, md, rs } i := by
    unfold Potential.hstep
    rw [hid]
  have h4 := hc _ hin
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true, norm_st, norm_jump] at h4
  rcases h4 with ⟨h5, h6⟩ | h5
  · rcases hsj with h7 | h7
    · exact absurd h5 h7
    · rw [h6] at h7; exact absurd h7 (by decide)
  · rw [e] at h5
    exact h5

/-! ### The frames with no jump

With no jump since first control, every frame in the air is `vstepR` or its landing (`RoomRun.vair_of`), and every frame that starts standing ends as `StandNext` allows
(`RoomRun.vstand_of`: `InRoom.stand`). So the vertical states are those of a finite set. The check `noJumpCheck` goes through it frame by frame from the states at first
control (`njRun`): at each frame the states first seen there meet `noJumpOk` (in the state 0 or 2; in the state 2 both next frames in the air are `VDrop`), are not on the
floor before `fall`, and their next states (`noJumpNext`) not yet seen are the states first seen at the next frame. Each `vstepR` is computed once (`njStep`). So a sequence
of states from first control with each frame a next state meets the check at each frame (`njRun_sound`, `noJump_ok`). -/

/-- the vertical states one frame later with no jump: in the air `vstepR` with A pressed or not, and its landing if it falls; standing, the state 0 or 2 with the height and
the speed kept, or the landing, with A pressed or not -/
def noJumpNext (sy : Syms) (m : Machine) (s : VS) : List VS :=
  if s.st == 0 then [true, false].flatMap fun a => [{ s with st := 0, prevA := a }, { s with st := 2, prevA := a }, { VertAir.land s with prevA := a }]
  else [true, false].flatMap fun a => let t := vstepR sy m s a; if falling t then [t, VertAir.land t] else [t]

/-- he stands on the floor, as a check -/
def onFloorB (sy : Syms) (s : VS) : Bool := s.st == 0 && decide (s.y.toNat = groundY sy)

/-- a state with no jump: in the state 0 or 2; in the state 2 both next frames in the air are in the state 2 and `VDrop`, and so are their landings -/
def noJumpOk (sy : Syms) (m : Machine) (s : VS) : Bool :=
  s.st == 0 || (s.st == 2 && [true, false].all fun a => let t := vstepR sy m s a; t.st == 2 && vdropB s t && (!falling t || vdropB s (VertAir.land t)))

/-- `noJumpOk` and `noJumpNext` of a state together, each `vstepR` computed once (`njStep_eq`) -/
def njStep (sy : Syms) (m : Machine) (s : VS) : Bool × List VS :=
  if s.st == 0 then (true, [true, false].flatMap fun a => [{ s with st := 0, prevA := a }, { s with st := 2, prevA := a }, { VertAir.land s with prevA := a }])
  else
    let tT := vstepR sy m s true
    let tF := vstepR sy m s false
    let one := fun t => if falling t then [t, VertAir.land t] else [t]
    let okT := fun t => t.st == 2 && vdropB s t && (!falling t || vdropB s (VertAir.land t))
    (s.st == 2 && (okT tT && okT tF), one tT ++ one tF)

/-- the states of `L` not yet in `H` go into `H` and into the list `F` -/
def njAdd (H : Std.HashSet VS) (F : List VS) : List VS → Std.HashSet VS × List VS
  | [] => (H, F)
  | t :: L => if H.contains t then njAdd H F L else njAdd (H.insert t) (t :: F) L

/-- **The check, frame by frame**: `F` holds the states first seen at frame `d`, `H` the states seen so far. Each state of `F` meets `noJumpOk` and is not on the floor
before `fall`; its next states not yet seen make the states first seen at frame `d + 1`. For `k` frames -/
def njRun (sy : Syms) (m : Machine) (N : Nums) : Nat → Nat → Std.HashSet VS → List VS → Bool
  | 0, _, _, _ => true
  | k + 1, d, H, F =>
    let G := F.map fun s => (s, njStep sy m s)
    G.all (fun g => g.2.1 && (decide (N.fall ≤ d) || !onFloorB sy g.1)) &&
      njRun sy m N k (d + 1) (njAdd H [] (G.flatMap fun g => g.2.2)).1 (njAdd H [] (G.flatMap fun g => g.2.2)).2

/-- **The check on the ROM of the frames with no jump**: from the states at first control, frame by frame up to frame `standF − 1` -/
def noJumpCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  njRun sy m N (N.standF - 1) 0 (Std.HashSet.ofList N.vStart) N.vStart

/-! ### The frames from the first stand on, with any input

A frame that starts standing with a new press of A ends on the takeoff `VertJump.jumpOff` of its height and of the stored speed that the frame reads (`InRoom.jump`). So
with any input the next vertical states are those of `noJumpNext` and, standing, the takeoffs of the height for every stored speed (`anyNext`). From the vertical states at
first control alone this set reaches the floor before `fall`: the walks give a landing at any height, and from such a landing a jump. The first stand away from the floor
is at frame `wallF` or later (`RoomRun.stand_late`: `stand_first` and the field `wall`), and it is the landing of a state of the first fall (`fallLands`). The check
`anyCheck` goes frame by frame up to frame `fall − 1` through the states from such a first stand on (`ajRun`): each state first seen at a frame is not on the floor and,
standing, is on a whole row (`anyOk`); its next states, and the landings of the first fall's layer if the next frame is `wallF` or later, are the states first seen at the
next frame. -/

/-- the takeoff frame from a stand at the height `y` with the stored speed `abs`, on the machine of the player's routine -/
abbrev jumpOffR (sy : Syms) (m : Machine) (y abs : UInt8) : VS := VertJump.jumpOff sy m (FrameModel.ctrlStack sy m) y abs

/-- the takeoffs from the height `y`, for every stored speed -/
def jumpOffs (sy : Syms) (m : Machine) (y : UInt8) : List VS := ((List.range 256).map fun v => jumpOffR sy m y v.toUInt8).eraseDups

/-- **The check on the ROM of the takeoff from the floor**: for every stored speed, the takeoff from the floor's height is the first state of a jump from the floor
(`arcStart`, which has the stored speeds up to the top speed) -/
def offCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  let xs := arcStart sy m (groundY sy) N.h
  (List.range 256).all fun v => xs.any fun x => x.s == jumpOffR sy m (groundY sy).toUInt8 v.toUInt8

theorem offCheck_spec {sy : Syms} {m : Machine} {N : Nums} (h : offCheck sy m N = true) (abs : UInt8) :
    ∃ x ∈ arcStart sy m (groundY sy) N.h, x.s = jumpOffR sy m (groundY sy).toUInt8 abs := by
  have h1 := List.all_eq_true.mp h abs.toNat (List.mem_range.2 abs.toNat_lt)
  obtain ⟨x, hx, e⟩ := List.any_eq_true.mp h1
  refine ⟨x, hx, ?_⟩
  simpa only [UInt8.ofNat_toNat, beq_iff_eq] using e

/-- the takeoffs from the whole row `r` -/
def offRow (sy : Syms) (m : Machine) (r : Nat) : List VS := jumpOffs sy m (16 * r).toUInt8

/-- the takeoffs from each of the 16 whole rows -/
def offTable (sy : Syms) (m : Machine) : Array (List VS) := Array.ofFn (n := 16) fun r => offRow sy m r.val

/-- the vertical states one frame later with any input: those of `noJumpNext` and, standing, the takeoffs of the row from the table `T` -/
def anyNext (sy : Syms) (m : Machine) (T : Array (List VS)) (s : VS) : List VS :=
  noJumpNext sy m s ++ (if s.st == 0 then T[(s.y >>> 4).toNat]! else [])

/-- a state from the first stand on: not on the floor, and standing on a whole row -/
def anyOk (sy : Syms) (s : VS) : Bool := !onFloorB sy s && (s.st != 0 || s.y &&& 0x0F == 0)

/-- the landings one frame after the states of a layer of the first fall -/
def fallLands (sy : Syms) (m : Machine) (L : List VS) : List VS :=
  L.flatMap fun s => [true, false].flatMap fun a => if falling (vstepR sy m s a) then [VertAir.land (vstepR sy m s a)] else []

/-- **The check, frame by frame**: `Lf` is the layer of the first fall at frame `d`, `F` holds the states first seen at frame `d`, `H` the states seen so far. Each state of
`F` meets `anyOk`; its next states and, if `wallF ≤ d + 1`, the landings of `Lf`, not yet seen, make the states first seen at frame `d + 1`. For `k` frames -/
def ajRun (sy : Syms) (m : Machine) (N : Nums) (T : Array (List VS)) : Nat → Nat → List VS → Std.HashSet VS → List VS → Bool
  | 0, _, _, _, _ => true
  | k + 1, d, Lf, H, F =>
    F.all (anyOk sy) &&
      ajRun sy m N T k (d + 1) (fallNext sy m Lf)
        (njAdd H [] (F.flatMap (anyNext sy m T) ++ if N.wallF ≤ d + 1 then fallLands sy m Lf else [])).1
        (njAdd H [] (F.flatMap (anyNext sy m T) ++ if N.wallF ≤ d + 1 then fallLands sy m Lf else [])).2

/-- **The check on the ROM of the frames from the first stand on**: from no state at first control, with the landings of the first fall from frame `wallF` on, frame by
frame up to frame `fall − 1` -/
def anyCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  ajRun sy m N (offTable sy m) N.fall 0 N.vStart {} []

/-- **The bound of `low_by` at frame `C + j`** (since round 27, page `1-1/c-7-5-20-LowBound.md`): up to `runF`, one frame at the top speed for each frame after
`hitF − 1`, where he is left of the corner (`corner_late`); after `runF`, one frame at the top speed for each frame after `runF`. Past the corner by
`16·top·(j − (hitF − 1)) − 1` or `16·top·(j − runF) − 1` -/
def lowB (sy : Syms) (N : Nums) (j : Nat) : Int :=
  cornerP sy - 1 + 16 * (top sy : Int) * ((if j ≤ N.runF then j - (N.hitF - 1) else j - N.runF : Nat) : Int)

/-- the numbers fit together -/
structure NumFacts (sy : Syms) (m : Machine) (N : Nums) : Prop where
  air_pos : 1 ≤ sy.AirFastSpeed.toNat
  stop_small : N.stopPhi + 255 < 256 * (sy.AirFastSpeed.toNat : Int)
  stop_nonneg : 0 ≤ N.stopPhi
  low_nonneg : 0 ≤ N.lowSlack
  hit_ge : N.fall + 1 ≤ N.hitF
  hit_rise : N.hitF ≤ N.fall + 2 + N.rise
  run_le : N.runF ≤ N.fall + 1 + N.rise
  /-- the slow pairs, with the frame on the block and the air speed, then `capDist`, are short of the goal -/
  slow_pairs : N.slow.all (fun q => decide (N.rise ≤ q.1) && decide (N.fall + 1 + q.2 ≤ N.goalF) && decide (q.1 ≤ q.2) &&
      decide (cornerP sy - 1 + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((q.2 - q.1 : Nat) : Int) +
        capDist sy m (N.goalF - (N.fall + 1 + q.2)) < goalP sy)) = true
  fast_pairs : N.fast.all (fun q => decide (N.rise ≤ q.1)) = true
  /-- the slack of a low frame is less than one frame at the top speed (`low_by` bounds the low frames by `16·top − 1` past the corner) -/
  low_top : N.lowSlack ≤ 16 * (top sy : Int) - 1
  /-- a stop with `RunningSpeed` 0 while his feet are low, on each frame from `hitF` to `runF`: the bound `lowB` of that frame (`low_by`) and the potential from it -/
  hit_J : (List.range (N.runF + 1)).all (fun j => decide (j < N.hitF) ||
      decide (lowB sy N j + dbound sy m N.stopPhi (N.goalF - j) < goalP sy)) = true
  /-- a stop with any `RunningSpeed` while his feet are low, on each frame after `runF` to the end of the low frames -/
  hit_F : (List.range (N.fall + 2 + N.rise)).all (fun j => decide (j ≤ N.runF) ||
      decide (lowB sy N j + fastDist sy m N.stopPhi (N.goalF - j) < goalP sy)) = true
  /-- a stop later: at most the top speed after the low frames, and not far past the corner -/
  hit_late : (List.range (N.goalF + 1)).all (fun j => decide (j ≤ N.fall + 1 + N.rise) ||
      decide (min (lowB sy N (N.fall + 1 + N.rise) + 16 * (top sy : Int) * ((j - (N.fall + 1 + N.rise) : Nat) : Int))
        (cornerP sy + N.stopSlack) + fastDist sy m N.stopPhi (N.goalF - j) < goalP sy)) = true
  /-- a takeoff after the last one searched: the top speed from the end of the low frames -/
  late : cornerP sy + N.lowSlack + 16 * (top sy : Int) * ((N.goalF - (N.fall + N.lastG + 2 + N.rise) : Nat) : Int) < goalP sy
  /-- over the block in one jump: below the threshold, the air speed all the way -/
  over_capped : cornerP sy + N.stopSlack + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((N.lenA + 1 : Nat) : Int) < goalP sy
  /-- at the threshold or more, the top speed after the low frames -/
  over_top : cornerP sy + N.lowSlack + 16 * (top sy : Int) * ((N.lenF - N.rise : Nat) : Int) < goalP sy
  /-- or a stop on the way -/
  over_stop : cornerP sy + N.stopSlack + fastDist sy m N.stopPhi (N.lenF - N.rise) < goalP sy
  len_ok : N.lenS < arcFrames ∧ N.lenF < arcFrames ∧ N.lenB < arcFrames ∧ N.lenA < arcFrames
  /-- off the block: a fast jump gives the bound; the others are not shorter, or are short of the mouth -/
  above_le : N.aboveF ≤ N.aboveS + 1
  walk_le : N.aboveF ≤ N.walk + 1
  air_ge : N.aboveS ≤ N.airS + 1
  slow_mouth : goalP sy + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (N.aboveS : Int) ≤ SidePipe.mouthP sy 0
  /-- the order of the frames -/
  rise_lt : N.rise < arcFrames
  corner_le : cornerY sy N.h ≤ groundY sy
  corner_goal : cornerP sy ≤ goalP sy
  last_le : N.lastG ≤ N.rise
  hit_run : N.hitF ≤ N.runF
  /-- the room's start is at least 8 px right of the start of the position's range -/
  start_far : 2048 ≤ 256 * (sy.RoomStartX.toNat : Int)
  run_ge : N.fall + 1 ≤ N.runF
  goal_ge : N.runF + 1 ≤ N.goalF
  fall_wall : N.wallF + 1 + N.wallK ≤ N.fall
  back_le : N.backK ≤ N.fall
  wall_two : 2 ≤ N.wallF
  gs_le : gSlow sy m ≤ gFast sy m
  gs_stop : gSlow sy m ≤ N.stopPhi
  a1_nonneg : 0 ≤ a1 sy m
  /-- with no wall he is left of the corner before `hitF` -/
  corner_open : (room sy N).P1 + airDist sy m (phi sy m (room sy N).s0) N.fall + capDist sy m (N.hitF - 1 - N.fall) < cornerP sy
  /-- the wall is too far for the frames before `wallF - 1` -/
  wall_far : N.wallP < (room sy N).P0 - leftDist sy m (phi sy m (room sy N).s0) (N.wallF - 2)
  /-- after a wall hit he stays left of the corner: before `hitF`, at the corner stops, on the floor, on the low frames -/
  wall_corner : N.wallP + dbound sy m N.stopPhi (N.hitF - 1 - N.wallF) < cornerP sy
  wall_late : N.wallP + dbound sy m N.stopPhi (N.runF - N.wallF) + 16 * (top sy : Int) < cornerP sy
  wall_low : N.wallP + dbound sy m N.stopPhi (N.runF + 1 - N.wallF) +
    16 * (top sy : Int) * ((N.fall + 1 + N.rise - (N.runF + 1) : Nat) : Int) ≤ cornerP sy + N.lowSlack
  /-- a stop by `runF` with `RunningSpeed` not 0, after a wall hit -/
  wall_stops : (List.range (N.goalF + 1)).all (fun j => decide (j < N.hitF) || decide (N.runF < j) ||
    decide (N.wallP + dbound sy m N.stopPhi (j - N.wallF) + fastDist sy m N.stopPhi (N.goalF - j) < goalP sy)) = true
  /-- a wall hit by frame `wallD` or later -/
  wall_near : N.wallP + dbound sy m N.stopPhi (N.goalF - N.wallD) < goalP sy
  wallD_le : N.wallD ≤ N.fall
  /-- facing right after a wall hit before `wallD`: one frame of any kind, then air frames to the end of the fall -/
  wall_phi : nxt sy m N.stopPhi < theta sy
  wall_Q : nxt sy m N.stopPhi + a1 sy m * ((N.fall - N.wallF - 1 : Nat) : Int) ≤ N.fastQ
  wall_open : N.wallP + 16 * (nxt sy m N.stopPhi / 256) + airDist sy m (nxt sy m N.stopPhi) (N.fall - N.wallF - 1) +
    dbound sy m N.fastQ (N.goalF - N.fall) < goalP sy
  wall_u : nxt sy m N.stopPhi < N.fastQ + 1 - 2 * c sy m - gSlow sy m * ((N.wallK - 1 : Nat) : Int)
  wall_k : 1 ≤ N.wallK
  wall_back : N.wallP + 16 * (nxt sy m N.stopPhi / 256) + airDist sy m (nxt sy m N.stopPhi) (N.fall - N.wallK - N.wallF - 1) -
    backD sy m (N.fastQ + 1 - 2 * c sy m) N.wallK + capDist sy m (N.goalF - N.fall) < goalP sy
  /-- turned away after a wall hit before `wallD`: he falls, below the air threshold, until the floor -/
  fall_le : N.fall ≤ N.standF
  /-- the jumps' first frames are before `standF`; a jump off the block or stepping off takes a frame after `t0` at least -/
  vf : N.fall + N.lastG + 1 + N.rise ≤ N.standF ∧ 2 ≤ N.aboveS ∧ 2 ≤ N.aboveF ∧ 1 ≤ N.walk
  gap_D : N.wallD ≤ N.wallF + N.gapF
  gap_two : 2 ≤ N.gapF
  gap_V : iterN sy m N.stopPhi (N.gapF - 2) < N.standV
  stand_far : N.standP < (room sy N).P0 - leftDist sy m (phi sy m (room sy N).s0) (N.wallF - 1)
  gaps_all : (List.range N.wallD).all (fun j => decide (j ≤ N.wallF) || N.gaps.any (fun q => q.1 == j)) = true
  gaps_ok : N.gaps.all (fun q => decide (N.wallD ≤ q.1 + q.2) && decide (q.1 + q.2 + 2 ≤ N.standF) && decide (q.1 + q.2 + 1 ≤ N.goalF) &&
    decide (standB N q.1 + fallSum 0 (N.fallF : Int) q.2 < 256 * (groundY sy : Int)) &&
    decide (N.wallP + capRamp sy m N.stopPhi (q.2 + 1) + capDist sy m (N.goalF - (q.1 + q.2 + 1)) < goalP sy)) = true
  /-- `RunningSpeed` by `runF` with no wall -/
  safe_bound : iterN sy m N.safeP (N.runF - N.fall - 1) < runTheta sy
  stop_safe : iterN sy m N.stopPhi (N.runF - N.fall - 1) < runTheta sy
  back_ok : (room sy N).P1 + airDist sy m (phi sy m (room sy N).s0) (N.fall - N.backK) -
    backD sy m (N.safeP + 1 - 2 * c sy m) N.backK + 16 * (top sy : Int) * ((N.runF - N.fall : Nat) : Int) ≤ N.backP
  hit_B : N.backP + fastDist sy m N.stopPhi (N.goalF - N.hitF) < goalP sy

/-- **The checks for the first stand of the fall** (`RoomRun.stand_first`): one frame of `hstep` from a state that moves left at `standV` or more, for each facing; the
heights of the first fall; `standP` one pixel more is left of 16 px on the first page; the floor's height is a byte -/
structure WallFacts (sy : Syms) (m : Machine) (N : Nums) : Prop where
  sp : speedsComplete sy = true
  neg1 : negCheckJ sy m N.standV 1 = true
  neg2 : negCheckJ sy m N.standV 2 = true
  neg3 : negCheckJ sy m N.standV 3 = true
  y : wallYCheck sy m N = true
  small : N.standP + 256 < 4096
  ground : groundY sy < 256
  /-- round 30 (`RoomRun.stand_hit_of`): a frame `d < wallF` after first control with every frame before following `hstep`, with the speed of `iterN` from the start
  at most: from at or left of `wallP` it ends its move left of 17 px; and from x at most 12 at the end of the move it started at or left of `standP` (that speed, one
  adder, a fraction) -/
  standX : (List.range N.wallF).all (fun d => decide (N.wallP + (iterN sy m (phi sy m (room sy N).s0) d + gFast sy m) / 16 < 256 * 17) &&
    decide (16 * (256 * 13 - 1) + iterN sy m (phi sy m (room sy N).s0) d + gFast sy m + 255 ≤ 16 * N.standP + 15)) = true
  /-- round 30: the heights of the first fall before its last frame are above the floor's -/
  yX : wallYCheckX sy m N = true
  /-- round 30 (`RoomRun.fall_left`): before the end of the fall he is more than one pixel left of the corner: with no hit, from the start and the air frames of the fall;
  after a hit, from `wallP` and the potential of a stop -/
  fallQ : (room sy N).P1 + airDist sy m (phi sy m (room sy N).s0) N.fall + 256 < cornerP sy ∧ N.wallP + dbound sy m N.stopPhi (N.fall - N.wallF) + 256 < cornerP sy

/-- from a vertical state, the frames of a jump for `k` more frames, with A or not, end at `cornerY + 16` or below (round 28) -/
def riseFrom (sy : Syms) (m : Machine) (N : Nums) : VS → Nat → Bool
  | s, 0 => decide (cornerY sy N.h + 16 ≤ s.y.toNat)
  | s, k + 1 => decide (cornerY sy N.h + 16 ≤ s.y.toNat) && [true, false].all fun a => riseFrom sy m N (vstep sy m s a 0) k

theorem riseFrom_y {sy : Syms} {m : Machine} {N : Nums} {s : VS} {k : Nat} (h : riseFrom sy m N s k = true) : cornerY sy N.h + 16 ≤ s.y.toNat := by
  cases k with
  | zero => simpa [riseFrom] using h
  | succ k =>
    simp only [riseFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem riseFrom_next {sy : Syms} {m : Machine} {N : Nums} {s : VS} {k : Nat} (h : riseFrom sy m N s (k + 1) = true) (a : Bool) :
    riseFrom sy m N (vstep sy m s a 0) k = true := by
  simp only [riseFrom, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases a with _ | _
  · exact h.2 false (Or.inr rfl)
  · exact h.2 true (Or.inl rfl)

/-- **The takeoffs from the floor rise slowly** (round 28): from the takeoff of the floor's height with any stored speed, the frames of the jump end at `cornerY + 16`
or below up to `runF − fall − 1` frames after the takeoff frame below the air threshold, and up to `runF − fall − 2` at it or more -/
def riseCheck (sy : Syms) (m : Machine) (N : Nums) : Bool :=
  (List.range 256).all fun v => riseFrom sy m N (jumpOffR sy m (groundY sy).toUInt8 v.toUInt8)
    (if sy.AirFastSpeed.toNat ≤ v then N.runF - N.fall - 2 else N.runF - N.fall - 1)

/-- **The numbers of the block's left side** (`RoomRun.low_floor_of`): the corner's position is that of the coordinate `cornerX` on the page 0, and five pixels more
are on that page; the slack of a low frame is at least one pixel less one 256th, and at least one frame at the top speed less a pixel; with one frame at the top speed
it is below five pixels; from a stop or from moving left one frame gains less than 17 of speed; the charge for the facing is not negative -/
structure CornerFacts (sy : Syms) (m : Machine) (N : Nums) : Prop where
  cx : cornerP sy = 256 * (cornerX sy : Int)
  cx1 : 1 ≤ cornerX sy
  cx5 : cornerX sy + 5 ≤ 256
  slack1 : 255 ≤ N.lowSlack
  slack2 : 16 * (top sy : Int) - 257 ≤ N.lowSlack
  slack3 : N.lowSlack + 16 * (top sy : Int) < 1280
  small : N.stopPhi + amax sy m < 17 * 256
  c_nonneg : 0 ≤ Potential.c sy m
  /-- the least slack is at least one pixel less one 256th (round 28) -/
  tight : 255 ≤ lowT sy
  /-- from moving left, one frame of `hstep` in the air gains at most `gFast` (round 28, `push_one`) -/
  gain1 : gainCheck sy m 1 = true
  gain2 : gainCheck sy m 2 = true
  gain3 : gainCheck sy m 3 = true
  /-- the takeoff frame from the floor and the floor end at `cornerY + 16` or below (round 28) -/
  off16 : (arcStart sy m (groundY sy) N.h).all (fun x => decide (cornerY sy N.h + 16 ≤ x.s.y.toNat)) = true
  floor16 : cornerY sy N.h + 16 ≤ groundY sy
  /-- the takeoffs from the floor rise slowly (round 28) -/
  rise : riseCheck sy m N = true
  /-- the first frame after the fall is before `hitF − 1` -/
  fall2 : N.fall + 2 ≤ N.hitF

/-- the takeoff frame of a jump from the floor ends at `cornerY + 16` or below -/
theorem takeoff16 {sy : Syms} {m : Machine} {N : Nums} (hF : CornerFacts sy m N) {fr : Frames} {T : Nat} (h : OnArc sy m N fr T (T + 1)) :
    cornerY sy N.h + 16 ≤ (fr.vs (T + 1)).y.toNat := by
  obtain ⟨_, x, u, hx, hr, hv⟩ := h
  rw [show T + 1 - (T + 1) = 0 by omega] at hr
  have e := Cert.Reach.zero hr
  have h1 := hF.off16
  simp only [List.all_eq_true, decide_eq_true_eq] at h1
  rw [hv, e]
  exact h1 x hx

/-- the checks of the earlier theorems -/
structure Checks (sy : Syms) (m : Machine) (N : Nums) : Prop where
  air : CFacts sy m
  normI : normIdem = true
  roomOk : roomCheck sy m (room sy N) = true
  /-- the search with one low air frame less, for a big player's fast takeoff (`fast_short`), and the slow pairs for a big player's later slow takeoff -/
  roomBig : 1 ≤ N.rise ∧ roomCheck sy m (roomB sy N) = true ∧ slowBigOk sy m N = true
  /-- for a big player's slow takeoff on the first frame after the fall: the search of `LandDist` from the room's first frame, and the table of the frames after
  the landing (once the field `Approach.slowBig`) -/
  slowLand : LandDist.slowCheck sy m (room sy N) N.slow N.fall N.goalF = true
  window : arcCheck sy m (groundY sy) N.h (windowOk sy N.h N.slow N.fast) = true
  drop : arcCheck sy m (standY sy N.h) N.h (dropOk sy N.aboveS N.aboveF N.airS) = true
  walk : walkOk sy m N.h N.walk = true
  lenG : arcCheck sy m (groundY sy) N.h (lenOk N.lenS N.lenF) = true
  lenY : N.heights.all (fun y0 => arcCheck sy m y0 N.h (lenOk N.lenA N.lenA)) = true
  lenB : arcCheck sy m (standY sy N.h) N.h (lenOk N.lenB N.lenB) = true
  /-- every jump from the floor -/
  floor : ∃ hop, arcCheck sy m (groundY sy) N.h (floorArcOk sy N.h N.rise hop) = true
  /-- the frames of the fall -/
  fall : airCheck sy m = true
  safe : safeCheck sy m (phi sy m (room sy N).s0 + a1 sy m * (N.fall : Int)) (N.runF - N.fall - 1) = true
  /-- a real frame follows the model -/
  model : FrameModel.modelOK sy m (FrameModel.ctrlStack sy m) = true
  /-- the routine of the friction, for `TopSpeed.Frame` -/
  fric : TopSpeed.frictionCheck sy m = true
  /-- the other side of the friction, for `FrameModel.frame_readQL` (round 30) -/
  fricLow : FrameModel.frictionLowCheck sy m = true
  /-- the running threshold is a byte that is not 0 (round 31, `RoomRun.stop_run_of`) -/
  runMin : sy.RunSpeedMin.toUInt8 ≠ 0 ∧ sy.RunSpeedMin.toNat < 256
  nums : NumFacts sy m N
  /-- the first fall: `vstepR` from the states at first control -/
  first : fallCheck sy m N = true
  /-- the frames with no jump since first control -/
  nojump : noJumpCheck sy m N = true
  /-- the frames from the first stand on, with any input -/
  anyin : anyCheck sy m N = true
  /-- the landing frame: at the height `landY`, not rising -/
  land : landCheck sy m N = true
  /-- at the end of the first fall, one pixel right of the farthest frame end is left of `landX`, which is on the first page -/
  landP : (room sy N).P1 + 16 * (top sy : Int) * (N.fall : Int) + 256 < 256 * (N.landX : Int) ∧ N.landX ≤ 256
  /-- the first fall does not rise, and keeps the vertical page 1 -/
  high : highCheck sy m N = true
  /-- the takeoff from the floor is the first state of a jump from the floor -/
  off : offCheck sy m N = true
  /-- after the fall, up to the last frame of the jumps' first frames, one pixel right of the farthest frame end is left of `landX` -/
  floorP : (room sy N).P1 + 16 * (top sy : Int) * ((N.fall + N.lastG + 1 + N.rise : Nat) : Int) + 256 < 256 * (N.landX : Int)
  /-- the floor's height is a whole row -/
  floorRow : (groundY sy).toUInt8 &&& 0xF0 = (groundY sy).toUInt8
  /-- the first stand of the fall -/
  standW : WallFacts sy m N
  /-- the block's left side -/
  corner : CornerFacts sy m N
  /-- on a jump's first frames from the floor the height does not grow -/
  down : arcDown sy m N = true

/-! ## Lists of frames -/

/-- the inputs of frames `u + 1 .. u + n` -/
def seg (inp : Nat → HIn) : Nat → Nat → List HIn
  | _, 0 => []
  | u, n + 1 => inp (u + 1) :: seg inp (u + 1) n

theorem length_seg (inp : Nat → HIn) : ∀ u n, (seg inp u n).length = n
  | _, 0 => rfl
  | u, n + 1 => by simp [seg, length_seg inp (u + 1) n]

theorem seg_add (inp : Nat → HIn) : ∀ u a b, seg inp u (a + b) = seg inp u a ++ seg inp (u + a) b
  | _, 0, b => by simp [seg]
  | u, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [seg, List.cons_append]
    rw [seg_add inp (u + 1) a b, show u + 1 + a = u + (a + 1) by omega]

theorem mem_seg {inp : Nat → HIn} {P : HIn → Prop} : ∀ {u n}, (∀ j, u ≤ j → j < u + n → P (inp (j + 1))) → ∀ i ∈ seg inp u n, P i
  | _, 0, _, i, hi => by simp [seg] at hi
  | u, n + 1, h, i, hi => by
    simp only [seg, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact h u (by omega) (by omega)
    · exact mem_seg (u := u + 1) (n := n) (fun j h1 h2 => h j (by omega) (by omega)) i hi

variable {sy : Syms} {m : Machine} {N : Nums}

/-- following `hstep`, the position and state are those of `go` -/
theorem go_seg {fr : Frames} : ∀ u n, (∀ j, u ≤ j → j < u + n → Follow sy m fr j) →
    go sy m (fr.hs u, fr.P u) (seg fr.inp u n) = (fr.hs (u + n), fr.P (u + n))
  | _, 0, _ => rfl
  | u, n + 1, h => by
    have h0 := h u (by omega) (by omega)
    simp only [seg, go]
    have h1 : adv sy m (fr.hs u, fr.P u) (fr.inp (u + 1)) = (fr.hs (u + 1), fr.P (u + 1)) := by
      unfold adv
      simp only
      rw [← h0.2.1, h0.2.2]
    rw [h1, go_seg (u + 1) n (fun j h2 h3 => h j (by omega) (by omega)),
      show u + 1 + n = u + (n + 1) by omega]

theorem hdist_seg {fr : Frames} (u n : Nat) (h : ∀ j, u ≤ j → j < u + n → Follow sy m fr j) :
    fr.P (u + n) = fr.P u + hdist sy m (fr.hs u) (seg fr.inp u n) := by
  have h1 := go_seg u n h
  have h2 := FastTakeoff.go_snd (sy := sy) (m := m) (seg fr.inp u n) (fr.hs u, fr.P u)
  rw [h1] at h2
  exact h2

theorem inputs_seg {fr : Frames} (u n : Nat) (h : ∀ j, u ≤ j → j < u + n → Follow sy m fr j) :
    ∀ i ∈ seg fr.inp u n, i ∈ inputs :=
  mem_seg (fun j h1 h2 => (h j h1 h2).1)

/-- `P` left of the corner on the frames gives `Low` -/
theorem low_seg {fr : Frames} {cp : Int} : ∀ u n, (∀ j, u ≤ j → j < u + n → Follow sy m fr j) →
    (∀ j, u ≤ j → j < u + n → fr.P (j + 1) < cp) → Low sy m cp (fr.hs u, fr.P u) (seg fr.inp u n)
  | _, 0, _, _ => trivial
  | u, n + 1, h, hl => by
    have h0 := h u (by omega) (by omega)
    have h1 : adv sy m (fr.hs u, fr.P u) (fr.inp (u + 1)) = (fr.hs (u + 1), fr.P (u + 1)) := by
      unfold adv
      simp only
      rw [← h0.2.1, h0.2.2]
    refine ⟨by rw [h1]; exact hl u (by omega) (by omega), ?_⟩
    rw [h1]
    exact low_seg (u + 1) n (fun j h2 h3 => h j (by omega) (by omega)) (fun j h2 h3 => hl j (by omega) (by omega))

/-! ## Bounds on `hdist` -/

theorem fastDist_nonneg (hg : 0 ≤ gFast sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ fastDist sy m p n
  | 0, _, _ => by simp [fastDist]
  | n + 1, p, hp => by
    have ih := fastDist_nonneg hg n (p + gFast sy m) (by omega)
    simp only [fastDist]
    omega

theorem fastDist_mono (hg : 0 ≤ gFast sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → fastDist sy m p n ≤ fastDist sy m p (n + k)
  | 0, k, p, hp => by
    have := fastDist_nonneg hg k p hp
    simpa [fastDist] using this
  | n + 1, k, p, hp => by
    have ih := fastDist_mono hg n k (p + gFast sy m) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [fastDist]
    omega

theorem fast_dist_le (F : Facts sy m) : ∀ (is : List HIn) (s : HS) (p : Int), inD sy s = true → phi sy m s ≤ p →
    (∀ i ∈ is, i ∈ inputs) → hdist sy m s is ≤ fastDist sy m p is.length
  | [], _, _, _, _, _ => by simp [hdist, fastDist]
  | i :: rest, s, p, hD, hp, his => by
    obtain ⟨h1, h2⟩ := FastTakeoff.step_facts F hD (his i (by simp))
    have ih := fast_dist_le F rest _ (p + gFast sy m) h1 (by omega) (fun j hj => his j (by simp [hj]))
    have hpt := phi_ge F (hstep sy m s i)
    generalize ht : hstep sy m s i = t at *
    have hVt : 256 * sbyte t.v ≤ ((V t).natAbs : Int) := by
      have : (0 : Int) ≤ (t.f.toNat : Int) := by omega
      unfold V; omega
    have htop : sbyte t.v ≤ (top sy : Int) := by
      simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at h1
      omega
    have h3 : sbyte t.v ≤ (p + gFast sy m) / 256 := by omega
    simp only [hdist, fastDist, ht]
    omega

theorem dbound_nonneg (F : Facts sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ dbound sy m p n
  | 0, _, _ => by simp [dbound]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := dbound_nonneg F n (nxt sy m p) (by omega)
    simp only [dbound]
    omega

theorem dbound_mono (F : Facts sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → dbound sy m p n ≤ dbound sy m p (n + k)
  | 0, k, p, hp => by
    have := dbound_nonneg F k p hp
    simpa [dbound] using this
  | n + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := dbound_mono F n k (nxt sy m p) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [dbound]
    omega

/-- `capDist` grows with the frames -/
theorem cap_mono (hA : 1 ≤ sy.AirFastSpeed.toNat) (n k : Nat) : capDist sy m n ≤ capDist sy m (n + k) := by
  have h := landing_later (sy := sy) (m := m) 0 n k
  rw [Int.zero_add, Int.mul_zero, Int.zero_add] at h
  have h0 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) := by omega
  have h1 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (k : Int) := Int.mul_nonneg h0 (by omega)
  omega

/-- the same as `FastTakeoff.left_spec`, for any number of frames up to `D` -/
theorem left_spec_le (F : Facts sy m) {D : Nat} {goal : Int} {es : List Ent} {y : Pos}
    (hl : leftOk sy m D goal es = true) (hc : Cov es y)
    (hv : sbyte y.1.v ≤ -(sy.AirFastSpeed.toNat : Int)) {rest : List HIn} (hin : ∀ i ∈ rest, i ∈ inputs)
    (hlen : rest.length ≤ D) : (go sy m y rest).2 < goal := by
  simp only [leftOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hl
  obtain ⟨hall, hgoal⟩ := hl
  obtain ⟨a, b, h1, h2, h3⟩ := FastTakeoff.cov_filter (f := fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int)))
    hc (fun _ _ => by simp only [decide_eq_true_eq]; exact hv)
  obtain ⟨⟨h4, h5⟩, h6⟩ := hall _ h1
  simp only at h4 h5 h6
  generalize hH : List.foldl (fun b (e : Ent) => max b e.2.2) (0 : Int)
    (es.filter fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int))) = H at hgoal h5
  generalize hQ : List.foldl (fun b (e : Ent) => max b (Opening.pOf sy m e.1)) (0 : Int)
    (es.filter fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int))) = Q at hgoal h6
  obtain ⟨hJ1, hJ2, hJ3⟩ := Opening.J_pOf (sy := sy) (m := m) h4
  have hJ : J sy m y.1 Q := ⟨hJ1, by omega, fun h => by have := hJ3 h; omega⟩
  have h7 := dist_le F rest y.1 Q hJ hin
  have hQ0 : 0 ≤ Q := by
    have h8 := phi_ge F y.1
    have h9 := hJ.2.1
    omega
  obtain ⟨k, hk⟩ : ∃ k, D = rest.length + k := ⟨D - rest.length, by omega⟩
  have h10 := dbound_mono F rest.length k Q hQ0
  rw [← hk] at h10
  rw [FastTakeoff.go_snd]
  omega

/-! ## Arcs -/

theorem arcStart_low {sy : Syms} {m : Machine} {y0 h : Nat} {x : Arc} (hx : x ∈ arcStart sy m y0 h) : x.low = 0 := by
  unfold arcStart at hx
  obtain ⟨_, _, h2⟩ := List.mem_map.1 (List.mem_eraseDups.1 hx)
  rw [← h2]

/-- the last low frame is not after the frame -/
theorem arc_low {h : Nat} : ∀ {x u : Arc} {n : Nat}, Cert.Reach (arcSucc sy m h) x n u → x.low ≤ x.k → u.low ≤ u.k
  | _, _, _, .refl _, h0 => h0
  | x, _, _, @Cert.Reach.step _ _ _ y _ _ h1 h2, h0 => by
    refine arc_low h2 ?_
    unfold arcSucc at h1
    split at h1
    · simp at h1
    · simp only [List.mem_map] at h1
      obtain ⟨_, _, h3⟩ := h1
      rw [← h3]
      simp only
      split <;> omega

/-- every arc of a check of `lenOk` ends in time -/
theorem arc_len {y0 h ks kf : Nat} (hc : arcCheck sy m y0 h (lenOk ks kf) = true) {x u : Arc} (hx : x ∈ arcStart sy m y0 h)
    {n : Nat} (hr : Cert.Reach (arcSucc sy m h) x n u) (hs : ks < arcFrames) (hf : kf < arcFrames) :
    n ≤ if x.fast then kf else ks := by
  have hspec := arc_spec hc x hx
  have hK : (if x.fast then kf else ks) < arcFrames := by split <;> assumption
  generalize hK2 : (if x.fast then kf else ks) = K at hK ⊢
  by_cases hn : n ≤ K
  · exact hn
  · exfalso
    have hsp : n = (K + 1) + (n - (K + 1)) := by omega
    rw [hsp] at hr
    obtain ⟨y, h1, _⟩ := Cert.Reach.split (K + 1) (n - (K + 1)) hr
    have h2 := hspec (K + 1) y (by omega) h1
    obtain ⟨h3, h4⟩ := arc_k h1
    have h5 := arcStart_k hx
    simp only [lenOk, decide_eq_true_eq] at h2
    rw [h4, hK2] at h2
    omega


/-! ## The air frames of the fall -/

/-- below the air threshold, facing right, `RunningSpeed` 0 -/
structure FallSt (sy : Syms) (s : HS) : Prop where
  dom : inD sy s = true
  cap : capped sy s = true
  fd : s.fd = 1
  rs : s.rs = 0

theorem psiP_eq_phi {s : HS} (h : 0 ≤ V s) : phi sy m s = psiP sy m s := by
  unfold psiP phi
  rw [if_pos h]
  omega

/-- `Ψ` is at most `Φ`, or the doubled adder -/
theorem psiP_le (ha : 0 ≤ a1 sy m) {s : HS} {p : Int} (h1 : phi sy m s ≤ p) (h2 : gSlow sy m ≤ p) : psiP sy m s ≤ p := by
  by_cases h : 0 ≤ V s
  · rw [← psiP_eq_phi h]
    exact h1
  · have h3 : gSlow sy m = 2 * a1 sy m := rfl
    unfold psiP
    rw [if_neg h]
    split <;> (try split) <;> (try split) <;> omega

theorem v_le_psiP (F : Facts sy m) (s : HS) : 256 * sbyte s.v ≤ psiP sy m s := by
  have h1 := w_nonneg F s
  have h2 : (0 : Int) ≤ (s.f.toNat : Int) := by omega
  unfold psiP
  split
  · unfold V at *
    omega
  · have h3 : 256 * sbyte s.v ≤ V s := by
      unfold V
      omega
    have h4 := Int.le_max_left 0 (if 256 - gSlow sy m ≤ V s then V s + a1 sy m
      else if -gSlow sy m ≤ V s then V s + gSlow sy m
      else if -gSlow sy m - a1 sy m ≤ V s then V s + gSlow sy m + a1 sy m else 0)
    omega

/-- one air frame -/
theorem air_step (H : Checks sy m N) {s : HS} (hs : FallSt sy s) {i : HIn} (hi : AirIn i) :
    FallSt sy (hstep sy m s i) ∧ psiP sy m (hstep sy m s i) ≤ psiP sy m s + a1 sy m ∧ V s - V (hstep sy m s i) ≤ gSlow sy m := by
  have F := H.air.pot
  obtain ⟨hD, hc, hfd, hrs⟩ := hs
  have hD0 := hD
  have hc0 := hc
  obtain ⟨v, f, fd, md, rs⟩ := s
  simp only [inD, Bool.and_eq_true, List.contains_iff_mem] at hD
  obtain ⟨⟨⟨hv, _⟩, hmd⟩, _⟩ := hD
  simp only at hfd hrs
  subst hfd
  subst hrs
  have hvs : v ∈ speedsB sy := by
    have hsp := H.air.speeds
    simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_iff_mem] at hsp
    rcases hsp v (mem_bytes v) with h | h
    · rw [h] at hv; exact absurd hv (by decide)
    · exact h
  have hcv : (sbyte v).natAbs < sy.AirFastSpeed.toNat := by
    simpa only [capped, decide_eq_true_eq] using hc
  have hmem : ({ v, f, fd := 1, md, rs := 0 } : HS) ∈ fallStates sy :=
    List.mem_flatMap.2 ⟨v, List.mem_filter.2 ⟨hvs, by simpa only [decide_eq_true_eq] using hcv⟩,
      List.mem_flatMap.2 ⟨f, mem_bytes f, List.mem_map.2 ⟨md, hmd, rfl⟩⟩⟩
  have hall := H.fall
  simp only [airCheck, List.all_eq_true] at hall
  have h := hall _ hmem _ (FastTakeoff.mem_airI hi)
  rw [show airOk sy m _ (norm i) = airOk sy m _ i by
    unfold airOk
    rw [FastTakeoff.hstep_norm H.normI hi.1]] at h
  simp only [airOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨(FastTakeoff.step_facts F hD0 hi.1).1, ?_, h1, ?_⟩, h2, h3⟩
  · rcases step_cap H.air hD0 hc0 hi.1 with h4 | ⟨h4, _⟩
    · exact h4
    · have : isAir i = true := by simp [isAir, hi.2.1]
      rw [this] at h4
      exact absurd h4 (by decide)
  · have h4 := F.check _ hD0 i hi.1
    have har := F.air_le_run
    simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, beq_iff_eq,
      bne_iff_ne, ne_eq] at h4
    rcases h4.2 with (h5 | h5) | h5
    · exact h5
    · exact absurd trivial h5
    · omega

theorem airDist_mono {p : Int} (hp : 0 ≤ p) (ha : 0 ≤ a1 sy m) (n k : Nat) : airDist sy m p n ≤ airDist sy m p (n + k) := by
  induction k with
  | zero => exact Int.le_refl _
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by omega]
    simp only [airDist]
    have h1 : 0 ≤ a1 sy m * ((n + k + 1 : Nat) : Int) := Int.mul_nonneg ha (by omega)
    have h2 : 0 ≤ (p + a1 sy m * ((n + k + 1 : Nat) : Int)) / 256 := by omega
    omega

theorem leftDist_nonneg (F : Facts sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ leftDist sy m p n
  | 0, _, _ => by simp [leftDist]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := leftDist_nonneg F n (nxt sy m p) (by omega)
    simp only [leftDist]
    omega

theorem leftDist_mono (F : Facts sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → leftDist sy m p n ≤ leftDist sy m p (n + k)
  | 0, k, p, hp => by
    have := leftDist_nonneg F k p hp
    simpa [leftDist] using this
  | n + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := leftDist_mono F n k (nxt sy m p) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [leftDist]
    omega

/-- moving left is bounded by `Φ` too -/
theorem left_dist_le (F : Facts sy m) : ∀ (is : List HIn) (s : HS) (p : Int), J sy m s p → (∀ i ∈ is, i ∈ inputs) →
    -hdist sy m s is ≤ leftDist sy m p is.length
  | [], _, _, _, _ => by simp [hdist, leftDist]
  | i :: rest, s, p, hJ, his => by
    obtain ⟨hJ', _, _⟩ := step_J F hJ (his i (by simp))
    have ih := left_dist_le F rest _ _ hJ' (fun j hj => his j (by simp [hj]))
    have h1 := hJ'.2.1
    have h2 := phi_ge F (hstep sy m s i)
    simp only [hdist, leftDist]
    generalize hstep sy m s i = t at *
    have hf : t.f.toNat < 256 := t.f.toNat_lt
    have h3 : -(256 * sbyte t.v) ≤ ((V t).natAbs : Int) + 255 := by
      unfold V
      omega
    omega

/-! ## The bound on `Φ` over frames -/

theorem iterN_le (F : Facts sy m) : ∀ (k : Nat) (p : Int), p ≤ iterN sy m p k
  | 0, _ => by simp [iterN]
  | k + 1, p => by
    have h1 := le_nxt F p
    have h2 := iterN_le F k (nxt sy m p)
    simp only [iterN]
    omega

theorem nxt_mono (hg : gSlow sy m ≤ gFast sy m) {p q : Int} (h : p ≤ q) : nxt sy m p ≤ nxt sy m q := by
  unfold nxt
  split <;> split <;> omega

theorem iterN_mono (hg : gSlow sy m ≤ gFast sy m) : ∀ (k : Nat) {p q : Int}, p ≤ q → iterN sy m p k ≤ iterN sy m q k
  | 0, _, _, h => by simpa [iterN] using h
  | k + 1, _, _, h => by
    simp only [iterN]
    exact iterN_mono hg k (nxt_mono hg h)

theorem iterN_succ (F : Facts sy m) : ∀ (c : Nat) (p : Int), iterN sy m p c ≤ iterN sy m p (c + 1)
  | 0, p => by simpa [iterN] using le_nxt F p
  | c + 1, p => by
    simp only [iterN]
    exact iterN_succ F c (nxt sy m p)

theorem iterN_count (F : Facts sy m) : ∀ (k j : Nat) (p : Int), iterN sy m p k ≤ iterN sy m p (k + j)
  | k, 0, _ => Int.le_refl _
  | k, j + 1, p => by
    have h1 := iterN_count F k j p
    have h2 := iterN_succ F (k + j) p
    rw [show k + (j + 1) = k + j + 1 by omega]
    omega

/-- below `runTheta`, the speed is below the running threshold -/
theorem speed_lt_of_phi (F : Facts sy m) {s : HS} (h : phi sy m s < runTheta sy) :
    (sbyte s.v).natAbs < sy.RunSpeedMin.toNat := by
  have h1 := phi_ge F s
  have hf : s.f.toNat < 256 := s.f.toNat_lt
  unfold runTheta at h
  unfold V at h1
  omega

/-- a state with a bound that stays below `runTheta` passes `safeFrom` -/
theorem safe_of_bound (F : Facts sy m) (hg : gSlow sy m ≤ gFast sy m) :
    ∀ (k : Nat) {s : HS} {p : Int}, phi sy m s ≤ p → iterN sy m p k < runTheta sy → safeFrom sy m k s = true
  | k, s, p, h1, h2 => by
    have h3 := iterN_le F k p
    have h4 := speed_lt_of_phi F (s := s) (by omega)
    cases k with
    | zero => simpa only [safeFrom, decide_eq_true_eq] using h4
    | succ k =>
      have h5 := iterN_mono hg (k + 1) h1
      simp only [safeFrom, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨h4, Or.inl (by omega)⟩

/-- one frame: `safeFrom` goes on, and `RunningSpeed` stays 0 -/
theorem safe_step (F : Facts sy m) (hg : gSlow sy m ≤ gFast sy m) (hn : normIdem = true) {k : Nat} {s : HS} (hD : inD sy s = true)
    (hrs : s.rs = 0) (hsafe : safeFrom sy m (k + 1) s = true) {i : HIn} (hi : i ∈ inputs) :
    safeFrom sy m k (hstep sy m s i) = true ∧ (hstep sy m s i).rs = 0 := by
  simp only [safeFrom, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hsafe
  obtain ⟨h1, h2⟩ := hsafe
  constructor
  · rcases h2 with h2 | h2
    · have hJ : J sy m s (phi sy m s) := ⟨hD, Int.le_refl _, fun h => absurd hrs h⟩
      obtain ⟨hJ', _, _⟩ := step_J F hJ hi
      exact safe_of_bound F hg k hJ'.2.1 (by simpa only [iterN] using h2)
    · have h3 := h2 (norm i) (FastTakeoff.norm_mem hi)
      rwa [FastTakeoff.hstep_norm hn hi] at h3
  · have h4 := F.check s hD i hi
    simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, beq_iff_eq,
      bne_iff_ne, ne_eq] at h4
    rcases h4.2 with (h5 | h5) | h5
    · exact h5
    · exact absurd hrs h5
    · omega

/-! ## Jumps from the floor -/


theorem reach_snoc {h : Nat} : ∀ {x u y : Arc} {n : Nat}, Cert.Reach (arcSucc sy m h) x n u → y ∈ arcSucc sy m h u →
    Cert.Reach (arcSucc sy m h) x (n + 1) y
  | _, _, _, _, .refl _, hy => .step hy (.refl _)
  | _, _, _, _, .step h1 h2, hy => .step h1 (reach_snoc h2 hy)

/-- on the first frames of a jump the feet are low, he is rising and in the air state -/
theorem arc_facts (H : Checks sy m N) {fr : Frames} {T n : Nat} (h : OnArc sy m N fr T n) (hk : n - (T + 1) ≤ N.rise) :
    cornerY sy N.h ≤ (fr.vs n).y.toNat ∧ falling (fr.vs n) = false ∧ (fr.vs n).st ≠ 0 := by
  obtain ⟨hop, hf⟩ := H.floor
  obtain ⟨_, x, u, hx, hr, hv⟩ := h
  have h1 := arc_spec hf x hx _ u (by have := H.nums.rise_lt; omega) hr
  obtain ⟨h2, _⟩ := arc_k hr
  have h3 := arcStart_k hx
  have h4 : ¬N.rise < u.k := by omega
  simp only [floorArcOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, h4, false_or, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at h1
  rw [hv]
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2⟩

/-- the next frame of a jump, before its low frames are over -/
theorem arc_next (H : Checks sy m N) {fr : Frames} {T n : Nat} (h : OnArc sy m N fr T n) (hk : n + 1 - (T + 1) ≤ N.rise)
    (hv : VFrame sy m N fr n) : OnArc sy m N fr T (n + 1) ∧ AirIn (fr.inp (n + 1)) := by
  have hT := h.1
  obtain ⟨_, hfall, hst⟩ := arc_facts H h (by omega)
  obtain ⟨_, x, u, hx, hr, hu⟩ := h
  -- the arc's next state, with the frame's A
  let y : Arc :=
    { s := vstep sy m u.s (fr.a (n + 1)) 0, k := u.k + 1,
      low := if cornerY sy N.h ≤ (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat then u.k + 1 else u.low,
      above := if (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat < standY sy N.h then 0 else u.above + 1, fast := u.fast }
  have hy : y ∈ arcSucc sy m N.h u := by
    unfold arcSucc
    rw [← hu, hfall]
    simp only [Bool.false_and, if_false, Bool.false_eq_true]
    rw [hu]
    cases ha : fr.a (n + 1) with
    | true => simp [y, ha]
    | false => simp [y, ha]
  have hr' : Cert.Reach (arcSucc sy m N.h) x (n + 1 - (T + 1)) y := by
    rw [show n + 1 - (T + 1) = n - (T + 1) + 1 by omega]
    exact reach_snoc hr hy
  cases hv with
  | stay h1 _ _ => exact absurd h1.1 hst
  | takeoff h1 _ _ _ _ => exact absurd h1.1 hst
  | other _ h2 => exact absurd h2 hst
  | air _ h2 hi =>
    refine ⟨⟨by omega, x, y, hx, hr', ?_⟩, hi⟩
    rw [h2, hu]
  | fall _ h2 =>
    exfalso
    obtain ⟨_, h3, _⟩ := arc_facts H (fr := { fr with vs := fun j => if j = n + 1 then y.s else fr.vs j }) (T := T) (n := n + 1)
      ⟨by omega, x, y, hx, hr', by simp⟩ hk
    simp only [if_true] at h3
    simp only [y] at h3
    rw [hu] at h2
    rw [h2] at h3
    exact absurd h3 (by decide)

/-- the next frame of a jump, before its low frames are over, when it follows `vstep` -/
theorem arc_step (H : Checks sy m N) {fr : Frames} {T n : Nat} (h : OnArc sy m N fr T n) (hk : n + 1 - (T + 1) ≤ N.rise)
    (hv : fr.vs (n + 1) = vstep sy m (fr.vs n) (fr.a (n + 1)) 0) : OnArc sy m N fr T (n + 1) := by
  have hT := h.1
  obtain ⟨_, hfall, _⟩ := arc_facts H h (by omega)
  obtain ⟨_, x, u, hx, hr, hu⟩ := h
  let y : Arc :=
    { s := vstep sy m u.s (fr.a (n + 1)) 0, k := u.k + 1,
      low := if cornerY sy N.h ≤ (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat then u.k + 1 else u.low,
      above := if (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat < standY sy N.h then 0 else u.above + 1, fast := u.fast }
  have hy : y ∈ arcSucc sy m N.h u := by
    unfold arcSucc
    rw [← hu, hfall]
    simp only [Bool.false_and, if_false, Bool.false_eq_true]
    rw [hu]
    cases ha : fr.a (n + 1) with
    | true => simp [y, ha]
    | false => simp [y, ha]
  have hr' : Cert.Reach (arcSucc sy m N.h) x (n + 1 - (T + 1)) y := by
    rw [show n + 1 - (T + 1) = n - (T + 1) + 1 by omega]
    exact reach_snoc hr hy
  refine ⟨by omega, x, y, hx, hr', ?_⟩
  rw [hv, hu]

/-- **`arc_step` on every frame of a jump**: a frame on a jump from the floor that does not start at or below the ground falling, and that follows `vstep`, is on the jump -/
theorem arc_step_all {fr : Frames} {T n : Nat} (h : OnArc sy m N fr T n) (hg : (falling (fr.vs n) && decide (groundY sy ≤ (fr.vs n).y.toNat)) = false)
    (hv : fr.vs (n + 1) = vstep sy m (fr.vs n) (fr.a (n + 1)) 0) : OnArc sy m N fr T (n + 1) := by
  have hT := h.1
  obtain ⟨_, x, u, hx, hr, hu⟩ := h
  let y : Arc :=
    { s := vstep sy m u.s (fr.a (n + 1)) 0, k := u.k + 1,
      low := if cornerY sy N.h ≤ (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat then u.k + 1 else u.low,
      above := if (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat < standY sy N.h then 0 else u.above + 1, fast := u.fast }
  have hy : y ∈ arcSucc sy m N.h u := by
    unfold arcSucc
    rw [← hu, hg]
    simp only [if_false, Bool.false_eq_true]
    rw [hu]
    cases ha : fr.a (n + 1) with
    | true => simp [y, ha]
    | false => simp [y, ha]
  have hr' : Cert.Reach (arcSucc sy m N.h) x (n + 1 - (T + 1)) y := by
    rw [show n + 1 - (T + 1) = n - (T + 1) + 1 by omega]
    exact reach_snoc hr hy
  refine ⟨by omega, x, y, hx, hr', ?_⟩
  rw [hv, hu]

/-! ## The run -/

namespace RoomCore

variable {sz : UInt8} (r : RoomCore sy m N sz)

theorem inD_start (H : Checks sy m N) : inD sy (r.fr.hs r.C) = true := by
  have h := H.roomOk
  simp only [roomCheck, Bool.and_eq_true] at h
  rw [r.start]
  exact h.1.1

/-- every frame up to `t0` is in the domain -/
theorem inD_all (H : Checks sy m N) : ∀ d, r.C + d ≤ r.t0 → inD sy (r.fr.hs (r.C + d)) = true
  | 0, _ => r.inD_start H
  | d + 1, h => by
    have ih := inD_all H d (by omega)
    rcases r.frames (r.C + d) (by omega) (by omega) with h1 | h1
    · rw [show r.C + (d + 1) = r.C + d + 1 by omega, h1.2.1]
      exact (FastTakeoff.step_facts H.air.pot ih h1.1).1
    · exact h1.1

theorem inD_at (H : Checks sy m N) {n : Nat} (h1 : r.C ≤ n) (h2 : n ≤ r.t0) : inD sy (r.fr.hs n) = true := by
  have := inD_all r H (n - r.C) (by omega)
  rwa [show r.C + (n - r.C) = n by omega] at this

/-- a frame that does not stop him follows `hstep` -/
theorem follow_of (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) {n : Nat} (h1 : r.C + N.hitF ≤ n + 1)
    (h2 : n < r.t0) (hC : r.C ≤ n) : Follow sy m r.fr n := by
  rcases r.frames n hC h2 with h | h
  · exact h
  · exact absurd h (hs (n + 1) h1 (by omega))

/-- the last stop -/
theorem last_stop {a : Nat} : ∀ w, a ≤ w → (∃ h, a ≤ h ∧ h ≤ w ∧ Stop sy m N r.fr h) →
    ∃ h, a ≤ h ∧ h ≤ w ∧ Stop sy m N r.fr h ∧ ∀ n, h < n → n ≤ w → ¬Stop sy m N r.fr n
  | w, hw, ⟨h, h1, h2, h3⟩ => by
    induction w with
    | zero =>
      have : h = 0 := by omega
      subst this
      exact ⟨0, h1, h2, h3, fun n h4 h5 => by omega⟩
    | succ w ih =>
      by_cases hs : Stop sy m N r.fr (w + 1)
      · exact ⟨w + 1, by omega, by omega, hs, fun n h4 h5 => by omega⟩
      · have hne : h ≠ w + 1 := fun he => hs (he ▸ h3)
        obtain ⟨h', h4, h5, h6, h7⟩ := ih (by omega) (by omega)
        refine ⟨h', h4, by omega, h6, fun n h8 h9 => ?_⟩
        by_cases hn : n = w + 1
        · rw [hn]; exact hs
        · exact h7 n h8 (by omega)

/-- `μ` per frame, or not past `B` -/
theorem reach_le {P : Nat → Int} {u : Nat} {B μ : Int} (hB : P u ≤ B) (hμ : 0 ≤ μ) {w : Nat}
    (hstep : ∀ n, u ≤ n → n < w → P (n + 1) ≤ P n + μ ∨ P (n + 1) ≤ B) :
    ∀ d, u + d ≤ w → P (u + d) ≤ B + μ * (d : Int)
  | 0, _ => by simpa using hB
  | d + 1, h => by
    have ih := reach_le hB hμ hstep d (by omega)
    have hm : μ * ((d + 1 : Nat) : Int) = μ * (d : Int) + μ := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    have hd : 0 ≤ μ * (d : Int) := Int.mul_nonneg hμ (by omega)
    rw [show u + (d + 1) = u + d + 1 by omega, hm]
    rcases hstep (u + d) (by omega) (by omega) with h1 | h1 <;> omega

/-- **After a stop, what remains is bounded by the speed near 0**: the position at `t0`, from the last stop -/
theorem after_stop {a : Nat} (ha : r.C ≤ a) (h2 : a ≤ r.t0) (hs : ∃ h, a ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h) :
    ∃ h, a ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h ∧ r.fr.P r.t0 = r.fr.P h + hdist sy m (r.fr.hs h) (seg r.fr.inp h (r.t0 - h)) ∧
      ∀ i ∈ seg r.fr.inp h (r.t0 - h), i ∈ inputs := by
  obtain ⟨h', h3, h4, h5, h6⟩ := last_stop r (a := a) r.t0 h2 hs
  have hfol : ∀ j, h' ≤ j → j < h' + (r.t0 - h') → Follow sy m r.fr j := fun j h7 h8 => by
    rcases r.frames j (by omega) (by omega) with h9 | h9
    · exact h9
    · exact absurd h9 (h6 (j + 1) (by omega) (by omega))
  have h7 := hdist_seg h' (r.t0 - h') hfol
  rw [show h' + (r.t0 - h') = r.t0 by omega] at h7
  exact ⟨h', h3, h4, h5, h7, inputs_seg h' (r.t0 - h') hfol⟩

/-- a stopped state is below the air threshold -/
theorem capped_of_stop (H : Checks sy m N) {n : Nat} (hs : Stop sy m N r.fr n) : capped sy (r.fr.hs n) = true := by
  have h1 := phi_ge H.air.pot (r.fr.hs n)
  have h2 := hs.2.1
  have h3 := H.nums.stop_small
  have h4 : (r.fr.hs n).f.toNat < 256 := (r.fr.hs n).f.toNat_lt
  simp only [capped, decide_eq_true_eq]
  unfold V at h1
  omega

/-- air frames or stops keep the speed below the threshold -/
theorem capped_along (H : Checks sy m N) {u w : Nat} (hu : r.C ≤ u) (hw : w ≤ r.t0) (hc : capped sy (r.fr.hs u) = true)
    (hair : ∀ n, u ≤ n → n < w → isAir (r.fr.inp (n + 1)) = true ∨ Stop sy m N r.fr (n + 1)) :
    ∀ d, u + d ≤ w → capped sy (r.fr.hs (u + d)) = true
  | 0, _ => hc
  | d + 1, h => by
    have ih := capped_along H hu hw hc hair d (by omega)
    rw [show u + (d + 1) = u + d + 1 by omega]
    rcases r.frames (u + d) (by omega) (by omega) with h1 | h1
    · rcases hair (u + d) (by omega) (by omega) with h2 | h2
      · rw [h1.2.1]
        rcases step_cap H.air (inD_at r H (by omega) (by omega)) ih h1.1 with h3 | ⟨h3, _⟩
        · exact h3
        · rw [h2] at h3
          exact absurd h3 (by decide)
      · exact capped_of_stop r H h2
    · exact capped_of_stop r H h1

/-! ### The fall -/

/-- the state at first control -/
theorem start_fall (H : Checks sy m N) : FallSt sy (r.fr.hs r.C) := by
  have h := H.nums.air_pos
  rw [r.start]
  refine ⟨?_, ?_, rfl, rfl⟩
  · have h1 := H.roomOk
    simp only [roomCheck, Bool.and_eq_true] at h1
    exact h1.1.1
  · show capped sy { v := 0, f := 0, fd := 1, md := 0, rs := 0 } = true
    simp only [capped, decide_eq_true_eq]
    have h2 : (sbyte (0 : UInt8)).natAbs = 0 := by decide
    rw [h2]
    omega

theorem psiP_start : psiP sy m (r.fr.hs r.C) ≤ phi sy m (room sy N).s0 := by
  rw [r.start]
  have h : (0 : Int) ≤ V (room sy N).s0 := by
    have h1 : (room sy N).s0 = { v := 0, f := 0, fd := 1, md := 0, rs := 0 } := rfl
    rw [h1]
    unfold V
    have h2 : sbyte (0 : UInt8) = 0 := by decide
    rw [h2]
    omega
  rw [← psiP_eq_phi h]
  exact Int.le_refl _

theorem phi0_nonneg (H : Checks sy m N) : 0 ≤ phi sy m (room sy N).s0 := by
  have := phi_ge H.air.pot (room sy N).s0
  omega

/-- air frames from `a` -/
theorem fall_run (H : Checks sy m N) {a : Nat} {p : Int} (hst : FallSt sy (r.fr.hs a)) (hp : psiP sy m (r.fr.hs a) ≤ p) :
    ∀ j, (∀ i, a ≤ i → i < a + j → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1))) →
      FallSt sy (r.fr.hs (a + j)) ∧ psiP sy m (r.fr.hs (a + j)) ≤ p + a1 sy m * (j : Int) ∧
        r.fr.P (a + j) ≤ r.fr.P a + airDist sy m p j
  | 0, _ => by simpa [airDist] using And.intro hst hp
  | j + 1, h => by
    obtain ⟨h1, h2, h3⟩ := fall_run H hst hp j (fun i h4 h5 => h i h4 (by omega))
    obtain ⟨h4, h5⟩ := h (a + j) (by omega) (by omega)
    obtain ⟨h6, h7, h8⟩ := air_step H h1 h5
    have h9 := v_le_psiP H.air.pot (hstep sy m (r.fr.hs (a + j)) (r.fr.inp (a + j + 1)))
    rw [show a + (j + 1) = a + j + 1 by omega, h4.2.1]
    have h10 := h4.2.2
    rw [h4.2.1] at h10
    have hm : a1 sy m * ((j + 1 : Nat) : Int) = a1 sy m * (j : Int) + a1 sy m := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    refine ⟨h6, by rw [hm]; omega, ?_⟩
    simp only [airDist]
    rw [hm]
    omega

/-- moving left at the end of air frames: how far he has moved -/
theorem back_run (H : Checks sy m N) {b : Nat} :
    ∀ (k : Nat) (u : Int), (∀ i, b ≤ i → i < b + k → FallSt sy (r.fr.hs i) ∧ Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1))) →
      u ≤ -V (r.fr.hs (b + k)) → r.fr.P (b + k) ≤ r.fr.P b - backD sy m u k
  | 0, _, _, _ => by simp [backD]
  | k + 1, u, h, hu => by
    obtain ⟨h1, h2, h3⟩ := h (b + k) (by omega) (by omega)
    obtain ⟨_, _, h4⟩ := air_step H h1 h3
    rw [show b + (k + 1) = b + k + 1 by omega] at hu ⊢
    have h5 := h2.2.2
    rw [h2.2.1] at hu h5
    have ih := back_run H k (u - gSlow sy m) (fun i h6 h7 => h i h6 (by omega)) (by omega)
    generalize hstep sy m (r.fr.hs (b + k)) (r.fr.inp (b + k + 1)) = t at *
    have hf : (0 : Int) ≤ (t.f.toNat : Int) := by omega
    have h6 : 256 * sbyte t.v ≤ -u := by
      unfold V at hu
      omega
    simp only [backD]
    omega

theorem back_speed (H : Checks sy m N) {b : Nat} :
    ∀ (k : Nat) (u : Int), (∀ i, b ≤ i → i < b + k → FallSt sy (r.fr.hs i) ∧ Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1))) →
      u ≤ -V (r.fr.hs (b + k)) → u - gSlow sy m * (k : Int) ≤ -V (r.fr.hs b)
  | 0, _, _, hu => by simpa using hu
  | k + 1, u, h, hu => by
    obtain ⟨h1, h2, h3⟩ := h (b + k) (by omega) (by omega)
    obtain ⟨_, _, h4⟩ := air_step H h1 h3
    rw [show b + (k + 1) = b + k + 1 by omega, h2.2.1] at hu
    have ih := back_speed H k (u - gSlow sy m) (fun i h6 h7 => h i h6 (by omega)) (by omega)
    have hm : gSlow sy m * ((k + 1 : Nat) : Int) = gSlow sy m * (k : Int) + gSlow sy m := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [hm]
    omega

/-- with no wall hit, the states of the fall -/
theorem fall_states (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) (hair : ∀ n, r.C ≤ n → n < r.C + N.fall → AirIn (r.fr.inp (n + 1))) :
    ∀ d, d ≤ N.fall → r.C + d ≤ r.t0 → FallSt sy (r.fr.hs (r.C + d))
  | 0, _, _ => start_fall r H
  | d + 1, h1, h2 => by
    have ih := fall_states H hw hair d (by omega) (by omega)
    have h3 := hair (r.C + d) (by omega) (by omega)
    have hg := H.nums.hit_ge
    have hf : Follow sy m r.fr (r.C + d) := hw _ (by omega) (by omega)
    rw [show r.C + (d + 1) = r.C + d + 1 by omega, hf.2.1]
    exact (air_step H ih h3).1

/-! ### Standing -/

/-- with `Follow` on the frame, off the floor he is not standing at its end -/
theorem st_ne {n : Nat} (hn : r.C ≤ n) (h1 : n + 1 < r.C + N.standF)
    (hs : n + 1 < r.C + N.fall ∨ ∃ j, r.C < j ∧ j ≤ n ∧ (r.fr.vs j).st = 0 ∧ ∀ l, j ≤ l → l ≤ n → (r.fr.inp (l + 1)).jump = false)
    (hf : Follow sy m r.fr n) (h2 : ¬OnFloor sy (r.fr.vs (n + 1))) : (r.fr.vs (n + 1)).st ≠ 0 :=
  fun h3 => r.stand_off n hn h1 hs h3 h2 hf

/-- as long as he has touched nothing, the frames of the fall are air frames -/
theorem fall_air (H : Checks sy m N) {n : Nat} (h1 : r.C ≤ n) (h2 : n < r.C + N.fall) (hall : ∀ j, r.C ≤ j → j < n → Follow sy m r.fr j) :
    AirIn (r.fr.inp (n + 1)) := by
  have hle := H.nums.fall_le
  apply r.air_in n h1 (by omega)
  by_cases he : n = r.C
  · rw [he, r.v_start.1]
    decide
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact st_ne r (by omega) (by omega) (Or.inl (by omega)) (hall n' (by omega) (by omega)) (r.fall_long _ h1 h2)

/-! ### The left wall -/

/-- the first frame that does not follow `hstep` -/
theorem first_hit {fr : Frames} {C : Nat} : ∀ n, (¬∀ j, C ≤ j → j < n → Follow sy m fr j) →
    ∃ h, C ≤ h ∧ h < n ∧ ¬Follow sy m fr h ∧ ∀ j, C ≤ j → j < h → Follow sy m fr j
  | 0, hn => absurd (fun j _ h2 => absurd h2 (by omega)) hn
  | n + 1, hn => by
    by_cases h : ∀ j, C ≤ j → j < n → Follow sy m fr j
    · by_cases hc : C ≤ n ∧ ¬Follow sy m fr n
      · exact ⟨n, hc.1, by omega, hc.2, h⟩
      · exfalso
        apply hn
        intro j h1 h2
        by_cases h3 : j < n
        · exact h j h1 h3
        · have h4 : j = n := by omega
          subst h4
          by_cases h5 : Follow sy m fr j
          · exact h5
          · exact absurd ⟨h1, h5⟩ hc
    · obtain ⟨k, h1, h2, h3, h4⟩ := first_hit n h
      exact ⟨k, h1, by omega, h3, h4⟩

/-- the last frame stopped at the wall, up to `w`, and the frames from it on -/
structure Anchor (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C w a : Nat) : Prop where
  ge : C + N.wallF ≤ a
  le : a ≤ w
  P_le : fr.P a ≤ N.wallP
  J' : J sy m (fr.hs a) N.stopPhi
  rs : (fr.hs a).rs = 0
  fol : ∀ i, a ≤ i → i < w → Follow sy m fr i

theorem anchor_P (H : Checks sy m N) {w a : Nat} (ha : Anchor sy m N r.fr r.C w a) :
    r.fr.P w ≤ N.wallP + dbound sy m N.stopPhi (w - (r.C + N.wallF)) := by
  have hF := H.air.pot
  have hfol : ∀ j, a ≤ j → j < a + (w - a) → Follow sy m r.fr j := fun j h1 h2 => ha.fol j h1 (by have := ha.le; omega)
  have h1 := hdist_seg a (w - a) hfol
  have h2 := dist_le hF _ _ _ ha.J' (inputs_seg a (w - a) hfol)
  rw [length_seg] at h2
  have hle := ha.le
  have hge := ha.ge
  rw [show a + (w - a) = w by omega] at h1
  obtain ⟨k, hk⟩ : ∃ k, w - (r.C + N.wallF) = (w - a) + k := ⟨a - (r.C + N.wallF), by omega⟩
  have h3 := dbound_mono hF (w - a) k N.stopPhi H.nums.stop_nonneg
  rw [← hk] at h3
  have h4 := ha.P_le
  omega

/-- with no hit before `h`, a position at `X`, far from the start, is late -/
theorem left_far (H : Checks sy m N) {h K : Nat} {X : Int} (h1 : r.C ≤ h) (h2 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j)
    (hP : r.fr.P h ≤ X) (hf : X < (room sy N).P0 - leftDist sy m (phi sy m (room sy N).s0) K) : r.C + K < h := by
  by_cases hc : r.C + K < h
  · exact hc
  · exfalso
    have hF := H.air.pot
    have hfol : ∀ j, r.C ≤ j → j < r.C + (h - r.C) → Follow sy m r.fr j := fun j h3 h4 => h2 j h3 (by omega)
    have h3 := hdist_seg r.C (h - r.C) hfol
    rw [show r.C + (h - r.C) = h by omega] at h3
    have hJ : J sy m (r.fr.hs r.C) (phi sy m (room sy N).s0) := by
      refine ⟨(start_fall r H).dom, by rw [r.start]; exact Int.le_refl _, fun h4 => absurd (start_fall r H).rs h4⟩
    have h4 := left_dist_le hF _ _ _ hJ (inputs_seg r.C (h - r.C) hfol)
    rw [length_seg] at h4
    obtain ⟨k, hk⟩ : ∃ k, K = (h - r.C) + k := ⟨K - (h - r.C), by omega⟩
    have h5 := leftDist_mono hF (h - r.C) k _ (phi0_nonneg H)
    rw [← hk] at h5
    have h7 := r.startP0
    omega

/-- the first wall frame is late: the wall is far from the start -/
theorem wall_first (H : Checks sy m N) {h : Nat} (h1 : r.C ≤ h) (h2 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j)
    (hP : r.fr.P h ≤ N.wallP) : r.C + N.wallF ≤ h + 1 := by
  have h3 := left_far r H h1 h2 hP H.nums.wall_far
  have h4 := H.nums.wall_two
  omega

/-- from the first wall frame on, up to `runF + 1`, there is a last wall frame -/
theorem anchor_at (H : Checks sy m N) {h : Nat} (h1 : r.C ≤ h) (h2 : h + 1 < r.C + N.hitF) (h3 : ¬Follow sy m r.fr h)
    (h4 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j) (ht : h < r.t0) :
    ∀ d, h + 1 + d ≤ r.C + N.runF + 1 → h + 1 + d ≤ r.t0 → ∃ a, Anchor sy m N r.fr r.C (h + 1 + d) a
  | 0, _, _ => by
    have hw := r.wall h h1 h2 h3
    have hs := (r.frames h h1 ht).resolve_left h3
    exact ⟨h + 1, wall_first r H h1 h4 hw.before, by omega, hw.after, ⟨hs.1, hs.2.1, fun h5 => absurd hw.run h5⟩, hw.run,
      fun i h5 h6 => by omega⟩
  | d + 1, h5, h6 => by
    obtain ⟨a, ha⟩ := anchor_at H h1 h2 h3 h4 ht d (by omega) (by omega)
    rw [show h + 1 + (d + 1) = h + 1 + d + 1 by omega] at h6 ⊢
    have hC : r.C ≤ h + 1 + d := by omega
    by_cases hf : Follow sy m r.fr (h + 1 + d)
    · refine ⟨a, ha.ge, by have := ha.le; omega, ha.P_le, ha.J', ha.rs, fun i h7 h8 => ?_⟩
      by_cases h9 : i < h + 1 + d
      · exact ha.fol i h7 h9
      · rw [show i = h + 1 + d by omega]
        exact hf
    · have hw : WallAt N r.fr (h + 1 + d) := by
        by_cases h7 : h + 1 + d + 1 < r.C + N.hitF
        · exact r.wall _ hC h7 hf
        · rcases r.late _ (by omega) (by omega) ⟨h, h1, by omega, h2, h3⟩ hf with h8 | h8
          · exact h8
          · exfalso
            have hn := H.nums
            have h9 := anchor_P r H ha
            have hge := ha.ge
            obtain ⟨k, hk⟩ : ∃ k, N.runF - N.wallF = (h + 1 + d - (r.C + N.wallF)) + k :=
              ⟨N.runF - N.wallF - (h + 1 + d - (r.C + N.wallF)), by omega⟩
            have h10 := dbound_mono H.air.pot (h + 1 + d - (r.C + N.wallF)) k N.stopPhi hn.stop_nonneg
            rw [← hk] at h10
            have h11 := hn.wall_late
            omega
      have hs := (r.frames _ hC (by omega)).resolve_left hf
      exact ⟨h + 1 + d + 1, by have := ha.ge; have := ha.le; omega, by omega, hw.after,
        ⟨hs.1, hs.2.1, fun h7 => absurd hw.run h7⟩, hw.run, fun i h7 h8 => by omega⟩

/-- with a wall hit before `hitF`: the anchor of any frame from `hitF - 1` to `runF + 1` -/
theorem anchor_of_wall (H : Checks sy m N) (hw : ¬NoWall sy m N r.fr r.C) {w : Nat} (h1 : r.C + N.hitF - 1 ≤ w)
    (h2 : w ≤ r.C + N.runF + 1) (h3 : w ≤ r.t0) : ∃ a, Anchor sy m N r.fr r.C w a := by
  have hg := H.nums.hit_ge
  have hn : ¬∀ j, r.C ≤ j → j < r.C + N.hitF - 1 → Follow sy m r.fr j := fun h4 => hw fun n h5 h6 => h4 n h5 (by omega)
  obtain ⟨h, h4, h5, h6, h7⟩ := first_hit _ hn
  obtain ⟨a, ha⟩ := anchor_at r H h4 (by omega) h6 h7 (by omega) (w - (h + 1)) (by omega) (by omega)
  rw [show h + 1 + (w - (h + 1)) = w by omega] at ha
  exact ⟨a, ha⟩

/-! ### Before `hitF` he is not at the corner -/

/-- **`corner_late`**: before `hitF` he is left of the corner. With no hit, the air frames of the fall and two more frames. With a hit, the
potential from the wall -/
theorem corner_late (H : Checks sy m N) {n : Nat} (h1 : r.C ≤ n) (h2 : n < r.C + N.hitF) (h3 : n ≤ r.t0) : r.fr.P n < cornerP sy := by
  have hN := H.nums
  have hg := hN.hit_ge
  have hA := hN.air_pos
  by_cases hall : ∀ j, r.C ≤ j → j < n → Follow sy m r.fr j
  · have hair : ∀ i, r.C ≤ i → i < n → i < r.C + N.fall → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h4 h5 h6 =>
      ⟨hall i h4 h5, fall_air r H h4 h6 (fun j h7 h8 => hall j h7 (by omega))⟩
    have hp : psiP sy m (r.fr.hs r.C) ≤ phi sy m (room sy N).s0 := psiP_start r
    have hp0 := phi0_nonneg H
    have hcap0 : 0 ≤ capDist sy m (N.hitF - 1 - N.fall) := by
      have := cap_mono (m := m) hA 0 (N.hitF - 1 - N.fall)
      simpa [capDist] using this
    have hc := hN.corner_open
    have hP1 := r.startP1
    by_cases hn : n ≤ r.C + N.fall
    · obtain ⟨_, _, h4⟩ := fall_run r H (start_fall r H) hp (n - r.C) (fun i h5 h6 => hair i h5 (by omega) (by omega))
      rw [show r.C + (n - r.C) = n by omega] at h4
      obtain ⟨k, hk⟩ : ∃ k, N.fall = (n - r.C) + k := ⟨N.fall - (n - r.C), by omega⟩
      have h5 := airDist_mono (sy := sy) (m := m) hp0 hN.a1_nonneg (n - r.C) k
      rw [← hk] at h5
      omega
    · obtain ⟨h4, _, h5⟩ := fall_run r H (start_fall r H) hp N.fall (fun i h5 h6 => hair i h5 (by omega) (by omega))
      have hfol : ∀ j, r.C + N.fall ≤ j → j < r.C + N.fall + (n - (r.C + N.fall)) → Follow sy m r.fr j := fun j h6 h7 =>
        hall j (by omega) (by omega)
      have h6 := hdist_seg (r.C + N.fall) (n - (r.C + N.fall)) hfol
      rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at h6
      have h7 := AirCap.dist_capped H.air _ _ h4.dom h4.cap (inputs_seg (r.C + N.fall) (n - (r.C + N.fall)) hfol)
      rw [length_seg] at h7
      obtain ⟨k, hk⟩ : ∃ k, N.hitF - 1 - N.fall = (n - (r.C + N.fall)) + k := ⟨N.hitF - 1 - N.fall - (n - (r.C + N.fall)), by omega⟩
      have h8 := cap_mono (m := m) hA (n - (r.C + N.fall)) k
      rw [← hk] at h8
      omega
  · obtain ⟨h, h4, h5, h6, h7⟩ := first_hit _ hall
    obtain ⟨a, ha⟩ := anchor_at r H h4 (by omega) h6 h7 (by omega) (n - (h + 1)) (by have := hN.hit_run; omega) (by omega)
    rw [show h + 1 + (n - (h + 1)) = n by omega] at ha
    have h8 := anchor_P r H ha
    have hge := ha.ge
    have hle := ha.le
    obtain ⟨k, hk⟩ : ∃ k, N.hitF - 1 - N.wallF = (n - (r.C + N.wallF)) + k := ⟨N.hitF - 1 - N.wallF - (n - (r.C + N.wallF)), by omega⟩
    have h9 := dbound_mono H.air.pot (n - (r.C + N.wallF)) k N.stopPhi hN.stop_nonneg
    rw [← hk] at h9
    have h10 := hN.wall_corner
    omega

/-- he is not past the block's right end before `hitF` -/
theorem t0_late (H : Checks sy m N) : r.C + N.hitF ≤ r.t0 := by
  by_cases h : r.C + N.hitF ≤ r.t0
  · exact h
  · exfalso
    have h1 := corner_late r H r.t0_ge (by omega) (Nat.le_refl _)
    have h2 := r.past
    have h3 := H.nums.corner_goal
    omega

/-! ### The heights after the fall -/

/-- with no wall: from the fall on, he is on the floor or in the first frames of a jump from the floor -/
theorem v_chain (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) :
    ∀ d, d ≤ 1 + N.rise → r.C + N.fall + d ≤ r.t0 → r.C + N.fall + d < r.E → (∀ e, e ≤ d → OnFloor sy (r.fr.vs (r.C + N.fall + e))) ∨
      ∃ T, r.C + N.fall ≤ T ∧ T < r.C + N.fall + d ∧ OnArc sy m N r.fr T (r.C + N.fall + d)
  | 0, _, _, _ => Or.inl (fun e he => by rw [show e = 0 by omega]; exact r.floor_at hw)
  | d + 1, h1, ht, hE => by
    have ih := v_chain H hw d (by omega) (by omega) (by omega)
    rw [show r.C + N.fall + (d + 1) = r.C + N.fall + d + 1 by omega]
    rcases ih with hf | ⟨T, h2, h3, ha⟩
    · have hall : ∀ j, r.C + N.fall ≤ j → j ≤ r.C + N.fall + d → OnFloor sy (r.fr.vs j) := by
        intro j hj1 hj2
        have h4 := hf (j - (r.C + N.fall)) (by omega)
        rwa [show r.C + N.fall + (j - (r.C + N.fall)) = j by omega] at h4
      have hf0 := hf d (Nat.le_refl _)
      cases r.vfloor hw (r.C + N.fall + d) (by omega) (by omega) (by omega) hall with
      | stay _ h2 _ =>
        refine Or.inl (fun e he => ?_)
        rcases Nat.lt_or_ge e (d + 1) with h5 | h5
        · exact hf e (by omega)
        · rw [show r.C + N.fall + e = r.C + N.fall + d + 1 by omega]
          exact h2
      | takeoff _ x hx h2 _ =>
        refine Or.inr ⟨r.C + N.fall + d, by omega, by omega, by omega, x, x, hx, ?_, h2⟩
        rw [show r.C + N.fall + d + 1 - (r.C + N.fall + d + 1) = 0 by omega]
        exact .refl _
      | air h2 _ _ => exact absurd hf0.1 h2
      | fall h2 _ => exact absurd hf0.1 h2
      | other h2 _ => exact absurd hf0 h2
    · exact Or.inr ⟨T, h2, by omega, arc_step H ha (by omega) (r.varc T _ (by omega) (by omega) (by omega) ha (by omega))⟩

/-- `v_chain`, with the frames on the floor up to the takeoff, and each frame of the jump up to frame `C + fall + d` on its arc -/
theorem v_chain2 (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) :
    ∀ d, d ≤ 1 + N.rise → r.C + N.fall + d ≤ r.t0 → r.C + N.fall + d < r.E → (∀ e, e ≤ d → OnFloor sy (r.fr.vs (r.C + N.fall + e))) ∨
      ∃ T, r.C + N.fall ≤ T ∧ T < r.C + N.fall + d ∧ (∀ j, r.C + N.fall ≤ j → j ≤ T → OnFloor sy (r.fr.vs j)) ∧
        ∀ j, T < j → j ≤ r.C + N.fall + d → OnArc sy m N r.fr T j
  | 0, _, _, _ => Or.inl (fun e he => by rw [show e = 0 by omega]; exact r.floor_at hw)
  | d + 1, h1, ht, hE => by
    have ih := v_chain2 H hw d (by omega) (by omega) (by omega)
    rw [show r.C + N.fall + (d + 1) = r.C + N.fall + d + 1 by omega]
    rcases ih with hf | ⟨T, h2, h3, hfl, ha⟩
    · have hall : ∀ j, r.C + N.fall ≤ j → j ≤ r.C + N.fall + d → OnFloor sy (r.fr.vs j) := by
        intro j hj1 hj2
        have h4 := hf (j - (r.C + N.fall)) (by omega)
        rwa [show r.C + N.fall + (j - (r.C + N.fall)) = j by omega] at h4
      have hf0 := hf d (Nat.le_refl _)
      cases r.vfloor hw (r.C + N.fall + d) (by omega) (by omega) (by omega) hall with
      | stay _ h2 _ =>
        refine Or.inl (fun e he => ?_)
        rcases Nat.lt_or_ge e (d + 1) with h5 | h5
        · exact hf e (by omega)
        · rw [show r.C + N.fall + e = r.C + N.fall + d + 1 by omega]
          exact h2
      | takeoff _ x hx h2 _ =>
        refine Or.inr ⟨r.C + N.fall + d, by omega, by omega, hall, fun j hj1 hj2 => ?_⟩
        rw [show j = r.C + N.fall + d + 1 by omega]
        refine ⟨by omega, x, x, hx, ?_, h2⟩
        rw [show r.C + N.fall + d + 1 - (r.C + N.fall + d + 1) = 0 by omega]
        exact .refl _
      | air h2 _ _ => exact absurd hf0.1 h2
      | fall h2 _ => exact absurd hf0.1 h2
      | other h2 _ => exact absurd hf0 h2
    · have hn := ha (r.C + N.fall + d) (by omega) (Nat.le_refl _)
      have hn1 := arc_step H hn (by omega) (r.varc T _ (by omega) (by omega) (by omega) hn (by omega))
      refine Or.inr ⟨T, h2, by omega, hfl, fun j hj1 hj2 => ?_⟩
      rcases Nat.lt_or_ge j (r.C + N.fall + d + 1) with e | e
      · exact ha j hj1 (by omega)
      · rw [show j = r.C + N.fall + d + 1 by omega]
        exact hn1

/-- **On a jump from the floor, up to its last low frame, the height does not grow** (`arcDown`, `varc`): frame `n` ends at the height of an earlier frame of the jump,
or higher -/
theorem arc_down (H : Checks sy m N) {T n : Nat} (hE : n < r.E) (ht : n ≤ r.t0) (hk : n - (T + 1) ≤ N.rise) (hC : r.C ≤ T)
    (harc : ∀ j, T < j → j ≤ n → OnArc sy m N r.fr T j) : ∀ d, T < n - d → (r.fr.vs n).y.toNat ≤ (r.fr.vs (n - d)).y.toNat
  | 0, _ => Nat.le_refl _
  | d + 1, h => by
    have ih := arc_down H hE ht hk hC harc d (by omega)
    have hi := harc (n - (d + 1)) h (by omega)
    have hv := r.varc T (n - (d + 1)) (by omega) (by omega) (by omega) hi (by omega)
    rw [show n - (d + 1) + 1 = n - d by omega] at hv
    obtain ⟨_, x, u, hx, hru, hu⟩ := hi
    have hmem := VertAir.mem_arcSet hx hru (show n - (d + 1) - (T + 1) ≤ N.rise by omega)
    have hku : u.k = n - (d + 1) - (T + 1) := by
      have := (arc_k hru).1
      rw [arcStart_k hx] at this
      omega
    have hc := List.all_eq_true.1 H.down u hmem
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hc
    rcases hc with hc | hc
    · omega
    · have e : (r.fr.vs (n - d)).y.toNat ≤ (r.fr.vs (n - (d + 1))).y.toNat := by
        rw [hv, hu]
        generalize r.fr.a (n - d) = b
        cases b
        · exact hc.2
        · exact hc.1
      omega

/-- **With no wall, on the floor since the end of the fall, each frame from `hitF − 1` to the end of the low frames is `LowAt`**: before `hitF` he is left of the corner
(`corner_late`), and then each frame by `low_floor` -/
theorem low_floors (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) {s : Int} (hs : SlackOK sy s) : ∀ d, r.C + N.hitF - 1 + d ≤ r.C + N.fall + 1 + N.rise → r.C + N.hitF - 1 + d ≤ r.t0 →
    (∀ j, r.C + N.fall ≤ j → j ≤ r.C + N.hitF - 1 + d → OnFloor sy (r.fr.vs j)) → LowS sy m N r.fr s (r.C + N.hitF - 1 + d)
  | 0, _, h3, _ => by
    have hg := H.nums.hit_ge
    have hl := hs.1
    have h := corner_late r H (n := r.C + N.hitF - 1 + 0) (by omega) (by omega) h3
    exact ⟨by omega, Or.inr (Or.inl h)⟩
  | d + 1, h2, h3, hall => by
    have hg := H.nums.hit_ge
    have ih := low_floors H hw hs d (by omega) (by omega) (fun j a b => hall j a (by omega))
    have e : r.C + N.hitF - 1 + (d + 1) = r.C + N.hitF - 1 + d + 1 := by omega
    rw [e] at hall h2 h3 ⊢
    exact r.low_floor hw (r.C + N.hitF - 1 + d) (by omega) h2 (by omega) hall s hs ih

/-- `low_floors` at a frame, with any slack of `SlackOK` -/
theorem low_floor_atS (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) {s : Int} (hs : SlackOK sy s) {n : Nat} (h1 : r.C + N.hitF - 1 ≤ n)
    (h2 : n ≤ r.C + N.fall + 1 + N.rise) (h3 : n ≤ r.t0) (hall : ∀ j, r.C + N.fall ≤ j → j ≤ n → OnFloor sy (r.fr.vs j)) : LowS sy m N r.fr s n := by
  have e : r.C + N.hitF - 1 + (n - (r.C + N.hitF - 1)) = n := by omega
  have h := low_floors r H hw hs (n - (r.C + N.hitF - 1)) (by omega) (by omega) (fun j a b => hall j a (by omega))
  rwa [e] at h

/-- `lowSlack` meets `SlackOK` -/
theorem slack_ok (H : Checks sy m N) : SlackOK sy N.lowSlack := ⟨H.corner.slack1, H.corner.slack2, H.corner.slack3⟩

/-- the least slack `lowT` meets `SlackOK`, and it is at most `lowSlack` -/
theorem tight_ok (H : Checks sy m N) : SlackOK sy (lowT sy) ∧ lowT sy ≤ N.lowSlack := by
  have h1 := H.corner.tight
  have h2 := H.corner.slack2
  have h3 := H.corner.slack3
  unfold lowT at h1 ⊢
  exact ⟨⟨h1, Int.le_refl _, by omega⟩, h2⟩

/-- `low_floors` at a frame -/
theorem low_floor_at (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) {n : Nat} (h1 : r.C + N.hitF - 1 ≤ n) (h2 : n ≤ r.C + N.fall + 1 + N.rise) (h3 : n ≤ r.t0)
    (hall : ∀ j, r.C + N.fall ≤ j → j ≤ n → OnFloor sy (r.fr.vs j)) : LowAt sy m N r.fr n :=
  low_floor_atS r H hw (slack_ok H) h1 h2 h3 hall

/-- **`low_by`**: through the low frames of the earliest jump he is not far past the corner: the bound `lowB` of the frame. Up to `runF`, from `hitF − 1`, where he
is left of the corner (`corner_late`), one frame at the top speed per frame (`move_top`). After `runF`, from a frame left of the corner from `runF` on, the same (`move_top`);
if there is none: with no wall, the heights and the collision routine (`LowAt`: at most `lowSlack ≤ 16·top − 1` past the corner), and on a frame that ends from `cornerY` to
`cornerY + 15` frame by frame from frame `runF` (`LowS` with the least slack `lowT`, `push_one`, `move_top`; frame `runF` ends at `cornerY + 16` or below: `off_ab`,
`ab_of`, `riseCheck`; until round 27 the field `low_at`); with a wall hit, the potential from the wall -/
theorem low_by (H : Checks sy m N) (hE : r.t0 < r.E) {n : Nat} (h1 : r.C ≤ n) (h2 : n ≤ r.C + N.fall + 1 + N.rise) (h3 : n ≤ r.t0) :
    r.fr.P n ≤ lowB sy N (n - r.C) := by
  have hN := H.nums
  have hlt := hN.low_top
  have hl := hN.low_nonneg
  have hg := hN.hit_ge
  have hhr := hN.hit_run
  have ht16 : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  -- from a frame `k` left of the corner: one frame at the top speed per frame
  have chain : ∀ k, r.C ≤ k → k ≤ n → r.fr.P k < cornerP sy → r.fr.P n ≤ cornerP sy - 1 + 16 * (top sy : Int) * ((n - k : Nat) : Int) := by
    intro k hk1 hk2 hk3
    have h7 := reach_le (P := r.fr.P) (u := k) (B := cornerP sy - 1) (μ := 16 * (top sy : Int)) (w := r.t0) (by omega) ht16
      (fun j h8 h9 => Or.inl (r.move_top j (by omega) h9)) (n - k) (by omega)
    rwa [show k + (n - k) = n by omega] at h7
  by_cases hn : n < r.C + N.hitF
  · have h0 := corner_late r H h1 hn h3
    have h5 : (0 : Int) ≤ 16 * (top sy : Int) * ((if n - r.C ≤ N.runF then n - r.C - (N.hitF - 1) else n - r.C - N.runF : Nat) : Int) :=
      Int.mul_nonneg ht16 (by omega)
    unfold lowB
    omega
  by_cases hr : n ≤ r.C + N.runF
  · -- from `hitF − 1`, where he is left of the corner
    have h0 := corner_late r H (n := r.C + N.hitF - 1) (by omega) (by omega) (by omega)
    have h7 := chain (r.C + N.hitF - 1) (by omega) (by omega) h0
    unfold lowB
    rw [if_pos (by omega), show n - r.C - (N.hitF - 1) = n - (r.C + N.hitF - 1) by omega]
    exact h7
  -- after `runF`: the bound is at least one frame at the top speed past the corner
  have hB : ∀ d, 1 ≤ d → d = n - (r.C + N.runF) → cornerP sy + 16 * (top sy : Int) - 1 ≤ lowB sy N (n - r.C) := by
    intro d hd1 hd2
    unfold lowB
    rw [if_neg (by omega), show n - r.C - N.runF = d by omega]
    have : 16 * (top sy : Int) * 1 ≤ 16 * (top sy : Int) * (d : Int) := Int.mul_le_mul_of_nonneg_left (by omega) ht16
    omega
  have hB1 := hB (n - (r.C + N.runF)) (by omega) rfl
  by_cases hk : ∃ k, r.C + N.runF ≤ k ∧ k < n ∧ r.fr.P k < cornerP sy
  · obtain ⟨k, hk1, hk2, hk3⟩ := hk
    have h7 := chain k (by omega) (by omega) hk3
    have h8 : 16 * (top sy : Int) * ((n - k : Nat) : Int) ≤ 16 * (top sy : Int) * ((n - r.C - N.runF : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) ht16
    unfold lowB
    rw [if_neg (by omega)]
    omega
  have hall : ∀ k, r.C + N.runF ≤ k → k < n → cornerP sy ≤ r.fr.P k := fun k a b => by
    by_cases h : r.fr.P k < cornerP sy
    · exact absurd ⟨k, a, b, h⟩ hk
    · omega
  by_cases hw : NoWall sy m N r.fr r.C
  · rcases v_chain r H hw (n - (r.C + N.fall)) (by omega) (by omega) (by omega) with hf | ⟨T, h4, h5, ha⟩
    · have hlf := (low_floor_at r H hw (n := n) (by omega) h2 h3 (fun j hj1 hj2 => by
        have h := hf (j - (r.C + N.fall)) (by omega)
        rwa [show r.C + N.fall + (j - (r.C + N.fall)) = j by omega] at h)).1
      omega
    · rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at h5 ha
      have hfa := arc_facts H ha (by omega)
      by_cases hp : r.fr.P n < cornerP sy
      · omega
      · by_cases hy : (r.fr.vs n).y.toNat < cornerY sy N.h + 16
        · -- every frame from `runF` on is at or past the corner
          unfold lowB
          rw [if_neg (by omega), show n - r.C - N.runF = n - (r.C + N.runF) by omega]
          have hF := H.corner
          obtain ⟨hT1, _⟩ := tight_ok H
          have hvf := hN.vf.1
          have hrl := hN.run_le
          rcases v_chain2 r H hw (n - (r.C + N.fall)) (by omega) (by omega) (by omega) with hf | ⟨T', g1, g2, hfl, harc⟩
          · have := hf (n - (r.C + N.fall)) (Nat.le_refl _)
            rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at this
            exact absurd this.1 hfa.2.2
          rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at g2 harc
          by_cases hyR : (r.fr.vs (r.C + N.runF)).y.toNat < cornerY sy N.h + 16
          · -- frame `runF` does not end above `cornerY + 16` (round 28): it is a frame of the jump from the floor (the floor ends lower), whose takeoff frame reads
            -- the stored speed; right after the fall it is below the air threshold (the fall's frames are air frames, `capped_along`; `ab_of`), and the jump's frames
            -- end at `cornerY + 16` or below up to frame `runF` (`riseCheck` along `varc`)
            exfalso
            have hTR : T' < r.C + N.runF := by
              by_cases h5 : r.C + N.runF ≤ T'
              · have := (hfl (r.C + N.runF) (by omega) h5).2
                have := hF.floor16
                omega
              · omega
            have hfT := hfl T' g1 (Nat.le_refl _)
            have hj : (r.fr.inp (T' + 1)).jump = true := by
              rcases r.vfloor hw T' g1 (by omega) (by omega) hfl with ⟨_, h5, _⟩ | ⟨_, _, _, _, hi⟩ | ⟨h5, _, _⟩ | ⟨h5, _⟩ | ⟨h5, _⟩
              · exact absurd h5.1 (arc_facts H (harc (T' + 1) (by omega) (by omega)) (by omega)).2.2
              · exact hi.2.2
              · exact absurd hfT.1 h5
              · exact absurd hfT.1 h5
              · exact absurd hfT h5
            obtain ⟨hoff, hab256⟩ := r.off_ab T' (by omega) (by omega) (by omega) hj
            have hyT : (r.fr.vs T').y = (groundY sy).toUInt8 := by
              rw [← hfT.2]
              exact (UInt8.ofNat_toNat).symm
            rw [hyT] at hoff
            have hab : T' = r.C + N.fall → r.fr.ab T' < sy.AirFastSpeed.toNat := by
              intro hT0
              have hcap : capped sy (r.fr.hs (r.C + N.fall)) = true :=
                capped_along r H (u := r.C) (w := r.C + N.fall) (Nat.le_refl _) (by omega) (start_fall r H).cap
                  (fun j h5 h6 => Or.inl (by
                    have := fall_air r H (n := j) h5 h6 (fun k a b => hw k a (by omega))
                    simp [isAir, this.2.1]))
                  N.fall (Nat.le_refl _)
              simp only [capped, decide_eq_true_eq] at hcap
              rcases r.ab_of T' (by omega) (by omega) with h5 | ⟨_, h5⟩
              · rw [h5, hT0]
                exact hcap
              · exact h5 (by have := hF.fall2; omega)
            have hrc := hF.rise
            simp only [riseCheck, List.all_eq_true] at hrc
            have h0' := hrc (r.fr.ab T') (List.mem_range.2 hab256)
            have h0 : riseFrom sy m N (r.fr.vs (T' + 1)) (if sy.AirFastSpeed.toNat ≤ r.fr.ab T' then N.runF - N.fall - 2 else N.runF - N.fall - 1) = true := by
              rw [hoff]
              exact h0'
            generalize hDe : (if sy.AirFastSpeed.toNat ≤ r.fr.ab T' then N.runF - N.fall - 2 else N.runF - N.fall - 1) = D at h0
            have hD : r.C + N.runF - (T' + 1) ≤ D := by
              split at hDe
              · rename_i h5
                have h6 : T' ≠ r.C + N.fall := fun h7 => by have := hab h7; omega
                omega
              · omega
            have hstep : ∀ k, k ≤ r.C + N.runF - (T' + 1) → riseFrom sy m N (r.fr.vs (T' + 1 + k)) (D - k) = true := by
              intro k
              induction k with
              | zero => intro _; simpa using h0
              | succ k ih =>
                intro hk
                have h5 := ih (by omega)
                have hv := r.varc T' (T' + 1 + k) (by omega) (by omega) (by omega) (harc (T' + 1 + k) (by omega) (by omega)) (by omega)
                rw [show T' + 1 + (k + 1) = T' + 1 + k + 1 by omega, hv]
                rw [show D - k = (D - (k + 1)) + 1 by omega] at h5
                exact riseFrom_next h5 _
            have h6 := riseFrom_y (hstep (r.C + N.runF - (T' + 1)) (Nat.le_refl _))
            rw [show T' + 1 + (r.C + N.runF - (T' + 1)) = r.C + N.runF by omega] at h6
            omega
          · -- frame `runF` ends at `cornerY + 16` or below: from there frame by frame (round 28). A frame that ends at `cornerY + 16` or below is a frame of the
            -- jump from the floor (the floor and the takeoff frame end lower), it is `LowS` with the least slack `lowT` (`low_jump`), at or past the corner, so
            -- stopped or moving left, and the next frame moves at most one pixel right (`push_one`): `lowT + 256 = 16·top − 1`. After a frame that ends above,
            -- one frame at the top speed (`move_top`)
            · have hind : ∀ d, r.C + N.runF + d ≤ n → (r.fr.vs (r.C + N.runF + d)).y.toNat < cornerY sy N.h + 16 →
                  r.fr.P (r.C + N.runF + d) ≤ cornerP sy - 1 + 16 * (top sy : Int) * (d : Int) := by
                intro d
                induction d with
                | zero => intro _ h; exact absurd h hyR
                | succ d ih =>
                  intro hd hyd
                  have e1 : r.C + N.runF + (d + 1) = r.C + N.runF + d + 1 := by omega
                  have e2 : 16 * (top sy : Int) * ((d + 1 : Nat) : Int) = 16 * (top sy : Int) * (d : Int) + 16 * (top sy : Int) := by
                    rw [show ((d + 1 : Nat) : Int) = (d : Int) + 1 by omega, Int.mul_add, Int.mul_one]
                  rw [e1] at hd hyd ⊢
                  rw [e2]
                  have hd0 : (0 : Int) ≤ 16 * (top sy : Int) * (d : Int) := Int.mul_nonneg ht16 (by omega)
                  have hmt := r.move_top (r.C + N.runF + d) (by omega) (by omega)
                  by_cases hyj : (r.fr.vs (r.C + N.runF + d)).y.toNat < cornerY sy N.h + 16
                  · have := ih (by omega) hyj
                    omega
                  · -- frame `runF + d` is a frame of the jump
                    have hTj : T' < r.C + N.runF + d := by
                      by_cases h5 : r.C + N.runF + d + 1 ≤ T'
                      · have := (hfl (r.C + N.runF + d + 1) (by omega) h5).2
                        have := hF.floor16
                        omega
                      · by_cases h6 : r.C + N.runF + d = T'
                        · have := takeoff16 hF (harc (T' + 1) (by omega) (by omega))
                          rw [← h6] at this
                          omega
                        · omega
                    have hylo : ∀ k, T' < k → k ≤ r.C + N.runF + d → cornerY sy N.h + 16 ≤ (r.fr.vs k).y.toNat := by
                      intro k hk1 hk2
                      have := arc_down r H (T := T') (n := r.C + N.runF + d) (by omega) (by omega) (by omega) (by omega)
                        (fun k' a b => harc k' a (by omega)) (r.C + N.runF + d - k) (by omega)
                      rw [show r.C + N.runF + d - (r.C + N.runF + d - k) = k by omega] at this
                      omega
                    have hTl : LowS sy m N r.fr (lowT sy) T' := by
                      by_cases hTe : T' < r.C + N.hitF
                      · have := corner_late r H (n := T') (by omega) hTe (by omega)
                        exact ⟨by have := hT1.1; omega, Or.inr (Or.inl this)⟩
                      · exact low_floor_atS r H hw hT1 (n := T') (by omega) (by omega) (by omega) hfl
                    have hL := r.low_jump hw T' (r.C + N.runF + d) g1 (by omega) (by omega) (by omega) hfl (fun k a b => harc k a (by omega)) hylo (lowT sy) hT1 hTl
                    have hPc := hall (r.C + N.runF + d) (by omega) (by omega)
                    have hsv : Stop sy m N r.fr (r.C + N.runF + d) ∨ sbyte (r.fr.hs (r.C + N.runF + d)).v < 0 := by
                      rcases hL.2 with h | h | h
                      · exact Or.inl h
                      · omega
                      · exact Or.inr h
                    have hst := (arc_facts H (harc (r.C + N.runF + d) (by omega) (by omega)) (by omega)).2.2
                    have hp1 := r.push_one (r.C + N.runF + d) (by omega) (by omega) (by omega) hst hsv
                    have hl1 := hL.1
                    unfold lowT at hl1
                    omega
              have h7 := hind (n - (r.C + N.runF)) (by omega) (by rw [show r.C + N.runF + (n - (r.C + N.runF)) = n by omega]; exact hy)
              rwa [show r.C + N.runF + (n - (r.C + N.runF)) = n by omega] at h7
        · -- the frame ends at `cornerY + 16` or below, and so does every frame of the jump before it (`arc_down`): `low_jump` from the takeoff
          rcases v_chain2 r H hw (n - (r.C + N.fall)) (by omega) (by omega) (by omega) with hf | ⟨T, g1, g2, hfl, harc⟩
          · have := hf (n - (r.C + N.fall)) (Nat.le_refl _)
            rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at this
            exact absurd this.1 hfa.2.2
          · rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at g2 harc
            have hylo : ∀ j, T < j → j ≤ n → cornerY sy N.h + 16 ≤ (r.fr.vs j).y.toNat := by
              intro j hj1 hj2
              have := arc_down r H (T := T) (n := n) (by omega) h3 (by omega) (by omega) harc (n - j) (by omega)
              rw [show n - (n - j) = j by omega] at this
              omega
            have hT : LowAt sy m N r.fr T := by
              by_cases hTe : T < r.C + N.hitF
              · have := corner_late r H (n := T) (by omega) hTe (by omega)
                exact ⟨by omega, Or.inr (Or.inl this)⟩
              · exact low_floor_at r H hw (n := T) (by omega) (by omega) (by omega) hfl
            have hlj := (r.low_jump hw T n g1 (by omega) h2 h3 hfl harc hylo N.lowSlack (slack_ok H) hT).1
            omega
  · have hg := hN.hit_run
    have hmin : min n (r.C + N.runF + 1) ≤ r.t0 := by omega
    obtain ⟨a, ha⟩ := anchor_of_wall r H hw (w := min n (r.C + N.runF + 1)) (by omega) (by omega) hmin
    have h4 := anchor_P r H ha
    have hge := ha.ge
    have hle := ha.le
    obtain ⟨k, hk⟩ : ∃ k, N.runF + 1 - N.wallF = (min n (r.C + N.runF + 1) - (r.C + N.wallF)) + k :=
      ⟨N.runF + 1 - N.wallF - (min n (r.C + N.runF + 1) - (r.C + N.wallF)), by omega⟩
    have h5 := dbound_mono H.air.pot (min n (r.C + N.runF + 1) - (r.C + N.wallF)) k N.stopPhi hN.stop_nonneg
    rw [← hk] at h5
    have h6 := hN.wall_low
    have h7 := reach_le (P := r.fr.P) (u := min n (r.C + N.runF + 1)) (B := r.fr.P (min n (r.C + N.runF + 1))) (μ := 16 * (top sy : Int))
      (w := r.t0) (Int.le_refl _) ht16 (fun j h8 h9 => Or.inl (r.move_top j (by omega) h9)) (n - min n (r.C + N.runF + 1)) (by omega)
    rw [show min n (r.C + N.runF + 1) + (n - min n (r.C + N.runF + 1)) = n by omega] at h7
    have h8 : 16 * (top sy : Int) * ((n - min n (r.C + N.runF + 1) : Nat) : Int) ≤
        16 * (top sy : Int) * ((N.fall + 1 + N.rise - (N.runF + 1) : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) ht16
    omega

/-! ### `RunningSpeed` by `runF` -/

theorem rs_step (F : Facts sy m) {s : HS} (hD : inD sy s = true) (hrs : s.rs = 0) (hv : (sbyte s.v).natAbs < sy.RunSpeedMin.toNat)
    {i : HIn} (hi : i ∈ inputs) : (hstep sy m s i).rs = 0 := by
  have h4 := F.check s hD i hi
  simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq] at h4
  rcases h4.2 with (h5 | h5) | h5
  · exact h5
  · exact absurd hrs h5
  · omega

/-- from a state that passes `safeFrom` at the end of the fall, `RunningSpeed` stays 0 through `runF` -/
theorem rs_of_safe (H : Checks sy m N) (h0 : (r.fr.hs (r.C + N.fall)).rs = 0)
    (hs : safeFrom sy m (N.runF - N.fall - 1) (r.fr.hs (r.C + N.fall)) = true) :
    ∀ d, d ≤ N.runF - N.fall - 1 → r.C + N.fall + d ≤ r.t0 →
      (r.fr.hs (r.C + N.fall + d)).rs = 0 ∧ safeFrom sy m (N.runF - N.fall - 1 - d) (r.fr.hs (r.C + N.fall + d)) = true
  | 0, _, _ => ⟨h0, hs⟩
  | d + 1, h1, h2 => by
    obtain ⟨h3, h4⟩ := rs_of_safe H h0 hs d (by omega) (by omega)
    have hN := H.nums
    have hge := hN.run_ge
    rw [show r.C + N.fall + (d + 1) = r.C + N.fall + d + 1 by omega]
    rw [show N.runF - N.fall - 1 - d = (N.runF - N.fall - 1 - (d + 1)) + 1 by omega] at h4
    by_cases hf : Follow sy m r.fr (r.C + N.fall + d)
    · rw [hf.2.1]
      have hD := inD_at r H (n := r.C + N.fall + d) (by omega) (by omega)
      have h5 := safe_step H.air.pot hN.gs_le H.normI hD h3 h4 hf.1
      exact ⟨h5.2, h5.1⟩
    · have hs2 := (r.frames (r.C + N.fall + d) (by omega) (by omega)).resolve_left hf
      have hv : (sbyte (r.fr.hs (r.C + N.fall + d)).v).natAbs < sy.RunSpeedMin.toNat := by
        have h5 := h4
        simp only [safeFrom, Bool.and_eq_true, decide_eq_true_eq] at h5
        exact h5.1
      refine ⟨r.stop_run _ (by omega) (by omega) h3 hv hf, ?_⟩
      refine safe_of_bound H.air.pot hN.gs_le _ hs2.2.1 ?_
      obtain ⟨k, hk⟩ : ∃ k, N.runF - N.fall - 1 = (N.runF - N.fall - 1 - (d + 1)) + k := ⟨d + 1, by omega⟩
      have h5 := iterN_count H.air.pot (N.runF - N.fall - 1 - (d + 1)) k N.stopPhi
      rw [← hk] at h5
      have h6 := hN.stop_safe
      omega

/-- **`RunningSpeed` not 0 at a stop by `runF`, with no wall**: he moved left fast at the end of the fall, so he is far back. Moving right, or
slower, `safeFrom` shows `RunningSpeed` is 0 -/
theorem no_wall_back (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) {h' : Nat} (hc : r.C + N.hitF ≤ h') (hr : h' ≤ r.C + N.runF)
    (ht : h' ≤ r.t0) (hrs : (r.fr.hs h').rs ≠ 0) : r.fr.P h' ≤ N.backP := by
  have hN := H.nums
  have hg := hN.hit_ge
  have hge := hN.run_ge
  have F := H.air.pot
  have hair : ∀ i, r.C ≤ i → i < r.C + N.fall → AirIn (r.fr.inp (i + 1)) := fun i h1 h2 =>
    fall_air r H h1 h2 (fun j h3 h4 => hw j h3 (by omega))
  have hp : psiP sy m (r.fr.hs r.C) ≤ phi sy m (room sy N).s0 := psiP_start r
  have hrun : ∀ i, r.C ≤ i → i < r.C + N.fall → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h1 h2 =>
    ⟨hw i h1 (by omega), hair i h1 h2⟩
  obtain ⟨hst, hpsi, hP⟩ := fall_run r H (start_fall r H) hp N.fall (fun i h1 h2 => hrun i h1 h2)
  -- `safeFrom` at the end of the fall gives `RunningSpeed` 0 at `h'`
  have hno : safeFrom sy m (N.runF - N.fall - 1) (r.fr.hs (r.C + N.fall)) = true → False := fun hs => by
    by_cases hlast : h' ≤ r.C + N.fall + (N.runF - N.fall - 1)
    · obtain ⟨h1, _⟩ := rs_of_safe r H hst.rs hs (h' - (r.C + N.fall)) (by omega) (by omega)
      rw [show r.C + N.fall + (h' - (r.C + N.fall)) = h' by omega] at h1
      exact hrs h1
    · have hh : h' = r.C + N.fall + (N.runF - N.fall - 1) + 1 := by omega
      obtain ⟨h1, h2⟩ := rs_of_safe r H hst.rs hs (N.runF - N.fall - 1) (Nat.le_refl _) (by omega)
      rw [show N.runF - N.fall - 1 - (N.runF - N.fall - 1) = 0 by omega] at h2
      simp only [safeFrom, decide_eq_true_eq] at h2
      apply hrs
      rw [hh]
      by_cases hf : Follow sy m r.fr (r.C + N.fall + (N.runF - N.fall - 1))
      · rw [hf.2.1]
        exact rs_step F (inD_at r H (by omega) (by omega)) h1 h2 hf.1
      · exact r.stop_run _ (by omega) (by omega) h1 h2 hf
  by_cases hV : 0 ≤ V (r.fr.hs (r.C + N.fall))
  · exfalso
    apply hno
    -- moving right: the check
    have hphi := psiP_eq_phi (sy := sy) (m := m) hV
    obtain ⟨hD, hcap, hfd, hrs0⟩ := hst
    generalize r.fr.hs (r.C + N.fall) = s at *
    obtain ⟨v, f, fd, md, rs⟩ := s
    simp only at hfd hrs0
    subst hfd
    subst hrs0
    have hD' := hD
    simp only [inD, Bool.and_eq_true, List.contains_iff_mem] at hD'
    obtain ⟨⟨⟨hv, _⟩, hmd⟩, _⟩ := hD'
    have hvs : v ∈ speedsB sy := by
      have hsp := H.air.speeds
      simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.contains_iff_mem] at hsp
      rcases hsp v (mem_bytes v) with h | h
      · rw [h] at hv; exact absurd hv (by decide)
      · exact h
    have hcv : (sbyte v).natAbs < sy.AirFastSpeed.toNat := by
      simpa only [capped, decide_eq_true_eq] using hcap
    have hfr : f.toNat < 256 := f.toNat_lt
    have hv0 : 0 ≤ sbyte v := by
      unfold V at hV
      simp only at hV
      omega
    have hmem : ({ v, f, fd := 1, md, rs := 0 } : HS) ∈ safeStates sy :=
      List.mem_flatMap.2 ⟨v, List.mem_filter.2 ⟨hvs, by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hv0, hcv⟩⟩,
        List.mem_flatMap.2 ⟨f, mem_bytes f, List.mem_map.2 ⟨md, hmd, rfl⟩⟩⟩
    have hall := H.safe
    simp only [safeCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hall
    rcases hall _ hmem with h1 | h1
    · exact absurd (by rw [hphi]; exact hpsi) h1
    · exact h1
  · by_cases hq : phi sy m (r.fr.hs (r.C + N.fall)) ≤ N.safeP
    · exfalso
      exact hno (safe_of_bound F hN.gs_le _ hq hN.safe_bound)
    · -- moving left fast: he is far back
      have hle := hN.back_le
      have hb : r.C + N.fall - N.backK + N.backK = r.C + N.fall := by omega
      have hu : N.safeP + 1 - 2 * c sy m ≤ -V (r.fr.hs (r.C + N.fall)) := by
        have h1 := AirCap.w_le F (r.fr.hs (r.C + N.fall))
        unfold phi at hq
        omega
      rw [← hb] at hu
      have hst2 : ∀ i, r.C + N.fall - N.backK ≤ i → i < r.C + N.fall - N.backK + N.backK →
          FallSt sy (r.fr.hs i) ∧ Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h1 h2 => by
        have h3 := fall_states r H hw hair (i - r.C) (by omega) (by omega)
        rw [show r.C + (i - r.C) = i by omega] at h3
        exact ⟨h3, hrun i (by omega) (by omega)⟩
      have h1 := back_run r H N.backK _ hst2 hu
      rw [hb] at h1
      obtain ⟨_, _, h2⟩ := fall_run r H (start_fall r H) hp (N.fall - N.backK) (fun i h3 h4 => hrun i h3 (by omega))
      rw [show r.C + (N.fall - N.backK) = r.C + N.fall - N.backK by omega] at h2
      have htop : (0 : Int) ≤ 16 * (top sy : Int) := by omega
      have h3 := reach_le (P := r.fr.P) (u := r.C + N.fall) (B := r.fr.P (r.C + N.fall)) (μ := 16 * (top sy : Int)) (w := r.t0)
        (Int.le_refl _) htop (fun j h4 h5 => Or.inl (r.move_top j (by omega) h5)) (h' - (r.C + N.fall)) (by omega)
      rw [show r.C + N.fall + (h' - (r.C + N.fall)) = h' by omega] at h3
      have h4 : 16 * (top sy : Int) * ((h' - (r.C + N.fall) : Nat) : Int) ≤ 16 * (top sy : Int) * ((N.runF - N.fall : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by omega) htop
      have h5 := hN.back_ok
      have h6 := r.startP1
      omega

/-- a stop by `runF` with `RunningSpeed` not 0 is short of the goal -/
theorem run_short (H : Checks sy m N) {h' : Nat} (hs : Stop sy m N r.fr h') (hc : r.C + N.hitF ≤ h') (hr : h' ≤ r.C + N.runF)
    (h4 : h' ≤ r.t0) (hrs : (r.fr.hs h').rs ≠ 0) (ht : r.t0 ≤ r.C + N.goalF)
    (hin : ∀ i ∈ seg r.fr.inp h' (r.t0 - h'), i ∈ inputs)
    (h7 : r.fr.P r.t0 = r.fr.P h' + hdist sy m (r.fr.hs h') (seg r.fr.inp h' (r.t0 - h'))) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have h8 := fast_dist_le F _ _ _ hs.1 hs.2.1 hin
  rw [length_seg] at h8
  by_cases hw : NoWall sy m N r.fr r.C
  · have h1 := no_wall_back r H hw hc hr h4 hrs
    obtain ⟨k, hk⟩ : ∃ k, N.goalF - N.hitF = (r.t0 - h') + k := ⟨N.goalF - N.hitF - (r.t0 - h'), by omega⟩
    have h9 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hN.stop_nonneg
    rw [← hk] at h9
    have h10 := hN.hit_B
    omega
  · obtain ⟨a, ha⟩ := anchor_of_wall r H hw (w := h') (by omega) (by omega) h4
    have h1 := anchor_P r H ha
    have h9 := hN.wall_stops
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h9
    rcases h9 (h' - r.C) (List.mem_range.2 (by have := hN.goal_ge; omega)) with (h10 | h10) | h10
    · omega
    · omega
    · rw [show h' - r.C - N.wallF = h' - (r.C + N.wallF) by omega] at h10
      obtain ⟨k, hk⟩ : ∃ k, N.goalF - (h' - r.C) = (r.t0 - h') + k := ⟨N.goalF - (h' - r.C) - (r.t0 - h'), by omega⟩
      have h11 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hN.stop_nonneg
      rw [← hk] at h11
      omega

/-- **A stop from `hitF` on is short of the goal**, whatever he does after it: the speed is near 0, and the potential bounds the
rest. This covers a hit at the corner on the floor or in the air, a jump with a stale stored speed after it, and a jump from the
side of the block. -/
theorem stop_short (H : Checks sy m N) (hE : r.t0 < r.E) {h : Nat} (h1 : r.C + N.hitF ≤ h) (h2 : h ≤ r.t0) (hs : Stop sy m N r.fr h)
    (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  obtain ⟨h', h3, h4, h5, h7, hin⟩ := after_stop r (a := r.C + N.hitF) (by omega) (by omega) ⟨h, h1, h2, hs⟩
  have F := H.air.pot
  have hn := H.nums
  have hrl := hn.run_le
  have hl0 := hn.low_nonneg
  by_cases hrun : h' ≤ r.C + N.runF
  · by_cases hz : (r.fr.hs h').rs = 0
    · have hJ : J sy m (r.fr.hs h') N.stopPhi := ⟨h5.1, h5.2.1, fun hne => absurd hz hne⟩
      have h8 := dist_le F _ _ _ hJ hin
      rw [length_seg] at h8
      obtain ⟨k, hk⟩ : ∃ k, N.goalF - (h' - r.C) = (r.t0 - h') + k := ⟨N.goalF - (h' - r.C) - (r.t0 - h'), by omega⟩
      have h9 := dbound_mono F (r.t0 - h') k N.stopPhi hn.stop_nonneg
      rw [← hk] at h9
      have h10 := hn.hit_J
      simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h10
      have h11 := low_by r H hE (n := h') (by omega) (by omega) h4
      rcases h10 (h' - r.C) (List.mem_range.2 (by omega)) with h10 | h10
      · omega
      · omega
    · exact run_short r H h5 h3 hrun h4 hz ht hin h7
  · have h8 := fast_dist_le F _ _ _ h5.1 h5.2.1 hin
    rw [length_seg] at h8
    by_cases hlow : h' ≤ r.C + N.fall + 1 + N.rise
    · obtain ⟨k, hk⟩ : ∃ k, N.goalF - (h' - r.C) = (r.t0 - h') + k := ⟨N.goalF - (h' - r.C) - (r.t0 - h'), by omega⟩
      have h9 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hn.stop_nonneg
      rw [← hk] at h9
      have h10 := hn.hit_F
      simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h10
      have h11 := low_by r H hE (n := h') (by omega) hlow h4
      rcases h10 (h' - r.C) (List.mem_range.2 (by omega)) with h10 | h10
      · omega
      · omega
    · -- later: at most the top speed after the low frames, and not far past the corner
      let j := h' - r.C
      have h9 := hn.hit_late
      simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h9
      rcases h9 j (List.mem_range.2 (by omega)) with h10 | h10
      · omega
      · obtain ⟨k, hk⟩ : ∃ k, N.goalF - j = (r.t0 - h') + k := ⟨N.goalF - j - (r.t0 - h'), by omega⟩
        have h11 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hn.stop_nonneg
        rw [← hk] at h11
        have h12 := h5.2.2
        let u0 := r.C + N.fall + 1 + N.rise
        have h12' := low_by r H hE (n := u0) (by omega) (by omega) (by omega)
        rw [show u0 - r.C = N.fall + 1 + N.rise by omega] at h12'
        have h13 := reach_le (P := r.fr.P) (u := u0) (B := lowB sy N (N.fall + 1 + N.rise)) (μ := 16 * (top sy : Int)) (w := r.t0)
          h12' (by omega)
          (fun n h14 h15 => Or.inl (r.move_top n (by omega) h15)) (h' - u0) (by omega)
        rw [show u0 + (h' - u0) = h' by omega] at h13
        have h14 : ((j - (N.fall + 1 + N.rise) : Nat) : Int) = ((h' - u0 : Nat) : Int) := by
          congr 1
          omega
        rw [h14] at h10
        omega

/-- no stop from `hitF` on: on the low frames he is left of the corner -/
theorem left_of_corner (H : Checks sy m N) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) {w : Nat}
    (hw : w ≤ r.t0) (hlow : ∀ n, r.C + N.hitF ≤ n → n ≤ w → LowAt sy m N r.fr n) :
    ∀ d, r.C + N.hitF + d ≤ w + 1 → d = 0 ∨ r.fr.P (r.C + N.hitF + d - 1) < cornerP sy
  | 0, _ => Or.inl rfl
  | d + 1, h => by
    right
    rw [show r.C + N.hitF + (d + 1) - 1 = r.C + N.hitF + d by omega]
    have hprev : r.fr.P (r.C + N.hitF + d - 1) < cornerP sy := by
      rcases left_of_corner H hs hw hlow d (by omega) with h0 | h0
      · subst h0
        have hF := H.nums.hit_ge
        exact corner_late r H (by omega) (by omega) (by omega)
      · exact h0
    obtain ⟨_, h1⟩ := hlow (r.C + N.hitF + d) (by omega) (by omega)
    rcases h1 with h1 | h1 | h1
    · exact absurd h1 (hs _ (by omega) (by omega))
    · exact h1
    · have hF := H.nums.hit_ge
      have h2 : Follow sy m r.fr (r.C + N.hitF + d - 1) :=
        follow_of r hs (by omega) (by omega) (by omega)
      have h3 := h2.2.2
      rw [show r.C + N.hitF + d - 1 + 1 = r.C + N.hitF + d by omega] at h3
      omega

theorem left_at (H : Checks sy m N) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) {w : Nat}
    (hw : w ≤ r.t0) (hlow : ∀ n, r.C + N.hitF ≤ n → n ≤ w → LowAt sy m N r.fr n) {n : Nat} (hC : r.C ≤ n) (hn : n ≤ w) :
    r.fr.P n < cornerP sy := by
  by_cases h1 : n < r.C + N.hitF
  · exact corner_late r H hC h1 (by omega)
  · rcases left_of_corner r H hs hw hlow (n + 1 - (r.C + N.hitF)) (by omega) with h2 | h2
    · omega
    · rwa [show r.C + N.hitF + (n + 1 - (r.C + N.hitF)) - 1 = n by omega] at h2

/-! ### Over the block in one jump -/

/-- **No landing on the block**: he does not pass over the whole block in one jump, from the floor or from its side -/
theorem no_landing (H : Checks sy m N) (o : Over sy m N r.fr r.C r.t0) : False := by
  have hn := H.nums
  have hy := H.lenY
  simp only [List.all_eq_true] at hy
  have hlenA := arc_len (hy o.y0 o.y0_mem) o.x_mem o.reach hn.len_ok.2.2.2 hn.len_ok.2.2.2
  simp only [ite_self] at hlenA
  have hT1 := o.T1_ge
  have hT2 := o.T1_lt
  have hpast := r.past
  have hA := hn.air_pos
  have hl0 := hn.low_nonneg
  have F := H.air.pot
  cases hcap : capped sy (r.fr.hs o.T1) with
  | true =>
    -- below the threshold: the air speed all the way
    have hc := capped_along r H (u := o.T1) (w := r.t0) hT1 (by omega) hcap o.air
    have h1 := reach_le (P := r.fr.P) (u := o.T1) (B := cornerP sy + N.stopSlack)
      (μ := 16 * ((sy.AirFastSpeed.toNat : Int) - 1)) (w := r.t0) o.start (by omega) (fun n h3 h4 => by
        rcases r.frames n (by omega) h4 with h5 | h5
        · left
          have h6 := hc (n + 1 - o.T1) (by omega)
          rw [show o.T1 + (n + 1 - o.T1) = n + 1 by omega] at h6
          simp only [capped, decide_eq_true_eq] at h6
          have h7 := h5.2.2
          omega
        · right
          exact h5.2.2) (r.t0 - o.T1) (by omega)
    rw [show o.T1 + (r.t0 - o.T1) = r.t0 by omega] at h1
    have h2 := hn.over_capped
    have h3 : r.t0 - o.T1 ≤ N.lenA + 1 := by omega
    have h4 : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((r.t0 - o.T1 : Nat) : Int) ≤
        16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((N.lenA + 1 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  | false =>
    -- at the threshold or more: it is a fast jump from the floor
    have hf : o.x.fast = true := by
      cases hf : o.x.fast with
      | true => rfl
      | false =>
        have := o.slowC hf
        rw [hcap] at this
        exact absurd this (by decide)
    obtain ⟨hg, hlowf⟩ := o.low hcap
    have hxm := o.x_mem
    rw [hg] at hxm
    have hlen := arc_len H.lenG hxm o.reach hn.len_ok.1 hn.len_ok.2.1
    rw [hf] at hlen
    simp only [if_true] at hlen
    let u0 := min (o.T1 + 1 + N.rise) r.t0
    have hu0 := hlowf u0 (by omega) (by omega) (by omega)
    by_cases hstop : ∃ h, u0 ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h
    · obtain ⟨h', h3, h4, h5, h7, hin⟩ := after_stop r (a := u0) (by omega) (by omega) hstop
      have h8 := fast_dist_le F _ _ _ h5.1 h5.2.1 hin
      rw [length_seg] at h8
      obtain ⟨k, hk⟩ : ∃ k, N.lenF - N.rise = (r.t0 - h') + k := ⟨N.lenF - N.rise - (r.t0 - h'), by omega⟩
      have h9 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hn.stop_nonneg
      rw [← hk] at h9
      have h10 := hn.over_stop
      have h11 := h5.2.2
      omega
    · have h1 := reach_le (P := r.fr.P) (u := u0) (B := cornerP sy + N.lowSlack) (μ := 16 * (top sy : Int)) (w := r.t0)
        hu0 (by omega) (fun n h3 h4 => Or.inl (r.move_top n (by omega) h4)) (r.t0 - u0) (by omega)
      rw [show u0 + (r.t0 - u0) = r.t0 by omega] at h1
      have h2 := hn.over_top
      have h3 : 16 * (top sy : Int) * ((r.t0 - u0 : Nat) : Int) ≤ 16 * (top sy : Int) * ((N.lenF - N.rise : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega

/-! ### Landing on the block -/

/-- the pair of the jump table for this landing -/
theorem window_pair (H : Checks sy m N) {x u : Arc} {n : Nat} (hx : x ∈ arcStart sy m (groundY sy) N.h)
    (hreach : Cert.Reach (arcSucc sy m N.h) x n u)
    (hw : falling u.s = true ∧ standY sy N.h ≤ u.s.y.toNat ∧ u.s.y.toNat < standY sy N.h + sy.LandDepth.toNat) :
    u.k = n ∧ ∃ q ∈ (if x.fast then N.fast else N.slow), q.1 ≤ u.low ∧ q.2 ≤ u.k := by
  have hn := H.nums
  have hlen := arc_len H.lenG hx hreach hn.len_ok.1 hn.len_ok.2.1
  have hle : n ≤ arcFrames := by
    have h1 := hn.len_ok.1
    have h2 := hn.len_ok.2.1
    split at hlen <;> omega
  have h1 := arc_spec H.window x hx n u hle hreach
  obtain ⟨h2, h3⟩ := arc_k hreach
  have h4 := arcStart_k hx
  refine ⟨by omega, ?_⟩
  have hw' : (falling u.s && decide (standY sy N.h ≤ u.s.y.toNat) &&
      decide (u.s.y.toNat < standY sy N.h + sy.LandDepth.toNat)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  unfold windowOk at h1
  rw [hw', h3] at h1
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1

/-- the slow bound, moved to the earliest frames of the pair: landing later never raises it -/
theorem pair_bound (hA : 1 ≤ sy.AirFastSpeed.toNat) {q1 q2 S0 L0 s L t G : Nat} (h1 : S0 + q2 = L0 + q1) (hq : q1 ≤ q2)
    (hs : S0 ≤ s) (hL : L0 ≤ L) (hsL : s ≤ L) (hLt : L ≤ t) (htG : t ≤ G) :
    16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((L - s : Nat) : Int) + capDist sy m (t - L) ≤
      16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((q2 - q1 : Nat) : Int) + capDist sy m (G - L0) := by
  have h0 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) := by omega
  have h2 := landing_later (sy := sy) (m := m) ((q2 - q1 : Nat) : Int) (t - L) (L - L0)
  have h3 : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((L - s : Nat) : Int) ≤
      16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (((q2 - q1 : Nat) : Int) + ((L - L0 : Nat) : Int)) :=
    Int.mul_le_mul_of_nonneg_left (by omega) h0
  have h4 := cap_mono (m := m) hA (t - L + (L - L0)) (G - t)
  rw [show t - L + (L - L0) + (G - t) = G - L0 by omega] at h4
  omega

/-! ### The floor up to the takeoff -/

/-- **The landing on the block comes after the low frames of the jump**: on them he is rising (`arc_facts`), and a landing needs a fall -/
theorem land_late (H : Checks sy m N) (a : Approach sy m N r.fr r.C r.t0 sz) : a.T1 + 1 + N.rise < a.L := by
  by_cases h : a.T1 + 1 + N.rise < a.L
  · exact h
  · exfalso
    have hL := a.L_gt
    obtain ⟨_, h3, _⟩ := arc_facts H (fr := { r.fr with vs := fun j => if j = a.L then a.u.s else r.fr.vs j }) (T := a.T1) (n := a.L)
      ⟨by omega, a.x, a.u, a.x_mem, a.reach, by simp⟩ (by omega)
    simp only [if_true] at h3
    rw [a.window.1] at h3
    cases h3

/-- **`floor_low`**, with no wall: up to a takeoff by the last frame searched he has stayed on the floor. An earlier jump would still be in its
low frames -/
theorem floor_all (H : Checks sy m N) (hE : r.t0 ≤ r.E) (hw : NoWall sy m N r.fr r.C) (a : Approach sy m N r.fr r.C r.t0 sz)
    (hearly : a.T1 ≤ r.C + N.fall + N.lastG) {n : Nat} (h1 : r.C + N.fall ≤ n) (h2 : n ≤ a.T1) : OnFloor sy (r.fr.vs n) := by
  have hN := H.nums
  have hl := hN.last_le
  have hT := a.T1_lt
  rcases v_chain r H hw (n - (r.C + N.fall)) (by omega) (by omega) (by omega) with hf | ⟨T, h3, h4, ha⟩
  · have hf := hf _ (Nat.le_refl _)
    rwa [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at hf
  · exfalso
    rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at h4 ha
    have hgo : ∀ e, n + e ≤ a.T1 → OnArc sy m N r.fr T (n + e) := by
      intro e
      induction e with
      | zero => exact fun _ => ha
      | succ e ih =>
        intro h5
        have h6 := ih (by omega)
        rw [show n + (e + 1) = n + e + 1 by omega]
        exact arc_step H h6 (by omega) (r.varc T (n + e) (by omega) (by omega) (by omega) h6 (by omega))
    have h7 := hgo (a.T1 - n) (by omega)
    rw [show n + (a.T1 - n) = a.T1 by omega] at h7
    exact (arc_facts H h7 (by omega)).2.2 a.T1_floor.1

/-- the frames of the jump's low frames -/
theorem arc_from (H : Checks sy m N) (hE : r.t0 ≤ r.E) (hw : NoWall sy m N r.fr r.C) (a : Approach sy m N r.fr r.C r.t0 sz)
    (hearly : a.T1 ≤ r.C + N.fall + N.lastG) : ∀ e, e ≤ N.rise → OnArc sy m N r.fr a.T1 (a.T1 + 1 + e)
  | 0, _ => by
    refine ⟨by omega, a.x, a.x, a.x_mem, ?_, a.x_vs⟩
    rw [show a.T1 + 1 + 0 - (a.T1 + 1) = 0 by omega]
    exact .refl _
  | e + 1, h1 => by
    have h2 := arc_from H hE hw a hearly e (by omega)
    have hT := a.T1_ge
    have hL := land_late r H a
    have hL2 := a.L_le
    rw [show a.T1 + 1 + (e + 1) = a.T1 + 1 + e + 1 by omega]
    exact arc_step H h2 (by omega) (r.varc a.T1 _ (by omega) (by omega) (by omega) h2 (by omega))

/-- **`floor_low`**: the frames from `hitF` to a takeoff by the last frame searched are low -/
theorem floor_low (H : Checks sy m N) (hE : r.t0 ≤ r.E) (hw : NoWall sy m N r.fr r.C) (a : Approach sy m N r.fr r.C r.t0 sz) (hearly : a.T1 ≤ r.C + N.fall + N.lastG)
    {n : Nat} (h1 : r.C + N.hitF ≤ n) (h2 : n ≤ a.T1) : LowAt sy m N r.fr n := by
  have hN := H.nums
  have hT := a.T1_lt
  have hl := hN.last_le
  have hg := hN.hit_ge
  exact low_floor_at r H hw (n := n) (by omega) (by omega) (by omega) (fun j hj1 hj2 => floor_all r H hE hw a hearly hj1 (by omega))

/-- **`early`**, with no wall: a fast takeoff by the last frame searched has the frames of `FastTakeoff` -/
theorem early_of (H : Checks sy m N) (hE : r.t0 ≤ r.E) (hw : NoWall sy m N r.fr r.C)
    (a : Approach sy m N r.fr r.C r.t0 sz) (hearly : a.T1 ≤ r.C + N.fall + N.lastG) : Early sy m N r.fr r.C a.T1 := by
  have hN := H.nums
  have hT := a.T1_ge
  have hTl := a.T1_lt
  have hL := land_late r H a
  have hL2 := a.L_le
  have hl := hN.last_le
  have harc0 : (r.fr.vs (a.T1 + 1)).st ≠ 0 := (arc_facts H (arc_from r H hE hw a hearly 0 (by omega)) (by omega)).2.2
  have hhg := hN.hit_ge
  refine ⟨hw, fun n h1 h2 => fall_air r H h1 h2 (fun j h3 h4 => hw j h3 (by omega)), ?_, ?_, ?_⟩
  · intro n h1 h2
    have h3 := floor_all r H hE hw a hearly h1 (by omega)
    have h4 := floor_all r H hE hw a hearly (n := n + 1) (by omega) (by omega)
    cases r.vfloor hw n h1 (by omega) (by omega) (fun j hj1 hj2 => floor_all r H hE hw a hearly hj1 (by omega)) with
    | stay _ _ hi => exact hi
    | takeoff _ x hx h5 _ =>
      exfalso
      have h6 : OnArc sy m N r.fr n (n + 1) := by
        refine ⟨by omega, x, x, hx, ?_, h5⟩
        rw [show n + 1 - (n + 1) = 0 by omega]
        exact .refl _
      exact (arc_facts H h6 (by omega)).2.2 h4.1
    | air h5 _ _ => exact absurd h3.1 h5
    | fall h5 _ => exact absurd h3.1 h5
    | other h5 _ => exact absurd h3 h5
  · cases r.vfloor hw a.T1 (by omega) (by omega) (by omega) (fun j hj1 hj2 => floor_all r H hE hw a hearly hj1 hj2) with
    | stay _ h2 _ => exact absurd h2.1 harc0
    | takeoff _ _ _ _ hi => exact hi
    | air h1 _ _ => exact absurd a.T1_floor.1 h1
    | fall h1 _ => exact absurd a.T1_floor.1 h1
    | other h1 _ => exact absurd a.T1_floor h1
  · intro n h1 h2
    have h3 := arc_from r H hE hw a hearly (n - (a.T1 + 1)) (by omega)
    rw [show a.T1 + 1 + (n - (a.T1 + 1)) = n by omega] at h3
    exact r.air_in n (by omega) (by have := hN.vf.1; omega) (arc_facts H h3 (by omega)).2.2

/-! ### A wall hit: short of the goal with no jump analysis -/

/-- the distance to `t0` from a frame, with every frame following `hstep` -/
theorem dist_from (H : Checks sy m N) {u : Nat} {p : Int} (hJ : J sy m (r.fr.hs u) p) (hu : u ≤ r.t0)
    (hfol : ∀ i, u ≤ i → i < r.t0 → Follow sy m r.fr i) : r.fr.P r.t0 ≤ r.fr.P u + dbound sy m p (r.t0 - u) := by
  have hf : ∀ i, u ≤ i → i < u + (r.t0 - u) → Follow sy m r.fr i := fun i h1 h2 => hfol i h1 (by omega)
  have h1 := hdist_seg u (r.t0 - u) hf
  rw [show u + (r.t0 - u) = r.t0 by omega] at h1
  have h2 := dist_le H.air.pot _ _ _ hJ (inputs_seg u (r.t0 - u) hf)
  rw [length_seg] at h2
  omega

/-- `J` along frames that follow `hstep` -/
theorem J_run (F : Facts sy m) : ∀ (d u : Nat) (p : Int), J sy m (r.fr.hs u) p → (∀ i, u ≤ i → i < u + d → Follow sy m r.fr i) →
    J sy m (r.fr.hs (u + d)) (iterN sy m p d)
  | 0, _, _, h, _ => h
  | d + 1, u, p, h, hf => by
    have h1 := hf u (Nat.le_refl _) (by omega)
    have h2 := (step_J F h h1.1).1
    rw [← h1.2.1] at h2
    have h3 := J_run F d (u + 1) _ h2 (fun i h4 h5 => hf i (by omega) (by omega))
    rwa [show u + 1 + d = u + (d + 1) by omega] at h3

/-- two stands in the fall are apart: from a stand, a frame stopped by the wall, he needs speed to stand again -/
theorem stand_gap (H : Checks sy m N) {i j : Nat} (hi : r.C ≤ i) (hij : i < j) (hj : j < r.C + N.fall) (h1 : (r.fr.vs i).st = 0)
    (h2 : (r.fr.vs j).st = 0) : i + N.gapF ≤ j := by
  have hN := H.nums
  have F := H.air.pot
  have hle := hN.fall_le
  have hg := hN.hit_ge
  have hhr := hN.hit_run
  have hlate := t0_late r H
  have h2' := hN.gap_two
  have hiC : i ≠ r.C := fun h3 => by
    rw [h3, r.v_start.1] at h1
    exact absurd h1 (by decide)
  obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
  have h3 := r.stand_off l (by omega) (by omega) (Or.inl (by omega)) h1 (r.fall_long _ hi (by omega))
  have hn : ¬∀ k, r.C ≤ k → k < l + 1 → Follow sy m r.fr k := fun h4 => h3 (h4 l (by omega) (by omega))
  obtain ⟨h, h4, h5, h6, h7⟩ := first_hit _ hn
  obtain ⟨a, ha⟩ := anchor_at r H h4 (by omega) h6 h7 (by omega) (j - 1 - (h + 1)) (by omega) (by omega)
  rw [show h + 1 + (j - 1 - (h + 1)) = j - 1 by omega] at ha
  have hal : l + 1 ≤ a := by
    by_cases h8 : l + 1 ≤ a
    · exact h8
    · exact absurd (ha.fol l (by omega) (by omega)) h3
  have hle2 := ha.le
  have h9 := J_run r F (j - 1 - a) a N.stopPhi ha.J' (fun k h10 h11 => ha.fol k h10 (by omega))
  rw [show a + (j - 1 - a) = j - 1 by omega] at h9
  have h10 := phi_ge F (r.fr.hs (j - 1))
  have h11 := h9.2.1
  obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h12 := r.stand_fast j' (by omega) (by omega) (Or.inr ⟨l + 1, by omega, by omega, h1⟩) (by rw [← hj']; exact h2)
  rw [show j' = j - 1 by omega] at h12
  by_cases h13 : l + 1 + N.gapF ≤ j
  · exact h13
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, N.gapF - 2 = (j - 1 - a) + k := ⟨N.gapF - 2 - (j - 1 - a), by omega⟩
    have h14 := iterN_count F (j - 1 - a) k N.stopPhi
    rw [← hk] at h14
    have h15 := hN.gap_V
    omega

/-- the frame after the last wall frame: in `J` with `nxt`, below the threshold, and not far -/
theorem wall_next (H : Checks sy m N) {b : Nat} (hP : r.fr.P b ≤ N.wallP) (hJ : J sy m (r.fr.hs b) N.stopPhi) (hf : Follow sy m r.fr b) :
    J sy m (r.fr.hs (b + 1)) (nxt sy m N.stopPhi) ∧ capped sy (r.fr.hs (b + 1)) = true ∧ (r.fr.hs (b + 1)).rs = 0 ∧
      r.fr.P (b + 1) ≤ N.wallP + 16 * (nxt sy m N.stopPhi / 256) := by
  have F := H.air.pot
  have hN := H.nums
  obtain ⟨hJ1, h256, _⟩ := step_J F hJ hf.1
  rw [← hf.2.1] at hJ1 h256
  have h1 := phi_ge F (r.fr.hs (b + 1))
  have h2 := hJ1.2.1
  have h3 := hN.wall_phi
  have h4 : (r.fr.hs (b + 1)).f.toNat < 256 := (r.fr.hs (b + 1)).f.toNat_lt
  have h5 := hf.2.2
  refine ⟨hJ1, ?_, ?_, ?_⟩
  · simp only [capped, decide_eq_true_eq]
    unfold V at h1
    unfold theta at h3
    omega
  · by_cases h6 : (r.fr.hs (b + 1)).rs = 0
    · exact h6
    · have := hJ1.2.2 h6
      omega
  · omega

/-- **After a wall hit before `wallD`, facing right.** One frame of any kind, then air frames to the end of the fall: `Ψ` is small. Moving right
at the end of the fall, or with `Φ ≤ fastQ`, the potential gives the bound. Moving left fast, he has gone back -/
theorem wall_right (H : Checks sy m N) {b : Nat} (hge : r.C + N.wallF ≤ b) (hP : r.fr.P b ≤ N.wallP) (hJ : J sy m (r.fr.hs b) N.stopPhi)
    (hb : b + 1 ≤ r.C + N.fall) (hfol : ∀ i, b ≤ i → i < r.t0 → Follow sy m r.fr i) (hb0 : b < r.t0) (hfall : r.C + N.fall ≤ r.t0)
    (hfd : (r.fr.hs (b + 1)).fd = 1) (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have ha1 := hN.a1_nonneg
  have hgs := F.gs_nonneg
  have hle := hN.fall_le
  have hfw := hN.fall_wall
  have hwk := hN.wall_k
  obtain ⟨hJ1, hc1, hrs1, hP1⟩ := wall_next r H hP hJ (hfol b (Nat.le_refl _) hb0)
  have hst1 : FallSt sy (r.fr.hs (b + 1)) := ⟨hJ1.1, hc1, hfd, hrs1⟩
  have hs0 := hN.stop_nonneg
  have hle1 := le_nxt F N.stopPhi
  have hgn : gSlow sy m ≤ nxt sy m N.stopPhi := by
    have := hN.gs_stop
    omega
  have hpn : 0 ≤ nxt sy m N.stopPhi := by omega
  have hpsi1 : psiP sy m (r.fr.hs (b + 1)) ≤ nxt sy m N.stopPhi := psiP_le ha1 hJ1.2.1 hgn
  -- the air frames
  have hrun : ∀ i, b + 1 ≤ i → i < r.C + N.fall → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h1 h2 => by
    refine ⟨hfol i (by omega) (by omega), r.air_in i (by omega) (by omega) ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', i = n' + 1 := ⟨i - 1, by omega⟩
    exact st_ne r (by omega) (by omega) (Or.inl (by omega)) (hfol n' (by omega) (by omega)) (r.fall_long _ (by omega) h2)
  have hd : b + 1 + (r.C + N.fall - (b + 1)) = r.C + N.fall := by omega
  obtain ⟨hst34, hpsi, hP34⟩ := fall_run r H hst1 hpsi1 (r.C + N.fall - (b + 1)) (fun i h1 h2 => hrun i h1 (by omega))
  rw [hd] at hst34 hpsi hP34
  have hfol34 : ∀ i, r.C + N.fall ≤ i → i < r.t0 → Follow sy m r.fr i := fun i h1 h2 => hfol i (by omega) h2
  have ha : a1 sy m * ((r.C + N.fall - (b + 1) : Nat) : Int) ≤ a1 sy m * ((N.fall - N.wallF - 1 : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) ha1
  have hQ0 := hN.wall_Q
  by_cases hQ : phi sy m (r.fr.hs (r.C + N.fall)) ≤ N.fastQ
  · -- the potential from the end of the fall
    have hJ34 : J sy m (r.fr.hs (r.C + N.fall)) N.fastQ := ⟨hst34.dom, hQ, fun h1 => absurd hst34.rs h1⟩
    have h1 := dist_from r H hJ34 hfall hfol34
    have hq0 : 0 ≤ N.fastQ := by
      have := phi_ge F (r.fr.hs (r.C + N.fall))
      omega
    obtain ⟨k, hk⟩ : ∃ k, N.goalF - N.fall = (r.t0 - (r.C + N.fall)) + k := ⟨N.goalF - N.fall - (r.t0 - (r.C + N.fall)), by omega⟩
    have h2 := dbound_mono F (r.t0 - (r.C + N.fall)) k N.fastQ hq0
    rw [← hk] at h2
    obtain ⟨k2, hk2⟩ : ∃ k, N.fall - N.wallF - 1 = (r.C + N.fall - (b + 1)) + k := ⟨N.fall - N.wallF - 1 - (r.C + N.fall - (b + 1)), by omega⟩
    have h3 := airDist_mono (sy := sy) (m := m) hpn ha1 (r.C + N.fall - (b + 1)) k2
    rw [← hk2] at h3
    have h4 := hN.wall_open
    omega
  · -- moving left at the end of the fall
    have hV : V (r.fr.hs (r.C + N.fall)) < 0 := by
      by_cases h1 : V (r.fr.hs (r.C + N.fall)) < 0
      · exact h1
      · exfalso
        apply hQ
        rw [psiP_eq_phi (by omega)]
        omega
    have hu : N.fastQ + 1 - 2 * c sy m ≤ -V (r.fr.hs (r.C + N.fall)) := by
      have h1 := AirCap.w_le F (r.fr.hs (r.C + N.fall))
      unfold phi at hQ
      omega
    have hst : ∀ i, b + 1 ≤ i → i ≤ r.C + N.fall → FallSt sy (r.fr.hs i) := fun i h1 h2 => by
      obtain ⟨h3, _, _⟩ := fall_run r H hst1 hpsi1 (i - (b + 1)) (fun j h3 h4 => hrun j h3 (by omega))
      rwa [show b + 1 + (i - (b + 1)) = i by omega] at h3
    have hbk : b + 1 ≤ r.C + N.fall - N.wallK := by
      by_cases h1 : b + 1 ≤ r.C + N.fall - N.wallK
      · exact h1
      · exfalso
        have hu2 := hu
        rw [← hd] at hu2
        have h3 := back_speed r H (b := b + 1) (r.C + N.fall - (b + 1)) _ (fun i h3 h4 => by
          have h5 := hrun i h3 (by omega)
          exact ⟨hst i (by omega) (by omega), h5.1, h5.2⟩) hu2
        have h4 : gSlow sy m * ((r.C + N.fall - (b + 1) : Nat) : Int) ≤ gSlow sy m * ((N.wallK - 1 : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_left (by omega) hgs
        have h5 := hN.wall_u
        have h6 := phi_ge F (r.fr.hs (b + 1))
        have h7 := hJ1.2.1
        omega
    have hb2 : r.C + N.fall - N.wallK + N.wallK = r.C + N.fall := by omega
    have hu3 := hu
    rw [← hb2] at hu3
    have h1 := back_run r H (b := r.C + N.fall - N.wallK) N.wallK _ (fun i h3 h4 => by
      have h5 := hrun i (by omega) (by omega)
      exact ⟨hst i (by omega) (by omega), h5.1, h5.2⟩) hu3
    rw [hb2] at h1
    obtain ⟨_, _, h2⟩ := fall_run r H hst1 hpsi1 (r.C + N.fall - N.wallK - (b + 1)) (fun i h3 h4 => hrun i h3 (by omega))
    rw [show b + 1 + (r.C + N.fall - N.wallK - (b + 1)) = r.C + N.fall - N.wallK by omega] at h2
    obtain ⟨k, hk⟩ : ∃ k, N.fall - N.wallK - N.wallF - 1 = (r.C + N.fall - N.wallK - (b + 1)) + k :=
      ⟨N.fall - N.wallK - N.wallF - 1 - (r.C + N.fall - N.wallK - (b + 1)), by omega⟩
    have h3 := airDist_mono (sy := sy) (m := m) hpn ha1 (r.C + N.fall - N.wallK - (b + 1)) k
    rw [← hk] at h3
    have hfol2 : ∀ j, r.C + N.fall ≤ j → j < r.C + N.fall + (r.t0 - (r.C + N.fall)) → Follow sy m r.fr j := fun j h4 h5 =>
      hfol34 j h4 (by omega)
    have h4 := hdist_seg (r.C + N.fall) (r.t0 - (r.C + N.fall)) hfol2
    rw [show r.C + N.fall + (r.t0 - (r.C + N.fall)) = r.t0 by omega] at h4
    have h5 := AirCap.dist_capped H.air _ _ hst34.dom hst34.cap (inputs_seg _ _ hfol2)
    rw [length_seg] at h5
    obtain ⟨k2, hk2⟩ : ∃ k, N.goalF - N.fall = (r.t0 - (r.C + N.fall)) + k := ⟨N.goalF - N.fall - (r.t0 - (r.C + N.fall)), by omega⟩
    have h6 := cap_mono (m := m) hN.air_pos (r.t0 - (r.C + N.fall)) k2
    rw [← hk2] at h6
    have h7 := hN.wall_back
    omega

/-- frames with no jump: the height and the speed from a frame -/
theorem drop_run {u : Nat} {w0 : Int} (hu : r.C ≤ u) (h0 : ∀ j, r.C ≤ j → j < u → (r.fr.inp (j + 1)).jump = false) (h1 : (r.fr.vs u).st ≠ 1)
    (h2 : (r.fr.vs u).vfd.toNat = N.fallF) (h3 : VW (r.fr.vs u) ≤ w0) :
    ∀ e, u + e < r.C + N.standF → (∀ j, u ≤ j → j < u + e → (r.fr.inp (j + 1)).jump = false) →
      (r.fr.vs (u + e)).st ≠ 1 ∧ (r.fr.vs (u + e)).vfd.toNat = N.fallF ∧ VW (r.fr.vs (u + e)) ≤ w0 + (N.fallF : Int) * (e : Int) ∧
        VY (r.fr.vs (u + e)) ≤ VY (r.fr.vs u) + fallSum w0 (N.fallF : Int) e
  | 0, _, _ => by simpa [fallSum] using And.intro h1 (And.intro h2 h3)
  | e + 1, h4, h5 => by
    obtain ⟨h6, h7, h8, h9⟩ := drop_run hu h0 h1 h2 h3 e (by omega) (fun j h10 h11 => h5 j h10 (by omega))
    have hv := r.vfall (u + e) (by omega) (by omega) h6 (fun j h10 h11 => by
      by_cases h12 : j < u
      · exact h0 j h10 h12
      · exact h5 j (by omega) (by omega))
    have hm : (N.fallF : Int) * ((e + 1 : Nat) : Int) = (N.fallF : Int) * (e : Int) + (N.fallF : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [show u + (e + 1) = u + e + 1 by omega, hm]
    simp only [fallSum]
    have h10 := hv.y_le
    have h11 := hv.w_le
    rw [show (u + e + 1) = u + e + 1 from rfl] at *
    refine ⟨hv.st, by rw [hv.vfd]; exact h7, by omega, by omega⟩

theorem capRamp_nonneg (hA : 1 ≤ sy.AirFastSpeed.toNat) (F : Facts sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ capRamp sy m p n
  | 0, _, _ => by simp [capRamp]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := capRamp_nonneg hA F n (nxt sy m p) (by omega)
    simp only [capRamp]
    have h2 : 0 ≤ min ((sy.AirFastSpeed.toNat : Int) - 1) (nxt sy m p / 256) := Int.le_min.2 ⟨by omega, by omega⟩
    omega

theorem capRamp_mono (hA : 1 ≤ sy.AirFastSpeed.toNat) (F : Facts sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → capRamp sy m p n ≤ capRamp sy m p (n + k)
  | 0, k, p, hp => by
    have := capRamp_nonneg hA F k p hp
    simpa [capRamp] using this
  | n + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := capRamp_mono hA F n k (nxt sy m p) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [capRamp]
    omega

/-- frames below the threshold: at most the air speed, and at most the potential -/
theorem ramp_run (F : Facts sy m) : ∀ (d u : Nat) (p : Int), J sy m (r.fr.hs u) p →
    (∀ i, u ≤ i → i < u + d → Follow sy m r.fr i) → (∀ i, u < i → i ≤ u + d → capped sy (r.fr.hs i) = true) →
      r.fr.P (u + d) ≤ r.fr.P u + capRamp sy m p d
  | 0, _, _, _, _, _ => by simp [capRamp]
  | d + 1, u, p, hJ, h1, h2 => by
    have hf := h1 u (Nat.le_refl _) (by omega)
    obtain ⟨hJ1, h256, _⟩ := step_J F hJ hf.1
    rw [← hf.2.1] at hJ1 h256
    have ih := ramp_run F d (u + 1) _ hJ1 (fun i h3 h4 => h1 i (by omega) (by omega)) (fun i h3 h4 => h2 i (by omega) (by omega))
    have hc := h2 (u + 1) (by omega) (by omega)
    simp only [capped, decide_eq_true_eq] at hc
    have h5 := hf.2.2
    rw [show u + 1 + d = u + (d + 1) by omega] at ih
    simp only [capRamp]
    have h6 : sbyte (r.fr.hs (u + 1)).v ≤ min ((sy.AirFastSpeed.toNat : Int) - 1) (nxt sy m p / 256) := Int.le_min.2 ⟨by omega, by omega⟩
    omega

/-- **After a wall hit before `wallD`, turned away from the right.** That needs a ground frame with no jump, on a stand in the fall, and it is
the only stand so far. He falls with the first force, so he is not on the floor for `k` frames after the stand, and all those frames are air frames:
below the threshold. After them, any frames -/
theorem wall_turn (H : Checks sy m N) {b : Nat} (hge : r.C + N.wallF ≤ b) (hbD : b < r.C + N.wallD) (hP : r.fr.P b ≤ N.wallP)
    (hJ : J sy m (r.fr.hs b) N.stopPhi) (hfol : ∀ i, b ≤ i → i < r.t0 → Follow sy m r.fr i) (hb0 : b < r.t0)
    (hfd : (r.fr.hs (b + 1)).fd ≠ 1) (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have hle := hN.fall_le
  have hwD := hN.wallD_le
  have hgap := hN.gap_D
  have hg := hN.hit_ge
  have hA := hN.air_pos
  have hbF : b < r.C + N.fall := by omega
  obtain ⟨hst0, hY0, hW0, hf0⟩ := r.v_start
  -- a ground frame with no jump, up to `b + 1`
  have hex : ∃ i, r.C ≤ i ∧ i ≤ b ∧ (r.fr.inp (i + 1)).st = 0 ∧ (r.fr.inp (i + 1)).jump = false := by
    by_cases hc : ∃ i, r.C ≤ i ∧ i ≤ b ∧ (r.fr.inp (i + 1)).st = 0 ∧ (r.fr.inp (i + 1)).jump = false
    · exact hc
    · exfalso
      have hchain : ∀ d, r.C + d ≤ b + 1 → (r.fr.hs (r.C + d)).fd = 1 := by
        intro d
        induction d with
        | zero => exact fun _ => (start_fall r H).fd
        | succ d ih =>
          intro h1
          have h2 := ih (by omega)
          have h3 : (r.fr.inp (r.C + d + 1)).st ≠ 0 ∨ (r.fr.inp (r.C + d + 1)).jump = true := by
            by_cases h4 : (r.fr.inp (r.C + d + 1)).st = 0
            · right
              by_cases h5 : (r.fr.inp (r.C + d + 1)).jump = true
              · exact h5
              · exact absurd ⟨r.C + d, by omega, by omega, h4, by simpa using h5⟩ hc
            · exact Or.inl h4
          rw [show r.C + (d + 1) = r.C + d + 1 by omega, r.facing (r.C + d) (by omega) (by omega) h3]
          exact h2
      have h1 := hchain (b + 1 - r.C) (by omega)
      rw [show r.C + (b + 1 - r.C) = b + 1 by omega] at h1
      exact hfd h1
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hex
  -- it starts on a stand
  have hst : (r.fr.vs i).st = 0 := by
    by_cases h1 : (r.fr.vs i).st = 0
    · exact h1
    · have h2 := (r.air_in i hi1 (by omega) h1).2.1
      rw [hi3] at h2
      exact absurd h2 (by decide)
  have hiC : i ≠ r.C := fun h1 => by
    rw [h1, hst0] at hst
    exact absurd hst (by decide)
  -- no stand before it
  have hfirst : ∀ l, r.C ≤ l → l < i → (r.fr.vs l).st ≠ 0 := fun l h1 h2 h3 => by
    have h4 := stand_gap r H h1 h2 (by omega) h3 hst
    have hlC : l ≠ r.C := fun h5 => by
      rw [h5, hst0] at h3
      exact absurd h3 (by decide)
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have h5 := r.stand_off l' (by omega) (by omega) (Or.inl (by omega)) h3 (r.fall_long _ h1 (by omega))
    have hn : ¬∀ j, r.C ≤ j → j < l' + 1 → Follow sy m r.fr j := fun h6 => h5 (h6 l' (by omega) (by omega))
    obtain ⟨h', h6, h7, h8, h9⟩ := first_hit _ hn
    have h10 := wall_first r H h6 h9 (r.wall h' h6 (by omega) h8).before
    omega
  -- it is not on the frame `wallF + 1` or before
  have hlate : r.C + N.wallF + 1 ≤ i := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have h5 := r.stand_off i' (by omega) (by omega) (Or.inl (by omega)) hst (r.fall_long _ hi1 (by omega))
    have hn : ¬∀ j, r.C ≤ j → j < i' + 1 → Follow sy m r.fr j := fun h6 => h5 (h6 i' (by omega) (by omega))
    obtain ⟨h', h6, h7, h8, h9⟩ := first_hit _ hn
    by_cases h10 : h' = i'
    · subst h10
      by_cases hw : h' < r.C + N.wallF
      · have h11 := left_far r H h6 h9 (r.stand_hit h' h6 (by omega) hw h9 h8 (fun l hl1 hl2 => hfirst l (by omega) (by omega)) hst) hN.stand_far
        omega
      · omega
    · have h11 := wall_first r H h6 h9 (r.wall h' h6 (by omega) h8).before
      omega
  -- the height on the stand
  have hjump0 : ∀ j, r.C ≤ j → j < i → (r.fr.inp (j + 1)).jump = false := fun j h1 h2 =>
    (r.air_in j h1 (by omega) (hfirst j h1 h2)).2.2
  obtain ⟨h1, h2, h3, h4⟩ := drop_run r (u := r.C) (Nat.le_refl _) (fun j h5 h6 => absurd h6 (by omega)) (by rw [hst0]; decide) hf0 hW0 (i - r.C) (by omega)
    (fun j h5 h6 => hjump0 j h5 (by omega))
  rw [show r.C + (i - r.C) = i by omega] at h1 h2 h3 h4
  obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hrow := r.stand_row i' (by omega) (by omega) (hfirst i' (by omega) (by omega)) (by rw [← hi']; exact hst)
  rw [← hi'] at hrow
  obtain ⟨hr1, hr2⟩ := hrow
  have hYi : VY (r.fr.vs i) ≤ standB N (i - r.C) := by
    unfold standB
    generalize fallSum N.startW (N.fallF : Int) (i - r.C) = S at h4
    have hd : (r.fr.vs i).dummy.toNat < 256 := (r.fr.vs i).dummy.toNat_lt
    have h5 : VY (r.fr.vs i) ≤ N.startY + S := by omega
    unfold VY at h5 ⊢
    omega
  -- the pair of numbers
  have hany : N.gaps.any (fun q => q.1 == i - r.C) = true := by
    have h5 := hN.gaps_all
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h5
    rcases h5 (i - r.C) (List.mem_range.2 (by omega)) with h6 | h6
    · omega
    · exact h6
  obtain ⟨q, hq, hq1⟩ := List.any_eq_true.1 hany
  have hq2 : q.1 = i - r.C := by simpa using hq1
  have hok := hN.gaps_ok
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hq3, hq4⟩, hq5⟩, hq6⟩, hq7⟩ := hok q hq
  rw [hq2] at hq3 hq4 hq5 hq6 hq7
  generalize q.2 = k at hq3 hq4 hq5 hq6 hq7
  -- not on the floor for `k` frames
  have hsum : ∀ e, e ≤ k → fallSum 0 (N.fallF : Int) e ≤ fallSum 0 (N.fallF : Int) k := by
    intro e he
    obtain ⟨c, hc⟩ : ∃ c, k = e + c := ⟨k - e, by omega⟩
    rw [hc]
    clear hc
    induction c with
    | zero => exact Int.le_refl _
    | succ c ih =>
      rw [show e + (c + 1) = e + c + 1 by omega]
      simp only [fallSum]
      have : (0 : Int) ≤ (N.fallF : Int) * ((e + c : Nat) : Int) := Int.mul_nonneg (by omega) (by omega)
      omega
  have hw0 : VW (r.fr.vs i) ≤ 0 := by omega
  have hnoj : ∀ e, e ≤ k → i + e ≤ r.t0 → ∀ j, i ≤ j → j < i + e → (r.fr.inp (j + 1)).jump = false := by
    intro e
    induction e with
    | zero => exact fun _ _ j h5 h6 => by omega
    | succ e ih =>
      intro h5 h6 j h7 h8
      by_cases h9 : j < i + e
      · exact ih (by omega) (by omega) j h7 h9
      · have hj : j = i + e := by omega
        subst hj
        by_cases he : e = 0
        · subst he
          exact hi4
        · obtain ⟨_, _, _, h10⟩ := drop_run r (u := i) hi1 hjump0 (by rw [hst]; decide) h2 hw0 e (by omega) (ih (by omega) (by omega))
          have h11 := hsum e (by omega)
          have hnf : ¬OnFloor sy (r.fr.vs (i + e)) := fun h12 => by
            have h13 := h12.2
            have hd : (0 : Int) ≤ ((r.fr.vs (i + e)).dummy.toNat : Int) := by omega
            unfold VY at h10
            rw [h13] at h10
            unfold VY at hYi
            unfold standB at hq6 hYi
            omega
          refine (r.air_in (i + e) (by omega) (by omega) ?_).2.2
          by_cases h12 : i + e ≤ b
          · intro h13
            have h14 := stand_gap r H hi1 (by omega) (by omega) hst h13
            omega
          · obtain ⟨n', hn'⟩ : ∃ n', i + e = n' + 1 := ⟨i + e - 1, by omega⟩
            rw [hn']
            exact st_ne r (by omega) (by omega) (Or.inr ⟨i, by omega, by omega, hst, fun l hl1 hl2 => ih (by omega) (by omega) l hl1 (by omega)⟩)
              (hfol n' (by omega) (by omega)) (by rw [← hn']; exact hnf)
  -- so every frame after `b` up to there is an air frame
  let n2 := min r.t0 (i + k + 1)
  have hn2 : b + 1 ≤ n2 := by
    simp only [n2]
    omega
  have hairF : ∀ n, b + 1 ≤ n → n < n2 → isAir (r.fr.inp (n + 1)) = true ∨ Stop sy m N r.fr (n + 1) := fun n h5 h6 => by
    left
    simp only [n2] at h6
    have h7 := hnoj (n - i) (by omega) (by omega)
    obtain ⟨_, _, _, h10⟩ := drop_run r (u := i) hi1 hjump0 (by rw [hst]; decide) h2 hw0 (n - i) (by omega) h7
    rw [show i + (n - i) = n by omega] at h10
    have h11 := hsum (n - i) (by omega)
    have hnf : ¬OnFloor sy (r.fr.vs n) := fun h12 => by
      have h13 := h12.2
      have hd : (0 : Int) ≤ ((r.fr.vs n).dummy.toNat : Int) := by omega
      unfold VY at h10
      rw [h13] at h10
      unfold VY at hYi
      unfold standB at hq6 hYi
      omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h12 := r.air_in (n' + 1) (by omega) (by omega)
      (st_ne r (by omega) (by omega) (Or.inr ⟨i, by omega, by omega, hst, fun l hl1 hl2 => h7 l hl1 (by omega)⟩) (hfol n' (by omega) (by omega)) hnf)
    simp [isAir, h12.2.1]
  obtain ⟨hJ1, hc1, _, _⟩ := wall_next r H hP hJ (hfol b (Nat.le_refl _) hb0)
  have hcap := capped_along r H (u := b + 1) (w := n2) (by omega) (by simp only [n2]; omega) hc1 hairF
  have hcap' : ∀ j, b < j → j ≤ n2 → capped sy (r.fr.hs j) = true := fun j h5 h6 => by
    have h7 := hcap (j - (b + 1)) (by omega)
    rwa [show b + 1 + (j - (b + 1)) = j by omega] at h7
  have hP2 := ramp_run r F (n2 - b) b N.stopPhi hJ (fun j h5 h6 => hfol j h5 (by simp only [n2] at h6; omega))
    (fun j h5 h6 => hcap' j h5 (by omega))
  rw [show b + (n2 - b) = n2 by omega] at hP2
  obtain ⟨c1, hc1'⟩ : ∃ c, k + 1 = (n2 - b) + c := ⟨k + 1 - (n2 - b), by
    simp only [n2]
    omega⟩
  have hP3 := capRamp_mono hA F (n2 - b) c1 N.stopPhi hN.stop_nonneg
  rw [← hc1'] at hP3
  -- then any frames
  have hfol2 : ∀ j, n2 ≤ j → j < n2 + (r.t0 - n2) → Follow sy m r.fr j := fun j h5 h6 => hfol j (by omega) (by simp only [n2] at h6 ⊢; omega)
  have h5 := hdist_seg n2 (r.t0 - n2) hfol2
  rw [show n2 + (r.t0 - n2) = r.t0 by simp only [n2]; omega] at h5
  have h6 := AirCap.dist_capped H.air _ _ (inD_at r H (n := n2) (by omega) (by simp only [n2]; omega)) (hcap' n2 (by omega) (Nat.le_refl _))
    (inputs_seg _ _ hfol2)
  rw [length_seg] at h6
  obtain ⟨c2, hc2⟩ : ∃ c, N.goalF - (i - r.C + k + 1) = (r.t0 - n2) + c := ⟨N.goalF - (i - r.C + k + 1) - (r.t0 - n2), by
    simp only [n2]
    omega⟩
  have h7 := cap_mono (m := m) hA (r.t0 - n2) c2
  rw [← hc2] at h7
  omega

/-- **A wall hit before `hitF`, and no stop from `hitF` on: he is short of the goal**, whatever he does: there is no need to look at a jump -/
theorem wall_short (H : Checks sy m N) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) (hw : ¬NoWall sy m N r.fr r.C)
    (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have hg := hN.hit_ge
  have hhr := hN.hit_run
  have hlate := t0_late r H
  have hwD := hN.wallD_le
  have hfA : ∀ j, r.C + N.hitF ≤ j + 1 → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 => follow_of r hs h1 h2 (by omega)
  obtain ⟨b, hb⟩ := anchor_of_wall r H hw (w := r.C + N.hitF - 1) (by omega) (by omega) (by omega)
  have hle := hb.le
  have hge := hb.ge
  have hfol : ∀ i, b ≤ i → i < r.t0 → Follow sy m r.fr i := fun i h1 h2 => by
    by_cases h3 : i < r.C + N.hitF - 1
    · exact hb.fol i h1 h3
    · exact hfA i (by omega) h2
  by_cases hnear : r.C + N.wallD ≤ b
  · have h1 := dist_from r H hb.J' (by omega) hfol
    obtain ⟨k, hk⟩ : ∃ k, N.goalF - N.wallD = (r.t0 - b) + k := ⟨N.goalF - N.wallD - (r.t0 - b), by omega⟩
    have h2 := dbound_mono F (r.t0 - b) k N.stopPhi hN.stop_nonneg
    rw [← hk] at h2
    have h3 := hN.wall_near
    have h4 := hb.P_le
    omega
  · by_cases hfd : (r.fr.hs (b + 1)).fd = 1
    · exact wall_right r H hge hb.P_le hb.J' (by omega) hfol (by omega) (by omega) hfd ht
    · exact wall_turn r H hge (by omega) hb.P_le hb.J' hfol (by omega) hfd ht

/-- **A fast takeoff** of `landed_short`, with the search of `FastTakeoff` for `L'` low air frames after the jump frame (`hc`): with no stop from `hitF` on, every frame
up to `T1 + 1 + L'` left of the corner is impossible for a run that is past the goal by `C + goalF`. `L'` is `rise` (`room`), or `rise − 1` (`roomB`) when the last low
frame of a big player may be past the corner -/
theorem fast_short (H : Checks sy m N) (hE : r.t0 < r.E) (hw : NoWall sy m N r.fr r.C) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n)
    (a : Approach sy m N r.fr r.C r.t0 sz) (ht : r.t0 ≤ r.C + N.goalF) (hf : a.x.fast = true) (hearly : a.T1 ≤ r.C + N.fall + N.lastG)
    {L' : Nat} (hL : L' ≤ N.rise) (hc : roomCheck sy m (bonusRoom sy N.fall N.lastG L' (N.goalF - N.fall)) = true)
    (hleft : ∀ n, r.C ≤ n → n ≤ a.T1 + 1 + L' → r.fr.P n < cornerP sy) : False := by
  have hn := H.nums
  have hpast := r.past
  have hT1 := a.T1_ge
  have hT2 := a.T1_lt
  have hhr := hn.hit_rise
  have hhg := hn.hit_ge
  have hll := land_late r H a
  have hLt := a.L_le
  have hfol : ∀ j, r.C + N.hitF ≤ j + 1 → r.C ≤ j → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 h3 =>
    follow_of r hs h1 h3 h2
  have hth : sy.AirFastSpeed.toNat ≤ (sbyte (r.fr.hs a.T1).v).natAbs := by
    have h1 := a.x_ab
    rw [hf] at h1
    have h2 : sy.AirFastSpeed.toNat ≤ r.fr.ab a.T1 := by simpa using h1.symm
    rcases r.ab_of a.T1 (by omega) (by omega) with h3 | ⟨h3, h4⟩
    · omega
    · -- a stop right after the takeoff: before `hitF`, so the stored speed is below the threshold
      by_cases h5 : a.T1 + 1 < r.C + N.hitF
      · have := h4 h5
        omega
      · exact absurd h3 (hs (a.T1 + 1) (by omega) (by omega))
  have E := early_of r H (Nat.le_of_lt hE) hw a hearly
  have hF : ∀ j, r.C ≤ j → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 => by
    by_cases h3 : j + 1 < r.C + N.hitF
    · exact E.follow j h1 h3
    · exact hfol j (by omega) h1 h2
  let R := bonusRoom sy N.fall N.lastG L' (N.goalF - N.fall)
  have hg0 : a.T1 - (r.C + N.fall) ≤ N.lastG := by omega
  let fa := seg r.fr.inp r.C N.fall
  let g := seg r.fr.inp (r.C + N.fall) (a.T1 - (r.C + N.fall))
  let k := seg r.fr.inp (a.T1 + 1) L'
  have hTk : Takeoff R fa g (r.fr.inp (a.T1 + 1)) k :=
    { fall_in := mem_seg (P := AirIn) fun j h1 h2 => E.fall_in j h1 h2
      fall_len := length_seg _ _ _
      gnd_in := mem_seg (P := GndIn) fun j h1 h2 => E.gnd_in j h1 (by omega)
      jump_in := E.jump_in
      air_in := mem_seg (P := AirIn) fun j h1 h2 => E.air_in j h1 (by omega)
      air_len := length_seg _ _ _ }
  have hs0 : R.s0 = (room sy N).s0 := rfl
  have hgo1 : go sy m (R.s0, r.fr.P r.C) fa = (r.fr.hs (r.C + N.fall), r.fr.P (r.C + N.fall)) := by
    have h1 := go_seg (fr := r.fr) (sy := sy) (m := m) r.C N.fall (fun j h2 h3 => hF j h2 (by omega))
    rw [r.start, ← hs0] at h1
    exact h1
  have hgo2 : go sy m (R.s0, r.fr.P r.C) (fa ++ g) = (r.fr.hs a.T1, r.fr.P a.T1) := by
    rw [FastTakeoff.go_append, hgo1]
    have h1 := go_seg (fr := r.fr) (sy := sy) (m := m) (r.C + N.fall) (a.T1 - (r.C + N.fall))
      (fun j h2 h3 => hF j (by omega) (by omega))
    rw [show r.C + N.fall + (a.T1 - (r.C + N.fall)) = a.T1 by omega] at h1
    exact h1
  have hlow0 : Low sy m R.cp (go sy m (R.s0, r.fr.P r.C) fa) (g ++ r.fr.inp (a.T1 + 1) :: k) := by
    rw [hgo1]
    have h1 : g ++ r.fr.inp (a.T1 + 1) :: k = seg r.fr.inp (r.C + N.fall) (a.T1 - (r.C + N.fall) + (1 + L')) := by
      rw [seg_add, show r.C + N.fall + (a.T1 - (r.C + N.fall)) = a.T1 by omega, Nat.add_comm 1 L']
      simp only [g, k, seg]
    rw [h1]
    exact low_seg _ _ (fun j h2 h3 => hF j (by omega) (by omega)) (fun j h2 h3 => hleft (j + 1) (by omega) (by omega))
  have hp0 : R.P0 ≤ r.fr.P r.C := r.startP0
  have hp1 : r.fr.P r.C ≤ R.P1 := r.startP1
  have FT : TFacts sy m := ⟨H.air.pot, H.normI⟩
  by_cases hv : (sy.AirFastSpeed.toNat : Int) ≤ sbyte (r.fr.hs a.T1).v
  · -- moving right: he does not stay left of the corner
    refine FastTakeoff.no_right_takeoff FT hc hp0 hp1 hTk (by rw [length_seg]; exact hg0) ?_ hlow0
    rw [hgo2]
    exact hv
  · -- moving left: he is too far back
    have hv2 : sbyte (r.fr.hs a.T1).v ≤ -(sy.AirFastSpeed.toNat : Int) := by omega
    have hlowg : Low sy m R.cp (go sy m (R.s0, r.fr.P r.C) fa) g := (FastTakeoff.low_append g _ _ hlow0).1
    obtain ⟨es, _, h2, h3⟩ := FastTakeoff.layer_of FT hc hp0 hp1 hTk.fall_in hTk.fall_len hTk.gnd_in
      (by rw [length_seg]; exact hg0) (by rw [hgo2]; exact hth) hlowg
    rw [hgo2] at h3
    have hrest : ∀ j, a.T1 ≤ j → j < a.T1 + (r.t0 - a.T1) → Follow sy m r.fr j := fun j h4 h5 =>
      hF j (by omega) (by omega)
    have h5 := left_spec_le H.air.pot h2 h3 hv2 (rest := seg r.fr.inp a.T1 (r.t0 - a.T1)) (inputs_seg _ _ hrest)
      (by
        rw [length_seg, length_seg]
        show r.t0 - a.T1 ≤ N.goalF - N.fall - (a.T1 - (r.C + N.fall))
        omega)
    rw [go_seg a.T1 (r.t0 - a.T1) hrest, show a.T1 + (r.t0 - a.T1) = r.t0 by omega] at h5
    have h7 : r.fr.P r.t0 < goalP sy := h5
    omega

/-- with no stop from `hitF` on, a landing on the block is short of the goal in time: the case split on the takeoff. When the last low frame is not `LowAt` (a big player
past the corner there, `Approach.low`), a fast takeoff is the search with one low frame less (`roomB`), a slow one after the first frame after the fall is the bound
from the frame before the last low frame (`slowBigOk`, `Checks.roomBig`), and a slow one on that frame is the search of `LandDist` from the room's first frame to the
frame `T1 + q.1` of the pair, then the air frames and the table of the frames after the landing (`LandDist.slow_short`, `Checks.slowLand`) -/
theorem landed_short (H : Checks sy m N) (hE : r.t0 < r.E) (hw : NoWall sy m N r.fr r.C) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n)
    (a : Approach sy m N r.fr r.C r.t0 sz) (ht : r.t0 ≤ r.C + N.goalF) : False := by
  have hn := H.nums
  have hpast := r.past
  have hT1 := a.T1_ge
  have hT2 := a.T1_lt
  have hT := a.L_gt
  have hLt := a.L_le
  have hl0 := hn.low_nonneg
  have hA := hn.air_pos
  obtain ⟨hk, q, hq, hq1, hq2⟩ := window_pair H a.x_mem a.reach a.window
  -- the last low frame is not after the landing
  have hlowk : a.u.low ≤ a.u.k := arc_low a.reach (by rw [arcStart_low a.x_mem, arcStart_k a.x_mem]; omega)
  -- the pair has at least the low frames of every jump
  have hrq : N.rise ≤ q.1 := by
    have h1 := hn.slow_pairs
    have h2 := hn.fast_pairs
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    cases hf : a.x.fast with
    | false =>
      rw [hf] at hq
      exact (h1 q (by simpa using hq)).1.1.1
    | true =>
      rw [hf] at hq
      exact h2 q (by simpa using hq)
  have hfol : ∀ j, r.C + N.hitF ≤ j + 1 → r.C ≤ j → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 h3 =>
    follow_of r hs h1 h3 h2
  have hhr := hn.hit_rise
  have hhg := hn.hit_ge
  -- a takeoff after the last one searched: the top speed
  by_cases hlate : r.C + N.fall + N.lastG < a.T1
  · let u0 := a.T1 + 1 + N.rise
    -- a low frame is not far past the corner
    have hu0 : r.fr.P u0 ≤ cornerP sy + N.lowSlack := by
      by_cases hp : r.fr.P u0 < cornerP sy
      · omega
      · rcases a.low u0 (by omega) (by omega) (by omega) (Or.inl hlate) with h | ⟨_, _, h⟩
        · exact h.1
        · exact h
    have h1 := reach_le (P := r.fr.P) (u := u0) (B := cornerP sy + N.lowSlack) (μ := 16 * (top sy : Int)) (w := r.t0) hu0
      (by omega) (fun n h3 h4 => Or.inl (r.move_top n (by omega) h4)) (r.t0 - u0) (by omega)
    rw [show u0 + (r.t0 - u0) = r.t0 by omega] at h1
    have h2 := hn.late
    have h3 : 16 * (top sy : Int) * ((r.t0 - u0 : Nat) : Int) ≤
        16 * (top sy : Int) * ((N.goalF - (N.fall + N.lastG + 2 + N.rise) : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have hearly : a.T1 ≤ r.C + N.fall + N.lastG := by omega
  let s := a.T1 + 1 + a.u.low
  have hsL : s ≤ a.L := by omega
  -- the low frames: by C + fall + 1 + rise, while the jump ends at `cornerY + 16` or below, `LowAt` by `low_jump` from the takeoff; else the field
  have alow : ∀ n, a.T1 + 1 ≤ n → n ≤ s → LowAt sy m N r.fr n ∨ (sz = 0 ∧ n = s ∧ r.fr.P n ≤ cornerP sy + N.lowSlack) := fun n h1 h2 => by
    by_cases hp : r.fr.P n < cornerP sy
    · exact Or.inl ⟨by omega, Or.inr (Or.inl hp)⟩
    by_cases hc : n ≤ r.C + N.fall + 1 + N.rise ∧ ∀ j, a.T1 < j → j ≤ n → cornerY sy N.h + 16 ≤ (r.fr.vs j).y.toNat
    · left
      have hT : LowAt sy m N r.fr a.T1 := by
        by_cases hTe : a.T1 < r.C + N.hitF
        · have := corner_late r H (n := a.T1) (by omega) hTe (by omega)
          exact ⟨by omega, Or.inr (Or.inl this)⟩
        · exact floor_low r H (Nat.le_of_lt hE) hw a hearly (by omega) (Nat.le_refl _)
      have harc : ∀ j, a.T1 < j → j ≤ n → OnArc sy m N r.fr a.T1 j := fun j g1 g2 => by
        have h := arc_from r H (Nat.le_of_lt hE) hw a hearly (j - (a.T1 + 1)) (by omega)
        rwa [show a.T1 + 1 + (j - (a.T1 + 1)) = j by omega] at h
      exact r.low_jump hw a.T1 n hT1 (by omega) hc.1 (by omega) (fun j g1 g2 => floor_all r H (Nat.le_of_lt hE) hw a hearly g1 g2) harc hc.2 N.lowSlack (slack_ok H) hT
    · have hd : r.C + N.fall + N.lastG < a.T1 ∨ r.C + N.fall + 1 + N.rise < n ∨ ∃ j, a.T1 < j ∧ j ≤ n ∧ (r.fr.vs j).y.toNat < cornerY sy N.h + 16 := by
        by_cases h3 : n ≤ r.C + N.fall + 1 + N.rise
        · right; right
          by_cases h4 : ∃ j, a.T1 < j ∧ j ≤ n ∧ (r.fr.vs j).y.toNat < cornerY sy N.h + 16
          · exact h4
          · exact absurd ⟨h3, fun j g1 g2 => by
              by_cases h5 : (r.fr.vs j).y.toNat < cornerY sy N.h + 16
              · exact absurd ⟨j, g1, g2, h5⟩ h4
              · omega⟩ hc
        · right; left; omega
      exact a.low n h1 h2 (by omega) hd
  -- every low frame before the last is `LowAt`
  have hlowlt : ∀ n, r.C + N.hitF ≤ n → n < s → LowAt sy m N r.fr n := fun n h1 h2 => by
    by_cases h3 : n ≤ a.T1
    · exact floor_low r H (Nat.le_of_lt hE) hw a hearly h1 h3
    · rcases alow n (by omega) (by omega) with h4 | ⟨_, h4, _⟩
      · exact h4
      · omega
  by_cases hLs : LowAt sy m N r.fr s
  · -- every low frame is left of the corner
    have hlowall : ∀ n, r.C + N.hitF ≤ n → n ≤ s → LowAt sy m N r.fr n := fun n h1 h2 => by
      by_cases h3 : n < s
      · exact hlowlt n h1 h3
      · rw [show n = s by omega]
        exact hLs
    have hleft : ∀ n, r.C ≤ n → n ≤ s → r.fr.P n < cornerP sy := fun n h1 h2 =>
      left_at r H hs (w := s) (by omega) hlowall h1 h2
    cases hf : a.x.fast with
    | false =>
      -- a slow takeoff: the air speed cap from the last low frame
      rw [hf] at hq
      simp only [Bool.false_eq_true, if_false] at hq
      -- below the threshold from the takeoff, or from the stop right after it
      obtain ⟨u, hu1, hu2, hc0⟩ : ∃ u, a.T1 ≤ u ∧ u ≤ a.T1 + 1 ∧ capped sy (r.fr.hs u) = true := by
        rcases r.ab_of a.T1 (by omega) (by omega) with h2 | ⟨h2, _⟩
        · have h1 := a.x_ab
          rw [hf] at h1
          have h3 : ¬sy.AirFastSpeed.toNat ≤ r.fr.ab a.T1 := by simpa using h1.symm
          refine ⟨a.T1, Nat.le_refl _, by omega, ?_⟩
          simp only [capped, decide_eq_true_eq]
          omega
        · exact ⟨a.T1 + 1, by omega, Nat.le_refl _, capped_of_stop r H h2⟩
      have hcap := capped_along r H (u := u) (w := a.L) (by omega) hLt hc0 (fun n h1 h2 => Or.inl (a.air n (by omega) h2))
        (s - u) (by omega)
      rw [show u + (s - u) = s by omega] at hcap
      have hD := inD_at r H (n := s) (by omega) (by omega)
      have hF : ∀ j, s ≤ j → j < s + (r.t0 - s) → Follow sy m r.fr j := fun j h1 h2 =>
        hfol j (by omega) (by omega) (by omega)
      have h1 := hdist_seg s (r.t0 - s) hF
      rw [show s + (r.t0 - s) = r.t0 by omega] at h1
      have hsplit : seg r.fr.inp s (r.t0 - s) = seg r.fr.inp s (a.L - s) ++ seg r.fr.inp a.L (r.t0 - a.L) := by
        rw [show r.t0 - s = (a.L - s) + (r.t0 - a.L) by omega, seg_add, show s + (a.L - s) = a.L by omega]
      rw [hsplit] at h1
      have h2 := landing_bound H.air (r.fr.hs s) hD hcap (seg r.fr.inp s (a.L - s)) (seg r.fr.inp a.L (r.t0 - a.L))
        (mem_seg (P := fun i => i ∈ inputs ∧ isAir i = true) fun j h3 h4 =>
          ⟨(hF j h3 (by omega)).1, a.air j (by omega) (by omega)⟩)
        (mem_seg (P := fun i => i ∈ inputs) fun j h3 h4 => (hF j (by omega) (by omega)).1)
      rw [length_seg, length_seg] at h2
      have hp := hn.slow_pairs
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨⟨⟨_, hq3⟩, hq4⟩, hq5⟩ := hp q hq
      have h3 := pair_bound (sy := sy) (m := m) hA (q1 := q.1) (q2 := q.2) (S0 := r.C + N.fall + 1 + q.1)
        (L0 := r.C + N.fall + 1 + q.2) (s := s) (L := a.L) (t := r.t0) (G := r.C + N.goalF) (by omega) hq4 (by omega) (by omega)
        hsL hLt ht
      rw [show r.C + N.goalF - (r.C + N.fall + 1 + q.2) = N.goalF - (N.fall + 1 + q.2) by omega] at h3
      have h4 := hleft s (by omega) (Nat.le_refl s)
      omega
    | true =>
      -- a fast takeoff: the search of `FastTakeoff` with `rise` low air frames
      exact fast_short r H hE hw hs a ht hf hearly (L' := N.rise) (Nat.le_refl _) H.roomOk (fun n h1 h2 => hleft n h1 (by omega))
  · -- the last low frame is not `LowAt`: a big player past the corner there
    have hsz : sz = 0 := by
      rcases alow s (by omega) (Nat.le_refl _) with h | ⟨h, _, _⟩
      · exact absurd h hLs
      · exact h
    have hr1 := H.roomBig.1
    have hleft1 : ∀ n, r.C ≤ n → n ≤ s - 1 → r.fr.P n < cornerP sy := fun n h1 h2 =>
      left_at r H hs (w := s - 1) (by omega) (fun j h3 h4 => hlowlt j h3 (by omega)) h1 h2
    cases hf : a.x.fast with
    | false =>
      by_cases hT0 : a.T1 = r.C + N.fall
      · -- a slow takeoff on the first frame after the fall: the search of `LandDist` from the room's first frame to the frame `T1 + q.1`, then the air
        -- frames to the landing and the table of the frames after it (`Checks.slowLand`)
        rw [hf] at hq
        simp only [Bool.false_eq_true, if_false] at hq
        have hp := hn.slow_pairs
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨⟨⟨hq0, hq3⟩, hq4⟩, _⟩ := hp q hq
        let s2 := a.T1 + q.1
        have E := early_of r H (Nat.le_of_lt hE) hw a hearly
        have hF : ∀ j, r.C ≤ j → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 => by
          by_cases h3 : j + 1 < r.C + N.hitF
          · exact E.follow j h1 h3
          · exact hfol j (by omega) h1 h2
        -- the run up to `s2` is covered by the search
        have hgo1 : go sy m ((room sy N).s0, r.fr.P r.C) (seg r.fr.inp r.C N.fall) = (r.fr.hs (r.C + N.fall), r.fr.P (r.C + N.fall)) := by
          have h1 := go_seg (fr := r.fr) (sy := sy) (m := m) r.C N.fall (fun j h2 h3 => hF j h2 (by omega))
          rw [r.start] at h1
          exact h1
        have hseg : seg r.fr.inp r.C N.fall ++ r.fr.inp (a.T1 + 1) :: seg r.fr.inp (a.T1 + 1) (q.1 - 1) =
            seg r.fr.inp r.C (N.fall + (q.1 - 1 + 1)) := by
          rw [seg_add, hT0]
          rfl
        have hgo2 : go sy m ((room sy N).s0, r.fr.P r.C) (seg r.fr.inp r.C N.fall ++ r.fr.inp (a.T1 + 1) :: seg r.fr.inp (a.T1 + 1) (q.1 - 1)) =
            (r.fr.hs s2, r.fr.P s2) := by
          rw [hseg]
          have h1 := go_seg (fr := r.fr) (sy := sy) (m := m) r.C (N.fall + (q.1 - 1 + 1)) (fun j h2 h3 => hF j h2 (by omega))
          rw [r.start, show r.C + (N.fall + (q.1 - 1 + 1)) = s2 by omega] at h1
          exact h1
        have hlow : Low sy m (room sy N).cp (go sy m ((room sy N).s0, r.fr.P r.C) (seg r.fr.inp r.C N.fall))
            (r.fr.inp (a.T1 + 1) :: seg r.fr.inp (a.T1 + 1) (q.1 - 1)) := by
          rw [hgo1, hT0]
          exact low_seg (sy := sy) (m := m) (fr := r.fr) (cp := cornerP sy) (r.C + N.fall) (q.1 - 1 + 1)
            (fun j h2 h3 => hF j (by omega) (by omega)) (fun j h2 h3 => hleft1 (j + 1) (by omega) (by omega))
        have hcov := LandDist.search_cov (sy := sy) (m := m) H.normI (R := room sy N) r.startP0 r.startP1
          (mem_seg (P := AirIn) fun j h1 h2 => E.fall_in j h1 h2) (length_seg _ _ _) E.jump_in
          (mem_seg (P := fun i => i ∈ inputs ∧ isAir i = true) fun j h1 h2 => ⟨(hF j (by omega) (by omega)).1, a.air j (by omega) (by omega)⟩) hlow
        rw [hgo2, length_seg] at hcov
        -- below the threshold at `s2`
        obtain ⟨u, hu1, hu2, hc0⟩ : ∃ u, a.T1 ≤ u ∧ u ≤ a.T1 + 1 ∧ capped sy (r.fr.hs u) = true := by
          rcases r.ab_of a.T1 (by omega) (by omega) with h2 | ⟨h2, _⟩
          · have h1 := a.x_ab
            rw [hf] at h1
            have h3 : ¬sy.AirFastSpeed.toNat ≤ r.fr.ab a.T1 := by simpa using h1.symm
            refine ⟨a.T1, Nat.le_refl _, by omega, ?_⟩
            simp only [capped, decide_eq_true_eq]
            omega
          · exact ⟨a.T1 + 1, by omega, Nat.le_refl _, capped_of_stop r H h2⟩
        have hcap := capped_along r H (u := u) (w := a.L) (by omega) hLt hc0 (fun n h1 h2 => Or.inl (a.air n (by omega) h2))
          (s2 - u) (by omega)
        rw [show u + (s2 - u) = s2 by omega] at hcap
        have hD := inD_at r H (n := s2) (by omega) (by omega)
        -- the frames from `s2`: air frames to the landing, then the frames after it
        have hF2 : ∀ j, s2 ≤ j → j < s2 + (r.t0 - s2) → Follow sy m r.fr j := fun j h1 h2 => hF j (by omega) (by omega)
        have h1 := hdist_seg s2 (r.t0 - s2) hF2
        rw [show s2 + (r.t0 - s2) = r.t0 by omega] at h1
        have hsplit : seg r.fr.inp s2 (r.t0 - s2) = seg r.fr.inp s2 (a.L - s2) ++ seg r.fr.inp a.L (r.t0 - a.L) := by
          rw [show r.t0 - s2 = (a.L - s2) + (r.t0 - a.L) by omega, seg_add, show s2 + (a.L - s2) = a.L by omega]
        rw [hsplit] at h1
        have h2 := LandDist.slow_short H.air H.slowLand hq (x := (r.fr.hs s2, r.fr.P s2)) hcov hD hcap (hleft1 s2 (by omega) (by omega))
          (seg r.fr.inp s2 (a.L - s2)) (seg r.fr.inp a.L (r.t0 - a.L))
          (mem_seg (P := fun i => i ∈ inputs ∧ isAir i = true) fun j h3 h4 => ⟨(hF2 j h3 (by omega)).1, a.air j (by omega) (by omega)⟩)
          (mem_seg (P := fun i => i ∈ inputs) fun j h3 h4 => (hF2 j (by omega) (by omega)).1)
          (by rw [length_seg]; simp only [LandDist.bOf]; omega) (by rw [length_seg, length_seg]; simp only [LandDist.kOf]; omega)
        have h5 : (room sy N).goal = goalP sy := rfl
        dsimp only at h2
        omega
      · -- a later slow takeoff: the air speed cap from the frame before the last low frame, one frame more in the air, the landing one frame later
        rw [hf] at hq
        simp only [Bool.false_eq_true, if_false] at hq
        have hp := hn.slow_pairs
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨⟨⟨_, hq3⟩, hq4⟩, hq5⟩ := hp q hq
        let s' := s - 1
        have hs'1 : a.T1 + 1 ≤ s' := by omega
        obtain ⟨u, hu1, hu2, hc0⟩ : ∃ u, a.T1 ≤ u ∧ u ≤ a.T1 + 1 ∧ capped sy (r.fr.hs u) = true := by
          rcases r.ab_of a.T1 (by omega) (by omega) with h2 | ⟨h2, _⟩
          · have h1 := a.x_ab
            rw [hf] at h1
            have h3 : ¬sy.AirFastSpeed.toNat ≤ r.fr.ab a.T1 := by simpa using h1.symm
            refine ⟨a.T1, Nat.le_refl _, by omega, ?_⟩
            simp only [capped, decide_eq_true_eq]
            omega
          · exact ⟨a.T1 + 1, by omega, Nat.le_refl _, capped_of_stop r H h2⟩
        have hcap := capped_along r H (u := u) (w := a.L) (by omega) hLt hc0 (fun n h1 h2 => Or.inl (a.air n (by omega) h2))
          (s' - u) (by omega)
        rw [show u + (s' - u) = s' by omega] at hcap
        have hD := inD_at r H (n := s') (by omega) (by omega)
        have hF : ∀ j, s' ≤ j → j < s' + (r.t0 - s') → Follow sy m r.fr j := fun j h1 h2 =>
          hfol j (by omega) (by omega) (by omega)
        have h1 := hdist_seg s' (r.t0 - s') hF
        rw [show s' + (r.t0 - s') = r.t0 by omega] at h1
        have hsplit : seg r.fr.inp s' (r.t0 - s') = seg r.fr.inp s' (a.L - s') ++ seg r.fr.inp a.L (r.t0 - a.L) := by
          rw [show r.t0 - s' = (a.L - s') + (r.t0 - a.L) by omega, seg_add, show s' + (a.L - s') = a.L by omega]
        rw [hsplit] at h1
        have h2 := landing_bound H.air (r.fr.hs s') hD hcap (seg r.fr.inp s' (a.L - s')) (seg r.fr.inp a.L (r.t0 - a.L))
          (mem_seg (P := fun i => i ∈ inputs ∧ isAir i = true) fun j h3 h4 =>
            ⟨(hF j h3 (by omega)).1, a.air j (by omega) (by omega)⟩)
          (mem_seg (P := fun i => i ∈ inputs) fun j h3 h4 => (hF j (by omega) (by omega)).1)
        rw [length_seg, length_seg] at h2
        have h3 := pair_bound (sy := sy) (m := m) hA (q1 := q.1) (q2 := q.2 + 1) (S0 := r.C + N.fall + 1 + q.1)
          (L0 := r.C + N.fall + 2 + q.2) (s := s') (L := a.L) (t := r.t0) (G := r.C + N.goalF) (by omega) (by omega) (by omega) (by omega)
          (by omega) hLt ht
        rw [show r.C + N.goalF - (r.C + N.fall + 2 + q.2) = N.goalF - (N.fall + 2 + q.2) by omega] at h3
        have hB := H.roomBig.2.2
        simp only [slowBigOk, List.all_eq_true, decide_eq_true_eq] at hB
        have h5 := hB q hq
        have h4 := hleft1 s' (by omega) (Nat.le_refl _)
        omega
    | true =>
      -- the frames before the last low frame are left of the corner, and a fast jump has at least `rise` low air frames
      have hq' : N.rise ≤ a.u.low := by omega
      have hleft := hleft1
      exact fast_short r H hE hw hs a ht hf hearly (L' := N.rise - 1) (by omega) H.roomBig.2.1 (fun n h1 h2 => hleft n h1 (by omega))

/-- **The entry is not before `t0`**: on the entry frame he is at the mouth (`mouth`), past the goal, and before `t0` he is not past the goal. The way off the block puts the
entry after first control. So the frames that the proof asks to be `VFrame` are before the entry. -/
theorem t0_le_E (H : Checks sy m N) (off : Off sy m N r.fr r.C r.t0 r.E) : r.t0 ≤ r.E := by
  have hm := r.mouth
  have hs := H.nums.slow_mouth
  have hA := H.nums.air_pos
  have h0 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (N.aboveS : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) (by omega)) (by omega)
  cases off with
  | jump T1 n F x u T1_ge x_mem reach floor hF F_le above slowJ =>
    by_cases h : r.t0 ≤ r.E
    · exact h
    · exfalso
      have h1 := r.first r.E (by omega) (by omega)
      omega
  | step F f d f_mem hF F_le => omega

/-- **The entry comes after `t0`**: a jump off the block reaches the floor `aboveS` or `aboveF` frames after he was last above it, and stepping off takes `walk`
frames, each at least one frame more than he needs to get past the block's end -/
theorem t0_lt_E (H : Checks sy m N) (off : Off sy m N r.fr r.C r.t0 r.E) : r.t0 < r.E := by
  have hn := H.nums
  have hv := hn.vf
  cases off with
  | jump T1 n F x u T1_ge x_mem reach floor hF F_le above slowJ =>
    have hle : n ≤ arcFrames := by
      have h0 := arc_len H.lenB x_mem reach hn.len_ok.2.2.1 hn.len_ok.2.2.1
      simp only [ite_self] at h0
      have := hn.len_ok.2.2.1
      omega
    have h1 := arc_spec H.drop x x_mem n u hle reach
    obtain ⟨_, h3⟩ := arc_k reach
    have hfl : (falling u.s && decide (groundY sy ≤ u.s.y.toNat)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact floor
    unfold dropOk at h1
    rw [hfl, h3] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    cases hf : x.fast with
    | true =>
      rw [hf] at h1
      simp only [if_true, decide_eq_true_eq] at h1
      omega
    | false =>
      rw [hf] at h1
      simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at h1
      omega
  | step F f d f_mem hF F_le =>
    have hw2 := H.walk
    simp only [walkOk, List.all_eq_true, decide_eq_true_eq] at hw2
    have h1 := hw2 f f_mem d (mem_bytes d)
    omega

/-- he is not past the block's right end by frame `C + goalF` -/
theorem past_late (H : Checks sy m N) : r.C + N.goalF < r.t0 := by
  by_cases ht : r.t0 ≤ r.C + N.goalF
  · exfalso
    cases hw : r.way with
    | over o => exact no_landing r H o
    | onto a off =>
      have hE := t0_lt_E r H off
      by_cases hstop : ∃ h, r.C + N.hitF ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h
      · obtain ⟨h, h1, h2, h3⟩ := hstop
        have h4 := stop_short r H hE h1 h2 h3 ht
        have h5 := r.past
        omega
      · have hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n := fun n h1 h2 h3 => hstop ⟨n, h1, h2, h3⟩
        by_cases hnw : NoWall sy m N r.fr r.C
        · exact landed_short r H hE hnw hs (a hnw hs) ht
        · have h4 := wall_short r H hs hnw ht
          have h5 := r.past
          omega
  · omega

/-! ### Off the block -/

/-- a slow jump: at most the air speed on every frame -/
theorem slow_move (H : Checks sy m N) {u F : Nat} (hc : capped sy (r.fr.hs u) = true) (hD : inD sy (r.fr.hs u) = true)
    (hfr : ∀ i, u ≤ i → i < F → (Follow sy m r.fr i ∧ isAir (r.fr.inp (i + 1)) = true) ∨ Moved sy r.fr i) :
    ∀ d, u + d ≤ F → capped sy (r.fr.hs (u + d)) = true ∧ inD sy (r.fr.hs (u + d)) = true ∧
      r.fr.P (u + d) ≤ r.fr.P u + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (d : Int)
  | 0, _ => ⟨hc, hD, by simp⟩
  | d + 1, h => by
    obtain ⟨h1, h2, h3⟩ := slow_move H hc hD hfr d (by omega)
    have hm : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((d + 1 : Nat) : Int) =
        16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (d : Int) + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [show u + (d + 1) = u + d + 1 by omega, hm]
    rcases hfr (u + d) (by omega) (by omega) with ⟨h4, h5⟩ | ⟨h4, h5, h6⟩
    · obtain ⟨h7, h8, h9⟩ := h4
      have h10 : capped sy (r.fr.hs (u + d + 1)) = true := by
        rw [h8]
        rcases step_cap H.air h2 h1 h7 with h11 | ⟨h11, _⟩
        · exact h11
        · rw [h5] at h11
          exact absurd h11 (by decide)
      refine ⟨h10, ?_, ?_⟩
      · rw [h8]
        exact (FastTakeoff.step_facts H.air.pot h2 h7).1
      · simp only [capped, decide_eq_true_eq] at h10
        omega
    · exact ⟨h4, h5, by omega⟩

/-- **The bonus room.** From a run and the checks: the entry comes at least `goalF + aboveF` frames after first control -/
theorem entry_ge (H : Checks sy m N) : r.C + N.goalF + N.aboveF ≤ r.E := by
  have hN := past_late r H
  have hn := H.nums
  cases hw : r.way with
  | over o => exact (no_landing r H o).elim
  | onto _ off =>
    cases off with
    | jump T1 n F x u T1_ge x_mem reach floor hF F_le above slowJ =>
      have hlen := arc_len H.lenB x_mem reach hn.len_ok.2.2.1 hn.len_ok.2.2.1
      simp only [ite_self] at hlen
      have hle : n ≤ arcFrames := by
        have := hn.len_ok.2.2.1
        omega
      have h1 := arc_spec H.drop x x_mem n u hle reach
      obtain ⟨h2, h3⟩ := arc_k reach
      have h4 := arcStart_k x_mem
      have hfl : (falling u.s && decide (groundY sy ≤ u.s.y.toNat)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact floor
      unfold dropOk at h1
      rw [hfl, h3] at h1
      simp only [Bool.not_true, Bool.false_or] at h1
      cases hf : x.fast with
      | true =>
        rw [hf] at h1
        simp only [if_true, decide_eq_true_eq] at h1
        omega
      | false =>
        rw [hf] at h1
        simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at h1
        by_cases hE : r.C + N.goalF + N.aboveF ≤ r.E
        · exact hE
        · exfalso
          have hab := hn.above_le
          have hag := hn.air_ge
          have hFE : F = r.E := by omega
          have hFv : F = r.C + N.goalF + N.aboveS := by omega
          have hT1 : T1 ≤ r.C + N.goalF := by omega
          obtain ⟨hc, hfr⟩ := slowJ hf hFE
          have hD := inD_at r H T1_ge (by omega)
          obtain ⟨h5, h6, _⟩ := slow_move r H hc hD hfr (r.C + N.goalF - T1) (by omega)
          rw [show T1 + (r.C + N.goalF - T1) = r.C + N.goalF by omega] at h5 h6
          obtain ⟨_, _, h7⟩ := slow_move r H h5 h6 (F := F) (fun i h8 h9 => hfr i (by omega) h9) N.aboveS (by omega)
          rw [← hFv, hFE] at h7
          have h8 := r.first (r.C + N.goalF) (by omega) hN
          have h9 := r.mouth
          have h10 := hn.slow_mouth
          omega
    | step F f d f_mem hF F_le =>
      have hw2 := H.walk
      simp only [walkOk, List.all_eq_true, decide_eq_true_eq] at hw2
      have h1 := hw2 f f_mem d (mem_bytes d)
      have h3 := hn.walk_le
      omega

end RoomCore

/-! ## The check of the first fall -/

theorem fallLayer_shift (L : List VS) : ∀ e, fallLayer sy m (fallNext sy m L) e = fallLayer sy m L (e + 1)
  | 0 => rfl
  | e + 1 => by
    show fallNext sy m (fallLayer sy m (fallNext sy m L) e) = fallNext sy m (fallLayer sy m L (e + 1))
    rw [fallLayer_shift L e]

theorem fallRun_spec : ∀ (k d : Nat) (L : List VS), fallRun sy m N k d L = true → ∀ e, e < k → ∀ s ∈ fallLayer sy m L e, fallOk sy m N (d + e) s
  | 0, _, _, _, e, he, _, _ => absurd he (Nat.not_lt_zero _)
  | k + 1, d, L, h, e, he, s, hs => by
    simp only [fallRun, Bool.and_eq_true, List.all_eq_true] at h
    cases e with
    | zero => exact h.1 s hs
    | succ e =>
      rw [← fallLayer_shift] at hs
      have h2 := fallRun_spec k (d + 1) (fallNext sy m L) h.2 e (by omega) s hs
      rwa [show d + 1 + e = d + (e + 1) by omega] at h2

/-- what the check of the first fall gives -/
theorem fall_ok (h : fallCheck sy m N = true) : 0 < N.fall ∧ N.fall < N.standF ∧ (room sy N).P1 + 16 * (top sy : Int) * (N.standF : Int) < goalP sy ∧
    ∀ d, d < N.standF → ∀ s ∈ fallLayer sy m N.vStart d, fallOk sy m N d s := by
  simp only [fallCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun d hd s hs => ?_⟩
  have h5 := fallRun_spec N.standF 0 N.vStart h4 d hd s hs
  rwa [Nat.zero_add] at h5

theorem vdropB_spec {s t : VS} (h : vdropB s t = true) : VDrop s t := by
  simp only [vdropB, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem fallStep_spec {d : Nat} {s : VS} {a : Bool} (h : fallStep sy m N d s a = true) :
    (vstepR sy m s a).st = 2 ∧ VDrop s (vstepR sy m s a) ∧ (falling (vstepR sy m s a) = true → VDrop s (VertAir.land (vstepR sy m s a))) ∧
    (d + 1 < N.fall → falling (vstepR sy m s a) = true → (VertAir.land (vstepR sy m s a)).y.toNat ≠ groundY sy) ∧
    (d + 1 = N.fall → falling (vstepR sy m s a) = true ∧ (VertAir.land (vstepR sy m s a)).y.toNat = groundY sy) := by
  unfold fallStep at h
  generalize vstepR sy m s a = t at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, vdropB_spec h2, fun hf => ?_, fun hd hf => ?_, fun hd => ?_⟩
  · rcases h3 with h3 | h3
    · rw [hf] at h3
      cases h3
    · exact vdropB_spec h3
  · rcases h4 with (h4 | h4) | h4
    · omega
    · rw [hf] at h4
      cases h4
    · exact h4
  · rcases h5 with h5 | h5
    · exact absurd hd h5
    · exact h5

theorem fallOk_spec {d : Nat} {s : VS} (h : fallOk sy m N d s = true) : s.st = 2 ∧ ∀ a, fallStep sy m N d s a = true := by
  simp only [fallOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun a => ?_⟩
  cases a
  · exact h3
  · exact h2

theorem mem_fallNext {L : List VS} {s : VS} (hs : s ∈ L) (a : Bool) : vstepR sy m s a ∈ fallNext sy m L := by
  refine List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨s, hs, ?_⟩)
  cases a <;> simp

theorem njStep_eq (s : VS) : njStep sy m s = (noJumpOk sy m s, noJumpNext sy m s) := by
  unfold njStep noJumpOk noJumpNext
  by_cases h : s.st == 0
  · simp [h]
  · simp only [h, Bool.false_or]
    simp [List.all_cons, List.all_nil, Bool.and_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem njAdd_spec (H : Std.HashSet VS) (F : List VS) (L : List VS) :
    (∀ x, H.contains x = true → (njAdd H F L).1.contains x = true) ∧ (∀ t ∈ L, (njAdd H F L).1.contains t = true) ∧
    (∀ x, (njAdd H F L).1.contains x = true → H.contains x = true ∨ x ∈ (njAdd H F L).2) ∧
    (∀ x ∈ (njAdd H F L).2, x ∈ F ∨ (njAdd H F L).1.contains x = true) ∧ (∀ x ∈ F, x ∈ (njAdd H F L).2) := by
  induction L generalizing H F with
  | nil => exact ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil, fun _ h => Or.inl h, fun _ h => Or.inl h, fun _ h => h⟩
  | cons t L ih =>
    unfold njAdd
    split
    · rename_i hc
      obtain ⟨a1, a2, a3, a4, a5⟩ := ih H F
      refine ⟨a1, fun u hu => ?_, a3, a4, a5⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact a1 _ hc
      · exact a2 u hu
    · obtain ⟨a1, a2, a3, a4, a5⟩ := ih (H.insert t) (t :: F)
      have hin : ∀ x, H.contains x = true → (H.insert t).contains x = true := fun x hx => by
        rw [Std.HashSet.contains_insert]; simp [hx]
      have hself : (H.insert t).contains t = true := by rw [Std.HashSet.contains_insert]; simp
      refine ⟨fun x hx => a1 x (hin x hx), fun u hu => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => a5 x (List.mem_cons_of_mem _ hx)⟩
      · rcases List.mem_cons.1 hu with rfl | hu
        · exact a1 _ hself
        · exact a2 u hu
      · rcases a3 x hx with h1 | h1
        · rw [Std.HashSet.contains_insert] at h1
          simp only [Bool.or_eq_true, beq_iff_eq] at h1
          rcases h1 with rfl | h1
          · exact Or.inr (a5 _ List.mem_cons_self)
          · exact Or.inl h1
        · exact Or.inr h1
      · rcases a4 x hx with h1 | h1
        · rcases List.mem_cons.1 h1 with rfl | h1
          · exact Or.inr (a1 _ hself)
          · exact Or.inl h1
        · exact Or.inr h1

/-- a state seen by frame `d` whose frame is done: it meets `noJumpOk`, it is not on the floor if `d < fall`, and its next states are in `H` -/
def NjDone (sy : Syms) (m : Machine) (N : Nums) (H : Std.HashSet VS) (d : Nat) (x : VS) : Prop :=
  noJumpOk sy m x = true ∧ (d < N.fall → ¬OnFloor sy x) ∧ ∀ t ∈ noJumpNext sy m x, H.contains t = true

theorem not_onFloor_of {s : VS} (h : onFloorB sy s = false) : ¬OnFloor sy s := fun hf => by
  have : onFloorB sy s = true := by
    unfold onFloorB
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨hf.1, hf.2⟩
  rw [this] at h
  cases h

/-- **What the check frame by frame gives**: every sequence of states that starts in `H` at frame `d` and goes from each state to one of its next states meets `noJumpOk`
at each frame up to `d + k`, and is not on the floor before `fall`. `H` holds `F`, and every state of `H` is in `F` or done -/
theorem njRun_sound : ∀ (k d : Nat) (H : Std.HashSet VS) (F : List VS), njRun sy m N k d H F = true → (∀ x ∈ F, H.contains x = true) →
    (∀ x, H.contains x = true → x ∈ F ∨ NjDone sy m N H d x) →
    ∀ (q : Nat → VS) (n : Nat), d ≤ n → n < d + k → H.contains (q d) = true → (∀ j, d ≤ j → j < n → q (j + 1) ∈ noJumpNext sy m (q j)) →
      noJumpOk sy m (q n) = true ∧ (n < N.fall → ¬OnFloor sy (q n))
  | 0, _, _, _, _, _, _, _, _, h1, h2, _, _ => absurd h2 (by omega)
  | k + 1, d, H, F, h, hF, hI, q, n, h1, h2, h3, h4 => by
    unfold njRun at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
    obtain ⟨hall, hrest⟩ := h
    generalize hL : (F.map fun s => (s, njStep sy m s)).flatMap (fun g => g.2.2) = L at hrest
    obtain ⟨a1, a2, a3, a4, _⟩ := njAdd_spec H [] L
    -- a state of `F` is done now
    have doneF : ∀ x ∈ F, NjDone sy m N (njAdd H [] L).1 d x := by
      intro x hx
      have e := hall x hx
      rw [njStep_eq] at e
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at e
      obtain ⟨e1, e2⟩ := e
      refine ⟨e1, fun hd => ?_, fun t ht => a2 t ?_⟩
      · rcases e2 with e2 | e2
        · exact absurd e2 (by omega)
        · exact not_onFloor_of e2
      · rw [← hL]
        refine List.mem_flatMap.2 ⟨(x, njStep sy m x), List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
        rw [njStep_eq]
        exact ht
    have mono : ∀ x, NjDone sy m N H d x → NjDone sy m N (njAdd H [] L).1 (d + 1) x := fun x ⟨b1, b2, b3⟩ =>
      ⟨b1, fun hd => b2 (by omega), fun t ht => a1 t (b3 t ht)⟩
    have doneH : ∀ x, H.contains x = true → NjDone sy m N (njAdd H [] L).1 d x := by
      intro x hx
      rcases hI x hx with h5 | h5
      · exact doneF x h5
      · exact ⟨h5.1, h5.2.1, fun t ht => a1 t (h5.2.2 t ht)⟩
    by_cases hn : n = d
    · subst hn
      exact ⟨(doneH _ h3).1, (doneH _ h3).2.1⟩
    · have hq : (njAdd H [] L).1.contains (q (d + 1)) = true := (doneH _ h3).2.2 _ (h4 d (Nat.le_refl _) (by omega))
      refine njRun_sound k (d + 1) _ _ hrest (fun x hx => ?_) (fun x hx => ?_) q n (by omega) (by omega) hq (fun j hj1 hj2 => h4 j (by omega) hj2)
      · rcases a4 x hx with h5 | h5
        · exact absurd h5 List.not_mem_nil
        · exact h5
      · rcases a3 x hx with h5 | h5
        · rcases hI x h5 with h6 | h6
          · exact Or.inr ⟨(doneF x h6).1, fun hd => (doneF x h6).2.1 (by omega), (doneF x h6).2.2⟩
          · exact Or.inr (mono x h6)
        · exact Or.inl h5

/-- **What the check of the frames with no jump gives**: a sequence of states from a state at first control, from each state to one of its next states, meets `noJumpOk`
at each frame `n` with `n + 1 < standF`, and is not on the floor before `fall` -/
theorem noJump_ok (h : noJumpCheck sy m N = true) (q : Nat → VS) (h0 : q 0 ∈ N.vStart) {n : Nat} (hn : n + 1 < N.standF)
    (hq : ∀ j, j < n → q (j + 1) ∈ noJumpNext sy m (q j)) : noJumpOk sy m (q n) = true ∧ (n < N.fall → ¬OnFloor sy (q n)) := by
  have hc : ∀ x, (Std.HashSet.ofList N.vStart).contains x = true ↔ x ∈ N.vStart := fun x => by
    rw [Std.HashSet.contains_ofList]
    exact List.elem_iff
  exact njRun_sound (N.standF - 1) 0 _ _ h (fun x hx => (hc x).2 hx) (fun x hx => Or.inl ((hc x).1 hx)) q n (Nat.zero_le _) (by omega) ((hc _).2 h0)
    (fun j _ hj => hq j hj)

/-- a state in the air one frame later with no jump: `vstepR`, or its landing if it falls -/
theorem mem_noJumpNext_air {s t : VS} {a : Bool} (hs : s.st ≠ 0)
    (h : t = vstepR sy m s a ∨ (falling (vstepR sy m s a) = true ∧ t = VertAir.land (vstepR sy m s a))) : t ∈ noJumpNext sy m s := by
  have e : (s.st == 0) = false := by simpa using hs
  unfold noJumpNext
  rw [e, if_neg (by decide)]
  refine List.mem_flatMap.2 ⟨a, by cases a <;> simp, ?_⟩
  simp only
  rcases h with rfl | ⟨hf, rfl⟩
  · split <;> simp
  · rw [if_pos hf]
    simp

/-- a state standing one frame later with no jump: as `StandNext` allows -/
theorem mem_noJumpNext_stand {s t : VS} (hs : s.st = 0) (h : StandNext s t) : t ∈ noJumpNext sy m s := by
  unfold noJumpNext
  rw [hs, if_pos (by decide)]
  refine List.mem_flatMap.2 ⟨t.prevA, by cases t.prevA <;> simp, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨y, mf, vy, dummy, vf, vfd, origin, st, pa⟩ := t
  obtain ⟨y', mf', vy', dummy', vf', vfd', origin', st', pa'⟩ := s
  simp only at h1 h2 h3 h4 h5 hs ⊢
  subst h1 h2 h3 h4 hs
  rcases h5 with ⟨e1, e2, e3, e4 | e4⟩ | ⟨e1, e2, e3, e4⟩
  · subst e1 e2 e3 e4
    simp
  · subst e1 e2 e3 e4
    simp
  · subst e1 e2 e3 e4
    simp [VertAir.land]

/-! ### The frames from the first stand on, with any input -/

theorem offTable_get (i : Nat) (h : i < 16) : (offTable sy m)[i]! = offRow sy m i := by
  have hs : i < (offTable sy m).size := by
    unfold offTable
    rw [Array.size_ofFn]
    exact h
  rw [getElem!_pos (offTable sy m) i hs]
  unfold offTable
  rw [Array.getElem_ofFn]

theorem row_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x0F = 0 →
    (UInt8.ofNat n.val >>> 4).toNat < 16 ∧ UInt8.ofNat (16 * (UInt8.ofNat n.val >>> 4).toNat) = UInt8.ofNat n.val := by decide +kernel

/-- the takeoff from the height `y` with any stored speed is one of `jumpOffs y` -/
theorem mem_jumpOffs (y abs : UInt8) : jumpOffR sy m y abs ∈ jumpOffs sy m y := by
  refine List.mem_eraseDups.2 (List.mem_map.2 ⟨abs.toNat, List.mem_range.2 abs.toNat_lt, ?_⟩)
  show jumpOffR sy m y (UInt8.ofNat abs.toNat) = _
  rw [UInt8.ofNat_toNat]

/-- a takeoff from a stand on a whole row is a next state -/
theorem mem_anyNext_jump {s : VS} (hs : s.st = 0) (hy : s.y &&& 0x0F = 0) (abs : UInt8) : jumpOffR sy m s.y abs ∈ anyNext sy m (offTable sy m) s := by
  have h := row_all ⟨s.y.toNat, s.y.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  obtain ⟨h1, h2⟩ := h hy
  unfold anyNext
  rw [hs, if_pos (by decide), offTable_get _ h1]
  refine List.mem_append_right _ ?_
  show jumpOffR sy m s.y abs ∈ jumpOffs sy m (UInt8.ofNat (16 * (s.y >>> 4).toNat))
  rw [h2]
  exact mem_jumpOffs s.y abs

/-- a next state with no jump is a next state with any input -/
theorem mem_anyNext_of {T : Array (List VS)} {s t : VS} (h : t ∈ noJumpNext sy m s) : t ∈ anyNext sy m T s := List.mem_append_left _ h

theorem anyOk_spec {s : VS} (h : anyOk sy s = true) : ¬OnFloor sy s ∧ (s.st = 0 → s.y &&& 0x0F = 0) := by
  simp only [anyOk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  refine ⟨not_onFloor_of h.1, fun h0 => ?_⟩
  rcases h.2 with e | e
  · exact absurd h0 e
  · exact e

/-- the landing of a state one frame after a state of the layer `L` is in `fallLands L` -/
theorem mem_fallLands {L : List VS} {s : VS} (hs : s ∈ L) {a : Bool} (hf : falling (vstepR sy m s a) = true) :
    VertAir.land (vstepR sy m s a) ∈ fallLands sy m L := by
  refine List.mem_flatMap.2 ⟨s, hs, List.mem_flatMap.2 ⟨a, by cases a <;> simp, ?_⟩⟩
  rw [if_pos hf]
  exact List.mem_singleton.2 rfl

/-- a state seen whose frame is done: it meets `anyOk`, and its next states are in `H` -/
def AjDone (sy : Syms) (m : Machine) (T : Array (List VS)) (H : Std.HashSet VS) (x : VS) : Prop :=
  anyOk sy x = true ∧ ∀ t ∈ anyNext sy m T x, H.contains t = true

/-- **What the check frame by frame gives**: a sequence of states that at a frame `d'` is in `H` (if `d' = d`) or is a landing of the first fall's layer of frame
`d' − 1` (if `d < d'` and `wallF ≤ d'`), and from there goes from each state to one of its next states, meets `anyOk` at each frame from `d'` up to `d + k − 1`. `Lf` is
the layer of the first fall at frame `d`, `H` holds `F`, and every state of `H` is in `F` or done -/
theorem ajRun_sound {T : Array (List VS)} : ∀ (k d : Nat) (Lf : List VS) (H : Std.HashSet VS) (F : List VS), ajRun sy m N T k d Lf H F = true →
    Lf = fallLayer sy m N.vStart d → (∀ x ∈ F, H.contains x = true) → (∀ x, H.contains x = true → x ∈ F ∨ AjDone sy m T H x) →
    ∀ (q : Nat → VS) (d' n : Nat), d' ≤ n → n < d + k →
      ((d' = d ∧ H.contains (q d') = true) ∨ (d < d' ∧ N.wallF ≤ d' ∧ q d' ∈ fallLands sy m (fallLayer sy m N.vStart (d' - 1)))) →
      (∀ j, d' ≤ j → j < n → q (j + 1) ∈ anyNext sy m T (q j)) → anyOk sy (q n) = true
  | 0, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, _ => by
    rcases h3 with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
  | k + 1, d, Lf, H, F, h, hL, hF, hI, q, d', n, h1, h2, h3, h4 => by
    unfold ajRun at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hall, hrest⟩ := h
    generalize hLL : (F.flatMap (anyNext sy m T) ++ if N.wallF ≤ d + 1 then fallLands sy m Lf else []) = L at hrest
    obtain ⟨a1, a2, a3, a4, _⟩ := njAdd_spec H [] L
    have doneF : ∀ x ∈ F, AjDone sy m T (njAdd H [] L).1 x := fun x hx =>
      ⟨hall x hx, fun t ht => a2 t (by rw [← hLL]; exact List.mem_append_left _ (List.mem_flatMap.2 ⟨x, hx, ht⟩))⟩
    have doneH : ∀ x, H.contains x = true → AjDone sy m T (njAdd H [] L).1 x := by
      intro x hx
      rcases hI x hx with h5 | h5
      · exact doneF x h5
      · exact ⟨h5.1, fun t ht => a1 t (h5.2 t ht)⟩
    have hL' : fallNext sy m Lf = fallLayer sy m N.vStart (d + 1) := by rw [hL]; rfl
    have hF' : ∀ x ∈ (njAdd H [] L).2, (njAdd H [] L).1.contains x = true := fun x hx => by
      rcases a4 x hx with h5 | h5
      · exact absurd h5 List.not_mem_nil
      · exact h5
    have hI' : ∀ x, (njAdd H [] L).1.contains x = true → x ∈ (njAdd H [] L).2 ∨ AjDone sy m T (njAdd H [] L).1 x := fun x hx => by
      rcases a3 x hx with h5 | h5
      · exact Or.inr (doneH x h5)
      · exact Or.inl h5
    rcases h3 with ⟨e, h3⟩ | ⟨e, hw, h3⟩
    · subst e
      by_cases hn : n = d'
      · subst hn
        exact (doneH _ h3).1
      · have hq : (njAdd H [] L).1.contains (q (d' + 1)) = true := (doneH _ h3).2 _ (h4 d' (Nat.le_refl _) (by omega))
        exact ajRun_sound k (d' + 1) _ _ _ hrest hL' hF' hI' q (d' + 1) n (by omega) (by omega) (Or.inl ⟨rfl, hq⟩) (fun j hj1 hj2 => h4 j (by omega) hj2)
    · by_cases he : d' = d + 1
      · subst he
        have hq : (njAdd H [] L).1.contains (q (d + 1)) = true := by
          refine a2 _ ?_
          rw [← hLL, if_pos hw]
          refine List.mem_append_right _ ?_
          rw [hL]
          rw [Nat.add_sub_cancel] at h3
          exact h3
        exact ajRun_sound k (d + 1) _ _ _ hrest hL' hF' hI' q (d + 1) n h1 (by omega) (Or.inl ⟨rfl, hq⟩) h4
      · exact ajRun_sound k (d + 1) _ _ _ hrest hL' hF' hI' q d' n h1 (by omega) (Or.inr ⟨by omega, hw, h3⟩) h4

/-- **What the check of the frames from the first stand on gives**: a sequence of states that at a frame `d'`, `wallF` or later, is a landing of the first fall's layer of
frame `d' − 1`, and from there goes from each state to one of its next states with any input, meets `anyOk` at each frame from `d'` on before `fall`: not on the floor, and
standing on a whole row -/
theorem any_ok (h : anyCheck sy m N = true) (q : Nat → VS) {d' n : Nat} (hd : 1 ≤ d') (hw : N.wallF ≤ d') (h1 : d' ≤ n) (h2 : n < N.fall)
    (h0 : q d' ∈ fallLands sy m (fallLayer sy m N.vStart (d' - 1))) (hq : ∀ j, d' ≤ j → j < n → q (j + 1) ∈ anyNext sy m (offTable sy m) (q j)) :
    anyOk sy (q n) = true :=
  ajRun_sound N.fall 0 _ _ _ h rfl (fun x hx => absurd hx List.not_mem_nil) (fun x hx => by simp at hx) q d' n h1 (by omega) (Or.inr ⟨by omega, hw, h0⟩) hq

theorem joyOf_mem : ∀ n : Fin 256, FrameModel.joyOf (UInt8.ofNat n.val) ∈ groundInputs := by decide +kernel

/-- **Every input read from a machine is one of `inputs`**: the state 0 or 1, a jump only in the state 0, and the buttons B, Up, Down, Left, Right -/
theorem readIn_mem (sy : Syms) (x : Machine) : FrameModel.readIn sy x ∈ inputs := by
  have hj := joyOf_mem ⟨(peek x sy.SavedJoypadBits).toNat, (peek x sy.SavedJoypadBits).toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at hj
  unfold FrameModel.readIn inputs
  refine List.mem_flatMap.2 ?_
  by_cases h0 : peek x sy.Player_State == 0
  · refine ⟨(0, peek x sy.SavedJoypadBits &&& 0x80 != 0 && peek x sy.PreviousA_B_Buttons &&& 0x80 == 0), ?_, ?_⟩
    · cases (peek x sy.SavedJoypadBits &&& 0x80 != 0 && peek x sy.PreviousA_B_Buttons &&& 0x80 == 0) <;> simp
    · refine List.mem_flatMap.2 ⟨_, hj, ?_⟩
      simp only [h0, if_true, Bool.true_and, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      by_cases hr : peek x sy.RunningTimer == 0
      · exact ⟨0, Or.inl rfl, by simp [hr]⟩
      · exact ⟨1, Or.inr rfl, by simp [hr]⟩
  · refine ⟨(1, false), by simp, List.mem_flatMap.2 ⟨_, hj, ?_⟩⟩
    simp only [Bool.not_eq_true] at h0
    simp only [h0, Bool.false_and, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    by_cases hr : peek x sy.RunningTimer == 0
    · exact ⟨0, Or.inl rfl, by simp [hr]⟩
    · exact ⟨1, Or.inr rfl, by simp [hr]⟩

/-- the first `j` after `a` with `P j`, below `n` -/
theorem first_of {P : Nat → Prop} {a : Nat} : ∀ n, (∃ j, a < j ∧ j < n ∧ P j) → ∃ j, a < j ∧ j < n ∧ P j ∧ ∀ i, a < i → i < j → ¬P i
  | 0, ⟨_, _, h, _⟩ => absurd h (Nat.not_lt_zero _)
  | n + 1, ⟨j, h1, h2, h3⟩ => by
    by_cases h : ∃ j, a < j ∧ j < n ∧ P j
    · obtain ⟨i, i1, i2, i3, i4⟩ := first_of n h
      exact ⟨i, i1, by omega, i3, i4⟩
    · exact ⟨j, h1, h2, h3, fun i hi1 hi2 hi3 => h ⟨i, hi1, by omega, hi3⟩⟩

namespace RoomRun

variable {S : FrameKeep.RealRun} {b lim : Nat} (r : RoomRun sy m N S b lim)

/-- what the walks of the room's frames give (`Route.Run.inRoom`) -/
structure InRoom (r : RoomRun sy m N S b lim) : Prop where
  /-- `E − C` frames from `b` on end not paused by the end of frame `b + lim`: so the room's frames up to `E` are real frames of `S` (`RoomRun.next`) that end not paused
  (`RoomRun.up`). `Route.Run.roomMany` proves it from the counts of `clock` (`chg.hb₁`, `chg.ha₂`) and `roomLag`: in the room a frame that ends paused is a `lag` frame -/
  many : r.E - r.C ≤ r.ups
  /-- the frames between the end of the room's frame `n` and the start of its frame `n + 1` keep what the model reads: the horizontal state, the position and the vertical
  state (`Route.Run.roomKeep`: they end paused, so the walk to the player's routine says that they do not come there and keep the bytes of `RoomVert.vKeepA`) -/
  keep : ∀ n, r.C ≤ n → n < r.E → FrameModel.readHS sy (r.fm n) = FrameModel.readHS sy (r.fe n) ∧ posP sy (r.fm n) = posP sy (r.fe n) ∧
    SurfaceFrames.vsOf sy (r.fm n) = SurfaceFrames.vsOf sy (r.fe n)
  /-- frame `E` ends with the position at or right of the mouth's left end (`SideEntryRest.mouth_of_rows`: the walk of `SideEntryEnd` up to the write, and the walk of the
  room from there to the frame's end) -/
  mouthE : SidePipe.mouthP sy 0 ≤ posP sy (PipeTransition.frame (r.fm (r.E - 1)) (r.pad r.E))
  /-- no frame of the room before the entry comes to the head's collision with a block: neither to its routine nor to the bump on a solid block (`RoomMap.head_of_rows`,
  `RoomMap.bump_of_rows`) -/
  bump : ∀ n, r.C ≤ n → n < r.E → ∀ j, (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc ≠ PipeWrites.headAt sy m ∧
    (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc ≠ SideFrame.bumpAt sy m
  /-- a frame of the room before the entering frame, on a state of a jump's first frames, that comes to the player's routine at `k` in the state `VertAir.AtV` and leaves him
  rising on such a state, follows `vstep` (`RoomVert.air_arc`: the two walks of the room's frames, and the movement routine in the air) -/
  vert : ∀ n, r.C ≤ n → n + 1 < r.E → ∀ k, VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (peek (r.fm n) sy.Player_State = 1 → peek (r.fm n) sy.DiffToHaltJump = 1) →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 →
    VertModel.vsOf sy (r.fm n) ∈ (VertAir.arcSet sy m N.h N.rise).map (·.s) →
    vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∈
      (VertAir.arcSet sy m N.h N.rise).map (·.s) →
    (vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&& 0x80 = 0x80 →
    VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) =
      vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0
  /-- a frame of the room before the entering frame that starts in the air and comes to the player's routine at `k` in the state `VertAir.AtV` follows `vstep` on the
  machine of the player's routine (`vstepR`) up to the landing: `t` is in the air, and the vertical bytes at the frame's end are `t`, or `t` falls and they are its
  landing (`RoomFall.jump_room`: the three walks of the room's frames, and the movement routine in the air) -/
  air : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State ≠ 0 → ∀ k,
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (peek (r.fm n) sy.Player_State = 1 → peek (r.fm n) sy.DiffToHaltJump = 1) →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 →
    ((vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)).st = 1 ∨
     (vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)).st = 2) ∧
    (VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) =
       vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) ∨
     (falling (vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)) = true ∧
      VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) =
        VertAir.land (vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0))))
  /-- a frame of the room before the entering frame that starts standing and comes to the player's routine at `k` with no jump in the input that the model reads there ends
  as `StandNext` allows: the height's fraction, the forces and the jump's origin stay, and the height and the speed stay with the state 0 or 2, or he lands
  (`RoomStand.stand_room`: the walk to the player's routine, and the walk from there standing) -/
  stand : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State = 0 → ∀ k, (PipeEntryRule.trace (r.fm n) (r.inAt n) k).pc = sy.PlayerCtrlRoutine →
    (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) k)).jump = false →
    StandNext (VertModel.vsOf sy (r.fm n)) (VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)))
  /-- at the end of each frame of the room before the entry, in a jump the jump's halt value is 1, and bit 7 of A of the frame before is bit 7 of A (`RoomPair.pair_run`:
  the rows of the change at first control, and two walks of the room's frames). Once the fields `halt` and `prevA` -/
  pair : ∀ n, r.C ≤ n → n < r.E → (peek (r.fm n) sy.Player_State = 1 → peek (r.fm n) sy.DiffToHaltJump = 1) ∧
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80
  /-- the first control comes no later than the entry (`Route.Run.room_le`) -/
  le : r.C ≤ r.E
  /-- each instruction of each frame of the room before the entry that is not at the idle loop runs at least 64 dots before the frame's end (`SiteOK`: the handler is done
  6000 dots before the frame's end), and the idle loop is a `JMP` to itself -/
  time : ∃ idle, FrameModel.idleAt (FrameModel.Rom.of m) idle = true ∧ ∀ n, r.C ≤ n → n < r.E → ∀ j,
    (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc ≠ idle → (PipeEntryRule.trace (r.fm n) (r.inAt n) j).fdot ≤ dotsPerFrame - 64
  /-- each frame of the room before the entry comes to the player's routine before its end (`RoomVert.before_R`: the walk's states at the frame's end are not there) -/
  arrive : ∀ n, r.C ≤ n → n < r.E → ∀ j, (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerCtrlRoutine →
    (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame
  /-- each frame of the room before the entry that ends with the game not paused comes to the player's routine, a first time at `arr n` (`RoomVert.arrive_R`: the walk to
  the player's routine splits the pause byte's low bit where the NMI loads it; its states at the frame's end that have not come there know the game paused) -/
  reach : ∀ n, r.C ≤ n → n < r.E → CtrlKeep.Unpaused sy m (PipeTransition.frame (r.fm n) (r.inAt n)) →
    (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).pc = sy.PlayerCtrlRoutine
  /-- in each frame of the room before the entry, at the player's routine the machine is in the state `VertAir.AtV` (`RoomVert.cut_R`: the walk to the player's routine
  knows the stack, the NMI, the routine byte, the area's type, the jumpspring and the swimming flag there; `RoomPair.quad_run`: the player's state is 0, 1 or 2 and the
  change of size is 0 at the frame's start, and the walk keeps them). The old part of `clean`'s `at_ctrl` and `at_frame` but the values -/
  cut : ∀ n, r.C ≤ n → n < r.E → ∀ j, (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerCtrlRoutine →
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) j)
  /-- in each frame of the room before the entry, at the player's routine the horizontal bytes are those of the frame's start (`RoomVert.hbytes_at_R`). The old part
  `before` of `clean` -/
  before : ∀ n, r.C ≤ n → n < r.E → ∀ j, (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerCtrlRoutine →
    ∀ a ∈ FrameModel.hBytes sy, peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) a = peek (r.fm n) a
  /-- the vertical state at first control is one of `N.vStart` (`Route.Run.roomV0`: the rows of the change know the vertical bytes there, `RoomPair.rowsCheck`) -/
  vstart : SurfaceFrames.vsOf sy (r.fe r.C) ∈ N.vStart
  /-- in each frame of the room before the entry, at the player's routine the player's state is that of the frame's start (`RoomVert.st_at_R`: the walk to the player's
  routine keeps the bytes of `vKeepA`) -/
  stR : ∀ n, r.C ≤ n → n < r.E → ∀ j, (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerCtrlRoutine →
    peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_State = peek (r.fm n) sy.Player_State
  /-- a frame of the room before the entering frame that comes to the player's routine at `k` in the state `VertAir.AtV` with a jump in the input that the model reads
  there (standing, a new press of A) ends on the takeoff `VertJump.jumpOff` of the height at the frame's start and of the stored speed at the player's routine
  (`RoomJump.jump_room`: the two walks of the room's frames of `RoomVert`, and the walk of two machines on a takeoff) -/
  jump : ∀ n, r.C ≤ n → n + 1 < r.E → ∀ k, VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) k)).jump = true →
    VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) =
      VertJump.jumpOff sy m (FrameModel.ctrlStack sy m) (peek (r.fm n) sy.Player_Y_Position)
        (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.Player_XSpeedAbsolute)
  /-- a frame of the room before the entering frame in the air, as `air`, comes to the end of its move `j` with the vertical bytes of `vstepR`; if `vstepR` is at the
  height `landY` and does not rise, and the end of the move meets `LandQ`, the vertical bytes at the frame's end are its landing (`Route.Run.roomLand`:
  `RoomLand.stand_at`, a walk from the end of the move that knows the map's cells, and `RoomFall.land_frame`) -/
  land : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State ≠ 0 → ∀ k,
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (peek (r.fm n) sy.Player_State = 1 → peek (r.fm n) sy.DiffToHaltJump = 1) →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 →
    ∃ j, k ≤ j ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame ∧
      VertModel.vsOf sy (PipeEntryRule.trace (r.fm n) (r.inAt n) j) =
        vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) ∧
      ((vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)).y = landY sy →
       (vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)).vy &&& 0x80 = 0 →
       LandQ sy N (PipeEntryRule.trace (r.fm n) (r.inAt n) j) →
       VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) =
         VertAir.land (vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)))
  /-- the frames between the end of the room's frame `n` and the start of its frame `n + 1` keep the vertical page (`Route.Run.roomKeepA`: the bytes of
  `RoomVert.vKeepA`) -/
  keepH : ∀ n, r.C ≤ n → n < r.E → peek (r.fm n) sy.Player_Y_HighPos = peek (r.fe n) sy.Player_Y_HighPos
  /-- a frame of the room before the entering frame in the air, as `air`, that starts with the vertical page 1: at each instruction from the player's routine on at the
  end of its move the vertical page is that of the machine of `vstepR` after the movement routine (`vRunR`), and if `vstepR` does not rise, so it is at the frame's end
  (`Route.Run.roomHigh`: `RoomFall.high_room`) -/
  high : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State ≠ 0 → ∀ k,
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (peek (r.fm n) sy.Player_State = 1 → peek (r.fm n) sy.DiffToHaltJump = 1) →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 →
    peek (r.fm n) sy.Player_Y_HighPos = 1 →
    (∀ j, k ≤ j → (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs → (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame →
      peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_Y_HighPos = peek (vRunR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)) sy.Player_Y_HighPos) ∧
    ((vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)).vy &&& 0x80 = 0 →
      peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_HighPos = peek (vRunR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0)) sy.Player_Y_HighPos)
  /-- a frame of the room before the entering frame that starts standing with the vertical page 1, and comes to the player's routine at `k` in the state `VertAir.AtV`
  with no jump in the input that the model reads there, comes to the end of its move `j`. If it starts on the floor's height with the vertical speed not negative, and at
  `j` the page is 0 and the horizontal coordinate below `landX`, it ends landed on the floor: the state 0, the vertical speed 0, the floor's height with its low four bits
  0, the vertical page 1 (`Route.Run.roomFloor`: `RoomFloor.floor_frame`, and `RoomLand.stand_at` at the floor's height) -/
  floor : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State = 0 → ∀ k,
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) k)).jump = false →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 → peek (r.fm n) sy.Player_Y_HighPos = 1 →
    ∃ j, k ≤ j ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame ∧
      (peek (r.fm n) sy.Player_Y_Position = (groundY sy).toUInt8 → peek (r.fm n) sy.Player_Y_Speed &&& 0x80 = 0 →
        (PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_PageLoc) = 0 →
        ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position)).toNat < N.landX →
        peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_State = 0 ∧ peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_Speed = 0 ∧
        peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_Position = (groundY sy).toUInt8 &&& 0xF0 ∧
        peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_HighPos = 1)
  /-- a frame of the room before the entering frame in the air, as `air`, comes to the end of its move `j` with the vertical bytes of `vstepR`; if the end of the move meets
  `WallQ`, the frame ends with the state not 0, or in the state 0 at the floor's height, or with the speed 0 (`Route.Run.roomWall`: `RoomFall.land_frame` up to the end of
  the move, `RoomWall.wall_frame` from there); since round 30, it comes to the end of its move once (`RoomVert.after_Q`), and if that meets `WallX` (x from 13 to 16), the
  frame ends with the state not 0 (`RoomWall.wall_frameX`); and if it meets `WallF` (x from 13 to the one before `cornerX`, a height of the first fall), too
  (`RoomWall.wall_frameF`) -/
  wall : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State ≠ 0 → ∀ k,
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (peek (r.fm n) sy.Player_State = 1 → peek (r.fm n) sy.DiffToHaltJump = 1) →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 →
    ∃ j, k ≤ j ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame ∧
      VertModel.vsOf sy (PipeEntryRule.trace (r.fm n) (r.inAt n) j) =
        vstepR sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) ∧
      (WallQ sy (PipeEntryRule.trace (r.fm n) (r.inAt n) j) →
        peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_State ≠ 0 ∨
        (peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_State = 0 ∧
          peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_Position = (groundY sy).toUInt8) ∨
        peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Speed = 0) ∧
      (∀ j', k ≤ j' → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').pc = sy.PlayerSubs → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').frame = (r.fm n).frame → j' = j) ∧
      (WallX sy (PipeEntryRule.trace (r.fm n) (r.inAt n) j) → peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_State ≠ 0) ∧
      (WallF sy (ysFall sy m N) (PipeEntryRule.trace (r.fm n) (r.inAt n) j) → peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_State ≠ 0)
  /-- a frame of the room before the entering frame that starts standing with the vertical page 1, and comes to the player's routine at `k` in the state `VertAir.AtV`
  with no jump in the input that the model reads there, comes to the end of its move `j`, and to no other `PlayerSubs`. If it starts at the floor's height with the
  vertical speed not negative, and at `j` the page is 0 and the coordinate one of `xsC` (his right side check in the block's left column), it ends `CornerEnd`: pushed back
  one pixel with the speed 0, or moving left as at `j` (`Route.Run.roomCorner`: `RoomFloor.floor_frame` up to the end of the move, `RoomVert.after_Q` for the one
  `PlayerSubs`, `RoomCorner.corner_frame` from there) -/
  corner : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State = 0 → ∀ k,
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) k)).jump = false →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 → peek (r.fm n) sy.Player_Y_HighPos = 1 →
    ∃ j, k ≤ j ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame ∧
      (∀ j', k ≤ j' → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').pc = sy.PlayerSubs → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').frame = (r.fm n).frame → j' = j) ∧
      (peek (r.fm n) sy.Player_Y_Position = (groundY sy).toUInt8 → peek (r.fm n) sy.Player_Y_Speed &&& 0x80 = 0 →
        (PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_PageLoc) = 0 →
        (PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position) ∈ xsC sy →
        CornerEnd sy (cornerY sy N.h) ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position))
          ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Speed)) (PipeTransition.frame (r.fm n) (r.inAt n)))
  /-- a frame of the room before the entering frame that starts at the floor's height with the vertical page 1, and comes to the player's routine at `k` in the state
  `VertAir.AtV` with a jump in the input that the model reads there, ends with the vertical page 1; it comes to the end of its move `j` once, and with the page 0 and the
  coordinate one of `xsC` there it ends `CornerEnd` (`Route.Run.roomHighJ`: `RoomHigh.jump_roomH`, the takeoff's walk with the vertical page and `RoomVert.after_QP`;
  `RoomHigh.offCheck`; `RoomCorner.corner_frame` from the end of the move, rising) -/
  highJ : ∀ n, r.C ≤ n → n + 1 < r.E → ∀ k, VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) k)).jump = true → peek (r.fm n) sy.Player_Y_HighPos = 1 →
    peek (r.fm n) sy.Player_Y_Position = (groundY sy).toUInt8 →
    peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_HighPos = 1 ∧
    ∃ j, k ≤ j ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame ∧
      (∀ j', k ≤ j' → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').pc = sy.PlayerSubs → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').frame = (r.fm n).frame → j' = j) ∧
      ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_PageLoc) = 0 →
        (PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position) ∈ xsC sy →
        CornerEnd sy (cornerY sy N.h) ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position))
          ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Speed)) (PipeTransition.frame (r.fm n) (r.inAt n)))
  /-- a frame of the room before the entering frame in the air, as `air`, with the vertical page 1, on a state of a jump's first frames that `vstep` leaves rising on such
  a state, ends with the vertical page 1; it comes to the end of its move `j` once, and with the page 0, the coordinate one of `xsC` and the height of `vstep` at
  `cornerY + 16` or below there it ends `CornerEnd` (`Route.Run.roomHighA`: `RoomHigh.air_roomH`, `RoomHigh.arcCheckH`, `RoomCorner.corner_frame` from the end of the
  move, rising) -/
  highA : ∀ n, r.C ≤ n → n + 1 < r.E → peek (r.fm n) sy.Player_State ≠ 0 → ∀ k,
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) k) →
    (peek (r.fm n) sy.Player_State = 1 → peek (r.fm n) sy.DiffToHaltJump = 1) →
    peek (r.fm n) sy.PreviousA_B_Buttons &&& 0x80 = peek (r.fm n) sy.A_B_Buttons &&& 0x80 → peek (r.fm n) sy.Player_Y_HighPos = 1 →
    VertModel.vsOf sy (r.fm n) ∈ (VertAir.arcSet sy m N.h N.rise).map (·.s) →
    vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∈
      (VertAir.arcSet sy m N.h N.rise).map (·.s) →
    (vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&& 0x80 = 0x80 →
    peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_HighPos = 1 ∧
    ∃ j, k ≤ j ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs ∧ (PipeEntryRule.trace (r.fm n) (r.inAt n) j).frame = (r.fm n).frame ∧
      (∀ j', k ≤ j' → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').pc = sy.PlayerSubs → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').frame = (r.fm n).frame → j' = j) ∧
      ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_PageLoc) = 0 →
        (PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position) ∈ xsC sy →
        cornerY sy N.h + 16 ≤
          (vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.SavedJoypadBits &&& 0x80 != 0) 0).y.toNat →
        CornerEnd sy (cornerY sy N.h) ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position))
          ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Speed)) (PipeTransition.frame (r.fm n) (r.inAt n)))
  /-- a frame of the room before the entering frame that comes to the player's routine at `k` in the air (the state 1 or 2), or on the ground with a new press of A (the
  state 0, bit 7 of the joypad set and bit 7 of A of the frame before clear), ends with the facing it had there (round 29, `Route.Run.roomFace`: `RoomFace.face_frame`, a walk
  of the room's whole frame that follows the facing from the player's routine) -/
  face : ∀ n, r.C ≤ n → n + 1 < r.E → ∀ k, (PipeEntryRule.trace (r.fm n) (r.inAt n) k).pc = sy.PlayerCtrlRoutine →
    (PipeEntryRule.trace (r.fm n) (r.inAt n) k).frame = (r.fm n).frame →
    ((PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.Player_State) = 1 ∨
      (PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.Player_State) = 2 ∨
      ((PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.Player_State) = 0 ∧
        (PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.SavedJoypadBits) &&& 0x80 = 0x80 ∧
        (PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.PreviousA_B_Buttons) &&& 0x80 = 0)) →
    peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.PlayerFacingDir = peek (PipeEntryRule.trace (r.fm n) (r.inAt n) k) sy.PlayerFacingDir
  /-- a frame of the room before the entering frame that comes to the player's routine at `k` with `RunningSpeed` 0, in the air (the state 1 or 2), or on the ground (the
  state 0) with the stored speed below `RunSpeedMin` or a new press of A (bit 7 of the joypad set, bit 7 of A of the frame before clear: the jump starts before the
  movement routine), ends with `RunningSpeed` 0 (round 31, `Route.Run.roomRun`: `RoomRunSpeed.run_frame`, a walk of the room's whole
  frame that follows `RunningSpeed` from the player's routine; `GetPlayerAnimSpeed`, the only writer, stores the stored speed only from `RunSpeedMin` on) -/
  run : ∀ n, r.C ≤ n → n + 1 < r.E → ∀ k, (PipeEntryRule.trace (r.fm n) (r.inAt n) k).pc = sy.PlayerCtrlRoutine →
    (PipeEntryRule.trace (r.fm n) (r.inAt n) k).frame = (r.fm n).frame →
    (PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.RunningSpeed) = 0 →
    ((PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.Player_State) = 1 ∨
      (PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.Player_State) = 2 ∨
      ((PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.Player_State) = 0 ∧
        ((PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.Player_XSpeedAbsolute) < sy.RunSpeedMin.toUInt8 ∨
          ((PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.SavedJoypadBits) &&& 0x80 = 0x80 ∧
            (PipeEntryRule.trace (r.fm n) (r.inAt n) k).ram.get! (FrameModel.I sy.PreviousA_B_Buttons) &&& 0x80 = 0)))) →
    peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.RunningSpeed = 0

/-- **`mouth`**: on the entry frame he is at the mouth, or past its left end. `P(E)` is read at the frame's end (`read_PE`), and the walks of the room's frames put the position
there (`InRoom.mouthE`) -/
theorem mouth_of (hr : r.InRoom) : SidePipe.mouthP sy 0 ≤ r.fr.P r.E := by
  rw [r.read_PE]
  exact hr.mouthE

/-- the goal is left of the mouth: `slow_mouth`, `air_pos` -/
theorem goal_mouth (H : Checks sy m N) : goalP sy ≤ SidePipe.mouthP sy 0 := by
  have h3 := H.nums.slow_mouth
  have h4 := H.nums.air_pos
  have h5 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (N.aboveS : Int) := Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  omega

/-- the goal is far below the end of the position's range: the mouth is on page 0 -/
theorem goal_small (H : Checks sy m N) : goalP sy + 2048 < 0x1000000 := by
  have h1 := goal_mouth H
  have h2 := sy.RoomPipeByte.toNat_lt
  unfold SidePipe.mouthP SidePipe.xLo SidePipe.column at h1
  omega

/-- **The entry comes no earlier than `t0`**: before `t0` he is left of the goal (`first`), the goal is left of the mouth, and on the entry frame he is at the mouth or
past it -/
theorem t0_le_E (H : Checks sy m N) (hr : r.InRoom) : r.t0 ≤ r.E := by
  rcases Nat.lt_or_ge r.E r.t0 with h | h
  · exfalso
    have h1 := r.first r.E hr.le h
    have h2 := r.mouth_of hr
    have h3 := goal_mouth H
    omega
  · exact h

/-- the room's frame `n + 1` before the entry is a counted frame within `b + lim`: from `InRoom.many` -/
theorem ups_lt (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (hE : n < r.E) : n + 1 - r.C ≤ r.ups := by
  have := hr.many
  omega

/-- the state at the end of frame `n` is read from `fe n` (`read_hs`) -/
theorem hs_fe {n : Nat} (hC : r.C ≤ n) (h2 : n ≤ r.t0) : r.fr.hs n = FrameModel.readHS sy (r.fe n) := r.read_hs n hC h2

/-- the position at the end of frame `n` is read from `fe n` (`read_P`) -/
theorem P_fe {n : Nat} (hC : r.C ≤ n) (h2 : n ≤ r.t0) : r.fr.P n = posP sy (r.fe n) := r.read_P n hC h2

/-- the vertical state at the end of frame `n` is read from `fe n` (`read_vs`) -/
theorem vs_fe {n : Nat} (hC : r.C ≤ n) (h2 : n ≤ r.t0) : r.fr.vs n = VertModel.vsOf sy (r.fe n) := r.read_vs n hC h2

/-- **The state at the end of frame `n` is that of the machine where frame `n + 1` begins**: `read_hs` and `InRoom.keep` -/
theorem hs_fm (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n ≤ r.t0) (hE : n < r.E) : r.fr.hs n = FrameModel.readHS sy (r.fm n) := by
  rw [r.hs_fe hC h2, (hr.keep n hC hE).1]

/-- the position, likewise -/
theorem P_fm (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n ≤ r.t0) (hE : n < r.E) : r.fr.P n = posP sy (r.fm n) := by
  rw [r.P_fe hC h2, (hr.keep n hC hE).2.1]

/-- the vertical state, likewise -/
theorem vs_fm (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n ≤ r.t0) (hE : n < r.E) : r.fr.vs n = VertModel.vsOf sy (r.fm n) := by
  rw [r.vs_fe hC h2]
  exact (hr.keep n hC hE).2.2.symm

/-- `InRoom.before` for each frame before `t0` -/
theorem before_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0)
    (hpc : (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).pc = sy.PlayerCtrlRoutine) :
    ∀ a ∈ FrameModel.hBytes sy, peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) a = peek (r.fm n) a := by
  have hE := r.t0_le_E H hr
  exact hr.before n hC (by omega) _ hpc

/-- **The frame's time** for each frame before `t0`, at its arrival at the player's routine: `InRoom.time` and `InRoom.arrive`, with `t0 ≤ E` -/
theorem inTime_of (H : Checks sy m N) (hr : r.InRoom) : ∃ idle, ∀ n, r.C ≤ n → n < r.t0 → (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).pc = sy.PlayerCtrlRoutine →
    FrameModel.InTime (FrameModel.Rom.of m) idle (r.fm n) (r.inAt n) (r.arr n) := by
  obtain ⟨idle, hidle, ht⟩ := hr.time
  have hE := r.t0_le_E H hr
  exact ⟨idle, fun n hC h2 hpc => ⟨hidle, hr.arrive n hC (by omega) _ hpc, ht n hC (by omega)⟩⟩

/-- the state at first control, as numbers -/
theorem start_hs (st : StartAt sy N (r.fe r.C)) : r.fr.hs r.C = (room sy N).s0 := by
  rw [r.hs_fe (Nat.le_refl _) r.t0_ge]
  exact st.hs

theorem start_P (st : StartAt sy N (r.fe r.C)) : (room sy N).P0 ≤ r.fr.P r.C ∧ r.fr.P r.C ≤ (room sy N).P1 := by
  rw [r.P_fe (Nat.le_refl _) r.t0_ge]
  exact ⟨st.P0, st.P1⟩

/-- **Each frame before `t0` comes to the player's routine at `arr n`**: it ends not paused by the definition of the room's frames (`RoomRun.up`), and `InRoom.reach`.
The old field `unpaused` -/
theorem arrive (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0) :
    (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).pc = sy.PlayerCtrlRoutine := by
  have hE := r.t0_le_E H hr
  exact hr.reach n hC (by omega) (r.up hC (r.ups_lt hr hC (by omega)))

/-- **`AtV` at the arrival** of each frame before `t0`: `arrive` and `InRoom.cut` -/
theorem atV_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0) :
    VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) := by
  have hE := r.t0_le_E H hr
  exact hr.cut n hC (by omega) _ (r.arrive H hr hC h2)

/-- a frame before `t0` that `clean` says follows the model is `FrameModel.CleanR` -/
theorem cleanR_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0)
    (hc : CleanW sy (r.fm n) (r.inAt n) (r.arr n)) : FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n) :=
  hc.toR (r.atV_of H hr hC h2)

/-- the speed at the start of a frame is in the domain's range: so it is at the player's routine (`InRoom.before`) -/
theorem speed_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0) (hd : inD sy (r.fr.hs n) = true) :
    TopSpeed.inSpeed sy (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.Player_X_Speed) = true := by
  have hE := r.t0_le_E H hr
  rw [r.before_of H hr hC h2 (r.arrive H hr hC h2) sy.Player_X_Speed (by simp [FrameModel.hBytes])]
  rw [r.hs_fm hr hC (by omega) (by omega)] at hd
  simp only [inD, Bool.and_eq_true] at hd
  exact hd.1.1.1

/-- a frame before `t0` that `clean` says stops him is `FrameModel.ReadR`, when the speed at its start is in the domain -/
theorem readR_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0) (hd : inD sy (r.fr.hs n) = true)
    (hc : ReadW sy (r.fm n) (r.inAt n) (r.arr n)) : FrameModel.ReadR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n) :=
  hc.toR (r.atV_of H hr hC h2) (r.speed_of H hr hC h2 hd)

/-- the position's range, from 8 px at the start of the frame: the other end from `first` -/
theorem far_up (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (h : 2048 ≤ posP sy (r.fm n)) :
    2048 ≤ posP sy (r.fm n) ∧ posP sy (r.fm n) + 2048 < 0x1000000 := by
  refine ⟨h, ?_⟩
  have hE := r.t0_le_E H hr
  have h1 := r.first n hC ht
  rw [r.P_fm hr hC (by omega) (by omega)] at h1
  have h2 := goal_small H
  omega

/-- a frame that follows the model follows `hstep`, given the position at its start at 8 px or more -/
theorem follow_of_far (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0) (hf : 2048 ≤ posP sy (r.fm n))
    (hc : FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n)) : Follow sy m r.fr n := by
  obtain ⟨idle, hT⟩ := r.inTime_of H hr
  obtain ⟨h1, h3⟩ := FrameModel.clean_frameR H.model hc (r.before_of H hr hC h2 hc.at_ctrl.pc) (hT n hC h2 hc.at_ctrl.pc) (r.far_up H hr hC h2 hf)
  have hE := r.t0_le_E H hr
  rw [← r.next hC (r.ups_lt hr hC (by omega))] at h1 h3
  have e0 := r.hs_fm hr hC (by omega) (by omega)
  have e1 := r.hs_fe (n := n + 1) (by omega) (by omega)
  have p0 := r.P_fm hr hC (by omega) (by omega)
  have p1 := r.P_fe (n := n + 1) (by omega) (by omega)
  have e2 := r.read_in n hC h2 hc
  refine ⟨?_, ?_, ?_⟩
  · rw [e2]
    exact FrameModel.readIn_mem (FrameModel.joy_of_model H.model) _
  · rw [e1, h1, e0, e2]
  · rw [p1, h3, p0, e1]

/-- **One frame before `t0`**, from the position at 8 px or more and the state in the domain at its start: it follows `hstep` or leaves him stopped, it moves him left by
at most `16·top + 256`, and the state at its end is in the domain -/
theorem step_far (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0) (hf : 2048 ≤ posP sy (r.fm n)) (hd : inD sy (r.fr.hs n) = true) :
    (Follow sy m r.fr n ∨ Stop sy m N r.fr (n + 1)) ∧ posP sy (r.fm n) - 16 * (top sy : Int) - 256 ≤ posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) ∧
      inD sy (r.fr.hs (n + 1)) = true := by
  have hE := r.t0_le_E H hr
  have hnx := r.next hC (r.ups_lt hr hC (by omega))
  have p0 := r.P_fm hr hC (by omega) (by omega)
  have p1 := r.P_fe (n := n + 1) (by omega) (by omega)
  rcases r.clean n hC h2 with hc | ⟨hs, hc⟩
  · have hF := r.follow_of_far H hr hC h2 hf (r.cleanR_of H hr hC h2 hc)
    have hd1 := (FastTakeoff.step_facts H.air.pot hd hF.1).1
    rw [← hF.2.1] at hd1
    refine ⟨Or.inl hF, ?_, hd1⟩
    have hd2 := hd1
    simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hd2
    have h4 := hd2.1.1.1
    have h5 := hF.2.2
    rw [← hnx, ← p0, ← p1]
    omega
  · obtain ⟨idle, hT⟩ := r.inTime_of H hr
    have hR := r.readR_of H hr hC h2 hd hc
    have hl := FrameModel.frame_readR_low H.model H.fric hR (r.before_of H hr hC h2 hR.at_frame.pc) (hT n hC h2 hR.at_frame.pc) (r.far_up H hr hC h2 hf)
    exact ⟨Or.inr hs, hl, hs.1⟩

/-- **At the start of each frame before `t0` he is at 8 px or more, and the state is in the domain**: at first control from the room's start (`start_far`) and the
domain's check; then each frame keeps both, by `step_far`, and by `farNear` near the left end. The frames that end paused in between keep the position
(`InRoom.keep`) -/
theorem far_inD (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) :
    ∀ d, r.C + d < r.t0 → 2048 ≤ posP sy (r.fm (r.C + d)) ∧ inD sy (r.fr.hs (r.C + d)) = true
  | 0, h0 => by
    have hE := r.t0_le_E H hr
    refine ⟨?_, ?_⟩
    · have h1 := st.P0
      have h2 := H.nums.start_far
      rw [show r.C + 0 = r.C from rfl, (hr.keep r.C (Nat.le_refl _) (by omega)).2.1]
      unfold room bonusRoom at h1
      exact Int.le_trans h2 h1
    · have h := H.roomOk
      simp only [roomCheck, Bool.and_eq_true] at h
      rw [show r.C + 0 = r.C from rfl, r.start_hs st]
      exact h.1.1
  | d + 1, hd => by
    have hE := r.t0_le_E H hr
    obtain ⟨h1, h2⟩ := far_inD H hr st d (by omega)
    obtain ⟨_, h4, h5⟩ := r.step_far H hr (n := r.C + d) (by omega) (by omega) h1 h2
    rw [show r.C + (d + 1) = r.C + d + 1 by omega]
    refine ⟨?_, h5⟩
    rw [(hr.keep (r.C + d + 1) (by omega) (by omega)).2.1, r.next (n := r.C + d) (by omega) (r.ups_lt hr (by omega) (by omega))]
    by_cases hn : posP sy (r.fm (r.C + d)) < 2048 + 16 * (top sy : Int) + 256
    · exact r.farNear (r.C + d) (by omega) (by omega) h1 hn
    · omega

/-- **The position at the start of each frame before `t0` is away from both ends of its range** -/
theorem far_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) :
    2048 ≤ posP sy (r.fm n) ∧ posP sy (r.fm n) + 2048 < 0x1000000 := by
  have h := (r.far_inD H hr st (n - r.C) (by omega)).1
  rw [show r.C + (n - r.C) = n by omega] at h
  exact r.far_up H hr hC ht h

/-- a frame that follows the model follows `hstep`: `FrameModel.clean_frameR`, with the frame's time and the position's range -/
theorem follow_of_clean (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0)
    (hc : FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n)) : Follow sy m r.fr n :=
  r.follow_of_far H hr hC h2 (r.far_of H hr st hC h2).1 hc

/-- each frame follows `hstep` or leaves him stopped -/
theorem frames_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : ∀ n, r.C ≤ n → n < r.t0 → Follow sy m r.fr n ∨ Stop sy m N r.fr (n + 1) := by
  intro n h1 h2
  rcases r.clean n h1 h2 with h3 | h3
  · exact Or.inl (r.follow_of_clean H hr st h1 h2 (r.cleanR_of H hr h1 h2 h3))
  · exact Or.inr h3.1

/-- every frame up to `t0` is in the domain -/
theorem inD_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : ∀ d, r.C + d ≤ r.t0 → inD sy (r.fr.hs (r.C + d)) = true
  | 0, _ => by
    have h := H.roomOk
    simp only [roomCheck, Bool.and_eq_true] at h
    rw [show r.C + 0 = r.C from rfl, r.start_hs st]
    exact h.1.1
  | d + 1, h => by
    obtain ⟨h1, h2⟩ := r.far_inD H hr st d (by omega)
    rw [show r.C + (d + 1) = r.C + d + 1 by omega]
    exact (r.step_far H hr (n := r.C + d) (by omega) (by omega) h1 h2).2.2

/-- every frame moves him at most the top speed: a frame that follows `hstep` by the bound on its domain -/
theorem move_top_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : ∀ n, r.C ≤ n → n < r.t0 → r.fr.P (n + 1) ≤ r.fr.P n + 16 * (top sy : Int) := by
  intro n h1 h2
  obtain ⟨idle, hT⟩ := r.inTime_of H hr
  have hdn := r.inD_of H hr st (n - r.C) (by omega)
  rw [show r.C + (n - r.C) = n by omega] at hdn
  rcases r.clean n h1 h2 with h3 | h3
  · have hf := r.follow_of_clean H hr st h1 h2 (r.cleanR_of H hr h1 h2 h3)
    have hd := r.inD_of H hr st (n + 1 - r.C) (by omega)
    rw [show r.C + (n + 1 - r.C) = n + 1 by omega] at hd
    simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hd
    have h4 := hd.1.1.1
    rw [hf.2.2]
    omega
  · -- a `TopSpeed.Frame`: `Frame.bound`, from the domain
    have hR := r.readR_of H hr h1 h2 hdn h3.2
    obtain ⟨f, e1, _, e3, _, _, e6⟩ := FrameModel.frame_readR H.model H.fric hR (r.before_of H hr h1 h2 hR.at_frame.pc) (hT n h1 h2 hR.at_frame.pc) (r.far_of H hr st h1 h2)
    have hE := r.t0_le_E H hr
    have hd := hdn
    rw [r.hs_fm hr h1 (by omega) (by omega)] at hd
    simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hd
    have h4 : (sbyte (peek (r.fm n) sy.Player_X_Speed)).natAbs ≤ top sy := hd.1.1.1
    have h16 : (16 : Int) ≤ (top sy : Int) := by
      have := (FrameModel.facts_of H.model).top16
      show (16 : Int) ≤ (TopSpeed.top sy : Int)
      omega
    have hb := f.bound h16 (by rw [e1]; omega)
    rw [r.P_fe (n := n + 1) (by omega) (by omega), r.P_fm hr h1 (by omega) (by omega), r.next h1 (r.ups_lt hr h1 (by omega)), ← e6, ← e3]
    omega

theorem start_v (st : StartAt sy N (r.fe r.C)) :
    (r.fr.vs r.C).st = 2 ∧ VY (r.fr.vs r.C) ≤ N.startY ∧ VW (r.fr.vs r.C) ≤ N.startW ∧ (r.fr.vs r.C).vfd.toNat = N.fallF := by
  rw [r.vs_fe (Nat.le_refl _) r.t0_ge]
  exact st.v

/-- a frame that follows the model reads the stored speed `|v|`: `AtCtrl.abs`, and nothing wrote the speed before the player's routine -/
theorem ab_clean (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0)
    (hc : FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n)) :
    r.fr.ab n = (sbyte (r.fr.hs n).v).natAbs := by
  have e1 := hc.at_ctrl.abs
  have e2 := r.before_of H hr hC h2 hc.at_ctrl.pc sy.Player_X_Speed (by simp [FrameModel.hBytes])
  rw [e2] at e1
  have hE := r.t0_le_E H hr
  rw [r.read_ab n hC h2, e1, SurfaceFrames.absB_natAbs, r.hs_fm hr hC (by omega) (by omega)]
  rfl

/-- the stored speed that each frame reads is `|v|`, or the frame leaves him stopped and, before `hitF`, the stored speed is below the threshold -/
theorem ab_of_run (H : Checks sy m N) (hr : r.InRoom) : ∀ n, r.C ≤ n → n < r.t0 → r.fr.ab n = (sbyte (r.fr.hs n).v).natAbs ∨
    (Stop sy m N r.fr (n + 1) ∧ (n + 1 < r.C + N.hitF → r.fr.ab n < sy.AirFastSpeed.toNat)) := by
  intro n h1 h2
  by_cases hc : FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n)
  · exact Or.inl (r.ab_clean H hr h1 h2 hc)
  · rcases r.clean n h1 h2 with h3 | h3
    · exact absurd (r.cleanR_of H hr h1 h2 h3) hc
    · exact Or.inr ⟨h3.1, fun h4 => r.ab_early n h1 h4 h2 hc⟩

/-- at each read of the block buffer routine before the write in frame `E`, the side pipe's tiles are only in the pipe's column. No longer a field of `RoomRun`: `RoomMap.map_of_rows` proves it
on the frames of the room, and `Route.Run.roomTiles` joins frame `E` to them. -/
def TilesE (r : RoomRun sy m N S b lim) : Prop :=
  ∀ n j, SideEntryRule.WriteStep sy (r.fm (r.E - 1)) (r.pad r.E) n → j ≤ n → PoleEntryRule.AtRead (SideEntryRule.spots sy m) (PipeEntryRule.trace (r.fm (r.E - 1)) (r.pad r.E) j) →
    PoleEntryRule.TilesOK (SideEntryRule.spots sy m) (PipeEntryRule.trace (r.fm (r.E - 1)) (r.pad r.E) j)

/-- frame `E` starts in the idle loop, in control, with the screen's bytes of the room (`SideFrame.roomG`). No longer a field of `RoomRun`: `RoomMap.start_of_rowsF` proves it on
the frames of the room, and `Route.Run.roomStartE` joins frame `E` to them. -/
def StartE (r : RoomRun sy m N S b lim) : Prop := PipeWrites.FrameStart (SideFrame.roomG sy m) (PipeEntryRule.envOf m) (r.fm (r.E - 1))

/-- each instruction of frame `E` up to the write is `Clean` with the room's guard. No longer a field of `RoomRun`: `RoomMap.clean_of_rows` proves it on the frames of the room, and
`Route.Run.roomCleanE` joins frame `E` to them. -/
def CleanE (r : RoomRun sy m N S b lim) : Prop :=
  ∀ n, SideEntryRule.WriteStep sy (r.fm (r.E - 1)) (r.pad r.E) n → ∀ j, j ≤ n → PipeWrites.Clean (SideFrame.roomG sy m) (PipeEntryRule.trace (r.fm (r.E - 1)) (r.pad r.E) j)

/-- frame `E` does not come to the routine of the head's collision with a block. Once part of the field `edgeE`: `RoomMap.head_of_rows` proves it on the frames of the room, and
`Route.Run.roomHeadE` joins frame `E` to them. -/
def HeadE (r : RoomRun sy m N S b lim) : Prop := ∀ j, (PipeEntryRule.trace (r.fm (r.E - 1)) (r.pad r.E) j).pc ≠ PipeWrites.headAt sy m


theorem vsOf_same (m' : Machine) : SurfaceFrames.vsOf sy m' = VertModel.vsOf sy m' := rfl

theorem vy_of_falling {s : VS} (h : falling s = false) : s.vy &&& 0x80 = 0x80 := by
  have a : ∀ n : Fin 256, (decide (UInt8.ofNat n.val < 0x80)) = false → UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel
  have := a ⟨s.vy.toNat, s.vy.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this (by simpa [falling] using h)

/-- **`varc`**: a frame of the room on the first frames of a jump from the floor follows `vstep`. From the reading of the vertical state, the frame at the player's routine
(`clean`), and the walks of the room's frames (`InRoom.vert`, `InRoom.pair`) -/
theorem varc_of (H : Checks sy m N) (hr : r.InRoom) {T n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E) (ha : OnArc sy m N r.fr T n)
    (hk : n + 1 - (T + 1) ≤ N.rise) : r.fr.vs (n + 1) = vstep sy m (r.fr.vs n) (r.fr.a (n + 1)) 0 := by
  -- the frame at the player's routine
  have hcl : VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) := r.atV_of H hr hC ht
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (n + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.vs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hT := ha.1
  obtain ⟨hfall, _⟩ := (arc_facts H ha (by omega)).2
  obtain ⟨_, x, u, hx, hru, hu⟩ := ha
  let a := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.SavedJoypadBits &&& 0x80 != 0
  let y : Arc :=
    { s := vstep sy m u.s a 0, k := u.k + 1,
      low := if cornerY sy N.h ≤ (vstep sy m u.s a 0).y.toNat then u.k + 1 else u.low,
      above := if (vstep sy m u.s a 0).y.toNat < standY sy N.h then 0 else u.above + 1, fast := u.fast }
  have hy : y ∈ arcSucc sy m N.h u := by
    unfold arcSucc
    rw [← hu, hfall]
    simp only [Bool.false_and, if_false, Bool.false_eq_true]
    rw [hu]
    cases ha' : a with
    | true => simp [y, ha']
    | false => simp [y, ha']
  have hyr : Cert.Reach (arcSucc sy m N.h) x (n + 1 - (T + 1)) y := by
    rw [show n + 1 - (T + 1) = n - (T + 1) + 1 by omega]
    exact reach_snoc hru hy
  obtain ⟨_, hyf, _⟩ := arc_facts H (fr := { r.fr with vs := fun j => if j = n + 1 then y.s else r.fr.vs j }) (T := T) (n := n + 1)
    ⟨by omega, x, y, hx, hyr, by simp⟩ hk
  simp only [if_true] at hyf
  have e := hr.vert n hC hE (r.arr n) hcl (hr.pair n hC (by omega)).1 (hr.pair n hC (by omega)).2
    (by rw [← hv0, hu]; exact List.mem_map.2 ⟨u, VertAir.mem_arcSet hx hru (by omega), rfl⟩)
    (by rw [← hv0, hu]; exact List.mem_map.2 ⟨y, VertAir.mem_arcSet hx hyr hk, rfl⟩)
    (by rw [← hv0, hu]; exact vy_of_falling hyf)
  have hA : r.fr.a (n + 1) = a := by
    show (r.fr.vs (n + 1)).prevA = a
    rw [hv1, e]
    rfl
  rw [hA, hv1, e, hv0]

/-- **Every frame of the room in the air follows `vstep` up to the landing**: a frame before `t0` and before the entering frame that starts in the air is `vstepR` of the
frame before, with A of the frame, or `vstepR` falls and the frame is its landing; and `vstepR` stays in the air. From the reading of the vertical state, the frame at the
player's routine (`clean`), and the walks of the room's frames (`InRoom.air`, `InRoom.pair`) -/
theorem vair_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E) (hst : (r.fr.vs n).st ≠ 0) :
    ((vstepR sy m (r.fr.vs n) (r.fr.a (n + 1))).st = 1 ∨ (vstepR sy m (r.fr.vs n) (r.fr.a (n + 1))).st = 2) ∧
    (r.fr.vs (n + 1) = vstepR sy m (r.fr.vs n) (r.fr.a (n + 1)) ∨
     (falling (vstepR sy m (r.fr.vs n) (r.fr.a (n + 1))) = true ∧ r.fr.vs (n + 1) = VertAir.land (vstepR sy m (r.fr.vs n) (r.fr.a (n + 1))))) := by
  have hcl := r.atV_of H hr hC ht
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (n + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.vs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hst' : peek (r.fm n) sy.Player_State ≠ 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).st = peek (r.fm n) sy.Player_State := rfl
    rw [← e, ← hv0]
    exact hst
  have e := hr.air n hC hE hst' (r.arr n) hcl (hr.pair n hC (by omega)).1 (hr.pair n hC (by omega)).2
  have hA : r.fr.a (n + 1) = (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.SavedJoypadBits &&& 0x80 != 0) := by
    show (r.fr.vs (n + 1)).prevA = _
    rw [hv1]
    rcases e.2 with e1 | ⟨_, e1⟩ <;> rw [e1] <;> rfl
  rw [hA, hv1, hv0]
  exact e

theorem hi_row : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0xF0).toNat % 16 = 0 := by decide +kernel

/-- **`stand_row`**: from the air to standing, his height is a whole row and his vertical speed is 0, on each frame before `t0`. A frame in the air follows `vstepR`, which
stays in the air, or lands (`vair_of`); the entering frame is not before `t0` (`t0_le_E`) -/
theorem stand_row_of (H : Checks sy m N) (hr : r.InRoom) : ∀ n, r.C ≤ n → n + 1 < r.t0 → (r.fr.vs n).st ≠ 0 → (r.fr.vs (n + 1)).st = 0 →
    (r.fr.vs (n + 1)).y.toNat % 16 = 0 ∧ VW (r.fr.vs (n + 1)) = 0 := by
  intro n hC ht hst h0
  have hE := r.t0_le_E H hr
  obtain ⟨h1, h2⟩ := r.vair_of H hr hC (by omega) (by omega) hst
  rcases h2 with e | ⟨_, e⟩
  · rw [e] at h0
    rcases h1 with e1 | e1 <;> rw [e1] at h0 <;> exact absurd h0 (by decide)
  · rw [e]
    refine ⟨?_, by simp [VW, VertAir.land]⟩
    show ((vstepR sy m (r.fr.vs n) (r.fr.a (n + 1))).y &&& 0xF0).toNat % 16 = 0
    generalize (vstepR sy m (r.fr.vs n) (r.fr.a (n + 1))).y = x
    have := hi_row ⟨x.toNat, x.toNat_lt⟩
    simpa using this

/-- **Every frame of a jump from the floor follows `vstep` up to the landing**: a frame before `t0` and before the entering frame, on a jump from the floor (`OnArc`), that
does not start at or below the ground falling, is `vstep` of the frame before with A of the frame, or `vstep` falls and the frame is its landing. `vair_of`, and on the
jumps from the floor `vstepR` is `vstep` on `m` (`hb`: `VertAir.bridgeAll`, every state of every jump from the floor up to the ground) -/
theorem varc_all (H : Checks sy m N) (hr : r.InRoom) (hb : VertAir.bridgeAll sy m (FrameModel.ctrlStack sy m) (groundY sy) N.h = true) {T n : Nat}
    (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E) (ha : OnArc sy m N r.fr T n)
    (hg : (falling (r.fr.vs n) && decide (groundY sy ≤ (r.fr.vs n).y.toNat)) = false) :
    r.fr.vs (n + 1) = vstep sy m (r.fr.vs n) (r.fr.a (n + 1)) 0 ∨
    (falling (vstep sy m (r.fr.vs n) (r.fr.a (n + 1)) 0) = true ∧ r.fr.vs (n + 1) = VertAir.land (vstep sy m (r.fr.vs n) (r.fr.a (n + 1)) 0)) := by
  obtain ⟨_, x, u, hx, hru, hu⟩ := ha
  obtain ⟨b1, b2⟩ := VertAir.bridgeAll_of hb hx hru
  have hne : arcSucc sy m N.h u ≠ [] := by
    unfold arcSucc
    rw [← hu, hg]
    simp
  have hst : (r.fr.vs n).st ≠ 0 := by
    rw [hu]
    rcases b1 with e | e <;> rw [e] <;> decide
  have e := (r.vair_of H hr hC ht hE hst).2
  have hbr := b2 hne (r.fr.a (n + 1))
  rw [← hu] at hbr
  simp only [vstepR] at e
  rw [hbr] at e
  exact e

/-! ### The first fall

The vertical state at first control is a state of `N.vStart` (`InRoom.vstart`). Up to the first stand each frame starts in the air, so it is `vstepR` of the frame
before or its landing (`vair_of`), and a landing is a stand. So up to the first stand, `d` frames after first control the state is in `fallLayer d` (`fall_mem`), and
the check `fallCheck` on these states gives `VDrop` (`vfall_first`) and the heights (`fall_first`, `floor_at_of`). Before `standF` these frames are before `t0`:
at the top speed from the start he is not past the block's right end (`t0_far`). -/

theorem vs_start (hr : r.InRoom) : r.fr.vs r.C ∈ N.vStart := by
  rw [r.read_vs r.C (Nat.le_refl _) r.t0_ge]
  exact hr.vstart

/-- **The frames before `standF` are before `t0`**: each frame moves him at most the top speed (`move_top_of`) from the start (`start_P`) -/
theorem t0_far (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : r.C + N.standF < r.t0 := by
  obtain ⟨_, _, hf, _⟩ := fall_ok H.first
  have hmv := r.move_top_of H hr st
  have hP1 := (r.start_P st).2
  have hp := r.past
  have h0 := r.t0_ge
  have h16 : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  have key : ∀ k, r.C + k ≤ r.t0 → r.fr.P (r.C + k) ≤ r.fr.P r.C + 16 * (top sy : Int) * (k : Int) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := hmv (r.C + k) (by omega) (by omega)
      have h2 := ih (by omega)
      rw [show r.C + (k + 1) = r.C + k + 1 by omega]
      have e : 16 * (top sy : Int) * ((k + 1 : Nat) : Int) = 16 * (top sy : Int) * (k : Int) + 16 * (top sy : Int) := by
        push_cast
        rw [Int.mul_add, Int.mul_one]
      omega
  by_cases h : r.C + N.standF < r.t0
  · exact h
  · exfalso
    have h1 := key (r.t0 - r.C) (by omega)
    rw [show r.C + (r.t0 - r.C) = r.t0 by omega] at h1
    have h2 : 16 * (top sy : Int) * ((r.t0 - r.C : Nat) : Int) ≤ 16 * (top sy : Int) * (N.standF : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) h16
    omega

/-- **Up to the first stand the state is a state of the first fall** -/
theorem fall_mem (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) :
    ∀ d, d < N.standF → (∀ j, r.C < j → j ≤ r.C + d → (r.fr.vs j).st ≠ 0) → r.fr.vs (r.C + d) ∈ fallLayer sy m N.vStart d
  | 0, _, _ => r.vs_start hr
  | d + 1, h1, h2 => by
    have ih := fall_mem H hr st d (by omega) (fun j a b => h2 j a (by omega))
    have hok := (fall_ok H.first).2.2.2 d (by omega) _ ih
    have hst := (fallOk_spec hok).1
    have hfar := r.t0_far H hr st
    have hE := r.t0_le_E H hr
    obtain ⟨_, h3⟩ := r.vair_of H hr (n := r.C + d) (by omega) (by omega) (by omega) (by rw [hst]; decide)
    rw [show r.C + (d + 1) = r.C + d + 1 by omega]
    rcases h3 with e | ⟨_, e⟩
    · rw [e]
      exact mem_fallNext ih _
    · exfalso
      exact h2 (r.C + d + 1) (by omega) (by omega) (by rw [e]; rfl)

/-- the frame after a state of the first fall: the check holds on the state, and the frame is `vstepR` or its landing -/
theorem fall_next (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {d : Nat} (hd : d < N.standF)
    (hn : ∀ j, r.C < j → j ≤ r.C + d → (r.fr.vs j).st ≠ 0) :
    fallOk sy m N d (r.fr.vs (r.C + d)) = true ∧
    (r.fr.vs (r.C + d + 1) = vstepR sy m (r.fr.vs (r.C + d)) (r.fr.a (r.C + d + 1)) ∨
     (falling (vstepR sy m (r.fr.vs (r.C + d)) (r.fr.a (r.C + d + 1))) = true ∧
      r.fr.vs (r.C + d + 1) = VertAir.land (vstepR sy m (r.fr.vs (r.C + d)) (r.fr.a (r.C + d + 1))))) := by
  have hok := (fall_ok H.first).2.2.2 d hd _ (r.fall_mem H hr st d hd hn)
  have hst := (fallOk_spec hok).1
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  exact ⟨hok, (r.vair_of H hr (n := r.C + d) (by omega) (by omega) (by omega) (by rw [hst]; decide)).2⟩

/-- **`vfall` before the first stand**: a frame of the first fall is `VDrop` -/
theorem vfall_first (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n + 1 < r.C + N.standF)
    (hn : ∀ j, r.C < j → j ≤ n → (r.fr.vs j).st ≠ 0) : VDrop (r.fr.vs n) (r.fr.vs (n + 1)) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = r.C + d := ⟨n - r.C, by omega⟩
  obtain ⟨hok, h2⟩ := r.fall_next H hr st (d := d) (by omega) hn
  obtain ⟨_, s2, s3, _, _⟩ := fallStep_spec ((fallOk_spec hok).2 (r.fr.a (r.C + d + 1)))
  rcases h2 with e | ⟨hf, e⟩
  · rw [e]
    exact s2
  · rw [e]
    exact s3 hf

/-- **`fall_long` up to the first stand**: a frame of the first fall before `C + fall`, or the stand that ends it, is not on the floor -/
theorem fall_first (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n < r.C + N.fall)
    (hn : ∀ j, r.C < j → j < n → (r.fr.vs j).st ≠ 0) : ¬OnFloor sy (r.fr.vs n) := by
  obtain ⟨_, hfs, _, _⟩ := fall_ok H.first
  obtain ⟨d, rfl⟩ : ∃ d, n = r.C + d := ⟨n - r.C, by omega⟩
  intro hfl
  cases d with
  | zero =>
    have hs := (fallOk_spec ((fall_ok H.first).2.2.2 0 (by omega) _ (r.fall_mem H hr st 0 (by omega) (fun j a b => by omega)))).1
    have h3 := hfl.1
    rw [hs] at h3
    exact absurd h3 (by decide)
  | succ d =>
    obtain ⟨hok, h2⟩ := r.fall_next H hr st (d := d) (by omega) (fun j a b => hn j a (by omega))
    obtain ⟨s1, _, _, s4, _⟩ := fallStep_spec ((fallOk_spec hok).2 (r.fr.a (r.C + d + 1)))
    rw [show r.C + (d + 1) = r.C + d + 1 by omega] at hfl
    rcases h2 with e | ⟨hf, e⟩
    · have h3 := hfl.1
      rw [e, s1] at h3
      exact absurd h3 (by decide)
    · exact s4 (by omega) hf (by rw [← e]; exact hfl.2)

/-! ### The frames with no jump -/

/-- **A frame's input is read from the machine** at its first arrival at the player's routine, on each frame before `t0`: a frame that follows the model by `read_in`, the
others by `read_stop` -/
theorem read_inp {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) :
    r.fr.inp (n + 1) = FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) := by
  by_cases hc : FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n)
  · exact r.read_in n hC ht hc
  · exact r.read_stop n hC ht hc

/-- **The jump bit of a frame's input is read from the machine**: a frame before `t0` with no jump in its input has none in the input that the model reads at the player's
routine (`read_inp`) -/
theorem jump_read {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hj : (r.fr.inp (n + 1)).jump = false) :
    (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n))).jump = false := by
  rw [← r.read_inp hC ht]
  exact hj

theorem and80_ne : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 ≠ 0 → UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel

/-- an input read at the player's routine with an air input or a jump: the state there is 1 or 2, or 0 with a new press of A -/
theorem faceIn_of_read {T : Machine} (hst : peek T sy.Player_State ∈ [(0 : UInt8), 1, 2])
    (hin : (FrameModel.readIn sy T).st ≠ 0 ∨ (FrameModel.readIn sy T).jump = true) :
    T.ram.get! (FrameModel.I sy.Player_State) = 1 ∨ T.ram.get! (FrameModel.I sy.Player_State) = 2 ∨
      (T.ram.get! (FrameModel.I sy.Player_State) = 0 ∧ T.ram.get! (FrameModel.I sy.SavedJoypadBits) &&& 0x80 = 0x80 ∧
        T.ram.get! (FrameModel.I sy.PreviousA_B_Buttons) &&& 0x80 = 0) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hin with h | h
  · rcases hst with e | e | e
    · simp only [FrameModel.readIn] at h
      rw [e] at h
      exact absurd rfl h
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · simp only [FrameModel.readIn, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨h2, h3⟩, h4⟩ := h
    have h5 := and80_ne ⟨(T.ram.get! (FrameModel.I sy.SavedJoypadBits)).toNat, (T.ram.get! (FrameModel.I sy.SavedJoypadBits)).toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at h5
    exact Or.inr (Or.inr ⟨h2, h5 h3, h4⟩)

/-- **`facing`** (round 29): before the end of the fall a frame with an air input or a jump input keeps the facing. The input is read at the player's routine
(`read_inp`): the state there is 1 or 2 (`InRoom.cut`), or 0 with a new press of A (`faceIn_of_read`). `InRoom.face` says that such a frame ends with the facing it
had at the player's routine, and that is the facing at the frame's start (`InRoom.before`). No condition on `hstep` -/
theorem facing_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : ∀ n, r.C ≤ n → n < r.C + N.fall →
    (r.fr.inp (n + 1)).st ≠ 0 ∨ (r.fr.inp (n + 1)).jump = true → (r.fr.hs (n + 1)).fd = (r.fr.hs n).fd := by
  intro n hC h1 hin
  have hle := H.nums.fall_le
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have ht : n < r.t0 := by omega
  have hpc := r.arrive H hr hC ht
  have hf := hr.arrive n hC (by omega) _ hpc
  rw [r.read_inp hC ht] at hin
  have hfi := faceIn_of_read (r.atV_of H hr hC ht).st hin
  have hface := hr.face n hC (by omega) _ hpc hf hfi
  have hb := hr.before n hC (by omega) _ hpc sy.PlayerFacingDir (by simp [FrameModel.hBytes])
  rw [r.hs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega)), r.hs_fm hr hC (by omega) (by omega)]
  show peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.PlayerFacingDir = peek (r.fm n) sy.PlayerFacingDir
  rw [hface, hb]

/-- **`stop_run`** (round 31): from the end of the fall to `runF`, a frame that does not follow `hstep`, with `RunningSpeed` 0 and the speed below the running threshold
at its start, leaves `RunningSpeed` 0. At the player's routine `RunningSpeed` is that of the frame's start (`InRoom.before`), so 0, and the state is 0, 1 or 2
(`InRoom.cut`). In the air, and on the ground with a new press of A, that is `InRoom.run`'s condition. On the ground with no jump the stored speed it reads (`read_ab`)
is the size of the speed at the start, or before `hitF` below the air threshold (`ab_early`: the frame is not `CleanR`, or it would follow `hstep`), or the field
`ab_run`; so below the threshold, and `InRoom.run` says that the frame ends with `RunningSpeed` 0 -/
theorem stop_run_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (h1 : r.C + N.fall ≤ n) (h2 : n < r.C + N.runF)
    (hrs : (r.fr.hs n).rs = 0) (hv : (sbyte (r.fr.hs n).v).natAbs < sy.RunSpeedMin.toNat) (hf : ¬Follow sy m r.fr n) : (r.fr.hs (n + 1)).rs = 0 := by
  have hN := H.nums
  have hvf := hN.vf
  have hrl := hN.run_le
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hC : r.C ≤ n := by omega
  have ht : n + 1 < r.t0 := by omega
  have hpc := r.arrive H hr hC (by omega)
  have hfr := hr.arrive n hC (by omega) _ hpc
  have hb := hr.before n hC (by omega) _ hpc sy.RunningSpeed (by simp [FrameModel.hBytes])
  have hst := hr.stR n hC (by omega) _ hpc
  have hat := r.atV_of H hr hC (by omega)
  obtain ⟨hm1, hm2⟩ := H.runMin
  -- `RunningSpeed` 0 at the frame's start, so at the player's routine
  have hrs0 : peek (r.fm n) sy.RunningSpeed = 0 := by
    rw [r.hs_fm hr hC (by omega) (by omega)] at hrs
    simp only [FrameModel.readHS] at hrs
    split at hrs
    · rename_i hc
      simpa using hc
    · exact absurd hrs hm1
  have hrsK : (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.RunningSpeed) = 0 := by
    show peek _ sy.RunningSpeed = 0
    rw [hb, hrs0]
  -- the state at the player's routine
  have hsts : peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.Player_State ∈ [(0 : UInt8), 1, 2] := hat.st
  have hin : (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.Player_State) = 1 ∨
      (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.Player_State) = 2 ∨
      ((PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.Player_State) = 0 ∧
        ((PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.Player_XSpeedAbsolute) < sy.RunSpeedMin.toUInt8 ∨
          ((PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.SavedJoypadBits) &&& 0x80 = 0x80 ∧
            (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.PreviousA_B_Buttons) &&& 0x80 = 0))) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsts
    rcases hsts with e | e | e
    · refine Or.inr (Or.inr ⟨e, ?_⟩)
      by_cases hj : (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n))).jump = true
      · right
        simp only [FrameModel.readIn, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hj
        obtain ⟨⟨_, h3⟩, h4⟩ := hj
        have h5 := and80_ne ⟨((PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.SavedJoypadBits)).toNat,
          ((PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)).ram.get! (FrameModel.I sy.SavedJoypadBits)).toNat_lt⟩
        simp only [UInt8.ofNat_toNat] at h5
        exact ⟨h5 h3, h4⟩
      left
      have hj' : (r.fr.inp (n + 1)).jump = false := by
        rw [r.read_inp hC (by omega)]
        simpa using hj
      -- the stored speed below the threshold
      have hab : r.fr.ab n < sy.RunSpeedMin.toNat := by
        by_cases hs : r.fr.ab n = (sbyte (r.fr.hs n).v).natAbs
        · omega
        · by_cases hh : n + 1 < r.C + N.hitF
          · have hnc : ¬FrameModel.CleanR sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.inAt n) (r.arr n) := fun hc =>
              hf (r.follow_of_clean H hr st hC (by omega) hc)
            have h3 := r.ab_early n hC hh (by omega) hnc
            have h4 := H.air.pot.air_le_run
            omega
          · have hvs : (r.fr.vs n).st = 0 := by
              rw [r.vs_fm hr hC (by omega) (by omega)]
              show peek (r.fm n) sy.Player_State = 0
              rw [← hst]
              exact e
            exact r.ab_run n (by omega) h2 hrs hf hvs hj' hs
      have hread := r.read_ab n hC (by omega)
      show peek _ sy.Player_XSpeedAbsolute < sy.RunSpeedMin.toUInt8
      rw [UInt8.lt_iff_toNat_lt, UInt16.toNat_toUInt8, Nat.mod_eq_of_lt hm2]
      have e2 : (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) = PipeEntryRule.trace (startAt sy m S b lim r.C n) (inpAt sy m S b lim r.C n)
        (CtrlKeep.arrAt sy (startAt sy m S b lim r.C n) (inpAt sy m S b lim r.C n)) := rfl
      rw [e2]
      omega
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  have hend := hr.run n hC (by omega) _ hpc hfr hrsK hin
  rw [r.hs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  simp only [FrameModel.readHS, hend, beq_self_eq_true, if_true]

/-- **`air_in`**: a frame before `standF` that starts in the air has an air input. The input is read from the machine (`read_inp`), and at the player's routine the
player's state is that of the frame's start (`InRoom.stR`): so not 0, and no jump; and every input read from a machine is one of `inputs` (`readIn_mem`) -/
theorem air_in_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : ∀ n, r.C ≤ n → n < r.C + N.standF → (r.fr.vs n).st ≠ 0 →
    AirIn (r.fr.inp (n + 1)) := by
  intro n hC h1 hst
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hst' : peek (r.fm n) sy.Player_State ≠ 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).st = peek (r.fm n) sy.Player_State := rfl
    rw [← e, ← hv0]
    exact hst
  have hs := hr.stR n hC (by omega) _ (r.arrive H hr hC (by omega))
  rw [r.read_inp hC (by omega)]
  generalize PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n) = x at hs
  have h0 : (peek x sy.Player_State == 0) = false := by rw [hs]; simpa using hst'
  refine ⟨readIn_mem sy x, ?_, ?_⟩
  · show (if peek x sy.Player_State == 0 then (0 : UInt8) else 1) = 1
    rw [h0]
    rfl
  · show (peek x sy.Player_State == 0 && peek x sy.SavedJoypadBits &&& 0x80 != 0 && peek x sy.PreviousA_B_Buttons &&& 0x80 == 0) = false
    rw [h0]
    rfl

/-- **A frame that starts standing with no jump** ends as `StandNext` allows: from the reading of the vertical state, the jump bit (`jump_read`), and the walks of the room's
frames (`InRoom.stand`) -/
theorem vstand_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E) (hst : (r.fr.vs n).st = 0)
    (hj : (r.fr.inp (n + 1)).jump = false) : StandNext (r.fr.vs n) (r.fr.vs (n + 1)) := by
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (n + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.vs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hst' : peek (r.fm n) sy.Player_State = 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).st = peek (r.fm n) sy.Player_State := rfl
    rw [← e, ← hv0]
    exact hst
  rw [hv0, hv1]
  exact hr.stand n hC hE hst' (r.arr n) (r.arrive H hr hC ht) (r.jump_read hC ht hj)

/-- **With no jump the frame goes to a next state of `noJumpNext`**: standing as `StandNext` allows (`vstand_of`), in the air `vstepR` or its landing (`vair_of`) -/
theorem nj_next (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {d : Nat} (hd : d + 1 < N.standF) (hj : (r.fr.inp (r.C + d + 1)).jump = false) :
    r.fr.vs (r.C + (d + 1)) ∈ noJumpNext sy m (r.fr.vs (r.C + d)) := by
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  rw [show r.C + (d + 1) = r.C + d + 1 by omega]
  by_cases hs : (r.fr.vs (r.C + d)).st = 0
  · exact mem_noJumpNext_stand hs (r.vstand_of H hr (n := r.C + d) (by omega) (by omega) (by omega) hs hj)
  · exact mem_noJumpNext_air hs (r.vair_of H hr (n := r.C + d) (by omega) (by omega) (by omega) hs).2

/-- **With no jump since first control the check holds on the state**: `noJumpOk`, and not on the floor before `fall` -/
theorem nj_ok (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (hn : n + 1 < r.C + N.standF)
    (hj : ∀ j, r.C ≤ j → j < n → (r.fr.inp (j + 1)).jump = false) :
    noJumpOk sy m (r.fr.vs n) = true ∧ (n < r.C + N.fall → ¬OnFloor sy (r.fr.vs n)) := by
  have h := noJump_ok H.nojump (fun d => r.fr.vs (r.C + d)) (by simpa using r.vs_start hr) (n := n - r.C) (by omega)
    (fun d hd => r.nj_next H hr st (by omega) (hj _ (by omega) (by omega)))
  simp only [show r.C + (n - r.C) = n by omega] at h
  exact ⟨h.1, fun h1 => h.2 (by omega)⟩

/-- **`vfall`**: a frame with no jump since first control, from a state that is not in a jump, is `VDrop`. Standing it ends as `StandNext` allows (`vstand_of`); in the
air the check of the frames with no jump gives it (`noJumpCheck`) -/
theorem vfall_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : ∀ n, r.C ≤ n → n + 1 < r.C + N.standF → (r.fr.vs n).st ≠ 1 →
    (∀ j, r.C ≤ j → j ≤ n → (r.fr.inp (j + 1)).jump = false) → VDrop (r.fr.vs n) (r.fr.vs (n + 1)) := by
  intro n hC h1 _ h3
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hok := (r.nj_ok H hr st hC h1 (fun j a b => h3 j a (by omega))).1
  by_cases hs : (r.fr.vs n).st = 0
  · exact (r.vstand_of H hr hC (by omega) (by omega) hs (h3 n hC (Nat.le_refl _))).vdrop
  · have hs2 : (r.fr.vs n).st = 2 ∧ ∀ a, (vstepR sy m (r.fr.vs n) a).st = 2 ∧ VDrop (r.fr.vs n) (vstepR sy m (r.fr.vs n) a) ∧
        (falling (vstepR sy m (r.fr.vs n) a) = true → VDrop (r.fr.vs n) (VertAir.land (vstepR sy m (r.fr.vs n) a))) := by
      unfold noJumpOk at hok
      simp only [Bool.or_eq_true, beq_iff_eq, hs, false_or, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at hok
      obtain ⟨k1, k2⟩ := hok
      refine ⟨k1, fun a => ?_⟩
      have k3 := k2 a (by cases a <;> simp)
      simp only [Bool.not_eq_true'] at k3
      obtain ⟨⟨k4, k5⟩, k6⟩ := k3
      refine ⟨k4, vdropB_spec k5, fun hf => ?_⟩
      rcases k6 with k7 | k7
      · rw [hf] at k7
        cases k7
      · exact vdropB_spec k7
    obtain ⟨_, e2⟩ := r.vair_of H hr hC (by omega) (by omega) hs
    obtain ⟨_, a2, a3⟩ := hs2.2 (r.fr.a (n + 1))
    rcases e2 with e | ⟨hf, e⟩
    · rw [e]
      exact a2
    · rw [e]
      exact a3 hf

/-- **With no jump he is not on the floor during the fall**: the check of the frames with no jump -/
theorem fall_nojump (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n < r.C + N.fall)
    (hj : ∀ j, r.C ≤ j → j < n → (r.fr.inp (j + 1)).jump = false) : ¬OnFloor sy (r.fr.vs n) := by
  obtain ⟨_, hfs, _, _⟩ := fall_ok H.first
  exact (r.nj_ok H hr st hC (by omega) hj).2 h1

/-! ### The first stand of the fall -/

/-- the position at the end of frame `C + d` of the first `standF` frames is at most `d` frames of the top speed right of the start's right end -/
theorem P_upto (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) :
    ∀ d, d ≤ N.standF → r.fr.P (r.C + d) ≤ (room sy N).P1 + 16 * (top sy : Int) * (d : Int)
  | 0, _ => by
    have := (r.start_P st).2
    simpa using this
  | d + 1, hd => by
    have ih := P_upto H hr st d (by omega)
    have hfar := r.t0_far H hr st
    have hm := r.move_top_of H hr st (r.C + d) (by omega) (by omega)
    rw [show r.C + (d + 1) = r.C + d + 1 by omega]
    have e : 16 * (top sy : Int) * ((d + 1 : Nat) : Int) = 16 * (top sy : Int) * (d : Int) + 16 * (top sy : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [e]
    generalize 16 * (top sy : Int) * (d : Int) = A at ih ⊢
    generalize 16 * (top sy : Int) = B at hm ⊢
    omega

/-- **The page and the horizontal coordinate at the end of the move of a frame before `t0`**: after the player's routine, at a `PlayerSubs` of frame `n + 1`, the page is
0 and the coordinate below `X`, if `n + 1 − C ≤ d` and `d` frames of the top speed from the start, and one pixel more, are left of `X` on the first page. The frame is
`CleanW` (from the scroll handler on nothing writes the position) or `ReadW` (the frame's end is within 1 px of the scroll handler's position, `FrameModel.Collide`); the
end of the frame is at most `n + 1 − C` frames of the top speed right of the start (`P_upto`) -/
theorem q_pos (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n d X : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hd : n + 1 - r.C ≤ d)
    (hdS : d ≤ N.standF) (hX : (room sy N).P1 + 16 * (top sy : Int) * (d : Int) + 256 < 256 * (X : Int)) (hX2 : X ≤ 256) {j : Nat} (hj : r.arr n ≤ j)
    (hq : (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs) :
    (PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_PageLoc) = 0 ∧
      ((PipeEntryRule.trace (r.fm n) (r.inAt n) j).ram.get! (FrameModel.I sy.Player_X_Position)).toNat < X := by
  have hE := r.t0_le_E H hr
  have hup := r.P_upto H hr st (n + 1 - r.C) (by omega)
  have hend : r.fr.P (n + 1) = posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.P_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  rw [show r.C + (n + 1 - r.C) = n + 1 by omega, hend] at hup
  have hQ : posP sy (PipeEntryRule.trace (r.fm n) (r.inAt n) j) ≤ posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) + 256 := by
    rcases r.clean n hC ht with hc | ⟨_, hc⟩
    · have e := FrameModel.posP_congr (sy := sy) ((r.cleanR_of H hr hC ht hc).after j hj hq)
      omega
    · have hd' := (r.far_inD H hr st (n - r.C) (by omega)).2
      rw [show r.C + (n - r.C) = n by omega] at hd'
      have hc' := (r.readR_of H hr hC ht hd' hc).collide j hj hq
      rcases hc'.P with e | e | ⟨e, _⟩ <;> omega
  have hp := FrameModel.posP_eq sy (PipeEntryRule.trace (r.fm n) (r.inAt n) j)
  unfold FrameModel.posOf at hp
  have p1 := (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_PageLoc).toNat_lt
  have p2 := (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_X_Position).toNat_lt
  have p3 := (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.SprObject_X_MoveForce).toNat_lt
  have htop : 16 * (top sy : Int) * ((n + 1 - r.C : Nat) : Int) ≤ 16 * (top sy : Int) * (d : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (Int.mul_nonneg (by omega) (by omega))
  have htop0 : (0 : Int) ≤ 16 * (top sy : Int) * ((n + 1 - r.C : Nat) : Int) := Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  generalize 16 * (top sy : Int) * ((n + 1 - r.C : Nat) : Int) = T at hup htop htop0
  generalize 16 * (top sy : Int) * (d : Int) = T' at hX htop
  refine ⟨?_, ?_⟩
  · have : (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_PageLoc).toNat = 0 := by omega
    exact UInt8.toNat_inj.mp (by simpa [peek] using this)
  · show (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) j) sy.Player_X_Position).toNat < X
    omega

/-- **The page and the horizontal coordinate at the end of the move of the landing frame**: `q_pos` for frame `C + fall`, with `landP` -/
theorem landQ_pos (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {j : Nat} (hj : r.arr (r.C + (N.fall - 1)) ≤ j)
    (hq : (PipeEntryRule.trace (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1))) j).pc = sy.PlayerSubs) :
    (PipeEntryRule.trace (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1))) j).ram.get! (FrameModel.I sy.Player_PageLoc) = 0 ∧
      ((PipeEntryRule.trace (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1))) j).ram.get! (FrameModel.I sy.Player_X_Position)).toNat < N.landX := by
  obtain ⟨hf0, hfs, _, _⟩ := fall_ok H.first
  have hfar := r.t0_far H hr st
  exact r.q_pos H hr st (d := N.fall) (by omega) (by omega) (by omega) (by omega) H.landP.1 H.landP.2 hj hq

/-- **The vertical page is 1 through the first fall**, at the start of each of its frames: it is 1 at first control (`StartAt.high`); the frames between keep it
(`InRoom.keepH`); a frame of the first fall does not rise and ends with the vertical page of the machine of `vstepR` after the movement routine (`InRoom.high`), which is
1 (`highCheck`) -/
theorem high_upto (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {D : Nat} (hD : D ≤ N.fall)
    (hns : ∀ j, r.C < j → j < r.C + D → (r.fr.vs j).st ≠ 0) : ∀ d, d < D → peek (r.fm (r.C + d)) sy.Player_Y_HighPos = 1
  | 0, _ => by
    obtain ⟨hf0, hfs, _, _⟩ := fall_ok H.first
    have hfar := r.t0_far H hr st
    have hE := r.t0_le_E H hr
    rw [Nat.add_zero, hr.keepH r.C (Nat.le_refl _) (by omega)]
    exact st.high
  | d + 1, hd => by
    obtain ⟨hf0, hfs, _, _⟩ := fall_ok H.first
    have hfar := r.t0_far H hr st
    have hE := r.t0_le_E H hr
    have ih := high_upto H hr st hD hns d (by omega)
    have hC : r.C ≤ r.C + d := by omega
    have ht : r.C + d < r.t0 := by omega
    have hE' : r.C + d + 1 < r.E := by omega
    have hmem := r.fall_mem H hr st d (by omega) (fun j a b => hns j a (by omega))
    have hv0 : r.fr.vs (r.C + d) = VertModel.vsOf sy (r.fm (r.C + d)) := r.vs_fm hr hC (by omega) (by omega)
    have hok := (fall_ok H.first).2.2.2 d (by omega) _ hmem
    have hst' : peek (r.fm (r.C + d)) sy.Player_State ≠ 0 := by
      have e : (VertModel.vsOf sy (r.fm (r.C + d))).st = peek (r.fm (r.C + d)) sy.Player_State := rfl
      rw [← e, ← hv0, (fallOk_spec hok).1]
      decide
    rw [hv0] at hmem
    have hc := highCheck_spec H.high (d := d) (by omega) hmem
    have hend := (hr.high (r.C + d) hC hE' hst' (r.arr (r.C + d)) (r.atV_of H hr hC ht)
      (hr.pair (r.C + d) hC (by omega)).1 (hr.pair (r.C + d) hC (by omega)).2 ih).2 (hc _).1
    rw [show r.C + (d + 1) = r.C + d + 1 by omega, hr.keepH (r.C + d + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
    exact hend.trans (hc _).2

/-- **The vertical page is 1 through the first fall** (`high_upto` up to its end) -/
theorem high_fall (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C))
    (hns : ∀ j, r.C < j → j < r.C + N.fall → (r.fr.vs j).st ≠ 0) : ∀ d, d < N.fall → peek (r.fm (r.C + d)) sy.Player_Y_HighPos = 1 :=
  r.high_upto H hr st (Nat.le_refl _) hns

/-- at a `PlayerSubs` of frame `n + 1` before `t0` the position is at most 1 px right of the frame's end: the frame is `CleanW` (from the scroll handler on nothing
writes the position) or `ReadW` (`FrameModel.Collide`), as in `q_pos` -/
theorem q_le_end (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) {j : Nat} (hj : r.arr n ≤ j)
    (hq : (PipeEntryRule.trace (r.fm n) (r.inAt n) j).pc = sy.PlayerSubs) :
    posP sy (PipeEntryRule.trace (r.fm n) (r.inAt n) j) ≤ posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) + 256 := by
  rcases r.clean n hC ht with hc | ⟨_, hc⟩
  · have e := FrameModel.posP_congr (sy := sy) ((r.cleanR_of H hr hC ht hc).after j hj hq)
    omega
  · have hd' := (r.far_inD H hr st (n - r.C) (by omega)).2
    rw [show r.C + (n - r.C) = n by omega] at hd'
    have hc' := (r.readR_of H hr hC ht hd' hc).collide j hj hq
    rcases hc'.P with e | e | ⟨e, _⟩ <;> omega

/-- a machine whose position is left of `X` px on the first page (`X ≤ 256`) has the page 0 and x below `X` -/
theorem page_x_of {q : Machine} {X : Nat} (h : posP sy q < 256 * (X : Int)) (hX : X ≤ 256) :
    q.ram.get! (FrameModel.I sy.Player_PageLoc) = 0 ∧ (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat < X := by
  have hp := FrameModel.posP_eq sy q
  unfold FrameModel.posOf at hp
  have p1 := (peek q sy.Player_PageLoc).toNat_lt
  have p2 := (peek q sy.Player_X_Position).toNat_lt
  have p3 := (peek q sy.SprObject_X_MoveForce).toNat_lt
  refine ⟨?_, ?_⟩
  · have : (peek q sy.Player_PageLoc).toNat = 0 := by omega
    exact UInt8.toNat_inj.mp (by simpa [peek] using this)
  · show (peek q sy.Player_X_Position).toNat < X
    omega

theorem speed_byte_ne {v : UInt8} (h : 129 ≤ v.toNat) : v ≠ 0 := fun e => by rw [e] at h; exact absurd h (by decide)

/-! ### Round 30: the position before the first stand, on the real run -/

theorem start_fallR (H : Checks sy m N) (st : StartAt sy N (r.fe r.C)) : FallSt sy (r.fr.hs r.C) := by
  have h := H.nums.air_pos
  rw [r.start_hs st]
  refine ⟨?_, ?_, rfl, rfl⟩
  · have h1 := H.roomOk
    simp only [roomCheck, Bool.and_eq_true] at h1
    exact h1.1.1
  · show capped sy { v := 0, f := 0, fd := 1, md := 0, rs := 0 } = true
    simp only [capped, decide_eq_true_eq]
    have h2 : (sbyte (0 : UInt8)).natAbs = 0 := by decide
    rw [h2]
    omega

theorem psiP_startR (st : StartAt sy N (r.fe r.C)) : psiP sy m (r.fr.hs r.C) ≤ phi sy m (room sy N).s0 := by
  rw [r.start_hs st]
  have h : (0 : Int) ≤ V (room sy N).s0 := by
    have h1 : (room sy N).s0 = { v := 0, f := 0, fd := 1, md := 0, rs := 0 } := rfl
    rw [h1]
    unfold V
    have h2 : sbyte (0 : UInt8) = 0 := by decide
    rw [h2]
    omega
  rw [← psiP_eq_phi h]
  exact Int.le_refl _

theorem fall_runR (H : Checks sy m N) {a : Nat} {p : Int} (hst : FallSt sy (r.fr.hs a)) (hp : psiP sy m (r.fr.hs a) ≤ p) :
    ∀ j, (∀ i, a ≤ i → i < a + j → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1))) →
      FallSt sy (r.fr.hs (a + j)) ∧ psiP sy m (r.fr.hs (a + j)) ≤ p + a1 sy m * (j : Int) ∧
        r.fr.P (a + j) ≤ r.fr.P a + airDist sy m p j
  | 0, _ => by simpa [airDist] using And.intro hst hp
  | j + 1, h => by
    obtain ⟨h1, h2, h3⟩ := fall_runR H hst hp j (fun i h4 h5 => h i h4 (by omega))
    obtain ⟨h4, h5⟩ := h (a + j) (by omega) (by omega)
    obtain ⟨h6, h7, h8⟩ := air_step H h1 h5
    have h9 := v_le_psiP H.air.pot (hstep sy m (r.fr.hs (a + j)) (r.fr.inp (a + j + 1)))
    rw [show a + (j + 1) = a + j + 1 by omega, h4.2.1]
    have h10 := h4.2.2
    rw [h4.2.1] at h10
    have hm : a1 sy m * ((j + 1 : Nat) : Int) = a1 sy m * (j : Int) + a1 sy m := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    refine ⟨h6, by rw [hm]; omega, ?_⟩
    simp only [airDist]
    rw [hm]
    omega

theorem anchor_PR (H : Checks sy m N) {w a : Nat} (ha : RoomCore.Anchor sy m N r.fr r.C w a) :
    r.fr.P w ≤ N.wallP + dbound sy m N.stopPhi (w - (r.C + N.wallF)) := by
  have hF := H.air.pot
  have hfol : ∀ j, a ≤ j → j < a + (w - a) → Follow sy m r.fr j := fun j h1 h2 => ha.fol j h1 (by have := ha.le; omega)
  have h1 := hdist_seg a (w - a) hfol
  have h2 := dist_le hF _ _ _ ha.J' (inputs_seg a (w - a) hfol)
  rw [length_seg] at h2
  have hle := ha.le
  have hge := ha.ge
  rw [show a + (w - a) = w by omega] at h1
  obtain ⟨k, hk⟩ : ∃ k, w - (r.C + N.wallF) = (w - a) + k := ⟨a - (r.C + N.wallF), by omega⟩
  have h3 := dbound_mono hF (w - a) k N.stopPhi H.nums.stop_nonneg
  rw [← hk] at h3
  have h4 := ha.P_le
  omega

theorem left_farR (H : Checks sy m N) (st : StartAt sy N (r.fe r.C)) {h K : Nat} {X : Int} (h1 : r.C ≤ h) (h2 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j)
    (hP : r.fr.P h ≤ X) (hf : X < (room sy N).P0 - leftDist sy m (phi sy m (room sy N).s0) K) : r.C + K < h := by
  by_cases hc : r.C + K < h
  · exact hc
  · exfalso
    have hF := H.air.pot
    have hfol : ∀ j, r.C ≤ j → j < r.C + (h - r.C) → Follow sy m r.fr j := fun j h3 h4 => h2 j h3 (by omega)
    have h3 := hdist_seg r.C (h - r.C) hfol
    rw [show r.C + (h - r.C) = h by omega] at h3
    have hJ : J sy m (r.fr.hs r.C) (phi sy m (room sy N).s0) := by
      refine ⟨(r.start_fallR H st).dom, by rw [r.start_hs st]; exact Int.le_refl _, fun h4 => absurd (r.start_fallR H st).rs h4⟩
    have h4 := left_dist_le hF _ _ _ hJ (inputs_seg r.C (h - r.C) hfol)
    rw [length_seg] at h4
    obtain ⟨k, hk⟩ : ∃ k, K = (h - r.C) + k := ⟨K - (h - r.C), by omega⟩
    have h5 := leftDist_mono hF (h - r.C) k _ (RoomCore.phi0_nonneg H)
    rw [← hk] at h5
    have h7 := (r.start_P st).1
    omega

theorem wall_firstR (H : Checks sy m N) (st : StartAt sy N (r.fe r.C)) {h : Nat} (h1 : r.C ≤ h) (h2 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j)
    (hP : r.fr.P h ≤ N.wallP) : r.C + N.wallF ≤ h + 1 := by
  have h3 := r.left_farR H st h1 h2 hP H.nums.wall_far
  have h4 := H.nums.wall_two
  omega

theorem anchor_atR (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {h : Nat} (h1 : r.C ≤ h) (h2 : h + 1 < r.C + N.hitF) (h3 : ¬Follow sy m r.fr h)
    (h4 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j) (ht : h < r.t0) :
    ∀ d, h + 1 + d ≤ r.C + N.runF + 1 → h + 1 + d ≤ r.t0 → ∃ a, RoomCore.Anchor sy m N r.fr r.C (h + 1 + d) a
  | 0, _, _ => by
    have hw := r.wall h h1 h2 h3
    have hs := (r.frames_of H hr st h h1 ht).resolve_left h3
    exact ⟨h + 1, r.wall_firstR H st h1 h4 hw.before, by omega, hw.after, ⟨hs.1, hs.2.1, fun h5 => absurd hw.run h5⟩, hw.run,
      fun i h5 h6 => by omega⟩
  | d + 1, h5, h6 => by
    obtain ⟨a, ha⟩ := anchor_atR H hr st h1 h2 h3 h4 ht d (by omega) (by omega)
    rw [show h + 1 + (d + 1) = h + 1 + d + 1 by omega] at h6 ⊢
    have hC : r.C ≤ h + 1 + d := by omega
    by_cases hf : Follow sy m r.fr (h + 1 + d)
    · refine ⟨a, ha.ge, by have := ha.le; omega, ha.P_le, ha.J', ha.rs, fun i h7 h8 => ?_⟩
      by_cases h9 : i < h + 1 + d
      · exact ha.fol i h7 h9
      · rw [show i = h + 1 + d by omega]
        exact hf
    · have hw : WallAt N r.fr (h + 1 + d) := by
        by_cases h7 : h + 1 + d + 1 < r.C + N.hitF
        · exact r.wall _ hC h7 hf
        · rcases r.late _ (by omega) (by omega) ⟨h, h1, by omega, h2, h3⟩ hf with h8 | h8
          · exact h8
          · exfalso
            have hn := H.nums
            have h9 := r.anchor_PR H ha
            have hge := ha.ge
            obtain ⟨k, hk⟩ : ∃ k, N.runF - N.wallF = (h + 1 + d - (r.C + N.wallF)) + k :=
              ⟨N.runF - N.wallF - (h + 1 + d - (r.C + N.wallF)), by omega⟩
            have h10 := dbound_mono H.air.pot (h + 1 + d - (r.C + N.wallF)) k N.stopPhi hn.stop_nonneg
            rw [← hk] at h10
            have h11 := hn.wall_late
            omega
      have hs := (r.frames_of H hr st _ hC (by omega)).resolve_left hf
      exact ⟨h + 1 + d + 1, by have := ha.ge; have := ha.le; omega, by omega, hw.after,
        ⟨hs.1, hs.2.1, fun h7 => absurd hw.run h7⟩, hw.run, fun i h7 h8 => by omega⟩


/-- **Before the first stand of the fall he is at least one pixel left of the block's corner** (round 30), on the real run: `RoomCore.corner_late` with the frames
before the stand. With no hit, the frames of the fall are air frames (`air_in_of`, the states before the stand), and the potential of the fall gives the position
(`fall_runR`); after a hit, the last wall frame and the potential from there (`anchor_atR`, `anchor_PR`). The check `WallFacts.fallQ`. The lemmas `start_fallR`,
`psiP_startR`, `fall_runR`, `anchor_PR`, `left_farR`, `wall_firstR`, `anchor_atR` are those of `RoomCore` with the fields of `RoomRun`: `RoomCore`'s use `stand_off`
and `fall_long`, whose proofs use `stand_first` -/
theorem fall_left (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {k : Nat} (h1 : r.C ≤ k) (h2 : k < r.C + N.fall)
    (hns : ∀ j, r.C < j → j < k → (r.fr.vs j).st ≠ 0) : r.fr.P k + 256 < cornerP sy := by
  have hN := H.nums
  have hg := hN.hit_ge
  have hA := hN.air_pos
  have hle := hN.fall_le
  have hQ := H.standW.fallQ
  have hfar := r.t0_far H hr st
  by_cases hall : ∀ j, r.C ≤ j → j < k → Follow sy m r.fr j
  · have hair : ∀ i, r.C ≤ i → i < r.C + (k - r.C) → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h4 h5 => by
      refine ⟨hall i h4 (by omega), r.air_in_of H hr st i h4 (by omega) ?_⟩
      by_cases he : i = r.C
      · rw [he, (r.start_v st).1]; decide
      · exact hns i (by omega) (by omega)
    have hp := r.psiP_startR st
    have hp0 := RoomCore.phi0_nonneg H
    obtain ⟨_, _, h4⟩ := r.fall_runR H (r.start_fallR H st) hp (k - r.C) hair
    rw [show r.C + (k - r.C) = k by omega] at h4
    obtain ⟨c, hc⟩ : ∃ c, N.fall = (k - r.C) + c := ⟨N.fall - (k - r.C), by omega⟩
    have h5 := airDist_mono (sy := sy) (m := m) hp0 hN.a1_nonneg (k - r.C) c
    rw [← hc] at h5
    have hP1 := (r.start_P st).2
    omega
  · obtain ⟨h, h4, h5, h6, h7⟩ := RoomCore.first_hit _ hall
    obtain ⟨a, ha⟩ := r.anchor_atR H hr st h4 (by omega) h6 h7 (by omega) (k - (h + 1)) (by have := hN.hit_run; omega) (by omega)
    rw [show h + 1 + (k - (h + 1)) = k by omega] at ha
    have h8 := r.anchor_PR H ha
    have hge := ha.ge
    have hle2 := ha.le
    obtain ⟨c, hc⟩ : ∃ c, N.fall - N.wallF = (k - (r.C + N.wallF)) + c := ⟨N.fall - N.wallF - (k - (r.C + N.wallF)), by omega⟩
    have h9 := dbound_mono H.air.pot (k - (r.C + N.wallF)) c N.stopPhi hN.stop_nonneg
    rw [← hc] at h9
    omega

/-- **The first stand of the fall does not follow `hstep`**: a frame `n + 1` before `C + fall`, with no stand from first control to frame `n`, that ends standing away
from the floor. Under `Follow` the speed at its end is that of `hstep` from the frame before, which moves left at `standV` or more (the field `stand_fast`): a byte from
129 on (`WallFacts`, `negJ_of_check`), not 0. The field `clean` makes it the speed at the end of the move `Q`. The state at frame `n` is one of the first fall
(`fall_mem`), in the air, so at `Q` the vertical bytes are those of `vstepR` (`InRoom.wall`): the state 2 (`fallCheck`), the vertical speed not negative and the
vertical page 1 (`highCheck`, `high_upto`, `InRoom.high`), the height from 32 to 206 (`wallYCheck`). The frame's end is more than one pixel left of the block's corner
(`fall_left`, round 30; until then the field `stand_P`), and `Q` is at most 1 px right of it (`q_le_end`): the page 0 and x below `cornerX`. With x from 13 on, `Q`
meets `WallF` (its height is one of the first fall, `ysFall`) and the frame ends with the state not 0 (`InRoom.wall`). With x at most 12, `Q` meets `WallQ`, and the frame
ends with the state not 0, or standing at the floor's height, or with the speed 0 (`InRoom.wall`): each is false. Uses the fields `stand_fast`, `clean`, `wall`, `late` and
those of `far_inD`, `t0_far`; not `stand_wall` -/
theorem stand_first (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n + 1 < r.C + N.fall)
    (hns : ∀ j, r.C < j → j ≤ n → (r.fr.vs j).st ≠ 0) (h0 : (r.fr.vs (n + 1)).st = 0) (hnf : ¬OnFloor sy (r.fr.vs (n + 1))) : ¬Follow sy m r.fr n := by
  intro hf
  obtain ⟨hf0, hfs, _, _⟩ := fall_ok H.first
  have hle := H.nums.fall_le
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have W := H.standW
  obtain ⟨d, rfl⟩ : ∃ d, n = r.C + d := ⟨n - r.C, by omega⟩
  have hC' : r.C ≤ r.C + d := by omega
  have ht : r.C + d < r.t0 := by omega
  have hE' : r.C + d + 1 < r.E := by omega
  have hd : d < N.fall := by omega
  -- the speed at the frame's end: `hstep`'s, a byte from 129 on
  have hD : inD sy (r.fr.hs (r.C + d)) = true := (r.far_inD H hr st d (by omega)).2
  have hsf := r.stand_fast (r.C + d) hC' h1 (Or.inl hf) h0
  have hneg := negJ_of_check W.sp H.normI W.neg1 W.neg2 W.neg3 (r.fr.hs (r.C + d)) hD (by omega) (r.fr.inp (r.C + d + 1)) hf.1
  rw [← hf.2.1] at hneg
  have hv : (r.fr.hs (r.C + d + 1)).v = peek (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) sy.Player_X_Speed := by
    rw [r.hs_fe (n := r.C + d + 1) (by omega) (by omega), r.next hC' (r.ups_lt hr hC' (by omega))]
    rfl
  rw [hv] at hneg
  have hne := speed_byte_ne hneg
  -- the state at frame `n`: one of the first fall, in the air
  have hmem := r.fall_mem H hr st d (by omega) hns
  have hv0 : r.fr.vs (r.C + d) = VertModel.vsOf sy (r.fm (r.C + d)) := r.vs_fm hr hC' (by omega) (by omega)
  have hok := (fall_ok H.first).2.2.2 d (by omega) _ hmem
  have hst' : peek (r.fm (r.C + d)) sy.Player_State ≠ 0 := by
    have e : (VertModel.vsOf sy (r.fm (r.C + d))).st = peek (r.fm (r.C + d)) sy.Player_State := rfl
    rw [← e, ← hv0, (fallOk_spec hok).1]
    decide
  have hcl := r.atV_of H hr hC' ht
  have hp1 := (hr.pair (r.C + d) hC' (by omega)).1
  have hp2 := (hr.pair (r.C + d) hC' (by omega)).2
  obtain ⟨j, hkj, hq, hfj, hvj, himp, -, -, himpF⟩ := hr.wall (r.C + d) hC' hE' hst' (r.arr (r.C + d)) hcl hp1 hp2
  generalize ha : (peek (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) (r.arr (r.C + d))) sy.SavedJoypadBits &&& 0x80 != 0) = a at hvj
  have hmem' : VertModel.vsOf sy (r.fm (r.C + d)) ∈ fallLayer sy m N.vStart d := by rw [← hv0]; exact hmem
  have hok' : fallOk sy m N d (VertModel.vsOf sy (r.fm (r.C + d))) = true := by rw [← hv0]; exact hok
  have hc := highCheck_spec H.high hd hmem' a
  have hyc := wallYCheck_spec W.y hd hmem' a
  have hs2 := (fallStep_spec ((fallOk_spec hok').2 a)).1
  -- the vertical page at `Q`
  have hhi : peek (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) sy.Player_Y_HighPos = 1 := by
    have hh := r.high_upto H hr st (D := d + 1) (by omega) (fun j a b => hns j a (by omega)) d (by omega)
    have e := ((hr.high (r.C + d) hC' hE' hst' (r.arr (r.C + d)) hcl hp1 hp2 hh).1 j hkj hq hfj)
    rw [e, ha]
    exact (highCheck_spec H.high hd hmem' a).2
  -- the page and x at `Q`: left of the block's corner (`fall_left`)
  have hPe : r.fr.P (r.C + d + 1) = posP sy (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) := by
    rw [r.P_fe (n := r.C + d + 1) (by omega) (by omega), r.next hC' (r.ups_lt hr hC' (by omega))]
  have hfl := r.fall_left H hr st (k := r.C + d + 1) (by omega) h1 (fun j a b => hns j a (by omega))
  have hQe := r.q_le_end H hr st hC' ht hkj hq
  have hcx := H.corner.cx
  have hcx5 := H.corner.cx5
  have hpx := page_x_of (sy := sy) (X := cornerX sy) (q := PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) (by omega) (by omega)
  have ey : (VertModel.vsOf sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j)).y =
      (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_Y_Position) := rfl
  have es : (VertModel.vsOf sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j)).st =
      (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_State) := rfl
  have ev : (VertModel.vsOf sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j)).vy =
      (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_Y_Speed) := rfl
  rw [hvj] at ey es ev
  -- the frame's end
  have hv1 : r.fr.vs (r.C + d + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) := by
    rw [r.vs_fe (n := r.C + d + 1) (by omega) (by omega), r.next hC' (r.ups_lt hr hC' (by omega))]
  have hend0 : peek (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) sy.Player_State = 0 := by
    have e2 : (VertModel.vsOf sy (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d)))).st =
        peek (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) sy.Player_State := rfl
    rw [← e2, ← hv1]
    exact h0
  by_cases h13 : 13 ≤ ((PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_X_Position)).toNat
  · -- x from 13 to the one before `cornerX`: no foot in a solid cell (`WallF`)
    have hWF : WallF sy (ysFall sy m N) (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) := by
      refine ⟨hhi, hpx.1, h13, hpx.2, ?_, ?_, ?_⟩
      · rw [← ey]; exact mem_ysFall (by omega) hmem' a
      · rw [← es, hs2]
      · rw [← ev]; exact hc.1
    exact himpF hWF hend0
  -- x at most 12: `WallQ`
  -- the speed at `Q`
  have hvq : peek (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) sy.Player_X_Speed =
      peek (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) sy.Player_X_Speed := by
    rcases r.clean (r.C + d) hC' ht with hcw | ⟨_, hcw⟩
    · exact hcw.after j hkj hq _ (by simp [FrameModel.hBytes])
    · rcases (hcw.collide j hkj hq).v with e | e
      · exact e
      · exact absurd e hne
  have hW : WallQ sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) := by
    refine ⟨hhi, hpx.1, by omega, ?_, ?_, ?_, ?_, Or.inr ?_⟩
    · rw [← ey]; exact hyc.1
    · rw [← ey]; exact hyc.2
    · rw [← es, hs2]; decide
    · rw [← ev]; exact hc.1
    · show 129 ≤ (peek (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) sy.Player_X_Speed).toNat
      rw [← hvq]
      exact hneg
  rcases himp hW with e | ⟨_, e⟩ | e
  · exact e hend0
  · apply hnf
    refine ⟨h0, ?_⟩
    have e2 : (VertModel.vsOf sy (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d)))).y =
        peek (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) sy.Player_Y_Position := rfl
    rw [hv1, e2, e]
    have := W.ground
    simp
    omega
  · exact hne e

/-- `J` along frames that follow `hstep`, on the real run (as `RoomCore.J_run`) -/
theorem J_runR (F : Facts sy m) : ∀ (d u : Nat) (p : Int), J sy m (r.fr.hs u) p → (∀ i, u ≤ i → i < u + d → Follow sy m r.fr i) →
    J sy m (r.fr.hs (u + d)) (iterN sy m p d)
  | 0, _, _, h, _ => h
  | d + 1, u, p, h, hf => by
    have h1 := hf u (Nat.le_refl _) (by omega)
    have h2 := (step_J F h h1.1).1
    rw [← h1.2.1] at h2
    have h3 := J_runR F d (u + 1) _ h2 (fun i h4 h5 => hf i (by omega) (by omega))
    rwa [show u + 1 + d = u + (d + 1) by omega] at h3

/-- the arithmetic of `stand_hit_of` at the end of the move: one frame from at or left of `W`, with the speed with its fraction at most `Φ`, ends its move at most
`(Φ + A) / 16` right of its start -/
theorem hitQ_arith {P PQ v v₁ f f₁ v₂ f₂ A W Φ : Int} (hmove : PQ = P + 16 * v₂) (hP : P ≤ W) (hxQ : W + (Φ + A) / 16 < 256 * 17)
    (hV : ((256 * v + f).natAbs : Int) ≤ Φ) (han : (v₁ = v ∧ f₁ = f) ∨ (v₁ = 0 ∧ f₁ = 0)) (hgain : 256 * v₂ + f₂ ≤ max (256 * v₁ + f₁) 0 + A) (hf2 : 0 ≤ f₂) :
    PQ < 256 * 17 := by
  rcases han with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> subst a1 a2 <;> omega

/-- the arithmetic of `stand_hit_of` for the move: from `PQ` below 13 px, the start was at most the speed `Φ`, one adder `A` and a fraction left of it -/
theorem hitP_arith {P PQ v v₁ f f₁ v₂ f₂ A Φ S : Int} (hmove : PQ = P + 16 * v₂) (hPQ : PQ < 256 * 13) (hf2 : f₂ ≤ 255)
    (hV : ((256 * v + f).natAbs : Int) ≤ Φ) (han : (v₁ = v ∧ f₁ = f) ∨ (v₁ = 0 ∧ f₁ = 0)) (hlow : min (256 * v₁ + f₁) 0 - A ≤ 256 * v₂ + f₂)
    (hX : 16 * (256 * 13 - 1) + Φ + A + 255 ≤ 16 * S + 15) : P ≤ S := by
  rcases han with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> subst a1 a2 <;> omega

/-- a machine on the page 0 with x below `X` is left of `X` px -/
theorem pos_lt_of {q : Machine} {X : Nat} (hp : q.ram.get! (FrameModel.I sy.Player_PageLoc) = 0)
    (hx : (q.ram.get! (FrameModel.I sy.Player_X_Position)).toNat < X) : posP sy q < 256 * (X : Int) := by
  have hpe := FrameModel.posP_eq sy q
  unfold FrameModel.posOf at hpe
  have p3 := (peek q sy.SprObject_X_MoveForce).toNat_lt
  have e0 : (peek q sy.Player_PageLoc).toNat = 0 := by
    show (q.ram.get! (FrameModel.I sy.Player_PageLoc)).toNat = 0
    rw [hp]; rfl
  have ex : (peek q sy.Player_X_Position).toNat < X := hx
  omega

/-- **The first stand of the fall, when it is the first frame that does not follow `hstep` and comes before `C + wallF + 1`: the frame before is at or left of
`standP`** (round 30). The frame is not `CleanW` (that frame would follow `hstep`), so it is a `TopSpeed.Frame` with the friction's lower bound
(`FrameModel.frame_readQL`), whose end of the move is the one `PlayerSubs` of `InRoom.wall`. Every frame before follows `hstep`, so the speed at the frame's start is
at most the potential of `iterN` from the start (`J_runR`). The field `wall` puts the frame's start at or left of `wallP`, so the end of the move is left of 17 px on the
first page (`standX`). There the vertical bytes are those of the first fall (`fall_mem`): the state 2, the vertical speed not negative, the vertical page 1 (`highCheck`), the
height from 32 to one above the floor's (`wallYCheck`, `wallYCheckX`). So with x from 13 to 16 the frame would end with the state not 0 (`InRoom.wall` with `WallX`): x is at
most 12. So the move takes him left by at most that speed, one adder and a fraction (`frame_readQL`, `standX`). Uses the fields `wall` and `clean`; not `stand_P`,
`stand_fast`, `stand_wall` -/
theorem stand_hit_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n + 1 < r.C + N.fall)
    (hW : n < r.C + N.wallF) (hall : ∀ j, r.C ≤ j → j < n → Follow sy m r.fr j) (hnf : ¬Follow sy m r.fr n)
    (hns : ∀ j, r.C < j → j ≤ n → (r.fr.vs j).st ≠ 0) (h0 : (r.fr.vs (n + 1)).st = 0) : r.fr.P n ≤ N.standP := by
  have hle := H.nums.fall_le
  have hhit := H.nums.hit_ge
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have W := H.standW
  have eg : gFast sy m = amax sy m := rfl
  obtain ⟨d, rfl⟩ : ∃ d, n = r.C + d := ⟨n - r.C, by omega⟩
  have hC' : r.C ≤ r.C + d := by omega
  have ht : r.C + d < r.t0 := by omega
  have hE' : r.C + d + 1 < r.E := by omega
  have hd : d < N.fall := by omega
  -- a `TopSpeed.Frame` with the friction's lower bound
  have hD : inD sy (r.fr.hs (r.C + d)) = true := r.inD_of H hr st d (by omega)
  rcases r.clean (r.C + d) hC' ht with hc | ⟨_, hc⟩
  · exact absurd (r.follow_of_clean H hr st hC' ht (r.cleanR_of H hr hC' ht hc)) hnf
  have hR := r.readR_of H hr hC' ht hD hc
  obtain ⟨idle, hT⟩ := r.inTime_of H hr
  obtain ⟨f, kB, e1, e2, e3, _, _, _, hpcB, hfB, eP2, _, _, hlow⟩ := FrameModel.frame_readQL H.model H.fric H.fricLow hR
    (r.before_of H hr hC' ht hR.at_frame.pc) (hT (r.C + d) hC' ht hR.at_frame.pc) (r.far_of H hr st hC' ht)
  have eV : V (r.fr.hs (r.C + d)) = 256 * f.v + f.f := by
    rw [e1, e2, r.hs_fm hr hC' (by omega) (by omega)]
    rfl
  have eP : r.fr.P (r.C + d) = f.P := by rw [r.P_fm hr hC' (by omega) (by omega), e3]
  -- the speed at the start: at most the potential from the start
  have hJ0 : J sy m (r.fr.hs r.C) (phi sy m (room sy N).s0) := by
    refine ⟨by simpa using r.inD_of H hr st 0 (by omega), by rw [r.start_hs st]; exact Int.le_refl _, fun h => absurd ?_ h⟩
    rw [r.start_hs st]
    rfl
  have hJ := J_runR r H.air.pot d r.C _ hJ0 (fun i h3 h4 => hall i h3 (by omega))
  have hphi := hJ.2.1
  have hVabs := phi_ge H.air.pot (r.fr.hs (r.C + d))
  have hX := List.all_eq_true.mp W.standX d (List.mem_range.2 (by omega))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hX
  have hV' : ((V (r.fr.hs (r.C + d))).natAbs : Int) ≤ iterN sy m (phi sy m (room sy N).s0) d := Int.le_trans hVabs hphi
  rw [eV] at hV'
  -- the frame's start is at or left of `wallP`
  have hw := (r.wall (r.C + d) hC' (by omega) hnf).before
  have hgain := f.friction_gain
  have hfrac := f.frac
  have hmove := f.move
  have han := f.anim
  -- the end of the move: the one `PlayerSubs` of `InRoom.wall`
  have hmem := r.fall_mem H hr st d (by omega) hns
  have hv0 : r.fr.vs (r.C + d) = VertModel.vsOf sy (r.fm (r.C + d)) := r.vs_fm hr hC' (by omega) (by omega)
  have hok := (fall_ok H.first).2.2.2 d (by omega) _ hmem
  have hst' : peek (r.fm (r.C + d)) sy.Player_State ≠ 0 := by
    have e : (VertModel.vsOf sy (r.fm (r.C + d))).st = peek (r.fm (r.C + d)) sy.Player_State := rfl
    rw [← e, ← hv0, (fallOk_spec hok).1]
    decide
  have hcl := r.atV_of H hr hC' ht
  have hp1 := (hr.pair (r.C + d) hC' (by omega)).1
  have hp2 := (hr.pair (r.C + d) hC' (by omega)).2
  obtain ⟨j, hkj, hq, hfj, hvj, _, huq, himpX, -⟩ := hr.wall (r.C + d) hC' hE' hst' (r.arr (r.C + d)) hcl hp1 hp2
  have hjB : r.arr (r.C + d) + kB = j := huq _ (Nat.le_add_right _ _) hpcB hfB
  rw [hjB] at eP2
  generalize ha : (peek (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) (r.arr (r.C + d))) sy.SavedJoypadBits &&& 0x80 != 0) = a at hvj
  have hmem' : VertModel.vsOf sy (r.fm (r.C + d)) ∈ fallLayer sy m N.vStart d := by rw [← hv0]; exact hmem
  have hok' : fallOk sy m N d (VertModel.vsOf sy (r.fm (r.C + d))) = true := by rw [← hv0]; exact hok
  have hc := highCheck_spec H.high hd hmem' a
  have hyc := wallYCheck_spec W.y hd hmem' a
  have hyx := wallYCheckX_spec W.yX (by omega) hmem' a
  have hs2 := (fallStep_spec ((fallOk_spec hok').2 a)).1
  have hhi : peek (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) sy.Player_Y_HighPos = 1 := by
    have hh := r.high_upto H hr st (D := d + 1) (by omega) (fun j a b => hns j a (by omega)) d (by omega)
    have e := ((hr.high (r.C + d) hC' hE' hst' (r.arr (r.C + d)) hcl hp1 hp2 hh).1 j hkj hq hfj)
    rw [e, ha]
    exact (highCheck_spec H.high hd hmem' a).2
  -- left of 17 px at the end of the move
  have hQ16 : posP sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) < 256 * (17 : Nat) := by
    rw [← eP2]
    have hP' : f.P ≤ N.wallP := by rw [← eP]; exact hw
    have h := hitQ_arith hmove hP' hX.1 hV' han hgain hfrac.1
    omega
  have hpx := page_x_of (sy := sy) (X := 17) (q := PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) hQ16 (by decide)
  -- x at most 12 there: with 13 to 15 the frame would end in the air
  have hv1 : r.fr.vs (r.C + d + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) := by
    rw [r.vs_fe (n := r.C + d + 1) (by omega) (by omega), r.next hC' (r.ups_lt hr hC' (by omega))]
  have hx12 : ((PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_X_Position)).toNat < 13 := by
    by_cases h13 : 13 ≤ ((PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_X_Position)).toNat
    · exfalso
      have ey : (VertModel.vsOf sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j)).y =
          (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_Y_Position) := rfl
      have es : (VertModel.vsOf sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j)).st =
          (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_State) := rfl
      have ev : (VertModel.vsOf sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j)).vy =
          (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j).ram.get! (FrameModel.I sy.Player_Y_Speed) := rfl
      rw [hvj] at ey es ev
      have hWX : WallX sy (PipeEntryRule.trace (r.fm (r.C + d)) (r.inAt (r.C + d)) j) := by
        refine ⟨hhi, hpx.1, h13, hpx.2, ?_, ?_, ?_, ?_⟩
        · rw [← ey]; exact hyc.1
        · rw [← ey]; exact hyx
        · rw [← es, hs2]; decide
        · rw [← ev]; exact hc.1
      apply himpX hWX
      have e2 : (VertModel.vsOf sy (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d)))).st =
          peek (PipeTransition.frame (r.fm (r.C + d)) (r.inAt (r.C + d))) sy.Player_State := rfl
      rw [← e2, ← hv1]
      exact h0
    · omega
  have hQ13 := pos_lt_of (sy := sy) hpx.1 hx12
  -- the move: at most the speed of the start, one adder and a fraction
  rw [eP]
  have hPQ : f.P₂ < 256 * 13 := by rw [eP2]; omega
  exact hitP_arith hmove hPQ hfrac.2 hV' han hlow hX.2

/-- **He stands away from the floor before `standF` only at the end of a frame that does not follow `hstep`**: the first stand of the fall by `stand_first`, the
others by the field `stand_wall` -/
theorem stand_off_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) :
    ∀ n, r.C ≤ n → n + 1 < r.C + N.standF →
      (n + 1 < r.C + N.fall ∨ ∃ j, r.C < j ∧ j ≤ n ∧ (r.fr.vs j).st = 0 ∧ ∀ l, j ≤ l → l ≤ n → (r.fr.inp (l + 1)).jump = false) → (r.fr.vs (n + 1)).st = 0 →
      ¬OnFloor sy (r.fr.vs (n + 1)) → ¬Follow sy m r.fr n := by
  intro n hC h1 hs h0 hf
  by_cases h : ∃ j, r.C < j ∧ j ≤ n ∧ (r.fr.vs j).st = 0
  · exact r.stand_wall n hC h1 h hs h0 hf
  · rcases hs with h2 | ⟨j, h2, h3, h4, _⟩
    · exact r.stand_first H hr st hC h2 (fun j a b c => h ⟨j, a, b, c⟩) h0 hf
    · exact absurd ⟨j, h2, h3, h4⟩ h

/-! ### The frames from the first stand on, with any input -/

/-- **The first frames have no stand away from the floor**: a stand away from the floor at the end of frame `n + 1`, before the end of the fall, is at frame `C + wallF` or
later. The frame does not follow `hstep` (`stand_off_of`: for the first stand `stand_first`), so the first frame that does not is by then; it is stopped at the left wall (the field `wall`), and the
wall is too far from the start for the frames before `wallF − 1` (`wall_far`) -/
theorem stand_late (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n + 1 < r.C + N.fall) (h0 : (r.fr.vs (n + 1)).st = 0)
    (hf : ¬OnFloor sy (r.fr.vs (n + 1))) : r.C + N.wallF ≤ n + 1 := by
  have hN := H.nums
  have hfl := hN.fall_le
  have hhit := hN.hit_ge
  have hnf : ¬Follow sy m r.fr n := r.stand_off_of H hr st n hC (by omega) (Or.inl h1) h0 hf
  obtain ⟨h, h4, h5, h6, h7⟩ := RoomCore.first_hit (sy := sy) (m := m) (fr := r.fr) (C := r.C) (n + 1) (fun hall => hnf (hall n hC (by omega)))
  have hw := r.wall h h4 (by omega) h6
  -- the wall is far from the start
  have hF := H.air.pot
  have hd0 : inD sy (room sy N).s0 = true := by
    have h1 := H.roomOk
    simp only [roomCheck, Bool.and_eq_true] at h1
    exact h1.1.1
  have hfol : ∀ j, r.C ≤ j → j < r.C + (h - r.C) → Follow sy m r.fr j := fun j h8 h9 => h7 j h8 (by omega)
  have h8 := hdist_seg r.C (h - r.C) hfol
  rw [show r.C + (h - r.C) = h by omega] at h8
  have hJ : J sy m (r.fr.hs r.C) (phi sy m (room sy N).s0) := by
    rw [r.start_hs st]
    exact ⟨hd0, Int.le_refl _, fun h9 => absurd rfl h9⟩
  have h9 := left_dist_le hF _ _ _ hJ (inputs_seg r.C (h - r.C) hfol)
  rw [length_seg] at h9
  by_cases hc : r.C + (N.wallF - 2) < h
  · have := hN.wall_two
    omega
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, N.wallF - 2 = (h - r.C) + k := ⟨N.wallF - 2 - (h - r.C), by omega⟩
    have h10 := leftDist_mono hF (h - r.C) k _ (RoomCore.phi0_nonneg H)
    rw [← hk] at h10
    have h11 := (r.start_P st).1
    have h12 := hN.wall_far
    have h13 := hw.before
    omega

/-- **A frame with a jump in its input ends on the takeoff of its height**, for the stored speed that the frame reads at the player's routine: from the reading of the
vertical state and of the input (`read_inp`), and the walks of the room's frames (`InRoom.jump`) -/
theorem vjump_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E) (hj : (r.fr.inp (n + 1)).jump = true) :
    ∃ abs, r.fr.vs (n + 1) = jumpOffR sy m (r.fr.vs n).y abs := by
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (n + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.vs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hjr : (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n))).jump = true := by
    rw [← r.read_inp hC ht]
    exact hj
  refine ⟨peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.Player_XSpeedAbsolute, ?_⟩
  rw [hv1, hv0]
  exact hr.jump n hC hE (r.arr n) (r.atV_of H hr hC ht) hjr

/-- **The input of a frame before `standF` that starts standing** is one of `inputs`, with the state 0: it is read from the machine (`read_inp`), and at the player's
routine the player's state is that of the frame's start (`InRoom.stR`) -/
theorem gnd_in_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n < r.C + N.standF) (hst : (r.fr.vs n).st = 0) :
    r.fr.inp (n + 1) ∈ inputs ∧ (r.fr.inp (n + 1)).st = 0 := by
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hst' : peek (r.fm n) sy.Player_State = 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).st = peek (r.fm n) sy.Player_State := rfl
    rw [← e, ← hv0]
    exact hst
  have hs := hr.stR n hC (by omega) _ (r.arrive H hr hC (by omega))
  rw [r.read_inp hC (by omega)]
  generalize PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n) = x at hs
  refine ⟨readIn_mem sy x, ?_⟩
  show (if peek x sy.Player_State == 0 then (0 : UInt8) else 1) = 0
  rw [hs, hst']
  rfl

/-- **A floor frame before `standF` with a jump in its input takes off**: it ends on the takeoff of the floor's height (`vjump_of`), which is the first state of a jump
from the floor (`offCheck`); its input is a jump input (`gnd_in_of`) -/
theorem takeoff_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n < r.C + N.standF)
    (hfl : OnFloor sy (r.fr.vs n)) (hj : (r.fr.inp (n + 1)).jump = true) : VFrame sy m N r.fr n := by
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  obtain ⟨abs, e⟩ := r.vjump_of H hr hC (by omega) (by omega) hj
  have hy : (r.fr.vs n).y = (groundY sy).toUInt8 := by
    rw [← hfl.2]
    exact (UInt8.ofNat_toNat).symm
  obtain ⟨x, hx, hxs⟩ := offCheck_spec H.off abs
  obtain ⟨g1, g2⟩ := r.gnd_in_of H hr st hC h1 hfl.1
  exact VFrame.takeoff hfl x hx (by rw [e, hy, hxs]) ⟨g1, g2, hj⟩

/-- **With any input the frame goes to a next state of `anyNext`**, from a state that meets `anyOk`: standing with no jump as `StandNext` allows (`vstand_of`), standing
with a jump the takeoff of the row (`vjump_of`), in the air `vstepR` or its landing (`vair_of`) -/
theorem any_next (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n + 1 < r.C + N.fall)
    (hok : anyOk sy (r.fr.vs n) = true) : r.fr.vs (n + 1) ∈ anyNext sy m (offTable sy m) (r.fr.vs n) := by
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hfl := H.nums.fall_le
  by_cases hs : (r.fr.vs n).st = 0
  · cases hj : (r.fr.inp (n + 1)).jump with
    | false => exact mem_anyNext_of (mem_noJumpNext_stand hs (r.vstand_of H hr hC (by omega) (by omega) hs hj))
    | true =>
      obtain ⟨abs, e⟩ := r.vjump_of H hr hC (by omega) (by omega) hj
      rw [e]
      exact mem_anyNext_jump hs ((anyOk_spec hok).2 hs) abs
  · exact mem_anyNext_of (mem_noJumpNext_air hs (r.vair_of H hr hC (by omega) (by omega) hs).2)

/-- **From a first stand at frame `i`, the landing of a state of the first fall at `C + wallF` or later, each frame before `C + fall` meets `anyOk`**, and each frame goes
to a next state with any input -/
theorem any_chain (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {i : Nat} (hi : r.C < i) (hw : r.C + N.wallF ≤ i)
    (hm : r.fr.vs i ∈ fallLands sy m (fallLayer sy m N.vStart (i - r.C - 1))) :
    ∀ e, i + e < r.C + N.fall → (∀ j, i ≤ j → j < i + e → r.fr.vs (j + 1) ∈ anyNext sy m (offTable sy m) (r.fr.vs j)) ∧ anyOk sy (r.fr.vs (i + e)) = true := by
  have key : ∀ n, i ≤ n → n < r.C + N.fall → (∀ j, i ≤ j → j < n → r.fr.vs (j + 1) ∈ anyNext sy m (offTable sy m) (r.fr.vs j)) →
      anyOk sy (r.fr.vs n) = true := by
    intro n h1 h2 hch
    have h := any_ok H.anyin (fun d => r.fr.vs (r.C + d)) (d' := i - r.C) (n := n - r.C) (by omega) (by omega) (by omega) (by omega)
      (by
        show r.fr.vs (r.C + (i - r.C)) ∈ _
        rw [show r.C + (i - r.C) = i by omega]
        exact hm)
      (fun j hj1 hj2 => by
        have := hch (r.C + j) (by omega) (by omega)
        rwa [show r.C + j + 1 = r.C + (j + 1) by omega] at this)
    simp only [show r.C + (n - r.C) = n by omega] at h
    exact h
  intro e
  induction e with
  | zero => exact fun h => ⟨fun j h1 h2 => absurd h2 (by omega), key i (Nat.le_refl _) (by omega) (fun j h1 h2 => absurd h2 (by omega))⟩
  | succ e ih =>
    intro h
    obtain ⟨c1, c2⟩ := ih (by omega)
    have hn := r.any_next H hr st (n := i + e) (by omega) (by omega) c2
    have hch : ∀ j, i ≤ j → j < i + (e + 1) → r.fr.vs (j + 1) ∈ anyNext sy m (offTable sy m) (r.fr.vs j) := by
      intro j h1 h2
      by_cases hje : j < i + e
      · exact c1 j h1 hje
      · rw [show j = i + e by omega]
        exact hn
    exact ⟨hch, key (i + (e + 1)) (by omega) h hch⟩

/-- **He is not on the floor during the fall, with any input.** Up to the first stand the first fall gives it (`fall_first`). After it: the first stand is away from the
floor, so it is at frame `C + wallF` or later (`stand_late`: `stand_first` and the field `wall`), and it is the landing of a state of the first fall; from there the
states with any input are those of `anyCheck`, none on the floor. The old field `fall_jump` -/
theorem fall_any (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h1 : n < r.C + N.fall) :
    ¬OnFloor sy (r.fr.vs n) := by
  obtain ⟨_, hfs, _, _⟩ := fall_ok H.first
  by_cases hs : ∃ j, r.C < j ∧ j < n ∧ (r.fr.vs j).st = 0
  · obtain ⟨i, i1, i2, i3, i4⟩ := first_of (P := fun j => (r.fr.vs j).st = 0) n hs
    have h5 := r.fall_first H hr st (n := i) (by omega) (by omega) (fun k a b => i4 k a b)
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hlate := r.stand_late H hr st (n := i') (by omega) (by omega) i3 h5
    obtain ⟨d, rfl⟩ : ∃ d, i' = r.C + d := ⟨i' - r.C, by omega⟩
    have hns : ∀ j, r.C < j → j ≤ r.C + d → (r.fr.vs j).st ≠ 0 := fun j a b => i4 j a (by omega)
    have hmem := r.fall_mem H hr st d (by omega) hns
    obtain ⟨hok, h2⟩ := r.fall_next H hr st (d := d) (by omega) hns
    obtain ⟨s1, _, _, _, _⟩ := fallStep_spec ((fallOk_spec hok).2 (r.fr.a (r.C + d + 1)))
    have hland : r.fr.vs (r.C + d + 1) ∈ fallLands sy m (fallLayer sy m N.vStart (r.C + d + 1 - r.C - 1)) := by
      rw [show r.C + d + 1 - r.C - 1 = d by omega]
      rcases h2 with e | ⟨hf, e⟩
      · have i3' : (r.fr.vs (r.C + d + 1)).st = 0 := i3
        rw [e, s1] at i3'
        exact absurd i3' (by decide)
      · rw [e]
        exact mem_fallLands hmem hf
    obtain ⟨_, hok2⟩ := r.any_chain H hr st (i := r.C + d + 1) (by omega) hlate hland (n - (r.C + d + 1)) (by omega)
    rw [show r.C + d + 1 + (n - (r.C + d + 1)) = n by omega] at hok2
    exact (anyOk_spec hok2).1
  · exact r.fall_first H hr st hC h1 (fun j a b c => hs ⟨j, a, b, c⟩)

/-- **`fall_long`**: he is not on the floor during the fall. With no jump from the set of the states with no jump (`fall_nojump`), after a jump from the set of the
states with any input from the first stand on (`fall_any`) -/
theorem fall_long_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) : ∀ n, r.C ≤ n → n < r.C + N.fall → ¬OnFloor sy (r.fr.vs n) := by
  intro n hC h1
  by_cases h : ∃ j, r.C ≤ j ∧ j < n ∧ (r.fr.inp (j + 1)).jump = true
  · exact r.fall_any H hr st hC h1
  · exact r.fall_nojump H hr st hC h1 (fun j a b => by
      cases e : (r.fr.inp (j + 1)).jump with
      | false => rfl
      | true => exact absurd ⟨j, a, b, e⟩ h)

/-- **`land_at`**: with no wall he stands at the end of the fall, on frame `C + fall`. There is no stand before (`fall_first`, `stand_off_of`), so the state one frame before
is one of the first fall (`fall_mem`), from which `vstepR` is at the height `landY` and does not rise (`landCheck`); with `landQ` at the end of the move the frame ends
on the landing (`InRoom.land`): there the vertical page is 1 (`high_fall`, `InRoom.high`), and the page and x are those of `landQ_pos`. So the state and the vertical
speed are 0 at the frame's end; and the vertical page is 1 there (`InRoom.high`, `highCheck`), and at the start of the next frame (`InRoom.keepH`) -/
theorem land_end_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) :
    (r.fr.vs (r.C + N.fall)).st = 0 ∧ (r.fr.vs (r.C + N.fall)).vy = 0 ∧ peek (r.fm (r.C + N.fall)) sy.Player_Y_HighPos = 1 := by
  obtain ⟨hf0, hfs, _, _⟩ := fall_ok H.first
  have hhit := H.nums.hit_ge
  have hns : ∀ j, r.C < j → j < r.C + N.fall → (r.fr.vs j).st ≠ 0 := by
    intro j h1 h2 h3
    obtain ⟨i, i1, i2, i3, i4⟩ := first_of (P := fun j => (r.fr.vs j).st = 0) (r.C + N.fall) ⟨j, h1, h2, h3⟩
    have h5 := r.fall_first H hr st (n := i) (by omega) i2 (fun k a b => i4 k a b)
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact r.stand_off_of H hr st i' (by omega) (by omega) (Or.inl (by omega)) i3 h5 (hw i' (by omega) (by omega))
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hmem := r.fall_mem H hr st (N.fall - 1) (by omega) (fun j a b => hns j a (by omega))
  have e1 : r.C + N.fall - 1 = r.C + (N.fall - 1) := by omega
  have hC : r.C ≤ r.C + (N.fall - 1) := by omega
  have ht : r.C + (N.fall - 1) < r.t0 := by omega
  have hE' : r.C + (N.fall - 1) + 1 < r.E := by omega
  have hcl := r.atV_of H hr hC ht
  have hv0 : r.fr.vs (r.C + (N.fall - 1)) = VertModel.vsOf sy (r.fm (r.C + (N.fall - 1))) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (r.C + (N.fall - 1) + 1) =
      VertModel.vsOf sy (PipeTransition.frame (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1)))) := by
    rw [r.vs_fe (n := r.C + (N.fall - 1) + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hok := (fall_ok H.first).2.2.2 (N.fall - 1) (by omega) _ hmem
  have hst' : peek (r.fm (r.C + (N.fall - 1))) sy.Player_State ≠ 0 := by
    have e : (VertModel.vsOf sy (r.fm (r.C + (N.fall - 1)))).st = peek (r.fm (r.C + (N.fall - 1))) sy.Player_State := rfl
    rw [← e, ← hv0, (fallOk_spec hok).1]
    decide
  obtain ⟨j, hkj, hq, hf, _, himp⟩ := hr.land (r.C + (N.fall - 1)) hC hE' hst' (r.arr (r.C + (N.fall - 1))) hcl
    (hr.pair (r.C + (N.fall - 1)) hC (by omega)).1 (hr.pair (r.C + (N.fall - 1)) hC (by omega)).2
  have hhQ : peek (PipeEntryRule.trace (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1))) j) sy.Player_Y_HighPos = 1 := by
    have hc := highCheck_spec H.high (d := N.fall - 1) (by omega) (s := VertModel.vsOf sy (r.fm (r.C + (N.fall - 1)))) (by rw [← hv0]; exact hmem)
    exact ((hr.high (r.C + (N.fall - 1)) hC hE' hst' (r.arr (r.C + (N.fall - 1))) hcl (hr.pair (r.C + (N.fall - 1)) hC (by omega)).1
      (hr.pair (r.C + (N.fall - 1)) hC (by omega)).2 (r.high_fall H hr st hns (N.fall - 1) (by omega))).1 j hkj hq hf).trans (hc _).2
  have hhE : peek (PipeTransition.frame (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1)))) sy.Player_Y_HighPos = 1 := by
    have hc := highCheck_spec H.high (d := N.fall - 1) (by omega) (s := VertModel.vsOf sy (r.fm (r.C + (N.fall - 1)))) (by rw [← hv0]; exact hmem)
    exact ((hr.high (r.C + (N.fall - 1)) hC hE' hst' (r.arr (r.C + (N.fall - 1))) hcl (hr.pair (r.C + (N.fall - 1)) hC (by omega)).1
      (hr.pair (r.C + (N.fall - 1)) hC (by omega)).2 (r.high_fall H hr st hns (N.fall - 1) (by omega))).2 (hc _).1).trans (hc _).2
  have hlc := List.all_eq_true.mp H.land _ hmem
  rw [hv0] at hlc
  generalize (peek (PipeEntryRule.trace (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1))) (r.arr (r.C + (N.fall - 1)))) sy.SavedJoypadBits &&& 0x80 != 0) = a at himp
  have hya : (vstepR sy m (VertModel.vsOf sy (r.fm (r.C + (N.fall - 1)))) a).y = landY sy ∧
      (vstepR sy m (VertModel.vsOf sy (r.fm (r.C + (N.fall - 1)))) a).vy &&& 0x80 = 0 := by
    have h := List.all_eq_true.mp hlc a (by cases a <;> simp)
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h
  have hl : LandQ sy N (PipeEntryRule.trace (r.fm (r.C + (N.fall - 1))) (r.inAt (r.C + (N.fall - 1))) j) := by
    obtain ⟨hpg, hx⟩ := r.landQ_pos H hr st hkj hq
    exact ⟨hhQ, hpg, hx⟩
  have e2 := himp hya.1 hya.2 hl
  have e3 : r.C + N.fall = r.C + (N.fall - 1) + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [e3, hv1, e2]
    rfl
  · rw [e3, hv1, e2]
    rfl
  · rw [e3, hr.keepH (r.C + (N.fall - 1) + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
    exact hhE

/-- **`land_at`**: with no wall he stands at the end of the fall, on frame `C + fall` (`land_end_of`). This was the field `land_at`, and then the field `landQ` -/
theorem land_at_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) : (r.fr.vs (r.C + N.fall)).st = 0 :=
  (r.land_end_of H hr st hw).1

/-- **A floor frame after the fall with no jump in its input stays on the floor**, if it starts with the vertical page 1 and the vertical speed not negative: at the end
of its move the page is 0 and the horizontal coordinate below `landX` (`q_pos`, `floorP`), so it lands there on the floor (`InRoom.floor`). At its end he is on the floor
with the vertical speed 0, and the next frame starts with the vertical page 1 (`InRoom.keepH`) -/
theorem stay_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (hn : n < r.C + N.fall + N.lastG + 1 + N.rise)
    (hfl : OnFloor sy (r.fr.vs n)) (hj : (r.fr.inp (n + 1)).jump = false) (hhi : peek (r.fm n) sy.Player_Y_HighPos = 1) (hvy : (r.fr.vs n).vy &&& 0x80 = 0) :
    OnFloor sy (r.fr.vs (n + 1)) ∧ (r.fr.vs (n + 1)).vy = 0 ∧ peek (r.fm (n + 1)) sy.Player_Y_HighPos = 1 := by
  have hvf := H.nums.vf.1
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have ht : n < r.t0 := by omega
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (n + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.vs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hst' : peek (r.fm n) sy.Player_State = 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).st = peek (r.fm n) sy.Player_State := rfl
    rw [← e, ← hv0]
    exact hfl.1
  have hy' : peek (r.fm n) sy.Player_Y_Position = (groundY sy).toUInt8 := by
    have e : (VertModel.vsOf sy (r.fm n)).y = peek (r.fm n) sy.Player_Y_Position := rfl
    rw [← e, ← hv0, ← hfl.2]
    exact (UInt8.ofNat_toNat).symm
  have hvy' : peek (r.fm n) sy.Player_Y_Speed &&& 0x80 = 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).vy = peek (r.fm n) sy.Player_Y_Speed := rfl
    rw [← e, ← hv0]
    exact hvy
  obtain ⟨jq, hkj, hq, _, himp⟩ := hr.floor n hC (by omega) hst' (r.arr n) (r.atV_of H hr hC ht) (r.jump_read hC ht hj) (hr.pair n hC (by omega)).2 hhi
  obtain ⟨hpg, hx⟩ := r.q_pos H hr st (d := N.fall + N.lastG + 1 + N.rise) hC ht (by omega) hvf H.floorP H.landP.2 hkj hq
  obtain ⟨f1, f2, f3, f4⟩ := himp hy' hvy' hpg hx
  have hy1 : (r.fr.vs (n + 1)).y = (r.fr.vs n).y := by
    rw [hv1, hv0]
    show peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_Position = peek (r.fm n) sy.Player_Y_Position
    rw [f3, H.floorRow, hy']
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hv1]
    exact f1
  · rw [hy1]
    exact hfl.2
  · rw [hv1]
    exact f2
  · rw [hr.keepH (n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
    exact f4

/-- **On the floor since the end of the fall, each frame starts with the vertical page 1 and the vertical speed 0**: at the end of the fall he has landed (`land_end_of`),
and a frame on the floor followed by one on the floor has no jump (a takeoff ends in the air: `vjump_of`, `offCheck`, `arc_facts`) and stays there (`stay_of`) -/
theorem floor_run (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) : ∀ d,
    r.C + N.fall + d < r.C + N.fall + N.lastG + 1 + N.rise → (∀ e, e ≤ d → OnFloor sy (r.fr.vs (r.C + N.fall + e))) →
    peek (r.fm (r.C + N.fall + d)) sy.Player_Y_HighPos = 1 ∧ (r.fr.vs (r.C + N.fall + d)).vy = 0
  | 0, _, _ => ⟨(r.land_end_of H hr st hw).2.2, (r.land_end_of H hr st hw).2.1⟩
  | d + 1, h1, hf => by
    have hvf := H.nums.vf.1
    have hfar := r.t0_far H hr st
    have hE := r.t0_le_E H hr
    obtain ⟨ih1, ih2⟩ := floor_run H hr st hw d (by omega) (fun e he => hf e (by omega))
    have hf0 := hf d (by omega)
    have hf1 := hf (d + 1) (Nat.le_refl _)
    rw [show r.C + N.fall + (d + 1) = r.C + N.fall + d + 1 by omega] at hf1 ⊢
    have hj : (r.fr.inp (r.C + N.fall + d + 1)).jump = false := by
      cases hj : (r.fr.inp (r.C + N.fall + d + 1)).jump with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨abs, e⟩ := r.vjump_of H hr (n := r.C + N.fall + d) (by omega) (by omega) (by omega) hj
        obtain ⟨x, hx, hxs⟩ := offCheck_spec H.off abs
        have hy : (r.fr.vs (r.C + N.fall + d)).y = (groundY sy).toUInt8 := by
          rw [← hf0.2]
          exact (UInt8.ofNat_toNat).symm
        have h6 : OnArc sy m N r.fr (r.C + N.fall + d) (r.C + N.fall + d + 1) := by
          refine ⟨by omega, x, x, hx, ?_, by rw [e, hy, hxs]⟩
          rw [show r.C + N.fall + d + 1 - (r.C + N.fall + d + 1) = 0 by omega]
          exact .refl _
        exact (arc_facts H h6 (by omega)).2.2 hf1.1
    obtain ⟨_, g2, g3⟩ := r.stay_of H hr st (n := r.C + N.fall + d) (by omega) (by omega) hf0 hj ih1 (by rw [ih2]; rfl)
    exact ⟨g3, g2⟩

theorem sub_one_ne (x : UInt8) : x - 1 ≠ x := by
  intro h
  have e := congrArg UInt8.toNat h
  rw [UInt8.toNat_sub] at e
  have e1 : UInt8.toNat 1 = 1 := rfl
  have := x.toNat_lt
  omega

theorem sub_one_toNat (x : UInt8) (h : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  rw [UInt8.toNat_sub_of_le]
  · rfl
  · show (1 : UInt8).toNat ≤ x.toNat
    exact h

theorem sbyte_neg {v : UInt8} (h : ¬ v < 0x80) : sbyte v < 0 := by
  unfold sbyte
  rw [if_neg h]
  have := v.toNat_lt
  omega

/-- the charge for the facing is not negative when `c` is not -/
theorem w_nonneg {sy : Syms} {m : Machine} (s : HS) (hc : 0 ≤ Potential.c sy m) : 0 ≤ Potential.w sy m s := by
  unfold Potential.w
  split
  · split <;> omega
  · split <;> omega

/-- **At or past the corner and less than five pixels past it: the page 0 and a coordinate of `xsC`** -/
theorem corner_window {sy : Syms} {m : Machine} {N : Nums} (hF : CornerFacts sy m N) {pg x f : UInt8} (h1 : cornerP sy ≤ FrameModel.posOf pg x f)
    (h2 : FrameModel.posOf pg x f < cornerP sy + 1280) : pg = 0 ∧ x ∈ xsC sy := by
  have e := hF.cx
  have c5 := hF.cx5
  unfold FrameModel.posOf at h1 h2
  have hf := f.toNat_lt
  have hx := x.toNat_lt
  have hp : pg.toNat = 0 := by omega
  refine ⟨UInt8.toNat_inj.mp (by rw [hp]; rfl), ?_⟩
  exact List.mem_map.2 ⟨x.toNat - cornerX sy, List.mem_range.2 (by omega), by rw [show cornerX sy + (x.toNat - cornerX sy) = x.toNat by omega]; simp⟩

/-- **One frame at the block's left side** (the step of `low_floor_of` and `low_jump_of`): after a frame that is `LowAt`, a frame that ends at the corner's height
or below, whose end of the move `jq` is its one `PlayerSubs`, and that ends `CornerEnd` when `jq` has the page 0 and a coordinate of `xsC`, is `LowAt`. If he is left of the
corner at `jq`, he ends at most one pixel more right (`Collide`), or as at `jq`. If not, `jq` is at most five pixels past the corner (`move_top`, the slack): the page 0 and
a coordinate of `xsC`, and the frame ends `CornerEnd`. A frame that follows the model keeps the coordinate after `jq`, so it is not pushed back: it moves left. A frame that
does not is `Stop` (`clean`), and its end of the move is that of `FrameModel.frame_readQ` (the one `PlayerSubs`): pushed back one pixel from `P + 16·v₂`, where `v₂` is at
most the top speed, and at most 16 after a frame that is stopped or moves left; or moving left -/
theorem low_step (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (h3 : n < r.t0)
    {s : Int} (hsk : SlackOK sy s) (hlow : LowS sy m N r.fr s n) (hy2 : cornerY sy N.h ≤ (r.fr.vs (n + 1)).y.toNat) {jq : Nat} (hkj : r.arr n ≤ jq)
    (hq : (PipeEntryRule.trace (r.fm n) (r.inAt n) jq).pc = sy.PlayerSubs)
    (huniq : ∀ j', r.arr n ≤ j' → (PipeEntryRule.trace (r.fm n) (r.inAt n) j').pc = sy.PlayerSubs →
      (PipeEntryRule.trace (r.fm n) (r.inAt n) j').frame = (r.fm n).frame → j' = jq)
    (himp : (PipeEntryRule.trace (r.fm n) (r.inAt n) jq).ram.get! (FrameModel.I sy.Player_PageLoc) = 0 →
      (PipeEntryRule.trace (r.fm n) (r.inAt n) jq).ram.get! (FrameModel.I sy.Player_X_Position) ∈ xsC sy →
      CornerEnd sy (cornerY sy N.h) ((PipeEntryRule.trace (r.fm n) (r.inAt n) jq).ram.get! (FrameModel.I sy.Player_X_Position))
        ((PipeEntryRule.trace (r.fm n) (r.inAt n) jq).ram.get! (FrameModel.I sy.Player_X_Speed)) (PipeTransition.frame (r.fm n) (r.inAt n))) :
    LowS sy m N r.fr s (n + 1) := by
  have hN := H.nums
  have hF := H.corner
  have hl0 : 0 ≤ s := by have := hsk.1; omega
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hnx := r.next hC (r.ups_lt hr hC (by omega))
  have p0 : r.fr.P n = posP sy (r.fm n) := r.P_fm hr hC (by omega) (by omega)
  have p1 : r.fr.P (n + 1) = posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.P_fe (n := n + 1) (by omega) (by omega), hnx]
  have hv1 : (r.fr.hs (n + 1)).v = peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Speed := by
    rw [r.hs_fe (n := n + 1) (by omega) (by omega), hnx]
    rfl
  have hy1 : ¬ ((PipeTransition.frame (r.fm n) (r.inAt n)).ram.get! (FrameModel.I sy.Player_Y_Position)).toNat < cornerY sy N.h := by
    have e : (r.fr.vs (n + 1)).y = peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_Position := by
      rw [r.vs_fe (n := n + 1) (by omega) (by omega), hnx]
      rfl
    have h5 := hy2
    rw [e] at h5
    show ¬ (peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_Position).toNat < cornerY sy N.h
    omega
  have hmt := r.move_top_of H hr st n hC h3
  have hl1 := hlow.1
  have h3' := hsk.2.2
  rcases r.clean n hC h3 with hc | ⟨hs, hc⟩
  · -- the frame follows the model: nothing writes the horizontal bytes after the end of the move
    have hf := r.follow_of_clean H hr st hC h3 (r.cleanR_of H hr hC h3 hc)
    have hafter := hc.after jq hkj hq
    have hPF : posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) = posP sy (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) := FrameModel.posP_congr hafter
    have hXF := hafter sy.Player_X_Position (by simp [FrameModel.hBytes])
    have hVF := hafter sy.Player_X_Speed (by simp [FrameModel.hBytes])
    by_cases hlt : r.fr.P (n + 1) < cornerP sy
    · exact ⟨by omega, Or.inr (Or.inl hlt)⟩
    · obtain ⟨hpg, hx⟩ := corner_window hF (pg := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_PageLoc)
        (x := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_X_Position) (f := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.SprObject_X_MoveForce)
        (by rw [← FrameModel.posP_eq, ← hPF, ← p1]; omega) (by rw [← FrameModel.posP_eq, ← hPF, ← p1]; omega)
      have hce := himp hpg hx
      unfold CornerEnd at hce
      rcases hce with hce | ⟨_, hce⟩
      · exact absurd hce hy1
      · split at hce
        · exfalso
          obtain ⟨_, hx1⟩ := hce
          exact sub_one_ne _ (hx1.symm.trans hXF)
        · rename_i hneg
          have hsb : sbyte (r.fr.hs (n + 1)).v < 0 := by
            rw [hv1, hVF]
            exact sbyte_neg hneg
          refine ⟨?_, Or.inr (Or.inr hsb)⟩
          rw [hf.2.2]
          omega
  · -- the frame does not follow the model: it is `Stop`, and a `TopSpeed.Frame` whose end of the move is `jq`
    have hd : inD sy (r.fr.hs n) = true := by
      have h := r.inD_of H hr st (n - r.C) (by omega)
      rwa [show r.C + (n - r.C) = n by omega] at h
    have hR := r.readR_of H hr hC h3 hd hc
    obtain ⟨idle, hT⟩ := r.inTime_of H hr
    obtain ⟨f, kB, e1, e2, e3, _, _, _, hpcB, hfB, eP2, ev2, _⟩ := FrameModel.frame_readQ H.model H.fric hR (r.before_of H hr hC h3 hR.at_frame.pc)
      (hT n hC h3 hR.at_frame.pc) (r.far_of H hr st hC h3)
    have hjB : r.arr n + kB = jq := huniq _ (Nat.le_add_right _ _) hpcB hfB
    have hco : FrameModel.Collide sy (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n + kB)) (PipeTransition.frame (r.fm n) (r.inAt n)) :=
      hc.collide (r.arr n + kB) (Nat.le_add_right _ _) hpcB
    rw [hjB] at eP2 ev2 hco
    refine ⟨?_, Or.inl hs⟩
    have hmove := f.move
    have hfr2 := f.friction
    have hgain := f.friction_gain
    have hfrac := f.frac
    have han := f.anim
    have hdd := hd
    rw [r.hs_fm hr hC (by omega) (by omega)] at hdd
    simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hdd
    have hva : (sbyte (peek (r.fm n) sy.Player_X_Speed)).natAbs ≤ top sy := hdd.1.1.1
    have hv1' : -(top sy : Int) ≤ f.v₁ ∧ f.v₁ ≤ (top sy : Int) := by
      rcases han with ⟨a, _⟩ | ⟨a, _⟩
      · rw [a, e1]
        omega
      · rw [a]
        omega
    have hv2 := hfr2 hv1'
    have hcoP := hco.P
    rw [p1]
    have hP2 : posP sy (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) = r.fr.P n + 16 * f.v₂ := by rw [← eP2, hmove, e3, p0]
    by_cases hq' : posP sy (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) < cornerP sy
    · have := hsk.1
      rcases hcoP with e | e | ⟨e, _⟩ <;> omega
    · obtain ⟨hpg, hx⟩ := corner_window hF (pg := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_PageLoc)
        (x := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_X_Position) (f := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.SprObject_X_MoveForce)
        (by rw [← FrameModel.posP_eq]; omega) (by rw [← FrameModel.posP_eq]; omega)
      have hce := himp hpg hx
      unfold CornerEnd at hce
      have ePF := FrameModel.posP_eq sy (PipeTransition.frame (r.fm n) (r.inAt n))
      have ePQ := FrameModel.posP_eq sy (PipeEntryRule.trace (r.fm n) (r.inAt n) jq)
      unfold FrameModel.posOf at ePF ePQ
      have mF := (peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.SprObject_X_MoveForce).toNat_lt
      have mQ := (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.SprObject_X_MoveForce).toNat_lt
      have hpgQ : (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_PageLoc).toNat = 0 := by rw [hpg]; rfl
      have hxq : 1 ≤ (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_X_Position).toNat := by
        have := hF.cx
        have := hF.cx1
        omega
      rcases hce with hce | ⟨hpgF, hce⟩
      · exact absurd hce hy1
      · have hpgF' : (peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_PageLoc).toNat = 0 := by
          show ((PipeTransition.frame (r.fm n) (r.inAt n)).ram.get! (FrameModel.I sy.Player_PageLoc)).toNat = 0
          rw [hpgF]
          rfl
        split at hce
        · -- pushed back one pixel with the speed 0
          obtain ⟨_, hxF⟩ := hce
          have hxF' : (peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Position).toNat =
              (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_X_Position).toNat - 1 := by
            show ((PipeTransition.frame (r.fm n) (r.inAt n)).ram.get! (FrameModel.I sy.Player_X_Position)).toNat = _
            rw [hxF]
            exact sub_one_toNat _ hxq
          have hPF : posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) = posP sy (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) - 256 := by
            rcases hcoP with e | e | ⟨e, _⟩ <;> omega
          rw [hPF, hP2]
          by_cases hn0 : r.fr.P n < cornerP sy
          · have := hsk.2.1
            omega
          · have hsmall := hF.small
            have hsn := hN.stop_nonneg
            have eV : V (r.fr.hs n) = 256 * f.v + f.f := by
              rw [e1, e2, r.hs_fm hr hC (by omega) (by omega)]
              rfl
            have hff := (r.fr.hs n).f.toNat_lt
            have hV : 256 * f.v₂ ≤ N.stopPhi + amax sy m := by
              rcases hlow.2 with hS | hL | hL
              · obtain ⟨_, hphi, _⟩ := hS
                have hw0 := w_nonneg (sy := sy) (m := m) (r.fr.hs n) hF.c_nonneg
                unfold phi at hphi
                rcases han with ⟨a, b'⟩ | ⟨a, b'⟩ <;> omega
              · exact absurd hL hn0
              · have hfe : f.f = ((r.fr.hs n).f.toNat : Int) := by
                  rw [e2, r.hs_fm hr hC (by omega) (by omega)]
                  rfl
                have hve : f.v = sbyte (r.fr.hs n).v := by
                  rw [e1, r.hs_fm hr hC (by omega) (by omega)]
                  rfl
                rcases han with ⟨a, b'⟩ | ⟨a, b'⟩ <;> omega
            omega
        · -- moving left, as at `jq`
          rename_i hneg
          obtain ⟨_, hxF⟩ := hce
          have hxF' : (peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_X_Position).toNat =
              (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) sy.Player_X_Position).toNat := by
            show ((PipeTransition.frame (r.fm n) (r.inAt n)).ram.get! (FrameModel.I sy.Player_X_Position)).toNat = _
            rw [hxF]
            rfl
          have hPF : posP sy (PipeTransition.frame (r.fm n) (r.inAt n)) = posP sy (PipeEntryRule.trace (r.fm n) (r.inAt n) jq) := by
            rcases hcoP with e | e | ⟨e, _⟩ <;> omega
          have hsb : f.v₂ < 0 := by
            rw [ev2]
            exact sbyte_neg hneg
          rw [hPF, hP2]
          omega

/-- **`low_floor`**: with no wall, a frame from `hitF` to the end of the low frames that ends on the floor, on the floor since the end of the fall, after a frame that is
`LowAt`, is `LowAt`. It starts on the floor with the vertical page 1 and the vertical speed 0 (`floor_run`), with no jump (a takeoff ends in the air), so `InRoom.corner`
gives its one end of the move `jq`. If he is left of the corner at `jq`, he ends at most one pixel more right (`Collide`), or as at `jq`. If not, `jq` is at most five pixels
past the corner (`move_top`, the slack): the page 0 and a coordinate of `xsC`, and the frame ends `CornerEnd`. A frame that follows the model keeps the coordinate after
`jq`, so it is not pushed back: it moves left. A frame that does not is `Stop` (`clean`), and its end of the move is that of `FrameModel.frame_readQ` (the one `PlayerSubs`):
pushed back one pixel from `P + 16·v₂`, where `v₂` is at most the top speed, and at most 16 after a frame that is stopped or moves left; or moving left -/
theorem low_floor_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) {n : Nat}
    (h1 : r.C + N.hitF ≤ n + 1) (h2 : n + 1 ≤ r.C + N.fall + 1 + N.rise) (h3 : n < r.t0)
    (hall : ∀ j, r.C + N.fall ≤ j → j ≤ n + 1 → OnFloor sy (r.fr.vs j)) {s : Int} (hsk : SlackOK sy s) (hlow : LowS sy m N r.fr s n) : LowS sy m N r.fr s (n + 1) := by
  have hN := H.nums
  have hF := H.corner
  have hvf := hN.vf.1
  have hg := hN.hit_ge
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hC : r.C ≤ n := by omega
  have hfl0 := hall n (by omega) (by omega)
  have hfl1 := hall (n + 1) (by omega) (Nat.le_refl _)
  have hfr := r.floor_run H hr st hw (n - (r.C + N.fall)) (by omega) (fun e he => hall _ (by omega) (by omega))
  rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at hfr
  have hj : (r.fr.inp (n + 1)).jump = false := by
    cases hj : (r.fr.inp (n + 1)).jump with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨abs, e⟩ := r.vjump_of H hr (n := n) hC h3 (by omega) hj
      obtain ⟨x, hx, hxs⟩ := offCheck_spec H.off abs
      have hy : (r.fr.vs n).y = (groundY sy).toUInt8 := by
        rw [← hfl0.2]
        exact (UInt8.ofNat_toNat).symm
      have h6 : OnArc sy m N r.fr n (n + 1) := by
        refine ⟨by omega, x, x, hx, ?_, by rw [e, hy, hxs]⟩
        rw [show n + 1 - (n + 1) = 0 by omega]
        exact .refl _
      exact (arc_facts H h6 (by omega)).2.2 hfl1.1
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hst' : peek (r.fm n) sy.Player_State = 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).st = peek (r.fm n) sy.Player_State := rfl
    rw [← e, ← hv0]
    exact hfl0.1
  have hy' : peek (r.fm n) sy.Player_Y_Position = (groundY sy).toUInt8 := by
    have e : (VertModel.vsOf sy (r.fm n)).y = peek (r.fm n) sy.Player_Y_Position := rfl
    rw [← e, ← hv0, ← hfl0.2]
    exact (UInt8.ofNat_toNat).symm
  have hvy' : peek (r.fm n) sy.Player_Y_Speed &&& 0x80 = 0 := by
    have e : (VertModel.vsOf sy (r.fm n)).vy = peek (r.fm n) sy.Player_Y_Speed := rfl
    rw [← e, ← hv0, hfr.2]
    rfl
  obtain ⟨jq, hkj, hq, _, huniq, himp⟩ := hr.corner n hC (by omega) hst' (r.arr n) (r.atV_of H hr hC h3) (r.jump_read hC h3 hj)
    (hr.pair n hC (by omega)).2 hfr.1
  have hy2 : cornerY sy N.h ≤ (r.fr.vs (n + 1)).y.toNat := by
    have h5 := hfl1.2
    have h6 := hN.corner_le
    omega
  exact low_step r H hr st hC h3 hsk hlow hy2 hkj hq huniq (himp hy' hvy')

/-- the frame of an arc's state: on frame `n` of a jump from the floor, before its last low frame, the vertical state at frame `n`'s end and its `vstep` with A at the
player's routine are states of the jump's first frames (`VertAir.arcSet`), rising; and frame `n + 1` ends on that `vstep` (as `varc_of`) -/
theorem varc_at (H : Checks sy m N) (hr : r.InRoom) {T n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E) (ha : OnArc sy m N r.fr T n)
    (hk : n + 1 - (T + 1) ≤ N.rise) :
    VertModel.vsOf sy (r.fm n) ∈ (VertAir.arcSet sy m N.h N.rise).map (·.s) ∧
    vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∈
      (VertAir.arcSet sy m N.h N.rise).map (·.s) ∧
    (vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&& 0x80 = 0x80 ∧
    r.fr.vs (n + 1) = vstep sy m (VertModel.vsOf sy (r.fm n)) (peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.SavedJoypadBits &&& 0x80 != 0) 0 := by
  have hcl : VertAir.AtV sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) := r.atV_of H hr hC ht
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (n + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.vs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hT := ha.1
  obtain ⟨hfall, _⟩ := (arc_facts H ha (by omega)).2
  obtain ⟨_, x, u, hx, hru, hu⟩ := ha
  let a := peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.SavedJoypadBits &&& 0x80 != 0
  let y : Arc :=
    { s := vstep sy m u.s a 0, k := u.k + 1,
      low := if cornerY sy N.h ≤ (vstep sy m u.s a 0).y.toNat then u.k + 1 else u.low,
      above := if (vstep sy m u.s a 0).y.toNat < standY sy N.h then 0 else u.above + 1, fast := u.fast }
  have hy : y ∈ arcSucc sy m N.h u := by
    unfold arcSucc
    rw [← hu, hfall]
    simp only [Bool.false_and, if_false, Bool.false_eq_true]
    rw [hu]
    cases ha' : a with
    | true => simp [y, ha']
    | false => simp [y, ha']
  have hyr : Cert.Reach (arcSucc sy m N.h) x (n + 1 - (T + 1)) y := by
    rw [show n + 1 - (T + 1) = n - (T + 1) + 1 by omega]
    exact reach_snoc hru hy
  obtain ⟨_, hyf, _⟩ := arc_facts H (fr := { r.fr with vs := fun j => if j = n + 1 then y.s else r.fr.vs j }) (T := T) (n := n + 1)
    ⟨by omega, x, y, hx, hyr, by simp⟩ hk
  simp only [if_true] at hyf
  have m1 : VertModel.vsOf sy (r.fm n) ∈ (VertAir.arcSet sy m N.h N.rise).map (·.s) := by
    rw [← hv0, hu]
    exact List.mem_map.2 ⟨u, VertAir.mem_arcSet hx hru (by omega), rfl⟩
  have m2 : vstep sy m (VertModel.vsOf sy (r.fm n)) a 0 ∈ (VertAir.arcSet sy m N.h N.rise).map (·.s) := by
    rw [← hv0, hu]
    exact List.mem_map.2 ⟨y, VertAir.mem_arcSet hx hyr hk, rfl⟩
  have m3 : (vstep sy m (VertModel.vsOf sy (r.fm n)) a 0).vy &&& 0x80 = 0x80 := by
    rw [← hv0, hu]
    exact vy_of_falling hyf
  have e := hr.vert n hC hE (r.arr n) hcl (hr.pair n hC (by omega)).1 (hr.pair n hC (by omega)).2 m1 m2 m3
  exact ⟨m1, m2, m3, by rw [hv1, e]⟩

/-- the vertical page at the start of frame `n + 1`, from the end of frame `n` -/
theorem high_next (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E)
    (h : peek (PipeTransition.frame (r.fm n) (r.inAt n)) sy.Player_Y_HighPos = 1) : peek (r.fm (n + 1)) sy.Player_Y_HighPos = 1 := by
  rw [hr.keepH (n + 1) (by omega) hE, r.next hC (r.ups_lt hr hC (by omega))]
  exact h

/-- **`low_jump`**: with no wall, the frames of a jump from the floor after the fall, while every frame of the jump ends at `cornerY + 16` or below, are `LowAt` after a
takeoff from a frame `T` that is `LowAt`. Each frame keeps the vertical page 1 (`floor_run` at `T`, `InRoom.highJ` for the takeoff, `InRoom.highA` in the air, on the
states of `varc_at`), and comes to the end of its move once and ends `CornerEnd` at the block's left side: so it is `LowAt` (`low_step`). -/
theorem low_jump_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) {T n : Nat} (h0 : r.C + N.fall ≤ T) (h1 : T < n)
    (h2 : n ≤ r.C + N.fall + 1 + N.rise) (h3 : n ≤ r.t0) (hfl : ∀ j, r.C + N.fall ≤ j → j ≤ T → OnFloor sy (r.fr.vs j))
    (harc : ∀ j, T < j → j ≤ n → OnArc sy m N r.fr T j) (hylo : ∀ j, T < j → j ≤ n → cornerY sy N.h + 16 ≤ (r.fr.vs j).y.toNat)
    {s : Int} (hsk : SlackOK sy s) (hT : LowS sy m N r.fr s T) : LowS sy m N r.fr s n := by
  have hN := H.nums
  have hvf := hN.vf.1
  have hfar := r.t0_far H hr st
  have hE := r.t0_le_E H hr
  have hr8 := hN.rise_lt
  -- the takeoff frame `T + 1`: the vertical page 1, and `LowAt`
  have hfr := r.floor_run H hr st hw (T - (r.C + N.fall)) (by omega) (fun e he => hfl _ (by omega) (by omega))
  rw [show r.C + N.fall + (T - (r.C + N.fall)) = T by omega] at hfr
  have hfT := hfl T h0 (Nat.le_refl _)
  have hCT : r.C ≤ T := by omega
  have hjT : (r.fr.inp (T + 1)).jump = true := by
    cases hj : (r.fr.inp (T + 1)).jump with
    | true => rfl
    | false =>
      exfalso
      have h5 := (r.stay_of H hr st (n := T) hCT (by omega) hfT hj hfr.1 (by rw [hfr.2]; rfl)).1
      exact (arc_facts H (harc (T + 1) (by omega) (by omega)) (by omega)).2.2 h5.1
  have hv0 : r.fr.vs T = VertModel.vsOf sy (r.fm T) := r.vs_fm hr hCT (by omega) (by omega)
  have hyT : peek (r.fm T) sy.Player_Y_Position = (groundY sy).toUInt8 := by
    have e : (VertModel.vsOf sy (r.fm T)).y = peek (r.fm T) sy.Player_Y_Position := rfl
    rw [← e, ← hv0, ← hfT.2]
    exact (UInt8.ofNat_toNat).symm
  have hjr : (FrameModel.readIn sy (PipeEntryRule.trace (r.fm T) (r.inAt T) (r.arr T))).jump = true := by
    rw [← r.read_inp hCT (by omega)]
    exact hjT
  obtain ⟨hhJ, jq, hkj, hq, _, huniq, himp⟩ := hr.highJ T hCT (by omega) (r.arr T) (r.atV_of H hr hCT (by omega)) hjr hfr.1 hyT
  have hy2 : cornerY sy N.h ≤ (r.fr.vs (T + 1)).y.toNat := by have := hylo (T + 1) (by omega) (by omega); omega
  have hL1 := low_step r H hr st hCT (by omega) hsk hT hy2 hkj hq huniq himp
  have hH1 := high_next r hr hCT (by omega) (by omega) hhJ
  -- the frames in the air: by induction
  have step : ∀ d, T + 1 + d ≤ n → LowS sy m N r.fr s (T + 1 + d) ∧ peek (r.fm (T + 1 + d)) sy.Player_Y_HighPos = 1 := by
    intro d
    induction d with
    | zero => intro _; exact ⟨hL1, hH1⟩
    | succ d ih =>
      intro hd
      obtain ⟨hL, hH⟩ := ih (by omega)
      have e : T + 1 + (d + 1) = T + 1 + d + 1 := by omega
      rw [e]
      have hCn : r.C ≤ T + 1 + d := by omega
      have hta : T + 1 + d < r.t0 := by omega
      have ha := harc (T + 1 + d) (by omega) (by omega)
      have hfa := arc_facts H ha (by omega)
      obtain ⟨m1, m2, m3, hv1⟩ := varc_at r H hr hCn hta (by omega) ha (by omega)
      have hv0' : r.fr.vs (T + 1 + d) = VertModel.vsOf sy (r.fm (T + 1 + d)) := r.vs_fm hr hCn (by omega) (by omega)
      have hst : peek (r.fm (T + 1 + d)) sy.Player_State ≠ 0 := by
        have e2 : (VertModel.vsOf sy (r.fm (T + 1 + d))).st = peek (r.fm (T + 1 + d)) sy.Player_State := rfl
        rw [← e2, ← hv0']
        exact hfa.2.2
      obtain ⟨hhA, jq, hkj, hq, _, huniq, himp⟩ := hr.highA (T + 1 + d) hCn (by omega) hst (r.arr (T + 1 + d)) (r.atV_of H hr hCn hta)
        (hr.pair (T + 1 + d) hCn (by omega)).1 (hr.pair (T + 1 + d) hCn (by omega)).2 hH m1 m2 m3
      have hyl := hylo (T + 1 + d + 1) (by omega) (by omega)
      have hy2 : cornerY sy N.h ≤ (r.fr.vs (T + 1 + d + 1)).y.toNat := by omega
      rw [hv1] at hyl
      exact ⟨low_step r H hr st hCn hta hsk hL hy2 hkj hq huniq (fun hpg hx => himp hpg hx hyl), high_next r hr hCn hta (by omega) hhA⟩
  have := (step (n - (T + 1)) (by omega)).1
  rwa [show T + 1 + (n - (T + 1)) = n by omega] at this

/-- **`vfloor`**: with no wall, a frame after the fall that starts on the floor, when he has stood on the floor since the end of the fall, is `VFrame`. With a jump in its
input it takes off (`takeoff_of`); with none it stays on the floor (`stay_of`, with the vertical page and the vertical speed of `floor_run`), with a ground input
(`gnd_in_of`). Once a field of `RoomRun` -/
theorem vfloor_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) {n : Nat} (h1 : r.C + N.fall ≤ n)
    (h2 : n < r.C + N.fall + N.lastG + 1 + N.rise) (hall : ∀ j, r.C + N.fall ≤ j → j ≤ n → OnFloor sy (r.fr.vs j)) : VFrame sy m N r.fr n := by
  have hvf := H.nums.vf.1
  have hfl := hall n h1 (Nat.le_refl _)
  cases hj : (r.fr.inp (n + 1)).jump with
  | true => exact r.takeoff_of H hr st (by omega) (by omega) hfl hj
  | false =>
    obtain ⟨g1, g2⟩ := r.gnd_in_of H hr st (by omega) (by omega) hfl.1
    have hfr := r.floor_run H hr st hw (n - (r.C + N.fall)) (by omega) (fun e he => hall _ (by omega) (by omega))
    rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at hfr
    have hs := r.stay_of H hr st (by omega) h2 hfl hj hfr.1 (by rw [hfr.2]; rfl)
    exact VFrame.stay hfl hs.1 ⟨g1, g2, hj⟩

/-- **`floor_at`**: with no wall the fall ends on the floor. A stand before `C + fall` would be the first stand, not on the floor (`fall_first`), so a frame stopped
by a side (`stand_off_of`); with no wall there is none. So frame `C + fall` is `vstepR` of the first fall or its landing, and he stands there (`land_at`): the landing,
on the floor's height (`fallCheck`) -/
theorem floor_at_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) (hw : NoWall sy m N r.fr r.C) : OnFloor sy (r.fr.vs (r.C + N.fall)) := by
  obtain ⟨hf0, hfs, _, _⟩ := fall_ok H.first
  have hhit := H.nums.hit_ge
  have hns : ∀ j, r.C < j → j < r.C + N.fall → (r.fr.vs j).st ≠ 0 := by
    intro j h1 h2 h3
    obtain ⟨i, i1, i2, i3, i4⟩ := first_of (P := fun j => (r.fr.vs j).st = 0) (r.C + N.fall) ⟨j, h1, h2, h3⟩
    have h5 := r.fall_first H hr st (n := i) (by omega) i2 (fun k a b => i4 k a b)
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact r.stand_off_of H hr st i' (by omega) (by omega) (Or.inl (by omega)) i3 h5 (hw i' (by omega) (by omega))
  obtain ⟨hok, h2⟩ := r.fall_next H hr st (d := N.fall - 1) (by omega) (fun j a b => hns j a (by omega))
  obtain ⟨s1, _, _, _, s5⟩ := fallStep_spec ((fallOk_spec hok).2 (r.fr.a (r.C + (N.fall - 1) + 1)))
  have e0 : r.C + (N.fall - 1) + 1 = r.C + N.fall := by omega
  have hl := r.land_at_of H hr st hw
  rw [← e0] at hl ⊢
  rcases h2 with e | ⟨_, e⟩
  · rw [e, s1] at hl
    exact absurd hl (by decide)
  · obtain ⟨_, hy⟩ := s5 (by omega)
    rw [e]
    exact ⟨rfl, hy⟩

/-- **`off_ab`**: a frame with a jump in its input ends on the takeoff of its height for the stored speed it reads at the player's routine (`InRoom.jump`, as
`vjump_of`, with `read_ab`) -/
theorem off_ab_of (H : Checks sy m N) (hr : r.InRoom) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hE : n + 1 < r.E) (hj : (r.fr.inp (n + 1)).jump = true) :
    r.fr.vs (n + 1) = jumpOffR sy m (r.fr.vs n).y (r.fr.ab n).toUInt8 ∧ r.fr.ab n < 256 := by
  have hv0 : r.fr.vs n = VertModel.vsOf sy (r.fm n) := r.vs_fm hr hC (by omega) (by omega)
  have hv1 : r.fr.vs (n + 1) = VertModel.vsOf sy (PipeTransition.frame (r.fm n) (r.inAt n)) := by
    rw [r.vs_fe (n := n + 1) (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega))]
  have hjr : (FrameModel.readIn sy (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n))).jump = true := by
    rw [← r.read_inp hC ht]
    exact hj
  have hab := r.read_ab n hC ht
  have eab : (r.fr.ab n).toUInt8 = peek (PipeEntryRule.trace (r.fm n) (r.inAt n) (r.arr n)) sy.Player_XSpeedAbsolute := by
    rw [hab]
    exact UInt8.ofNat_toNat
  refine ⟨?_, by rw [hab]; exact UInt8.toNat_lt _⟩
  rw [eab, hv1, hv0]
  exact hr.jump n hC hE (r.arr n) (r.atV_of H hr hC ht) hjr

/-- **`push_one`**: after a frame that is stopped or moves left, a frame that starts in the air moves him at most one pixel right (round 28). At its start
`V ≤ stopPhi`: stopped, `|V| ≤ Φ ≤ stopPhi`; moving left, `V < 0`. A frame that follows `hstep` ends with `V' < 17·256`: from a stop `|V'| ≤ Φ' ≤ Φ + gFast`
(`Potential.stepOk`), from moving left `V' ≤ gFast` (`gainCheck`, the input is an air input: `air_in_of`); so `16·v' ≤ 256`. A frame that does not is a `TopSpeed.Frame`
(`FrameModel.frame_readR`): `V₂ ≤ max(V, 0) + amax < 17·256`, so `P₂ ≤ P + 256`, and the collision leaves `P₂`, `P₂ − 256`, or at most `P + 256` -/
theorem push_one_of (H : Checks sy m N) (hr : r.InRoom) (st : StartAt sy N (r.fe r.C)) {n : Nat} (hC : r.C ≤ n) (ht : n < r.t0) (hsF : n < r.C + N.standF)
    (hst : (r.fr.vs n).st ≠ 0) (hn : Stop sy m N r.fr n ∨ sbyte (r.fr.hs n).v < 0) : r.fr.P (n + 1) ≤ r.fr.P n + 256 := by
  have hF := H.corner
  have hsm := hF.small
  have hsn := H.nums.stop_nonneg
  have hE := r.t0_le_E H hr
  have eg : gFast sy m = amax sy m := rfl
  have hdn : inD sy (r.fr.hs n) = true := by
    have h := r.inD_of H hr st (n - r.C) (by omega)
    rwa [show r.C + (n - r.C) = n by omega] at h
  have hfn := (r.fr.hs n).f.toNat_lt
  -- at the start: `V ≤ stopPhi`
  have hV0 : V (r.fr.hs n) ≤ N.stopPhi := by
    rcases hn with ⟨_, hphi, _⟩ | hneg
    · have := phi_ge H.air.pot (r.fr.hs n)
      omega
    · unfold V
      omega
  rcases r.clean n hC ht with hc | ⟨_, hc⟩
  · -- the frame follows `hstep`
    obtain ⟨hi, hh, hP⟩ := r.follow_of_clean H hr st hC ht (r.cleanR_of H hr hC ht hc)
    have hV1 : V (r.fr.hs (n + 1)) < 17 * 256 := by
      rcases hn with ⟨_, hphi, _⟩ | hneg
      · have hok := H.air.pot.check _ hdn _ hi
        simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        have h1 := hok.1.1.2
        rw [← hh] at h1
        have h2 := phi_ge H.air.pot (r.fr.hs (n + 1))
        have h3 : V (r.fr.hs (n + 1)) ≤ ((V (r.fr.hs (n + 1))).natAbs : Int) := by omega
        omega
      · have hai := r.air_in_of H hr st n hC hsF hst
        have h1 := gain_of_check H.standW.sp H.normI hF.gain1 hF.gain2 hF.gain3 _ hdn hneg _ hi (by rw [hai.2.1]; decide)
        rw [← hh] at h1
        omega
    have hf1 := (r.fr.hs (n + 1)).f.toNat_lt
    unfold V at hV1
    rw [hP]
    omega
  · -- a `TopSpeed.Frame`
    have hR := r.readR_of H hr hC ht hdn hc
    obtain ⟨idle, hT⟩ := r.inTime_of H hr
    obtain ⟨f, e1, e2, e3, _, _, e6⟩ := FrameModel.frame_readR H.model H.fric hR (r.before_of H hr hC ht hR.at_frame.pc) (hT n hC ht hR.at_frame.pc)
      (r.far_of H hr st hC ht)
    have eV : V (r.fr.hs n) = 256 * f.v + f.f := by
      rw [e1, e2, r.hs_fm hr hC (by omega) (by omega)]
      rfl
    have hgain := f.friction_gain
    have hfr := f.frac
    have hm := f.move
    have hB := f.baseP rfl
    have hv2 : 256 * f.v₂ < 17 * 256 := by
      rcases f.anim with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · rw [a1, a2] at hgain
        have : max (256 * f.v + f.f) 0 ≤ N.stopPhi := by omega
        omega
      · rw [a1, a2] at hgain
        omega
    rw [r.P_fe (n := n + 1) (by omega) (by omega), r.P_fm hr hC (by omega) (by omega), r.next hC (r.ups_lt hr hC (by omega)), ← e6, ← e3]
    rcases f.impedeP with h | h | ⟨h, _⟩ <;> omega

/-- the frames as numbers -/
def toCore (H : Checks sy m N) (st : StartAt sy N (r.fe r.C)) (hr : r.InRoom) : RoomCore sy m N ((S.seq b).ram.get! (FrameModel.I sy.PlayerSize)) :=
  { r.toRoomFields with
    vfloor := fun hw _ h1 h2 _ hall => r.vfloor_of H hr st hw h1 h2 hall
    varc := fun _ _ hC ht hE ha hk => r.varc_of H hr hC ht hE ha hk
    stand_row := r.stand_row_of H hr, stand_off := r.stand_off_of H hr st
    stand_hit := fun _ hC h1 hW hall hnf hns h0 => r.stand_hit_of H hr st hC h1 hW hall hnf hns h0
    stop_run := fun _ h1 h2 hrs hv hf => r.stop_run_of H hr st h1 h2 hrs hv hf
    facing := r.facing_of H hr st
    low_floor := fun hw _ h1 h2 h3 hall _ hs hl => r.low_floor_of H hr st hw h1 h2 h3 hall hs hl
    low_jump := fun hw _ _ h0 h1 h2 h3 hfl harc hylo _ hs hT => r.low_jump_of H hr st hw h0 h1 h2 h3 hfl harc hylo hs hT
    push_one := fun _ hC ht hsF hst hn => r.push_one_of H hr st hC ht hsF hst hn
    off_ab := fun _ hC ht hE hj => r.off_ab_of H hr hC ht hE hj
    air_in := r.air_in_of H hr st, fall_long := r.fall_long_of H hr st, vfall := r.vfall_of H hr st, floor_at := r.floor_at_of H hr st
    start := r.start_hs st, startP0 := (r.start_P st).1, startP1 := (r.start_P st).2, v_start := r.start_v st
    frames := r.frames_of H hr st, move_top := r.move_top_of H hr st, mouth := r.mouth_of hr, ab_of := r.ab_of_run H hr }

/-- **The entry comes at least `goalF + aboveF` frames after first control.** `st` is the state at first control on the machine, `hr` what the room's frames give about frame
`E`. -/
theorem entry_ge (H : Checks sy m N) (st : StartAt sy N (r.fe r.C)) (hr : r.InRoom) : r.C + N.goalF + N.aboveF ≤ r.E := (r.toCore H st hr).entry_ge H

end RoomRun

end Smbrta.RoomJoin
