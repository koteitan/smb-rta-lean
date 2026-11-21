import Theorems.Route
import Theorems.PoleTileKeep

/-!
# The pole's tiles at control above ground: from the rows of the change

`PoleTileWalk.frames_colMap` carries the map `ColMap` (every pole's tile in the block buffers is in the pole's column) from the machine at control above ground to the start
of the touch's frame. Here the map at control is proved. The rows of the change out of the side pipe (`SideChangeSound`) cover the machine at control
(`SidePause.EndRunQ.inRows`). In every state of the rows that has control, every byte of the block buffers is known, and none is a pole's tile out of the pole's column
(`mapCheckK`, a check on the ROM). So the machine at control has the map (`EndRunQ.colMap`, `colMap₀` on a real run of the route).
In the same states the two bytes that `PoleTileKeep` watches have their values (`watchCheckK`, `watch₀`).

There is no game data in this file. Page: `1-1/f-6-17-2-PoleTileWalk.md`.
-/

namespace Smbrta.PoleTileCtl

open TaintRun (AS Sim Env)
open SideChangeEnd (Row Ctx InvL knowsAd mOf)
open PoleEntryRule (Spots onCol)
open PoleTileWalk (ColMap)

/-- a state of a row: it knows the bytes of control, and if it has control, it knows every byte of the block buffers, and none is a pole's tile out of the pole's
column -/
def rowMap (sy : Syms) (Q : Spots) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || (List.range Q.bufBytes).all fun k =>
      (S.getK (Q.bufLo + k)).isK && (!PoleTiles.tileB Q (S.getK (Q.bufLo + k)).v || onCol Q (Q.bufLo + k)))

/-- every state of the rows -/
def rowsMap (sy : Syms) (Q : Spots) (l : List Row) : Bool := l.all fun r => r.R.all (rowMap sy Q)

/-- **The check on the ROM**: the block buffers end in the pole's map in every state with control of the rows of the change out of the side pipe -/
def mapCheckK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  decide ((PoleFrame.spotsF sy m0).bufLo + (PoleFrame.spotsF sy m0).bufBytes ≤ 2048) &&
    rowsMap sy (PoleFrame.spotsF sy m0) ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row))

variable {sy : Syms}

/-- a covered machine with control has the map -/
theorem map_of_state {E : Env} {F : Nat × UInt8} {Q : Spots} {S : AS} {m : Machine} (hb : Q.bufLo + Q.bufBytes ≤ 2048) (hs : Sim E F S m)
    (hr : rowMap sy Q S = true) (h : controllable sy m = true) : ColMap Q m := by
  simp only [rowMap, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | h1
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · intro i h2 h3 ht
    have hi := List.all_eq_true.1 h1 (i - Q.bufLo) (List.mem_range.2 (by omega))
    rw [show Q.bufLo + (i - Q.bufLo) = i by omega] at hi
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
    obtain ⟨hk1, hc⟩ := hi
    have e := PipeEntryRule.known_eq hk1 (hs.ram i (by omega))
    rcases hc with hc | hc
    · rw [e] at ht
      rw [PoleTiles.tileB_spec.2 ht] at hc
      cases hc
    · exact hc

theorem map_of_invL {C : Ctx} {Q : Spots} (hb : Q.bufLo + Q.bufBytes ≤ 2048) :
    ∀ {l : List Row}, rowsMap sy Q l = true → ∀ {m : Machine}, InvL C l m → controllable sy m = true → ColMap Q m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsMap, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact map_of_state hb hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact map_of_invL hb hl.2 h hc

section
variable {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine} {m0 : Machine}

/-- **The machine at control has the map**, on a real run of the change, from the rows of `SideChangeSound` (the run of `SidePause`) -/
theorem EndRunQ.colMap (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : mapCheckK sy m0 nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    ColMap (PoleFrame.spotsF sy m0) (R'.seq R'.b) := by
  simp only [mapCheckK, Bool.and_eq_true, decide_eq_true_eq] at hk
  exact map_of_invL hk.1 hk.2 (SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)) R'.atCtl

end

section
open Route

variable {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : PipeTransitionAll.Names} {d₁ : PipeChangeEnd.Data}
  {nm₂ nx₂ nmS : PipeTransitionAll.Names} {fc : FlagRule.Ctx} {tc : TitleStart.Ctx}

/-- **The map at control above ground**, on the real machines: from the last rows of the change, under the same conditions as `Route.Run.atCtl₀`. `hm` is the check on
the ROM. With `PoleJoin.Run.bufAll` it gives the map at the start of the touch's frame (`PoleJoin.Run.tilesStart`). -/
theorem colMap₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : mapCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ColMap (PoleFrame.spotsF sy m0) (R.pole.seq 0) := by
  rw [R.atCtl]
  exact EndRunQ.colMap hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

end

/-! ## The two bytes of `PoleTileKeep` at control, from the rows of the change -/


/-- a state of a row: it knows the bytes of control, and if it has control, the watched bits `W` -/
def rowW (sy : Syms) (W : List FrameKeep.Watch) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) && (!controllable sy (mOf S) || FrameKeep.watchOK W S)

/-- every state of the rows -/
def rowsW (sy : Syms) (W : List FrameKeep.Watch) (l : List Row) : Bool := l.all fun r => r.R.all (rowW sy W)

/-- **The check on the ROM**: the two bytes have their watched bits in every state with control of the rows of the change out of the side pipe -/
def watchCheckK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  rowsW sy (PoleTileKeep.watchB sy m0) ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row))

/-- **The two checks in one pass over the rows**: `mapCheckK` and `watchCheckK` -/
def mapWatchK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  let l := (SideChangeSound.rowsOf sy nm nx e A B R).map (·.row)
  decide ((PoleFrame.spotsF sy m0).bufLo + (PoleFrame.spotsF sy m0).bufBytes ≤ 2048) && rowsMap sy (PoleFrame.spotsF sy m0) l && rowsW sy (PoleTileKeep.watchB sy m0) l

theorem mapWatch_map {sy : Syms} {m0 : Machine} {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} (h : mapWatchK sy m0 nm nx e A B R = true) :
    mapCheckK sy m0 nm nx e A B R = true := by
  simp only [mapWatchK, mapCheckK, Bool.and_eq_true] at h ⊢
  exact h.1

theorem mapWatch_watch {sy : Syms} {m0 : Machine} {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} (h : mapWatchK sy m0 nm nx e A B R = true) :
    watchCheckK sy m0 nm nx e A B R = true := by
  simp only [mapWatchK, watchCheckK, Bool.and_eq_true] at h ⊢
  exact h.2

theorem watch_of_state {sy : Syms} {E : Env} {F : Nat × UInt8} {W : List FrameKeep.Watch} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowW sy W S = true)
    (h : controllable sy m = true) : FrameKeep.Watched W m := by
  simp only [rowW, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | h1
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · exact FrameKeep.watched_of h1 hs

theorem watch_of_invL {sy : Syms} {C : Ctx} {W : List FrameKeep.Watch} :
    ∀ {l : List Row}, rowsW sy W l = true → ∀ {m : Machine}, InvL C l m → controllable sy m = true → FrameKeep.Watched W m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsW, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact watch_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact watch_of_invL hl.2 h hc

section
variable {sy : Syms} {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine} {m0 : Machine}

/-- **The machine at control has the two bytes' watched bits**, on a real run of the change, from the rows of `SideChangeSound` (the run of `SidePause`) -/
theorem EndRunQ.watch (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : watchCheckK sy m0 nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R'.seq R'.b) :=
  watch_of_invL hk (SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)) R'.atCtl

end

section
open Route

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : PipeTransitionAll.Names} {d₁ : PipeChangeEnd.Data}
  {nm₂ nx₂ nmS : PipeTransitionAll.Names} {fc : FlagRule.Ctx} {tc : TitleStart.Ctx}

/-- **The two bytes at control above ground**, on the real machines: from the last rows of the change, under the same conditions as `PoleTileCtl.colMap₀`. `hm` is the
check on the ROM. -/
theorem watch₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : watchCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.pole.seq 0) := by
  rw [R.atCtl]
  exact EndRunQ.watch hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

end


end Smbrta.PoleTileCtl
