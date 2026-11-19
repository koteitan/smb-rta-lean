import Theorems.RoomLanding

/-! Instruction prefixes from a cut to a selected foot call.
The check is a local sufficient condition, not an added Run field. -/
namespace Smbrta.RoomFootPrefix
open FrameModel

/-- Select the caller by its saved return address, so a preceding head call
to the same collision routine does not stop the walk. -/
def callCut (entry ret : UInt16) (sp : UInt8) : Cut :=
  {pc := entry,s := sp,
   K := [(stkI (sp+1),(ret-1).toUInt8),(stkI (sp+2),((ret-1) >>> 8).toUInt8)],
   ra := some 0,x := some 0}

def callStop (entry ret : UInt16) (sp : UInt8) (T : TS) : Bool :=
  T.pc == entry && T.s == some sp &&
    (callCut entry ret sp).K.all (fun kv => (T.ram kv.1).same == some kv.2)

/-- Both the coordinates and the offset index are checked at the actual
collision routine's entry, after the overlapping BIT wrapper. -/
def check (E : Rom) (P : RoomCollision.Places) (c : Cut)
    (ret : UInt16) (sp index : UInt8) (fuel : Nat) : Bool :=
  walkT E (callStop P.entry ret sp)
    (fun T => goalC (callCut P.entry ret sp) (RoomCollision.coords P) T &&
      T.y.same == some index) fuel (startQ c)

theorem returnPc_at {E : Rom} {entry ret : UInt16} {sp : UInt8} {R : Machine}
    (h : At E (callCut entry ret sp) R) : RoomCollision.returnPc R = ret := by
  have lo := h.K _ (List.mem_cons_self ..)
  have hi := h.K _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold RoomCollision.returnPc
  rw [h.s]
  change ((R.ram.get! (stkI (sp+1))).toUInt16 |||
    ((R.ram.get! (stkI (sp+1+1))).toUInt16 <<< 8))+1 = ret
  have e : sp+1+1 = sp+2 := by bv_decide
  rw [e,lo,hi]
  bv_decide

/-- A successful bounded prefix reaches the chosen real call, preserves all
address coordinates and supplies its exact foot index and vertical-read flag. -/
theorem foot_prefix {E : Rom} {P : RoomCollision.Places} {c : Cut}
    {ret : UInt16} {sp index : UInt8} {fuel : Nat} {Q : Machine}
    (hc : check E P c ret sp index fuel = true) (hq : At E c Q)
    (hb : ∀ j ∈ RoomCollision.coords P, j < 2048) :
    ∃ k, k ≤ fuel ∧ Good E (stepN k Q) ∧ (stepN k Q).pc = P.entry ∧
      (stepN k Q).x = 0 ∧ (stepN k Q).a = 0 ∧ (stepN k Q).y = index ∧
      RoomCollision.returnPc (stepN k Q) = ret ∧
      (∀ j ∈ RoomCollision.coords P, (stepN k Q).ram.get! j = Q.ram.get! j) ∧
      InFrameN E Q k := by
  obtain ⟨k,T,hk,_,hg,H,hh⟩ := walkT_spec fuel (startQ c) Q Q hc (lk_self hq)
  have hgoal : goalC (callCut P.entry ret sp) (RoomCollision.coords P) T = true ∧
      (T.y.same == some index) = true := by
    simpa only [Bool.and_eq_true] using hg
  obtain ⟨ha,hw,_⟩ := at_of_goal hgoal.1 H
  have hy : (stepN k Q).y = index :=
    (Tag.same_spec (beq_iff_eq.1 hgoal.2) H.regs.y).1
  exact ⟨k,hk,ha.good,ha.pc,ha.x 0 rfl,ha.ra 0 rfl,hy,
    returnPc_at ha,fun j hj => hw j hj (hb j hj),
    fun j hj => by obtain ⟨_,_,_,_,hi,_⟩ := hh j hj; exact hi⟩

/-- The local prefix and the complete collision routine compose: if the map
is solid at the read, the selected actual foot call returns the map cell
computed from the cut's coordinates and the checked foot index.
This does not yet follow the caller's landing branch. -/
theorem returned_map {sy : Syms} {nm : PipeTransitionAll.Names}
    {m0 Q M : Machine} {cs : List UInt8} {c : Cut}
    {ret : UInt16} {sp index : UInt8} {fuel : Nat}
    (hp : check (Rom.of m0) (RoomCollision.places sy m0) c ret sp index fuel = true)
    (hq : At (Rom.of m0) c Q) (hc : RoomCollision.check sy nm m0 = true)
    (solid : ∀ j, RoomBlocks.Solid (EntryHeight.hpOf sy nm m0).P cs M (stepN j Q))
    (hl : (EntryHeight.hpOf sy nm m0).P.bufLo ≤
      I (RoomCollision.readAddress (Rom.of m0) (EntryHeight.hpOf sy nm m0).P
        (RoomCollision.places sy m0) {Q with y := index}))
    (hr : I (RoomCollision.readAddress (Rom.of m0) (EntryHeight.hpOf sy nm m0).P
        (RoomCollision.places sy m0) {Q with y := index}) <
        (EntryHeight.hpOf sy nm m0).P.bufLo+(EntryHeight.hpOf sy nm m0).P.bufN)
    (nc : M.ram.get! (I (RoomCollision.readAddress (Rom.of m0)
        (EntryHeight.hpOf sy nm m0).P (RoomCollision.places sy m0) {Q with y := index})) ∉ cs) :
    ∃ k nr nt, k ≤ fuel ∧ nr ≤ 93 ∧ nt ≤ 25 ∧
      (stepN k Q).pc = sy.BlockBufferCollision ∧ (stepN k Q).y = index ∧
      (stepN (k+nr+nt) Q).pc = ret ∧
      (stepN (k+nr+nt) Q).a = M.ram.get! (I (RoomCollision.readAddress (Rom.of m0)
        (EntryHeight.hpOf sy nm m0).P (RoomCollision.places sy m0) {Q with y := index})) := by
  have F := RoomCollision.facts_of_check hc
  obtain ⟨k,hk,g,pc,x,_,hy,hret,coord,_⟩ := foot_prefix hp hq
    (fun j hj => F.ram_lt (List.mem_append_left _ hj))
  obtain ⟨nr,nt,hnr,hnt,_,H,_⟩ := RoomCollision.routine hc g pc x
  have hs := solid (k+nr)
  have hs' : RoomBlocks.Solid (EntryHeight.hpOf sy nm m0).P cs M (stepN nr (stepN k Q)) := by
    simpa only [stepN_add] using hs
  have hl' := hl
  have hr' := hr
  have nc' := nc
  rw [← hy] at hl' hr' nc'
  have av := RoomCollision.returned_map_from_coords H hs' coord hl' hr' nc'
  rw [hy] at av
  refine ⟨k,nr,nt,hk,hnr,hnt,pc,hy,?_,?_⟩
  · simpa only [stepN_add,hret] using H.pc
  · simpa only [stepN_add] using av

end Smbrta.RoomFootPrefix

namespace Smbrta.Route
open PipeTransitionAll (Names)
open FrameModel (Good Rom idleAt I)

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {fc : FlagRule.Ctx}
  {tc : TitleStart.Ctx}


/-- A checked prefix inside a room frame supplies the call for roomCollisionMap.
Only local prefix and cell conditions are additional; no Run field is added. -/
theorem Run.roomFootMap {es₁ : List Machine}
    (hT₁ : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hM : RoomMap.MapFacts sy nmS m0)
    (hS : RoomMap.startCheckT sy nm₁ d₁ (PipeTransition.entry m0) nmS m0 = true)
    (hW : RoomBlocks.BChecks sy nmS m0)
    (hRw : RoomBlocks.rowsCheckR sy nm₁ d₁ nmS m0 rN.vStart = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc)
    {k n fuel : Nat} {c : FrameModel.Cut} {ret : UInt16} {sp index : UInt8}
    (hk0 : R.base.b₁ sy ≤ k) (hk1 : k < R.base.a₂ sy nmS m0)
    (hc : RoomCollision.check sy nmS m0 = true)
    (hp : RoomFootPrefix.check (Rom.of m0) (RoomCollision.places sy m0) c ret sp index fuel = true)
    (hq : FrameModel.At (Rom.of m0) c (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n))
    (hf : (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n).frame = (R.base.seq k).frame)
    (loop : idleAt (Rom.of m0) (ScreenPage.placesR sy nmS m0).idle = true)
    (hl : (ScreenPage.placesR sy nmS m0).bufLo ≤ I (RoomCollision.readAddress (Rom.of m0)
      (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0)
        {(PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n) with y := index}))
    (hr : I (RoomCollision.readAddress (Rom.of m0)
      (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0)
        {(PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n) with y := index}) <
        (ScreenPage.placesR sy nmS m0).bufLo+(ScreenPage.placesR sy nmS m0).bufN)
    (nc : (RoomMap.mapRef m0).ram.get! (I (RoomCollision.readAddress (Rom.of m0)
      (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0)
        {(PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n) with y := index})) ∉
        RoomBlocks.coinsOf (ScreenPage.placesR sy nmS m0)) :
    ∃ np nr nt, np ≤ fuel ∧ nr ≤ 93 ∧ nt ≤ 25 ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np)).pc = sy.BlockBufferCollision ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np)).y = index ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np+nr+nt)).pc = ret ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np+nr+nt)).a =
        (RoomMap.mapRef m0).ram.get! (I (RoomCollision.readAddress (Rom.of m0)
          (ScreenPage.placesR sy nmS m0) (RoomCollision.places sy m0)
            {(PipeEntryRule.trace (R.base.seq k) (R.base.inp k) n) with y := index})) ∧
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np+nr+nt)).frame = (R.base.seq k).frame := by
  have FC := RoomCollision.facts_of_check hc
  obtain ⟨np,hnp,g,pc,x,_,hy,hret,coord,ifr⟩ := RoomFootPrefix.foot_prefix hp hq
    (fun j hj => FC.ram_lt (List.mem_append_left _ hj))
  have time : ∀ j, (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) j).pc ≠
      (ScreenPage.placesR sy nmS m0).idle →
      (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) j).fdot ≤ dotsPerFrame-64 := by
    intro j hj
    apply Nat.le_trans ((R.chg.roomSites k hk0 hk1 j).late hj)
    change dotsPerFrame-6000 ≤ dotsPerFrame-64
    decide
  have eq := FrameModel.trace_inFrame loop hf ifr time np (Nat.le_refl _)
  have ad := RoomCollision.readAddress_from_coords
    (E := Rom.of m0) (B := ScreenPage.placesR sy nmS m0) coord
  rw [hy] at ad
  have gr : Good (Rom.of m0) (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np)) := by
    rw [eq.1]; exact g
  have pr : (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np)).pc = sy.BlockBufferCollision := by
    rw [eq.1]; exact pc
  have xr : (PipeEntryRule.trace (R.base.seq k) (R.base.inp k) (n+np)).x = 0 := by
    rw [eq.1]; exact x
  obtain ⟨nr,nt,hnr,hnt,prout,arout,frout⟩ :=
    R.roomCollisionMap hT₁ hM hS hW hRw hB hK hk0 hk1 hc gr pr xr eq.2 loop
      (by rw [eq.1,ad]; exact hl) (by rw [eq.1,ad]; exact hr) (by rw [eq.1,ad]; exact nc)
  refine ⟨np,nr,nt,hnp,hnr,hnt,pr,?_,?_,?_,frout⟩
  · rw [eq.1]; exact hy
  · rw [prout,eq.1,hret]
  · rw [arout,eq.1,ad]

end Smbrta.Route
