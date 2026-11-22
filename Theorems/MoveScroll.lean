import Theorems.PlaceKeep

/-!
# Above ground: the byte the move stores for the scroll

The scroll handler moves the screen by the byte that the move stores (`ScrollRule.Places.xs`, round 27: the platforms' force is 0 there), when the scroll lock and
the side collision's timer are 0 and his place on the screen is at least a threshold (`ScrollRule.Allows`). The mover (`FrameModel.tailOK`) adds `16·v` to the
position in three digits: the fraction with the low digit, the pixel with the middle digit and the carry, the page with the high digit and the carry. It returns
the middle digit plus the carry out of the fraction, and the routine that called it stores that as the byte. So the byte is the change of his pixel (with the page)
in the frame up to the scroll handler, modulo 256.

This file proves it on the ROM for each cut of the mover (`xsTailOK`, `xs_tail`): from the load of the fraction to the push of the carry, and from there to the
scroll handler, which keeps the middle digit, the speed and the stack and stores the byte. With the position's change of `FrameModel.tail_spec` this gives, when
the byte is from 1 to 128 (as the scroll needs it), pixel16(Q) = pixel16(R) + xs(Q), where `R` is the frame's first arrival at the player's routine and `Q` its
scroll handler (`move_xs`).

So the field `near` of `SurfaceFrames.OnFrames` (`EdgeStep.NearX` at the scroll handler) follows from a condition on the state at the arrival (`NearA`), with the
walks of `PlaceKeep.keep_place` (the timer, the place byte, the lock and the edge kept from the arrival to the scroll handler): `nearX_of_a`.

No game data: the cuts and the bytes come from `FrameModel.sitesOf` and `ScrollRule.places`. Page: `1-1/e-2-10-3-16-MoveScroll.md`.
-/

namespace Smbrta.MoveScroll
open FrameModel
open PipeEntryRule (trace)

variable {sy : Syms} {E : Rom}

/-! ## The check on the ROM -/

/-- the sixteen values of the low digit of `16·v` -/
def lows : List UInt8 := (List.range 16).map fun n => (n * 16).toUInt8

/-- the facts of the digits that the byte needs: the low digit is one of `lows`; `16·v` is 256 times the middle digit (as a signed byte, from −8 to 7) plus the low
digit; the middle digit plus a carry, when it is from 1 to 128, is that number -/
def xsDigits : Bool :=
  TopSpeed.bytes.all fun b =>
    lows.contains (lOf b) && (16 * sbyte b == 256 * sbyte (dOf b) + ((lOf b).toNat : Int)) && decide (-8 ≤ sbyte (dOf b)) && decide (sbyte (dOf b) ≤ 7) &&
      [false, true].all fun c => !ScrollRule.xOK (dOf b + cB c) || (sbyte (dOf b) + (if c then 1 else 0) == ((dOf b + cB c).toNat : Int))

/-- **The walks of the byte, from the cut `c4` of the mover**: from the load of the fraction (`sF`, the fraction and the low digit known) to the load of the pixel
(`sX`), the carry is pushed and the middle digit, the speed and the bytes of the cut are not written; from there, with the carry on the stack, the middle digit, the speed
and the bytes of the cut known, to the scroll handler, which the walk reaches with the byte `xs` = middle digit + carry -/
def xsTailOK (sy : Syms) (E : Rom) (xs : Nat) (c4 : Cut) : Bool :=
  let M := sitesOf sy E
  let v := I sy.Player_X_Speed
  let mf := I sy.SprObject_X_MoveForce
  decide (xs < 2048) && decide (stkI c4.s < 2048) &&
  TopSpeed.bytes.all (fun f => lows.all fun l =>
    pieceOK E { pc := M.sF, s := c4.s, K := [(mf, f), (M.iL, l)], x := some 0 }
      { pc := M.sX, s := c4.s - 1, K := [(stkI c4.s, cB (adcC f l false).2)], x := some 0 } (M.iD :: v :: c4.ids) fuelS) &&
  TopSpeed.bytes.all (fun b => [false, true].all fun c =>
    pieceOK E { pc := M.sX, s := c4.s - 1, K := (stkI c4.s, cB c) :: (M.iD, dOf b) :: (v, b) :: c4.K, x := some 0 }
      { pc := sy.PlayerSubs, s := (cutV sy E c4).s, K := [(xs, dOf b + cB c)] } [] (fuelW + 4 * fuelS))

/-- **The check on the ROM**: the digits, and the walks of the byte from every cut of the mover -/
def xsCheck (sy : Syms) (m0 : Machine) : Bool :=
  xsDigits && (tailsOf sy m0 (ctrlStack sy m0)).all (xsTailOK sy (Rom.of m0) (ScrollRule.places sy m0).xs)

/-! ## The mover's byte, on a real machine -/

/-- **From the cut of the mover to the scroll handler** the machine stores the byte `xs` = middle digit of `16·v` + the carry out of the fraction plus the low
digit (`v` the speed, `f` the fraction at the cut) -/
theorem xs_tail {c4 : Cut} {R : Machine} {xs : Nat} (ht : tailOK sy E c4 = true) (hc : xsTailOK sy E xs c4 = true) (hd : xsDigits = true) (h : At E c4 R) :
    ∃ k, (stepN k R).pc = sy.PlayerSubs ∧
      (stepN k R).ram.get! xs = dOf (R.ram.get! (I sy.Player_X_Speed)) +
        cB (adcC (R.ram.get! (I sy.SprObject_X_MoveForce)) (lOf (R.ram.get! (I sy.Player_X_Speed))) false).2 ∧ InFrameN E R k := by
  simp only [tailOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hiD⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hK⟩, _⟩, _⟩, _⟩, a7⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := ht
  simp only [xsTailOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨_, hstk⟩, b1⟩, b2⟩ := hc
  simp only [xsDigits, List.all_eq_true, Bool.and_eq_true] at hd
  have hb := fun (b : UInt8) => Potential.mem_bytes b
  generalize hM : sitesOf sy E = M at a7 b1 b2 hiD
  generalize hb0 : R.ram.get! (I sy.Player_X_Speed) = b
  generalize hf0 : R.ram.get! (I sy.SprObject_X_MoveForce) = f0
  -- to the load of the fraction (the piece of `tailOK`)
  have hA1 : At E { c4 with K := (I sy.Player_X_Speed, b) :: c4.K } R := by
    refine ⟨h.good, h.pc, h.s, ?_, h.B, h.ra, h.x, h.cf⟩
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hb0
    · exact h.K p hp
  obtain ⟨k1, _, A1, W1, _, C1⟩ := piece_spec (a7 b (hb b)) hA1
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have hL : R1.ram.get! M.iL = lOf b := A1.K (M.iL, lOf b) List.mem_cons_self
  have hD1 : R1.ram.get! M.iD = dOf b := A1.K (M.iD, dOf b) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hC1 : ∀ p ∈ c4.K, R1.ram.get! p.1 = p.2 := fun p hp => A1.K p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)))
  have hmf1 : R1.ram.get! (I sy.SprObject_X_MoveForce) = f0 := by rw [W1 _ List.mem_cons_self (I_lt _)]; exact hf0
  have hv1 : R1.ram.get! (I sy.Player_X_Speed) = b := by
    rw [W1 _ (by simp [keepM]) (I_lt _)]
    exact hb0
  -- the push of the carry
  have hl : lOf b ∈ lows := List.contains_iff_mem.1 (hd b (hb b)).1.1.1.1
  have hA2 : At E { pc := M.sF, s := c4.s, K := [(I sy.SprObject_X_MoveForce, f0), (M.iL, lOf b)], x := some 0 } R1 := by
    refine ⟨A1.good, A1.pc, A1.s, ?_, ?_, ?_, A1.x, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hmf1
      · rcases List.mem_singleton.1 hp with rfl
        exact hL
    · intro p hp
      cases hp
    · intro v hv
      cases hv
    · intro v hv
      cases hv
  obtain ⟨k2, _, A2, W2, _, C2⟩ := piece_spec (b1 f0 (hb f0) (lOf b) hl) hA2
  generalize hR2 : stepN k2 R1 = R2 at A2 W2
  have hS2 : R2.ram.get! (stkI c4.s) = cB (adcC f0 (lOf b) false).2 := A2.K _ List.mem_cons_self
  have hD2 : R2.ram.get! M.iD = dOf b := by rw [W2 _ List.mem_cons_self hiD]; exact hD1
  have hv2 : R2.ram.get! (I sy.Player_X_Speed) = b := by rw [W2 _ (List.mem_cons_of_mem _ List.mem_cons_self) (I_lt _)]; exact hv1
  have hC2 : ∀ p ∈ c4.K, R2.ram.get! p.1 = p.2 := fun p hp => by
    rw [W2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨p, hp, rfl⟩))) (hK p hp)]
    exact hC1 p hp
  -- to the scroll handler
  have hA3 : At E { pc := M.sX, s := c4.s - 1, K := (stkI c4.s, cB (adcC f0 (lOf b) false).2) :: (M.iD, dOf b) :: (I sy.Player_X_Speed, b) :: c4.K, x := some 0 } R2 := by
    refine ⟨A2.good, A2.pc, A2.s, ?_, ?_, ?_, A2.x, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hS2
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hD2
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hv2
      · exact hC2 p hp
    · intro p hp
      cases hp
    · intro v hv
      cases hv
    · intro v hv
      cases hv
  obtain ⟨k3, _, A3, _, _, C3⟩ := piece_spec (b2 b (hb b) (adcC f0 (lOf b) false).2 (by cases (adcC f0 (lOf b) false).2 <;> simp)) hA3
  have hfin : stepN (k1 + (k2 + k3)) R = stepN k3 R2 := by rw [stepN_add, hR1, stepN_add, hR2]
  refine ⟨k1 + (k2 + k3), by rw [hfin]; exact A3.pc, by rw [hfin]; exact A3.K _ List.mem_cons_self, InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)⟩

/-- **The pixel moves by the byte**: the position moves by `16·v` (modulo 2²⁴), the byte is the middle digit plus the carry out of the fraction, it is from 1 to 128,
and the position is away from the end of its range; then the pixel with the page moves by the byte -/
theorem pix_of_xs {p x f p' x' f' b : UInt8} (hd : xsDigits = true) (hP : (posOf p' x' f' - posOf p x f - 16 * sbyte b) % 0x1000000 = 0)
    (hfar : posOf p x f + 2048 < 0x1000000) (hok : ScrollRule.xOK (dOf b + cB (adcC f (lOf b) false).2) = true) :
    p'.toNat * 256 + x'.toNat = p.toNat * 256 + x.toNat + (dOf b + cB (adcC f (lOf b) false).2).toNat := by
  simp only [xsDigits, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hd
  obtain ⟨⟨⟨⟨_, e1⟩, e2⟩, e3⟩, e4⟩ := hd b (Potential.mem_bytes b)
  have hn := adcC_nat f (lOf b) false
  have hc := e4 (adcC f (lOf b) false).2 (by cases (adcC f (lOf b) false).2 <;> simp)
  have h1 := p.toNat_lt
  have h2 := x.toNat_lt
  have h3 := f.toNat_lt
  have h4 := p'.toNat_lt
  have h5 := x'.toNat_lt
  have h6 := f'.toNat_lt
  have h7 := (adcC f (lOf b) false).1.toNat_lt
  unfold posOf at hP hfar
  generalize (adcC f (lOf b) false).1 = f1 at hn h7
  generalize hcar : (adcC f (lOf b) false).2 = c at hn hc hok
  rcases hc with hc | hc
  · rw [hc] at hok
    cases hok
  · cases c <;> simp only [Bool.false_eq_true, if_false, if_true] at hn hc <;> omega

/-- **At the scroll handler the pixel is that of the arrival plus the byte**, when the byte is from 1 to 128: a frame read up to the scroll handler
(`SurfaceRead.ReadH`) comes to it at `k` (the walks of `FrameModel.frame_pathI`, `FrameModel.tail_spec` and `xs_tail`), and it comes there once (`honce`) -/
theorem move_xs {m0 M : Machine} {i : UInt8} {n₀ : Nat} (h : SurfaceRead.ReadH sy m0 M i n₀) (hx : xsCheck sy m0 = true)
    (honce : ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace M i k).pc = sy.PlayerSubs → (trace M i k').pc = sy.PlayerSubs → k = k') :
    ∃ k, n₀ ≤ k ∧ (trace M i k).pc = sy.PlayerSubs ∧
      (ScrollRule.xOK ((trace M i k).ram.get! (ScrollRule.places sy m0).xs) = true →
        EdgeStep.pixel16 sy (trace M i k) = EdgeStep.pixel16 sy (trace M i n₀) + ((trace M i k).ram.get! (ScrollRule.places sy m0).xs).toNat) := by
  simp only [xsCheck, Bool.and_eq_true, List.all_eq_true] at hx
  obtain ⟨hd, hxt⟩ := hx
  have hF := facts_of h.model
  have hb := base_good hF.base
  obtain ⟨k1, _, _, _, A1, _, _, S1, I1⟩ := frame_pathI hb h.fric hF h.at_frame
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h.at_frame)
  have e4 : t = (planOf sy m0 (ctrlStack sy m0) (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  have hxl := hxt t ht
  rw [e4] at htl hxl
  obtain ⟨k2, _, _, p2, _, _, _, _, _, q2, I2⟩ := tail_spec htl hF.digits A1
  obtain ⟨k3, p3, x3, I3⟩ := xs_tail htl hxl hd A1
  have e2 := (trace_inFrame h.time.loop h.time.start (InFrameN.add' I1 rfl I2) h.time.time (k1 + k2) (Nat.le_refl _)).1
  have e3 := (trace_inFrame h.time.loop h.time.start (InFrameN.add' I1 rfl I3) h.time.time (k1 + k3) (Nat.le_refl _)).1
  rw [stepN_add] at e2 e3
  have ek : n₀ + (k1 + k2) = n₀ + (k1 + k3) := honce _ _ (by omega) (by omega) (by rw [e2]; exact p2) (by rw [e3]; exact p3)
  have ek2 : k2 = k3 := by omega
  subst ek2
  refine ⟨n₀ + (k1 + k2), by omega, by rw [e2]; exact p2, fun hok => ?_⟩
  rw [e2] at hok ⊢
  rw [x3] at hok ⊢
  generalize hR1 : stepN k1 (trace M i n₀) = R1 at S1 q2 hok ⊢
  obtain ⟨s1, s2, s3⟩ := S1
  have hfar : posOf (R1.ram.get! (I sy.Player_PageLoc)) (R1.ram.get! (I sy.Player_X_Position)) (R1.ram.get! (I sy.SprObject_X_MoveForce)) + 2048 < 0x1000000 := by
    rw [s1, s2, s3]
    show posP sy (trace M i n₀) + 2048 < 0x1000000
    rw [posP_congr h.before]
    exact h.far.2
  rw [posP_eq, posP_eq] at q2
  have e := pix_of_xs hd q2 hfar hok
  have ep : peek R1 sy.Player_PageLoc = peek (trace M i n₀) sy.Player_PageLoc := s2
  have ex : peek R1 sy.Player_X_Position = peek (trace M i n₀) sy.Player_X_Position := s1
  unfold EdgeStep.pixel16
  rw [e, ep, ex]
  rfl

/-! ## The condition at the arrival -/

/-- **NearA(R)**, at the first arrival at the player's routine `R`: when the side collision's timer and the scroll lock are 0 and his place on the screen is at
least the scroll's threshold, he is at least 2 px right of the screen's left edge -/
def NearA (sy : Syms) (P : ScrollRule.Places) (R : Machine) : Prop :=
  R.ram.get! P.sideB = 0 → R.ram.get! P.lockB = 0 → P.thr1 ≤ R.ram.get! P.pfs → ScrollRule.left16 P R + 2 ≤ EdgeStep.pixel16 sy R

/-- **`NearA` at the arrival gives `NearX` at the scroll handler**: the scroll's three bytes and the edge are those of the arrival (`hkeep`, `PlaceKeep.keep_place`),
the platforms' force is 0 there (`hp0`), and the pixel is that of the arrival plus the byte the move stores (`hmove`, `move_xs`) -/
theorem nearX_of_a {m0 R Q : Machine} (ha : NearA sy (ScrollRule.places sy m0) R)
    (hkeep : ∀ x ∈ PlaceKeep.placeI sy m0, Q.ram.get! x = R.ram.get! x) (hp0 : Q.ram.get! (ScrollRule.places sy m0).plat = 0)
    (hmove : ScrollRule.xOK (Q.ram.get! (ScrollRule.places sy m0).xs) = true →
      EdgeStep.pixel16 sy Q = EdgeStep.pixel16 sy R + (Q.ram.get! (ScrollRule.places sy m0).xs).toNat) :
    EdgeStep.NearX sy (ScrollRule.places sy m0) Q := by
  intro hal
  obtain ⟨hl, hpf, hs, hx⟩ := hal
  have k1 : Q.ram.get! (ScrollRule.places sy m0).sideB = R.ram.get! (ScrollRule.places sy m0).sideB := hkeep _ (by simp [PlaceKeep.placeI])
  have k2 : Q.ram.get! (ScrollRule.places sy m0).pfs = R.ram.get! (ScrollRule.places sy m0).pfs := hkeep _ (by simp [PlaceKeep.placeI])
  have k3 : Q.ram.get! (ScrollRule.places sy m0).lockB = R.ram.get! (ScrollRule.places sy m0).lockB := hkeep _ (by simp [PlaceKeep.placeI])
  have k4 : Q.ram.get! (ScrollRule.places sy m0).lx = R.ram.get! (ScrollRule.places sy m0).lx := hkeep _ (by simp [PlaceKeep.placeI])
  have k5 : Q.ram.get! (ScrollRule.places sy m0).lp = R.ram.get! (ScrollRule.places sy m0).lp := hkeep _ (by simp [PlaceKeep.placeI])
  have hxs : ScrollRule.amountOf (ScrollRule.places sy m0) Q = Q.ram.get! (ScrollRule.places sy m0).xs := by
    unfold ScrollRule.amountOf
    rw [hp0]
    exact UInt8.add_zero _
  rw [hxs] at hx
  have hA := ha (by rw [← k1]; exact hs) (by rw [← k3]; exact hl) (by rw [← k2]; exact hpf)
  have hL : ScrollRule.left16 (ScrollRule.places sy m0) Q = ScrollRule.left16 (ScrollRule.places sy m0) R := by
    unfold ScrollRule.left16
    rw [k4, k5]
  rw [hL, hmove hx]
  omega

end Smbrta.MoveScroll
