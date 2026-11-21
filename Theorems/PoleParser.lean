import Theorems.PoleTileCtl

/-!
# The area parser against the screen's left edge: the invariant, its steps, and its value at control

`PoleJoin.Run.tilesCol` says: at a read of the side check two or more pages before the pole's, in the pole's column of the block buffers, the byte read is not
one of the pole's tiles. The block buffers hold 32 columns; the pole's column there is also the column 512 px before the pole. The area parser draws the columns
ahead of the screen. While it has not drawn the pole's column, that place holds the column 512 px before it. The parser draws a column a fixed distance ahead
of the screen's left edge. So the pole's tiles come into the block buffers only when the edge is near the pole, and then he cannot be two pages before it.

This file has the first part of that argument: the parser's bytes, found from the code (`places`), the invariant on one state (`Inv`), that the parser's steps of
one frame keep it (`Rule`, `inv_rule`), what it says about the edge when the parser has come to a column (`edge_of_col`), and that it holds at control above ground
(`inv₀`, from the rows of the change out of the side pipe, as `PoleTileCtl.watch₀`).

The invariant, with col the parser's column (16 px each, with its page), N the parser's tasks left, p(N) = [N ≥ 1] + [N ≥ 5] the column steps still to come in
those tasks, S the scroll counter of 32 px and edge the screen's left edge in px:

  N ≤ 8 ∧ 16·col + 16·p(N) + S = edge + L.

`L` is a parameter: the check at control gives its value. What is not proved here: that each frame in control moves these bytes by `Rule` (the scroll's part, the
parser's part; measured by `pole-keep parser`), and that he is not far left of the edge at the read. So `tilesCol` stays.

The code of one frame, as the rule follows it (UpdScrollVar, the parser's task routine, the column's step):
* the scroll handler adds the scroll's amount Y to S and to the edge;
* if the screen buffers' control byte is 6, nothing else;
* if N = 0 and 32 ≤ S < 160 (the code's `CMP`, `BMI`), S − 32, and N becomes 8;
* if N ≠ 0 then, the task N − 1 runs and N falls by 1; the tasks 0 and 4 step the column by one.

There is no game data in this file. Page: `1-1/f-6-17-8-PoleParser.md`.
-/

namespace Smbrta.PoleParser

open TaintRun (AS Sim Env)
open SideChangeEnd (Row Ctx InvL knowsAd mOf)

/-! ## The places, from the code -/

/-- the parser's bytes and the screen's left edge, as addresses -/
structure Places where
  /-- the screen buffers' control byte -/
  ctrl : UInt16
  /-- the parser's tasks left -/
  task : UInt16
  /-- the scroll counter of 32 px -/
  s32 : UInt16
  /-- the parser's column in its page, and its page -/
  col : UInt16
  page : UInt16
  /-- the screen's left edge: its pixel and its page -/
  ex : UInt16
  ep : UInt16
  deriving Inhabited

/-- a word of the program, its low byte first -/
def romW (m0 : Machine) (a : UInt16) : UInt16 := (romByte m0 a).toUInt16 ||| ((romByte m0 (a + 1)).toUInt16 <<< 8)

/-- **The places, from the program**: in `UpdScrollVar`, the operands of its first load (the control byte), of its load of the task count and of its load of the
scroll counter, and its call of the task handler; in the task handler its call of the task routine; that routine's first entry is the column's step, whose first
`INC` is the column and whose second `INC` is the page. The edge is that of the clamp (`ScreenClamp.places`). -/
def places (sy : Syms) (m0 : Machine) : Places :=
  let u := sy.UpdScrollVar
  let h := romW m0 (u + 0x21)
  let t := romW m0 (h + 0x0D)
  let i := romW m0 (t + 3)
  { ctrl := romW m0 (u + 1), task := romW m0 (u + 8), s32 := romW m0 (u + 13), col := romW m0 (i + 1), page := romW m0 (i + 0x0E)
    ex := (ScreenClamp.places sy m0).edgeX, ep := (ScreenClamp.places sy m0).edgeP }

/-! ## The invariant on one state -/

/-- the column steps still to come in the tasks left: the tasks 4 and 0 step the column -/
def pend (n : Nat) : Nat := (if 1 ≤ n then 1 else 0) + (if 5 ≤ n then 1 else 0)

/-- the parser's column with its page, 16 columns a page -/
def colOf (P : Places) (m : Machine) : Nat := (peek m P.page).toNat * 16 + (peek m P.col).toNat

/-- the screen's left edge in px -/
def edgeOf (P : Places) (m : Machine) : Nat := (peek m P.ep).toNat * 256 + (peek m P.ex).toNat

/-- the parser's sum: `16·col + 16·p(N) + S` -/
def sumOf (P : Places) (m : Machine) : Nat := 16 * colOf P m + 16 * pend (peek m P.task).toNat + (peek m P.s32).toNat

/-- **The invariant**: at most 8 tasks left, and the parser's sum is `L` px past the edge -/
def Inv (P : Places) (L : Nat) (m : Machine) : Prop := (peek m P.task).toNat ≤ 8 ∧ sumOf P m = edgeOf P m + L

/-- **The parser's column and the edge**: with the invariant, the parser's column is at most `L` px past the edge -/
theorem col_le {P : Places} {L : Nat} {m : Machine} (h : Inv P L m) : 16 * colOf P m ≤ edgeOf P m + L := by
  have := h.2
  unfold sumOf at this
  omega

/-- **When the parser has come to a column `c`, the edge is at least `16·c − L`** -/
theorem edge_of_col {P : Places} {L c : Nat} {m : Machine} (h : Inv P L m) (hc : c ≤ colOf P m) : 16 * c ≤ edgeOf P m + L := by
  have := col_le h
  omega

/-! ## The steps of one frame -/

/-- the values that the rule speaks of: the tasks left, the scroll counter, the column, the edge -/
structure Vals where
  n : Nat
  s : Nat
  col : Nat
  edge : Nat

/-- the values of a machine -/
def valsOf (P : Places) (m : Machine) : Vals := ⟨(peek m P.task).toNat, (peek m P.s32).toNat, colOf P m, edgeOf P m⟩

/-- the invariant on values -/
def InvV (L : Nat) (v : Vals) : Prop := v.n ≤ 8 ∧ 16 * v.col + 16 * pend v.n + v.s = v.edge + L

theorem invV_iff {P : Places} {L : Nat} {m : Machine} : Inv P L m ↔ InvV L (valsOf P m) := Iff.rfl

/-- **The scroll**: the scroll handler adds `Y` to the counter and to the edge (the counter does not pass 255) -/
def Scroll (a b : Vals) : Prop := ∃ y, b.n = a.n ∧ b.col = a.col ∧ b.s = a.s + y ∧ b.edge = a.edge + y

/-- **The parser's part of one frame**, from the counter and the tasks left at `UpdScrollVar` (`ctl6`: the control byte is 6 there) -/
def Parse (ctl6 : Bool) (a b : Vals) : Prop :=
  b.edge = a.edge ∧
  if ctl6 then b.n = a.n ∧ b.s = a.s ∧ b.col = a.col
  else if a.n = 0 then
    (32 ≤ a.s ∧ a.s < 160 ∧ b.n = 7 ∧ b.s = a.s - 32 ∧ b.col = a.col) ∨ ((a.s < 32 ∨ 160 ≤ a.s) ∧ b.n = a.n ∧ b.s = a.s ∧ b.col = a.col)
  else b.n = a.n - 1 ∧ b.s = a.s ∧ b.col = (if a.n = 1 ∨ a.n = 5 then a.col + 1 else a.col)

/-- **The rule of one frame**: the scroll, then the parser's part -/
def Rule (a b : Vals) : Prop := ∃ ctl6 c, Scroll a c ∧ Parse ctl6 c b

theorem pend_cases (n : Nat) (h : n ≤ 8) :
    (n = 0 ∧ pend n = 0) ∨ (1 ≤ n ∧ n ≤ 4 ∧ pend n = 1) ∨ (5 ≤ n ∧ pend n = 2) := by
  unfold pend
  by_cases h1 : 1 ≤ n <;> by_cases h5 : 5 ≤ n <;> simp [h1, h5] <;> omega

/-- the scroll keeps the invariant -/
theorem inv_scroll {L : Nat} {a b : Vals} (h : InvV L a) (hs : Scroll a b) : InvV L b := by
  obtain ⟨y, e1, e2, e3, e4⟩ := hs
  obtain ⟨h1, h2⟩ := h
  refine ⟨by omega, ?_⟩
  rw [e1, e2, e3, e4]
  omega

/-- the parser's part keeps the invariant -/
theorem inv_parse {L : Nat} {ctl6 : Bool} {a b : Vals} (h : InvV L a) (hp : Parse ctl6 a b) : InvV L b := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨he, hp⟩ := hp
  cases ctl6 with
  | true =>
    simp only [if_true] at hp
    obtain ⟨e1, e2, e3⟩ := hp
    exact ⟨by omega, by rw [e1, e2, e3, he]; exact h2⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at hp
    by_cases hn : a.n = 0
    · rw [if_pos hn] at hp
      rcases hp with ⟨s1, _, e1, e2, e3⟩ | ⟨_, e1, e2, e3⟩
      · refine ⟨by omega, ?_⟩
        rw [e1, e2, e3, he]
        have hp0 : pend a.n = 0 := by rw [hn]; rfl
        have hp7 : pend 7 = 2 := rfl
        rw [hp0] at h2
        rw [hp7]
        omega
      · exact ⟨by omega, by rw [e1, e2, e3, he]; exact h2⟩
    · rw [if_neg hn] at hp
      obtain ⟨e1, e2, e3⟩ := hp
      refine ⟨by omega, ?_⟩
      rw [e1, e2, e3, he]
      rcases pend_cases a.n h1 with ⟨h0, _⟩ | ⟨g1, g4, g⟩ | ⟨g5, g⟩
      · exact absurd h0 hn
      · by_cases h1' : a.n = 1
        · rw [if_pos (Or.inl h1')]
          have : pend (a.n - 1) = 0 := by rw [h1']; rfl
          rw [this]
          omega
        · rw [if_neg (by omega)]
          rcases pend_cases (a.n - 1) (by omega) with ⟨_, _⟩ | ⟨_, _, g'⟩ | ⟨_, _⟩
          · omega
          · omega
          · omega
      · by_cases h5 : a.n = 5
        · rw [if_pos (Or.inr h5)]
          have : pend (a.n - 1) = 1 := by rw [h5]; rfl
          rw [this]
          omega
        · rw [if_neg (by omega)]
          rcases pend_cases (a.n - 1) (by omega) with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, g'⟩
          · omega
          · omega
          · omega

/-- **The rule of one frame keeps the invariant** -/
theorem inv_rule {L : Nat} {a b : Vals} (h : InvV L a) (hr : Rule a b) : InvV L b := by
  obtain ⟨ctl6, c, hs, hp⟩ := hr
  exact inv_parse (inv_scroll h hs) hp

/-- **Frames by the rule keep the invariant**: if each frame `j + 1` from the values `v j` follows the rule to `v (j + 1)`, the invariant at `v 0` holds at every `v n` -/
theorem inv_frames {L : Nat} {v : Nat → Vals} (h0 : InvV L (v 0)) (hr : ∀ j, Rule (v j) (v (j + 1))) : ∀ n, InvV L (v n)
  | 0 => h0
  | n + 1 => inv_rule (inv_frames h0 hr n) (hr n)

/-- **The parser's column does not fall**: by the rule -/
theorem col_rule {a b : Vals} (hr : Rule a b) : a.col ≤ b.col := by
  obtain ⟨ctl6, c, ⟨y, _, e2, _, _⟩, ⟨_, hp⟩⟩ := hr
  cases ctl6 with
  | true => simp only [if_true] at hp; omega
  | false =>
    simp only [Bool.false_eq_true, if_false] at hp
    by_cases hn : c.n = 0
    · rw [if_pos hn] at hp; rcases hp with ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ <;> omega
    · rw [if_neg hn] at hp
      obtain ⟨_, _, e⟩ := hp
      split at e <;> omega

/-- **The edge does not fall**: by the rule -/
theorem edge_rule {a b : Vals} (hr : Rule a b) : a.edge ≤ b.edge := by
  obtain ⟨_, c, ⟨y, _, _, _, e4⟩, ⟨he, _⟩⟩ := hr
  omega

/-! ## At control, from the rows of the change -/

/-- the bytes of the invariant -/
def bytesOf (P : Places) : List UInt16 := [P.task, P.s32, P.col, P.page, P.ex, P.ep]

/-- a state of a row: it knows the bytes of control, and if it has control, it knows the bytes of the invariant and they meet it -/
def rowInv (sy : Syms) (P : Places) (L : Nat) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || ((bytesOf P).all (knowsAd S) && decide ((peek (mOf S) P.task).toNat ≤ 8) && sumOf P (mOf S) == edgeOf P (mOf S) + L))

/-- **No pole's tile in the block buffers** (one state) -/
def NoTiles (Q : PoleEntryRule.Spots) (m : Machine) : Prop := ∀ i, Q.bufLo ≤ i → i < Q.bufLo + Q.bufBytes → ¬ PoleTiles.Tile Q (m.ram.get! i)

/-- a state of a row: it knows the bytes of control, and if it has control, it knows every byte of the block buffers and none is a pole's tile -/
def rowNo (sy : Syms) (Q : PoleEntryRule.Spots) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || (List.range Q.bufBytes).all fun k => (S.getK (Q.bufLo + k)).isK && !PoleTiles.tileB Q (S.getK (Q.bufLo + k)).v)

/-- every state of the rows -/
def rowsInv (sy : Syms) (P : Places) (L : Nat) (l : List Row) : Bool := l.all fun r => r.R.all (rowInv sy P L)

/-- every state of the rows -/
def rowsNo (sy : Syms) (Q : PoleEntryRule.Spots) (l : List Row) : Bool := l.all fun r => r.R.all (rowNo sy Q)

/-- **The check on the ROM**: in every state with control of the rows of the change out of the side pipe the invariant holds with `L`, and the block buffers hold no
pole's tile -/
def invCheckK (sy : Syms) (m0 : Machine) (L : Nat) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  let l := (SideChangeSound.rowsOf sy nm nx e A B R).map (·.row)
  decide ((PoleFrame.spotsF sy m0).bufLo + (PoleFrame.spotsF sy m0).bufBytes ≤ 2048) && rowsInv sy (places sy m0) L l && rowsNo sy (PoleFrame.spotsF sy m0) l

variable {sy : Syms}

/-- a known byte of a covered machine is the state's -/
theorem peek_of_known {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) {a : UInt16} (hk : knowsAd S a = true) :
    peek m a = peek (mOf S) a := by
  have hi : (a &&& 0x7FF).toNat < 2048 := by
    have : (a &&& 0x7FF).toNat ≤ 0x7FF := by
      have := UInt16.and_le_right (a := a) (b := 0x7FF)
      exact UInt16.le_iff_toNat_le.1 this
    omega
  have e := PipeEntryRule.known_eq hk (hs.ram _ hi)
  show m.ram.get! (a &&& 0x7FF).toNat = S.ram.get! (a &&& 0x7FF).toNat
  rw [e]
  rfl

theorem inv_of_state {E : Env} {F : Nat × UInt8} {P : Places} {L : Nat} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowInv sy P L S = true)
    (h : controllable sy m = true) : Inv P L m := by
  simp only [rowInv, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨⟨h1, h2⟩, h3⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · have hb := List.all_eq_true.1 h1
    simp only [bytesOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hb
    have e1 := peek_of_known hs k1
    have e2 := peek_of_known hs k2
    have e3 := peek_of_known hs k3
    have e4 := peek_of_known hs k4
    have e5 := peek_of_known hs k5
    have e6 := peek_of_known hs k6
    simp only [decide_eq_true_eq] at h2
    simp only [beq_iff_eq] at h3
    refine ⟨by rw [e1]; exact h2, ?_⟩
    unfold sumOf colOf edgeOf at h3 ⊢
    rw [e1, e2, e3, e4, e5, e6]
    exact h3

theorem no_of_state {E : Env} {F : Nat × UInt8} {Q : PoleEntryRule.Spots} {S : AS} {m : Machine} (hb : Q.bufLo + Q.bufBytes ≤ 2048) (hs : Sim E F S m)
    (hr : rowNo sy Q S = true) (h : controllable sy m = true) : NoTiles Q m := by
  simp only [rowNo, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | h1
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · intro i h2 h3 ht
    have hi := List.all_eq_true.1 h1 (i - Q.bufLo) (List.mem_range.2 (by omega))
    rw [show Q.bufLo + (i - Q.bufLo) = i by omega] at hi
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
    obtain ⟨hk1, hc⟩ := hi
    have e := PipeEntryRule.known_eq hk1 (hs.ram i (by omega))
    rw [e] at ht
    rw [PoleTiles.tileB_spec.2 ht] at hc
    cases hc

theorem no_of_invL {C : Ctx} {Q : PoleEntryRule.Spots} (hb : Q.bufLo + Q.bufBytes ≤ 2048) :
    ∀ {l : List Row}, rowsNo sy Q l = true → ∀ {m : Machine}, InvL C l m → controllable sy m = true → NoTiles Q m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsNo, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact no_of_state hb hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact no_of_invL hb hl.2 h hc

theorem inv_of_invL {C : Ctx} {P : Places} {L : Nat} :
    ∀ {l : List Row}, rowsInv sy P L l = true → ∀ {m : Machine}, InvL C l m → controllable sy m = true → Inv P L m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsInv, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact inv_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact inv_of_invL hl.2 h hc

section
variable {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine} {m0 : Machine} {L : Nat}

/-- **The machine at control has the invariant**, on a real run of the change, from the rows of `SideChangeSound` (the run of `SidePause`) -/
theorem EndRunQ.inv (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : invCheckK sy m0 L nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    Inv (places sy m0) L (R'.seq R'.b) ∧ NoTiles (PoleFrame.spotsF sy m0) (R'.seq R'.b) := by
  simp only [invCheckK, Bool.and_eq_true, decide_eq_true_eq] at hk
  have hI := SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)
  exact ⟨inv_of_invL hk.1.2 hI R'.atCtl, no_of_invL hk.1.1 hk.2 hI R'.atCtl⟩

end

section
open Route

variable {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : PipeTransitionAll.Names} {d₁ : PipeChangeEnd.Data}
  {nm₂ nx₂ nmS : PipeTransitionAll.Names} {fc : FlagRule.Ctx} {tc : TitleStart.Ctx} {L : Nat}

/-- **The invariant at control above ground, and no pole's tile in the block buffers**, on the real machines: from the last rows of the change, under the same
conditions as `PoleTileCtl.watch₀`. `hm` is the check on the ROM. -/
theorem inv₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : invCheckK sy m0 L nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    Inv (places sy m0) L (R.pole.seq 0) ∧ NoTiles (PoleFrame.spotsF sy m0) (R.pole.seq 0) := by
  rw [R.atCtl]
  exact EndRunQ.inv hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

end

/-! ## What `tilesCol` would follow from

At a read of the side check two or more pages before the pole's, in the pole's column of the block buffers (the premises of `PoleTileFar.TileCol`), the byte read is
not a pole's tile, if at that state:
* (`hslot`) a pole's tile read in the pole's column means that the parser has come to the pole's column;
* (`hcol`) the parser's column is at most `L` px past the edge (`col_le`, from `Inv`);
* (`hnear`) he is at most `δ` px left of the edge;
* (`hread`) the read is, in the 32 columns of the block buffers (the column's number mod 32), at the column of his pixel plus an adder `a < A`;
with `A ≤ 16` and `L + δ ≤ 496`. Measured on real frames: `L = 384`, `δ = 0`, the adders below 16 (`pole-keep parser`). None of the four is proved here for the
touch's frame: `inv₀` gives `Inv` at control only. -/

/-- the pole's column with its page, 16 columns a page -/
def colPole (Q : PoleEntryRule.Spots) : Nat := 16 * Q.pg + Q.col.toNat

/-- his pixel with its page -/
def pixOf (Q : PoleEntryRule.Spots) (m : Machine) : Nat := (m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat

/-- **`TileCol` from the four facts**: pure arithmetic -/
theorem tileCol_of {Q : PoleEntryRule.Spots} {P : Places} {L δ A : Nat} {m : Machine} (hA : A ≤ 16) (hL : L + δ ≤ 496) (hc16 : Q.col.toNat < 16)
    (hslot : (m.a = Q.ball ∨ m.a = Q.shaft) → PoleEntryRule.onCol Q (PoleFrame.readAt Q m) = true → colPole Q ≤ colOf P m)
    (hcol : 16 * colOf P m ≤ edgeOf P m + L)
    (hnear : edgeOf P m ≤ pixOf Q m + δ)
    (hread : PoleEntryRule.onCol Q (PoleFrame.readAt Q m) = true → ∃ a, a < A ∧ (pixOf Q m + a) / 16 % 32 = colPole Q % 32) :
    PoleTileFar.TileCol Q m := by
  intro _ _ hpg hon ht
  have h1 := hslot ht hon
  obtain ⟨a, ha, hm⟩ := hread hon
  have hx : (m.ram.get! Q.xI).toNat < 256 := (m.ram.get! Q.xI).toNat_lt
  unfold pixOf at hm hnear
  unfold colPole at h1 hm
  -- his pixel plus the adder is in a column before the pole's page, and at the pole's column mod 32: so 32 columns or more before the pole's
  have hlt : (((m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat) + a) / 16 + 32 ≤ 16 * Q.pg + Q.col.toNat := by
    omega
  omega

/-! ## The first piece of a frame: from its start to the scroll handler the parser's bytes are kept

The walks of `EdgeStep` (`qCheck`, `keep_q`, `keep_noCut`) with the parser's four bytes in place of the edge's two (`pI`): the walk of `CtrlKeep` with the byte
followed, and from the cut the first walk with the byte followed to the scroll handler. The guard of the walks protects the followed byte (`AfterKeep.guardH`):
here that is the hypothesis `hH`, a condition on each instruction (no store through an index or a pointer writes the byte). It is not a field: nothing in the route
uses this yet. Measured on real frames: no such store writes a parser's byte (`pole-keep parser`). -/

/-- the parser's four bytes, as indices of RAM: the tasks left, the scroll counter, the column, the page -/
def pI (sy : Syms) (m0 : Machine) : List Nat := [P.task, P.s32, P.col, P.page].map fun a => (a &&& 0x7FF).toNat
where P := places sy m0

/-- **The check of the parser's bytes up to the scroll handler**: `EdgeStep.qCheck` for the bytes of `pI` -/
def qCheckP (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
  (pI sy m0).all fun b =>
    let C1 := EdgeStep.qbCfg sy m0 v b cuts
    CtrlKeep.ctrlCheck1 (EdgeStep.cfgQb sy m0 v q b C1) && C1.t.all (EdgeStep.walkQR C1 (FrameKeep.ctlI sy) sy.PlayerSubs EdgeStep.atRk FrameKeep.fuelK)

section Frames
open PipeEntryRule (trace)
open PipeTransition (frame)
open EdgeStep (cfgQb qbCfg walkQR atRk qR_run watched_at)
open AfterKeep (guardH)
open FrameModel (Good Rom)

variable {m0 : Machine}

/-- **A frame in control that does not come to the player's routine keeps the parser's bytes** (as `EdgeStep.keep_noCut`) -/
theorem keep_noCutP {v : UInt8} (hq : qCheckP sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) : ∀ x ∈ pI sy m0, (frame m i).ram.get! x = m.ram.get! x := by
  simp only [qCheckP, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hq
  obtain ⟨_, hb⟩ := hq
  intro x hx
  obtain ⟨h1, _⟩ := hb x hx
  generalize CtrlKeep.cutTable sy m0 true = q at h1
  rcases CtrlKeep.cut_or_end (C := cfgQb sy m0 v q x _) h1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hcl with ⟨k, h2, h3, _, _⟩ | ⟨B, hB, hs⟩
  · exact absurd h2 (hn k h3)
  · simp only [CtrlKeep.endR, Bool.and_eq_true, Bool.not_eq_true'] at hB
    have e := hs.rkv hB.1.1
    rw [if_neg (by simp [hB.1.2])] at e
    exact e

/-- **A frame in control keeps the parser's bytes from its start to the scroll handler** (as `EdgeStep.keep_q`, with the bytes of `pI`): the frame starts in the
idle loop in control, each instruction meets `CleanK` of `FrameKeep.guardF` and of the walk's guard for each byte (`hH`), and writes neither the routine, nor the
mode, nor the task by its address; the area's type is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time,
and to the scroll handler at `k`, the first time after `n₀`. Then at `k` the machine is `Good` and has the parser's bytes of the frame's start. -/
theorem keep_qP (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pI sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    {k : Nat} (hk : n₀ ≤ k) (hpc : (trace m i k).pc = sy.PlayerSubs) (hb : ∀ j, n₀ < j → j < k → (trace m i j).pc ≠ sy.PlayerSubs) :
    ∀ x ∈ pI sy m0, Good (Rom.of m0) (trace m i k) ∧ (trace m i k).ram.get! x = m.ram.get! x := by
  simp only [qCheckP, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hq
  obtain ⟨⟨hne1, _⟩, hbq⟩ := hq
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  intro x hxI
  obtain ⟨h1, ht⟩ := hbq x hxI
  generalize CtrlKeep.cutTable sy m0 true = q at h1 ht
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at h1 ht
  rcases CtrlKeep.cut_or_end2 (C := cfgQb sy m0 v q x (qbCfg sy m0 v x cuts)) h1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k₀, a1, a2, _, a4, a5, B, hB1, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    simp only [CtrlKeep.atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB1
    have hcut := hs.rkv hB1.1.1.1.1.1.1
    rw [if_neg (by simp [hB1.1.1.1.1.1.2])] at hcut
    have hV := watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hsR := AfterKeep.sim_rkOn (b := x) hsA
    have hw : walkQR (qbCfg sy m0 v x cuts) (FrameKeep.ctlI sy) sy.PlayerSubs atRk FrameKeep.fuelK
        (AfterKeep.rkOn (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B)) = true := hB2
    obtain ⟨k₁, hk1, hq1, _, _, hbt, B₁, hat, hs₁⟩ := qR_run (C := qbCfg sy m0 v x cuts) ht rfl rfl hw hsR a2 a5 (hH x hxI) hx'
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [a1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exact absurd hq1 (hb k₁ hk1 h)
    subst hkk
    simp only [atRk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hat
    obtain ⟨⟨⟨hrk, hsp⟩, hnmi⟩, hctl⟩ := hat
    refine ⟨⟨hs₁.prg, hs₁.mask, by rw [hs₁.nmi]; exact hnmi, hs₁.halted, hs₁.trk, hs₁.size, CtrlKeep.nmi_off_of (by rw [hctl]; rfl) hs₁.ppuCtrl⟩, ?_⟩
    have e := hs₁.rkv hrk
    rw [if_neg (by simp [hsp])] at e
    exact e.trans hcut
  · exact absurd harr (hno n₀ hf0)

end Frames

/-! ## The second piece: from the scroll handler's call to `UpdScrollVar`

Three walks after those of `EdgeStep.rCheck` (the walk of the pause bit up to the cut, the first walk of `AfterKeep` to the scroll handler, the middle walk to the
instruction after its call `R`):
* for the tasks left, the column and the page, a middle walk with the byte followed, from the scroll handler to `R` (`keep_mP`): the scroll handler keeps them;
* for each of the four bytes, a walk with the byte followed from `R` to the first `UpdScrollVar` (`keep_uP`). A path stops at a store to his position by its address
  outside the push and the clamp (`EdgeStep.cutPos`): the field `posW` of the frames above ground excludes it. That cut stops the loop back of a castle, which moves
  the parser's page back.
So at `UpdScrollVar` the tasks left, the column and the page are those of the frame's start, and the scroll counter is that of `R`. -/

open TaintRun in
/-- **A walk to `Q` with a followed byte and a cut**: `EdgeStep.walkQR`, and a path stops at an instruction where `cutP` holds -/
def walkQP (C : FrameKeep.CfgK) (l : List Nat) (cutP : UInt16 → Bool) (Q : UInt16) (atQ : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || cutP A.pc || (FrameKeep.preK C.S C.G A).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => B.k == A.k && (if B.pc == Q then atQ B else (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkQP C l cutP Q atQ n B)

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun

variable {E : Env} {F : Nat × UInt8} {C : FrameKeep.CfgK} {l : List Nat} {cutP : UInt16 → Bool} {Q : UInt16} {Fu : Nat} {atQ' : AS → Bool}

/-- `A` covers `m`, and the walk with the cut succeeds from `A` -/
def LiveQP (C : FrameKeep.CfgK) (l : List Nat) (cutP : UInt16 → Bool) (Q : UInt16) (atQ' : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkQP C l cutP Q atQ' n A = true

theorem cover_liveQP (ht : C.t.all (walkQP C l cutP Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveQP C l cutP Q atQ' F D m := by
  unfold FrameKeep.coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = PipeWrites.knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, sim_le hle hs, Fu, hall⟩
  · cases h2

theorem live_stepQP (ht : C.t.all (walkQP C l cutP Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveQP C l cutP Q atQ' F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false)
    (hp : cutP m.pc = false) :
    (∃ A', LiveQP C l cutP Q atQ' F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc = Q ∧ ∃ B, atQ' B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkQP] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    have hp' : cutP A.pc = false := by rw [← hs.pc]; exact hp
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    simp only [walkQP, hx', hp', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    obtain ⟨r, hr, hB⟩ := AfterKeep.s_kstepL hops hd hh hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      simp only [Bool.and_eq_true, beq_iff_eq] at hw3
      obtain ⟨hkB, hw4⟩ := hw3
      rcases h2 with ⟨_, k2, k3⟩ | ⟨k1, _⟩
      · by_cases hq : B.pc = Q
        · rw [if_pos (by simp [hq])] at hw4
          exact Or.inr ⟨k2, k3, by rw [h1.pc]; exact hq, B, hw4, h1⟩
        · rw [if_neg (by simp [hq])] at hw4
          have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw4
          rcases hw4 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD⟩ := cover_liveQP ht hkl h1 h3
            exact Or.inl ⟨D, hD, k2, k3, hq'⟩
          · exact Or.inl ⟨B, ⟨h1, n, h3⟩, k2, k3, hq'⟩
      · exfalso
        rw [hk1] at k1
        omega

/-- **The walk with the cut: to `Q`.** As `EdgeStep.qR_run`, when no instruction of the frame from `k` on is at a place of `cutP`. -/
theorem qP_run (ht : C.t.all (walkQP C l cutP Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkQP C l cutP Q atQ' Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame)
    (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → cutP (trace m i j).pc = false) :
    ∃ k₁, k < k₁ ∧ (trace m i k₁).pc = Q ∧ (trace m i k₁).frame = m.frame ∧ m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧ (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧
      ∃ B, atQ' B = true ∧ Sim C.E F B (trace m i k₁) := by
  have key : ∀ d, (∃ A, LiveQP C l cutP Q atQ' F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
        ∀ j, k < j → j ≤ k + d → (trace m i j).pc ≠ Q) ∨
      (∃ k₁, k < k₁ ∧ k₁ ≤ k + d ∧ (trace m i k₁).pc = Q ∧ (trace m i k₁).frame = m.frame ∧ m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧
        (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧ ∃ B, atQ' B = true ∧ Sim C.E F B (trace m i k₁)) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd, fun j h1 h2 => absurd h2 (by omega)⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | h
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepQP ht hkl hops h1 (hcl (k + d)) (hx (k + d)) (hp (k + d) (by omega) h2) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, a2, a3, B, b1, b2⟩
        · rw [← e] at a1 a2 a3 a4
          refine Or.inl ⟨A', a1, a2.trans h2, by omega, fun j hj1 hj2 => ?_⟩
          by_cases h5 : j ≤ k + d
          · exact h4 j hj1 h5
          · rw [show j = k + (d + 1) by omega]
            exact a4
        · rw [← e] at a1 a2 a3 b2
          exact Or.inr ⟨k + (d + 1), by omega, Nat.le_refl _, a3, a1.trans h2, by omega, fun j hj1 hj2 => h4 j hj1 (by omega), B, b1, b2⟩
      · obtain ⟨k₁, h1, h2, h3⟩ := h
        exact Or.inr ⟨k₁, h1, by omega, h3⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3, _⟩ | ⟨k₁, h1, _, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · exact ⟨k₁, h1, h3⟩

end

/-- the parser's three bytes that the scroll handler does not write: the tasks left, the column, the page -/
def pK (sy : Syms) (m0 : Machine) : List Nat := [P.task, P.col, P.page].map fun a => (a &&& 0x7FF).toNat
where P := places sy m0

open AfterKeep (walkQ1 tableBut rkOn guardH) in
/-- **The middle walk with the byte `b` followed**, from the states at the scroll handler `starts` to the instruction after its call: its table -/
def qmCfg (sy : Syms) (m0 : Machine) (v : UInt8) (b : Nat) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardH sy m0 b
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let W := CtrlKeep.watchA sy m0 v
  let key := PrevKeep.keyP S G W
  let P := PrevKeep.searchFrom sy m0 E (b :: CtrlKeep.spareI sy m0) [] W (FrameKeep.ctlI sy) (fun A => A.pc == EdgeStep.rPc sy) (starts.map rkOn)
  let q := tableBut key (EdgeStep.rPc sy) P.X
  { E, ops := (TaintRun.aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

open AfterKeep (tableBut rkOn guardH) in
/-- **The walk with the byte `b` followed** from the states after the scroll handler's call `starts` to `UpdScrollVar`: its table -/
def quCfg (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardH sy m0 b
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let P := PrevKeep.searchFrom sy m0 E (b :: CtrlKeep.spareI sy m0) [] [] (FrameKeep.ctlI sy) (fun A => A.pc == sy.UpdScrollVar) (starts.map rkOn)
  let q := tableBut key sy.UpdScrollVar P.X
  { E, ops := (TaintRun.aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- at the end of a walk with a followed byte: the byte still followed and not decremented -/
def atRkU (B : TaintRun.AS) : Bool := B.rk && !B.spent

/-- the bytes followed to `UpdScrollVar`: the parser's four and the edge's two -/
def pU (sy : Syms) (m0 : Machine) : List Nat := pI sy m0 ++ EdgeStep.eI sy m0

/-- the edge's pixel, the byte of the walk to the frame's end that shows no second arrival after the call -/
def e0 (sy : Syms) (m0 : Machine) : Nat := ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat

/-- what the middle walk asks after the scroll handler's call: for each byte the walk to `UpdScrollVar` succeeds, and the walk of `EdgeStep` to the frame's end -/
def atRU (sy : Syms) (m0 : Machine) (Cu Cn : List FrameKeep.CfgK) (B : TaintRun.AS) : Bool :=
  (Cu.all fun C => walkQP C (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) sy.UpdScrollVar atRkU FrameKeep.fuelK (AfterKeep.rkOn B)) &&
    Cn.all fun C => EdgeStep.walkKP C (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (EdgeStep.rPc sy) FrameKeep.fuelK (AfterKeep.rkOn B)

/-- what the first walk asks at the scroll handler: the middle walk succeeds, and for each of `pK` the middle walk with the byte followed -/
def atSU (sy : Syms) (m0 : Machine) (Cs : FrameKeep.CfgK) (Cm Cu Cn : List FrameKeep.CfgK) (B : TaintRun.AS) : Bool :=
  AfterKeep.walkQ1 Cs (FrameKeep.ctlI sy) (EdgeStep.rPc sy) (atRU sy m0 Cu Cn) FrameKeep.fuelK B &&
    Cm.all fun C => EdgeStep.walkQR C (FrameKeep.ctlI sy) (EdgeStep.rPc sy) atRkU FrameKeep.fuelK (AfterKeep.rkOn B)

/-- the walk of the pause bit up to the cut, then the first walk to the scroll handler, the middle walks, the walks to `UpdScrollVar` -/
def cfgPU (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 Cs : FrameKeep.CfgK) (Cm Cu Cn : List FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atSU sy m0 Cs Cm Cu Cn) FrameKeep.fuelK
      (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check of the parser's bytes after the scroll handler**: as `EdgeStep.rCheck`, with the middle walks for `pK`, the walks to `UpdScrollVar` for `pU`, and the
walk of `EdgeStep` to the frame's end for the edge's pixel (it shows that the frame does not come to the instruction after the call again) -/
def uCheckP (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let Ps := EdgeStep.qsSearch sy m0 v P.stops.toList
  let Cs := EdgeStep.qsCfg sy m0 v Ps
  let Cm := (pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList
  let Cu := (pU sy m0).map fun b => quCfg sy m0 b Ps.stops.toList
  let Cn := [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList]
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop && EdgeStep.rPc sy != sy.EndlessLoop && sy.UpdScrollVar != EdgeStep.rPc sy &&
    CtrlKeep.ctrlCheck1 (cfgPU sy m0 v q C1 Cs Cm Cu Cn) &&
    C1.t.all (AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atSU sy m0 Cs Cm Cu Cn) FrameKeep.fuelK) &&
    Cs.t.all (AfterKeep.walkQ1 Cs (FrameKeep.ctlI sy) (EdgeStep.rPc sy) (atRU sy m0 Cu Cn) FrameKeep.fuelK) &&
    (Cm.all fun C => C.t.all (EdgeStep.walkQR C (FrameKeep.ctlI sy) (EdgeStep.rPc sy) atRkU FrameKeep.fuelK)) &&
    (Cu.all fun C => C.t.all (walkQP C (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) sy.UpdScrollVar atRkU FrameKeep.fuelK)) &&
    (Cn.all fun C => C.t.all (EdgeStep.walkKP C (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (EdgeStep.rPc sy) FrameKeep.fuelK))

section Frames2
open PipeEntryRule (trace)
open PipeTransition (frame)
open AfterKeep (guardH)

variable {m0 : Machine}

theorem pK_sub {x : Nat} (h : x ∈ pK sy m0) : x ∈ pI sy m0 := by
  simp only [pK, pK.P, pI, pI.P, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h <;> simp [h]

/-- two first instructions at `Q` after `k` are the same -/
theorem first_eq {m : Machine} {i : UInt8} {k a b : Nat} {Q : UInt16} (ha : k < a) (hqa : (trace m i a).pc = Q) (hfa : ∀ j, k < j → j < a → (trace m i j).pc ≠ Q)
    (hb : k < b) (hqb : (trace m i b).pc = Q) (hfb : ∀ j, k < j → j < b → (trace m i j).pc ≠ Q) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd hqa (hfb a ha h)
  · exact h
  · exact absurd hqb (hfa b hb h)

theorem pU_sub {x : Nat} (h : x ∈ pI sy m0) : x ∈ pU sy m0 := List.mem_append_left _ h

theorem e0_mem : e0 sy m0 ∈ pU sy m0 := List.mem_append_right _ List.mem_cons_self

/-- **A frame in control keeps the parser's bytes from the scroll handler to `UpdScrollVar`.** The conditions of `keep_qP`, with the walk's guard for the bytes of
`pU` (the parser's four, the edge's two). Then the frame comes to the scroll handler at `kq`, the first time after `n₀`, and to the instruction after its call `R`
at `k₁`, the first time after `kq`; the tasks left, the column and the page at `k₁` are those at `kq`; and if from `kq` on no instruction of the frame is a store to
his position by its address outside the push and the clamp (the field `posW`), the frame comes to `R` after `kq` only at `k₁`, and it comes to `UpdScrollVar` after
`k₁`, and at the first time `k₂` there the six bytes are those at `k₁`. `hc`, `hu` are the checks on the ROM. -/
theorem keep_uP (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hu : uCheckP sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ kq, n₀ < kq ∧ (trace m i kq).pc = sy.PlayerSubs ∧ (trace m i kq).frame = m.frame ∧ (∀ j, n₀ < j → j < kq → (trace m i j).pc ≠ sy.PlayerSubs) ∧
    ∃ k₁, kq < k₁ ∧ (trace m i k₁).pc = EdgeStep.rPc sy ∧ (trace m i k₁).frame = m.frame ∧ (∀ j, kq < j → j < k₁ → (trace m i j).pc ≠ EdgeStep.rPc sy) ∧
      (∀ x ∈ pK sy m0, (trace m i k₁).ram.get! x = (trace m i kq).ram.get! x) ∧
      ((∀ j, kq ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false) →
        (∀ n, kq < n → (trace m i n).pc = EdgeStep.rPc sy → n = k₁) ∧
        ∃ k₂, k₁ < k₂ ∧ (trace m i k₂).pc = sy.UpdScrollVar ∧ (trace m i k₂).frame = m.frame ∧ (∀ j, k₁ < j → j < k₂ → (trace m i j).pc ≠ sy.UpdScrollVar) ∧
          ∀ x ∈ pU sy m0, (trace m i k₂).ram.get! x = (trace m i k₁).ram.get! x) := by
  simp only [uCheckP, Bool.and_eq_true, bne_iff_ne, ne_eq] at hu
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hne3⟩, _⟩, hp1⟩, hp2⟩, hp3⟩, hp4⟩, hp5⟩, hp6⟩ := hu
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3 hp4 hp5 hp6
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3 hp4 hp5 hp6
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3 hp4 hp5 hp6
  generalize EdgeStep.qsSearch sy m0 v P.stops.toList = Ps at hp1 hp2 hp3 hp4 hp5 hp6
  rcases CtrlKeep.cut_or_end2 (C := cfgPU sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (EdgeStep.qsCfg sy m0 v Ps) ((pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList)
      ((pU sy m0).map fun b => quCfg sy m0 b Ps.stops.toList) [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList]) hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := EdgeStep.watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : AfterKeep.walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs
        (atSU sy m0 (EdgeStep.qsCfg sy m0 v Ps) ((pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList) ((pU sy m0).map fun b => quCfg sy m0 b Ps.stops.toList)
          [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList])
        FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨kq, hkq, hqq, hfq, hdq, hbq, Bq, hatq, hsq⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA a2 a5 hcl hx'
    refine ⟨kq, hkq, hqq, hfq, hbq, ?_⟩
    simp only [atSU, Bool.and_eq_true, List.all_eq_true] at hatq
    obtain ⟨hw1, hwm⟩ := hatq
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hb1, B₁, hat1, hs1⟩ :=
      AfterKeep.q1_run (C := EdgeStep.qsCfg sy m0 v Ps) hp3 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw1 hsq hfq hdq hcl hx'
    refine ⟨k₁, hk1, hq1, hf1, hb1, ?_, ?_⟩
    · intro x hxK
      have hmem : qmCfg sy m0 v x P.stops.toList ∈ (pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList := List.mem_map.2 ⟨x, hxK, rfl⟩
      have hw2 := hwm _ hmem
      have ht2 := List.all_eq_true.1 hp4 _ hmem
      have hs2 : TaintRun.Sim (qmCfg sy m0 v x P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i kq).ram.get! x) (AfterKeep.rkOn Bq) (trace m i kq) :=
        AfterKeep.sim_rkOn hsq
      obtain ⟨k₁', hk1', hq1', _, _, hb1', B₂, hat2, hs₂⟩ :=
        EdgeStep.qR_run (C := qmCfg sy m0 v x P.stops.toList) ht2 rfl rfl hw2 hs2 hfq hdq (hH x (pU_sub (pK_sub hxK))) hx'
      have e1 : k₁' = k₁ := first_eq hk1' hq1' hb1' hk1 hq1 hb1
      subst e1
      simp only [atRkU, Bool.and_eq_true, Bool.not_eq_true'] at hat2
      have e := hs₂.rkv hat2.1
      rw [if_neg (by simp [hat2.2])] at e
      exact e
    · intro hp
      simp only [atRU, Bool.and_eq_true, List.all_eq_true] at hat1
      obtain ⟨hatU, hatN⟩ := hat1
      -- no second arrival at the instruction after the call: the walk of `EdgeStep` to the frame's end
      have huniq : ∀ n, kq < n → (trace m i n).pc = EdgeStep.rPc sy → n = k₁ := by
        have hmem : EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList ∈ [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList] := List.mem_singleton.2 rfl
        have hw2 := hatN _ hmem
        have ht2 := List.all_eq_true.1 hp6 _ hmem
        have hs2 : TaintRun.Sim (EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! (e0 sy m0))
            (AfterKeep.rkOn B₁) (trace m i k₁) := AfterKeep.sim_rkOn hs1
        obtain ⟨_, hnoQ⟩ := EdgeStep.endKP (C := EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList) ht2 rfl rfl hne3 hw2 hs2 hf1 hd1 (hH _ e0_mem) hx'
          (fun j hj hfj => hp j (by omega) hfj)
        intro n hn hrp
        rcases Nat.lt_trichotomy n k₁ with h | h | h
        · exact absurd hrp (hb1 n hn h)
        · exact h
        · exfalso
          have := hnoQ (n - k₁) (by omega)
          rw [show k₁ + (n - k₁) = n by omega] at this
          exact this hrp
      refine ⟨huniq, ?_⟩
      have run : ∀ x ∈ pU sy m0, ∃ k₂, k₁ < k₂ ∧ (trace m i k₂).pc = sy.UpdScrollVar ∧ (trace m i k₂).frame = m.frame ∧
          (∀ j, k₁ < j → j < k₂ → (trace m i j).pc ≠ sy.UpdScrollVar) ∧ (trace m i k₂).ram.get! x = (trace m i k₁).ram.get! x := by
        intro x hxI
        have hmem : quCfg sy m0 x Ps.stops.toList ∈ (pU sy m0).map fun b => quCfg sy m0 b Ps.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
        have hw2 := hatU _ hmem
        have ht2 := List.all_eq_true.1 hp5 _ hmem
        have hs2 : TaintRun.Sim (quCfg sy m0 x Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (AfterKeep.rkOn B₁) (trace m i k₁) :=
          AfterKeep.sim_rkOn hs1
        obtain ⟨k₂, hk2, hq2, hf2, _, hb2, B₂, hat2, hs₂⟩ := qP_run (C := quCfg sy m0 x Ps.stops.toList) ht2 rfl rfl hw2 hs2 hf1 hd1 (hH x hxI) hx'
          (fun j hj hfj => hp j (by omega) hfj)
        simp only [atRkU, Bool.and_eq_true, Bool.not_eq_true'] at hat2
        have e := hs₂.rkv hat2.1
        rw [if_neg (by simp [hat2.2])] at e
        exact ⟨k₂, hk2, hq2, hf2, hb2, e⟩
      have h0x : e0 sy m0 ∈ pU sy m0 := e0_mem
      obtain ⟨k₂, hk2, hq2, hf2, hb2, _⟩ := run _ h0x
      refine ⟨k₂, hk2, hq2, hf2, hb2, fun x hxI => ?_⟩
      obtain ⟨k₂', hk2', hq2', _, hb2', e⟩ := run x hxI
      have e2 : k₂' = k₂ := first_eq hk2' hq2' hb2' hk2 hq2 hb2
      rw [← e2]
      exact e
  · exact absurd harr (hno n₀ hf0)

end Frames2

/-! ## The third piece: the scroll handler moves the scroll counter and the edge by the same `Y`

The pieces of `ScrollRule` (part e), with the scroll counter `S` in place of the fraction (`placesS`): every piece that keeps the position keeps `S`. Only the scroll
itself is cut in two: its first five instructions move `S` by `Y` (`sCheck`), the next ones move the edge's pixel by `Y` with the carry (`mCheck`). The clamp's part up
to the return keeps the edge and `S` (`tailS`). So from the call of the scroll handler to the instruction after it, both are kept, or both move by the same `Y`
(`scroll_callS`). -/

section Scroll
open FrameModel ImpedePosition ScrollRule

/-- the places of `ScrollRule`, with the scroll counter in place of the fraction -/
def placesS (sy : Syms) (m0 : Machine) : ScrollRule.Places := { ScrollRule.places sy m0 with frac := I (places sy m0).s32 }

/-- the counter's part of the scroll: `S` moves by `Y` -/
def sCheck (E : Rom) (P : ScrollRule.Places) (y w : UInt8) : Bool :=
  ScreenClamp.pieceY E { pc := P.scr, s := 0, K := [(P.frac, w)] } { pc := P.scr + 11, s := 0, K := [(P.frac, (adcC w y false).1)] }
    ([P.lx, P.lp, P.x, P.page] ++ stackI) y 8

/-- the edge's part of the scroll: its pixel moves by `Y`, with the carry -/
def mCheck (E : Rom) (P : ScrollRule.Places) (y u : UInt8) : Bool :=
  ScreenClamp.pieceY E { pc := P.scr + 11, s := 0, K := [(P.lx, u)] } { pc := P.pg, s := 0, K := [(P.lx, (adcC u y false).1)], cf := some (adcC u y false).2 }
    ([P.lp] ++ posW P ++ stackI) y 16

/-- from the clamp's call to the scroll handler's return: the edge and the counter kept -/
def tailS (E : Rom) (P : ScrollRule.Places) (s : UInt8) : Bool :=
  pieceOK E { pc := P.chk, s, K := [(stkI (s + 1), retLo P), (stkI (s + 1 + 1), retHi P)] } (cAtS (P.subs + 3) (s + 1 + 1)) [P.lx, P.lp, P.frac] 400

def checkPartsS (E : Rom) (P : ScrollRule.Places) : Bool :=
  [P.xs, P.plat, P.lockB, P.pfs, P.sideB, P.lx, P.lp, P.x, P.page, P.frac].all (fun i => decide (i < 2048)) &&
  (List.range 256).all (fun a => (List.range 256).all fun b => amountCheck E P a.toUInt8 b.toUInt8) &&
  (List.range 256).all (fun v => lockCheck E P v.toUInt8) &&
  (List.range 256).all (fun w => pfsCheck E P w.toUInt8) &&
  (List.range 256).all (fun t => sideCheck E P t.toUInt8) &&
  (List.range 256).all (fun x => ldyCheck E P x.toUInt8) &&
  (List.range 256).all (fun y => (List.range 256).all fun w => nearCheck E P y.toUInt8 w.toUInt8) &&
  (List.range 256).all (fun x => ldy2Check E P x.toUInt8) &&
  (List.range 256).all (fun y => (List.range 256).all fun w => sCheck E P y.toUInt8 w.toUInt8) &&
  (List.range 256).all (fun y => (List.range 256).all fun u => mCheck E P y.toUInt8 u.toUInt8) &&
  (List.range 256).all (fun s => (List.range 256).all fun p => [false, true].all fun c => pgCheck E P s.toUInt8 p.toUInt8 c) &&
  initCheck E P &&
  (List.range 256).all (fun s => jsrCheck E P s.toUInt8) && (List.range 256).all (fun s => tailS E P s.toUInt8)

/-- **The check on the ROM** -/
def checkS (sy : Syms) (m0 : Machine) : Bool := checkPartsS (Rom.of m0) (placesS sy m0)

structure FactsS (E : Rom) (P : ScrollRule.Places) : Prop where
  lt : ∀ i ∈ [P.xs, P.plat, P.lockB, P.pfs, P.sideB, P.lx, P.lp, P.x, P.page, P.frac], i < 2048
  amount : ∀ a b, amountCheck E P a b = true
  lock : ∀ v, lockCheck E P v = true
  pfs : ∀ w, pfsCheck E P w = true
  side : ∀ t, sideCheck E P t = true
  ldy : ∀ x, ldyCheck E P x = true
  near : ∀ y w, nearCheck E P y w = true
  ldy2 : ∀ x, ldy2Check E P x = true
  sc : ∀ y w, sCheck E P y w = true
  mc : ∀ y u, mCheck E P y u = true
  pg : ∀ s p c, pgCheck E P s p c = true
  init : initCheck E P = true
  jsr : ∀ s, jsrCheck E P s = true
  tail : ∀ s, tailS E P s = true

theorem factsS_of_check {E : Rom} {P : ScrollRule.Places} (h : checkPartsS E P = true) : FactsS E P := by
  simp only [checkPartsS, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hA⟩, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩, hS⟩, hM⟩, hI⟩, hJ⟩, hK⟩, hL⟩ := h
  refine ⟨fun i hi => by simpa using List.all_eq_true.1 h0 i hi, fun a b => ?_, all256 hB, all256 hC, all256 hD, all256 hE, fun y w => ?_, all256 hG,
    fun y w => ?_, fun y u => ?_, fun s p c => ?_, hJ, all256 hK, all256 hL⟩
  · exact all256 (f := fun b => amountCheck E P a b) (all256 (f := fun a => (List.range 256).all fun b => amountCheck E P a b.toUInt8) hA a) b
  · exact all256 (f := fun w => nearCheck E P y w) (all256 (f := fun y => (List.range 256).all fun w => nearCheck E P y w.toUInt8) hF y) w
  · exact all256 (f := fun w => sCheck E P y w) (all256 (f := fun y => (List.range 256).all fun w => sCheck E P y w.toUInt8) hS y) w
  · exact all256 (f := fun u => mCheck E P y u) (all256 (f := fun y => (List.range 256).all fun u => mCheck E P y u.toUInt8) hM y) u
  · have h1 := all256 (f := fun p => [false, true].all fun c => pgCheck E P s p c)
      (all256 (f := fun s => (List.range 256).all fun p => [false, true].all fun c => pgCheck E P s p.toUInt8 c) hI s) p
    exact List.all_eq_true.1 h1 c (by cases c <;> simp)

variable {E : Rom} {P : ScrollRule.Places}

theorem ltS_lx (F : FactsS E P) : P.lx < 2048 := F.lt _ (by simp)
theorem ltS_lp (F : FactsS E P) : P.lp < 2048 := F.lt _ (by simp)
theorem ltS_xs (F : FactsS E P) : P.xs < 2048 := F.lt _ (by simp)
theorem ltS_pfs (F : FactsS E P) : P.pfs < 2048 := F.lt _ (by simp)
theorem ltS_side (F : FactsS E P) : P.sideB < 2048 := F.lt _ (by simp)
theorem ltS_lock (F : FactsS E P) : P.lockB < 2048 := F.lt _ (by simp)
theorem ltS_s (F : FactsS E P) : P.frac < 2048 := F.lt _ (by simp)

theorem adc_mod (w y : UInt8) : (adcC w y false).1.toNat = (w.toNat + y.toNat) % 256 := by
  have h := adcC_nat w y false
  have h1 := (adcC w y false).1.toNat_lt
  generalize (adcC w y false).1.toNat = r at h h1 ⊢
  generalize (adcC w y false).2 = c at h
  cases c <;> simp at h <;> omega

/-- the end of the scroll's part: at the clamp's call, the stack and the return address kept, and the edge and the counter kept, or both moved by the same `Y` -/
def EndsS (E : Rom) (P : ScrollRule.Places) (R R' : Machine) : Prop :=
  Good E R' ∧ R'.pc = P.chk ∧ R'.s = R.s ∧ (∀ i ∈ stk2 R.s, R'.ram.get! i = R.ram.get! i) ∧
    ((left16 P R' = left16 P R ∧ R'.ram.get! P.frac = R.ram.get! P.frac) ∨
      (∃ Y : UInt8, left16 P R' = (left16 P R + Y.toNat) % 65536 ∧ (R'.ram.get! P.frac).toNat = ((R.ram.get! P.frac).toNat + Y.toNat) % 256))

theorem exitS_init (F : FactsS E P) {R Ri : Machine} (h : Seg E (kw P R.s) R Ri) (hg : Good E Ri) (hpc : Ri.pc = P.init) :
    ∃ k, EndsS E P R (stepN k R) ∧ InFrameN E R k := by
  have A : At E {cAt P.init with s := Ri.s} Ri := mkAt hg hpc (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k, _, A1, W1, C1⟩ := piece0_spec F.init A
  have S : Seg E (kw P R.s) R (stepN k Ri) :=
    h.trans (seg_of A1.s W1 C1) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  obtain ⟨k', e, f, s, w⟩ := S
  refine ⟨k', ?_, f⟩
  rw [e]
  refine ⟨A1.good, A1.pc, s, fun i hi => w i (List.mem_append_right _ hi) (stk_lt hi), Or.inl ⟨?_, ?_⟩⟩
  · unfold left16
    rw [w _ (by simp [kw]) (ltS_lx F), w _ (by simp [kw]) (ltS_lp F)]
  · exact w _ (by simp [kw, posW]) (ltS_s F)

/-- **The scroll with the counter**, on real machines: from the scroll handler's entry to the clamp's call, the stack and the return address are kept, and the edge
and the counter are kept, or both move by the same `Y`. -/
theorem scrollS_of_facts (F : FactsS E P) {R : Machine} (hg : Good E R) (hpc : R.pc = P.entry) :
    ∃ k, EndsS E P R (stepN k R) ∧ InFrameN E R k := by
  -- the amount
  have A0 : At E {cA P (R.ram.get! P.xs) (R.ram.get! P.plat) with s := R.s} R := by
    refine mkAt hg hpc ?_ (fun _ h => by cases h) (fun _ h => by cases h)
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · rfl
    · rw [List.mem_singleton.1 hq]
  obtain ⟨k1, _, A1, W1, C1⟩ := piece0_spec (F.amount _ _) A0
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have S1 : Seg E (kw P R.s) R R1 :=
    ⟨k1, hR1, C1, A1.s, fun i hi hl => W1 i (mem_w hi (by simp) (by simp) pos_in stk_in) hl⟩
  have x1 : R1.ram.get! P.xs = amountOf P R := A1.K _ (List.mem_singleton.2 rfl)
  have lk1 : R1.ram.get! P.lockB = R.ram.get! P.lockB := W1 _ (by simp) (ltS_lock F)
  have pf1 : R1.ram.get! P.pfs = R.ram.get! P.pfs := W1 _ (by simp) (ltS_pfs F)
  have sd1 : R1.ram.get! P.sideB = R.ram.get! P.sideB := W1 _ (by simp) (ltS_side F)
  -- the scroll lock
  have B0 : At E {cLock P (R1.ram.get! P.lockB) with s := R1.s} R1 :=
    mkAt A1.good A1.pc (kat rfl) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k2, _, A2, W2, C2⟩ := piece0_spec (F.lock _) B0
  generalize hR2 : stepN k2 R1 = R2 at A2 W2
  have S2 : Seg E (kw P R.s) R R2 :=
    S1.trans ⟨k2, hR2, C2, A2.s, W2⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  by_cases hv : R.ram.get! P.lockB = 0
  case neg =>
    have hpc2 : R2.pc = P.init := by
      have e := A2.pc
      rw [lk1] at e
      simpa [cAt, hv] using e
    exact exitS_init F S2 A2.good hpc2
  have hpc2 : R2.pc = P.pfs1 := by
    have e := A2.pc
    rw [lk1] at e
    simpa [cAt, hv] using e
  have x2 : R2.ram.get! P.xs = amountOf P R := (W2 _ (by simp) (ltS_xs F)).trans x1
  have pf2 : R2.ram.get! P.pfs = R.ram.get! P.pfs := (W2 _ (by simp) (ltS_pfs F)).trans pf1
  have sd2 : R2.ram.get! P.sideB = R.ram.get! P.sideB := (W2 _ (by simp) (ltS_side F)).trans sd1
  -- his place on the screen
  have C0 : At E {cPfs P (R2.ram.get! P.pfs) with s := R2.s} R2 :=
    mkAt A2.good hpc2 (kat rfl) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k3, _, A3, W3, C3⟩ := piece0_spec (F.pfs _) C0
  generalize hR3 : stepN k3 R2 = R3 at A3 W3
  have S3 : Seg E (kw P R.s) R R3 :=
    S2.trans ⟨k3, hR3, C3, A3.s, W3⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  by_cases hw : R.ram.get! P.pfs < P.thr1
  · have hpc3 : R3.pc = P.init := by
      have e := A3.pc
      rw [pf2] at e
      simpa [cAt, hw] using e
    exact exitS_init F S3 A3.good hpc3
  have hpc3 : R3.pc = P.side := by
    have e := A3.pc
    rw [pf2] at e
    simpa [cAt, hw] using e
  have x3 : R3.ram.get! P.xs = amountOf P R := (W3 _ (by simp) (ltS_xs F)).trans x2
  have pf3 : R3.ram.get! P.pfs = R.ram.get! P.pfs := (W3 _ (by simp) (ltS_pfs F)).trans pf2
  have sd3 : R3.ram.get! P.sideB = R.ram.get! P.sideB := (W3 _ (by simp) (ltS_side F)).trans sd2
  -- the side collision's timer
  have D0 : At E {cSide P (R3.ram.get! P.sideB) with s := R3.s} R3 :=
    mkAt A3.good hpc3 (kat rfl) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k4, _, A4, W4, C4⟩ := piece0_spec (F.side _) D0
  generalize hR4 : stepN k4 R3 = R4 at A4 W4
  have S4 : Seg E (kw P R.s) R R4 :=
    S3.trans ⟨k4, hR4, C4, A4.s, W4⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  by_cases ht : R.ram.get! P.sideB = 0
  case neg =>
    have hpc4 : R4.pc = P.init := by
      have e := A4.pc
      rw [sd3] at e
      simpa [cAt, ht] using e
    exact exitS_init F S4 A4.good hpc4
  have hpc4 : R4.pc = P.ldy := by
    have e := A4.pc
    rw [sd3] at e
    simpa [cAt, ht] using e
  have x4 : R4.ram.get! P.xs = amountOf P R := (W4 _ (by simp) (ltS_xs F)).trans x3
  have pf4 : R4.ram.get! P.pfs = R.ram.get! P.pfs := (W4 _ (by simp) (ltS_pfs F)).trans pf3
  -- the amount, decremented
  have E0 : At E {cLdy P (amountOf P R) with s := R4.s} R4 :=
    mkAt A4.good hpc4 (kat x4) (fun _ h => by cases h) (fun _ h => by cases h)
  have hE := F.ldy (amountOf P R)
  unfold ldyCheck at hE
  by_cases hx : xOK (amountOf P R) = true
  case neg =>
    rw [if_neg hx] at hE
    obtain ⟨k5, _, A5, W5, C5⟩ := piece0_spec hE E0
    have S5 : Seg E (kw P R.s) R (stepN k5 R4) :=
      S4.trans (seg_of A5.s W5 C5) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
    exact exitS_init F S5 A5.good A5.pc
  rw [if_pos hx] at hE
  obtain ⟨k5, _, A5, y5, W5, C5⟩ := piece0Y_spec hE E0
  generalize hR5 : stepN k5 R4 = R5 at A5 y5 W5
  have S5 : Seg E (kw P R.s) R R5 :=
    S4.trans ⟨k5, hR5, C5, A5.s, W5⟩ (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
  have x5 : R5.ram.get! P.xs = amountOf P R := (W5 _ (by simp) (ltS_xs F)).trans x4
  have pf5 : R5.ram.get! P.pfs = R.ram.get! P.pfs := (W5 _ (by simp) (ltS_pfs F)).trans pf4
  -- at the scroll
  have hYS : ∃ Rs : Machine, Seg E (kw P R.s) R Rs ∧ Good E Rs ∧ Rs.pc = P.scr := by
    have N0 : At E {cNear P (R.ram.get! P.pfs) with s := R5.s} R5 :=
      mkAt A5.good A5.pc (kat pf5) (fun _ h => by cases h) (fun _ h => by cases h)
    obtain ⟨k6, _, A6, y6, W6, C6⟩ := ScreenClamp.pieceY_spec (F.near _ _) N0 y5
    have S6 : Seg E (kw P R.s) R (stepN k6 R5) :=
      S5.trans (seg_of A6.s W6 C6) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩)
    by_cases hn : R.ram.get! P.pfs < P.thr2
    · have hpc6 : (stepN k6 R5).pc = P.scr := by
        have e := A6.pc
        simpa [cAt, hn] using e
      exact ⟨stepN k6 R5, S6, A6.good, hpc6⟩
    · have hpc6 : (stepN k6 R5).pc = P.ldy2 := by
        have e := A6.pc
        simpa [cAt, hn] using e
      have x6 : (stepN k6 R5).ram.get! P.xs = amountOf P R := (W6 _ (by simp) (ltS_xs F)).trans x5
      have G0 : At E {cLdy2 P (amountOf P R) with s := (stepN k6 R5).s} (stepN k6 R5) :=
        mkAt A6.good hpc6 (kat x6) (fun _ h => by cases h) (fun _ h => by cases h)
      obtain ⟨k7, _, A7, _, W7, C7⟩ := piece0Y_spec (F.ldy2 _) G0
      exact ⟨stepN k7 (stepN k6 R5), S6.trans (seg_of A7.s W7 C7) (fun i hi => ⟨hi, mem_w hi (by simp) (by simp) pos_in stk_in⟩), A7.good, A7.pc⟩
  obtain ⟨Rs, Ss, gs, pcs⟩ := hYS
  have lxs : Rs.ram.get! P.lx = R.ram.get! P.lx := by
    obtain ⟨_, _, _, _, w⟩ := Ss
    exact w _ (by simp [kw]) (ltS_lx F)
  have lps : Rs.ram.get! P.lp = R.ram.get! P.lp := by
    obtain ⟨_, _, _, _, w⟩ := Ss
    exact w _ (by simp [kw]) (ltS_lp F)
  have ss : Rs.ram.get! P.frac = R.ram.get! P.frac := by
    obtain ⟨_, _, _, _, w⟩ := Ss
    exact w _ (by simp [kw, posW]) (ltS_s F)
  -- the counter's part
  have H0 : At E {pc := P.scr, s := Rs.s, K := [(P.frac, R.ram.get! P.frac)]} Rs :=
    mkAt gs pcs (kat ss) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k8, _, A8, y8, W8, C8⟩ := ScreenClamp.pieceY_spec (F.sc Rs.y _) H0 rfl
  generalize hR8 : stepN k8 Rs = R8 at A8 y8 W8
  have S8 : Seg E (stk2 R.s) R R8 :=
    Ss.trans ⟨k8, hR8, C8, A8.s, W8⟩ (fun i hi => ⟨List.mem_append_right _ hi, stk_in i hi⟩)
  have s8 : R8.s = R.s := by obtain ⟨_, _, _, e, _⟩ := S8; exact e
  have s8a : R8.ram.get! P.frac = (adcC (R.ram.get! P.frac) Rs.y false).1 := A8.K _ (List.mem_singleton.2 rfl)
  have lx8 : R8.ram.get! P.lx = R.ram.get! P.lx := (W8 _ (by simp) (ltS_lx F)).trans lxs
  have lp8 : R8.ram.get! P.lp = R.ram.get! P.lp := (W8 _ (by simp) (ltS_lp F)).trans lps
  -- the edge's pixel
  have H1 : At E {pc := P.scr + 11, s := R8.s, K := [(P.lx, R.ram.get! P.lx)]} R8 :=
    mkAt A8.good A8.pc (kat lx8) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k9, _, A9, _, W9, C9⟩ := ScreenClamp.pieceY_spec (F.mc R8.y _) H1 rfl
  generalize hR9 : stepN k9 R8 = R9 at A9 W9
  have S9 : Seg E (stk2 R.s) R R9 :=
    S8.trans ⟨k9, hR9, C9, A9.s, W9⟩ (fun i hi => ⟨hi, stk_in i hi⟩)
  have s9 : R9.s = R.s := by obtain ⟨_, _, _, e, _⟩ := S9; exact e
  have lx9 : R9.ram.get! P.lx = (adcC (R.ram.get! P.lx) R8.y false).1 := A9.K _ (List.mem_singleton.2 rfl)
  have sf9 : R9.ram.get! P.frac = (adcC (R.ram.get! P.frac) Rs.y false).1 := (W9 _ (by simp [posW]) (ltS_s F)).trans s8a
  have lp9 : R9.ram.get! P.lp = R.ram.get! P.lp := (W9 _ (by simp) (ltS_lp F)).trans lp8
  -- the page and the screen's right edge
  have I0 : At E (cPg P R9.s (R.ram.get! P.lp) (adcC (R.ram.get! P.lx) R8.y false).2) R9 :=
    mkAt A9.good A9.pc (kat lp9) (fun _ h => by cases h) (fun b hb => by cases hb; exact A9.cf _ rfl)
  obtain ⟨k10, _, A10, W10, _, C10⟩ := piece_spec (F.pg _ _ _) I0
  generalize hR10 : stepN k10 R9 = R10 at A10 W10
  have S10 : Seg E (stk2 R.s) R R10 :=
    S9.trans ⟨k10, hR10, C10, A10.s, W10⟩ (fun i hi => ⟨hi, by rw [s9]; exact List.mem_append_right _ hi⟩)
  have lp10 : R10.ram.get! P.lp = (adcC (R.ram.get! P.lp) 0 (adcC (R.ram.get! P.lx) R8.y false).2).1 := A10.K _ (List.mem_singleton.2 rfl)
  have lx10 : R10.ram.get! P.lx = (adcC (R.ram.get! P.lx) R8.y false).1 := (W10 _ (by simp) (ltS_lx F)).trans lx9
  have sf10 : R10.ram.get! P.frac = (adcC (R.ram.get! P.frac) Rs.y false).1 := (W10 _ (by simp [posW]) (ltS_s F)).trans sf9
  obtain ⟨k, e, f, sk, w⟩ := S10
  refine ⟨k, ?_, f⟩
  rw [e]
  refine ⟨A10.good, A10.pc, sk, fun i hi => w i hi (stk_lt hi), Or.inr ⟨Rs.y, ?_, ?_⟩⟩
  · unfold left16
    rw [lp10, lx10, left_add, y8]
  · rw [sf10]
    exact adc_mod _ _

end Scroll

section ScrollCall
open FrameModel ImpedePosition ScrollRule

/-- **The scroll handler's call with the counter**, on real machines: from the call at the end of the player's routine (`PlayerSubs`) to the instruction after it,
the stack is kept, and the edge (`left16`) and the scroll counter are kept, or both move by the same `Y`. `hc` is the check on the ROM. -/
theorem scroll_callS {sy : Syms} {m0 : Machine} (hc : checkS sy m0 = true) {Q : Machine} (hg : Good (Rom.of m0) Q) (hpc : Q.pc = sy.PlayerSubs) :
    ∃ k, Good (Rom.of m0) (stepN k Q) ∧ (stepN k Q).pc = sy.PlayerSubs + 3 ∧ (stepN k Q).s = Q.s ∧
      ((left16 (placesS sy m0) (stepN k Q) = left16 (placesS sy m0) Q ∧ (stepN k Q).ram.get! (placesS sy m0).frac = Q.ram.get! (placesS sy m0).frac) ∨
        (∃ Y : UInt8, left16 (placesS sy m0) (stepN k Q) = (left16 (placesS sy m0) Q + Y.toNat) % 65536 ∧
          ((stepN k Q).ram.get! (placesS sy m0).frac).toNat = ((Q.ram.get! (placesS sy m0).frac).toNat + Y.toNat) % 256)) ∧ InFrameN (Rom.of m0) Q k := by
  have F := factsS_of_check hc
  have hsub : (placesS sy m0).subs = sy.PlayerSubs := rfl
  rw [← hsub] at hpc ⊢
  generalize Rom.of m0 = E at F hg ⊢
  generalize placesS sy m0 = P at F hpc ⊢
  -- the call
  have J0 : At E (cAtS P.subs Q.s) Q := mkAt hg hpc (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  obtain ⟨k1, _, A1, W1, _, C1⟩ := piece_spec (F.jsr Q.s) J0
  generalize hR1 : stepN k1 Q = R1 at A1 W1
  have s1 : R1.s = Q.s - 1 - 1 := A1.s
  have hi1 : R1.ram.get! (stkI Q.s) = retHi P := A1.K (stkI Q.s, retHi P) (by simp)
  have lo1 : R1.ram.get! (stkI (Q.s - 1)) = retLo P := A1.K (stkI (Q.s - 1), retLo P) (by simp)
  -- the scroll and the clamp's call
  obtain ⟨k2, ⟨g2, pc2, s2, st2, L2⟩, C2⟩ := scrollS_of_facts F A1.good A1.pc
  generalize hR2 : stepN k2 R1 = R2 at g2 pc2 s2 st2 L2
  have lo2 : R2.ram.get! (stkI (R2.s + 1)) = retLo P := by
    rw [s2, s1, sub2_add1]
    have e := st2 (stkI (R1.s + 1)) (by simp [stk2])
    rw [s1, sub2_add1] at e
    rw [e, lo1]
  have hi2 : R2.ram.get! (stkI (R2.s + 1 + 1)) = retHi P := by
    rw [s2, s1, sub2_add2]
    have e := st2 (stkI (R1.s + 1 + 1)) (by simp [stk2])
    rw [s1, sub2_add2] at e
    rw [e, hi1]
  -- the clamp, up to the return
  have T0 : At E { pc := P.chk, s := R2.s, K := [(stkI (R2.s + 1), retLo P), (stkI (R2.s + 1 + 1), retHi P)] } R2 := by
    refine mkAt g2 pc2 ?_ (fun _ h => by cases h) (fun _ h => by cases h)
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact lo2
    · rw [List.mem_singleton.1 hq]
      exact hi2
  obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec (F.tail R2.s) T0
  have s3 : (stepN k3 R2).s = Q.s := by
    rw [A3.s]
    show R2.s + 1 + 1 = Q.s
    rw [s2, s1, sub2_add2]
  have lx3 : (stepN k3 R2).ram.get! P.lx = R2.ram.get! P.lx := W3 _ (by simp) (ltS_lx F)
  have lp3 : (stepN k3 R2).ram.get! P.lp = R2.ram.get! P.lp := W3 _ (by simp) (ltS_lp F)
  have sf3 : (stepN k3 R2).ram.get! P.frac = R2.ram.get! P.frac := W3 _ (by simp) (ltS_s F)
  have L3 : left16 P (stepN k3 R2) = left16 P R2 := by unfold left16; rw [lx3, lp3]
  have L1 : left16 P R1 = left16 P Q := by
    unfold left16
    rw [W1 _ (by simp) (ltS_lx F), W1 _ (by simp) (ltS_lp F)]
  have sf1 : R1.ram.get! P.frac = Q.ram.get! P.frac := W1 _ (by simp [posW]) (ltS_s F)
  refine ⟨k1 + (k2 + k3), ?_⟩
  have eq : stepN (k1 + (k2 + k3)) Q = stepN k3 R2 := by rw [stepN_add, hR1, stepN_add, hR2]
  rw [eq]
  refine ⟨A3.good, A3.pc, s3, ?_, InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)⟩
  rw [L3, sf3, ← L1, ← sf1]
  exact L2

end ScrollCall

/-! ## A frame up to `UpdScrollVar`, as a whole

The three pieces joined: from a frame's start in control to the first `UpdScrollVar` after the scroll handler's call, the tasks left, the column and the page are
kept, and the edge and the scroll counter are kept, or both move by the same `Y` (`frame_toU`). This is the scroll's part of `Rule` (`Scroll`) on a real frame,
read at `UpdScrollVar`. -/

section FrameU
open PipeEntryRule (trace)
open PipeTransition (frame)
open AfterKeep (guardH)
open FrameModel (Good Rom)

variable {m0 : Machine}

theorem lx_mem : (placesS sy m0).lx ∈ pU sy m0 := List.mem_append_right _ List.mem_cons_self
theorem lp_mem : (placesS sy m0).lp ∈ pU sy m0 := List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem s_memI : (placesS sy m0).frac ∈ pI sy m0 := List.mem_map.2 ⟨(places sy m0).s32, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

/-- **A frame in control, from its start to `UpdScrollVar`**: the conditions of `keep_qP` and `keep_uP`, the checks of the edge (`EdgeStep.qCheck`) and of the
scroll with the counter (`checkS`), the time of the frame (`ht`, as `CleanK` gives it) and no store to his position by its address outside the push and the clamp
from the scroll handler on (`hp`, the field `posW`). Then the frame comes to `UpdScrollVar` at `k₂`, in the frame, where the tasks left, the column and the page are
those of the frame's start, and the edge and the counter are those of the start, or both moved by the same `Y`. -/
theorem frame_toU (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (hu : uCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false) :
    ∃ k₂, (trace m i k₂).pc = sy.UpdScrollVar ∧ (trace m i k₂).frame = m.frame ∧
      (∀ x ∈ pK sy m0, (trace m i k₂).ram.get! x = m.ram.get! x) ∧
      ((ScrollRule.left16 (placesS sy m0) (trace m i k₂) = ScrollRule.left16 (placesS sy m0) m ∧
          (trace m i k₂).ram.get! (placesS sy m0).frac = m.ram.get! (placesS sy m0).frac) ∨
        (∃ Y : UInt8, ScrollRule.left16 (placesS sy m0) (trace m i k₂) = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 ∧
          ((trace m i k₂).ram.get! (placesS sy m0).frac).toNat = ((m.ram.get! (placesS sy m0).frac).toNat + Y.toNat) % 256)) := by
  obtain ⟨kq, hkq, hqq, hfq, hbq, k₁, hk1, hq1, hf1, hb1, hK, HU⟩ := keep_uP hc hu h0 hcl hH hx hv harr hf0 hfirst
  have HQ := keep_qP hc hq h0 hcl (fun x hx j => hH x (pU_sub hx) j) hx hv harr hf0 hfirst (Nat.le_of_lt hkq) hqq hbq
  have HE := EdgeStep.keep_q hc hqe h0 hcl (fun x hx j => hH x (List.mem_append_right _ hx) j) hx hv harr hf0 hfirst (Nat.le_of_lt hkq) hqq hbq
  have hgQ := (HQ _ s_memI).1
  obtain ⟨k, _, pcR, _, L, ifr⟩ := scroll_callS hs hgQ hqq
  have eq := FrameModel.trace_inFrame hidle hfq ifr ht k (Nat.le_refl _)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with e | e
    · exfalso
      subst e
      have e2 : (FrameModel.stepN 0 (trace m i kq)).pc = sy.PlayerSubs := hqq
      rw [pcR] at e2
      have e3 := congrArg UInt16.toNat e2
      simp only [UInt16.toNat_add] at e3
      have e4 : (3 : UInt16).toNat = 3 := rfl
      rw [e4] at e3
      have := sy.PlayerSubs.toNat_lt
      omega
    · exact e
  obtain ⟨huniq, k₂, _, hq2, hf2, _, hU⟩ := HU (fun j hj hfj => hp kq hqq j hj hfj)
  have e1 : kq + k = k₁ := huniq (kq + k) (by omega) (by rw [eq.1]; exact pcR)
  have hk₁ : trace m i k₁ = FrameModel.stepN k (trace m i kq) := by rw [← e1]; exact eq.1
  refine ⟨k₂, hq2, hf2, fun x hx => ?_, ?_⟩
  · rw [hU x (pU_sub (pK_sub hx)), hK x hx]
    exact (HQ x (pK_sub hx)).2
  · have lx2 : (trace m i k₂).ram.get! (placesS sy m0).lx = (trace m i k₁).ram.get! (placesS sy m0).lx := hU _ lx_mem
    have lp2 : (trace m i k₂).ram.get! (placesS sy m0).lp = (trace m i k₁).ram.get! (placesS sy m0).lp := hU _ lp_mem
    have s2 : (trace m i k₂).ram.get! (placesS sy m0).frac = (trace m i k₁).ram.get! (placesS sy m0).frac := hU _ (pU_sub s_memI)
    have lxq : (trace m i kq).ram.get! (placesS sy m0).lx = m.ram.get! (placesS sy m0).lx := (HE _ List.mem_cons_self).2
    have lpq : (trace m i kq).ram.get! (placesS sy m0).lp = m.ram.get! (placesS sy m0).lp := (HE _ (List.mem_cons_of_mem _ List.mem_cons_self)).2
    have sq : (trace m i kq).ram.get! (placesS sy m0).frac = m.ram.get! (placesS sy m0).frac := (HQ _ s_memI).2
    have L2 : ScrollRule.left16 (placesS sy m0) (trace m i k₂) = ScrollRule.left16 (placesS sy m0) (FrameModel.stepN k (trace m i kq)) := by
      unfold ScrollRule.left16
      rw [lx2, lp2, hk₁]
    have Lq : ScrollRule.left16 (placesS sy m0) (trace m i kq) = ScrollRule.left16 (placesS sy m0) m := by
      unfold ScrollRule.left16
      rw [lxq, lpq]
    rw [L2, s2, hk₁, ← Lq, ← sq]
    exact L

end FrameU

/-! ## The run: what is left for the invariant at every frame's start

With the frames of a run `ms (n + 1) = frame (ms n) (ins n)`, the invariant holds at every frame's start if it holds at the first (`inv₀` at control) and every
frame follows `Rule` (`inv_run`). A frame follows `Rule` (`rule_of_toU`) if it has the conclusion of `frame_toU` at `UpdScrollVar`, the scroll does not wrap the
counter or the edge (`S + Y < 256`, `edge + Y < 2¹⁶`), and from `UpdScrollVar` to its end it follows `Parse` (`ParseU`, not proved). A frame that does not come to
the player's routine keeps the six bytes (`keep_noCutP`, `EdgeStep.keep_noCut`), so it follows `Rule` (`rule_of_kept`). -/

section Run
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {m0 : Machine}

/-- the values are read from the bytes: the tasks left, the counter, the column with its page, the edge -/
theorem vals_eq {m m' : Machine} (hn : peek m' (places sy m0).task = peek m (places sy m0).task) (hs : peek m' (places sy m0).s32 = peek m (places sy m0).s32)
    (hc : peek m' (places sy m0).col = peek m (places sy m0).col) (hp : peek m' (places sy m0).page = peek m (places sy m0).page)
    (hx : peek m' (places sy m0).ex = peek m (places sy m0).ex) (he : peek m' (places sy m0).ep = peek m (places sy m0).ep) :
    valsOf (places sy m0) m' = valsOf (places sy m0) m := by
  unfold valsOf colOf edgeOf
  rw [hn, hs, hc, hp, hx, he]

/-- **A frame that keeps the six bytes follows the rule** (the control byte read as 6, no scroll) -/
theorem rule_of_kept {m m' : Machine} (h : valsOf (places sy m0) m' = valsOf (places sy m0) m) :
    Rule (valsOf (places sy m0) m) (valsOf (places sy m0) m') := by
  refine ⟨true, valsOf (places sy m0) m, ⟨0, rfl, rfl, by simp, by simp⟩, ?_⟩
  rw [h]
  exact ⟨rfl, by simp⟩

/-- **A frame that comes to the player's routine and does not**: `keep_noCutP` and `EdgeStep.keep_noCut` keep the six bytes -/
theorem rule_of_noCut {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) :
    Rule (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) := by
  have A := keep_noCutP hq h0 hcl hn
  have B := EdgeStep.keep_noCut hqe h0 hcl hn
  refine rule_of_kept (vals_eq ?_ ?_ ?_ ?_ ?_ ?_)
  · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
  · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
  · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩)
  · exact B _ List.mem_cons_self
  · exact B _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **What is not proved of one frame**: from `UpdScrollVar` (the machine `u`) to the frame's end `e` the parser's part of the rule, with the control byte read at `u` -/
def ParseU (sy : Syms) (m0 u e : Machine) : Prop := Parse (peek u (places sy m0).ctrl == 6) (valsOf (places sy m0) u) (valsOf (places sy m0) e)

/-- **A frame with the conclusion of `frame_toU`, no wrap of the scroll, and `ParseU`, follows the rule** -/
theorem rule_of_toU {m u e : Machine}
    (hK : ∀ x ∈ pK sy m0, u.ram.get! x = m.ram.get! x)
    (hS : (ScrollRule.left16 (placesS sy m0) u = ScrollRule.left16 (placesS sy m0) m ∧ u.ram.get! (placesS sy m0).frac = m.ram.get! (placesS sy m0).frac) ∨
      (∃ Y : UInt8, ScrollRule.left16 (placesS sy m0) u = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 ∧
        (u.ram.get! (placesS sy m0).frac).toNat = ((m.ram.get! (placesS sy m0).frac).toNat + Y.toNat) % 256))
    (hw : ∀ Y : UInt8, ScrollRule.left16 (placesS sy m0) u = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 →
      (m.ram.get! (placesS sy m0).frac).toNat + Y.toNat < 256 ∧ ScrollRule.left16 (placesS sy m0) m + Y.toNat < 65536)
    (hP : ParseU sy m0 u e) :
    Rule (valsOf (places sy m0) m) (valsOf (places sy m0) e) := by
  have hn : peek u (places sy m0).task = peek m (places sy m0).task := hK _ (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  have hc : peek u (places sy m0).col = peek m (places sy m0).col := hK _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
  have hp : peek u (places sy m0).page = peek m (places sy m0).page :=
    hK _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
  have el : ∀ x : Machine, edgeOf (places sy m0) x = ScrollRule.left16 (placesS sy m0) x := fun _ => rfl
  have es : ∀ x : Machine, (peek x (places sy m0).s32) = x.ram.get! (placesS sy m0).frac := fun _ => rfl
  refine ⟨peek u (places sy m0).ctrl == 6, valsOf (places sy m0) u, ?_, hP⟩
  rcases hS with ⟨h1, h2⟩ | ⟨Y, h1, h2⟩
  · refine ⟨0, ?_, ?_, ?_, ?_⟩
    · show (peek u (places sy m0).task).toNat = (peek m (places sy m0).task).toNat
      rw [hn]
    · show colOf (places sy m0) u = colOf (places sy m0) m
      unfold colOf
      rw [hc, hp]
    · show (peek u (places sy m0).s32).toNat = (peek m (places sy m0).s32).toNat + 0
      rw [es, es, h2]
      exact (Nat.add_zero _).symm
    · show edgeOf (places sy m0) u = edgeOf (places sy m0) m + 0
      rw [el, el, h1]
      exact (Nat.add_zero _).symm
  · obtain ⟨w1, w2⟩ := hw Y h1
    refine ⟨Y.toNat, ?_, ?_, ?_, ?_⟩
    · show (peek u (places sy m0).task).toNat = (peek m (places sy m0).task).toNat
      rw [hn]
    · show colOf (places sy m0) u = colOf (places sy m0) m
      unfold colOf
      rw [hc, hp]
    · show (peek u (places sy m0).s32).toNat = (peek m (places sy m0).s32).toNat + Y.toNat
      rw [es, es, h2]
      exact Nat.mod_eq_of_lt w1
    · show edgeOf (places sy m0) u = edgeOf (places sy m0) m + Y.toNat
      rw [el, el, h1]
      exact Nat.mod_eq_of_lt w2

/-- **The invariant at every frame's start of a run**, from the first and the rule of each frame -/
theorem inv_run {L : Nat} {ms : Nat → Machine} (h0 : Inv (places sy m0) L (ms 0))
    (hr : ∀ n, Rule (valsOf (places sy m0) (ms n)) (valsOf (places sy m0) (ms (n + 1)))) : ∀ n, Inv (places sy m0) L (ms n) :=
  inv_frames (v := fun n => valsOf (places sy m0) (ms n)) h0 hr

end Run

end Smbrta.PoleParser
