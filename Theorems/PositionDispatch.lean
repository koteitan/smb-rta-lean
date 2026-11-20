import Theorems.PositionPieces

/-! Constructing position cuts by dispatching ordinary instructions and complete calls.
Coverage of the reachable dispatch states is an explicit local obligation, not a Run field. -/
namespace Smbrta.PositionDispatch
open FrameModel

def Ordinary (sy : Syms) (R : Machine) : Prop :=
  ∀ a ∈ [sy.Player_X_Position,sy.Player_PageLoc,sy.SprObject_X_MoveForce],
    I a ∉ StepWrites.stepLocs R

/-- Requirements at dispatch states only; interiors of summarized calls are skipped. -/
def Ready (sy : Syms) (m0 R : Machine) : Prop :=
  if R.pc = sy.ImpedePlayerMove then
    Good (Rom.of m0) R ∧ 256 ≤ posP sy R ∧ posP sy R+256 < 0x1000000
  else if R.pc = (ScreenClamp.places sy m0).entry then
    Good (Rom.of m0) R ∧ R.y ∈ [0,(1 : UInt8)] ∧
      0 ≤ ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) R R.y ∧
      ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) R R.y < 0x1000000
  else Ordinary sy R

/-- A certified actual trace piece, including its chronological endpoints. -/
inductive Edge (sy : Syms) (m0 : Machine) (T : Nat → Machine) : Nat → Nat → Int → Prop
  | ordinary {a : Nat} (notImpede : (T a).pc ≠ sy.ImpedePlayerMove)
      (notClamp : (T a).pc ≠ (ScreenClamp.places sy m0).entry) (noStore : Ordinary sy (T a))
      (effect : posP sy (T (a+1)) = posP sy (T a)) : Edge sy m0 T a (a+1) 0
  | impede {a b : Nat} (forward : a < b) (entry : (T a).pc = sy.ImpedePlayerMove)
      (ret : (T b).pc = ImpedePosition.returnPc (T a)) (stack : (T b).s = (T a).s+1+1)
      (effect : posP sy (T b) = posP sy (T a)+
        256*ImpedePosition.delta ((T a).ram.get! (ImpedePosition.sites sy m0).side) (peek (T a) sy.Player_X_Speed)) :
      Edge sy m0 T a b (256*ImpedePosition.delta ((T a).ram.get! (ImpedePosition.sites sy m0).side) (peek (T a) sy.Player_X_Speed))
  | clamp {a b : Nat} (forward : a < b) (entry : (T a).pc = (ScreenClamp.places sy m0).entry)
      (ret : (T b).pc = ImpedePosition.returnPc (T a)) (stack : (T b).s = (T a).s+1+1)
      (effect : posP sy (T b) = ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) (T a) (T a).y) :
      Edge sy m0 T a b (ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) (T a) (T a).y-posP sy (T a))

theorem Edge.forward {sy m0 T a b e} (h : Edge sy m0 T a b e) : a < b := by
  cases h with
  | ordinary => omega
  | impede f _ _ _ _ => exact f
  | clamp f _ _ _ _ => exact f

theorem Edge.effect {sy m0 T a b e} (h : Edge sy m0 T a b e) :
    posP sy (T b) = posP sy (T a)+e := by
  cases h with
  | ordinary _ _ _ h => simpa using h
  | impede _ _ _ _ h => exact h
  | clamp _ _ _ _ h => omega

/-- States reached by the dispatcher, not all instructions inside calls. -/
inductive Reached (sy : Syms) (m0 : Machine) (T : Nat → Machine) (q : Nat) : Nat → Prop
  | start : Reached sy m0 T q q
  | next {a b e} : Reached sy m0 T q a → Edge sy m0 T a b e → Reached sy m0 T q b

inductive Chain (sy : Syms) (m0 : Machine) (T : Nat → Machine) : Nat → Nat → List Int → Prop
  | nil (a) : Chain sy m0 T a a []
  | cons {a b c e es} : Edge sy m0 T a b e → Chain sy m0 T b c es → Chain sy m0 T a c (e::es)

theorem Chain.sum {sy m0 T a b es} (h : Chain sy m0 T a b es) :
    posP sy (T b) = posP sy (T a)+es.sum := by
  induction h with
  | nil => simp
  | cons edge _ ih => have := edge.effect; simp only [List.sum_cons]; omega

/-- Once the trace ends, no later index can still be in the old frame. -/
theorem before_end {M : Machine} {input : UInt8} {b n : Nat}
    (finish : (PipeEntryRule.trace M input b).frame = M.frame+1)
    (live : (PipeEntryRule.trace M input n).frame = M.frame) : n < b := by
  by_cases hn : n < b
  · exact hn
  · have stop : ((PipeEntryRule.trace M input b).frame ≥ M.frame+1 ||
        (PipeEntryRule.trace M input b).halted) = true := by simp [finish]
    have eq := PipeEntryRule.trace_stop stop (n-b)
    have e : b+(n-b) = n := by omega
    rw [e] at eq
    have f := congrArg Machine.frame eq
    rw [live,finish] at f
    omega

private theorem positive_return {R : Machine} {k : Nat}
    (stack : (stepN k R).s = R.s+1+1) : 0 < k := by
  have finite : ∀ n : Fin 256, UInt8.ofNat n.val ≠ UInt8.ofNat n.val+1+1 := by decide +kernel
  have diff : ∀ s : UInt8, s ≠ s+1+1 := by
    intro s
    simpa using finite ⟨s.toNat,s.toNat_lt⟩
  by_cases h : k = 0
  · subst k
    exact False.elim (diff R.s stack)
  · omega

/-- Choose the next actual cut. Calls return in the same frame before its end;
ordinary instructions advance one index. No supplied partition is needed. -/
theorem next_piece {sy : Syms} {m0 M : Machine} {input : UInt8} {n b : Nat}
    (hi : ImpedePosition.check sy m0 = true) (hc : ScreenClamp.check sy m0 = true)
    (idle : idleAt (Rom.of m0) sy.EndlessLoop = true)
    (time : ∀ j, (PipeEntryRule.trace M input j).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace M input j).fdot ≤ dotsPerFrame-64)
    (finish : (PipeEntryRule.trace M input b).frame = M.frame+1)
    (live : (PipeEntryRule.trace M input n).frame = M.frame) (nb : n < b)
    (ready : Ready sy m0 (PipeEntryRule.trace M input n)) :
    ∃ c e, c ≤ b ∧ Edge sy m0 (PipeEntryRule.trace M input) n c e := by
  let R := PipeEntryRule.trace M input n
  change Ready sy m0 R at ready
  by_cases pi : R.pc = sy.ImpedePlayerMove
  · have h : Good (Rom.of m0) R ∧ 256 ≤ posP sy R ∧ posP sy R+256 < 0x1000000 := by
      simpa only [Ready,if_pos pi] using ready
    obtain ⟨k,_,_,ret,sp,pos,ifr⟩ := PositionPieces.impede_piece hi h.1 pi h.2.1 h.2.2
    have kp := positive_return sp
    have eq := trace_inFrame idle live ifr time k (Nat.le_refl _)
    have cb := before_end finish eq.2
    refine ⟨n+k,_,by omega,Edge.impede (by omega) pi ?_ ?_ ?_⟩
    · rw [eq.1]; exact ret
    · rw [eq.1]; exact sp
    · rw [eq.1]; exact pos
  · by_cases pc : R.pc = (ScreenClamp.places sy m0).entry
    · have h : Good (Rom.of m0) R ∧ R.y ∈ [0,(1 : UInt8)] ∧
          0 ≤ ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) R R.y ∧
          ScreenClamp.target (Rom.of m0) (ScreenClamp.places sy m0) R R.y < 0x1000000 := by
        simpa only [Ready,if_neg pi,if_pos pc] using ready
      obtain ⟨k,_,_,ret,sp,pos,ifr⟩ := PositionPieces.clamp_piece hc h.1 pc h.2.1 h.2.2
      have kp := positive_return sp
      have eq := trace_inFrame idle live ifr time k (Nat.le_refl _)
      have cb := before_end finish eq.2
      refine ⟨n+k,_,by omega,Edge.clamp (by omega) pc ?_ ?_ ?_⟩
      · rw [eq.1]; exact ret
      · rw [eq.1]; exact sp
      · rw [eq.1]; exact pos
    · have ordinary : Ordinary sy R := by simpa only [Ready,if_neg pi,if_neg pc] using ready
      have halted : R.halted = false := by
        cases hh : R.halted with
        | false => rfl
        | true =>
          have stop : ((PipeEntryRule.trace M input n).frame ≥ M.frame+1 ||
              (PipeEntryRule.trace M input n).halted) = true := by simp [R,← hh]
          have eq := PipeEntryRule.trace_stop stop (b-n)
          have e : n+(b-n) = b := by omega
          rw [e] at eq
          have f := congrArg Machine.frame eq
          rw [finish,live] at f
          omega
      have e : PipeEntryRule.trace M input (n+1) = stepN 1 R := by
        change PipeEntryRule.nxt (M.frame+1) R = (PipeTransitionAll.go step R).2
        simp [PipeEntryRule.nxt,show R.frame = M.frame from live,halted]
        omega
      refine ⟨n+1,0,by omega,Edge.ordinary pi pc ordinary ?_⟩
      rw [e]
      exact ImpedePosition.ordinary_step ordinary

/-- Local coverage at reached dispatch cuts constructs a chronological complete
chain. Proving this coverage from the route's guards is still required. -/
theorem partition {sy : Syms} {m0 M : Machine} {input : UInt8} {q b : Nat}
    (hi : ImpedePosition.check sy m0 = true) (hc : ScreenClamp.check sy m0 = true)
    (idle : idleAt (Rom.of m0) sy.EndlessLoop = true)
    (time : ∀ j, (PipeEntryRule.trace M input j).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace M input j).fdot ≤ dotsPerFrame-64)
    (finish : (PipeEntryRule.trace M input b).frame = M.frame+1) (qb : q ≤ b)
    (live : ∀ n, q ≤ n → n < b → (PipeEntryRule.trace M input n).frame = M.frame)
    (coverage : ∀ n, q ≤ n → n < b → Reached sy m0 (PipeEntryRule.trace M input) q n →
      Ready sy m0 (PipeEntryRule.trace M input n)) :
    ∃ es, Chain sy m0 (PipeEntryRule.trace M input) q b es ∧
      posP sy (PipeEntryRule.trace M input b) = posP sy (PipeEntryRule.trace M input q)+es.sum := by
  have build : ∀ d a, b-a = d → q ≤ a → a ≤ b →
      Reached sy m0 (PipeEntryRule.trace M input) q a →
      ∃ es, Chain sy m0 (PipeEntryRule.trace M input) a b es := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro a dist qa ab reached
      by_cases done : a = b
      · subst a; exact ⟨[],Chain.nil b⟩
      · have lt : a < b := by omega
        obtain ⟨c,e,cb,edge⟩ := next_piece hi hc idle time finish (live a qa lt) lt (coverage a qa lt reached)
        have ac := edge.forward
        obtain ⟨es,tail⟩ := ih (b-c) (by omega) c rfl (by omega) cb (Reached.next reached edge)
        exact ⟨e::es,Chain.cons edge tail⟩
  obtain ⟨es,chain⟩ := build (b-q) q rfl (Nat.le_refl _) qb Reached.start
  exact ⟨es,chain,chain.sum⟩

/-- Extract the numeric cuts consumed by PositionPieces.trace_sum. -/
theorem Chain.cuts {sy m0 T a b es} (h : Chain sy m0 T a b es) :
    ∃ cuts : Nat → Nat, cuts 0 = a ∧ cuts es.length = b ∧
      ∀ j, j < es.length → Edge sy m0 T (cuts j) (cuts (j+1)) es[j]! := by
  induction h with
  | nil a => exact ⟨fun _ => a,rfl,rfl,fun j hj => by simp at hj⟩
  | @cons a b c e es edge tail ih =>
    obtain ⟨old,first,last,pieces⟩ := ih
    refine ⟨fun j => match j with | 0 => a | n+1 => old n,rfl,?_,?_⟩
    · simpa using last
    · intro j hj
      cases j with
      | zero => simpa [first] using edge
      | succ j => simpa using pieces j (by simpa using hj)

/-- Pixel coordinates separate the live edge from both fractions. -/
def pixel (page x : UInt8) : Int := 256*(page.toNat : Int)+(x.toNat : Int)

def edgeGap (sy : Syms) (E : Rom) (P : ScreenClamp.Places) (M R : Machine) (selector : UInt8) : Int :=
  pixel (peek R (P.edgeP+selector.toUInt16)) (peek R (P.edgeX+selector.toUInt16)) -
    pixel (peek M sy.Player_PageLoc) (peek M sy.Player_X_Position) -
    (ScreenClamp.amount E P selector).toNat

theorem target_difference (sy : Syms) (E : Rom) (P : ScreenClamp.Places) (M R : Machine) (selector : UInt8) :
    ScreenClamp.target E P R selector-posP sy M = 256*edgeGap sy E P M R selector +
      (R.ram.get! P.frac).toNat-(peek M sy.SprObject_X_MoveForce).toNat := by
  unfold ScreenClamp.target edgeGap pixel posOf posP peek
  omega

/-- An exact two-cut reformulation of the tested target bound. This does not
prove the screen-edge relation or either selector unreachable. -/
theorem target_bound_iff (sy : Syms) (E : Rom) (P : ScreenClamp.Places) (M R : Machine) (selector : UInt8) :
    ScreenClamp.target E P R selector ≤ posP sy M+256 ↔
      edgeGap sy E P M R selector ≤ 0 ∨
      (edgeGap sy E P M R selector = 1 ∧
        (R.ram.get! P.frac).toNat ≤ (peek M sy.SprObject_X_MoveForce).toNat) := by
  have eq := target_difference sy E P M R selector
  have f := (R.ram.get! P.frac).toNat_lt
  have g := (peek M sy.SprObject_X_MoveForce).toNat_lt
  omega

end Smbrta.PositionDispatch
