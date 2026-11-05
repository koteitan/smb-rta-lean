import Theorems.Reach

/-!
# The horizontal frame and a potential for the acceleration

`hstep` is one frame of the horizontal state, as the game runs it: `X_Physics` (speed caps and
friction adder), then on the ground `GetPlayerAnimSpeed` (may stop a skid), the facing direction
set from Left/Right, and `ImposeFriction`; in the air `ImposeFriction` only when Left or Right
is held; at the end the moving direction is set from the sign of the speed. The routines are
the game's own code (`runSub`); the order and the two direction writes are the frame code
around them (from the disassembly). Open area: `Player_CollisionBits` as at the 1-1 start.

Potential `Φ = |V| + w(facing, moving)` with `V = 256·v + subspeed`. The doubled adder
(`facing ≠ moving`) needs a frame that sets the facing direction, so `w` charges for it.
`potCheck` checks, for every state and input: `Φ' ≤ Φ + g_fast`, and `Φ' ≤ Φ + g_slow` while
slow (`RunningSpeed = 0` and `|v|` below the air threshold of `X_Physics`).
Page: `Reach.md`.
-/

namespace Smbrta.Potential

open TopSpeed (top speedsB bytes absB inSpeed)

/-- the horizontal state at the start of a frame -/
structure HS where
  /-- `Player_X_Speed` -/
  v : UInt8
  /-- `Player_X_MoveForce` (subspeed) -/
  f : UInt8
  /-- `PlayerFacingDir` -/
  fd : UInt8
  /-- `Player_MovingDir` -/
  md : UInt8
  /-- `RunningSpeed`, as 0 or `RunSpeedMin` (the game reads it only as zero or not) -/
  rs : UInt8
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- the input of a frame -/
structure HIn where
  /-- `Player_State` at the start of the frame: 0 on the ground, 1 in the air -/
  st : UInt8
  /-- A newly pressed: on the ground this starts a jump before `X_Physics` -/
  jump : Bool
  /-- the buttons Right, Left, Down, Up, B -/
  joy : UInt8
  /-- `RunningTimer` as 0 or 1 (read only as zero or not; it counts down elsewhere, so it is
  chosen freely in every frame) -/
  rt : UInt8
  deriving DecidableEq, Repr

/-- drop what a frame does not read. In the air (`X_Physics` on its air path, no
`GetPlayerAnimSpeed`) only Left/Right count, and on a jump start also Down (it clears Left/Right
while still on the ground); the running timer is not read. On the ground the running timer is
not read when B is held (B sets it), and Up counts only in `GetPlayerAnimSpeed`'s test for any
button other than A, so not when Right, Left, Down or B is held. -/
def norm (i : HIn) : HIn :=
  if i.st == 0 && !i.jump then
    { i with joy := if i.joy &&& 0x47 != 0 then i.joy &&& 0x47 else i.joy,
             rt := if i.joy &&& 0x40 != 0 then 0 else i.rt }
  else { i with joy := i.joy &&& (if i.st == 0 then 0x07 else 0x03), rt := 0 }

/-- one frame of the horizontal state, on the normalized input -/
def hstepN (sy : Syms) (m0 : Machine) (s : HS) (i : HIn) : HS :=
  let lr0 := i.joy &&& 3
  -- pressing Down on the ground clears Left/Right
  let lr := if i.joy &&& 4 != 0 && i.st == 0 && lr0 != 0 then 0 else lr0
  let st : UInt8 := if i.st == 0 && i.jump then 1 else i.st
  let m := poke m0 sy.Player_State st
  let m := poke m sy.Player_X_Speed s.v
  let m := poke m sy.Player_X_MoveForce s.f
  let m := poke m sy.Player_XSpeedAbsolute (absB s.v)
  let m := poke m sy.PlayerFacingDir s.fd
  let m := poke m sy.Player_MovingDir s.md
  let m := poke m sy.RunningSpeed s.rs
  let m := poke m sy.RunningTimer i.rt
  let m := poke m sy.Left_Right_Buttons lr
  let m := poke m sy.A_B_Buttons (i.joy &&& 0x40 ||| (if i.jump then 0x80 else 0))
  let m := poke m sy.SavedJoypadBits (i.joy ||| (if i.jump then 0x80 else 0))
  let m := poke m sy.GameEngineSubroutine sy.Eng_PlayerCtrl.toUInt8
  let m := runSub m sy.X_Physics 0 0 0
  let m := if st == 0 then
      let m := runSub m sy.GetPlayerAnimSpeed 0 0 0
      let m := if lr != 0 then poke m sy.PlayerFacingDir lr else m
      runSub m sy.ImposeFriction lr 0 0
    else if lr != 0 then runSub m sy.ImposeFriction lr 0 0 else m
  let v' := peek m sy.Player_X_Speed
  let md' := if v' == 0 then peek m sy.Player_MovingDir else if v' < 0x80 then 1 else 2
  { v := v', f := peek m sy.Player_X_MoveForce, fd := peek m sy.PlayerFacingDir, md := md',
    rs := if peek m sy.RunningSpeed == 0 then 0 else sy.RunSpeedMin.toUInt8 }

/-- one frame of the horizontal state -/
def hstep (sy : Syms) (m0 : Machine) (s : HS) (i : HIn) : HS := hstepN sy m0 s (norm i)

/-- moving directions that fit the speed: its sign, or anything when it is 0 -/
def mds (v : UInt8) : List UInt8 := if v == 0 then [0, 1, 2, 3] else if v < 0x80 then [1] else [2]
def facings : List UInt8 := [1, 2, 3]
def rsVals (sy : Syms) : List UInt8 := [0, sy.RunSpeedMin.toUInt8]

def inD (sy : Syms) (s : HS) : Bool :=
  inSpeed sy s.v && facings.contains s.fd && (mds s.v).contains s.md && (rsVals sy).contains s.rs

/-- the inputs: start on the ground, start a jump, or in the air; every button set; the timer -/
def inputs : List HIn :=
  [((0 : UInt8), false), (0, true), (1, false)].flatMap fun (st, jump) =>
    groundInputs.flatMap fun joy => [(0 : UInt8), 1].map fun rt => { st, jump, joy, rt }

/-! ## The potential -/

def a0 (sy : Syms) (m : Machine) : Int := (romByte m sy.FrictionData).toNat
def a1 (sy : Syms) (m : Machine) : Int := (romByte m (sy.FrictionData + 1)).toNat
/-- the charge for `facing ≠ moving` -/
def c (sy : Syms) (m : Machine) : Int := 2 * a0 sy m - 2 * a1 sy m
def gSlow (sy : Syms) (m : Machine) : Int := 2 * a1 sy m
def gFast (sy : Syms) (m : Machine) : Int := amax sy m

def V (s : HS) : Int := 256 * sbyte s.v + s.f.toNat
def w (sy : Syms) (m : Machine) (s : HS) : Int :=
  if s.md == 1 || s.md == 2 then (if s.fd == s.md then 0 else c sy m)
  else if s.md == 0 then c sy m else 2 * c sy m
def phi (sy : Syms) (m : Machine) (s : HS) : Int := ((V s).natAbs : Int) + w sy m s

def slow (sy : Syms) (s : HS) : Bool := s.rs == 0 && decide ((sbyte s.v).natAbs < sy.AirFastSpeed.toNat)

def stepOk (sy : Syms) (m : Machine) (s : HS) (i : HIn) : Bool :=
  let t := hstep sy m s i
  inD sy t && decide (phi sy m t ≤ phi sy m s + gFast sy m) &&
    (!slow sy s || decide (phi sy m t ≤ phi sy m s + gSlow sy m)) &&
    (t.rs == 0 || s.rs != 0 || decide ((sbyte s.v).natAbs ≥ sy.RunSpeedMin.toNat))

/-- the states with facing direction `fd` -/
def statesFd (sy : Syms) (fd : UInt8) : List HS :=
  (speedsB sy).flatMap fun v => bytes.flatMap fun f => (mds v).flatMap fun md =>
    (rsVals sy).map fun rs => { v, f, fd, md, rs }

/-- the normalized inputs -/
def inputsN : List HIn := (inputs.map norm).eraseDups

/-- every state with facing direction `fd`, every normalized input -/
def potCheck (sy : Syms) (m : Machine) (fd : UInt8) : Bool :=
  (statesFd sy fd).all fun s => inputsN.all (stepOk sy m s)

/-- `norm` is idempotent on the inputs -/
def normIdem : Bool := inputs.all fun i => norm (norm i) == norm i

/-! ## From the check to bounds on the speed and the distance

`J s p`: `s` is in the domain, `Φ ≤ p`, and `RunningSpeed ≠ 0` only once `p ≥ θ`
(`θ = 256·AirFastSpeed − 255`: below it `|v|` is under the air threshold). While `p < θ` every
state is slow, so one frame raises the bound by `g_slow`; after that by `g_fast`. -/

def theta (sy : Syms) : Int := 256 * (sy.AirFastSpeed.toNat : Int) - 255

/-- the bound on `Φ` one frame later -/
def nxt (sy : Syms) (m : Machine) (p : Int) : Int := p + (if p < theta sy then gSlow sy m else gFast sy m)

/-- the bound after `k` frames -/
def iterN (sy : Syms) (m : Machine) : Int → Nat → Int
  | p, 0 => p
  | p, k + 1 => iterN sy m (nxt sy m p) k

def hrun (sy : Syms) (m : Machine) (s : HS) (is : List HIn) : HS := is.foldl (hstep sy m) s

/-- how far `P` moves in the frames, in the open area: `16·v` per frame with the new speed -/
def hdist (sy : Syms) (m : Machine) : HS → List HIn → Int
  | _, [] => 0
  | s, i :: rest => 16 * sbyte (hstep sy m s i).v + hdist sy m (hstep sy m s i) rest

/-- the bound on the distance of `n` frames, from `Φ ≤ p` -/
def dbound (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * min (top sy : Int) (nxt sy m p / 256) + dbound sy m (nxt sy m p) n

def J (sy : Syms) (m : Machine) (s : HS) (p : Int) : Prop :=
  inD sy s = true ∧ phi sy m s ≤ p ∧ (s.rs ≠ 0 → theta sy ≤ p)

/-- what the computation provides -/
structure Facts (sy : Syms) (m : Machine) : Prop where
  check : ∀ s, inD sy s = true → ∀ i ∈ inputs, stepOk sy m s i = true
  c_nonneg : 0 ≤ c sy m
  gs_nonneg : 0 ≤ gSlow sy m
  gf_nonneg : 0 ≤ gFast sy m
  air_le_run : sy.AirFastSpeed.toNat ≤ sy.RunSpeedMin.toNat

theorem w_nonneg {sy : Syms} {m : Machine} (F : Facts sy m) (s : HS) : 0 ≤ w sy m s := by
  have := F.c_nonneg
  unfold w; split <;> (try split) <;> omega

theorem phi_ge {sy : Syms} {m : Machine} (F : Facts sy m) (s : HS) :
    ((V s).natAbs : Int) ≤ phi sy m s := by
  have := w_nonneg F s
  unfold phi; omega

/-- one frame keeps `J` with the next bound; the new speed is at most `nxt p / 256` and `top` -/
theorem step_J {sy : Syms} {m : Machine} (F : Facts sy m) {s : HS} {p : Int} (hJ : J sy m s p)
    {i : HIn} (hi : i ∈ inputs) :
    J sy m (hstep sy m s i) (nxt sy m p) ∧ 256 * sbyte (hstep sy m s i).v ≤ nxt sy m p ∧
      sbyte (hstep sy m s i).v ≤ (top sy : Int) := by
  obtain ⟨hD, hphi, hrs⟩ := hJ
  have h := F.check s hD i hi
  generalize ht : hstep sy m s i = t at h ⊢
  simp only [stepOk, ht, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hDt, hfast⟩, hslow⟩, hrun⟩ := h
  have hDt' := hDt
  simp only [inD, inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hDt'
  have htop := hDt'.1.1.1
  have hpt := phi_ge F t
  have hps := phi_ge F s
  have hgs := F.gs_nonneg
  have hgf := F.gf_nonneg
  have har := F.air_le_run
  have hf : (0 : Int) ≤ (t.f.toNat : Int) := by omega
  have hVt : 256 * sbyte t.v ≤ ((V t).natAbs : Int) := by unfold V; omega
  have hVs : 256 * ((sbyte s.v).natAbs : Int) ≤ ((V s).natAbs : Int) + 255 := by
    have : s.f.toNat < 256 := s.f.toNat_lt
    unfold V; omega
  unfold nxt
  by_cases hp : p < theta sy
  · -- slow: `RunningSpeed = 0` and `|v|` under the threshold
    have hrs0 : s.rs = 0 := by
      by_cases hne : s.rs = 0
      · exact hne
      · have := hrs hne; omega
    have hv : (sbyte s.v).natAbs < sy.AirFastSpeed.toNat := by unfold theta at hp; omega
    have hsT : slow sy s = true := by
      simp only [slow, hrs0, Bool.and_eq_true, beq_self_eq_true, decide_eq_true_eq, true_and]; exact hv
    have hsl : phi sy m t ≤ phi sy m s + gSlow sy m := by
      rcases hslow with h0 | h0
      · rw [hsT] at h0; exact absurd h0 (by decide)
      · exact h0
    simp only [hp, if_true]
    refine ⟨⟨hDt, by omega, fun hne => ?_⟩, by omega, by omega⟩
    rcases hrun with (h0 | h0) | h0
    · exact absurd h0 hne
    · exact absurd hrs0 h0
    · omega
  · simp only [hp, if_false]
    refine ⟨⟨hDt, by omega, fun _ => by omega⟩, by omega, by omega⟩

/-- `J` after any frames -/
theorem run_J {sy : Syms} {m : Machine} (F : Facts sy m) :
    ∀ (is : List HIn) (s : HS) (p : Int), J sy m s p → (∀ i ∈ is, i ∈ inputs) →
      J sy m (hrun sy m s is) (iterN sy m p is.length)
  | [], _, _, hJ, _ => hJ
  | i :: rest, s, p, hJ, his =>
    run_J F rest _ _ (step_J F hJ (his i (by simp))).1 (fun j hj => his j (by simp [hj]))

/-- the distance is at most `dbound` -/
theorem dist_le {sy : Syms} {m : Machine} (F : Facts sy m) :
    ∀ (is : List HIn) (s : HS) (p : Int), J sy m s p → (∀ i ∈ is, i ∈ inputs) →
      hdist sy m s is ≤ dbound sy m p is.length
  | [], _, _, _, _ => by simp [hdist, dbound]
  | i :: rest, s, p, hJ, his => by
    obtain ⟨hJ', h256, htop⟩ := step_J F hJ (his i (by simp))
    have ih := dist_le F rest _ _ hJ' (fun j hj => his j (by simp [hj]))
    simp only [hdist, dbound]
    have : sbyte (hstep sy m s i).v ≤ nxt sy m p / 256 := by omega
    omega

theorem le_nxt {sy : Syms} {m : Machine} (F : Facts sy m) (p : Int) : p ≤ nxt sy m p := by
  have := F.gs_nonneg; have := F.gf_nonneg
  unfold nxt; split <;> omega

/-- once the bound reaches the top speed, each frame adds `16·top` -/
theorem dbound_top {sy : Syms} {m : Machine} (F : Facts sy m) :
    ∀ (n : Nat) (p : Int), 256 * (top sy : Int) ≤ nxt sy m p → dbound sy m p n = 16 * (top sy : Int) * n
  | 0, _, _ => by simp [dbound]
  | n + 1, p, hp => by
    have ih := dbound_top F n (nxt sy m p) (Int.le_trans hp (le_nxt F _))
    have hq : min (top sy : Int) (nxt sy m p / 256) = top sy := by omega
    simp only [dbound]
    rw [ih, hq]
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

theorem dbound_add {sy : Syms} {m : Machine} :
    ∀ (k n : Nat) (p : Int), dbound sy m p (k + n) = dbound sy m p k + dbound sy m (iterN sy m p k) n
  | 0, n, p => by simp [dbound, iterN]
  | k + 1, n, p => by
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [dbound, iterN]
    rw [dbound_add k n (nxt sy m p)]
    omega

/-- the closed form past `K` frames -/
theorem dbound_closed {sy : Syms} {m : Machine} (F : Facts sy m) (p : Int) (K : Nat)
    (hK : 256 * (top sy : Int) ≤ nxt sy m (iterN sy m p K)) (n : Nat) :
    dbound sy m p (K + n) = dbound sy m p K + 16 * (top sy : Int) * n := by
  rw [dbound_add, dbound_top F n _ hK]

/-! ## The check covers every state of the domain -/

theorem mem_bytes (b : UInt8) : b ∈ bytes :=
  List.mem_map.2 ⟨b.toNat, List.mem_range.2 b.toNat_lt, by simp⟩

/-- every speed in range is in `speedsB` (checked over all bytes) -/
def speedsComplete (sy : Syms) : Bool := bytes.all fun v => !inSpeed sy v || (speedsB sy).contains v

theorem stepOk_norm {sy : Syms} {m : Machine} (s : HS) (i : HIn) (h : norm (norm i) = norm i) :
    stepOk sy m s (norm i) = stepOk sy m s i := by
  unfold stepOk hstep; rw [h]

theorem check_of {sy : Syms} {m : Machine} (hsp : speedsComplete sy = true) (hn : normIdem = true)
    (h1 : potCheck sy m 1 = true) (h2 : potCheck sy m 2 = true) (h3 : potCheck sy m 3 = true) :
    ∀ s, inD sy s = true → ∀ i ∈ inputs, stepOk sy m s i = true := by
  intro s hD i hi
  obtain ⟨v, f, fd, md, rs⟩ := s
  simp only [inD, Bool.and_eq_true, List.contains_iff_mem] at hD
  obtain ⟨⟨⟨hv, hfd⟩, hmd⟩, hrs⟩ := hD
  have hvs : v ∈ speedsB sy := by
    simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_iff_mem] at hsp
    rcases hsp v (mem_bytes v) with h | h
    · rw [h] at hv; exact absurd hv (by decide)
    · exact h
  have hmem : ({ v, f, fd, md, rs } : HS) ∈ statesFd sy fd :=
    List.mem_flatMap.2 ⟨v, hvs, List.mem_flatMap.2 ⟨f, mem_bytes f,
      List.mem_flatMap.2 ⟨md, hmd, List.mem_map.2 ⟨rs, hrs, rfl⟩⟩⟩⟩
  have hall : potCheck sy m fd = true := by
    simp only [facings, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with h | h | h <;> subst h
    · exact h1
    · exact h2
    · exact h3
  simp only [potCheck, List.all_eq_true] at hall
  have hin : norm i ∈ inputsN := List.mem_eraseDups.2 (List.mem_map.2 ⟨i, hi, rfl⟩)
  have hid : norm (norm i) = norm i := by
    simp only [normIdem, List.all_eq_true, beq_iff_eq] at hn
    exact hn i hi
  rw [← stepOk_norm _ i hid]
  exact hall _ hmem _ hin

/-- the horizontal state of the 1-1 start -/
def startHS (sy : Syms) (ctx : Machine) : HS :=
  let p := PState.read sy ctx
  { v := p.speed, f := p.fricMF, fd := p.faceDir, md := p.movDir,
    rs := if p.runSpd == 0 then 0 else sy.RunSpeedMin.toUInt8 }

/-- the first `K` after which every frame adds `16·top` -/
def openK (sy : Syms) (m : Machine) (p : Int) : Nat := Id.run do
  let mut k := 0
  let mut q := p
  while k < 1000 && nxt sy m q < 256 * (top sy : Int) do
    q := nxt sy m q
    k := k + 1
  return k

end Smbrta.Potential
