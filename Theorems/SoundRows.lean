import Theorems.StepWrites

/-!
# Rows of a change with the sound's bytes in tables

The rows of a change (`SideChangeEnd.Row`) are states of the frames after the pipe, one row for each value of `left`. Here the rows forget the sound's bytes outside the
sound routine, and each row carries two tables of states of these bytes (`StepWrites.Ph`): before the call of the routine, and after its return. At the call a state is
split by the first table and the routine is walked with the bytes known; at the return the bytes must be in the second table, and they are forgotten (`StepWrites.tsuccs`).
At the frame's end the table that holds is in the next row's first table. This is the method of `SideChangeSound`, for any rows: `chainS` checks the frames, `chain_stepS`
is one frame in the rows, `ctl_of_zeroS` is control where `left` is 0. A machine in the last row, with the bytes of a state of its table, is covered by the state with these
bytes (`covered_refine`): `ctlRow` lists these states. The search here keeps the states at dot 0 apart, as the frames after a pipe's exit need (`ysearchS`); it is no part of
the proof. There is no game data in this file.
-/

namespace Smbrta.SoundRows

open TaintRun (AS Env AB AM Sim aRows coverIn sim_le walkFuel bitList Search keyOf)
open SideChangeEnd (Row Ctx rowCfg rowEnv statesOK InvL Covered mOf normD sim_normD nextStatesD coreFrame noStart noStartPad two_le sim_pad sim_unpad
  core_of_known left_of_covered)
open StepWrites (Rt SState SIn entails tabOK Ph twalk tsuccs tframe_of_walk retag forgetAll aLocs keepOK joinUnder sIn_entails refineAll agrees)
open PipeTransition (frame)

/-! ## The search: no part of the proof -/

/-- the key of the search: a state at dot 0 stays apart, since the next tick decides the vblank flag; `dg` stays apart -/
def ykey (E : Env) (keep : List Nat) (A : AS) : Nat :=
  ((SideChangeEnd.xkey E keep A * 2 + (if A.lo == 0 then 1 else 0)) * 2 + (if A.dg then 1 else 0)) * 4096 + A.log.headD 0 % 4096

def yroute (E : Env) (keep : List Nat) (X : Search) (B : AS) : Search :=
  let K := ykey E keep B
  match X.pending[K]? with
  | some P => { X with pending := X.pending.insert K (P.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
  | none => { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

/-- the search for a frame with the step `step`: one step at a time, in the order of the key. A state at a place of `hold` waits there, joined with the others by its key,
until no other state is pending; then the waiting states go on, turned by `norm`. From a state at a place of `alone`, each path goes on alone, with no joins, up to a place of
`hold` or the frame's end. -/
partial def yloop (step : AS → List (Option AS)) (E : Env) (keep : List Nat) (hold alone : UInt16 → Bool) (norm : AS → AS) (limit : Nat) (X0 : Search) : Search := Id.run do
  let mut X := X0
  let mut c := 0
  let mut held : Std.HashMap Nat AS := {}
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none =>
      if held.isEmpty then break
      for (_, A) in held.toList do
        X := yroute E keep X (norm A)
        X := { X with inN := X.inN.insert (ykey E keep (norm A)) 2 }
      held := {}
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      c := c + 1
      if n ≥ 2 || c % 64 == 0 then X := { X with out := X.out.push A }
      if alone A.pc then
        let mut todo : List AS := [A]
        while !todo.isEmpty && X.steps ≤ limit do
          let B := todo.head!
          todo := todo.tail!
          let rs := step B
          X := { X with steps := X.steps + rs.length }
          if rs.any (·.isNone) then
            X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some B }
          for b in rs.filterMap id do
            if b.k != B.k then X := { X with ends := X.ends.push b }
            else if hold b.pc then
              let K := ykey E keep (norm b)
              held := held.insert K (match held[K]? with
                | some P => P.join b
                | none => b)
            else todo := b :: todo
      else
        let rs := step A
        X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
        if rs.any (·.isNone) then
          X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A }
        for b in rs.filterMap id do
          if b.k != A.k then X := { X with ends := X.ends.push b }
          else if hold b.pc then
            let K := ykey E keep (norm b)
            held := held.insert K (match held[K]? with
              | some P => P.join b
              | none => b)
          else X := yroute E keep X b
  return X

def ysearchS (step : AS → List (Option AS)) (E : Env) (keep : List Nat) (R : List AS) (hold : UInt16 → Bool := fun _ => false) (alone : UInt16 → Bool := fun _ => false)
    (norm : AS → AS := id) (limit : Nat := 8000000) : Search :=
  yloop step E keep hold alone norm limit (R.foldl (yroute E keep) {})

/-- for the search: at the call of the routine the tag of the start state is dropped, so that the states of all starts join there; at the return the registers are
forgotten. The check holds whatever the search does; this only joins paths. -/
def atRet (R : Rt) (A : AS) : AS :=
  if A.pc == R.call then { A with a := AB.top, x := AB.top, y := AB.top, p := AB.top, log := [] }
  else if A.pc == R.ret then { A with a := AB.top, x := AB.top, y := AB.top, p := AB.top, log := [] } else A

/-- what the search of a frame gives: the writes to the routine's bytes outside it before the return and after it, the routine's bytes at the returns, the states of the search,
and the states at the frame's end -/
structure Scan where
  wb : List SState
  wa : List SState
  rets : List SState
  out : Array AS
  ends : List AS
  fails : Nat

/-- the frame's search with the call split by `T`, and nothing asked at the return or of a write outside the routine (as `SideChangeSound.scan`, with `ysearchS`). Its states
are those of the walk with `tsuccs` when the walk does not fail, so they serve as its table. -/
def scan (E : Env) (R : Rt) (keep : List Nat) (T : List SState) (Rs : List AS) : Scan := Id.run do
  let ops := (aRows E).toArray
  let mark := fun (tag : Nat) (B : AS) => ({ B with k := B.k + 1, log := [tag] } : AS)
  let P : Nat → Bool := fun i => R.SB.contains i
  let step := fun (A : AS) =>
    let rs := if R.inR A.pc || A.pc == R.call then tsuccs E ops R T [[]] A
      else (SideChangeEnd.xsuccs E ops A).map (·.map (retag A.spent))
    let extra : List AS :=
      if R.inR A.pc then (SideChangeEnd.xsuccs E ops A).filterMap fun o => o.bind fun B => if B.pc == R.ret && B.k == A.k then some (mark 1 B) else none
      else if A.pc != R.call && !keepOK E P A then [mark 2 A]
      else []
    rs ++ extra.map some
  -- each start state in the idle loop goes alone up to the call (its tag is in the search's key), so that the forms of the screen buffer are not joined; a start state in
  -- the middle of a routine joins the others, so that a loop's turns join
  let starts := Rs.zipIdx.map fun p =>
    if TaintRun.isIdle E p.1.pc (E.prg.get! (p.1.pc &&& E.mask).toNat) then ({ p.1 with log := [100 + p.2] } : AS) else p.1
  let X := ysearchS step E keep starts (fun pc => pc == R.ret || pc == R.call) (fun pc => pc == R.call) (atRet R)
  let mut wb : List SState := []
  let mut wa : List SState := []
  let mut rets : List SState := []
  let mut ends : List AS := []
  for Z in X.ends do
    if Z.log == [1] then
      let u : SState := R.SB.map fun i => (i, Z.getK i)
      if !rets.contains u then rets := rets ++ [u]
    else if Z.log == [2] then
      let A := ({ Z with k := Z.k - 1, log := [] } : AS)
      match aLocs E A with
      | some L =>
        for o in SideChangeEnd.xsuccs E ops A do
          match o with
          | some B =>
            let w : SState := (L.filter fun i => R.SB.contains i).map fun i => (i, B.getK i)
            if A.spent then
              if !wa.contains w then wa := wa ++ [w]
            else if !wb.contains w then wb := wb ++ [w]
          | none => pure ()
      | none => pure ()
    else ends := Z :: ends
  return { wb, wa, rets, out := X.out, ends := ends.reverse, fails := X.fails }

/-! ## Rows with tables -/

/-- a row, with the tables of its frame: the routine's bytes are in a state of `T0` before the call, and of `T1` after the return -/
structure SRow where
  row : Row
  T0 : List SState
  T1 : List SState

/-- the index of a table of states, as `SideChangeEnd.rowsFrom` makes it -/
def indexOf (E : Env) (keep : List Nat) (t : Array AS) : Std.HashMap Nat (List Nat) × ByteArray :=
  let P := t.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyOf E keep A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  (P.1, P.2.1)

/-- `left` on the first state -/
def leftHead (c : Ctx) (R : List AS) : Nat := (R.head?.map (fun S => c.left (mOf S))).getD 0

/-- the states after the frame's end, as `nextStatesD`, and states that the search keeps apart joined -/
def afterEnds (c : Ctx) (last : Bool) (ends : List AS) : List AS :=
  let R := (nextStatesD c.E last ends).map (retag false)
  let m : Std.HashMap Nat AS := R.foldl (fun (h : Std.HashMap Nat AS) A =>
    let k := ykey c.E c.keep A
    match h[k]? with
    | some B => h.insert k (B.join A)
    | none => h.insert k A) {}
  m.values

/-- the rows from the states `Rs` and the table `T`, for `n` frames. For each frame: the writes before the return are joined into `T` (the first table), the bytes at the
returns, turned by `grp`, with the writes after them make the second table, and the states of the search are the table of the walk. The next table holds the first table if a path
of the frame does not come to the return, and the second if one does. `grp k` may join states of the second table of the frame with `k` frames left, and so forget what later frames
do not read; the check decides. -/
def rowsFromS (c : Ctx) (R : Rt) (grp : Nat → List SState → List SState) : Nat → List AS → List SState → List SRow
  | 0, Rs, T => [{ row := { core := false, R := Rs, v := leftHead c Rs, t := #[], idx := {}, cut := ByteArray.empty }, T0 := T, T1 := [] }]
  | n + 1, Rs, T =>
    let core := Rs.any fun S => coreFrame c.sy c.eng (mOf S)
    let e : Env := if core then { c.E with pad := noStartPad } else c.E
    let s1 := scan e R c.keep T Rs
    let T0 := joinUnder s1.wb T
    let s2 := if s1.wb.isEmpty then s1 else scan e R c.keep T0 Rs
    let T1 := joinUnder s2.wa (grp (n + 1) s2.rets)
    let I := indexOf e c.keep s2.out
    let ends := s2.ends
    { row := { core, R := Rs, v := leftHead c Rs, t := s2.out, idx := I.1, cut := I.2 }, T0, T1 } ::
      rowsFromS c R grp n (afterEnds c (n == 0) ends)
        ((if ends.any (!·.spent) then T0 else []) ++ (if ends.any (·.spent) then T1 else []))

/-! ## The check of the rows -/

/-- every state of `T` is in a state of `T'` -/
def incl (T T' : List SState) : Bool := T.all fun t => T'.any (entails t)

/-- at the frame's end: a state of the next row, and the table that holds there (the first before the return, the second after it) is in the next row's first table -/
def finS (D : List Nat) (inc0 inc1 : Bool) (R' : List AS) (B : AS) : Bool :=
  !B.rk && (if B.spent then inc1 else inc0) && R'.any fun S => (normD D ({ B with k := 0, spent := false } : AS)).le S

/-- a frame from a row to the next -/
def linkS (c : Ctx) (R : Rt) (r r' : SRow) : Bool :=
  let C := rowCfg c r.row
  let fin := finS c.E.D (incl r.T0 r'.T0) (incl r.T1 r'.T0) r'.row.R
  statesOK c r.row && statesOK c r'.row && decide (r.row.v ≤ r'.row.v + 1) && tabOK R.SB r.T0 && tabOK R.SB r.T1 &&
    C.t.all (twalk C R r.T0 r.T1 fin walkFuel) && r.row.R.all (twalk C R r.T0 r.T1 fin walkFuel)

/-- all the frames: `left` is 0 at the last row, whose first table has bytes of the routine only -/
def chainS (c : Ctx) (R : Rt) : List SRow → Bool
  | [] => true
  | [r] => statesOK c r.row && r.row.v == 0 && tabOK R.SB r.T0
  | r :: r' :: t => linkS c R r r' && chainS c R (r' :: t)

section
variable {c : Ctx} {R : Rt}

/-- a machine is in a row: a state of the row covers it, and the routine's bytes are in a state of the row's first table (`Ph`) -/
def CoveredS (c : Ctx) (R : Rt) (r : SRow) (m : Machine) : Prop := ∃ S ∈ r.row.R, Sim c.E (m.frame, 2) S m ∧ Ph R r.T0 r.T1 S m

theorem sIn_incl {T T' : List SState} (h : incl T T' = true) {t : SState} (ht : t ∈ T) {m : Machine} (hm : SIn t m) : ∃ t' ∈ T', SIn t' m := by
  obtain ⟨t', ht', he⟩ := List.any_eq_true.1 (List.all_eq_true.1 h t ht)
  exact ⟨t', ht', sIn_entails hm he⟩

/-- at the frame's end `Ph` goes over to the next row's first table -/
theorem ph_next {T0 T1 T0' T1' : List SState} {B D : AS} {m : Machine} (hp : Ph R T0 T1 B m) (hpc : B.pc = D.pc) (hsp : D.spent = false)
    (h0 : B.spent = false → incl T0 T0' = true) (h1 : B.spent = true → incl T1 T0' = true) : Ph R T0' T1' D m := by
  rcases hp with h | ⟨hs, t, ht, hm⟩ | ⟨hs, t, ht, hm⟩
  · left
    rw [← hpc]
    exact h
  · obtain ⟨t', ht', hm'⟩ := sIn_incl (h0 hs) ht hm
    exact Or.inr (Or.inl ⟨hsp, t', ht', hm'⟩)
  · obtain ⟨t', ht', hm'⟩ := sIn_incl (h1 hs) ht hm
    exact Or.inr (Or.inl ⟨hsp, t', ht', hm'⟩)

theorem normD_pc (D : List Nat) (B : AS) : (normD D B).pc = B.pc := by
  unfold normD
  split <;> rfl

theorem normD_spent (D : List Nat) (B : AS) : (normD D B).spent = B.spent := by
  unfold normD
  split <;> rfl

/-- **A frame from a row to the next.** -/
theorem link_frameS (hE : c.E.pad = AB.top) {r r' : SRow} (h : linkS c R r r' = true) {m : Machine} (hc : CoveredS c R r m) {i : UInt8}
    (hi : coreFrame c.sy c.eng m = true → noStart i = true) : CoveredS c R r' (frame m i) := by
  simp only [linkS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, _⟩, _⟩, ht0⟩, ht1⟩, h4⟩, h5⟩ := h
  obtain ⟨S, hS, hs, hp⟩ := hc
  have h1' := h1
  simp only [statesOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true] at h1'
  obtain ⟨⟨⟨⟨⟨_, _⟩, a3⟩, _⟩, _⟩, a6⟩ := h1' S hS
  have hs1 : Sim (rowCfg c r.row).E (m.frame, 2) S { m with pad := smbToPad i } := by
    show Sim (rowEnv c r.row) (m.frame, 2) S { m with pad := smbToPad i }
    unfold rowEnv
    split
    · rename_i hcore
      apply sim_pad hs
      have hcf : coreFrame c.sy c.eng (mOf S) = true := by
        rcases a6 with a6 | a6
        · rw [hcore] at a6
          cases a6
        · exact a6
      have hn := hi (core_of_known hs a3 hcf)
      have e : smbToPad i &&& 0x08 = 0 := by simpa [noStart] using hn
      show smbToPad i &&& 0x08 = 0 &&& 0x08
      rw [e]
      rfl
    · exact { hs with pad := by rw [hE]; exact TaintRun.mem_top _ }
  obtain ⟨_, B, g2, _, g4, g5⟩ := tframe_of_walk (C := rowCfg c r.row) (F := (m.frame, 2)) h4 rfl two_le ht0 ht1 (List.all_eq_true.1 h5 S hS) hs1 hp
  have g4' : Sim c.E (m.frame, 2) B (frame m i) := by
    have e4 : Sim (rowEnv c r.row) (m.frame, 2) B (frame m i) := g4
    unfold rowEnv at e4
    split at e4
    · exact sim_unpad hE e4
    · exact e4
  simp only [finS, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at g2
  obtain ⟨⟨hrk, hinc⟩, D, hD, hle⟩ := g2
  have hbase : Sim c.E ((frame m i).frame, 2) ({ B with k := 0, spent := false } : AS) (frame m i) := by
    refine { g4' with fr := ?_, rkv := ?_ }
    · show (frame m i).frame = (frame m i).frame + 0
      rfl
    · intro hr2
      have : B.rk = true := hr2
      rw [hrk] at this
      cases this
  have hps := StepWrites.le_pc_spent hle
  rw [normD_pc, normD_spent] at hps
  refine ⟨D, hD, sim_le hle (sim_normD hbase), ph_next g5 hps.1 hps.2.symm (fun h0 => ?_) (fun h1 => ?_)⟩
  · rw [h0] at hinc
    simpa using hinc
  · rw [h1] at hinc
    simpa using hinc

/-- a machine is in one of the rows -/
def InvS (c : Ctx) (R : Rt) : List SRow → Machine → Prop
  | [], _ => False
  | r :: t, m => CoveredS c R r m ∨ InvS c R t m

theorem left_of_coveredS {r : SRow} {m : Machine} (hr : statesOK c r.row = true) (h : CoveredS c R r m) : c.left m = r.row.v := by
  obtain ⟨S, hS, hs, _⟩ := h
  exact left_of_covered hr ⟨S, hS, hs⟩

/-- **A frame in the rows.** `left` is 0 already, or the machine stays in the rows and `left` falls by at most one. -/
theorem chain_stepS (hE : c.E.pad = AB.top) : ∀ (l : List SRow), chainS c R l = true → ∀ {m : Machine}, InvS c R l m → ∀ {i : UInt8},
    (coreFrame c.sy c.eng m = true → noStart i = true) → c.left m = 0 ∨ (InvS c R l (frame m i) ∧ c.left m ≤ c.left (frame m i) + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ m h
    cases h
  | cons r t ih =>
    intro hl m h i hi
    cases t with
    | nil =>
      simp only [chainS, Bool.and_eq_true, beq_iff_eq] at hl
      rcases h with h | h
      · left
        rw [left_of_coveredS hl.1.1 h, hl.1.2]
      · cases h
    | cons r2 t2 =>
      simp only [chainS, Bool.and_eq_true] at hl
      obtain ⟨h1, h2⟩ := hl
      rcases h with h | h
      · right
        have hn := link_frameS hE h1 h hi
        refine ⟨Or.inr (Or.inl hn), ?_⟩
        simp only [linkS, Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, _⟩, _⟩, _⟩ := h1
        rw [left_of_coveredS a1 h, left_of_coveredS a2 hn]
        exact a3
      · rcases ih h2 h hi with h3 | ⟨h3, h4⟩
        · exact Or.inl h3
        · exact Or.inr ⟨Or.inr h3, h4⟩

theorem states_of_chainS : ∀ (l : List SRow), chainS c R l = true → ∀ r ∈ l, statesOK c r.row = true
  | [], _, r, hr => by cases hr
  | [r0], h, r, hr => by
    simp only [chainS, Bool.and_eq_true] at h
    rw [List.mem_singleton] at hr
    rw [hr]
    exact h.1.1
  | r0 :: r1 :: t, h, r, hr => by
    simp only [chainS, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hr with e | hr
    · rw [e]
      simp only [linkS, Bool.and_eq_true] at h1
      obtain ⟨⟨⟨⟨⟨⟨a1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h1
      exact a1
    · exact states_of_chainS (r1 :: t) h2 r hr

/-- the rows without their tables are rows of `SideChangeEnd` -/
theorem invL_of_invS : ∀ {l : List SRow} {m : Machine}, InvS c R l m → InvL c (l.map (·.row)) m
  | [], _, h => by cases h
  | r :: t, m, h => by
    rcases h with ⟨S, hS, hs, _⟩ | h
    · exact Or.inl ⟨S, hS, hs⟩
    · exact Or.inr (invL_of_invS h)

/-- **Control where `left` is 0**, in rows that pass `zeroCtl` -/
theorem ctl_of_zeroS {sy : Syms} {l : List SRow} (hl : chainS c R l = true) (hz : SideChangeEnd.zeroCtl sy (l.map (·.row)) = true) {m : Machine} (h : InvS c R l m)
    (h0 : c.left m = 0) : controllable sy m = true := by
  refine SideChangeEnd.ctl_of_zero (fun r hr => ?_) hz (invL_of_invS h) h0
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
  exact states_of_chainS l hl r0 hr0

/-- the first row of the rows from `Rs` has the states `Rs` -/
theorem rowsFromS_head (grp : Nat → List SState → List SState) (n : Nat) (Rs : List AS) (T : List SState) :
    ∃ r t, rowsFromS c R grp n Rs T = r :: t ∧ r.row.R = Rs := by
  cases n with
  | zero => exact ⟨_, _, rfl, rfl⟩
  | succ n => exact ⟨_, _, rfl, rfl⟩

/-- the first table of the first row holds `T` -/
def headIncl (l : List SRow) (T : List SState) : Bool :=
  match l with
  | r :: _ => incl T r.T0
  | [] => false

/-- a machine of the first states, with the routine's bytes in a state of `T`, is in the rows -/
theorem inv_headS (grp : Nat → List SState → List SState) (n : Nat) (Rs : List AS) (T : List SState) (hh : headIncl (rowsFromS c R grp n Rs T) T = true) {m : Machine} {S : AS}
    (hS : S ∈ Rs) (hs : Sim c.E (m.frame, 2) S m) (hsp : S.spent = false) {t : SState} (ht : t ∈ T) (hm : SIn t m) : InvS c R (rowsFromS c R grp n Rs T) m := by
  obtain ⟨r, l, e, hr⟩ := rowsFromS_head (c := c) (R := R) grp n Rs T
  rw [e] at hh ⊢
  simp only [headIncl] at hh
  obtain ⟨t', ht', hm'⟩ := sIn_incl hh ht hm
  exact Or.inl ⟨S, by rw [hr]; exact hS, hs, Or.inr (Or.inl ⟨hsp, t', ht', hm'⟩)⟩

/-! ## The last row with its table: the states with the sound's bytes -/

/-- the states of a row, each with the bytes of each state of the row's first table that agrees with it, when the state is not in the routine and the routine has not
returned: the machines of the row are covered by these states (`covered_refine`) -/
def refineRow (R : Rt) (r : SRow) : List AS :=
  r.row.R.flatMap fun S => if R.inR S.pc || S.spent then [S] else r.T0.filterMap fun t => if agrees t S then some (refineAll t S) else none

/-- a row of `SideChangeEnd` with these states -/
def ctlRow (R : Rt) (r : SRow) : Row := { core := false, R := refineRow R r, v := r.row.v, t := #[], idx := {}, cut := ByteArray.empty }

/-- the rows where `left` is 0, each with its table, as rows of `SideChangeEnd` -/
def zeroRows (R : Rt) (l : List SRow) : List Row := (l.filter (·.row.v == 0)).map (ctlRow R)

/-- every byte of a table's state is in RAM -/
theorem lt_of_tabOK {SB : List Nat} {T : List SState} (h : tabOK SB T = true) {t : SState} (ht : t ∈ T) : ∀ p ∈ t, p.1 < 2048 := by
  intro p hp
  have := List.all_eq_true.1 (List.all_eq_true.1 h t ht) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

/-- **A machine of a row is covered by a state of the row with the bytes of the table** -/
theorem covered_refine {r : SRow} (ht : tabOK R.SB r.T0 = true) {m : Machine} (h : CoveredS c R r m) : Covered c (ctlRow R r) m := by
  obtain ⟨S, hS, hs, hp⟩ := h
  by_cases hq : (R.inR S.pc || S.spent) = true
  · exact ⟨S, List.mem_flatMap.2 ⟨S, hS, by rw [if_pos hq]; exact List.mem_singleton.2 rfl⟩, hs⟩
  · have hq' : R.inR S.pc = false ∧ S.spent = false := by simpa using hq
    rcases hp with h1 | ⟨_, t, htT, hm⟩ | ⟨h2, _⟩
    · rw [hq'.1] at h1
      cases h1
    · have hlt := lt_of_tabOK ht htT
      have hag : agrees t S = true := StepWrites.agrees_of hs hlt hm
      refine ⟨refineAll t S, List.mem_flatMap.2 ⟨S, hS, ?_⟩, StepWrites.sim_refineAll t hs hm⟩
      rw [if_neg hq]
      exact List.mem_filterMap.2 ⟨t, htT, by rw [if_pos hag]⟩
    · rw [hq'.2] at h2
      cases h2

theorem tab_of_chainS : ∀ (l : List SRow), chainS c R l = true → ∀ r ∈ l, tabOK R.SB r.T0 = true
  | [], _, r, hr => by cases hr
  | [r0], h, r, hr => by
    simp only [chainS, Bool.and_eq_true] at h
    rw [List.mem_singleton] at hr
    rw [hr]
    exact h.2
  | r0 :: r1 :: t, h, r, hr => by
    simp only [chainS, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hr with e | hr
    · rw [e]
      simp only [linkS, Bool.and_eq_true] at h1
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, a4⟩, _⟩, _⟩, _⟩ := h1
      exact a4
    · exact tab_of_chainS (r1 :: t) h2 r hr

theorem mem_of_invS : ∀ {l : List SRow} {m : Machine}, InvS c R l m → ∃ r ∈ l, CoveredS c R r m
  | [], _, h => by cases h
  | r :: t, _, h => by
    rcases h with h | h
    · exact ⟨r, List.mem_cons_self, h⟩
    · obtain ⟨r', hr', h'⟩ := mem_of_invS h
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem invL_of_mem : ∀ {L : List Row} {r : Row}, r ∈ L → ∀ {m : Machine}, Covered c r m → InvL c L m
  | [], _, hr, _, _ => by cases hr
  | r0 :: t, r, hr, m, h => by
    rcases List.mem_cons.1 hr with e | hr
    · subst e
      exact Or.inl h
    · exact Or.inr (invL_of_mem hr h)

/-- **A machine in the rows with `left` 0 is in the rows `zeroRows`**: a state of a row where `left` is 0, with the bytes of a state of that row's table -/
theorem invL_zero {l : List SRow} (hl : chainS c R l = true) {m : Machine} (h : InvS c R l m) (h0 : c.left m = 0) : InvL c (zeroRows R l) m := by
  obtain ⟨r, hr, hc⟩ := mem_of_invS h
  have hv : r.row.v = 0 := by
    rw [← left_of_coveredS (states_of_chainS l hl r hr) hc]
    exact h0
  have hmem : ctlRow R r ∈ zeroRows R l := List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simp [hv]⟩, rfl⟩
  exact invL_of_mem hmem (covered_refine (tab_of_chainS l hl r hr) hc)

end

/-! ## The kinds of a table: what a machine's bytes must be -/

section

theorem bit_of_ne {v : UInt8} (h : v ≠ 0) : ∃ b ∈ bitList, v &&& b = b := by
  have hj : ∃ j, j < 8 ∧ TaintRun.bt v j = true := by
    apply Classical.byContradiction
    intro hno
    apply h
    apply TaintRun.bt_ext
    intro i hi
    rw [TaintRun.bt_zero hi]
    cases hc : TaintRun.bt v i with
    | true => exact absurd ⟨i, hi, hc⟩ hno
    | false => rfl
  obtain ⟨j, hj8, hjb⟩ := hj
  obtain ⟨b, hbm, hbb⟩ := TaintRun.bit_list ⟨j, hj8⟩
  refine ⟨b, hbm, TaintRun.bt_ext fun i hi => ?_⟩
  rw [TaintRun.bt_and, hbb ⟨i, hi⟩]
  by_cases hij : i = j
  · subst hij
    simp [hjb]
  · simp [hij]

theorem mem_eq {w v : UInt8} (h : w = v) : (AB.known v).mem w := by
  rw [h]
  exact TaintRun.mem_known_self v

theorem sIn_append {a b : SState} {m : Machine} (h1 : SIn a m) (h2 : SIn b m) : SIn (a ++ b) m := fun p hp =>
  (List.mem_append.1 hp).elim (h1 p) (h2 p)

/-- the bytes of a row of exact values, as a state of a table -/
def ofRow (q : List (Nat × UInt8)) : SState := q.map fun p => (p.1, AB.known p.2)

theorem sIn_ofRow {q : List (Nat × UInt8)} {m : Machine} (h : ∀ p ∈ q, m.ram.get! p.1 = p.2) : SIn (ofRow q) m := by
  intro p hp
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
  exact mem_eq (h p0 hp0)

end

end Smbrta.SoundRows
