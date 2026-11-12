import Theorems.SideChangeEnd

/-!
# The sound routine as one step

The rows of `SideChangeEnd` run the sound routine instruction by instruction. With the song not known they fail there. This file looks at a call of the sound
routine alone: from its entry to its return, with the sound's bytes not known. It has no theorem: it holds what the program `sound-check` uses, the list of the
sound's bytes, pieces of a byte by its lowest bit that is 1 (`ctzPieces`, not proved), and a search that stops at the return (`ssearch`).
The finding (page `1-1/d-2-3-SideChangeEnd.md`): a summary of the call cannot hold for any values of the sound's bytes, since some values make the call never
return and others make it read a register; on the 207 sound states of real frames after the exit the walk from each state closes. There is no game data in this file.
-/

namespace Smbrta.SoundWalk

open TaintRun
open PipeTransitionAll (go Names asmValue)
open SideChangeBound (bytesOf)

/-! ## The sound's bytes -/

/-- the bytes of the sound routine: the queues, the buffers, the song's pointer, offsets and counters, the effects' counters, the pause's bytes -/
def soundNames : List (String × Nat × Nat) :=
  [("NoteLenLookupTblOfs", 0, 1), ("Square1SoundBuffer", 0, 1), ("Square2SoundBuffer", 0, 1), ("NoiseSoundBuffer", 0, 1), ("AreaMusicBuffer", 0, 1),
   ("MusicData", 0, 2), ("MusicOffset_Square2", 0, 1), ("MusicOffset_Square1", 0, 1), ("MusicOffset_Triangle", 0, 1), ("PauseSoundQueue", 0, 1),
   ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1), ("Square2SoundQueue", 0, 1), ("Square1SoundQueue", 0, 1),
   ("MusicOffset_Noise", 0, 1), ("EventMusicBuffer", 0, 1), ("PauseSoundBuffer", 0, 1), ("Squ2_NoteLenBuffer", 0, 1), ("Squ2_NoteLenCounter", 0, 1),
   ("Squ2_EnvelopeDataCtrl", 0, 1), ("Squ1_NoteLenCounter", 0, 1), ("Squ1_EnvelopeDataCtrl", 0, 1), ("Tri_NoteLenBuffer", 0, 1), ("Tri_NoteLenCounter", 0, 1),
   ("Noise_BeatLenCounter", 0, 1), ("Squ1_SfxLenCounter", 0, 1), ("Squ2_SfxLenCounter", 0, 1), ("Sfx_SecondaryCounter", 0, 1), ("Noise_SfxLenCounter", 0, 1),
   ("DAC_Counter", 0, 1), ("NoiseDataLoopbackOfs", 0, 1), ("NoteLengthTblAdder", 0, 1), ("AreaMusicBuffer_Alt", 0, 1), ("PauseModeFlag", 0, 1),
   ("GroundMusicHeaderOfs", 0, 1), ("AltRegContentFlag", 0, 1)]

/-- a number of the disassembly, in hexadecimal or binary -/
def asmNum (lines : List String) (n : String) : Option Nat :=
  lines.findSome? fun l =>
    match (l.splitOn "=").map (fun x => (x.splitOn ";").headD "") with
    | a :: b :: _ =>
      if a.trimAscii.toString == n then
        match b.trimAscii.toString.toList with
        | '$' :: ds => some (ds.foldl (fun v c => 16 * v + (hexDigit c).toNat) 0)
        | '%' :: ds => some (ds.foldl (fun v c => 2 * v + (if c == '1' then 1 else 0)) 0)
        | _ => none
      else none
    | _ => none

/-- the names this file needs -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  ((soundNames.map (·.1)) ++ ["OperMode", "MusicDataHigh", "MusicDataLow", "VictoryMusic", "TimeRunningOutMusic", "DeathMusic"]).eraseDups.filterMap fun n => (asmNum ls n).map (n, ·)

/-- the sound's bytes as RAM indices -/
def soundBytes (ns : Names) : List Nat := bytesOf ns soundNames

/-! ## Pieces by the lowest bit that is set -/

/-- the bytes of both, if they agree on the bits both know -/
def meet? (a b : AB) : Option AB :=
  if (a.v ^^^ b.v) &&& a.k &&& b.k != 0 then none else some (AB.mk ((a.v &&& a.k) ||| (b.v &&& b.k)) (a.k ||| b.k))

/-- the pieces of a byte by the lowest bit of `mask` that is set: one piece for each bit of the mask, and one where the bits of the mask are 0 -/
def ctzPieces (mask : UInt8) (b : AB) : List AB :=
  let bits := bitList.filter (fun x => x &&& mask != 0)
  ((bits.map fun x => AB.mk x (x ||| (mask &&& (x - 1)))) ++ [AB.mk 0 mask]).filterMap (meet? b)

/-- `LDA` of a byte of the list: its pieces -/
def splitCtz (E : Env) (L : List (Nat × UInt8)) (A : AS) : List AS :=
  if A.nmi || A.pc < 0x8000 then [A] else
  match ldaAddr E A.pc (E.prg.get! (A.pc &&& E.mask).toNat) with
  | none => [A]
  | some d =>
    match L.find? (·.1 == d) with
    | none => [A]
    | some p =>
      -- an `AND #` right after the load gives the mask
      let n := if E.prg.get! (A.pc &&& E.mask).toNat == 0xA5 then A.pc + 2 else A.pc + 3
      let mask := if E.prg.get! (n &&& E.mask).toNat == 0x29 then E.prg.get! ((n + 1) &&& E.mask).toNat else p.2
      (ctzPieces mask (A.getK d)).map (A.setK d)

/-- the step with these pieces -/
def ctzSuccs (E : Env) (ops : Array (AM Unit)) (L : List (Nat × UInt8)) (A : AS) : List (Option AS) :=
  (splitCtz E L A).flatMap (SideChangeEnd.xsuccs E ops)

/-! ## The search: no part of the proof -/

/-- the search of one call -/
structure SSearch where
  pending : Std.TreeMap Nat AS compare := {}
  steps : Nat := 0
  fails : Nat := 0
  failPcs : Std.HashMap Nat Nat := {}
  firstFail : Option AS := none
  /-- states at the return -/
  ends : Array AS := #[]
  /-- states at a frame's end -/
  over : Nat := 0
  visited : Std.HashMap Nat Unit := {}
  /-- for each key, the join of the states taken -/
  seen : Std.HashMap Nat AS := {}

/-- the search, one step at a time in the order of `xprio`, joining states with the same key; a state that `done` accepts is an end -/
partial def sloop (step : AS → List (Option AS)) (key : AS → Nat) (done : AS → Bool) (limit : Nat) (X0 : SSearch) : SSearch := Id.run do
  let mut X := X0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k, visited := X.visited.insert A.pc.toNat () }
      let rs := step A
      X := { X with steps := X.steps + rs.length }
      if rs.any (·.isNone) then
        X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A, failPcs := X.failPcs.insert A.pc.toNat (X.failPcs.getD A.pc.toNat 0 + 1) }
      for b in rs.filterMap id do
        if b.k != A.k then X := { X with over := X.over + 1 }
        else if done b then X := { X with ends := X.ends.push b }
        else
          let K := key b
          match X.seen[K]? with
          | some D =>
            if b.le D then pure ()
            else
              let J := D.join b
              X := { X with seen := X.seen.insert K J, pending := X.pending.insert K J }
          | none => X := { X with seen := X.seen.insert K b, pending := X.pending.insert K b }
  return X

/-- the search from some states -/
def ssearch (step : AS → List (Option AS)) (key : AS → Nat) (done : AS → Bool) (limit : Nat) (starts : List AS) : SSearch :=
  sloop step key done limit { pending := starts.foldl (fun t S => t.insert (key S) S) {}, seen := starts.foldl (fun t S => t.insert (key S) S) {} }

end Smbrta.SoundWalk
