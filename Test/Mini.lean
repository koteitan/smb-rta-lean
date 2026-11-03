import Smbrta
import Config
open Smbrta

/-! Check the frame loop, NMI and controller with the homemade cartridge `tools/make_mini_rom.py`. -/

def rev8 (v : UInt8) : UInt8 := Id.run do
  let mut r : UInt8 := 0
  for i in [0:8] do
    if (v >>> i.toUInt8) &&& 1 == 1 then r := r ||| ((1 : UInt8) <<< (7 - i).toUInt8)
  return r

def miniInputs : Array UInt8 := (Array.range 17868).map fun k => (k * 37 + 11).toUInt8

/-- what the cartridge should compute if NMI `k` happens in movie frame `k` for `k ≥ 2` -/
def expected : Nat × Nat :=
  let ks := (List.range 17868).drop 2
  (ks.length % 256, (ks.foldl (fun s k => s + (rev8 (miniInputs[k]!)).toNat) 0) % 65536)

def miniResult (cart : Machine) : Nat × Nat :=
  let (_, m) := firstFrameWhere (powerOn cart 0) miniInputs (fun _ => false)
  ((peek m 0).toNat, (peek m 2).toNat + 256 * (peek m 3).toNat)

def main : IO UInt32 := do
  let cart ← match Machine.ofINes (← IO.FS.readBinFile (← (← Config.load none).path "miniRom")) with
    | .ok m => pure m
    | .error e => throw (IO.userError e)
  let t0 ← IO.monoMsNow
  let got := miniResult cart
  let t1 ← IO.monoMsNow
  IO.println s!"expected {expected}, got {got}, {t1 - t0} ms"
  return if got == expected then 0 else 1
