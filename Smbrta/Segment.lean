import Smbrta.Jump

/-!
# Running one routine of the game

`runSub m addr a x y` calls the routine at `addr` with the registers `a`, `x`, `y`
(JSR with a sentinel return address) and runs it to its RTS.
-/

namespace Smbrta

def runSub (m : Machine) (addr : UInt16) (a x y : UInt8) (fuel : Nat := 2000) : Machine :=
  callSub { m with a, x, y } addr fuel

/-- the ROM byte at `addr` -/
def romByte (m : Machine) (addr : UInt16) : UInt8 := m.prg.get! (addr &&& m.prgMask).toNat

/-- signed value of a byte -/
def sbyte (v : UInt8) : Int := if v < 0x80 then v.toNat else (v.toNat : Int) - 256

/-- 24-bit position page:x:fraction of the player -/
def posP (sy : Syms) (m : Machine) : Int :=
  ((peek m sy.Player_PageLoc).toNat * 256 + (peek m sy.Player_X_Position).toNat) * 256 +
    (peek m sy.SprObject_X_MoveForce).toNat

/-- `n` ROM bytes from `addr` -/
def tbl (m : Machine) (addr : UInt16) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => romByte m (addr + i.toUInt16)

/-- the right speed caps: the four entries of the right table -/
def maxRs (sy : Syms) (m : Machine) : List UInt8 := tbl m sy.MaxRightXSpdData 4
/-- the left speed caps: the three entries of the left table (all negative) -/
def maxLs (sy : Syms) (m : Machine) : List UInt8 := tbl m sy.MaxLeftXSpdData 3
/-- friction adders: a table entry, or the entry doubled (low byte shifted, high byte = carry) -/
def adders (sy : Syms) (m : Machine) : List (UInt8 × UInt8) :=
  (tbl m sy.FrictionData 3).flatMap fun f => [(f, 0), (f <<< 1, f >>> 7)]
/-- the largest adder, in 1/256 speed units -/
def amax (sy : Syms) (m : Machine) : Int :=
  ((adders sy m).map fun (lo, hi) => (256 * hi.toNat + lo.toNat : Int)).foldl max 0

end Smbrta
