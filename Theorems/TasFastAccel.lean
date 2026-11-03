import Theorems.FastAccel

/-!
# TAS fast accel: the same with Left+Right allowed

`FastAccel.Bounds sy ctx lrInputsA relaxInputsLR 30 32`. The witness is the opening of the
HappyLee TAS (tasvideos 1715M). That 31 frames is impossible was found by the pruned exact
search (`smbrta realize ROM 31 lr`), not by Lean. Page: `Theorems/TasFastAccel.md`.
-/

namespace Smbrta.TasFastAccel

/-- 32 frames with Left+Right: the HappyLee TAS opening after the first controllable frame -/
def witness : List UInt8 := [0x03, 0x81, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x41, 0x02, 0x81, 0x01,
  0x01, 0x01, 0x01, 0x01, 0x01, 0x01]

end Smbrta.TasFastAccel
