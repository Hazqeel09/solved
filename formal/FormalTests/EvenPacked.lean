import Formal.ICG.EvenPacked

/-!
# Regression tests for `Solved.ICG.certifyP`

The order `2p` (maximiser `{1, 2, p}`, energy `4p - 2` for `p ≥ 3`) and `2p⁴`, with the field
width `w` and coefficient count `D` the certificate generator chooses. Every deliberately wrong
certificate must evaluate to `false` in the kernel, including ones that only the size and length
guards reject.
-/

namespace Solved.ICG.Tests

example : certifyP 1 1 3 12 2 [-2, 4] [0, 1, 2] [true, true, true] [] = true := by
  decide +kernel

example : certifyP 1 4 3 21 5 [2, 4, -6, -8, 10] [0, 5, 1, 6, 2, 7, 3, 8, 4]
    [true, true, false, false, true, false, true, true, false] [] = true := by
  decide +kernel

/-- wrong energy polynomial -/
example : certifyP 1 1 3 12 2 [-2, 5] [0, 1, 2] [true, true, true] [] = false := by
  decide +kernel
/-- a non-maximiser claimed as the maximiser -/
example : certifyP 1 1 3 12 2 [-2, 4] [0, 1, 2] [true, true, false] [] = false := by
  decide +kernel
/-- a non-maximiser claimed as a second maximiser -/
example : certifyP 1 1 3 12 2 [-2, 4] [0, 1, 2] [true, true, true] [[true, true, false]] =
    false := by
  decide +kernel
/-- the cell order misses or repeats a cell, or names the top cell -/
example : certifyP 1 1 3 12 2 [-2, 4] [0, 1] [true, true, true] [] = false := by decide +kernel
example : certifyP 1 1 3 12 2 [-2, 4] [0, 1, 1] [true, true, true] [] = false := by decide +kernel
example : certifyP 1 1 3 12 2 [-2, 4] [0, 1, 2, 3] [true, true, true] [] = false := by
  decide +kernel
/-- the maximiser has the wrong length -/
example : certifyP 1 1 3 12 2 [-2, 4] [0, 1, 2] [true, true, true, false] [] = false := by
  decide +kernel
/-- the same claim from `p ≥ 1` -/
example : certifyP 1 1 1 12 2 [-2, 4] [0, 1, 2] [true, true, true] [] = false := by
  decide +kernel
/-- the narrowest safe width is `w = 11` (`4 m B + T = 526 < 2^10`); `w = 10` is rejected -/
example : certifyP 1 1 3 11 2 [-2, 4] [0, 1, 2] [true, true, true] [] = true := by
  decide +kernel
example : certifyP 1 1 3 10 2 [-2, 4] [0, 1, 2] [true, true, true] [] = false := by
  decide +kernel
example : certifyP 1 1 3 0 2 [-2, 4] [0, 1, 2] [true, true, true] [] = false := by
  decide +kernel
/-- too few coefficients per polynomial -/
example : certifyP 1 1 3 12 1 [-2, 4] [0, 1, 2] [true, true, true] [] = false := by
  decide +kernel
example : certifyP 1 1 3 12 0 [-2, 4] [0, 1, 2] [true, true, true] [] = false := by
  decide +kernel

end Solved.ICG.Tests
