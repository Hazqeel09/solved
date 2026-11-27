import Formal.ICG.EvenCert

/-!
# Regression tests for `Solved.ICG.certify`

The order `2p`: the maximiser is `{1, 2, p}` (cells `(0,0), (0,1), (1,0)`) with energy `4p - 2`
for `p ≥ 3`. Every deliberately wrong certificate below must evaluate to `false` in the kernel.
-/

namespace Solved.ICG.Tests

example : certify 1 1 3 [-2, 4] [0, 1, 2] [true, true, true] [] = true := by decide +kernel

/-- wrong energy polynomial -/
example : certify 1 1 3 [-2, 5] [0, 1, 2] [true, true, true] [] = false := by decide +kernel
/-- a non-maximiser claimed as the maximiser -/
example : certify 1 1 3 [-2, 4] [0, 1, 2] [true, true, false] [] = false := by decide +kernel
/-- a non-maximiser claimed as a second maximiser -/
example : certify 1 1 3 [-2, 4] [0, 1, 2] [true, true, true] [[true, true, false]] = false := by
  decide +kernel
/-- the cell order misses a cell -/
example : certify 1 1 3 [-2, 4] [0, 1] [true, true, true] [] = false := by decide +kernel
/-- the cell order repeats a cell -/
example : certify 1 1 3 [-2, 4] [0, 1, 1] [true, true, true] [] = false := by decide +kernel
/-- the cell order names the top cell (the order itself) -/
example : certify 1 1 3 [-2, 4] [0, 1, 2, 3] [true, true, true] [] = false := by decide +kernel
/-- the maximiser has the wrong length -/
example : certify 1 1 3 [-2, 4] [0, 1, 2] [true, true, true, false] [] = false := by
  decide +kernel
/-- the same claim from `p ≥ 1` instead of `p ≥ 3` is rejected -/
example : certify 1 1 1 [-2, 4] [0, 1, 2] [true, true, true] [] = false := by decide +kernel

end Solved.ICG.Tests
