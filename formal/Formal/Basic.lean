import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Smoke test that the Mathlib dependency resolves; real modules follow. -/

example : (2 : ℤ) + 2 = 4 := by norm_num
