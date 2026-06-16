import Mathlib.Algebra.IsPrimePow

example : IsPrimePow 10093 := by decide_cbv

example : IsPrimePow 100999 := by decide_cbv

example : ¬ IsPrimePow 15 := by decide_cbv

example : ¬ IsPrimePow 111111111111111155 := by decide_cbv
