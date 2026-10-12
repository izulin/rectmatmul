module

public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Numerical bounds, separated from the tensor and program interfaces. -/

namespace Rectangular

noncomputable section

/-- The threshold is zero at `a = b = 0`, using real division's convention. -/
def thinThreshold (a b : ℝ) : ℝ := a * b / (a + b)

/-- The general bound, intended for `a ≥ b ≥ c ≥ 0`. -/
def shapeBound (a b c : ℝ) : ℝ :=
  if c ≤ thinThreshold a b then a + b
  else (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4

/-- The full curve, intended for every real `k ≥ 0`. -/
def curveBound (k : ℝ) : ℝ :=
  if k ≤ (0.5 : ℝ) then 2 else 1 + k + 1 / (4 * k)

end

end Rectangular
