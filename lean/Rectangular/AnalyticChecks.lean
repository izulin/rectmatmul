module

public import Rectangular.AngularBound

/-! Boundary checks for the analytic lemma, independently of tensor interfaces. -/

-- The thin endpoint is angular-feasible and attains the bound.
example :
    Real.pi / 2 ≤ Real.arccos (Real.sqrt (1 : ℝ)) +
      Real.arccos (Real.sqrt (1 : ℝ)) + Real.arccos (Real.sqrt (0 : ℝ)) ∧
    (1 : ℝ) * 1 + 1 * 1 + 0.5 * 0 = Rectangular.shapeBound 1 1 0.5 := by
  constructor <;> norm_num [Real.arccos_one, Real.arccos_zero,
    Rectangular.shapeBound, Rectangular.thinThreshold]

-- The square endpoint is feasible and attains 2.25, using pi/6 angles.
example :
    Real.pi / 6 + Real.pi / 6 + Real.pi / 6 = Real.pi / 2 ∧
    (Real.cos (Real.pi / 6) ^ 2 + Real.cos (Real.pi / 6) ^ 2 +
      Real.cos (Real.pi / 6) ^ 2) = Rectangular.shapeBound 1 1 1 := by
  constructor
  · ring
  · simp only [Real.sq_cos_pi_div_six]
    norm_num [Rectangular.shapeBound, Rectangular.thinThreshold]

-- The classical identity includes a fully degenerate triangle.
example (v w : ℝ) :
    (v + w) ^ 2 + v ^ 2 + w ^ 2 -
      2 * (v * w * Real.cos Real.pi + w * (v + w) * Real.cos 0 +
        (v + w) * v * Real.cos 0) = 0 := by
  have h := Rectangular.wolstenholme_identity (v + w) v w
    Real.pi 0 0 (by ring)
  simpa using h

-- The rank-one branch is obtained by applying the analytic theorem.
example : (1 : ℝ) * 1 + 0 * 0 + 0 * 0 ≤ Rectangular.shapeBound 1 0 0 := by
  apply Rectangular.weighted_bound_of_angular
  all_goals norm_num [Real.arccos_one, Real.arccos_zero]
  all_goals linarith [Real.pi_pos]

-- The all-zero shape is covered by the same theorem.
example : (0 : ℝ) * 0 + 0 * 0 + 0 * 0 ≤ Rectangular.shapeBound 0 0 0 := by
  apply Rectangular.weighted_bound_of_angular
  all_goals norm_num [Real.arccos_zero]
  all_goals linarith [Real.pi_pos]
