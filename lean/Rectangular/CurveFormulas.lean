module

public import Rectangular.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! Pure numerical identities connecting the sorted-shape formula to the
one-parameter curve. No tensor or arithmetic-program interfaces are used. -/

namespace Rectangular

noncomputable section

theorem shapeBound_one_one (k : ℝ) : shapeBound 1 1 k=curveBound k := by
  have hthreshold : thinThreshold 1 1=(0.5:ℝ) := by norm_num [thinThreshold]
  unfold shapeBound curveBound
  rw [hthreshold]
  split_ifs with hk
  · norm_num
  · have hk0 : k ≠ 0 := by linarith
    field_simp [hk0]; ring

theorem shapeBound_large_one_one {k : ℝ} (hk : 1 ≤ k) :
    shapeBound k 1 1=curveBound k := by
  have hk0 : k ≠ 0 := by linarith
  have hsum : 0 < k+1 := by linarith
  have hthin : ¬(1:ℝ) ≤ thinThreshold k 1 := by
    unfold thinThreshold
    simp only [mul_one]
    exact not_le.mpr ((div_lt_one hsum).mpr (by linarith))
  have hhalf : ¬k ≤ (0.5:ℝ) := by linarith
  rw [shapeBound,ite_eq_right hthin,curveBound,ite_eq_right hhalf]
  field_simp [hk0]; ring

theorem curveBound_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ curveBound k := by
  unfold curveBound
  split_ifs <;> positivity

end

end Rectangular
