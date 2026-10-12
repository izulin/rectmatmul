module

public import Rectangular.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

/-!
# Weighted bounds from the angular constraint

This module is purely real analysis. It does not assume the spectral theorem
or that tensor characters satisfy the angular constraint.

The classical Wolstenholme inequality is Equation (1), p. 147, of J. Liu,
"An Improved Result of a Weighted Trigonometric Inequality in Acute Triangles
with Applications", J. Math. Inequalities 14 (2020), 147–160,
DOI 10.7153/jmi-2020-14-11. We prove it directly by a sum of two squares,
for all real angles whose sum is pi, including degenerate triangles.
-/

namespace Rectangular

open Real

/-- The two-square identity behind Wolstenholme's inequality. -/
theorem wolstenholme_identity (u v w α β γ : ℝ) (hsum : α + β + γ = π) :
    u ^ 2 + v ^ 2 + w ^ 2 -
      2 * (v * w * cos α + w * u * cos β + u * v * cos γ) =
    (u - v * cos γ - w * cos β) ^ 2 +
      (v * sin γ - w * sin β) ^ 2 := by
  have hcos : cos α = -(cos γ * cos β - sin γ * sin β) := by
    rw [show α = π - (γ + β) by linarith, cos_pi_sub, cos_add]
  rw [hcos]
  calc
    _ = (u - v * cos γ - w * cos β) ^ 2 +
        (v * sin γ - w * sin β) ^ 2 +
        v ^ 2 * (1 - (sin γ ^ 2 + cos γ ^ 2)) +
        w ^ 2 * (1 - (sin β ^ 2 + cos β ^ 2)) := by ring
    _ = _ := by rw [sin_sq_add_cos_sq γ, sin_sq_add_cos_sq β]; ring

/-- No strict positivity of the angles is needed. -/
theorem wolstenholme (u v w α β γ : ℝ) (hsum : α + β + γ = π) :
    2 * (v * w * cos α + w * u * cos β + u * v * cos γ) ≤
      u ^ 2 + v ^ 2 + w ^ 2 := by
  have h := wolstenholme_identity u v w α β γ hsum
  nlinarith [sq_nonneg (u - v * cos γ - w * cos β),
    sq_nonneg (v * sin γ - w * sin β)]

/-- Algebraic weighted bound when the three angles sum to `pi / 2`.
The substitution `(u,v,w) = (bc,ac,ab)` avoids square roots of weights. -/
theorem weighted_cos_sq_le_dense_exact {a b c x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : x + y + z = π / 2) :
    a * cos x ^ 2 + b * cos y ^ 2 + c * cos z ^ 2 ≤
      (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 := by
  have h := wolstenholme (b * c) (a * c) (a * b)
    (2 * x) (2 * y) (2 * z) (by linarith)
  rw [cos_two_mul, cos_two_mul, cos_two_mul] at h
  have hnum : 0 ≤ (b * c) ^ 2 + (a * c) ^ 2 + (a * b) ^ 2 -
      2 * ((a * c) * (a * b) * (2 * cos x ^ 2 - 1) +
        (a * b) * (b * c) * (2 * cos y ^ 2 - 1) +
        (b * c) * (a * c) * (2 * cos z ^ 2 - 1)) := by linarith
  have hden : 0 ≤ 4 * a * b * c := by positivity
  have hdiv := div_nonneg hnum hden
  have hid :
      (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 -
        (a * cos x ^ 2 + b * cos y ^ 2 + c * cos z ^ 2) =
      ((b * c) ^ 2 + (a * c) ^ 2 + (a * b) ^ 2 -
        2 * ((a * c) * (a * b) * (2 * cos x ^ 2 - 1) +
          (a * b) * (b * c) * (2 * cos y ^ 2 - 1) +
          (b * c) * (a * c) * (2 * cos z ^ 2 - 1))) / (4 * a * b * c) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
    ring
  rw [← hid] at hdiv
  linarith

/-- Decrease angles to make their sum exactly `pi / 2`. This includes
the cases of zero angles, without a limiting argument. -/
theorem shrink_angles {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxu : x ≤ π / 2)
    (hsum : π / 2 ≤ x + y + z) :
    ∃ x' y' z' : ℝ,
      (0 ≤ x' ∧ x' ≤ x) ∧ (0 ≤ y' ∧ y' ≤ y) ∧
      (0 ≤ z' ∧ z' ≤ z) ∧ x' + y' + z' = π / 2 := by
  by_cases hxy : x + y ≤ π / 2
  · exact ⟨x, y, π / 2 - x - y, ⟨hx, le_rfl⟩, ⟨hy, le_rfl⟩,
      ⟨by linarith, by linarith⟩, by ring⟩
  · exact ⟨x, π / 2 - x, 0, ⟨hx, le_rfl⟩,
      ⟨by linarith, by linarith⟩, ⟨le_rfl, hz⟩, by ring⟩

/-- On the relevant angle interval, decreasing an angle increases its
cosine squared. -/
theorem cos_sq_antitone {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ π / 2)
    (hxy : x ≤ y) : cos y ^ 2 ≤ cos x ^ 2 := by
  have hcos := cos_le_cos_of_nonneg_of_le_pi hx
    (show y ≤ π by linarith [pi_pos]) hxy
  have hnonneg : 0 ≤ cos y :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hy⟩
  simpa only [sq] using mul_self_le_mul_self hnonneg hcos

/-- The dense formula for every angular-feasible point, not just the
boundary where the angle sum equals `pi / 2`. -/
theorem weighted_cos_sq_le_dense {a b c x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxu : x ≤ π / 2) (hyu : y ≤ π / 2) (hzu : z ≤ π / 2)
    (hsum : π / 2 ≤ x + y + z) :
    a * cos x ^ 2 + b * cos y ^ 2 + c * cos z ^ 2 ≤
      (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 := by
  obtain ⟨x', y', z', ⟨hx', hxx⟩, ⟨hy', hyy⟩, ⟨hz', hzz⟩, heq⟩ :=
    shrink_angles hx hy hz hxu hsum
  have hp := mul_le_mul_of_nonneg_left (cos_sq_antitone hx' hxu hxx) ha.le
  have hq := mul_le_mul_of_nonneg_left (cos_sq_antitone hy' hyu hyy) hb.le
  have hr := mul_le_mul_of_nonneg_left (cos_sq_antitone hz' hzu hzz) hc.le
  exact (add_le_add (add_le_add hp hq) hr).trans
    (weighted_cos_sq_le_dense_exact ha hb hc heq)

/-- At the thin threshold the dense formula is exactly `a+b`. -/
theorem dense_at_threshold {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b + thinThreshold a b) / 2 +
      (a * b / thinThreshold a b + a * thinThreshold a b / b +
        b * thinThreshold a b / a) / 4 = a + b := by
  unfold thinThreshold
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt (add_pos ha hb)]
  ring

/-- Both branches of the bound, including all zero weights, for sorted
nonnegative weights and arbitrary feasible angles. -/
theorem weighted_cos_sq_le_shapeBound {a b c x y z : ℝ}
    (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxu : x ≤ π / 2) (hyu : y ≤ π / 2) (hzu : z ≤ π / 2)
    (hsum : π / 2 ≤ x + y + z) :
    a * cos x ^ 2 + b * cos y ^ 2 + c * cos z ^ 2 ≤ shapeBound a b c := by
  have hb : 0 ≤ b := hc.trans hcb
  have ha : 0 ≤ a := hb.trans hba
  by_cases hbzero : b = 0
  · have hczero : c = 0 := le_antisymm (by simpa [hbzero] using hcb) hc
    have hcos : cos x ^ 2 ≤ 1 := by
      nlinarith [sin_sq_add_cos_sq x, sq_nonneg (sin x)]
    simpa [hbzero, hczero, shapeBound, thinThreshold] using
      mul_le_mul_of_nonneg_left hcos ha
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
  have hapos : 0 < a := hbpos.trans_le hba
  have htpos : 0 < thinThreshold a b :=
    div_pos (mul_pos hapos hbpos) (add_pos hapos hbpos)
  by_cases hthin : c ≤ thinThreshold a b
  · rw [shapeBound, ite_eq_left hthin]
    calc
      _ ≤ a * cos x ^ 2 + b * cos y ^ 2 + thinThreshold a b * cos z ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hthin (sq_nonneg _))
      _ ≤ _ := by
        have h := weighted_cos_sq_le_dense hapos hbpos htpos
          hx hy hz hxu hyu hzu hsum
        rwa [dense_at_threshold hapos hbpos] at h
  · rw [shapeBound, ite_eq_right hthin]
    exact weighted_cos_sq_le_dense hapos hbpos
      (htpos.trans (lt_of_not_ge hthin)) hx hy hz hxu hyu hzu hsum

/-- The angle associated with any parameter in `[0,1]`. -/
theorem parameter_angle {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ arccos (sqrt p) ∧ arccos (sqrt p) ≤ π / 2 ∧
      cos (arccos (sqrt p)) ^ 2 = p := by
  refine ⟨arccos_nonneg _, arccos_le_pi_div_two.mpr (sqrt_nonneg _), ?_⟩
  rw [cos_arccos (by linarith [sqrt_nonneg p]) (sqrt_le_one.mpr hp1), sq_sqrt hp]

/-- The analytic pilot: the angular constraint alone implies the weighted
bound for every real sorted nonnegative shape. -/
theorem weighted_bound_of_angular {a b c p q r : ℝ}
    (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hangular : π / 2 ≤ arccos (sqrt p) + arccos (sqrt q) + arccos (sqrt r)) :
    a * p + b * q + c * r ≤ shapeBound a b c := by
  obtain ⟨hθp, hθp1, hθpeq⟩ := parameter_angle hp hp1
  obtain ⟨hθq, hθq1, hθqeq⟩ := parameter_angle hq hq1
  obtain ⟨hθr, hθr1, hθreq⟩ := parameter_angle hr hr1
  simpa only [hθpeq, hθqeq, hθreq] using
    weighted_cos_sq_le_shapeBound hba hcb hc
      hθp hθq hθr hθp1 hθq1 hθr1 hangular

end Rectangular
