module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Optimization
public import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! The individual-character version of the entropy optimization step.
Unlike the upstream final profile bounds, this does not multiply over leg orders.
The finite entropy identity is reused from the pinned source.
-/

noncomputable section

namespace Rectangular

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

/-- Optimizing all finite probability laws turns an entropy tag bound into a
power sum. Positivity excludes empty sectors; `p > 0` is essential. -/
theorem entropy_power_sum_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι → ℝ) (hV : ∀ i, 0 < V i) {p T : ℝ} (hp : 0 < p) (hT : 0 < T)
    (hbound : ∀ q : FiniteLaw ι,
      Real.exp (p * finiteEntropy q.mass) * (∏ i, V i ^ q.mass i) ≤ T) :
    (∑ i, V i ^ (1 / p)) ≤ T ^ (1 / p) := by
  let W : ι → ℝ := fun i => V i ^ (1 / p)
  have hW : ∀ i, 0 < W i := fun i => Real.rpow_pos_of_pos (hV i) _
  have hsum : 0 < ∑ i, W i := Finset.sum_pos (fun i _ => hW i) Finset.univ_nonempty
  let q : FiniteLaw ι := {
    mass := fun i => W i / (∑ j, W j)
    nonneg := fun i => (div_pos (hW i) hsum).le
    total := by rw [← Finset.sum_div, div_self hsum.ne'] }
  have hprod : 0 < ∏ i, V i ^ q.mass i :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hV i) _)
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hprod) (hbound q)
  rw [Real.log_mul (Real.exp_pos _).ne' hprod.ne', Real.log_exp,
    Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hV i) _).ne')] at hlog
  simp only [Real.log_rpow (hV _)] at hlog
  have hnormalized : finiteEntropy q.mass + (∑ i, Real.log (W i) * q.mass i)
      ≤ Real.log (T ^ (1 / p)) := by
    have hdiv := div_le_div_of_nonneg_right hlog hp.le
    rw [Real.log_rpow hT]
    dsimp only [W]
    simp only [Real.log_rpow (hV _)]
    have hsumlog : (∑ i, 1 / p * Real.log (V i) * q.mass i) =
        (∑ i, q.mass i * Real.log (V i)) / p := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsumlog]
    convert hdiv using 1 <;> field_simp [hp.ne']
  have hidentity : finiteEntropy q.mass + (∑ i, Real.log (W i) * q.mass i) =
      Real.log (∑ i, W i) := by
    simpa [q, finiteEntropy, entropyTerm, Finset.sum_neg_distrib] using
      finite_entropy_log_partition Finset.univ W Finset.univ_nonempty (fun i _ => hW i)
  rw [hidentity] at hnormalized
  exact (Real.log_le_log_iff hsum (Real.rpow_pos_of_pos hT _)).mp hnormalized

end Rectangular
