module

public import Rectangular.CharacterAlgorithms
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.FieldDescent
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead

@[expose] public section

/-! Rectangular algebraic descent. The published spectral consequence is
supplied over the algebraic closure of the target field. The finite extension,
its dimension, and the tensor-power block are all chosen before input sizes.
No characteristic or separability hypothesis is needed by this route. -/

namespace Rectangular

open OAI.MatrixMultiplication
open Foundation AuxiliarySeparation

noncomputable section

theorem exists_power_absorb_constant {r ρ C : ℝ}
    (hr : 0 ≤ r) (hrρ : r < ρ) (hC : 1 ≤ C) :
    ∃ t : ℕ, 1 ≤ t ∧ C*r^t < ρ^t := by
  by_contra h
  have hall : ∀ t : ℕ, ρ^t ≤ C*r^t := by
    intro t
    by_cases ht : 1 ≤ t
    · exact le_of_not_gt (fun hh => h ⟨t,ht,hh⟩)
    · have ht0 : t=0 := by omega
      simpa [ht0] using hC
  have hh := le_of_pow_le_const_mul_pow hr hall
  linarith

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/-- Exact matrix coefficients are preserved by every scalar extension. -/
theorem matrix_tensor_scalar_extension (m l q : ℕ) :
    (fun x y z => algebraMap F E (matrixMultiplicationTensor (K := F) m l q x y z)) =
      matrixMultiplicationTensor (K := E) m l q := by
  funext x y z
  unfold matrixMultiplicationTensor
  split_ifs <;> simp

/-- Near-optimal rectangular rank blocks descend through an algebraic
extension. The fixed overhead d² disappears after choosing a larger power. -/
theorem rankBlocks_descend_algebraic [Algebra.IsAlgebraic F E]
    {a b c s : ℝ} (hblocks : ShapeRankBlocks E a b c s) :
    ShapeRankBlocks F a b c s := by
  intro δ hδ
  obtain ⟨B,m,l,q,R,hB,hm,hl,hq,hcoverm,hcoverl,hcoverq,hRank,hrate⟩ :=
    hblocks (δ/2) (by linarith)
  have hB1 : 1 < (B:ℝ) := by exact_mod_cast (by omega : 1 < B)
  have hB0 : 0 < (B:ℝ) := zero_lt_one.trans hB1
  have hext : Tensor.RankAtMost
      (fun x y z => algebraMap F E (matrixMultiplicationTensor (K := F) m l q x y z)) R := by
    rw [matrix_tensor_scalar_extension]
    exact hRank
  obtain ⟨d,hd,hpow⟩ := hext.descend_algebraic_powers
  have hρ : (R:ℝ) < (B:ℝ)^(s+δ) := hrate.trans
    (Real.rpow_lt_rpow_of_exponent_lt hB1 (by linarith))
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨t,ht,habsorb⟩ := exists_power_absorb_constant (Nat.cast_nonneg R) hρ
    (show (1:ℝ) ≤ (d:ℝ)^2 by nlinarith)
  refine ⟨B^t,m^t,l^t,q^t,R^t*d*d,
    hB.trans (Nat.le_self_pow (by omega) B),pow_pos hm _,pow_pos hl _,pow_pos hq _,
    ?_,?_,?_,rectangular_rank_of_power (hpow t),?_⟩
  · rw [Nat.cast_pow, ←Real.rpow_pow_comm hB0.le]
    exact_mod_cast pow_le_pow_left₀ (Real.rpow_nonneg hB0.le a) hcoverm t
  · rw [Nat.cast_pow, ←Real.rpow_pow_comm hB0.le]
    exact_mod_cast pow_le_pow_left₀ (Real.rpow_nonneg hB0.le b) hcoverl t
  · rw [Nat.cast_pow, ←Real.rpow_pow_comm hB0.le]
    exact_mod_cast pow_le_pow_left₀ (Real.rpow_nonneg hB0.le c) hcoverq t
  · rw [Nat.cast_pow, ←Real.rpow_pow_comm hB0.le]
    push_cast
    nlinarith [habsorb]

/-- The same admissible exponent holds in the base field after algebraic
rank descent and the checked rectangular program conversion. -/
theorem shapeAdmissible_descend_algebraic [Algebra.IsAlgebraic F E]
    {a b c s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hblocks : ShapeRankBlocks E a b c s) :
    ShapeAdmissibleExponent F a b c s :=
  shapeAdmissible_of_rankBlocks ha hb hc hs (rankBlocks_descend_algebraic hblocks)

/-- Theorem 1.1 (`cor:general-exponents`), after field descent.
The writeup's introduction states the characteristic-zero transfer; this
checked interface also covers positive characteristic.
General shape bound over any field, with the standard spectral input
over its algebraic closure exposed rather than installed as an axiom. -/
theorem shapeAdmissible_all_fields (F : Type) [Field F]
    (spectral : SpectralInputOver (AlgebraicClosure F))
    {a b c : ℝ} (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c) :
    ShapeAdmissibleExponent F a b c (shapeBound a b c) := by
  have hb := hc.trans hcb
  have ha := hb.trans hba
  apply shapeAdmissible_descend_algebraic (E := AlgebraicClosure F)
    ha hb hc (shapeBound_nonneg hba hcb hc)
  exact rankBlocks_of_character_bound spectral ha hb hc
    (weighted_character_bound_over hba hcb hc)

end

end Rectangular
