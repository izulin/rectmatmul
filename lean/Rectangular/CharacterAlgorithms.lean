module

public import Rectangular.BlockAlgorithms
public import Rectangular.SpectralInput
public import Rectangular.AngularConstraint

@[expose] public section

/-! Character bounds give finite blocks and then uniform running-time bounds.
Spectral duality is the explicit published input; every rounding and program
conversion below is proved rather than included in that input. -/

namespace Rectangular

open OAI.MatrixMultiplication
open Foundation AuxiliarySeparation

noncomputable section

variable {K : Type} [Field K]

theorem exists_nat_rpow_gt {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ B : ℕ, 2 ≤ B ∧ C < (B:ℝ)^δ := by
  obtain ⟨B,hB⟩ := exists_nat_gt (max 2 (C^δ⁻¹))
  have hB2 : (2:ℝ) < B := (le_max_left _ _).trans_lt hB
  have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg hC _)
    ((le_max_right _ _).trans_lt hB) hδ
  rw [Real.rpow_inv_rpow hC hδ.ne'] at hpow
  exact ⟨B,by exact_mod_cast hB2.le,hpow⟩

/-- Each rounded coordinate contributes at most a factor two. -/
theorem rounded_parameter_bound {n : ℕ} (hn : 1 ≤ n)
    {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Arithmetic.innerSize n a:ℝ)^p ≤ 2*(n:ℝ)^(a*p) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ (2*(n:ℝ)^a)^p := Real.rpow_le_rpow (Nat.cast_nonneg _)
      (Arithmetic.innerSize_cast_le hn ha) hp
    _ = (2:ℝ)^p * (n:ℝ)^(a*p) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hn0.le a),
        ←Real.rpow_mul hn0.le]
    _ ≤ 2*(n:ℝ)^(a*p) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp1

/-- Rounding is uniform in the character, with the orientation (pY,pZ,pX). -/
theorem rounded_matrix_character_bound {n : ℕ} (hn : 1 ≤ n)
    {a b c E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (χ : Character K) (hweight : a*χ.pY+b*χ.pZ+c*χ.pX ≤ E) :
    χ.value (matrixMultiplicationTensor (K := K)
      (Arithmetic.innerSize n a) (Arithmetic.innerSize n b)
      (Arithmetic.innerSize n c)) ≤ 8*(n:ℝ)^E := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [matrixMultiplicationTensor_eq_matrixCoefficients,
    χ.value_matrixCoefficients
      (by have h := Arithmetic.one_le_innerSize hn a; omega)
      (by have h := Arithmetic.one_le_innerSize hn b; omega)
      (by have h := Arithmetic.one_le_innerSize hn c; omega)]
  have ha' := rounded_parameter_bound hn ha χ.pY_nonneg χ.pY_le_one
  have hb' := rounded_parameter_bound hn hb χ.pZ_nonneg χ.pZ_le_one
  have hc' := rounded_parameter_bound hn hc χ.pX_nonneg χ.pX_le_one
  calc
    _ ≤ (2*(n:ℝ)^(b*χ.pZ))*(2*(n:ℝ)^(a*χ.pY))*(2*(n:ℝ)^(c*χ.pX)) := by
      gcongr
    _ = 8*(n:ℝ)^(a*χ.pY+b*χ.pZ+c*χ.pX) := by
      rw [Real.rpow_add hn0, Real.rpow_add hn0]; ring
    _ ≤ 8*(n:ℝ)^E := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hweight) (by norm_num)

theorem matrix_tensor_ne_zero_over {m l q : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hq : 0 < q) :
    matrixMultiplicationTensor (K := K) m l q ≠ 0 := by
  let i : Fin m := ⟨0,hm⟩
  let j : Fin l := ⟨0,hl⟩
  let k : Fin q := ⟨0,hq⟩
  intro h
  have hh := congrArg (fun T => T (i,j) (j,k) (k,i)) h
  simp at hh

/-- Fix a large rounding base, then a finite tensor power. Both choices are
independent of the matrix input size used by the resulting programs. -/
theorem rankBlocks_of_character_bound (spectral : SpectralInputOver K)
    {a b c E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hweight : ∀ χ : Character K, a*χ.pY+b*χ.pZ+c*χ.pX ≤ E) :
    ShapeRankBlocks K a b c E := by
  intro δ hδ
  obtain ⟨B,hB,h8⟩ := exists_nat_rpow_gt (C := 8) (by norm_num) hδ
  have hB0 : 0 < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hB1 : 1 ≤ B := by omega
  let m := Arithmetic.innerSize B a
  let l := Arithmetic.innerSize B b
  let q := Arithmetic.innerSize B c
  have hm : 0 < m := by have h := Arithmetic.one_le_innerSize hB1 a; omega
  have hl : 0 < l := by have h := Arithmetic.one_le_innerSize hB1 b; omega
  have hq : 0 < q := by have h := Arithmetic.one_le_innerSize hB1 c; omega
  have hval : ∀ χ : Character K,
      χ.value (matrixMultiplicationTensor (K := K) m l q) ≤ 8*(B:ℝ)^E :=
    fun χ => rounded_matrix_character_bound hB1 ha hb hc χ (hweight χ)
  have hgap : 8*(B:ℝ)^E < (B:ℝ)^(E+δ) := by
    rw [Real.rpow_add hB0]
    simpa only [mul_comm] using
      mul_lt_mul_of_pos_right h8 (Real.rpow_pos_of_pos hB0 E)
  obtain ⟨N,R,hN,hRank,hR⟩ := spectral.finite_power_bound
    (matrixMultiplicationTensor (K := K) m l q) (8*(B:ℝ)^E) ((B:ℝ)^(E+δ))
    (matrix_tensor_ne_zero_over hm hl hq) hval
    (Real.rpow_pos_of_pos hB0 _) hgap
  have hBN : 2 ≤ B^N := hB.trans (Nat.le_self_pow (by omega) B)
  refine ⟨B^N,m^N,l^N,q^N,R,hBN,pow_pos hm _,pow_pos hl _,pow_pos hq _,
    ?_,?_,?_,rectangular_rank_of_power hRank,?_⟩
  · rw [Nat.cast_pow, ←Real.rpow_pow_comm hB0.le]
    exact_mod_cast pow_le_pow_left₀ (Real.rpow_nonneg hB0.le a) (Nat.le_ceil _) N
  · rw [Nat.cast_pow, ←Real.rpow_pow_comm hB0.le]
    exact_mod_cast pow_le_pow_left₀ (Real.rpow_nonneg hB0.le b) (Nat.le_ceil _) N
  · rw [Nat.cast_pow, ←Real.rpow_pow_comm hB0.le]
    exact_mod_cast pow_le_pow_left₀ (Real.rpow_nonneg hB0.le c) (Nat.le_ceil _) N
  · simpa only [Nat.cast_pow, Real.rpow_pow_comm hB0.le] using hR

/-- Lemma 6.1 (`lem:cost-conversion`), with the standard spectral input exposed. -/
theorem shapeAdmissible_of_character_bound (spectral : SpectralInputOver K)
    {a b c E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hweight : ∀ χ : Character K, a*χ.pY+b*χ.pZ+c*χ.pX ≤ E) :
    ShapeAdmissibleExponent K a b c E := by
  have hblocks := rankBlocks_of_character_bound spectral ha hb hc hweight
  exact shapeAdmissible_of_rankBlocks ha hb hc (shapeRankBlocks_nonneg hblocks) hblocks

/-- The numerical bound is nonnegative throughout its stated domain. -/
theorem shapeBound_nonneg {a b c : ℝ} (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c) :
    0 ≤ shapeBound a b c := by
  have hb := hc.trans hcb
  have ha := hb.trans hba
  unfold shapeBound
  split_ifs <;> positivity

/-- The angular argument applies over every infinite algebraically closed
field; it does not require symmetry of an individual character. -/
theorem weighted_character_bound_over [Infinite K] [IsAlgClosed K]
    {a b c : ℝ} (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c) (χ : Character K) :
    a*χ.pY+b*χ.pZ+c*χ.pX ≤ shapeBound a b c := by
  apply weighted_bound_of_angular hba hcb hc
    χ.pY_nonneg χ.pY_le_one χ.pZ_nonneg χ.pZ_le_one χ.pX_nonneg χ.pX_le_one
  have hh := character_angular_constraint χ
  linarith

theorem shapeAdmissible_over [Infinite K] [IsAlgClosed K]
    (spectral : SpectralInputOver K) {a b c : ℝ}
    (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c) :
    ShapeAdmissibleExponent K a b c (shapeBound a b c) :=
  shapeAdmissible_of_character_bound spectral ((hc.trans hcb).trans hba)
    (hc.trans hcb) hc
    (weighted_character_bound_over hba hcb hc)

/-- Theorem 1.1 (`cor:general-exponents`), upper bound, proved in Section 6:
the complex general-shape running-time target. Equality is `sizeOptimalTarget`. -/
theorem mainTarget (spectral : SpectralInput) : MainTarget := by
  intro a b c hba hcb hc
  exact shapeAdmissible_over spectral hba hcb hc

end

end Rectangular
