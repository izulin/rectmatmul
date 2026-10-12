module

public import Rectangular.FieldTransfer
public import Rectangular.InputLowerBound
public import Rectangular.CurveFormulas
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

@[expose] public section

/-! Main shape, exactness, and full rectangular curve, with their standard
spectral inputs visible in the theorem signatures. -/

namespace Rectangular

open OAI.MatrixMultiplication
open AuxiliarySeparation

noncomputable section

variable {K : Type} [Field K]

/-- Apply the sorted-weight bound in the appropriate orientation, retaining
the actual parameters of this character throughout. -/
theorem weighted_curve_bound [Infinite K] [IsAlgClosed K]
    {k : ℝ} (hk : 0 ≤ k) (χ : Character K) :
    χ.pY+k*χ.pZ+χ.pX ≤ curveBound k := by
  have hang := character_angular_constraint χ
  by_cases hk1 : k ≤ 1
  · have hh := weighted_bound_of_angular (a := 1) (b := 1) (c := k)
      (by norm_num) hk1 hk χ.pY_nonneg χ.pY_le_one
      χ.pX_nonneg χ.pX_le_one χ.pZ_nonneg χ.pZ_le_one (by linarith)
    rw [shapeBound_one_one] at hh
    simp only [one_mul] at hh
    linarith
  · have hh := weighted_bound_of_angular (a := k) (b := 1) (c := 1)
      (le_of_not_ge hk1) (by norm_num) (by norm_num)
      χ.pZ_nonneg χ.pZ_le_one χ.pY_nonneg χ.pY_le_one
      χ.pX_nonneg χ.pX_le_one (by linarith)
    rw [shapeBound_large_one_one (le_of_not_ge hk1)] at hh
    simp only [one_mul] at hh
    linarith

theorem curve_rankBlocks_over [Infinite K] [IsAlgClosed K]
    (spectral : SpectralInputOver K) {k : ℝ} (hk : 0 ≤ k) :
    ShapeRankBlocks K 1 k 1 (curveBound k) := by
  apply rankBlocks_of_character_bound spectral (by norm_num) hk (by norm_num)
  intro χ
  simpa only [one_mul] using weighted_curve_bound hk χ

theorem curveAdmissible_over [Infinite K] [IsAlgClosed K]
    (spectral : SpectralInputOver K) {k : ℝ} (hk : 0 ≤ k) :
    Arithmetic.RectangularAdmissibleExponent K k (curveBound k) :=
  (shapeAdmissible_one_k_one_iff K k _).mp
    (shapeAdmissible_of_rankBlocks (by norm_num) hk (by norm_num)
      (curveBound_nonneg hk) (curve_rankBlocks_over spectral hk))

theorem sizeOptimalTarget (spectral : SpectralInput) : SizeOptimalTarget := by
  intro a b c hba hcb hc hthin
  constructor
  · have hh := mainTarget spectral a b c hba hcb hc
    simpa only [shapeBound,ite_eq_left hthin] using hh
  · intro E hE
    exact shapeAdmissible_left_lower hE

theorem curveTarget (spectral : SpectralInput) : CurveTarget := by
  intro k hk
  have hadm := curveAdmissible_over spectral hk
  refine ⟨hadm, ?_⟩
  intro hhalf
  have hupper := Arithmetic.rectangularOmega_le_of_admissibleExponent hadm
  rw [curveBound,ite_eq_left hhalf] at hupper
  exact le_antisymm hupper (Arithmetic.rectangularOmega_two_le k)

theorem complexAlpha_half_le (spectral : SpectralInput) :
    (0.5:ℝ) ≤ Arithmetic.complexAlpha :=
  Arithmetic.le_complexAlpha (by norm_num)
    ((curveTarget spectral 0.5 (by norm_num)).2 (by norm_num))

/-- Size-optimal exactness after the checked algebraic-closure descent. -/
theorem sizeOptimal_all_fields (F : Type) [Field F]
    (spectral : SpectralInputOver (AlgebraicClosure F))
    {a b c : ℝ} (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c)
    (hthin : c ≤ thinThreshold a b) :
    ShapeAdmissibleExponent F a b c (a+b) ∧
      ∀ E : ℝ, ShapeAdmissibleExponent F a b c E → a+b ≤ E := by
  constructor
  · have hh := shapeAdmissible_all_fields F spectral hba hcb hc
    simpa only [shapeBound,ite_eq_left hthin] using hh
  · intro E hE
    exact shapeAdmissible_left_lower hE

theorem curveAdmissible_all_fields (F : Type) [Field F]
    (spectral : SpectralInputOver (AlgebraicClosure F))
    {k : ℝ} (hk : 0 ≤ k) :
    Arithmetic.RectangularAdmissibleExponent F k (curveBound k) := by
  apply (shapeAdmissible_one_k_one_iff F k _).mp
  exact shapeAdmissible_descend_algebraic (E := AlgebraicClosure F)
    (by norm_num) hk (by norm_num) (curveBound_nonneg hk)
    (curve_rankBlocks_over spectral hk)

theorem rectangularOmega_all_fields_le (F : Type) [Field F]
    (spectral : SpectralInputOver (AlgebraicClosure F))
    {k : ℝ} (hk : 0 ≤ k) : Arithmetic.rectangularOmega F k ≤ curveBound k :=
  Arithmetic.rectangularOmega_le_of_admissibleExponent
    (curveAdmissible_all_fields F spectral hk)

theorem rectangularOmega_all_fields_eq_two (F : Type) [Field F]
    (spectral : SpectralInputOver (AlgebraicClosure F))
    {k : ℝ} (hk : 0 ≤ k) (hhalf : k ≤ (0.5:ℝ)) :
    Arithmetic.rectangularOmega F k=2 := by
  have hupper := rectangularOmega_all_fields_le F spectral hk
  rw [curveBound,ite_eq_left hhalf] at hupper
  exact le_antisymm hupper (Arithmetic.rectangularOmega_two_le k)

end

end Rectangular
