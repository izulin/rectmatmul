module

public import Rectangular.Results

/-! Boundary shapes, rounded dimensions, the free-load program model,
unequal tensor powers, and finite-characteristic descent. -/

namespace Rectangular

open OAI.MatrixMultiplication
open Foundation AuxiliarySeparation Arithmetic

-- Loading an input is free and does not put it into the counted-gate set.
example : ProgramInputs.used
    ((Program.nil : Program ℚ (Fin 1) 0).step (.input 0)) = ∅ := by
  simp [ProgramInputs.used, ProgramInputs.gateInputs]

-- The scalar multiplication gate uses both input coordinates.
example : ProgramInputs.used (scalarAlgorithm ℚ).program =
    {Sum.inl ((0:Fin 1),0), Sum.inr ((0:Fin 1),0)} := by
  decide

-- A skinny product has few outputs but many essential left inputs.
example (P : MatrixAlgorithm (ZMod 2) 5 3 1) (hP : P.Correct) : 15 ≤ 2*P.cost := by
  simpa using left_input_size_le_twice_cost (by norm_num : 0 < 1) P hP

-- The same argument covers dot products, including finite fields.
example {l : ℕ} (P : MatrixAlgorithm (ZMod 2) 1 l 1) (hP : P.Correct) :
    l ≤ 2*P.cost := by
  simpa using left_input_size_le_twice_cost (by norm_num : 0 < 1) P hP

-- Unequal tensor dimensions remain unequal after taking powers.
example {R : ℕ} (h : Tensor.RankAtMost
    (Tensor.power (matrixMultiplicationTensor (K := ℚ) 2 3 1) 2) R) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := ℚ) 4 9 1) R := by
  simpa using rectangular_rank_of_power h

example {R : ℕ} (h : Tensor.RankAtMost
    (matrixMultiplicationTensor (K := ZMod 2) 2 3 1) R) :
    6 ≤ R ∧ 3 ≤ R ∧ 2 ≤ R := by
  simpa using rectangular_rank_pair_lower (by norm_num : 0 < 2)
    (by norm_num : 0 < 3) (by norm_num : 0 < 1) h

-- The recursive block program is field-generic, even in characteristic two.
example {R : ℕ} (h : Tensor.RankAtMost
    (matrixMultiplicationTensor (K := ZMod 2) 2 3 1) R) (t : ℕ) :
    ∃ P : MatrixAlgorithm (ZMod 2) (2^t) (3^t) (1^t), P.Correct ∧
      P.cost ≤ rectangularBlockCost R (2*R*(2*3+3*1+2*1)) t :=
  rectangular_power_programs (by norm_num) (by norm_num) (by norm_num) h t

-- The zero shape still needs a scalar product, but constant time has exponent zero.
example : ShapeAdmissibleExponent ℚ 0 0 0 0 := by
  intro ε hε
  refine ⟨1,by norm_num,?_⟩
  intro n hn
  rw [OAI.MatrixMultiplication.Arithmetic.innerSize_zero n]
  refine ⟨scalarAlgorithm ℚ,scalarAlgorithm_correct ℚ,?_⟩
  simpa using Real.one_le_rpow (by exact_mod_cast hn) hε.le

example (spectral : SpectralInput) : ShapeAdmissibleExponent ℂ 1 1 0.5 2 := by
  have hh := mainTarget spectral 1 1 0.5 (by norm_num) (by norm_num) (by norm_num)
  norm_num [shapeBound,thinThreshold] at hh ⊢
  exact hh

example (spectral : SpectralInput) : ShapeAdmissibleExponent ℂ 1 1 1 2.25 := by
  have hh := mainTarget spectral 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num [shapeBound,thinThreshold] at hh ⊢
  exact hh

example (spectral : SpectralInput) : ShapeAdmissibleExponent ℂ 2 1 1 3.125 := by
  have hh := mainTarget spectral 2 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num [shapeBound,thinThreshold] at hh ⊢
  exact hh

example {E : ℝ} (hE : E < 2) : ¬ShapeAdmissibleExponent ℂ 1 1 0.5 E := by
  intro h
  have hh := shapeAdmissible_left_lower h
  linarith

example (spectral : SpectralInput) : rectangularOmega ℂ 2 ≤ 3.125 := by
  have hh := rectangularOmega_le_of_admissibleExponent
    ((curveTarget spectral 2 (by norm_num)).1)
  norm_num [curveBound] at hh ⊢
  exact hh

example (spectral : SpectralInput) : rectangularOmega ℂ 0.5=2 :=
  (curveTarget spectral 0.5 (by norm_num)).2 (by norm_num)

example (spectral : SpectralInput) {k : ℝ} (hk : 0 ≤ k) (hhalf : k ≤ 0.5) :
    rectangularOmega ℂ k=2 := (curveTarget spectral k hk).2 hhalf

example (spectral : SpectralInput) : rectangularOmega ℂ 3 ≤ 4+1/12 := by
  have hh := rectangularOmega_le_of_admissibleExponent
    ((curveTarget spectral 3 (by norm_num)).1)
  norm_num [curveBound] at hh ⊢
  exact hh

-- The curve is proved for real parameters, not merely rational ones.
example (spectral : SpectralInput) :
    rectangularOmega ℂ (Real.sqrt 2) ≤ curveBound (Real.sqrt 2) :=
  rectangularOmega_le_of_admissibleExponent
    ((curveTarget spectral _ (Real.sqrt_nonneg 2)).1)

example (spectral : SpectralInputOver (AlgebraicClosure ℚ)) :
    ShapeAdmissibleExponent ℚ 2 1 1 3.125 := by
  have hh := shapeAdmissible_all_fields ℚ spectral
    (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
  norm_num [shapeBound,thinThreshold] at hh ⊢
  exact hh

example (spectral : SpectralInputOver (AlgebraicClosure (ZMod 2))) :
    rectangularOmega (ZMod 2) 0.5=2 :=
  rectangularOmega_all_fields_eq_two (ZMod 2) spectral (by norm_num) (by norm_num)

example (F : Type) [Field F] (spectral : SpectralInputOver (AlgebraicClosure F))
    {a b c : ℝ} (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c) :
    ShapeAdmissibleExponent F a b c (shapeBound a b c) :=
  shapeAdmissible_all_fields F spectral hba hcb hc

-- A fixed coefficient-descent loss can be absorbed by a positive power gap.
example : ∃ t : ℕ, 1 ≤ t ∧ (9:ℝ) < 2^t := by
  simpa using exists_power_absorb_constant (r := 1) (ρ := 2) (C := 9)
    (by norm_num) (by norm_num) (by norm_num)

end Rectangular
