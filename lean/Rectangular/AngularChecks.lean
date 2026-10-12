module

public import Rectangular.AngularConstraint

/-! Scalar degeneracies, tight budgets, and character orientation checks for step 8. -/

namespace Rectangular

open Real
open OAI.MatrixMultiplication.AuxiliarySeparation

-- Both quadratic endpoint coefficients may vanish.
example : PairRatio 1 1 1 1 := by
  apply pairRatio_of_quadratic (by norm_num) (by norm_num)
  intro t ht
  norm_num

-- At p=q=0.5, both offsets may vanish; no division by offsets is allowed.
example : PairRatio 0.5 0.5 0 0 := by
  apply pairRatio_of_quadratic (by norm_num) (by norm_num)
  intro t ht
  norm_num

-- The square equality point has all six offsets equal to 0.5.
example : PairRatio 0.75 0.75 0.5 0.5 := by
  apply pairRatio_of_quadratic (by norm_num) (by norm_num)
  intro t ht
  nlinarith [sq_nonneg (t-1)]

-- A zero leading coefficient still forces the linear coefficient nonnegative.
example {B C : ℝ} (hC : 0≤C)
    (h : ∀ ⦃t : ℝ⦄, 0<t → 0≤B*t+C) : 0≤B := by
  have hh := positive_quadratic_linear_bound (A := 0) (B := B) (C := C)
    (by norm_num) hC (by intro t ht; simpa using h ht)
  simpa using hh

-- The pair bound handles p=1 without a positive (1-p) denominator.
example {c d : ℝ} (hc : 0≤c) (hd : 0≤d) (h : PairRatio 1 1 c d) :
    1 ≤ sqrt (c*d) := by
  simpa using h.offset_product_lower (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hc hd

-- Too-small offsets cannot support two unit parameters.
example : ¬PairRatio 1 1 0.5 0.5 := by
  intro h
  have hh := h (by norm_num : (0:ℝ)<1)
  norm_num at hh

-- Three saturated row budgets admit the square angular equality point.
example : Real.pi/2 ≤ arccos (sqrt 0.75)+arccos (sqrt 0.75)+arccos (sqrt 0.75) := by
  have hp : PairRatio 0.75 0.75 0.5 0.5 := by
    apply pairRatio_of_quadratic (by norm_num) (by norm_num)
    intro t ht
    nlinarith [sq_nonneg (t-1)]
  exact pair_offset_angular_constraint (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp hp hp

-- Derivative comparison works from the positive side at an equality point.
example {f : ℝ → ℝ} {a : ℝ} (hf : HasDerivAt f a 0) (h0 : f 0=1)
    (h : ∀ ⦃ε : ℝ⦄, 0<ε → f ε≤1+ε) : a≤1 :=
  right_derivative_compare hf ((hasDerivAt_id (0:ℝ)).const_add 1)
    (by simpa using h0) h

-- Only the elementary lower bound is differentiated, including p=1 and zero c.
example : HasDerivAt (fun ε : ℝ => (1+ε)^1*(1+ε)^1) 2 0 := by
  have hh := joint_lower_derivative (p := 1) (q := 1) (c := 0) (d := 0)
    (r := 1) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh ⊢
  exact hh

variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]

-- Every permutation is included, with its own dot parameters.
example (χ : Character K) (i : Fin 6) :
    Real.pi/2 ≤ arccos (sqrt (χ.permutedCharacter i).pX)+
      arccos (sqrt (χ.permutedCharacter i).pY)+arccos (sqrt (χ.permutedCharacter i).pZ) :=
  character_angular_constraint (χ.permutedCharacter i)

-- The zero-parameter case is included in the actual character theorem.
example (χ : Character K) (_hp : χ.pX=0) :
    Real.pi/2 ≤ arccos (sqrt χ.pX)+arccos (sqrt χ.pY)+arccos (sqrt χ.pZ) :=
  character_angular_constraint χ

-- The weighted bound no longer asks the caller for an angular premise.
example {a b c : ℝ} (hba : b≤a) (hcb : c≤b) (hc : 0≤c) :
    WeightedCharacterBound a b c (shapeBound a b c) :=
  characterBoundTarget a b c hba hcb hc

end Rectangular
