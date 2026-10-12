module

public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import Rectangular.Bounds

@[expose] public section

/-!
# Targets for the rectangular formalization

These definitions state the results to be proved. They do not assert them.
We reuse the upstream division-free program model: additions, subtractions,
and multiplications cost one; input loads and constants cost zero.
`Arithmetic.innerSize n a` is the natural ceiling of `n ^ a`, and is used
for each of the three matrix dimensions.
-/

namespace Rectangular

open OAI.MatrixMultiplication

noncomputable section

/-- One constant works for all positive sizes, after fixing the shape and slack.
The program is correct for every pair of input matrices of the given sizes. -/
def ShapeAdmissibleExponent (F : Type*) [Field F] (a b c E : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm F
        (Arithmetic.innerSize n a) (Arithmetic.innerSize n b)
        (Arithmetic.innerSize n c),
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (E + ε)

/-- Matrix dimensions `(a,b,c)` correspond to dot-product weights `(pY,pZ,pX)`.
This keeps the orientation of the imported character interface. -/
def WeightedCharacterBound (a b c E : ℝ) : Prop :=
  ∀ χ : AuxiliarySeparation.Character ℂ,
    a * χ.pY + b * χ.pZ + c * χ.pX ≤ E

/-- Analytic target, proved in step 8 after discharging the angular premise.
It is not part of the cited spectral input. -/
def CharacterBoundTarget : Prop :=
  ∀ a b c : ℝ, b ≤ a → c ≤ b → 0 ≤ c →
    WeightedCharacterBound a b c (shapeBound a b c)

/-- Main result, stated directly as a uniform arithmetic cost bound. -/
def MainTarget : Prop :=
  ∀ a b c : ℝ, b ≤ a → c ≤ b → 0 ≤ c →
    ShapeAdmissibleExponent ℂ a b c (shapeBound a b c)

/-- Exact exponent in the size-optimal range, without introducing a
new infimum whose boundedness would itself need to be proved. -/
def SizeOptimalTarget : Prop :=
  ∀ a b c : ℝ, b ≤ a → c ≤ b → 0 ≤ c → c ≤ thinThreshold a b →
    ShapeAdmissibleExponent ℂ a b c (a + b) ∧
      ∀ E : ℝ, ShapeAdmissibleExponent ℂ a b c E → a + b ≤ E

/-- Rectangular curve and equality in its exponent-two range. -/
def CurveTarget : Prop :=
  ∀ k : ℝ, 0 ≤ k →
    Arithmetic.RectangularAdmissibleExponent ℂ k (curveBound k) ∧
      (k ≤ (0.5 : ℝ) → Arithmetic.rectangularOmega ℂ k = 2)

/-- The three-shape cost definition agrees with the existing one-parameter API. -/
theorem shapeAdmissible_one_k_one_iff (F : Type*) [Field F] (k E : ℝ) :
    ShapeAdmissibleExponent F 1 k 1 E ↔
      Arithmetic.RectangularAdmissibleExponent F k E := by
  unfold ShapeAdmissibleExponent Arithmetic.RectangularAdmissibleExponent
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hprogram⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    have h := hprogram n hn
    rw [Arithmetic.innerSize_one] at h
    exact h
  · intro h ε hε
    obtain ⟨C, hC, hprogram⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    rw [Arithmetic.innerSize_one]
    exact hprogram n hn

/-- The second branch cannot introduce a zero denominator on the stated domain. -/
theorem denseBranch_positive {a b c : ℝ}
    (hba : b ≤ a) (hcb : c ≤ b) (hc : 0 ≤ c)
    (hthin : ¬ c ≤ thinThreshold a b) : 0 < a ∧ 0 < b ∧ 0 < c := by
  have hb : 0 ≤ b := hc.trans hcb
  have ha : 0 ≤ a := hb.trans hba
  have hthreshold : 0 ≤ thinThreshold a b :=
    div_nonneg (mul_nonneg ha hb) (add_nonneg ha hb)
  have hcpos : 0 < c := hthreshold.trans_lt (lt_of_not_ge hthin)
  have hbpos : 0 < b := hcpos.trans_le hcb
  exact ⟨hbpos.trans_le hba, hbpos, hcpos⟩

-- Boundary checks for the target formulas; none proves a target above.
example : thinThreshold 0 0 = 0 := by norm_num [thinThreshold]
example : shapeBound 0 0 0 = 0 := by norm_num [shapeBound, thinThreshold]
example : shapeBound 1 0 0 = 1 := by norm_num [shapeBound, thinThreshold]
example : shapeBound 1 1 0.5 = 2 := by norm_num [shapeBound, thinThreshold]
example : shapeBound 1 1 1 = 2.25 := by norm_num [shapeBound, thinThreshold]
example : shapeBound 2 1 1 = 3.125 := by norm_num [shapeBound, thinThreshold]
example : curveBound 0 = 2 := by norm_num [curveBound]
example : curveBound 0.5 = 2 := by norm_num [curveBound]
example : curveBound 1 = 2.25 := by norm_num [curveBound]
example : curveBound 2 = 3.125 := by norm_num [curveBound]

end

end Rectangular
