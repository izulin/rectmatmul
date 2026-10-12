module

public import Rectangular.DiscreteConvolution
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Integer boundary and orientation checks for the new discrete interfaces. -/

namespace Rectangular

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable (χ : Character ℂ)

-- The opposite initial boundary retains pY, rather than silently using pX.
example : convolutionValue χ 3 1 = (3 : ℝ) ^ χ.pY :=
  convolutionValue_one_right χ (by norm_num)

-- Exchanging the last two legs preserves the common first-leg parameter.
example : exchangedValue χ 1 3 = (3 : ℝ) ^ χ.pX := by
  rw [exchangedValue_eq, convolutionValue_one_left χ.swap23Character (by norm_num),
    Character.swap23Character_pX]
  norm_num

-- At the left dot-product boundary, midpoint concavity is an equality.
example (hp : 0 < χ.pX) :
    convolutionValue χ 1 3 ^ (1 / χ.pX) +
      convolutionValue χ 1 1 ^ (1 / χ.pX) =
      2 * convolutionValue χ 1 2 ^ (1 / χ.pX) := by
  rw [convolutionValue_one_left_power χ (by norm_num) hp,
    convolutionValue_one_left_power χ (by norm_num) hp,
    convolutionValue_one_left_power χ (by norm_num) hp]
  norm_num

-- The smallest tripling case is sharp, including its exchanged middle leg.
example (hp : 0 < χ.pX) :
    2 * convolutionValue χ 1 1 ^ (1 / χ.pX) +
      exchangedValue χ 1 1 ^ (1 / χ.pX) =
      convolutionValue χ 1 3 ^ (1 / χ.pX) := by
  rw [exchangedValue_eq, convolutionValue_one_left χ.swap23Character (by norm_num)]
  rw [convolutionValue_one_left_power χ (by norm_num) hp,
    convolutionValue_one_left_power χ (by norm_num) hp]
  norm_num

-- The input-swap identity is valid for unequal lengths; symmetry is not assumed.
example : convolutionValue χ.swap23Character.cyclicCharacter 3 2 =
    convolutionValue χ 2 3 := convolutionValue_input_swap χ 2 3

-- Each of the six orientations has its own powered tripling bound.
example (i : Fin 6) (hp : 0 < (χ.permutedCharacter i).pX) :
    2 * convolutionValue (χ.permutedCharacter i) 2 1 ^
        (1 / (χ.permutedCharacter i).pX) +
      exchangedValue (χ.permutedCharacter i) 2 1 ^
        (1 / (χ.permutedCharacter i).pX) ≤
      convolutionValue (χ.permutedCharacter i) 2 4 ^
        (1 / (χ.permutedCharacter i).pX) := by
  simpa using convolution_tripling (χ.permutedCharacter i) (by norm_num : 0 < 2)
    (by norm_num : 0 < 1) hp

-- The unpowered boundary identities do not require a positive pX or pY.
example (hp : χ.pX = 0) : convolutionValue χ 1 3 = 1 := by
  rw [convolutionValue_one_left χ (by norm_num), hp, Real.rpow_zero]

end Rectangular
