module

public import Rectangular.RescaledProfiles

/-! Boundary, orientation, and rounding checks for manuscript Lemma 4.1. -/

namespace Rectangular

open Filter Set
open scoped Topology
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K] [Infinite K]

-- Unequal positive lengths have the correct rank-envelope bounds.
example (χ : Character K) : 1 ≤ rescaledProfile χ 1 3 ∧ rescaledProfile χ 1 3 ≤ 4 := by
  have h := rescaledProfile_bounds χ (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 3)
  norm_num at h
  exact h

-- Homogeneity accepts a noninteger positive scale.
example (χ : Character K) :
    rescaledProfile χ (3 / 2) 3 = (3 / 2) * rescaledProfile χ 1 2 := by
  simpa using rescaledProfile_homogeneous χ (r := 1) (s := 2) (t := 3 / 2)
    (by norm_num) (by norm_num) (by norm_num)

-- Input interchange retains the character orientation, for all six permutations.
example (χ : Character K) (i : Fin 6) :
    rescaledProfile (χ.permutedCharacter i).swap23Character.cyclicCharacter 3 1 =
      rescaledProfile (χ.permutedCharacter i) 1 3 :=
  rescaledProfile_input_swap (χ.permutedCharacter i) 1 3

-- A zero dot parameter does not obstruct construction or the full ceiling limit.
example (χ : Character K) (_hp : χ.pX = 0) :
    Tendsto (fun n : ℕ => convolutionValue χ (rounded 1 n) (rounded 2 n) / n)
      atTop (𝓝 (rescaledProfile χ 1 2)) :=
  rescaledProfile_limit χ (by norm_num) (by norm_num)

-- Unequal fixed additions to the rounded coordinates do not change the limit.
example (χ : Character K) :
    Tendsto (fun n : ℕ => convolutionValue χ (rounded 1 n + 1) (rounded 3 n + 5) / n)
      atTop (𝓝 (rescaledProfile χ 1 3)) :=
  rescaledProfile_shift_limit χ (by norm_num) (by norm_num) 1 5

-- Continuity is joint on the positive quadrant, even at irrational lengths.
example (χ : Character K) :
    ContinuousAt (fun z : ℝ × ℝ => rescaledProfile χ z.1 z.2) (1, Real.sqrt 2) :=
  rescaledProfile_continuousAt χ (by norm_num) (by positivity)

-- The second coordinate retains powered midpoint concavity.
example [IsAlgClosed K] (χ : Character K) (hp : 0 < χ.pX) :
    rescaledProfile χ 1 1 ^ (1 / χ.pX) + rescaledProfile χ 1 3 ^ (1 / χ.pX) ≤
      2 * rescaledProfile χ 1 2 ^ (1 / χ.pX) := by
  have hconc := rescaledProfile_concave_second χ hp (by norm_num : (0 : ℝ) < 1)
  have hfun := hconc.2
  have h := hfun
    (x := 1) (y := 3) (by norm_num) (by norm_num)
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [smul_eq_mul] at h
  simp only [one_div]
  linarith only [h]

-- The first coordinate uses pY, without imposing character symmetry.
example [IsAlgClosed K] (χ : Character K) (hp : 0 < χ.pY) :
    ConcaveOn ℝ (Ioi 0) (fun r => rescaledProfile χ r 2 ^ (1 / χ.pY)) :=
  rescaledProfile_concave_first χ hp (by norm_num)

-- Tripling uses the exchanged character as its middle term, at unequal lengths.
example [IsAlgClosed K] (χ : Character K) (hp : 0 < χ.pX) :
    2 * rescaledProfile χ 2 1 ^ (1 / χ.pX) +
      rescaledProfile χ.swap23Character 2 1 ^ (1 / χ.pX) ≤
        rescaledProfile χ 2 5 ^ (1 / χ.pX) := by
  have h := rescaledProfile_tripling χ hp (r := 2) (s := 1) (by norm_num) (by norm_num)
  norm_num at h
  simpa using h

end Rectangular
