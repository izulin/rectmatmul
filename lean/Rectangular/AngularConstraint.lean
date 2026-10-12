module

public import Rectangular.CommonSlopes
public import Rectangular.ProfileIncrements
public import Rectangular.OffsetGeometry
public import Rectangular.AngularCharacter

@[expose] public section
noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K]

theorem character_input_swap_involutive (χ : Character K) :
    χ.swap23Character.cyclicCharacter.swap23Character.cyclicCharacter=χ := by
  cases χ
  rfl

/-- The reverse of the Y,Z orientation is the Z,Y partner of the Z row. -/
theorem character_yz_reverse (χ : Character K) :
    χ.swap23Character.cyclicCharacter.swap23Character.swap23Character.cyclicCharacter =
      χ.cyclicCharacter.swap23Character := by
  cases χ
  rfl

variable [Infinite K]

theorem rescaledProfile_positive_homogeneous (χ : Character K) :
    PositiveHomogeneousProfile (rescaledProfile χ) where
  pos := by intro r s hr hs; exact rescaledProfile_pos χ hr hs
  homogeneous := by intro r s t hr hs ht; exact rescaledProfile_homogeneous χ hr hs ht

theorem AffineSlopePair.left_row_bounds (χ : Character K) {L c d : ℝ}
    (h : AffineSlopePair (poweredRow χ) (poweredRow χ.swap23Character) L c d) :
    PoweredRowBounds (rescaledProfile χ) χ.pX L c where
  slope_pos := h.slope_pos
  offset_nonneg := h.left_nonneg
  increment := by
    intro s t hs ht
    simpa only [profilePoweredRow, poweredRow] using h.left_increment hs ht
  upper := by
    intro s hs
    simpa only [profilePoweredRow, poweredRow] using h.left_upper hs

theorem AffineSlopePair.right_row_bounds (χ : Character K) {L c d : ℝ}
    (h : AffineSlopePair (poweredRow χ) (poweredRow χ.swap23Character) L c d) :
    PoweredRowBounds (rescaledProfile χ.swap23Character) χ.swap23Character.pX L d where
  slope_pos := h.slope_pos
  offset_nonneg := h.right_nonneg
  increment := by
    intro s t hs ht
    simpa only [profilePoweredRow, poweredRow] using h.right_increment hs ht
  upper := by
    intro s hs
    simpa only [profilePoweredRow, poweredRow] using h.right_upper hs

/-- Equation (23) (`eq:ratio-bound`) in the proof of Proposition 5.2
(`prop:angular-cap`); Appendix G supplies the finite-increment justification. -/
theorem character_profile_pair_ratio (χ : Character K) {L M c d : ℝ}
    (hp : 0<χ.pX) (hq : 0<χ.pY)
    (hP : PoweredRowBounds (rescaledProfile χ) χ.pX L c)
    (hQ : PoweredRowBounds (rescaledProfile χ.swap23Character.cyclicCharacter)
      χ.swap23Character.cyclicCharacter.pX M d) : PairRatio χ.pX χ.pY c d := by
  have heq : (fun r s => rescaledProfile χ s r) =
      rescaledProfile χ.swap23Character.cyclicCharacter := by
    funext r s
    exact (rescaledProfile_input_swap χ s r).symm
  have hQ' : PoweredRowBounds (fun r s => rescaledProfile χ s r) χ.pY M d := by
    rw [heq]
    simpa only [Character.cyclicCharacter_pX, Character.swap23Character_pZ] using hQ
  intro t ht
  have hh := profile_pair_ratio_bound (rescaledProfile_positive_homogeneous χ)
    hP hQ' hp hq ht (by norm_num : (0:ℝ)<1)
  simpa only [mul_one, one_mul] using hh

/-- Proposition 5.2 (`prop:angular-cap`), equation (22) (`eq:angular-cap`),
with all six offsets kept in their own orientations. The proof follows the
rigorous finite-increment route of Appendix G (`app:slopes-angular`). -/
theorem character_angular_constraint [IsAlgClosed K] (χ : Character K) :
    Real.pi/2 ≤ Real.arccos (Real.sqrt χ.pX)+Real.arccos (Real.sqrt χ.pY)+
      Real.arccos (Real.sqrt χ.pZ) := by
  by_cases hx : χ.pX=0
  · simp only [hx, Real.sqrt_zero, Real.arccos_zero]
    linarith [Real.arccos_nonneg (Real.sqrt χ.pY), Real.arccos_nonneg (Real.sqrt χ.pZ)]
  by_cases hy : χ.pY=0
  · simp only [hy, Real.sqrt_zero, Real.arccos_zero]
    linarith [Real.arccos_nonneg (Real.sqrt χ.pX), Real.arccos_nonneg (Real.sqrt χ.pZ)]
  by_cases hz : χ.pZ=0
  · simp only [hz, Real.sqrt_zero, Real.arccos_zero]
    linarith [Real.arccos_nonneg (Real.sqrt χ.pX), Real.arccos_nonneg (Real.sqrt χ.pY)]
  have hpX : 0<χ.pX := lt_of_le_of_ne χ.pX_nonneg (Ne.symm hx)
  have hpY : 0<χ.pY := lt_of_le_of_ne χ.pY_nonneg (Ne.symm hy)
  have hpZ : 0<χ.pZ := lt_of_le_of_ne χ.pZ_nonneg (Ne.symm hz)
  obtain ⟨LX, a, b, hX⟩ := character_common_slopes χ hpX
  obtain ⟨LY, c, d, hY⟩ := character_common_slopes χ.swap23Character.cyclicCharacter
    (by simpa using hpY)
  obtain ⟨LZ, e, f, hZ⟩ := character_common_slopes χ.cyclicCharacter (by simpa using hpZ)
  have hXY : PairRatio χ.pX χ.pY a c := character_profile_pair_ratio χ hpX hpY
    (hX.left_row_bounds χ) (hY.left_row_bounds _)
  have hXZ : PairRatio χ.pX χ.pZ b e := by
    have hh := character_profile_pair_ratio χ.swap23Character
      (by simpa using hpX) (by simpa using hpZ) (hX.right_row_bounds χ)
      (by simpa only [character_swap23_involutive] using hZ.left_row_bounds χ.cyclicCharacter)
    simpa only [Character.swap23Character_pX, Character.swap23Character_pY] using hh
  have hYZ : PairRatio χ.pY χ.pZ d f := by
    have hh := character_profile_pair_ratio χ.swap23Character.cyclicCharacter.swap23Character
      (by simpa using hpY) (by simpa using hpZ)
      (hY.right_row_bounds χ.swap23Character.cyclicCharacter)
      (by rw [character_yz_reverse]; exact hZ.right_row_bounds χ.cyclicCharacter)
    simpa only [Character.swap23Character_pX, Character.swap23Character_pY,
      Character.cyclicCharacter_pX, Character.cyclicCharacter_pZ,
      Character.swap23Character_pZ] using hh
  exact pair_offset_angular_constraint χ.pX_nonneg χ.pX_le_one
    χ.pY_nonneg χ.pY_le_one χ.pZ_nonneg χ.pZ_le_one
    hX.left_nonneg hX.right_nonneg hY.left_nonneg hY.right_nonneg
    hZ.left_nonneg hZ.right_nonneg hX.budget hY.budget hZ.budget hXY hXZ hYZ

theorem angularConstraintTarget : AngularConstraintTarget := by
  intro χ
  have hh := character_angular_constraint χ
  linarith

/-- The weighted character bound now has no unproved angular premise. -/
theorem characterBoundTarget : CharacterBoundTarget :=
  characterBound_of_angular angularConstraintTarget

end Rectangular
