module

public import Rectangular.AffineOffsets
public import Rectangular.RescaledProfiles

@[expose] public section
noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K] [Infinite K]

omit [Infinite K] in
theorem character_swap23_involutive (χ : Character K) :
    χ.swap23Character.swap23Character = χ := by
  cases χ
  rfl

/-- The first-coordinate-one powered row, retaining its character orientation. -/
def poweredRow (χ : Character K) (s : ℝ) : ℝ :=
  rescaledProfile χ 1 s ^ (1/χ.pX)

theorem poweredRow_pos (χ : Character K) {s : ℝ} (hs : 0<s) :
    0 < poweredRow χ s :=
  Real.rpow_pos_of_pos (rescaledProfile_pos χ (by norm_num) hs) _

theorem poweredRow_mono (χ : Character K) (hp : 0<χ.pX) :
    MonotoneOn (poweredRow χ) (Ioi 0) := by
  intro s hs t ht hst
  apply Real.rpow_le_rpow (rescaledProfile_pos χ (by norm_num) hs).le
    (rescaledProfile_mono χ (by norm_num) hs le_rfl hst)
  positivity

theorem poweredRow_curve [IsAlgClosed K] (χ : Character K) (hp : 0<χ.pX) :
    PositiveConcaveCurve (poweredRow χ) where
  pos := by intro s hs; exact poweredRow_pos χ hs
  mono := poweredRow_mono χ hp
  concave := rescaledProfile_concave_second χ hp (by norm_num)

theorem poweredRow_coupled_tripling [IsAlgClosed K] (χ : Character K) (hp : 0<χ.pX) :
    CoupledTripling (poweredRow χ) (poweredRow χ.swap23Character) where
  left := by
    intro s hs
    simpa only [poweredRow, Character.swap23Character_pX] using
      rescaledProfile_tripling χ hp (by norm_num : (0:ℝ)<1) hs
  right := by
    intro s hs
    simpa only [poweredRow, Character.swap23Character_pX, character_swap23_involutive] using
      rescaledProfile_tripling χ.swap23Character (by simpa using hp)
        (by norm_num : (0:ℝ)<1) hs

/-- Lemma 5.1 (`lem:intercepts`), proved in Appendix G (`app:slopes-angular`),
including the limits and canonical residual offsets. -/
theorem character_common_slopes [IsAlgClosed K] (χ : Character K) (hp : 0<χ.pX) :
    ∃ L c d : ℝ, AffineSlopePair (poweredRow χ) (poweredRow χ.swap23Character) L c d :=
  common_slopes_affine_bounds (poweredRow_curve χ hp)
    (poweredRow_curve χ.swap23Character (by simpa using hp))
    (poweredRow_coupled_tripling χ hp)

end Rectangular
