module

public import Rectangular.AngularBound
public import Rectangular.Target

@[expose] public section

/-! Connection of the analytic pilot to the oriented character interface.
This module isolates the angular implication. `AngularConstraint.lean`
proves its premise in step 8; it is not included in `SpectralInput`.
-/

namespace Rectangular

open OAI.MatrixMultiplication AuxiliarySeparation

/-- The tensor/profile angular statement. No symmetry of a character is assumed. -/
def AngularConstraintTarget : Prop :=
  ∀ χ : Character ℂ,
    Real.pi / 2 ≤ Real.arccos (Real.sqrt χ.pY) +
      Real.arccos (Real.sqrt χ.pZ) + Real.arccos (Real.sqrt χ.pX)

/-- The remaining character-bound obligation reduces to the angular constraint. -/
theorem characterBound_of_angular (hangular : AngularConstraintTarget) :
    CharacterBoundTarget := by
  intro a b c hba hcb hc χ
  exact weighted_bound_of_angular hba hcb hc
    χ.pY_nonneg χ.pY_le_one χ.pZ_nonneg χ.pZ_le_one
    χ.pX_nonneg χ.pX_le_one (hangular χ)

end Rectangular
