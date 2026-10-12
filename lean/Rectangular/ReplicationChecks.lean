module

public import Rectangular.Replication
public import Mathlib.Algebra.Field.ZMod

/-! Boundary, orientation, and characteristic checks for the finite certificate. -/

namespace Rectangular

open Polynomial
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K] [Infinite K]

-- The one-copy case gives a finite certificate, with unequal input lengths.
example : Nonempty (Tensor.PolynomialRestrictionDegeneration
    (convolution (K := K) 2 3) (Replication.copies (K := K) 1 2 3) 3 1 2 3) :=
  ⟨convolution_replication (K := K) 1 (r := 2) (s := 3) (by norm_num) (by norm_num)⟩

-- The minimum lengths give a zero-leading-power certificate (ordinary restriction).
example : Nonempty (Tensor.PolynomialRestrictionDegeneration
    (convolution (K := K) 3 3) (Replication.copies (K := K) 3 1 1) 0 0 0 0) :=
  ⟨convolution_replication (K := K) 3 (r := 1) (s := 1) (by norm_num) (by norm_num)⟩

-- A non-square block grows in both dimensions, with no dot-parameter hypotheses.
example (χ : Character K) :
    2 * convolutionValue χ 2 3 ≤ convolutionValue χ 4 6 := by
  simpa using convolutionValue_replication χ 2 (by norm_num : 0 < 2) (by norm_num : 0 < 3)

-- All six individual orientations retain the same comparison.
example (χ : Character K) (i : Fin 6) :
    3 * convolutionValue (χ.permutedCharacter i) 1 2 ≤
      convolutionValue (χ.permutedCharacter i) 3 6 := by
  simpa using convolutionValue_replication (χ.permutedCharacter i) 3
    (by norm_num : 0 < 1) (by norm_num : 0 < 2)

-- An empty copy family is allowed, without requesting any interpolation points.
example (χ : Character K) : 0 ≤ convolutionValue χ 0 0 := by
  simpa using convolutionValue_replication χ 0 (by norm_num : 0 < 1) (by norm_num : 0 < 1)

-- Nonmatching sector labels kill the leading product coefficient.
example (nodes : Fin 2 → K) (hinj : Function.Injective nodes) :
    (taylor (nodes 0)
      (Replication.localBasis nodes 2 0 (1 : Fin 2) *
        Replication.localBasis nodes 1 1 (0 : Fin 1))).coeff 1 = 0 := by
  simpa using Replication.localBasis_product_leading nodes hinj
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 1)

-- The finite certificate works in characteristic two with two distinct points,
-- even though t^2-1 has only one root there. Infinitude is needed only by the
-- automatic-node choice and current character-monotonicity adapter.
example : Nonempty (Tensor.PolynomialRestrictionDegeneration
    (convolution (K := ZMod 2) 4 2) (Replication.copies (K := ZMod 2) 2 2 1) 1 1 0 1) := by
  let nodes : Fin 2 → ZMod 2 := fun i => (i.val : ZMod 2)
  have hinj : Function.Injective nodes := by decide
  exact ⟨Replication.degeneration nodes hinj (by norm_num : 0 < 2) (by norm_num : 0 < 1)⟩

end Rectangular
