module

public import Rectangular.ReplicationTensor
public import Rectangular.DiscreteConvolution

@[expose] public section

/-! Manuscript Lemma 2.2 (`lem:replication`) and its character consequence.
The finite proof uses local Lagrange polynomials, whereas Appendix E
(`app:replication`) uses polynomial division and evaluation.
Distinct nodes are chosen
over an infinite field; the finite certificate itself only needs distinct nodes.
The copy count may be zero, and both convolution input lengths are positive.
-/

noncomputable section

namespace Rectangular

open Polynomial
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K]

namespace Replication

def nodes [Infinite K] (m : ℕ) (i : Fin m) : K := interpolationNode m i.castSucc

theorem nodes_injective [Infinite K] (m : ℕ) : Function.Injective (nodes (K := K) m) := by
  intro i j h
  exact Fin.castSucc_injective _ (interpolationNode_injective (K := K) m h)

end Replication

/-- Lemma 2.2, equation (6) (`eq:replication`): exact finite replication
certificate, using polynomial local maps. -/
def convolution_replication [Infinite K] (m : ℕ) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    Tensor.PolynomialRestrictionDegeneration
      (convolution (K := K) (m * r) (m * s)) (Replication.copies (K := K) m r s)
      (r + s - 2) (r - 1) (s - 1) (r + s - 2) :=
  Replication.degeneration (Replication.nodes m) (Replication.nodes_injective m) hr hs

theorem value_replication_copies (χ : Character K) (m r s : ℕ) :
    χ.value (Replication.copies (K := K) m r s) = (m : ℝ) * convolutionValue χ r s := by
  simp [Replication.copies, χ.map_directSum, convolutionValue]

/-- Equation (17) (`eq:profile-replication`), following Lemma 2.2.
Replication is a checked finite construction, so character monotonicity
gives the scaling comparison required by the real-profile step. -/
theorem convolutionValue_replication [Infinite K] (χ : Character K) (m : ℕ)
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (m : ℝ) * convolutionValue χ r s ≤ convolutionValue χ (m * r) (m * s) := by
  -- Lemma 3.1 (`lem:degeneration-interpolation`), character-monotonicity
  -- consequence, provided by the pinned interpolation proof.
  have h := χ.value_polynomialRestrictionDegeneration_le
    (convolution_replication (K := K) m hr hs)
  simpa only [value_replication_copies, convolutionValue] using h

/-- Input-leg interchange preserves the same replication comparison. -/
theorem exchangedValue_replication [Infinite K] (χ : Character K) (m : ℕ)
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (m : ℝ) * exchangedValue χ r s ≤ exchangedValue χ (m * r) (m * s) := by
  simpa only [exchangedValue_eq] using convolutionValue_replication χ.swap23Character m hr hs

end Rectangular
