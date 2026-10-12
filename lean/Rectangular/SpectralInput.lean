module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds

public section

/-!
# The published spectral input

`SpectralInputOver K` is an explicit theorem hypothesis, not a new Lean axiom
or a proof of Strassen's theorem. `SpectralInput` is its complex specialization.
It contains only the finite-power rank
consequence needed below. It assumes no rectangular parameter inequality,
rounding lemma, or conversion from rank to arithmetic programs.

Source: Wigderson--Zuiddam, *Asymptotic spectra: Theory, applications and
extensions*, author version August 5, 2025, Definition 2.8, Example 2.20,
and Corollary 3.30 (printed pp. 20, 26--27, and 41).
https://www.math.ias.edu/~avi/PUBLICATIONS/Wigderson_Zuiddam_2025.pdf
The latter restates Strassen's spectral theorem. Asymptotic rank is the
infimum of the positive tensor-power rank roots. If all character values
are at most B, that infimum is at most B, so every positive rho > B admits
a finite power of rank strictly less than rho ^ N.

Finite index types live in `Type`, matching the upstream `Character` API.
Restriction is by arbitrary independent linear substitutions on the legs;
`RankAtMost` means an exact coefficient decomposition over the stated field.
Example 2.20 starts with an arbitrary field, so the same published input is
applicable over an algebraic closure in any characteristic for field descent.
-/

namespace Rectangular

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

/-- The upper-bound consequence of spectral duality, supplied explicitly to
later theorems. The tensor and numerical bounds are fixed before choosing N. -/
structure SpectralInputOver (K : Type) [Field K] : Prop where
  finite_power_bound :
    ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
      (T : Tensor K X Y Z) (B ρ : ℝ),
      T ≠ 0 → (∀ χ : Character K, χ.value T ≤ B) → 0 < ρ → B < ρ →
      ∃ N R : ℕ, 1 ≤ N ∧ Tensor.RankAtMost (Tensor.power T N) R ∧
        (R : ℝ) < ρ ^ N

/-- The original complex-field interface is retained unchanged. -/
abbrev SpectralInput := SpectralInputOver ℂ

/-- Independently checked easy direction: every exact power decomposition
bounds the corresponding power of every character value. -/
theorem character_power_le_rank {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (χ : Character ℂ) (T : Tensor ℂ X Y Z) {N R : ℕ}
    (h : Tensor.RankAtMost (Tensor.power T N) R) :
    χ.value T ^ N ≤ (R : ℝ) := by
  simpa only [χ.value_power] using χ.value_le_rank h

/-- Positive matrix dimensions give a nonzero coefficient tensor. -/
theorem matrixTensor_ne_zero {m l q : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hq : 0 < q) :
    matrixMultiplicationTensor (K := ℂ) m l q ≠ 0 := by
  let i : Fin m := ⟨0, hm⟩
  let j : Fin l := ⟨0, hl⟩
  let k : Fin q := ⟨0, hq⟩
  intro h
  have hentry := congrArg (fun T => T (i, j) (j, k) (k, i)) h
  simp at hentry

/-- Specialize the explicit spectral input to any positive rectangular block.
The character bound is a caller's obligation, not an assumed rectangular result. -/
theorem matrix_power_rank_bound (spectral : SpectralInput)
    {m l q : ℕ} (hm : 0 < m) (hl : 0 < l) (hq : 0 < q)
    {B ρ : ℝ}
    (hB : ∀ χ : Character ℂ,
      χ.value (matrixMultiplicationTensor (K := ℂ) m l q) ≤ B)
    (hρ : 0 < ρ) (hBρ : B < ρ) :
    ∃ N R : ℕ, 1 ≤ N ∧
      Tensor.RankAtMost
        (Tensor.power (matrixMultiplicationTensor (K := ℂ) m l q) N) R ∧
      (R : ℝ) < ρ ^ N :=
  spectral.finite_power_bound _ B ρ (matrixTensor_ne_zero hm hl hq) hB hρ hBρ

end Rectangular
