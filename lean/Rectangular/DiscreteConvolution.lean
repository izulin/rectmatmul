module

public import Rectangular.EntropyPowerSum
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Character
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Character
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.ProductBounds
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Permutation
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Rank

@[expose] public section

/-! Integer convolution values for individual, possibly asymmetric characters.
The finite determinant and three-sector constructions are reused from the pinned
source; the powered bounds below are obtained without symmetrizing characters.
No replication or extension to real arguments is assumed here.

Writeup: Lemma 2.1 (`lem:openai-inputs`) supplies the finite constructions;
Lemma 3.3 (`lem:power-sum`) and Lemma 3.4 (`lem:discrete`) are their character
consequences below. The pinned source uses `6M` separation and determinant
splitting rather than the writeup's `2M` filter and coefficient construction.
-/

noncomputable section

namespace Rectangular

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K]

/-- `C_XY(r,s)` has coefficients `[i+j=k]`, with leg order fixed. -/
def convolutionValue (χ : Character K) (r s : ℕ) : ℝ :=
  χ.value (convolution (K := K) r s)

/-- Exchanging only the last two tensor legs gives `C_XZ(r,s)`. -/
def exchangedValue (χ : Character K) (r s : ℕ) : ℝ :=
  χ.value (Sector.exchangedConvolution (K := K) r s)

theorem exchangedValue_eq (χ : Character K) (r s : ℕ) :
    exchangedValue χ r s = convolutionValue χ.swap23Character r s := rfl

theorem convolutionValue_pos (χ : Character K) {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) : 0 < convolutionValue χ r s :=
  zero_lt_one.trans_le (χ.one_le_value (convolution_nonzero hr hs))

theorem convolutionValue_one_le (χ : Character K) {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) : 1 ≤ convolutionValue χ r s :=
  χ.one_le_value (convolution_nonzero hr hs)

theorem convolutionValue_le [Infinite K] (χ : Character K) (r s : ℕ) :
    convolutionValue χ r s ≤ (r + s - 1 : ℕ) :=
  χ.value_le_rank (convolution_rankAtMost r s)

/-- Coordinatewise inclusion is an actual tensor restriction. -/
theorem convolutionValue_mono (χ : Character K) {r s R S : ℕ}
    (hr : r ≤ R) (hs : s ≤ S) :
    convolutionValue χ r s ≤ convolutionValue χ R S := by
  have hout : r + s - 1 ≤ R + S - 1 := by omega
  have heq : Tensor.pullback (Fin.castLE hr) (Fin.castLE hs) (Fin.castLE hout)
      (convolution (K := K) R S) = convolution (K := K) r s := by
    funext i j k
    simp [Tensor.pullback, convolution]
  simpa only [heq, convolutionValue] using χ.value_pullback_le (convolution (K := K) R S)
    (Fin.castLE hr) (Fin.castLE hs) (Fin.castLE hout)

theorem convolutionValue_one_left (χ : Character K) {s : ℕ} (hs : 0 < s) :
    convolutionValue χ 1 s = (s : ℝ) ^ χ.pX := by
  have h := χ.value_reindex (convolution (K := K) 1 s)
    convolutionOneInputEquiv (Equiv.refl (Fin s)) (convolutionOneOutputEquiv s)
  rw [convolution_one_left_dotPairing, χ.value_cyclic_cyclic_dotPairing hs] at h
  exact h.symm

theorem convolutionValue_one_right (χ : Character K) {r : ℕ} (hr : 0 < r) :
    convolutionValue χ r 1 = (r : ℝ) ^ χ.pY := by
  have h := χ.value_reindex (convolution (K := K) r 1)
    (Equiv.refl (Fin r)) convolutionOneInputEquiv (convolutionRightOneOutputEquiv r)
  rw [convolution_one_right_dotPairing, χ.value_cyclic_dotPairing hr] at h
  exact h.symm

/-- The powered left boundary is exactly the second integer length. -/
theorem convolutionValue_one_left_power (χ : Character K) {s : ℕ}
    (hs : 0 < s) (hp : 0 < χ.pX) :
    convolutionValue χ 1 s ^ (1 / χ.pX) = (s : ℝ) := by
  rw [convolutionValue_one_left χ hs, ← Real.rpow_mul (Nat.cast_nonneg s),
    mul_one_div_cancel hp.ne', Real.rpow_one]

/-- Input swap changes the character as well as the two integer lengths. -/
theorem convolutionValue_input_swap (χ : Character K) (r s : ℕ) :
    convolutionValue χ.swap23Character.cyclicCharacter s r =
      convolutionValue χ r s := by
  let T : Tensor K (Fin r) (Fin s) (Fin (s + r - 1)) :=
    fun i j k => convolution (K := K) s r j i k
  have heq : Tensor.pullback (Equiv.refl (Fin r)) (Equiv.refl (Fin s))
      (finCongr (by omega : s + r - 1 = r + s - 1))
      (convolution (K := K) r s) = T := by
    funext i j k
    simp only [Tensor.pullback, Equiv.refl_apply, T, convolution, finCongr_apply,
      Fin.val_cast, Nat.add_comm]
  have h := χ.value_reindex (convolution (K := K) r s)
    (Equiv.refl (Fin r)) (Equiv.refl (Fin s))
    (finCongr (by omega : s + r - 1 = r + s - 1))
  rw [heq] at h
  exact h

/-- Lemma 3.3 (`lem:power-sum`), with the first input shared. This follows
from the checked finite separation construction and its arbitrary-law tag bound. -/
theorem sharedFirst_power_sum [IsAlgClosed K]
    (χ : Character K) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (hs : 0 < s) (B : Fin s → Tensor K X Y Z)
    (hB : ∀ i, B i ≠ 0) (hp : 0 < χ.pX) :
    (∑ i, χ.value (B i) ^ (1 / χ.pX)) ≤
      χ.value (sharedFirstTensor B) ^ (1 / χ.pX) := by
  let i : Fin s := ⟨0, hs⟩
  let : Nonempty (Fin s) := ⟨i⟩
  exact entropy_power_sum_le (fun i => χ.value (B i))
    (fun i => zero_lt_one.trans_le (χ.one_le_value (hB i))) hp
    (zero_lt_one.trans_le (χ.one_le_value (sharedFirstTensor_ne_zero_of_branch B i (hB i))))
    (fun q => χ.sharedFirst_tag q B hB)

/-- Lemma 3.4 (`lem:discrete`), second-coordinate concavity.
The finite two-sector construction gives powered midpoint concavity in
the second length, for each character individually. -/
theorem convolution_concavity_second [IsAlgClosed K] (χ : Character K)
    {r s : ℕ} (hr : 0 < r) (hs : 2 ≤ s) (hp : 0 < χ.pX) :
    convolutionValue χ r (s + 1) ^ (1 / χ.pX) +
      convolutionValue χ r (s - 1) ^ (1 / χ.pX) ≤
      2 * convolutionValue χ r s ^ (1 / χ.pX) := by
  have h := finite_product_concavity (ι := Unit)
    (fun _ => convolutionValue χ r s)
    (fun _ => convolutionValue χ r (s + 1))
    (fun _ => convolutionValue χ r (s - 1)) (fun _ => χ.pX)
    hp (by simp)
    (fun _ => convolutionValue_pos χ hr (by omega))
    (fun _ => convolutionValue_pos χ hr (by omega))
    (fun _ => convolutionValue_pos χ hr (by omega))
    (fun _ q hq₀ hq₁ => χ.convolution_concavity_tag r s hr hs q hq₀ hq₁)
  simpa using h

/-- Lemma 3.4 (`lem:discrete`), first-coordinate concavity.
The other coordinate uses its own dot-product parameter, `pY`. -/
theorem convolution_concavity_first [IsAlgClosed K] (χ : Character K)
    {r s : ℕ} (hr : 2 ≤ r) (hs : 0 < s) (hp : 0 < χ.pY) :
    convolutionValue χ (r + 1) s ^ (1 / χ.pY) +
      convolutionValue χ (r - 1) s ^ (1 / χ.pY) ≤
      2 * convolutionValue χ r s ^ (1 / χ.pY) := by
  have h := convolution_concavity_second χ.swap23Character.cyclicCharacter hs hr
    (by simpa using hp)
  simpa only [Character.cyclicCharacter_pX, Character.swap23Character_pZ,
    convolutionValue_input_swap] using h

/-- Lemma 3.4, equation (16) (`eq:discrete-tripling`).
The actual three-sector splitting gives the asymmetric powered tripling
inequality. Only the middle sector exchanges legs; no character symmetry is used. -/
theorem convolution_tripling [IsAlgClosed K] (χ : Character K)
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hp : 0 < χ.pX) :
    2 * convolutionValue χ r s ^ (1 / χ.pX) +
      exchangedValue χ r s ^ (1 / χ.pX) ≤
      convolutionValue χ r (3 * s + r - 1) ^ (1 / χ.pX) := by
  have h := entropy_power_sum_le
    (fun i : Fin 3 => χ.value (Sector.branchFamily (K := K) r s i))
    (fun i => zero_lt_one.trans_le (χ.one_le_value (Sector.branchFamily_nonzero hr hs i)))
    hp (convolutionValue_pos χ hr (by omega : 0 < 3 * s + r - 1))
    (fun q => by
      have htag := χ.sharedFirst_tag q (Sector.branchFamily (K := K) r s)
        (Sector.branchFamily_nonzero hr hs)
      rw [Sector.value_sharedFirst_branchFamily] at htag
      exact htag.trans (Sector.value_retained_le_source χ r s))
  simp only [Fin.sum_univ_three, Sector.branchFamily_zero, Sector.branchFamily_one,
    Sector.branchFamily_two, Sector.value_leftTensor, Sector.value_middleTensor,
    Sector.value_rightTensor] at h
  change convolutionValue χ r s ^ (1 / χ.pX) +
    exchangedValue χ r s ^ (1 / χ.pX) + convolutionValue χ r s ^ (1 / χ.pX) ≤
      convolutionValue χ r (3 * s + r - 1) ^ (1 / χ.pX) at h
  linarith

end Rectangular
