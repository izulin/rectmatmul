module

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.MatrixMultiplication

@[expose] public section

/-! Rectangular tensor powers and the three elementary flattening bounds. -/

namespace Rectangular

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

noncomputable section

variable {K : Type*} [Field K]

/-- Relabel a rectangular tensor power without changing its exact rank bound. -/
theorem rectangular_rank_of_power {m l q N R : ℕ}
    (h : Tensor.RankAtMost
      (Tensor.power (matrixMultiplicationTensor (K := K) m l q) N) R) :
    Tensor.RankAtMost
      (matrixMultiplicationTensor (K := K) (m^N) (l^N) (q^N)) R := by
  classical
  let em : Fin (m^N) ≃ (Fin N → Fin m) := Fintype.equivOfCardEq (by simp)
  let el : Fin (l^N) ≃ (Fin N → Fin l) := Fintype.equivOfCardEq (by simp)
  let eq : Fin (q^N) ≃ (Fin N → Fin q) := Fintype.equivOfCardEq (by simp)
  let fx := fun x : Fin (m^N) × Fin (l^N) => fun i => (em x.1 i, el x.2 i)
  let fy := fun y : Fin (l^N) × Fin (q^N) => fun i => (el y.1 i, eq y.2 i)
  let fz := fun z : Fin (q^N) × Fin (m^N) => fun i => (eq z.1 i, em z.2 i)
  have hp := h.pullback fx fy fz
  have heq : Tensor.pullback fx fy fz
      (Tensor.power (matrixMultiplicationTensor (K := K) m l q) N) =
      matrixMultiplicationTensor (K := K) (m^N) (l^N) (q^N) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, matrixMultiplicationTensor,
      fx, fy, fz, Fintype.prod_boole, forall_and, ← funext_iff,
      em.injective.eq_iff, el.injective.eq_iff, eq.injective.eq_iff]
  rwa [heq] at hp

/-- The output flattening has an identity minor of size m*q. -/
theorem rectangular_rank_output_lower {m l q R : ℕ} (hl : 0 < l)
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := K) m l q) R) :
    m*q ≤ R := by
  classical
  let j : Fin l := ⟨0, hl⟩
  have hh := h.card_le_of_identity
    (fun i : Fin m × Fin q => (i.1,j))
    (fun i : Fin m × Fin q => (j,i.2))
    (fun i : Fin m × Fin q => (i.2,i.1)) (by
      intro i k
      simp only [matrixMultiplicationTensor]
      split_ifs <;> simp_all [Prod.ext_iff])
  simpa using hh

/-- Permuting the legs supplies the other two flattenings. -/
theorem rectangular_rank_pair_lower {m l q R : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hq : 0 < q)
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := K) m l q) R) :
    m*l ≤ R ∧ l*q ≤ R ∧ m*q ≤ R := by
  have h1 := Tensor.matrixCoefficients_cyclic_rank h
  have h2 := Tensor.matrixCoefficients_cyclic_rank h1
  have ha := rectangular_rank_output_lower (K := K) hq h1
  have hb := rectangular_rank_output_lower (K := K) hm h2
  have hc := rectangular_rank_output_lower (K := K) hl h
  exact ⟨by simpa [Nat.mul_comm] using ha,
    by simpa [Nat.mul_comm] using hb, hc⟩

end

end Rectangular
