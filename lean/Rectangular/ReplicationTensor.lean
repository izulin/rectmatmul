module

public import Rectangular.ReplicationPolynomial
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Degeneration

@[expose] public section

/-! An explicit finite degeneration from one enlarged convolution to independent
copies. The local maps use the Lagrange coordinates checked in the polynomial
module. All tensor equalities are coefficient identities over the base field.
-/

noncomputable section

namespace Rectangular.Replication

open Polynomial
open scoped BigOperators
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K] {m : ℕ}

def copies (m r s : ℕ) :
    Tensor K (Fin m × Fin r) (Fin m × Fin s) (Fin m × Fin (r + s - 1)) :=
  Tensor.directSum (fun _ : Fin m => convolution (K := K) r s)

/-- Input coefficient map, shifted so all parameter exponents are nonnegative. -/
def inputMap (nodes : Fin m → K) (r : ℕ) (x : Fin m × Fin r) (i : Fin (m * r)) : K[X] :=
  monomial (r - 1 - x.2.val) ((localBasis nodes r x.1 x.2).coeff i.val)

/-- Extract the Taylor coefficient at the output's point and scale it by its order. -/
def outputMap (nodes : Fin m → K) (r s : ℕ)
    (z : Fin m × Fin (r + s - 1)) (k : Fin (m * r + m * s - 1)) : K[X] :=
  monomial z.2.val ((taylor (nodes z.1) (X ^ k.val)).coeff z.2.val)

def family (nodes : Fin m → K) (r s : ℕ) :
    Tensor K[X] (Fin m × Fin r) (Fin m × Fin s) (Fin m × Fin (r + s - 1)) :=
  Tensor.restrict (inputMap nodes r) (inputMap nodes s) (outputMap nodes r s)
    (fun i j k => C (convolution (K := K) (m * r) (m * s) i j k))

/-- Contracting the convolution coefficients gives the chosen Taylor functional
of the product of the two input polynomials. -/
theorem convolution_coeff_sum {R S : ℕ} (P Q : K[X])
    (hP : P.natDegree < R) (hQ : Q.natDegree < S) (α : K) (c : ℕ) :
    (∑ i : Fin R, ∑ j : Fin S, ∑ k : Fin (R + S - 1),
      P.coeff i.val * Q.coeff j.val * (taylor α (X ^ k.val)).coeff c *
        convolution (K := K) R S i j k) = (taylor α (P * Q)).coeff c := by
  rw [taylor_product_coeff_sum P Q hP hQ α c]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (convolutionOutput i j)]
  · simp [convolutionOutput]
  · intro k _ hk
    have hne : i.val + j.val ≠ k.val := by
      intro heq
      apply hk
      apply Fin.ext
      exact heq.symm
    simp [convolution, hne]
  · simp

/-- The entire restricted coefficient is one parameter monomial. Its scalar
coefficient is the Taylor coefficient of a localized polynomial product. -/
theorem family_apply (nodes : Fin m → K) (hinj : Function.Injective nodes) (r s : ℕ)
    (x : Fin m × Fin r) (y : Fin m × Fin s) (z : Fin m × Fin (r + s - 1)) :
    family nodes r s x y z =
      monomial (r - 1 - x.2.val + (s - 1 - y.2.val) + z.2.val)
        ((taylor (nodes z.1)
          (localBasis nodes r x.1 x.2 * localBasis nodes s y.1 y.2)).coeff z.2.val) := by
  unfold family Tensor.restrict inputMap outputMap
  simp only [monomial_mul_monomial, monomial_mul_C]
  simpa only [map_sum] using
    congrArg (monomial (r - 1 - x.2.val + (s - 1 - y.2.val) + z.2.val))
      (convolution_coeff_sum _ _ (localBasis_natDegree_lt nodes hinj r x.1 x.2)
        (localBasis_natDegree_lt nodes hinj s y.1 y.2) (nodes z.1) z.2.val)

theorem inputMap_degree (nodes : Fin m → K) (r : ℕ)
    (x : Fin m × Fin r) (i : Fin (m * r)) :
    (inputMap nodes r x i).degree ≤ ((r - 1 : ℕ) : WithBot ℕ) := by
  apply (degree_monomial_le (r - 1 - x.2.val) _).trans
  exact WithBot.coe_le_coe.mpr (Nat.sub_le _ _)

theorem outputMap_degree (nodes : Fin m → K) (r s : ℕ)
    (z : Fin m × Fin (r + s - 1)) (k : Fin (m * r + m * s - 1)) :
    (outputMap nodes r s z k).degree ≤ ((r + s - 2 : ℕ) : WithBot ℕ) := by
  have hz : z.2.val ≤ r + s - 2 := by
    have hz := z.2.isLt
    omega
  exact (degree_monomial_le z.2.val _).trans (WithBot.coe_le_coe.mpr hz)

theorem family_vanishes (nodes : Fin m → K) (hinj : Function.Injective nodes)
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (x : Fin m × Fin r) (y : Fin m × Fin s) (z : Fin m × Fin (r + s - 1))
    {n : ℕ} (hn : n < r + s - 2) : (family nodes r s x y z).coeff n = 0 := by
  rw [family_apply nodes hinj, coeff_monomial]
  split_ifs with heq
  · have ha := x.2.isLt
    have hb := y.2.isLt
    exact localBasis_product_vanishes nodes x.1 y.1 z.1 x.2 y.2 (by omega)
  · rfl

theorem family_leading (nodes : Fin m → K) (hinj : Function.Injective nodes)
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (x : Fin m × Fin r) (y : Fin m × Fin s) (z : Fin m × Fin (r + s - 1)) :
    (family nodes r s x y z).coeff (r + s - 2) = copies (K := K) m r s x y z := by
  rw [family_apply nodes hinj, coeff_monomial]
  have ha := x.2.isLt
  have hb := y.2.isLt
  by_cases hc : z.2.val = x.2.val + y.2.val
  · have heq : r - 1 - x.2.val + (s - 1 - y.2.val) + z.2.val = r + s - 2 := by omega
    rw [ite_eq_left heq, hc, localBasis_product_leading nodes hinj]
    by_cases hx : x.1 = z.1 <;> by_cases hy : y.1 = z.1 <;>
      simp_all [copies, Tensor.directSum, convolution, eq_comm]
  · have heq : r - 1 - x.2.val + (s - 1 - y.2.val) + z.2.val ≠ r + s - 2 := by omega
    simp [heq, copies, Tensor.directSum, convolution, Ne.symm hc]

/-- The finite certificate: the leading power is r+s-2, and the three local
map degree bounds are r-1, s-1, r+s-2. -/
def degeneration (nodes : Fin m → K) (hinj : Function.Injective nodes)
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    Tensor.PolynomialRestrictionDegeneration
      (convolution (K := K) (m * r) (m * s)) (copies (K := K) m r s)
      (r + s - 2) (r - 1) (s - 1) (r + s - 2) where
  leftMap := inputMap nodes r
  middleMap := inputMap nodes s
  rightMap := outputMap nodes r s
  left_degree := inputMap_degree nodes r
  middle_degree := inputMap_degree nodes s
  right_degree := outputMap_degree nodes r s
  vanishes := fun x y z _ hn => family_vanishes nodes hinj hr hs x y z hn
  leading := family_leading nodes hinj hr hs

end Rectangular.Replication
