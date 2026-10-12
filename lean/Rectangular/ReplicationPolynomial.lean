module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Local polynomial coordinates for replication. Raising a Lagrange cardinal
polynomial to the input length kills all unwanted Taylor coefficients at the
other interpolation points. No inverse Taylor series or roots of unity are used.
-/

noncomputable section

namespace Rectangular.Replication

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {m : ℕ}

/-- A polynomial of degree below `m*n`, with prescribed first nonzero Taylor
coefficient at its own point and higher vanishing at the other points. -/
def localBasis (nodes : Fin m → K) (n : ℕ) (h : Fin m) (a : Fin n) : K[X] :=
  (Lagrange.basis Finset.univ nodes h) ^ n * (X - C (nodes h)) ^ a.val

theorem localBasis_natDegree_lt (nodes : Fin m → K) (hinj : Function.Injective nodes)
    (n : ℕ) (h : Fin m) (a : Fin n) : (localBasis nodes n h a).natDegree < m * n := by
  have hdeg : (Lagrange.basis Finset.univ nodes h).natDegree = m - 1 := by
    simpa using Lagrange.natDegree_basis hinj.injOn (Finset.mem_univ h)
  have hbound : (localBasis nodes n h a).natDegree ≤ n * (m - 1) + a.val := by
    unfold localBasis
    apply natDegree_mul_le.trans
    apply add_le_add
    · simpa only [hdeg] using (natDegree_pow_le (p := Lagrange.basis Finset.univ nodes h)
        (n := n))
    · simp [natDegree_pow]
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel (by have := h.isLt; omega)
  have ha := a.isLt
  nlinarith

theorem localBasis_taylor_dvd_other (nodes : Fin m → K) (n : ℕ)
    (h l : Fin m) (a : Fin n) (hne : h ≠ l) :
    (X : K[X]) ^ n ∣ taylor (nodes l) (localBasis nodes n h a) := by
  have hx : (X : K[X]) ∣ taylor (nodes l) (Lagrange.basis Finset.univ nodes h) := by
    apply X_dvd_iff.mpr
    simpa using Lagrange.eval_basis_of_ne hne (Finset.mem_univ l)
  simp only [localBasis, taylor_mul, taylor_pow]
  exact (pow_dvd_pow_of_dvd hx n).mul_right _

theorem localBasis_taylor_dvd (nodes : Fin m → K) (n : ℕ)
    (h l : Fin m) (a : Fin n) :
    (X : K[X]) ^ a.val ∣ taylor (nodes l) (localBasis nodes n h a) := by
  by_cases heq : h = l
  · subst l
    simp only [localBasis, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C,
      add_sub_cancel_right]
    exact dvd_mul_left _ _
  · exact (pow_dvd_pow X a.isLt.le).trans (localBasis_taylor_dvd_other nodes n h l a heq)

theorem localBasis_taylor_leading (nodes : Fin m → K) (hinj : Function.Injective nodes)
    (n : ℕ) (h l : Fin m) (a : Fin n) :
    (taylor (nodes l) (localBasis nodes n h a)).coeff a.val = if h = l then 1 else 0 := by
  by_cases heq : h = l
  · subst l
    simp only [localBasis, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C,
      add_sub_cancel_right, ite_true]
    rw [coeff_mul_X_pow']
    simp only [le_refl, ite_true, Nat.sub_self]
    change constantCoeff (taylor (nodes h) (Lagrange.basis Finset.univ nodes h) ^ n) = 1
    rw [map_pow]
    change ((taylor (nodes h) (Lagrange.basis Finset.univ nodes h)).coeff 0) ^ n = 1
    simp [Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ h)]
  · rw [ite_eq_right heq]
    exact X_pow_dvd_iff.mp (localBasis_taylor_dvd_other nodes n h l a heq) a.val a.isLt

/-- Leading coefficients multiply once the lower coefficients vanish. -/
theorem coeff_mul_at_order {P Q : K[X]} {a b : ℕ}
    (hP : X ^ a ∣ P) (hQ : X ^ b ∣ Q) :
    (P * Q).coeff (a + b) = P.coeff a * Q.coeff b := by
  obtain ⟨U, rfl⟩ := hP
  obtain ⟨V, rfl⟩ := hQ
  have heq : (X ^ a * U) * (X ^ b * V) = X ^ (a + b) * (U * V) := by
    rw [pow_add]
    ring
  rw [heq]
  rw [coeff_X_pow_mul', coeff_X_pow_mul', coeff_X_pow_mul']
  simp only [le_refl, ite_true, Nat.sub_self]
  exact mul_coeff_zero U V

theorem localBasis_product_vanishes (nodes : Fin m → K) {r s : ℕ}
    (h j l : Fin m) (a : Fin r) (b : Fin s) {c : ℕ} (hc : c < a.val + b.val) :
    (taylor (nodes l) (localBasis nodes r h a * localBasis nodes s j b)).coeff c = 0 := by
  rw [taylor_mul]
  apply X_pow_dvd_iff.mp _ c hc
  rw [pow_add]
  exact mul_dvd_mul (localBasis_taylor_dvd nodes r h l a)
    (localBasis_taylor_dvd nodes s j l b)

theorem localBasis_product_leading (nodes : Fin m → K) (hinj : Function.Injective nodes)
    {r s : ℕ} (h j l : Fin m) (a : Fin r) (b : Fin s) :
    (taylor (nodes l) (localBasis nodes r h a * localBasis nodes s j b)).coeff
      (a.val + b.val) = if h = l ∧ j = l then 1 else 0 := by
  rw [taylor_mul, coeff_mul_at_order (localBasis_taylor_dvd nodes r h l a)
    (localBasis_taylor_dvd nodes s j l b), localBasis_taylor_leading nodes hinj,
    localBasis_taylor_leading nodes hinj]
  split_ifs <;> simp_all

/-- Expand a bounded-degree polynomial using a fixed finite coefficient vector. -/
theorem sum_coeff_monomials {n : ℕ} (P : K[X]) (hP : P.natDegree < n) :
    (∑ i : Fin n, C (P.coeff i.val) * X ^ i.val) = P := by
  calc
    _ = ∑ i ∈ Finset.range n, C (P.coeff i) * X ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i) n
    _ = P := (P.as_sum_range_C_mul_X_pow' hP).symm

/-- The Taylor coefficient of a product is a bilinear expression in the
two finite coefficient vectors. This identifies the convolution restriction. -/
theorem taylor_product_coeff_sum {R S : ℕ} (P Q : K[X])
    (hP : P.natDegree < R) (hQ : Q.natDegree < S) (α : K) (c : ℕ) :
    (taylor α (P * Q)).coeff c =
      ∑ i : Fin R, ∑ j : Fin S,
        P.coeff i.val * Q.coeff j.val * (taylor α (X ^ (i.val + j.val))).coeff c := by
  have hexpand : P * Q = ∑ i : Fin R, ∑ j : Fin S,
      C (P.coeff i.val * Q.coeff j.val) * X ^ (i.val + j.val) := by
    calc
      _ = (∑ i : Fin R, C (P.coeff i.val) * X ^ i.val) *
          (∑ j : Fin S, C (Q.coeff j.val) * X ^ j.val) := by
        rw [sum_coeff_monomials P hP, sum_coeff_monomials Q hQ]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_add, map_mul]
        ring
  rw [hexpand]
  simp only [map_sum, finsetSum_coeff, taylor_mul, taylor_C, coeff_C_mul]

end Rectangular.Replication
