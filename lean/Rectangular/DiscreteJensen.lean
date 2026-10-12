module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ConcaveSlopes

@[expose] public section

/-! Supporting lines turn integer midpoint concavity into weighted inequalities
at rounded input lengths. No real-profile or character premise is used. -/

namespace Rectangular

open OAI.MatrixMultiplication.AuxiliarySeparation

theorem concave_sequence_backward_affine {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) (n k : ℕ) :
    u n + (k : ℝ) * (u (n + k + 1) - u (n + k)) ≤ u (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hD := hd (show n + k ≤ n + (k + 1) by omega)
    have hmul := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (α := ℝ) k)
    simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] at ih hD hmul ⊢
    linarith only [ih, hD, hmul]

theorem concave_sequence_supporting_line {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) (c n : ℕ) :
    u n ≤ u c + ((n : ℝ) - c) * (u (c + 1) - u c) := by
  by_cases h : n ≤ c
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hh := concave_sequence_backward_affine hd n k
    push_cast
    nlinarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge h)
    have hh := concave_sequence_le_affine hd c k
    push_cast
    nlinarith

theorem concave_sequence_weighted_le {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) (hm : Monotone u)
    (a b c : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1)
    (hmean : x * a + y * b ≤ (c : ℝ)) : x * u a + y * u b ≤ u c := by
  have hA := concave_sequence_supporting_line hd c a
  have hB := concave_sequence_supporting_line hd c b
  have hD : 0 ≤ u (c + 1) - u c := sub_nonneg.mpr (hm (by omega))
  calc
    _ ≤ x * (u c + ((a : ℝ) - c) * (u (c + 1) - u c)) +
        y * (u c + ((b : ℝ) - c) * (u (c + 1) - u c)) :=
      add_le_add (mul_le_mul_of_nonneg_left hA hx) (mul_le_mul_of_nonneg_left hB hy)
    _ = (x + y) * u c + (x * a + y * b - (x + y) * c) *
        (u (c + 1) - u c) := by ring
    _ = u c + (x * a + y * b - c) * (u (c + 1) - u c) := by rw [hxy]; ring
    _ ≤ u c := by
      have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmean) hD
      linarith

theorem positive_discrete_jensen {u : ℕ → ℝ}
    (hc : ∀ n, 2 ≤ n → u (n + 1) + u (n - 1) ≤ 2 * u n)
    (hm : ∀ {a b}, 0 < a → a ≤ b → u a ≤ u b)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hcc : 0 < c)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1)
    (hmean : x * a + y * b ≤ (c : ℝ)) : x * u a + y * u b ≤ u c := by
  let v : ℕ → ℝ := fun n => u (n + 1)
  have hd : Antitone (fun n => v (n + 1) - v n) := by
    apply antitone_increments_of_discrete_concavity
    intro n
    have hh := hc (n + 2) (by omega)
    have heq : n + 2 - 1 = n + 1 := by omega
    simpa only [v, heq, Nat.add_assoc] using hh
  have hv : Monotone v := fun _ _ hab => hm (by omega) (by omega)
  have hmean' : x * (a - 1 : ℕ) + y * (b - 1 : ℕ) ≤ ((c - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ b),
      Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one]
    nlinarith
  have hh := concave_sequence_weighted_le hd hv (a - 1) (b - 1) (c - 1)
    hx hy hxy hmean'
  simpa only [v, Nat.sub_add_cancel (by omega : 1 ≤ a),
    Nat.sub_add_cancel (by omega : 1 ≤ b), Nat.sub_add_cancel (by omega : 1 ≤ c)] using hh

end Rectangular
