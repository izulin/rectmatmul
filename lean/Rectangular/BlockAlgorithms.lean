module

public import Rectangular.Target
public import Rectangular.RectangularTensor
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Growth

@[expose] public section

/-! Uniform rectangular program bounds from one finite exact block. -/

namespace Rectangular

open OAI.MatrixMultiplication
open Foundation AuxiliarySeparation

noncomputable section

variable {F : Type*} [Field F]

/-- All choices of a finite block precede the input-size quantifier. -/
def ShapeRankBlocks (F : Type*) [Field F] (a b c E : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ B m l q R : ℕ,
    2 ≤ B ∧ 0 < m ∧ 0 < l ∧ 0 < q ∧
    (B:ℝ)^a ≤ m ∧ (B:ℝ)^b ≤ l ∧ (B:ℝ)^c ≤ q ∧
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) m l q) R ∧
    (R:ℝ) < (B:ℝ)^(E+δ)

def rectangularBlockCost (R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | t+1 => R*rectangularBlockCost R K t + K*R^t

/-- A fixed block identity recursively produces the required rectangular
dimensions. The flattening lower bounds pay for every linear combination. -/
theorem rectangular_power_programs {m l q R : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hq : 0 < q)
    (hRank : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) m l q) R) :
    ∀ t : ℕ, ∃ P : Arithmetic.MatrixAlgorithm F (m^t) (l^t) (q^t),
      P.Correct ∧ P.cost ≤ rectangularBlockCost R (2*R*(m*l+l*q+m*q)) t := by
  obtain ⟨hml, hlq, hmq⟩ := rectangular_rank_pair_lower hm hl hq hRank
  intro t
  induction t with
  | zero =>
    exact ⟨Arithmetic.scalarAlgorithm F, Arithmetic.scalarAlgorithm_correct F,
      by simp [rectangularBlockCost]⟩
  | succ t ih =>
    obtain ⟨P,hP,hcost⟩ := ih
    obtain ⟨Q,hQ,hQcost⟩ := Arithmetic.RecursiveBlock.rank_block_step hRank P hP
    have hmlt : m^t*l^t ≤ R^t := by
      rw [←mul_pow]; exact Nat.pow_le_pow_left hml t
    have hlqt : l^t*q^t ≤ R^t := by
      rw [←mul_pow]; exact Nat.pow_le_pow_left hlq t
    have hmqt : m^t*q^t ≤ R^t := by
      rw [←mul_pow]; exact Nat.pow_le_pow_left hmq t
    have hover : m*l*m^t*l^t + l*q*l^t*q^t + m*q*m^t*q^t ≤ (m*l+l*q+m*q)*R^t := by
      calc
        _ = (m*l)*(m^t*l^t)+(l*q)*(l^t*q^t)+(m*q)*(m^t*q^t) := by ring
        _ ≤ (m*l)*R^t+(l*q)*R^t+(m*q)*R^t :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hmlt)
            (Nat.mul_le_mul_left _ hlqt)) (Nat.mul_le_mul_left _ hmqt)
        _ = _ := by ring
    have hbound : Q.cost ≤ rectangularBlockCost R (2*R*(m*l+l*q+m*q)) (t+1) := by
      rw [hQcost, rectangularBlockCost]
      calc
        _ ≤ R*rectangularBlockCost R (2*R*(m*l+l*q+m*q)) t +
            2*R*((m*l+l*q+m*q)*R^t) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hcost) (Nat.mul_le_mul_left _ hover)
        _ = _ := by ring
    have result : ∃ Q : Arithmetic.MatrixAlgorithm F
        (m*m^t) (l*l^t) (q*q^t), Q.Correct ∧
        Q.cost ≤ rectangularBlockCost R (2*R*(m*l+l*q+m*q)) (t+1) :=
      ⟨Q,hQ,hbound⟩
    rw [pow_succ' m t, pow_succ' l t, pow_succ' q t]
    exact result

/-- Padding covers all three rounded dimensions at the same recursion depth. -/
theorem shape_power_padding_bound {B m l q : ℕ} (hB : 2 ≤ B)
    {a b c s C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (hC : 0 < C)
    (hm : (B:ℝ)^a ≤ m) (hl : (B:ℝ)^b ≤ l) (hq : (B:ℝ)^c ≤ q)
    (hpower : ∀ t : ℕ, ∃ P : Arithmetic.MatrixAlgorithm F (m^t) (l^t) (q^t),
      P.Correct ∧ (P.cost:ℝ) ≤ C*((B:ℝ)^s)^t) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm F (Arithmetic.innerSize n a)
        (Arithmetic.innerSize n b) (Arithmetic.innerSize n c),
        P.Correct ∧ (P.cost:ℝ) ≤ D*(n:ℝ)^s := by
  have hB0 : 0 < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  refine ⟨C*(B:ℝ)^s, mul_pos hC (Real.rpow_pos_of_pos hB0 s), ?_⟩
  intro n hn
  obtain ⟨t,hnt,htn⟩ := Arithmetic.exists_power_cover hB hn
  obtain ⟨P,hP,hcost⟩ := hpower t
  obtain ⟨Q,hQ,hQP⟩ := Arithmetic.MatrixAlgorithm.exists_restrict
    (Arithmetic.innerSize_le_pow ha hnt hm)
    (Arithmetic.innerSize_le_pow hb hnt hl)
    (Arithmetic.innerSize_le_pow hc hnt hq) P hP
  refine ⟨Q,hQ, ?_⟩
  calc
    (Q.cost:ℝ) ≤ (P.cost:ℝ) := by exact_mod_cast hQP
    _ ≤ C*((B:ℝ)^s)^t := hcost
    _ = C*((B^t:ℕ):ℝ)^s := by
      rw [Real.rpow_pow_comm hB0.le, Nat.cast_pow]
    _ ≤ C*((B:ℝ)*(n:ℝ))^s :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast htn) hs) hC.le
    _ = (C*(B:ℝ)^s)*(n:ℝ)^s := by
      rw [Real.mul_rpow hB0.le (Nat.cast_nonneg n)]; ring

/-- The recurrence is bounded by any strictly larger geometric rate. This
absorbs a possible logarithmic overhead at equality with a flattening. -/
theorem shape_uniform_costs_of_rankBlock {B m l q R : ℕ} (hB : 2 ≤ B)
    {a b c s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hm : 0 < m) (hl : 0 < l) (hq : 0 < q)
    (hcoverm : (B:ℝ)^a ≤ m) (hcoverl : (B:ℝ)^b ≤ l)
    (hcoverq : (B:ℝ)^c ≤ q)
    (hRank : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) m l q) R)
    (hrate : (R:ℝ) < (B:ℝ)^s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm F (Arithmetic.innerSize n a)
        (Arithmetic.innerSize n b) (Arithmetic.innerSize n c),
        P.Correct ∧ (P.cost:ℝ) ≤ C*(n:ℝ)^s := by
  let K := 2*R*(m*l+l*q+m*q)
  obtain ⟨C,hC,hbound⟩ := Arithmetic.geometric_cost_recurrence_bound
    (fun t => (rectangularBlockCost R K t:ℝ)) (R:ℝ) (K:ℝ) (R:ℝ) ((B:ℝ)^s)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hrate hrate.le (by
      intro t; simp [rectangularBlockCost])
  apply shape_power_padding_bound hB ha hb hc hs hC hcoverm hcoverl hcoverq
  intro t
  obtain ⟨P,hP,hcost⟩ := rectangular_power_programs hm hl hq hRank t
  exact ⟨P,hP,(by exact_mod_cast hcost : (P.cost:ℝ) ≤ (rectangularBlockCost R K t:ℝ)).trans (hbound t)⟩

/-- Positive matrix blocks exclude negative limiting rank exponents. -/
theorem shapeRankBlocks_nonneg {a b c E : ℝ}
    (hblocks : ShapeRankBlocks F a b c E) : 0 ≤ E := by
  by_contra hE
  have hEneg : E < 0 := lt_of_not_ge hE
  obtain ⟨B,m,l,q,R,hB,hm,hl,hq,_,_,_,hRank,hrate⟩ :=
    hblocks (-E/2) (by linarith)
  have hml := (rectangular_rank_pair_lower hm hl hq hRank).1
  have hR1 : (1:ℝ) ≤ R := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos hm hl)).trans hml
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hB1
    (show E+(-E/2) ≤ 0 by linarith)
  linarith

/-- Arbitrarily close finite block certificates suffice for an admissible
exponent; no finite block is required to attain the limiting exponent. -/
theorem shapeAdmissible_of_rankBlocks {a b c E : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hE : 0 ≤ E)
    (hblocks : ShapeRankBlocks F a b c E) : ShapeAdmissibleExponent F a b c E := by
  intro ε hε
  obtain ⟨B,m,l,q,R,hB,hm,hl,hq,hcoverm,hcoverl,hcoverq,hRank,hrate⟩ :=
    hblocks ε hε
  exact shape_uniform_costs_of_rankBlock hB ha hb hc (by linarith)
    hm hl hq hcoverm hcoverl hcoverq hRank hrate

end

end Rectangular
