module

public import Rectangular.Target
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison
public import Mathlib.Data.Finset.Option

@[expose] public section

/-! Essential inputs must feed counted gates. Free input loads therefore
do not invalidate the largest-leg lower exponent. The finite bound loses
only a factor two, which disappears in exponent comparisons. -/

namespace Rectangular

open OAI.MatrixMultiplication
open Arithmetic
open scoped BigOperators

noncomputable section

namespace ProgramInputs

variable {F Input : Type*} [Field F] [DecidableEq Input]

def source : {r : ℕ} → Program F Input r → Fin r → Option Input
  | 0, .nil => Fin.elim0
  | _+1, .step p g =>
    Fin.cases
      (match g with | .input x => some x | _ => none) (source p)

def gateInputs {r : ℕ} (p : Program F Input r) : Gate F Input (Fin r) → Finset Input
  | .input _ | .constant _ => ∅
  | .add i j | .sub i j | .mul i j => (source p i).toFinset ∪ (source p j).toFinset

def used : {r : ℕ} → Program F Input r → Finset Input
  | 0, .nil => ∅
  | _+1, .step p g => used p ∪ gateInputs p g

omit [Field F] in
theorem gateInputs_card {r : ℕ} (p : Program F Input r) (g : Gate F Input (Fin r)) :
    (gateInputs p g).card ≤ 2*g.cost := by
  have hopt (o : Option Input) : o.toFinset.card ≤ 1 := by cases o <;> simp
  cases g with
  | constant z => simp [gateInputs, Gate.cost]
  | input x => simp [gateInputs, Gate.cost]
  | add i j =>
    exact (Finset.card_union_le _ _).trans (by
      have hi := hopt (source p i)
      have hj := hopt (source p j)
      simpa [Gate.cost] using Nat.add_le_add hi hj)
  | sub i j =>
    exact (Finset.card_union_le _ _).trans (by
      have hi := hopt (source p i)
      have hj := hopt (source p j)
      simpa [Gate.cost] using Nat.add_le_add hi hj)
  | mul i j =>
    exact (Finset.card_union_le _ _).trans (by
      have hi := hopt (source p i)
      have hj := hopt (source p j)
      simpa [Gate.cost] using Nat.add_le_add hi hj)

omit [Field F] in
theorem used_card {r : ℕ} (p : Program F Input r) : (used p).card ≤ 2*p.cost := by
  induction p with
  | nil => simp [used, Program.cost]
  | step p g ih =>
    have hh := (Finset.card_union_le (used p) (gateInputs p g)).trans
      (Nat.add_le_add ih (gateInputs_card p g))
    simpa [used, Program.cost, Nat.mul_add] using hh

omit [Field F] [DecidableEq Input] in
theorem source_none_of_positive {r : ℕ} (p : Program F Input r) (i : Fin r)
    (hi : 0 < p.registerCost i) : source p i = none := by
  induction p with
  | nil => exact Fin.elim0 i
  | @step r p g ih =>
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      cases g <;> simp_all [source, Program.registerCost, Gate.cost]
    · intro hi
      exact ih j hi

/-- If an input never enters a counted gate, changing it leaves every
register except its direct input loads unchanged. -/
theorem eval_eq_of_not_used {r : ℕ} (p : Program F Input r) {x : Input}
    (hx : x ∉ used p) {u v : Input → F} (huv : ∀ y, y ≠ x → u y=v y) :
    ∀ i : Fin r, source p i ≠ some x → p.eval u i=p.eval v i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    have hxold : x ∉ used p := fun hh => hx (Finset.mem_union_left _ hh)
    have hxgate : x ∉ gateInputs p g := fun hh => hx (Finset.mem_union_right _ hh)
    have hold := ih hxold
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hs
      change g.eval u (p.eval u)=g.eval v (p.eval v)
      cases g with
      | constant z => rfl
      | input y => exact huv y (by intro hy; subst y; exact hs rfl)
      | add i j =>
        have havoids : source p i ≠ some x ∧ source p j ≠ some x := by
          simpa [gateInputs, Option.mem_def] using hxgate
        exact congrArg₂ (·+·) (hold i havoids.1) (hold j havoids.2)
      | sub i j =>
        have havoids : source p i ≠ some x ∧ source p j ≠ some x := by
          simpa [gateInputs, Option.mem_def] using hxgate
        exact congrArg₂ (·-·) (hold i havoids.1) (hold j havoids.2)
      | mul i j =>
        have havoids : source p i ≠ some x ∧ source p j ≠ some x := by
          simpa [gateInputs, Option.mem_def] using hxgate
        exact congrArg₂ (·*·) (hold i havoids.1) (hold j havoids.2)
    · intro hs
      exact hold j hs

end ProgramInputs

variable {F : Type*} [Field F]

/-- Every left input influences a matrix-product output when c is positive. -/
theorem left_input_used {m l q : ℕ} (hq : 0 < q)
    (P : MatrixAlgorithm F m l q) (hP : P.Correct) (i : Fin m) (j : Fin l) :
    Sum.inl (i,j) ∈ ProgramInputs.used P.program := by
  classical
  by_contra hx
  let k : Fin q := ⟨0,hq⟩
  let A := elementaryLeft (F := F) i j
  let B := elementaryRight (F := F) j k
  have hl : 1 ≤ l := by have hh := j.isLt; omega
  have hsource := ProgramInputs.source_none_of_positive P.program (P.output i k)
    (by have h := P.one_le_output_registerCost hl hP i k; omega)
  have heval := ProgramInputs.eval_eq_of_not_used P.program hx
    (u := matrixInputs (0 : Matrix (Fin m) (Fin l) F) B)
    (v := matrixInputs A B) (by
      intro y hy
      cases y with
      | inl y =>
        rcases y with ⟨ii,jj⟩
        by_cases hi : ii=i <;> by_cases hj : jj=j <;> simp_all [matrixInputs, A, elementaryLeft]
      | inr y => rfl)
    (P.output i k) (by rw [hsource]; simp)
  change P.eval 0 B i k=P.eval A B i k at heval
  rw [hP 0 B, hP A B] at heval
  simp [A,B,elementaryProduct] at heval

/-- At most two fresh essential inputs can enter one arithmetic operation. -/
theorem left_input_size_le_twice_cost {m l q : ℕ} (hq : 0 < q)
    (P : MatrixAlgorithm F m l q) (hP : P.Correct) : m*l ≤ 2*P.cost := by
  classical
  let f : Fin m × Fin l → {x // x ∈ ProgramInputs.used P.program} :=
    fun x => ⟨Sum.inl x,left_input_used hq P hP x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Sum.inl.inj (congrArg Subtype.val h)
  have hh := Fintype.card_le_of_injective f hf
  have hcard : m*l ≤ (ProgramInputs.used P.program).card := by
    simpa using hh
  exact hcard.trans (ProgramInputs.used_card P.program)

/-- The largest sorted tensor leg supplies the lower exponent, in the
actual program model rather than by charging free input loads. -/
theorem shapeAdmissible_left_lower {a b c E : ℝ}
    (h : ShapeAdmissibleExponent F a b c E) : a+b ≤ E := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C,hC,hprogram⟩ := h ε hε
  apply AuxiliarySeparation.rpow_exponent_le_of_nat_bound (C := 2*C)
  intro n hn
  obtain ⟨P,hP,hcost⟩ := hprogram n hn
  have hq : 0 < innerSize n c := by have h := one_le_innerSize hn c; omega
  have hleft := left_input_size_le_twice_cost hq P hP
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    (n:ℝ)^(a+b) = (n:ℝ)^a*(n:ℝ)^b := Real.rpow_add hn0 a b
    _ ≤ (innerSize n a:ℝ)*(innerSize n b:ℝ) :=
      mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _)
        (Real.rpow_nonneg hn0.le b) (Nat.cast_nonneg _)
    _ ≤ 2*(P.cost:ℝ) := by exact_mod_cast hleft
    _ ≤ (2*C)*(n:ℝ)^(E+ε) := by nlinarith

end

end Rectangular
