module

public import Rectangular.CommonSlopes

/-! Boundary and orientation checks for manuscript Lemma 5.1. -/

namespace Rectangular

open Filter Set
open scoped Topology
open OAI.MatrixMultiplication.AuxiliarySeparation

private theorem affine_curve {L c : ℝ} (hL : 0<L) (hc : 0≤c) :
    PositiveConcaveCurve (fun s => L*(s+c)) where
  pos := by intro s hs; exact mul_pos hL (by linarith)
  mono := by
    intro s hs t ht hst
    apply mul_le_mul_of_nonneg_left _ hL.le
    linarith
  concave := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro s hs t ht a b ha hb hab
    simp only [smul_eq_mul]
    have hrel : L*c*(a+b) = L*c := by rw [hab, mul_one]
    nlinarith [hrel]

private theorem affine_tripling {L c d : ℝ} (hL : 0≤L) (hb : c+d≤1) :
    CoupledTripling (fun s => L*(s+c)) (fun s => L*(s+d)) where
  left := by
    intro s hs
    have hh := mul_nonneg hL (sub_nonneg.mpr hb)
    nlinarith
  right := by
    intro s hs
    have hh := mul_nonneg hL (sub_nonneg.mpr hb)
    nlinarith

-- The entire offset budget may lie on one side; zero offsets are allowed.
example : ∃ L c d : ℝ,
    AffineSlopePair (fun s => 2*s) (fun s => 2*(s+1)) L c d := by
  have hp := affine_curve (L := 2) (c := 0) (by norm_num) (by norm_num)
  have hq := affine_curve (L := 2) (c := 1) (by norm_num) (by norm_num)
  have ht := affine_tripling (L := 2) (c := 0) (d := 1) (by norm_num) (by norm_num)
  simpa only [add_zero] using common_slopes_affine_bounds hp hq ht

-- Unequal fractional offsets exhaust the budget, without requiring symmetry.
example : ∃ L c d : ℝ,
    AffineSlopePair (fun s => 3*(s+0.25)) (fun s => 3*(s+0.75)) L c d :=
  common_slopes_affine_bounds
    (affine_curve (by norm_num) (by norm_num))
    (affine_curve (by norm_num) (by norm_num))
    (affine_tripling (by norm_num) (by norm_num))

-- A strict budget and two zero offsets also satisfy the hypotheses.
example : CoupledTripling (fun s => s) (fun s => s) := by
  simpa using affine_tripling (L := 1) (c := 0) (d := 0) (by norm_num) (by norm_num)

-- The canonical supremum offset of an affine row is exactly its intercept.
example {L c : ℝ} (hL : 0<L) : profileOffset (fun s => L*(s+c)) L = c := by
  have heq (s : ℝ) : profileResidual (fun x => L*(x+c)) L s = c := by
    unfold profileResidual
    field_simp [ne_of_gt hL]
    ring
  have hset : {v | ∃ s : ℝ, 0<s ∧ v=profileResidual (fun x => L*(x+c)) L s} = {c} := by
    ext v
    simp only [heq, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, hv⟩; exact hv
    · intro hv; exact ⟨1, by norm_num, hv⟩
  unfold profileOffset
  rw [hset, csSup_singleton]

-- Positive constants are concave but cannot satisfy coupled tripling.
example : ¬CoupledTripling (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) := by
  intro h
  have hh := h.left (by norm_num : (0:ℝ)<1)
  norm_num at hh

-- Different linear slopes violate coupling even though each curve is admissible.
example : ¬CoupledTripling (fun s => s) (fun s => 2*s) := by
  intro h
  have hh := h.left (by norm_num : (0:ℝ)<2)
  norm_num at hh

-- Taking two offset suprema must respect mixed, rather than merely same-point, bounds.
example : ¬CoupledTripling (fun s => s+0.75) (fun s => s+0.75) := by
  intro h
  have hh := h.left (by norm_num : (0:ℝ)<1)
  norm_num at hh

-- The increment statement works at noninteger positions and increments.
example {P Q : ℝ → ℝ} {L c d : ℝ} (h : AffineSlopePair P Q L c d) :
    P 0.25+L*0.75 ≤ P 1 := by
  simpa only [show (0.25+0.75:ℝ)=1 by norm_num] using
    h.left_increment (s := 0.25) (t := 0.75) (by norm_num) (by norm_num)

variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]

-- All six orientations retain their own parameters and exchanged partners.
example (χ : Character K) (i : Fin 6) (hp : 0<(χ.permutedCharacter i).pX) :
    ∃ L c d : ℝ, AffineSlopePair (poweredRow (χ.permutedCharacter i))
      (poweredRow (χ.permutedCharacter i).swap23Character) L c d :=
  character_common_slopes (χ.permutedCharacter i) hp

-- The endpoint pX=1 is included, with the full residual limits.
example (χ : Character K) (hp : χ.pX=1) :
    ∃ L c d : ℝ, AffineSlopePair (poweredRow χ) (poweredRow χ.swap23Character) L c d :=
  character_common_slopes χ (by rw [hp]; norm_num)

-- At pX=0, the required positive-parameter premise is unavailable.
omit [Infinite K] [IsAlgClosed K] in
example (χ : Character K) (hp : χ.pX=0) : ¬0<χ.pX := by simp [hp]

end Rectangular
