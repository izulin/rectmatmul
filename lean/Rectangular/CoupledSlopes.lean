module

public import Rectangular.RealConcaveSlopes

@[expose] public section
noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology

structure CoupledTripling (P Q : ℝ → ℝ) : Prop where
  left : ∀ ⦃s⦄, 0 < s → 2 * P s + Q s ≤ P (3*s+1)
  right : ∀ ⦃s⦄, 0 < s → 2 * Q s + P s ≤ Q (3*s+1)

theorem tripling_slope_compare {P Q : ℝ → ℝ} {A B : ℝ}
    (htrip : ∀ ⦃s⦄, 0 < s → 2*P s+Q s ≤ P (3*s+1))
    (hP : Tendsto (fun s => P s/s) atTop (𝓝 A))
    (hQ : Tendsto (fun s => Q s/s) atTop (𝓝 B)) : B ≤ A := by
  have hindex : Tendsto (fun s : ℝ => 3*s+1) atTop atTop := by
    simpa only [id_eq] using
      (tendsto_atTop_add_const_right atTop (1:ℝ)
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<3)))
  have hinv := real_const_div_tendsto_zero (1:ℝ)
  have hright := (hP.comp hindex).mul ((tendsto_const_nhds (x := (3:ℝ))).add hinv)
  have hright' : Tendsto (fun s => P (3*s+1)/s) atTop (𝓝 (A*3)) := by
    convert hright.congr' ((eventually_gt_atTop (0:ℝ)).mono ?_) using 1
    · simp
    intro s hs
    have hi : 3*s+1 ≠ 0 := by linarith
    change (P (3*s+1)/(3*s+1))*(3+1/s) = P (3*s+1)/s
    field_simp
  have hleft := (hP.const_mul 2).add hQ
  have hh := le_of_tendsto_of_tendsto hleft hright' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    have ht := div_le_div_of_nonneg_right (htrip hs) hs.le
    simpa only [add_div, mul_div_assoc] using ht)
  linarith

theorem CoupledTripling.slopes_equal {P Q : ℝ → ℝ} (h : CoupledTripling P Q)
    {A B : ℝ} (hP : Tendsto (fun s => P s/s) atTop (𝓝 A))
    (hQ : Tendsto (fun s => Q s/s) atTop (𝓝 B)) : A = B :=
  le_antisymm (tripling_slope_compare h.right hQ hP)
    (tripling_slope_compare h.left hP hQ)

/-- The exact real trajectory retains the additive shift in tripling. -/
def triplingPoint (s : ℝ) (n : ℕ) : ℝ := (3:ℝ)^n*(s+0.5)-0.5

theorem triplingPoint_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < triplingPoint s n := by
  have hp : (1:ℝ) ≤ 3^n := one_le_pow₀ (by norm_num)
  unfold triplingPoint
  nlinarith

theorem triplingPoint_succ (s : ℝ) (n : ℕ) :
    triplingPoint s (n+1) = 3*triplingPoint s n+1 := by
  simp only [triplingPoint, pow_succ]
  ring

theorem real_tripling_affine_bound {R : ℝ → ℝ} {D s : ℝ} (hs : 0 < s)
    (htrip : ∀ ⦃x⦄, 0 < x → 3*R x ≤ R (3*x+1))
    (hlim : Tendsto (fun x => R x/x) atTop (𝓝 D)) : R s ≤ D*(s+0.5) := by
  have hpow : Tendsto (fun n : ℕ => (3:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hindex : Tendsto (triplingPoint s) atTop atTop := by
    change Tendsto (fun n : ℕ => (3:ℝ)^n*(s+0.5)-0.5) atTop atTop
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-0.5:ℝ)
        (hpow.atTop_mul_const (by linarith : 0 < s+0.5))
  have hz := hpow.const_div_atTop (0.5:ℝ)
  have hscaled : Tendsto (fun n => triplingPoint s n/(3:ℝ)^n)
      atTop (𝓝 (s+0.5)) := by
    convert ((tendsto_const_nhds (x := s+0.5)).sub hz).congr (fun n => ?_) using 1
    · simp
    unfold triplingPoint
    field_simp
  have hprofile : Tendsto (fun n => R (triplingPoint s n)/(3:ℝ)^n)
      atTop (𝓝 (D*(s+0.5))) := by
    apply ((hlim.comp hindex).mul hscaled).congr
    intro n
    have hi := ne_of_gt (triplingPoint_pos hs n)
    change R (triplingPoint s n)/triplingPoint s n *
      (triplingPoint s n/(3:ℝ)^n) = R (triplingPoint s n)/(3:ℝ)^n
    field_simp
  have hgrowth (n : ℕ) : (3:ℝ)^n*R s ≤ R (triplingPoint s n) := by
    induction n with
    | zero => simp [triplingPoint]
    | succ n ih =>
      have hh := htrip (triplingPoint_pos hs n)
      rw [triplingPoint_succ]
      simp only [pow_succ]
      nlinarith
  apply ge_of_tendsto hprofile
  apply Eventually.of_forall
  intro n
  apply (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<3) n)).mpr
  simpa only [mul_comm] using hgrowth n

theorem CoupledTripling.sum_bound {P Q : ℝ → ℝ} (h : CoupledTripling P Q)
    {L s : ℝ} (hP : Tendsto (fun x => P x/x) atTop (𝓝 L))
    (hQ : Tendsto (fun x => Q x/x) atTop (𝓝 L)) (hs : 0 < s) :
    P s+Q s ≤ L*(2*s+1) := by
  have hr : Tendsto (fun x => (P x+Q x)/x) atTop (𝓝 (2*L)) := by
    simpa only [add_div, ← two_mul] using hP.add hQ
  have hh := real_tripling_affine_bound hs (R := fun x => P x+Q x) (D := 2*L)
    (by intro x hx; have hp := h.left hx; have hq := h.right hx; linarith) hr
  nlinarith

end Rectangular
