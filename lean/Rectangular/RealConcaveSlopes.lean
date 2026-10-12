module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology

theorem real_const_div_tendsto_zero (C : ℝ) :
    Tendsto (fun x : ℝ => C/x) atTop (𝓝 0) := tendsto_id.const_div_atTop C

/-- The analytic hypotheses of a single powered profile, on its positive domain. -/
structure PositiveConcaveCurve (P : ℝ → ℝ) : Prop where
  pos : ∀ ⦃s⦄, 0 < s → 0 < P s
  mono : MonotoneOn P (Ioi 0)
  concave : ConcaveOn ℝ (Ioi 0) P

/-- Clamping the far endpoint makes the decreasing secants a globally defined function. -/
def tailSecant (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  (P (max 1 x + 1) - P 1) / max 1 x

theorem PositiveConcaveCurve.tailSecant_antitone {P : ℝ → ℝ}
    (h : PositiveConcaveCurve P) : Antitone (tailSecant P) := by
  intro x y hxy
  have hx : 0 < max 1 x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hy : 0 < max 1 y := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hh := h.concave.neg.secant_mono (a := 1) (x := max 1 x + 1)
    (y := max 1 y + 1) (by norm_num) (by change 0 < max 1 x+1; linarith)
    (by change 0 < max 1 y+1; linarith) (by linarith) (by linarith)
    (by have := max_le_max_left (1:ℝ) hxy; linarith)
  simp only [Pi.neg_apply, add_sub_cancel_right] at hh
  have heq (z : ℝ) : (-P (max 1 z+1)- -P 1)/max 1 z = -tailSecant P z := by
    unfold tailSecant
    ring
  rw [heq, heq] at hh
  linarith

theorem PositiveConcaveCurve.tailSecant_nonneg {P : ℝ → ℝ}
    (h : PositiveConcaveCurve P) (x : ℝ) : 0 ≤ tailSecant P x := by
  have hx : 0 < max 1 x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  apply div_nonneg _ hx.le
  exact sub_nonneg.mpr (h.mono (by norm_num)
    (by change 0 < max 1 x+1; linarith) (by linarith))

/-- A finite nonnegative limiting slope, without differentiability or an endpoint at zero. -/
theorem PositiveConcaveCurve.exists_slope {P : ℝ → ℝ} (h : PositiveConcaveCurve P) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun s => P s / s) atTop (𝓝 L) := by
  let L := ⨅ x : ℝ, tailSecant P x
  have hbounded : BddBelow (range (tailSecant P)) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact h.tailSecant_nonneg x⟩
  have hlim := tendsto_atTop_ciInf h.tailSecant_antitone hbounded
  have hL : 0 ≤ L := le_ciInf (fun x => h.tailSecant_nonneg x)
  have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop :=
    by simpa only [id_eq, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1:ℝ) tendsto_id
  have hsec := hlim.comp hshift
  have hinv := real_const_div_tendsto_zero (1 : ℝ)
  have hconst := real_const_div_tendsto_zero (P 1)
  have hh := hsec.mul ((tendsto_const_nhds (x := (1:ℝ))).sub hinv)
  have hresult : Tendsto
      (fun x => tailSecant P (x-1)*(1-1/x)+P 1/x) atTop (𝓝 L) := by
    simpa only [Function.comp_def, sub_zero, mul_one, add_zero] using hh.add hconst
  refine ⟨L, hL, ?_⟩
  apply hresult.congr'
  filter_upwards [eventually_gt_atTop (2:ℝ)] with x hx
  simp only [tailSecant, max_eq_right (by linarith : 1 ≤ x - 1), sub_add_cancel]
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Any fixed secant dominates the limiting slope. -/
theorem PositiveConcaveCurve.slope_le_secant {P : ℝ → ℝ} (h : PositiveConcaveCurve P)
    {L u v : ℝ} (hlim : Tendsto (fun s => P s / s) atTop (𝓝 L))
    (hu : 0 < u) (huv : u < v) : L ≤ (P v - P u) / (v - u) := by
  have hc := real_const_div_tendsto_zero (P v)
  have hv := real_const_div_tendsto_zero v
  have hfar := (hlim.sub hc).div (tendsto_const_nhds.sub hv) (by norm_num : (1:ℝ)-0≠0)
  have hfar' : Tendsto (fun x => (P x - P v) / (x - v)) atTop (𝓝 L) := by
    convert hfar.congr' ((eventually_gt_atTop (max v 0)).mono ?_) using 1
    · simp
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt (le_max_right _ _) hx)
    have hxv : x - v ≠ 0 := by have := lt_of_le_of_lt (le_max_left _ _) hx; linarith
    change (P x/x-P v/x)/(1-v/x) = (P x-P v)/(x-v)
    field_simp
  apply le_of_tendsto hfar'
  filter_upwards [eventually_gt_atTop v] with x hx
  exact h.concave.slope_anti_adjacent hu (by change 0 < x; linarith) huv hx

theorem PositiveConcaveCurve.increment_lower {P : ℝ → ℝ} (h : PositiveConcaveCurve P)
    {L s t : ℝ} (hlim : Tendsto (fun x => P x / x) atTop (𝓝 L))
    (hs : 0 < s) (ht : 0 < t) : P s + L * t ≤ P (s + t) := by
  have hh := h.slope_le_secant hlim hs (by linarith : s < s+t)
  have hh' := (le_div_iff₀ (by linarith : 0 < s+t-s)).mp hh
  nlinarith

theorem PositiveConcaveCurve.linear_lower {P : ℝ → ℝ} (h : PositiveConcaveCurve P)
    {L s : ℝ} (hlim : Tendsto (fun x => P x / x) atTop (𝓝 L))
    (hs : 0 < s) : L * s ≤ P s := by
  have hz := real_const_div_tendsto_zero s
  have hh : Tendsto (fun x => L*(s-s/x)) atTop (𝓝 (L*s)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := L)).mul ((tendsto_const_nhds (x := s)).sub hz)
  have hbound : ∀ᶠ x : ℝ in atTop, L * (s - s/x) ≤ P s := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have hu : 0 < s/x := div_pos hs (by linarith)
    have hus : s/x < s := (div_lt_iff₀ (by linarith : 0 < x)).mpr (by nlinarith)
    have hi := h.increment_lower hlim hu (sub_pos.mpr hus)
    have hp := h.pos hu
    simp only [add_sub_cancel] at hi
    linarith
  have := le_of_tendsto hh hbound
  simpa using this

end Rectangular
