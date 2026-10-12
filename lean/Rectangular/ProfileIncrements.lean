module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology

structure PositiveHomogeneousProfile (g : ℝ → ℝ → ℝ) : Prop where
  pos : ∀ ⦃r s⦄, 0<r → 0<s → 0<g r s
  homogeneous : ∀ ⦃r s t⦄, 0<r → 0<s → 0<t → g (t*r) (t*s)=t*g r s

def profilePoweredRow (g : ℝ → ℝ → ℝ) (p s : ℝ) : ℝ := g 1 s ^ (1/p)

structure PoweredRowBounds (g : ℝ → ℝ → ℝ) (p L c : ℝ) : Prop where
  slope_pos : 0<L
  offset_nonneg : 0≤c
  increment : ∀ ⦃s t⦄, 0<s → 0<t →
    profilePoweredRow g p s+L*t ≤ profilePoweredRow g p (s+t)
  upper : ∀ ⦃s⦄, 0<s → profilePoweredRow g p s ≤ L*(s+c)

theorem PositiveHomogeneousProfile.swap {g : ℝ → ℝ → ℝ}
    (h : PositiveHomogeneousProfile g) : PositiveHomogeneousProfile (fun r s => g s r) where
  pos := by intro r s hr hs; exact h.pos hs hr
  homogeneous := by intro r s t hr hs ht; exact h.homogeneous hs hr ht

theorem PositiveHomogeneousProfile.row_formula {g : ℝ → ℝ → ℝ}
    (h : PositiveHomogeneousProfile g) {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    g r s = r*g 1 (s/r) := by
  have hh := h.homogeneous (by norm_num : (0:ℝ)<1) (div_pos hs hr) hr
  simpa only [mul_one, mul_div_cancel₀ _ (ne_of_gt hr)] using hh

theorem profilePoweredRow_pos {g : ℝ → ℝ → ℝ} (h : PositiveHomogeneousProfile g)
    (p : ℝ) {s : ℝ} (hs : 0<s) : 0<profilePoweredRow g p s :=
  Real.rpow_pos_of_pos (h.pos (by norm_num) hs) _

theorem profilePoweredRow_recover {g : ℝ → ℝ → ℝ} (h : PositiveHomogeneousProfile g)
    {p s : ℝ} (hp : 0<p) (hs : 0<s) : (profilePoweredRow g p s)^p = g 1 s := by
  unfold profilePoweredRow
  rw [one_div, Real.rpow_inv_rpow (h.pos (by norm_num) hs).le (ne_of_gt hp)]

theorem PoweredRowBounds.ratio_increment {g : ℝ → ℝ → ℝ} {p L c s t : ℝ}
    (h : PoweredRowBounds g p L c) (hg : PositiveHomogeneousProfile g)
    (hs : 0<s) (ht : 0<t) :
    1+t/(s+c) ≤ profilePoweredRow g p (s+t)/profilePoweredRow g p s := by
  have hden : 0<s+c := by linarith [h.offset_nonneg]
  have hpos := profilePoweredRow_pos hg p hs
  have hu := mul_le_mul_of_nonneg_left (h.upper hs) (div_pos ht hden).le
  have heq : (t/(s+c))*(L*(s+c)) = L*t := by field_simp
  rw [heq] at hu
  have hi := h.increment hs ht
  apply (le_div_iff₀ hpos).mpr
  nlinarith

theorem PoweredRowBounds.profile_increment {g : ℝ → ℝ → ℝ} {p L c r s t : ℝ}
    (h : PoweredRowBounds g p L c) (hg : PositiveHomogeneousProfile g)
    (hp : 0<p) (hr : 0<r) (hs : 0<s) (ht : 0<t) :
    (1+t/(s+c*r))^p ≤ g r (s+t)/g r s := by
  have hu := div_pos hs hr
  have hv := div_pos ht hr
  have hden : 0<s+c*r := by nlinarith [mul_nonneg h.offset_nonneg hr.le]
  have hnorm : 0<s/r+c := by linarith [h.offset_nonneg]
  have heq : (t/r)/(s/r+c) = t/(s+c*r) := by field_simp
  have hi := h.ratio_increment hg hu hv
  have hbase : 0≤1+(t/r)/(s/r+c) := by positivity
  have hpow := Real.rpow_le_rpow hbase hi hp.le
  rw [heq] at hpow
  have hratio : g r (s+t)/g r s =
      (profilePoweredRow g p (s/r+t/r)/profilePoweredRow g p (s/r))^p := by
    rw [Real.div_rpow (profilePoweredRow_pos hg p (by linarith : 0<s/r+t/r)).le
      (profilePoweredRow_pos hg p hu).le,
      profilePoweredRow_recover hg hp (by linarith : 0<s/r+t/r),
      profilePoweredRow_recover hg hp hu,
      hg.row_formula hr (by linarith : 0<s+t), hg.row_formula hr hs, add_div]
    have hg1 := ne_of_gt (hg.pos (by norm_num : (0:ℝ)<1) hu)
    field_simp
  rw [hratio]
  exact hpow

/-- The profile is never differentiated: only its explicit increment lower bound is. -/
theorem joint_scale_increment_lower {g : ℝ → ℝ → ℝ} {p q L M c d r s ε : ℝ}
    (hg : PositiveHomogeneousProfile g)
    (hP : PoweredRowBounds g p L c)
    (hQ : PoweredRowBounds (fun r s => g s r) q M d)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s) (hε : 0<ε) :
    (1+ε*r/(r+d*s))^q * (1+ε*s/(s+c*(1+ε)*r))^p ≤ 1+ε := by
  have hr' : 0<(1+ε)*r := mul_pos (by linarith) hr
  have hs' : 0<(1+ε)*s := mul_pos (by linarith) hs
  have hfirst := hQ.profile_increment hg.swap hq hs hr (mul_pos hε hr)
  have hsecond := hP.profile_increment hg hp hr' hs (mul_pos hε hs)
  rw [show r+ε*r=(1+ε)*r by ring] at hfirst
  rw [show s+ε*s=(1+ε)*s by ring] at hsecond
  have hden1 : 0<r+d*s := by nlinarith [mul_nonneg hQ.offset_nonneg hs.le]
  have hden2 : 0<s+c*((1+ε)*r) := by nlinarith [mul_nonneg hP.offset_nonneg hr'.le]
  have hb : 0≤(1+ε*s/(s+c*((1+ε)*r)))^p :=
    Real.rpow_nonneg (by positivity) _
  have hg0 := hg.pos hr hs
  have hg1 := hg.pos hr' hs
  have hm := mul_le_mul hfirst hsecond hb (div_pos hg1 hg0).le
  have heq : (g ((1+ε)*r) s/g r s) *
      (g ((1+ε)*r) ((1+ε)*s)/g ((1+ε)*r) s) = 1+ε := by
    rw [hg.homogeneous hr hs (by linarith : 0<1+ε)]
    field_simp
  rw [heq] at hm
  simpa only [mul_assoc] using hm

theorem right_derivative_compare {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0) (h0 : f 0=g 0)
    (h : ∀ ⦃ε : ℝ⦄, 0<ε → f ε≤g ε) : a≤b := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope_zero_right hg.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [zero_add, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hε.le)
  rw [h0]
  exact sub_le_sub_right (h hε) _

/-- The derivative of the explicit two-step lower bound at zero. -/
theorem joint_lower_derivative {p q c d r s : ℝ}
    (hc : 0≤c) (hd : 0≤d) (hr : 0<r) (hs : 0<s) :
    HasDerivAt (fun ε : ℝ =>
      (1+ε*r/(r+d*s))^q*(1+ε*s/(s+c*(1+ε)*r))^p)
      (q*r/(r+d*s)+p*s/(s+c*r)) 0 := by
  have hden1 : 0<r+d*s := by nlinarith [mul_nonneg hd hs.le]
  have hden2 : 0<s+c*r := by nlinarith [mul_nonneg hc hr.le]
  have hN : HasDerivAt (fun ε : ℝ => ε*s) s 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).mul_const s
  have hD : HasDerivAt (fun ε : ℝ => s+c*(1+ε)*r) (c*r) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_add 1).const_mul c).mul_const r |>.const_add s
  have hA : HasDerivAt (fun ε : ℝ => 1+ε*r/(r+d*s)) (r/(r+d*s)) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const r).div_const (r+d*s)).const_add 1
  have hB : HasDerivAt (fun ε : ℝ => 1+ε*s/(s+c*(1+ε)*r)) (s/(s+c*r)) 0 := by
    convert (hN.fun_div hD (by simpa using ne_of_gt hden2)).const_add 1 using 1
    simp only [zero_mul, add_zero, mul_one, sub_zero]
    field_simp
  have hAp := hA.rpow_const (p := q) (Or.inl (by simp))
  have hBp := hB.rpow_const (p := p) (Or.inl (by simp))
  convert hAp.mul hBp using 1
  simp only [zero_mul, zero_div, add_zero, Real.one_rpow, mul_one]
  ring

theorem profile_pair_ratio_bound {g : ℝ → ℝ → ℝ} {p q L M c d r s : ℝ}
    (hg : PositiveHomogeneousProfile g)
    (hP : PoweredRowBounds g p L c)
    (hQ : PoweredRowBounds (fun r s => g s r) q M d)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s) :
    p*s/(s+c*r)+q*r/(r+d*s) ≤ 1 := by
  have hh := right_derivative_compare
    (joint_lower_derivative hP.offset_nonneg hQ.offset_nonneg hr hs)
    ((hasDerivAt_id (0:ℝ)).const_add 1) (by simp)
    (by intro ε hε; exact joint_scale_increment_lower hg hP hQ hp hq hr hs hε)
  linarith

end Rectangular
