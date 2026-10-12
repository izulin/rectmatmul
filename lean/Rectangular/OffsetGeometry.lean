module

public import Rectangular.AngularBound
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace Rectangular

open Real

/-- The normalized two-coordinate constraint, with independently oriented offsets. -/
def PairRatio (p q c d : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 0<t → p/(1+c*t)+q*t/(t+d) ≤ 1

theorem positive_quadratic_linear_bound {A B C : ℝ} (hA : 0≤A) (hC : 0≤C)
    (h : ∀ ⦃t : ℝ⦄, 0<t → 0≤A*t^2+B*t+C) : -2*sqrt (A*C) ≤ B := by
  by_cases hB : 0≤B
  · linarith [sqrt_nonneg (A*C)]
  have hall : ∀ t : ℝ, 0≤A*(t*t)+B*t+C := by
    intro t
    by_cases ht : 0<t
    · simpa only [sq] using h ht
    · have hb := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hB) (le_of_not_gt ht)
      have ha := mul_nonneg hA (mul_self_nonneg t)
      linarith
  have hd := discrim_le_zero hall
  unfold discrim at hd
  have hs := sq_sqrt (mul_nonneg hA hC)
  nlinarith [sqrt_nonneg (A*C)]

theorem PairRatio.quadratic {p q c d : ℝ} (h : PairRatio p q c d)
    (hc : 0≤c) (hd : 0≤d) {t : ℝ} (ht : 0<t) :
    0≤(1-q)*c*t^2+(1-p-q+c*d)*t+(1-p)*d := by
  have h1 : 0<1+c*t := by nlinarith [mul_nonneg hc ht.le]
  have h2 : 0<t+d := by linarith
  have hh := mul_le_mul_of_nonneg_right (h ht) (mul_pos h1 h2).le
  have heq : (p/(1+c*t)+q*t/(t+d))*((1+c*t)*(t+d)) =
      p*(t+d)+q*t*(1+c*t) := by
    field_simp
  rw [heq] at hh
  nlinarith

theorem pairRatio_of_quadratic {p q c d : ℝ} (hc : 0≤c) (hd : 0≤d)
    (h : ∀ ⦃t : ℝ⦄, 0<t → 0≤(1-q)*c*t^2+(1-p-q+c*d)*t+(1-p)*d) :
    PairRatio p q c d := by
  intro t ht
  have h1 : 0<1+c*t := by nlinarith [mul_nonneg hc ht.le]
  have h2 : 0<t+d := by linarith
  have heq : p/(1+c*t)+q*t/(t+d) =
      (p*(t+d)+q*t*(1+c*t))/((1+c*t)*(t+d)) := by field_simp
  rw [heq]
  apply (div_le_iff₀ (mul_pos h1 h2)).mpr
  have hh := h ht
  nlinarith

theorem PairRatio.offset_product_lower {p q c d : ℝ} (h : PairRatio p q c d)
    (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (hc : 0≤c) (hd : 0≤d) :
    sqrt (p*q)-sqrt ((1-p)*(1-q)) ≤ sqrt (c*d) := by
  have hp' : 0≤1-p := by linarith
  have hq' : 0≤1-q := by linarith
  have hcd := mul_nonneg hc hd
  have hpq := mul_nonneg hp hq
  have hab := mul_nonneg hp' hq'
  have hh := positive_quadratic_linear_bound
    (mul_nonneg hq' hc) (mul_nonneg hp' hd)
    (by intro t ht; exact h.quadratic hc hd ht)
  have heq : (1-q)*c*((1-p)*d) = ((1-p)*(1-q))*(c*d) := by ring
  rw [heq, sqrt_mul hab] at hh
  have hsqc := sq_sqrt hcd
  have hsqa := sq_sqrt hab
  have hsqp := sq_sqrt hpq
  have hs : sqrt (p*q) ≤ sqrt (c*d)+sqrt ((1-p)*(1-q)) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    nlinarith
  linarith

theorem offset_amgm {c d : ℝ} (hc : 0≤c) (hd : 0≤d) (x y : ℝ) :
    2*sqrt (c*d)*x*y ≤ c*x^2+d*y^2 := by
  rw [sqrt_mul hc]
  have hs := sq_nonneg (sqrt c*x-sqrt d*y)
  have hsc := sq_sqrt hc
  have hsd := sq_sqrt hd
  nlinarith

theorem offset_quadratic_budget {a b c d e f : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e) (hf : 0≤f)
    (hX : a+b≤1) (hY : c+d≤1) (hZ : e+f≤1) (x y z : ℝ) :
    2*sqrt (a*c)*x*y+2*sqrt (b*e)*x*z+2*sqrt (d*f)*y*z ≤ x^2+y^2+z^2 := by
  have hxy := offset_amgm ha hc x y
  have hxz := offset_amgm hb he x z
  have hyz := offset_amgm hd hf y z
  have hxx := mul_le_mul_of_nonneg_right hX (sq_nonneg x)
  have hyy := mul_le_mul_of_nonneg_right hY (sq_nonneg y)
  have hzz := mul_le_mul_of_nonneg_right hZ (sq_nonneg z)
  nlinarith

theorem cosine_row_identity (x y z : ℝ) :
    cos (x+y)*cos y+cos (x+z)*cos z =
      cos x+cos (x+y+z)*cos (y-z) := by
  have h1 := two_mul_cos_mul_cos (x+y) y
  have h2 := two_mul_cos_mul_cos (x+z) z
  have h3 := two_mul_cos_mul_cos (x+y+z) (y-z)
  rw [show x+y-y=x by ring] at h1
  rw [show x+z-z=x by ring] at h2
  rw [show x+y+z-(y-z)=x+z+z by ring,
    show x+y+z+(y-z)=x+y+y by ring] at h3
  linarith

theorem cosine_row_strict {x y z : ℝ} (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hS : x+y+z<Real.pi/2) :
    cos x < cos (x+y)*cos y+cos (x+z)*cos z := by
  have hsum : 0<cos (x+y+z) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hS⟩
  have hdiff : 0<cos (y-z) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rw [cosine_row_identity]
  linarith [mul_pos hsum hdiff]

theorem offset_angle_contradiction {a b c d e f x y z : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e) (hf : 0≤f)
    (hX : a+b≤1) (hY : c+d≤1) (hZ : e+f≤1)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hxy : cos (x+y)≤sqrt (a*c)) (hxz : cos (x+z)≤sqrt (b*e))
    (hyz : cos (y+z)≤sqrt (d*f)) : Real.pi/2 ≤ x+y+z := by
  by_contra hnot
  have hS : x+y+z<Real.pi/2 := lt_of_not_ge hnot
  have hxp : 0<cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hyp : 0<cos y := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hzp : 0<cos z := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hrowX := mul_lt_mul_of_pos_right (cosine_row_strict hx hy hz hS) hxp
  have hrowY := mul_lt_mul_of_pos_right
    (cosine_row_strict hy hx hz (by linarith)) hyp
  have hrowZ := mul_lt_mul_of_pos_right
    (cosine_row_strict hz hx hy (by linarith)) hzp
  have hxy' := mul_le_mul_of_nonneg_right hxy (mul_pos hxp hyp).le
  have hxz' := mul_le_mul_of_nonneg_right hxz (mul_pos hxp hzp).le
  have hyz' := mul_le_mul_of_nonneg_right hyz (mul_pos hyp hzp).le
  have hbudget := offset_quadratic_budget ha hb hc hd he hf hX hY hZ (cos x) (cos y) (cos z)
  rw [show y+x=x+y by ring] at hrowY
  rw [show z+x=x+z by ring, show z+y=y+z by ring] at hrowZ
  nlinarith

theorem pair_offset_angular_constraint {p q r a b c d e f : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) (hr : 0≤r) (hr1 : r≤1)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e) (hf : 0≤f)
    (hX : a+b≤1) (hY : c+d≤1) (hZ : e+f≤1)
    (hXY : PairRatio p q a c) (hXZ : PairRatio p r b e) (hYZ : PairRatio q r d f) :
    Real.pi/2 ≤ arccos (sqrt p)+arccos (sqrt q)+arccos (sqrt r) := by
  have hpair {u v A B : ℝ} (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1)
      (hA : 0≤A) (hB : 0≤B) (h : PairRatio u v A B) :
      cos (arccos (sqrt u)+arccos (sqrt v)) ≤ sqrt (A*B) := by
    have hh := h.offset_product_lower hu hu1 hv hv1 hA hB
    rw [sqrt_mul hu, sqrt_mul (by linarith : 0≤1-u)] at hh
    rw [cos_add, cos_arccos (by linarith [sqrt_nonneg u]) (sqrt_le_one.mpr hu1),
      cos_arccos (by linarith [sqrt_nonneg v]) (sqrt_le_one.mpr hv1),
      sin_arccos, sin_arccos, sq_sqrt hu, sq_sqrt hv]
    exact hh
  exact offset_angle_contradiction ha hb hc hd he hf hX hY hZ
    (arccos_nonneg _) (arccos_nonneg _) (arccos_nonneg _)
    (hpair hp hp1 hq hq1 ha hc hXY) (hpair hp hp1 hr hr1 hb he hXZ)
    (hpair hq hq1 hr hr1 hd hf hYZ)

end Rectangular
