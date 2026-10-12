module

public import Rectangular.ProfileLimit
public import Rectangular.DiscreteJensen
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-! Discrete concavity and asymmetric tripling pass to the full real profiles.
Fixed integer additions absorb all rounding errors. -/

noncomputable section

namespace Rectangular.IntegerProfile

open Filter Set
open scoped Topology

variable (P : Rectangular.IntegerProfile)

theorem profile_concave_second {p : ℝ} (hp : 0 < p)
    (hc : ∀ r s : ℕ, 0 < r → 2 ≤ s →
      P.value r (s + 1) ^ (1 / p) + P.value r (s - 1) ^ (1 / p) ≤
        2 * P.value r s ^ (1 / p)) {r : ℝ} (hr : 0 < r) :
    ConcaveOn ℝ (Ioi 0) (fun s => P.profile r s ^ (1 / p)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro s₁ hs₁ s₂ hs₂ x y hx hy hxy
  simp only [mem_Ioi] at hs₁ hs₂
  simp only [smul_eq_mul]
  let s := x * s₁ + y * s₂
  have hs : 0 < s := by
    have hcv : Convex ℝ (Ioi (0 : ℝ)) := convex_Ioi 0
    have hm := hcv hs₁ hs₂ hx hy hxy
    simpa only [smul_eq_mul, mem_Ioi, s] using hm
  have hleft := ((P.profile_limit hr hs₁).rpow_const (p := 1 / p)
    (Or.inl (P.profile_pos hr hs₁).ne')).const_mul x
  have hright := ((P.profile_limit hr hs₂).rpow_const (p := 1 / p)
    (Or.inl (P.profile_pos hr hs₂).ne')).const_mul y
  have hout := (P.profile_shift_limit hr hs 0 2).rpow_const (p := 1 / p)
    (Or.inl (P.profile_pos hr hs).ne')
  apply le_of_tendsto_of_tendsto (hleft.add hright) hout
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hR := Rectangular.rounded_pos hr hnpos
  have hA := Rectangular.rounded_pos hs₁ hnpos
  have hB := Rectangular.rounded_pos hs₂ hnpos
  have hmean : x * Rectangular.rounded s₁ n + y * Rectangular.rounded s₂ n ≤
      ((Rectangular.rounded s n + 2 : ℕ) : ℝ) := by
    have ha := (Nat.ceil_lt_add_one (mul_nonneg hs₁.le hn'.le)).le
    have hb := (Nat.ceil_lt_add_one (mul_nonneg hs₂.le hn'.le)).le
    have hcx := Nat.le_ceil (s * (n : ℝ))
    change (Rectangular.rounded s₁ n : ℝ) ≤ s₁ * n + 1 at ha
    change (Rectangular.rounded s₂ n : ℝ) ≤ s₂ * n + 1 at hb
    change s * (n : ℝ) ≤ (Rectangular.rounded s n : ℝ) at hcx
    have hxa := mul_le_mul_of_nonneg_left ha hx
    have hyb := mul_le_mul_of_nonneg_left hb hy
    rw [Nat.cast_add, Nat.cast_ofNat]
    dsimp [s] at *
    nlinarith
  have hraw := Rectangular.positive_discrete_jensen
    (u := fun k => P.value (Rectangular.rounded r n) k ^ (1 / p))
    (fun k hk => hc _ k hR hk)
    (fun {a b} _ hab => Real.rpow_le_rpow (P.nonneg (Rectangular.rounded r n) a)
      (P.mono (le_refl _) hab) (one_div_pos.mpr hp).le)
    hA hB (by omega : 0 < Rectangular.rounded s n + 2) hx hy hxy hmean
  have hdiv := div_le_div_of_nonneg_right hraw
    (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / p))
  simp only [add_div, mul_div_assoc] at hdiv
  rw [← Real.div_rpow (P.nonneg _ _) hn'.le,
    ← Real.div_rpow (P.nonneg _ _) hn'.le,
    ← Real.div_rpow (P.nonneg _ _) hn'.le] at hdiv
  simpa only [scaled, Nat.add_zero] using hdiv

theorem profile_tripling (Q : Rectangular.IntegerProfile) {p : ℝ} (hp : 0 < p)
    (ht : ∀ r s : ℕ, 0 < r → 0 < s →
      2 * P.value r s ^ (1 / p) + Q.value r s ^ (1 / p) ≤
        P.value r (3 * s + r - 1) ^ (1 / p))
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    2 * P.profile r s ^ (1 / p) + Q.profile r s ^ (1 / p) ≤
      P.profile r (3 * s + r) ^ (1 / p) := by
  have htarget : 0 < 3 * s + r := by positivity
  have hleft := ((P.profile_limit hr hs).rpow_const (p := 1 / p)
    (Or.inl (P.profile_pos hr hs).ne')).const_mul 2
  have hmiddle := (Q.profile_limit hr hs).rpow_const (p := 1 / p)
    (Or.inl (Q.profile_pos hr hs).ne')
  have hout := (P.profile_shift_limit hr htarget 0 4).rpow_const (p := 1 / p)
    (Or.inl (P.profile_pos hr htarget).ne')
  apply le_of_tendsto_of_tendsto (hleft.add hmiddle) hout
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hR := Rectangular.rounded_pos hr hnpos
  have hS := Rectangular.rounded_pos hs hnpos
  have hcoord : 3 * Rectangular.rounded s n + Rectangular.rounded r n - 1 ≤
      Rectangular.rounded (3 * s + r) n + 4 := by
    have ha := (Nat.ceil_lt_add_one (mul_nonneg hr.le hn'.le)).le
    have hb := (Nat.ceil_lt_add_one (mul_nonneg hs.le hn'.le)).le
    have hcx := Nat.le_ceil ((3 * s + r) * (n : ℝ))
    change (Rectangular.rounded r n : ℝ) ≤ r * n + 1 at ha
    change (Rectangular.rounded s n : ℝ) ≤ s * n + 1 at hb
    change (3 * s + r) * (n : ℝ) ≤ (Rectangular.rounded (3 * s + r) n : ℝ) at hcx
    have hnat : 3 * Rectangular.rounded s n + Rectangular.rounded r n ≤
        Rectangular.rounded (3 * s + r) n + 4 := by
      exact_mod_cast (show (3 : ℝ) * Rectangular.rounded s n + Rectangular.rounded r n ≤
        Rectangular.rounded (3 * s + r) n + 4 by nlinarith)
    exact (Nat.sub_le _ _).trans hnat
  have hraw := (ht _ _ hR hS).trans (Real.rpow_le_rpow (P.nonneg _ _)
    (P.mono (le_refl _) hcoord) (one_div_pos.mpr hp).le)
  have hdiv := div_le_div_of_nonneg_right hraw
    (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / p))
  simp only [add_div, mul_div_assoc] at hdiv
  rw [← Real.div_rpow (P.nonneg _ _) hn'.le,
    ← Real.div_rpow (Q.nonneg _ _) hn'.le,
    ← Real.div_rpow (P.nonneg _ _) hn'.le] at hdiv
  simpa only [scaled, Nat.add_zero] using hdiv

end Rectangular.IntegerProfile
