module

public import Rectangular.ProfileEnvelope

@[expose] public section

/-! The envelope is the full ceiling-rescaled limit. Replication gives a lower
comparison for every admissible sample; continuity gives the upper comparison.
Fixed nonnegative shifts of the rounded lengths have the same limit. -/

noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology

def rounded (r : ℝ) (n : ℕ) : ℕ := ⌈r * (n : ℝ)⌉₊

theorem rounded_pos {r : ℝ} {n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    0 < rounded r n := Nat.ceil_pos.mpr (mul_pos hr (Nat.cast_pos.mpr hn))

theorem rounded_ratio_tendsto {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => (rounded r n : ℝ) / n) atTop (𝓝 r) :=
  (tendsto_nat_ceil_mul_div_atTop hr).comp tendsto_natCast_atTop_atTop

theorem rounded_shift_ratio_tendsto {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    Tendsto (fun n : ℕ => ((rounded r n + k : ℕ) : ℝ) / n) atTop (𝓝 r) := by
  have h := (rounded_ratio_tendsto hr).add (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  simpa only [Nat.cast_add, add_div, add_zero] using h

namespace IntegerProfile

variable (P : IntegerProfile)

def scaled (r s : ℝ) (a b n : ℕ) : ℝ :=
  P.value (rounded r n + a) (rounded s n + b) / n

theorem scaled_upper {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (a b : ℕ) {n : ℕ} (hn : 0 < n) :
    P.scaled r s a b n ≤
      P.profile (((rounded r n + a : ℕ) : ℝ) / n)
        (((rounded s n + b : ℕ) : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply P.sample_le (by have := rounded_pos hr hn; omega)
    (by have := rounded_pos hs hn; omega) hn'
  · exact le_of_eq (by field_simp)
  · exact le_of_eq (by field_simp)

theorem envelope_rounded_tendsto {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (a b : ℕ) :
    Tendsto (fun n : ℕ => P.profile (((rounded r n + a : ℕ) : ℝ) / n)
      (((rounded s n + b : ℕ) : ℝ) / n)) atTop (𝓝 (P.profile r s)) :=
  (P.profile_continuousAt hr hs).tendsto.comp
    ((rounded_shift_ratio_tendsto hr.le a).prodMk_nhds
      (rounded_shift_ratio_tendsto hs.le b))

theorem replicated_sample_le {r s t : ℝ} {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (har : (a : ℝ) ≤ t * r) (hbs : (b : ℝ) ≤ t * s)
    {n : ℕ} (hn : 0 < n) :
    ((⌊(1 / t) * (n : ℝ)⌋₊ : ℕ) : ℝ) / n * P.value a b ≤ P.scaled r s 0 0 n := by
  let k := ⌊(1 / t) * (n : ℝ)⌋₊
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hk : (k : ℝ) ≤ (1 / t) * n := Nat.floor_le (by positivity)
  have hA : k * a ≤ rounded r n := by
    have hmul := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg (α := ℝ) a)
    have had : (a : ℝ) / t ≤ r := (div_le_iff₀ ht).mpr (by nlinarith)
    have hdiv := mul_le_mul_of_nonneg_left had hn'.le
    have hround := Nat.le_ceil (r * (n : ℝ))
    have heq : (1 / t) * (n : ℝ) * a = n * ((a : ℝ) / t) := by ring
    rw [heq] at hmul
    exact_mod_cast (show (k : ℝ) * a ≤ (rounded r n : ℝ) by
      change r * (n : ℝ) ≤ (rounded r n : ℝ) at hround
      nlinarith)
  have hB : k * b ≤ rounded s n := by
    have hmul := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg (α := ℝ) b)
    have hbd : (b : ℝ) / t ≤ s := (div_le_iff₀ ht).mpr (by nlinarith)
    have hdiv := mul_le_mul_of_nonneg_left hbd hn'.le
    have hround := Nat.le_ceil (s * (n : ℝ))
    have heq : (1 / t) * (n : ℝ) * b = n * ((b : ℝ) / t) := by ring
    rw [heq] at hmul
    exact_mod_cast (show (k : ℝ) * b ≤ (rounded s n : ℝ) by
      change s * (n : ℝ) ≤ (rounded s n : ℝ) at hround
      nlinarith)
  have hh := (P.replicate k ha hb).trans (P.mono hA hB)
  have hdiv := div_le_div_of_nonneg_right hh hn'.le
  simpa only [scaled, Nat.add_zero, k, div_mul_eq_mul_div] using hdiv

theorem profile_limit {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Tendsto (P.scaled r s 0 0) atTop (𝓝 (P.profile r s)) := by
  apply tendsto_order.mpr
  constructor
  · intro z hz
    obtain ⟨v, hv, hzv⟩ := (lt_csSup_iff (P.samples_bdd r s)
      (P.samples_nonempty hr hs)).mp hz
    obtain ⟨a, b, t, ha, hb, ht, har, hbs, rfl⟩ := hv
    have hfloor := (tendsto_nat_floor_mul_div_atTop (one_div_pos.mpr ht).le).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hlim : Tendsto (fun n : ℕ => ((⌊(1 / t) * (n : ℝ)⌋₊ : ℕ) : ℝ) /
      n * P.value a b) atTop (𝓝 (P.value a b / t)) := by
      simpa only [Function.comp_apply, div_mul_eq_mul_div, one_mul] using
        hfloor.mul_const (P.value a b)
    have hevent := (tendsto_order.mp hlim).1 z hzv
    filter_upwards [hevent, eventually_ge_atTop 1] with n hn hnpos
    exact hn.trans_le (P.replicated_sample_le ha hb ht har hbs (by omega))
  · intro z hz
    have hevent := (tendsto_order.mp (P.envelope_rounded_tendsto hr hs 0 0)).2 z hz
    filter_upwards [hevent, eventually_ge_atTop 1] with n hn hnpos
    exact (P.scaled_upper hr hs 0 0 (by omega)).trans_lt hn

theorem profile_shift_limit {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (a b : ℕ) :
    Tendsto (P.scaled r s a b) atTop (𝓝 (P.profile r s)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (P.profile_limit hr hs) (P.envelope_rounded_tendsto hr hs a b)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply div_le_div_of_nonneg_right (P.mono (by omega) (by omega))
    exact Nat.cast_nonneg n
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact P.scaled_upper hr hs a b (by omega)

end IntegerProfile
end Rectangular
