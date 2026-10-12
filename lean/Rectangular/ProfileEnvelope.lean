module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Tactic

@[expose] public section

/-! A real-scale envelope of an integer profile. All integer hypotheses are
displayed in the structure; the character adapter proves them separately. -/

noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology

structure IntegerProfile where
  value : ℕ → ℕ → ℝ
  nonneg : ∀ (a b : ℕ), 0 ≤ value a b
  mono : ∀ {a b A B : ℕ}, a ≤ A → b ≤ B → value a b ≤ value A B
  upper : ∀ (a b : ℕ), value a b ≤ (a : ℝ) + b
  replicate : ∀ (m : ℕ) {a b : ℕ}, 0 < a → 0 < b →
    (m : ℝ) * value a b ≤ value (m * a) (m * b)
  unit : value 1 1 = 1

namespace IntegerProfile

variable (P : IntegerProfile)

def samples (r s : ℝ) : Set ℝ :=
  {v | ∃ (a b : ℕ) (t : ℝ), 0 < a ∧ 0 < b ∧ 0 < t ∧
    (a : ℝ) ≤ t * r ∧ (b : ℝ) ≤ t * s ∧ v = P.value a b / t}

def profile (r s : ℝ) : ℝ := sSup (P.samples r s)

theorem samples_nonempty {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (P.samples r s).Nonempty := by
  let t := max (1 / r) (1 / s)
  have ht : 0 < t := lt_max_iff.mpr (Or.inl (one_div_pos.mpr hr))
  refine ⟨P.value 1 1 / t, 1, 1, t, by omega, by omega, ht, ?_, ?_, rfl⟩
  · simpa only [Nat.cast_one] using
      (div_le_iff₀ hr).mp (show (1 : ℝ) / r ≤ t from le_max_left _ _)
  · simpa only [Nat.cast_one] using
      (div_le_iff₀ hs).mp (show (1 : ℝ) / s ≤ t from le_max_right _ _)

theorem samples_le {r s v : ℝ} (hv : v ∈ P.samples r s) : v ≤ r + s := by
  obtain ⟨a, b, t, _, _, ht, ha, hb, rfl⟩ := hv
  apply (div_le_iff₀ ht).mpr
  have hu := P.upper a b
  nlinarith

theorem samples_bdd (r s : ℝ) : BddAbove (P.samples r s) :=
  ⟨r + s, fun _ hv => P.samples_le hv⟩

theorem sample_le {r s : ℝ} {a b : ℕ} {t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (har : (a : ℝ) ≤ t * r) (hbs : (b : ℝ) ≤ t * s) :
    P.value a b / t ≤ P.profile r s :=
  le_csSup (P.samples_bdd r s) ⟨a, b, t, ha, hb, ht, har, hbs, rfl⟩

theorem profile_upper {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    P.profile r s ≤ r + s :=
  csSup_le (P.samples_nonempty hr hs) (fun _ hv => P.samples_le hv)

theorem profile_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 ≤ P.profile r s := by
  obtain ⟨v, hv⟩ := P.samples_nonempty hr hs
  obtain ⟨a, b, t, ha, hb, ht, har, hbs, rfl⟩ := hv
  exact (div_nonneg (P.nonneg a b) ht.le).trans (P.sample_le ha hb ht har hbs)

theorem profile_mono {r s R S : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hR : r ≤ R) (hS : s ≤ S) : P.profile r s ≤ P.profile R S := by
  apply csSup_le_csSup (P.samples_bdd R S) (P.samples_nonempty hr hs)
  rintro v ⟨a, b, t, ha, hb, ht, har, hbs, hv⟩
  exact ⟨a, b, t, ha, hb, ht,
    har.trans (mul_le_mul_of_nonneg_left hR ht.le),
    hbs.trans (mul_le_mul_of_nonneg_left hS ht.le), hv⟩

theorem profile_homogeneous {r s t : ℝ} (hr : 0 < r) (hs : 0 < s)
    (ht : 0 < t) : P.profile (t * r) (t * s) = t * P.profile r s := by
  apply le_antisymm
  · apply csSup_le (P.samples_nonempty (mul_pos ht hr) (mul_pos ht hs))
    rintro v ⟨a, b, q, ha, hb, hq, har, hbs, rfl⟩
    have h := P.sample_le ha hb (mul_pos hq ht)
      (by nlinarith : (a : ℝ) ≤ q * t * r)
      (by nlinarith : (b : ℝ) ≤ q * t * s)
    have heq : P.value a b / q = t * (P.value a b / (q * t)) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left h ht.le
  · have h : P.profile r s ≤ P.profile (t * r) (t * s) / t := by
      apply csSup_le (P.samples_nonempty hr hs)
      rintro v ⟨a, b, q, ha, hb, hq, har, hbs, rfl⟩
      have hqr : q / t * (t * r) = q * r := by field_simp
      have hqs : q / t * (t * s) = q * s := by field_simp
      have hh := P.sample_le (r := t * r) (s := t * s) ha hb (div_pos hq ht)
        (by simpa only [hqr] using har) (by simpa only [hqs] using hbs)
      apply (le_div_iff₀ ht).mpr
      have heq : P.value a b / q * t = P.value a b / (q / t) := by field_simp
      simpa only [heq] using hh
    nlinarith [(le_div_iff₀ ht).mp h]

theorem integer_le_profile {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    P.value a b ≤ P.profile a b := by
  simpa using P.sample_le ha hb (by norm_num : (0 : ℝ) < 1) (by simp) (by simp)

theorem profile_lower {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    min r s ≤ P.profile r s := by
  let d := min r s
  have hd : 0 < d := lt_min hr hs
  have ht : 0 < 1 / d := one_div_pos.mpr hd
  have htd : (1 / d) * d = 1 := one_div_mul_cancel hd.ne'
  have har : (1 : ℝ) ≤ (1 / d) * r := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left r s) ht.le]
  have hbs : (1 : ℝ) ≤ (1 / d) * s := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right r s) ht.le]
  simpa only [P.unit, one_div_one_div] using
    P.sample_le (r := r) (s := s) (a := 1) (b := 1)
      (by omega) (by omega) ht (by simpa using har) (by simpa using hbs)

theorem profile_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 < P.profile r s := (lt_min hr hs).trans_le (P.profile_lower hr hs)

theorem profile_compare {r s R S : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hR : 0 < R) (hS : 0 < S) :
    min (R / r) (S / s) * P.profile r s ≤ P.profile R S ∧
      P.profile R S ≤ max (R / r) (S / s) * P.profile r s := by
  have ha : 0 < min (R / r) (S / s) := lt_min (div_pos hR hr) (div_pos hS hs)
  have hb : 0 < max (R / r) (S / s) :=
    lt_max_iff.mpr (Or.inl (div_pos hR hr))
  constructor
  · rw [← P.profile_homogeneous hr hs ha]
    exact P.profile_mono (mul_pos ha hr) (mul_pos ha hs)
      ((le_div_iff₀ hr).mp (min_le_left _ _))
      ((le_div_iff₀ hs).mp (min_le_right _ _))
  · rw [← P.profile_homogeneous hr hs hb]
    exact P.profile_mono hR hS
      ((div_le_iff₀ hr).mp (le_max_left _ _))
      ((div_le_iff₀ hs).mp (le_max_right _ _))

theorem profile_continuousAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ContinuousAt (fun z : ℝ × ℝ => P.profile z.1 z.2) (r, s) := by
  have hfst : Tendsto (fun z : ℝ × ℝ => z.1 / r) (𝓝 (r, s)) (𝓝 1) := by
    simpa [hr.ne'] using (continuous_fst.tendsto (r, s)).div_const r
  have hsnd : Tendsto (fun z : ℝ × ℝ => z.2 / s) (𝓝 (r, s)) (𝓝 1) := by
    simpa [hs.ne'] using (continuous_snd.tendsto (r, s)).div_const s
  have hlo := (hfst.min hsnd).mul_const (P.profile r s)
  have hhi := (hfst.max hsnd).mul_const (P.profile r s)
  simp only [min_self, max_self, one_mul] at hlo hhi
  have hz₁ : ∀ᶠ z : ℝ × ℝ in 𝓝 (r, s), 0 < z.1 :=
    (continuous_fst.tendsto (r, s)).eventually (eventually_gt_nhds hr)
  have hz₂ : ∀ᶠ z : ℝ × ℝ in 𝓝 (r, s), 0 < z.2 :=
    (continuous_snd.tendsto (r, s)).eventually (eventually_gt_nhds hs)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hz₁, hz₂] with z hz₁ hz₂
    exact (P.profile_compare hr hs hz₁ hz₂).1
  · filter_upwards [hz₁, hz₂] with z hz₁ hz₂
    exact (P.profile_compare hr hs hz₁ hz₂).2

theorem profile_continuousOn :
    ContinuousOn (fun z : ℝ × ℝ => P.profile z.1 z.2)
      {z | 0 < z.1 ∧ 0 < z.2} := by
  intro z hz
  exact (P.profile_continuousAt hz.1 hz.2).continuousWithinAt

end IntegerProfile
end Rectangular
