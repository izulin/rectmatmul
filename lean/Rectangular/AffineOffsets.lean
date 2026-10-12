module

public import Rectangular.CoupledSlopes

@[expose] public section
noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology

def profileResidual (P : ℝ → ℝ) (L s : ℝ) : ℝ := P s / L - s

def profileOffset (P : ℝ → ℝ) (L : ℝ) : ℝ :=
  sSup {v | ∃ s : ℝ, 0 < s ∧ v = profileResidual P L s}

theorem PositiveConcaveCurve.residual_nonneg {P : ℝ → ℝ} (h : PositiveConcaveCurve P)
    {L s : ℝ} (hL : 0 < L) (hlim : Tendsto (fun x => P x/x) atTop (𝓝 L))
    (hs : 0 < s) : 0 ≤ profileResidual P L s := by
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hL).mpr
  simpa only [mul_comm] using h.linear_lower hlim hs

theorem PositiveConcaveCurve.residual_mono {P : ℝ → ℝ} (h : PositiveConcaveCurve P)
    {L : ℝ} (hL : 0 < L) (hlim : Tendsto (fun x => P x/x) atTop (𝓝 L)) :
    MonotoneOn (profileResidual P L) (Ioi 0) := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · rfl
  have hi := h.increment_lower hlim hs (sub_pos.mpr hst)
  simp only [add_sub_cancel] at hi
  have hd : P s/L + (t-s) ≤ P t/L := by
    apply (le_div_iff₀ hL).mpr
    have heq : (P s/L+(t-s))*L = P s+L*(t-s) := by
      field_simp [ne_of_gt hL]
    rw [heq]
    exact hi
  unfold profileResidual
  linarith

theorem residual_sum_le_one {P Q : ℝ → ℝ} {L s : ℝ} (hL : 0 < L)
    (hb : P s+Q s ≤ L*(2*s+1)) :
    profileResidual P L s + profileResidual Q L s ≤ 1 := by
  have hd : (P s+Q s)/L ≤ 2*s+1 :=
    (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hb)
  rw [add_div] at hd
  unfold profileResidual
  linarith

/-- Monotonicity allows the two suprema to be compared at a common larger point. -/
theorem residual_mixed_budget {P Q : ℝ → ℝ} {L : ℝ}
    (hP : MonotoneOn (profileResidual P L) (Ioi 0))
    (hQ : MonotoneOn (profileResidual Q L) (Ioi 0))
    (hb : ∀ ⦃s⦄, 0 < s → profileResidual P L s+profileResidual Q L s ≤ 1)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    profileResidual P L s+profileResidual Q L t ≤ 1 := by
  have hw : 0 < max s t := lt_of_lt_of_le hs (le_max_left _ _)
  have hp := hP hs hw (le_max_left s t)
  have hq := hQ ht hw (le_max_right s t)
  have hh := hb hw
  linarith

theorem profileOffset_nonneg {P : ℝ → ℝ} {L : ℝ}
    (hb : ∀ ⦃s⦄, 0 < s → profileResidual P L s ≤ 1)
    (hn : ∀ ⦃s⦄, 0 < s → 0 ≤ profileResidual P L s) :
    0 ≤ profileOffset P L := by
  have hbounded : BddAbove {v | ∃ s : ℝ, 0<s ∧ v=profileResidual P L s} :=
    ⟨1, by rintro v ⟨s, hs, rfl⟩; exact hb hs⟩
  exact (hn (by norm_num : (0:ℝ)<1)).trans
    (le_csSup hbounded ⟨1, by norm_num, rfl⟩)

theorem profileResidual_le_offset {P : ℝ → ℝ} {L s : ℝ}
    (hb : ∀ ⦃x⦄, 0 < x → profileResidual P L x ≤ 1) (hs : 0 < s) :
    profileResidual P L s ≤ profileOffset P L := by
  have hbounded : BddAbove {v | ∃ x : ℝ, 0<x ∧ v=profileResidual P L x} :=
    ⟨1, by rintro v ⟨x, hx, rfl⟩; exact hb hx⟩
  exact le_csSup hbounded ⟨s, hs, rfl⟩

theorem profileOffset_le {P : ℝ → ℝ} {L A : ℝ}
    (hb : ∀ ⦃s⦄, 0<s → profileResidual P L s ≤ A) : profileOffset P L ≤ A := by
  have hne : ({v | ∃ s : ℝ, 0<s ∧ v=profileResidual P L s} : Set ℝ).Nonempty :=
    ⟨profileResidual P L 1, 1, by norm_num, rfl⟩
  unfold profileOffset
  apply csSup_le hne
  rintro v ⟨s, hs, rfl⟩
  exact hb hs

theorem profileOffset_budget {P Q : ℝ → ℝ} {L : ℝ}
    (hP : MonotoneOn (profileResidual P L) (Ioi 0))
    (hQ : MonotoneOn (profileResidual Q L) (Ioi 0))
    (hb : ∀ ⦃s⦄, 0 < s → profileResidual P L s+profileResidual Q L s ≤ 1) :
    profileOffset P L+profileOffset Q L ≤ 1 := by
  have hc : profileOffset P L ≤ 1-profileOffset Q L := by
    apply profileOffset_le
    intro s hs
    have hd : profileOffset Q L ≤ 1-profileResidual P L s := by
      apply profileOffset_le
      intro t ht
      have hh := residual_mixed_budget hP hQ hb hs ht
      linarith
    linarith
  linarith

theorem profileResidual_tendsto_offset {P : ℝ → ℝ} {L : ℝ}
    (hm : MonotoneOn (profileResidual P L) (Ioi 0))
    (hb : ∀ ⦃s⦄, 0 < s → profileResidual P L s ≤ 1) :
    Tendsto (profileResidual P L) atTop (𝓝 (profileOffset P L)) := by
  let H : ℝ → ℝ := fun x => profileResidual P L (max 1 x)
  have hpos (x : ℝ) : 0 < max 1 x :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hmono : Monotone H := fun _ _ hxy => hm (hpos _) (hpos _)
    (max_le_max_left 1 hxy)
  have hbounded : BddAbove (range H) :=
    ⟨1, by rintro v ⟨x, rfl⟩; exact hb (hpos x)⟩
  have heq : (⨆ x, H x) = profileOffset P L := by
    apply le_antisymm
    · exact ciSup_le (fun x => profileResidual_le_offset hb (hpos x))
    · apply profileOffset_le
      intro s hs
      exact le_ciSup_of_le hbounded s (hm hs (hpos s) (le_max_right _ _))
  rw [← heq]
  apply (tendsto_atTop_ciSup hmono hbounded).congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with s hs
  simp [H, max_eq_right hs]

/-- The complete interface of manuscript Lemma 5.1, with canonical offsets. -/
structure AffineSlopePair (P Q : ℝ → ℝ) (L c d : ℝ) : Prop where
  slope_pos : 0 < L
  left_nonneg : 0 ≤ c
  right_nonneg : 0 ≤ d
  budget : c+d ≤ 1
  left_ratio : Tendsto (fun s => P s/s) atTop (𝓝 L)
  right_ratio : Tendsto (fun s => Q s/s) atTop (𝓝 L)
  left_increment : ∀ ⦃s t⦄, 0<s → 0<t → P s+L*t ≤ P (s+t)
  right_increment : ∀ ⦃s t⦄, 0<s → 0<t → Q s+L*t ≤ Q (s+t)
  left_lower : ∀ ⦃s⦄, 0<s → L*s ≤ P s
  right_lower : ∀ ⦃s⦄, 0<s → L*s ≤ Q s
  left_upper : ∀ ⦃s⦄, 0<s → P s ≤ L*(s+c)
  right_upper : ∀ ⦃s⦄, 0<s → Q s ≤ L*(s+d)
  left_offset : c = profileOffset P L
  right_offset : d = profileOffset Q L
  left_residual_limit : Tendsto (profileResidual P L) atTop (𝓝 c)
  right_residual_limit : Tendsto (profileResidual Q L) atTop (𝓝 d)

theorem common_slopes_affine_bounds {P Q : ℝ → ℝ}
    (hP : PositiveConcaveCurve P) (hQ : PositiveConcaveCurve Q)
    (ht : CoupledTripling P Q) : ∃ L c d : ℝ, AffineSlopePair P Q L c d := by
  obtain ⟨L, _, hPlim⟩ := hP.exists_slope
  obtain ⟨M, _, hQlim⟩ := hQ.exists_slope
  have hLM := ht.slopes_equal hPlim hQlim
  subst M
  have hsum : ∀ ⦃s : ℝ⦄, 0<s → P s+Q s ≤ L*(2*s+1) :=
    fun {s} hs => ht.sum_bound hPlim hQlim hs
  have hL : 0 < L := by
    have hb := hsum (by norm_num : (0:ℝ)<1)
    have hp := hP.pos (by norm_num : (0:ℝ)<1)
    have hq := hQ.pos (by norm_num : (0:ℝ)<1)
    nlinarith
  have hnP : ∀ ⦃s : ℝ⦄, 0<s → 0≤profileResidual P L s :=
    fun {s} hs => hP.residual_nonneg hL hPlim hs
  have hnQ : ∀ ⦃s : ℝ⦄, 0<s → 0≤profileResidual Q L s :=
    fun {s} hs => hQ.residual_nonneg hL hQlim hs
  have hmP := hP.residual_mono hL hPlim
  have hmQ := hQ.residual_mono hL hQlim
  have hb : ∀ ⦃s⦄, 0<s → profileResidual P L s+profileResidual Q L s ≤ 1 :=
    fun {s} hs => residual_sum_le_one hL (hsum hs)
  have hbP : ∀ ⦃s⦄, 0<s → profileResidual P L s ≤ 1 := by
    intro s hs; have := hb hs; have := hnQ hs; linarith
  have hbQ : ∀ ⦃s⦄, 0<s → profileResidual Q L s ≤ 1 := by
    intro s hs; have := hb hs; have := hnP hs; linarith
  have hupper (R : ℝ → ℝ) (hR : ∀ ⦃s⦄, 0<s → profileResidual R L s ≤ 1)
      {s : ℝ} (hs : 0<s) : R s ≤ L*(s+profileOffset R L) := by
    have hh := profileResidual_le_offset hR hs
    unfold profileResidual at hh
    have hd : R s/L ≤ s+profileOffset R L := by linarith
    have hi := (div_le_iff₀ hL).mp hd
    nlinarith
  refine ⟨L, profileOffset P L, profileOffset Q L, {
    slope_pos := hL
    left_nonneg := profileOffset_nonneg hbP hnP
    right_nonneg := profileOffset_nonneg hbQ hnQ
    budget := profileOffset_budget hmP hmQ hb
    left_ratio := hPlim
    right_ratio := hQlim
    left_increment := by intro s t hs ht; exact hP.increment_lower hPlim hs ht
    right_increment := by intro s t hs ht; exact hQ.increment_lower hQlim hs ht
    left_lower := by intro s hs; exact hP.linear_lower hPlim hs
    right_lower := by intro s hs; exact hQ.linear_lower hQlim hs
    left_upper := by intro s hs; exact hupper P hbP hs
    right_upper := by intro s hs; exact hupper Q hbQ hs
    left_offset := rfl
    right_offset := rfl
    left_residual_limit := profileResidual_tendsto_offset hmP hbP
    right_residual_limit := profileResidual_tendsto_offset hmQ hbQ }⟩

end Rectangular
