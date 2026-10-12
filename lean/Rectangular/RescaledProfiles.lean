module

public import Rectangular.ProfileConcavity
public import Rectangular.Replication

@[expose] public section

/-! Manuscript Lemma 4.1 (`lem:homogeneous`), with the complete proof in
Appendix F (`app:counting-rescaling`), for individual characters. The real profile is
constructed, and every hypothesis of the analytic interface is proved here.
No spectral or angular input is assumed. -/

noncomputable section

namespace Rectangular

open Filter Set
open scoped Topology
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type} [Field K] [Infinite K]

def characterIntegerProfile (χ : Character K) : IntegerProfile where
  value := convolutionValue χ
  nonneg := fun a b => χ.nonneg (convolution (K := K) a b)
  mono := fun ha hb => convolutionValue_mono χ ha hb
  upper := fun a b => (convolutionValue_le χ a b).trans (by
    exact_mod_cast (Nat.sub_le (a + b) 1))
  replicate := fun m {a b} ha hb => convolutionValue_replication χ m (r := a) (s := b) ha hb
  unit := by simpa using convolutionValue_one_left χ (by omega : 0 < 1)

/-- Equation (18) (`eq:rescaled-profile`): the real profile, constructed here
as an envelope; `rescaledProfile_limit` proves that it equals the stated limit. -/
def rescaledProfile (χ : Character K) (r s : ℝ) : ℝ :=
  (characterIntegerProfile χ).profile r s

/-- Lemma 4.1, equation (19) (`eq:limit-rank`): the two size bounds. -/
theorem rescaledProfile_bounds (χ : Character K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    min r s ≤ rescaledProfile χ r s ∧ rescaledProfile χ r s ≤ r + s :=
  ⟨(characterIntegerProfile χ).profile_lower hr hs,
    (characterIntegerProfile χ).profile_upper hr hs⟩

theorem rescaledProfile_pos (χ : Character K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 < rescaledProfile χ r s := (characterIntegerProfile χ).profile_pos hr hs

/-- Lemma 4.1 (`lem:homogeneous`): coordinatewise monotonicity. -/
theorem rescaledProfile_mono (χ : Character K) {r s R S : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hR : r ≤ R) (hS : s ≤ S) :
    rescaledProfile χ r s ≤ rescaledProfile χ R S :=
  (characterIntegerProfile χ).profile_mono hr hs hR hS

/-- Lemma 4.1, equation (19) (`eq:limit-rank`): homogeneity. -/
theorem rescaledProfile_homogeneous (χ : Character K) {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    rescaledProfile χ (t * r) (t * s) = t * rescaledProfile χ r s :=
  (characterIntegerProfile χ).profile_homogeneous hr hs ht

theorem rescaledProfile_continuousAt (χ : Character K) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    ContinuousAt (fun z : ℝ × ℝ => rescaledProfile χ z.1 z.2) (r, s) :=
  (characterIntegerProfile χ).profile_continuousAt hr hs

/-- Lemma 4.1 (`lem:homogeneous`): continuity on positive real lengths. -/
theorem rescaledProfile_continuousOn (χ : Character K) :
    ContinuousOn (fun z : ℝ × ℝ => rescaledProfile χ z.1 z.2)
      {z | 0 < z.1 ∧ 0 < z.2} :=
  (characterIntegerProfile χ).profile_continuousOn

/-- Lemma 4.1 (`lem:homogeneous`): existence of the limit in equation (18)
(`eq:rescaled-profile`), including the ceilings on both lengths. -/
theorem rescaledProfile_limit (χ : Character K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Tendsto (fun n : ℕ => convolutionValue χ (rounded r n) (rounded s n) / n)
      atTop (𝓝 (rescaledProfile χ r s)) := by
  exact (characterIntegerProfile χ).profile_limit hr hs

theorem rescaledProfile_shift_limit (χ : Character K) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (a b : ℕ) :
    Tendsto (fun n : ℕ => convolutionValue χ (rounded r n + a) (rounded s n + b) / n)
      atTop (𝓝 (rescaledProfile χ r s)) :=
  (characterIntegerProfile χ).profile_shift_limit hr hs a b

/-- Lemma 4.1, equation (19) (`eq:limit-rank`): exchanging the polynomial inputs. -/
theorem rescaledProfile_input_swap (χ : Character K) (r s : ℝ) :
    rescaledProfile χ.swap23Character.cyclicCharacter s r = rescaledProfile χ r s := by
  unfold rescaledProfile IntegerProfile.profile
  congr 1
  ext v
  constructor
  · rintro ⟨a, b, t, ha, hb, ht, has, hbr, hv⟩
    refine ⟨b, a, t, hb, ha, ht, hbr, has, ?_⟩
    simpa only [characterIntegerProfile, convolutionValue_input_swap] using hv
  · rintro ⟨a, b, t, ha, hb, ht, har, hbs, hv⟩
    refine ⟨b, a, t, hb, ha, ht, hbs, har, ?_⟩
    simpa only [characterIntegerProfile, convolutionValue_input_swap] using hv

/-- Lemma 4.1 (`lem:homogeneous`): powered concavity in the second length. -/
theorem rescaledProfile_concave_second [IsAlgClosed K] (χ : Character K)
    (hp : 0 < χ.pX) {r : ℝ} (hr : 0 < r) :
    ConcaveOn ℝ (Ioi 0) (fun s => rescaledProfile χ r s ^ (1 / χ.pX)) :=
  (characterIntegerProfile χ).profile_concave_second hp
    (fun _ _ ha hb => convolution_concavity_second χ ha hb hp) hr

/-- Lemma 4.1 (`lem:homogeneous`): powered concavity in the first length. -/
theorem rescaledProfile_concave_first [IsAlgClosed K] (χ : Character K)
    (hp : 0 < χ.pY) {s : ℝ} (hs : 0 < s) :
    ConcaveOn ℝ (Ioi 0) (fun r => rescaledProfile χ r s ^ (1 / χ.pY)) := by
  have hh := rescaledProfile_concave_second χ.swap23Character.cyclicCharacter
    (by simpa using hp) hs
  simpa only [Character.cyclicCharacter_pX, Character.swap23Character_pZ,
    rescaledProfile_input_swap] using hh

/-- Lemma 4.1, equation (20) (`eq:general-tripling`): real-length tripling. -/
theorem rescaledProfile_tripling [IsAlgClosed K] (χ : Character K)
    (hp : 0 < χ.pX) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    2 * rescaledProfile χ r s ^ (1 / χ.pX) +
      rescaledProfile χ.swap23Character r s ^ (1 / χ.pX) ≤
        rescaledProfile χ r (3 * s + r) ^ (1 / χ.pX) :=
  (characterIntegerProfile χ).profile_tripling (characterIntegerProfile χ.swap23Character) hp
    (fun _ _ ha hb => by
      simpa only [characterIntegerProfile, exchangedValue_eq] using
        convolution_tripling χ ha hb hp) hr hs

end Rectangular
