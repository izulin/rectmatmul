module

public import Rectangular.Baseline
public import Rectangular.Target
public import Rectangular.SpectralInput
public import Rectangular.AngularCharacter
public import Rectangular.DiscreteConvolution
public import Rectangular.Replication
public import Rectangular.RescaledProfiles
public import Rectangular.CommonSlopes
public import Rectangular.AngularConstraint
public import Rectangular.Results
public import Rectangular.InterfaceAudit

/-!
# Correspondence with the writeup (`main.tex`)

Numbers below refer to the current writeup; the LaTeX labels remain stable
when numbering changes. Detailed references also appear beside declarations.

* Theorem 1.1 (`cor:general-exponents`): `mainTarget`, `sizeOptimalTarget`.
* Corollary 1.2 (`thm:curve`): `curveTarget`.
* Lemma 2.1 (`lem:openai-inputs`): pinned separation and splitting constructions
  used by `DiscreteConvolution.lean`. These use a different finite certificate
  from the writeup; its exact `2M` filter is not separately formalized.
* Lemma 2.2 (`lem:replication`): `convolution_replication`.
* Lemma 3.1 (`lem:degeneration-interpolation`): its character-monotonicity
  consequence is the pinned `Character.value_polynomialRestrictionDegeneration_le`,
  used by `Replication.lean`; the exact restriction certificate is not restated here.
* Theorem 3.2 (`thm:spectral`): the external theorem parameter `SpectralInputOver`.
* Lemma 3.3 (`lem:power-sum`): `sharedFirst_power_sum`.
* Lemma 3.4 (`lem:discrete`): `convolution_concavity_second`,
  `convolution_concavity_first`, `convolution_tripling`.
* Lemma 4.1 (`lem:homogeneous`): the `rescaledProfile_*` results.
* Lemma 5.1 (`lem:intercepts`): `character_common_slopes`.
* Proposition 5.2 (`prop:angular-cap`): `character_angular_constraint`.
* Lemma 6.1 (`lem:cost-conversion`): `shapeAdmissible_of_character_bound`.

See `PROOF-MAP.md` for scope and differences in proof route. The application
algorithms in Section 7 are outside the formalization.
-/
