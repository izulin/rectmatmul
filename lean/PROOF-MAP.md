# Manuscript and Lean interfaces

The correspondence is by mathematical statement, rather than by every
line of the manuscript proof. The main body keeps its short informal
derivative argument; the checked analytic proof justifies it without
assuming differentiability of the profile.

| Manuscript result | Lean interface | Step |
| --- | --- | --- |
| Tensor characters and dot parameters | Pinned `Character/Basic.lean`, `Character/Dot.lean` | 1–2 |
| Published spectral theorem | `SpectralInputOver K`; complex alias `SpectralInput` | 2, 9–10 |
| Polynomial splitting and discrete inequalities | `DiscreteConvolution.lean`, `EntropyPowerSum.lean` | 4 |
| Convolution replication (Lemma 2.2) | `convolution_replication`; explicit local-polynomial maps | 5 |
| Real rescaled profiles (Lemma 4.1) | `RescaledProfiles.lean` | 6 |
| Common slopes and affine bounds (Lemma 5.1) | `character_common_slopes` | 7 |
| Angular constraint (Proposition 5.2) | `character_angular_constraint` | 8 |
| Weighted analytic optimization | `weighted_bound_of_angular`, `weighted_character_bound_over` | 3, 8–9 |
| Character bounds give algorithms (Lemma 6.1) | `shapeAdmissible_of_character_bound` | 9 |
| General shape bound | `mainTarget`, `shapeAdmissible_over` | 9 |
| Size-optimal exactness | `sizeOptimalTarget`, `shapeAdmissible_left_lower` | 9 |
| Complete rectangular curve | `curveTarget` | 9 |
| Field descent | `rankBlocks_descend_algebraic`, `shapeAdmissible_all_fields` | 10 |
| Curve and exactness after descent | `curveAdmissible_all_fields`, `sizeOptimal_all_fields`, `rectangularOmega_all_fields_eq_two` | 10 |

All ten steps passed the final locked build on 2026-10-12, with 193 recursive
axiom guards and 72 dedicated check examples. See README.md for reproduction.

The accepted external input is **precisely the published spectral
finite-power consequence**. It is a theorem parameter, not a global Lean
axiom. The complex main targets require `spectral : SpectralInput`.
The arbitrary-field variants require
`spectral : SpectralInputOver (AlgebraicClosure F)` for the stated field F.
Neither input assumes a rectangular character inequality, finite-block
construction, cost conversion, or field descent.

The checked deductions include rounding, choosing a finite power,
recursive block programs, every linear-combination cost, padding to all
positive integer sizes, and the operation lower bound. The field adapter
uses the pinned finite algebraic-coefficient descent and absorbs its fixed
overhead before the matrix input size varies. It has no characteristic or
separability hypothesis.

Two finite-construction routes differ from the current manuscript: the
discrete splitting interfaces reuse the pinned `6M` separation and
determinant construction, and replication uses local Lagrange polynomials.
The manuscript's exact filter and rewritten splitting construction are
not separately formalized. The checked resulting inequalities and main
targets agree. Application algorithms are not formalized by this project.
