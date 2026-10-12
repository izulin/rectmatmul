# Lean formalization

Steps 1–10 are complete within the agreed published-input scope. The full
locked build passed on 2026-10-12 (9,102 jobs), with all 193 recursive axiom
guards and 72 local check examples passing without warnings or errors.
The manuscript is unchanged.

The checked results cover the angular constraint, weighted character bound,
character-to-program conversion, general rectangular shape bound,
size-optimal exactness, and complete real curve. Field descent supplies the
same shape and curve bounds over arbitrary fields, including finite fields.
See [PROOF-MAP.md](PROOF-MAP.md) for the correspondence with the manuscript.

## Main interfaces and external input

`Rectangular/Results.lean` exports `mainTarget`, `sizeOptimalTarget`, and
`curveTarget`. These prove the specifications from `Target.lean` over C,
with `spectral : SpectralInput` supplied explicitly.

`SpectralInputOver K` contains precisely the published spectral consequence:
a strict upper bound on every character value of a nonzero finite tensor
admits a finite exact tensor-power decomposition below that growth rate.
It is a theorem parameter, not a Lean axiom. The source is Strassen's
spectral theorem, as restated in Wigderson–Zuiddam,
[Example 2.20 and Corollary 3.30](https://www.math.ias.edu/~avi/PUBLICATIONS/Wigderson_Zuiddam_2025.pdf).
No rectangular inequality, rounding or program conversion is assumed in it.

The field variants require
`spectral : SpectralInputOver (AlgebraicClosure F)` for the stated field F.
`FieldTransfer.lean` proves the rectangular algebraic descent using a fixed
finite coefficient extension, then absorbs its fixed overhead by tensor
powers. Neither characteristic nor separability is restricted. The complex
input alone is not asserted to supply the separate algebraic-closure input.

The program model counts additions, subtractions and multiplications;
constants and input loads are free. For every fixed real shape and positive
exponent slack, one constant bounds correct programs at all integer sizes
n>=1, with dimensions rounded upward. Correctness quantifies over all input
matrices. This is a nonuniform operation bound; program construction and
bit complexity are outside the statement.

## Reproduce

From this directory, with Pixi installed (Linux x86-64):

```sh
pixi run --locked bootstrap
LEAN_NUM_THREADS=4 pixi run --locked build
```

`pixi.toml` and `pixi.lock` define the environment and tasks. Bootstrap installs
elan 4.2.4 and the pinned Lean toolchain locally, fetches the dependencies,
checks their revisions and downloads the Mathlib cache. It does not change
shell profiles. Builds use one Lean worker by default; the command above
selects four. `pixi run --locked check-pins` checks revisions separately.
The revision verifier is the only standalone setup script.

The foundation is the preserved
[PALOMAR-2026-10-08-000005 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-08-000005&version=1)
all-fields matrix multiplication source. `foundation-pin.json`,
`lake-manifest.json` and `lean-toolchain` pin its source, nine dependencies
and Lean 4.35.0-rc2. The dependency retains its Apache-2.0 licence and upstream
attribution. Installed tools, compiled artifacts and logs are ignored.

## Validation and coverage

`InterfaceAudit.lean` recursively checks 193 named declarations for unexpected
axioms, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
The local check modules contain 72 examples, including zero and thin-boundary
shapes, unequal powers, all character orientations, irrational curve
parameters, essential-input counting and characteristic-two descent.
All passed in the full build; ten separate target-formula examples also
compiled. All ten dependency revisions and the toolchain pin passed.
No proof placeholders, `native_decide`, or new axiom declarations were added.

Compiler and dependency validation uses the pinned cached foundations;
it does not independently replay their kernel verification. The standard
spectral theorem is not locally formalized.

The integer splitting interfaces reuse the pinned `6M` separation and
determinant certificates; replication uses explicit local Lagrange
polynomials. The manuscript's exact filter and rewritten splitting
construction are not separately formalized. The resulting inequalities and
main targets agree. Application algorithms are outside this formalization.
