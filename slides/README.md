# Preliminary slides

[Presentation PDF](rectangular-slides.pdf) · [Beamer source](rectangular-slides.tex)

48 main slides and twenty-four holdout slides for a TCS talk.
Slides 1–8 retain the human-reviewed source; slides 9 onward remain drafts
for human review.

## Common-slope proof

The original global common-slope argument is retained. Slide 38 now
compares concave secants directly instead of iterating tripling. For
`R=P+Q` and `0<u<S`, adding the two secant bounds gives
`R(u)/(2u+1) <= R(S)/(2S+1)`. Sending `S` to infinity yields
`R(u) <= L_i*(2u+1)` and proves `L_i>0`. The residual limits, global
increment bounds, pair inequality, and weight substitution keep their
original form. The paper's Section 5 summary and Appendix G use the
same argument.

The finite-cutoff comparison slide and its six replacement slides have
been removed after review, and the original slide numbers are restored.
The profiles on slide 36 explicitly have real arguments: they use the
rescaling from slide 35 / Lemma 4.1, whose proof is in Appendix F.

The proof and separate review are recorded in
[QS-GLOBAL-SUM](../../research/proofs/quantitative-rectangular-boundary-size.md#qs-global-sum-remove-iteration-while-keeping-the-global-formulation).

Validation on 2026-10-21: the 72-page slide PDF and the 16-page paper PDF
build without TeX warnings or overflow messages. Comparison against the
original deck confirms that only slides 36 (real-domain clarification)
and 38 (the direct proof) have changed frame bodies; slides 1–8 are
unchanged. The revised slides and Appendix G were visually checked.

## Build

Build from this directory with `pixi run build`; `pixi run preview` also
renders every page under `build/preview/`. The build uses `latexmk` and
TeX Live with Beamer, Latin Modern, AMS math, booktabs, and TikZ/PGF.
The Pixi environment supplies Python, PyMuPDF, and Pillow for previews.

## Talk outline

After the proof roadmap on slide 9, slides 10–22 introduce the tools
used in the proof:

1. The ordinary eight block products and the question of reducing their number
   by using linear combinations of the inputs.
2. All seven Strassen products, the additions/subtractions for all four outputs,
   and the resulting seven-branch recurrence.
3. The full equality between the eight ordinary tensor terms and seven Strassen
   terms, explaining tensor rank and the output leg.
4. The general matrix multiplication tensor, the historical bilinear framework,
   and the implication from a rank bound to a block algorithm and a bound on omega.
5. Restriction: linear input encoding and output decoding, illustrated by
   keeping only the first row of a matrix product.
6. Direct sum: independent inputs and outputs, illustrated by two scalar
   products; concatenate the algorithms to obtain the rank upper bound.
7. A paired-coordinate derivation of block composition: the outer and inner
   summation indices form one inner index of the larger matrix product.
   A brief mention extends the pairing argument to rank submultiplicativity
   for general tensors.
8. The definition of degeneration: parameter-dependent linear substitutions
   into an available tensor produce tensors converging coefficient by
   coefficient to the desired tensor.
9. A degeneration beyond ordinary restriction: two scalar products approach
   a rank-three tensor. The output substitutions contain `1/eps`, but their
   singular terms cancel. An elementary proof of the target's rank is in backup.
10. Asymptotic rank and why it gives the same bounds on omega as rank:
    choose a fixed tensor power, use its rank identity as a block algorithm,
    and recurse.
11. Exact interpolation and the resulting asymptotic-rank bound.
12. Tensor characters: nonnegative numerical values respecting direct sum,
    tensor product, the scalar-product unit, and restriction. Their values
    give lower bounds on asymptotic rank, as follows directly from the rules.
13. Strassen's spectral theorem: asymptotic rank equals the maximum character
    value. Uniform upper bounds on character values therefore give
    asymptotic-rank bounds and matrix-multiplication exponents.

Slide 25 derives the matrix-multiplication character formula by matching each
matrix index with the two tensor legs that carry it. The later proof uses a
concrete shared-variable example to explain the
power-sum rule on slide 26. Slides 27–31 give its proof: group sector words
by multiplicity, state the finite-separation lemma, apply it and reorder,
evaluate a character on one group, then sum the estimates and take roots.
The six-slide separation proof is retained in holdout slides 50–55.
Slides 32–33 state the two-sector and three-sector lemmas, including the
shared-leg and disjoint-sector structure. All polynomial-space semantics,
tensor-product explanations, source/target maps, and proofs are in backup:
slides 56–60 for two sectors and slides 61–66 for three sectors.
Slide 34 derives the character inequalities from the two lemmas. Replication
and rescaling share one slide (35). Slides 36–38 state the concavity and
coupled tripling inequalities for `P=P_ij` and `Q=P_ik`, show that their
limiting slopes exist and agree, then prove the common slope is positive
by comparing concave secants for `R=P+Q`. Slide 39 visualizes the residual budget, defines both limiting offsets,
and gives the resulting affine bounds.
The backup slides retain profile size bounds, input interchange, and
character monotonicity under degeneration. The main proof now proceeds as follows:

- Slide 40 derives the finite-increment growth bound from the common slope
  and affine upper bound.
- Slide 41 increases the two input lengths successively, uses homogeneity,
  and takes the elementary logarithm limit to obtain the pair inequality.
- Slides 42–43 choose lengths reciprocal to arbitrary positive weights,
  sum over pairs, and apply `1/x + 1/y >= 4/(x+y)` with the offset budgets.
  No auxiliary name is introduced for the sum of reciprocal weights.
- Slide 44 recalls the character-to-algorithm implication.
- Slide 45 substitutes the shape weights to obtain `omega(a,b,c) <= E(a,b,c)`
  for every positive shape.
- Slide 46 obtains the thin branch by padding to `c0 = a*b/(a+b)` and
  substituting `E(a,b,c0) = a+b`. It includes `c=0` and treats `b=0` directly.

Zero character parameters are handled by assigning zero offsets to their
rows. A pair involving a zero parameter satisfies the pair inequality
because its other summand is at most one. The dedicated backup slide
explains this boundary case. Complexities suppress `+o(1)` in the exponent,
as in the note.

Suggested pacing:

| Slides | Topic | Minutes |
| --- | --- | ---: |
| 1–9 | Definitions, results, and proof roadmap | 7 |
| 10–22 | Bilinear algorithms and the tensor toolset | 13 |
| 23–26 | Convolution, character values, and the power-sum rule | 4 |
| 27–31 | Proof of the power-sum inequality | 5 |
| 32–34 | Splitting lemma statements and character inequalities | 2 |
| 35–46 | Rescaling, common slopes, reciprocal bound, and padding | 11 |
| 47–48 | Applications and contribution | 2 |

Sources and provenance are included in the deck. The numerical application
bounds are those in the manuscript; later application research results are not incorporated.
The curve figure is reused from `../rectangular-exponent-curve.pdf`.

Slide 13 uses “Strassen-type” for the general bilinear framework, including
tensor powers and degenerations. Its historical context follows
[Alman (2021), Section 1](https://theoryofcomputing.org/articles/v017a001/v017a001.pdf);
the generic tensor and rank-to-time implication agree with Sections 2 and 6
of the note. The rank-to-exponent statement fixes an integer block size
`q >= 2` before taking the input-size limit and counts all linear-map costs.

Slides 14–15 explain restriction and direct sum separately. Their rank
inequalities follow by substituting into or concatenating rank decompositions,
respectively. The restriction example is
`<2,2,2> >= <1,2,2>`: zero the second row of the first input matrix and retain
the first output row.

Slide 16 derives the tensor-product identity by matching the coefficient of
each output label. Paired row, inner, and column indices each range over
`q*s` values; the bijection `(i,u) -> (i-1)*s+u` identifies the result with
ordinary matrix multiplication of side `q*s`. Iterating proves the tensor-power
identity. The paired variables remain independent coordinates, so this statement
applies to arbitrary block matrices. It also mentions that pairing rank-one
terms gives `rank(T tensor S) <= rank(T) * rank(S)` for general tensors.

Slide 17 defines degeneration, with `T` the available computation and `S`
the desired computation. The family `P(eps)` is obtained by linear
substitutions into `T` for every nonzero `eps`, and its coefficients converge
to those of `S`.

Slide 18 illustrates why the substitutions themselves need not have a value at
zero. The slide explicitly gives the available tensor
`T = a'_0*b'_0*c'_0 + a'_1*b'_1*c'_1`, with independent primed variables,
and the target `S = a_0*b_0*c_0 + (a_0*b_1 + a_1*b_0)*c_1`.
It lists all six substitutions: `a'_0 -> a_0`, `b'_0 -> b_0`,
`c'_0 -> c_0 - c_1/eps`, `a'_1 -> a_0 + eps*a_1`,
`b'_1 -> b_0 + eps*b_1`, and `c'_1 -> c_1/eps`.
The displayed transformed tensor expands to `P(eps) = S + eps*a_1*b_1*c_1`.
The two output substitutions are singular, but the tensor coefficients converge.
The target has rank three, so no ordinary restriction from a rank-two tensor
can produce it. This is the standard W-tensor after exchanging the output
coordinates; the rank fact is verified in
[Christandl–Jensen–Zuiddam (2018), proof of Proposition 13, p. 131](https://ir.cwi.nl/pub/27285/1-s2.0-S0024379517306900-main.pdf#page=7).
The first backup slide supplies a separate elementary proof: the plane of the
two output coefficient matrices contains only one rank-one direction, whereas
a rank-two tensor would require two independent rank-one generators.

Slide 19 defines asymptotic rank as the limit (equivalently, infimum) of
`rank(T^N)^(1/N)`. For a fixed square matrix tensor `<q,q,q>`, any fixed
power gives a block algorithm of side `q^N`. Recursing bounds omega by
`log_q(rank(<q,q,q>^N))/N`; taking the infimum shows that
`asymptotic-rank(<q,q,q>) <= R` implies `omega <= log_q(R)`.
Slide 20 then explains interpolation and the resulting asymptotic-rank bound,
using the definition already introduced.

Slide 21 introduces tensor characters, their four rules, and the inequality
`lambda(T) <= asymptotic-rank(T)`. This follows by applying
`lambda(T) <= rank(T)` to tensor powers and taking roots.

Slide 22 separately states Strassen's spectral duality:
`asymptotic-rank(T) = max_lambda lambda(T)` for nonzero tensors over the
complex numbers, with the maximum over all tensor characters. This is
Theorem 3.2 of the note and
[Corollary 3.30, p. 41 of the August 5, 2025 author version of Wigderson–Zuiddam](https://www.math.ias.edu/~avi/PUBLICATIONS/Wigderson_Zuiddam_2025.pdf#page=41).
The source explicitly uses compactness to replace the supremum by a maximum.
Thus bounding every character from above bounds asymptotic rank; the slide
also connects this conclusion to the bound on omega from slide 19.
Slide 23 directly defines convolution and all three oriented dot-product
tensors, without worked examples. It explains that the subscripts of
`C_ij(r,s)` identify the input legs, whereas the subscript of `B_i(q)`
identifies the scalar leg. The three-parameter slide (24) uses these definitions
to focus on dot-product character values.
It briefly justifies the power law using `B_i(q) tensor B_i(r) = B_i(q*r)`
up to coordinate relabeling, character multiplicativity, and monotonicity in
the dimension. Its highlighted conclusion is the dot-product power law:
one exponent for each orientation determines the values at every length.

Slide 25 gives and derives the matrix formula. The row index occurs on
legs X and Z, giving `B_Y(A)`; the inner index occurs on X and Y, giving
`B_Z(B)`; and the column index occurs on Y and Z, giving `B_X(C)`.
Each subscript names the scalar leg. Pairing these independent indices gives
`<A,B,C> = B_Y(A) tensor B_Z(B) tensor B_X(C)` up to coordinate relabeling.
Character multiplicativity then gives `A^p_Y * B^p_Z * C^p_X`, as in
Sections 2–3 of the note.

Slides 27–31 prove the power-sum inequality for matched sectors sharing leg
`i`, with a fixed character and `p = p_i > 0`. For multiplicities `n_h`
summing to `N`, there are `M = multinomial(N; n_1,...,n_s)` sector words.
Keeping them on the two unshared legs and applying finite separation gives
`(2M) T^N` degenerating to `M` independent copies of
`(tensor_h T_h^n_h) tensor B_i(M)`. Once all three legs distinguish the
words, their factors can be reordered independently.

Slide 28 separately states the finite-separation lemma (Lemma 2.1(1)) for
`Q = sum_w F_w`, with sectors sharing leg `i` and disjoint coordinates on
each other leg. It defines `(2M)Q` as `2M` independent copies and shows the
conclusion `(2M)Q` degenerating to the direct sum of
`F_w tensor B_i(M)`. A diagram shows the shared leg before separation and
private leg variables in each resulting sector. The source note identifies
the root-of-unity filter of length `2M` and the subsequent epsilon weights,
with a link to the six proof slides in holdout.

Holdout slides 50–55 give the complete construction from the paper's appendix.
They follow the existing rank-three proof on the first holdout slide (52).
Their mathematical content is unchanged:

1. Write `Q = sum_h F_h` with
   `F_h = sum_(a,b,c) mu_(h,a,b,c) x_a y_(h,b) z_(h,c)`, explaining which
   variables are shared and which are private. State the independent target.
2. Set `L = 2M`, choose a primitive `L`-th root of unity, and display the
   three linear substitutions in each of the `L` source copies. Introduce
   all new indices and coordinates.
3. Expand the sum over copies. The finite geometric sum keeps
   `g + u = h + v`; the bound `|g+u-h-v| <= 2M-2 < L` removes modular
   ambiguity. Display the exact restricted tensor `R`.
4. Give the epsilon scalings on the three legs. On retained terms, their
   exponents sum to `(g-h)^2`, using `u-v = h-g`.
5. Display the transformed tensor and its coefficientwise limit. The
   nonnegative square exponents justify the limit even though individual
   substitutions use negative powers. Only `g=h` and `u=v` remain.
6. Match the surviving coordinates with `F_h tensor B_X(M)`. The index `h`
   now appears on every leg, proving that the result is a direct sum.

The proof is given for a shared first leg over the complex numbers, with
`M >= 1` and finite coordinate sets. Permuting the legs gives the other
orientations. The detailed construction is retained for later presentation
review.

Slide 29 explicitly displays the chain from `(2M)T^N` to `(2M)Q`, then the
lemma's direct sum, and finally the reordered sectors `U tensor B_i(M)`.
The first degeneration repeats the preceding retention step in each copy;
the second invokes the newly stated lemma. Independent reordering is the
final tensor isomorphism, with a link back to the lemma and a reference to
the six proof slides in holdout.

Character evaluation gives
`2M lambda(T)^N >= M^(1+p) product_h lambda(T_h)^n_h`.
With `a_h = lambda(T_h)^(1/p)`, this yields
`M product_h a_h^n_h <= 2^(1/p) lambda(T)^(N/p)` for each tuple.
There are at most `(N+1)^s` tuples; summing by the multinomial theorem
and taking `N`-th roots removes this polynomial factor and proves Lemma 3.3.
Monotonicity under degeneration is supplied by interpolation (Lemma 3.1),
as also explained in backup. The expanded suggested pacing totals 47 minutes.

Slide 32 states the two-sector degeneration for `r >= 1, s >= 2`:
`C_ij(r,s) tensor B_i(2)` degenerates to `T_+ + T_-`, with the two
sectors isomorphic to `C_ij(r,s+1)` and `C_ij(r,s-1)`. The coordinate
interpretation and proof are in backup slides 56–60 and treat arbitrary
parameters, using orientation `X,Y`. Backup slide 56 defines the polynomial
spaces and source/target maps. Both the source and target are bilinear in the first polynomial `f` and a
second input consisting of a pair of independent polynomials.
Slide 57 explicitly gives the two bilinear factors, pairs corresponding
spaces, and evaluates the product on `f tensor 1` and
`a tensor e_0 + b tensor e_1` to obtain `(f*a,f*b)`.
The parameters `r,s,2` specify dimensions; `B_X(2)` has a scalar first
input and a vector second input.

The backup proof gives the input and output linear maps:

1. Slide 58 takes independent inputs with `deg f < r`, `deg p <= s`,
   `deg h <= s-2`, and writes `p_s = [t^s]p`. For nonzero `eps`, it encodes
   `a = p - p_s*t^s - eps^(-1)*t*h` and
   `b = eps^(-1)*h + p_s*t^(s-1)`. Both have degree less than `s`.
   Compute `U=f*a` and `V=f*b` using the tensor in the lemma's left side.
2. Slide 59 sets `m=r+s-2` and gives linear output maps
   `P=U+t*V` and `H_eps=eps*(V-([t^m]V)*t^m)`. The output lengths are
   `r+s` and `r+s-2`. It proves `P=f*p` and
   `[t^m]V = p_s*f_(r-1)` from `deg(f*h) <= m-1`.
3. Slide 60 derives the exact formula
   `H_eps=f*h+eps*p_s*t^(s-1)*(f-f_(r-1)*t^(r-1))`.
   The coefficients converge to the pair `(f*p,f*h)`, whose independent
   second inputs have lengths `s+1,s-1`. The first leg is shared and the
   output blocks are separate. The argument includes `r=1`, when the error
   is zero; permutation gives the other leg orientations.

Slide 33 states the three-sector degeneration for `r,s >= 1`:
`C_ij(r,3s+r-1)` degenerates to `T_1 + T_2 + T_3`. The coordinate
interpretation and proof are in backup slides 61–66. Slide 61 introduces
the input/output spaces and sector orientations. Slide 62 fixes
`X,Y` as inputs and `Z` as output for every sector. Write the second
input as `g=g_L+t^s*q+t^(2s+r-1)*g_R`, with lengths `s,r+s-1,s`.
The target map is `(f,(g_L,q,g_R)) -> (f*g_L,M_f(q),f*g_R)`, where
`M_f(q)` consists of coefficients `r-1,...,r+s-2` of `f*q`.
The middle block can also be read with `X,Z` as inputs and `Y` as output;
that reading, with the first-input coefficients reversed, gives the
`C_XZ(r,s)` identification.

The backup proof supplies these maps and block identifications:

1. Slide 63 sets `n=3s+r-1` and expands the tensor as
   `sum_(a=0)^(r-1) sum_(b=0)^(n-1) x_a*y_b*z_(a+b)`.
   It gives the full three-interval partitions of the Y and Z coordinates.
   Encode the second input as
   `g_eps=g_L+eps*t^s*q+t^(2s+r-1)*g_R`; divide the middle output block by
   `eps` and retain the outer output blocks. These are the middle-Y
   scaling by `eps` and middle-Z scaling by `eps^(-1)`.
2. Slide 64 proves the zero pattern: left Y forces left Z, and right Y
   forces right Z, by the bounds on `a`. Its block table lists every
   possible multiplier (`0`, `1`, or `eps`). Thus no supported term has
   negative epsilon degree, and the limit keeps exactly the three matched
   blocks. The two outer blocks are `T_1,T_2`; the middle is `T_3`.
3. Slide 65 writes both outer tensors in full. The left is `C_XY(r,s)`;
   translating the right Y and Z indices by `A=2s+r-1` identifies the right
   with a second copy. These maps keep the first-leg basis unchanged.
4. Slide 66 writes a middle output index as `c=s+r-1+v` and the first index
   as `a=r-1-u`; then `b=c-a=s+u+v`. This gives the full middle block
   `sum_(u,v) x_(r-1-u)*y_(s+u+v)*z_(s+r-1+v)`.
   Read the Z coefficients as an input polynomial `h` and the Y
   coordinates as output labels `q_d`. Their coefficients are those of
   `f_reversed*h`, explicitly giving the map with inputs on X and Z.
   Reversing the first-input basis identifies this individual tensor
   with `C_XZ(r,s)`, while the
   whole degeneration uses the common original X coordinates.

The former worked examples with fixed parameter values are removed.
The displayed proofs supply linear maps, correctness calculations, parameter
ranges, and the coefficientwise limits for the general statements.

Slide 34 introduces `f_ij(r,s) = lambda(C_ij(r,s))` and applies the
power-sum rule with `p = p_i > 0`. The two-sector source contributes
`lambda(B_i(2)) = 2^p`, giving
`2*f_ij(r,s)^(1/p) >= f_ij(r,s+1)^(1/p) + f_ij(r,s-1)^(1/p)`.
The three-sector lemma gives
`f_ij(r,3s+r-1)^(1/p) >= 2*f_ij(r,s)^(1/p) + f_ik(r,s)^(1/p)`.
The former is discrete concavity in the second length; the latter couples
the two orientations using the same shared-leg parameter. Slide 35 then
uses these already defined convolution values for replication and rescaling.

Slides 36–39 expand the common-slope argument from Lemma 5.1 and Appendix G:

1. Slide 36 defines `P(s)=g_ij(1,s)^(1/p_i)` and
   `Q(s)=g_ik(1,s)^(1/p_i)`. It states positivity, monotonicity, midpoint
   concavity for both functions, and both coupled tripling inequalities.
2. Slide 37 notes that `(P(s)-P(1))/(s-1)` is nonnegative and decreasing,
   so its finite limit exists and equals `lim P(s)/s`; similarly for Q.
   Dividing tripling by s gives `3*L_P >= 2*L_P+L_Q` and its reverse,
   establishing `L_P=L_Q=L_i >= 0`.
3. Slide 38 sets `R=P+Q`. For `0<u<S`, concavity bounds each secant on
   `[u,S]` below by its secant on `[S,3*S+1]`, and tripling bounds the
   latter below by `R(S)/(2*S+1)`. Adding and rearranging gives
   `R(u)/(2*u+1) <= R(S)/(2*S+1)`. Letting S tend to infinity gives
   `R(u) <= L_i*(2*u+1)`, hence `L_i > 0`.
4. Slide 39 rewrites the sum estimate as `a(s)+b(s) <= 1`, where
   `a(s)=P(s)/L_i-s` and `b(s)=Q(s)/L_i-s`. A stacked diagram shows their
   shared budget and limiting offsets. Both residuals are nonnegative,
   nondecreasing, and bounded by one, so the limits
   `c_ij=lim a(s)` and `c_ik=lim b(s)` exist. Their sum is at most one;
   bounding each residual by its limit gives the affine bounds.

Slides 40–46 implement the three proof simplifications recorded in
[the manuscript review](../notes/reciprocal-proof-simplification.md).
The finite-increment proof is now in the main talk. The weighted bound
uses only the pair inequality, the three offset budgets, and the elementary
reciprocal inequality. The thin case uses monotonicity of omega by padding;
no continuity assumption on omega is needed. The old derivative sketch,
quadratic elimination, angular argument, and triangle-normal optimization
are removed from this presentation.

The Lean formalization retains its earlier angular proof route. Its main
statements agree with the manuscript, but this new presentation has not
been separately formalized.
