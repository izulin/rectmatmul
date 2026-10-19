# Preliminary slides

[Presentation PDF](rectangular-slides.pdf) · [Beamer source](rectangular-slides.tex)

51 main slides and twenty-four holdout slides for a TCS talk.
Slides 1–8 retain the human-reviewed source; slides 9 onward remain drafts
for human review. After the proof roadmap on
slide 9, slides 10–22 introduce the tools used in the proof:

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
The six-slide separation proof is retained in holdout slides 53–58.
Slides 32–33 state the two-sector and three-sector lemmas, including the
shared-leg and disjoint-sector structure. All polynomial-space semantics,
tensor-product explanations, source/target maps, and proofs are in backup:
slides 59–63 for two sectors and slides 64–69 for three sectors.
Slide 34 derives the character inequalities from the two lemmas. Replication
and rescaling share one slide (35). Slides 36–38 state the concavity and
coupled tripling inequalities for `P=P_ij` and `Q=P_ik`, show that their
limiting slopes exist and agree, then prove the common slope is positive
by iterating tripling for `R=P+Q`. Slide 39 visualizes the residual budget, defines both limiting offsets,
and gives the resulting affine bounds.
The backup slides retain profile size bounds, input interchange,
character monotonicity under degeneration, and the finite-increment proof. Slide 40 derives relative-growth lower bounds from the
profile slope and affine bounds, then uses input interchange for the
other derivative. Slide 41 combines them with the differentiated homogeneity
identity to obtain the ratio bound, without assuming an angular conclusion.
These slides explicitly label the derivative sketch;
the finite-increment proof is in backup. Slide 42 derives the pairwise
constraint. Slide 43 first states the complete optimization problem in
`p_i` and `c_ij`: maximize `W(p)=a*p_1+b*p_2+c*p_3` subject to the parameter
ranges, offset budgets, and pairwise product bounds. Slide 44 then uses
`p_i=cos(theta_i)^2` to state the equivalent problem in `theta_i` and `c_ij`: maximize
`W(theta)=a*cos(theta_1)^2+b*cos(theta_2)^2+c*cos(theta_3)^2`, with the angle
ranges, offset budgets, and `sqrt(c_ij*c_ji)>=cos(theta_i+theta_j)` displayed. The proof from this point uses only
these numerical hypotheses. Slide 45 states its target
`theta_1+theta_2+theta_3>=pi/2` at the start, then gives a direct symmetric proof: weight the pairwise bounds by the cosines, sum using
the row budgets, and factor the resulting expression into `cos(S)` times a
positive factor. Slides 46–48 give a symmetric weighted
proof: scale all angles to the boundary, introduce the outward normals of
the doubled-angle triangle, expand a squared norm, and apply the triangle
inequality for the thin case. Complexities suppress `+o(1)` in the
exponent, as in the note.

Suggested pacing:

| Slides | Topic | Minutes |
| --- | --- | ---: |
| 1–9 | Definitions, results, and proof roadmap | 7 |
| 10–22 | Bilinear algorithms and the tensor toolset | 13 |
| 23–26 | Convolution, character values, and the power-sum rule | 4 |
| 27–31 | Proof of the power-sum inequality | 5 |
| 32–34 | Splitting lemma statements and character inequalities | 2 |
| 35–49 | Rescaling, common slopes, angular constraint, and the arithmetic exponent | 14 |
| 50–51 | Applications and contribution | 2 |

Sources and provenance are included in the deck. The numerical application
bounds are those in the manuscript; later research notes are not incorporated.
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

Holdout slides 53–58 give the complete construction from the paper's appendix.
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
interpretation and proof are in backup slides 59–63 and treat arbitrary
parameters, using orientation `X,Y`. Backup slide 59 defines the polynomial
spaces and source/target maps. Both the source and target are bilinear in the first polynomial `f` and a
second input consisting of a pair of independent polynomials.
Slide 60 explicitly gives the two bilinear factors, pairs corresponding
spaces, and evaluates the product on `f tensor 1` and
`a tensor e_0 + b tensor e_1` to obtain `(f*a,f*b)`.
The parameters `r,s,2` specify dimensions; `B_X(2)` has a scalar first
input and a vector second input.

The backup proof gives the input and output linear maps:

1. Slide 61 takes independent inputs with `deg f < r`, `deg p <= s`,
   `deg h <= s-2`, and writes `p_s = [t^s]p`. For nonzero `eps`, it encodes
   `a = p - p_s*t^s - eps^(-1)*t*h` and
   `b = eps^(-1)*h + p_s*t^(s-1)`. Both have degree less than `s`.
   Compute `U=f*a` and `V=f*b` using the tensor in the lemma's left side.
2. Slide 62 sets `m=r+s-2` and gives linear output maps
   `P=U+t*V` and `H_eps=eps*(V-([t^m]V)*t^m)`. The output lengths are
   `r+s` and `r+s-2`. It proves `P=f*p` and
   `[t^m]V = p_s*f_(r-1)` from `deg(f*h) <= m-1`.
3. Slide 63 derives the exact formula
   `H_eps=f*h+eps*p_s*t^(s-1)*(f-f_(r-1)*t^(r-1))`.
   The coefficients converge to the pair `(f*p,f*h)`, whose independent
   second inputs have lengths `s+1,s-1`. The first leg is shared and the
   output blocks are separate. The argument includes `r=1`, when the error
   is zero; permutation gives the other leg orientations.

Slide 33 states the three-sector degeneration for `r,s >= 1`:
`C_ij(r,3s+r-1)` degenerates to `T_1 + T_2 + T_3`. The coordinate
interpretation and proof are in backup slides 64–69. Slide 64 introduces
the input/output spaces and sector orientations. Slide 65 fixes
`X,Y` as inputs and `Z` as output for every sector. Write the second
input as `g=g_L+t^s*q+t^(2s+r-1)*g_R`, with lengths `s,r+s-1,s`.
The target map is `(f,(g_L,q,g_R)) -> (f*g_L,M_f(q),f*g_R)`, where
`M_f(q)` consists of coefficients `r-1,...,r+s-2` of `f*q`.
The middle block can also be read with `X,Z` as inputs and `Y` as output;
that reading, with the first-input coefficients reversed, gives the
`C_XZ(r,s)` identification.

The backup proof supplies these maps and block identifications:

1. Slide 66 sets `n=3s+r-1` and expands the tensor as
   `sum_(a=0)^(r-1) sum_(b=0)^(n-1) x_a*y_b*z_(a+b)`.
   It gives the full three-interval partitions of the Y and Z coordinates.
   Encode the second input as
   `g_eps=g_L+eps*t^s*q+t^(2s+r-1)*g_R`; divide the middle output block by
   `eps` and retain the outer output blocks. These are the middle-Y
   scaling by `eps` and middle-Z scaling by `eps^(-1)`.
2. Slide 67 proves the zero pattern: left Y forces left Z, and right Y
   forces right Z, by the bounds on `a`. Its block table lists every
   possible multiplier (`0`, `1`, or `eps`). Thus no supported term has
   negative epsilon degree, and the limit keeps exactly the three matched
   blocks. The two outer blocks are `T_1,T_2`; the middle is `T_3`.
3. Slide 68 writes both outer tensors in full. The left is `C_XY(r,s)`;
   translating the right Y and Z indices by `A=2s+r-1` identifies the right
   with a second copy. These maps keep the first-leg basis unchanged.
4. Slide 69 writes a middle output index as `c=s+r-1+v` and the first index
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
3. Slide 38 sets `R=P+Q`, iterates `R(3*s+1) >= 3*R(s)` along
   `s_n=3^n*(s+1/2)-1/2`, and uses `R(s_n)/s_n -> 2*L_i` to obtain
   `R(s) <= L_i*(2*s+1)`. Since R is positive, `L_i > 0`.
4. Slide 39 rewrites the sum estimate as `a(s)+b(s) <= 1`, where
   `a(s)=P(s)/L_i-s` and `b(s)=Q(s)/L_i-s`. A stacked diagram shows their
   shared budget and limiting offsets. Both residuals are nonnegative,
   nondecreasing, and bounded by one, so the limits
   `c_ij=lim a(s)` and `c_ik=lim b(s)` exist. Their sum is at most one;
   bounding each residual by its limit gives the affine bounds.

Slide 40 supplies the intermediate calculation for the angular argument.
For differentiable `g=g_ij` and positive `p_i,p_j`, the profile bounds give
`P_ij'(t)/P_ij(t) >= 1/(t+c_ij)`. Homogeneity writes
`g(r,s)=r*P_ij(s/r)^p_i`; the chain rule gives
`partial_s(g)/g >= p_i/(s+c_ij*r)`. Input interchange and the reversed
profile `P_ji` give `partial_r(g)/g >= p_j/(r+c_ji*s)`.
Slide 41 explicitly invokes these two bounds when combining them with
Euler's identity. Its conclusion is the ratio bound; it does not announce
the angular result before the numerical proof. The finite-increment
argument remains in holdout.

Slides 42–45 organize the optimization and prove the angular constraint:

1. Slide 42 sets `t=r/s`, displays the quadratic with coefficients A,B,C,
   and uses `B >= -inf_(t>0)(A*t+C/t) = -2*sqrt(A*C)`. Completing the
   square gives the lower bound on `sqrt(c_ij*c_ji)`.
2. Slide 43 states the problem before substitution: maximize
   `W(p)=a*p_1+b*p_2+c*p_3` over the three parameters and six offsets,
   with `0<=p_i<=1`, nonnegative offsets satisfying `c_ij+c_ik<=1`, and
   `sqrt(c_ij*c_ji)>=sqrt(p_i*p_j)-sqrt((1-p_i)*(1-p_j))` for all distinct
   indices. The weights `a,b,c` are fixed and nonnegative.
3. Slide 44 makes the substitution `p_i=cos(theta_i)^2` and explicitly
   states the equivalent optimization: maximize
   `W(theta)=a*cos(theta_1)^2+b*cos(theta_2)^2+c*cos(theta_3)^2` over the
   three angles and six offsets, for fixed nonnegative weights. The
   constraints are `0<=theta_i<=pi/2`, nonnegative offsets with
   `c_ij+c_ik<=1`, and `sqrt(c_ij*c_ji)>=cos(theta_i+theta_j)`, for all
   distinct indices. All angle endpoints are included.
4. Slide 45 begins with the goal `S=sum_i theta_i>=pi/2`, then proves it
   by one direct calculation. If an angle is at least pi/2, the conclusion is
   immediate. Otherwise every cosine is positive. Multiplying the pairwise
   bounds by `2*cos(theta_i)*cos(theta_j)`, applying AM–GM, and summing with
   the row budgets shows that
   `D=2*sum_(i<j) cos(theta_i+theta_j)*cos(theta_i)*cos(theta_j)-sum_i cos(theta_i)^2`
   is nonpositive. Cosine addition factors this expression as
   `D=cos(S)*sum_i cos(theta_i)*cos(theta_j-theta_k)`, where `S=sum_i theta_i`
   and j,k are the other indices. The second factor is positive, so
   `cos(S)<=0`; since `0<=S<3*pi/2`, we obtain `S>=pi/2`. This proves
   Proposition 5.2 directly from the numerical constraints. The auxiliary
   variables and the contradiction step are removed.

Slides 46–48 replace the cited weighted inequality and the separate
thin-range monotonicity argument with one symmetric vector proof:

1. Slide 46 starts with the monotonicity reduction: scaling down the
   angles only increases `W(theta)`, so for an upper bound it suffices to
   maximize over the relaxed region of all nonnegative angles with sum
   pi/2. Every original feasible tuple scales into this region with an
   objective at least as large. A diagram then introduces the outward unit
   normal `n_i` opposite angle `2*theta_i` of the resulting triangle, so
   `n_j dot n_k = -cos(2*theta_i)`.
2. Slide 47 defines `ell_1=sqrt(b*c/a)` and its cyclic counterparts.
   Since `ell_2*ell_3=a` cyclically, expansion gives
   `W=E(a,b,c)-norm(sum_i ell_i*n_i)^2/4`.
3. Slide 48 starts by assuming the thin case `a>=b>=c>0` and
   `c<=ab/(a+b)`. Thus `ell_3-ell_1-ell_2=(a*b-a*c-b*c)/sqrt(a*b*c)>=0`.
   The triangle inequality bounds the norm below by this nonnegative gap.
   Inserting it into the squared-norm identity gives
   `W<=E-(a*b-a*c-b*c)^2/(4*a*b*c)=a+b`. Threshold equality is included;
   the zero-weight case follows directly from `0<=p_i<=1`.

The backup section contains twenty-four slides (52–75):

- Slide 52 proves the degeneration target has rank three.
- Slides 53–58 give the finite-separation construction.
- Slides 59–63 explain the two-sector tensor semantics and prove the lemma:
  source/target maps (59), the tensor-product interpretation (60), then
  input encoding, output decoding, and the limit (61–63).
- Slides 64–69 explain and prove the three-sector lemma: spaces and sector
  orientations (64), a fixed-output interpretation (65), then the four
  coordinate proof slides (66–69). The main statements link to each group.
- Slide 70 retains profile size bounds, coordinatewise monotonicity,
  input interchange, and powered concavity in the first length.
- Slide 71 applies the interpolation restriction from slide 20 directly
  to a character and takes N-th roots to prove `lambda(S) <= lambda(T)`.
- Slide 72 gives the growth inequality without differentiability.
- Slide 73 retains proof-route differences, field descent, scope, and
  the full provenance statement.
- Slides 74–75 contain the references.

The redundant multinomial summary and rectangular-specialization backup
are removed. The repeated formalization summary is omitted from slide 73.

With Pixi and TeX Live (`latexmk`, `pdflatex`, Beamer, PGF/TikZ, Latin Modern):

```sh
cd slides
pixi run --locked build
pixi run --locked preview
```

The pinned Pixi environment supplies PDF rendering tools. TeX tools use the
existing installation on `PATH`. Build intermediates and previews stay in
the ignored `build/` directory. The bibliography is inlined; BibTeX is not
needed.
