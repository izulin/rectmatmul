# Rectangular matrix multiplication from shared-leg entropy

Przemysław Uznański — Pathway

This note extends the shared-leg entropy analysis to rectangular
matrix multiplication over fields of characteristic zero, proving

$$
\omega(1,k,1)\le
\begin{cases}
2,&0\le k\le\frac{1}{2},\\
1+k+\frac{1}{4k},&k\ge\frac{1}{2}.
\end{cases}
$$

The shared-leg entropy inequality, determinant construction, and three-sector
degeneration come from the recent nine-fourths result by OpenAI.
The note adds a Hermite-interpolation degeneration, uses superadditivity
to obtain ordinary scaling limits, and couples the profile slopes and
intercepts to prove $\sum_i\arccos\sqrt{p_i}\ge\pi/2$.
Optimizing this constraint gives bounds for $\omega(a,b,c)$, including
the exact exponent $a+b$ when $a\ge b\ge c\ge0$ and $c(a+b)\le ab$;
the displayed rectangular curve follows as a corollary.
Consequences include
$\alpha\ge\frac{1}{2}$ and exponent **2.5** for Zwick's directed
unweighted APSP algorithm, improved to **2.4999** when combined with
Alman--Vassilevska Williams. Applications also include all-pairs LCA,
Hamming distance, minimum/maximum witnesses, and sparse multiplication.

[Read the note](main.pdf) · [LaTeX source](main.tex)

Build from this directory with TeX Live and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The bibliography uses the `plain` style and is inlined in `main.tex`;
no BibTeX step or external bibliography file is needed.

The included figure, `rectangular-exponent-curve.pdf`, is beside `main.tex`.
Its plotting source and SVG/PNG versions are in `figures/`;
regenerating the figure requires Python, Matplotlib, and NumPy.
