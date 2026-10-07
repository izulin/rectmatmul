# Rectangular matrix multiplication from shared-leg entropy

Przemysław Uznański — Pathway

This note extends the shared-leg entropy analysis to rectangular
matrix multiplication over the complex numbers, proving

$$
\omega(1,k,1)\le
\begin{cases}
2,&0\le k\le\frac{1}{2},\\
1+k+\frac{1}{4k},&k\ge\frac{1}{2}.
\end{cases}
$$

The tensor constructions and entropy inequality are taken from OpenAI's
nine-fourths paper; partial symmetrization adapts its averaging argument.
The additional analysis uses logarithmic homogenization and bounds on
profile slopes and intercepts to derive $b\le4a(1-a)$. Consequences include
$\alpha\ge\frac{1}{2}$ and exponent **2.5** for Zwick's directed
unweighted APSP algorithm, improved to **2.4999** when combined with
Alman--Vassilevska Williams. Applications also include all-pairs LCA,
Hamming distance, minimum/maximum witnesses, and sparse multiplication.

[Read the note](main.pdf) · [LaTeX source](main.tex)

Build from this directory with TeX Live and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The bibliography uses the `alpha` style and is inlined in `main.tex`;
no BibTeX step or external bibliography file is needed.

The included figure, `rectangular-exponent-curve.pdf`, is beside `main.tex`.
Its plotting source and SVG/PNG versions are in `figures/`;
regenerating the figure requires Python, Matplotlib, and NumPy.
