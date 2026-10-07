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

The proof uses logarithmic averaging of oriented profiles to derive
the constraint $b\le4a(1-a)$. Consequences include
$\alpha\ge\frac{1}{2}$ and exponent **2.5** for Zwick's directed
unweighted APSP algorithm. Applications to all-pairs LCA and Hamming
distance are also recorded.

[Read the note](main.pdf) · [LaTeX source](main.tex)

Build from this directory with TeX Live and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The curve figure and its plotting source are in `figures/`;
regenerating it requires Python, Matplotlib, and NumPy.
