"""Create the manuscript's vector figure for the rectangular exponent bound."""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np


def main():
    output = Path(__file__).resolve().parent
    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.serif": ["DejaVu Serif"],
            "mathtext.fontset": "cm",
            "font.size": 11,
            "axes.labelsize": 12,
            "legend.fontsize": 10,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
            "svg.fonttype": "none",
        }
    )

    # Include the transition and the two annotated values exactly.
    k = np.unique(np.concatenate((np.linspace(0, 2, 1201), [0.5, 1.0, 2.0])))
    upper = np.full_like(k, 2.0)
    curved = k > 0.5
    upper[curved] = 1 + k[curved] + 1 / (4 * k[curved])
    lower = np.maximum(2, 1 + k)

    fig, ax = plt.subplots(figsize=(6.0, 3.25), layout="constrained")
    blue = "#245c9b"
    ax.plot(k, upper, color=blue, lw=2.3, label=r"Upper bound $F(k)$", zorder=3)
    ax.plot(
        k,
        lower,
        color="#777777",
        lw=1.35,
        linestyle=(0, (4, 3)),
        label=r"Lower bound $\max\{2,1+k\}$",
        zorder=4,
    )
    ax.scatter([0.5, 1, 2], [2, 2.25, 3.125], s=23, color=blue, zorder=5)
    ax.annotate(
        r"$F(\frac{1}{2})=2$",
        xy=(0.5, 2),
        xytext=(-6, 22),
        textcoords="offset points",
        ha="right",
        color=blue,
    )
    ax.annotate(
        r"$F(1)=2.25$",
        xy=(1, 2.25),
        xytext=(-12, 18),
        textcoords="offset points",
        ha="right",
        color=blue,
    )
    ax.annotate(
        r"$F(2)=3.125$",
        xy=(2, 3.125),
        xytext=(-10, 13),
        textcoords="offset points",
        ha="right",
        color=blue,
    )
    ax.set(xlim=(0, 2.04), ylim=(1.95, 3.28), xlabel=r"$k$", ylabel="Exponent")
    ax.set_xticks(
        [0, 0.5, 1, 1.5, 2],
        [r"$0$", r"$\frac{1}{2}$", r"$1$", r"$\frac{3}{2}$", r"$2$"],
    )
    ax.set_yticks([2, 2.25, 2.5, 2.75, 3], ["2", "2.25", "2.5", "2.75", "3"])
    ax.grid(axis="y", color="#dddddd", linewidth=0.6)
    ax.spines[["top", "right"]].set_visible(False)
    ax.legend(loc="upper left", frameon=False)

    for extension in ["pdf", "svg", "png"]:
        path = output / f"rectangular-exponent-curve.{extension}"
        fig.savefig(path, dpi=200)
        if extension == "svg":
            path.write_text(
                "\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n"
            )
    plt.close(fig)


if __name__ == "__main__":
    main()
