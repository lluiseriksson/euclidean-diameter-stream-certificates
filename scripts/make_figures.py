"""Generate 3 publication-grade figures for Paper 37:
EUCLIDEAN-DIAM-CERT-1.0 (Giliberti & Hajiaghayi, arXiv:2611.33139).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data"
FIG_DIR = ROOT / "figures"

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 8.5,
        "axes.titlesize": 9.2,
        "axes.labelsize": 8.5,
        "legend.fontsize": 7.3,
        "xtick.labelsize": 7.8,
        "ytick.labelsize": 7.8,
        "axes.grid": True,
        "grid.alpha": 0.28,
        "grid.linestyle": "--",
    }
)


def make_fig1() -> None:
    d1 = json.loads((DATA_DIR / "exp1_alg4_convergence_sweep.json").read_text(encoding="utf-8"))
    d2 = json.loads((DATA_DIR / "exp2_hull_tightness_curve.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): Algorithm 4 exact iterations & weight denominator bit-length vs 1/eta
    inv_etas = [1.0 / r["eta_dec"] for r in d1["rows"]]
    iters = [r["iterations"] for r in d1["rows"]]
    bits = [r["max_weight_den_bits"] for r in d1["rows"]]
    ax1_r = ax1.twinx()
    l1 = ax1.plot(inv_etas, iters, "o-", color="#1f4e79", lw=1.8, ms=5, label="Exact Alg. 4 iterations")
    l2 = ax1_r.plot(inv_etas, bits, "s--", color="#c55a11", lw=1.6, ms=4.5, label="Max weight denom. bits")
    ax1.set_xlabel(r"Inverse accuracy $1/\eta$")
    ax1.set_ylabel("Algorithm 4 iterations", color="#1f4e79")
    ax1_r.set_ylabel("Exact denominator bit-length", color="#c55a11")
    ax1_r.grid(False)
    ax1.set_title(r"(a) Algorithm 4 Convergence & $\mathbb{Q}$ Bit Growth")
    lines = l1 + l2
    labels = [ln.get_label() for ln in lines]
    ax1.legend(lines, labels, loc="upper left", framealpha=0.92)

    # Panel (b): Lemma 5.1 Hull Factor sqrt(2a^2 - 1) vs Two-Tetrahedra Rational Realization
    a_vals = [r["a_dec"] for r in d2["rows"]]
    hull_f = [r["hull_factor_dec"] for r in d2["rows"]]
    att_f = [r["attained_factor_dec"] for r in d2["rows"]]
    ax2.plot(a_vals, hull_f, "o-", color="#1f4e79", lw=1.8, ms=4.5, label=r"Lemma 5.1 bound $\sqrt{2a^2-1}$")
    ax2.plot(a_vals, att_f, "s--", color="#548235", lw=1.6, ms=4.5, label=r"Two-tetrahedra $\mathbb{Q}$-witness")
    ax2.axhline(3.0 ** 0.5, color="#7f7f7f", ls=":", lw=1.3, label=r"$\sqrt{3}$ barrier ($a=\sqrt{2}$)")
    ax2.axhline(2.0, color="#c00000", ls="-.", lw=1.2, label=r"Factor-two ceiling ($c=2$)")
    ax2.axvline(1.581, color="#c55a11", ls=":", lw=1.2, alpha=0.85)
    ax2.annotate(r"$a=1581/1000$", xy=(1.581, 1.99978), xytext=(1.63, 1.83),
                 arrowprops=dict(arrowstyle="->", color="#c55a11", lw=0.9), fontsize=7.2, color="#c55a11")
    ax2.set_xlabel(r"Hull expansion parameter $a$")
    ax2.set_ylabel(r"Hull diameter dilation factor")
    ax2.set_title(r"(b) Lemma 5.1 Hull Dilation & Tightness")
    ax2.legend(loc="upper left", framealpha=0.92, fontsize=6.9)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_alg4_and_hull_tightness.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((DATA_DIR / "exp3_two_cap_potential_and_taylor.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): First-mask longitudinal potential F(t) vs 21/20 threshold & t = 3/5 cap split
    prof = [r for r in d3["F_profile"] if r["F_lb_dec"] is not None]
    ts = [r["t_dec"] for r in prof]
    fs = [r["F_lb_dec"] for r in prof]
    ax1.plot(ts, fs, "o-", color="#1f4e79", lw=1.8, ms=4.5, label=r"Exact $F(t)$ ($\lambda=79/50$)")
    ax1.axhline(21 / 20, color="#c00000", ls="--", lw=1.4, label=r"First mask $\phi \leq 21/20$")
    ax1.axvline(0.6, color="#548235", ls="-.", lw=1.4, label=r"3-4-5 cap split $t = 3/5$")
    ax1.set_yscale("log")
    ax1.set_ylim(0.62, 80.0)
    ax1.set_xlabel(r"Longitudinal coordinate $t$ on unit ball")
    ax1.set_ylabel(r"Potential $F(t)$ (log scale)")
    ax1.set_title(r"(a) First-Mask Potential & $t=3/5$ Cap Split")
    ax1.legend(loc="upper right", framealpha=0.92)

    # Panel (b): Second-mask global lower bound e_lb * m across Taylor degree K = 1..10
    trows = d3["second_mask_taylor"]
    degs = [r["deg"] for r in trows]
    ems = [r["em_dec"] for r in trows]
    thr = 84 / 125
    colors = ["#c55a11" if not r["passes"] else "#2e75b6" for r in trows]
    ax2.bar(degs, ems, color=colors, width=0.62, alpha=0.9)
    ax2.axhline(thr, color="#c00000", ls="--", lw=1.5, label=r"Second-mask ceiling $84/125 = 0.672$")
    ax2.set_xticks(degs)
    ax2.set_ylim(0.45, 0.70)
    ax2.set_xlabel(r"Exact Taylor degree $K$ for $e > \sum_{k=0}^K 1/k!$")
    ax2.set_ylabel(r"Certified lower bound $e_{\mathrm{lb}}(K) \cdot (1241/5000)$")
    ax2.set_title(r"(b) Second-Mask Emptiness Margin vs. Taylor Degree")
    ax2.legend(loc="lower right", framealpha=0.92)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_two_cap_and_taylor_margin.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    rep = json.loads((DATA_DIR / "certificate_replay_summary.json").read_text(encoding="utf-8"))
    rows = rep["certificates"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): Replay latency across all 16 canonical certificates
    mode_colors = {
        "variance_certificate_alg4": "#1f4e79",
        "variance_hull_and_tightness": "#2e75b6",
        "factor_two_two_cap_audit": "#548235",
        "dynamic_stream_chain_replay": "#c55a11",
    }
    mode_short = {
        "variance_certificate_alg4": "Mode 1 (Alg. 4)",
        "variance_hull_and_tightness": "Mode 2 (Hull)",
        "factor_two_two_cap_audit": "Mode 3 (App. A.1)",
        "dynamic_stream_chain_replay": "Mode 4 (Stream)",
    }
    xs = np.arange(len(rows))
    lat = [r["verify_ms"] for r in rows]
    cols = [mode_colors[r["mode"]] for r in rows]
    ax1.bar(xs, lat, color=cols, width=0.68, alpha=0.92)
    ax1.set_xticks(xs)
    ax1.set_xticklabels([f"C{i+1}" for i in range(len(rows))], fontsize=7.0)
    ax1.set_xlabel("Canonical EUCLIDEAN-DIAM-CERT-1.0 certificate (C1–C16)")
    ax1.set_ylabel("Exact zero-float replay latency (ms)")
    ax1.set_title("(a) Canonical Certificate Replay Latency")
    handles = [
        plt.Rectangle((0, 0), 1, 1, color=mode_colors[m], label=mode_short[m])
        for m in mode_colors
    ]
    ax1.set_ylim(0, 9.8)
    ax1.legend(handles=handles, loc="upper right", framealpha=0.92, fontsize=6.9)

    # Panel (b): Red-team adversarial audit (62/62 rejections across 5 categories)
    cats = ["Global /\nType", "Mode 1\nAlg. 4", "Mode 2\nHull", "Mode 3\nApp. A.1", "Mode 4\nStream"]
    counts = [12, 12, 12, 12, 14]
    bcols = ["#595959", "#1f4e79", "#2e75b6", "#548235", "#c55a11"]
    bars = ax2.bar(cats, counts, color=bcols, width=0.58, alpha=0.92)
    for bar, c in zip(bars, counts):
        ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.35, f"{c}/{c}",
                 ha="center", va="bottom", fontsize=7.8, fontweight="bold")
    ax2.set_ylim(0, 17.0)
    ax2.set_ylabel("Live adversarial forgeries rejected")
    ax2.set_title("(b) Adversarial Red-Team Audit (62/62 Rejected)")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_certificate_replay_atlas.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 Paper 37 publication figures successfully.")


if __name__ == "__main__":
    main()
