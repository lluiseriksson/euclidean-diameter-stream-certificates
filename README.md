# Machine-Checked Exact-Rational Variance-Hull, Two-Cap Mask, and Factor-Two Certificates for Euclidean Diameter in Dynamic Streams

**Author:** Lluis Eriksson (prepared with transparent AI assistance via Google Antigravity)
**Target Reference:** Jeff Giliberti & MohammadTaghi Hajiaghayi, *On Euclidean Diameter in Dynamic Streams*, `arXiv:2611.33139` (November 24, 2026).
**Licenses:** Manuscript (`paper/main.tex`, `paper/main.pdf`) under `CC-BY-4.0`; code, Lean 4 proofs, and exact certificates under `MIT`.

## Highlights
- **Zero-Dependency Lean 4 Kernel (`lean/EuclideanDiameterStream.lean`, Lean 4.35.0):** 18 constructive theorems, `0` `sorry`, `0` warnings, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, **5 zero-axiom theorems** (`none`) and 13 `[propext, Quot.sound]` (covering cleared parallel-axis identity, Lemma 5.1 hull diameter & two-simplex tightness, Algorithm 4 exact variance growth & $8V_0$ cap, 3-4-5 spherical-cap containment, SOS potential margin, Section 8.2 geometric shrinkage, and the complete Appendix A.1 factor-two rational suite).
- **Pure-Stdlib Zero-Float Verifier (`EUCLIDEAN-DIAM-CERT-1.0`, `src/diameter_certifier.py`):** Four exact-$\mathbb{Q}$ modes auditing Algorithm 4 rational variance certificates, Lemma 5.1 hulls & witness radii, Appendix A.1 Table 3 & two-cap masks, and dynamic insert/delete ball chains.
- **Canonical Atlas & Adversarial Audit:** 16/16 canonical certificates replayed in `0.181–8.834 ms` and **62/62 live adversarial forgery attacks rejected**.

## Quick Reproduction
```bash
# 1. Build & audit Lean 4 kernel
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..

# 2. Run deterministic end-to-end verification (Lean + 16 certs + 60/60 attacks + SHA-256 manifest)
python scripts/verify_all.py

# Optional: regenerate certificates, wall-clock benchmark JSONs, and figures
python scripts/run_all_experiments.py
python scripts/make_figures.py
```
