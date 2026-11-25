# Certified Verification of Polynomial Decompositions, Discrete Tomography Reconfiguration, and Legendre Cross-Polytope Slice Integrals

[![License: MIT](https://img.shields.io/badge/Code%20%26%20Lean-MIT-blue.svg)](LICENSE)
[![Paper License: CC-BY-4.0](https://img.shields.io/badge/Paper-CC--BY--4.0-green.svg)](paper/main.tex)

**Author:** Lluis Eriksson

Machine-checked **Lean 4.35.0** formalization and zero-floating-point exact $\mathbb{Q}/\mathbb{Z}$ certificate audit (`POLY-DECOMP-CERT-1.0`) for **Peter Keevash and Jeck Lim** ([arXiv:2611.33120](https://arxiv.org/abs/2611.33120), Nov 24, 2026), *"Efficient reconfiguration, polynomial decompositions and approximate counting"*.

---

## Key Verified Artifacts

| Artifact | Verification Metric | Result |
| :--- | :--- | :--- |
| **Lean 4.35.0 Kernel** (`lean/PolyDecompReconfig.lean`) | 18 theorems, zero `sorry`, zero warnings, zero `Classical.choice` | **18 / 18 PASS** (`3` `none`, `1` `[propext]`, `14` `[propext, Quot.sound]`) |
| **Exact $\mathbb{Q}/\mathbb{Z}$ Verifier** (`src/polydecomp_certifier.py`) | Zero `float()`, `math.`, or `numpy`; 4-mode `POLY-DECOMP-CERT-1.0` | **16 / 16 PASS** (`0.062–2.740 ms`, total `8.07 ms`) |
| **Adversarial Red-Team Suite** (`tests/test_suite.py`) | 60 live forged payloads (12 global + 12/mode) | **60 / 60 REJECTED** |
| **SHA-256 Integrity Manifest** (`SHA256_MANIFEST.json`) | Full deterministic replay check (`scripts/verify_all.py`) | **39 / 39 MATCH** |
| **Manuscript** (`paper/main.pdf`) | 3 pages, 3 publication figures (`300 DPI`) | **0 warnings, 0 overfulls** |

---

## Four Certificate Modes (`POLY-DECOMP-CERT-1.0`)

1. **`legendre_miracle_thm16_cert` (Mode 1 — Theorem 1.6):** Performs exact symbolic 4-variable polynomial integration over $\mathbb{Q}$ for $R_l(r, s) = T_1 + T_2 + T_3 + T_4$, verifies Murphy's Legendre polynomial $L_{k-1}$, checks exact monomials, both global symmetries $R_l(-r,-s) = R_l(s,r) = R_l(r,s)$, degree $\le k-1$, exact marginal cancellation $\int_{-1}^1 R_l(r, s)\,ds = 2/k!$, and overdetermination $3k(k-1)/2 > k$.
2. **`m_basic_poly_decomp_cert` (Mode 2 — Theorems 1.2 & 1.4):** Reconstructs every $m$-basic polynomial $\pm x^a \prod_{i=1}^k (1 - x^{m_i a_i})$ in $\mathbb{Z}[x]$, verifies exact summation to $P$, computes $k$-fold exact division by $(1 - x)$ verifying $P/(1-x)^k$, and audits exact $L^1$ norms and decomposition cost.
3. **`discrete_tomography_switch_cert` (Mode 3 — Section 1.1 & Theorem 1.1):** Checks primitive non-collinear lattice directions, verifies $\pi_v(A) = \pi_v(B)$ for every direction $v$, replays every multi-directional basic switch confirming in-bounds vertices and $\pi_v(S_t) \equiv 0$, verifies reconfiguration to $B$, and audits $|A - B|_1$ and peak entry magnitude.
4. **`filling_norm_lower_bound_cert` (Mode 4 — Proposition 3.7 & Section 4.1):** Audits `prop37_filling_witness` ($F_{a,b,ab}(1) = F'(1) = F''(1) = 0$, exact $(1-x)^3$ quotient, $4m+3$ overdetermined equations, and base-$t$ Cramer non-vanishing) and `cyclotomic_factorization` (exact $\Phi_d(x)$ for every $d \mid m$ and $\prod_{d\mid m}\Phi_d(x) = x^m - 1$).

---

## Quick Reproduction

```bash
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```

---

## Licenses & Transparency Disclosure

- **Code, Lean proofs, certificates, and scripts:** [MIT License](LICENSE).
- **Manuscript (`paper/main.tex`, `paper/main.pdf`) and figures:** CC-BY-4.0.
- **AI Assistance Disclosure:** Prepared by sole author Lluis Eriksson with AI coding, formalization, and drafting assistance from Google Antigravity; all Lean proofs, exact rational/integer certificates, and adversarial tests were independently compiled and machine-verified locally.
