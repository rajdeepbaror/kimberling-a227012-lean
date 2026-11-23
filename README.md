# Lean 4 Formalization: Clark Kimberling's Harmonic-Mean Conjectures (OEIS A227012 & General Integer Cubics)

This repository contains a complete, zero-`sorry` **Lean 4** formalization (with Mathlib4) and accompanying mathematical manuscript resolving:

1. **All four conjectured formulas on [OEIS A227012](https://oeis.org/A227012)** (Clark Kimberling, July 1, 2013; F. M. Ramaharo, April 12, 2018), where
   $$a(n) = \left\lfloor M\!\left((n-1)^3 + 1, \dots, n^3\right) \right\rfloor$$
   and $M$ denotes the harmonic mean.
2. **Clark Kimberling's General Cubic Recurrence Conjecture** (Case 3 in the Comments of [OEIS A227012](https://oeis.org/A227012)) for *every* integer cubic $g(n) = an^3 + bn^2 + cn + d$ ($a > 0$), including the **exact minimal eventual recurrence order classification** (Corollary 8), which also resolves the conjectured eventual order-7 recurrence on [OEIS A227015](https://oeis.org/A227015).

## Verified Theorems

All 12 exported theorems compile cleanly under `leanprover/lean4:v4.37.0-rc1` with **zero `sorry`s** and depend solely on the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

| File | Theorem | Result |
| :--- | :--- | :--- |
| `A227012.lean` | `OEIS_A227012.a227012_ramaharo` | Ramaharo's explicit closed form for $a(n)$ for all $n \ge 1$ |
| `A227012.lean` | `OEIS_A227012.a227012_trig` | Trigonometric formula for $a(n)$ for all $n \ge 1$ |
| `A227012.lean` | `OEIS_A227012.a227012_recurrence` | Exact order-7 linear recurrence $(3, -3, 1, 1, -3, 3, -1)$ for $n \ge 8$ |
| `A227012.lean` | `OEIS_A227012.a227012_gf` | Exact rational generating function identity in $\mathbb{Q}\llbracket X \rrbracket$ |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.nonvanishing_c1_c2_c3` | Non-vanishing of $(c_1, c_2, c_3)$ for integer cubics ($c_1 = c_2 = 0 \implies c_3 = \frac{9a^2+350}{4200a} > 0$) |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.nonvanishing_c1_c2_c3_real` | Full real-coefficient Lemma 7 for all $a > 0$, $b,c,d \in \mathbb{R}$ |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.M_g_asymptotic_limit` | Asymptotic expansion $u^3(M_g(n) - P_g(n) - c_1/u - c_2/u^2) \to c_3$ ($u = n - \frac{1}{2}$) |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.kimberling_general_cubic_floor` | Eventual exact floor/ceiling formula $m_g(n) = \lfloor P_g(n)\rfloor$ or $\lceil P_g(n)\rceil - 1$ |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.kimberling_general_cubic_recurrence` | Universal eventual order-7 recurrence $(3, -3, 1, 1, -3, 3, -1)$ for all $a > 0$ |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.kimberling_even_order5` | Eventual order-5 recurrence $(3, -2, -2, 3, -1)$ when $2 \mid a$ |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.kimberling_div4_order4` | Eventual order-4 recurrence $(4, -6, 4, -1)$ when $4 \mid a$ |
| `GeneralCubic.lean` | `GeneralCubic.IntCubic.kimberling_minimal_order` | Complete Corollary 8 minimality over $\mathbb{R}$: order $\ge 4$ always; order $4 \iff 4 \mid a$; order $5 \iff 2 \mid a$; order $7$ minimal $\iff 2 \nmid a$ |

## How to Verify Locally

Requires [elan](https://github.com/leanprover/elan) (the Lean 4 toolchain manager).

```bash
git clone <your-repo-url>
cd kimberling-a227012-lean
lake exe cache get
lake build
```

Both `A227012.lean` and `GeneralCubic.lean` end with `#print axioms` statements so `lake build` directly prints the exact axiom set of every top-level theorem.

## Repository Structure

- `A227012.lean` — Theorem 1 (all four conjectures on OEIS A227012)
- `GeneralCubic.lean` — Lemma 6, Lemma 7 (integer & real), Theorem 2, and Corollary 8 (exact minimal recurrence order)
- `paper/kimberling_a227012_proof.tex` — Publication-ready LaTeX manuscript
- `paper/kimberling_a227012_proof.pdf` — Compiled PDF manuscript
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` — Pinned Lean 4 + Mathlib4 build configuration
