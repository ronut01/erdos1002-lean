# Erdős 1002 Lean Formalization

This repository is the public workspace for a separate collaborative Lean 4 formalization of Sangyoon Kwon's proof of [Erdős Problem 1002](https://www.erdosproblems.com/1002).

## Status

Formalization in progress. Sections 2, 3, and 5 are substantially complete,
and the single analytic input that gated sections 4, 6 and 7 — the
large-deviation bound for the continuants, displays (16)/(20) — is now
**proved**. See **Current state** below for figures.

The formalization target is pinned by hash in `manuscript/PROVENANCE.md`.

## Scope and provenance

- Sangyoon Kwon's mathematical manuscript remains his separately submitted, sole-authored work.
- This repository is intended for the separate collaborative Lean 4 companion project with Ibby Mian and Shayaan Siddique.
- The independent pre-collaboration audit was completed and published before this collaboration began. Subsequent review and development are collaborative work.
- This project formalizes Kwon's proof architecture and is distinct from Shouqiao Wang's independent proof and formalization.

See the [independent verification report](https://github.com/ibrahimmian36/Tesserarius/blob/main/reports/erdos-1002.md) for the dated audit record and collaboration disclosure.

## Collaboration

Repository collaborators may commit and push directly to `main`; pull requests are not required. Force-pushing to or deleting `main` should remain disabled.

The Lean toolchain, axiom policy, treatment of work-in-progress placeholders, CI checks, module structure, and contribution workflow will be agreed on before formalization begins.

## License

Apache License 2.0. See [LICENSE](LICENSE).

## Current state (2026-08-12)

The Lean development builds against Lean v4.27.0 and mathlib pinned in
`lake-manifest.json`.

**1,742 theorems, 1,560 of them axiom-clean**, under the discipline this
project enforces in CI: axioms exactly `propext`, `Classical.choice`,
`Quot.sound`, with no `sorry` in any completed result, no `native_decide`,
and no custom axioms anywhere, including the vendored infrastructure. The
current measurement reports **zero** theorems on a non-standard axiom. Of
the theorems still open, 86 carry a placeholder directly; the rest depend
on one.  (Measurement 2026-08-12, after the large-deviation chain landed:
1,742 / 1,560 / 0, up from 1,681 / 1,499 / 0.)

**The large-deviation input is closed.** Display (16) is proved
(`Kwon1002/LDDeviation.lean`, `continuant_large_deviation`): for all
`r ≥ 1` and `v > 0`,

```
Leb{α ∈ (0,1) : |log q_r − λ·r| > v} ≤ C·exp(−c·min(v²/r, v/(1+log(r+1))²))
```

with `λ = π²/(12 log 2)` — and the identification of that closed form as
the Gauss mean of `−log` is itself proved
(`LDLyapunov.integral_neg_log_gauss`), so nothing is parameterized.
Display (20) follows as a **proved instance of `P42Cases.Display20`** at
every window constant: `display20_of_pos` and `display20_holds` in
`Kwon1002/LDMain.lean`. Its two conditional consumers are now
unconditional: the retained-cylinder cut
(`nonzero_mode_cut_unconditional`, step 1 of the nonzero-mode chain of
§4) and the corrected Lemma 6.3 good-cylinder selection
(`good_cylinder_selection_unconditional`).

On (16) the manuscript and the formalization take different routes to the
same estimate, by agreement with the author. The manuscript proves it
through the perturbed transfer operator, analytic perturbation of the
leading eigenvalue, and a Chernoff argument, with Vallée (Acta Arith. 81,
1997) as the Gauss-specific reference for that framework. This
development proves the same bound by a self-contained route built on the
mixing estimates already formalized here, since reproducing the full
perturbation machinery in Lean would be disproportionate. Shouqiao Wang's
vendored code is used throughout as shared Gauss-transfer infrastructure,
not as route-specific proof architecture.

The route, now carried out in `Kwon1002/LD*.lean`: the exact spine
`log q_r ≤ Σ_{i<r}(−log x_i) ≤ log q_r + log 2` from the identity
`q_{k+1}β_k + q_k β_{k+1} = 1` (`LDSpine`); the centering
`∫(−log x)dν = π²/(12 log 2)` by the alternating moment series against
Euler's `ζ(2)` (`LDLyapunov`); truncation at cap `u ≍ 4 log r` with a
dyadic-rank excess tail over the digit-tail product (`LDExcess`);
cap-uniform covariance decay by distance-dependent recapping through the
Lipschitz contraction (`LDVariance`); relative ψ-type decoupling of an
arbitrary bounded nonnegative future from the digit past through the
in-tree cylinder conditional densities (`LDPsi`); digit-window block
approximation and the two-parity exponential-moment bound (`LDBlocks`);
and the Chernoff assembly (`LDDeviation`). The proved exponent is
`min(v²/r, v/(1+log(r+1))²)`: identical to the manuscript's on the
quadratic branch, with a `log²r` loss on the linear branch that no
consumer uses — display (20) sits at `v ≍ L^{3/4}`, `r ≤ 2m_n ≍ L`,
where both branches deliver the required `e^{−c√L}` with margin. The
verbatim linear branch `e^{−cv}` for `v ≳ r/log²r` is a spectral-gap
statement and is deliberately not claimed.

Section 2 is formalized. Section 3 is formalized apart from Lemma 3.1(i),
which this development does not use. The conditional multi-block mixing
estimate is obtained instead by taking Shouqiao Wang's Lipschitz contraction
from the vendored substrate (rate `527/540`) and transferring it to bounded
variation by an explicit mollification, giving a spectral gap at rate
`√(527/540)` with the constant depending on the BV norm as Lemma 3.2
requires. A BV Lasota-Yorke inequality, `Var(Lf) ≤ (3/4)·Var f + ‖f‖₁`, is
separately proved here but is deliberately not on that critical path; it is
used for its variation lemmas. Lemma 3.3 comes through the word-reversal
argument.
Section 5's analytic core is formalized, including the characteristic
function of the limit law; the scale 1/(2π) is confirmed by three
independent routes inside Lean.

The natural extension of section 6 is now fully constructed and its
dynamics proved: the base measure is a probability measure with both
coordinate marginals the Gauss measure; the extension map, its inverse,
and the Gauss-torus skew product all preserve it; **the skew product is
mixing (Lemma 6.2), proved for arbitrary measurable sets**, with the
cylinder-character class shown dense in L²; the system is ergodic; the
no-reset probability tends to zero; and the invariant carry graph of
display (56) exists with the absolute bound `D = 9`. Lemma 6.1, the window
laws, the resonance obstruction (50), and the event-truncation step of
Proposition 6.4 are proved. The corrected Lemma 6.3 selection and the
§4 retained-cylinder cut are now unconditional consequences of the proved
display (20); the remaining open goals of sections 4, 6 and 7 sit
downstream of the phase bounds and are no longer gated by (16)/(20).

`wang_substrate/` contains Shouqiao Wang's MIT-licensed infrastructure,
vendored verbatim at commit `d28713ac8245` with a provenance header added to
each file, and used with his explicit agreement. See `wang_substrate/PROVENANCE.md`.

`manuscript/` holds every version of the manuscript received, pinned by
sha256 in `manuscript/PROVENANCE.md`. The current target is **version 9**
(August 11, 2026). The v8-to-v9 diff is verified minimal — a reference,
a clarifying paragraph, and the date, with no statement, equation, or
constant changed — so the completed v8 reconciliation
(`RECONCILIATION_V8.md`) carries over to v9 unchanged.
