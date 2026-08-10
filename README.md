# Erdős 1002 Lean Formalization

This repository is the public workspace for a separate collaborative Lean 4 formalization of Sangyoon Kwon's proof of [Erdős Problem 1002](https://www.erdosproblems.com/1002).

## Status

Formalization in progress. Sections 2, 3, and 5 are substantially complete;
sections 4, 6, and 7 are open. See **Current state** below for figures.

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

## Current state (2026-08-10)

The Lean development builds against Lean v4.27.0 and mathlib pinned in
`lake-manifest.json`.

**1,681 theorems, 1,499 of them axiom-clean**, under the discipline this
project enforces in CI: axioms exactly `propext`, `Classical.choice`,
`Quot.sound`, with no `sorry` in any completed result, no `native_decide`,
and no custom axioms anywhere, including the vendored infrastructure. The
current measurement reports **zero** theorems on a non-standard axiom. Of
the theorems still open, 86 carry a placeholder directly; the rest depend
on one.

Nearly every remaining open goal now traces to a single analytic input:
the manuscript's display (16) and its corollary (20), the large-deviation
bound for the continuants, which is absent from this development and from
the vendored substrate. The conditional machinery is in place on both
consuming paths, so a proof or citation for (16) discharges them at once.

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
Proposition 6.4 are proved. Lemma 6.3 remains open pending the
large-deviation input (16)/(20), and sections 4 and 7 are open.

`wang_substrate/` contains Shouqiao Wang's MIT-licensed infrastructure,
vendored verbatim at commit `d28713ac8245` with a provenance header added to
each file, and used with his explicit agreement. See `wang_substrate/PROVENANCE.md`.

`manuscript/` holds every version of the manuscript received, pinned by
sha256 in `manuscript/PROVENANCE.md`. The current target is **version 8**
(August 6, 2026); reconciliation of the development against it is in
progress, and until that completes the statements here are formalized
against v5 except where a file records otherwise.
