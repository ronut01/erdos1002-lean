# Erdős 1002 Lean Formalization

This repository is the public workspace for a separate collaborative Lean 4 formalization of Sangyoon Kwon's proof of [Erdős Problem 1002](https://www.erdosproblems.com/1002).

## Status

Initial project setup only. This repository does not yet contain a completed or kernel-verified formalization.

The formalization target will be pinned to an exact manuscript commit and PDF hash after the revised manuscript is finalized.

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

## Current state (2026-08-04)

The Lean development from the pre-collaboration work has been migrated here.
It builds against Lean v4.27.0 and mathlib pinned in `lake-manifest.json`.

At migration: **1,081 theorems, 919 axiom-clean** under the discipline this
project enforces in CI, axioms exactly `propext`, `Classical.choice`,
`Quot.sound`, with no `sorry` in any completed result, no `native_decide`,
and no custom axioms anywhere, including the vendored infrastructure.

Sections 2 and 3 of the manuscript are formalized (except Lemma 3.1(i),
which this development does not use: Lemma 3.2 is obtained through an exact
cylinder-transfer identity together with a bounded-variation Lasota-Yorke
inequality proved here, and Lemma 3.3 through the word-reversal argument).
Section 5's analytic core is formalized, including the characteristic
function of the limit law; the scale 1/(2π) is confirmed by three
independent routes inside Lean. Sections 4 and 6 are in progress.

`wang_substrate/` contains Shouqiao Wang's MIT-licensed infrastructure,
vendored verbatim at commit `d28713ac8245` with a provenance header added to
each file, and used with his explicit agreement. See `wang_substrate/PROVENANCE.md`.

`manuscript/` pins the v5 manuscript this formalization targets.
