# Manuscript provenance

The formalization target. Every version received is kept, so that any
statement in the Lean development can be traced to the exact text it was
formalized against.

## Current target

**Version 8, dated August 6, 2026.**

| File | sha256 |
|---|---|
| `erdos1002_cauchy_limit_revision_v8.pdf` | `54736403682df31a3d6e0770892602b580b529241a8bb8d44c4c343ae7210017` |
| `erdos1002_cauchy_limit_revision_v8.tex` | `d4e8a2d3cfb3836392a838ad4b947f9764dcaea32f9d529320d6067d67d29bbc` |

## Superseded

| File | sha256 |
|---|---|
| `erdos1002_cauchy_limit_revision_v5.pdf` | `80382e1bc6819aa0ab9a68d2b456892e07536f3bcc12fc2708a7cca9911d626d` |
| `erdos1002_cauchy_limit_revision_v5.tex` | `2203c69a147ba28a94475e886bf90d7d1f4ce67e426cc23f1fb679c4a9cb01e3` |
| `revision_notes_v5.pdf` | `61773be3be4f2cc1e93bc5613beab65969308862f44713f68674bffb06d11ab8` |
| `proposition_6_4_revision_note.pdf` | `ba3bbc8da3bf6624c05334e9c2757257e0cf3091f6e37ae7b25973a9d1a9db2a` |

## What changed from v5 to v8

Twenty-six hunks. Two are the corrections raised from the formalization:

- **Lemma 6.1** now hypothesizes `(z_0, z_1) != (0,0)` in place of "not
  identically zero", and proves the bound by two-step doubling of
  `S_i = |z_i| + |z_{i+1}|` over aligned and unaligned indices.
- **The block character reduction** (identity (31) of v5) now states the
  condition `j >= R+1` explicitly, matching the widened window
  `t = -R-1, ..., R`.

The remainder tightens implicit hypotheses and adds four pieces of argument:

- Explicit integrality and positivity quantifiers throughout Sections 3
  and 4: Lemma 3.1(i) over integer `r >= 0` and with a second constant `c`,
  Lemma 3.4 over integers `s, M >= 1` and `d >= 0`, Lemma 3.3 with
  `epsilon > 0`, and similar elsewhere.
- A convergence justification for the analytic family on `BV`, via the
  branch series and its `t`-derivatives on smaller discs.
- A restructured Section 4 phase-freeze argument, refining retained
  cylinders to complete prefixes of depth `k+R` and `j+R`.
- A concrete natural extension, `Omega-hat = (0,1)^2`, with sigma-invariance
  of the density proved by branchwise change of variables and preservation
  of Haar measure on the torus.
- A rewritten Section 5 small-jump step: a new displayed probability bound
  and a direct passage `Y_epsilon => Cauchy(0, 1/(2 pi))`, in place of the
  diagonal choice of `epsilon_n`.
- Measurability and compactness repairs in Section 6: Borel measurability
  of `G`, and a compact exhaustion `X_{R,K}` for the separation argument.

Reconciliation of the Lean development against v8 is in progress; until it
completes, statements in this development are formalized against v5 except
where a file records otherwise.
