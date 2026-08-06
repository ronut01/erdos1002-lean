# Kwon 1002 formalization: mathlib gap inventory

Measured 2026-08-02 against mathlib v4.27.0 (the pin used in both audits),
by grepping the actual mathlib source tree, not from memory.

## Status

`Kwon1002/Statement.lean` **compiles**. It fixes the target: the sawtooth,
the rotation sum, the normalized statistic, the finite-N distribution
function, the Cauchy CDF of scale 1/(2π), both the concrete and the
official (existential) forms of the conclusion, and a proof that the
concrete form implies the official one. That last implication is real
content and is done: `official_of_conclusion`. Nothing here depends on
the manuscript revision, which is why it could be settled first.

## The gaps

Everything at the analytic core of the argument is missing from mathlib:

| Needed by the proof | In mathlib v4.27.0 |
|---|---|
| Gauss map dynamics | **absent** |
| Gauss invariant measure | **absent** |
| Transfer operator | **absent** |
| ψ-mixing of continued-fraction digits | **absent** |
| Gauss-Kuzmin digit law | **absent** |
| Poisson point processes | **absent** |
| Random measures | **absent** |
| Compound Poisson limits | **absent** |
| Lévy continuity theorem | **absent** |
| Vague convergence | **absent** |

What does exist and is usable:

| Available | Where |
|---|---|
| Continued fractions: convergents, continuants, determinant identity | `Algebra/ContinuedFractions/*`, `NumberTheory/DiophantineApproximation/*` (14 files) |
| Basic ergodic theory: `Ergodic`, `MeasurePreserving`, `Conservative` | `Dynamics/Ergodic/*` (20 files) |
| `Int.fract` API | 23 files |
| Weak convergence, `ProbabilityMeasure` | 94 files |
| `charFun`, characteristic-function basics | 8 files |

So mathlib supplies the *arithmetic* of continued fractions and generic
measure-theoretic scaffolding, and none of the *ergodic theory of the
Gauss map* or the *point-process limit theory*. That substrate is not a
detail of the formalization; it is most of it.

## Consequence for the schedule

Wang's 1002 development is 146,510 lines, of which roughly **76,900 lines
are exactly this substrate** (his `Gauss*`, `*Poisson*`, `PsiMixing`,
`LevyContinuity`, `ContinuedFractions` modules). That is the measured
cost of building it once.

- If that layer can be reused, Kwon's proof is the top layer only, and
  the estimate is weeks.
- If it must be rebuilt, the estimate is materially longer, and the
  ergodic-theory substrate is the long pole rather than Kwon's own
  argument.

The blocking fact is that `ShouqiaoW/erdos` carries **no LICENSE**, so at
present none of it may be reused. The licensing question is therefore not
a convenience; it decides the shape of the project.

## Next, in order

1. ~~Resolve the licensing question with Wang.~~ **RESOLVED 2026-08-02:
   Wang licensed the entire repository MIT at commit d28713ac8245 (parent
   = the audited 61325b1; LICENSE is the only diff). Reuse pin fixed.**
2. Skeleton the argument (Thm 1.1; Props 2.1-2.2; Lems 3.1-3.4;
   Props 4.1-4.2; §5 Poisson chain; §6 resonance and carry; §7 assembly)
   as sorried statements, so independent agents can take disjoint
   subtrees. Hold §6 until the revised Prop 6.4 arrives, since that is
   the passage under revision.
3. Build or import the substrate, per (1).


## Skeleton status (superseded, see AUDIT.md for current, audited numbers)

The counts below were accurate when written and are now stale. For the
current measurement see the README; for the audit record see AUDIT.md.

### Original note (2026-08-03)

M1 delivered for the revision-independent part; whole project compiles
(7,891 jobs) with exactly six sorries: Prop 2.1 (reciprocity), display
(3) (alternating identity), (7) (height-error bound), Prop 2.2
(principal term, audit-pinned C0), Lem 3.3 (anti-concentration, stated
against the self-contained continuant recursion), and the master target
`kwon_main : Erdos1002Conclusion`. Lems 3.1-3.2 and section 4-5
statements await the M2 substrate import; section 6 held for Kwon's
revision by design. See ERDOS1002_KWON_FORMALIZATION_PHASE0.md.