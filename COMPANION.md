# A machine-checked proof of Erdős Problem 1002

**Ibrahim Mian and Shayaan Siddique**
*Millennium Research*

*Draft for the author's review. Not yet submitted.*

---

## Abstract

We report a complete formalization in Lean 4 of Sangyoon Kwon's proof
that, for the discrepancy sum `S_n(α) = Σ_{k≤n}(1/2 − {kα})`, the
normalized statistic `S_n(α)/log n` converges in distribution to a
centred Cauchy law of scale `1/(2π)`, resolving Erdős Problem 1002. The
formal theorem is stated against the problem's own data and depends on
exactly Lean's three standard axioms, with no placeholder anywhere in its
dependency closure. The development was rebuilt from source on
independent hardware under two separately compiled toolchains and
replayed through an independent kernel implementation.

We also record what the formalization found that reading did not: five
statements that were false as written, a symbol class that provably
cannot contain the objects it was applied to, and a defect invisible to
the standard axiom check. Several of these led to revisions of the
manuscript.

## 1. The result

The manuscript is Kwon's, sole-authored and separately submitted. Our
contribution is the formalization and the verification of it.

The formal statement is

```lean
def Erdos1002Conclusion : Prop :=
  ∀ c : ℝ, Tendsto (fun N : ℕ => distributionValue N c) atTop
             (𝓝 (cauchyLimitCDF c))
```

where `distributionValue N c` is the Lebesgue measure of
`{α ∈ (0,1) : S_N(α)/log N ≤ c}` and `cauchyLimitCDF` is the distribution
function of the centred Cauchy law of scale `1/(2π)`. The existential
form Erdős asked for — some nondecreasing `g` with limits `0` and `1`
that is the limiting distribution function — is proved alongside it as
`Erdos1002Official`.

The theorem is `Kwon1002.ProofComplete.erdos1002Conclusion`. It is stated
in `Statement.lean` against the problem's own data and is **not restated
anywhere on the route**, so no paraphrase sits between the goal and the
proof. Both forms carry `assert_no_sorry`.

To check it:

```
lake build
lake env lean scripts/closure.lean   # sorry-leaves: [] for both forms
lake env lean scripts/sweep.lean     # axiom census over the namespace
```

The development is 130 modules and roughly 80,000 lines, containing 2,583
theorems of which 2,406 are axiom-clean. The remaining declarations carry
placeholders but none lies in the main theorem's dependency closure; they
are exploratory or superseded statements retained for the record. Every
figure here regenerates from `scripts/sweep.lean`.

## 2. Provenance

The relationship between the two documents deserves stating precisely,
because the order matters.

An independent audit of an earlier formalization of the same problem was
completed and published before any collaboration began. Only afterwards
did the author and the present authors agree to work together on this
Lean development. Feedback arising from that collaboration is
collaborator feedback, not a second independent referee opinion. We are
not authors of the manuscript.

Shouqiao Wang's Gauss-transfer infrastructure is vendored under its MIT
licence, 35 modules, byte-identical to upstream apart from a provenance
header, with his agreement. It is used as shared infrastructure, not as
route-specific proof architecture.

## 3. Where the formalization takes a different route

Two divergences, both agreed with the author in advance.

**Display (16), the large-deviation bound for the continuants.** The
manuscript proves it through a perturbed transfer operator, analytic
perturbation of the leading eigenvalue, and a Chernoff argument, citing
Vallée for the Gauss-specific Ruelle–Mayer framework. Reproducing that in
Lean would have required perturbation theory the library does not have.
We prove the same estimate by a self-contained route: the exact spine
`log q_r ≤ Σ_{i<r}(−log x_i) ≤ log q_r + log 2`, centring by the Gauss
mean of `−log` (proved, via an alternating moment series against `ζ(2)`),
truncation with a dyadic excess tail, a two-parity block
exponential-moment bound resting on the mixing already formalized, and
Chernoff.

The exponent we prove is `min(v²/r, v/(1+log(r+1))²)`. On the quadratic
branch this is the manuscript's bound verbatim; on the linear branch it
carries a `log²r` loss. **No consumer uses the linear branch** — display
(20) sits where both branches deliver what is needed with margin — and
the clean linear branch is a spectral-gap statement we deliberately do
not claim. We record the gap rather than close it.

**Section 3's mixing estimate.** The development does not use the
bounded-variation Lasota–Yorke inequality it proves. The estimate comes
from Wang's Lipschitz contraction, transferred to bounded variation by an
explicit mollification. The spectral gap is his.

## 4. What the formalization found

The interesting defects were not errors in reasoning. They were cases
where the statement being proved was not the statement anyone intended —
a class of problem reading does not catch, because reading checks the
argument against the intended meaning rather than against the text.

**Five statements false as written.** Our rendering of display (33)
omitted the standing hypotheses on `α` and is false at `α = 1/2`; our
rendering of the Lemma 6.3 selection step quantified the exceptional set
before the pair it had to serve, making it false for every choice of
constants; the bounded-window observable is unbounded, because the window
type does not couple the digit block to the real block; a pointwise
recursion holds only almost everywhere; and a set used as a compact
exhaustion is not compact. Each is refuted by a counterexample that is
itself a proved theorem in the development. In every case the manuscript
was not making the false claim — the formal rendering had committed to
something stronger than the prose.

**A class that cannot contain an indicator.** Display (24)'s symbol class
had been consumed throughout the argument without a member ever being
exhibited. Building one showed that every symbol in the class is a
trigonometric polynomial, so a two-valued symbol is constant. An
indicator can therefore never lie in the class, only be approximated by
it *with a rate*, and no rate exists under measurability alone. The sets
the argument uses are truncation windows and so finite unions of
intervals, which supplies the rate; the hypothesis was simply unstated.
The author added it in version 10. A second fact surfaced at the same
time: the class parameter and the digit-cut parameter, written with the
same letter, must be different constants.

**A defect the axiom checker could not see.** Two modules declared the
same fully-qualified name for Lemma 6.1, one proving it and one leaving
it open, and neither imported the other. Which one the build used was
decided by the order of two adjacent import lines. `#print axioms`
reported a clean tree either way: it checks what a theorem depends on,
not whether the theorem it is checking is the one you intended. This was
caught by a type-check guard asserting two statements are the same
proposition, and such guards are now required on every cross-module
restatement.

**A structural pathology, seven times.** Canonical statements were
declared with placeholders in modules *below* the modules proving them,
where they can never shed the placeholder by mathematics alone. One
instance sat directly beneath the main theorem's first hypothesis.

**A claimed obstruction that was false.** A recorded finding held that a
band-mass estimate could not be derived from available tail bounds, and
stood for several rounds. The adversarial law it imagined cannot exist:
the quantity is a digit times a fixed sawtooth average, and the
sawtooth's level sets have measure `√(1−8u)` exactly. Both halves of the
argument had been present for some time; nobody had combined them.

**A silent vacuity.** For tuples of length two or more, nothing had
checked that the two conditions defining a good tuple are simultaneously
satisfiable, and the relevant proposition had never been used above one
level, so it could not surface. Non-vacuity is now proved with an
explicit witness.

The full list, with counterexamples and repairs, is in `FINDINGS.md`.

## 5. Verification

Building successfully is weak evidence: it shows the development compiles
against a cached library on the machine that produced it. We ran a
stronger check.

On hardware that had never seen the project, twice — once under a Lean
toolchain compiled from source with gcc, once with clang — we compiled
the toolchain from source, built mathlib and the development **with no
cache**, re-ran the project's own gates, replayed the entire environment
through `lean4checker`, and recorded sha256 digests of all 131 compiled
files.

Both legs passed every stage. In each, the main theorem depends on
exactly `propext`, `Classical.choice`, `Quot.sound`; the closure scan
reports an empty leaf set; the axiom census reports no theorem on a
non-standard axiom; and `lean4checker` replayed the environment without
objection. Across the two legs **all 131 files were byte-identical**.

Roughly two hours per leg. Logs and method are in `verification/`.

## 6. Discipline

Four practices did the work, and each exists because something went wrong
without it.

**Refute before proving.** Every non-trivial statement was probed at its
edge cases before any proof attempt — domain boundaries, the system's own
conventions, degenerate parameters. Roughly a dozen failed. The correct
response was always to report and restate, never to weaken a proved
result to fit.

**Machine-checked identity guards** on every cross-module restatement, so
drift between two copies of a statement cannot pass unnoticed.

**One reproducible measurement.** The axiom census and closure scan live
in the repository, so any figure in this report regenerates exactly
rather than being trusted. An earlier version of the measurement was
recreated by hand with a different convention, and successive figures
became incomparable; that is why it is committed.

**Honest partials.** Where a target resisted, the residual was named
precisely and left open. Several such notes later turned out to be stale,
and correcting them was itself productive — in a development this size,
obsolete obstruction notes cost more time than open goals.

## 7. Availability

Repository: `github.com/ronut01/erdos1002-lean`. Lean `v4.27.0`, mathlib
pinned in `lake-manifest.json`. Every manuscript version received is
pinned by sha256 in `manuscript/PROVENANCE.md`; the current target is
version 10.

## Acknowledgements

Sangyoon Kwon, for the proof, for revising it on our reports, and for
contributing directly to the formalization. Shouqiao Wang, for the
MIT-licensed Gauss-transfer infrastructure and for permission to vendor
it.
