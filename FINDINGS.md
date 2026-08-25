# What the formalization found

Formalization is usually defended as a way to gain confidence in an
argument. That was not the interesting part of this project. The
interesting part is a class of defect that reading cannot catch, because
it is not about whether a proof is *correct* — it is about whether the
statement being proved is the statement anyone intended.

This is the consolidated list. Each entry names the defect, how it was
caught, and what was done. Every counterexample cited is itself a proved
theorem in this repository, not an informal argument.

---

## Statements that were false as written

**Display (33), the monomial frequency.** Our rendering omitted the
standing hypotheses on `α`. It is false at `α = 1/2`, `n = 1`, `j = 2`,
`(r,s) = (0,1)`: the left side is `1`, the right `−1`. The Gauss orbit of
a rational reaches `0`, where Lean's `0⁻¹ = 0` convention makes the digit
`0` and breaks the recursion. Refuted by
`CharacterReduction.torusChar_monomial_frequency_false`; the corrected
form carries `α ∈ Ioo 0 1` and `Irrational α`.

**The Lemma 6.3 selection step.** Our rendering quantified the
exceptional set *before* the pair it had to serve. It is false for
**every** choice of the constants: take the pair `(q_{j−1}, q_j)`, which
makes the frequency vanish at every irrational, so the complement of the
exceptional set contains no irrational at all. Refuted by
`Lemma63.not_goodCylinderSelection`. The manuscript was never making this
claim; the repair quantifies the pair first.

**The bounded-window observable.** Asserted bounded; it is not. The
window type does not couple the digit block to the real block, so the
expression runs to `−∞` along windows with a large central digit while
the real coordinate stays pinned. Refuted by `bwindow_unbounded`. The
manuscript asserts only that a bounded *representative* exists; the
formal rendering had written the naive formula on the whole type. The
author supplied the repair, clamping at exactly the bound the
formalization had independently proved for the true process.

**A pointwise recursion that holds only almost everywhere.** The
composition of the extension map with its inverse is not the identity
pointwise, because the Gauss map of the reconstructed coordinate equals
the original only inside `[0,1)`. Handled by an invariant region of full
measure rather than by assertion.

**A compactness claim.** A set used as the compact exhaustion is not
compact: it caps the digit block while the real and torus blocks are full
copies of `ℝ`. Refuted by `not_isCompact_digitCapEvent`; the genuinely
compact object is a different set, now named and proved.

---

## A class that could not contain what it was assumed to contain

Display (24)'s symbol class had been consumed throughout the argument
without a single member ever being exhibited. Building one
(`isInPD_separable`) surfaced two facts invisible from reading.

Every symbol in the class is a trigonometric polynomial, so a symbol
taking only the values `0` and `1` is **constant**
(`JacksonGate.isInPD_const_of_two_valued`). An indicator can therefore
never lie in the class — only be approximated by it, with a *rate*. Under
measurability alone no rate exists, and null boundary does not supply one
either, since it gives approximability without a rate. The passage needs
finite boundary complexity of the set.

Every set the argument actually uses is a truncation window, which is a
union of two intervals, so nothing breaks. But the hypothesis was
unstated. The author added it to the manuscript in version 10.

Second fact: the class parameter and the digit-cut parameter, written
with the same letter, must be **different constants** — a symbol carrying
both a cut and a phase factor needs a strictly larger class.

---

## A defect the axiom checker was structurally blind to

Two files declared the same fully-qualified name for Lemma 6.1, one
proving it and one leaving it open, in modules that did not import each
other. Which one the build used was decided entirely by the order of two
adjacent import lines in the root file. The axiom sweep reported a clean
tree either way: it checks what a theorem depends on, not whether the
theorem it is checking is the one you think it is.

This was caught by a type-check guard, and such guards — an `example`
asserting two statements are literally the same proposition — are now
mandatory on anything restated across modules. They caught a second real
problem later, where overwriting a definition would have turned a true
refutation into a false theorem.

---

## A structural pathology, seven times

Canonical statements were repeatedly declared with placeholders in
modules *below* the modules that proved them. Such a name can never shed
its placeholder by mathematics alone, no matter what is proved.

This looks like tidiness and is not. One instance sat directly beneath
the main theorem's first hypothesis, and the whole of section 5 was
blocked behind another: every module declaring a section 5 residual
failed to import every module proving section 4. The fix is relocation,
or a join module importing both families. It is now the first thing to
check when a proved statement fails to discharge its consumer.

---

## A claimed obstruction that was not one

A recorded finding held that a certain band-mass estimate could not be
derived from the available tail bounds, and it stood through several
rounds of work as the one genuinely missing input.

It was wrong. The adversarial law it imagined cannot exist, because the
quantity is a digit times a fixed sawtooth average, and the sawtooth's
own geometry constrains it: the level sets have measure `√(1−8u)`
exactly. The estimate follows without the local digit law everyone
assumed was needed. Both halves of the argument had been in the tree for
some time; nobody had multiplied them together.

---

## A silent vacuity

For tuples of length two or more, nothing in the development had checked
that the two conditions defining a good tuple can be satisfied
*simultaneously*. Every statement quantified over good tuples was
therefore unguarded above one level, and Proposition 4.1 had never been
used above one level anywhere, so the vacuity had no way to surface.
`eventually_exists_goodTuple` now proves non-vacuity with an explicit
witness.

A related observation, harmless but worth knowing: the constant `200` in
display (19) keeps the bulk index set empty until `n` exceeds roughly
`exp(5·10^10)`. Every statement of the form "eventually in `n`, for all
`j` in the bulk" is therefore vacuously true at any computable scale.

---

## Records that were stale

Repeatedly, work was blocked on an obstruction that had already been
removed, because a docstring recorded a state that was no longer true. In
a development this size, obsolete obstruction notes cost more time than
open goals do. Correcting a falsified record became a standing
requirement of every work item.

---

## The discipline that produced these

**Refute before proving.** Every non-trivial statement was probed at its
edge cases before any proof was attempted — domain boundaries, the
system's own conventions (inversion at zero, fractional parts at
integers), degenerate parameters. Roughly a dozen statements failed that
probe. In each case the correct outcome was to report and restate, never
to weaken a proved result to fit.

**Machine-checked identity guards** on every cross-module restatement, so
a drift between two copies of a statement cannot go unnoticed.

**One reproducible measurement.** The axiom sweep and the closure scan
live in `scripts/`, so any figure quoted in a report can be regenerated
exactly rather than trusted.

**Honest partials.** Where a target resisted, the residual was named
precisely and left open rather than forced. Several such notes later
turned out to be stale, and correcting them was itself productive.
