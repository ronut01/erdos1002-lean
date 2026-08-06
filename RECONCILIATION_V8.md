# Reconciliation against manuscript v8

Every section of the v8 manuscript checked against the Lean development,
statement by statement. v8 is pinned by hash in `manuscript/PROVENANCE.md`.

**Nothing in the development is invalidated by v8.** No completed,
axiom-clean result rests on a step v8 removed. What follows is the list of
amendments, in priority order, followed by the section-by-section record.

## Amendments that block work

### 1. Two canonical statements are false, and are refuted in this tree

Both are currently `sorry`, so nothing is tainted; but neither can ever be
closed, and any file citing the canonical name inherits a permanent
`sorryAx`. These must be **replaced**, not proved.

- `Section4.torusChar_monomial_frequency` — display (33), the step that
  turns every two-block integrand into a pure phase. Refuted by
  `CharacterReduction.torusChar_monomial_frequency_false`, with the
  counterexample `α = 1/2`, `n = 1`, `j = 2`, `(r,s) = (0,1)`. The
  statement needs `α ∈ Ioo 0 1` and `Irrational α`; the corrected form is
  already proved as `CharacterReduction.torusChar_monomial_frequency'`.
  Every route to Proposition 4.2 passes through this.

- `Section6Skeleton.lemma_6_3_good_cylinder_selection` — refuted by
  `Lemma63.not_goodCylinderSelection`, for *every* `κ` and `δ`: the
  exceptional set is quantified before the pair `(A,B)`, and the pair
  `(q_{j-1}, q_j)` makes `Q_j = 0` at every irrational `α`. The
  replacement, `Lemma63.good_cylinder_selection_antiConc`, quantifies the
  pair first and is proved.

### 2. Error budget in the nonzero-mode chain

`ZeroMode.nonzero_mode_three_step` allocates the three-step error in a way
v8's proof does not deliver. v8 restores the discarded depth-`k+`
cylinders *after* the stationary-mean replacement, at cost
`L^{O(1)} e^{-cL^{1/2}}`; the Lean chain permits `e^{-c sqrt L}` only in
step 1 and only `e^{-c_0 H}` in step 3. Since `e^{-c sqrt L}` dominates
`e^{-cH}` at `H = L^{3/4}`, neither assignment of the intermediate terms is
derivable. Add the `sqrt L` summand to the step-2 bound. The consumer,
`ErrorShape.nonzero_mode_small`, already carries all three summands, so the
fix is downstream-safe. This is the last open goal on the Proposition 4.1
route.

### 3. The local-good predicate is narrower than its own consumers

`P42Cases.Display20` quantifies over `∀ j ∈ bulkJ n`. v8 states the range
explicitly as every integer `0 ≤ t ≤ 2 m_n`, and section 4 consumes the
predicate four times at `t-` and `t+`, which lie outside the bulk. It is a
`def` that nothing yet assumes, so widening it now is cheap.

### 4. The canonical window reduction is one coordinate short

`Section4.window_character_reduction` covers `t` in `[-R, R]` under
`R <= j`. The manuscript's window is `[-R-1, R]` under `j >= R+1`. The
full-range form is already proved as
`V5Identity31.window_character_reduction_v5`, with exactly the manuscript's
range and hypothesis, so this is a plumbing repair: point the canonical
name at the proved full-range statement.

## Hypotheses v8 made explicit that this development already carried

These required no change, and are recorded because they are the formal
development feeding back into the manuscript.

- The second constant `c` in Lemma 3.1, carried by every section 3
  existential.
- `∀ r : ℕ` in Lemma 3.1(i), and `1 ≤ A i` in the digit-tail product,
  where the Lean form quantifies over reals and is more general.
- Integer typing of `s`, `M`, `d`, `t_i` in Lemma 3.2, forced by `ℕ`.
- `0 < ε` in Lemma 3.4, together with a measurability hypothesis and a
  support condition that v8 now acknowledges in prose. v8's `R_w > 0` is
  not needed by the Lean statement at all.
- `D, A > 0` in Proposition 4.1, and the two-sided bars in (26).
- Borel measurability of `G` in section 6, already hypothesised in the
  skeleton.
- The natural-extension measure `dx dy / (log 2 (1+xy)^2)` on `(0,1)^2`,
  pinned in `Section4.hatMu0` since the skeleton pass, which v8 section 6
  now writes out.
- In section 5: the identity that the centered principal sum is exactly
  `Y + R`, the Chebyshev bound v8 now displays, `R_{n,ε}` as a named
  object, and the explicit diagonal construction — all four proved here
  before v8 displayed them.

Two Lean statements are strictly stronger than v8's: the descendant
estimate puts the absolute value inside the sum, and the phase freeze holds
for every `Q : ℤ` with no `Q ≠ 0`.

## Section record

**Sections 1 and 2.** Match. `reciprocity` already carried
`(N : ℕ) (hN : 1 ≤ N)`, which is v8's newly explicit "integer `N ≥ 1`".
The empty-sum convention `S_0 = 0` is definitionally true of
`rotationSum`, since `Finset.Icc 1 0` is empty.

**Section 3.** One amendment (item 3 above). One genuine analytic gap:
display (16), the large-deviation bound for `log q_r`, is absent from this
development and from the vendored substrate; display (20) is its corollary,
and v8's new analytic-family paragraph is the manuscript's justification for
it. Formalizing it needs a perturbed operator, which does not exist here.

Note on how this development reaches Lemma 3.2: **not** through the
bounded-variation Lasota-Yorke inequality proved here. It takes Wang's
Lipschitz contraction from the vendored substrate, rate `527/540`, and
transfers it to bounded variation by the mollification in `BVMixing`,
giving a spectral gap at rate `sqrt(527/540)`. The Lasota-Yorke inequality
here is real and sorry-free but is used only for its variation lemmas.

**Section 4.** Three amendments (items 1, 2, 4 above). The largest v8
restructure — refining retained cylinders into complete prefixes of depth
`k+R` and `j+R` — **costs nothing**: it lands inside the proofs of
`laterMode_phase_bound` and `earlierMode_phase_bound`, both stated as
black-box bounds over `bulkPairs n`, and `descendant_cylinder_estimate` is
already quantified over all `d < k`. The reason v8 needed the refinement is
a genuine measurability gap in v5, since the two-block amplitude is not
constant on depth-`j` cylinders. The one new obligation is the
depth-ordering side conditions the refinement creates, each of which holds
with room to spare from (19) but none of which is stated.

**Section 5.** No amendment forced by v8. Lines 834 to 1056 of v8 are
byte-identical to v5, and the diagonal choice of `ε_n` was not removed but
written out explicitly. `FourierPairs.charFun_cauchyProb` is more
load-bearing under v8, not less, since concluding weak convergence to a
named law needs exactly that identification. Two standing items, neither
introduced by v8: the truncation here is the hard cutoff where the
manuscript uses a smooth one, which differ on a shell and require an L1
approximation in place of v8's Jackson step; and the unsigned
`SmallJumps.small_jumps_variance` is not the statement section 5 consumes,
with `CorFinal.variance_not_monotone_under_sign` a proved counterexample to
deriving the signed form from it.

**Section 6.** Lemma 6.1 matches v8 line by line, including the two-step
doubling and `C = 7 / log 2`; the hypothesis `∃ i ≤ m+1, z i ≠ 0` is
equivalent to v8's `(z_0,z_1) ≠ (0,0)` under the recurrence, proved inline.
The window laws match. v8's `X_{R,K}` compact exhaustion already exists here
as `Prop64.digitCapEvent`, which retires a named obstruction in
`Lemma63`; what remains is its compactness. One residual: v8 now derives
`ℓ = 0 iff k = 0` from invertibility, while `Lemma62.resonance_bounded`
still assumes both are nonzero and so misses the mixed case. Since
`fibreMatrix_det = -1` is proved, closing this is short.

**Section 7.** No reconciliation needed. Its only diff hunk falls on the
acknowledgment boundary; the mathematics is identical between v5 and v8.

## The natural extension

v8 supplies the two justifications the Lean statements were assuming:
branchwise change of variables for the density, and Haar preservation for
the fibre matrix. Its concrete model matches this development object for
object — `Ω̂ = (0,1)^2` is `Section4.hatMu0`, `σ` is
`Section6Skeleton.natExtMap`, `S` is `hatS`, and `A_a` is `fibreMatrix`,
whose determinant `-1` is already proved. **No redefinition is required.**

Mathlib supplies almost nothing here. Verified absent: any Gauss map or
Gauss measure, any definition of mixing, any natural-extension
construction, any toral-automorphism Haar preservation, the pointwise
ergodic theorem (only the mean ergodic theorem exists), and any
measure-preservation constructor from a countable branch cover. What it
does supply and this work should use: `MeasurePreserving.skew_product` and
`measurePreserving_swap` for the fibre, the one-dimensional Jacobian
lemmas for the branchwise argument, `Measure.ext_of_iUnion_eq_univ` for the
countable assembly, the `AddCircle` bridge lemmas for the torus, and the
full `Ergodic` and `Conservative` machinery once the map is known
measure-preserving on a probability space.

Honest estimate for the unblock end to end: **eight to twelve weeks**, of
which base measure-preservation, two-sided mixing, and the L2 density
account for most of the cost. Two-sided mixing is the long pole: v8's
one-line justification is not formalizable as stated, since mathlib has no
mixing predicate to invoke, so it must be done by hand against the concrete
model, reducing to this development's own proved mixing chain.

One correction to the repository's own record: the torus fibre map is
listed alongside the long items as blocked, on the grounds that mathlib's
`AddCircle` machinery is not connected to the `Int.fract` representation.
That obstruction is softer than recorded — the bridge lemmas exist, and the
fibre map factors as a swap composed with a skew product. It is a
days-scale task and should be pulled forward.

## Work available now, blocked on nothing

Four measurability goals in `Prop64`; two bookkeeping goals in the
skeleton, including `resetSet_measure_pos`, which needs only a density
bound on an explicit box; compactness of `digitCapEvent`, which retires the
`Lemma63` obstruction; the mixed-case strengthening of `resonance_bounded`;
merging four skeleton goals already closed elsewhere in the tree; and
replacing the one refuted skeleton statement. Separately, `digit_truncation`
needs only continued-fraction contraction, for which mathlib's
approximation results are reusable.

When merging a statement proved elsewhere into the skeleton, keep the
`example : ... := _root_.Kwon1002....` type-check idiom already used in
`Lemma63`, so that a weakened restatement cannot be substituted silently.
