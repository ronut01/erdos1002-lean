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

### 5. Residual 2 of `TupleFinal` quantified over a class its own route cannot reach

`TupleFinal.goodSet_mark_factorization` (Proposition 4.1 for the mark event)
quantified over merely measurable `B`, with only `∃ δ > 0, ∀ x ∈ B, δ ≤ |x|`
and `∃ R, ∀ x ∈ B, |x| ≤ R`. `Kwon1002/JacksonGate.lean` shows the route the
residual's own docstring names cannot reach that class:
`JacksonGate.continuous_of_isInPD` proves every symbol of display (24)'s class
`P_D(L)` is continuous (the coefficients vanish outside `|v| ≤ L^D`, so the
`tsum` is a trigonometric polynomial), and `isInPD_const_of_two_valued` draws
the consequence that a two-valued member is constant. So `1_B` is never *in*
the class; the passage is an approximation, and the residual's own error budget
fixes the rate at `η_L = O(L^{-2})` uniformly in the digit. For a merely
measurable `B` no such rate exists — and `volume (frontier B) = 0` does not
repair it, since it gives qualitative approximability without a rate.

**What was done.** The residual is *split*, not weakened, and no consumer
signature changed.

- `TupleFinal.goodSet_mark_factorization_intervals` — residual 2a, the Jackson
  step at the class it admits. It carries the added hypothesis
  `IntervalClass.IsFiniteUnionOfIntervals B`. That predicate is defined in the
  new `Kwon1002/IntervalClass.lean` as "a union of at most `m` order-convex
  sets"; order-convexity (`Set.OrdConnected`) is the rendering of "interval"
  that is stable under the operations the argument performs and needs no
  endpoint bookkeeping.

- `TupleFinal.goodSet_intervals_to_measurable` — residual 2b, the implication
  *interval case ⟹ measurable case*, uniformly in `k`. This is the
  approximation step, and isolating it is the whole point: the consumers
  (`det_quasi_independence`, `det_tuple_measure_convergence`,
  `tuple_measure_convergence`, `tuple_quasi_independence`, and through the
  token-identity checks the canonical `LevyExponent.tuple_measure_convergence`
  and `TupleMeasure.tuple_quasi_independence`) quantify over measurable `B`,
  and those statements are expected to be *true* at that generality. Pushing
  the interval hypothesis into them would weaken true statements, so it is not
  done.

- `TupleFinal.goodSet_mark_factorization` — statement byte-identical to before
  (checked against `git show`; the only textual change is `:= by` becoming
  `:=`), every consumer and every token-identity check untouched, but no longer
  a bare `sorry`: it is now *derived* from 2a and 2b.

**Why `IsFiniteUnionOfIntervals` is the right hypothesis, machine-checked.**
`IntervalClass.markSection_isUnionOfIntervals` proves that `W(θ) = {θ}(1-{θ})/2`
is piecewise monotone with exactly two branches on the fundamental cell
(increasing on `[0,1/2]` by `monotoneOn_W_left`, decreasing on `[1/2,1)` by
`antitoneOn_W_right`), so for `B` a union of `m` intervals the `θ`-section
`{θ ∈ [0,1) : κ·W(θ) ∈ B}` is a union of at most `2m` intervals **for every
real `κ`** — hence uniformly in the digit `a` and in the sign `(-1)^j`, which
enter only through `κ = ±a/L`. That uniformity is exactly what the tuple sum
needs and what the Jackson rate `O(m/deg)` is available at.

**Every instantiation the development makes supplies it.**
`IntervalClass.isUnionOfIntervals_truncation` proves the large-jump truncation
window `{x : ε < |x| ∧ |x| ≤ R}` — the only shape `B` ever takes below
Proposition 5.1, and the shape the residual's own `_hB0`/`_hBbd` force — is a
union of **two** intervals. `TupleFinal.goodSet_mark_factorization_truncation`
records that instance as a named theorem, so residual 2a alone already covers
every concrete use; residual 2b exists only to keep the consumers stated at
their present generality.

**What remains open in 2a.** Proposition 4.1 itself is now unconditional
(`prop_4_1_marked_factorization_unconditional`), and the sorting bijection is
discharged (`JacksonGate.exists_goodTuple_of_sepGoodSet`). The single remaining
obstruction is the Jackson construction proper: from "the section is a union of
at most `2m` intervals" to "a trigonometric polynomial of degree `L^D` within
`L¹`-distance `O(m·L^{-D})` of its indicator, with coefficient `ℓ¹` norm inside
display (24)'s budget". Mathlib carries no Fejér or Jackson kernel
(`Mathlib/Analysis/Fourier/` has `AddCircle`, `FourierTransform`,
`RiemannLebesgueLemma`, `Inversion`, `PoissonSummation` and no summability
kernel of positive type), so this is a from-scratch construction.

### 6. The `ℓ¹` budget of display (24) is binding, and forces two distinct `D`s

`Kwon1002/OneLevelLaw.lean` exhibits the first member of `IsInPD` anywhere in
the development (`isInPD_separable`; the class had only ever been consumed,
never populated, so nothing had checked that display (24) admits the symbols
§5 needs). Building it surfaces that the third clause of (24),
`∑_{a,v} |c(a,v)| ≤ L^D`, is not bookkeeping. A digit weight of size `O(1)` on
the cut `a ≤ L^D` already spends the whole allowance, so a symbol that *also*
carries a nonconstant phase factor — a Jackson polynomial of degree `L^D`,
whose coefficients contribute a further `log`-sized `ℓ¹` norm — overshoots and
must be placed in `P_{D'}(L)` for some `D' > D`. Proposition 4.1 holds for
every `D > 0`, so this costs nothing; but the `D` of the symbol class and the
`D` of the digit cut are then *different constants*, and any statement tying
them together is mis-stated. Recorded on `goodSet_mark_factorization_intervals`
and in the header of `Kwon1002/OneLevelLaw.lean`.

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
with room to spare from (19). Update (stage C): these are now stated and
proved in `Kwon1002/PhaseBounds.lean` §6 (`lt_kMinus_of_bulk`,
`prefix_lt_kMinus_toNat_of_bulk` — `j+R < t₋` and `k+R < t₋` over the bulk
with `60H − R − 1` to spare, `succ_lt_kMinus_toNat_of_bulk` — the
`j_s + 1 < k₋` ordering that display (22) consumes in the §4 body,
`subResonance_prefix_lt_kMinus_toNat` — `k + R < t₋` under `k < t₀ − 100H`,
and the (20)-range bounds `kMinus/kPlus_toNat_le_two_mIndex_of_bulk`).
Also in stage C: `natExt_marginal` is proved (case 1 of the proof of 4.2 is
now sorry-free end to end in its primed form), and PhaseBounds §7 proves the
(20)-free sub-steps of cases 2 and 3 — the pair oscillatory form
(`monoAt_mul_oscillatory`), frequency freezing (`Qpair_congr`), the
explicit-`O(1)` exponent identities at both cuts
(`kMinus/kPlus_exponent_identity`, defect `A ∈ (−3λ, 0]`), and the retained
`q_{t₋}² ≤ 2e^{−cH} n|Q|` / ascended `q_{t₊}² ≥ e^{γ₊H/2} n|Q_j|`
inequalities (`retained_descendant_bound_at_cut`,
`ascended_descendant_bound_at_cut`).

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

**Status update.** That item is now **done**, and it needed no `AddCircle`
bridge at all. `Lemma62.torusFibre_measurePreserving` is proved: the map
is `Prod.swap` followed by `MeasurePreserving.skew_product` over the
identity, and the fibre rotation `r ↦ {r - c}` preserves Lebesgue measure
on `(0,1)` by cutting `[0,1)` at `1 - {c}` and translating the two pieces
(`NatExtMeasure.map_fract_add_Ico`).

Two further pieces of the natural extension have landed with it, both in
`Kwon1002/NatExtMeasure.lean`. The base measure has a name, `hatNu`, and a
total mass, `hatNu_univ = 1`; and `hatMu0_eq_prod` puts `μ̂₀` in the
product shape `μ̂₀ = ν̂ ⊗ m_{T²}` that `skew_product` consumes, which also
yields `IsProbabilityMeasure hatMu0` (previously only `IsFiniteMeasure`).
The single remaining input to `hatS_measurePreserving` is therefore
`natExtMap_measurePreserving`, the branchwise change of variables for the
density on the base.

## Work available now, blocked on nothing

Four measurability goals in `Prop64`; two bookkeeping goals in the
skeleton, including `resetSet_measure_pos`, which needs only a density
bound on an explicit box; the mixed-case strengthening of
`resonance_bounded`; merging four skeleton goals already closed elsewhere
in the tree; and replacing the one refuted skeleton statement.

Two entries of this list have been corrected by the work itself.

*Compactness of `digitCapEvent` is false.* This list claimed it as
available work that would retire the `Lemma63` obstruction.
`Prop64.not_isCompact_digitCapEvent` proves the opposite: the digit cap
constrains only the digit block, and the Lean type `WindowSpace R` carries
the real and torus blocks as full copies of `ℝ`, so the set contains an
affine copy of `ℝ^{2R+1}`. The compact object is `Prop64.digitCapCube`,
v8's `X_{R,K}`, which caps the digits *and* confines the other two blocks
to the closed unit cube; `Prop64.isCompact_digitCapCube` is proved and the
`Lemma63` note now points at it.

*`digit_truncation` needed more than contraction.* It is not pointwise
true on `WindowSpace (R+M)`, where the digit and real blocks are
unrelated. The structural input is the marginal description of the window
law, now supplied as `Kwon1002.ae_orbitConsistent`
(`Kwon1002/WindowMarginal.lean`): `μ_R`-almost every window is an
irrational Gauss orbit with its own digits, so `1/x_t = a_t + x_{t+1}`.
What remains for `digit_truncation` is the contraction estimate proper
plus a uniform modulus for the continuous factors on the cube; both are
now formulable, and neither is written.

When merging a statement proved elsewhere into the skeleton, keep the
`example : ... := _root_.Kwon1002....` type-check idiom already used in
`Lemma63`, so that a weakened restatement cannot be substituted silently.
