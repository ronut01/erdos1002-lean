# Independent audit of this development

An auditor with no knowledge of what we believed we had proved was given
this repository and asked, adversarially, which theorems are real. Its
findings outrank our own claims. Recorded here in full, including the
findings against us.

## Machine-determined inventory

These are the figures **as the audit found them**, and are left unchanged so
the record stands. The development has grown since; for the current
measurement see the README.

| | count |
|---|---|
| Declarations in `Kwon1002` | 625 |
| Theorems **axiom-clean** (`propext, Classical.choice, Quot.sound`) | **458** |
| Theorems carrying `sorryAx` | 33 |
| Theorems with any **other** axiom (custom, `native_decide`) | **0** |

`collectAxioms` is transitive, so the clean theorems are clean *through*
the vendored `wang_substrate` too: no sorried third-party lemma leaks in,
and no custom axiom exists anywhere in the dependency cone.

## Fidelity

Ten theorems were checked line-by-line against the manuscript displays
they claim to formalize. Nine **FAITHFUL**; two of those (`principal_term`,
`shrinking_anti_concentration`) are *stronger* than the paper states, the
paper allows a constant depending on `(r,s)` where the formalization
proves it uniform, and pins `C₀ = E*/2 + 5/8` as a closed term where the
paper says only "there is an absolute constant".

No vacuity anywhere: every `∃ C` places the constant outermost, `Estar` is
backed by a proved summability lemma, the tuple count's `.ncard` is over a
set made finite by an explicit support condition, and no proved theorem is
quantified over an empty set or witnessed trivially.

## Findings against us, and what we did

1. **`descendant_phase_small` was weaker than display (23)**, it fixed one
   gratuitous extra digit (`∀ i ≤ k` where (23) is a depth-`k` cylinder,
   `∀ i < k`). The proof never used the surplus. **FIXED**: strengthened to
   `∀ i < k`, recompiled, still axiom-clean.
2. **Display (22), the substantive half of Lemma 3.4, is not in this
   project**, not proved, not stated. Only its converse (23) exists. The
   module headers say "converse", but to be unambiguous: *Lemma 3.4 is not
   formalized here.*
3. **`poisson_count_limit` is manuscript-independent.** Its two
   manuscript-linking hypotheses are unused (`_hlaw`, `_hrate`); it
   delegates to Wang's factorial-moment theorem for arbitrary inputs. It is
   true and its docstring is candid, but **it must not be cited as a
   formalization of Prop 5.1.**
4. Stale docstring (fixed) and a stale sorry count in `GAPS.md` (fixed).

## Shadow check

For each of the 33 sorried theorems the auditor tested definitional
equality of its type against all 458 clean ones. Exactly five sorried
statements have a clean discharge, and in every case the types are
**definitionally identical**, so `Discharge.lean`'s claim that it restates
canonical goals *verbatim* is true. The other 28 have **no clean
counterpart anywhere**: nothing is being quietly claimed under a weakened
restatement.

## Scope, stated plainly

§2 essentially complete. §3: three of four estimates (see finding 2).
§4: supporting results proved, main propositions sorried. §5: partial -
the analytic core (the classical integral, the Cauchy characteristic
function, the Lévy exponent) is unconditional; the Poisson limit is not.
§6 absent by design, pending Kwon's revision. §7 and the master theorem
`kwon_main` are a single sorried goal.

**This is not a proof of Erdős 1002 and does not claim to be.**


---

# Second pass (2026-08-03, later): 973 theorems

A nine-agent fleet in two dependency-ordered waves closed the largest
remaining gaps. Counts re-measured after integration: **973 theorems** in
the `Kwon1002` namespace (from 625), **20** sorried goals.

## The two headline closures

* **Display (22), Lemma 3.4's substantive half, is now PROVED**
  (`Kwon1002.descendant_cylinder_estimate`, axiom-clean). This was
  finding (b) of the first audit: previously absent from the project in
  any form. Lemma 3.4 is now genuinely formalized, not just its converse.
* **Lemma 3.2 is now unconditional** (`TransferIdentity.lemma_3_2'`,
  axiom-clean), via the cylinder-transfer identity
  (`TransferIdentity.cylinder_transfer_eq_kwonDensity_Ioo`).

## A FALSE STATEMENT IN OUR OWN FORMALIZATION, found and fixed

`TransferMixing.cylinder_transfer_eq_kwonDensity` asserted Kwon's display
(14) for all `y ∈ Icc 0 1`. **That is false at `y = 1`**: Wang's cylinders
are `Ioc (1/(q+1)) (1/q)`, so at `y = 1` the point `1/(n+1+y) = 1/(n+2)`
is a right endpoint and the surviving branch index shifts. For `w = [1]`
the left side is `0` while the right side is bounded below by a positive
constant. This is machine-refuted:
`TransferIdentity.cylinder_transfer_eq_kwonDensity_Icc_false`.

**Fixed**: both the identity and `isCondDensity_of_transfer_eq` now read
`Ioo`, and a new `gaussMeasure_ae_Ioo` (ν{1} = 0, since ν has a Lebesgue
density) carries every consumer, which only ever used the identity ν-a.e.
Nothing downstream weakened. **The defect was ours, not Kwon's**, his
manuscript states (14) on the interior.

## A genuine mathematical wall (NOT waiting on Kwon)

Prop 4.1's mixing input cannot be derived from the Lemma 3.2 we have, and
this is a real obstruction rather than bookkeeping:

* `Prop41.lem_3_2_conditional_multiblock_mixing` quantifies over
  **BV** observables (`BVBoundedBy`: bounded sup + bounded variation).
* `TransferMixing.lemma_3_2` quantifies over **Lipschitz** observables,
  because Wang's Lasota-Yorke contraction is proved only for the
  Lipschitz seminorm.

These are not comparable in the needed direction, and §4's actual
observables sit exactly in the gap: the first-digit indicator is proved
**BV** (`firstDigitIndicator_bv`) and proved **not Lipschitz for any
constant** (`firstDigitIndicator_not_lipschitz`).

**Closing §4 therefore requires a BV Lasota-Yorke inequality**
(`Var(L²f) ≤ ρ₀ Var f + C‖f‖₁` plus Helly), which neither Kwon's
manuscript nor Wang's development formalizes. That is new mathematics -
not something Kwon's revision supplies. Four further differences between
the two statements (sign, constant shape, cylinder convention,
measurability) are all repairable once the norm class is fixed, and are
recorded in `TransferIdentity.lean`.

## Other findings recorded by the fleet

* `Assembly5.signed_small_jumps_variance` cannot be derived from
  `SmallJumps.small_jumps_variance`: the `(-1)^j` factor squares away only
  on the diagonal, and the off-diagonal terms genuinely differ.
* Display (30)'s error bracket has an implicit upper constraint on `c`
  that the manuscript leaves unstated.
* §5 switches between the deterministic bulk index set of (19) and a
  random one without remark.
* `Prop42.two_block_monomial_core`'s own docstring misdescribed its role
  (corrected in-file).


---

# Third pass, final measured state (2026-08-03, late)

**The numbers reported in the section above ("973 theorems … 20 sorried
goals") are STALE and should not be quoted.** An independent auditor
re-measured the environment with two mutually independent methods
(`collectAxioms`, and a constant-graph walk that never calls it), which
agreed exactly, and cross-checked against a raw `sorry`-token grep:

| | count |
|---|---|
| Hand-written theorems in `Kwon1002` (internals filtered) | **825** |
| **Axiom-clean** (`propext, Classical.choice, Quot.sound`) | **728** |
| Sorry-primary (own proof term) | **54** |
| Sorry-consumer (clean body, sorried dependency) | 43 |
| **Any non-standard axiom (custom / native_decide)** | **0** |

Also: 0 `axiom` declarations in our namespace, and 0 across the 1108
vendored `Erdos1002` declarations. The earlier "973" counted Lean's
auto-generated internals; the earlier "20 sorried goals" was wrong by a
factor of 2.7.

## The obstruction reported earlier today is fully closed

The BV-versus-Lipschitz wall, which required a Lasota-Yorke inequality
that existed in no formalization anywhere, is gone, and the whole chain
verifies axiom-clean:

    BVLasotaYorke.gaussTransfer_bv_lasotaYorke        (Var(Lf) ≤ ¾Var f + ‖f‖₁)
      → BVMixing.lemma_3_2_BV                          (BV multi-block mixing)
      → MixingBV.lem_3_2_conditional_multiblock_mixing' (Prop 4.1's stated input)
      → Bridge.good_tuple_multiblock_mixing'           (§4's good-tuple mixing)

Six lemmas of variation theory absent from mathlib were built along the
way (`eVariationOn_add_le`, `_finsum_le`, `_mul_le`, `_le_of_lipschitz`,
`_le_of_tendsto`, `abs_le_var_add_mean`), plus interval-indicator
variation bounds, all candidates for upstreaming.

## Findings this pass

* **A stated justification was wrong (benign).** Two docstrings justify
  the BV bound on the zero-mode digit observable by counting jumps; that
  argument yields only `O(L^{2D})`, not the claimed `2L^D`. The constant
  is nevertheless correct, but it needs display (24)'s ℓ¹ mass bound,
  not the jump count. Proved that way (`bv_of_firstDigit_step`); the
  docstrings should cite (24).
* All headline theorems re-verified: **zero deviations** from
  `[propext, Classical.choice, Quot.sound]`.
