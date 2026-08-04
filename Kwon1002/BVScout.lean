/-
Scratch file (BV scout agent): ATTACK (d), SCOUT AND STATE.

The bottleneck: §4 of Kwon's manuscript feeds *digit indicators* into
Lemma 3.2, and those are `BV(0,1)` but (machine-checked in-tree,
`Kwon1002.TransferIdentity.firstDigitIndicator_not_lipschitz`) not
Lipschitz.  Everything currently proved about the Gauss transfer operator
- Wang's `Erdos1002.gaussTransfer_strict_lipschitz_contraction` (rate
`527/540`) and hence `Kwon1002.Transfer.lemma_3_2` /
`Kwon1002.TransferIdentity.lemma_3_2'`, lives on the Lipschitz seminorm.

This file is the *scouting* deliverable:

1. an exhaustive inventory of the variation API actually present in this
   environment (Mathlib and Wang's substrate), with exact names, and an
   explicit list of what is **absent**;
2. the missing pieces of the BV *algebra*, **proved** here (they are the
   things every route to a Lasota-Yorke inequality needs, and none of them
   is in Mathlib);
3. the sharpest BV Lasota-Yorke inequality these APIs can express, stated
   faithfully (sorried), together with its iterate and the BV form of
   Lemma 3.1(i) it is meant to produce;
4. the BV form of Lemma 3.2 that §4 needs, reproduced **token-identically**
   from `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing`;
5. a second, cheaper route to (4) that **bypasses** the Lasota-Yorke
   inequality entirely, decomposed into named sorried steps.

Nothing here is weakened.  No shared module is edited.
-/
import Kwon1002.Prop41
import Kwon1002.TransferIdentity

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002.BVScout

open Prop41

noncomputable section

/-!
# 1. Inventory

## 1.1 Mathlib: `Mathlib/Topology/EMetricSpace/BoundedVariation.lean`

This is the *entire* variation API of Mathlib (plus the five differentiability
consequences in `Mathlib/Analysis/BoundedVariation.lean`).  All of it lives at
the generality `{α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]`.

**Definitions.**
* `eVariationOn (f : α → E) (s : Set α) : ℝ≥0∞`
  `:= ⨆ p : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s},`
  `     ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i+1))) (f (p.2.1 i))`
* `BoundedVariationOn f s := eVariationOn f s ≠ ∞`
* `LocallyBoundedVariationOn f s := ∀ a b, a ∈ s → b ∈ s → BoundedVariationOn f (s ∩ Icc a b)`
* `variationOnFromTo f s a b : ℝ`, the *signed* variation, `.toReal`-squashed.

**Lemmas, `namespace eVariationOn`.**
* `nonempty_monotone_mem`, `eq_of_edist_zero_on`, `eq_of_eqOn`
* `sum_le`, `sum_le_of_monotoneOn_Icc`, `sum_le_of_monotoneOn_Iic`   (the
  "any sampling sequence is dominated by the variation" workhorse)
* `mono` (set monotonicity), `BoundedVariationOn.mono`,
  `BoundedVariationOn.locallyBoundedVariationOn`
* `edist_le` : `edist (f x) (f y) ≤ eVariationOn f s` for `x y ∈ s`
* `eq_zero_iff`, `constant_on`, `eVariationOn.subsingleton`
* `lowerSemicontinuous_aux`, `lowerSemicontinuous` (pointwise-on-`s`
  convergence), `lowerSemicontinuous_uniformOn`
* `BoundedVariationOn.dist_le`, `BoundedVariationOn.sub_le`
* `add_point`
* **additivity in the set**: `add_le_union`, `union`, `Icc_add_Icc`, `sum`,
  `sum'` , `sum` and `sum'` are *finite* partitions into consecutive `Icc`s
* **reparametrisation**: `comp_le_of_monotoneOn`, `comp_le_of_antitoneOn`,
  `comp_eq_of_monotoneOn`, `comp_inter_Icc_eq_of_monotoneOn`,
  `comp_eq_of_antitoneOn`, `comp_ofDual`

**Outside the namespace.**
* `MonotoneOn.eVariationOn_le : eVariationOn f (s ∩ Icc a b) ≤ ENNReal.ofReal (f b - f a)`
* `MonotoneOn.locallyBoundedVariationOn`
* `variationOnFromTo.{self, nonneg_of_le, eq_neg_swap, nonpos_of_ge, eq_of_le,`
  `  eq_of_ge, add, edist_zero_of_eq_zero, eq_left_iff, eq_zero_iff_of_le,`
  `  eq_zero_iff_of_ge, eq_zero_iff, monotoneOn, antitoneOn,`
  `  sub_self_monotoneOn, comp_eq_of_monotoneOn}`
* `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`, **Jordan
  decomposition**, `f = p - q` with `p q` monotone on `s`
* `LipschitzOnWith.comp_eVariationOn_le : eVariationOn (f ∘ g) s ≤ C * eVariationOn g s`
  (Lipschitz on the **outside**), `LipschitzOnWith.comp_boundedVariationOn`,
  `LipschitzOnWith.comp_locallyBoundedVariationOn`,
  `LipschitzWith.comp_boundedVariationOn`, `LipschitzWith.comp_locallyBoundedVariationOn`,
  `LipschitzOnWith.locallyBoundedVariationOn`, `LipschitzWith.locallyBoundedVariationOn`
* `Mathlib/Analysis/BoundedVariation.lean`:
  `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_real`,
  `…_of_mem_pi`, `…_of_mem`, `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`,
  `LocallyBoundedVariationOn.ae_differentiableWithinAt`, `…ae_differentiableAt`,
  `LipschitzOnWith.ae_differentiableWithinAt_of_mem_real`,
  `LipschitzOnWith.ae_differentiableWithinAt_real`,
  `LipschitzWith.ae_differentiableAt_real`
* `Mathlib/Analysis/ConstantSpeed.lean` uses `eVariationOn` for arc length
  (`variationOnFromTo` reparametrisation); nothing reusable here.

## 1.2 What Mathlib does **not** have (verified by exhaustive grep)

* **No BV algebra at all.**  There is *no* lemma about
  `eVariationOn (f + g)`, `eVariationOn (c • f)`, `eVariationOn (f * g)`,
  `eVariationOn (∑ …)` or `eVariationOn (∑' …)`.  `eVariationOn.sum` /
  `sum'` are about summing over a *partition of the domain*, not over
  functions.  §2 below supplies the four that a Lasota-Yorke proof needs.
* **No countable domain additivity.**  `eVariationOn.sum` is finite only;
  the Gauss branch partition `⋃_{q≥1} [1/(q+1), 1/q]` is countable and
  accumulates at `0`, so `∑' q, eVariationOn f (I q) ≤ eVariationOn f (Ioo 0 1)`
  has to be built by hand (finite sums + `ENNReal.tsum_eq_iSup_sum`).
* **No `‖f‖_∞ ≤ Var f + ‖f‖₁ / μ(s)`.**  The one-sided
  `BoundedVariationOn.sub_le` is the closest thing.
* **No Helly selection theorem** for BV (the only `Helly` in Mathlib is the
  convex-geometry one in `Mathlib/Analysis/Convex/Radon.lean`).
* **No `BVFunction` / `BV` normed space**, no `BV` completeness, no compact
  embedding `BV ↪ L¹`.
* **No transfer operator, no Perron-Frobenius, no Ruelle operator, no
  Lasota-Yorke, no Ionescu-Tulcea-Marinescu / Hennion quasi-compactness**
  anywhere in Mathlib.  (Grep for `Perron`, `Ruelle`, `Lasota`,
  `transferOperator` returns only `Perron` as a name in the
  Denjoy-Perron-Henstock integral bibliography.)

## 1.3 Wang's substrate

`grep -rn 'eVariationOn|Variation|variation|BV' wang_substrate/` returns
**nothing**.  The substrate has no variation content whatsoever; its whole
regularity theory is the Lipschitz predicate

* `Erdos1002.GaussUnitLipschitzBound (K : ℝ) (f : ℝ → ℝ) : Prop :=`
  `  ∀ ⦃x⦄, x ∈ Icc 0 1 → ∀ ⦃y⦄, y ∈ Icc 0 1 → |f x - f y| ≤ K * |x - y|`
  (`GaussTransferContraction.lean:432`)

together with `Erdos1002.GaussUnitNonnegative` and
`Erdos1002.GaussUnitUpperBound A` (`GaussTransferAdjoint.lean:288,291`), and
the contraction chain

* `Erdos1002.gaussTransfer_strict_lipschitz_contraction`
  `: GaussUnitLipschitzBound K f → GaussUnitLipschitzBound ((527/540) * K) (gaussTransfer f)`
* `Erdos1002.gaussTransfer_strict_lipschitz_contraction_general`
* `Erdos1002.gaussCenteredTransfer_strict_lipschitz_contraction`
  and its iterate (rate `(527/540)^m`)
* `Erdos1002.abs_gaussTransfer_iterate_sub_integral_le` (the sup-norm gap)

The `BVBoundedBy`-style predicate the task mentions is **not** in the
substrate.  It exists in exactly two places in the tree, and they agree
token-for-token:

* `Kwon1002.Prop41.BVBoundedBy` (`Kwon1002/Prop41.lean:251`)
* `Kwon1002.TransferIdentity.BVBoundedBy'` (`Kwon1002/TransferIdentity.lean:548`)

```
def BVBoundedBy (K : ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ K) ∧ eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K
```

Everything known about it in-tree is:
* `Kwon1002.TransferIdentity.firstDigitIndicator_bv`, the §4 observable is in
  the class, with `K = 1`;
* `Kwon1002.TransferIdentity.firstDigitIndicator_not_lipschitz`, it is not in
  the Lipschitz class for any constant;
* `Kwon1002.ErrorShape.good_tuple_multiblock_mixing`, the sole consumer,
  which consumes the sorried
  `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing`.

So: `BVBoundedBy` currently has **no closure lemmas at all**.  §2 gives it
some.

## 1.4 The one place the substrate is *stronger* than it looks

`Erdos1002.gaussTransfer` is normalised against the **Gauss** measure, not
Lebesgue:

```
gaussTransfer f y = ∑' n, gaussBranchRatio (n+1) y * f (gaussInverseBranch (n+1) y)
gaussBranchRatio q y = (1 + y) / ((q + y) * (q + y + 1))
```

This matters for the Lasota-Yorke constant.  In the *Lebesgue*
normalisation the branch Jacobian is `|h_q'(y)| = (q+y)^{-2}`, which equals
`1` at `q = 1, y = 0`; that is exactly why the textbook Gauss-map
Lasota-Yorke needs the **second** iterate.  In the `ν`-normalisation the
weight is `gaussBranchRatio q y`, whose supremum over `q ≥ 1`, `y ∈ [0,1]`
is attained at `q = 1, y = 0` and equals `1/2 < 1`.  So the `ν`-normalised
Gauss transfer operator contracts the variation at the **first** iterate.
See §3 for the resulting explicit constant.
-/

/-!
# 2. The missing BV algebra (proved)

None of §2 exists in Mathlib.  All four are needed by any Lasota-Yorke
argument: `eVariationOn_add_le` and `eVariationOn_tsum_le` to split the
branch sum, `eVariationOn_mul_le` to split the weight from the observable,
and `eVariationOn_le_of_gaussUnitLipschitzBound` to connect the substrate's
class to Kwon's.
-/

/-- **Subadditivity in the function.**  `Var(f + g) ≤ Var f + Var g`.
Not in Mathlib. -/
theorem eVariationOn_add_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  refine le_trans (Finset.sum_le_sum (fun i _ =>
    edist_add_add_le (f (u (i + 1))) (g (u (i + 1))) (f (u i)) (g (u i)))) ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

/-- **Homogeneity.**  `Var(c · f) ≤ |c| · Var f` (in fact `=`, but `≤` is
what is used and avoids the `ENNReal` zero/top case split).  Not in Mathlib. -/
theorem eVariationOn_const_mul_le (c : ℝ) (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => c * f x) s ≤ ENNReal.ofReal |c| * eVariationOn f s := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have key : ∀ i : ℕ, edist (c * f (u (i + 1))) (c * f (u i))
      = ENNReal.ofReal |c| * edist (f (u (i + 1))) (f (u i)) := by
    intro i
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      ← ENNReal.ofReal_mul (abs_nonneg c), ← abs_mul]
    congr 1
    ring_nf
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => key i))) ?_
  rw [← Finset.mul_sum]
  gcongr
  exact eVariationOn.sum_le f n hu us

/-- **The product rule.**  `Var(f g) ≤ ‖f‖_∞ Var g + ‖g‖_∞ Var f`.
Not in Mathlib.  This is the step that separates the branch weight
`gaussBranchRatio q` from the observable `f ∘ gaussInverseBranch q` in a
Lasota-Yorke estimate. -/
theorem eVariationOn_mul_le {f g : ℝ → ℝ} {s : Set ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ s, |f x| ≤ A) (hg : ∀ x ∈ s, |g x| ≤ B) :
    eVariationOn (fun x => f x * g x) s
      ≤ ENNReal.ofReal A * eVariationOn g s + ENNReal.ofReal B * eVariationOn f s := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have key : ∀ i : ℕ, edist (f (u (i + 1)) * g (u (i + 1))) (f (u i) * g (u i))
      ≤ ENNReal.ofReal A * edist (g (u (i + 1))) (g (u i))
        + ENNReal.ofReal B * edist (f (u (i + 1))) (f (u i)) := by
    intro i
    rw [edist_dist, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, Real.dist_eq,
      ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsplit : f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i)
        = f (u (i + 1)) * (g (u (i + 1)) - g (u i))
          + (f (u (i + 1)) - f (u i)) * g (u i) := by ring
    have e1 : |f (u (i + 1))| * |g (u (i + 1)) - g (u i)|
        ≤ A * |g (u (i + 1)) - g (u i)| :=
      mul_le_mul_of_nonneg_right (hf _ (us _)) (abs_nonneg _)
    have e2 : |f (u (i + 1)) - f (u i)| * |g (u i)|
        ≤ B * |f (u (i + 1)) - f (u i)| := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hg _ (us _)) (abs_nonneg _)
    have e0 : |f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i)|
        ≤ |f (u (i + 1))| * |g (u (i + 1)) - g (u i)|
          + |f (u (i + 1)) - f (u i)| * |g (u i)| := by
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
    linarith
  refine le_trans (Finset.sum_le_sum (fun i _ => key i)) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  gcongr
  · exact eVariationOn.sum_le g n hu us
  · exact eVariationOn.sum_le f n hu us

/-- **Lipschitz ⇒ BV, in the substrate's own class.**  Mathlib only offers
`LipschitzWith.locallyBoundedVariationOn` (qualitative, and about
`LipschitzWith`, not about `Erdos1002.GaussUnitLipschitzBound`); the
quantitative bound `Var ≤ K · |I|` is not there. -/
theorem eVariationOn_le_of_gaussUnitLipschitzBound {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (h : Erdos1002.GaussUnitLipschitzBound K f) :
    eVariationOn f (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have hmem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := fun i => Ioo_subset_Icc_self (us i)
  have key : ∀ i : ℕ, edist (f (u (i + 1))) (f (u i))
      ≤ ENNReal.ofReal (K * (u (i + 1) - u i)) := by
    intro i
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have habs : |u (i + 1) - u i| = u (i + 1) - u i := abs_of_nonneg (by linarith)
    have hlip := h (hmem (i + 1)) (hmem i)
    rw [habs] at hlip
    exact hlip
  refine le_trans (Finset.sum_le_sum (fun i _ => key i)) ?_
  have hnn : ∀ i ∈ Finset.range n, (0 : ℝ) ≤ K * (u (i + 1) - u i) := by
    intro i _
    exact mul_nonneg hK (by linarith [hu (Nat.le_succ i)])
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← Finset.mul_sum,
    Finset.sum_range_sub (fun i => u i)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 := (us 0).1
  have h1 := (us n).2
  calc K * (u n - u 0) ≤ K * 1 := mul_le_mul_of_nonneg_left (by linarith) hK
    _ = K := mul_one K

/-- **Lipschitz + bounded ⇒ `BVBoundedBy`.**  The containment is strict:
`Kwon1002.TransferIdentity.firstDigitIndicator_bv` together with
`Kwon1002.TransferIdentity.firstDigitIndicator_not_lipschitz` exhibits a
member of the right-hand class that is in no left-hand class. -/
theorem bvBoundedBy_of_gaussUnitLipschitzBound {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hA : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ A)
    (h : Erdos1002.GaussUnitLipschitzBound K f) :
    BVBoundedBy (max A K) f := by
  refine ⟨fun x hx => le_trans (hA x hx) (le_max_left _ _), ?_⟩
  refine le_trans (eVariationOn_le_of_gaussUnitLipschitzBound hK h) ?_
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- `BVBoundedBy` is closed under scaling, with the expected constant. -/
theorem bvBoundedBy_const_mul {K c : ℝ} {g : ℝ → ℝ} (hc : 0 ≤ c) (h : BVBoundedBy K g) :
    BVBoundedBy (c * K) (fun x => c * g x) := by
  obtain ⟨hsup, hvar⟩ := h
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hsup x hx) hc
  · refine le_trans (eVariationOn_const_mul_le c g _) ?_
    rw [abs_of_nonneg hc, ENNReal.ofReal_mul hc]
    gcongr

/-- The sup-variation comparison Mathlib *does* have, recorded in the form a
Lasota-Yorke proof uses it: on `s`, the sup norm is controlled by the value
at any single point plus the variation. -/
theorem abs_le_of_bvBoundedBy_at_point {g : ℝ → ℝ} {s : Set ℝ}
    (h : BoundedVariationOn g s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    |g x| ≤ |g y| + (eVariationOn g s).toReal := by
  have hd : dist (g x) (g y) ≤ (eVariationOn g s).toReal := h.dist_le hx hy
  rw [Real.dist_eq] at hd
  calc |g x| = |g y + (g x - g y)| := by ring_nf
    _ ≤ |g y| + |g x - g y| := abs_add_le _ _
    _ ≤ |g y| + (eVariationOn g s).toReal := by linarith

/-!
## 2.1 The two BV-algebra facts that are *not* proved here, and why

* **Countable subadditivity in the function**,
  `eVariationOn (fun x => ∑' n, F n x) s ≤ ∑' n, eVariationOn (F n) s`.
  `eVariationOn_add_le` gives the finite case by induction; the passage to
  `tsum` needs `eVariationOn.lowerSemicontinuous_aux` applied to the partial
  sums along `atTop`, *plus* pointwise summability of `fun n => F n x` at
  every `x ∈ s` (which for `gaussTransfer` is
  `Erdos1002.summable_gaussTransfer_branch_of_unit_bounds`, available only
  under `GaussUnitNonnegative` + `GaussUnitUpperBound`).  Stated below as
  `eVariationOn_tsum_le`.

* **Countable additivity in the domain**,
  `∑' q, eVariationOn f (Icc (1/(q+2)) (1/(q+1))) ≤ eVariationOn f (Ioo 0 1)`.
  `eVariationOn.sum'` gives every finite truncation (after reindexing, since
  `q ↦ 1/(q+1)` is *anti*tone and `sum'` wants `Monotone`); `ENNReal.tsum_eq_iSup_sum`
  finishes.  Stated below as `tsum_eVariationOn_branch_le`.

Both are pure Mathlib-level work with no manuscript content.  They are
listed as separate targets because they are exactly the two places a first
attempt will stall.
-/

/-- Countable subadditivity of the variation in the function.  See §2.1 for
the obstruction (lower semicontinuity along the partial sums). -/
theorem eVariationOn_tsum_le (F : ℕ → ℝ → ℝ) (s : Set ℝ)
    (hsum : ∀ x ∈ s, Summable fun n => F n x) :
    eVariationOn (fun x => ∑' n, F n x) s ≤ ∑' n, eVariationOn (F n) s := by
  sorry

/-- The Gauss branch intervals `I_q = [1/(q+2), 1/(q+1)]` (`q = 0` is
`[1/2, 1]`, i.e. first digit `1`) partition `(0,1]` up to endpoints. -/
def branchInterval (q : ℕ) : Set ℝ := Icc (1 / ((q : ℝ) + 2)) (1 / ((q : ℝ) + 1))

/-- Countable additivity of the variation in the domain, along the Gauss
branch partition.  See §2.1 for the obstruction (`eVariationOn.sum'` is
finite and wants a `Monotone` index sequence, so the reindexing is by hand). -/
theorem tsum_eVariationOn_branch_le (f : ℝ → ℝ) :
    ∑' q : ℕ, eVariationOn f (branchInterval q) ≤ eVariationOn f (Ioc (0 : ℝ) 1) := by
  sorry

/-!
# 3. The BV Lasota-Yorke inequality for the Gauss transfer operator

## 3.1 The computation the statements below encode

With `L = Erdos1002.gaussTransfer` (Gauss-measure normalisation),
`h_q y = gaussInverseBranch q y = 1/(q+y)` and
`ρ_q y = gaussBranchRatio q y = (1+y)/((q+y)(q+y+1))`,

  `L f (y) = ∑_{q ≥ 1} ρ_q(y) · f(h_q y)`.

Then, using §2:

  `Var_{(0,1)}(L f) ≤ ∑_q Var(ρ_q · (f ∘ h_q))`                     (`eVariationOn_tsum_le`)
  `                ≤ ∑_q [ ‖ρ_q‖_∞ Var(f ∘ h_q) + ‖f ∘ h_q‖_∞ Var(ρ_q) ]`
                                                                    (`eVariationOn_mul_le`)
  `Var_{[0,1]}(f ∘ h_q) = Var_{I_q}(f)`                              (`eVariationOn.comp_eq_of_antitoneOn`)
  `∑_q Var_{I_q}(f) ≤ Var_{(0,1]}(f)`                                (`tsum_eVariationOn_branch_le`)
  `‖f ∘ h_q‖_∞ = sup_{I_q}|f| ≤ Var_{I_q} f + inf_{I_q}|f|`          (`abs_le_of_bvBoundedBy_at_point`)
  `inf_{I_q}|f| ≤ ν(I_q)⁻¹ ∫_{I_q} |f| dν`.

The constants:
* `sup_{q ≥ 1, y ∈ [0,1]} ρ_q(y) = ρ_1(0) = 1/2`;
* `Var_{[0,1]}(ρ_1) = 1/2 - 1/3 = 1/6`, and `Var_{[0,1]}(ρ_q) ≤ 1/6` for `q ≥ 2`
  (indeed `≤ ρ_q(0) + ρ_q(1) ≤ 1/6 + 1/6`);
* hence the contraction coefficient is
  `max_q (‖ρ_q‖_∞ + Var ρ_q) = 1/2 + 1/6 = 2/3 < 1` at the **first** iterate;
* `sup_q Var(ρ_q) / ν(I_q) < ∞` because `Var(ρ_q) ≍ q^{-2}` and
  `ν(I_q) = log((q+1)²/(q(q+2)))/log 2 ≍ q^{-2}`; this is the `C` below.

The last bullet is the only genuinely quantitative input that has to be
computed rather than estimated crudely, and it is where a first attempt
should aim.

## 3.2 The leading constant, machine-checked

The first bullet of §3.1, the one that decides whether the *first* iterate
contracts, is proved outright here, and is sharp.
-/

/-- **The Lasota-Yorke leading constant.**  Every Gauss branch weight in the
`ν`-normalisation is at most `1/2` on the state interval.

This is the reason the `ν`-normalised Gauss transfer operator contracts the
variation at the **first** iterate, whereas the Lebesgue-normalised one does
not: there the weight is the Jacobian `(q+y)^{-2}`, which equals `1` at
`q = 1, y = 0`, and the textbook argument has to pass to `L²`. -/
theorem gaussBranchRatio_le_half {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Erdos1002.gaussBranchRatio q y ≤ 1 / 2 := by
  obtain ⟨hy0, hy1⟩ := hy
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < ((q : ℝ) + y) * ((q : ℝ) + y + 1) := by nlinarith
  rw [Erdos1002.gaussBranchRatio, div_le_iff₀ hden]
  nlinarith [sq_nonneg y, mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1) hy0]

/-- …and `1/2` is attained, at `q = 1, y = 0`, so the constant of
`gaussBranchRatio_le_half` cannot be improved. -/
theorem gaussBranchRatio_one_zero : Erdos1002.gaussBranchRatio 1 0 = 1 / 2 := by
  rw [Erdos1002.gaussBranchRatio]
  norm_num

/-!
## 3.3 Statements

`gaussTransfer_bv_lasota_yorke` is the interface that everything downstream
consumes; `gaussTransfer_bv_lasota_yorke_two_thirds` is the explicit form
§3.1 computes.  The explicit form is stated separately, and deliberately
*not* used to prove the existential one, because only its leading constant
(`gaussBranchRatio_le_half`) is machine-checked: if the `1/6` coming from
`sup_q Var(gaussBranchRatio q)` turns out to be off, only the explicit
statement is affected.
-/

/-- **BV Lasota-Yorke for the Gauss transfer operator** (the interface form).

`Var(L f) ≤ ρ · Var(f) + C · ‖f‖_{L¹(ν)}` with `ρ < 1`.

This is the single missing ingredient named in the task.  It is in neither
Mathlib, nor Wang's substrate, nor Kwon's manuscript.

The hypotheses are the minimum under which `Erdos1002.gaussTransfer f` is
even known to be a well-defined pointwise sum: the substrate's summability
lemma `Erdos1002.summable_gaussTransfer_branch_of_unit_bounds` needs
`GaussUnitNonnegative` and `GaussUnitUpperBound`.  For a general BV `f` one
first splits `f = f⁺ - f⁻` (or adds the constant `K`, using
`Erdos1002.gaussTransfer_one`); the nonnegative case stated here is the
substantive one. -/
theorem gaussTransfer_bv_lasota_yorke :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < C ∧
      ∀ (A : ℝ) (f : ℝ → ℝ), Measurable f →
        Erdos1002.GaussUnitNonnegative f → Erdos1002.GaussUnitUpperBound A f →
        BoundedVariationOn f (Ioo (0 : ℝ) 1) →
        eVariationOn (Erdos1002.gaussTransfer f) (Ioo (0 : ℝ) 1)
          ≤ ENNReal.ofReal ρ * eVariationOn f (Ioo (0 : ℝ) 1)
            + ENNReal.ofReal (C * ∫ x, |f x| ∂Erdos1002.gaussMeasure) := by
  sorry

/-- The explicit constant §3.1 computes: `ρ = 2/3`, at the **first** iterate.
(The Lebesgue-normalised Gauss transfer operator would need the second
iterate; the `ν`-normalisation removes that, see §1.4.) -/
theorem gaussTransfer_bv_lasota_yorke_two_thirds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℝ) (f : ℝ → ℝ), Measurable f →
        Erdos1002.GaussUnitNonnegative f → Erdos1002.GaussUnitUpperBound A f →
        BoundedVariationOn f (Ioo (0 : ℝ) 1) →
        eVariationOn (Erdos1002.gaussTransfer f) (Ioo (0 : ℝ) 1)
          ≤ ENNReal.ofReal (2 / 3) * eVariationOn f (Ioo (0 : ℝ) 1)
            + ENNReal.ofReal (C * ∫ x, |f x| ∂Erdos1002.gaussMeasure) := by
  sorry

/-- The iterated form, which is what a spectral-gap argument consumes.
Note the shape: `ρ^n` multiplies the variation, but the `L¹` term does
**not** decay, it is summed geometrically, so the constant is `C/(1-ρ)`.
This follows from `gaussTransfer_bv_lasota_yorke` by induction, using that
`L` is an `L¹(ν)` contraction (`Erdos1002` proves
`∫ (gaussTransfer f) dν = ∫ f dν` for the classes above; the `|·|` version
needs `|L f| ≤ L |f|`, which is immediate from the definition since
`gaussBranchRatio q ≥ 0` on `[0,1]`). -/
theorem gaussTransfer_iterate_bv_lasota_yorke :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < C ∧
      ∀ (n : ℕ) (A : ℝ) (f : ℝ → ℝ), Measurable f →
        Erdos1002.GaussUnitNonnegative f → Erdos1002.GaussUnitUpperBound A f →
        BoundedVariationOn f (Ioo (0 : ℝ) 1) →
        eVariationOn ((Erdos1002.gaussTransfer^[n]) f) (Ioo (0 : ℝ) 1)
          ≤ ENNReal.ofReal (ρ ^ n) * eVariationOn f (Ioo (0 : ℝ) 1)
            + ENNReal.ofReal (C * ∫ x, |f x| ∂Erdos1002.gaussMeasure) := by
  sorry

/-- **Lemma 3.1(i) of the manuscript, in Kwon's own `BV` class.**

Compare `Kwon1002.Transfer.lemma_3_1_i`, which is the same display with the
three substrate hypotheses `GaussUnitNonnegative` + `GaussUnitUpperBound A`
+ `GaussUnitLipschitzBound K` in place of `BVBoundedBy K`.  This is what
Kwon actually states, and it is the direct consequence of
`gaussTransfer_iterate_bv_lasota_yorke` plus a Hennion/Ionescu-Tulcea-Marinescu
(or, for this operator, a direct Doeblin) argument.

Deriving this from the Lasota-Yorke inequality is a *second*, independent
piece of work: LY alone gives quasi-compactness of `L` on `BV`, and one then
needs that `1` is a simple isolated eigenvalue with eigenfunction `1`, for
`gaussTransfer` the latter is `Erdos1002.gaussTransfer_one` plus ergodicity. -/
theorem lemma_3_1_i_bv :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ {K : ℝ} {f : ℝ → ℝ}, 0 ≤ K → Measurable f → BVBoundedBy K f → ∀ r : ℕ,
        (∫ y, |(Erdos1002.gaussTransfer^[r]) f y - ∫ x, f x ∂Erdos1002.gaussMeasure|
            ∂Erdos1002.gaussMeasure) ≤ C * ρ ^ r * K := by
  sorry

/-!
# 4. The target: Lemma 3.2 in `BV`

Reproduced **token-identically** from
`Kwon1002/Prop41.lean`, lines 265-283 (`theorem
lem_3_2_conditional_multiblock_mixing`); only the name carries a prime.
I diffed the two statement blocks character-for-character.  Nothing is
weakened: same `s`, same `BVBoundedBy K`, same start/gap conditions, same
`C * ρ ^ M * K ^ s`.
-/

/-- Machine check that the three identifiers occurring in the reproduction
below really are the target's, not local look-alikes. -/
example : @BVBoundedBy = @Kwon1002.Prop41.BVBoundedBy := rfl

-- `cylinder` is ambiguous as a bare identifier (`MeasureTheory.cylinder` is
-- also in scope, exactly as in `Kwon1002/Prop41.lean`, which also opens
-- `MeasureTheory`); applied to `(d : ℕ) (w : ℕ → ℕ)` both files resolve it
-- the same way.
example (d : ℕ) (w : ℕ → ℕ) : cylinder d w = Kwon1002.Prop41.cylinder d w := rfl

example : @gaussIter = @Kwon1002.gaussIter := rfl

theorem lem_3_2_conditional_multiblock_mixing' (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : ℕ → ℕ) (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → BVBoundedBy K (g i)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        0 < (Erdos1002.gaussMeasure (cylinder d w)).toReal →
        |(∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
              ∂Erdos1002.gaussMeasure) / (Erdos1002.gaussMeasure (cylinder d w)).toReal
            - ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ M * K ^ s := by
  sorry

/-!
# 5. A cheaper route that **bypasses** the Lasota-Yorke inequality

This is the main strategic finding of this scout.

Lemma 3.2 quantifies `ρ` **existentially** (`∃ C ρ, … ρ < 1 …`).  That slack
is enough to trade the BV theory for a Lipschitz approximation, because the
conditional density of a cylinder is *uniformly bounded*, Kwon's
`sup_w ‖ρ_w‖_∞ < ∞` is already proved in-tree as the explicit constant `8`
(`Kwon1002.Transfer.kwonDensity_le`).  So an `L¹` perturbation of the
observables is controlled *uniformly over cylinders*, which is exactly the
uniformity §4 needs.

The four steps:

* **B1 (mollification).**  `g ∈ BV(0,1)` with `‖g‖_∞ ≤ K`, `Var g ≤ K`.  Put
  `g_ε(x) = ε⁻¹ ∫_x^{x+ε} g`.  Then `‖g_ε‖_∞ ≤ K`,
  `Lip(g_ε) ≤ 2K/ε`, and `‖g - g_ε‖_{L¹(ν)} ≤ 2 ε K`
  (Lebesgue gives `ε · Var g`; `dν/dx = ((1+x) log 2)⁻¹ ≤ (log 2)⁻¹ < 2`).
* **B2 (conditional `L¹` stability, constant `8`).**  Provable *now* from
  `Kwon1002.TransferIdentity.exists_cylinder_condDensity'` (axiom-clean) and
  `Kwon1002.Transfer.kwonDensity_le`.  Proved below.
* **B3 (Lipschitz mixing).**  `Kwon1002.TransferIdentity.lemma_3_2'` -
  already proved, axiom-clean, uniform in the cylinder, rate `527/540`.
* **B4 (optimise `ε`).**  With `ρ₀ = 527/540`, B3 applied to the `g_ε`'s
  costs `s · ρ₀^M · (2K/ε) · (2K)^s` and B1+B2 cost `O_s(ε K^{s})`.  Taking
  `ε = ρ₀^{M/2}` gives the total `C_s K^{s+1} (√ρ₀)^M`, and the extra power
  of `K` is removed by homogeneity (apply the result to `g_i / K`; the
  left-hand side of Lemma 3.2 is `s`-multilinear in `(g_1,…,g_s)`).  So
  Lemma 3.2 holds with `ρ = √(527/540)`.

Two bookkeeping wrinkles, both standard and both recorded as hypotheses
below: `conditional_multiblock_mixing` requires the observables to be
**nonnegative**, so one first replaces `g_i` by `g_i + K ≥ 0` and expands
the product into `2^s` terms (absorbed into `C_s`); and the target is
`ν`-conditioned on `Prop41.cylinder d w` while `lemma_3_2'` is conditioned
on `Erdos1002.gaussHalfOpenPrefixCylinder w`, which differ at the countably
many rational endpoints (a `ν`-null set).

**Consequence for the programme.**  The BV Lasota-Yorke inequality of §3 is
*not* on the critical path for §4.  It is on the critical path only if one
wants Lemma 3.1(i) in BV with the sharp rate, or the sup-norm form.  §4 and
§5 can be unblocked through §5's route using only what is already
axiom-clean in-tree.
-/

/-- **B1**: quantitative Lipschitz approximation of a `BV` observable in
`L¹(ν)`.  The Lipschitz constant blows up like `1/ε` and the `L¹` error is
linear in `ε`; that trade is what B4 optimises.

Obstruction: Mathlib has no "mollification of a BV function" API.  What is
needed is `‖g(· + ε) - g‖_{L¹} ≤ ε · Var(g)` for `g ∈ BV`, which follows
from the Jordan decomposition `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`
(already in Mathlib) plus the monotone case, for which
`MonotoneOn.eVariationOn_le` gives the telescoping bound. -/
theorem exists_lipschitz_L1_approx (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε)
    (g : ℝ → ℝ) (hg : BVBoundedBy K g) :
    ∃ gε : ℝ → ℝ, Measurable gε ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, |gε x| ≤ K) ∧
      Erdos1002.GaussUnitLipschitzBound (2 * K / ε) gε ∧
      (∫ x, |g x - gε x| ∂Erdos1002.gaussMeasure) ≤ 2 * ε * K := by
  sorry

/-- **B2**: conditioning on a cylinder is `L¹(ν)`-stable with the explicit
constant `8`, **uniformly in the cylinder**.  This is the step that makes
the whole bypass work, and it is proved outright from
`Kwon1002.TransferIdentity.exists_cylinder_condDensity'` (axiom-clean) and
`Kwon1002.Transfer.kwonDensity_le`. -/
theorem condMean_comp_orbit_abs_le (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal)
    (F : ℝ → ℝ) (hF : Measurable F) (hFint : Integrable F Erdos1002.gaussMeasure) :
    |Kwon1002.Transfer.condMean (Erdos1002.gaussHalfOpenPrefixCylinder w)
        (fun α => F (Erdos1002.gaussOrbit w.length α))|
      ≤ 8 * ∫ x, |F x| ∂Erdos1002.gaussMeasure := by
  obtain ⟨a, b, ha, hb, hrep⟩ :=
    Kwon1002.TransferIdentity.exists_cylinder_condDensity' w hw hpos
  rw [hrep F hF]
  have hφ0 : ∀ᵐ y ∂Erdos1002.gaussMeasure, 0 ≤ Kwon1002.Transfer.kwonDensity a b y := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    exact Kwon1002.Transfer.kwonDensity_nonneg ha hb ⟨hy.1.le, hy.2⟩
  have hφ8 : ∀ᵐ y ∂Erdos1002.gaussMeasure, Kwon1002.Transfer.kwonDensity a b y ≤ 8 := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    exact Kwon1002.Transfer.kwonDensity_le ha hb ⟨hy.1.le, hy.2⟩
  have hmul : Integrable
      (fun y => Kwon1002.Transfer.kwonDensity a b y * F y) Erdos1002.gaussMeasure := by
    refine Integrable.bdd_mul (c := 8) hFint
      (Kwon1002.Transfer.measurable_kwonDensity a b).aestronglyMeasurable ?_
    filter_upwards [hφ0, hφ8] with y h0 h8
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h8
  calc |∫ y, Kwon1002.Transfer.kwonDensity a b y * F y ∂Erdos1002.gaussMeasure|
      ≤ ∫ y, |Kwon1002.Transfer.kwonDensity a b y * F y| ∂Erdos1002.gaussMeasure :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, 8 * |F y| ∂Erdos1002.gaussMeasure := by
        refine integral_mono_ae hmul.abs (hFint.abs.const_mul 8) ?_
        filter_upwards [hφ0, hφ8] with y h0 h8
        rw [abs_mul, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_right h8 (abs_nonneg _)
    _ = 8 * ∫ y, |F y| ∂Erdos1002.gaussMeasure := integral_const_mul _ _

/-- **B4**, packaged: Lemma 3.2 in `BV` *follows from* the Lipschitz Lemma
3.2 already proved in-tree, given only B1.  Stated as the reduction, so
that a future session can discharge B1 alone and be done.

The conclusion is `lem_3_2_conditional_multiblock_mixing'` verbatim. -/
theorem lem_3_2_bv_of_lipschitz_approx
    (happrox : ∀ (K ε : ℝ), 0 ≤ K → 0 < ε → ∀ g : ℝ → ℝ, BVBoundedBy K g →
      ∃ gε : ℝ → ℝ, Measurable gε ∧
        (∀ x ∈ Ioo (0 : ℝ) 1, |gε x| ≤ K) ∧
        Erdos1002.GaussUnitLipschitzBound (2 * K / ε) gε ∧
        (∫ x, |g x - gε x| ∂Erdos1002.gaussMeasure) ≤ 2 * ε * K)
    (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : ℕ → ℕ) (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → BVBoundedBy K (g i)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        0 < (Erdos1002.gaussMeasure (cylinder d w)).toReal →
        |(∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
              ∂Erdos1002.gaussMeasure) / (Erdos1002.gaussMeasure (cylinder d w)).toReal
            - ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ M * K ^ s := by
  sorry

/-!
# 6. Summary of what a prover should pick up next

Ordered by (value / difficulty):

1. **B2 is done** (above, no sorry).  **B1** is the only genuinely missing
   ingredient of the bypass, and it is ordinary real analysis with no
   dynamics in it: mollify, use the Jordan decomposition, telescope.
   Discharging B1 + the bookkeeping of `lem_3_2_bv_of_lipschitz_approx`
   closes `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing` and hence
   unblocks `Kwon1002.ErrorShape.good_tuple_multiblock_mixing`.
2. **`eVariationOn_tsum_le`** and **`tsum_eVariationOn_branch_le`** (§2.1) -
   pure Mathlib gap-filling, reusable, and prerequisites for §3.
3. **`gaussTransfer_bv_lasota_yorke`**, the named bottleneck.  With §2 and
   item 2 in hand the proof is the six-line chain of §3.1.  Its leading
   constant is already machine-checked and sharp
   (`gaussBranchRatio_le_half`, `gaussBranchRatio_one_zero`), so the only
   arithmetic left is `sup_q Var(gaussBranchRatio q) / ν(I_q) < ∞`.
4. **`lemma_3_1_i_bv`**, needs 3 *plus* a quasi-compactness argument that
   does not exist anywhere in Mathlib.  This is the expensive one, and §5
   shows §4 does not need it.

## Statements consumed

This file consumes no sorried result in any shared module.  Ten results are
proved outright, all with axioms exactly `[propext, Classical.choice,
Quot.sound]`: `eVariationOn_add_le`, `eVariationOn_const_mul_le`,
`eVariationOn_mul_le`, `eVariationOn_le_of_gaussUnitLipschitzBound`,
`bvBoundedBy_of_gaussUnitLipschitzBound`, `bvBoundedBy_const_mul`,
`abs_le_of_bvBoundedBy_at_point`, `gaussBranchRatio_le_half`,
`gaussBranchRatio_one_zero`, `condMean_comp_orbit_abs_le`.
`condMean_comp_orbit_abs_le`
is proved from `Kwon1002.TransferIdentity.exists_cylinder_condDensity'`,
`Kwon1002.Transfer.kwonDensity_nonneg`, `Kwon1002.Transfer.kwonDensity_le`,
`Kwon1002.Transfer.measurable_kwonDensity` and
`Erdos1002.gaussMeasure_unit_ae`, all of which are sorry-free.
-/

end

end Kwon1002.BVScout
