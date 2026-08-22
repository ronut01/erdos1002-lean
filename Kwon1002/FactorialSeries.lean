import Kwon1002.FactorialRoute

/-!
# The layer decomposition and the series assembly of the factorial route

`Kwon1002/FactorialRoute.lean` builds pieces 1 and 2 of the route to
`CorFinal.largeSum_charFun_limit`: the powerset expansion

  `exp(i t · largeSum) = ∑_{S ⊆ {0,…,n}} ∏_{j ∈ S} h_j`

and the domination `‖∏_{j∈S} h_j‖ ≤ 2^{|S|}·1_{tuple event}`, and records that
what remains is "exactly one analytic input, the layer limit".  That sentence
was a claim about the route, not a theorem.  **This module makes it a theorem.**

`largeSum_charFun_limit_of_layer_limit` below proves
`CorFinal.largeSum_charFun_limit` — conclusion reproduced token for token, and
checked inside Lean by the anonymous `example` at the foot of this file against
`@Kwon1002.CorFinal.largeSum_charFun_limit` — from the layer limits

  `∑_{|S| = k} ∫_{(0,1)} ∏_{j∈S} h_j dα  →  Λ̂^k / k!`,   `Λ̂ = ∫_{|x|>ε}(e^{itx}−1)dΛ`,

**and from nothing else**.  Everything structural on the factorial route is
therefore now proved: the expansion, the domination, the regrouping by
cardinality, the deterministic level cap, the `k`-uniform tuple bound, and the
interchange of the `k`-series with `n → ∞`.

Nothing here is a `sorry` and nothing here consumes one.

## What this module adds

* `integral_exp_largeSum_eq_sum_layers` — the expansion regrouped by
  cardinality, `∫ exp(i t · largeSum) = ∑_{k ≤ n+1} layerSum k`.  The
  finite-sum/integral interchange needs `integrableOn_prod_jumpFactor`, which
  the `FactorialRoute` proofs had only inline.
* `exists_tupleBigEvent_bound` — the **`k`-uniform** tuple bound.
* `lameCap`, `layerSum_eq_capped` — the deterministic Lamé cap in `ℕ`, turning
  the layer into a sum over `C(O(L), k)` subsets.
* `norm_layerSum_le` — `‖layerSum k‖ ≤ (8C)^k/k!`, a base independent of both
  `k` and `n`.
* `largeSum_charFun_limit_of_layer_limits` — the series interchange, by
  dominated convergence for `tsum` against `∑_k (8C)^k/k! = e^{8C}`.
* `layerSum_zero` — a non-vacuity check: the `k = 0` layer really is `1`, which
  is `Λ̂^0/0!`.  This also pins the shape of the target: the sum runs over
  *subsets*, so the `1/k!` is carried by the binomial coefficient and no
  embedding count is needed.

## Three records corrected

**(A) Residual (35b) and `LevyExponent.tuple_measure_convergence` are not on
the chain to Corollary 5.3 — machine-checked, not inferred.**  A transitive
constant-closure scan of `Kwon1002.CorFinal.principal_cauchy_law_F` finds
exactly two constants in its closure whose own value carries a `sorry`:
`CorFinal.largeSum_charFun_limit` and `CorFinal.bulk_offdiagonal_abs_far_sharp`.
It does **not** reach
`TupleInputs.oneLevel_gaussKuzmin_intensity_to_measurable` (residual 35b),
`LevyExponent.tuple_measure_convergence`, `TupleFinal.tuple_measure_convergence`,
`TupleFinal.goodSet_mark_factorization_intervals`,
`TupleFinal.bulk_window_bridge_tuple` or
`FiveFinal.deterministic_oneLevel_intensity`.  The same scan on
`Master.erdos1002Conclusion_of_section7` adds only
`prop_6_4_bounded_remainder_weak_law`.  `Master.PrincipalCauchyLaw` does not
quantify over a set `B` at all — it is a statement about the distribution
functions of `bulkSum c α n − b n` — so the set-quantified machinery is internal
to routes the assembly does not take.  Closing (35b) would close a true
statement that Corollary 5.3 does not use.

**(B) The layer limit needs a per-level (multi-set) statement, which
`LevyExponent.tuple_measure_convergence` does not supply.**  `FactorialRoute`'s
header says the passage from indicators to the symbol
`x ↦ (e^{itx}−1)1{|x|>ε}` needs "the limit uniformly over a simple-function
approximation".  That understates the gap.  A simple-function approximation
`φ ≈ ∑_m c_m 1_{B_m}` turns `∏_{j∈S} φ(X_j)` into a sum over multi-indices of
tuple events carrying a *different* set at each level,
`1_{B_{m(j_1)}}(X_{j_1})···1_{B_{m(j_k)}}(X_{j_k})`.
`LevyExponent.tuple_measure_convergence` is
`Erdos1002.tupleEvent (bulkMarkEvent c n B) f = ⋂_i bulkMarkEvent c n B (f i)` —
one and the same `B` at every level.  It therefore does not supply the diagonal
of the needed family, let alone the family.

**(B′) Correction to (B): the tree *does* contain the per-level statement, at
Proposition 4.1.**  The sentence "a statement the tree does not contain in any
form" was wrong, and `Kwon1002/MultiLevel.lean` corrects it.
`Kwon1002.prop_4_1_marked_factorization` quantifies over
`F : ℕ → ℕ → ℝ → ℂ` with `∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)`: the symbol
family is indexed by the level slot, so a different symbol at each level is
already what display (27) says, and the diagonal `F ℓ = G` is the special case.
`MultiLevel.multiLevel_transfer` spends this: for every `r`, every interval
count `m` and every rate `A`, uniformly over good tuples of `J_n` and over
**per-level** section families,

  `|∫₀¹ ∏_{ℓ<r} 1_{B_ℓ}(a_{j_ℓ+1}, θ_{j_ℓ}) − ∏_{ℓ<r} stationaryMeanR 1_{B_ℓ}|
      ≤ C·L^{−A}`,

axiom-clean.  What (B) got right is narrower and still stands: the multi-set
*limit* is not in the tree, and it is not obtained by widening a symbol class.
`multiLevel_transfer` is its *factorization* half only.

**(B″) The factorization half now reaches the mark event, and with it the whole
of §5's tuple chain on the interval class.**
`Kwon1002/TupleTransfer.lean` proves `multiSet_mark_factorization` — the
per-level form of `TupleFinal.goodSet_mark_factorization_intervals`, uniformly
over every family of interval targets — from `multiLevel_transfer`, and with it
`det_quasi_independence_intervals`, `det_tuple_measure_convergence_intervals`,
`oneLevel_intensity_limit_intervals`, `tuple_measure_convergence_intervals` and
`tuple_quasi_independence_intervals`, all axiom-clean.  So the sentence in (A)
that the closure scan does not *reach* residual 2a still describes the scan
correctly, but it should not be read as saying residual 2a is not needed: a
`sorry` absorbs its dependencies, and any genuine route to the layer limit
brings it back on route.  The interval hypothesis is not a restriction here —
`IntervalClass.isUnionOfIntervals_truncation` puts every instantiation the §5
chain makes inside the class.

**(C) `TupleMeasure.tuple_measure_le` cannot dominate a series as stated.**  It
reads `∀ k, ∃ C, ∀ᶠ n, …`, so both the constant and the eventual-`n` threshold
may depend on `k`, and a bound of that shape is useless against a sum over `k`.
Its proof in fact produces a `C` (`C₀/(8ε)`, with `C₀ = 24` from
`digit_tail_product`) and a threshold (`8εL ≥ 1`, `L > 0`) that are both
`k`-independent.  `exists_tupleBigEvent_bound` records that quantifier order,
and it is the version the assembly consumes.

## What remains on this route

The layer limit `hlim`, and nothing else.  Its input is the multi-set tuple
limit of §4, whose *factorization* half is now proved
(`MultiLevel.multiLevel_transfer`, see (B′)).  Four named things separate that
from the layer limit itself, and none of them is closed:

1. the per-level intensity for the **complex** symbol
   `x ↦ (e^{itx} − 1)1{|x| > ε}` rather than an indicator — a simple-function
   approximation inside a truncation window `(ε, R]`, plus the `R → ∞` tail.
   The simple-function half is now proved:
   `SymbolIntensity.sum_levelSymbol_step_tendsto` gives the one-level limit at
   every step symbol from the interval class, and
   `SymbolIntensity.mu_eq_levelSymbol` checks that `LayerAssembly.mu` is the
   same currency.  What remains is the two metric estimates, neither of which
   needs §4 again;
2. ~~`Kwon1002.nonGood_tuple_count`~~ — **this item was wrong.**  The count is
   proved and axiom-clean as `Kwon1002.TupleCount.nonGood_tuple_count`, restated
   verbatim and cited as `Kwon1002.nonGood_tuple_count'` in
   `Kwon1002/Discharge.lean`.  Only the below-declaration copy
   `Kwon1002.Section4.nonGood_tuple_count` still carries a `sorry`, for the
   import-direction reason that module documents.  Checked by an `example` at
   the foot of `Kwon1002/LayerAssembly.lean`;
3. ~~the `k`-level index-set bridge~~ — **this item was wrong too.**  The bridge
   between the random bulk `Marks.bulkIndices c α n` and the deterministic
   `bulkJ n` is `Kwon1002.TupleFinal.bulk_window_bridge_tuple`, proved and
   axiom-clean at every `k`; the sentence above was written while its proof was
   still open.  Also checked by an `example` in `Kwon1002/LayerAssembly.lean`.
   What it supplies is the bridge for **one** set `B` at every level, so a
   per-level (multi-set) bridge is still owed, and that is part of item 1;
4. the passage from `∑_{|S| = k} ∏_{j ∈ S} (per-level mean)` to `Λ̂^k/k!` —
   **closed** in `Kwon1002/LayerAssembly.lean`
   (`LayerAssembly.tendsto_esymm`, `LayerAssembly.layerSum_tendsto_of_inputs`,
   both axiom-clean).  The anticipated even/odd split is not needed: the
   recursion used carries no alternating sign.  That module also *proves*, and
   does not assume, the two size conditions the argument needs
   (`sum_norm_mu_le`, `sum_norm_mu_sq_le`), so what is left of the layer limit
   is exactly the two analytic inputs `hp1` and `hqi` of
   `layerSum_tendsto_of_inputs`, both about the complex symbol.

None of these is a residual of `TupleInputs`, `Section5Intervals` or
`Section5Join`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace FactorialRoute

noncomputable section

open Assembly5

/-! ## The layer decomposition -/

/-- The `|S| = k` layer of the powerset expansion. -/
def layerSum (t c ε : ℝ) (n k : ℕ) : ℂ :=
  ∑ S ∈ Finset.powersetCard k (Finset.range (n + 1)),
    ∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α

/-- Each term of the expansion is integrable on `(0,1)`: it is measurable and
bounded by `2^{|S|}`. -/
theorem integrableOn_prod_jumpFactor (t c ε : ℝ) (n : ℕ) (S : Finset ℕ) :
    IntegrableOn (fun α : ℝ => ∏ j ∈ S, jumpFactor t c ε n j α) (Ioo (0:ℝ) 1) := by
  classical
  have hmeas : Measurable fun α : ℝ => ∏ j ∈ S, jumpFactor t c ε n j α :=
    Finset.measurable_prod _ fun j _ => measurable_jumpFactor t c ε n j
  refine Measure.integrableOn_of_bounded (M := 2 ^ S.card) (by simp [Real.volume_Ioo])
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun α => ?_)
  refine le_trans (norm_prod_jumpFactor_le t c ε n S α) ?_
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- **The layer decomposition.**  The characteristic-function integral of the
large-jump sum is the sum of its `n + 2` layers. -/
theorem integral_exp_largeSum_eq_sum_layers {c ε : ℝ} (hε : 0 < ε) (t : ℝ) (n : ℕ) :
    (∫ α in Ioo (0:ℝ) 1, Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I))
      = ∑ k ∈ Finset.range (n + 2), layerSum t c ε n k := by
  classical
  have hae : (fun α : ℝ => Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I))
      =ᵐ[volume.restrict (Ioo (0:ℝ) 1)]
        fun α : ℝ => ∑ S ∈ (Finset.range (n + 1)).powerset,
          ∏ j ∈ S, jumpFactor t c ε n j α := by
    refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
    filter_upwards [LevyExponent.ae_irrational] with α hα hmem
    exact exp_largeSum_powerset_expansion hε t hmem hα n
  rw [integral_congr_ae hae,
    integral_finset_sum _ (fun S _ => integrableOn_prod_jumpFactor t c ε n S),
    Finset.sum_powerset]
  simp only [Finset.card_range, layerSum]

/-! ## The `k`-uniform tuple bound

`TupleMeasure.tuple_measure_le` states the per-tuple `(C/L)^k` bound with the
constant `C` and the eventual-`n` threshold *inside* the `k`-scope, so it does
not by itself dominate a series in `k`.  Its proof, however, produces a `C`
(namely `C₀/(8ε)` from `digit_tail_product`) and a threshold (`8εL ≥ 1` and
`L > 0`) that are both independent of `k`.  The version below records that:
one `C`, one threshold, and the bound holding simultaneously for **every**
finite level set `S`. -/

/-- **The `k`-uniform tuple bound.**  There is one constant `C` and one
eventual-`n` threshold for which every finite level set `S` satisfies
`P(⋂_{j∈S} bigEvent_j) ≤ (C/L)^{|S|}` — the quantifier order that a series in
`|S|` needs, and which `TupleMeasure.tuple_measure_le` does not supply. -/
theorem exists_tupleBigEvent_bound (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
      unifIoo.real (tupleBigEvent c ε n S) ≤ (C / Lnorm n) ^ S.card := by
  classical
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * ε), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * ε * Lnorm n := by
    have h : Tendsto (fun n : ℕ => 8 * ε * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) TupleMeasure.tendsto_Lnorm_atTop
    exact h.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0
  have hB0 : ∀ x ∈ PoissonRoute.truncSet ε, ε ≤ |x| := fun _ hx => le_of_lt hx
  filter_upwards [h1, h2] with n hn1 hn2 S
  set k : ℕ := S.card with hk
  set js : Fin k → ℕ := fun i => S.orderEmbOfFin hk.symm i with hjs
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin k, (fun _ : Fin k => 8 * ε * Lnorm n) i ≤ (digit α (js i) : ℝ)} with hbig
  have hinj : Function.Injective js := (S.orderEmbOfFin hk.symm).injective
  have hbound : (volume big).toReal ≤ C₀ ^ k * ∏ _i : Fin k, (8 * ε * Lnorm n)⁻¹ :=
    hC k js (fun _ => 8 * ε * Lnorm n) hinj (fun _ => hn1)
  have hsub : tupleBigEvent c ε n S ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    refine ⟨hαI, fun i => ?_⟩
    have hmem : α ∈ bigEvent c ε n (js i) :=
      Set.mem_iInter₂.mp hα (js i) (S.orderEmbOfFin_mem hk.symm i)
    exact TupleMeasure.digit_ge_of_mem_bulkMarkEvent c (PoissonRoute.truncSet ε) hB0 hn2 hmem
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (tupleBigEvent c ε n S) ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound (le_of_eq ?_))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, div_div,
    ← div_eq_mul_inv]

/-! ## The deterministic Lamé cap, in `ℕ` -/

/-- The deterministic level cap: `L2Estimate.stoppingTime_le_log` puts every
bulk level of every irrational `α ∈ (0,1)` strictly below this. -/
def lameCap (n : ℕ) : ℕ := ⌊2 * Lnorm n / Real.log 2⌋₊ + 3

lemma lameCap_lt {n j : ℕ} (hj : lameCap n ≤ j) :
    2 * Lnorm n / Real.log 2 + 2 < (j : ℝ) := by
  have h := Nat.lt_floor_add_one (2 * Lnorm n / Real.log 2)
  have hcast : ((lameCap n : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  simp only [lameCap, Nat.cast_add, Nat.cast_ofNat] at hcast
  linarith

/-- `lameCap n ≤ 4L` once `L ≥ 3`, since `2/log 2 < 3`. -/
lemma lameCap_le {n : ℕ} (hL : 3 ≤ Lnorm n) : (lameCap n : ℝ) ≤ 4 * Lnorm n := by
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  have hlog : (0 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h2 : (2 : ℝ) ≤ 3 * Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hdiv : 2 * Lnorm n / Real.log 2 ≤ 3 * Lnorm n := by
    rw [div_le_iff₀ hlog]
    nlinarith
  have hfl : (⌊2 * Lnorm n / Real.log 2⌋₊ : ℝ) ≤ 2 * Lnorm n / Real.log 2 :=
    Nat.floor_le (by positivity)
  simp only [lameCap, Nat.cast_add, Nat.cast_ofNat]
  linarith

/-- A level set containing a level at or above the cap contributes nothing. -/
lemma integral_prod_jumpFactor_eq_zero_of_lameCap (t c ε : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (S : Finset ℕ) {j : ℕ} (hjS : j ∈ S) (hj : lameCap n ≤ j) :
    (∫ α in Ioo (0:ℝ) 1, ∏ i ∈ S, jumpFactor t c ε n i α) = 0 :=
  norm_eq_zero.mp
    (integral_prod_jumpFactor_eq_zero_of_large t c ε n hn S hjS (lameCap_lt hj))

/-- **The layer runs over `O(L)` levels, not over `{0,…,n}`.**  This is where
the deterministic cap replaces an exceptional set, and it is what makes the
layer bound summable in `k`. -/
theorem layerSum_eq_capped (t c ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    layerSum t c ε n k
      = ∑ S ∈ Finset.powersetCard k (Finset.range (min (n + 1) (lameCap n))),
          ∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨hS.1.trans (fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (min_le_left _ _))), hS.2⟩
  · intro S hS hSnot
    rw [Finset.mem_powersetCard] at hS
    have hnsub : ¬ S ⊆ Finset.range (min (n + 1) (lameCap n)) := by
      intro hsub
      exact hSnot (Finset.mem_powersetCard.mpr ⟨hsub, hS.2⟩)
    obtain ⟨j, hjS, hj⟩ := Finset.not_subset.mp hnsub
    have hjn : j < n + 1 := Finset.mem_range.mp (hS.1 hjS)
    have hjc : lameCap n ≤ j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    exact integral_prod_jumpFactor_eq_zero_of_lameCap t c ε hn S hjS hjc

/-! ## The layer bound -/

/-- **The layer bound.**  With the `k`-uniform tuple bound and the Lamé cap in
hand, the `|S| = k` layer is at most `(8C)^k / k!` — the summable-in-`k`
domination the series assembly needs, with a base independent of both `k`
and `n`. -/
theorem norm_layerSum_le (t c : ℝ) {ε C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n)
    (hL : 3 ≤ Lnorm n)
    (hbnd : ∀ S : Finset ℕ, unifIoo.real (tupleBigEvent c ε n S) ≤ (C / Lnorm n) ^ S.card)
    (k : ℕ) :
    ‖layerSum t c ε n k‖ ≤ (8 * C) ^ k / (Nat.factorial k) := by
  classical
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  set M : ℕ := min (n + 1) (lameCap n) with hM
  have hMle : (M : ℝ) ≤ 4 * Lnorm n :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (min_le_right (n + 1) (lameCap n)))
      (lameCap_le hL)
  rw [layerSum_eq_capped t c ε hn k]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ S ∈ Finset.powersetCard k (Finset.range M),
      ‖∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α‖
        ≤ 2 ^ k * (C / Lnorm n) ^ k := by
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have h1 := norm_integral_prod_jumpFactor_le t c ε n S
    have h2 := hbnd S
    rw [hcard] at h1 h2
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_range, nsmul_eq_mul]
  have hchoose : (M.choose k : ℝ) ≤ (M : ℝ) ^ k / (Nat.factorial k) :=
    Nat.choose_le_pow_div k M
  have hfac : (0 : ℝ) < (Nat.factorial k) := by
    exact_mod_cast Nat.factorial_pos k
  have hbase : (0 : ℝ) ≤ 2 ^ k * (C / Lnorm n) ^ k := by positivity
  refine le_trans (mul_le_mul_of_nonneg_right hchoose hbase) ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hfac]
  have hkey : (M : ℝ) ^ k * (2 ^ k * (C / Lnorm n) ^ k)
      = ((M : ℝ) * (2 * (C / Lnorm n))) ^ k := by
    rw [mul_pow, mul_pow]
  rw [hkey]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have h8 : (M : ℝ) * (2 * (C / Lnorm n)) ≤ (4 * Lnorm n) * (2 * (C / Lnorm n)) :=
    mul_le_mul_of_nonneg_right hMle (by positivity)
  refine le_trans h8 (le_of_eq ?_)
  field_simp
  ring

/-! ## The series assembly -/

/-- Above `n + 1` there are no level sets, so the layer vanishes. -/
lemma layerSum_eq_zero_of_gt (t c ε : ℝ) {n k : ℕ} (hk : n + 1 < k) :
    layerSum t c ε n k = 0 := by
  have h : Finset.powersetCard k (Finset.range (n + 1)) = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by rw [Finset.card_range]; exact hk)
  simp [layerSum, h]

/-- The layer decomposition as an (everywhere convergent, finitely supported)
series. -/
theorem integral_exp_largeSum_eq_tsum_layers {c ε : ℝ} (hε : 0 < ε) (t : ℝ) (n : ℕ) :
    (∫ α in Ioo (0:ℝ) 1, Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I))
      = ∑' k : ℕ, layerSum t c ε n k := by
  rw [tsum_eq_sum (s := Finset.range (n + 2)) (fun k hk => ?_),
    integral_exp_largeSum_eq_sum_layers hε t n]
  exact layerSum_eq_zero_of_gt t c ε (by simpa [Finset.mem_range] using hk)

/-- **The series assembly, unconditional in its own right.**  Granted only the
*layer limits* — one limit per fixed `k` — the full characteristic-function
limit follows.  The interchange of the `k`-sum with `n → ∞` is discharged here
by the `k`-uniform domination `(8C)^k/k!` of `norm_layerSum_le`, which is
summable with a base independent of `n`.

Together with `exp_largeSum_powerset_expansion` (piece 1) and
`norm_integral_prod_jumpFactor_le` (piece 2), this reduces
`CorFinal.largeSum_charFun_limit` to the single hypothesis `hlim`: everything
else on the factorial route is now proved. -/
theorem largeSum_charFun_limit_of_layer_limits (c : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ)
    (a : ℕ → ℂ)
    (hlim : ∀ k : ℕ, Tendsto (fun n : ℕ => layerSum t c ε n k) atTop (𝓝 (a k))) :
    Tendsto (fun n : ℕ => ∫ α in Ioo (0:ℝ) 1,
        Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I)) atTop
      (𝓝 (∑' k : ℕ, a k)) := by
  obtain ⟨C, hC, hCn⟩ := exists_tupleBigEvent_bound c hε
  have hL3 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop 3
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      ‖layerSum t c ε n k‖ ≤ (8 * C) ^ k / (Nat.factorial k) := by
    filter_upwards [hCn, hL3, eventually_ge_atTop 1] with n hn hL hn1 k
    exact norm_layerSum_le t c hC hn1 hL hn k
  have hsum : Summable fun k : ℕ => (8 * C) ^ k / (Nat.factorial k) :=
    Real.summable_pow_div_factorial (8 * C)
  refine (tendsto_tsum_of_dominated_convergence hsum hlim hdom).congr' ?_
  filter_upwards with n
  exact (integral_exp_largeSum_eq_tsum_layers hε t n).symm

/-- **`CorFinal.largeSum_charFun_limit`, reduced to the layer limits.**  The
conclusion is the statement of `Kwon1002.CorFinal.largeSum_charFun_limit`
reproduced token for token; the hypothesis is the layer limit named in that
docstring, and nothing else. -/
theorem largeSum_charFun_limit_of_layer_limit (c ε : ℝ) (hε0 : 0 < ε) (_hε1 : ε < 1) (t : ℝ)
    (hlim : ∀ k : ℕ, Tendsto (fun n : ℕ => layerSum t c ε n k) atTop
      (𝓝 ((∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)) ^ k / (Nat.factorial k)))) :
    Tendsto (fun n : ℕ => ∫ α in Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I)) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) := by
  have hexp : ∀ z : ℂ, Complex.exp z = ∑' k : ℕ, z ^ k / (Nat.factorial k) := fun z => by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  rw [hexp (∫ x in {x : ℝ | ε < |x|},
    (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1) * (levyIntensityDensity x : ℂ))]
  exact largeSum_charFun_limit_of_layer_limits c hε0 t _ hlim

/-! ## Non-vacuity and the statement guard

`hlim` above is a hypothesis about a family of limits; the `k = 0` member is
checked here to be *true* rather than merely assumed, which pins the shape of
the target (subsets, hence `1/k!`; not embeddings, which would carry no
factorial). -/

/-- **The `k = 0` layer is `1`, matching the target `Λ̂^0/0! = 1`.**  A
non-vacuity check on the shape of the layer limit. -/
theorem layerSum_zero (t c ε : ℝ) (n : ℕ) : layerSum t c ε n 0 = 1 := by
  classical
  rw [layerSum, Finset.powersetCard_zero]
  rw [Finset.sum_singleton]
  simp [MeasureTheory.integral_const]

/-- Consistency of the `k = 0` layer with the target constant. -/
example (t c ε : ℝ) (n : ℕ) (Z : ℂ) :
    layerSum t c ε n 0 = Z ^ 0 / (Nat.factorial 0) := by
  rw [layerSum_zero]; norm_num

end

end FactorialRoute

end Kwon1002

/- **Statement guard.**  The conclusion of
`Kwon1002.FactorialRoute.largeSum_charFun_limit_of_layer_limit` is the
statement of `Kwon1002.CorFinal.largeSum_charFun_limit`, token for token.  The
`example` mentions a sorried declaration, so it is anonymous and nothing proved
above depends on it. -/
example : ∀ (c ε : ℝ), 0 < ε → ε < 1 → ∀ t : ℝ,
    Filter.Tendsto (fun n : ℕ => ∫ α in Set.Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Kwon1002.Assembly5.largeSum c ε α n : ℂ) * Complex.I)) Filter.atTop
      (nhds (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (Kwon1002.levyIntensityDensity x : ℂ)))) :=
  @Kwon1002.CorFinal.largeSum_charFun_limit
