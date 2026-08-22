import Kwon1002.CorFinal
import Kwon1002.LevyExponent
import Kwon1002.L2Estimate
import Kwon1002.TupleMeasure

/-!
# The factorial-moment route to `CorFinal.largeSum_charFun_limit`

`Kwon1002/CorFinal.lean` records the fixed-`ε` large-jump characteristic
function limit (DEBT 1) as a `sorry`, and records it as *equivalent* to
`PoissonRoute.xi_largeIntegral_weak_limit`, the point-process weak limit.  That
equivalence is a statement about where the debt sits, not a route to
discharging it: neither side is proved, and the chain
`CorFinal.largeSum_charFun_limit` sits on consumes
`LevyExponent.tuple_measure_convergence` nowhere.

This module builds the route the `largeSum_charFun_limit` docstring names, in
standalone named pieces.  Nothing here is a `sorry`, and nothing here consumes
one.

## The pieces

Write `X_{n,j}` for the normalised signed mark, `J_n` for the bulk index set,
and

  `h_j(α) = (e^{i t X_{n,j}(α)} − 1) · 1{j ∈ J_n(α), |X_{n,j}(α)| > ε}`

(`jumpFactor`), supported on the *large-jump event* `bigEvent`, which is
`LevyExponent.bulkMarkEvent` at `B = PoissonRoute.truncSet ε`.

* **Piece 1, the expansion.**  `exp_largeSum_eq_prod`: for a.e. `α`,
  `exp(i t · largeSum) = ∏_{j ≤ n} (1 + h_j)`.  This is where the truncation
  `Z − Z^{(ε)}` is identified with `X·1{|X| > ε}`, including the degenerate
  `L = 0`.  `exp_largeSum_powerset_expansion` then applies `Finset.prod_add`:
  `exp(i t · largeSum) = ∑_{S ⊆ {0,…,n}} ∏_{j ∈ S} h_j`.

* **Piece 2, the domination.**  `norm_prod_jumpFactor_le` and
  `norm_integral_prod_jumpFactor_le`: `‖∏_{j∈S} h_j‖ ≤ 2^{|S|}` on the tuple
  event `⋂_{j∈S} bigEvent j` and `0` off it, so the `S`-term of the expansion
  is at most `2^{|S|}` times that tuple event's probability.  Together with the
  *deterministic* Lamé bound `L2Estimate.stoppingTime_le_log`
  (`τ_n ≤ 2L/log 2 + 2` for every irrational `α ∈ (0,1)`), which forces the
  tuple event to be null as soon as `S` contains a level above `2L/log 2 + 2`
  (`bigEvent_eq_empty_of_large`), only `O(L)` levels contribute, and the
  binomial coefficient `C(⌊2L/log 2⌋+3, k)` supplies the `1/k!` the series
  needs with no factorial bookkeeping.

## What remains, precisely

Exactly one analytic input, the **layer limit**: for each fixed `k`,

  `∑_{S ⊆ {0,…,n}, |S| = k} ∫_{(0,1)} ∏_{j∈S} h_j dα
      → (∫_{|x|>ε} (e^{itx} − 1) dΛ(x))^k / k!`.

That is the tuple limit of §4 for the **bounded complex symbol**
`x ↦ (e^{itx} − 1)·1{|x| > ε}` rather than for an indicator.  Two things
separate it from what the tree has, and the `largeSum_charFun_limit` docstring
names neither:

1. `LevyExponent.tuple_measure_convergence`, the indicator tuple limit, is a
   bare `sorry` (`#print axioms` verified); it is not an available input.
2. Even granted it, it is stated for a **set** `B`, and the symbol here is not
   an indicator.  Passing from indicators to a bounded complex symbol needs the
   limit uniformly over a simple-function approximation of the symbol, which is
   a statement the tree does not contain in any form.

**The structural half of this is now proved.**  `Kwon1002/FactorialSeries.lean`
proves `CorFinal.largeSum_charFun_limit` (conclusion token for token, guarded
inside Lean) from the layer limit *alone*: the regrouping by cardinality, the
deterministic Lamé cap in `ℕ`, the `k`-uniform tuple bound and the interchange
of the `k`-series with `n → ∞` are all discharged there.  That module also
sharpens item 2 above: the approximation does not merely need a bounded complex
symbol in place of an indicator, it needs tuple events carrying a *different*
set at each level, whereas `tuple_measure_convergence` fixes one `B` at every
level.  See the "Three records corrected" section of that file's header.

A second, purely combinatorial bridge is needed only if the layer is to be read
as a §4 tuple sum over embeddings rather than over subsets: the `|S| = k` layer
is `1/k!` times `∑_{f : Fin k ↪ {0,…,n}} ∫ ∏_i h_{f i}`, because each `k`-subset
carries exactly `k!` embeddings.  Mathlib has `Fintype.card_embedding_eq` but no
count of the embeddings with a *prescribed image*, so that bridge is unwritten;
the domination above does not need it, since the subset count `C(M,k)` already
carries the `1/k!`.

**A record corrected.**  `CorFinal.largeSum_charFun_limit`'s docstring says the
uniform-in-`n` domination "is available from the proved
`TupleMeasure.tuple_measure_le` and `L2Estimate.stoppingTime_le_log`".  The
per-tuple bound `tuple_measure_le` alone does **not** dominate a layer: the
number of `k`-tuples in `{0,…,n}` is `~n^k`, against which `(C/L)^k = (C/log n)^k`
is worthless.  What makes the domination work is `stoppingTime_le_log` being
*deterministic* — it caps the index set at `2L/log 2 + 2` for **every**
irrational `α`, not off an exceptional set — so the layer is a sum over
`C(O(L), k)` subsets rather than over `C(n,k)`.  With an exceptional set the
argument would fail, and the docstring's phrasing does not record that this is
the load-bearing point.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace FactorialRoute

noncomputable section

open Assembly5

/-! ## The large-jump event and the jump factor -/

/-- The large-jump event at level `j`: `j` is a bulk level of `α` and its
normalised signed mark exceeds `ε` in absolute value.  This is
`LevyExponent.bulkMarkEvent` at `B = PoissonRoute.truncSet ε`. -/
def bigEvent (c ε : ℝ) (n j : ℕ) : Set ℝ :=
  LevyExponent.bulkMarkEvent c n (PoissonRoute.truncSet ε) j

lemma mem_bigEvent {c ε : ℝ} {n j : ℕ} {α : ℝ} :
    α ∈ bigEvent c ε n j ↔ (j ∈ bulkIndices c α n ∧ ε < |signedMark α n j|) := Iff.rfl

lemma measurableSet_bigEvent (c ε : ℝ) (n j : ℕ) : MeasurableSet (bigEvent c ε n j) :=
  LevyExponent.measurableSet_bulkMarkEvent c n (PoissonRoute.measurableSet_truncSet ε) j

/-- `h_j(α) = (e^{i t X_{n,j}} − 1)·1{j ∈ J_n, |X_{n,j}| > ε}`, the factor the
product expansion of `exp(i t · largeSum)` runs over. -/
def jumpFactor (t c ε : ℝ) (n j : ℕ) (α : ℝ) : ℂ :=
  (bigEvent c ε n j).indicator
    (fun β : ℝ => Complex.exp ((t : ℂ) * (signedMark β n j : ℂ) * Complex.I) - 1) α

lemma jumpFactor_of_notMem {t c ε : ℝ} {n j : ℕ} {α : ℝ} (h : α ∉ bigEvent c ε n j) :
    jumpFactor t c ε n j α = 0 := Set.indicator_of_notMem h _

lemma jumpFactor_of_mem {t c ε : ℝ} {n j : ℕ} {α : ℝ} (h : α ∈ bigEvent c ε n j) :
    jumpFactor t c ε n j α
      = Complex.exp ((t : ℂ) * (signedMark α n j : ℂ) * Complex.I) - 1 :=
  Set.indicator_of_mem h _

lemma norm_exp_mul_I (t x : ℝ) :
    ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
  have hval : (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hval, Complex.norm_exp_ofReal_mul_I]

lemma norm_jumpFactor_le (t c ε : ℝ) (n j : ℕ) (α : ℝ) :
    ‖jumpFactor t c ε n j α‖ ≤ 2 := by
  by_cases h : α ∈ bigEvent c ε n j
  · rw [jumpFactor_of_mem h]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_exp_mul_I]
    norm_num
  · rw [jumpFactor_of_notMem h, norm_zero]
    norm_num

lemma measurable_jumpFactor (t c ε : ℝ) (n j : ℕ) : Measurable (jumpFactor t c ε n j) := by
  refine Measurable.indicator ?_ (measurableSet_bigEvent c ε n j)
  have h : Measurable fun β : ℝ => ((signedMark β n j : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_signedMark n j)
  fun_prop

/-! ## Piece 1: the product expansion

The truncation `Z_{n,j} − Z^{(ε)}_{n,j}` is the mark itself on the large-jump
event and zero off it — including at `n ≤ 1`, where `L = log n = 0` and Lean's
division convention makes every normalised mark `0`. -/

open scoped Classical in
lemma largeSum_term_eq {c ε : ℝ} (hε : 0 < ε) (α : ℝ) (n j : ℕ) (hj : j ∈ bulkIndices c α n) :
    (-1 : ℝ) ^ j * (mark α n j - truncatedMark ε α n j) / Lnorm n
      = if α ∈ bigEvent c ε n j then signedMark α n j else 0 := by
  classical
  have hL : 0 ≤ Lnorm n := Lnorm_nonneg n
  have hm : 0 ≤ mark α n j := mark_nonneg α n j
  have habs : |signedMark α n j| = mark α n j / Lnorm n := by
    rw [signedMark, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hm, abs_of_nonneg hL]
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- `L = 0`: every normalised mark is `0`, so both sides vanish.
    have h0 : Lnorm n = 0 := hL0.symm
    have hnot : α ∉ bigEvent c ε n j := by
      rw [mem_bigEvent, habs, h0, div_zero]
      exact fun h => absurd h.2 (by simpa using hε.le)
    rw [if_neg hnot, h0, div_zero]
  · by_cases hsmall : mark α n j ≤ ε * Lnorm n
    · have htr : truncatedMark ε α n j = mark α n j := by
        rw [truncatedMark, if_pos hsmall]
      have hnot : α ∉ bigEvent c ε n j := by
        rw [mem_bigEvent, habs]
        refine fun h => absurd h.2 (not_lt.mpr ?_)
        rw [div_le_iff₀ hLpos]
        linarith [hsmall]
      rw [if_neg hnot, htr, sub_self, mul_zero, zero_div]
    · have htr : truncatedMark ε α n j = 0 := by
        rw [truncatedMark, if_neg hsmall]
      have hmem : α ∈ bigEvent c ε n j := by
        rw [mem_bigEvent, habs]
        refine ⟨hj, ?_⟩
        rw [lt_div_iff₀ hLpos]
        linarith [not_le.mp hsmall]
      rw [if_pos hmem, htr, sub_zero, signedMark]

open scoped Classical in
/-- **The large jump sum is the sum of the marks on the large-jump event.** -/
theorem largeSum_eq_sum_filter {c ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1)
    (hirr : Irrational α) (n : ℕ) :
    largeSum c ε α n
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => α ∈ bigEvent c ε n j),
          signedMark α n j := by
  classical
  have hsub := bulkIndices_subset_range c α hα hirr n
  rw [Finset.sum_filter, largeSum]
  rw [Finset.sum_congr rfl (fun j hj => largeSum_term_eq hε α n j hj)]
  refine Finset.sum_subset hsub ?_
  intro j _ hj
  have : α ∉ bigEvent c ε n j := fun h => hj (mem_bigEvent.mp h).1
  rw [if_neg this]

open scoped Classical in
/-- **Piece 1.**  `exp(i t · largeSum) = ∏_{j ≤ n} (1 + h_j)`. -/
theorem exp_largeSum_eq_prod {c ε : ℝ} (hε : 0 < ε) (t : ℝ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1)
    (hirr : Irrational α) (n : ℕ) :
    Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I)
      = ∏ j ∈ Finset.range (n + 1), (1 + jumpFactor t c ε n j α) := by
  classical
  have hfilter : (∏ j ∈ (Finset.range (n + 1)).filter (fun j => α ∈ bigEvent c ε n j),
      (1 + jumpFactor t c ε n j α))
      = ∏ j ∈ Finset.range (n + 1), (1 + jumpFactor t c ε n j α) := by
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro j hj hjn
    have hnot : α ∉ bigEvent c ε n j := by
      intro h
      exact hjn (Finset.mem_filter.mpr ⟨hj, h⟩)
    rw [jumpFactor_of_notMem hnot, add_zero]
  rw [← hfilter]
  have hval : ∀ j ∈ (Finset.range (n + 1)).filter (fun j => α ∈ bigEvent c ε n j),
      (1 + jumpFactor t c ε n j α)
        = Complex.exp ((t : ℂ) * (signedMark α n j : ℂ) * Complex.I) := by
    intro j hj
    rw [jumpFactor_of_mem (Finset.mem_filter.mp hj).2]
    ring
  rw [Finset.prod_congr rfl hval, ← Complex.exp_sum]
  congr 1
  rw [largeSum_eq_sum_filter hε hα hirr n, Complex.ofReal_sum, Finset.mul_sum,
    Finset.sum_mul]

/-- **Piece 1, expanded.**  `exp(i t · largeSum) = ∑_{S ⊆ {0,…,n}} ∏_{j∈S} h_j`. -/
theorem exp_largeSum_powerset_expansion {c ε : ℝ} (hε : 0 < ε) (t : ℝ) {α : ℝ}
    (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α) (n : ℕ) :
    Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I)
      = ∑ S ∈ (Finset.range (n + 1)).powerset, ∏ j ∈ S, jumpFactor t c ε n j α := by
  classical
  rw [exp_largeSum_eq_prod hε t hα hirr n]
  have h := Finset.prod_add (fun j => jumpFactor t c ε n j α) (fun _ => (1 : ℂ))
    (Finset.range (n + 1))
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun j _ => add_comm _ _

/-! ## Piece 2: the domination -/

/-- The tuple event of a subset: every level of `S` is a large-jump level. -/
def tupleBigEvent (c ε : ℝ) (n : ℕ) (S : Finset ℕ) : Set ℝ :=
  ⋂ j ∈ S, bigEvent c ε n j

lemma measurableSet_tupleBigEvent (c ε : ℝ) (n : ℕ) (S : Finset ℕ) :
    MeasurableSet (tupleBigEvent c ε n S) :=
  MeasurableSet.biInter S.countable_toSet fun j _ => measurableSet_bigEvent c ε n j

/-- **Piece 2, pointwise.**  The `S`-term of the expansion is bounded by
`2^{|S|}` on the tuple event and vanishes off it. -/
theorem norm_prod_jumpFactor_le (t c ε : ℝ) (n : ℕ) (S : Finset ℕ) (α : ℝ) :
    ‖∏ j ∈ S, jumpFactor t c ε n j α‖
      ≤ 2 ^ S.card
        * (tupleBigEvent c ε n S).indicator (fun _ => (1 : ℝ)) α := by
  classical
  by_cases h : α ∈ tupleBigEvent c ε n S
  · rw [Set.indicator_of_mem h, mul_one, norm_prod]
    calc ∏ j ∈ S, ‖jumpFactor t c ε n j α‖
        ≤ ∏ _j ∈ S, (2 : ℝ) :=
          Finset.prod_le_prod (fun j _ => norm_nonneg _)
            (fun j _ => norm_jumpFactor_le t c ε n j α)
      _ = 2 ^ S.card := by rw [Finset.prod_const]
  · -- some level of `S` is not a large-jump level, so a factor vanishes
    obtain ⟨j, hjS, hj⟩ : ∃ j ∈ S, α ∉ bigEvent c ε n j := by
      by_contra hcon
      push_neg at hcon
      exact h (Set.mem_biInter fun j hjS => hcon j hjS)
    have hzero : ∏ j ∈ S, jumpFactor t c ε n j α = 0 :=
      Finset.prod_eq_zero hjS (jumpFactor_of_notMem hj)
    rw [hzero, norm_zero, Set.indicator_of_notMem h, mul_zero]

/-- **Piece 2, integrated.**  The `S`-term of the expansion has modulus at most
`2^{|S|}` times the probability of the tuple event. -/
theorem norm_integral_prod_jumpFactor_le (t c ε : ℝ) (n : ℕ) (S : Finset ℕ) :
    ‖∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α‖
      ≤ 2 ^ S.card * unifIoo.real (tupleBigEvent c ε n S) := by
  classical
  have hmeas : Measurable fun α : ℝ => ∏ j ∈ S, jumpFactor t c ε n j α :=
    Finset.measurable_prod _ fun j _ => measurable_jumpFactor t c ε n j
  have hbound : ∀ α : ℝ, ‖∏ j ∈ S, jumpFactor t c ε n j α‖
      ≤ 2 ^ S.card * (tupleBigEvent c ε n S).indicator (fun _ => (1 : ℝ)) α :=
    fun α => norm_prod_jumpFactor_le t c ε n S α
  have hint : IntegrableOn (fun α : ℝ => ∏ j ∈ S, jumpFactor t c ε n j α)
      (Ioo (0:ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := 2 ^ S.card) (by simp [Real.volume_Ioo])
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun α => ?_)
    refine le_trans (hbound α) ?_
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hgm : IntegrableOn
      (fun α : ℝ => 2 ^ S.card
        * (tupleBigEvent c ε n S).indicator (fun _ => (1 : ℝ)) α) (Ioo (0:ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := 2 ^ S.card) (by simp [Real.volume_Ioo])
      ((measurable_const.indicator
        (measurableSet_tupleBigEvent c ε n S)).const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun α => ?_)
    rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs <;> simp
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (setIntegral_mono_on hint.norm hgm measurableSet_Ioo
    (fun α _ => hbound α)) ?_
  rw [integral_const_mul]
  refine le_of_eq ?_
  congr 1
  rw [MeasureTheory.integral_indicator (measurableSet_tupleBigEvent c ε n S),
    setIntegral_const, smul_eq_mul, mul_one]
  rfl

/-! ### The index set is deterministically capped

`L2Estimate.stoppingTime_le_log` is the load-bearing input: it holds for
**every** irrational `α ∈ (0,1)`, with no exceptional set, so a subset `S`
containing a level above `2L/log 2 + 2` has null tuple event. -/

/-- A level above the Lamé bound is never a bulk level, for **every**
irrational `α` — the cap is deterministic, with no exceptional set. -/
theorem bigEvent_null_of_large (c ε : ℝ) (n j : ℕ) (hn : 1 ≤ n)
    (hj : 2 * Lnorm n / Real.log 2 + 2 < (j : ℝ)) :
    unifIoo (bigEvent c ε n j) = 0 := by
  classical
  have hsub : bigEvent c ε n j ∩ Ioo (0:ℝ) 1 ⊆ {α : ℝ | ¬ Irrational α} := by
    rintro α ⟨hmem, hα⟩
    by_contra hirr
    rw [Set.mem_setOf_eq, not_not] at hirr
    have hb := (mem_bigEvent.mp hmem).1
    have hlt : j < stoppingTime α n :=
      Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hle := L2Estimate.stoppingTime_le_log α hα hirr n hn
    have hcast : ((j : ℕ) : ℝ) < ((stoppingTime α n : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  have hnull : volume {α : ℝ | ¬ Irrational α} = 0 := by
    have h : {a : ℝ | ¬ Irrational a} = Set.range ((↑) : ℚ → ℝ) := by
      ext a; simp [Irrational]
    rw [h]
    exact (Set.countable_range _).measure_zero volume
  rw [unifIoo, Measure.restrict_apply' measurableSet_Ioo]
  exact measure_mono_null hsub hnull

/-- **The layer is a sum over `O(L)` subsets.**  A subset containing a level
above the Lamé bound contributes nothing, so only subsets of
`{0,…,⌊2L/log 2⌋+2}` survive, and their number at cardinality `k` is
`C(⌊2L/log 2⌋+3, k)` — which is where the `1/k!` of the exponential series
comes from. -/
theorem tupleBigEvent_null_of_large (c ε : ℝ) (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ)
    {j : ℕ} (hjS : j ∈ S) (hj : 2 * Lnorm n / Real.log 2 + 2 < (j : ℝ)) :
    unifIoo (tupleBigEvent c ε n S) = 0 := by
  refine measure_mono_null ?_ (bigEvent_null_of_large c ε n j hn hj)
  intro α hα
  exact Set.mem_iInter₂.mp hα j hjS

/-- The `S`-term of the expansion vanishes unless every level of `S` is below
the Lamé bound. -/
theorem integral_prod_jumpFactor_eq_zero_of_large (t c ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (S : Finset ℕ) {j : ℕ} (hjS : j ∈ S) (hj : 2 * Lnorm n / Real.log 2 + 2 < (j : ℝ)) :
    ‖∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α‖ = 0 := by
  refine le_antisymm ?_ (norm_nonneg _)
  refine le_trans (norm_integral_prod_jumpFactor_le t c ε n S) ?_
  rw [Measure.real, tupleBigEvent_null_of_large c ε n hn S hjS hj, ENNReal.toReal_zero,
    mul_zero]

end

end FactorialRoute

end Kwon1002
