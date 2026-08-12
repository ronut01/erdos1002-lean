import Kwon1002.L2Estimate

/-!
# OffDiagonal, the off-diagonal input of Lemma 5.2

Targets, both reproduced **token for token** (diffed against the sources):

* `bulk_offdiagonal_input'` = `Kwon1002.L2Estimate.bulk_offdiagonal_input`
  (`Kwon1002/L2Estimate.lean`, line 577);
* `truncatedBulkSum_centered_L2'` = `Kwon1002.truncatedBulkSum_centered_L2`
  (`Kwon1002/SmallJumps.lean`, line 504).

## Proved outright (all axiom-clean: `propext, Classical.choice, Quot.sound`)

* `le_dyadic_sum`, `0 ≤ x ≤ 2^{m+1} ⟹ x ≤ 1 + Σ_{i≤m} 2^i 1{2^i < x}`.
* `integral_le_of_tail`, `integral_mul_le_of_tails`, layer-cake first and
  mixed second moments from tail bounds, in abstract form.  The dyadic
  majorant replaces the (double) integration of the layer-cake formula, so
  no Tonelli argument is needed:
  `E[XY] ≤ 1 + 2K(m+1) + C(m+1)²` from `P(X>s) ≤ K/(1+s)`,
  `P(Y>t) ≤ K/(1+t)` and `P(X>s, Y>t) ≤ C/((1+s)(1+t))`.
* `dyDepth`, `shift_le_two_pow`, `dyDepth_succ_le`, the dyadic depth
  `m_n = ⌈2 log(2+L)⌉` really dominates the mark (`2+L ≤ 2^{m_n+1}`, from
  `2 log 2 ≥ 1`) and costs only `m_n + 1 ≤ 2(1 + log(2+L))`.
* **`truncatedMark_joint_moment`, display (42), second half**:
  `E|Z^{(ε)}_{n,j} Z^{(ε)}_{n,k}| ≤ C (1 + log(2+L))²` for `j ≠ k`,
  uniformly in `ε ∈ (0,1)`, `n` and the pair.  Input: `mark_joint_tail_bound`
  and `mark_tail_bound` of `Kwon1002/L2Estimate.lean`, hence ultimately
  `digit_tail_product` (Lem 3.1(ii)), which is **proved** in
  `Kwon1002/DigitTail.lean`.
* `truncatedMark_first_moment`, the companion `E Z^{(ε)}_{n,j} ≤ C(1+log(2+L))`.
* `centered_pair_integral`, `Cov = E[g_j g_k] − E g_j · E g_k` for the bulk
  summands.
* **`bulkTermCentered_offdiag_bound`**, (42) after the `1/L` normalization:
  for `j ≠ k`,
  `|Cov(g_j, g_k)| ≤ C (1 + log(2+L))² / L²`.
* **`near_pair_decay`**, the manuscript's `O(LH log²L) = o(L²)`: for every
  `δ > 0` and all large `n`,
  `κ·L·H · (C (1+log(2+L))²/L²) ≤ δ`.  Proof: with `v = L^{1/16}`,
  `1 + log(2+L) ≤ 33 v` (from `log x ≤ 16 x^{1/16}`) and
  `L·H/L² = L^{-1/4}`, so the whole expression is `≤ κ C 1089 · L^{-1/8} → 0`.
  This is where `H = L^{3/4}` is used: any `H = L^{θ}` with `θ < 1` works.
* `sum_offdiag_eq`, `bulk_offdiagonal_input'`,
  `truncatedBulkSum_centered_L2'`, the assembly.

## The one sorried input, and the precise obstruction

`bulk_offdiagonal_far`, **Proposition 4.1 for pairs**.  There is a set `B`
of pairs with `#B = O(L·H)` (the manuscript's overlapping, `H`-near and
resonance-near pairs, the same `O(L·H)` shape as
`Kwon1002.prop_4_2_two_block_factorization`) outside of which the
covariances sum to `≤ ε/2`.  This is the step the manuscript performs by
cutting each digit at `A_L = L^D` (`D > 2`), Jackson-approximating the
Lipschitz truncation, and applying Proposition 4.1 with `A` so large that
`L² O_A(L^{-A}) = o(1)`.

It cannot be discharged here because Proposition 4.1 is itself sorried in
this development: `Kwon1002.prop_4_1_marked_factorization`
(`Kwon1002/Section4.lean`, display (30)) and
`Kwon1002.Prop41.prop_4_1_error_shape`.

**One honest caveat about the scope of `bulk_offdiagonal_far`.**  The
manuscript's (41) sums over the random set `J_n` only, whereas the shared
file's `bulk_offdiagonal_input`, reproduced here token-identically, sums
over the deterministic range `{0,…,n}`, with `bulkTerm` extended by `0` off
the bulk.  Pairs `(j,k)` with `j` or `k` far beyond `τ_n` therefore still
contribute `−E g_j · E g_k`, and controlling them is *not* part of
Proposition 4.1: it is the off-diagonal analogue of the already-proved
`Kwon1002.L2Estimate.bulk_window_input` (which does the same job for the
diagonal, out of `stoppingTime_le_log`).  That bookkeeping is folded into
`bulk_offdiagonal_far` here rather than isolated, so `bulk_offdiagonal_far`
= Proposition 4.1 for pairs **plus** the off-diagonal window tail.  Both
halves are `o(1)`; separating them is a natural next refinement.

**Sorried results consumed as inputs: exactly one**, `bulk_offdiagonal_far`,
stated in this file.  Nothing else in this file depends on a `sorry`:
`digit_tail_product` (Lem 3.1(ii)) is proved in `Kwon1002/DigitTail.lean`,
and `shrinking_anti_concentration` (Lem 3.3) is not used.

## Two remarks on the split

1. The *near* half of the manuscript's argument is now unconditional.  In
   particular display (42)'s second half is proved with the sharper
   constant `C(1+log(2+L))²` rather than `C log²(2+L)`; the difference is
   immaterial and the proved form is valid for all `n` (including `n ≤ 2`,
   where `L` degenerates).
2. `near_pair_decay` shows the near half has *room to spare*: it decays like
   `L^{-1/8}`, so `bulk_offdiagonal_far` could be weakened to allow a bad
   set of size `O(L^{2-1/9})` and the assembly would still go through.  The
   statement is kept at the manuscript's `O(L·H)` so that it can be matched
   directly against §4/§7 output.
-/

open Filter MeasureTheory Set

namespace Kwon1002

namespace OffDiag

noncomputable section

/-! ### 1. A dyadic majorant -/

/-- For `0 ≤ x ≤ 2^{m+1}`, `x ≤ 1 + Σ_{i≤m} 2^i 1{2^i < x}`. -/
lemma le_dyadic_sum (m : ℕ) : ∀ x : ℝ, 0 ≤ x → x ≤ 2 ^ (m + 1) →
    x ≤ 1 + ∑ i ∈ Finset.range (m + 1), 2 ^ i * (if (2:ℝ) ^ i < x then (1:ℝ) else 0) := by
  induction m with
  | zero =>
      intro x hx0 hxM
      have h2 : x ≤ 2 := by simpa using hxM
      rw [Finset.sum_range_one, pow_zero, one_mul]
      by_cases h : (1:ℝ) < x
      · rw [if_pos h]; linarith
      · rw [if_neg h]; push_neg at h; linarith
  | succ m ih =>
      intro x hx0 hxM
      by_cases h : x ≤ 2 ^ (m + 1)
      · have hprev := ih x hx0 h
        rw [Finset.sum_range_succ]
        have hnn : (0:ℝ) ≤ 2 ^ (m + 1) * (if (2:ℝ) ^ (m + 1) < x then (1:ℝ) else 0) := by
          positivity
        linarith
      · push_neg at h
        have hall : ∀ i ∈ Finset.range (m + 1 + 1),
            (2:ℝ) ^ i * (if (2:ℝ) ^ i < x then (1:ℝ) else 0) = 2 ^ i := by
          intro i hi
          have hile : i ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hmono : (2:ℝ) ^ i ≤ 2 ^ (m + 1) := by
            exact pow_le_pow_right₀ (by norm_num) hile
          have hlt : (2:ℝ) ^ i < x := lt_of_le_of_lt hmono h
          rw [if_pos hlt, mul_one]
        rw [Finset.sum_congr rfl hall]
        have hgeom : ∑ i ∈ Finset.range (m + 1 + 1), (2:ℝ) ^ i = 2 ^ (m + 1 + 1) - 1 := by
          rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
          norm_num
        rw [hgeom]
        linarith [hxM]

/-! ### 2. Moment bounds from tail bounds -/

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_of_abs_le {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ ω, |f ω| ≤ M) : Integrable f ν := by
  refine memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable M ?_)
  exact Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hM ω

lemma integrable_const_mul_indicator {ν : Measure Ω} [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) (c : ℝ) :
    Integrable (fun ω => c * s.indicator (fun _ => (1:ℝ)) ω) ν :=
  ((integrable_const (1:ℝ)).indicator hs).const_mul c

lemma integral_const_mul_indicator {ν : Measure Ω} [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) (c : ℝ) :
    ∫ ω, c * s.indicator (fun _ => (1:ℝ)) ω ∂ν = c * (ν s).toReal := by
  rw [integral_const_mul, integral_indicator_const (1:ℝ) hs]
  simp [measureReal_def]

/-- Layer-cake first moment from a `K/(1+t)` tail: `E X ≤ 1 + K(m+1)`
whenever `0 ≤ X ≤ 2^{m+1}`. -/
theorem integral_le_of_tail {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (m : ℕ) (hXM : ∀ ω, X ω ≤ 2 ^ (m + 1))
    {K : ℝ} (hK : 0 ≤ K)
    (hXt : ∀ s : ℝ, 0 < s → (ν {ω | s < X ω}).toReal ≤ K / (1 + s)) :
    ∫ ω, X ω ∂ν ≤ 1 + K * ((m : ℝ) + 1) := by
  classical
  set S : ℕ → Set Ω := fun i => {ω | (2:ℝ) ^ i < X ω} with hS
  have hSm : ∀ i, MeasurableSet (S i) := fun i => measurableSet_lt measurable_const hX
  set G : Ω → ℝ := fun ω =>
    1 + ∑ i ∈ Finset.range (m + 1), 2 ^ i * (S i).indicator (fun _ => (1:ℝ)) ω with hG
  have hpt : ∀ ω, X ω ≤ G ω := by
    intro ω
    have h := le_dyadic_sum m (X ω) (hX0 ω) (hXM ω)
    have heq : ∑ i ∈ Finset.range (m + 1),
          (2:ℝ) ^ i * (if (2:ℝ) ^ i < X ω then (1:ℝ) else 0)
        = ∑ i ∈ Finset.range (m + 1), 2 ^ i * (S i).indicator (fun _ => (1:ℝ)) ω := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
    rw [heq] at h
    simpa [hG] using h
  have hXint : Integrable X ν :=
    integrable_of_abs_le hX (M := 2 ^ (m + 1)) fun ω => by
      rw [abs_of_nonneg (hX0 ω)]; exact hXM ω
  have hGsum : Integrable
      (fun ω => ∑ i ∈ Finset.range (m + 1), 2 ^ i * (S i).indicator (fun _ => (1:ℝ)) ω) ν :=
    integrable_finset_sum _ fun i _ => integrable_const_mul_indicator (hSm i) _
  have hGint : Integrable G ν := (integrable_const (1:ℝ)).add hGsum
  have hGval : ∫ ω, G ω ∂ν
      = 1 + ∑ i ∈ Finset.range (m + 1), 2 ^ i * (ν (S i)).toReal := by
    have h1 : ∫ ω, G ω ∂ν = (∫ _ω : Ω, (1:ℝ) ∂ν)
        + ∫ ω, (∑ i ∈ Finset.range (m + 1),
            2 ^ i * (S i).indicator (fun _ => (1:ℝ)) ω) ∂ν := by
      rw [hG]; exact integral_add (integrable_const (1:ℝ)) hGsum
    have h2 : (∫ _ω : Ω, (1:ℝ) ∂ν) = 1 := by simp
    have h3 : ∫ ω, (∑ i ∈ Finset.range (m + 1),
          2 ^ i * (S i).indicator (fun _ => (1:ℝ)) ω) ∂ν
        = ∑ i ∈ Finset.range (m + 1), 2 ^ i * (ν (S i)).toReal := by
      rw [integral_finset_sum _ fun i _ => integrable_const_mul_indicator (hSm i) _]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul_indicator (hSm i) _
    rw [h1, h2, h3]
  have hterm : ∀ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * (ν (S i)).toReal ≤ K := by
    intro i _
    have hpos : (0:ℝ) < 2 ^ i := by positivity
    have h1 : (ν (S i)).toReal ≤ K / (1 + 2 ^ i) := hXt _ hpos
    have h2 : (2:ℝ) ^ i * (ν (S i)).toReal ≤ 2 ^ i * (K / (1 + 2 ^ i)) :=
      mul_le_mul_of_nonneg_left h1 hpos.le
    refine le_trans h2 ?_
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + 2 ^ i)]
    nlinarith
  calc ∫ ω, X ω ∂ν ≤ ∫ ω, G ω ∂ν := integral_mono hXint hGint hpt
    _ = 1 + ∑ i ∈ Finset.range (m + 1), 2 ^ i * (ν (S i)).toReal := hGval
    _ ≤ 1 + ∑ _i ∈ Finset.range (m + 1), K := by
        have := Finset.sum_le_sum hterm
        linarith
    _ = 1 + K * ((m : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Two-dimensional layer-cake bound: with `0 ≤ X, Y ≤ 2^{m+1}`, marginal
tails `K/(1+t)` and joint tail `C/((1+s)(1+t))`,
`E[XY] ≤ 1 + 2K(m+1) + C(m+1)²`.  This is display (42)'s second half in
abstract form (the dyadic decomposition replaces the double integration). -/
theorem integral_mul_le_of_tails {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (m : ℕ) (hXM : ∀ ω, X ω ≤ 2 ^ (m + 1)) (hYM : ∀ ω, Y ω ≤ 2 ^ (m + 1))
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hXt : ∀ s : ℝ, 0 < s → (ν {ω | s < X ω}).toReal ≤ K / (1 + s))
    (hYt : ∀ t : ℝ, 0 < t → (ν {ω | t < Y ω}).toReal ≤ K / (1 + t))
    (hjoint : ∀ s t : ℝ, 0 < s → 0 < t →
      (ν {ω | s < X ω ∧ t < Y ω}).toReal ≤ C / ((1 + s) * (1 + t))) :
    ∫ ω, X ω * Y ω ∂ν ≤ 1 + 2 * K * ((m : ℝ) + 1) + C * ((m : ℝ) + 1) ^ 2 := by
  classical
  set SX : ℕ → Set Ω := fun i => {ω | (2:ℝ) ^ i < X ω} with hSX
  set SY : ℕ → Set Ω := fun l => {ω | (2:ℝ) ^ l < Y ω} with hSY
  have hSXm : ∀ i, MeasurableSet (SX i) := fun i => measurableSet_lt measurable_const hX
  have hSYm : ∀ l, MeasurableSet (SY l) := fun l => measurableSet_lt measurable_const hY
  set A : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range (m + 1), 2 ^ i * (SX i).indicator (fun _ => (1:ℝ)) ω with hA
  set B : Ω → ℝ := fun ω =>
    ∑ l ∈ Finset.range (m + 1), 2 ^ l * (SY l).indicator (fun _ => (1:ℝ)) ω with hB
  set D : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
      2 ^ (i + l) * (SX i ∩ SY l).indicator (fun _ => (1:ℝ)) ω with hD
  -- pointwise majorant
  have hAnn : ∀ ω, 0 ≤ A ω := by
    intro ω
    refine Finset.sum_nonneg fun i _ => ?_
    have : (0:ℝ) ≤ (SX i).indicator (fun _ => (1:ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    positivity
  have hBnn : ∀ ω, 0 ≤ B ω := by
    intro ω
    refine Finset.sum_nonneg fun l _ => ?_
    have : (0:ℝ) ≤ (SY l).indicator (fun _ => (1:ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    positivity
  have hXA : ∀ ω, X ω ≤ 1 + A ω := by
    intro ω
    have h := le_dyadic_sum m (X ω) (hX0 ω) (hXM ω)
    have heq : ∑ i ∈ Finset.range (m + 1),
          (2:ℝ) ^ i * (if (2:ℝ) ^ i < X ω then (1:ℝ) else 0) = A ω := by
      rw [hA]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
    rw [heq] at h
    exact h
  have hYB : ∀ ω, Y ω ≤ 1 + B ω := by
    intro ω
    have h := le_dyadic_sum m (Y ω) (hY0 ω) (hYM ω)
    have heq : ∑ l ∈ Finset.range (m + 1),
          (2:ℝ) ^ l * (if (2:ℝ) ^ l < Y ω then (1:ℝ) else 0) = B ω := by
      rw [hB]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
    rw [heq] at h
    exact h
  have hAB : ∀ ω, A ω * B ω = D ω := by
    intro ω
    rw [hA, hB, hD, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    have hsplit : ((2:ℝ) ^ i * (SX i).indicator (fun _ => (1:ℝ)) ω)
          * ((2:ℝ) ^ l * (SY l).indicator (fun _ => (1:ℝ)) ω)
        = 2 ^ (i + l) * ((SX i).indicator (fun _ => (1:ℝ)) ω
            * (SY l).indicator (fun _ => (1:ℝ)) ω) := by
      rw [pow_add]; ring
    rw [hsplit]
    congr 1
    simp only [Set.indicator_apply, Set.mem_inter_iff]
    by_cases h1 : ω ∈ SX i <;> by_cases h2 : ω ∈ SY l <;> simp [h1, h2]
  have hpt : ∀ ω, X ω * Y ω ≤ 1 + A ω + B ω + D ω := by
    intro ω
    have h := mul_le_mul (hXA ω) (hYB ω) (hY0 ω) (by linarith [hAnn ω])
    have hexp : (1 + A ω) * (1 + B ω) = 1 + A ω + B ω + A ω * B ω := by ring
    rw [hexp, hAB ω] at h
    exact h
  -- integrability
  have hAint : Integrable A ν :=
    integrable_finset_sum _ fun i _ => integrable_const_mul_indicator (hSXm i) _
  have hBint : Integrable B ν :=
    integrable_finset_sum _ fun l _ => integrable_const_mul_indicator (hSYm l) _
  have hDint : Integrable D ν :=
    integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun l _ =>
        integrable_const_mul_indicator ((hSXm i).inter (hSYm l)) _
  have hXY : Integrable (fun ω => X ω * Y ω) ν := by
    refine integrable_of_abs_le (hX.mul hY) (M := 2 ^ (m + 1) * 2 ^ (m + 1)) fun ω => ?_
    rw [abs_of_nonneg (mul_nonneg (hX0 ω) (hY0 ω))]
    exact mul_le_mul (hXM ω) (hYM ω) (hY0 ω) (by positivity)
  have hmajint : Integrable (fun ω => 1 + A ω + B ω + D ω) ν :=
    (((integrable_const (1:ℝ)).add hAint).add hBint).add hDint
  -- integral of the majorant
  have hAval : ∫ ω, A ω ∂ν
      = ∑ i ∈ Finset.range (m + 1), 2 ^ i * (ν (SX i)).toReal := by
    rw [hA, integral_finset_sum _ fun i _ => integrable_const_mul_indicator (hSXm i) _]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul_indicator (hSXm i) _
  have hBval : ∫ ω, B ω ∂ν
      = ∑ l ∈ Finset.range (m + 1), 2 ^ l * (ν (SY l)).toReal := by
    rw [hB, integral_finset_sum _ fun l _ => integrable_const_mul_indicator (hSYm l) _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul_indicator (hSYm l) _
  have hDval : ∫ ω, D ω ∂ν
      = ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
          2 ^ (i + l) * (ν (SX i ∩ SY l)).toReal := by
    rw [hD, integral_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun l _ =>
        integrable_const_mul_indicator ((hSXm i).inter (hSYm l)) _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun l _ =>
      integrable_const_mul_indicator ((hSXm i).inter (hSYm l)) _]
    exact Finset.sum_congr rfl fun l _ =>
      integral_const_mul_indicator ((hSXm i).inter (hSYm l)) _
  have hmajval : ∫ ω, (1 + A ω + B ω + D ω) ∂ν
      = 1 + (∫ ω, A ω ∂ν) + (∫ ω, B ω ∂ν) + ∫ ω, D ω ∂ν := by
    have e1 : ∫ ω, ((1 + A ω + B ω) + D ω) ∂ν
        = (∫ ω, ((1:ℝ) + A ω + B ω) ∂ν) + ∫ ω, D ω ∂ν :=
      integral_add (((integrable_const (1:ℝ)).add hAint).add hBint) hDint
    have e2 : ∫ ω, ((1 + A ω) + B ω) ∂ν
        = (∫ ω, ((1:ℝ) + A ω) ∂ν) + ∫ ω, B ω ∂ν :=
      integral_add ((integrable_const (1:ℝ)).add hAint) hBint
    have e3 : ∫ ω, ((1:ℝ) + A ω) ∂ν = (∫ _ω : Ω, (1:ℝ) ∂ν) + ∫ ω, A ω ∂ν :=
      integral_add (integrable_const (1:ℝ)) hAint
    have e4 : (∫ _ω : Ω, (1:ℝ) ∂ν) = 1 := by simp
    rw [e1, e2, e3, e4]
  -- termwise bounds
  have htermX : ∀ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * (ν (SX i)).toReal ≤ K := by
    intro i _
    have hpos : (0:ℝ) < 2 ^ i := by positivity
    have h1 : (ν (SX i)).toReal ≤ K / (1 + 2 ^ i) := hXt _ hpos
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    refine le_trans h2 ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 1 + 2 ^ i)]
    nlinarith
  have htermY : ∀ l ∈ Finset.range (m + 1), (2:ℝ) ^ l * (ν (SY l)).toReal ≤ K := by
    intro l _
    have hpos : (0:ℝ) < 2 ^ l := by positivity
    have h1 : (ν (SY l)).toReal ≤ K / (1 + 2 ^ l) := hYt _ hpos
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    refine le_trans h2 ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 1 + 2 ^ l)]
    nlinarith
  have htermD : ∀ i ∈ Finset.range (m + 1), ∀ l ∈ Finset.range (m + 1),
      (2:ℝ) ^ (i + l) * (ν (SX i ∩ SY l)).toReal ≤ C := by
    intro i _ l _
    have hposi : (0:ℝ) < 2 ^ i := by positivity
    have hposl : (0:ℝ) < 2 ^ l := by positivity
    have hset : SX i ∩ SY l = {ω | (2:ℝ) ^ i < X ω ∧ (2:ℝ) ^ l < Y ω} := by
      ext ω; simp [hSX, hSY, Set.mem_inter_iff]
    rw [hset]
    have h1 := hjoint ((2:ℝ) ^ i) ((2:ℝ) ^ l) hposi hposl
    have hposil : (0:ℝ) < 2 ^ (i + l) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hposil.le
    refine le_trans h2 ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < (1 + 2 ^ i) * (1 + 2 ^ l))]
    have hfac : (2:ℝ) ^ (i + l) = 2 ^ i * 2 ^ l := by rw [pow_add]
    rw [hfac]
    nlinarith [hposi, hposl, hC]
  -- assemble
  have hAle : (∫ ω, A ω ∂ν) ≤ K * ((m : ℝ) + 1) := by
    rw [hAval]
    calc ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * (ν (SX i)).toReal
        ≤ ∑ _i ∈ Finset.range (m + 1), K := Finset.sum_le_sum htermX
      _ = K * ((m : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hBle : (∫ ω, B ω ∂ν) ≤ K * ((m : ℝ) + 1) := by
    rw [hBval]
    calc ∑ l ∈ Finset.range (m + 1), (2:ℝ) ^ l * (ν (SY l)).toReal
        ≤ ∑ _l ∈ Finset.range (m + 1), K := Finset.sum_le_sum htermY
      _ = K * ((m : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hDle : (∫ ω, D ω ∂ν) ≤ C * ((m : ℝ) + 1) ^ 2 := by
    rw [hDval]
    calc ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
            (2:ℝ) ^ (i + l) * (ν (SX i ∩ SY l)).toReal
        ≤ ∑ _i ∈ Finset.range (m + 1), ∑ _l ∈ Finset.range (m + 1), C :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun l hl => htermD i hi l hl
      _ = C * ((m : ℝ) + 1) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc ∫ ω, X ω * Y ω ∂ν ≤ ∫ ω, (1 + A ω + B ω + D ω) ∂ν := integral_mono hXY hmajint hpt
    _ = 1 + (∫ ω, A ω ∂ν) + (∫ ω, B ω ∂ν) + ∫ ω, D ω ∂ν := hmajval
    _ ≤ 1 + 2 * K * ((m : ℝ) + 1) + C * ((m : ℝ) + 1) ^ 2 := by linarith

/-! ### 3. The dyadic depth attached to `L = log n` -/

/-- `m_n = ⌈2 log(2+L)⌉`: the dyadic depth at which the mark is cut off. -/
def dyDepth (n : ℕ) : ℕ := ⌈2 * Real.log (2 + Lnorm n)⌉₊

lemma log_two_ge_half : (1:ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / 2 by norm_num)
  have hinv : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hinv] at h
  linarith

lemma two_le_shift (n : ℕ) : (2:ℝ) ≤ 2 + Lnorm n := by
  have := Lnorm_nonneg n
  linarith

lemma log_shift_pos (n : ℕ) : (1:ℝ) / 2 ≤ Real.log (2 + Lnorm n) := by
  refine le_trans log_two_ge_half ?_
  exact Real.log_le_log (by norm_num) (two_le_shift n)

lemma one_le_logFactor (n : ℕ) : (1:ℝ) ≤ 1 + Real.log (2 + Lnorm n) := by
  have := log_shift_pos n
  linarith

/-- `2 + L ≤ 2^{m_n+1}`, the cutoff really dominates the mark. -/
lemma shift_le_two_pow (n : ℕ) : 2 + Lnorm n ≤ 2 ^ (dyDepth n + 1) := by
  set T : ℝ := 2 + Lnorm n with hT
  have hT2 : (2:ℝ) ≤ T := two_le_shift n
  have hTpos : (0:ℝ) < T := by linarith
  have hlogT : (1:ℝ) / 2 ≤ Real.log T := log_shift_pos n
  have hceil : 2 * Real.log T ≤ (dyDepth n : ℝ) := by
    have := Nat.le_ceil (2 * Real.log T)
    simpa [dyDepth, hT] using this
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := log_two_ge_half
  have hpowpos : (0:ℝ) < (2:ℝ) ^ (dyDepth n + 1) := by positivity
  have hkey : Real.log T ≤ Real.log ((2:ℝ) ^ (dyDepth n + 1)) := by
    rw [Real.log_pow]
    push_cast
    nlinarith [hlogT, hceil, hlog2]
  exact (Real.log_le_log_iff hTpos hpowpos).mp hkey

/-- `m_n + 1 ≤ 2(1 + log(2+L))`. -/
lemma dyDepth_succ_le (n : ℕ) :
    ((dyDepth n : ℝ) + 1) ≤ 2 * (1 + Real.log (2 + Lnorm n)) := by
  have hnn : (0:ℝ) ≤ 2 * Real.log (2 + Lnorm n) := by
    have := log_shift_pos n; linarith
  have h := Nat.ceil_lt_add_one hnn
  have : ((dyDepth n : ℝ)) < 2 * Real.log (2 + Lnorm n) + 1 := by
    simpa [dyDepth] using h
  linarith

/-! ### 4. Displays (42) for the truncated mark -/

lemma truncatedMark_restrict_tail {K : ℝ}
    (htail : ∀ (n j : ℕ) (t : ℝ), 0 < t →
      (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ t < mark α n j}).toReal ≤ K / (1 + t))
    (ε : ℝ) (n j : ℕ) :
    ∀ s : ℝ, 0 < s →
      ((volume.restrict (Ioo (0:ℝ) 1)) {α | s < truncatedMark ε α n j}).toReal
        ≤ K / (1 + s) := by
  intro s hs
  have hms : MeasurableSet {α : ℝ | s < truncatedMark ε α n j} :=
    measurableSet_lt measurable_const (measurable_truncatedMark ε n j)
  rw [Measure.restrict_apply hms]
  have hsub : {α : ℝ | s < truncatedMark ε α n j} ∩ Ioo (0:ℝ) 1
      ⊆ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ s < mark α n j} := by
    rintro α ⟨h1, h2⟩
    exact ⟨h2, lt_of_lt_of_le h1 (L2Estimate.truncatedMark_le_mark ε α n j)⟩
  exact le_trans (ENNReal.toReal_mono
    (L2Estimate.volume_ne_top_of_subset_Ioo (fun α hα => hα.1)) (measure_mono hsub))
    (htail n j s hs)

lemma truncatedMark_restrict_joint_tail {C : ℝ}
    (hjt : ∀ (n j k : ℕ), j ≠ k → ∀ (s t : ℝ), 0 < s → 0 < t →
      (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ s < mark α n j ∧ t < mark α n k}).toReal
        ≤ C / ((1 + s) * (1 + t)))
    (ε : ℝ) (n j k : ℕ) (hjk : j ≠ k) :
    ∀ s t : ℝ, 0 < s → 0 < t →
      ((volume.restrict (Ioo (0:ℝ) 1))
          {α | s < truncatedMark ε α n j ∧ t < truncatedMark ε α n k}).toReal
        ≤ C / ((1 + s) * (1 + t)) := by
  intro s t hs ht
  have hms : MeasurableSet
      {α : ℝ | s < truncatedMark ε α n j ∧ t < truncatedMark ε α n k} :=
    (measurableSet_lt measurable_const (measurable_truncatedMark ε n j)).inter
      (measurableSet_lt measurable_const (measurable_truncatedMark ε n k))
  rw [Measure.restrict_apply hms]
  have hsub : {α : ℝ | s < truncatedMark ε α n j ∧ t < truncatedMark ε α n k}
        ∩ Ioo (0:ℝ) 1
      ⊆ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ s < mark α n j ∧ t < mark α n k} := by
    rintro α ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, lt_of_lt_of_le h1 (L2Estimate.truncatedMark_le_mark ε α n j),
      lt_of_lt_of_le h2 (L2Estimate.truncatedMark_le_mark ε α n k)⟩
  exact le_trans (ENNReal.toReal_mono
    (L2Estimate.volume_ne_top_of_subset_Ioo (fun α hα => hα.1)) (measure_mono hsub))
    (hjt n j k hjk s t hs ht)

lemma truncatedMark_le_two_pow (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (α : ℝ) (n j : ℕ) :
    truncatedMark ε α n j ≤ 2 ^ (dyDepth n + 1) := by
  have h1 : truncatedMark ε α n j ≤ ε * Lnorm n := truncatedMark_le ε hε.le α n j
  have h2 : ε * Lnorm n ≤ Lnorm n := by
    have := Lnorm_nonneg n
    nlinarith
  have h3 := shift_le_two_pow n
  linarith

/-- **Display (42), second half**: `E|Z^{(ε)}_{n,j} Z^{(ε)}_{n,k}| ≤ C log²(2+L)`
for `j ≠ k`. -/
theorem truncatedMark_joint_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (n j k : ℕ), j ≠ k →
      (∫ α in Ioo (0:ℝ) 1, truncatedMark ε α n j * truncatedMark ε α n k)
        ≤ C * (1 + Real.log (2 + Lnorm n)) ^ 2 := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨K, hK, htail⟩ := L2Estimate.mark_tail_bound
  obtain ⟨C₀, hC₀, hjt⟩ := L2Estimate.mark_joint_tail_bound
  refine ⟨1 + 4 * K + 4 * C₀, by positivity, ?_⟩
  intro ε hε hε1 n j k hjk
  set m := dyDepth n with hm
  have hmain := integral_mul_le_of_tails (ν := volume.restrict (Ioo (0:ℝ) 1))
    (X := fun α => truncatedMark ε α n j) (Y := fun α => truncatedMark ε α n k)
    (measurable_truncatedMark ε n j) (measurable_truncatedMark ε n k)
    (fun α => truncatedMark_nonneg ε α n j) (fun α => truncatedMark_nonneg ε α n k)
    m (fun α => truncatedMark_le_two_pow ε hε hε1 α n j)
    (fun α => truncatedMark_le_two_pow ε hε hε1 α n k)
    hK.le hC₀.le
    (truncatedMark_restrict_tail htail ε n j)
    (truncatedMark_restrict_tail htail ε n k)
    (truncatedMark_restrict_joint_tail hjt ε n j k hjk)
  refine le_trans hmain ?_
  set u : ℝ := 1 + Real.log (2 + Lnorm n) with hu
  have hu1 : (1:ℝ) ≤ u := one_le_logFactor n
  have hmu : ((m : ℝ) + 1) ≤ 2 * u := dyDepth_succ_le n
  have hmnn : (0:ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hu2 : u ≤ u ^ 2 := by nlinarith
  have hone : (1:ℝ) ≤ u ^ 2 := by nlinarith
  have hA1 := mul_le_mul_of_nonneg_left hmu (by positivity : (0:ℝ) ≤ 2 * K)
  have hA2 := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ 4 * K)
  have hAe : 2 * K * (2 * u) = 4 * K * u := by ring
  have hBsq : ((m : ℝ) + 1) ^ 2 ≤ (2 * u) ^ 2 := pow_le_pow_left₀ hmnn hmu 2
  have hB1 := mul_le_mul_of_nonneg_left hBsq hC₀.le
  have hBe : C₀ * (2 * u) ^ 2 = 4 * C₀ * u ^ 2 := by ring
  have hfin : (1 + 4 * K + 4 * C₀) * u ^ 2 = u ^ 2 + 4 * K * u ^ 2 + 4 * C₀ * u ^ 2 := by ring
  rw [hAe] at hA1
  rw [hBe] at hB1
  rw [hfin]
  linarith

/-- The companion first moment: `E Z^{(ε)}_{n,j} ≤ C log(2+L)`. -/
theorem truncatedMark_first_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (n j : ℕ),
      (∫ α in Ioo (0:ℝ) 1, truncatedMark ε α n j)
        ≤ C * (1 + Real.log (2 + Lnorm n)) := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨K, hK, htail⟩ := L2Estimate.mark_tail_bound
  refine ⟨1 + 2 * K, by positivity, ?_⟩
  intro ε hε hε1 n j
  set m := dyDepth n with hm
  have hmain := integral_le_of_tail (ν := volume.restrict (Ioo (0:ℝ) 1))
    (X := fun α => truncatedMark ε α n j)
    (measurable_truncatedMark ε n j) (fun α => truncatedMark_nonneg ε α n j)
    m (fun α => truncatedMark_le_two_pow ε hε hε1 α n j) hK.le
    (truncatedMark_restrict_tail htail ε n j)
  refine le_trans hmain ?_
  set u : ℝ := 1 + Real.log (2 + Lnorm n) with hu
  have hu1 : (1:ℝ) ≤ u := one_le_logFactor n
  have hmu : ((m : ℝ) + 1) ≤ 2 * u := dyDepth_succ_le n
  have hA1 := mul_le_mul_of_nonneg_left hmu hK.le
  have hAe : K * (2 * u) = 2 * K * u := by ring
  have hfin : (1 + 2 * K) * u = u + 2 * K * u := by ring
  rw [hAe] at hA1
  rw [hfin]
  linarith

/-! ### 5. The per-pair covariance bound -/

lemma bulkTerm_nonneg (c ε : ℝ) (α : ℝ) (n j : ℕ) : 0 ≤ bulkTerm c ε α n j := by
  unfold bulkTerm
  split_ifs with h
  · exact truncatedMark_div_nonneg ε α n j
  · exact le_rfl

lemma bulkTerm_le_div (c ε : ℝ) (α : ℝ) (n j : ℕ) :
    bulkTerm c ε α n j ≤ truncatedMark ε α n j / Lnorm n := by
  unfold bulkTerm
  split_ifs with h
  · exact le_rfl
  · exact truncatedMark_div_nonneg ε α n j

lemma integrable_bulkTerm (c ε : ℝ) (hε : 0 < ε) (n j : ℕ) :
    Integrable (fun α : ℝ => bulkTerm c ε α n j) (volume.restrict (Ioo (0:ℝ) 1)) :=
  integrable_of_bound (measurable_bulkTerm c ε n j)
    (fun α => abs_bulkTerm_le c ε hε.le α n j)

lemma integrable_bulkTerm_mul (c ε : ℝ) (hε : 0 < ε) (n j k : ℕ) :
    Integrable (fun α : ℝ => bulkTerm c ε α n j * bulkTerm c ε α n k)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
  refine integrable_of_bound
    ((measurable_bulkTerm c ε n j).mul (measurable_bulkTerm c ε n k)) (M := ε * ε) ?_
  intro α
  rw [abs_mul]
  exact mul_le_mul (abs_bulkTerm_le c ε hε.le α n j) (abs_bulkTerm_le c ε hε.le α n k)
    (abs_nonneg _) (le_trans (abs_nonneg _) (abs_bulkTerm_le c ε hε.le α n j))

lemma integrable_truncatedMark_div (ε : ℝ) (hε : 0 < ε) (n j : ℕ) :
    Integrable (fun α : ℝ => truncatedMark ε α n j / Lnorm n)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
  refine integrable_of_bound
    ((measurable_truncatedMark ε n j).div measurable_const) (M := ε) ?_
  intro α
  rw [abs_of_nonneg (truncatedMark_div_nonneg ε α n j)]
  exact truncatedMark_div_le ε hε.le α n j

lemma integrable_truncatedMark_mul_div (ε : ℝ) (hε : 0 < ε) (n j k : ℕ) :
    Integrable
      (fun α : ℝ => truncatedMark ε α n j * truncatedMark ε α n k / (Lnorm n) ^ 2)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
  refine integrable_of_bound
    (((measurable_truncatedMark ε n j).mul (measurable_truncatedMark ε n k)).div
      measurable_const) (M := ε * ε) ?_
  intro α
  have heq : truncatedMark ε α n j * truncatedMark ε α n k / (Lnorm n) ^ 2
      = (truncatedMark ε α n j / Lnorm n) * (truncatedMark ε α n k / Lnorm n) := by
    rw [div_mul_div_comm, sq]
  rw [heq, abs_mul, abs_of_nonneg (truncatedMark_div_nonneg ε α n j),
    abs_of_nonneg (truncatedMark_div_nonneg ε α n k)]
  exact mul_le_mul (truncatedMark_div_le ε hε.le α n j) (truncatedMark_div_le ε hε.le α n k)
    (truncatedMark_div_nonneg ε α n k) hε.le

/-- The covariance is the second mixed moment minus the product of means. -/
lemma centered_pair_integral (c ε : ℝ) (hε : 0 < ε) (n j k : ℕ) :
    (∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
      = (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j * bulkTerm c ε α n k)
        - (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j)
          * (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n k) := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hIj := integrable_bulkTerm c ε hε n j
  have hIk := integrable_bulkTerm c ε hε n k
  have hIjk := integrable_bulkTerm_mul c ε hε n j k
  set a : ℝ := ∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j with ha
  set b : ℝ := ∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n k with hb
  have hdefj : ∀ α : ℝ, bulkTermCentered c ε α n j = bulkTerm c ε α n j - a := fun α => rfl
  have hdefk : ∀ α : ℝ, bulkTermCentered c ε α n k = bulkTerm c ε α n k - b := fun α => rfl
  have e1 : (∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
      = ∫ α in Ioo (0:ℝ) 1,
          ((bulkTerm c ε α n j * bulkTerm c ε α n k - b * bulkTerm c ε α n j
            - a * bulkTerm c ε α n k) + a * b) := by
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    dsimp only
    rw [hdefj α, hdefk α]
    ring
  have hcst : (∫ _α in Ioo (0:ℝ) 1, a * b) = a * b := by simp
  have e2 : (∫ α in Ioo (0:ℝ) 1, ((bulkTerm c ε α n j * bulkTerm c ε α n k
        - b * bulkTerm c ε α n j - a * bulkTerm c ε α n k) + a * b))
      = (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j * bulkTerm c ε α n k
          - b * bulkTerm c ε α n j - a * bulkTerm c ε α n k))
        + ∫ _α in Ioo (0:ℝ) 1, a * b :=
    integral_add ((hIjk.sub (hIj.const_mul b)).sub (hIk.const_mul a)) (integrable_const _)
  have e3 : (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j * bulkTerm c ε α n k
        - b * bulkTerm c ε α n j - a * bulkTerm c ε α n k))
      = (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j * bulkTerm c ε α n k
          - b * bulkTerm c ε α n j))
        - ∫ α in Ioo (0:ℝ) 1, a * bulkTerm c ε α n k :=
    integral_sub (hIjk.sub (hIj.const_mul b)) (hIk.const_mul a)
  have e4 : (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j * bulkTerm c ε α n k
        - b * bulkTerm c ε α n j))
      = (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j * bulkTerm c ε α n k)
        - ∫ α in Ioo (0:ℝ) 1, b * bulkTerm c ε α n j :=
    integral_sub hIjk (hIj.const_mul b)
  have e5 : (∫ α in Ioo (0:ℝ) 1, b * bulkTerm c ε α n j) = b * a := by
    rw [integral_const_mul, ← ha]
  have e6 : (∫ α in Ioo (0:ℝ) 1, a * bulkTerm c ε α n k) = a * b := by
    rw [integral_const_mul, ← hb]
  rw [e1, e2, e3, e4, e5, e6, hcst]
  ring

/-- **Display (42) after normalization**: for `j ≠ k` the covariance of the
`j`-th and `k`-th bulk summands is `O(log²(2+L)/L²)`. -/
theorem bulkTermCentered_offdiag_bound (c : ℝ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (n j k : ℕ), j ≠ k → 0 < Lnorm n →
      |∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|
        ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C₁, hC₁, hjm⟩ := truncatedMark_joint_moment
  obtain ⟨C₂, hC₂, hfm⟩ := truncatedMark_first_moment
  refine ⟨C₁ + C₂ ^ 2, by positivity, ?_⟩
  intro ε hε hε1 n j k hjk hL
  set U : ℝ := 1 + Real.log (2 + Lnorm n) with hU
  set Q : ℝ := U ^ 2 / (Lnorm n) ^ 2 with hQ
  have hQ0 : (0:ℝ) ≤ Q := by
    have : (0:ℝ) ≤ U := by rw [hU]; linarith [log_shift_pos n]
    rw [hQ]; positivity
  -- the mixed second moment
  have hP0 : (0:ℝ) ≤ ∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j * bulkTerm c ε α n k :=
    integral_nonneg fun α => mul_nonneg (bulkTerm_nonneg c ε α n j) (bulkTerm_nonneg c ε α n k)
  have hPstep : (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j * bulkTerm c ε α n k)
      ≤ (∫ α in Ioo (0:ℝ) 1, truncatedMark ε α n j * truncatedMark ε α n k)
          / (Lnorm n) ^ 2 := by
    rw [← integral_div]
    refine integral_mono (integrable_bulkTerm_mul c ε hε n j k)
      (integrable_truncatedMark_mul_div ε hε n j k) fun α => ?_
    have heq : truncatedMark ε α n j * truncatedMark ε α n k / (Lnorm n) ^ 2
        = (truncatedMark ε α n j / Lnorm n) * (truncatedMark ε α n k / Lnorm n) := by
      rw [div_mul_div_comm, sq]
    rw [heq]
    exact mul_le_mul (bulkTerm_le_div c ε α n j) (bulkTerm_le_div c ε α n k)
      (bulkTerm_nonneg c ε α n k) (truncatedMark_div_nonneg ε α n j)
  have hPle : (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j * bulkTerm c ε α n k) ≤ C₁ * Q := by
    refine le_trans hPstep ?_
    have h1 := hjm ε hε hε1 n j k hjk
    have hL2 : (0:ℝ) < (Lnorm n) ^ 2 := by positivity
    rw [hQ, div_le_iff₀ hL2]
    have heq : C₁ * (U ^ 2 / (Lnorm n) ^ 2) * (Lnorm n) ^ 2 = C₁ * U ^ 2 := by
      field_simp
    rw [heq]
    exact h1
  -- the means
  have hmean : ∀ i : ℕ, (0:ℝ) ≤ (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n i)
      ∧ (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n i) ≤ C₂ * U / Lnorm n := by
    intro i
    refine ⟨integral_nonneg fun α => bulkTerm_nonneg c ε α n i, ?_⟩
    have hstep : (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n i)
        ≤ (∫ α in Ioo (0:ℝ) 1, truncatedMark ε α n i) / Lnorm n := by
      rw [← integral_div]
      exact integral_mono (integrable_bulkTerm c ε hε n i)
        (integrable_truncatedMark_div ε hε n i) fun α => bulkTerm_le_div c ε α n i
    refine le_trans hstep ?_
    rw [div_le_div_iff₀ hL hL]
    nlinarith [hfm ε hε hε1 n i, hL]
  obtain ⟨ha0, hale⟩ := hmean j
  obtain ⟨hb0, hble⟩ := hmean k
  have hr0 : (0:ℝ) ≤ C₂ * U / Lnorm n := le_trans ha0 hale
  have hab : (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j)
      * (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n k) ≤ C₂ ^ 2 * Q := by
    have h1 : (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j)
        * (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n k)
        ≤ (C₂ * U / Lnorm n) * (C₂ * U / Lnorm n) :=
      mul_le_mul hale hble hb0 hr0
    have h2 : (C₂ * U / Lnorm n) * (C₂ * U / Lnorm n) = C₂ ^ 2 * Q := by
      rw [hQ]
      field_simp
    linarith [h1, h2.le, h2.ge]
  have habs : (0:ℝ) ≤ (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n j)
      * (∫ α in Ioo (0:ℝ) 1, bulkTerm c ε α n k) := mul_nonneg ha0 hb0
  rw [centered_pair_integral c ε hε n j k]
  have hgoal : (C₁ + C₂ ^ 2) * U ^ 2 / (Lnorm n) ^ 2 = (C₁ + C₂ ^ 2) * Q := by
    rw [hQ]; ring
  rw [hgoal]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [hC₁.le, hC₂.le, hQ0, hP0, hPle, hab, habs]

/-! ### 6. The `O(LH)` near-pair contribution is `o(1)` -/

lemma near_pair_decay (κ Cp δ : ℝ) (hκ : 0 < κ) (hCp : 0 < Cp) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (κ * Lnorm n * Hscale n)
          * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) ≤ δ := by
  have hLtop : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun n : ℕ => (Lnorm n) ^ (-(1/8) : ℝ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).comp hLtop
  have hpow : Tendsto (fun n : ℕ => κ * Cp * 1089 * (Lnorm n) ^ (-(1/8) : ℝ))
      atTop (nhds 0) := by
    simpa using h0.const_mul (κ * Cp * 1089)
  have hev1 : ∀ᶠ n : ℕ in atTop, κ * Cp * 1089 * (Lnorm n) ^ (-(1/8) : ℝ) < δ :=
    hpow.eventually_lt_const hδ
  have hev2 : ∀ᶠ n : ℕ in atTop, (1:ℝ) ≤ Lnorm n := hLtop.eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev1.and hev2)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hd1, hd2⟩ := hN n hn
  refine le_trans ?_ hd1.le
  set U : ℝ := 1 + Real.log (2 + Lnorm n) with hU
  set L : ℝ := Lnorm n with hLdef
  have hL0 : (0:ℝ) < L := by linarith
  set v : ℝ := L ^ (1/16 : ℝ) with hv
  have hv0 : (0:ℝ) < v := Real.rpow_pos_of_pos hL0 _
  have hvne : v ≠ 0 := ne_of_gt hv0
  have hv1 : (1:ℝ) ≤ v := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hd2 (by norm_num : (0:ℝ) ≤ 1/16)
    simpa [Real.one_rpow, hv] using h
  have hLv : L = v ^ (16:ℕ) := by
    rw [hv, ← Real.rpow_natCast (L ^ (1/16:ℝ)) 16, ← Real.rpow_mul hL0.le]
    norm_num
  have hHv : Hscale n = v ^ (12:ℕ) := by
    rw [Hscale, ← hLdef, hv, ← Real.rpow_natCast (L ^ (1/16:ℝ)) 12, ← Real.rpow_mul hL0.le]
    norm_num
  have hv2 : v ^ (2:ℕ) = L ^ (1/8 : ℝ) := by
    rw [hv, ← Real.rpow_natCast (L ^ (1/16:ℝ)) 2, ← Real.rpow_mul hL0.le]
    norm_num
  have hnegE : L ^ (-(1/8):ℝ) = (v ^ (2:ℕ))⁻¹ := by
    rw [Real.rpow_neg hL0.le, ← hv2]
  -- the logarithm is dominated by `33 v`
  have hU1 : (1:ℝ) ≤ U := by rw [hU]; linarith [log_shift_pos n]
  have hUv : U ≤ 33 * v := by
    have hlog := Real.log_le_rpow_div (x := 2 + L) (by linarith)
      (show (0:ℝ) < 1/16 by norm_num)
    have hdiv : (2 + L) ^ (1/16:ℝ) / (1/16:ℝ) = 16 * (2 + L) ^ (1/16:ℝ) := by ring
    rw [hdiv] at hlog
    have h3L : (2:ℝ) + L ≤ 3 * L := by linarith
    have hmono : (2 + L) ^ (1/16:ℝ) ≤ (3 * L) ^ (1/16:ℝ) :=
      Real.rpow_le_rpow (by linarith) h3L (by norm_num)
    have hsplit : (3 * L) ^ (1/16:ℝ) = (3:ℝ) ^ (1/16:ℝ) * v := by
      rw [Real.mul_rpow (by norm_num) hL0.le, hv]
    have h3 : (3:ℝ) ^ (1/16:ℝ) ≤ 2 := by
      have h65 : (3:ℝ) ≤ 65536 := by norm_num
      have hle := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 3) h65
        (by norm_num : (0:ℝ) ≤ 1/16)
      have he : (65536:ℝ) ^ (1/16:ℝ) = 2 := by
        rw [show (65536:ℝ) = (2:ℝ) ^ (16:ℕ) by norm_num,
          ← Real.rpow_natCast (2:ℝ) 16, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [he] at hle
      exact hle
    have step2 : 16 * (2 + L) ^ (1/16:ℝ) ≤ 16 * ((3:ℝ) ^ (1/16:ℝ) * v) := by
      rw [← hsplit]; linarith
    have step3 : 16 * ((3:ℝ) ^ (1/16:ℝ) * v) ≤ 32 * v := by nlinarith [hv0.le]
    linarith
  have husq : U ^ 2 ≤ 1089 * v ^ (2:ℕ) := by nlinarith [hUv, hU1, hv0.le]
  rw [hHv, hnegE, hLv]
  have hLHS : κ * (v ^ (16:ℕ)) * (v ^ (12:ℕ)) * (Cp * U ^ 2 / (v ^ (16:ℕ)) ^ 2)
      = κ * Cp * U ^ 2 / v ^ (4:ℕ) := by
    field_simp
  have hRHS : κ * Cp * 1089 * ((v ^ (2:ℕ))⁻¹) = κ * Cp * 1089 / v ^ (2:ℕ) := by
    field_simp
  rw [hLHS, hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey := mul_le_mul_of_nonneg_left husq
    (show (0:ℝ) ≤ κ * Cp * v ^ (2:ℕ) by positivity)
  nlinarith [hkey]

/-! ### 7. Proposition 4.1 as the far-pair input, and the assembly -/

/-- The `(j,k)` summand of the off-diagonal double sum of (41). -/
def offdiagTerm (c ε : ℝ) (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 = p.2 then 0 else
    ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2

lemma sum_offdiag_eq (c ε : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        (if j = k then 0 else
          ∫ α in Ioo (0:ℝ) 1,
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
      = ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), offdiagTerm c ε n p := by
  rw [Finset.sum_product]
  simp only [offdiagTerm]

/-- **The one remaining input**, Proposition 4.1 for pairs, in exactly the
form the manuscript's proof of Lemma 5.2 uses it (display (41), the
sentences after (42)).

The manuscript discards a set `B` of *overlapping*, `H`-near and
*resonance-near* pairs, of cardinality `O(LH)`, the same `O(L·H)` count as
`Kwon1002.prop_4_2_two_block_factorization` and
`Kwon1002.two_block_monomial_core` produce, and for the remaining pairs
cuts each digit at `A_L = L^D` (`D > 2`), applies Jackson approximation to
the Lipschitz truncation, and invokes **Proposition 4.1** with `A` so large
that `L² O_A(L^{-A}) = o(1)`.  That is what makes the surviving covariances
sum to `o(L²)`, i.e. (after the `1/L²` normalization already carried by
`bulkTermCentered`) to at most `ε/2` for all large `n`.

Not provable here: `Kwon1002.prop_4_1_marked_factorization`
(`Kwon1002/Section4.lean`, display (30)) and
`Kwon1002.Prop41.prop_4_1_error_shape` are themselves `sorry`-proved.  The
complementary half, that the `O(LH)` discarded pairs contribute `o(1)` -
is **proved** above (`bulkTermCentered_offdiag_bound` = display (42)'s
second half, and `near_pair_decay`). -/
theorem bulk_offdiagonal_far (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagTerm c ε n p ≤ ε / 2 := by
  sorry

/-- **The target**: `Kwon1002.L2Estimate.bulk_offdiagonal_input`, reproduced
token for token (line 577 of `Kwon1002/L2Estimate.lean`). -/
theorem bulk_offdiagonal_input' (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            ∫ α in Ioo (0:ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k) ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hpair⟩ := bulkTermCentered_offdiag_bound c
  obtain ⟨κ, hκ, hfar⟩ := bulk_offdiagonal_far c
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hfar ε hε hε1
  obtain ⟨N₂, hN₂⟩ := near_pair_decay κ Cp (ε / 2) hκ hCp (by positivity)
  refine ⟨max (max N₁ N₂) 3, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨B, hBcard, hBfar⟩ := hN₁ n hn1
  rw [sum_offdiag_eq c ε n]
  set P : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hP
  have hsplit : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagTerm c ε n p)
      + ∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagTerm c ε n p
      = ∑ p ∈ P, offdiagTerm c ε n p :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ∈ B) _
  have hnotB : P.filter (fun p => ¬ p ∈ B) = P \ B := (Finset.sdiff_eq_filter P B).symm
  have hQ0 : (0:ℝ) ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by positivity
  have hbound : ∀ p ∈ P.filter (fun p => p ∈ B),
      offdiagTerm c ε n p ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by
    intro p _
    simp only [offdiagTerm]
    by_cases hpq : p.1 = p.2
    · rw [if_pos hpq]
      exact hQ0
    · rw [if_neg hpq]
      exact le_trans (le_abs_self _) (hpair ε hε hε1 n p.1 p.2 hpq hL)
  have hnear : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagTerm c ε n p) ≤ ε / 2 := by
    have hb := Finset.sum_le_card_nsmul (P.filter (fun p => p ∈ B)) (offdiagTerm c ε n)
      (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) hbound
    rw [nsmul_eq_mul] at hb
    refine le_trans hb ?_
    have hcard : (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ) ≤ κ * Lnorm n * Hscale n := by
      refine le_trans ?_ hBcard
      exact_mod_cast Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).2)
    calc (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2)
        ≤ (κ * Lnorm n * Hscale n)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard hQ0
      _ ≤ ε / 2 := hN₂ n hn2
  have hfarsum : (∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagTerm c ε n p) ≤ ε / 2 := by
    rw [hnotB]
    exact hBfar
  linarith [hsplit, hnear, hfarsum]

/-- **Consequence**: `Kwon1002.truncatedBulkSum_centered_L2`, reproduced token
for token (line 504 of `Kwon1002/SmallJumps.lean`), now resting only on
`bulk_offdiagonal_far`. -/
theorem truncatedBulkSum_centered_L2' (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ b : ℝ,
        (∫ α in Ioo (0 : ℝ) 1,
            (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
          ≤ C * ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C₂, hC₂, hsm⟩ := L2Estimate.truncatedMark_second_moment
  obtain ⟨κ, hκ, hwin⟩ := L2Estimate.bulk_window_input c
  refine ⟨κ * C₂ + 2, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hwin ε hε hε1
  obtain ⟨N₂, hN₂⟩ := bulk_offdiagonal_input' c ε hε hε1
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨S, hSsub, hScard, hStail⟩ := hN₁ n hn1
  refine ⟨∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0:ℝ) 1, bulkTerm c ε β n j, ?_⟩
  rw [integral_centered_eq, centered_second_moment_expand c ε hε.le n]
  refine le_trans (le_of_eq (L2Estimate.sum_split_diag (n + 1) (fun j k =>
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k))) ?_
  have hoff := hN₂ n hn2
  have hdiagterm : ∀ j : ℕ,
      (∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2 :=
    fun j => L2Estimate.diagonal_le_second_moment c ε hε n j
  have hSbound : (∑ j ∈ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε := by
    calc (∑ j ∈ S,
        ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∑ _j ∈ S, (C₂ * ε / Lnorm n) := by
          refine Finset.sum_le_sum fun j _ => le_trans (hdiagterm j) ?_
          exact L2Estimate.bulkTerm_sq_integral_le c ε hε n j hL C₂ (hsm ε hε.le n j)
      _ = (S.card : ℝ) * (C₂ * ε / Lnorm n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (κ * Lnorm n) * (C₂ * ε / Lnorm n) := by
          refine mul_le_mul_of_nonneg_right hScard ?_
          have : (0:ℝ) ≤ C₂ * ε := by positivity
          positivity
      _ = κ * C₂ * ε := by field_simp
  have hRestBound : (∑ j ∈ Finset.range (n + 1) \ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ ε :=
    le_trans (Finset.sum_le_sum fun j _ => hdiagterm j) hStail
  have hdiag : (∑ j ∈ Finset.range (n + 1),
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε + ε := by
    rw [← Finset.sum_sdiff hSsub]
    linarith [hSbound, hRestBound]
  have hfinal : κ * C₂ * ε + ε + ε ≤ (κ * C₂ + 2) * ε := le_of_eq (by ring)
  linarith [hdiag, hoff, hfinal]

end

end OffDiag

end Kwon1002
