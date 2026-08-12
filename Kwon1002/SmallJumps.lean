import Kwon1002.PoissonLimit
import Kwon1002.GaussEstimates

/-!
# L52, Lemma 5.2 (small jumps), display (41)

Target: `small_jumps_variance` of `Kwon1002/PoissonLimit.lean`, reproduced
here verbatim as `small_jumps_variance`.

What is **proved** here:

* the pointwise arithmetic of the truncated mark (`0 ≤ Z^{(ε)} ≤ εL`,
  `mark ≤ a/8`, the "`W ≤ 1/8`" input of the manuscript proof);
* measurability of the whole mark chain in `α`
  (`gaussIter`, `digit`, `betaProd`, `theta`, `W`, `mark`, `truncatedMark`),
  of `heightSeq`, and of the stopping time `τ_n` (hence of the random
  index set `J_n`), no measurability input is assumed;
* `stoppingTime α n ≤ n` for irrational `α ∈ (0,1)`, hence
  `bulkIndices c α n ⊆ range (n+1)`, hence the random-index-set sum equals
  a sum over the *deterministic* range `{0,…,n}` a.e.;
* from that, `MemLp 2` of the truncated bulk sum (it is bounded by
  `(n+1)ε`);
* the covariance expansion `E[(Σ_j g_j - Σ_j E g_j)²] = Σ_{j,k} Cov(g_j,g_k)`
  over that deterministic range, the "diagonal + pairs" split the
  manuscript proof works with;
* the variational inequality `Var(X) ≤ E[(X - b)²]` for every constant `b`
  on a probability space, this is what lets §5's explicit centering be
  used in place of the mean;
* `small_jumps_variance` itself, from the single input below.

What remains **sorried**, and exactly why:

1. `truncatedBulkSum_centered_L2`, the analytic core of Lemma 5.2: there
   is a deterministic centering `b` with `E[(Σ_j Z^{(ε)}_{n,j}/L - b)²] ≤ Cε`.
   This is exactly (42) plus the pair count of the manuscript: the
   diagonal `E|U^{(ε)}_{n,j}|² ≤ CεL` (layer-cake integration of the
   uniform tail `P(Z_{n,j} > t) ≤ C/(1+t)`, which is `digit_tail_product`
   = Lem 3.1(ii) together with `W ≤ 1/8`), giving `O(εL²)`; the
   `O(LH log²L) = o(L²)` contribution of overlapping / `H`-near /
   resonance-near pairs; and the remaining covariances, killed by the
   digit cut at `A_L = L^D` (`D > 2`), Jackson approximation and
   Proposition 4.1. Proposition 4.1 is a §4 target that is not yet stated
   in this development, which is why this input cannot be discharged here.

Sorried results relied on: only the one above. `digit_tail_product` and
`shrinking_anti_concentration` (both sorried in `GaussEstimates`) are
*not* used by the proofs below, they are inputs to item 1, and are cited
in its docstring rather than consumed here.

Route from the remaining sorry to the estimate, all of it already built:
`integral_centered_eq` moves the centred second moment onto the
deterministic-range representative, and `centered_second_moment_expand`
turns it into `Σ_{j,k} Cov(g_j, g_k)` with `b = Σ_j E g_j`; what is left
is exactly (42) and the pair count.

## Manuscript note

`truncatedMark` (the shared file's `Z^{(ε)}`) is the **hard** truncation
`Z·1{Z ≤ εL}` and carries no `(-1)^j`, whereas the manuscript's (40) uses
the smooth cutoff `U^{(ε)}_{n,j} = (-1)^j Z_{n,j} χ(Z_{n,j}/(εL))`.
Neither difference weakens (41): the manuscript's proof bounds the
diagonal by `E|U|²` and the off-diagonal by `|Cov|`, and both bounds are
insensitive to the sign pattern and to replacing `zχ(z/(εL))` by
`z·1{z ≤ εL}` (the hard truncation is dominated by `2εL` in the same
way). The smooth `χ` is needed only for the Jackson-approximation step,
where the *Lipschitz* norm of `z ↦ zχ(z/(εL))` is used; a formalization
that keeps the hard truncation must instead exploit that
`z ↦ z·1{z ≤ εL}` is a monotone bounded function and approximate it in
`L¹` of the digit law. That is a real (if routine) extra step, and it is
worth recording as a divergence between the Lean file and (40).
-/

open Filter MeasureTheory Set

namespace Kwon1002

noncomputable section

/-! ### Elementary arithmetic of the truncated mark -/

lemma Lnorm_nonneg (n : ℕ) : 0 ≤ Lnorm n := by
  unfold Lnorm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hn)

lemma mark_nonneg (α : ℝ) (n j : ℕ) : 0 ≤ mark α n j :=
  mul_nonneg (Nat.cast_nonneg _) (W_nonneg _)

/-- `W ≤ 1/8` (the input the manuscript proof of Lem 5.2 opens with):
`Z_{n,j} ≤ a_{j+1}/8`. -/
lemma mark_le_digit_div_eight (α : ℝ) (n j : ℕ) :
    mark α n j ≤ (digit α j : ℝ) / 8 := by
  have hW := W_le_eighth (theta α n j)
  have hd : (0 : ℝ) ≤ (digit α j : ℝ) := Nat.cast_nonneg _
  unfold mark
  nlinarith

lemma truncatedMark_nonneg (ε α : ℝ) (n j : ℕ) : 0 ≤ truncatedMark ε α n j := by
  unfold truncatedMark
  split_ifs with h
  · exact mark_nonneg α n j
  · exact le_rfl

lemma truncatedMark_le (ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n j : ℕ) :
    truncatedMark ε α n j ≤ ε * Lnorm n := by
  unfold truncatedMark
  split_ifs with h
  · exact h
  · exact mul_nonneg hε (Lnorm_nonneg n)

lemma truncatedMark_div_nonneg (ε α : ℝ) (n j : ℕ) :
    0 ≤ truncatedMark ε α n j / Lnorm n :=
  div_nonneg (truncatedMark_nonneg ε α n j) (Lnorm_nonneg n)

lemma truncatedMark_div_le (ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n j : ℕ) :
    truncatedMark ε α n j / Lnorm n ≤ ε := by
  rcases (Lnorm_nonneg n).lt_or_eq with h | h
  · rw [div_le_iff₀ h]
    exact truncatedMark_le ε hε α n j
  · rw [← h, div_zero]
    exact hε

/-! ### Measurability of the mark chain -/

lemma measurable_gaussIter (j : ℕ) : Measurable fun α : ℝ => gaussIter α j := by
  induction j with
  | zero => simpa [gaussIter] using (measurable_id : Measurable fun α : ℝ => α)
  | succ j ih =>
      have h : (fun α : ℝ => gaussIter α (j + 1))
          = fun α : ℝ => Int.fract (gaussIter α j)⁻¹ := by
        funext α
        rw [gaussIter_succ]
        rfl
      rw [h]
      exact ih.inv.fract

lemma measurable_digitCast (j : ℕ) : Measurable fun α : ℝ => (digit α j : ℝ) := by
  have h : (fun α : ℝ => (digit α j : ℝ))
      = (fun z : ℤ => (z.toNat : ℝ)) ∘ fun α : ℝ => ⌊(gaussIter α j)⁻¹⌋ := by
    funext α; rfl
  rw [h]
  exact measurable_from_top.comp ((measurable_gaussIter j).inv.floor)

lemma measurable_betaProd (j : ℕ) : Measurable fun α : ℝ => betaProd α j := by
  unfold betaProd
  exact Finset.measurable_prod _ fun i _ => measurable_gaussIter i

lemma measurable_theta (n j : ℕ) : Measurable fun α : ℝ => theta α n j := by
  unfold theta
  exact (measurable_const.mul (measurable_betaProd j)).fract

lemma measurable_W : Measurable W := by
  unfold W
  exact (measurable_fract.mul (measurable_const.sub measurable_fract)).div measurable_const

lemma measurable_mark (n j : ℕ) : Measurable fun α : ℝ => mark α n j := by
  unfold mark
  exact (measurable_digitCast j).mul (measurable_W.comp (measurable_theta n j))

lemma measurable_truncatedMark (ε : ℝ) (n j : ℕ) :
    Measurable fun α : ℝ => truncatedMark ε α n j := by
  unfold truncatedMark
  exact Measurable.ite (measurableSet_le (measurable_mark n j) measurable_const)
    (measurable_mark n j) measurable_const

lemma measurable_heightSeq (n j : ℕ) : Measurable fun α : ℝ => heightSeq α n j := by
  induction j with
  | zero =>
      have h : (fun α : ℝ => heightSeq α n 0) = fun _ : ℝ => n := by
        funext α; rfl
      rw [h]
      exact measurable_const
  | succ j ih =>
      have hcast : Measurable fun α : ℝ => ((heightSeq α n j : ℕ) : ℝ) :=
        (measurable_from_top (f := fun m : ℕ => (m : ℝ))).comp ih
      have h : (fun α : ℝ => heightSeq α n (j + 1))
          = fun α : ℝ => (⌊((heightSeq α n j : ℕ) : ℝ) * gaussIter α j⌋).toNat := by
        funext α; rfl
      rw [h]
      exact (measurable_from_top (f := Int.toNat)).comp
        ((hcast.mul (measurable_gaussIter j)).floor)

/-- `sInf` of a set of naturals equals a positive `m` exactly when `m`
belongs and nothing below it does. -/
lemma sInf_eq_iff_pos {s : Set ℕ} {m : ℕ} (hm : 0 < m) :
    sInf s = m ↔ (m ∈ s ∧ ∀ k, k < m → k ∉ s) := by
  constructor
  · intro h
    have hne : s.Nonempty := Nat.nonempty_of_pos_sInf (by rw [h]; exact hm)
    refine ⟨h ▸ Nat.sInf_mem hne, fun k hk => Nat.notMem_of_lt_sInf (by rw [h]; exact hk)⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (Nat.sInf_le h1) ?_
    by_contra hlt
    push_neg at hlt
    exact h2 _ hlt (Nat.sInf_mem ⟨m, h1⟩)

/-- The stopping time `τ_n(α) = min {j : N_j(α) = 0}` is measurable in `α`:
`{α | τ_n = 0} = {N_0 = 0} ∪ ⋂_j {N_j ≠ 0}` and, for `m ≥ 1`,
`{α | τ_n = m} = {N_m = 0} ∩ ⋂_{k<m} {N_k ≠ 0}`. -/
theorem measurable_stoppingTime (n : ℕ) :
    Measurable fun α : ℝ => stoppingTime α n := by
  have hz : ∀ k : ℕ, MeasurableSet {α : ℝ | heightSeq α n k = 0} := by
    intro k
    have h : {α : ℝ | heightSeq α n k = 0} = (fun α : ℝ => heightSeq α n k) ⁻¹' {0} := rfl
    rw [h]
    exact measurable_heightSeq n k trivial
  refine measurable_to_countable' fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hset : (fun α : ℝ => stoppingTime α n) ⁻¹' {0}
        = {α : ℝ | heightSeq α n 0 = 0} ∪ ⋂ k : ℕ, {α : ℝ | heightSeq α n k = 0}ᶜ := by
      ext α
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_setOf_eq, stoppingTime]
      rw [Nat.sInf_eq_zero, Set.eq_empty_iff_forall_notMem]
      simp only [Set.mem_setOf_eq]
    rw [hset]
    exact (hz 0).union (MeasurableSet.iInter fun k => (hz k).compl)
  · have hset : (fun α : ℝ => stoppingTime α n) ⁻¹' {m}
        = {α : ℝ | heightSeq α n m = 0}
            ∩ ⋂ k : ℕ, ⋂ _ : k < m, {α : ℝ | heightSeq α n k = 0}ᶜ := by
      ext α
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_setOf_eq, stoppingTime]
      rw [sInf_eq_iff_pos hm]
      simp only [Set.mem_setOf_eq]
    rw [hset]
    exact (hz m).inter
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hz k).compl)

lemma measurableSet_mem_bulkIndices (c : ℝ) (n j : ℕ) :
    MeasurableSet {α : ℝ | j ∈ bulkIndices c α n} := by
  by_cases hc : c * Hscale n ≤ (j : ℝ)
  · have h : {α : ℝ | j ∈ bulkIndices c α n}
        = (fun α : ℝ => stoppingTime α n) ⁻¹' {m : ℕ | j < m} := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_preimage, bulkIndices, Finset.mem_filter,
        Finset.mem_range]
      simp [hc]
    rw [h]
    exact measurable_stoppingTime n trivial
  · have h : {α : ℝ | j ∈ bulkIndices c α n} = (∅ : Set ℝ) := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, bulkIndices, Finset.mem_filter,
        Finset.mem_range]
      simp [hc]
    rw [h]
    exact MeasurableSet.empty

/-! ### The bulk sum over a deterministic index range -/

/-- The truncated bulk sum rewritten over the deterministic range
`{0,…,n}`; equal to the real thing for irrational `α ∈ (0,1)` because
`τ_n(α) ≤ n`. -/
def truncatedBulkSumRange (c ε : ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (if j ∈ bulkIndices c α n then truncatedMark ε α n j / Lnorm n else 0)

lemma measurable_truncatedBulkSumRange (c ε : ℝ) (n : ℕ) :
    Measurable fun α : ℝ => truncatedBulkSumRange c ε α n := by
  unfold truncatedBulkSumRange
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_mem_bulkIndices c n j)
    ((measurable_truncatedMark ε n j).div measurable_const) measurable_const

lemma truncatedBulkSumRange_nonneg (c ε : ℝ) (α : ℝ) (n : ℕ) :
    0 ≤ truncatedBulkSumRange c ε α n := by
  simp only [truncatedBulkSumRange]
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact truncatedMark_div_nonneg ε α n j
  · exact le_rfl

lemma norm_truncatedBulkSumRange_le (c ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n : ℕ) :
    ‖truncatedBulkSumRange c ε α n‖ ≤ ((n : ℝ) + 1) * ε := by
  have h0 := truncatedBulkSumRange_nonneg c ε α n
  have h1 : truncatedBulkSumRange c ε α n ≤ ((n : ℝ) + 1) * ε := by
    have hstep : truncatedBulkSumRange c ε α n ≤ ∑ _j ∈ Finset.range (n + 1), ε := by
      simp only [truncatedBulkSumRange]
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h
      · exact truncatedMark_div_le ε hε α n j
      · exact hε
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hstep
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

lemma stoppingTime_le_self (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n : ℕ) : stoppingTime α n ≤ n :=
  Nat.sInf_le (heightSeq_self_eq_zero α hα hirr n)

lemma bulkIndices_subset_range (c α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n : ℕ) : bulkIndices c α n ⊆ Finset.range (n + 1) := by
  intro j hj
  have h1 : j ∈ Finset.range (stoppingTime α n) := Finset.mem_of_mem_filter j hj
  have h2 := Finset.mem_range.mp h1
  have h3 := stoppingTime_le_self α hα hirr n
  exact Finset.mem_range.mpr (by omega)

lemma truncatedBulkSum_eq_range (c ε α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n : ℕ) :
    (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n)
      = truncatedBulkSumRange c ε α n := by
  simp only [truncatedBulkSumRange]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (bulkIndices_subset_range c α hα hirr n)]

/-! ### The ambient probability space -/

lemma isProbabilityMeasure_restrict_Ioo :
    IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  simp

lemma ae_irrational_restrict :
    ∀ᵐ α ∂(volume.restrict (Ioo (0 : ℝ) 1)), Irrational α := by
  refine ae_restrict_of_ae ?_
  have hc : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have h0 : volume (Set.range ((↑) : ℚ → ℝ)) = 0 := hc.measure_zero volume
  have hset : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
    ext x
    simp [Irrational]
  rw [ae_iff, hset]
  exact h0

/-- Bridge: any centred second moment of the truncated bulk sum may be
computed with the deterministic-range representative. -/
lemma integral_centered_eq (c ε b : ℝ) (n : ℕ) :
    (∫ α in Ioo (0 : ℝ) 1,
        (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
      = ∫ α in Ioo (0 : ℝ) 1, (truncatedBulkSumRange c ε α n - b) ^ 2 := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict] with α hα hirr
  rw [truncatedBulkSum_eq_range c ε α hα hirr n]

/-- The truncated bulk sum is square-integrable on `(0,1)`: a.e. it is the
sum over the deterministic range `{0,…,n}`, hence measurable, and it lies
in `[0, (n+1)ε]`. -/
theorem truncatedBulkSum_memLp (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    MemLp (fun α : ℝ => ∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hae : (fun α : ℝ => ∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun α : ℝ => truncatedBulkSumRange c ε α n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict] with α hα hirr
    exact truncatedBulkSum_eq_range c ε α hα hirr n
  refine MemLp.of_bound
    (((measurable_truncatedBulkSumRange c ε n).aestronglyMeasurable).congr hae.symm)
    (((n : ℝ) + 1) * ε) ?_
  filter_upwards [hae] with α h
  rw [h]
  exact norm_truncatedBulkSumRange_le c ε hε α n

/-! ### The covariance expansion

The first structural step of the remaining estimate: over the
deterministic range the centred second moment *is* the double sum of
covariances, which is what the manuscript splits into "diagonal" and
"pairs". -/

/-- The `j`-th summand of the truncated bulk sum, extended by `0` off the
bulk. -/
def bulkTerm (c ε : ℝ) (α : ℝ) (n j : ℕ) : ℝ :=
  if j ∈ bulkIndices c α n then truncatedMark ε α n j / Lnorm n else 0

/-- The centred summand `g_j - E g_j`. -/
def bulkTermCentered (c ε : ℝ) (α : ℝ) (n j : ℕ) : ℝ :=
  bulkTerm c ε α n j - ∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j

lemma truncatedBulkSumRange_eq_sum (c ε α : ℝ) (n : ℕ) :
    truncatedBulkSumRange c ε α n = ∑ j ∈ Finset.range (n + 1), bulkTerm c ε α n j := rfl

lemma measurable_bulkTerm (c ε : ℝ) (n j : ℕ) :
    Measurable fun α : ℝ => bulkTerm c ε α n j := by
  unfold bulkTerm
  exact Measurable.ite (measurableSet_mem_bulkIndices c n j)
    ((measurable_truncatedMark ε n j).div measurable_const) measurable_const

lemma abs_bulkTerm_le (c ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n j : ℕ) :
    |bulkTerm c ε α n j| ≤ ε := by
  unfold bulkTerm
  split_ifs with h
  · rw [abs_of_nonneg (truncatedMark_div_nonneg ε α n j)]
    exact truncatedMark_div_le ε hε α n j
  · simpa using hε

lemma integrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ α, |f α| ≤ M) : Integrable f (volume.restrict (Ioo (0 : ℝ) 1)) := by
  haveI := isProbabilityMeasure_restrict_Ioo
  refine memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable M ?_)
  exact Eventually.of_forall fun α => by rw [Real.norm_eq_abs]; exact hM α

lemma abs_integral_bulkTerm_le (c ε : ℝ) (hε : 0 ≤ ε) (n j : ℕ) :
    |∫ α in Ioo (0 : ℝ) 1, bulkTerm c ε α n j| ≤ ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (C := ε)
    (f := fun α : ℝ => bulkTerm c ε α n j)
    (Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs]; exact abs_bulkTerm_le c ε hε α n j)
  simpa [Real.norm_eq_abs] using h

lemma measurable_bulkTermCentered (c ε : ℝ) (n j : ℕ) :
    Measurable fun α : ℝ => bulkTermCentered c ε α n j := by
  unfold bulkTermCentered
  exact (measurable_bulkTerm c ε n j).sub measurable_const

lemma abs_bulkTermCentered_le (c ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n j : ℕ) :
    |bulkTermCentered c ε α n j| ≤ 2 * ε := by
  have h1 := abs_le.mp (abs_bulkTerm_le c ε hε α n j)
  have h2 := abs_le.mp (abs_integral_bulkTerm_le c ε hε n j)
  unfold bulkTermCentered
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma integrable_bulkTermCentered_mul (c ε : ℝ) (hε : 0 ≤ ε) (n j k : ℕ) :
    Integrable (fun α : ℝ => bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine integrable_of_bound
    ((measurable_bulkTermCentered c ε n j).mul (measurable_bulkTermCentered c ε n k))
    (M := (2 * ε) * (2 * ε)) ?_
  intro α
  rw [abs_mul]
  exact mul_le_mul (abs_bulkTermCentered_le c ε hε α n j)
    (abs_bulkTermCentered_le c ε hε α n k) (abs_nonneg _) (by positivity)

/-- **Covariance expansion.** With the manuscript's centering
`b = Σ_j E g_j`, the centred second moment of the truncated bulk sum is
the double sum of covariances, the split into "diagonal" and "pairs"
that the proof of (41) works with. -/
theorem centered_second_moment_expand (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (∫ α in Ioo (0 : ℝ) 1,
        (truncatedBulkSumRange c ε α n
          - ∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j) ^ 2)
      = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          ∫ α in Ioo (0 : ℝ) 1,
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n k := by
  have hsum : ∀ α : ℝ, truncatedBulkSumRange c ε α n
      - ∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j
      = ∑ j ∈ Finset.range (n + 1), bulkTermCentered c ε α n j := by
    intro α
    simp only [truncatedBulkSumRange_eq_sum, bulkTermCentered, Finset.sum_sub_distrib]
  calc (∫ α in Ioo (0 : ℝ) 1,
        (truncatedBulkSumRange c ε α n
          - ∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j) ^ 2)
      = ∫ α in Ioo (0 : ℝ) 1, ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n k := by
        refine integral_congr_ae (Eventually.of_forall fun α => ?_)
        dsimp only
        rw [hsum α, sq, Finset.sum_mul_sum]
    _ = ∑ j ∈ Finset.range (n + 1), ∫ α in Ioo (0 : ℝ) 1, ∑ k ∈ Finset.range (n + 1),
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n k :=
        integral_finset_sum _ fun j _ =>
          integrable_finset_sum _ fun k _ => integrable_bulkTermCentered_mul c ε hε n j k
    _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            ∫ α in Ioo (0 : ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k :=
        Finset.sum_congr rfl fun j _ =>
          integral_finset_sum _ fun k _ => integrable_bulkTermCentered_mul c ε hε n j k

/-! ### The variance inequality -/

/-- On a probability space the mean minimizes the mean square deviation:
`∫ (f - E f)² ≤ ∫ (f - b)²` for every constant `b`. This is what allows
§5's explicit deterministic centering to be substituted for the mean. -/
lemma integral_sub_mean_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (b : ℝ)
    (hsq : Integrable (fun ω => (f ω - b) ^ 2) μ) :
    ∫ ω, (f ω - ∫ ω, f ω ∂μ) ^ 2 ∂μ ≤ ∫ ω, (f ω - b) ^ 2 ∂μ := by
  set m := ∫ ω, f ω ∂μ with hm
  have hconst : ∀ r : ℝ, ∫ _ω : Ω, r ∂μ = r := by
    intro r
    rw [integral_const]
    simp
  have hfb : Integrable (fun ω => f ω - b) μ := hf.sub (integrable_const b)
  have hlin : Integrable (fun ω => 2 * (m - b) * (f ω - b)) μ := hfb.const_mul _
  have hint2 : Integrable (fun ω => (f ω - b) ^ 2 - 2 * (m - b) * (f ω - b)) μ :=
    hsq.sub hlin
  have hint1 : ∫ ω, (f ω - b) ∂μ = m - b := by
    rw [integral_sub hf (integrable_const b), hconst, hm]
  have key : ∫ ω, (f ω - m) ^ 2 ∂μ
      = (∫ ω, (f ω - b) ^ 2 ∂μ) - 2 * (m - b) * (m - b) + (m - b) ^ 2 := by
    have e1 : ∫ ω, (f ω - m) ^ 2 ∂μ
        = ∫ ω, ((f ω - b) ^ 2 - 2 * (m - b) * (f ω - b) + (m - b) ^ 2) ∂μ := by
      congr 1
      funext ω
      ring
    rw [e1, integral_add hint2 (integrable_const _), hconst,
      integral_sub hsq hlin, integral_const_mul, hint1]
  rw [key]
  nlinarith [sq_nonneg (m - b)]

/-- **The single remaining sorried input**, the analytic core of Lemma 5.2, with the
manuscript's explicit deterministic centering `b` in place of the mean.

This is (42) plus the pair count: diagonal `E|U^{(ε)}_{n,j}|² ≤ CεL` by
layer-cake integration of `P(Z_{n,j} > t) ≤ C/(1+t)` (Lem 3.1(ii),
`digit_tail_product`, together with `W ≤ 1/8` =
`mark_le_digit_div_eight`), contributing `O(εL²)`; overlapping, `H`-near
and resonance-near pairs, `O(LH log²L) = o(L²)`; and the remaining
covariances, killed by the digit cut at `A_L = L^D` (`D > 2`), Jackson
approximation of the Lipschitz truncation, and Proposition 4.1. Prop 4.1
is a §4 target not yet stated in this development. -/
theorem truncatedBulkSum_centered_L2 (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ b : ℝ,
        (∫ α in Ioo (0 : ℝ) 1,
            (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
          ≤ C * ε := by
  sorry

/-! ### Lemma 5.2 -/

/-- **Lemma 5.2** (Small jumps), display (41), the statement of
`Kwon1002.small_jumps_variance`, reproduced verbatim. -/
theorem small_jumps_variance (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫ α in Ioo (0 : ℝ) 1,
            (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n
              - ∫ β in Ioo (0 : ℝ) 1,
                  ∑ j ∈ bulkIndices c β n, truncatedMark ε β n j / Lnorm n) ^ 2)
          ≤ C * ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C, hC, hmain⟩ := truncatedBulkSum_centered_L2 c
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨N, hN⟩ := hmain ε hε hε1
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨b, hb⟩ := hN n hn
  have hmem := truncatedBulkSum_memLp c ε hε.le n
  have hf : Integrable
      (fun α : ℝ => ∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n)
      (volume.restrict (Ioo (0 : ℝ) 1)) := hmem.integrable one_le_two
  have hsq : Integrable
      (fun α : ℝ => (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have := (hmem.sub (memLp_const b)).integrable_sq
    simpa using this
  exact le_trans (integral_sub_mean_sq_le hf b hsq) hb

end

end Kwon1002

