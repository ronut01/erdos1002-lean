import Kwon1002.StoppingWindow

/-!
# The window bridge in covariance currency

Every bridge the tree carries between the **random** §7 bulk
`Kwon1002.bulkIndices c α n` and the **deterministic** §4 bulk `Kwon1002.bulkJ n`
is stated for the measure of an *event*: `TupleFinal.bulk_window_bridge_tuple`,
`WindowBridgeFamily.exists_window_bridge_family`,
`DetQuasiFamily.exists_det_quasi_independence_family`,
`StepQuasi.exists_bulk_quasi_pattern` and `QuasiIndep.exists_tuple_bound_radii`
all speak in `unifIoo.real (tupleEvent …)`, and `MultiLevel.multiLevel_transfer`
speaks in the `α`-average of a product of indicators.

The off-diagonal sum of display (41) is not in that currency.  Its summand is
`|∫ g_j·g_k|` for the **centred** observable `g = bulkTermCentered`, and `g` is
`−E g_j` — not `0` — at the levels the random bulk omits.  So the random/
deterministic gap does not simply vanish outside the bulk the way it does for an
event indicator: the leakage is a nonzero constant at each level.

This module supplies the missing analogue.  The observation that makes it work is
that the leakage is *bounded*, not merely small in measure: `|bulkTerm| ≤ ε`
pointwise (`Kwon1002.abs_bulkTerm_le`), so the whole discrepancy between the
random-index and deterministic-index covariances is carried by the exceptional
set of `StoppingWindow`, on which nothing better than boundedness is needed.

* `detTerm`, `detTermCentered` — the deterministic-index twins of `bulkTerm`
  and `bulkTermCentered`, with `bulkJ n` in place of `bulkIndices c α n`.
* `bulkTerm_eq_detTerm` — off `StopWin.stopBad n` and off `StopWin.diffWindow c n`
  the two summands are *equal*, by `StopWin.mem_bulkIndices_iff`.
* `window_covariance_bridge` — hence the two covariances differ by at most
  `8·ε²·|stopBad n|`, which `StopWin.stopBad_measure_le` prices at
  `O(e^{−c√L})` — small enough to survive multiplication by the `O(L²)` pairs
  of the Lamé window (`StopWin.tendsto_Lnorm_mul_exp_neg_sqrt`).
* `abs_far_sharp_of_det_pair_decay` — the payoff: the statement of
  `Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` follows from a far-pair
  covariance decay stated **entirely over the deterministic bulk `bulkJ n`**,
  with no stopping time and no random index set anywhere in the hypothesis.
  That hypothesis is a §4 statement about the pair
  `(Z^{(ε)}_{n,j}, Z^{(ε)}_{n,k})`; the implication proved here is what carries
  it to §5's random-index display (41).

Nothing in this module is `sorry`ed, and nothing in it assumes the residual.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Kwon1002

namespace WindowCov

noncomputable section

/-! ## 1. The deterministic-index twin of the summand -/

/-- The `j`-th summand of (41) with the **deterministic** bulk `J_n` of display
(19) in place of the random `bulkIndices c α n`. -/
def detTerm (ε : ℝ) (α : ℝ) (n j : ℕ) : ℝ :=
  if j ∈ bulkJ n then truncatedMark ε α n j / Lnorm n else 0

/-- The centred deterministic-index summand `d_j − E d_j`. -/
def detTermCentered (ε : ℝ) (α : ℝ) (n j : ℕ) : ℝ :=
  detTerm ε α n j - ∫ β in Ioo (0 : ℝ) 1, detTerm ε β n j

lemma measurable_detTerm (ε : ℝ) (n j : ℕ) :
    Measurable fun α : ℝ => detTerm ε α n j := by
  unfold detTerm
  by_cases h : j ∈ bulkJ n
  · simp only [if_pos h]
    exact (measurable_truncatedMark ε n j).div measurable_const
  · simp only [if_neg h]
    exact measurable_const

lemma abs_detTerm_le (ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n j : ℕ) :
    |detTerm ε α n j| ≤ ε := by
  unfold detTerm
  split_ifs with h
  · rw [abs_of_nonneg (truncatedMark_div_nonneg ε α n j)]
    exact truncatedMark_div_le ε hε α n j
  · simpa using hε

lemma integrable_detTerm (ε : ℝ) (hε : 0 ≤ ε) (n j : ℕ) :
    Integrable (fun α : ℝ => detTerm ε α n j) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  integrable_of_bound (measurable_detTerm ε n j) (fun α => abs_detTerm_le ε hε α n j)

lemma abs_integral_detTerm_le (ε : ℝ) (hε : 0 ≤ ε) (n j : ℕ) :
    |∫ α in Ioo (0 : ℝ) 1, detTerm ε α n j| ≤ ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (C := ε)
    (f := fun α : ℝ => detTerm ε α n j)
    (Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs]; exact abs_detTerm_le ε hε α n j)
  simpa [Real.norm_eq_abs] using h

lemma measurable_detTermCentered (ε : ℝ) (n j : ℕ) :
    Measurable fun α : ℝ => detTermCentered ε α n j :=
  (measurable_detTerm ε n j).sub measurable_const

lemma abs_detTermCentered_le (ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n j : ℕ) :
    |detTermCentered ε α n j| ≤ 2 * ε := by
  unfold detTermCentered
  refine le_trans (abs_sub _ _) ?_
  linarith [abs_detTerm_le ε hε α n j, abs_integral_detTerm_le ε hε n j]

lemma measurable_bulkTermCentered (c ε : ℝ) (n j : ℕ) :
    Measurable fun α : ℝ => bulkTermCentered c ε α n j :=
  (measurable_bulkTerm c ε n j).sub measurable_const

lemma abs_bulkTermCentered_le (c ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n j : ℕ) :
    |bulkTermCentered c ε α n j| ≤ 2 * ε := by
  unfold bulkTermCentered
  refine le_trans (abs_sub _ _) ?_
  linarith [abs_bulkTerm_le c ε hε α n j, abs_integral_bulkTerm_le c ε hε n j]

/-- `detTerm` vanishes identically off the deterministic bulk, so the pair
covariance is carried by `bulkJ n × bulkJ n`. -/
lemma detTermCentered_eq_zero_of_not_mem (ε : ℝ) (n j : ℕ) (hj : j ∉ bulkJ n) (α : ℝ) :
    detTermCentered ε α n j = 0 := by
  have h0 : ∀ β : ℝ, detTerm ε β n j = 0 := by
    intro β; unfold detTerm; rw [if_neg hj]
  unfold detTermCentered
  simp only [h0, integral_zero, sub_zero]


/-! ## 2. The bridge at a single level

Off the exceptional set of `StoppingWindow` and off the `O(H)` window
`StopWin.diffWindow c n`, the random and deterministic summands are literally
equal.  Everywhere else they are merely both bounded by `ε`, and that is all the
argument uses. -/

/-- **The bridge, pointwise.**  `StopWin.mem_bulkIndices_iff` read at the level
of the summand rather than at the level of an event. -/
lemma bulkTerm_eq_detTerm (c ε : ℝ) (n j : ℕ) (hH : 0 ≤ Hscale n) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hgood : α ∉ StopWin.stopBad n)
    (hj : j ∉ StopWin.diffWindow c n) :
    bulkTerm c ε α n j = detTerm ε α n j := by
  unfold bulkTerm detTerm
  by_cases h : j ∈ bulkJ n
  · rw [if_pos h, if_pos ((StopWin.mem_bulkIndices_iff c n hH hgood hα hj).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((StopWin.mem_bulkIndices_iff c n hH hgood hα hj).mp hc))]

/-- A bounded measurable function supported (inside `(0,1)`) on a subset `S` of
`(0,1)` has `L¹` norm at most `M·|S|`.  This is the only measure-theoretic
device the bridge needs: the leakage is *bounded*, and it lives on `stopBad`. -/
lemma integral_abs_le_of_support_subset {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : 0 ≤ M) (hbd : ∀ α, |f α| ≤ M) {S : Set ℝ} (hSsub : S ⊆ Ioo (0 : ℝ) 1)
    (hsupp : ∀ α ∈ Ioo (0 : ℝ) 1, f α ≠ 0 → α ∈ S) :
    (∫ α in Ioo (0 : ℝ) 1, |f α|) ≤ M * (volume S).toReal := by
  classical
  haveI := isProbabilityMeasure_restrict_Ioo
  set T : Set ℝ := Ioo (0 : ℝ) 1 ∩ {α : ℝ | f α ≠ 0} with hT
  have hTmeas : MeasurableSet T := by
    refine measurableSet_Ioo.inter ?_
    have : {α : ℝ | f α ≠ 0} = (f ⁻¹' {0})ᶜ := by ext α; simp
    rw [this]
    exact (hf (measurableSet_singleton 0)).compl
  have hTS : T ⊆ S := by
    rintro α ⟨hα, hne⟩
    exact hsupp α hα hne
  have hTsub : T ⊆ Ioo (0 : ℝ) 1 := fun α hα => hα.1
  have hint1 : Integrable (fun α : ℝ => |f α|) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (integrable_of_bound hf hbd).abs
  have hint2 : Integrable (fun α : ℝ => M * T.indicator (fun _ => (1 : ℝ)) α)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine integrable_of_bound ((measurable_const.indicator hTmeas).const_mul M) (M := M) ?_
    intro α
    rw [abs_mul, abs_of_nonneg hM]
    have h1 : |T.indicator (fun _ => (1 : ℝ)) α| ≤ 1 := by
      unfold Set.indicator
      split_ifs <;> simp
    nlinarith
  have hmono : (∫ α in Ioo (0 : ℝ) 1, |f α|)
      ≤ ∫ α in Ioo (0 : ℝ) 1, M * T.indicator (fun _ => (1 : ℝ)) α := by
    refine integral_mono_ae hint1 hint2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with α hα
    by_cases hne : f α = 0
    · rw [hne]
      simp only [abs_zero]
      have : (0 : ℝ) ≤ T.indicator (fun _ => (1 : ℝ)) α :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) α
      nlinarith
    · have hmem : α ∈ T := ⟨hα, hne⟩
      rw [Set.indicator_of_mem hmem]
      simpa using hbd α
  refine le_trans hmono ?_
  rw [integral_const_mul, MeasureTheory.setIntegral_indicator hTmeas]
  have hcalc : (∫ _α in Ioo (0 : ℝ) 1 ∩ T, (1 : ℝ))
      = (volume (Ioo (0 : ℝ) 1 ∩ T)).toReal := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [hcalc]
  have hIT : Ioo (0 : ℝ) 1 ∩ T = T := Set.inter_eq_self_of_subset_right hTsub
  rw [hIT]
  have hStop : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hSsub)
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hle : (volume T).toReal ≤ (volume S).toReal :=
    ENNReal.toReal_mono hStop (measure_mono hTS)
  exact mul_le_mul_of_nonneg_left hle hM

/-- The `L¹` distance between the random-index and deterministic-index summands
is at most `2ε·|stopBad n|`. -/
lemma integral_abs_bulkTerm_sub_detTerm_le (c ε : ℝ) (hε : 0 ≤ ε) (n j : ℕ)
    (hH : 0 ≤ Hscale n) (hj : j ∉ StopWin.diffWindow c n) :
    (∫ α in Ioo (0 : ℝ) 1, |bulkTerm c ε α n j - detTerm ε α n j|)
      ≤ 2 * ε * (volume (StopWin.stopBad n)).toReal := by
  refine integral_abs_le_of_support_subset
    ((measurable_bulkTerm c ε n j).sub (measurable_detTerm ε n j))
    (M := 2 * ε) (S := StopWin.stopBad n) (by linarith) ?_ ?_ ?_
  · intro α
    refine le_trans (abs_sub _ _) ?_
    linarith [abs_bulkTerm_le c ε hε α n j, abs_detTerm_le ε hε α n j]
  · rintro α ⟨hα, -⟩; exact hα
  · intro α hα hne
    by_contra hcon
    exact hne (by rw [bulkTerm_eq_detTerm c ε n j hH hα hcon hj, sub_self])

/-- …and hence so is the distance between the two centrings. -/
lemma abs_integral_bulkTerm_sub_detTerm_le (c ε : ℝ) (hε : 0 ≤ ε) (n j : ℕ)
    (hH : 0 ≤ Hscale n) (hj : j ∉ StopWin.diffWindow c n) :
    |(∫ α in Ioo (0 : ℝ) 1, bulkTerm c ε α n j)
        - ∫ α in Ioo (0 : ℝ) 1, detTerm ε α n j|
      ≤ 2 * ε * (volume (StopWin.stopBad n)).toReal := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hsub : (∫ α in Ioo (0 : ℝ) 1, bulkTerm c ε α n j)
      - ∫ α in Ioo (0 : ℝ) 1, detTerm ε α n j
      = ∫ α in Ioo (0 : ℝ) 1, (bulkTerm c ε α n j - detTerm ε α n j) :=
    (integral_sub (integrable_of_bound (measurable_bulkTerm c ε n j)
        (fun α => abs_bulkTerm_le c ε hε α n j)) (integrable_detTerm ε hε n j)).symm
  rw [hsub]
  refine le_trans (abs_integral_le_integral_abs) ?_
  exact integral_abs_bulkTerm_sub_detTerm_le c ε hε n j hH hj

/-- The centred summands are `4ε·|stopBad n|`-close in `L¹`. -/
lemma integral_abs_centered_sub_le (c ε : ℝ) (hε : 0 ≤ ε) (n j : ℕ)
    (hH : 0 ≤ Hscale n) (hj : j ∉ StopWin.diffWindow c n) :
    (∫ α in Ioo (0 : ℝ) 1,
        |bulkTermCentered c ε α n j - detTermCentered ε α n j|)
      ≤ 4 * ε * (volume (StopWin.stopBad n)).toReal := by
  haveI := isProbabilityMeasure_restrict_Ioo
  set m : ℝ := (volume (StopWin.stopBad n)).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hptw : ∀ α : ℝ,
      |bulkTermCentered c ε α n j - detTermCentered ε α n j|
        ≤ |bulkTerm c ε α n j - detTerm ε α n j| + 2 * ε * m := by
    intro α
    unfold bulkTermCentered detTermCentered
    have hrw : bulkTerm c ε α n j - (∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j)
        - (detTerm ε α n j - ∫ β in Ioo (0 : ℝ) 1, detTerm ε β n j)
        = (bulkTerm c ε α n j - detTerm ε α n j)
          - ((∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j)
              - ∫ β in Ioo (0 : ℝ) 1, detTerm ε β n j) := by ring
    rw [hrw]
    refine le_trans (abs_sub _ _) ?_
    linarith [abs_integral_bulkTerm_sub_detTerm_le c ε hε n j hH hj]
  have hintL : Integrable
      (fun α : ℝ => |bulkTermCentered c ε α n j - detTermCentered ε α n j|)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine (integrable_of_bound
      (((measurable_bulkTermCentered c ε n j).sub (measurable_detTermCentered ε n j)).abs)
      (M := 4 * ε) ?_)
    intro α
    rw [abs_abs]
    refine le_trans (abs_sub _ _) ?_
    linarith [abs_bulkTermCentered_le c ε hε α n j, abs_detTermCentered_le ε hε α n j]
  have hintR : Integrable
      (fun α : ℝ => |bulkTerm c ε α n j - detTerm ε α n j| + 2 * ε * m)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine Integrable.add ?_ (integrable_const _)
    exact (integrable_of_bound
      (((measurable_bulkTerm c ε n j).sub (measurable_detTerm ε n j)).abs)
      (M := 2 * ε) (fun α => by
        rw [abs_abs]
        refine le_trans (abs_sub _ _) ?_
        linarith [abs_bulkTerm_le c ε hε α n j, abs_detTerm_le ε hε α n j]))
  have hmono := integral_mono hintL hintR hptw
  have hconst : (∫ _α in Ioo (0 : ℝ) 1,
      (|bulkTerm c ε _α n j - detTerm ε _α n j| + 2 * ε * m))
      = (∫ α in Ioo (0 : ℝ) 1, |bulkTerm c ε α n j - detTerm ε α n j|) + 2 * ε * m := by
    rw [integral_add (integrable_of_bound
      (((measurable_bulkTerm c ε n j).sub (measurable_detTerm ε n j)).abs)
      (M := 2 * ε) (fun α => by
        rw [abs_abs]
        refine le_trans (abs_sub _ _) ?_
        linarith [abs_bulkTerm_le c ε hε α n j, abs_detTerm_le ε hε α n j]))
      (integrable_const _)]
    have hc : (∫ _a in Ioo (0 : ℝ) 1, (2 * ε * m)) = 2 * ε * m := by simp
    rw [hc]
  rw [hconst] at hmono
  linarith [integral_abs_bulkTerm_sub_detTerm_le c ε hε n j hH hj]


/-! ## 3. The bridge in covariance currency

The centred observable is what display (41) sums, and this is the statement the
tree did not contain in any currency. -/

/-- **The covariance-currency window bridge.**  At two levels outside the
`O(H)` window `StopWin.diffWindow c n`, the random-index covariance and the
deterministic-index covariance differ by at most `16ε²·|stopBad n|`.

`StopWin.stopBad_measure_le` prices `|stopBad n|` at `O(e^{−c√L})`, and
`StopWin.tendsto_Lnorm_mul_exp_neg_sqrt` shows that survives multiplication by
the `O(L²)` pairs of the Lamé window; so the whole random/deterministic gap in
(41) is `o(1)` uniformly in `ε ∈ (0,1)`. -/
theorem window_covariance_bridge (c ε : ℝ) (hε : 0 ≤ ε) (n j k : ℕ)
    (hH : 0 ≤ Hscale n) (hj : j ∉ StopWin.diffWindow c n)
    (hk : k ∉ StopWin.diffWindow c n) :
    |(∫ α in Ioo (0 : ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
        - ∫ α in Ioo (0 : ℝ) 1, detTermCentered ε α n j * detTermCentered ε α n k|
      ≤ 16 * ε ^ 2 * (volume (StopWin.stopBad n)).toReal := by
  haveI := isProbabilityMeasure_restrict_Ioo
  set m : ℝ := (volume (StopWin.stopBad n)).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hgint : ∀ i : ℕ, Integrable
      (fun α : ℝ => bulkTermCentered c ε α n i) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun i => integrable_of_bound (measurable_bulkTermCentered c ε n i)
      (fun α => abs_bulkTermCentered_le c ε hε α n i)
  have hdint : ∀ i : ℕ, Integrable
      (fun α : ℝ => detTermCentered ε α n i) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun i => integrable_of_bound (measurable_detTermCentered ε n i)
      (fun α => abs_detTermCentered_le ε hε α n i)
  have hprodg : Integrable
      (fun α : ℝ => bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine integrable_of_bound
      ((measurable_bulkTermCentered c ε n j).mul (measurable_bulkTermCentered c ε n k))
      (M := 4 * ε ^ 2) ?_
    intro α
    rw [abs_mul]
    nlinarith [abs_bulkTermCentered_le c ε hε α n j, abs_bulkTermCentered_le c ε hε α n k,
      abs_nonneg (bulkTermCentered c ε α n j), abs_nonneg (bulkTermCentered c ε α n k)]
  have hprodd : Integrable
      (fun α : ℝ => detTermCentered ε α n j * detTermCentered ε α n k)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine integrable_of_bound
      ((measurable_detTermCentered ε n j).mul (measurable_detTermCentered ε n k))
      (M := 4 * ε ^ 2) ?_
    intro α
    rw [abs_mul]
    nlinarith [abs_detTermCentered_le ε hε α n j, abs_detTermCentered_le ε hε α n k,
      abs_nonneg (detTermCentered ε α n j), abs_nonneg (detTermCentered ε α n k)]
  have hsub : (∫ α in Ioo (0 : ℝ) 1,
        bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
      - ∫ α in Ioo (0 : ℝ) 1, detTermCentered ε α n j * detTermCentered ε α n k
      = ∫ α in Ioo (0 : ℝ) 1,
          (bulkTermCentered c ε α n j * bulkTermCentered c ε α n k
            - detTermCentered ε α n j * detTermCentered ε α n k) :=
    (integral_sub hprodg hprodd).symm
  rw [hsub]
  refine le_trans abs_integral_le_integral_abs ?_
  -- the pointwise telescoping, then the two `L¹` legs
  have hptw : ∀ α : ℝ,
      |bulkTermCentered c ε α n j * bulkTermCentered c ε α n k
          - detTermCentered ε α n j * detTermCentered ε α n k|
        ≤ 2 * ε * |bulkTermCentered c ε α n k - detTermCentered ε α n k|
          + 2 * ε * |bulkTermCentered c ε α n j - detTermCentered ε α n j| := by
    intro α
    have hrw : bulkTermCentered c ε α n j * bulkTermCentered c ε α n k
        - detTermCentered ε α n j * detTermCentered ε α n k
        = bulkTermCentered c ε α n j
            * (bulkTermCentered c ε α n k - detTermCentered ε α n k)
          + detTermCentered ε α n k
            * (bulkTermCentered c ε α n j - detTermCentered ε α n j) := by ring
    rw [hrw]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    have h1 := abs_bulkTermCentered_le c ε hε α n j
    have h2 := abs_detTermCentered_le ε hε α n k
    have h3 : (0 : ℝ) ≤ |bulkTermCentered c ε α n k - detTermCentered ε α n k| :=
      abs_nonneg _
    have h4 : (0 : ℝ) ≤ |bulkTermCentered c ε α n j - detTermCentered ε α n j| :=
      abs_nonneg _
    nlinarith
  have hLint : Integrable
      (fun α : ℝ => |bulkTermCentered c ε α n j * bulkTermCentered c ε α n k
          - detTermCentered ε α n j * detTermCentered ε α n k|)
      (volume.restrict (Ioo (0 : ℝ) 1)) := (hprodg.sub hprodd).abs
  have hDint : ∀ i : ℕ, Integrable
      (fun α : ℝ => |bulkTermCentered c ε α n i - detTermCentered ε α n i|)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun i => ((hgint i).sub (hdint i)).abs
  have hRint : Integrable
      (fun α : ℝ => 2 * ε * |bulkTermCentered c ε α n k - detTermCentered ε α n k|
        + 2 * ε * |bulkTermCentered c ε α n j - detTermCentered ε α n j|)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((hDint k).const_mul (2 * ε)).add ((hDint j).const_mul (2 * ε))
  have hmono := integral_mono hLint hRint hptw
  refine le_trans hmono ?_
  rw [integral_add ((hDint k).const_mul (2 * ε)) ((hDint j).const_mul (2 * ε)),
    integral_const_mul, integral_const_mul]
  have hbk := integral_abs_centered_sub_le c ε hε n k hH hk
  have hbj := integral_abs_centered_sub_le c ε hε n j hH hj
  nlinarith [hbk, hbj, hε, hm0]

/-! ## 4. The Lamé cap in covariance currency

Beyond `StopWin.Tcap n` the random bulk is empty for every irrational `α`, so the
summand — and hence the absolute off-diagonal term — vanishes identically. -/

lemma bulkTerm_eq_zero_of_Tcap (c ε α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hn : 1 ≤ n) (hj : StopWin.Tcap n ≤ j) :
    bulkTerm c ε α n j = 0 := by
  unfold bulkTerm
  rw [if_neg]
  intro hmem
  have hlt : j < stoppingTime α n :=
    Finset.mem_range.mp (Finset.mem_of_mem_filter j hmem)
  have := StopWin.stoppingTime_le_Tcap hα hirr hn
  omega

lemma integral_bulkTerm_eq_zero_of_Tcap (c ε : ℝ) (n j : ℕ) (hn : 1 ≤ n)
    (hj : StopWin.Tcap n ≤ j) :
    (∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j) = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
    with α hα hirr
  exact bulkTerm_eq_zero_of_Tcap c ε α hα hirr n j hn hj

lemma bulkTermCentered_eq_zero_of_Tcap (c ε α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hn : 1 ≤ n) (hj : StopWin.Tcap n ≤ j) :
    bulkTermCentered c ε α n j = 0 := by
  unfold bulkTermCentered
  rw [bulkTerm_eq_zero_of_Tcap c ε α hα hirr n j hn hj,
    integral_bulkTerm_eq_zero_of_Tcap c ε n j hn hj, sub_zero]

/-- The absolute off-diagonal summand of (41) vanishes at every pair with an
index beyond the Lamé cap. -/
lemma offdiagAbs_eq_zero_of_Tcap (c ε : ℝ) (n : ℕ) (hn : 1 ≤ n) (p : ℕ × ℕ)
    (hp : StopWin.Tcap n ≤ p.1 ∨ StopWin.Tcap n ≤ p.2) :
    (if p.1 = p.2 then 0 else
      |∫ α in Ioo (0 : ℝ) 1,
        bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2|) = 0 := by
  split_ifs with h
  · rfl
  · have hz : (∫ α in Ioo (0 : ℝ) 1,
        bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
        with α hα hirr
      rcases hp with h1 | h1
      · rw [bulkTermCentered_eq_zero_of_Tcap c ε α hα hirr n p.1 hn h1, zero_mul]
        rfl
      · rw [bulkTermCentered_eq_zero_of_Tcap c ε α hα hirr n p.2 hn h1, mul_zero]
        rfl
    rw [hz, abs_zero]


/-! ## 5. The pairs that are paid for rather than estimated

Three families go into the bad set, all of cardinality `O(L·H)`: the `H`-near
pairs of the manuscript's own display, the pairs with an index inside the
`O(H)` symmetric-difference window `StopWin.diffWindow c n`, and the
resonance-near pairs the hypothesis supplies. -/

/-- The pairs of the Lamé window that are `H`-near, or have an index inside the
window where the random and deterministic bulks may disagree. -/
def excPairs (c : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (StopWin.Tcap n) ×ˢ Finset.range (StopWin.Tcap n)).filter
    (fun p => |(p.1 : ℝ) - (p.2 : ℝ)| ≤ Hscale n
      ∨ p.1 ∈ StopWin.diffWindow c n ∨ p.2 ∈ StopWin.diffWindow c n)

lemma card_excPairs_le (c : ℝ) (n : ℕ) (hH : 0 ≤ Hscale n) :
    ((excPairs c n).card : ℝ)
      ≤ (StopWin.Tcap n : ℝ) * (2 * Hscale n + 1)
        + 2 * (StopWin.Tcap n : ℝ) * ((StopWin.diffWindow c n).card : ℝ) := by
  classical
  set m : ℕ := ⌊Hscale n⌋₊ with hm
  set T : ℕ := StopWin.Tcap n with hT
  set D : Finset ℕ := StopWin.diffWindow c n with hD
  set Near : Finset (ℕ × ℕ) := (Finset.range T).biUnion
    (fun j => (Finset.Icc (j - m) (j + m)).image (fun k => (j, k))) with hNear
  have hsub : excPairs c n ⊆ Near ∪ ((D ×ˢ Finset.range T) ∪ (Finset.range T ×ˢ D)) := by
    intro p hp
    simp only [excPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    rcases h3 with hnear | hw
    · refine Finset.mem_union_left _ ?_
      refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_range.mpr h1, ?_⟩
      refine Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩
      have habs := abs_le.mp hnear
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · rcases le_total p.1 p.2 with hle | hle
        · omega
        · have hd : ((p.1 - p.2 : ℕ) : ℝ) ≤ Hscale n := by
            rw [Nat.cast_sub hle]; linarith [habs.2]
          have : p.1 - p.2 ≤ m := Nat.le_floor hd
          omega
      · rcases le_total p.1 p.2 with hle | hle
        · have hd : ((p.2 - p.1 : ℕ) : ℝ) ≤ Hscale n := by
            rw [Nat.cast_sub hle]; linarith [habs.1]
          have : p.2 - p.1 ≤ m := Nat.le_floor hd
          omega
        · omega
    · refine Finset.mem_union_right _ ?_
      rcases hw with hw1 | hw2
      · exact Finset.mem_union_left _
          (Finset.mem_product.mpr ⟨hw1, Finset.mem_range.mpr h2⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨Finset.mem_range.mpr h1, hw2⟩)
  have hNearcard : Near.card ≤ T * (2 * m + 1) := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ j ∈ Finset.range T,
          ((Finset.Icc (j - m) (j + m)).image (fun k => (j, k))).card
        ≤ ∑ _j ∈ Finset.range T, (2 * m + 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine le_trans Finset.card_image_le ?_
          rw [Nat.card_Icc]
          omega
      _ = T * (2 * m + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hcard : (excPairs c n).card ≤ T * (2 * m + 1) + (D.card * T + T * D.card) := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    have h2 : ((D ×ˢ Finset.range T) ∪ (Finset.range T ×ˢ D)).card
        ≤ D.card * T + T * D.card := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_product, Finset.card_product, Finset.card_range]
    omega
  have hcast : ((excPairs c n).card : ℝ)
      ≤ (T : ℝ) * (2 * (m : ℝ) + 1) + 2 * (T : ℝ) * (D.card : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at this
    linarith
  have hmH : (m : ℝ) ≤ Hscale n := Nat.floor_le hH
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
  nlinarith [hcast, hmH, hT0]

/-! ## 6. The two arithmetic prices

`1 + log(2+L) ≤ 33·L^{1/16}`, hence `κ·L·H ≤ 35937·κ·L²/(1+log(2+L))³` — the
same computation `CorFinal.card_sharpen` performs, reproved here because the
declaration it is needed below sits under a different import. -/

lemma logFactor_le_rpow {L : ℝ} (hL : 1 ≤ L) :
    1 + Real.log (2 + L) ≤ 33 * L ^ (1 / 16 : ℝ) := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  set v : ℝ := L ^ (1 / 16 : ℝ) with hv
  have hv0 : (0 : ℝ) < v := Real.rpow_pos_of_pos hL0 _
  have hv1 : (1 : ℝ) ≤ v := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL (by norm_num : (0:ℝ) ≤ 1/16)
    simpa [Real.one_rpow, hv] using h
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

lemma card_sharpen (κ : ℝ) (hκ : 0 ≤ κ) (n : ℕ) (hL : 1 ≤ Lnorm n) :
    κ * Lnorm n * Hscale n
      ≤ (35937 * κ) * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3 := by
  set L : ℝ := Lnorm n with hLdef
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  set U : ℝ := 1 + Real.log (2 + L) with hUdef
  have hU1 : (1 : ℝ) ≤ U := by
    have : (0 : ℝ) ≤ Real.log (2 + L) := Real.log_nonneg (by linarith)
    simp only [hUdef]; linarith
  have hUpos : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU1
  set v : ℝ := L ^ (1 / 16 : ℝ) with hv
  have hv0 : (0 : ℝ) < v := Real.rpow_pos_of_pos hL0 _
  have hv1 : (1 : ℝ) ≤ v := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL (by norm_num : (0:ℝ) ≤ 1/16)
    simpa [Real.one_rpow, hv] using h
  have hLv : L = v ^ (16 : ℕ) := by
    rw [hv, ← Real.rpow_natCast (L ^ (1/16:ℝ)) 16, ← Real.rpow_mul hL0.le]
    norm_num
  have hHv : Hscale n = v ^ (12 : ℕ) := by
    rw [Hscale, ← hLdef, hv, ← Real.rpow_natCast (L ^ (1/16:ℝ)) 12, ← Real.rpow_mul hL0.le]
    norm_num
  have hU33 : U ≤ 33 * v := by
    simpa [hUdef, hv] using logFactor_le_rpow hL
  have hcube : U ^ 3 ≤ 35937 * v ^ 3 := by
    have h := pow_le_pow_left₀ (le_trans zero_le_one hU1) hU33 3
    calc U ^ 3 ≤ (33 * v) ^ 3 := h
      _ = 35937 * v ^ 3 := by ring
  rw [le_div_iff₀ (by positivity)]
  have hv31 : v ^ (31 : ℕ) ≤ v ^ (32 : ℕ) := by
    have : v ^ (31 : ℕ) * 1 ≤ v ^ (31 : ℕ) * v :=
      mul_le_mul_of_nonneg_left hv1 (by positivity)
    calc v ^ (31 : ℕ) = v ^ (31 : ℕ) * 1 := by ring
      _ ≤ v ^ (31 : ℕ) * v := this
      _ = v ^ (32 : ℕ) := by ring
  calc κ * L * Hscale n * U ^ 3
      = (κ * v ^ (28 : ℕ)) * U ^ 3 := by rw [hHv, hLv]; ring
    _ ≤ (κ * v ^ (28 : ℕ)) * (35937 * v ^ 3) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 35937 * κ * v ^ (31 : ℕ) := by ring
    _ ≤ 35937 * κ * v ^ (32 : ℕ) := by
        refine mul_le_mul_of_nonneg_left hv31 (by positivity)
    _ = 35937 * κ * L ^ 2 := by rw [hLv]; ring


lemma one_le_Lnorm_of_three_le (n : ℕ) (hn : 3 ≤ n) : (1 : ℝ) ≤ Lnorm n := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  simp only [Lnorm]
  exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp

lemma one_le_Hscale_of {n : ℕ} (hL : (1 : ℝ) ≤ Lnorm n) : (1 : ℝ) ≤ Hscale n := by
  have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL (by norm_num : (0:ℝ) ≤ 3/4)
  simpa [Hscale, Real.one_rpow] using h

/-! ## 7. The residual, reduced to a statement about the deterministic bulk

The payoff.  `Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` — §5's last
open input — follows from a far-pair covariance decay in which **no random
index set and no stopping time occur**: only `bulkJ n`, the deterministic bulk
of display (19), and the `ε`-truncated marks at two of its levels.

That hypothesis is `Kwon1002.prop_4_1_marked_factorization` at `r = 2` read on
the pair `(Z^{(ε)}_{n,j}, Z^{(ε)}_{n,k})`; everything §5-specific — the random
`bulkIndices`, the stopping time, the `O(H)` symmetric-difference window, the
Lamé cap and the `H`-near pairs — is discharged here.

The three bad-set families are all `O(L·H)`, the manuscript's own budget:
the `H`-near pairs, the pairs meeting `StopWin.diffWindow c n`, and the
resonance-near pairs `R` the hypothesis carries. -/
set_option maxHeartbeats 1000000 in
theorem abs_far_sharp_of_det_pair_decay (c : ℝ)
    (hdet : ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ R : Finset (ℕ × ℕ),
          ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
          ∀ j k : ℕ, j ∈ bulkJ n → k ∈ bulkJ n →
            Hscale n < |(j : ℝ) - (k : ℝ)| → (j, k) ∉ R →
            |∫ α in Ioo (0 : ℝ) 1, detTermCentered ε α n j * detTermCentered ε α n k|
              ≤ δ / (Lnorm n) ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            (if p.1 = p.2 then 0 else
              |∫ α in Ioo (0 : ℝ) 1,
                bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2|)
          ≤ ε / 2 := by
  classical
  obtain ⟨κR, hκR, hdec⟩ := hdet
  obtain ⟨Cs, c₀, hCs, hc₀, hstop⟩ := StopWin.stopBad_measure_le
  set Kd : ℝ := 2 * |c| + 405 + 2 * StopWin.trimConst with hKddef
  have hKd0 : 0 < Kd := by
    have h1 := StopWin.trimConst_pos
    have h2 := abs_nonneg c
    rw [hKddef]; linarith
  set Kexc : ℝ := 18 + 12 * Kd with hKexcdef
  have hKexc0 : 0 < Kexc := by rw [hKexcdef]; linarith
  refine ⟨35937 * (Kexc + κR), by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hdec ε hε hε1 (ε / 144) (by positivity)
  -- the exceptional mass, priced against the `O(L²)` pairs of the Lamé window
  have hlim : Tendsto (fun n : ℕ => Cs *
      ((Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n)))
        * (Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n))))) atTop (𝓝 0) := by
    have h := StopWin.tendsto_Lnorm_mul_exp_neg_sqrt (cs := c₀ / 2) (by linarith)
    have h2 := (h.mul h).const_mul Cs
    simpa using h2
  have hsmall : ∀ᶠ n : ℕ in atTop, Cs *
      ((Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n)))
        * (Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n)))) < 1 / 2304 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  have htail : ∀ᶠ n : ℕ in atTop,
      (Lnorm n) ^ 2 * (volume (StopWin.stopBad n)).toReal ≤ 1 / 2304 := by
    filter_upwards [hstop, hsmall] with n hstopn hsmalln
    have he : Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n))
        * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n))
        = Real.exp (-c₀ * Real.sqrt (Lnorm n)) := by
      rw [← Real.exp_add]; ring_nf
    have hsq : Cs * ((Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n)))
        * (Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n))))
        = (Lnorm n) ^ 2 * (Cs * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
      calc Cs * ((Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n)))
            * (Lnorm n * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n))))
          = (Lnorm n) ^ 2 * (Cs * (Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n))
              * Real.exp (-(c₀ / 2) * Real.sqrt (Lnorm n)))) := by ring
        _ = (Lnorm n) ^ 2 * (Cs * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by rw [he]
    have hL2 : (0 : ℝ) ≤ (Lnorm n) ^ 2 := sq_nonneg _
    have hmono : (Lnorm n) ^ 2 * (volume (StopWin.stopBad n)).toReal
        ≤ (Lnorm n) ^ 2 * (Cs * Real.exp (-c₀ * Real.sqrt (Lnorm n))) :=
      mul_le_mul_of_nonneg_left hstopn hL2
    rw [hsq] at hsmalln
    linarith
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp htail
  refine ⟨max (max N₁ N₂) 3, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 1 ≤ n := by omega
  have hL1 : (1 : ℝ) ≤ Lnorm n := one_le_Lnorm_of_three_le n hn3
  have hH1 : (1 : ℝ) ≤ Hscale n := one_le_Hscale_of hL1
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  have hm0 : (0 : ℝ) ≤ (volume (StopWin.stopBad n)).toReal := ENNReal.toReal_nonneg
  have hmtail : (Lnorm n) ^ 2 * (volume (StopWin.stopBad n)).toReal ≤ 1 / 2304 :=
    hN₂ n hn2
  obtain ⟨R, hRcard, hRdec⟩ := hN₁ n hn1
  refine ⟨excPairs c n ∪ R, ?_, ?_⟩
  · -- the cardinality budget
    have hT : (StopWin.Tcap n : ℝ) ≤ 6 * Lnorm n := by
      have := StopWin.Tcap_le n hL0.le; linarith
    have hT0 : (0 : ℝ) ≤ (StopWin.Tcap n : ℝ) := Nat.cast_nonneg _
    have hDcast : (((StopWin.diffWindow c n).card : ℕ) : ℝ)
        ≤ 2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1 := by
      have h1 := StopWin.card_diffWindow_le c n
      have := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at this
      linarith
    have hD : (((StopWin.diffWindow c n).card : ℕ) : ℝ) ≤ Kd * Hscale n := by
      have h2 := StopWin.bdryLen_le c n (by linarith)
      have h3 := StopWin.trimAmt_le n (by linarith)
      have hc := StopWin.trimConst_pos
      have habs := abs_nonneg c
      rw [hKddef]
      nlinarith [hDcast, h2, h3, hH1]
    have hexc := card_excPairs_le c n (by linarith)
    have hexcK : ((excPairs c n).card : ℝ) ≤ Kexc * Lnorm n * Hscale n := by
      have hstep : (StopWin.Tcap n : ℝ) * (2 * Hscale n + 1)
          + 2 * (StopWin.Tcap n : ℝ) * (((StopWin.diffWindow c n).card : ℕ) : ℝ)
          ≤ Kexc * Lnorm n * Hscale n := by
        rw [hKexcdef]
        nlinarith [hT, hT0, hD, hH1, hL1, hKd0.le]
      linarith
    have hunion : (((excPairs c n ∪ R).card : ℕ) : ℝ)
        ≤ ((excPairs c n).card : ℝ) + (R.card : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr (Finset.card_union_le (excPairs c n) R)
      push_cast at this
      linarith
    have hfin : (((excPairs c n ∪ R).card : ℕ) : ℝ)
        ≤ (Kexc + κR) * Lnorm n * Hscale n := by
      have : κR * Lnorm n * Hscale n + Kexc * Lnorm n * Hscale n
          = (Kexc + κR) * Lnorm n * Hscale n := by ring
      linarith [hunion, hexcK, hRcard]
    exact le_trans hfin (card_sharpen (Kexc + κR) (by positivity) n hL1)
  · -- the far sum
    set P : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hPdef
    set Bad : Finset (ℕ × ℕ) := excPairs c n ∪ R with hBaddef
    set F : (ℕ × ℕ) → ℝ := fun p => if p.1 = p.2 then 0 else
      |∫ α in Ioo (0 : ℝ) 1,
        bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2| with hFdef
    set Win : Finset (ℕ × ℕ) := (P \ Bad).filter
      (fun p => p.1 < StopWin.Tcap n ∧ p.2 < StopWin.Tcap n) with hWindef
    have hrestrict : ∑ p ∈ P \ Bad, F p = ∑ p ∈ Win, F p := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro p hp hnot
      rw [Finset.mem_filter, not_and] at hnot
      have h := hnot hp
      simp only [not_and_or, not_lt] at h
      exact offdiagAbs_eq_zero_of_Tcap c ε n hnpos p h
    have hQ : (0 : ℝ) ≤ ε / 144 / (Lnorm n) ^ 2
        + 16 * ε ^ 2 * (volume (StopWin.stopBad n)).toReal := by positivity
    have hbd : ∀ p ∈ Win, F p ≤ ε / 144 / (Lnorm n) ^ 2
        + 16 * ε ^ 2 * (volume (StopWin.stopBad n)).toReal := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpPB, hcond⟩ := hp
      obtain ⟨hpP, hpB⟩ := Finset.mem_sdiff.mp hpPB
      rw [hBaddef, Finset.mem_union, not_or] at hpB
      have hexc' : ¬ (|(p.1 : ℝ) - (p.2 : ℝ)| ≤ Hscale n
          ∨ p.1 ∈ StopWin.diffWindow c n ∨ p.2 ∈ StopWin.diffWindow c n) := by
        intro hcon
        exact hpB.1 (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hcond.1,
            Finset.mem_range.mpr hcond.2⟩, hcon⟩)
      push_neg at hexc'
      obtain ⟨hfar, hw1, hw2⟩ := hexc'
      have hne : p.1 ≠ p.2 := by
        intro heq
        rw [heq] at hfar
        simp only [sub_self, abs_zero] at hfar
        linarith
      simp only [hFdef, if_neg hne]
      have hbridge := window_covariance_bridge c ε hε.le n p.1 p.2 (by linarith) hw1 hw2
      have hdd : |∫ α in Ioo (0 : ℝ) 1,
          detTermCentered ε α n p.1 * detTermCentered ε α n p.2|
          ≤ ε / 144 / (Lnorm n) ^ 2 := by
        by_cases h1 : p.1 ∈ bulkJ n
        · by_cases h2 : p.2 ∈ bulkJ n
          · exact hRdec p.1 p.2 h1 h2 hfar (by simpa using hpB.2)
          · have hz : (∫ α in Ioo (0 : ℝ) 1,
                detTermCentered ε α n p.1 * detTermCentered ε α n p.2) = 0 := by
              simp only [detTermCentered_eq_zero_of_not_mem ε n p.2 h2, mul_zero,
                integral_zero]
            rw [hz, abs_zero]; positivity
        · have hz : (∫ α in Ioo (0 : ℝ) 1,
              detTermCentered ε α n p.1 * detTermCentered ε α n p.2) = 0 := by
            simp only [detTermCentered_eq_zero_of_not_mem ε n p.1 h1, zero_mul,
              integral_zero]
          rw [hz, abs_zero]; positivity
      set A : ℝ := ∫ α in Ioo (0 : ℝ) 1,
        bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2 with hAdef
      set Bv : ℝ := ∫ α in Ioo (0 : ℝ) 1,
        detTermCentered ε α n p.1 * detTermCentered ε α n p.2 with hBvdef
      have hsplit : A = Bv + (A - Bv) := by ring
      calc |A| = |Bv + (A - Bv)| := by rw [← hsplit]
        _ ≤ |Bv| + |A - Bv| := abs_add_le _ _
        _ ≤ ε / 144 / (Lnorm n) ^ 2
            + 16 * ε ^ 2 * (volume (StopWin.stopBad n)).toReal := by
              linarith [hdd, hbridge]
    have hcardWin : ((Win.card : ℕ) : ℝ) ≤ 36 * (Lnorm n) ^ 2 := by
      have hsub : Win ⊆ Finset.range (StopWin.Tcap n) ×ˢ Finset.range (StopWin.Tcap n) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hp.2.1, Finset.mem_range.mpr hp.2.2⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_range] at hc
      have hcast : ((Win.card : ℕ) : ℝ)
          ≤ (StopWin.Tcap n : ℝ) * (StopWin.Tcap n : ℝ) := by
        have := (Nat.cast_le (α := ℝ)).mpr hc
        push_cast at this
        linarith
      have hT : (StopWin.Tcap n : ℝ) ≤ 6 * Lnorm n := by
        have := StopWin.Tcap_le n hL0.le; linarith
      have hT0 : (0 : ℝ) ≤ (StopWin.Tcap n : ℝ) := Nat.cast_nonneg _
      nlinarith [hcast, hT, hT0, hL0.le]
    have hsum := Finset.sum_le_card_nsmul Win F
      (ε / 144 / (Lnorm n) ^ 2 + 16 * ε ^ 2 * (volume (StopWin.stopBad n)).toReal) hbd
    rw [nsmul_eq_mul] at hsum
    rw [hrestrict]
    refine le_trans hsum ?_
    have hstep : ((Win.card : ℕ) : ℝ)
        * (ε / 144 / (Lnorm n) ^ 2 + 16 * ε ^ 2 * (volume (StopWin.stopBad n)).toReal)
        ≤ (36 * (Lnorm n) ^ 2)
          * (ε / 144 / (Lnorm n) ^ 2 + 16 * ε ^ 2
              * (volume (StopWin.stopBad n)).toReal) :=
      mul_le_mul_of_nonneg_right hcardWin hQ
    refine le_trans hstep ?_
    have hone : (36 * (Lnorm n) ^ 2) * (ε / 144 / (Lnorm n) ^ 2) = ε / 4 := by
      have hLne : ((Lnorm n) ^ 2 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have hexpand : (36 * (Lnorm n) ^ 2)
        * (ε / 144 / (Lnorm n) ^ 2 + 16 * ε ^ 2
            * (volume (StopWin.stopBad n)).toReal)
        = (36 * (Lnorm n) ^ 2) * (ε / 144 / (Lnorm n) ^ 2)
          + 576 * ε ^ 2
            * ((Lnorm n) ^ 2 * (volume (StopWin.stopBad n)).toReal) := by ring
    rw [hexpand, hone]
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have hfinal : 576 * ε ^ 2
        * ((Lnorm n) ^ 2 * (volume (StopWin.stopBad n)).toReal) ≤ ε / 4 := by
      have h1 : (0 : ℝ) ≤ (Lnorm n) ^ 2 * (volume (StopWin.stopBad n)).toReal := by
        positivity
      nlinarith [hmtail, hε2, hε.le, sq_nonneg ε]
    linarith

end

end WindowCov

end Kwon1002
