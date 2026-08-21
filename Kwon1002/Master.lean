import Kwon1002.PoissonLimit
import Kwon1002.Section6Skeleton
import Kwon1002.CorFinal

/-!
# §7: stopping, centering, and the master assembly

This module carries out the manuscript's final section and proves
`Kwon1002.Erdos1002Conclusion` — Kwon's Theorem 1.1 — from three explicit
hypotheses.

## The exact list of hypotheses the conditional carries

`erdos1002Conclusion_of (c : ℝ)` takes these and nothing else:

1. `PrincipalCauchyLaw c` — Corollary 5.3, display (43).  Definitionally the
   statement of `Kwon1002.principal_cauchy_law` (guards at the foot of this
   file, against both that name and `CorFinal.principal_cauchy_law_F`).

   The canonical name `Kwon1002.principal_cauchy_law` is a bare `sorry` in
   `Kwon1002/PoissonLimit.lean`, and `PoissonLimit` sits *below* every module
   able to prove it (`CauchyLaw`, `Assembly5`, `CompoundCauchy`, `Finale`,
   `CorFinal` all import it), so that name can never shed `sorryAx` by
   mathematics alone.  This module therefore discharges hypothesis 1 from
   `Kwon1002.CorFinal.principal_cauchy_law_F`, the same `Prop` proved in the
   module that can actually reduce it; `CorFinal` reduces it to exactly two
   residuals, `CorFinal.largeSum_charFun_limit` and
   `CorFinal.bulk_offdiagonal_abs_far_sharp`.
2. `Prop64Statement` — Proposition 6.4, the bounded-remainder weak law.
   Definitionally the statement of
   `Kwon1002.prop_6_4_bounded_remainder_weak_law` (guard at the foot of this
   file).  This is the manuscript author's current work; §6 is not touched
   here.
3. `Section7EndTerms c` — §7's Lemma 7.1 together with the §7/§4 index-set
   bridge, defined in Part F.  Its two halves are the `O(H)` trimming below
   `c·H` and the passage between `Marks.bulkIndices c α n` (random, §7) and
   `Section4.bulkJ n` (deterministic, display (19)).  This is the only one of
   the three that is not already a named statement elsewhere in `Kwon1002/`;
   `erdos1002Conclusion_of_section7` records that fact by discharging the
   other two against the in-tree targets.

The trimming constant `c` is free: the theorem holds for every `c`.

## What is proved here outright (axiom-clean, no hypothesis)

* **Part A** — continuity of `cauchyLimitCDF` and its strict sign behaviour
  through `1/2`.
* **Part B** — the exact symmetry `S_N(1-α) = -S_N(α)` for irrational `α`,
  the invariance of Lebesgue measure on `(0,1)` under `α ↦ 1-α`, and the
  consequence that the median of the finite-`N` law sits at `0`:
  `distributionValue N y ≥ 1/2` for `y ≥ 0` and `≤ 1/2` for `y < 0`.
* **Part C** — `erdos1002Conclusion_of_shifted`: removal of the deterministic
  centering.  If `X_N - c_N` converges to the Cauchy law of scale `1/(2π)`
  then `c_N → 0` and `X_N` itself converges.  This is the manuscript's last
  paragraph, and it is proved with **no** hypothesis at all — and without
  tightness, subsequences, or a limit-uniqueness argument: Part B pins the
  median, and Part A makes the limit strictly increasing through `1/2`.
* **Part D** — `tendsto_cdf_of_perturbation`, Slutsky read on distribution
  functions, with a continuous limit.  No measurability hypothesis is needed.
* **Part E** — `normalizedRotationSum_decomp`, the exact §7 decomposition
  `S_n(α)/L = bulkSum + (1/L)∑_{j ∈ J_n} (−1)^j B_j + (end terms)`,
  from display (3) (`rotationSum_eq_alternating_sum`) and (11).
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace Master

noncomputable section

/-! ## Part A, elementary facts about the Cauchy distribution function -/

lemma continuous_cauchyLimitCDF : Continuous cauchyLimitCDF := by
  unfold cauchyLimitCDF
  fun_prop

lemma cauchyLimitCDF_pos_iff (y : ℝ) : 1 / 2 < cauchyLimitCDF y ↔ 0 < y := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hinv : (0 : ℝ) < 1 / Real.pi := by positivity
  constructor
  · intro h
    unfold cauchyLimitCDF at h
    have h1 : 0 < (1 / Real.pi) * Real.arctan (2 * Real.pi * y) := by linarith
    have h2 : 0 < Real.arctan (2 * Real.pi * y) := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h3 : (0 : ℝ) < 2 * Real.pi * y := by
      by_contra hc
      push_neg at hc
      have := Real.arctan_mono hc
      rw [Real.arctan_zero] at this
      linarith
    nlinarith
  · intro h
    unfold cauchyLimitCDF
    have h3 : (0 : ℝ) < 2 * Real.pi * y := by positivity
    have h2 : 0 < Real.arctan (2 * Real.pi * y) := by
      have := Real.arctan_strictMono (a := (0:ℝ)) (b := 2 * Real.pi * y) h3
      rwa [Real.arctan_zero] at this
    nlinarith

lemma cauchyLimitCDF_neg_iff (y : ℝ) : cauchyLimitCDF y < 1 / 2 ↔ y < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hinv : (0 : ℝ) < 1 / Real.pi := by positivity
  constructor
  · intro h
    unfold cauchyLimitCDF at h
    have h1 : (1 / Real.pi) * Real.arctan (2 * Real.pi * y) < 0 := by linarith
    have h2 : Real.arctan (2 * Real.pi * y) < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h3 : (2 * Real.pi * y) < 0 := by
      by_contra hc
      push_neg at hc
      have := Real.arctan_mono hc
      rw [Real.arctan_zero] at this
      linarith
    nlinarith
  · intro h
    unfold cauchyLimitCDF
    have h3 : (2 * Real.pi * y) < 0 := by nlinarith
    have h2 : Real.arctan (2 * Real.pi * y) < 0 := by
      have := Real.arctan_strictMono (a := 2 * Real.pi * y) (b := (0:ℝ)) h3
      rwa [Real.arctan_zero] at this
    nlinarith


/-! ## Part B, the exact symmetry of the law of `S_N`

`{k(1-α)} = 1 - {kα}` for irrational `α`, so `S_N(1-α) = -S_N(α)`, and
`α ↦ 1-α` preserves Lebesgue measure on `(0,1)`.  Consequently the law of
`X_N = S_N/log N` under Lebesgue measure on `(0,1)` is exactly symmetric,
for every `N`.  This is the input that removes the deterministic centering
at the very end of the manuscript's proof of Theorem 1.1. -/

lemma ae_irrational : ∀ᵐ α : ℝ, Irrational α := by
  have hc : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have h0 : volume (Set.range ((↑) : ℚ → ℝ)) = 0 := hc.measure_zero volume
  have hset : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
    ext x; simp [Irrational]
  rw [ae_iff, hset]; exact h0

lemma sawtooth_one_sub {α : ℝ} (hirr : Irrational α) {k : ℕ} (hk : 1 ≤ k) :
    sawtooth ((k : ℝ) * (1 - α)) = -sawtooth ((k : ℝ) * α) := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hirrk : Irrational ((k : ℝ) * α) := by
    simpa using hirr.natCast_mul (by omega : k ≠ 0)
  have hfr : Int.fract ((k : ℝ) * α) ≠ 0 := by
    intro h
    have : ((k : ℝ) * α) = (⌊(k : ℝ) * α⌋ : ℤ) := by
      have := Int.fract_add_floor ((k : ℝ) * α)
      rw [h] at this; linarith [this]
    exact hirrk.ne_int _ this
  have hrw : (k : ℝ) * (1 - α) = ((k : ℤ) : ℝ) + (-((k : ℝ) * α)) := by
    push_cast; ring
  unfold sawtooth
  rw [hrw, Int.fract_intCast_add, Int.fract_neg hfr]
  ring

lemma rotationSum_one_sub {α : ℝ} (hirr : Irrational α) (N : ℕ) :
    rotationSum N (1 - α) = -rotationSum N α := by
  unfold rotationSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact sawtooth_one_sub hirr (Finset.mem_Icc.mp hk).1

lemma normalizedRotationSum_one_sub {α : ℝ} (hirr : Irrational α) (N : ℕ) :
    normalizedRotationSum N (1 - α) = -normalizedRotationSum N α := by
  unfold normalizedRotationSum
  rw [rotationSum_one_sub hirr N, neg_div]

lemma measurable_normalizedRotationSum (N : ℕ) :
    Measurable (fun α : ℝ => normalizedRotationSum N α) := by
  unfold normalizedRotationSum rotationSum sawtooth
  refine Measurable.div_const ?_ _
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.sub (measurable_fract.comp (measurable_id.const_mul _))

/-- The half-line events of the law of `X_N`, as a set. -/
def cut (N : ℕ) (S : Set ℝ) : Set ℝ :=
  Ioo (0 : ℝ) 1 ∩ (fun α : ℝ => normalizedRotationSum N α) ⁻¹' S

lemma measurableSet_cut (N : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (cut N S) :=
  measurableSet_Ioo.inter ((measurable_normalizedRotationSum N) hS)

lemma cut_le_eq (N : ℕ) (y : ℝ) :
    {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α ≤ y} = cut N (Iic y) := by
  ext α; simp [cut, and_comm]

lemma volume_cut_le_one (N : ℕ) (S : Set ℝ) : volume (cut N S) ≤ 1 := by
  have h := measure_mono (μ := volume) (Set.inter_subset_left (s := Ioo (0 : ℝ) 1)
    (t := (fun α : ℝ => normalizedRotationSum N α) ⁻¹' S))
  simpa [cut, Real.volume_Ioo] using h

lemma volume_cut_ne_top (N : ℕ) (S : Set ℝ) : volume (cut N S) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (volume_cut_le_one N S)

/-- **The symmetry.**  For every `N` and every measurable `S`, the law of
`X_N` gives `S` and `-S` the same mass. -/
lemma volume_cut_neg (N : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    volume (cut N (-S)) = volume (cut N S) := by
  have hmp : MeasurePreserving (fun α : ℝ => 1 - α) volume volume :=
    volume.measurePreserving_sub_left 1
  have hpre : (fun α : ℝ => 1 - α) ⁻¹' (cut N S) =ᵐ[volume] cut N (-S) := by
    filter_upwards [ae_irrational] with α hirr
    have h1 : (1 : ℝ) - α ∈ Ioo (0 : ℝ) 1 ↔ α ∈ Ioo (0 : ℝ) 1 := by
      simp only [mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have h2 : normalizedRotationSum N (1 - α) = -normalizedRotationSum N α :=
      normalizedRotationSum_one_sub hirr N
    show ((1 : ℝ) - α ∈ cut N S) = (α ∈ cut N (-S))
    have hS' : ∀ x : ℝ, (-x ∈ S) ↔ (x ∈ -S) := by
      intro x; simp [Set.mem_neg]
    simp only [cut, Set.mem_inter_iff, Set.mem_preimage, h2, eq_iff_iff]
    rw [h1, hS' (normalizedRotationSum N α)]
  rw [← measure_congr hpre, hmp.measure_preimage (measurableSet_cut N hS).nullMeasurableSet]

lemma half_le_distributionValue_zero (N : ℕ) :
    (1 : ℝ) / 2 ≤ distributionValue N 0 := by
  have hsym : volume (cut N (Ici (0 : ℝ))) = volume (cut N (Iic (0 : ℝ))) := by
    have h : (-(Iic (0 : ℝ))) = Ici (0 : ℝ) := by
      simp [Set.neg_Iic]
    rw [← h]
    exact volume_cut_neg N measurableSet_Iic
  have hcover : Ioo (0 : ℝ) 1 ⊆ cut N (Iic (0 : ℝ)) ∪ cut N (Ici (0 : ℝ)) := by
    intro α hα
    rcases le_or_gt (normalizedRotationSum N α) 0 with h | h
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr ⟨hα, h.le⟩
  have h1 : (1 : ℝ≥0∞) ≤ volume (cut N (Iic (0 : ℝ))) + volume (cut N (Ici (0 : ℝ))) := by
    calc (1 : ℝ≥0∞) = volume (Ioo (0 : ℝ) 1) := by simp [Real.volume_Ioo]
      _ ≤ volume (cut N (Iic (0 : ℝ)) ∪ cut N (Ici (0 : ℝ))) := measure_mono hcover
      _ ≤ _ := measure_union_le _ _
  rw [hsym] at h1
  have h2 : (1 : ℝ≥0∞) ≤ 2 * volume (cut N (Iic (0 : ℝ))) := by
    rw [two_mul]; exact h1
  have hfin := volume_cut_ne_top N (Iic (0 : ℝ))
  have h3 : (1 : ℝ) ≤ 2 * (volume (cut N (Iic (0 : ℝ)))).toReal := by
    have := ENNReal.toReal_mono (by finiteness) h2
    simpa [ENNReal.toReal_mul] using this
  unfold distributionValue
  rw [cut_le_eq]
  linarith

lemma distributionValue_le_half_of_neg (N : ℕ) {y : ℝ} (hy : y < 0) :
    distributionValue N y ≤ (1 : ℝ) / 2 := by
  have hsym : volume (cut N (Ici (-y))) = volume (cut N (Iic y)) := by
    have h : (-(Iic y)) = Ici (-y) := Set.neg_Iic y
    rw [← h]; exact volume_cut_neg N measurableSet_Iic
  have hdisj : Disjoint (cut N (Iic y)) (cut N (Ici (-y))) := by
    rw [Set.disjoint_left]
    rintro α ⟨_, hle⟩ ⟨_, hge⟩
    simp only [Set.mem_preimage, mem_Iic] at hle
    simp only [Set.mem_preimage, mem_Ici] at hge
    linarith
  have hsub : cut N (Iic y) ∪ cut N (Ici (-y)) ⊆ Ioo (0 : ℝ) 1 := by
    rintro α (h | h) <;> exact h.1
  have h1 : volume (cut N (Iic y)) + volume (cut N (Ici (-y))) ≤ 1 := by
    rw [← measure_union hdisj (measurableSet_cut N measurableSet_Ici)]
    calc volume (cut N (Iic y) ∪ cut N (Ici (-y))) ≤ volume (Ioo (0 : ℝ) 1) :=
          measure_mono hsub
      _ = 1 := by simp [Real.volume_Ioo]
  rw [hsym] at h1
  have h2 : 2 * volume (cut N (Iic y)) ≤ 1 := by rw [two_mul]; exact h1
  have h3 : 2 * (volume (cut N (Iic y))).toReal ≤ 1 := by
    have := ENNReal.toReal_mono (by finiteness) h2
    simpa [ENNReal.toReal_mul] using this
  unfold distributionValue
  rw [cut_le_eq]
  linarith

lemma monotone_distributionValue (N : ℕ) : Monotone (distributionValue N) := by
  intro a b hab
  unfold distributionValue
  refine ENNReal.toReal_mono ?_ (measure_mono ?_)
  · exact (cut_le_eq N b) ▸ volume_cut_ne_top N (Iic b)
  · rintro α ⟨hα, h⟩; exact ⟨hα, h.trans hab⟩

lemma half_le_distributionValue_of_nonneg (N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 : ℝ) / 2 ≤ distributionValue N y :=
  le_trans (half_le_distributionValue_zero N) (monotone_distributionValue N hy)

/-! ## Part C, removing the deterministic centering

The manuscript's last paragraph.  If `X_N - c_N` converges in distribution to
the Cauchy law of scale `1/(2π)` for *some* deterministic `c_N`, then `c_N → 0`
and `X_N` itself converges.  Proved outright, with no hypothesis beyond the
shifted convergence: the exact symmetry of Part B pins the median of `X_N` at
`0`, and the Cauchy limit is symmetric and strictly increasing through `1/2`,
so no nonzero shift survives.  No tightness, subsequence, or uniqueness
argument is needed. -/

/-- `X_N - c_N ⇒ Cauchy(0, 1/(2π))`, read on distribution functions. -/
def ShiftedCauchyLimit (cs : ℕ → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun N : ℕ =>
      (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α - cs N ≤ x}).toReal)
    atTop (𝓝 (cauchyLimitCDF x))

lemma shifted_eq_distributionValue (cs : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α - cs N ≤ x}).toReal
      = distributionValue N (x + cs N) := by
  unfold distributionValue
  have hset : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α - cs N ≤ x}
      = {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α ≤ x + cs N} := by
    ext α
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    constructor <;> intro h <;> linarith
  rw [hset]

/-- **The centering tends to zero.** -/
theorem tendsto_center_zero {cs : ℕ → ℝ} (h : ShiftedCauchyLimit cs) :
    Tendsto cs atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- `a < 0`: eventually `a < cs N`
    set y : ℝ := a / 2 with hy
    have hy0 : 0 < -y := by simp only [hy]; linarith
    have hlim := h (-y)
    have hgt : (1 : ℝ) / 2 < cauchyLimitCDF (-y) := (cauchyLimitCDF_pos_iff (-y)).mpr hy0
    have hev : ∀ᶠ N in atTop,
        (1 : ℝ) / 2 < (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          normalizedRotationSum N α - cs N ≤ -y}).toReal :=
      hlim.eventually (eventually_gt_nhds hgt)
    filter_upwards [hev] with N hN
    rw [shifted_eq_distributionValue] at hN
    by_contra hc
    push_neg at hc
    have : -y + cs N < 0 := by simp only [hy] at hc ⊢; linarith
    exact absurd hN (not_lt.mpr (distributionValue_le_half_of_neg N this))
  · -- `0 < a`: eventually `cs N < a`
    set y : ℝ := -(a / 2) with hy
    have hy0 : y < 0 := by simp only [hy]; linarith
    have hlim := h y
    have hlt : cauchyLimitCDF y < (1 : ℝ) / 2 := (cauchyLimitCDF_neg_iff y).mpr hy0
    have hev : ∀ᶠ N in atTop,
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          normalizedRotationSum N α - cs N ≤ y}).toReal < (1 : ℝ) / 2 :=
      hlim.eventually (eventually_lt_nhds hlt)
    filter_upwards [hev] with N hN
    rw [shifted_eq_distributionValue] at hN
    by_contra hc
    push_neg at hc
    have h0 : 0 ≤ y + cs N := by simp only [hy] at hc ⊢; linarith
    exact absurd hN (not_lt.mpr (half_le_distributionValue_of_nonneg N h0))

/-- **Removal of the centering.**  Fully proved: the shifted convergence
implies the unshifted one, which is Kwon's Theorem 1.1. -/
theorem erdos1002Conclusion_of_shifted {cs : ℕ → ℝ} (h : ShiftedCauchyLimit cs) :
    Erdos1002Conclusion := by
  have hcs := tendsto_center_zero h
  intro x
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a `δ` on which the limit CDF moves by less than `ε/2`
  obtain ⟨δ₁, hδ₁, hδ₁F⟩ := Metric.continuous_iff.mp continuous_cauchyLimitCDF x (ε / 2) (by linarith)
  set δ : ℝ := δ₁ / 2 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδlt : δ < δ₁ := by rw [hδdef]; linarith
  have hFup : |cauchyLimitCDF (x + δ) - cauchyLimitCDF x| < ε / 2 := by
    have hd : dist (x + δ) x < δ₁ := by
      rw [Real.dist_eq, show x + δ - x = δ by ring, abs_of_pos hδ0]; exact hδlt
    simpa [Real.dist_eq] using hδ₁F (x + δ) hd
  have hFdn : |cauchyLimitCDF (x - δ) - cauchyLimitCDF x| < ε / 2 := by
    have hd : dist (x - δ) x < δ₁ := by
      rw [Real.dist_eq, show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδ0]; exact hδlt
    simpa [Real.dist_eq] using hδ₁F (x - δ) hd
  -- the two shifted convergences and the vanishing of the centering
  have hup := (h (x + δ)).eventually
    (Metric.ball_mem_nhds (cauchyLimitCDF (x + δ)) (by linarith : (0:ℝ) < ε / 2))
  have hdn := (h (x - δ)).eventually
    (Metric.ball_mem_nhds (cauchyLimitCDF (x - δ)) (by linarith : (0:ℝ) < ε / 2))
  have hcsev := (Metric.tendsto_atTop.mp hcs) δ hδ0
  obtain ⟨N₃, hN₃⟩ := hcsev
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hup
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hdn
  refine ⟨max N₃ (max N₁ N₂), fun N hN => ?_⟩
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right N₃ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right N₃ _)) hN
  have hcsN : |cs N| < δ := by
    have := hN₃ N hN3; rwa [Real.dist_eq, sub_zero] at this
  have h1 : |distributionValue N ((x + δ) + cs N) - cauchyLimitCDF (x + δ)| < ε / 2 := by
    have := hN₁ N hN1
    rw [Real.dist_eq, shifted_eq_distributionValue] at this
    exact this
  have h2 : |distributionValue N ((x - δ) + cs N) - cauchyLimitCDF (x - δ)| < ε / 2 := by
    have := hN₂ N hN2
    rw [Real.dist_eq, shifted_eq_distributionValue] at this
    exact this
  have hmono1 : distributionValue N x ≤ distributionValue N ((x + δ) + cs N) :=
    monotone_distributionValue N (by cases abs_lt.mp hcsN; linarith)
  have hmono2 : distributionValue N ((x - δ) + cs N) ≤ distributionValue N x :=
    monotone_distributionValue N (by cases abs_lt.mp hcsN; linarith)
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := (abs_lt.mp h2).1
    have := (abs_lt.mp hFdn).1
    linarith
  · have := (abs_lt.mp h1).2
    have := (abs_lt.mp hFup).2
    linarith

/-! ## Part D, Slutsky at the level of distribution functions

If `V_n` converges in distribution to a *continuous* limit distribution
function and `X_n - V_n → 0` in probability on `(0,1)`, then `X_n` has the same
limit.  Proved outright; only `measure_union_le` and monotonicity are used, so
no measurability of `X_n` or `V_n` is required. -/

lemma vol_ne_top {A : Set ℝ} (h : A ⊆ Ioo (0 : ℝ) 1) : volume A ≠ ⊤ := by
  have hle : volume A ≤ 1 := by
    calc volume A ≤ volume (Ioo (0 : ℝ) 1) := measure_mono h
      _ = 1 := by simp [Real.volume_Ioo]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

lemma toReal_le_of_subset_union {A B C : Set ℝ} (hsub : A ⊆ B ∪ C)
    (hB : B ⊆ Ioo (0 : ℝ) 1) (hC : C ⊆ Ioo (0 : ℝ) 1) :
    (volume A).toReal ≤ (volume B).toReal + (volume C).toReal := by
  have hA : A ⊆ Ioo (0 : ℝ) 1 := hsub.trans (Set.union_subset hB hC)
  have h1 : volume A ≤ volume B + volume C :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  have htop : volume B + volume C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨vol_ne_top hB, vol_ne_top hC⟩
  have h2 := ENNReal.toReal_mono htop h1
  rwa [ENNReal.toReal_add (vol_ne_top hB) (vol_ne_top hC)] at h2

/-- The event that the two families differ by at least `ε`. -/
def gapSet (X V : ℕ → ℝ → ℝ) (n : ℕ) (ε : ℝ) : Set ℝ :=
  {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ ε ≤ |X n α - V n α|}

/-- **CDF-level Slutsky.** -/
theorem tendsto_cdf_of_perturbation (X V : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (hF : Continuous F)
    (hV : ∀ x : ℝ, Tendsto (fun n : ℕ =>
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ V n α ≤ x}).toReal) atTop (𝓝 (F x)))
    (hsmall : ∀ ε > 0, Tendsto (fun n : ℕ => (volume (gapSet X V n ε)).toReal) atTop (𝓝 0))
    (x : ℝ) :
    Tendsto (fun n : ℕ => (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ X n α ≤ x}).toReal)
      atTop (𝓝 (F x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁F⟩ := Metric.continuous_iff.mp hF x (ε / 4) (by linarith)
  set δ : ℝ := δ₁ / 2 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδlt : δ < δ₁ := by rw [hδdef]; linarith
  have hFup : |F (x + δ) - F x| < ε / 4 := by
    have hd : dist (x + δ) x < δ₁ := by
      rw [Real.dist_eq, show x + δ - x = δ by ring, abs_of_pos hδ0]; exact hδlt
    simpa [Real.dist_eq] using hδ₁F (x + δ) hd
  have hFdn : |F (x - δ) - F x| < ε / 4 := by
    have hd : dist (x - δ) x < δ₁ := by
      rw [Real.dist_eq, show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδ0]; exact hδlt
    simpa [Real.dist_eq] using hδ₁F (x - δ) hd
  -- the three convergences
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((hV (x + δ)).eventually (Metric.ball_mem_nhds (F (x + δ)) (by linarith : (0:ℝ) < ε / 4)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    ((hV (x - δ)).eventually (Metric.ball_mem_nhds (F (x - δ)) (by linarith : (0:ℝ) < ε / 4)))
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp (hsmall δ hδ0) (ε / 4) (by linarith)
  refine ⟨max N₃ (max N₁ N₂), fun n hn => ?_⟩
  have hn3 : N₃ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right N₃ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right N₃ _)) hn
  have hg : (volume (gapSet X V n δ)).toReal < ε / 4 := by
    have := hN₃ n hn3
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at this
  have h1 : |(volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ V n α ≤ x + δ}).toReal - F (x + δ)| < ε / 4 := by
    have := hN₁ n hn1; rwa [Real.dist_eq] at this
  have h2 : |(volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ V n α ≤ x - δ}).toReal - F (x - δ)| < ε / 4 := by
    have := hN₂ n hn2; rwa [Real.dist_eq] at this
  -- the two set inclusions
  have hsubA : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ X n α ≤ x}
      ⊆ {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ V n α ≤ x + δ} ∪ gapSet X V n δ := by
    rintro α ⟨hα, hle⟩
    by_cases hd : δ ≤ |X n α - V n α|
    · exact Or.inr ⟨hα, hd⟩
    · push_neg at hd
      refine Or.inl ⟨hα, ?_⟩
      have := (abs_lt.mp hd).1
      linarith
  have hsubB : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ V n α ≤ x - δ}
      ⊆ {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ X n α ≤ x} ∪ gapSet X V n δ := by
    rintro α ⟨hα, hle⟩
    by_cases hd : δ ≤ |X n α - V n α|
    · exact Or.inr ⟨hα, hd⟩
    · push_neg at hd
      refine Or.inl ⟨hα, ?_⟩
      have := (abs_lt.mp hd).2
      linarith
  have hIoo : ∀ (W : ℕ → ℝ → ℝ) (y : ℝ),
      {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ W n α ≤ y} ⊆ Ioo (0 : ℝ) 1 := fun W y α hα => hα.1
  have hgIoo : gapSet X V n δ ⊆ Ioo (0 : ℝ) 1 := fun α hα => hα.1
  have hA := toReal_le_of_subset_union hsubA (hIoo V (x + δ)) hgIoo
  have hB := toReal_le_of_subset_union hsubB (hIoo X x) hgIoo
  rw [Real.dist_eq, abs_lt]
  have e1 := (abs_lt.mp h1).2
  have e2 := (abs_lt.mp h2).1
  have f1 := (abs_lt.mp hFup).2
  have f2 := (abs_lt.mp hFdn).1
  constructor <;> linarith

/-! ## Part E, the exact §7 decomposition

Display (3) (`Kwon1002.rotationSum_eq_alternating_sum`, proved) writes
`S_n(α)` as the alternating sum of `Φ(x_j,u_j)` over `j < τ_n`.  Splitting that
range at the §7 trim `c·H` and using `(11)`, `B_j = Φ(x_j,u_j) − a_{j+1}W(θ_j)`,
gives the exact identity

`S_n(α)/L = bulkSum + (1/L)∑_{j ∈ J_n} (−1)^j B_j + (end terms)`,

with `J_n = Marks.bulkIndices c α n` the *random* §7 bulk.  Everything here is
an identity; no estimate is used. -/

/-- The §7 end terms: the levels below the trim `c·H`. -/
def endTerms (c α : ℝ) (n : ℕ) : ℝ :=
  (1 / Lnorm n) *
    ∑ j ∈ (Finset.range (stoppingTime α n)).filter (fun j : ℕ => ¬ (c * Hscale n ≤ (j : ℝ))),
      (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j)

/-- The bounded-remainder sum over the **random** §7 bulk. -/
def randRemainderSum (c α : ℝ) (n : ℕ) : ℝ :=
  (1 / Lnorm n) * ∑ j ∈ bulkIndices c α n, (-1 : ℝ) ^ j * Bremainder α n j

/-- The bounded-remainder sum over the **deterministic** §4 bulk of display
(19), the index set Proposition 6.4 is stated on. -/
def detRemainderSum (α : ℝ) (n : ℕ) : ℝ :=
  (1 / Lnorm n) * ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j * Bremainder α n j

/-- Its deterministic centering. -/
def detRemainderCenter (n : ℕ) : ℝ :=
  (1 / Lnorm n) * ∑ j ∈ bulkJ n,
    (-1 : ℝ) ^ j * ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j

lemma phi_eq_mark_add_remainder (α : ℝ) (n j : ℕ) :
    Phi (gaussIter α j) (carry α n j) = mark α n j + Bremainder α n j := by
  unfold Bremainder mark
  ring

/-- **The §7 decomposition.**  Exact, for every irrational `α ∈ (0,1)`. -/
theorem normalizedRotationSum_decomp (c : ℝ) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) {n : ℕ} (hn : 1 ≤ n) :
    normalizedRotationSum n α
      = bulkSum c α n + randRemainderSum c α n + endTerms c α n := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (stoppingTime α n))
    (fun j : ℕ => c * Hscale n ≤ (j : ℝ))
    (fun j => (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j))
  have hbulk : (Finset.range (stoppingTime α n)).filter (fun j : ℕ => c * Hscale n ≤ (j : ℝ))
      = bulkIndices c α n := rfl
  rw [hbulk] at hsplit
  have hterm : ∀ j ∈ bulkIndices c α n,
      (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j)
        = (-1 : ℝ) ^ j * mark α n j + (-1 : ℝ) ^ j * Bremainder α n j := by
    intro j _
    rw [phi_eq_mark_add_remainder]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at hsplit
  have hrot : rotationSum n α
      = (∑ j ∈ bulkIndices c α n, (-1 : ℝ) ^ j * mark α n j)
        + (∑ j ∈ bulkIndices c α n, (-1 : ℝ) ^ j * Bremainder α n j)
        + ∑ j ∈ (Finset.range (stoppingTime α n)).filter (fun j : ℕ => ¬ (c * Hscale n ≤ (j : ℝ))),
            (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j) := by
    rw [rotationSum_eq_alternating_sum α hα hirr n hn]
    linarith [hsplit]
  have hbs : bulkSum c α n
      = (1 / Lnorm n) * ∑ j ∈ bulkIndices c α n, (-1 : ℝ) ^ j * mark α n j := by
    unfold bulkSum signedMark
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [normalizedRotationSum, hrot, hbs]
  simp only [endTerms, randRemainderSum, Lnorm]
  ring

/-! ## Part F, the master assembly

The three inputs, and nothing else. -/

/-- Corollary 5.3, the principal Cauchy law: the statement of
`Kwon1002.principal_cauchy_law`, reproduced token for token.  (Checked by the
`example` at the very bottom of this file.) -/
def PrincipalCauchyLaw (c : ℝ) : Prop :=
  ∃ b : ℕ → ℝ, ∀ x : ℝ,
    Tendsto
      (fun n : ℕ =>
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
      atTop (𝓝 (cauchyLimitCDF x))

/-- Proposition 6.4, the bounded-remainder weak law: the statement of
`Kwon1002.prop_6_4_bounded_remainder_weak_law`, reproduced token for token.
(Checked by the `example` at the very bottom of this file.) -/
def Prop64Statement : Prop :=
  ∀ ε > 0,
    Tendsto
      (fun n : ℕ => (volume.restrict (Ioo (0 : ℝ) 1)).real
        {α : ℝ | ε ≤ |(1 / Lnorm n) *
          ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j *
            (Bremainder α n j - ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j)|})
      atTop (𝓝 0)

/-- The §7 set: the end terms below the trim, together with the difference
between the bounded-remainder sums over the random §7 bulk and the
deterministic §4 bulk of display (19). -/
def s7Set (c : ℝ) (n : ℕ) (ε : ℝ) : Set ℝ :=
  {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
    ε ≤ |endTerms c α n + (randRemainderSum c α n - detRemainderSum α n)|}

/-- **§7, Lemma 7.1 together with the §7/§4 index-set bridge**, in exactly the
form the assembly consumes: the end terms below `c·H`, plus the difference
between the two bulk conventions, vanish in probability.

This is the *only* hypothesis of the master theorem that is not already a named
statement elsewhere in the tree.  Its two halves are

* `(1/L)∑_{j < c·H} (−1)^j Φ(x_j,u_j) → 0`, display (44) of Lemma 7.1 (the
  `O(H)` trimming, with the uniform tail `P(|Φ| > t) ≤ C/(1+t)` of
  Lemma 2.3(ii)); and
* `(1/L)[∑_{j ∈ Marks.bulkIndices c α n} − ∑_{j ∈ Section4.bulkJ n}]
  (−1)^j B_j → 0`, the index-set bridge, which is the same obstruction as
  `Kwon1002.TupleFinal.bulk_window_bridge_tuple` read at `k = 1` on the
  bounded remainder rather than on the mark event. -/
def Section7EndTerms (c : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n : ℕ => (volume (s7Set c n ε)).toReal) atTop (𝓝 0)

lemma detRemainder_centered_eq (α : ℝ) (n : ℕ) :
    detRemainderSum α n - detRemainderCenter n
      = (1 / Lnorm n) * ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j *
          (Bremainder α n j - ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j) := by
  unfold detRemainderSum detRemainderCenter
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- The §6 set in the shape Part D consumes. -/
def p64Set (n : ℕ) (ε : ℝ) : Set ℝ :=
  {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ ε ≤ |detRemainderSum α n - detRemainderCenter n|}

lemma prop64_form (n : ℕ) (ε : ℝ) :
    (volume.restrict (Ioo (0 : ℝ) 1)).real
        {α : ℝ | ε ≤ |(1 / Lnorm n) *
          ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j *
            (Bremainder α n j - ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j)|}
      = (volume (p64Set n ε)).toReal := by
  have hset : {α : ℝ | ε ≤ |(1 / Lnorm n) *
        ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j *
          (Bremainder α n j - ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j)|} ∩ Ioo (0 : ℝ) 1
      = p64Set n ε := by
    ext α
    simp only [p64Set, Set.mem_inter_iff, Set.mem_setOf_eq, detRemainder_centered_eq]
    exact and_comm
  unfold Measure.real
  rw [Measure.restrict_apply' measurableSet_Ioo, hset]

lemma vol_nonIrrational_zero : volume {x : ℝ | ¬ Irrational x} = 0 := by
  have hc : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have hset : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
    ext x; simp [Irrational]
  rw [hset]; exact hc.measure_zero volume

/-- **The master assembly, conditional on exactly three inputs.**

`Erdos1002Conclusion` — Kwon's Theorem 1.1, pointwise convergence of the
distribution functions of `S_N(α)/log N` under Lebesgue measure on `(0,1)` to
the Cauchy distribution function of scale `1/(2π)` — follows from

1. `PrincipalCauchyLaw c`, Corollary 5.3 (`Kwon1002.principal_cauchy_law`,
   discharged in `erdos1002Conclusion_of_section7` from the definitionally
   equal `Kwon1002.CorFinal.principal_cauchy_law_F`);
2. `Prop64Statement`, Proposition 6.4
   (`Kwon1002.prop_6_4_bounded_remainder_weak_law`);
3. `Section7EndTerms c`, §7's Lemma 7.1 together with the §7/§4 index-set
   bridge,

for **any** trimming constant `c`.  Everything else — the exact §7
decomposition, Slutsky, the symmetry `S_N(1-α) = -S_N(α)`, the vanishing of the
deterministic centering, and the passage back to distribution functions — is
proved here outright.  In particular the centering removal
(`erdos1002Conclusion_of_shifted`) uses no hypothesis at all. -/
theorem erdos1002Conclusion_of (c : ℝ) (hprincipal : PrincipalCauchyLaw c)
    (hprop64 : Prop64Statement) (hstop : Section7EndTerms c) :
    Erdos1002Conclusion := by
  obtain ⟨b, hb⟩ := hprincipal
  set cs : ℕ → ℝ := fun n => b n + detRemainderCenter n with hcsdef
  refine erdos1002Conclusion_of_shifted (cs := cs) ?_
  set X : ℕ → ℝ → ℝ := fun n α => normalizedRotationSum n α - cs n with hXdef
  set V : ℕ → ℝ → ℝ := fun n α => bulkSum c α n - b n with hVdef
  have hsmall : ∀ ε > 0, Tendsto (fun n : ℕ => (volume (gapSet X V n ε)).toReal)
      atTop (𝓝 0) := by
    intro ε hε
    have hp := hprop64 (ε / 2) (by linarith)
    simp only [prop64_form] at hp
    have hs := hstop (ε / 2) (by linarith)
    refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_
      (by simpa using hp.add hs)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsub : gapSet X V n ε
        ⊆ p64Set n (ε / 2) ∪ s7Set c n (ε / 2) ∪ {x : ℝ | ¬ Irrational x} := by
      rintro α ⟨hα, hgap⟩
      by_cases hirr : Irrational α
      · have hdec := normalizedRotationSum_decomp c hα hirr hn
        have hXV : X n α - V n α
            = (detRemainderSum α n - detRemainderCenter n)
              + (endTerms c α n + (randRemainderSum c α n - detRemainderSum α n)) := by
          simp only [hXdef, hVdef, hcsdef]
          rw [hdec]; ring
        rw [hXV] at hgap
        have htri := abs_add_le (detRemainderSum α n - detRemainderCenter n)
          (endTerms c α n + (randRemainderSum c α n - detRemainderSum α n))
        rcases le_or_gt (ε / 2) |detRemainderSum α n - detRemainderCenter n| with h | h
        · exact Or.inl (Or.inl ⟨hα, h⟩)
        · refine Or.inl (Or.inr ⟨hα, ?_⟩)
          linarith
      · exact Or.inr hirr
    have hfin : volume (p64Set n (ε / 2)) + volume (s7Set c n (ε / 2)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨vol_ne_top fun α hα => hα.1, vol_ne_top fun α hα => hα.1⟩
    have hle : volume (gapSet X V n ε)
        ≤ volume (p64Set n (ε / 2)) + volume (s7Set c n (ε / 2)) := by
      calc volume (gapSet X V n ε)
          ≤ volume (p64Set n (ε / 2) ∪ s7Set c n (ε / 2) ∪ {x : ℝ | ¬ Irrational x}) :=
            measure_mono hsub
        _ ≤ volume (p64Set n (ε / 2) ∪ s7Set c n (ε / 2))
              + volume {x : ℝ | ¬ Irrational x} := measure_union_le _ _
        _ = volume (p64Set n (ε / 2) ∪ s7Set c n (ε / 2)) := by
            rw [vol_nonIrrational_zero, add_zero]
        _ ≤ _ := measure_union_le _ _
    have := ENNReal.toReal_mono hfin hle
    rwa [ENNReal.toReal_add (vol_ne_top fun α hα => hα.1)
      (vol_ne_top fun α hα => hα.1)] at this
  exact fun x => tendsto_cdf_of_perturbation X V cauchyLimitCDF continuous_cauchyLimitCDF
    (fun y => hb y) hsmall x


/-- **The endgame, in one line.**  Feeding the two named in-tree targets to the
master assembly leaves `Section7EndTerms c` as the *only* statement between the
development and Kwon's Theorem 1.1 that is not already a named target
elsewhere in `Kwon1002/`.

This declaration is sorry-tainted, through
`Kwon1002.CorFinal.principal_cauchy_law_F` and
`Kwon1002.prop_6_4_bounded_remainder_weak_law` and through nothing else; it is
recorded because it is the shape of the endgame, not because it proves
anything.

Hypothesis 1 is fed from `CorFinal`, not from the canonical
`Kwon1002.principal_cauchy_law`: the two are the same `Prop` (the guard below
checks it by `rfl`), but the canonical name is a bare `sorry` declared *below*
every module that could prove it, whereas the `CorFinal` form carries only the
two §5 residuals of that file.  Discharging those two residuals therefore
discharges hypothesis 1 here, which is not true of the canonical name. -/
theorem erdos1002Conclusion_of_section7 (c : ℝ) (hstop : Section7EndTerms c) :
    Erdos1002Conclusion :=
  erdos1002Conclusion_of c (CorFinal.principal_cauchy_law_F c)
    prop_6_4_bounded_remainder_weak_law hstop

/-- The official (existential) form Erdős asked for, from the same three
inputs. -/
theorem erdos1002Official_of (c : ℝ) (hprincipal : PrincipalCauchyLaw c)
    (hprop64 : Prop64Statement) (hstop : Section7EndTerms c) :
    Erdos1002Official :=
  official_of_conclusion (erdos1002Conclusion_of c hprincipal hprop64 hstop)

end

end Master

end Kwon1002


/- **Statement guards.**  Each `example` forces the hypothesis defined above to
be the *same statement* as the canonical one in the tree.  They mention sorried
declarations, so they are anonymous and nothing proved above depends on them. -/
example : ∀ c : ℝ, Kwon1002.Master.PrincipalCauchyLaw c := @Kwon1002.principal_cauchy_law

example : ∀ c : ℝ, Kwon1002.Master.PrincipalCauchyLaw c :=
  @Kwon1002.CorFinal.principal_cauchy_law_F

example : @Kwon1002.principal_cauchy_law = @Kwon1002.CorFinal.principal_cauchy_law_F := rfl

example : Kwon1002.Master.Prop64Statement :=
  Kwon1002.prop_6_4_bounded_remainder_weak_law
