import Kwon1002.PoissonLimit
import Kwon1002.Prop64Final
import Kwon1002.CorFinal
import Mathlib.NumberTheory.Harmonic.Bounds

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
   file).  The canonical root name is imported from `Kwon1002.Prop64Final`
   and is backed by the completed, axiom-clean §6 proof.
3. `Section7EndTerms c` — §7's Lemma 7.1 together with the §7/§4 index-set
   bridge, defined in Part F.  Its two halves are the `O(H)` trimming below
   `c·H` and the passage between `Marks.bulkIndices c α n` (random, §7) and
   `Section4.bulkJ n` (deterministic, display (19)).  This is the only one of
   the three that is not already a named statement elsewhere in `Kwon1002/`;
   `erdos1002Conclusion_of_section7` records that fact by discharging the
   other two against the in-tree targets.

   **The first half is PROVED** (Parts G and H below).  Display (46), the
   pointwise cap `|Φ(x,u)| ≤ 1/(8x) + 1/2`, is proved (`abs_Phi_le`) and read on
   the Gauss orbit as `|Φ(x_j,u_j)| ≤ a_{j+1}/8 + 5/8` (`abs_Phi_orbit_le`); the
   trim is proved to carry `O(H)` positions (`card_trimIndices_le`); and
   `abs_endTerms_le` combines them into
   `|end terms| ≤ (1/L)[(1/8)Σ_{j<c·H} a_{j+1} + (5/8)(c·H+1)]`.  The second
   summand is proved to vanish (`tendsto_trim_deterministic`, `H/L = L^{-1/4}`)
   and the digit sum to vanish in probability (`tendsto_window_digitSum`), so
   `tendsto_endTerms_prob` gives display (44) outright, for every `c ≥ 0`.  The
   uniform tail `P(a_{j+1} ≥ t) ≤ C/t` it needs — under **Lebesgue** measure on
   `(0,1)` and at **every** digit index — is `Kwon1002.digit_tail_product` of
   `Kwon1002/DigitTail.lean` read at one level; the Gauss-to-Lebesgue transport
   and the level shift are inside that proof already.

   **The second half is PROVED**, in `Kwon1002/Section7Bridge.lean`, which sits
   above this module.  Part I here names it `Section7Bridge c` and proves
   `Section7EndTerms c` from it (`section7EndTerms_of_bridge`), so
   `erdos1002Conclusion_of_bridge` takes the bridge in place of hypothesis 3;
   `Section7.section7Bridge_holds` then discharges it outright and
   `Section7.section7EndTerms_holds` discharges the whole of hypothesis 3.
   The content is `τ_n = L/λ + O_ℙ(H)`: display (20)'s large deviation
   (`LargeDeviation.display20_of_pos`, proved) applied at the two deterministic
   thresholds `q_j < n/(2E*)` and `q_j > n` that bracket the stopping time,
   through the height identity `N_j = nβ_{j−1} − E_j` of (2) and (7) and the
   classical sandwich `1/(2q_j) ≤ β_{j−1} ≤ 1/q_j`.  Only Proposition 2.2's
   uniform cap `|B_j| ≤ C₀` is then needed on the `O(H)` levels the two index
   sets disagree about.

   **Consequence.**  After `Kwon1002/Section7Bridge.lean` the master theorem
   carries only hypotheses 1 and 2:
   `Section7.erdos1002Conclusion_of_principal_and_prop64`.

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

/-- Proposition 6.4, the bounded-remainder weak law: the statement of the
completed `Kwon1002.prop_6_4_bounded_remainder_weak_law`, reproduced token for
token.  Checked by the `example` at the very bottom of this file. -/
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

This declaration now uses the completed Proposition 6.4.  Its only remaining
historical leaves come through `Kwon1002.CorFinal.principal_cauchy_law_F`;
the fully discharged principal-law route is supplied later by
`Kwon1002.TailTransferCauchy`.

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

/-! ## Part G, the `O(H)` trim of Lemma 7.1

The first of the two halves of `Section7EndTerms`.  Everything deterministic
about it is proved here; what is left is one named probabilistic input, stated
on `abs_endTerms_le`.
-/

lemma abs_Phi_le {x u : ℝ} (hx : 0 < x) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |Phi x u| ≤ 1 / (8 * x) + 1 / 2 := by
  have hnum0 : 0 ≤ u * (1 - u) := mul_nonneg hu0 (by linarith)
  have hnum1 : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have h2x : (0 : ℝ) < 2 * x := by linarith
  have h8x : (0 : ℝ) < 8 * x := by linarith
  have hupper : u * (1 - u) / (2 * x) ≤ 1 / (8 * x) := by
    rw [div_le_div_iff₀ h2x h8x]
    nlinarith
  have hlower : 0 ≤ u * (1 - u) / (2 * x) := by positivity
  have hinv : (0 : ℝ) < 1 / (8 * x) := by positivity
  rw [abs_le]
  constructor
  · unfold Phi; linarith
  · unfold Phi; linarith

lemma abs_Phi_orbit_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n j : ℕ) :
    |Phi (gaussIter α j) (carry α n j)| ≤ (digit α j : ℝ) / 8 + 5 / 8 := by
  have hx := gaussIter_mem_Ioo hα hirr j
  have hu0 : 0 ≤ carry α n j := Int.fract_nonneg _
  have hu1 : carry α n j ≤ 1 := (Int.fract_lt_one _).le
  have h := abs_Phi_le hx.1 hu0 hu1
  have hsplit := inv_gaussIter_eq hα hirr j
  have hnext := gaussIter_mem_Ioo hα hirr (j + 1)
  have hcap : 1 / (8 * gaussIter α j) ≤ ((digit α j : ℝ) + 1) / 8 := by
    have hinv : 1 / (8 * gaussIter α j) = (gaussIter α j)⁻¹ / 8 := by
      field_simp
    rw [hinv, hsplit]
    have := hnext.2
    linarith
  linarith

/-- The index set of the §7 trim: the levels below `c·H`. -/
def trimIndices (c α : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (stoppingTime α n)).filter (fun j : ℕ => ¬ (c * Hscale n ≤ (j : ℝ)))

lemma endTerms_eq (c α : ℝ) (n : ℕ) :
    endTerms c α n = (1 / Lnorm n) *
      ∑ j ∈ trimIndices c α n, (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j) := rfl

/-- **The trim has `O(H)` positions**, deterministically and with no input from
the stopping time: every index it carries is below `c·H`. -/
lemma card_trimIndices_le (c α : ℝ) (n : ℕ) (hc : 0 ≤ c * Hscale n) :
    (((trimIndices c α n).card : ℕ) : ℝ) ≤ c * Hscale n + 1 := by
  classical
  have hsub : trimIndices c α n ⊆ Finset.range ⌈c * Hscale n⌉₊ := by
    intro j hj
    simp only [trimIndices, Finset.mem_filter, Finset.mem_range, not_le] at hj
    rw [Finset.mem_range]
    have h2 : c * Hscale n ≤ (⌈c * Hscale n⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast lt_of_lt_of_le hj.2 h2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  have hcast : (((trimIndices c α n).card : ℕ) : ℝ) ≤ ((⌈c * Hscale n⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hceil : ((⌈c * Hscale n⌉₊ : ℕ) : ℝ) < c * Hscale n + 1 := Nat.ceil_lt_add_one hc
  linarith

/-- **The `O(H)` trim of Lemma 7.1, dominated.**

`|end terms| ≤ (1/L)·[ (1/8)·Σ_{j < c·H} a_{j+1} + (5/8)·(c·H + 1) ]`.

The second summand is deterministic and is `O(H/L) = O(L^{-1/4}) → 0`.  The
first is the whole remaining content of this half of `Section7EndTerms`: it is
a sum of `O(H)` continued-fraction digits, each with infinite mean, so it does
not converge pointwise and the passage to `o(L)` is genuinely probabilistic.
It is proved in Part H below (`tendsto_window_digitSum`), from the uniform
Lebesgue tail `P(a_{j+1} ≥ t) ≤ C/t` that `Kwon1002.digit_tail_product`
already supplies at every level.  `tendsto_endTerms_prob` is the conclusion. -/
theorem abs_endTerms_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (c : ℝ) (n : ℕ) (hL : 0 < Lnorm n) (hc : 0 ≤ c * Hscale n) :
    |endTerms c α n|
      ≤ (1 / Lnorm n) *
          ((1 / 8) * ∑ j ∈ trimIndices c α n, (digit α j : ℝ)
            + (5 / 8) * (c * Hscale n + 1)) := by
  classical
  rw [endTerms_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Lnorm n)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hstep : |∑ j ∈ trimIndices c α n, (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j)|
      ≤ ∑ j ∈ trimIndices c α n, ((digit α j : ℝ) / 8 + 5 / 8) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_Phi_orbit_le hα hirr n j
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_trimIndices_le c α n hc
  have hdig : ∑ j ∈ trimIndices c α n, (digit α j : ℝ) / 8
      = (1 / 8) * ∑ j ∈ trimIndices c α n, (digit α j : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hdig]
  have : (((trimIndices c α n).card : ℕ) : ℝ) * (5 / 8) ≤ (5 / 8) * (c * Hscale n + 1) := by
    nlinarith
  linarith

/-- `L = log n → ∞`.  Restated here rather than imported: the tree's copy lives
in `Kwon1002/TupleMeasure.lean`, which sits above this module. -/
lemma tendsto_Lnorm_atTop : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **The deterministic half of the `O(H)` trim vanishes.**  `H/L = L^{-1/4}`,
so the `(5/8)(c·H+1)/L` summand of `abs_endTerms_le` tends to `0` for every
trimming constant `c`.  What is left of that bound is the digit sum alone. -/
theorem tendsto_trim_deterministic (c : ℝ) :
    Tendsto (fun n : ℕ => (1 / Lnorm n) * ((5 / 8) * (c * Hscale n + 1))) atTop (𝓝 0) := by
  have hLtop : Tendsto (fun n : ℕ => Lnorm n) atTop atTop := tendsto_Lnorm_atTop
  have hHL : Tendsto (fun n : ℕ => Hscale n / Lnorm n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (Lnorm n) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hLtop
    refine h0.congr' ?_
    filter_upwards [hLtop.eventually_gt_atTop 0] with n hn
    have h : Hscale n / Lnorm n = (Lnorm n) ^ ((3 / 4 : ℝ) - 1) := by
      rw [Real.rpow_sub hn, Real.rpow_one, Hscale]
    rw [h]
    norm_num
  have hinv : Tendsto (fun n : ℕ => 1 / Lnorm n) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hLtop
  have hsum : Tendsto
      (fun n : ℕ => (5 / 8) * c * (Hscale n / Lnorm n) + (5 / 8) * (1 / Lnorm n))
      atTop (𝓝 0) := by
    have h1 := hHL.const_mul ((5 / 8) * c)
    have h2 := hinv.const_mul (5 / 8 : ℝ)
    simpa using h1.add h2
  refine hsum.congr' ?_
  filter_upwards [hLtop.eventually_gt_atTop 0] with n hn
  field_simp


/-! ## Part H, the digit sum of the trim, and Lemma 7.1's first half

`abs_endTerms_le` leaves exactly one thing between Part G and display (44): the
digit sum `(1/L)·Σ_{j ∈ trimIndices} a_{j+1}`.  It is a sum of `O(H)`
continued-fraction digits, each with infinite mean under Lebesgue measure, so it
does not converge pointwise and the passage to `o(1)` is genuinely
probabilistic.  It is carried out here, and `tendsto_endTerms_prob` closes the
first of the two halves of `Section7EndTerms`.

The input is `Kwon1002.digit_tail_product` of `Kwon1002/DigitTail.lean`, Lemma
3.1(ii) in the unconditional form (15).  Read at one level it is exactly the
uniform tail `P(a_{j+1} ≥ t) ≤ C/t` under **Lebesgue** measure on `(0,1)` and at
**every** level `j`: the Gauss-to-Lebesgue transport (the two measures have
density between `1/(2 log 2)` and `1/log 2`) and the level shift (Gauss
invariance) are both already inside its proof, so neither is a residual here.

The route is the manuscript's.  Cap the digits at `T = ⌈L²⌉₊`.  The capped
first moment of one digit is `Σ_{k<T} P(a ≥ k+1) ≤ C·(1 + log T)` by layer cake
and the harmonic bound, so Markov gives `O(H·log L/L)` for the capped sum, and
the uncapped event costs `O(H/L²)` by the tail again; both are
`O(log L / L^{1/4}) = o(1)`. -/

/-! ### 1. The uniform Lebesgue digit tail, at every level -/

/-- The constant of `Kwon1002.digit_tail_product`, fixed once. -/
def digitTailConst : ℝ := Classical.choose Kwon1002.digit_tail_product

lemma digitTailConst_pos : 0 < digitTailConst :=
  (Classical.choose_spec Kwon1002.digit_tail_product).1

lemma measurable_digit_nat (j : ℕ) : Measurable (fun x : ℝ => digit x j) := by
  have h1 : Measurable (fun x : ℝ => gaussIter x j) :=
    Erdos1002.measurable_gaussMap.iterate j
  have h2 : Measurable (fun x : ℝ => ⌊(gaussIter x j)⁻¹⌋) := h1.inv.floor
  exact (measurable_of_countable (fun n : ℤ => n.toNat)).comp h2

lemma measurableSet_digit_ge (j : ℕ) (t : ℝ) :
    MeasurableSet {α : ℝ | t ≤ (digit α j : ℝ)} :=
  measurableSet_le measurable_const (Kwon1002.measurable_digit_real j)

/-- **The uniform Lebesgue digit tail.**  `P(a_{j+1} ≥ t) ≤ C/t` under Lebesgue
measure on `(0,1)`, at **every** level `j`, with a constant independent of `j`. -/
lemma volume_digit_ge_le (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ t ≤ (digit α j : ℝ)}).toReal
      ≤ digitTailConst / t := by
  have h := (Classical.choose_spec Kwon1002.digit_tail_product).2
      1 (fun _ => j) (fun _ => t) (fun a b _ => Subsingleton.elim a b) (fun _ => ht)
  have hset : {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin 1, ((fun _ => t) i) ≤ ((digit α ((fun _ => j) i) : ℕ) : ℝ)}
      = {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ t ≤ ((digit α j : ℕ) : ℝ)} := by
    ext α; simp
  rw [hset] at h
  simpa [digitTailConst, pow_one, Fin.prod_univ_one, div_eq_mul_inv] using h

lemma volume_digit_ge_le' (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ t ≤ (digit α j : ℝ)}
      ≤ ENNReal.ofReal (digitTailConst / t) := by
  have hfin : volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ t ≤ (digit α j : ℝ)} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (volume_digit_ge_le j ht)

/-! ### 2. Layer cake: the truncated first moment of one digit -/

lemma min_eq_card_filter (a T : ℕ) :
    min a T = ((Finset.range T).filter (fun k => k + 1 ≤ a)).card := by
  classical
  have hfil : (Finset.range T).filter (fun k => k + 1 ≤ a) = Finset.range (min T a) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [hfil, Finset.card_range, Nat.min_comm]

lemma min_digit_eq_sum_indicator (j T : ℕ) (α : ℝ) :
    ((min (digit α j) T : ℕ) : ℝ≥0∞)
      = ∑ k ∈ Finset.range T,
          Set.indicator {β : ℝ | ((k : ℝ) + 1) ≤ (digit β j : ℝ)} (fun _ => (1 : ℝ≥0∞)) α := by
  classical
  have hind : ∀ k : ℕ,
      Set.indicator {β : ℝ | ((k : ℝ) + 1) ≤ (digit β j : ℝ)} (fun _ => (1 : ℝ≥0∞)) α
        = if k + 1 ≤ digit α j then (1 : ℝ≥0∞) else 0 := by
    intro k
    rw [Set.indicator_apply]
    have hiff : (α ∈ {β : ℝ | ((k : ℝ) + 1) ≤ (digit β j : ℝ)}) ↔ k + 1 ≤ digit α j := by
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; exact_mod_cast (by push_cast at h ⊢; linarith : ((k + 1 : ℕ) : ℝ) ≤ (digit α j : ℝ))
      · intro h
        have : ((k + 1 : ℕ) : ℝ) ≤ ((digit α j : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at this
        linarith
    by_cases h : k + 1 ≤ digit α j
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
  simp only [hind]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    mul_one, min_eq_card_filter]

lemma lintegral_min_digit_le (j T : ℕ) (_hT : 1 ≤ T) :
    ∫⁻ α, ((min (digit α j) T : ℕ) : ℝ≥0∞) ∂(volume.restrict (Ioo (0 : ℝ) 1))
      ≤ ENNReal.ofReal (digitTailConst * (1 + Real.log T)) := by
  classical
  have hmeas : ∀ k : ℕ, MeasurableSet {β : ℝ | ((k : ℝ) + 1) ≤ (digit β j : ℝ)} :=
    fun k => measurableSet_digit_ge j _
  calc ∫⁻ α, ((min (digit α j) T : ℕ) : ℝ≥0∞) ∂(volume.restrict (Ioo (0 : ℝ) 1))
      = ∫⁻ α, (∑ k ∈ Finset.range T,
            Set.indicator {β : ℝ | ((k : ℝ) + 1) ≤ (digit β j : ℝ)} (fun _ => (1 : ℝ≥0∞)) α)
          ∂(volume.restrict (Ioo (0 : ℝ) 1)) := by
        exact lintegral_congr (fun α => min_digit_eq_sum_indicator j T α)
    _ = ∑ k ∈ Finset.range T,
          (volume.restrict (Ioo (0 : ℝ) 1)) {β : ℝ | ((k : ℝ) + 1) ≤ (digit β j : ℝ)} := by
        rw [lintegral_finset_sum _ (fun k _ => (measurable_const.indicator (hmeas k)))]
        exact Finset.sum_congr rfl fun k _ => by
          rw [lintegral_indicator_const (hmeas k), one_mul]
    _ ≤ ∑ k ∈ Finset.range T, ENNReal.ofReal (digitTailConst / ((k : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
          have h := (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))
          linarith
        rw [Measure.restrict_apply (hmeas k)]
        have hset : {β : ℝ | ((k : ℝ) + 1) ≤ (digit β j : ℝ)} ∩ Ioo (0 : ℝ) 1
            = {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ ((k : ℝ) + 1) ≤ (digit α j : ℝ)} := by
          ext α; simp [and_comm]
        rw [hset]
        exact volume_digit_ge_le' j hk
    _ ≤ ENNReal.ofReal (digitTailConst * (1 + Real.log T)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg
          (fun k _ => div_nonneg digitTailConst_pos.le (by positivity))]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsum : ∑ k ∈ Finset.range T, digitTailConst / ((k : ℝ) + 1)
            = digitTailConst * ∑ k ∈ Finset.range T, ((k : ℝ) + 1)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [div_eq_mul_inv]
        have hharm : ((harmonic T : ℚ) : ℝ) = ∑ k ∈ Finset.range T, ((k : ℝ) + 1)⁻¹ := by
          rw [harmonic, Rat.cast_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          push_cast
          ring
        rw [hsum, ← hharm]
        exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log T) digitTailConst_pos.le

/-! ### 3. The trim window, and the digit sum capped at `T` -/

/-- The window the trim lives in: the first `⌈c·H⌉₊` levels. -/
def trimLen (c : ℝ) (n : ℕ) : ℕ := ⌈c * Hscale n⌉₊

lemma trimIndices_subset (c α : ℝ) (n : ℕ) :
    trimIndices c α n ⊆ Finset.range (trimLen c n) := by
  intro j hj
  simp only [trimIndices, Finset.mem_filter, Finset.mem_range, not_le] at hj
  rw [Finset.mem_range, trimLen]
  have h2 : c * Hscale n ≤ (⌈c * Hscale n⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast lt_of_lt_of_le hj.2 h2

lemma sum_trimIndices_le_window (c α : ℝ) (n : ℕ) :
    ∑ j ∈ trimIndices c α n, (digit α j : ℝ)
      ≤ ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ) :=
  Finset.sum_le_sum_of_subset_of_nonneg (trimIndices_subset c α n)
    (fun _ _ _ => Nat.cast_nonneg _)

/-- The digits over the trim window, each capped at `T`. -/
def cappedDigitSum (c : ℝ) (n T : ℕ) (α : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (trimLen c n), ((min (digit α j) T : ℕ) : ℝ≥0∞)

lemma measurable_cappedDigitSum (c : ℝ) (n T : ℕ) :
    Measurable (cappedDigitSum c n T) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_of_countable (fun m : ℕ => (m : ℝ≥0∞))).comp
    ((measurable_digit_nat j).min measurable_const)

lemma lintegral_cappedDigitSum_le (c : ℝ) (n T : ℕ) (hT : 1 ≤ T) :
    ∫⁻ α, cappedDigitSum c n T α ∂(volume.restrict (Ioo (0 : ℝ) 1))
      ≤ (trimLen c n : ℝ≥0∞) * ENNReal.ofReal (digitTailConst * (1 + Real.log T)) := by
  have hmeas : ∀ j ∈ Finset.range (trimLen c n),
      Measurable (fun α : ℝ => ((min (digit α j) T : ℕ) : ℝ≥0∞)) := fun j _ =>
    (measurable_of_countable (fun m : ℕ => (m : ℝ≥0∞))).comp
      ((measurable_digit_nat j).min measurable_const)
  calc ∫⁻ α, cappedDigitSum c n T α ∂(volume.restrict (Ioo (0 : ℝ) 1))
      = ∑ j ∈ Finset.range (trimLen c n),
          ∫⁻ α, ((min (digit α j) T : ℕ) : ℝ≥0∞) ∂(volume.restrict (Ioo (0 : ℝ) 1)) :=
        lintegral_finset_sum _ hmeas
    _ ≤ ∑ _j ∈ Finset.range (trimLen c n),
          ENNReal.ofReal (digitTailConst * (1 + Real.log T)) :=
        Finset.sum_le_sum fun j _ => lintegral_min_digit_le j T hT
    _ = (trimLen c n : ℝ≥0∞) * ENNReal.ofReal (digitTailConst * (1 + Real.log T)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Markov on the capped digit sum.** -/
lemma meas_cappedDigitSum_ge (c : ℝ) (n T : ℕ) (hT : 1 ≤ T) {r : ℝ≥0∞}
    (hr0 : r ≠ 0) (hrtop : r ≠ ⊤) :
    (volume.restrict (Ioo (0 : ℝ) 1)) {α : ℝ | r ≤ cappedDigitSum c n T α}
      ≤ ((trimLen c n : ℝ≥0∞)
          * ENNReal.ofReal (digitTailConst * (1 + Real.log T))) / r := by
  refine le_trans
    (meas_ge_le_lintegral_div (measurable_cappedDigitSum c n T).aemeasurable hr0 hrtop) ?_
  exact ENNReal.div_le_div_right (lintegral_cappedDigitSum_le c n T hT) r

/-! ### 4. The untruncated event, and the digit-sum estimate -/

/-- The event that some digit in the trim window exceeds the cap. -/
def bigDigitSet (c : ℝ) (n T : ℕ) : Set ℝ :=
  {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
    ∃ j ∈ Finset.range (trimLen c n), (T : ℝ) ≤ (digit α j : ℝ)}

lemma volume_bigDigitSet_le (c : ℝ) (n T : ℕ) (hT : 1 ≤ T) :
    volume (bigDigitSet c n T)
      ≤ (trimLen c n : ℝ≥0∞) * ENNReal.ofReal (digitTailConst / T) := by
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hsub : bigDigitSet c n T ⊆ ⋃ j ∈ Finset.range (trimLen c n),
      {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ (T : ℝ) ≤ (digit α j : ℝ)} := by
    rintro α ⟨hα, j, hj, hdj⟩
    exact Set.mem_biUnion hj ⟨hα, hdj⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  calc ∑ j ∈ Finset.range (trimLen c n),
        volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ (T : ℝ) ≤ (digit α j : ℝ)}
      ≤ ∑ _j ∈ Finset.range (trimLen c n), ENNReal.ofReal (digitTailConst / T) :=
        Finset.sum_le_sum fun j _ => volume_digit_ge_le' j hT'
    _ = (trimLen c n : ℝ≥0∞) * ENNReal.ofReal (digitTailConst / T) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-! ### 5. The digit-sum estimate -/

/-- **The digit sum below the trim, estimated.**  For every cap `T ≥ 1` and
every level `r > 0`, with `M = ⌈c·H⌉₊` the length of the trim window,

`P( Σ_{j < M} a_{j+1} ≥ r ) ≤ M·C/T + M·C·(1 + log T)/r`,

the first summand discarding the event that some digit exceeds the cap and the
second being Markov applied to the capped sum. -/
theorem volume_window_digitSum_ge_le (c : ℝ) (n T : ℕ) (hT : 1 ≤ T) {r : ℝ} (hr : 0 < r) :
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        r ≤ ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ)}).toReal
      ≤ (trimLen c n : ℝ) * digitTailConst / T
        + (trimLen c n : ℝ) * digitTailConst * (1 + Real.log T) / r := by
  classical
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < (T : ℝ) := lt_of_lt_of_le zero_lt_one hT'
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT'
  have hCpos := digitTailConst_pos
  set A : Set ℝ := {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      r ≤ ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ)} with hAdef
  set D : Set ℝ := {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      ENNReal.ofReal r ≤ cappedDigitSum c n T α} with hDdef
  -- (a) the split
  have hsub : A ⊆ bigDigitSet c n T ∪ D := by
    intro α hα
    by_cases hb : α ∈ bigDigitSet c n T
    · exact Or.inl hb
    · refine Or.inr ⟨hα.1, ?_⟩
      have hmin : ∀ j ∈ Finset.range (trimLen c n), min (digit α j) T = digit α j := by
        intro j hj
        have hlt : (digit α j : ℝ) < (T : ℝ) := by
          by_contra hcon
          exact hb ⟨hα.1, j, hj, not_lt.mp hcon⟩
        have : digit α j < T := by exact_mod_cast hlt
        omega
      have hcap : cappedDigitSum c n T α
          = ENNReal.ofReal (∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ)) := by
        rw [cappedDigitSum,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => Nat.cast_nonneg _)]
        exact Finset.sum_congr rfl fun j hj => by
          rw [hmin j hj, ENNReal.ofReal_natCast]
      rw [hcap]
      exact ENNReal.ofReal_le_ofReal hα.2
  -- (b) the two pieces
  have hBle : volume (bigDigitSet c n T)
      ≤ ENNReal.ofReal ((trimLen c n : ℝ) * digitTailConst / T) := by
    refine le_trans (volume_bigDigitSet_le c n T hT) ?_
    rw [← ENNReal.ofReal_natCast (trimLen c n),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_assoc]
  have hSmeas : MeasurableSet {α : ℝ | ENNReal.ofReal r ≤ cappedDigitSum c n T α} :=
    measurableSet_le measurable_const (measurable_cappedDigitSum c n T)
  have hDle : volume D
      ≤ ENNReal.ofReal ((trimLen c n : ℝ) * digitTailConst * (1 + Real.log T) / r) := by
    have hDeq : volume D
        = (volume.restrict (Ioo (0 : ℝ) 1))
            {α : ℝ | ENNReal.ofReal r ≤ cappedDigitSum c n T α} := by
      rw [Measure.restrict_apply hSmeas]
      congr 1
      ext α
      simp only [hDdef, Set.mem_setOf_eq, Set.mem_inter_iff]
      exact and_comm
    rw [hDeq]
    refine le_trans (meas_cappedDigitSum_ge c n T hT
      (by simpa using hr) ENNReal.ofReal_ne_top) ?_
    rw [← ENNReal.ofReal_natCast (trimLen c n),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_div_of_pos hr, ← mul_assoc]
  -- (c) combine
  have hXnn : (0 : ℝ) ≤ (trimLen c n : ℝ) * digitTailConst / T :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hCpos.le) hTpos.le
  have hYnn : (0 : ℝ) ≤ (trimLen c n : ℝ) * digitTailConst * (1 + Real.log T) / r :=
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCpos.le) (by linarith)) hr.le
  have hfin : volume A ≤ ENNReal.ofReal
      ((trimLen c n : ℝ) * digitTailConst / T
        + (trimLen c n : ℝ) * digitTailConst * (1 + Real.log T) / r) := by
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    rw [ENNReal.ofReal_add hXnn hYnn]
    exact add_le_add hBle hDle
  calc (volume A).toReal
      ≤ (ENNReal.ofReal ((trimLen c n : ℝ) * digitTailConst / T
          + (trimLen c n : ℝ) * digitTailConst * (1 + Real.log T) / r)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = _ := ENNReal.toReal_ofReal (by linarith)

/-! ### 6. Lemma 7.1's first half -/

lemma tendsto_Hscale_log_div_Lnorm :
    Tendsto (fun n : ℕ => Hscale n * Real.log (Lnorm n) / Lnorm n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 4)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hL : Tendsto (fun n : ℕ => Lnorm n) atTop atTop := tendsto_Lnorm_atTop
  refine (hlog.comp hL).congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0] with n hn
  have h1 : Hscale n / Lnorm n = (Lnorm n) ^ ((3 / 4 : ℝ) - 1) := by
    rw [Real.rpow_sub hn, Real.rpow_one, Hscale]
  have h2 : (Lnorm n) ^ ((3 / 4 : ℝ) - 1) = ((Lnorm n) ^ ((1 : ℝ) / 4))⁻¹ := by
    rw [show (3 / 4 : ℝ) - 1 = -((1 : ℝ) / 4) by norm_num, Real.rpow_neg hn.le]
  simp only [Function.comp_apply]
  rw [div_eq_mul_inv (Real.log (Lnorm n)) ((Lnorm n) ^ ((1 : ℝ) / 4)), ← h2, ← h1]
  ring

/-- **The first half of `Section7EndTerms`, closed.**  `(1/L)·Σ_{j < c·H} a_{j+1}`
tends to `0` in probability under Lebesgue measure on `(0,1)`.  With
`abs_endTerms_le` and `tendsto_trim_deterministic` this is everything the `O(H)`
trim of Lemma 7.1 needs.

The cap is `T = ⌈L²⌉₊`: the untruncated event costs `O(H/L²)` and the Markov
term `O(H·log L/L) = O(log L / L^{1/4})`, both `o(1)`. -/
theorem tendsto_window_digitSum (c : ℝ) (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          ε ≤ (1 / Lnorm n) * ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ)}).toReal)
      atTop (𝓝 0) := by
  have hCpos := digitTailConst_pos
  set K : ℝ := (c + 1) * digitTailConst * (1 + 4 / ε) with hKdef
  have hmaj : Tendsto (fun n : ℕ => K * (Hscale n * Real.log (Lnorm n) / Lnorm n))
      atTop (𝓝 0) := by
    simpa using tendsto_Hscale_log_div_Lnorm.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ hmaj
  filter_upwards [tendsto_Lnorm_atTop.eventually_ge_atTop (8 : ℝ)] with n hn
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  have hL1 : (1 : ℝ) ≤ Lnorm n := by linarith
  have hH1 : (1 : ℝ) ≤ Hscale n := by
    have h := Real.rpow_le_rpow zero_le_one hL1 (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rwa [Real.one_rpow, ← Hscale] at h
  have hH0 : (0 : ℝ) ≤ Hscale n := by linarith
  have hlogL : (1 : ℝ) ≤ Real.log (Lnorm n) := by
    have he : Real.exp 1 ≤ Lnorm n :=
      le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
    exact (Real.le_log_iff_exp_le hL0).mpr he
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  set T : ℕ := ⌈Lnorm n * Lnorm n⌉₊ with hTdef
  have hTge : Lnorm n * Lnorm n ≤ (T : ℝ) := Nat.le_ceil _
  have hTlt : (T : ℝ) < Lnorm n * Lnorm n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLT : Lnorm n ≤ (T : ℝ) := by nlinarith
  have hT1' : (1 : ℝ) ≤ (T : ℝ) := by linarith
  have hT1 : 1 ≤ T := by exact_mod_cast hT1'
  have hTpos : (0 : ℝ) < (T : ℝ) := by linarith
  have hsetEq : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        ε ≤ (1 / Lnorm n) * ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ)}
      = {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        ε * Lnorm n ≤ ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ)} := by
    ext α
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hL0]
  rw [hsetEq]
  have hr : (0 : ℝ) < ε * Lnorm n := by positivity
  refine le_trans (volume_window_digitSum_ge_le c n T hT1 hr) ?_
  have hM : (trimLen c n : ℝ) ≤ (c + 1) * Hscale n := by
    have h0 : (0 : ℝ) ≤ c * Hscale n := mul_nonneg hc hH0
    have hMlt : (trimLen c n : ℝ) < c * Hscale n + 1 := by
      rw [trimLen]; exact Nat.ceil_lt_add_one h0
    nlinarith
  have hlogTle : Real.log T ≤ 1 + 2 * Real.log (Lnorm n) := by
    have hle : (T : ℝ) ≤ 2 * (Lnorm n * Lnorm n) := by nlinarith
    have h1 := Real.log_le_log hTpos hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hL0.ne' hL0.ne'] at h1
    linarith
  have hcapLog : 1 + Real.log T ≤ 4 * Real.log (Lnorm n) := by linarith
  have hcapNN : (0 : ℝ) ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1'
    linarith
  have hdivL : ∀ a b : ℝ, a ≤ b → a / Lnorm n ≤ b / Lnorm n := by
    intro a b h
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hL0.le)
  have hdivT : ∀ a : ℝ, 0 ≤ a → a / (T : ℝ) ≤ a / Lnorm n := by
    intro a ha
    have h := one_div_le_one_div_of_le hL0 hLT
    rw [one_div, one_div] at h
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h ha
  have hdivEL : ∀ a b : ℝ, a ≤ b → a / (ε * Lnorm n) ≤ b / (ε * Lnorm n) := by
    intro a b h
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hr.le)
  set Y : ℝ := Hscale n * Real.log (Lnorm n) / Lnorm n with hYdef
  have hCHnn : (0 : ℝ) ≤ (c + 1) * Hscale n * digitTailConst :=
    mul_nonneg (mul_nonneg (by linarith) hH0) hCpos.le
  have hn1 : (trimLen c n : ℝ) * digitTailConst ≤ (c + 1) * Hscale n * digitTailConst :=
    mul_le_mul_of_nonneg_right hM hCpos.le
  have hterm1 : ((c + 1) * Hscale n * digitTailConst * Real.log (Lnorm n)) / Lnorm n
      = (c + 1) * digitTailConst * Y := by
    rw [hYdef]; field_simp
  have h1 : (trimLen c n : ℝ) * digitTailConst / T ≤ (c + 1) * digitTailConst * Y := by
    refine le_trans (hdivT _ (mul_nonneg (Nat.cast_nonneg _) hCpos.le)) ?_
    refine le_trans (hdivL _ _ hn1) ?_
    rw [← hterm1]
    exact hdivL _ _ (le_mul_of_one_le_right hCHnn hlogL)
  have hn3 : (trimLen c n : ℝ) * digitTailConst * (1 + Real.log T)
      ≤ (c + 1) * Hscale n * digitTailConst * (4 * Real.log (Lnorm n)) :=
    mul_le_mul hn1 hcapLog hcapNN hCHnn
  have hterm2 : ((c + 1) * Hscale n * digitTailConst * (4 * Real.log (Lnorm n)))
        / (ε * Lnorm n)
      = (c + 1) * digitTailConst * (4 / ε) * Y := by
    rw [hYdef]; field_simp
  have h2 : (trimLen c n : ℝ) * digitTailConst * (1 + Real.log T) / (ε * Lnorm n)
      ≤ (c + 1) * digitTailConst * (4 / ε) * Y := by
    rw [← hterm2]
    exact hdivEL _ _ hn3
  have hKY : K * Y
      = (c + 1) * digitTailConst * Y + (c + 1) * digitTailConst * (4 / ε) * Y := by
    rw [hKdef]; ring
  rw [hKY]
  linarith


/-- **The `O(H)` trim of Lemma 7.1, in probability.**  `(1/L)·Σ_{j < c·H} (−1)^j
Φ(x_j,u_j) → 0` in probability under Lebesgue measure on `(0,1)`, for every
trimming constant `c ≥ 0`.  This is display (44), the first of the two halves of
`Section7EndTerms`.

`abs_endTerms_le` splits the bound into the digit sum and a deterministic
`O(H/L)` remainder; `tendsto_trim_deterministic` kills the second and
`tendsto_window_digitSum` the first. -/
theorem tendsto_endTerms_prob (c : ℝ) (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ ε ≤ |endTerms c α n|}).toReal)
      atTop (𝓝 0) := by
  have hkey := tendsto_window_digitSum c hc (show (0 : ℝ) < 4 * ε by linarith)
  refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ hkey
  have hdet := (tendsto_trim_deterministic c).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  filter_upwards [tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ), hdet] with n hL0 hdetn
  have hH0 : (0 : ℝ) ≤ c * Hscale n :=
    mul_nonneg hc (Real.rpow_nonneg (le_of_lt hL0) _)
  set B : Set ℝ := {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      4 * ε ≤ (1 / Lnorm n) * ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ)} with hBdef
  have hsub : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ ε ≤ |endTerms c α n|}
      ⊆ B ∪ {x : ℝ | ¬ Irrational x} := by
    rintro α ⟨hα, hεα⟩
    by_cases hirr : Irrational α
    · refine Or.inl ⟨hα, ?_⟩
      have hbd := abs_endTerms_le hα hirr c n hL0 hH0
      have hwin := sum_trimIndices_le_window c α n
      have hinv : (0 : ℝ) < 1 / Lnorm n := by positivity
      have hstep : (1 / Lnorm n) *
            ((1 / 8) * ∑ j ∈ trimIndices c α n, (digit α j : ℝ)
              + (5 / 8) * (c * Hscale n + 1))
          ≤ (1 / 8) * ((1 / Lnorm n)
              * ∑ j ∈ Finset.range (trimLen c n), (digit α j : ℝ))
            + (1 / Lnorm n) * ((5 / 8) * (c * Hscale n + 1)) := by
        nlinarith [hwin, hinv]
      nlinarith [hbd, hstep, hεα, hdetn]
    · exact Or.inr hirr
  have hBfin : volume B ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  refine ENNReal.toReal_mono hBfin ?_
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [vol_nonIrrational_zero, add_zero]


/-! ## Part I, `Section7EndTerms` reduced to the index-set bridge

Part H proved the first of the two halves, so the third hypothesis of the master
theorem is now exactly its second half, and `erdos1002Conclusion_of_bridge`
records that. -/

/-- **The §7/§4 index-set bridge**, the second half of `Section7EndTerms`:
`(1/L)·[∑_{j ∈ Marks.bulkIndices c α n} − ∑_{j ∈ Section4.bulkJ n}] (−1)^j B_j → 0`
in probability. -/
def Section7Bridge (c : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n : ℕ => (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      ε ≤ |randRemainderSum c α n - detRemainderSum α n|}).toReal) atTop (𝓝 0)

/-- **`Section7EndTerms` is exactly the bridge now.**  Its `O(H)` trimming half
is proved (`tendsto_endTerms_prob`), so the whole hypothesis follows from the
index-set bridge alone. -/
theorem section7EndTerms_of_bridge (c : ℝ) (hc : 0 ≤ c) (hbridge : Section7Bridge c) :
    Section7EndTerms c := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have h1 := tendsto_endTerms_prob c hc hε2
  have h2 := hbridge (ε / 2) hε2
  have hmaj : Tendsto (fun n : ℕ =>
      (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ ε / 2 ≤ |endTerms c α n|}).toReal
        + (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
            ε / 2 ≤ |randRemainderSum c α n - detRemainderSum α n|}).toReal)
      atTop (𝓝 0) := by simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ hmaj
  refine Eventually.of_forall fun n => ?_
  set A : Set ℝ := {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ ε / 2 ≤ |endTerms c α n|} with hAdef
  set B : Set ℝ := {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      ε / 2 ≤ |randRemainderSum c α n - detRemainderSum α n|} with hBdef
  have hsub : s7Set c n ε ⊆ A ∪ B := by
    rintro α ⟨hα, hle⟩
    have htri : |endTerms c α n + (randRemainderSum c α n - detRemainderSum α n)|
        ≤ |endTerms c α n| + |randRemainderSum c α n - detRemainderSum α n| :=
      abs_add_le _ _
    by_cases h : ε / 2 ≤ |endTerms c α n|
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr ⟨hα, by push_neg at h; linarith⟩
  have hAfin : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hBfin : volume B ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  calc (volume (s7Set c n ε)).toReal
      ≤ (volume A + volume B).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩)
          (le_trans (measure_mono hsub) (measure_union_le _ _))
    _ = (volume A).toReal + (volume B).toReal := ENNReal.toReal_add hAfin hBfin

/-- **The master theorem from the bridge.**  Kwon's Theorem 1.1 from Corollary
5.3, Proposition 6.4 and the §7/§4 index-set bridge; §7's `O(H)` trimming is no
longer a hypothesis. -/
theorem erdos1002Conclusion_of_bridge (c : ℝ) (hc : 0 ≤ c)
    (hprincipal : PrincipalCauchyLaw c) (hprop64 : Prop64Statement)
    (hbridge : Section7Bridge c) : Erdos1002Conclusion :=
  erdos1002Conclusion_of c hprincipal hprop64 (section7EndTerms_of_bridge c hc hbridge)

end

end Master

end Kwon1002


/- **Statement guards.**  Each `example` forces the hypothesis defined above to
be the *same statement* as the canonical one in the tree.  They are anonymous,
so nothing proved above depends on the guards themselves. -/
example : ∀ c : ℝ, Kwon1002.Master.PrincipalCauchyLaw c := @Kwon1002.principal_cauchy_law

example : ∀ c : ℝ, Kwon1002.Master.PrincipalCauchyLaw c :=
  @Kwon1002.CorFinal.principal_cauchy_law_F

example : @Kwon1002.principal_cauchy_law = @Kwon1002.CorFinal.principal_cauchy_law_F := rfl

example : Kwon1002.Master.Prop64Statement :=
  Kwon1002.prop_6_4_bounded_remainder_weak_law
