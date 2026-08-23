import Kwon1002.Prop64
import Kwon1002.P42Cases
import Kwon1002.Section6OneBlock
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Util.AssertNoSorry

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

noncomputable section

namespace Prop64

/-- The quotient-valued law of the actual radius-`R` window. -/
def qActualWindowLaw (R n j : ℕ) : Measure (QWindow R) :=
  (actualWindowLaw R n j).map (quotientWindow R)

/-- The one-level form of `digit_tail_product`, kept local to the actual-window
argument so that no downstream production theorem is used. -/
private lemma volume_actual_digit_gt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m K : ℕ),
      volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ K < digit α m}
        ≤ ENNReal.ofReal (C / ((K : ℝ) + 1)) := by
  obtain ⟨C, hC, htail⟩ := digit_tail_product
  refine ⟨C, hC, fun m K ↦ ?_⟩
  have hreal :
      (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ K < digit α m}).toReal
        ≤ C / ((K : ℝ) + 1) := by
    have h := htail 1 (fun _ : Fin 1 ↦ m)
      (fun _ : Fin 1 ↦ (K : ℝ) + 1)
      (fun a b _ ↦ Subsingleton.elim a b)
      (fun _ ↦ by
        show (1 : ℝ) ≤ (K : ℝ) + 1
        have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        linarith)
    have hset :
        {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          ∀ i : Fin 1, (fun _ : Fin 1 ↦ (K : ℝ) + 1) i ≤
            (digit α ((fun _ : Fin 1 ↦ m) i) : ℝ)} =
        {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ K < digit α m} := by
      ext α
      simp only [Set.mem_setOf_eq, and_congr_right_iff]
      intro _
      constructor
      · intro h
        have hm := h 0
        simp only at hm
        exact_mod_cast hm
      · intro h i
        have hr : (K : ℝ) + 1 ≤ (digit α m : ℝ) := by exact_mod_cast h
        simpa using hr
    rw [hset] at h
    simpa [pow_one, Fin.prod_univ_one, div_eq_mul_inv] using h
  have hfin : volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ K < digit α m} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun _ h ↦ h.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Uniform digit truncation for actual quotient windows.  The hypothesis
`R ≤ j` is precisely the room needed to identify coordinate `i` with the
untruncated level `(j - R) + i`; the bound is uniform in both `n` and `j`. -/
theorem qActualWindowLaw_fullDigitCapQ_compl_le (R : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K n j : ℕ), R ≤ j →
      qActualWindowLaw R n j (fullDigitCapQ R K)ᶜ ≤
        ENNReal.ofReal
          (((2 * R + 1 : ℕ) : ℝ) * C / ((K : ℝ) + 1)) := by
  obtain ⟨C, hC, htail⟩ := volume_actual_digit_gt_le
  refine ⟨C, hC, fun K n j hj ↦ ?_⟩
  have hlevel (i : Fin (2 * R + 1)) :
      j + (i : ℕ) - R = (j - R) + (i : ℕ) := by omega
  have hpre :
      (fun α : ℝ ↦ quotientWindow R (actualWindow R α n j)) ⁻¹'
          (fullDigitCapQ R K)ᶜ =
        ⋃ i : Fin (2 * R + 1),
          {α : ℝ | K < digit α ((j - R) + (i : ℕ))} := by
    ext α
    simp only [Set.mem_preimage, Set.mem_compl_iff, fullDigitCapQ,
      Set.mem_setOf_eq, not_forall, not_le, Set.mem_iUnion, quotientWindow,
      actualWindow]
    exact exists_congr fun i ↦ by rw [hlevel i]
  rw [qActualWindowLaw, actualWindowLaw,
    Measure.map_map (measurable_quotientWindow R) (measurable_actualWindow R n j),
    Measure.map_apply
      ((measurable_quotientWindow R).comp (measurable_actualWindow R n j))
      (measurableSet_fullDigitCapQ R K).compl]
  change (volume.restrict (Ioo (0 : ℝ) 1))
      ((fun α : ℝ ↦ quotientWindow R (actualWindow R α n j)) ⁻¹'
        (fullDigitCapQ R K)ᶜ) ≤ _
  rw [hpre]
  refine le_trans (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  have hone (i : Fin (2 * R + 1)) :
      (volume.restrict (Ioo (0 : ℝ) 1))
          {α : ℝ | K < digit α ((j - R) + (i : ℕ))} ≤
        ENNReal.ofReal (C / ((K : ℝ) + 1)) := by
    have hm : MeasurableSet
        {α : ℝ | K < digit α ((j - R) + (i : ℕ))} :=
      measurableSet_lt measurable_const
        (Prop42.measurable_digitNat ((j - R) + (i : ℕ)))
    rw [Measure.restrict_apply hm]
    have hset :
        {α : ℝ | K < digit α ((j - R) + (i : ℕ))} ∩ Ioo (0 : ℝ) 1 =
          {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
            K < digit α ((j - R) + (i : ℕ))} := by
      ext α
      simp [and_comm]
    rw [hset]
    exact htail _ _
  calc
    ∑ i : Fin (2 * R + 1),
        (volume.restrict (Ioo (0 : ℝ) 1))
          {α : ℝ | K < digit α ((j - R) + (i : ℕ))}
        ≤ ∑ _i : Fin (2 * R + 1),
            ENNReal.ofReal (C / ((K : ℝ) + 1)) :=
      Finset.sum_le_sum (fun i _ ↦ hone i)
    _ = ENNReal.ofReal
          (((2 * R + 1 : ℕ) : ℝ) * C / ((K : ℝ) + 1)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

/-! ## Actual-window dense-algebra identities -/

/-- The torus block retained by `digitTruncWindow` is the actual block at
radius `R`.  The room hypothesis is stated at the radius `R + M` at which
the actual window is formed. -/
lemma digitTruncWindow_actual_torus {R M : ℕ} {α : ℝ} {n j : ℕ}
    (hj : R + M + 1 ≤ j) (i : Fin (2 * R + 2)) :
    (digitTruncWindow R M (actualWindow (R + M) α n j)).2.2 i =
      theta α n (j + (i : ℕ) - (R + 1)) := by
  change wTh (actualWindow (R + M) α n j)
      ((i : ℤ) - (R : ℤ) - 1) = _
  rw [wTh_actualWindow (R + M) α n j (by omega) (by omega) (by omega)]
  congr 1
  omega

/-- Actual-window version of identity (31) for one character occurring in a
`DenseElt`.  It uses the proved v5 identity only on actual windows. -/
lemma dense_character_actual_identity (R M : ℕ)
    (c : Fin (2 * R + 2) → ℤ) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ,
        R + M + 1 ≤ j →
        torusChar (∑ i : Fin (2 * R + 2), (c i : ℝ) *
            (digitTruncWindow R M (actualWindow (R + M) α n j)).2.2 i) =
          torusChar ((B (windowWord R α j) : ℝ) * thetaPred α n j +
            (A (windowWord R α j) : ℝ) * theta α n j) := by
  obtain ⟨A, B, hAB⟩ := V5Identity31.window_character_reduction_v5 R c
  refine ⟨A, B, ?_⟩
  intro α hirr hα n j hj
  obtain ⟨m, hm⟩ := hAB α hirr hα n j (by omega)
  have hcoords :
      (∑ i : Fin (2 * R + 2), (c i : ℝ) *
          (digitTruncWindow R M (actualWindow (R + M) α n j)).2.2 i) =
        ∑ i : Fin (2 * R + 2), (c i : ℝ) *
          theta α n (j + (i : ℕ) - (R + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [digitTruncWindow_actual_torus hj i]
  rw [hcoords, hm]
  have hreorder :
      (A (windowWord R α j) : ℝ) * theta α n j +
          (B (windowWord R α j) : ℝ) * thetaPred α n j + (m : ℝ) =
        ((B (windowWord R α j) : ℝ) * thetaPred α n j +
          (A (windowWord R α j) : ℝ) * theta α n j) + (m : ℝ) := by ring
  rw [hreorder, torusChar_add_int]

/-- Identity (31), assembled over all summands of one fixed `DenseElt`, on
the actual window only. -/
theorem denseElt_digitTrunc_actual_identity {R : ℕ} (M : ℕ) (G : DenseElt R) :
    ∃ A B : Fin G.len → (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ,
        R + M + 1 ≤ j →
        G.eval (digitTruncWindow R M (actualWindow (R + M) α n j)) =
          ∑ l : Fin G.len,
            G.D l (digitTruncWindow R M (actualWindow (R + M) α n j)).1 *
              G.g l (digitTruncWindow R M (actualWindow (R + M) α n j)).2.1 *
              torusChar ((B l (windowWord R α j) : ℝ) * thetaPred α n j +
                (A l (windowWord R α j) : ℝ) * theta α n j) := by
  choose A B hAB using fun l : Fin G.len => dense_character_actual_identity R M (G.c l)
  refine ⟨A, B, ?_⟩
  intro α hirr hα n j hj
  unfold DenseElt.eval
  apply Finset.sum_congr rfl
  intro l _
  rw [hAB l α hirr hα n j hj]

/-- The deterministic bulk eventually has room for every coordinate of a
fixed radius. -/
lemma eventually_bulk_radius (R' : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n, R' + 1 ≤ j := by
  filter_upwards [P42Cases.tendsto_Hscale.eventually_ge_atTop
    ((R' + 1 : ℝ) / 200)] with n hn
  intro j hj
  have hlo : 200 * Hscale n ≤ (j : ℝ) := ((Finset.mem_filter.1 hj).2).1
  have hcast : (R' + 1 : ℝ) ≤ 200 * Hscale n := by nlinarith
  exact_mod_cast hcast.trans hlo

/-- Transfer an actual mean to the stationary mean of one fixed symbol. -/
theorem actual_mean_to_symbol_stationary
    {R' K : ℕ} (P : WindowSymbol R' K) (F : WindowSpace R' → ℂ)
    (hactual : ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 →
      ∀ n j : ℕ, R' + 1 ≤ j → F (actualWindow R' α n j) = P.at α n j)
    (honeblock : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, P.at α n j) - P.stationaryIntegral‖ < ε) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, F (actualWindow R' α n j)) -
        P.stationaryIntegral‖ < ε := by
  intro ε hε
  filter_upwards [eventually_bulk_radius R', honeblock ε hε] with n hroom hn
  intro j hj
  have hint :
      (∫ α in Ioo (0 : ℝ) 1, F (actualWindow R' α n j)) =
        ∫ α in Ioo (0 : ℝ) 1, P.at α n j := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
      with α hα hirr
    exact hactual α hirr hα n j (hroom j hj)
  rw [hint]
  exact hn j hj

/-- Dense-algebra specialization of `actual_mean_to_symbol_stationary`. -/
theorem denseElt_digitTrunc_mean_transfer
    {R M K : ℕ} (G : DenseElt R) (P : WindowSymbol (R + M) K)
    (hactual : ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 →
      ∀ n j : ℕ, R + M + 1 ≤ j →
        G.eval (digitTruncWindow R M (actualWindow (R + M) α n j)) = P.at α n j)
    (honeblock : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, P.at α n j) - P.stationaryIntegral‖ < ε) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1,
          G.eval (digitTruncWindow R M (actualWindow (R + M) α n j))) -
        P.stationaryIntegral‖ < ε :=
  actual_mean_to_symbol_stationary P
    (fun w => G.eval (digitTruncWindow R M w)) hactual honeblock

end Prop64

end

end Kwon1002

namespace MeasureTheory

section Bulk

variable {Ω J : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω]

/-- A bulk-uniform estimate against every bounded continuous test function
remains valid along arbitrary bulk choices and subsequences. -/
theorem ProbabilityMeasure.tendsto_of_bulk_uniform_integral
    (μ : ProbabilityMeasure Ω) (μs : ℕ → J → ProbabilityMeasure Ω)
    (bulk : ℕ → Set J)
    (hbulk : ∀ f : BoundedContinuousFunction Ω ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ j ∈ bulk n,
        |(∫ x, f x ∂(μs n j : Measure Ω)) - ∫ x, f x ∂(μ : Measure Ω)| < ε)
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) {js : ℕ → J}
    (hjs : ∀ᶠ k in atTop, js k ∈ bulk (ns k)) :
    Tendsto (fun k ↦ μs (ns k) (js k)) atTop (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f ↦ ?_
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  apply eventually_atTop.mp
  filter_upwards [hns.eventually (hbulk f ε hε), hjs] with k hk hmem
  simpa [Real.dist_eq] using hk (js k) hmem

end Bulk

section PortmanteauConsequences

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- The null-frontier conclusion of Portmanteau, specialized to probability
measures. -/
theorem ProbabilityMeasure.tendsto_measure_nullFrontier
    {ι : Type*} {L : Filter ι} {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (hμ : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (hE : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hE

/-- Layer-cake transfer under the pointwise null-frontier Portmanteau
hypothesis. -/
theorem ProbabilityMeasure.tendsto_integral_of_ae_nullFrontier
    {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : Ω → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ : Measure Ω))
    (hfi : ∀ i, AEStronglyMeasurable f (μs i : Measure Ω))
    (hnn : 0 ≤ f) (hbdd : f ≤ fun _ ↦ M)
    (hfrontier : ∀ᵐ t ∂volume.restrict (Ioc 0 M),
      (μ : Measure Ω) (frontier {x | t ≤ f x}) = 0) :
    Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure Ω)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  have hint : Integrable f (μ : Measure Ω) := by
    refine ⟨hf, HasFiniteIntegral.mono' (integrable_const M).2 ?_⟩
    exact Eventually.of_forall fun x ↦ by
      simpa [abs_of_nonneg (hnn x)] using hbdd x
  have hints : ∀ i, Integrable f (μs i : Measure Ω) := fun i ↦ by
    refine ⟨hfi i, HasFiniteIntegral.mono' (integrable_const M).2 ?_⟩
    exact Eventually.of_forall fun x ↦ by
      simpa [abs_of_nonneg (hnn x)] using hbdd x
  rw [hint.integral_eq_integral_Ioc_meas_le (Eventually.of_forall hnn)
    (Eventually.of_forall hbdd)]
  simp_rw [(hints _).integral_eq_integral_Ioc_meas_le
    (Eventually.of_forall hnn) (Eventually.of_forall hbdd)]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ 1)
  · intro i
    have hm : Measurable
        (fun t : ℝ ↦ (μs i : Measure Ω).real {x : Ω | t ≤ f x}) :=
      Antitone.measurable fun (s t : ℝ) hst ↦ measureReal_mono
        (μ := (μs i : Measure Ω)) (fun _ hx ↦ hst.trans hx) (measure_ne_top _ _)
    exact hm.aestronglyMeasurable.restrict
  · haveI : IsFiniteMeasure (volume.restrict (Ioc 0 M)) := by
      constructor
      simp
    exact integrable_const 1
  · intro i
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    simpa only [Pi.one_apply] using measureReal_le_one (μ := (μs i : Measure Ω))
  · filter_upwards [hfrontier] with t ht
    exact (ENNReal.tendsto_toReal
      (measure_ne_top (μ : Measure Ω) {x | t ≤ f x})).comp
      (ProbabilityMeasure.tendsto_measure_nullFrontier hμ ht)

omit [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] in
/-- At almost every threshold, an a.e.-continuous measurable function has a
null frontier for its closed superlevel set. -/
lemma ae_nullFrontier_superlevel_of_ae_continuous
    (μ : ProbabilityMeasure Ω) {f : Ω → ℝ} (hf : Measurable f)
    (hcont : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x) :
    ∀ᵐ t ∂volume, (μ : Measure Ω) (frontier {x | t ≤ f x}) = 0 := by
  have hbad : (μ : Measure Ω) {x | ¬ContinuousAt f x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    simpa only [mem_setOf_eq, not_not] using hcont
  filter_upwards [meas_le_ae_eq_meas_lt (μ : Measure Ω) volume f] with t ht
  have hlevel : (μ : Measure Ω) {x | f x = t} = 0 := by
    have hdiff : {x : Ω | f x = t} = {x | t ≤ f x} \ {x | t < f x} := by
      ext x
      simp only [mem_setOf_eq, mem_diff]
      constructor
      · intro heq
        exact ⟨by rw [heq], by rw [heq]; exact lt_irrefl _⟩
      · intro hx
        exact le_antisymm (le_of_not_gt hx.2) hx.1
    rw [hdiff, measure_diff (μ := (μ : Measure Ω))
      (s₁ := {x : Ω | t ≤ f x}) (s₂ := {x : Ω | t < f x})
      (fun x hx ↦ show t ≤ f x from le_of_lt hx)
      ((hf measurableSet_Ioi).nullMeasurableSet) (measure_ne_top _ _), ht]
    simp
  apply measure_mono_null (t := {x | f x = t} ∪ {x | ¬ContinuousAt f x}) _
    (measure_union_null hlevel hbad)
  intro x hx
  by_cases hc : ContinuousAt f x
  · left
    apply le_antisymm
    · apply le_of_not_gt
      intro hgt
      have hnhds : {y : Ω | t < f y} ∈ 𝓝 x :=
        hc.eventually (isOpen_Ioi.mem_nhds hgt)
      have hinterior : x ∈ interior {y : Ω | t ≤ f y} := by
        rw [mem_interior_iff_mem_nhds]
        filter_upwards [hnhds] with y hy
        exact le_of_lt hy
      exact hx.2 hinterior
    · apply le_of_not_gt
      intro hlt
      have hnhds : {y : Ω | f y < t} ∈ 𝓝 x :=
        hc.eventually (isOpen_Iio.mem_nhds hlt)
      have hinterior : x ∈ interior ({y : Ω | t ≤ f y}ᶜ) := by
        rw [mem_interior_iff_mem_nhds]
        simpa only [compl_setOf, not_le] using hnhds
      have hfc : x ∈ frontier ({y : Ω | t ≤ f y}ᶜ) := by
        simpa only [frontier_compl] using hx
      exact Set.disjoint_left.1
        (disjoint_interior_frontier (s := {y : Ω | t ≤ f y}ᶜ)) hinterior hfc
  · exact Or.inr hc

/-- Weak convergence transfers integrals of bounded nonnegative measurable
functions continuous almost everywhere under the limiting measure. -/
theorem ProbabilityMeasure.tendsto_integral_of_ae_continuous
    {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : Ω → ℝ} {M : ℝ}
    (hf : Measurable f) (hcont : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x)
    (hnn : 0 ≤ f) (hbdd : f ≤ fun _ ↦ M) :
    Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure Ω)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  apply ProbabilityMeasure.tendsto_integral_of_ae_nullFrontier hμ
    hf.aestronglyMeasurable (fun _ ↦ hf.aestronglyMeasurable) hnn hbdd
  exact (ae_nullFrontier_superlevel_of_ae_continuous μ hf hcont).filter_mono
    (ae_mono Measure.restrict_le_self)

end PortmanteauConsequences

section BulkRecovery

variable {Ω J : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- Sequential contradiction upgrades bounded-continuous bulk control to
bulk control of a bounded nonnegative a.e.-continuous function. -/
theorem ProbabilityMeasure.bulk_uniform_integral_of_ae_continuous
    (μ : ProbabilityMeasure Ω) (μs : ℕ → J → ProbabilityMeasure Ω)
    (bulk : ℕ → Set J)
    (hbulk : ∀ g : BoundedContinuousFunction Ω ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ j ∈ bulk n,
        |(∫ x, g x ∂(μs n j : Measure Ω)) - ∫ x, g x ∂(μ : Measure Ω)| < ε)
    {f : Ω → ℝ} {M : ℝ} (hf : Measurable f)
    (hcont : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x)
    (hnn : 0 ≤ f) (hbdd : f ≤ fun _ ↦ M) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ j ∈ bulk n,
      |(∫ x, f x ∂(μs n j : Measure Ω)) - ∫ x, f x ∂(μ : Measure Ω)| < ε := by
  intro ε hε
  simp only [eventually_atTop]
  by_contra! hfail
  choose ns hns_ge js hjs_mem hbad using hfail
  have hns : Tendsto ns atTop atTop := tendsto_atTop.2 fun N ↦
    eventually_atTop.2 ⟨N, fun k hk ↦ hk.trans (hns_ge k)⟩
  have hweak : Tendsto (fun k ↦ μs (ns k) (js k)) atTop (𝓝 μ) :=
    ProbabilityMeasure.tendsto_of_bulk_uniform_integral μ μs bulk hbulk hns
      (Eventually.of_forall hjs_mem)
  have hint := ProbabilityMeasure.tendsto_integral_of_ae_continuous
    hweak hf hcont hnn hbdd
  have hnear : ∀ᶠ k in atTop,
      |(∫ x, f x ∂(μs (ns k) (js k) : Measure Ω)) -
        ∫ x, f x ∂(μ : Measure Ω)| < ε := by
    rcases Metric.tendsto_atTop.1 hint ε hε with ⟨N, hN⟩
    exact eventually_atTop.2 ⟨N, fun k hk ↦ by
      simpa only [Real.dist_eq] using hN k hk⟩
  rcases hnear.exists with ⟨k, hk⟩
  exact (not_le_of_gt hk) (hbad k)

/-- Bulk-uniform Portmanteau for a set with null frontier. -/
theorem ProbabilityMeasure.bulk_uniform_measure_of_nullFrontier
    (μ : ProbabilityMeasure Ω) (μs : ℕ → J → ProbabilityMeasure Ω)
    (bulk : ℕ → Set J)
    (hbulk : ∀ g : BoundedContinuousFunction Ω ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ j ∈ bulk n,
        |(∫ x, g x ∂(μs n j : Measure Ω)) - ∫ x, g x ∂(μ : Measure Ω)| < ε)
    {E : Set Ω} (hE : (μ : Measure Ω) (frontier E) = 0) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ j ∈ bulk n,
      |(μs n j : Measure Ω).real E - (μ : Measure Ω).real E| < ε := by
  intro ε hε
  simp only [eventually_atTop]
  by_contra! hfail
  choose ns hns_ge js hjs_mem hbad using hfail
  have hns : Tendsto ns atTop atTop := tendsto_atTop.2 fun N ↦
    eventually_atTop.2 ⟨N, fun k hk ↦ hk.trans (hns_ge k)⟩
  have hweak : Tendsto (fun k ↦ μs (ns k) (js k)) atTop (𝓝 μ) :=
    ProbabilityMeasure.tendsto_of_bulk_uniform_integral μ μs bulk hbulk hns
      (Eventually.of_forall hjs_mem)
  have hmeas : Tendsto
      (fun k ↦ (μs (ns k) (js k) : Measure Ω).real E) atTop
      (𝓝 ((μ : Measure Ω).real E)) :=
    (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure Ω) E)).comp
      (ProbabilityMeasure.tendsto_measure_nullFrontier hweak hE)
  have hnear : ∀ᶠ k in atTop,
      |(μs (ns k) (js k) : Measure Ω).real E -
        (μ : Measure Ω).real E| < ε := by
    rcases Metric.tendsto_atTop.1 hmeas ε hε with ⟨N, hN⟩
    exact eventually_atTop.2 ⟨N, fun k hk ↦ by
      simpa only [Real.dist_eq] using hN k hk⟩
  rcases hnear.exists with ⟨k, hk⟩
  exact (not_le_of_gt hk) (hbad k)

end BulkRecovery

end MeasureTheory

namespace Kwon1002.Prop64

noncomputable section
open scoped BoundedContinuousFunction

def actualQWindow (R : ℕ) (α : ℝ) (n j : ℕ) : QWindow R :=
  quotientWindow R (actualWindow R α n j)

/-- The finite-algebra one-block input, stated directly on corrected quotient
windows. -/
def DenseEltOneBlock (R : ℕ) : Prop :=
  ∀ G : DenseElt R, ∀ ε > 0,
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, G.qeval (actualQWindow R α n j)) -
          ∫ q, G.qeval q ∂qWindowLaw R‖ < ε

/-- Uniform tightness of the actual quotient windows on the same compact
full-digit cubes used by Stone--Weierstrass. -/
def ActualDigitTail (R : ℕ) : Prop :=
  ∀ δ > 0, ∃ K : ℕ,
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      (volume.restrict (Ioo (0 : ℝ) 1)).real
        {α : ℝ | actualQWindow R α n j ∉ fullDigitCubeQ R K} < δ

private lemma integrable_of_ae_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {u : X → E} (hu : AEStronglyMeasurable u μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖u x‖ ≤ C) [IsFiniteMeasure μ] : Integrable u μ := by
  have hC' : ∀ᵐ x ∂(μ.restrict Set.univ), ‖u x‖ ≤ C := by simpa using hC
  have h := Measure.integrableOn_of_bounded (μ := μ) (s := Set.univ)
    (measure_ne_top μ Set.univ) hu hC'
  simpa only [IntegrableOn, Measure.restrict_univ] using h

private lemma continuous_qeval' {R : ℕ} (G : DenseElt R) : Continuous G.qeval := by
  unfold DenseElt.qeval
  refine continuous_finset_sum _ fun l _ =>
    ((continuous_of_discreteTopology.comp continuous_fst).mul
      ((G.g_continuous l).comp (continuous_fst.comp continuous_snd))).mul ?_
  exact (UnitAddTorus.mFourier (G.c l)).continuous.comp
    (continuous_snd.comp continuous_snd)

/-- Common tail estimate.  The only use of the special shape of `DenseElt`
is that the Stone--Weierstrass approximant vanishes off its finite digit
projection. -/
private lemma integral_approximation_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (R K : ℕ) (f : QWindow R →ᵇ ℂ) (G : DenseElt R)
    (hGsupport : SupportedOnDigitWords (fullDigitCubeQ R K)
      (isCompact_fullDigitCubeQ R K) G)
    {η δ : ℝ} (hη : 0 < η)
    (hGunif : ∀ q : fullDigitCubeQ R K, ‖G.qeval q.1 - f q.1‖ < η)
    (φ : X → QWindow R) (hφ : Measurable φ)
    (hreal : ∀ᵐ x ∂μ, φ x ∈ qRealSupport R)
    (hmass : μ.real Set.univ = 1)
    (htail : μ.real {x | φ x ∉ fullDigitCubeQ R K} < δ) :
    ‖(∫ x, f (φ x) ∂μ) - ∫ x, G.qeval (φ x) ∂μ‖ <
      η + (‖f‖ + 1) * δ := by
  classical
  let bad : Set X := {x | φ x ∉ fullDigitCubeQ R K}
  change μ.real bad < δ at htail
  have hcube : MeasurableSet (fullDigitCubeQ R K) :=
    (isCompact_fullDigitCubeQ R K).isClosed.measurableSet
  have hbad : MeasurableSet bad := hcube.compl.preimage hφ
  have hfmeas : AEStronglyMeasurable (fun x => f (φ x)) μ :=
    (f.continuous.measurable.comp hφ).aestronglyMeasurable
  have hGmeas : AEStronglyMeasurable (fun x => G.qeval (φ x)) μ :=
    ((continuous_qeval' G).measurable.comp hφ).aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ,
      ‖f (φ x) - G.qeval (φ x)‖ ≤
        η + (‖f‖ + 1) * bad.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hreal] with x hxreal
    by_cases hx : φ x ∈ fullDigitCubeQ R K
    · rw [Set.indicator_of_notMem (show x ∉ bad by simpa [bad])]
      simp only [mul_zero, add_zero]
      exact (by simpa [norm_sub_rev] using (hGunif ⟨φ x, hx⟩).le)
    · rw [Set.indicator_of_mem (show x ∈ bad by simpa [bad])]
      have hncap : φ x ∉ fullDigitCapQ R K := by
        intro hcap
        apply hx
        exact ⟨hcap, ⟨fun i _ => hxreal i, Set.mem_univ _⟩⟩
      have hG0 : G.qeval (φ x) = 0 :=
        qeval_eq_zero_outside_fullDigitCapQ K hGsupport hncap
      rw [hG0, sub_zero, mul_one]
      exact (f.norm_coe_le_norm (φ x)).trans (by linarith [hη, norm_nonneg f])
  have hdiff : Integrable (fun x => f (φ x) - G.qeval (φ x)) μ := by
    apply integrable_of_ae_bound (C := η + (‖f‖ + 1)) (hfmeas.sub hGmeas)
    filter_upwards [hpoint] with x hx
    refine hx.trans ?_
    rw [Set.indicator_apply]
    split_ifs <;> simp only [mul_one, mul_zero, add_zero]
    · exact le_rfl
    · linarith [norm_nonneg f]
  have hfint : Integrable (fun x => f (φ x)) μ := by
    apply integrable_of_ae_bound hfmeas
    exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (φ x)
  have hGint : Integrable (fun x => G.qeval (φ x)) μ := by
    have : (fun x => G.qeval (φ x)) = (fun x => f (φ x)) -
        (fun x => f (φ x) - G.qeval (φ x)) := by funext x; simp
    rw [this]
    exact hfint.sub hdiff
  rw [← integral_sub hfint hGint]
  refine (norm_integral_le_integral_norm _).trans_lt ?_
  have hind : Integrable (bad.indicator (fun _ => (1 : ℝ))) μ := by
    apply integrable_of_ae_bound (C := 1)
      ((measurable_const.indicator hbad).aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs <;> norm_num
  have hmajor : Integrable
      (fun x => η + (‖f‖ + 1) * bad.indicator (fun _ => (1 : ℝ)) x) μ := by
    exact (integrable_const η).add (hind.const_mul (‖f‖ + 1))
  calc
    (∫ x, ‖f (φ x) - G.qeval (φ x)‖ ∂μ)
        ≤ ∫ x, (η + (‖f‖ + 1) * bad.indicator (fun _ => (1 : ℝ)) x) ∂μ :=
      integral_mono_ae hdiff.norm hmajor hpoint
    _ = η + (‖f‖ + 1) * μ.real bad := by
      rw [integral_add (integrable_const η) (hind.const_mul (‖f‖ + 1)),
        integral_const, hmass, one_smul, integral_const_mul,
        integral_indicator_const (1 : ℝ) hbad, smul_eq_mul, mul_one]
    _ < η + (‖f‖ + 1) * δ := by
      have hm := mul_lt_mul_of_pos_left htail (show 0 < ‖f‖ + 1 by positivity)
      linarith

private lemma fullDigitCubeQ_mono {R K L : ℕ} (hKL : K ≤ L) :
    fullDigitCubeQ R K ⊆ fullDigitCubeQ R L := by
  rintro q ⟨hq, hr, ht⟩
  exact ⟨fun i => (hq i).trans hKL, hr, ht⟩

private lemma qWindowLaw_real_univ (R : ℕ) :
    (qWindowLaw R).real Set.univ = 1 := by
  rw [Measure.real, qWindowLaw, Measure.map_apply_of_aemeasurable
    (measurable_quotientWindow R).aemeasurable MeasurableSet.univ]
  simp

private lemma stationary_cube_tail (R : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, (qWindowLaw R).real (fullDigitCubeQ R K)ᶜ < δ := by
  obtain ⟨K, hK⟩ := exists_nat_gt
    (((2 * R + 1 : ℕ) : ℝ) * 2 / δ)
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hnum : ((2 * R + 1 : ℕ) : ℝ) * (2 / ((K : ℝ) + 1)) < δ := by
    rw [div_lt_iff₀ hδ] at hK
    rw [show ((2 * R + 1 : ℕ) : ℝ) * (2 / ((K : ℝ) + 1)) =
      (((2 * R + 1 : ℕ) : ℝ) * 2) / ((K : ℝ) + 1) by ring,
      div_lt_iff₀ hKpos]
    nlinarith
  refine ⟨K, ?_⟩
  have hmono : qWindowLaw R (fullDigitCubeQ R K)ᶜ ≤
      qWindowLaw R (fullDigitCapQ R K)ᶜ := by
    apply measure_mono_ae
    filter_upwards [qWindowLaw_ae_mem_qRealSupport R] with q hqreal hq
    intro hcap
    apply hq
    exact ⟨hcap, ⟨fun i _ => hqreal i, Set.mem_univ _⟩⟩
  have hle := hmono.trans (qWindowLaw_fullDigitCapQ_compl_le R K)
  rw [Measure.real]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hle).trans_lt hnum

private lemma actualQWindow_ae_realSupport (R n j : ℕ) :
    ∀ᵐ α ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      actualQWindow R α n j ∈ qRealSupport R := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
    with α hα hirr
  intro i
  exact Ioo_subset_Icc_self (gaussIter_mem_Ioo hα hirr _)

/-- The proved uniform digit tail implies tightness of the actual quotient
windows on the compact full-digit cubes. -/
theorem actualDigitTail (R : ℕ) : ActualDigitTail R := by
  obtain ⟨C, hC, htail⟩ := qActualWindowLaw_fullDigitCapQ_compl_le R
  intro δ hδ
  obtain ⟨K, hK⟩ := exists_nat_gt
    (((2 * R + 1 : ℕ) : ℝ) * C / δ)
  refine ⟨K, ?_⟩
  filter_upwards [eventually_bulk_radius R] with n hroom
  intro j hj
  have hcap :
      (volume.restrict (Ioo (0 : ℝ) 1))
          {α : ℝ | actualQWindow R α n j ∉ fullDigitCapQ R K} =
        qActualWindowLaw R n j (fullDigitCapQ R K)ᶜ := by
    rw [qActualWindowLaw, actualWindowLaw,
      Measure.map_map (measurable_quotientWindow R) (measurable_actualWindow R n j),
      Measure.map_apply
        ((measurable_quotientWindow R).comp (measurable_actualWindow R n j))
        (measurableSet_fullDigitCapQ R K).compl]
    rfl
  have hbad :
      (volume.restrict (Ioo (0 : ℝ) 1))
          {α : ℝ | actualQWindow R α n j ∉ fullDigitCubeQ R K} ≤
        qActualWindowLaw R n j (fullDigitCapQ R K)ᶜ := by
    rw [← hcap]
    apply measure_mono_ae
    filter_upwards [actualQWindow_ae_realSupport R n j] with α hreal hcube
    intro hcapmem
    apply hcube
    exact ⟨hcapmem, ⟨fun i _ ↦ hreal i, Set.mem_univ _⟩⟩
  have hRj : R ≤ j := (by omega : R ≤ R + 1).trans (hroom j hj)
  have hle := hbad.trans (htail K n j hRj)
  rw [Measure.real]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hle).trans_lt ?_
  have hK' : (((2 * R + 1 : ℕ) : ℝ) * C) / δ < (K : ℝ) + 1 := by
    linarith
  rw [show (((2 * R + 1 : ℕ) : ℝ) * C / ((K : ℝ) + 1)) =
    (((2 * R + 1 : ℕ) : ℝ) * C) / ((K : ℝ) + 1) by ring]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) + 1)]
  rw [div_lt_iff₀ hδ] at hK'
  simpa [mul_comm] using hK'

private lemma measureReal_mono {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {s t : Set X} (hst : s ⊆ t) : μ.real s ≤ μ.real t := by
  exact ENNReal.toReal_mono (measure_ne_top μ t) (measure_mono hst)

/-- Bulk-uniform transfer for every bounded continuous test function on the
corrected quotient window.  The approximation is performed on the compact
`fullDigitCubeQ`; `fullDigitCapQ` occurs only internally in the already-proved
support lemma which says that the selected approximant vanishes off its
finite digit projection. -/
theorem boundedContinuous_transfer (R : ℕ) (f : QWindow R →ᵇ ℂ)
    (honeblock : DenseEltOneBlock R) (hactualTail : ActualDigitTail R) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, f (actualQWindow R α n j)) -
          ∫ q, f q ∂qWindowLaw R‖ < ε := by
  intro ε hε
  let η : ℝ := ε / 6
  let δ : ℝ := ε / (6 * (‖f‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ks, hKs⟩ := stationary_cube_tail R hδ
  obtain ⟨Ka, hKa⟩ := hactualTail δ hδ
  let K : ℕ := max Ka Ks
  have hKaK : Ka ≤ K := le_max_left _ _
  have hKsK : Ks ≤ K := le_max_right _ _
  let QK : Set (QWindow R) := fullDigitCubeQ R K
  let fK : C(QK, ℂ) :=
    ⟨fun q => f q.1, f.continuous.comp continuous_subtype_val⟩
  obtain ⟨G, hGsupport, hGunif⟩ :=
    exists_denseElt_uniformly_approximates QK (isCompact_fullDigitCubeQ R K)
      fK hη
  have hqfinite : qWindowLaw R Set.univ ≠ ⊤ := by
    rw [qWindowLaw, Measure.map_apply_of_aemeasurable
      (measurable_quotientWindow R).aemeasurable MeasurableSet.univ]
    simp
  letI : IsFiniteMeasure (qWindowLaw R) :=
    ⟨lt_top_iff_ne_top.2 hqfinite⟩
  have hstatTail : (qWindowLaw R).real (fullDigitCubeQ R K)ᶜ < δ := by
    refine (measureReal_mono ?_).trans_lt hKs
    exact compl_subset_compl.mpr (fullDigitCubeQ_mono hKsK)
  have hstatApprox :
      ‖(∫ q, f q ∂qWindowLaw R) - ∫ q, G.qeval q ∂qWindowLaw R‖ < ε / 3 := by
    have h := integral_approximation_lt R K f G
      (by simpa [QK] using hGsupport) hη
      (by intro q; simpa [QK, fK] using hGunif q)
      id measurable_id (qWindowLaw_ae_mem_qRealSupport R)
      (qWindowLaw_real_univ R) hstatTail
    refine h.trans_le ?_
    dsimp [η, δ]
    field_simp
    norm_num
  filter_upwards [hKa, honeblock G (ε / 3) (by positivity)] with n hn hblock
  intro j hj
  have hactTail : (volume.restrict (Ioo (0 : ℝ) 1)).real
      {α : ℝ | actualQWindow R α n j ∉ fullDigitCubeQ R K} < δ := by
    refine (measureReal_mono ?_).trans_lt (hn j hj)
    intro α hα hmem
    exact hα (fullDigitCubeQ_mono hKaK hmem)
  have hactApprox :
      ‖(∫ α in Ioo (0 : ℝ) 1, f (actualQWindow R α n j)) -
        ∫ α in Ioo (0 : ℝ) 1, G.qeval (actualQWindow R α n j)‖ < ε / 3 := by
    have h := integral_approximation_lt R K f G
      (by simpa [QK] using hGsupport) hη
      (by intro q; simpa [QK, fK] using hGunif q)
      (actualQWindow R · n j)
      ((measurable_quotientWindow R).comp (measurable_actualWindow R n j))
      (actualQWindow_ae_realSupport R n j)
      (by simp [Measure.real]) hactTail
    refine h.trans_le ?_
    dsimp [η, δ]
    field_simp
    norm_num
  calc
    ‖(∫ α in Ioo (0 : ℝ) 1, f (actualQWindow R α n j)) -
        ∫ q, f q ∂qWindowLaw R‖
      ≤ ‖(∫ α in Ioo (0 : ℝ) 1, f (actualQWindow R α n j)) -
          ∫ α in Ioo (0 : ℝ) 1, G.qeval (actualQWindow R α n j)‖ +
        ‖(∫ α in Ioo (0 : ℝ) 1, G.qeval (actualQWindow R α n j)) -
          ∫ q, G.qeval q ∂qWindowLaw R‖ +
        ‖(∫ q, G.qeval q ∂qWindowLaw R) - ∫ q, f q ∂qWindowLaw R‖ := by
        calc
          _ = ‖((∫ α in Ioo (0 : ℝ) 1, f (actualQWindow R α n j)) -
                ∫ α in Ioo (0 : ℝ) 1, G.qeval (actualQWindow R α n j)) +
              ((∫ α in Ioo (0 : ℝ) 1, G.qeval (actualQWindow R α n j)) -
                ∫ q, G.qeval q ∂qWindowLaw R) +
              ((∫ q, G.qeval q ∂qWindowLaw R) - ∫ q, f q ∂qWindowLaw R)‖ := by
                apply congrArg norm
                ring
          _ ≤ _ := norm_add₃_le
    _ < ε := by
      rw [norm_sub_rev (∫ q, G.qeval q ∂qWindowLaw R) (∫ q, f q ∂qWindowLaw R)]
      linarith [hactApprox, hblock j hj, hstatApprox]

/-- Continuous-test transfer with actual tightness discharged by the proved
uniform actual-window digit tail. -/
theorem boundedContinuous_transfer_of_oneBlock (R : ℕ) (f : QWindow R →ᵇ ℂ)
    (honeblock : DenseEltOneBlock R) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, f (actualQWindow R α n j)) -
          ∫ q, f q ∂qWindowLaw R‖ < ε :=
  boundedContinuous_transfer R f honeblock (actualDigitTail R)

end

end Kwon1002.Prop64

namespace Kwon1002.Prop64

noncomputable section
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1000000

open V5Identity31

/-- The manuscript identity (31) with its canonical coefficients exposed. -/
lemma window_character_reduction_v5_exact (R : ℕ)
    (c : Fin (2 * R + 2) → ℤ) :
    ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R + 1 ≤ j →
      ∃ m : ℤ,
        (∑ i : Fin (2 * R + 2), (c i : ℝ) *
            theta α n (j + (i : ℕ) - (R + 1))) =
          (winA1 R c (windowWord R α j) : ℝ) * theta α n j +
            (winB1 R c (windowWord R α j) : ℝ) * thetaPred α n j + (m : ℝ) := by
  intro α hirr hα n j hRj
  have hv : ∀ t, t < 2 * R → wordFn R (windowWord R α j) t = digit α (j + t - R) :=
    fun t ht => wordFn_windowWord R α j t ht
  have key : ∀ i : Fin (2 * R + 2), ∃ m : ℤ,
      theta α n (j + (i : ℕ) - (R + 1)) =
        ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).1 : ℝ) * theta α n j +
          ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).2 : ℝ) *
            thetaPred α n j + (m : ℝ) := by
    intro i
    have hi := i.isLt
    by_cases h : R + 1 ≤ (i : ℕ)
    · obtain ⟨m, hm⟩ := up_theta hα hirr n j R (wordFn R (windowWord R α j)) hv
          ((i : ℕ) - (R + 1)) (by omega)
      refine ⟨m, ?_⟩
      rw [show j + (i : ℕ) - (R + 1) = j + ((i : ℕ) - (R + 1)) from by omega,
        hm, winC1, if_pos h]
    · obtain ⟨m, hm⟩ := down_theta_ext hα hirr n j R hRj
          (wordFn R (windowWord R α j)) hv (R + 1 - (i : ℕ)) (by omega)
      refine ⟨m, ?_⟩
      rw [show j + (i : ℕ) - (R + 1) = j - (R + 1 - (i : ℕ)) from by omega,
        hm, winC1, if_neg h]
  choose m hm using key
  refine ⟨∑ i : Fin (2 * R + 2), c i * m i, ?_⟩
  calc
    (∑ i : Fin (2 * R + 2), (c i : ℝ) * theta α n (j + (i : ℕ) - (R + 1))) =
        ∑ i : Fin (2 * R + 2),
          ((c i : ℝ) * ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).1 : ℝ) *
              theta α n j +
            (c i : ℝ) * ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).2 : ℝ) *
              thetaPred α n j + (c i : ℝ) * (m i : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hm i]
      ring
    _ = (winA1 R c (windowWord R α j) : ℝ) * theta α n j +
          (winB1 R c (windowWord R α j) : ℝ) * thetaPred α n j +
            ((∑ i : Fin (2 * R + 2), c i * m i : ℤ) : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul]
      simp only [winA1, winB1]
      push_cast
      ring

theorem identity_31_both (R M K : ℕ) (G : DenseElt R) (hMpos : 1 ≤ M) :
    ∃ K' : ℕ, ∃ P : WindowSymbol (R + M) K',
      (∀ᵐ w ∂(windowLaw (R + M)),
        (digitCapEvent (R + M) K).indicator
            (fun v => G.eval (digitTruncWindow R M v)) w
          = P.evalWindow w) ∧
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ,
        R + M + 1 ≤ j →
        (digitCapEvent (R + M) K).indicator
            (fun v => G.eval (digitTruncWindow R M v))
            (actualWindow (R + M) α n j) = P.at α n j := by
  let R' := R + M
  let words : Finset (Fin (2 * R') → ℕ) :=
    Fintype.piFinset (fun _ : Fin (2 * R') => Finset.range (K + 1))
  let coreWord (w : Fin (2 * R') → ℕ) : Fin (2 * R) → ℕ :=
    fun i => w ⟨M + (i : ℕ), by have := i.isLt; dsimp [R']; omega⟩
  let denseDigits (w : Fin (2 * R') → ℕ) : Fin (2 * R + 1) → ℕ :=
    fun i => w ⟨M + (i : ℕ), by have := i.isLt; dsimp [R']; omega⟩
  let truncReals (w : Fin (2 * R') → ℕ) : Fin (2 * R + 1) → ℝ :=
    fun i => cfFinite (fun k => if hk : k < M then
      w ⟨M + (i : ℕ) + k,
        by have := i.isLt; dsimp [R']; omega⟩ else 0) M
  let A (l : Fin G.len) (w : Fin (2 * R') → ℕ) : ℤ :=
    V5Identity31.winA1 R (G.c l) (coreWord w)
  let B (l : Fin G.len) (w : Fin (2 * R') → ℕ) : ℤ :=
    V5Identity31.winB1 R (G.c l) (coreWord w)
  let amp (l : Fin G.len) (w : Fin (2 * R') → ℕ) : ℂ :=
    G.D l (denseDigits w) * G.g l (truncReals w)
  let pairs : Finset (Fin G.len × (Fin (2 * R') → ℕ)) := Finset.univ ×ˢ words
  let K' : ℕ := pairs.sup (fun p => (B p.1 p.2).natAbs + (A p.1 p.2).natAbs)
  let P : WindowSymbol R' K' :=
    { coeff := fun w r s =>
        if w ∈ words then
          ∑ l : Fin G.len, if r = B l w ∧ s = A l w then amp l w else 0
        else 0
      words := words
      coeff_support := by
        intro w r s hw
        simp [hw]
      mode_cap := by
        intro w r s hrs
        by_cases hw : w ∈ words
        · simp only [hw, if_true]
          refine Finset.sum_eq_zero fun l _ => ?_
          by_cases hm : r = B l w ∧ s = A l w
          · have hp : (l, w) ∈ pairs := by simp [pairs, hw]
            have hle : (B l w).natAbs + (A l w).natAbs ≤ K' :=
              Finset.le_sup (f := fun p => (B p.1 p.2).natAbs + (A p.1 p.2).natAbs) hp
            rw [if_pos hm]
            exfalso
            rw [hm.1, hm.2] at hrs
            omega
          · rw [if_neg hm]
        · simp [hw] }

  have hstationary :
      ∀ᵐ w ∂(windowLaw (R + M)),
        (digitCapEvent (R + M) K).indicator
            (fun v => G.eval (digitTruncWindow R M v)) w = P.evalWindow w := by
    have hGmeas : Measurable G.eval := by
      unfold DenseElt.eval
      refine Finset.measurable_sum _ fun l _ => Measurable.mul (Measurable.mul ?_ ?_) ?_
      · exact (Measurable.of_discrete (f := G.D l)).comp measurable_fst
      · exact ((G.g_continuous l).measurable).comp (measurable_fst.comp measurable_snd)
      · refine Prop42.continuous_torusChar.measurable.comp ?_
        exact Finset.measurable_sum _ fun t _ =>
          ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)).const_mul _
    have hCFmeas : ∀ (m : ℕ) (a : WindowSpace R' → ℕ → ℕ),
        (∀ k, Measurable fun w => a w k) → Measurable fun w => cfFinite (a w) m := by
      intro m
      induction m with
      | zero =>
          intro a _
          simpa only [cfFinite] using (measurable_const : Measurable fun _ : WindowSpace R' => (0 : ℝ))
      | succ m ih =>
          intro a ha
          have h0 : Measurable fun w : WindowSpace R' => ((a w 0 : ℕ) : ℝ) :=
            (measurable_from_top (f := fun q : ℕ => (q : ℝ))).comp (ha 0)
          have h1 : Measurable fun w : WindowSpace R' => cfFinite (fun k => a w (k + 1)) m :=
            ih (fun w k => a w (k + 1)) fun k => ha (k + 1)
          simpa only [cfFinite] using (h0.add h1).inv
    have hTruncMeas : Measurable (digitTruncWindow R M) := by
      unfold digitTruncWindow
      refine Measurable.prodMk (measurable_pi_lambda _ fun _ => measurable_wA _ _)
        (Measurable.prodMk ?_ (measurable_pi_lambda _ fun _ => measurable_wTh _ _))
      exact measurable_pi_lambda _ fun _ =>
        hCFmeas M _ fun _ => measurable_wA _ _
    have hLmeas : Measurable fun w : WindowSpace R' =>
        (digitCapEvent R' K).indicator (fun v => G.eval (digitTruncWindow R M v)) w :=
      Measurable.indicator (hGmeas.comp hTruncMeas) (measurableSet_digitCapEvent R' K)
    have hWordMeas : Measurable (windowWordOf R') :=
      measurable_pi_lambda _ fun _ => measurable_wA R' _
    have hPmeas : Measurable P.evalWindow := by
      unfold WindowSymbol.evalWindow
      refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ =>
        Measurable.mul ?_ ?_
      · exact (Measurable.of_discrete (f := fun v : Fin (2 * R') → ℕ => P.coeff v r s)).comp
          hWordMeas
      · exact Prop42.continuous_torusChar.measurable.comp
          (((measurable_wTh R' (-1)).const_mul _).add ((measurable_wTh R' 0).const_mul _))
    have hEqMeas : MeasurableSet {w : WindowSpace R' |
        (digitCapEvent R' K).indicator (fun v => G.eval (digitTruncWindow R M v)) w
          = P.evalWindow w} := measurableSet_eq_fun hLmeas hPmeas
    rw [windowLaw, ae_map_iff (measurable_stationaryWindow R').aemeasurable hEqMeas]
    filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz
    have hword : windowWordOf R' (stationaryWindow R' z) = natExtWord R' z.1 := by
      funext i
      rw [windowWordOf, wA_stationaryWindow R' z (by omega) (by omega)]
      exact (StationaryIdentity31.wordFn_natExtWord hz R' (i : ℕ) i.isLt).symm.trans (by
        simp [wordFn])
    have hprefix : ∀ i : Fin (2 * R'),
        (stationaryWindow R' z).1 ⟨(i : ℕ), by have := i.isLt; omega⟩ = natExtWord R' z.1 i := by
      intro i
      have hi := congrFun hword i
      have hc : 0 ≤ (i : ℤ) - (R' : ℤ) + (R' : ℤ) ∧
          (i : ℤ) - (R' : ℤ) + (R' : ℤ) < 2 * (R' : ℤ) + 1 := by omega
      have hidx : (⟨((i : ℤ) - (R' : ℤ) + (R' : ℤ)).toNat, by omega⟩ : Fin (2 * R' + 1))
          = ⟨(i : ℕ), by have := i.isLt; omega⟩ := by
        apply Fin.ext
        simp only
        omega
      simpa only [windowWordOf, wA, dif_pos hc, hidx] using hi
    have hmem : stationaryWindow R' z ∈ digitCapEvent R' K ↔ natExtWord R' z.1 ∈ words := by
      rw [Fintype.mem_piFinset]
      simp only [digitCapEvent, Set.mem_setOf_eq, Finset.mem_range]
      constructor
      · intro h i
        have hi := h i
        rw [hprefix i] at hi
        exact Nat.lt_succ_of_le hi
      · intro h i
        have hi := h i
        rw [hprefix i]
        exact Nat.le_of_lt_succ hi
    by_cases hw : natExtWord R' z.1 ∈ words
    · rw [Set.indicator_of_mem (hmem.mpr hw)]
      have hcore : coreWord (natExtWord R' z.1) = natExtWord R z.1 := by
        funext i
        have hbig := StationaryIdentity31.wordFn_natExtWord hz R' (M + (i : ℕ)) (by
          have := i.isLt
          dsimp [R']
          omega)
        have hsmall := StationaryIdentity31.wordFn_natExtWord hz R (i : ℕ) i.isLt
        have hbnd : M + (i : ℕ) < 2 * R' := by have := i.isLt; dsimp [R']; omega
        have hbig' : natExtWord R' z.1 ⟨M + (i : ℕ), hbnd⟩
            = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
          simpa [wordFn, hbnd] using hbig
        have hsmall' : natExtWord R z.1 i
            = digit (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1 0 := by
          simpa [wordFn, i.isLt] using hsmall
        simp only [coreWord]
        calc
          natExtWord R' z.1 ⟨M + (i : ℕ), _⟩
              = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := hbig'
          _ = digit (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1 0 := by
            have hoff : (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ))
                = (i : ℤ) - (R : ℤ) := by
              dsimp [R']
              omega
            rw [hoff]
          _ = natExtWord R z.1 i := hsmall'.symm
      have hdense : (digitTruncWindow R M (stationaryWindow R' z)).1
          = denseDigits (natExtWord R' z.1) := by
        funext i
        simp only [digitTruncWindow, denseDigits]
        rw [wA_stationaryWindow R' z (by dsimp [R']; omega) (by dsimp [R']; omega)]
        have hbig := StationaryIdentity31.wordFn_natExtWord hz R' (M + (i : ℕ)) (by
          have := i.isLt
          dsimp [R']
          omega)
        have hbnd : M + (i : ℕ) < 2 * R' := by have := i.isLt; dsimp [R']; omega
        have hbig' : natExtWord R' z.1 ⟨M + (i : ℕ), hbnd⟩
            = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
          simpa [wordFn, hbnd] using hbig
        calc
          digit (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1 0
              = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
                have hoff : ((i : ℤ) - (R : ℤ))
                    = (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) := by
                  dsimp [R']
                  omega
                rw [hoff]
          _ = natExtWord R' z.1 ⟨M + (i : ℕ), _⟩ := hbig'.symm
      have htrunc : (digitTruncWindow R M (stationaryWindow R' z)).2.1
          = truncReals (natExtWord R' z.1) := by
        funext i
        simp only [digitTruncWindow, truncReals]
        apply cfFinite_congr
        intro k hk
        rw [dif_pos hk, wA_stationaryWindow R' z (by dsimp [R']; omega)
          (by have := i.isLt; dsimp [R']; omega)]
        have hbig := StationaryIdentity31.wordFn_natExtWord hz R'
          (M + (i : ℕ) + k) (by have := i.isLt; dsimp [R']; omega)
        have hbnd : M + (i : ℕ) + k < 2 * R' := by have := i.isLt; dsimp [R']; omega
        have hbig' : natExtWord R' z.1 ⟨M + (i : ℕ) + k, hbnd⟩
            = digit (hatSzpow (((M + (i : ℕ) + k : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
          simpa [wordFn, hbnd] using hbig
        calc
          digit (hatSzpow ((i : ℤ) - (R : ℤ) + (k : ℤ)) z).1.1 0
              = digit (hatSzpow (((M + (i : ℕ) + k : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
                have hoff : ((i : ℤ) - (R : ℤ) + (k : ℤ))
                    = (((M + (i : ℕ) + k : ℕ) : ℤ) - (R' : ℤ)) := by
                  dsimp [R']
                  omega
                rw [hoff]
          _ = natExtWord R' z.1 ⟨M + (i : ℕ) + k, _⟩ := hbig'.symm
      have hchar : ∀ l : Fin G.len,
          torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
              (digitTruncWindow R M (stationaryWindow R' z)).2.2 t)
            = torusChar ((B l (natExtWord R' z.1) : ℝ) *
                wTh (stationaryWindow R' z) (-1)
              + (A l (natExtWord R' z.1) : ℝ) * wTh (stationaryWindow R' z) 0) := by
        intro l
        have hc := StationaryIdentity31.stationary_character_reduction R (G.c l) hz
        simp only [A, B, hcore]
        rw [wTh_stationaryWindow R' z (by dsimp [R']; omega) (by omega),
          wTh_stationaryWindow R' z (by dsimp [R']; omega) (by omega)]
        calc
          torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
              (digitTruncWindow R M (stationaryWindow R' z)).2.2 t)
              = torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
                  (hatSzpow ((t : ℤ) - (R : ℤ) - 1) z).2.2) := by
                congr 2
                funext t
                simp only [digitTruncWindow]
                rw [wTh_stationaryWindow R' z (by have := t.isLt; dsimp [R']; omega)
                  (by have := t.isLt; dsimp [R']; omega)]
          _ = _ := hc
          _ = _ := by simp [hatSzpow]
      have hmode : ∀ l : Fin G.len,
          B l (natExtWord R' z.1) ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ) ∧
          A l (natExtWord R' z.1) ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ) := by
        intro l
        have hp : (l, natExtWord R' z.1) ∈ pairs := by simp [pairs, hw]
        have hle : (B l (natExtWord R' z.1)).natAbs +
            (A l (natExtWord R' z.1)).natAbs ≤ K' :=
          Finset.le_sup (f := fun p => (B p.1 p.2).natAbs + (A p.1 p.2).natAbs) hp
        have hBabs : |B l (natExtWord R' z.1)| ≤ (K' : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast (le_trans (Nat.le_add_right _ _) hle)
        have hAabs : |A l (natExtWord R' z.1)| ≤ (K' : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast (le_trans (Nat.le_add_left _ _) hle)
        exact ⟨Finset.mem_Icc.mpr (abs_le.mp hBabs), Finset.mem_Icc.mpr (abs_le.mp hAabs)⟩
      unfold DenseElt.eval WindowSymbol.evalWindow
      simp only [P, hw, if_true, hword]
      rw [hdense, htrunc]
      simp only [amp]
      simp_rw [hchar]
      symm
      simp_rw [Finset.sum_mul]
      calc
        (∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
            ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
              ∑ l : Fin G.len, (if r = B l (natExtWord R' z.1) ∧
                  s = A l (natExtWord R' z.1) then amp l (natExtWord R' z.1) else 0) *
                torusChar ((r : ℝ) * wTh (stationaryWindow R' z) (-1) +
                  (s : ℝ) * wTh (stationaryWindow R' z) 0))
            = ∑ l : Fin G.len, ∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
                ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
                  (if r = B l (natExtWord R' z.1) ∧ s = A l (natExtWord R' z.1)
                    then amp l (natExtWord R' z.1) else 0) *
                  torusChar ((r : ℝ) * wTh (stationaryWindow R' z) (-1) +
                    (s : ℝ) * wTh (stationaryWindow R' z) 0) := by
              calc
                _ = ∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ), ∑ l : Fin G.len,
                      ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
                        (if r = B l (natExtWord R' z.1) ∧ s = A l (natExtWord R' z.1)
                          then amp l (natExtWord R' z.1) else 0) *
                        torusChar ((r : ℝ) * wTh (stationaryWindow R' z) (-1) +
                          (s : ℝ) * wTh (stationaryWindow R' z) 0) := by
                            refine Finset.sum_congr rfl fun r _ => ?_
                            rw [Finset.sum_comm]
                _ = _ := by rw [Finset.sum_comm]
        _ = ∑ l : Fin G.len, amp l (natExtWord R' z.1) *
              torusChar ((B l (natExtWord R' z.1) : ℝ) * wTh (stationaryWindow R' z) (-1) +
                (A l (natExtWord R' z.1) : ℝ) * wTh (stationaryWindow R' z) 0) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_eq_single (B l (natExtWord R' z.1))]
          · rw [Finset.sum_eq_single (A l (natExtWord R' z.1))]
            · simp
            · intro s _ hs
              rw [if_neg (by rintro ⟨_, hsl⟩; exact hs hsl)]
              simp
            · intro h
              exact (h (hmode l).2).elim
          · intro r _ hr
            refine Finset.sum_eq_zero fun s _ => ?_
            rw [if_neg (by rintro ⟨hrl, _⟩; exact hr hrl)]
            simp
          · intro h
            exact (h (hmode l).1).elim
        _ = _ := rfl
    · rw [Set.indicator_of_notMem (fun h => hw (hmem.mp h))]
      unfold WindowSymbol.evalWindow
      simp [P, hword, hw]

  refine ⟨K', P, hstationary, ?_⟩
  intro α hirr hα n j hj
  rw [← WindowSymbol.evalWindow_actualWindow P α n j hj]
  have hword : windowWordOf R' (actualWindow R' α n j) = windowWord R' α j := by
    funext i
    change wA (actualWindow R' α n j) ((i : ℤ) - (R' : ℤ)) = _
    rw [wA_actualWindow R' α n j (by omega) (by omega) (by omega)]
    congr 1
    omega
  have hprefix : ∀ i : Fin (2 * R'),
      (actualWindow R' α n j).1 ⟨(i : ℕ), by have := i.isLt; omega⟩ =
        windowWord R' α j i := by
    intro i
    rfl
  have hmem : actualWindow R' α n j ∈ digitCapEvent R' K ↔
      windowWord R' α j ∈ words := by
    rw [Fintype.mem_piFinset]
    simp only [digitCapEvent, Set.mem_setOf_eq, Finset.mem_range]
    constructor
    · intro h i
      have hi := h i
      rw [hprefix i] at hi
      exact Nat.lt_succ_of_le hi
    · intro h i
      have hi := h i
      rw [hprefix i]
      exact Nat.le_of_lt_succ hi
  by_cases hw : windowWord R' α j ∈ words
  · rw [Set.indicator_of_mem (hmem.mpr hw)]
    have hcore : coreWord (windowWord R' α j) = windowWord R α j := by
      funext i
      simp only [coreWord, windowWord]
      congr 1
      dsimp [R']
      omega
    have hdense : (digitTruncWindow R M (actualWindow R' α n j)).1 =
        denseDigits (windowWord R' α j) := by
      funext i
      simp only [digitTruncWindow, denseDigits]
      rw [wA_actualWindow R' α n j (by omega) (by dsimp [R']; omega)
        (by have := i.isLt; dsimp [R']; omega)]
      simp only [windowWord]
      congr 1
      dsimp [R']
      omega
    have htrunc : (digitTruncWindow R M (actualWindow R' α n j)).2.1 =
        truncReals (windowWord R' α j) := by
      funext i
      simp only [digitTruncWindow, truncReals]
      apply cfFinite_congr
      intro k hk
      rw [dif_pos hk, wA_actualWindow R' α n j (by omega)
        (by dsimp [R']; omega) (by have := i.isLt; dsimp [R']; omega)]
      simp only [windowWord]
      congr 1
      dsimp [R']
      omega
    have hchar : ∀ l : Fin G.len,
        torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
            (digitTruncWindow R M (actualWindow R' α n j)).2.2 t) =
          torusChar ((B l (windowWord R' α j) : ℝ) * thetaPred α n j +
            (A l (windowWord R' α j) : ℝ) * theta α n j) := by
      intro l
      obtain ⟨m, hm⟩ := window_character_reduction_v5_exact R (G.c l)
        α hirr hα n j (by omega)
      have hcoords :
          (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
              (digitTruncWindow R M (actualWindow R' α n j)).2.2 t) =
            ∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
              theta α n (j + (t : ℕ) - (R + 1)) := by
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        change wTh (actualWindow R' α n j) ((t : ℤ) - (R : ℤ) - 1) = _
        rw [wTh_actualWindow R' α n j (by omega) (by dsimp [R']; omega)
          (by have := t.isLt; dsimp [R']; omega)]
        congr 1
        omega
      rw [hcoords, hm]
      have hreorder :
          (winA1 R (G.c l) (windowWord R α j) : ℝ) * theta α n j +
              (winB1 R (G.c l) (windowWord R α j) : ℝ) * thetaPred α n j +
              (m : ℝ) =
            ((B l (windowWord R' α j) : ℝ) * thetaPred α n j +
              (A l (windowWord R' α j) : ℝ) * theta α n j) + (m : ℝ) := by
        simp only [A, B, hcore]
        ring
      rw [hreorder, torusChar_add_int]
    have hmode : ∀ l : Fin G.len,
        B l (windowWord R' α j) ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ) ∧
        A l (windowWord R' α j) ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ) := by
      intro l
      have hp : (l, windowWord R' α j) ∈ pairs := by simp [pairs, hw]
      have hle : (B l (windowWord R' α j)).natAbs +
          (A l (windowWord R' α j)).natAbs ≤ K' :=
        Finset.le_sup
          (f := fun p => (B p.1 p.2).natAbs + (A p.1 p.2).natAbs) hp
      have hBabs : |B l (windowWord R' α j)| ≤ (K' : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (le_trans (Nat.le_add_right _ _) hle)
      have hAabs : |A l (windowWord R' α j)| ≤ (K' : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (le_trans (Nat.le_add_left _ _) hle)
      exact ⟨Finset.mem_Icc.mpr (abs_le.mp hBabs),
        Finset.mem_Icc.mpr (abs_le.mp hAabs)⟩
    have hTm : wTh (actualWindow R' α n j) (-1) = thetaPred α n j := by
      rw [wTh_actualWindow R' α n j (by omega) (by dsimp [R']; omega)
        (by dsimp [R']; omega)]
      rw [show ((j : ℤ) + (-1)).toNat = j - 1 by omega]
      obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hj']
      rfl
    have hT0 : wTh (actualWindow R' α n j) 0 = theta α n j := by
      rw [wTh_actualWindow R' α n j (by omega) (by dsimp [R']; omega)
        (by dsimp [R']; omega)]
      simp
    unfold DenseElt.eval WindowSymbol.evalWindow
    simp only [P, hw, if_true, hword, hTm, hT0]
    rw [hdense, htrunc]
    have hamp : ∀ l : Fin G.len,
        G.D l (denseDigits (windowWord R' α j)) *
            G.g l (truncReals (windowWord R' α j)) = amp l (windowWord R' α j) :=
      fun _ => rfl
    simp_rw [hamp]
    simp_rw [hchar]
    symm
    simp_rw [Finset.sum_mul]
    calc
      (∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
          ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
            ∑ l : Fin G.len,
              (if r = B l (windowWord R' α j) ∧ s = A l (windowWord R' α j)
                then amp l (windowWord R' α j) else 0) *
              torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j)) =
          ∑ l : Fin G.len, ∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
            ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
              (if r = B l (windowWord R' α j) ∧ s = A l (windowWord R' α j)
                then amp l (windowWord R' α j) else 0) *
              torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j) := by
        calc
          _ = ∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ), ∑ l : Fin G.len,
                ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
                  (if r = B l (windowWord R' α j) ∧ s = A l (windowWord R' α j)
                    then amp l (windowWord R' α j) else 0) *
                  torusChar ((r : ℝ) * thetaPred α n j +
                    (s : ℝ) * theta α n j) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
      _ = ∑ l : Fin G.len, amp l (windowWord R' α j) *
            torusChar ((B l (windowWord R' α j) : ℝ) * thetaPred α n j +
              (A l (windowWord R' α j) : ℝ) * theta α n j) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_eq_single (B l (windowWord R' α j))]
        · rw [Finset.sum_eq_single (A l (windowWord R' α j))]
          · simp
          · intro s _ hs
            rw [if_neg (by rintro ⟨_, hsl⟩; exact hs hsl)]
            simp
          · intro h
            exact (h (hmode l).2).elim
        · intro r _ hr
          refine Finset.sum_eq_zero fun s _ => ?_
          rw [if_neg (by rintro ⟨hrl, _⟩; exact hr hrl)]
          simp
        · intro h
          exact (h (hmode l).1).elim
      _ = _ := rfl
  · have hnot : actualWindow (R + M) α n j ∉ digitCapEvent (R + M) K := by
      intro h
      apply hw
      exact hmem.mp (by simpa [R'] using h)
    rw [Set.indicator_of_notMem hnot]
    unfold WindowSymbol.evalWindow
    simp [P, hword, hw]

/-! ## Dense-algebra one-block closure -/

lemma actualWindow_orbitConsistent (R : ℕ) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) {n j : ℕ} (hj : R ≤ j) :
    OrbitConsistent R (actualWindow R α n j) := by
  constructor
  · intro t htlo hthi
    rw [wX_actualWindow R α n j hj htlo hthi,
      wA_actualWindow R α n j hj htlo hthi]
    let m := ((j : ℤ) + t).toNat
    have hm : (j : ℤ) + t = (m : ℤ) := by
      dsimp [m]
      rw [Int.toNat_of_nonneg]
      omega
    rw [hm]
    exact ⟨gaussIter_mem_Ioo hα hirr m, gaussIter_irrational hirr m, rfl⟩
  · intro t htlo hthi
    rw [wX_actualWindow R α n j hj (by omega) hthi,
      wX_actualWindow R α n j hj htlo (by omega)]
    have hm : ((j : ℤ) + (t + 1)).toNat = ((j : ℤ) + t).toNat + 1 := by
      have hnonneg : 0 ≤ (j : ℤ) + t := by omega
      omega
    rw [hm, gaussIter_succ]

/-- One Heine--Cantor/Fibonacci choice of `M` works pointwise on every
orbit-consistent window, hence both on the stationary support and on every
irrational actual window with enough room. -/
lemma exists_uniform_digitTrunc (R : ℕ) (G : DenseElt R) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℕ, 1 ≤ M ∧
      (∀ w : WindowSpace (R + M), OrbitConsistent (R + M) w →
        ‖G.eval (windowProj (Nat.le_add_right R M) w) -
          G.eval (digitTruncWindow R M w)‖ ≤ η / 2) := by
  classical
  have hA0 : (0 : ℝ) ≤ ∑ l : Fin G.len, ∑ v ∈ G.Dwords l, ‖G.D l v‖ :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun v _ => norm_nonneg _
  set A : ℝ := ∑ l : Fin G.len, ∑ v ∈ G.Dwords l, ‖G.D l v‖ with hAdef
  set η' : ℝ := η / (2 * (A + 1)) with hη'def
  have hη'0 : 0 < η' := div_pos hη (by linarith)
  set C : Set (Fin (2 * R + 1) → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ l : Fin G.len, ∀ x ∈ C, ∀ y ∈ C,
      dist x y < δ → dist (G.g l x) (G.g l y) < η' := by
    have hu : ∀ l : Fin G.len, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∀ y ∈ C,
        dist x y < δ → dist (G.g l x) (G.g l y) < η' := by
      intro l
      have hc : IsCompact C := isCompact_univ_pi fun _ => isCompact_Icc
      have huc : UniformContinuousOn (G.g l) C :=
        hc.uniformContinuousOn_of_continuous (G.g_continuous l).continuousOn
      rcases Metric.uniformContinuousOn_iff.mp huc η' hη'0 with ⟨δ, hδ0, hδ⟩
      exact ⟨δ, hδ0, fun x hx y hy hxy => hδ x hx y hy hxy⟩
    choose δf hδf0 hδf using hu
    rcases isEmpty_or_nonempty (Fin G.len) with hE | hNE
    · exact ⟨1, one_pos, fun l => (hE.false l).elim⟩
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty δf, ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        exact fun l _ => hδf0 l
      · intro l x hx y hy hxy
        exact hδf l x hx y hy
          (lt_of_lt_of_le hxy (Finset.inf'_le _ (Finset.mem_univ l)))
  obtain ⟨M₀, hM₀⟩ := exists_fib_inv_lt hδ0
  let M := M₀ + 1
  have hfib₀ : (0 : ℝ) < Nat.fib (M₀ + 1) := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < M₀ + 1))
  have hfib₁ : (0 : ℝ) < Nat.fib (M₀ + 2) := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < M₀ + 2))
  have hfible : ((Nat.fib (M₀ + 1) : ℕ) : ℝ) ≤ (Nat.fib (M₀ + 2) : ℝ) := by
    exact_mod_cast (Nat.fib_le_fib_succ (n := M₀ + 1))
  have hM : ((Nat.fib (M + 1) : ℝ))⁻¹ < δ := by
    rw [show M + 1 = M₀ + 2 by simp [M]]
    exact lt_of_le_of_lt ((inv_le_inv₀ hfib₁ hfib₀).2 hfible) hM₀
  refine ⟨M, by simp [M], ?_⟩
  intro w hw
  have hfst := digitTruncWindow_fst_eq R M w
  have htrd := digitTruncWindow_trd_eq R M w
  have hdiff : G.eval (windowProj (Nat.le_add_right R M) w)
      - G.eval (digitTruncWindow R M w) = ∑ l : Fin G.len,
        G.D l ((windowProj (Nat.le_add_right R M) w).1) *
          (G.g l ((windowProj (Nat.le_add_right R M) w).2.1) -
            G.g l ((digitTruncWindow R M w).2.1)) *
          torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
            (windowProj (Nat.le_add_right R M) w).2.2 t) := by
    unfold DenseElt.eval
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hfst, htrd]
    ring
  have hp : (windowProj (Nat.le_add_right R M) w).2.1 ∈ C := by
    intro i _
    rw [windowProj_snd_fst_eq_wX]
    have hi := i.isLt
    have hI := (hw.1 ((i : ℤ) - (R : ℤ)) (by push_cast; omega)
      (by push_cast; omega)).1
    exact ⟨hI.1.le, hI.2.le⟩
  have ht : (digitTruncWindow R M w).2.1 ∈ C := by
    intro i _
    change cfFinite (fun k => wA w ((i : ℤ) - (R : ℤ) + (k : ℤ))) M ∈ Icc (0 : ℝ) 1
    refine ⟨cfFinite_nonneg M _, cfFinite_le_one M _ fun k hk => ?_⟩
    have hi := i.isLt
    have h1 : -(((R + M) : ℕ) : ℤ) ≤ (i : ℤ) - (R : ℤ) + (k : ℤ) := by push_cast; omega
    have h2 : (i : ℤ) - (R : ℤ) + (k : ℤ) ≤ (((R + M) : ℕ) : ℤ) := by push_cast; omega
    obtain ⟨hI, hi', hd⟩ := hw.1 _ h1 h2
    rw [hd]
    exact one_le_digit hI hi' 0
  have hdist : dist ((windowProj (Nat.le_add_right R M) w).2.1)
      ((digitTruncWindow R M w).2.1) < δ := by
    rw [dist_pi_lt_iff hδ0]
    intro i
    have hi := i.isLt
    have h1 : -(((R + M) : ℕ) : ℤ) ≤ (i : ℤ) - (R : ℤ) := by push_cast; omega
    obtain ⟨hI, hi', -⟩ := hw.1 ((i : ℤ) - (R : ℤ)) h1 (by push_cast; omega)
    have hcf : cfFinite (fun k => wA w ((i : ℤ) - (R : ℤ) + (k : ℤ))) M =
        cfFinite (fun k => digit (wX w ((i : ℤ) - (R : ℤ))) k) M :=
      cfFinite_congr M _ _ (fun k hk =>
        orbitConsistent_wA_eq_digit hw h1 k (by push_cast; omega))
    rw [Real.dist_eq, windowProj_snd_fst_eq_wX]
    show |wX w ((i : ℤ) - (R : ℤ)) -
        cfFinite (fun k => wA w ((i : ℤ) - (R : ℤ) + (k : ℤ))) M| < δ
    rw [hcf]
    exact lt_of_le_of_lt (abs_sub_cfFinite_digit_le M hI hi') hM
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum
    (g := fun l => (∑ v ∈ G.Dwords l, ‖G.D l v‖) * η') ?_) ?_)
  · intro l _
    rw [norm_mul, norm_mul, Prop42.norm_torusChar, mul_one]
    have hD : ‖G.D l ((windowProj (Nat.le_add_right R M) w).1)‖ ≤
        ∑ v ∈ G.Dwords l, ‖G.D l v‖ := by
      by_cases hu : (windowProj (Nat.le_add_right R M) w).1 ∈ G.Dwords l
      · exact Finset.single_le_sum (fun v _ => norm_nonneg _) hu
      · rw [G.D_support l _ hu, norm_zero]
        exact Finset.sum_nonneg fun v _ => norm_nonneg _
    have hg : ‖G.g l ((windowProj (Nat.le_add_right R M) w).2.1) -
        G.g l ((digitTruncWindow R M w).2.1)‖ ≤ η' := by
      have := hδ l _ hp _ ht hdist
      rw [dist_eq_norm] at this
      exact this.le
    exact mul_le_mul hD hg (norm_nonneg _)
      (Finset.sum_nonneg fun v _ => norm_nonneg _)
  · rw [← Finset.sum_mul, ← hAdef]
    rw [hη'def, ← mul_div_assoc,
      div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (A + 1)) (by norm_num : (0 : ℝ) < 2)]
    nlinarith

lemma exists_common_digitCap_tail (R' : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ,
      (windowLaw R').real ((digitCapEvent R' K)ᶜ) < δ ∧
      ∀ n j : ℕ, R' ≤ j →
        (volume.restrict (Ioo (0 : ℝ) 1)).real
          {α : ℝ | actualWindow R' α n j ∉ digitCapEvent R' K} < δ := by
  obtain ⟨C, hC, hact⟩ := qActualWindowLaw_fullDigitCapQ_compl_le R'
  obtain ⟨K, hK⟩ := exists_nat_gt
    (max ((2 * (R' : ℝ)) * 2 / δ)
      ((((2 * R' + 1 : ℕ) : ℝ) * C) / δ))
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hstatNum : (2 * (R' : ℝ)) * (2 / ((K : ℝ) + 1)) < δ := by
    have hgt : (2 * (R' : ℝ)) * 2 / δ < (K : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hK
    rw [div_lt_iff₀ hδ] at hgt
    rw [show (2 * (R' : ℝ)) * (2 / ((K : ℝ) + 1)) =
      ((2 * (R' : ℝ)) * 2) / ((K : ℝ) + 1) by ring,
      div_lt_iff₀ hKpos]
    nlinarith
  have hactNum : (((2 * R' + 1 : ℕ) : ℝ) * C) / ((K : ℝ) + 1) < δ := by
    have hgt : (((2 * R' + 1 : ℕ) : ℝ) * C) / δ < (K : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hK
    rw [div_lt_iff₀ hδ] at hgt
    rw [div_lt_iff₀ hKpos]
    nlinarith
  refine ⟨K, ?_, ?_⟩
  · have hle := windowLaw_digitCapEvent_compl_le R' K
    rw [Measure.real]
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hle).trans_lt hstatNum
  · intro n j hj
    let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
    let bad : Set ℝ := {α : ℝ | actualWindow R' α n j ∉ digitCapEvent R' K}
    let qbad : Set ℝ := (fun α => quotientWindow R' (actualWindow R' α n j)) ⁻¹'
      (fullDigitCapQ R' K)ᶜ
    have hsub : bad ⊆ qbad := by
      intro α hα
      simp only [bad, qbad, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        fullDigitCapQ, digitCapEvent, not_forall, not_le] at hα ⊢
      obtain ⟨i, hi⟩ := hα
      exact ⟨⟨i, by omega⟩, hi⟩
    have hq : μ qbad = qActualWindowLaw R' n j ((fullDigitCapQ R' K)ᶜ) := by
      rw [qActualWindowLaw, actualWindowLaw,
        Measure.map_map (measurable_quotientWindow R') (measurable_actualWindow R' n j),
        Measure.map_apply
          ((measurable_quotientWindow R').comp (measurable_actualWindow R' n j))
          (measurableSet_fullDigitCapQ R' K).compl]
      rfl
    have hle : μ bad ≤ ENNReal.ofReal
        ((((2 * R' + 1 : ℕ) : ℝ) * C) / ((K : ℝ) + 1)) := by
      refine (measure_mono hsub).trans ?_
      rw [hq]
      exact hact K n j hj
    change μ.real bad < δ
    rw [Measure.real]
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hle).trans_lt hactNum

private lemma integrable_of_ae_bound_dense {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ] (f : X → E)
    (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) : Integrable f μ := by
  apply Integrable.mono' (integrable_const B) hf
  simpa using hB

private lemma integral_cap_error_le_dense {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → E) (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) (E₀ : Set X) (hE₀ : MeasurableSet E₀) :
    ‖(∫ x, f x ∂μ) - ∫ x, E₀.indicator f x ∂μ‖ ≤ B * μ.real E₀ᶜ := by
  have hfint := integrable_of_ae_bound_dense f hf hB
  rw [← integral_sub hfint (hfint.indicator hE₀)]
  have heq : (fun x => f x - E₀.indicator f x) = E₀ᶜ.indicator f := by
    funext x
    by_cases hx : x ∈ E₀ <;> simp [hx]
  rw [heq, integral_indicator hE₀.compl]
  exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top _ _)
    (by
      filter_upwards [hB.filter_mono (ae_mono Measure.restrict_le_self)] with x hx
      exact hx)

private lemma continuous_qeval_dense {R : ℕ} (G : DenseElt R) : Continuous G.qeval := by
  unfold DenseElt.qeval
  refine continuous_finset_sum _ fun l _ =>
    ((continuous_of_discreteTopology.comp continuous_fst).mul
      ((G.g_continuous l).comp (continuous_fst.comp continuous_snd))).mul ?_
  exact (UnitAddTorus.mFourier (G.c l)).continuous.comp
    (continuous_snd.comp continuous_snd)

lemma integral_qeval_eq_eval (R : ℕ) (G : DenseElt R) :
    (∫ q, G.qeval q ∂qWindowLaw R) = ∫ w, G.eval w ∂windowLaw R := by
  rw [qWindowLaw, integral_map (measurable_quotientWindow R).aemeasurable
    (continuous_qeval_dense G).aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => denseElt_qeval_quotientWindow G w

lemma integral_evalWindow_windowLaw {R K : ℕ} (U : WindowSymbol R K) :
    (∫ w, U.evalWindow w ∂windowLaw R) = U.stationaryIntegral := by
  rw [windowLaw, integral_map (measurable_stationaryWindow R).aemeasurable
    (measurable_evalWindow U).aestronglyMeasurable]
  unfold WindowSymbol.stationaryIntegral
  apply integral_congr_ae
  filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz
  have hword : windowWordOf R (stationaryWindow R z) = natExtWord R z.1 := by
    funext i
    rw [windowWordOf, wA_stationaryWindow R z (by omega) (by omega)]
    exact (StationaryIdentity31.wordFn_natExtWord hz R (i : ℕ) i.isLt).symm.trans (by
      simp [wordFn])
  have hT0 : wTh (stationaryWindow R z) 0 = z.2.2 := by
    rw [wTh_stationaryWindow R z (by omega) (by omega)]
    simp [hatSzpow]
  have hTm : wTh (stationaryWindow R z) (-1) = z.2.1 := by
    rw [wTh_stationaryWindow R z (by omega) (by omega)]
    have h := (StationaryIdentity31.hatSzpow_fst_torus hz 0).symm
    simpa [hatSzpow] using h
  unfold WindowSymbol.evalWindow WindowSymbol.eval
  rw [hword, hTm, hT0]

/-- Lemma 6.3 for one dense-algebra element, with the two currently
scratch-level inputs stated at their exact interfaces. -/
theorem denseElt_oneblock_full (R : ℕ)
    (hidentity : ∀ (R M K : ℕ) (G : DenseElt R), 1 ≤ M →
      ∃ K' : ℕ, ∃ P : WindowSymbol (R + M) K',
        (∀ᵐ w ∂(windowLaw (R + M)),
          (digitCapEvent (R + M) K).indicator
              (fun v => G.eval (digitTruncWindow R M v)) w = P.evalWindow w) ∧
        ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ,
          R + M + 1 ≤ j →
          (digitCapEvent (R + M) K).indicator
              (fun v => G.eval (digitTruncWindow R M v))
              (actualWindow (R + M) α n j) = P.at α n j)
    (honeblock : ∀ {R K : ℕ} (U : WindowSymbol R K) (ε : ℝ), 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n j) - U.stationaryIntegral‖ < ε) :
    DenseEltOneBlock R := by
  intro G ε hε
  let τ : ℝ := ε / 6
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨M, hMpos, htrunc⟩ := exists_uniform_digitTrunc R G (ε / 3) (by positivity)
  obtain ⟨B, hB0, hB⟩ := denseElt_bound G
  let δ : ℝ := τ / (B + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hstatTail, hactTail⟩ := exists_common_digitCap_tail (R + M) δ hδ
  obtain ⟨K', P, hPstat, hPact⟩ := hidentity R M K G hMpos
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let ν : Measure (WindowSpace (R + M)) := windowLaw (R + M)
  let π := windowProj (Nat.le_add_right R M)
  let F₀ : WindowSpace (R + M) → ℂ := fun w => G.eval (π w)
  let F₁ : WindowSpace (R + M) → ℂ := fun w => G.eval (digitTruncWindow R M w)
  let E₀ : Set (WindowSpace (R + M)) := digitCapEvent (R + M) K
  let F₂ : WindowSpace (R + M) → ℂ := E₀.indicator F₁
  have hmF₀ : Measurable F₀ :=
    (measurable_denseElt G).comp (measurable_windowProj _)
  have hmF₁ : Measurable F₁ :=
    (measurable_denseElt G).comp (measurable_digitTruncWindow R M)
  have hmE₀ : MeasurableSet E₀ := measurableSet_digitCapEvent _ _
  have hF₀B : ∀ᵐ w ∂ν, ‖F₀ w‖ ≤ B := by
    filter_upwards [ae_orbitConsistent (R + M)] with w hw
    change ‖G.eval (windowProj (Nat.le_add_right R M) w)‖ ≤ B
    apply hB
    intro i
    rw [windowProj_snd_fst_eq_wX]
    have hI := (hw.1 ((i : ℤ) - (R : ℤ)) (by push_cast; omega)
      (by push_cast; omega)).1
    exact ⟨hI.1.le, hI.2.le⟩
  have hF₁B : ∀ᵐ w ∂ν, ‖F₁ w‖ ≤ B := by
    filter_upwards [ae_orbitConsistent (R + M)] with w hw
    apply hB
    intro i
    refine ⟨cfFinite_nonneg M _, cfFinite_le_one M _ fun k hk => ?_⟩
    have h1 : -(((R + M) : ℕ) : ℤ) ≤ (i : ℤ) - (R : ℤ) + (k : ℤ) := by
      push_cast; omega
    obtain ⟨hI, hi, hd⟩ := hw.1 _ h1 (by push_cast; omega)
    rw [hd]
    exact one_le_digit hI hi 0
  have hF₀int : Integrable F₀ ν :=
    integrable_of_ae_bound_dense F₀ hmF₀.aestronglyMeasurable hF₀B
  have hF₁int : Integrable F₁ ν :=
    integrable_of_ae_bound_dense F₁ hmF₁.aestronglyMeasurable hF₁B
  have hstatTrunc : ‖(∫ w, F₀ w ∂ν) - ∫ w, F₁ w ∂ν‖ ≤ τ := by
    rw [← integral_sub hF₀int hF₁int]
    have hle := norm_integral_le_of_norm_le_const (C := τ) (by
      filter_upwards [ae_orbitConsistent (R + M)] with w hw
      have hwle := htrunc w hw
      change ‖F₀ w - F₁ w‖ ≤ τ
      change ‖G.eval (windowProj (Nat.le_add_right R M) w) -
        G.eval (digitTruncWindow R M w)‖ ≤ τ
      refine hwle.trans_eq ?_
      dsimp [τ]
      ring)
    simpa [ν] using hle
  have hstatCap : ‖(∫ w, F₁ w ∂ν) - ∫ w, F₂ w ∂ν‖ < τ := by
    refine (integral_cap_error_le_dense F₁ hmF₁.aestronglyMeasurable hF₁B E₀ hmE₀).trans_lt ?_
    have hm : B * δ < τ := by
      dsimp [δ]
      rw [mul_div]
      exact (div_lt_iff₀ (by positivity : 0 < B + 1)).2 (by nlinarith)
    by_cases hBz : B = 0
    · simpa [hBz] using hτ
    · exact (mul_lt_mul_of_pos_left hstatTail (lt_of_le_of_ne hB0 (Ne.symm hBz))).trans hm
  have hstatP : (∫ w, F₂ w ∂ν) = P.stationaryIntegral := by
    calc
      _ = ∫ w, P.evalWindow w ∂windowLaw (R + M) := by
        apply integral_congr_ae
        simpa [ν, F₂, E₀, F₁] using hPstat
      _ = P.stationaryIntegral := integral_evalWindow_windowLaw P
  have hprojStat : (∫ w, F₀ w ∂ν) = ∫ w, G.eval w ∂windowLaw R := by
    rw [← windowProj_map_windowLaw (Nat.le_add_right R M),
      integral_map (measurable_windowProj _).aemeasurable
        (measurable_denseElt G).aestronglyMeasurable]
  filter_upwards [eventually_bulk_radius (R + M), honeblock P τ hτ] with n hroom hn
  intro j hj
  let A₀ : ℝ → ℂ := fun α => F₀ (actualWindow (R + M) α n j)
  let A₁ : ℝ → ℂ := fun α => F₁ (actualWindow (R + M) α n j)
  let A₂ : ℝ → ℂ := fun α => F₂ (actualWindow (R + M) α n j)
  have hmA₀ : Measurable A₀ := hmF₀.comp (measurable_actualWindow _ n j)
  have hmA₁ : Measurable A₁ := hmF₁.comp (measurable_actualWindow _ n j)
  have hA₀B : ∀ᵐ α ∂μ, ‖A₀ α‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
      with α hα hirr
    change ‖G.eval (windowProj (Nat.le_add_right R M)
      (actualWindow (R + M) α n j))‖ ≤ B
    rw [windowProj_actualWindow _ α n j (hroom j hj)]
    apply hB
    intro i
    exact ⟨(gaussIter_mem_Ioo hα hirr _).1.le,
      (gaussIter_mem_Ioo hα hirr _).2.le⟩
  have hA₁B : ∀ᵐ α ∂μ, ‖A₁ α‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
      with α hα hirr
    have hjRM : R + M ≤ j := (Nat.le_succ (R + M)).trans (hroom j hj)
    have hw := actualWindow_orbitConsistent (R + M) hα hirr
      (n := n) (j := j) hjRM
    apply hB
    intro i
    refine ⟨cfFinite_nonneg M _, cfFinite_le_one M _ fun k hk => ?_⟩
    have h1 : -(((R + M) : ℕ) : ℤ) ≤ (i : ℤ) - (R : ℤ) + (k : ℤ) := by
      push_cast; omega
    obtain ⟨hI, hi, hd⟩ := hw.1 _ h1 (by push_cast; omega)
    rw [hd]
    exact one_le_digit hI hi 0
  have hA₀int := integrable_of_ae_bound_dense A₀ hmA₀.aestronglyMeasurable hA₀B
  have hA₁int := integrable_of_ae_bound_dense A₁ hmA₁.aestronglyMeasurable hA₁B
  have hactTrunc : ‖(∫ α, A₀ α ∂μ) - ∫ α, A₁ α ∂μ‖ ≤ τ := by
    rw [← integral_sub hA₀int hA₁int]
    refine (norm_integral_le_of_norm_le_const (C := τ) ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
        with α hα hirr
      have hjRM : R + M ≤ j := (Nat.le_succ (R + M)).trans (hroom j hj)
      have hw := actualWindow_orbitConsistent (R + M) hα hirr
        (n := n) (j := j) hjRM
      have hwle := htrunc (actualWindow (R + M) α n j) hw
      change ‖G.eval (windowProj (Nat.le_add_right R M)
          (actualWindow (R + M) α n j)) -
        G.eval (digitTruncWindow R M (actualWindow (R + M) α n j))‖ ≤ τ
      refine hwle.trans_eq ?_
      dsimp [τ]
      ring
    · simp [μ, Measure.real]
  have hactCap : ‖(∫ α, A₁ α ∂μ) - ∫ α, A₂ α ∂μ‖ < τ := by
    have hEact : MeasurableSet ((fun α => actualWindow (R + M) α n j) ⁻¹' E₀) :=
      hmE₀.preimage (measurable_actualWindow _ n j)
    have hcap := integral_cap_error_le_dense A₁ hmA₁.aestronglyMeasurable hA₁B _ hEact
    have hm : B * δ < τ := by
      dsimp [δ]
      rw [mul_div]
      exact (div_lt_iff₀ (by positivity : 0 < B + 1)).2 (by nlinarith)
    have hjRM : R + M ≤ j := (Nat.le_succ (R + M)).trans (hroom j hj)
    refine hcap.trans_lt ?_
    by_cases hBz : B = 0
    · simpa [hBz] using hτ
    · exact (mul_lt_mul_of_pos_left (hactTail n j hjRM)
        (lt_of_le_of_ne hB0 (Ne.symm hBz))).trans hm
  have hactP : (∫ α, A₂ α ∂μ) = ∫ α in Ioo (0 : ℝ) 1, P.at α n j := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
      with α hα hirr
    simpa [μ, A₂, F₂, E₀, F₁] using
      hPact α hirr hα n j (hroom j hj)
  have hA₀orig : (∫ α, A₀ α ∂μ) =
      ∫ α in Ioo (0 : ℝ) 1, G.qeval (actualQWindow R α n j) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with α hα
    change G.eval (windowProj (Nat.le_add_right R M) (actualWindow (R + M) α n j)) =
      G.qeval (actualQWindow R α n j)
    rw [windowProj_actualWindow _ α n j (hroom j hj), actualQWindow,
      denseElt_qeval_quotientWindow]
  rw [← hA₀orig, integral_qeval_eq_eval, ← hprojStat]
  have hmid : ‖(∫ α, A₂ α ∂μ) - ∫ w, F₂ w ∂ν‖ < τ := by
    rw [hactP, hstatP]
    exact hn j hj
  calc
    ‖(∫ α, A₀ α ∂μ) - ∫ w, F₀ w ∂ν‖
      ≤ ‖(∫ α, A₀ α ∂μ) - ∫ α, A₁ α ∂μ‖ +
        ‖(∫ α, A₁ α ∂μ) - ∫ α, A₂ α ∂μ‖ +
        ‖(∫ α, A₂ α ∂μ) - ∫ w, F₂ w ∂ν‖ +
        ‖(∫ w, F₂ w ∂ν) - ∫ w, F₁ w ∂ν‖ +
        ‖(∫ w, F₁ w ∂ν) - ∫ w, F₀ w ∂ν‖ := by
          calc
            _ = ‖((∫ α, A₀ α ∂μ) - ∫ α, A₁ α ∂μ) +
                ((∫ α, A₁ α ∂μ) - ∫ α, A₂ α ∂μ) +
                (((∫ α, A₂ α ∂μ) - ∫ w, F₂ w ∂ν) +
                 ((∫ w, F₂ w ∂ν) - ∫ w, F₁ w ∂ν) +
                 ((∫ w, F₁ w ∂ν) - ∫ w, F₀ w ∂ν))‖ := by
                apply congrArg norm
                ring
            _ ≤ ‖(∫ α, A₀ α ∂μ) - ∫ α, A₁ α ∂μ‖ +
                ‖(∫ α, A₁ α ∂μ) - ∫ α, A₂ α ∂μ‖ +
                ‖(((∫ α, A₂ α ∂μ) - ∫ w, F₂ w ∂ν) +
                 ((∫ w, F₂ w ∂ν) - ∫ w, F₁ w ∂ν) +
                 ((∫ w, F₁ w ∂ν) - ∫ w, F₀ w ∂ν))‖ := norm_add₃_le
            _ ≤ _ := by
              have htail :
                  ‖((∫ α, A₂ α ∂μ) - ∫ w, F₂ w ∂ν) +
                    ((∫ w, F₂ w ∂ν) - ∫ w, F₁ w ∂ν) +
                    ((∫ w, F₁ w ∂ν) - ∫ w, F₀ w ∂ν)‖ ≤
                    ‖(∫ α, A₂ α ∂μ) - ∫ w, F₂ w ∂ν‖ +
                    ‖(∫ w, F₂ w ∂ν) - ∫ w, F₁ w ∂ν‖ +
                    ‖(∫ w, F₁ w ∂ν) - ∫ w, F₀ w ∂ν‖ := norm_add₃_le
              linarith
    _ < ε := by
      rw [norm_sub_rev (∫ w, F₂ w ∂ν) (∫ w, F₁ w ∂ν),
        norm_sub_rev (∫ w, F₁ w ∂ν) (∫ w, F₀ w ∂ν)]
      have : τ + τ + τ + τ + τ < ε := by dsimp [τ]; linarith
      exact lt_of_le_of_lt (add_le_add (add_le_add (add_le_add (add_le_add hactTrunc hactCap.le) hmid.le)
        hstatCap.le) hstatTrunc) this

/-- Lemma 6.3 for every dense-algebra element, with identity (31) and the
finite-symbol one-block theorem discharged by proved production results. -/
theorem denseEltOneBlock (R : ℕ) : DenseEltOneBlock R :=
  denseElt_oneblock_full R identity_31_both
    (fun U ε hε ↦ Kwon1002.windowSymbol_oneblock U ε hε)

/-- Bulk-uniform convergence for every bounded continuous quotient-window
test, with both dense one-block convergence and actual tightness discharged. -/
theorem boundedContinuous_transfer_clean (R : ℕ) (f : QWindow R →ᵇ ℂ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, f (actualQWindow R α n j)) -
          ∫ q, f q ∂qWindowLaw R‖ < ε :=
  boundedContinuous_transfer_of_oneBlock R f (denseEltOneBlock R)

end

end Kwon1002.Prop64

assert_no_sorry Kwon1002.Prop64.identity_31_both
assert_no_sorry Kwon1002.Prop64.denseElt_oneblock_full
assert_no_sorry Kwon1002.Prop64.denseEltOneBlock
assert_no_sorry Kwon1002.Prop64.boundedContinuous_transfer_clean
