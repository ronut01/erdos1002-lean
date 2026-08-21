import Kwon1002.StationaryReplace
import Kwon1002.PhaseBounds

/-!
# The nonzero-mode branch of Proposition 4.1, unconditional

This file assembles the three-step chain of the `v_s ≠ 0` branch of §4
(`ZeroMode.nonzero_mode_three_step`) from parts that are now all proved:

* **step 1** — the retained-cylinder cut: display (20) is proved
  (`LargeDeviation.display20_of_pos`), and the three-cut retained family
  of `StationaryReplace.retainedWords` realises the manuscript's local
  complete-cylinder cuts at `j_s`, `k₋`, `k₊` with discarded mass
  `≤ 3C₀e^{-c₀√L}` (`volume_discarded_retainedWords_le`), so
  `ZeroMode.nonzero_mode_cut_of_retained` applies;
* **step 2** — the stationary-mean replacement: on each retained
  depth-`k₊` cylinder the phase is frozen
  (`phase_freeze_on_cylinder`, cost `n|Q|·diam(I_w)`, controlled by the
  second inequality of (29)), the post-resonance digit factors are
  replaced by their stationary Gauss means
  (`StationaryReplace.leb_halfOpen_multiblock_mixing_complex`, uniformised
  over the block count in `leb_mixing_complex_uniform`), and the discarded
  depth-`k₊` cylinders are restored (the v8 restoration, using the
  saturation property of the retained family), at total cost
  `L^{O_{r,D}(1)}(e^{-c√L} + e^{-cH} + ρ^{cH})`;
* **step 3** — the oscillatory kill: what remains is display (22)-shaped
  at prefix depth `j_s + 1` with depth-`k₋` descendants, whose support
  bound is the retained upper cut at `k₋` and whose frequency
  non-degeneracy is display (28) (`Prop41Canon.display_28`); the first
  inequality of (29) is checked from the frozen windows, and
  `Display22.descendant_cylinder_estimate_core` finishes.

The result, `nonzero_mode_small_unconditional`, is the exact statement of
the sorried `Kwon1002.ErrorShape.nonzero_mode_small`, proved outright; the
canonical three-step chain is restated and proved as
`nonzero_mode_three_step'`.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace NonzeroMode

open Prop41 ErrorShape ZeroMode RetainedCut StationaryReplace

noncomputable section

/-! ## 1. The mixing constants, uniform over the block count -/

/-- `leb_halfOpen_multiblock_mixing_complex`, with one constant pair
serving every block count `s ≤ r`. -/
theorem leb_mixing_complex_uniform (r : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s, s ≤ r →
      ∀ (d M : ℕ) (w : List ℕ), w.length = d → (∀ a ∈ w, 0 < a) → 0 < d →
      ∀ Δ : ℝ,
      (∀ x ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
        ∀ y ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
          Irrational x → Irrational y → |x - y| ≤ Δ) →
      ∀ (t : ℕ → ℕ) (G : ℕ → ℝ → ℂ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → Measurable (G i)) →
        (∀ i, i < s → Prop41.BVBoundedBy K (fun x => (G i x).re)) →
        (∀ i, i < s → Prop41.BVBoundedBy K (fun x => (G i x).im)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        ‖(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              ∏ i ∈ Finset.range s, G i (gaussIter α (t i)))
            - ((volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal : ℂ)
                * ∏ i ∈ Finset.range s, ∫ x, G i x ∂Erdos1002.gaussMeasure‖
          ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
              * 2 ^ r * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s := by
  classical
  have H := fun s : ℕ => leb_halfOpen_multiblock_mixing_complex s
  choose Cf ρf hCf hρf0 hρf1 hspec using H
  have hne : (Finset.range (r + 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r)
  refine ⟨∑ i ∈ Finset.range (r + 1), Cf i, (Finset.range (r + 1)).sup' hne ρf,
    Finset.sum_pos (fun i _ => hCf i) hne, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hne
    exact lt_of_lt_of_le (hρf0 i) (Finset.le_sup' ρf hi)
  · exact (Finset.sup'_lt_iff hne).mpr (fun i _ => hρf1 i)
  · intro s hs d M w hlen hpos hd0 Δ hΔ t G K hK hGm hre him h0 hstep
    have hbase := hspec s d M w hlen hpos hd0 Δ hΔ t G K hK hGm hre him h0 hstep
    refine le_trans hbase ?_
    have hν0 : (0 : ℝ)
        ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal :=
      ENNReal.toReal_nonneg
    have hΔ0 : (0 : ℝ) ≤ Δ := by
      obtain ⟨β, hβ, hβirr⟩ := exists_irrational_mem_halfOpen hpos
      have := hΔ β hβ β hβ hβirr hβirr
      calc (0 : ℝ) ≤ |β - β| := abs_nonneg _
        _ ≤ Δ := this
    have hmem : s ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
    have hCle : Cf s ≤ ∑ i ∈ Finset.range (r + 1), Cf i :=
      Finset.single_le_sum (fun i _ => (hCf i).le) hmem
    have hρle : ρf s ≤ (Finset.range (r + 1)).sup' hne ρf := Finset.le_sup' ρf hmem
    have hρM : ρf s ^ M ≤ ((Finset.range (r + 1)).sup' hne ρf) ^ M :=
      pow_le_pow_left₀ (hρf0 s).le hρle M
    have hsum0 : (0 : ℝ) < ∑ i ∈ Finset.range (r + 1), Cf i :=
      Finset.sum_pos (fun i _ => hCf i) hne
    have hbrk : Cf s * ρf s ^ M + Δ
        ≤ (∑ i ∈ Finset.range (r + 1), Cf i)
            * ((Finset.range (r + 1)).sup' hne ρf) ^ M + Δ := by
      have := mul_le_mul hCle hρM (pow_nonneg (hρf0 s).le M) hsum0.le
      linarith
    have h2s : (2 : ℝ) ^ s ≤ 2 ^ r := by
      exact pow_le_pow_right₀ (by norm_num) hs
    have hbrk0 : (0 : ℝ) ≤ Cf s * ρf s ^ M + Δ := by
      have := mul_nonneg (hCf s).le (pow_nonneg (hρf0 s).le M)
      linarith
    have hlog0 : (0 : ℝ) ≤ 2 * Real.log 2 := by positivity
    have hKs : (0 : ℝ) ≤ K ^ s := by positivity
    calc (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
          * 2 ^ s * (2 * Real.log 2) * (Cf s * ρf s ^ M + Δ) * K ^ s
        ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
          * 2 ^ r * (2 * Real.log 2) * (Cf s * ρf s ^ M + Δ) * K ^ s := by
          have h1 : (Erdos1002.gaussMeasure
                (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal * 2 ^ s
              ≤ (Erdos1002.gaussMeasure
                (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal * 2 ^ r :=
            mul_le_mul_of_nonneg_left h2s hν0
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 hlog0) hbrk0) hKs
      _ ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
          * 2 ^ r * (2 * Real.log 2)
          * ((∑ i ∈ Finset.range (r + 1), Cf i)
              * ((Finset.range (r + 1)).sup' hne ρf) ^ M + Δ) * K ^ s := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbrk ?_) hKs
          positivity

/-! ## 2. Phase freezing on a cylinder -/

/-- **The phase freeze.**  On a cylinder of diameter `≤ Δ`, the pure phase
`e(Kα)` can be replaced by its value at any irrational point of the
cylinder inside an integral against a bounded amplitude, at cost
`2π|K|Δ·B·λ(I_w)`. -/
theorem phase_freeze_on_cylinder {w : List ℕ} (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a)
    (G : ℝ → ℂ) (hGm : Measurable G) (B : ℝ) (hB0 : 0 ≤ B)
    (hGb : ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α → ‖G α‖ ≤ B)
    (K : ℝ) {β : ℝ} (hβ : β ∈ Erdos1002.gaussHalfOpenPrefixCylinder w)
    (hβirr : Irrational β) (Δ : ℝ)
    (hΔ : ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α → |α - β| ≤ Δ) :
    ‖(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, G α * torusChar (K * α))
        - torusChar (K * β) * ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, G α‖
      ≤ 2 * Real.pi * |K| * Δ * B
          * (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
  set S := Erdos1002.gaussHalfOpenPrefixCylinder w with hSdef
  have hSm : MeasurableSet S := Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hvfin : volume S < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (halfOpenCylinder_subset_Ioc hw hpos)) ?_
    rw [Real.volume_Ioc]
    simp
  have hae_irr : ∀ᵐ α ∂(volume.restrict S), α ∈ S ∧ Irrational α := by
    filter_upwards [ae_restrict_mem hSm,
      ae_restrict_of_ae (LargeDeviation.ae_irrational_volume)] with α h1 h2
    exact ⟨h1, h2⟩
  haveI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hoscm : Measurable fun α : ℝ => torusChar (K * α) :=
    ZeroMode.continuous_torusChar.measurable.comp (measurable_const.mul measurable_id)
  have hint1 : IntegrableOn (fun α => G α * torusChar (K * α)) S volume := by
    refine Integrable.of_bound (C := B) ((hGm.mul hoscm).aestronglyMeasurable) ?_
    filter_upwards [hae_irr] with α hα
    rw [norm_mul, Prop42.norm_torusChar, mul_one]
    exact hGb α hα.1 hα.2
  have hint2 : IntegrableOn G S volume := by
    refine Integrable.of_bound (C := B) (hGm.aestronglyMeasurable) ?_
    filter_upwards [hae_irr] with α hα
    exact hGb α hα.1 hα.2
  have hsplit : (∫ α in S, G α * torusChar (K * α)) - torusChar (K * β) * ∫ α in S, G α
      = ∫ α in S, G α * (torusChar (K * α) - torusChar (K * β)) := by
    rw [← integral_const_mul, ← integral_sub hint1 (hint2.const_mul _)]
    congr 1
    funext α
    ring
  rw [hsplit]
  have hΔ0 : (0 : ℝ) ≤ Δ := le_trans (abs_nonneg _) (hΔ β hβ hβirr)
  have hb := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun α => G α * (torusChar (K * α) - torusChar (K * β)))
    (s := S) (C := B * (2 * Real.pi * |K| * Δ)) hvfin ?_
  · calc ‖∫ α in S, G α * (torusChar (K * α) - torusChar (K * β))‖
        ≤ B * (2 * Real.pi * |K| * Δ) * volume.real S := hb
      _ = 2 * Real.pi * |K| * Δ * B * (volume S).toReal := by
          rw [measureReal_def]
          ring
  · filter_upwards [hae_irr] with α hα
    rw [norm_mul]
    have h1 : ‖G α‖ ≤ B := hGb α hα.1 hα.2
    have h2 : ‖torusChar (K * α) - torusChar (K * β)‖ ≤ 2 * Real.pi * |K| * Δ := by
      refine le_trans (StationaryReplace.norm_torusChar_sub_le _ _) ?_
      have : |K * α - K * β| = |K| * |α - β| := by
        rw [← mul_sub, abs_mul]
      rw [this]
      have h3 : |α - β| ≤ Δ := hΔ α hα.1 hα.2
      calc 2 * Real.pi * (|K| * |α - β|) ≤ 2 * Real.pi * (|K| * Δ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = 2 * Real.pi * |K| * Δ := by ring
    exact mul_le_mul h1 h2 (norm_nonneg _) hB0

/-! ## 3. Miscellaneous helpers -/

/-- A point of a positive cylinder lies in the cylinder of every prefix
of its word (for irrational points). -/
theorem mem_halfOpen_take {w : List ℕ} (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a)
    {α : ℝ} (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w)
    (hirr : Irrational α) (m : ℕ) :
    α ∈ Erdos1002.gaussHalfOpenPrefixCylinder (w.take m) := by
  have hαIoo : α ∈ Ioo (0 : ℝ) 1 := mem_Ioo_of_mem_halfOpen hw hpos hα hirr
  have horb : ∀ k : ℕ, Erdos1002.gaussOrbit k α ∈ Ioo (0 : ℝ) 1 := by
    intro k
    rw [← MixingBV.gaussIter_eq_gaussOrbit]
    exact gaussIter_mem_Ioo hαIoo hirr k
  rw [MixingBV.mem_halfOpen_iff _ α horb] at hα ⊢
  intro i hi
  have hi' : i < w.length := by
    have := hi
    rw [List.length_take] at this
    omega
  rw [List.getElem_take]
  exact hα i hi'

/-- Mode tuples have coefficients bounded by `L^D` after zero-extension. -/
theorem abs_modeExt_le {r : ℕ} {D L : ℝ} (hL : 0 ≤ L ^ D) {v : Fin r → ℤ}
    (hv : v ∈ modeTuples r D L) :
    ∀ ℓ : ℕ, |((modeExt r v ℓ : ℤ) : ℝ)| ≤ L ^ D := by
  intro ℓ
  by_cases h : ℓ < r
  · rw [modeExt_lt r v ℓ h]
    have hmem : v ⟨ℓ, h⟩ ∈ modeBox D L := by
      rw [modeTuples, Fintype.mem_piFinset] at hv
      exact hv _
    rw [modeBox, Finset.mem_Icc] at hmem
    have h1 : |v ⟨ℓ, h⟩| ≤ (⌊L ^ D⌋₊ : ℤ) := by
      rw [abs_le]
      omega
    have h2 : ((⌊L ^ D⌋₊ : ℤ) : ℝ) ≤ L ^ D := by
      push_cast
      exact Nat.floor_le hL
    have h3 : |((v ⟨ℓ, h⟩ : ℤ) : ℝ)| ≤ ((⌊L ^ D⌋₊ : ℤ) : ℝ) := by
      exact_mod_cast h1
    exact le_trans h3 h2
  · have : modeExt r v ℓ = 0 := dif_neg h
    rw [this]
    simpa using hL

/-- The Gauss mean of a digit observable is bounded by the `ℓ¹` mass. -/
theorem norm_integral_digitObs_le (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) {ℓ : ℕ} (hℓ : ℓ < r) :
    ‖∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure‖ ≤ L ^ D := by
  have hae : ∀ᵐ x ∂Erdos1002.gaussMeasure, ‖Prop4Final.digitObs c ℓ x‖ ≤ L ^ D :=
    Eventually.of_forall (fun x => Prop4Final.norm_digitObs_le r D L F c hc ℓ hℓ x)
  have h := norm_integral_le_of_norm_le_const (μ := Erdos1002.gaussMeasure) hae
  simpa [measureReal_def] using h

/-- Sums of Lebesgue volumes of distinct positive same-length cylinders are
at most `1`. -/
theorem sum_vol_halfOpen_le_one (W : Finset (List ℕ)) (d : ℕ) (hd0 : 0 < d)
    (hW : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) :
    ∑ w ∈ W, (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal ≤ 1 := by
  classical
  have hdisj : (W : Set (List ℕ)).PairwiseDisjoint
      (fun w => Erdos1002.gaussHalfOpenPrefixCylinder w) := by
    intro x hx y hy hxy
    exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
      (by rw [(hW x hx).1, (hW y hy).1]) ((hW x hx).2) ((hW y hy).2) hxy
  have hmeas : ∀ w ∈ W, MeasurableSet (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hunion : ∑ w ∈ W, volume (Erdos1002.gaussHalfOpenPrefixCylinder w)
      = volume (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    (measure_biUnion_finset hdisj hmeas).symm
  have hsub : (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w) ⊆ Ioc (0 : ℝ) 1 := by
    refine Set.iUnion₂_subset (fun w hw => ?_)
    have hwne : w ≠ [] := by
      intro hnil
      have := (hW w hw).1
      rw [hnil] at this
      simp at this
      omega
    exact ZeroMode.halfOpenCylinder_subset_Ioc hwne (hW w hw).2
  have hle : volume (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w) ≤ 1 := by
    refine le_trans (measure_mono hsub) ?_
    rw [Real.volume_Ioc]
    simp
  have hfin : ∀ w ∈ W, volume (Erdos1002.gaussHalfOpenPrefixCylinder w) ≠ ⊤ := by
    intro w hw
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    exact le_trans (measure_mono (Set.subset_biUnion_of_mem hw)) hle
  calc ∑ w ∈ W, (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
      = (∑ w ∈ W, volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal :=
        (ENNReal.toReal_sum hfin).symm
    _ ≤ (1 : ℝ≥0∞).toReal := by
        refine ENNReal.toReal_mono ENNReal.one_ne_top ?_
        rw [hunion]
        exact hle
    _ = 1 := by simp

/-- Sums of Gauss measures of distinct positive same-length cylinders are
at most `1`. -/
theorem sum_gauss_halfOpen_le_one (W : Finset (List ℕ)) (d : ℕ)
    (hW : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) :
    ∑ w ∈ W,
        (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
      ≤ 1 := by
  classical
  have hdisj : (W : Set (List ℕ)).PairwiseDisjoint
      (fun w => Erdos1002.gaussHalfOpenPrefixCylinder w) := by
    intro x hx y hy hxy
    exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
      (by rw [(hW x hx).1, (hW y hy).1]) ((hW x hx).2) ((hW y hy).2) hxy
  have hmeas : ∀ w ∈ W, MeasurableSet (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hunion : ∑ w ∈ W, Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)
      = Erdos1002.gaussMeasure (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    (measure_biUnion_finset hdisj hmeas).symm
  have hle : Erdos1002.gaussMeasure (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)
      ≤ 1 := prob_le_one
  have hfin : ∀ w ∈ W,
      Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w) ≠ ⊤ :=
    fun w _ => measure_ne_top _ _
  calc ∑ w ∈ W,
        (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
      = (∑ w ∈ W,
          Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal :=
        (ENNReal.toReal_sum hfin).symm
    _ ≤ (1 : ℝ≥0∞).toReal := by
        refine ENNReal.toReal_mono ENNReal.one_ne_top ?_
        rw [hunion]
        exact hle
    _ = 1 := by simp

/-- Products over a finset of naturals can be enumerated by the order
embedding of its card. -/
theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] (s : Finset ℕ) (f : ℕ → M) :
    ∏ i : Fin s.card, f (s.orderEmbOfFin rfl i) = ∏ ℓ ∈ s, f ℓ := by
  classical
  refine Finset.prod_bij (fun i _ => s.orderEmbOfFin rfl i) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.orderEmbOfFin_mem s rfl i
  · intro i _ i' _ h
    exact (s.orderEmbOfFin rfl).injective h
  · intro ℓ hℓ
    have : ℓ ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hℓ
    obtain ⟨i, hi⟩ := this
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    rfl

set_option maxHeartbeats 1600000 in
/-- **The restoration mass.**  For the three-cut retained family, the part
of each depth-`k₋` fiber cylinder not covered by its retained depth-`k₊`
children has total Lebesgue mass at most the display-(20) bad mass at
depth `k₊`: an irrational point of the fiber that satisfies the Lévy
window at `k₊` lies in a retained child, by the saturation property of
the family. -/
theorem sum_discard_fiber_le (n js km kp : ℕ) {C₀ c₀ : ℝ}
    (hkm0 : 0 < km) (hjs_le_km : js ≤ km) (hkm_le_kp : km ≤ kp)
    (h20kp : volume.real {α ∈ Ioo (0 : ℝ) 1 |
        ¬ (Real.exp (lyapunov * (kp : ℝ) - (1/2 : ℝ) * Hscale n) ≤ (denom α kp : ℝ)
            ∧ (denom α kp : ℝ)
              ≤ Real.exp (lyapunov * (kp : ℝ) + (1/2 : ℝ) * Hscale n))}
      ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) :
    ∑ z ∈ (StationaryReplace.retainedWords n js km kp (1/2)).image
        (fun w => w.take km),
      (volume (Erdos1002.gaussHalfOpenPrefixCylinder z \
          ⋃ w ∈ (StationaryReplace.retainedWords n js km kp (1/2)).filter
            (fun w => w.take km = z),
            Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
      ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := by
  set W := StationaryReplace.retainedWords n js km kp (1/2) with hWdef
  set Z := W.image (fun w => w.take km) with hZdef
  have hkp0 : 0 < kp := by omega
  have hWshape : ∀ w ∈ W, w.length = kp ∧ ∀ a ∈ w, 0 < a :=
    StationaryReplace.retainedWords_shape
  have hWne : ∀ w ∈ W, w ≠ [] := by
    intro w hw hnil
    have := (hWshape w hw).1
    rw [hnil] at this
    simp at this
    omega
  have hZshape : ∀ z ∈ Z, z.length = km ∧ ∀ a ∈ z, 0 < a := by
    intro z hz
    rw [hZdef] at hz
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hz
    constructor
    · rw [List.length_take, (hWshape w₀ hw₀).1]
      omega
    · intro a ha
      exact (hWshape w₀ hw₀).2 a (List.mem_of_mem_take ha)
  have hZorig : ∀ z ∈ Z, ∃ w₀ ∈ W, z = w₀.take km := by
    intro z hz
    rw [hZdef] at hz
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨w₀, hw₀, rfl⟩
  have hZne : ∀ z ∈ Z, z ≠ [] := by
    intro z hz hnil
    have := (hZshape z hz).1
    rw [hnil] at this
    simp at this
    omega
  have hvolfin : ∀ z ∈ Z, volume (Erdos1002.gaussHalfOpenPrefixCylinder z) < ⊤ := by
    intro z hz
    refine lt_of_le_of_lt (measure_mono
      (ZeroMode.halfOpenCylinder_subset_Ioc (hZne z hz) (hZshape z hz).2)) ?_
    rw [Real.volume_Ioc]
    simp
  set Ez : List ℕ → Set ℝ := fun z =>
    Erdos1002.gaussHalfOpenPrefixCylinder z \
      ⋃ w ∈ W.filter (fun w => w.take km = z),
        Erdos1002.gaussHalfOpenPrefixCylinder w with hEzdef
  have hEmeas : ∀ z, MeasurableSet (Ez z) := by
    intro z
    rw [hEzdef]
    refine MeasurableSet.diff
      (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder z) ?_
    refine Finset.measurableSet_biUnion _ ?_
    intro w _
    exact Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hEdisj : (Z : Set (List ℕ)).PairwiseDisjoint Ez := by
    intro x hx y hy hxy
    have hx1 := Finset.mem_coe.mp hx
    have hy1 := Finset.mem_coe.mp hy
    refine Set.disjoint_of_subset ?_ ?_
      (Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
        (by rw [(hZshape x hx1).1, (hZshape y hy1).1])
        ((hZshape x hx1).2) ((hZshape y hy1).2) hxy)
    · rw [hEzdef]
      exact Set.diff_subset
    · rw [hEzdef]
      exact Set.diff_subset
  have hEfin : ∀ z ∈ Z, volume (Ez z) ≠ ⊤ := by
    intro z hz
    rw [hEzdef]
    exact ne_top_of_le_ne_top (hvolfin z hz).ne (measure_mono Set.diff_subset)
  have hEsum : ∑ z ∈ Z, volume (Ez z) = volume (⋃ z ∈ Z, Ez z) :=
    (measure_biUnion_finset hEdisj (fun z _ => hEmeas z)).symm
  set BadKP : Set ℝ := {α ∈ Ioo (0 : ℝ) 1 |
      ¬ (Real.exp (lyapunov * (kp : ℝ) - (1/2 : ℝ) * Hscale n) ≤ (denom α kp : ℝ)
          ∧ (denom α kp : ℝ)
            ≤ Real.exp (lyapunov * (kp : ℝ) + (1/2 : ℝ) * Hscale n))} with hBadKP
  have hnullq : volume {α : ℝ | ¬ Irrational α} = 0 := by
    have hset : {α : ℝ | ¬ Irrational α} = Set.range ((↑) : ℚ → ℝ) := by
      ext x
      simp [Irrational]
    rw [hset]
    exact (Set.countable_range _).measure_zero volume
  have hcover : (⋃ z ∈ Z, Ez z) ⊆ BadKP ∪ {α : ℝ | ¬ Irrational α} := by
    intro α hα
    obtain ⟨z, hzmem, hαE⟩ := Set.mem_iUnion₂.mp hα
    rw [hEzdef] at hαE
    obtain ⟨hαz, hαnu⟩ := hαE
    by_cases hirr : Irrational α
    · left
      have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
        mem_Ioo_of_mem_halfOpen (hZne z hzmem) (hZshape z hzmem).2 hαz hirr
      rw [hBadKP]
      refine ⟨hαIoo, fun hwin => ?_⟩
      obtain ⟨w₀, hw₀, hz_eq⟩ := hZorig z hzmem
      have hdenjs : (denom α js : ℝ) = (wordDenom (z.take js) : ℝ) :=
        StationaryReplace.denom_eq_wordDenom_take (hZshape z hzmem).1
          (hZshape z hzmem).2 hαz hirr hkm0 hjs_le_km
      have hdenkm : (denom α km : ℝ) = (wordDenom z : ℝ) := by
        have h1 := StationaryReplace.denom_eq_wordDenom_take
          (hZshape z hzmem).1 (hZshape z hzmem).2 hαz hirr hkm0 (le_refl km)
        rwa [List.take_of_length_le (le_of_eq (hZshape z hzmem).1)] at h1
      have htakejs : z.take js = w₀.take js := by
        rw [hz_eq, List.take_take]
        congr 1
        omega
      have hwin1 := (StationaryReplace.mem_retainedWords_iff.mp hw₀).2.1
      have hwin2 := (StationaryReplace.mem_retainedWords_iff.mp hw₀).2.2.1
      have hw1 : Real.exp (lyapunov * (js : ℝ) - 1/2 * Hscale n)
          ≤ (denom α js : ℝ)
          ∧ (denom α js : ℝ)
            ≤ Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n) := by
        rw [hdenjs, htakejs]
        exact hwin1
      have hw2 : (denom α km : ℝ)
          ≤ Real.exp (lyapunov * (km : ℝ) + 1/2 * Hscale n) := by
        rw [hdenkm, hz_eq]
        exact hwin2
      obtain ⟨hmemW, hmemcyl⟩ :=
        StationaryReplace.mem_retainedWords_of_window (n := n)
          hjs_le_km hkm_le_kp hαIoo hirr hw1 hw2 hwin
      have hztake : (digitWordOf α kp).take km = z := by
        rw [StationaryReplace.digitWordOf_take α hkm_le_kp]
        exact (eq_digitWordOf_of_digits (hZshape z hzmem).1
          (digit_eq_of_mem_halfOpen hαIoo hirr hαz)).symm
      exact hαnu (Set.mem_iUnion₂.mpr
        ⟨digitWordOf α kp, Finset.mem_filter.mpr ⟨hmemW, hztake⟩, hmemcyl⟩)
    · right
      exact hirr
  have hbadfin : volume BadKP ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    simp
  have hle1 : volume (⋃ z ∈ Z, Ez z) ≤ volume BadKP := by
    calc volume (⋃ z ∈ Z, Ez z)
        ≤ volume (BadKP ∪ {α : ℝ | ¬ Irrational α}) := measure_mono hcover
      _ ≤ volume BadKP + volume {α : ℝ | ¬ Irrational α} := measure_union_le _ _
      _ = volume BadKP := by rw [hnullq, add_zero]
  simp only [Measure.real] at h20kp
  calc ∑ z ∈ Z, (volume (Ez z)).toReal
      = (∑ z ∈ Z, volume (Ez z)).toReal := (ENNReal.toReal_sum hEfin).symm
    _ ≤ (volume BadKP).toReal := by
        refine ENNReal.toReal_mono hbadfin ?_
        rw [hEsum]
        exact hle1
    _ ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := h20kp

/-! ## 4. The master estimate

Everything below is at a fixed `n`, with the eventual facts supplied as
explicit hypotheses; the `∀ᶠ` wrapper is §5. -/

set_option maxHeartbeats 3200000 in
/-- **The nonzero-mode three-step chain, at fixed `n`.**  Produces the
`T₁, T₂` of `ZeroMode.nonzero_mode_three_step` with fully explicit
constants: `T₁` is the retained-cylinder truncation with frozen
frequencies, `T₂` is the stationary-mean replacement restored over the
depth-`k₋` cylinders. -/
theorem nonzero_mode_master (r : ℕ) (D : ℝ) (hD : 0 < D)
    (Cu ρu : ℝ) (hCu : 0 < Cu) (hρu0 : 0 < ρu) (hρu1 : ρu < 1)
    (C₀ c₀ : ℝ) (hC₀ : 0 < C₀) (hc₀0 : 0 < c₀) (n : ℕ)
    (huni : ∀ s, s ≤ r →
      ∀ (d M : ℕ) (w : List ℕ), w.length = d → (∀ a ∈ w, 0 < a) → 0 < d →
      ∀ Δ : ℝ,
      (∀ x ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
        ∀ y ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
          Irrational x → Irrational y → |x - y| ≤ Δ) →
      ∀ (t : ℕ → ℕ) (G : ℕ → ℝ → ℂ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → Measurable (G i)) →
        (∀ i, i < s → Prop41.BVBoundedBy K (fun x => (G i x).re)) →
        (∀ i, i < s → Prop41.BVBoundedBy K (fun x => (G i x).im)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        ‖(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              ∏ i ∈ Finset.range s, G i (gaussIter α (t i)))
            - ((volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal : ℂ)
                * ∏ i ∈ Finset.range s, ∫ x, G i x ∂Erdos1002.gaussMeasure‖
          ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
              * 2 ^ r * (2 * Real.log 2) * (Cu * ρu ^ M + Δ) * K ^ s)
    (h20n : ∀ jj : ℕ, jj ≤ 2 * mIndex n →
      volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (jj : ℝ) - (1/2 : ℝ) * Hscale n) ≤ (denom α jj : ℝ)
              ∧ (denom α jj : ℝ) ≤ Real.exp (lyapunov * (jj : ℝ) + (1/2 : ℝ) * Hscale n))}
        ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
    (h28n : ∀ α : ℝ, α ∈ Ioo (0 : ℝ) 1 → Irrational α →
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ vv : ℕ → ℤ, (∀ ℓ, |(vv ℓ : ℝ)| ≤ (Lnorm n) ^ D) →
      ∀ s : ℕ, s < r → vv s ≠ 0 →
        (denom α (j s) : ℝ) / 2 ≤ |((Prop41Canon.freqQ α j vv s : ℤ) : ℝ)| ∧
          |((Prop41Canon.freqQ α j vv s : ℤ) : ℝ)|
            ≤ 2 * (Lnorm n) ^ D * (denom α (j s) : ℝ))
    (hn1 : 1 ≤ n) (hL1 : 1 ≤ Lnorm n) (hH1 : 1 ≤ Hscale n)
    (hLD : (Lnorm n) ^ D ≤ Real.exp (Hscale n))
    (hm40 : 40 * Hscale n ≤ (mIndex n : ℝ)) :
    ∀ j : ℕ → ℕ, GoodTuple n r j →
    ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ, RepresentsPD r D (Lnorm n) F c →
    ∀ v ∈ modeTuples r D (Lnorm n), v ≠ 0 →
      ∃ T₁ T₂ : ℂ,
        ‖modeTerm n r j c v - T₁‖
          ≤ ((Lnorm n) ^ D) ^ r * (3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))) ∧
        ‖T₁ - T₂‖
          ≤ ((Lnorm n) ^ D) ^ r *
              ((8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2) * Real.exp (-Hscale n)
                + 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ ⌊100 * Hscale n⌋₊
                + C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) ∧
        ‖T₂‖ ≤ ((Lnorm n) ^ D) ^ r * (14 * Real.exp (-Hscale n)) := by
  classical
  intro j hj F c hc v hv hv0
  obtain ⟨sF, hvs, htopF⟩ := exists_top_mode_index hv0
  set s : ℕ := (sF : ℕ) with hs_def
  have hs : s < r := sF.isLt
  have htop : ∀ ℓ : Fin r, s < (ℓ : ℕ) → v ℓ = 0 :=
    fun ℓ h => htopF ℓ (Fin.lt_def.mpr h)
  set js : ℕ := j s with hjs_def
  have hbulk : js ∈ bulkJ n := hj.1.2.2 s hs
  obtain ⟨hmemr, h200, hjsm⟩ := Finset.mem_filter.mp hbulk
  -- numerical constants
  have hlyap : (0 : ℝ) < lyapunov := Prop42.lyapunov_pos
  have h80 := Prop42.eighty_lyapunov_bounds
  have hH0 : (0 : ℝ) ≤ Hscale n := le_trans zero_le_one hH1
  set HH : ℝ := Hscale n with hHH
  set LL : ℝ := Lnorm n with hLL
  set K : ℝ := (Lnorm n) ^ D with hKdef
  have hK1 : (1 : ℝ) ≤ K := Real.one_le_rpow hL1 hD.le
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  -- the two cut depths
  set km : ℕ := (Prop41.kMinus n js).toNat with hkm_def
  set kp : ℕ := (Prop41.kPlus n js).toNat with hkp_def
  have hkmZ : (0 : ℝ) < ((Prop41.kMinus n js : ℤ) : ℝ) := by
    have h1 := PhaseBounds.lt_kMinus_of_bulk hbulk
    nlinarith [h200, hH1]
  have hkm_cast : ((km : ℕ) : ℝ) = ((Prop41.kMinus n js : ℤ) : ℝ) := by
    rw [hkm_def]
    have h0 : (0 : ℤ) ≤ Prop41.kMinus n js := by exact_mod_cast hkmZ.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
  have hkpZ : (0 : ℝ) < ((Prop41.kPlus n js : ℤ) : ℝ) := by
    have h1 : Prop41.resonanceTime n js + 40 * Hscale n - 1
        < ((Prop41.kPlus n js : ℤ) : ℝ) := Int.sub_one_lt_floor _
    have h2 : (js : ℝ) ≤ Prop41.resonanceTime n js := by
      rw [Prop41.resonanceTime]
      have : (js : ℝ) ≤ (mIndex n : ℝ) := by linarith [hH0]
      linarith
    nlinarith [h200, hH1]
  have hkp_cast : ((kp : ℕ) : ℝ) = ((Prop41.kPlus n js : ℤ) : ℝ) := by
    rw [hkp_def]
    have h0 : (0 : ℤ) ≤ Prop41.kPlus n js := by exact_mod_cast hkpZ.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
  have hkm_ub : (km : ℝ) ≤ ((mIndex n : ℝ) + (js : ℝ)) / 2 - 40 * HH := by
    rw [hkm_cast]
    have := PhaseBounds.kMinus_le_sub n js
    rw [Prop41.resonanceTime] at this
    exact this
  have hkp_ub : (kp : ℝ) ≤ ((mIndex n : ℝ) + (js : ℝ)) / 2 + 40 * HH := by
    rw [hkp_cast]
    have := PhaseBounds.kPlus_le_add n js
    rw [Prop41.resonanceTime] at this
    exact this
  have hkp_lb : ((mIndex n : ℝ) + (js : ℝ)) / 2 + 40 * HH - 1 < (kp : ℝ) := by
    rw [hkp_cast]
    have h1 : Prop41.resonanceTime n js + 40 * Hscale n - 1
        < ((Prop41.kPlus n js : ℤ) : ℝ) := Int.sub_one_lt_floor _
    rw [Prop41.resonanceTime] at h1
    exact h1
  have hjs_km : js + 1 < km :=
    PhaseBounds.succ_lt_kMinus_toNat_of_bulk hbulk (by linarith)
  have hkm_kp : km < kp := by
    have hreal : (km : ℝ) < (kp : ℝ) := by
      nlinarith [hkm_ub, hkp_lb, hH1]
    exact_mod_cast hreal
  have hkp0 : 0 < kp := by omega
  have hkp_2m : kp ≤ 2 * mIndex n := by
    have hjm : (js : ℝ) ≤ (mIndex n : ℝ) := by linarith [hH0]
    have hreal : (kp : ℝ) ≤ ((2 * mIndex n : ℕ) : ℝ) := by
      push_cast
      nlinarith [hkp_ub, hm40]
    exact_mod_cast hreal
  have hlm_ub : lyapunov * (mIndex n : ℝ) ≤ LL := by
    have h1 : ((mIndex n : ℕ) : ℝ) ≤ LL / lyapunov := by
      rw [show mIndex n = ⌊Lnorm n / lyapunov⌋₊ from rfl]
      exact Nat.floor_le (by positivity)
    calc lyapunov * (mIndex n : ℝ) ≤ lyapunov * (LL / lyapunov) := by
          exact mul_le_mul_of_nonneg_left h1 hlyap.le
      _ = LL := by field_simp
  have hlm_lb : LL - lyapunov < lyapunov * (mIndex n : ℝ) := by
    have h1 : LL / lyapunov < (mIndex n : ℝ) + 1 := by
      rw [show mIndex n = ⌊Lnorm n / lyapunov⌋₊ from rfl]
      exact Nat.lt_floor_add_one _
    have h2 : lyapunov * (LL / lyapunov) = LL := by field_simp
    nlinarith [mul_lt_mul_of_pos_left h1 hlyap]
  have hnexp : ((n : ℕ) : ℝ) = Real.exp LL := by
    rw [hLL, show Lnorm n = Real.log (n : ℝ) from rfl, Real.exp_log]
    exact_mod_cast lt_of_lt_of_le zero_lt_one (by exact_mod_cast hn1)
  -- the retained family
  set W : Finset (List ℕ) := StationaryReplace.retainedWords n js km kp (1/2)
    with hWdef
  have hWshape : ∀ w ∈ W, w.length = kp ∧ ∀ a ∈ w, 0 < a :=
    StationaryReplace.retainedWords_shape
  have hjs_le_km : js ≤ km := by omega
  have hkm_le_kp : km ≤ kp := by omega
  have hmass : (volume (Ioo (0 : ℝ) 1 \
      ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) :=
    StationaryReplace.volume_discarded_retainedWords_le n h20n hjs_le_km
      hkm_le_kp hkp_2m
  -- frozen frequencies
  have hQex : ∀ u : List ℕ, u ≠ [] → (∀ a ∈ u, 0 < a) →
      (∀ ℓ, ℓ ≤ s → j ℓ ≤ u.length) → ∃ Q : ℤ,
      ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u, Irrational α →
        Prop41Canon.freqQ α j (modeExt r v) s = Q :=
    fun u h1 h2 h3 => exists_frozen_freqQ r v j s u h1 h2 h3
  set Qfz : List ℕ → ℤ := fun u =>
    if h : u ≠ [] ∧ (∀ a ∈ u, 0 < a) ∧ (∀ ℓ, ℓ ≤ s → j ℓ ≤ u.length) then
      Classical.choose (hQex u h.1 h.2.1 h.2.2)
    else 0 with hQfzdef
  have hQfz : ∀ (u : List ℕ) (h1 : u ≠ []) (h2 : ∀ a ∈ u, 0 < a)
      (h3 : ∀ ℓ, ℓ ≤ s → j ℓ ≤ u.length),
      ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u, Irrational α →
        Prop41Canon.freqQ α j (modeExt r v) s = Qfz u := by
    intro u h1 h2 h3 α hα hirr
    have heq : Qfz u = Classical.choose (hQex u h1 h2 h3) := by
      rw [hQfzdef]
      exact dif_pos ⟨h1, h2, h3⟩
    rw [heq]
    exact Classical.choose_spec (hQex u h1 h2 h3) α hα hirr
  -- monotonicity of the tuple
  have hjmono_le : ∀ a b : ℕ, a ≤ b → b < r → j a ≤ j b := by
    intro a b hab hbr
    rcases eq_or_lt_of_le hab with rfl | h
    · exact le_rfl
    · exact (hj.1.2.1 a b h hbr).le
  have hjle_js : ∀ ℓ : ℕ, ℓ ≤ s → j ℓ ≤ js := fun ℓ h => hjmono_le ℓ s h hs
  -- pre- and post-resonance factors
  set M : ℕ := ⌊100 * Hscale n⌋₊ with hM
  have hM_le : (M : ℝ) ≤ 100 * HH := by
    rw [hM, hHH]
    exact Nat.floor_le (by positivity)
  set Pre : Finset ℕ := (Finset.range r).filter (fun ℓ => j ℓ < km) with hPre
  set Fut : Finset ℕ := (Finset.range r).filter (fun ℓ => ¬ j ℓ < km) with hFutdef
  have hFut_gt_s : ∀ ℓ ∈ Fut, s < ℓ := by
    intro ℓ hℓ
    rw [hFutdef, Finset.mem_filter] at hℓ
    by_contra hle
    push_neg at hle
    have h1 : j ℓ ≤ js := hjle_js ℓ hle
    exact hℓ.2 (by omega)
  have hFut_far : ∀ ℓ ∈ Fut, kp + M ≤ j ℓ := by
    intro ℓ hℓ
    have hgt := hFut_gt_s ℓ hℓ
    rw [hFutdef, Finset.mem_filter, Finset.mem_range] at hℓ
    have hkmle : km ≤ j ℓ := by omega
    have hdich := Prop41.good_avoids_resonance_window n r j hj hH1 s ℓ hgt hℓ.1
    rcases hdich with hlow | hhigh
    · exfalso
      have h1 : (j ℓ : ℝ) < (km : ℝ) := by
        rw [hkm_cast]
        nlinarith [hH1]
      have : j ℓ < km := by exact_mod_cast h1
      omega
    · have h2 : ((kp + M : ℕ) : ℝ) ≤ (j ℓ : ℝ) := by
        push_cast
        rw [← hkp_cast] at hhigh
        nlinarith [hM_le]
      exact_mod_cast h2
  have hcards : Pre.card + Fut.card = r := by
    rw [hPre, hFutdef]
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
    exact Finset.card_range r
  have hFcard_le : Fut.card ≤ r := by omega
  -- the stationary product and the frozen amplitudes
  set P : ℂ := ∏ ℓ ∈ Fut, ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure
    with hPdef
  have hP_norm : ‖P‖ ≤ K ^ Fut.card := by
    rw [hPdef]
    calc ‖∏ ℓ ∈ Fut, ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure‖
        = ∏ ℓ ∈ Fut, ‖∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure‖ :=
          norm_prod _ _
      _ ≤ ∏ _ℓ ∈ Fut, K := by
          refine Finset.prod_le_prod (fun ℓ _ => norm_nonneg _) (fun ℓ hℓ => ?_)
          have hℓr : ℓ < r := by
            have := (Finset.mem_filter.mp (hFutdef ▸ hℓ)).1
            exact Finset.mem_range.mp this
          exact norm_integral_digitObs_le r D (Lnorm n) F c hc hℓr
      _ = K ^ Fut.card := by rw [Finset.prod_const]
  set Afn : List ℕ → ℂ :=
    fun u => ∏ ℓ ∈ Pre, c ℓ (u.getD (j ℓ) 1) (modeExt r v ℓ) with hAfn
  have hA_norm : ∀ u : List ℕ, ‖Afn u‖ ≤ K ^ Pre.card := by
    intro u
    rw [hAfn]
    calc ‖∏ ℓ ∈ Pre, c ℓ (u.getD (j ℓ) 1) (modeExt r v ℓ)‖
        = ∏ ℓ ∈ Pre, ‖c ℓ (u.getD (j ℓ) 1) (modeExt r v ℓ)‖ := norm_prod _ _
      _ ≤ ∏ _ℓ ∈ Pre, K := by
          refine Finset.prod_le_prod (fun ℓ _ => norm_nonneg _) (fun ℓ hℓ => ?_)
          have hℓr : ℓ < r := by
            have := (Finset.mem_filter.mp (hPre ▸ hℓ)).1
            exact Finset.mem_range.mp this
          exact Prop4Final.coeff_norm_le r D (Lnorm n) F c hc ℓ hℓr _ _
      _ = K ^ Pre.card := by rw [Finset.prod_const]
  have hKr_split : K ^ Pre.card * K ^ Fut.card = K ^ r := by
    rw [← pow_add, hcards]
  -- the second family and the two truncations
  set Z : Finset (List ℕ) := W.image (fun w => w.take km) with hZdef
  set osc : List ℕ → ℝ → ℂ :=
    fun u α => torusChar ((n : ℝ) * ((Qfz (u.take (js + 1)) : ℤ) : ℝ) * α)
    with hoscdef
  set T₁ : ℂ := ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
      (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) * osc w α with hT₁def
  set T₂ : ℂ := ∑ z ∈ Z, (Afn z * P) *
      ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z, osc z α with hT₂def
  -- basic facts about retained words
  have hWne : ∀ w ∈ W, w ≠ [] := by
    intro w hw hnil
    have := (hWshape w hw).1
    rw [hnil] at this
    simp at this
    omega
  have hWtake_pos : ∀ w ∈ W, ∀ m : ℕ, ∀ a ∈ w.take m, 0 < a := by
    intro w hw m a ha
    exact (hWshape w hw).2 a (List.mem_of_mem_take ha)
  have hWjd : ∀ w ∈ W, ∀ ℓ, ℓ ≤ s → j ℓ ≤ (w.take (js + 1)).length := by
    intro w hw ℓ hℓ
    have h1 : (w.take (js + 1)).length = js + 1 := by
      rw [List.length_take, (hWshape w hw).1]
      omega
    rw [h1]
    exact le_trans (hjle_js ℓ hℓ) (by omega)
  have hWtake_ne : ∀ w ∈ W, w.take (js + 1) ≠ [] := by
    intro w hw hnil
    have h1 : (w.take (js + 1)).length = js + 1 := by
      rw [List.length_take, (hWshape w hw).1]
      omega
    rw [hnil] at h1
    simp at h1
  -- the frozen frequency read on a full retained cylinder
  have hfreqW : ∀ w ∈ W, ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
      Irrational α →
      Prop41Canon.freqQ α j (modeExt r v) s = Qfz (w.take (js + 1)) := by
    intro w hw α hα hirr
    have hαu : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder (w.take (js + 1)) :=
      mem_halfOpen_take (hWne w hw) (hWshape w hw).2 hα hirr (js + 1)
    exact hQfz (w.take (js + 1)) (hWtake_ne w hw) (hWtake_pos w hw (js + 1))
      (hWjd w hw) α hαu hirr
  have hmode_bd' : ∀ ℓ : ℕ, |((modeExt r v ℓ : ℤ) : ℝ)| ≤ (Lnorm n) ^ D :=
    abs_modeExt_le (by positivity) hv
  have hmode_ne' : modeExt r v s ≠ 0 := by
    rw [hs_def, modeExt_lt r v (sF : ℕ) sF.isLt]
    simpa using hvs
  refine ⟨T₁, T₂, ?_, ?_, ?_⟩
  · -- STEP 1: the retained-cylinder cut
    have hcut := nonzero_mode_cut_of_retained n r D j F c hc v s hs htop W kp hkp0
      hWshape (3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))) hmass
    have hT₁eq : T₁ = ∑ w ∈ W,
        ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
          (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
            torusChar ((n : ℝ) *
              ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α) := by
      rw [hT₁def]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      refine integral_congr_ae ?_
      have hSm : MeasurableSet (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
        Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
      filter_upwards [ae_restrict_mem hSm,
        ae_restrict_of_ae (LargeDeviation.ae_irrational_volume)] with α h1 h2
      rw [hoscdef]
      rw [hfreqW w hw α h1 h2]
    rw [hT₁eq]
    exact hcut
  · -- STEP 2: stationary-mean replacement and restoration
    have hn0 : 0 < n := hn1
    -- the uniform diameter of the retained cylinders
    set Δ : ℝ := Real.exp (Hscale n - 2 * lyapunov * (kp : ℝ)) with hΔdef
    have hΔ0 : (0 : ℝ) < Δ := Real.exp_pos _
    have hΔle : Δ ≤ Real.exp (-Hscale n) := by
      rw [hΔdef]
      refine Real.exp_le_exp.mpr ?_
      have h1 : lyapunov * (mIndex n : ℝ) + lyapunov * (js : ℝ)
          + 80 * lyapunov * HH - 2 * lyapunov < 2 * lyapunov * (kp : ℝ) := by
        nlinarith [hkp_lb, hlyap]
      have h2 : (0 : ℝ) ≤ lyapunov * (mIndex n : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ lyapunov * (js : ℝ) := by positivity
      nlinarith [h80.1, h80.2, hH1]
    have hΔdiam : ∀ w ∈ W, ∀ x ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
        ∀ y ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
        Irrational x → Irrational y → |x - y| ≤ Δ := by
      intro w hw x hx y hy hix hiy
      have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
        mem_Ioo_of_mem_halfOpen (hWne w hw) (hWshape w hw).2 hx hix
      have hyIoo : y ∈ Ioo (0 : ℝ) 1 :=
        mem_Ioo_of_mem_halfOpen (hWne w hw) (hWshape w hw).2 hy hiy
      have hdig : ∀ i, i < kp → digit x i = digit y i := by
        intro i hi
        have hi' : i < w.length := by rw [(hWshape w hw).1]; exact hi
        rw [digit_eq_of_mem_halfOpen hxIoo hix hx i hi',
          digit_eq_of_mem_halfOpen hyIoo hiy hy i hi']
      have hqlow := ((StationaryReplace.retainedWords_windows hkp0 hjs_le_km
        hkm_le_kp w hw x hx hix).2.2).1
      have hprod := Kwon1002.abs_sub_mul_denom_sq_le_one hxIoo hyIoo hix hiy
        kp hdig
      have hq0 : (0 : ℝ) < Real.exp (lyapunov * (kp : ℝ) - 1/2 * Hscale n) :=
        Real.exp_pos _
      have hq1 : (0 : ℝ) < (denom x kp : ℝ) := lt_of_lt_of_le hq0 hqlow
      have hsq : Real.exp (lyapunov * (kp : ℝ) - 1/2 * Hscale n) ^ 2
          ≤ (denom x kp : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ hq0.le hqlow 2
      have hsqval : Real.exp (lyapunov * (kp : ℝ) - 1/2 * Hscale n) ^ 2
          = Real.exp (2 * lyapunov * (kp : ℝ) - Hscale n) := by
        rw [sq, ← Real.exp_add]
        ring_nf
      have hΔinv : Δ = (Real.exp (2 * lyapunov * (kp : ℝ) - Hscale n))⁻¹ := by
        rw [hΔdef, ← Real.exp_neg]
        congr 1
        ring
      calc |x - y| ≤ 1 / (denom x kp : ℝ) ^ 2 := by
            rw [le_div_iff₀ (by positivity)]
            exact hprod
        _ ≤ 1 / Real.exp (2 * lyapunov * (kp : ℝ) - Hscale n) := by
            refine one_div_le_one_div_of_le (by positivity) ?_
            rw [← hsqval]
            exact hsq
        _ = Δ := by rw [hΔinv, one_div]
    -- getD of a prefix
    have hgetD_take : ∀ (l : List ℕ) (m i : ℕ), i < m →
        (l.take m).getD i 1 = l.getD i 1 := by
      intro l m i him
      by_cases h : i < l.length
      · have h1 : i < (l.take m).length := by
          rw [List.length_take]
          omega
        rw [List.getD_eq_getElem l 1 h, List.getD_eq_getElem _ 1 h1,
          List.getElem_take]
      · push_neg at h
        have h1 : (l.take m).length ≤ i := by
          rw [List.length_take]
          omega
        rw [List.getD_eq_default l 1 (by omega), List.getD_eq_default _ 1 h1]
    -- the amplitude and phase are prefix-determined
    have hAfn_take : ∀ w ∈ W, Afn (w.take km) = Afn w := by
      intro w hw
      rw [hAfn]
      refine Finset.prod_congr rfl (fun ℓ hℓ => ?_)
      have hℓ2 := hℓ
      rw [hPre] at hℓ2
      have hℓkm : j ℓ < km := (Finset.mem_filter.mp hℓ2).2
      rw [hgetD_take w km (j ℓ) hℓkm]
    have hosc_take : ∀ w ∈ W, osc (w.take km) = osc w := by
      intro w hw
      funext α
      simp only [hoscdef]
      have htt : (w.take km).take (js + 1) = w.take (js + 1) := by
        rw [List.take_take]
        congr 1
        omega
      rw [htt]
    -- the future block data
    have he_mem : ∀ i : Fin Fut.card, (Fut.orderEmbOfFin rfl i : ℕ) ∈ Fut :=
      fun i => Finset.orderEmbOfFin_mem Fut rfl i
    have hFutsub : ∀ ℓ ∈ Fut, ℓ < r := by
      intro ℓ hℓ
      rw [hFutdef] at hℓ
      exact Finset.mem_range.mp (Finset.mem_filter.mp hℓ).1
    have he_lt_r : ∀ i : Fin Fut.card, (Fut.orderEmbOfFin rfl i : ℕ) < r :=
      fun i => hFutsub _ (he_mem i)
    set tt : ℕ → ℕ := fun i =>
      if h : i < Fut.card then j (Fut.orderEmbOfFin rfl ⟨i, h⟩) else kp + M + i
      with httdef
    set GG : ℕ → ℝ → ℂ := fun i =>
      if h : i < Fut.card then Prop4Final.digitObs c (Fut.orderEmbOfFin rfl ⟨i, h⟩)
      else fun _ => 1 with hGGdef
    have htt0 : kp + M ≤ tt 0 := by
      rw [httdef]
      by_cases h : 0 < Fut.card
      · simp only [dif_pos h]
        exact hFut_far _ (he_mem ⟨0, h⟩)
      · simp only [dif_neg h]
        omega
    have httgap : ∀ i, i + 1 < Fut.card → tt i + M ≤ tt (i + 1) := by
      intro i hi1
      have hi : i < Fut.card := by omega
      rw [httdef]
      simp only [dif_pos hi, dif_pos hi1]
      have hlt : (Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ)
          < (Fut.orderEmbOfFin rfl ⟨i + 1, hi1⟩ : ℕ) := by
        have h1 : (⟨i, hi⟩ : Fin Fut.card) < ⟨i + 1, hi1⟩ := by
          rw [Fin.mk_lt_mk]
          omega
        exact (Fut.orderEmbOfFin rfl).strictMono h1
      have ha1r : (Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) + 1 < r := by
        have := he_lt_r ⟨i + 1, hi1⟩
        omega
      have hgap := hj.2.1 (Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) ha1r
      have hmono := hjmono_le ((Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) + 1)
        (Fut.orderEmbOfFin rfl ⟨i + 1, hi1⟩ : ℕ) (by omega) (he_lt_r _)
      have hreal : ((j (Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) + M : ℕ) : ℝ)
          ≤ (j ((Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) + 1) : ℝ) := by
        push_cast
        nlinarith [hM_le, hgap, hH0]
      have h2 : j (Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) + M
          ≤ j ((Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) + 1) := by
        exact_mod_cast hreal
      omega
    have hGGmeas : ∀ i, i < Fut.card → Measurable (GG i) := by
      intro i hi
      rw [hGGdef]
      simp only [dif_pos hi]
      exact (measurable_from_top
        (f := fun a : ℕ => c (Fut.orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) a 0)).comp
        (Prop42.measurable_digitNat 0)
    have hGGre : ∀ i, i < Fut.card →
        Prop41.BVBoundedBy (2 * K) (fun x => ((GG i) x).re) := by
      intro i hi
      rw [hGGdef]
      simp only [dif_pos hi]
      exact Bridge.digitObs_re_bv r D (Lnorm n) (by positivity) F c hc _
        (he_lt_r ⟨i, hi⟩)
    have hGGim : ∀ i, i < Fut.card →
        Prop41.BVBoundedBy (2 * K) (fun x => ((GG i) x).im) := by
      intro i hi
      rw [hGGdef]
      simp only [dif_pos hi]
      exact Bridge.digitObs_im_bv r D (Lnorm n) (by positivity) F c hc _
        (he_lt_r ⟨i, hi⟩)
    -- the future product, in enumerated and set-indexed forms
    have hGGprod : ∀ α : ℝ,
        (∏ i ∈ Finset.range Fut.card, GG i (gaussIter α (tt i)))
          = ∏ ℓ ∈ Fut, Prop4Final.digitObs c ℓ (gaussIter α (j ℓ)) := by
      intro α
      rw [← Fin.prod_univ_eq_prod_range
        (fun i => GG i (gaussIter α (tt i))) Fut.card]
      rw [← prod_orderEmbOfFin Fut
        (fun ℓ => Prop4Final.digitObs c ℓ (gaussIter α (j ℓ)))]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [hGGdef, httdef, dif_pos i.isLt, Fin.eta]
    have hGGint : (∏ i ∈ Finset.range Fut.card,
          ∫ x, GG i x ∂Erdos1002.gaussMeasure) = P := by
      rw [hPdef]
      rw [← Fin.prod_univ_eq_prod_range
        (fun i => ∫ x, GG i x ∂Erdos1002.gaussMeasure) Fut.card]
      rw [← prod_orderEmbOfFin Fut
        (fun ℓ => ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure)]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [hGGdef, dif_pos i.isLt, Fin.eta]
    -- the per-cylinder replacement
    set T₂' : ℂ := ∑ w ∈ W, (Afn w * P) *
        ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, osc w α with hT₂'def
    have hosc_w : ∀ w : List ℕ, ∀ α : ℝ, osc w α
        = torusChar (((n : ℝ) * ((Qfz (w.take (js + 1)) : ℤ) : ℝ)) * α) := by
      intro w α
      rw [hoscdef]
    have hstep2w : ∀ w ∈ W,
        ‖(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) * osc w α)
            - (Afn w * P) *
              ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, osc w α‖
          ≤ K ^ r * (8 * Real.pi * Real.exp (-Hscale n)
                * (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
              + 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
                * (Erdos1002.gaussMeasure
                    (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal) := by
      intro w hw
      have hwne := hWne w hw
      have hwpos := (hWshape w hw).2
      have hwlen := (hWshape w hw).1
      obtain ⟨β, hβ, hβirr⟩ := exists_irrational_mem_halfOpen hwpos
      set S := Erdos1002.gaussHalfOpenPrefixCylinder w with hSdef
      have hSm : MeasurableSet S :=
        Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
      set KK : ℝ := (n : ℝ) * ((Qfz (w.take (js + 1)) : ℤ) : ℝ) with hKKdef
      set vw : ℝ := (volume S).toReal with hvwdef
      set mw : ℝ := (Erdos1002.gaussMeasure S).toReal with hmwdef
      have hvw0 : 0 ≤ vw := ENNReal.toReal_nonneg
      have hmw0 : 0 ≤ mw := ENNReal.toReal_nonneg
      set Gfut : ℝ → ℂ :=
        fun α => ∏ ℓ ∈ Fut, Prop4Final.digitObs c ℓ (gaussIter α (j ℓ)) with hGfutdef
      have hGfut_meas : Measurable Gfut := by
        rw [hGfutdef]
        refine Finset.measurable_prod _ (fun ℓ hℓ => ?_)
        exact ((measurable_from_top (f := fun a : ℕ => c ℓ a 0)).comp
          (Prop42.measurable_digitNat 0)).comp (measurable_gaussIter (j ℓ))
      have hGfut_bd : ∀ α : ℝ, ‖Gfut α‖ ≤ K ^ Fut.card := by
        intro α
        rw [hGfutdef]
        calc ‖∏ ℓ ∈ Fut, Prop4Final.digitObs c ℓ (gaussIter α (j ℓ))‖
            = ∏ ℓ ∈ Fut, ‖Prop4Final.digitObs c ℓ (gaussIter α (j ℓ))‖ :=
              norm_prod _ _
          _ ≤ ∏ _ℓ ∈ Fut, K := by
              refine Finset.prod_le_prod (fun ℓ _ => norm_nonneg _)
                (fun ℓ hℓ => ?_)
              exact Prop4Final.norm_digitObs_le r D (Lnorm n) F c hc ℓ
                (hFutsub ℓ hℓ) _
          _ = K ^ Fut.card := by rw [Finset.prod_const]
      have hosc_char : osc w = fun α => torusChar (KK * α) := by
        funext α
        exact hosc_w w α
      -- the amplitude splits a.e. on the cylinder
      have hsplitprod : ∀ f : ℕ → ℂ,
          ∏ ℓ ∈ Finset.range r, f ℓ = (∏ ℓ ∈ Pre, f ℓ) * ∏ ℓ ∈ Fut, f ℓ := by
        intro f
        rw [hPre, hFutdef]
        exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
      have hamp : ∀ᵐ α ∂(volume.restrict S),
          (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) = Afn w * Gfut α := by
        filter_upwards [ae_restrict_mem hSm,
          ae_restrict_of_ae (LargeDeviation.ae_irrational_volume)] with α hα hirr
        have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
          mem_Ioo_of_mem_halfOpen hwne hwpos hα hirr
        have h1 : (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ))
            = ∏ ℓ ∈ Finset.range r, c ℓ (digit α (j ℓ)) (modeExt r v ℓ) := by
          rw [← Fin.prod_univ_eq_prod_range
            (fun ℓ => c ℓ (digit α (j ℓ)) (modeExt r v ℓ)) r]
          exact Finset.prod_congr rfl (fun ℓ _ => by rw [modeExt_fin])
        rw [h1, hsplitprod (fun ℓ => c ℓ (digit α (j ℓ)) (modeExt r v ℓ))]
        congr 1
        · rw [hAfn]
          refine Finset.prod_congr rfl (fun ℓ hℓ => ?_)
          have hℓ2 := hℓ
          rw [hPre] at hℓ2
          have hℓkm : j ℓ < km := (Finset.mem_filter.mp hℓ2).2
          have hℓlen : j ℓ < w.length := by
            rw [hwlen]
            omega
          rw [digit_eq_of_mem_halfOpen hαIoo hirr hα (j ℓ) hℓlen,
            List.getD_eq_getElem w 1 hℓlen]
        · rw [hGfutdef]
          refine Finset.prod_congr rfl (fun ℓ hℓ => ?_)
          have hgt := hFut_gt_s ℓ hℓ
          have hℓr := hFutsub ℓ hℓ
          have hzero : modeExt r v ℓ = 0 := by
            rw [modeExt_lt r v ℓ hℓr]
            exact htop ⟨ℓ, hℓr⟩ hgt
          rw [hzero]
          show c ℓ (digit α (j ℓ)) 0
            = c ℓ (digit (gaussIter α (j ℓ)) 0) 0
          rw [PhaseBounds.digit_gaussIter α (j ℓ) 0, Nat.add_zero]
      -- the integral against the frozen phase
      have hIeq : (∫ α in S,
            (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) * osc w α)
          = Afn w * ∫ α in S, Gfut α * osc w α := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hamp] with α hα
        rw [hα]
        ring
      -- phase freeze for the future product
      have hβS : β ∈ S := hβ
      have hΔS : ∀ α ∈ S, Irrational α → |α - β| ≤ Δ :=
        fun α hα hirr => hΔdiam w hw α hα β hβS hirr hβirr
      have hph1 := phase_freeze_on_cylinder hwne hwpos Gfut hGfut_meas
        (K ^ Fut.card) (by positivity) (fun α hα hirr => hGfut_bd α) KK hβS hβirr
        Δ hΔS
      rw [← hSdef] at hph1
      rw [← hvwdef] at hph1
      -- phase freeze for the constant `1`
      have hph2 := phase_freeze_on_cylinder hwne hwpos (fun _ => (1 : ℂ))
        measurable_const 1 zero_le_one (fun α _ _ => by simp) KK hβS hβirr Δ hΔS
      rw [← hSdef] at hph2
      rw [← hvwdef] at hph2
      have hone : (∫ α in S, (1 : ℂ) * torusChar (KK * α))
          = ∫ α in S, torusChar (KK * α) := by
        refine integral_congr_ae (Eventually.of_forall (fun α => ?_))
        simp only [one_mul]
      have hcv : (∫ _α in S, (1 : ℂ)) = ((vw : ℝ) : ℂ) := by
        rw [setIntegral_const, hvwdef]
        simp [measureReal_def, Complex.real_smul]
      rw [hone, hcv] at hph2
      simp only [mul_one] at hph2
      -- the mixing estimate, in set-indexed form
      have hmixw := huni Fut.card hFcard_le kp M w hwlen hwpos hkp0 Δ
        (hΔdiam w hw) tt GG (2 * K) (by positivity) hGGmeas hGGre hGGim
        htt0 httgap
      rw [← hSdef] at hmixw
      rw [← hvwdef, ← hmwdef] at hmixw
      have hmix_int : (∫ α in S,
            ∏ i ∈ Finset.range Fut.card, GG i (gaussIter α (tt i)))
          = ∫ α in S, Gfut α := by
        refine integral_congr_ae (Eventually.of_forall (fun α => ?_))
        simp only [hGfutdef]
        exact hGGprod α
      rw [hmix_int, hGGint] at hmixw
      -- the frequency bound
      have hQub : |((Qfz (w.take (js + 1)) : ℤ) : ℝ)|
          ≤ 2 * K * Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n) := by
        have h28 := (h28n β (mem_Ioo_of_mem_halfOpen hwne hwpos hβS hβirr) hβirr
          j hj (modeExt r v) hmode_bd' s hs hmode_ne').2
        rw [hfreqW w hw β hβS hβirr] at h28
        refine le_trans h28 ?_
        have hden : (denom β js : ℝ) = (wordDenom (w.take js) : ℝ) := by
          have := StationaryReplace.denom_eq_wordDenom_take hwlen hwpos hβS hβirr
            hkp0 (le_trans hjs_le_km hkm_le_kp)
          rw [hjs_def]
          exact this
        have hup := (StationaryReplace.mem_retainedWords_iff.mp hw).2.1.2
        rw [hjs_def] at hden
        rw [hden]
        have hK2 : (0 : ℝ) ≤ 2 * K := by positivity
        calc 2 * (Lnorm n) ^ D * (wordDenom (w.take js) : ℝ)
            ≤ 2 * (Lnorm n) ^ D
                * Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact hup
          _ = 2 * K * Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n) := by
              rw [hKdef]
      have hKKΔ : |KK| * Δ ≤ 2 * Real.exp (-Hscale n) := by
        rw [hKKdef, abs_mul, Nat.abs_cast, hΔdef]
        have h1 : (n : ℝ) * |((Qfz (w.take (js + 1)) : ℤ) : ℝ)|
            ≤ Real.exp LL * (2 * K * Real.exp (lyapunov * (js : ℝ)
                + 1/2 * Hscale n)) := by
          rw [← hnexp]
          exact mul_le_mul_of_nonneg_left hQub (Nat.cast_nonneg n)
        calc (n : ℝ) * |((Qfz (w.take (js + 1)) : ℤ) : ℝ)|
              * Real.exp (Hscale n - 2 * lyapunov * (kp : ℝ))
            ≤ Real.exp LL * (2 * K * Real.exp (lyapunov * (js : ℝ)
                + 1/2 * Hscale n))
              * Real.exp (Hscale n - 2 * lyapunov * (kp : ℝ)) := by
              exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = 2 * K * Real.exp (LL + lyapunov * (js : ℝ) + 3/2 * Hscale n
                - 2 * lyapunov * (kp : ℝ)) := by
              have hee : Real.exp LL
                    * Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n)
                    * Real.exp (Hscale n - 2 * lyapunov * (kp : ℝ))
                  = Real.exp (LL + lyapunov * (js : ℝ) + 3/2 * Hscale n
                      - 2 * lyapunov * (kp : ℝ)) := by
                rw [← Real.exp_add, ← Real.exp_add]
                congr 1
                ring
              calc Real.exp LL * (2 * K * Real.exp (lyapunov * (js : ℝ)
                    + 1/2 * Hscale n))
                  * Real.exp (Hscale n - 2 * lyapunov * (kp : ℝ))
                  = 2 * K * (Real.exp LL
                    * Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n)
                    * Real.exp (Hscale n - 2 * lyapunov * (kp : ℝ))) := by ring
                _ = 2 * K * Real.exp (LL + lyapunov * (js : ℝ) + 3/2 * Hscale n
                    - 2 * lyapunov * (kp : ℝ)) := by rw [hee]
          _ ≤ 2 * Real.exp (Hscale n) * Real.exp (LL + lyapunov * (js : ℝ)
                + 3/2 * Hscale n - 2 * lyapunov * (kp : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              rw [hKdef]
              nlinarith [hLD]
          _ = 2 * Real.exp (LL + lyapunov * (js : ℝ) + 5/2 * Hscale n
                - 2 * lyapunov * (kp : ℝ)) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 1
              ring
          _ ≤ 2 * Real.exp (-Hscale n) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              refine Real.exp_le_exp.mpr ?_
              have h2 : lyapunov * (mIndex n : ℝ) + lyapunov * (js : ℝ)
                  + 80 * lyapunov * HH - 2 * lyapunov
                  < 2 * lyapunov * (kp : ℝ) := by
                nlinarith [hkp_lb, hlyap]
              have h3 : LL < lyapunov * (mIndex n : ℝ) + lyapunov := by
                linarith [hlm_lb]
              nlinarith [h80.1, h80.2, hH1, hlyap]
      -- assemble the per-cylinder estimate
      rw [hIeq]
      have hdecomp : Afn w * (∫ α in S, Gfut α * osc w α)
            - (Afn w * P) * ∫ α in S, osc w α
          = Afn w * (((∫ α in S, Gfut α * osc w α)
              - torusChar (KK * β) * ∫ α in S, Gfut α)
            + torusChar (KK * β) * ((∫ α in S, Gfut α) - ((vw : ℝ) : ℂ) * P)
            + (torusChar (KK * β) * ((vw : ℝ) : ℂ)
                - ∫ α in S, osc w α) * P) := by
        ring
      rw [hdecomp, norm_mul]
      have hoscint : (∫ α in S, Gfut α * osc w α)
          = ∫ α in S, Gfut α * torusChar (KK * α) := by
        rw [hosc_char]
      have hoscint2 : (∫ α in S, osc w α) = ∫ α in S, torusChar (KK * α) := by
        rw [hosc_char]
      have e1 : ‖(∫ α in S, Gfut α * osc w α)
            - torusChar (KK * β) * ∫ α in S, Gfut α‖
          ≤ 2 * Real.pi * |KK| * Δ * K ^ Fut.card * vw := by
        rw [hoscint]
        exact hph1
      have e2 : ‖torusChar (KK * β) * ((∫ α in S, Gfut α) - ((vw : ℝ) : ℂ) * P)‖
          ≤ mw * 2 ^ r * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
              * (2 * K) ^ Fut.card := by
        rw [norm_mul, Prop42.norm_torusChar, one_mul]
        exact hmixw
      have e3 : ‖(torusChar (KK * β) * ((vw : ℝ) : ℂ)
            - ∫ α in S, osc w α) * P‖
          ≤ (2 * Real.pi * |KK| * Δ * vw) * K ^ Fut.card := by
        rw [norm_mul]
        have h1 : ‖torusChar (KK * β) * ((vw : ℝ) : ℂ) - ∫ α in S, osc w α‖
            ≤ 2 * Real.pi * |KK| * Δ * vw := by
          rw [hoscint2, norm_sub_rev]
          exact hph2
        exact mul_le_mul h1 hP_norm (norm_nonneg _) (by positivity)
      have htri : ‖((∫ α in S, Gfut α * osc w α)
              - torusChar (KK * β) * ∫ α in S, Gfut α)
            + torusChar (KK * β) * ((∫ α in S, Gfut α) - ((vw : ℝ) : ℂ) * P)
            + (torusChar (KK * β) * ((vw : ℝ) : ℂ)
                - ∫ α in S, osc w α) * P‖
          ≤ 2 * Real.pi * |KK| * Δ * K ^ Fut.card * vw
            + mw * 2 ^ r * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
              * (2 * K) ^ Fut.card
            + (2 * Real.pi * |KK| * Δ * vw) * K ^ Fut.card := by
        refine le_trans (norm_add_le _ _) ?_
        refine add_le_add (le_trans (norm_add_le _ _) (add_le_add e1 e2)) e3
      refine le_trans (mul_le_mul_of_nonneg_left htri (norm_nonneg (Afn w))) ?_
      -- fold the amplitude bound and the `|KK|Δ` estimate
      have hAle := hA_norm w
      have hA0 : (0 : ℝ) ≤ ‖Afn w‖ := norm_nonneg _
      have hKf0 : (0 : ℝ) ≤ K ^ Fut.card := by positivity
      have hπ0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have hKKΔ0 : (0 : ℝ) ≤ |KK| * Δ := mul_nonneg (abs_nonneg _) hΔ0.le
      have hbr0 : (0 : ℝ) ≤ Cu * ρu ^ M + Δ := by positivity
      have hterm1 : ‖Afn w‖ * (2 * Real.pi * |KK| * Δ * K ^ Fut.card * vw
            + (2 * Real.pi * |KK| * Δ * vw) * K ^ Fut.card)
          ≤ K ^ r * (8 * Real.pi * Real.exp (-Hscale n) * vw) := by
        have h1 : 2 * Real.pi * |KK| * Δ * K ^ Fut.card * vw
              + (2 * Real.pi * |KK| * Δ * vw) * K ^ Fut.card
            = (2 * Real.pi) * (|KK| * Δ) * (2 * (K ^ Fut.card * vw)) := by
          ring
        have h2 : (2 * Real.pi) * (|KK| * Δ) * (2 * (K ^ Fut.card * vw))
            ≤ (2 * Real.pi) * (2 * Real.exp (-Hscale n))
              * (2 * (K ^ Fut.card * vw)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKKΔ hπ0) ?_
          positivity
        calc ‖Afn w‖ * (2 * Real.pi * |KK| * Δ * K ^ Fut.card * vw
              + (2 * Real.pi * |KK| * Δ * vw) * K ^ Fut.card)
            ≤ K ^ Pre.card * ((2 * Real.pi) * (2 * Real.exp (-Hscale n))
              * (2 * (K ^ Fut.card * vw))) := by
              rw [h1]
              refine mul_le_mul hAle (le_trans h2 le_rfl) ?_ (by positivity)
              have := mul_nonneg (mul_nonneg hπ0 hKKΔ0)
                (by positivity : (0:ℝ) ≤ 2 * (K ^ Fut.card * vw))
              linarith [this]
          _ = K ^ Pre.card * K ^ Fut.card
                * (8 * Real.pi * Real.exp (-Hscale n) * vw) := by
              ring
          _ = K ^ r * (8 * Real.pi * Real.exp (-Hscale n) * vw) := by
              rw [hKr_split]
      have hterm2 : ‖Afn w‖ * (mw * 2 ^ r * (2 * Real.log 2)
            * (Cu * ρu ^ M + Δ) * (2 * K) ^ Fut.card)
          ≤ K ^ r * (2 ^ (2 * r) * (2 * Real.log 2)
              * (Cu * ρu ^ M + Δ) * mw) := by
        have h2K : (2 * K) ^ Fut.card = 2 ^ Fut.card * K ^ Fut.card :=
          mul_pow 2 K Fut.card
        have h2r : (2 : ℝ) ^ Fut.card ≤ 2 ^ r :=
          pow_le_pow_right₀ (by norm_num) hFcard_le
        calc ‖Afn w‖ * (mw * 2 ^ r * (2 * Real.log 2)
              * (Cu * ρu ^ M + Δ) * (2 * K) ^ Fut.card)
            ≤ K ^ Pre.card * (mw * 2 ^ r * (2 * Real.log 2)
              * (Cu * ρu ^ M + Δ) * (2 * K) ^ Fut.card) := by
              refine mul_le_mul_of_nonneg_right hAle ?_
              have : (0:ℝ) ≤ (2*K) ^ Fut.card := by positivity
              positivity
          _ = K ^ Pre.card * K ^ Fut.card * ((2:ℝ) ^ Fut.card
                * (mw * 2 ^ r * (2 * Real.log 2) * (Cu * ρu ^ M + Δ))) := by
              rw [h2K]
              ring
          _ ≤ K ^ Pre.card * K ^ Fut.card * ((2:ℝ) ^ r
                * (mw * 2 ^ r * (2 * Real.log 2) * (Cu * ρu ^ M + Δ))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              refine mul_le_mul_of_nonneg_right h2r ?_
              positivity
          _ = K ^ r * (2 ^ (2 * r) * (2 * Real.log 2)
                * (Cu * ρu ^ M + Δ) * mw) := by
              rw [hKr_split]
              ring
      calc ‖Afn w‖ * (2 * Real.pi * |KK| * Δ * K ^ Fut.card * vw
            + mw * 2 ^ r * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
              * (2 * K) ^ Fut.card
            + (2 * Real.pi * |KK| * Δ * vw) * K ^ Fut.card)
          = ‖Afn w‖ * (2 * Real.pi * |KK| * Δ * K ^ Fut.card * vw
              + (2 * Real.pi * |KK| * Δ * vw) * K ^ Fut.card)
            + ‖Afn w‖ * (mw * 2 ^ r * (2 * Real.log 2)
              * (Cu * ρu ^ M + Δ) * (2 * K) ^ Fut.card) := by
            ring
        _ ≤ K ^ r * (8 * Real.pi * Real.exp (-Hscale n) * vw)
            + K ^ r * (2 ^ (2 * r) * (2 * Real.log 2)
              * (Cu * ρu ^ M + Δ) * mw) := add_le_add hterm1 hterm2
        _ = K ^ r * (8 * Real.pi * Real.exp (-Hscale n) * vw
            + 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ) * mw) := by
            ring
    -- summation over the retained family
    have hT₁T₂' : ‖T₁ - T₂'‖
        ≤ K ^ r * ((8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2)
              * Real.exp (-Hscale n)
            + 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ M) := by
      have hsub : T₁ - T₂' = ∑ w ∈ W,
          ((∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) * osc w α)
            - (Afn w * P) *
              ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, osc w α) := by
        rw [hT₁def, hT₂'def, ← Finset.sum_sub_distrib]
      rw [hsub]
      have hsumvol := sum_vol_halfOpen_le_one W kp hkp0 hWshape
      have hsumm := sum_gauss_halfOpen_le_one W kp hWshape
      have hb0 : (0 : ℝ) ≤ 8 * Real.pi * Real.exp (-Hscale n) := by positivity
      have hc0' : (0 : ℝ) ≤ 2 ^ (2 * r) * (2 * Real.log 2)
          * (Cu * ρu ^ M + Δ) := by positivity
      calc ‖∑ w ∈ W,
            ((∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
                (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) * osc w α)
              - (Afn w * P) *
                ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, osc w α)‖
          ≤ ∑ w ∈ W,
            ‖(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
                (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) * osc w α)
              - (Afn w * P) *
                ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, osc w α‖ :=
            norm_sum_le _ _
        _ ≤ ∑ w ∈ W, (K ^ r * (8 * Real.pi * Real.exp (-Hscale n)
              * (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
            + 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
              * (Erdos1002.gaussMeasure
                  (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal)) :=
            Finset.sum_le_sum hstep2w
        _ = K ^ r * (8 * Real.pi * Real.exp (-Hscale n)
              * ∑ w ∈ W, (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
            + 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
              * ∑ w ∈ W, (Erdos1002.gaussMeasure
                  (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal) := by
            have hstep : ∀ w ∈ W, K ^ r * (8 * Real.pi * Real.exp (-Hscale n)
                  * (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
                + 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
                  * (Erdos1002.gaussMeasure
                      (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal)
                = K ^ r * (8 * Real.pi * Real.exp (-Hscale n))
                  * (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
                + K ^ r * (2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ))
                  * (Erdos1002.gaussMeasure
                      (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
              intro w _
              ring
            rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]
            ring
        _ ≤ K ^ r * (8 * Real.pi * Real.exp (-Hscale n) * 1
            + 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ) * 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact add_le_add (mul_le_mul_of_nonneg_left hsumvol hb0)
              (mul_le_mul_of_nonneg_left hsumm hc0')
        _ ≤ K ^ r * ((8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2)
              * Real.exp (-Hscale n)
            + 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ M) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hδ1 : 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M + Δ)
                ≤ 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M)
                  + 2 ^ (2 * r) * (2 * Real.log 2) * Real.exp (-Hscale n) := by
              have h1 : (0 : ℝ) ≤ 2 ^ (2 * r) * (2 * Real.log 2) := by positivity
              nlinarith [hΔle]
            have heq1 : 2 ^ (2 * r) * (2 * Real.log 2) * (Cu * ρu ^ M)
                = 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ M := by
              rw [pow_succ]
              ring
            have heq2 : 2 ^ (2 * r) * (2 * Real.log 2)
                = 2 ^ (2 * r + 1) * Real.log 2 := by
              rw [pow_succ]
              ring
            nlinarith [hδ1]
    -- the restoration of the discarded depth-`k₊` cylinders
    have hT₂'T₂ : ‖T₂' - T₂‖
        ≤ K ^ r * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
      -- shapes of the depth-`k₋` family (the kill branch is a separate goal)
      have hZshape : ∀ z ∈ Z, z.length = km ∧ ∀ a ∈ z, 0 < a := by
        intro z hz
        rw [hZdef] at hz
        obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hz
        constructor
        · rw [List.length_take, (hWshape w₀ hw₀).1]
          omega
        · intro a ha
          exact (hWshape w₀ hw₀).2 a (List.mem_of_mem_take ha)
      have hZorig : ∀ z ∈ Z, ∃ w₀ ∈ W, z = w₀.take km := by
        intro z hz
        rw [hZdef] at hz
        obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨w₀, hw₀, rfl⟩
      have hkm0 : 0 < km := by omega
      have hZne : ∀ z ∈ Z, z ≠ [] := by
        intro z hz hnil
        have := (hZshape z hz).1
        rw [hnil] at this
        simp at this
        omega
      have hoscm : ∀ u : List ℕ, Measurable (osc u) := by
        intro u
        have hosc' : osc u = fun α =>
            torusChar ((n : ℝ) * ((Qfz (u.take (js + 1)) : ℤ) : ℝ) * α) :=
          funext (hosc_w u)
        rw [hosc']
        exact ZeroMode.continuous_torusChar.measurable.comp
          ((measurable_const.mul measurable_const).mul measurable_id)
      have hoscb : ∀ (u : List ℕ) (α : ℝ), ‖osc u α‖ = 1 := by
        intro u α
        rw [hosc_w u α, Prop42.norm_torusChar]
      have hvolfin : ∀ z ∈ Z,
          volume (Erdos1002.gaussHalfOpenPrefixCylinder z) < ⊤ := by
        intro z hz
        refine lt_of_le_of_lt (measure_mono
          (ZeroMode.halfOpenCylinder_subset_Ioc (hZne z hz) (hZshape z hz).2)) ?_
        rw [Real.volume_Ioc]
        simp
      -- fiber regrouping of `T₂'`
      have hmaps : ∀ w ∈ W, w.take km ∈ Z := by
        intro w hw
        rw [hZdef]
        exact Finset.mem_image_of_mem _ hw
      have hT₂'fib : T₂' = ∑ z ∈ Z,
          ∑ w ∈ W.filter (fun w => w.take km = z),
            (Afn z * P) * ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              osc z α := by
        rw [hT₂'def, ← Finset.sum_fiberwise_of_maps_to hmaps
          (fun w => (Afn w * P) *
            ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, osc w α)]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [Finset.mem_filter] at hw
        rw [← hw.2, hAfn_take w hw.1, hosc_take w hw.1]
      -- the per-`z` remainder
      have hint_split : ∀ z ∈ Z,
          (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z, osc z α)
            = (∑ w ∈ W.filter (fun w => w.take km = z),
                ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, osc z α)
              + ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z \
                  ⋃ w ∈ W.filter (fun w => w.take km = z),
                    Erdos1002.gaussHalfOpenPrefixCylinder w, osc z α := by
        intro z hz
        set Wz := W.filter (fun w => w.take km = z) with hWzdef
        set Uz : Set ℝ := ⋃ w ∈ Wz, Erdos1002.gaussHalfOpenPrefixCylinder w
          with hUzdef
        have hmUz : MeasurableSet Uz :=
          Wz.measurableSet_biUnion
            (fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w)
        have hintOn : ∀ (T : Set ℝ), MeasurableSet T →
            T ⊆ Erdos1002.gaussHalfOpenPrefixCylinder z →
            IntegrableOn (osc z) T volume := by
          intro T hT hTsub
          have hTfin : volume T < ⊤ :=
            lt_of_le_of_lt (measure_mono hTsub) (hvolfin z hz)
          haveI : IsFiniteMeasure (volume.restrict T) :=
            ⟨by rwa [Measure.restrict_apply_univ]⟩
          refine Integrable.of_bound (C := 1) ((hoscm z).aestronglyMeasurable) ?_
          exact Eventually.of_forall (fun α => le_of_eq (hoscb z α))
        have hsplit := integral_inter_add_diff (μ := volume)
          (s := Erdos1002.gaussHalfOpenPrefixCylinder z) (t := Uz)
          (f := osc z) hmUz (hintOn _
            (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder z)
            (subset_refl _))
        have hinter : (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z ∩ Uz,
              osc z α)
            = ∑ w ∈ Wz, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
                osc z α := by
          have hIU : Erdos1002.gaussHalfOpenPrefixCylinder z ∩ Uz
              = ⋃ w ∈ Wz, (Erdos1002.gaussHalfOpenPrefixCylinder z
                  ∩ Erdos1002.gaussHalfOpenPrefixCylinder w) := by
            rw [hUzdef, Set.inter_iUnion₂]
          have hdisj : (Wz : Set (List ℕ)).PairwiseDisjoint
              (fun w => Erdos1002.gaussHalfOpenPrefixCylinder z
                ∩ Erdos1002.gaussHalfOpenPrefixCylinder w) := by
            intro x hx y hy hxy
            have hx1 := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
            have hy1 := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
            refine Set.disjoint_of_subset Set.inter_subset_right
              Set.inter_subset_right ?_
            exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
              (by rw [(hWshape x hx1.1).1, (hWshape y hy1.1).1])
              ((hWshape x hx1.1).2) ((hWshape y hy1.1).2) hxy
          rw [hIU, integral_biUnion_finset Wz
            (fun w _ => (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder z).inter
              (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w))
            hdisj
            (fun w hw => hintOn _
              ((Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder z).inter
                (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w))
              Set.inter_subset_left)]
          refine Finset.sum_congr rfl (fun w hw => ?_)
          refine setIntegral_congr_set ?_
          have hw1 := Finset.mem_filter.mp hw
          refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
          · rw [Set.diff_eq_empty.mpr Set.inter_subset_right]
            exact measure_empty
          · refine measure_mono_null (fun α hα => ?_)
              ((Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume)
            obtain ⟨hαw, hαni⟩ := hα
            by_cases hirr : Irrational α
            · exfalso
              have hαz : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder z := by
                rw [← hw1.2]
                exact mem_halfOpen_take (hWne w hw1.1) (hWshape w hw1.1).2
                  hαw hirr km
              exact hαni ⟨hαz, hαw⟩
            · simpa [Irrational] using hirr
        rw [← hsplit, hinter]
      -- the difference is carried by the discarded sets
      have hdiff : T₂' - T₂ = -∑ z ∈ Z, (Afn z * P) *
          ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z \
              ⋃ w ∈ W.filter (fun w => w.take km = z),
                Erdos1002.gaussHalfOpenPrefixCylinder w, osc z α := by
        rw [hT₂'fib, hT₂def, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [hint_split z hz, ← Finset.mul_sum]
        ring
      rw [hdiff, norm_neg]
      -- bound each remainder by the Lebesgue mass of the discarded set
      have hAPz : ∀ z : List ℕ, ‖Afn z * P‖ ≤ K ^ r := by
        intro z
        rw [norm_mul, ← hKr_split]
        exact mul_le_mul (hA_norm _) hP_norm (norm_nonneg _)
          (pow_nonneg hK0.le _)
      have hEbound : ∀ z ∈ Z,
          ‖(Afn z * P) * ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z \
              ⋃ w ∈ W.filter (fun w => w.take km = z),
                Erdos1002.gaussHalfOpenPrefixCylinder w, osc z α‖
            ≤ K ^ r * (volume (Erdos1002.gaussHalfOpenPrefixCylinder z \
                ⋃ w ∈ W.filter (fun w => w.take km = z),
                  Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
        intro z hz
        rw [norm_mul]
        have hfin : volume (Erdos1002.gaussHalfOpenPrefixCylinder z \
            ⋃ w ∈ W.filter (fun w => w.take km = z),
              Erdos1002.gaussHalfOpenPrefixCylinder w) < ⊤ := by
          refine lt_of_le_of_lt (measure_mono Set.diff_subset) ?_
          refine lt_of_le_of_lt (measure_mono
            (ZeroMode.halfOpenCylinder_subset_Ioc (hZne z hz)
              (hZshape z hz).2)) ?_
          rw [Real.volume_Ioc]
          simp
        have hIb := norm_setIntegral_le_of_norm_le_const (μ := volume)
          (f := osc z) (C := 1) hfin (fun α _ => le_of_eq (hoscb z α))
        rw [one_mul, measureReal_def] at hIb
        exact mul_le_mul (hAPz z) hIb (norm_nonneg _) (by positivity)
      -- sum the discarded masses: they are disjoint and covered by the
      -- display-(20) bad set at depth `k₊`
      have hsummass : ∑ z ∈ Z,
          (volume (Erdos1002.gaussHalfOpenPrefixCylinder z \
              ⋃ w ∈ W.filter (fun w => w.take km = z),
                Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
          ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := by
        have := sum_discard_fiber_le n js km kp hkm0 hjs_le_km hkm_le_kp
          (h20n kp hkp_2m)
        rw [← hWdef, ← hZdef] at this
        exact this
      calc ‖∑ z ∈ Z, (Afn z * P) *
            ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z \
                ⋃ w ∈ W.filter (fun w => w.take km = z),
                  Erdos1002.gaussHalfOpenPrefixCylinder w, osc z α‖
          ≤ ∑ z ∈ Z, ‖(Afn z * P) *
              ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z \
                  ⋃ w ∈ W.filter (fun w => w.take km = z),
                    Erdos1002.gaussHalfOpenPrefixCylinder w, osc z α‖ :=
            norm_sum_le _ _
        _ ≤ ∑ z ∈ Z, K ^ r * (volume (Erdos1002.gaussHalfOpenPrefixCylinder z \
              ⋃ w ∈ W.filter (fun w => w.take km = z),
                Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal :=
            Finset.sum_le_sum hEbound
        _ = K ^ r * ∑ z ∈ Z, (volume (Erdos1002.gaussHalfOpenPrefixCylinder z \
              ⋃ w ∈ W.filter (fun w => w.take km = z),
                Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ K ^ r * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
            refine mul_le_mul_of_nonneg_left hsummass (by positivity)
    calc ‖T₁ - T₂‖ = ‖(T₁ - T₂') + (T₂' - T₂)‖ := by ring_nf
      _ ≤ ‖T₁ - T₂'‖ + ‖T₂' - T₂‖ := norm_add_le _ _
      _ ≤ K ^ r * ((8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2)
              * Real.exp (-Hscale n)
            + 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ M)
          + K ^ r * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) :=
          add_le_add hT₁T₂' hT₂'T₂
      _ = K ^ r * ((8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2)
              * Real.exp (-Hscale n)
            + 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ M
            + C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by ring
  · -- STEP 3: the oscillatory kill
    have hn0 : 0 < n := hn1
    -- shapes of the second family and its prefixes
    have hZshape : ∀ z ∈ Z, z.length = km ∧ ∀ a ∈ z, 0 < a := by
      intro z hz
      rw [hZdef] at hz
      obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hz
      constructor
      · rw [List.length_take, (hWshape w₀ hw₀).1]
        omega
      · intro a ha
        exact (hWshape w₀ hw₀).2 a (List.mem_of_mem_take ha)
    have hZorig : ∀ z ∈ Z, ∃ w₀ ∈ W, z = w₀.take km := by
      intro z hz
      rw [hZdef] at hz
      obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨w₀, hw₀, rfl⟩
    have hZwin2 : ∀ z ∈ Z,
        (wordDenom z : ℝ) ≤ Real.exp (lyapunov * (km : ℝ) + 1/2 * Hscale n) := by
      intro z hz
      obtain ⟨w₀, hw₀, rfl⟩ := hZorig z hz
      exact (StationaryReplace.mem_retainedWords_iff.mp hw₀).2.2.1
    have hZwin1 : ∀ z ∈ Z,
        Real.exp (lyapunov * (js : ℝ) - 1/2 * Hscale n)
            ≤ (wordDenom (z.take js) : ℝ)
          ∧ (wordDenom (z.take js) : ℝ)
            ≤ Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n) := by
      intro z hz
      obtain ⟨w₀, hw₀, rfl⟩ := hZorig z hz
      have htt : (w₀.take km).take js = w₀.take js := by
        rw [List.take_take]
        congr 1
        omega
      rw [htt]
      exact (StationaryReplace.mem_retainedWords_iff.mp hw₀).2.1
    set U : Finset (List ℕ) := Z.image (fun z => z.take (js + 1)) with hUdef
    have hUshape : ∀ u ∈ U, u.length = js + 1 ∧ ∀ a ∈ u, 0 < a := by
      intro u hu
      rw [hUdef] at hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
      constructor
      · rw [List.length_take, (hZshape z hz).1]
        omega
      · intro a ha
        exact (hZshape z hz).2 a (List.mem_of_mem_take ha)
    have hUne : ∀ u ∈ U, u ≠ [] := by
      intro u hu hnil
      have := (hUshape u hu).1
      rw [hnil] at this
      simp at this
    have hUwin1 : ∀ u ∈ U,
        Real.exp (lyapunov * (js : ℝ) - 1/2 * Hscale n)
            ≤ (wordDenom (u.take js) : ℝ)
          ∧ (wordDenom (u.take js) : ℝ)
            ≤ Real.exp (lyapunov * (js : ℝ) + 1/2 * Hscale n) := by
      intro u hu
      rw [hUdef] at hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
      have htt : (z.take (js + 1)).take js = z.take js := by
        rw [List.take_take]
        congr 1
        omega
      rw [htt]
      exact hZwin1 z hz
    have hUjd : ∀ u ∈ U, ∀ ℓ, ℓ ≤ s → j ℓ ≤ u.length := by
      intro u hu ℓ hℓ
      rw [(hUshape u hu).1]
      exact le_trans (hjle_js ℓ hℓ) (by omega)
    -- the frequency lower bound on each prefix
    have hmode_bd : ∀ ℓ : ℕ, |((modeExt r v ℓ : ℤ) : ℝ)| ≤ (Lnorm n) ^ D :=
      abs_modeExt_le (by positivity) hv
    have hmode_ne : modeExt r v s ≠ 0 := by
      rw [hs_def, modeExt_lt r v (sF : ℕ) sF.isLt]
      simpa using hvs
    have hQlb : ∀ u ∈ U,
        Real.exp (lyapunov * (js : ℝ) - 1/2 * Hscale n) / 2
          ≤ |((Qfz u : ℤ) : ℝ)| := by
      intro u hu
      obtain ⟨α₀, hα₀, hα₀irr⟩ := exists_irrational_mem_halfOpen (hUshape u hu).2
      have hα₀Ioo : α₀ ∈ Ioo (0 : ℝ) 1 :=
        mem_Ioo_of_mem_halfOpen (hUne u hu) (hUshape u hu).2 hα₀ hα₀irr
      have h28 := (h28n α₀ hα₀Ioo hα₀irr j hj (modeExt r v) hmode_bd s hs hmode_ne).1
      have hfr : Prop41Canon.freqQ α₀ j (modeExt r v) s = Qfz u :=
        hQfz u (hUne u hu) (hUshape u hu).2 (hUjd u hu) α₀ hα₀ hα₀irr
      rw [hfr] at h28
      refine le_trans ?_ h28
      have hden : (denom α₀ js : ℝ) = (wordDenom (u.take js) : ℝ) :=
        StationaryReplace.denom_eq_wordDenom_take (hUshape u hu).1
          (hUshape u hu).2 hα₀ hα₀irr (by omega) (by omega)
      rw [hjs_def] at hden ⊢
      rw [hden] at h28 ⊢
      have := (hUwin1 u hu).1
      rw [hjs_def] at this
      linarith
    have hQne : ∀ u ∈ U, Qfz u ≠ 0 := by
      intro u hu h0
      have h1 := hQlb u hu
      rw [h0] at h1
      simp only [Int.cast_zero, abs_zero] at h1
      have := Real.exp_pos (lyapunov * (js : ℝ) - 1/2 * Hscale n)
      linarith
    -- the first inequality of (29)
    set εk : ℝ := Real.exp (-(90 : ℝ) * Hscale n) with hεkdef
    have hεk0 : 0 < εk := Real.exp_pos _
    have hRcond : ∀ u ∈ U,
        (Real.exp (lyapunov * (km : ℝ) + 1/2 * Hscale n)) ^ 2
          ≤ εk * (n : ℝ) * |((Qfz u : ℤ) : ℝ)| := by
      intro u hu
      have hsq : (Real.exp (lyapunov * (km : ℝ) + 1/2 * Hscale n)) ^ 2
          = Real.exp (2 * lyapunov * (km : ℝ) + Hscale n) := by
        rw [sq, ← Real.exp_add]
        ring_nf
      have hkm2 : 2 * lyapunov * (km : ℝ)
          ≤ lyapunov * (mIndex n : ℝ) + lyapunov * (js : ℝ)
            - 80 * lyapunov * HH := by
        nlinarith [hkm_ub, hlyap]
      have hX : (1 : ℝ) ≤ LL + lyapunov * (js : ℝ) - (91.5 : ℝ) * HH
          - 2 * lyapunov * (km : ℝ) := by
        nlinarith [hlm_ub, h80.1, hH1, hlyap]
      have hQb := hQlb u hu
      have hexpval : Real.exp (2 * lyapunov * (km : ℝ) + Hscale n) * 2
          ≤ Real.exp (-(90 : ℝ) * Hscale n) * Real.exp LL
            * Real.exp (lyapunov * (js : ℝ) - 1/2 * Hscale n) := by
        have h2e : (2 : ℝ) ≤ Real.exp (LL + lyapunov * (js : ℝ)
            - (91.5 : ℝ) * HH - 2 * lyapunov * (km : ℝ)) := by
          have := Real.add_one_le_exp (LL + lyapunov * (js : ℝ)
            - (91.5 : ℝ) * HH - 2 * lyapunov * (km : ℝ))
          linarith
        have hcomb : Real.exp (2 * lyapunov * (km : ℝ) + Hscale n) *
            Real.exp (LL + lyapunov * (js : ℝ)
              - (91.5 : ℝ) * HH - 2 * lyapunov * (km : ℝ))
            = Real.exp (-(90 : ℝ) * Hscale n) * Real.exp LL
              * Real.exp (lyapunov * (js : ℝ) - 1/2 * Hscale n) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          simp only [hHH]
          ring
        calc Real.exp (2 * lyapunov * (km : ℝ) + Hscale n) * 2
            ≤ Real.exp (2 * lyapunov * (km : ℝ) + Hscale n) *
                Real.exp (LL + lyapunov * (js : ℝ)
                  - (91.5 : ℝ) * HH - 2 * lyapunov * (km : ℝ)) := by
              exact mul_le_mul_of_nonneg_left h2e (Real.exp_pos _).le
          _ = Real.exp (-(90 : ℝ) * Hscale n) * Real.exp LL
              * Real.exp (lyapunov * (js : ℝ) - 1/2 * Hscale n) := hcomb
      have hQstep : εk * (n : ℝ) * (Real.exp (lyapunov * (js : ℝ)
            - 1/2 * Hscale n) / 2)
          ≤ εk * (n : ℝ) * |((Qfz u : ℤ) : ℝ)| := by
        refine mul_le_mul_of_nonneg_left hQb ?_
        have hn0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        positivity
      refine le_trans ?_ hQstep
      rw [hsq, hεkdef, hnexp]
      nlinarith [hexpval]
    -- coefficients for the descendant estimate
    set B : ℝ := K ^ r with hBdef
    have hB1 : (1 : ℝ) ≤ B := one_le_pow₀ hK1
    have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
    set ccoef : List ℕ → List ℕ → ℂ :=
      fun u vv => (Afn (u ++ vv) * P) / (B : ℂ) with hccoefdef
    have hccoef : ∀ u vv, ‖ccoef u vv‖ ≤ 1 := by
      intro u vv
      rw [hccoefdef]
      have hAP : ‖Afn (u ++ vv) * P‖ ≤ B := by
        rw [norm_mul, ← hKr_split]
        exact mul_le_mul (hA_norm _) hP_norm (norm_nonneg _)
          (pow_nonneg hK0.le _)
      have hnormB : ‖((B : ℝ) : ℂ)‖ = B := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
      rw [norm_div, hnormB, div_le_one hB0]
      exact hAP
    set Sdesc : List ℕ → Finset (List ℕ) :=
      fun u => (Z.filter (fun z => z.take (js + 1) = u)).image
        (fun z => z.drop (js + 1)) with hSdescdef
    have hSprop : ∀ u ∈ U, ∀ vv ∈ Sdesc u, vv.length = km - (js + 1) ∧
        (∀ a ∈ vv, 0 < a) ∧
        ((Erdos1002.cfTerminalDenominator (u ++ vv) : ℝ)
          ≤ Real.exp (lyapunov * (km : ℝ) + 1/2 * Hscale n)) := by
      intro u hu vv hvv
      rw [hSdescdef] at hvv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hvv
      rw [Finset.mem_filter] at hz
      have huz : u ++ z.drop (js + 1) = z := by
        rw [← hz.2, List.take_append_drop]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.length_drop, (hZshape z hz.1).1]
      · intro a ha
        exact (hZshape z hz.1).2 a (List.mem_of_mem_drop ha)
      · rw [huz, ← StationaryReplace.wordDenom_eq_cfTerminalDenominator]
        exact hZwin2 z hz.1
    -- the descendant-cylinder estimate
    have hcore := Kwon1002.descendant_cylinder_estimate_core (ε := εk) hεk0
      (n := n) (d := js + 1) (k := km) hn0 hjs_km U Qfz
      (fun _ => Real.exp (lyapunov * (km : ℝ) + 1/2 * Hscale n)) Sdesc ccoef
      hUshape hQne (fun u hu => hRcond u hu) hSprop (fun u vv => hccoef u vv)
    -- rewrite `T₂` into the shape of the estimate
    have hT₂form : T₂ = ((-1 : ℂ)) ^ km * (B : ℂ) *
        ∑ u ∈ U, ∑ vv ∈ Sdesc u, ccoef u vv *
          ∫ α in (Erdos1002.gaussInverseWord (u ++ vv) 0)..
            (Erdos1002.gaussInverseWord (u ++ vv) 1),
            Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qfz u : ℤ) : ℝ)) α := by
      rw [hT₂def]
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun z : List ℕ => z.take (js + 1)) (t := U)
        (fun z hz => Finset.mem_image_of_mem _ hz)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u hu => ?_)
      rw [Finset.mul_sum]
      rw [hSdescdef, Finset.sum_image ?hinj]
      case hinj =>
        intro z hz z' hz' hdrop
        have hz1 := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
        have hz1' := Finset.mem_filter.mp (Finset.mem_coe.mp hz')
        have h1 : z = z.take (js + 1) ++ z.drop (js + 1) :=
          (List.take_append_drop _ _).symm
        have h2 : z' = z'.take (js + 1) ++ z'.drop (js + 1) :=
          (List.take_append_drop _ _).symm
        have hdrop' : List.drop (js + 1) z = List.drop (js + 1) z' := hdrop
        rw [h1, h2, hz1.2, hz1'.2, hdrop']
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [Finset.mem_filter] at hz
      have huz : u ++ z.drop (js + 1) = z := by
        rw [← hz.2, List.take_append_drop]
      have hosc_eq : (osc z) = fun α =>
          Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qfz u : ℤ) : ℝ)) α := by
        funext α
        simp only [hoscdef]
        rw [hz.2]
        exact torusChar_eq_oscillatoryPhase _ _
      have hint_eq : (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z, osc z α)
          = ((-1 : ℂ)) ^ km *
            ∫ α in (Erdos1002.gaussInverseWord z 0)..
              (Erdos1002.gaussInverseWord z 1),
              Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qfz u : ℤ) : ℝ)) α := by
        rw [show (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder z, osc z α)
            = ∫ α in Erdos1002.closedGaussPrefixCylinder z, osc z α from
          setIntegral_congr_set (halfOpen_ae_eq_closed (hZshape z hz.1).2)]
        rw [hosc_eq]
        rw [setIntegral_closedCylinder_eq (hZshape z hz.1).2]
        rw [(hZshape z hz.1).1]
      rw [hint_eq]
      simp only [hccoefdef]
      rw [huz]
      have hBne : ((B : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt hB0
      field_simp
    rw [hT₂form]
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
    calc B * ‖∑ u ∈ U, ∑ vv ∈ Sdesc u, ccoef u vv *
          ∫ α in (Erdos1002.gaussInverseWord (u ++ vv) 0)..
            (Erdos1002.gaussInverseWord (u ++ vv) 1),
            Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qfz u : ℤ) : ℝ)) α‖
        ≤ B * ∑ u ∈ U, ‖∑ vv ∈ Sdesc u, ccoef u vv *
            ∫ α in (Erdos1002.gaussInverseWord (u ++ vv) 0)..
              (Erdos1002.gaussInverseWord (u ++ vv) 1),
              Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qfz u : ℤ) : ℝ)) α‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hB0.le
      _ ≤ B * (14 * εk) := mul_le_mul_of_nonneg_left hcore hB0.le
      _ ≤ K ^ r * (14 * Real.exp (-Hscale n)) := by
          rw [hBdef]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hεkdef]
          have : Real.exp (-(90 : ℝ) * Hscale n) ≤ Real.exp (-Hscale n) := by
            refine Real.exp_le_exp.mpr ?_
            nlinarith [hH0]
          nlinarith [this]



/-! ## 5. The three-step chain and the `v_s ≠ 0` branch, unconditional

The eventual numeric inputs of the master estimate are marshalled once,
and the three per-`n` bounds are converted into the manuscript's uniform
constants. -/

set_option maxHeartbeats 1600000 in
/-- **The nonzero-mode three-step chain, unconditional.**  Statement
reproduced token-identically from `ZeroMode.nonzero_mode_three_step`
(which is sorried in place, its proof living above it in the import
order); proved outright. -/
theorem nonzero_mode_three_step_unconditional (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C c₀ ρ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
      ∀ v ∈ modeTuples r D (Lnorm n), v ≠ 0 →
        ∃ T₁ T₂ : ℂ,
          ‖modeTerm n r j c v - T₁‖
              ≤ C * (Lnorm n) ^ (D * r) * Real.exp (-c₀ * Real.sqrt (Lnorm n)) ∧
            ‖T₁ - T₂‖
              ≤ C * (Lnorm n) ^ (D * r) *
                  (Real.exp (-c₀ * Real.sqrt (Lnorm n))
                    + Real.exp (-c₀ * Hscale n) + ρ ^ (c₀ * Hscale n)) ∧
            ‖T₂‖ ≤ C * (Lnorm n) ^ (D * r) * Real.exp (-c₀ * Hscale n) := by
  obtain ⟨Cu, ρu, hCu, hρu0, hρu1, huni⟩ := leb_mixing_complex_uniform r
  obtain ⟨C₀, c₀, hC₀, hc₀, h20⟩ :=
    LargeDeviation.display20_of_pos (1/2) (by norm_num)
  have h20' : ∀ᶠ n : ℕ in atTop, ∀ jj : ℕ, jj ≤ 2 * mIndex n →
      volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (jj : ℝ) - (1/2 : ℝ) * Hscale n)
                ≤ (denom α jj : ℝ)
              ∧ (denom α jj : ℝ)
                ≤ Real.exp (lyapunov * (jj : ℝ) + (1/2 : ℝ) * Hscale n))}
        ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := h20
  set c₁ : ℝ := min c₀ 1 with hc₁def
  have hc₁0 : 0 < c₁ := lt_min hc₀ one_pos
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set CC : ℝ := 4 * C₀ + 8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2 + 14
      + 2 ^ (2 * r + 1) * Real.log 2 * Cu / ρu with hCCdef
  have hCC0 : 0 < CC := by
    rw [hCCdef]
    positivity
  refine ⟨CC, c₁, ρu, hCC0, hc₁0, hρu0, hρu1, ?_⟩
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev28 := Prop41Canon.display_28 r D hD
  have hev80 : ∀ᶠ n : ℕ in atTop,
      80 * lyapunov ≤ (Lnorm n) ^ ((1 : ℝ)/4) := by
    filter_upwards [hLtend.eventually_ge_atTop
      (max ((80 * lyapunov) ^ (4 : ℕ)) 1)] with n hn
    have hbig : ((80 * lyapunov) ^ (4 : ℕ)) ≤ Lnorm n := le_trans (le_max_left _ _) hn
    have hL1' : (1 : ℝ) ≤ Lnorm n := le_trans (le_max_right _ _) hn
    have hb0 : (0 : ℝ) ≤ 80 * lyapunov := by
      have := Prop42.lyapunov_pos
      linarith
    have hmono : ((80 * lyapunov) ^ (4 : ℕ)) ^ ((1 : ℝ)/4)
        ≤ (Lnorm n) ^ ((1 : ℝ)/4) :=
      Real.rpow_le_rpow (pow_nonneg hb0 4) hbig (by norm_num)
    have hid : ((80 * lyapunov) ^ (4 : ℕ)) ^ ((1 : ℝ)/4) = 80 * lyapunov := by
      rw [← Real.rpow_natCast (80 * lyapunov) 4, ← Real.rpow_mul hb0]
      norm_num
    rwa [hid] at hmono
  filter_upwards [h20', hev28, hLtend.eventually_ge_atTop 1,
    eventually_ge_atTop 1, hLtend.eventually_ge_atTop (16 * D ^ 2),
    hev80, hLtend.eventually_ge_atTop (2 * lyapunov)]
    with n h20n h28n hL1 hn1 hLD2 h80L h2lL
  intro j hj F c hc v hv hv0
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le one_pos hL1
  have hH1 : (1 : ℝ) ≤ Hscale n := Real.one_le_rpow hL1 (by norm_num)
  have hH0 : (0 : ℝ) ≤ Hscale n := le_trans zero_le_one hH1
  have hlyap : (0 : ℝ) < lyapunov := Prop42.lyapunov_pos
  -- `L^D ≤ e^H`
  have hLD : (Lnorm n) ^ D ≤ Real.exp (Hscale n) := by
    have hlogle : Real.log (Lnorm n) ≤ (Lnorm n) ^ ((1:ℝ)/4) / (1/4) :=
      Real.log_le_rpow_div hL0.le (by norm_num)
    have h4D : 4 * D ≤ (Lnorm n) ^ ((1:ℝ)/2) := by
      have hsq : Real.sqrt (Lnorm n) = (Lnorm n) ^ ((1:ℝ)/2) :=
        Real.sqrt_eq_rpow _
      rw [← hsq]
      have h1 : (4 * D) ^ 2 ≤ Lnorm n := by nlinarith [hLD2]
      have h2 : (0 : ℝ) ≤ 4 * D := by positivity
      have h3 : Real.sqrt ((4 * D) ^ 2) ≤ Real.sqrt (Lnorm n) :=
        Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq h2] at h3
    have hsplit : (Lnorm n) ^ ((1:ℝ)/2) * (Lnorm n) ^ ((1:ℝ)/4)
        = Hscale n := by
      rw [show Hscale n = (Lnorm n) ^ ((3:ℝ)/4) from rfl,
        ← Real.rpow_add hL0]
      norm_num
    have hkey : D * Real.log (Lnorm n) ≤ Hscale n := by
      have h1 : D * Real.log (Lnorm n) ≤ D * (4 * (Lnorm n) ^ ((1:ℝ)/4)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD.le
        calc Real.log (Lnorm n) ≤ (Lnorm n) ^ ((1:ℝ)/4) / (1/4) := hlogle
          _ = 4 * (Lnorm n) ^ ((1:ℝ)/4) := by ring
      have h2 : D * (4 * (Lnorm n) ^ ((1:ℝ)/4))
          = (4 * D) * (Lnorm n) ^ ((1:ℝ)/4) := by ring
      have h3 : (4 * D) * (Lnorm n) ^ ((1:ℝ)/4)
          ≤ (Lnorm n) ^ ((1:ℝ)/2) * (Lnorm n) ^ ((1:ℝ)/4) := by
        refine mul_le_mul_of_nonneg_right h4D ?_
        positivity
      rw [← hsplit]
      linarith
    calc (Lnorm n) ^ D = Real.exp (Real.log (Lnorm n) * D) :=
          Real.rpow_def_of_pos hL0 D
      _ ≤ Real.exp (Hscale n) := by
          refine Real.exp_le_exp.mpr ?_
          rw [mul_comm]
          exact hkey
  -- `40H ≤ m_n`
  have hm40 : 40 * Hscale n ≤ (mIndex n : ℝ) := by
    have hsplit : (Lnorm n) ^ ((3:ℝ)/4) * (Lnorm n) ^ ((1:ℝ)/4) = Lnorm n := by
      rw [← Real.rpow_add hL0]
      norm_num
    have h80H : 80 * lyapunov * Hscale n ≤ Lnorm n := by
      calc 80 * lyapunov * Hscale n
          = Hscale n * (80 * lyapunov) := by ring
        _ ≤ Hscale n * (Lnorm n) ^ ((1:ℝ)/4) := by
            refine mul_le_mul_of_nonneg_left h80L hH0
        _ = Lnorm n := by
            rw [show Hscale n = (Lnorm n) ^ ((3:ℝ)/4) from rfl]
            exact hsplit
    have hmlb : Lnorm n / lyapunov < (mIndex n : ℝ) + 1 := by
      rw [show mIndex n = ⌊Lnorm n / lyapunov⌋₊ from rfl]
      exact Nat.lt_floor_add_one _
    have h1 : 40 * Hscale n ≤ Lnorm n / (2 * lyapunov) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h80H]
    have h2 : Lnorm n / (2 * lyapunov) ≤ Lnorm n / lyapunov - 1 := by
      have he : Lnorm n / lyapunov = 2 * (Lnorm n / (2 * lyapunov)) := by
        field_simp
      have h1' : (1 : ℝ) ≤ Lnorm n / (2 * lyapunov) := by
        rw [le_div_iff₀ (by positivity)]
        linarith [h2lL]
      linarith
    linarith
  obtain ⟨T₁, T₂, hb1, hb2, hb3⟩ := nonzero_mode_master r D hD Cu ρu hCu hρu0
    hρu1 C₀ c₀ hC₀ hc₀ n huni h20n h28n hn1 hL1 hH1 hLD hm40 j hj F c hc v hv hv0
  have hKr : ((Lnorm n) ^ D) ^ r = (Lnorm n) ^ (D * (r : ℝ)) := by
    rw [← Real.rpow_natCast ((Lnorm n) ^ D) r, ← Real.rpow_mul hL0.le]
  have hX0 : (0 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) := Real.rpow_nonneg hL0.le _
  have hc₁c₀ : c₁ ≤ c₀ := min_le_left _ _
  have hc₁1 : c₁ ≤ 1 := min_le_right _ _
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (Lnorm n) := Real.sqrt_nonneg _
  have hE1 : Real.exp (-c₀ * Real.sqrt (Lnorm n))
      ≤ Real.exp (-c₁ * Real.sqrt (Lnorm n)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hE2 : Real.exp (-Hscale n) ≤ Real.exp (-c₁ * Hscale n) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hρfloor : ρu ^ ⌊100 * Hscale n⌋₊
      ≤ ρu ^ ((100 : ℝ) * Hscale n) / ρu :=
    ZeroMode.pow_floor_le_rpow_div ρu hρu0 hρu1 _
  have hρexp : ρu ^ ((100 : ℝ) * Hscale n) ≤ ρu ^ (c₁ * Hscale n) := by
    refine Real.rpow_le_rpow_of_exponent_ge hρu0 hρu1.le ?_
    nlinarith
  have hE10 : (0 : ℝ) ≤ Real.exp (-c₁ * Real.sqrt (Lnorm n)) := (Real.exp_pos _).le
  have hE20 : (0 : ℝ) ≤ Real.exp (-c₁ * Hscale n) := (Real.exp_pos _).le
  have hE30 : (0 : ℝ) ≤ ρu ^ (c₁ * Hscale n) := (Real.rpow_pos_of_pos hρu0 _).le
  have hcoef1 : 3 * C₀ ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 * Cu / ρu := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 := by positivity
    nlinarith [hC₀, hπ0]
  have hcoefC₀ : C₀ ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 * Cu / ρu := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 := by positivity
    nlinarith [hC₀, hπ0]
  have hcoef2 : 8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2 ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 * Cu / ρu := by positivity
    nlinarith [hC₀]
  have hcoef3 : 2 ^ (2 * r + 1) * Real.log 2 * Cu / ρu ≤ CC := by
    rw [hCCdef]
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 := by positivity
    nlinarith [hC₀, hπ0]
  have hcoef4 : (14 : ℝ) ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 * Cu / ρu := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * r + 1) * Real.log 2 := by positivity
    nlinarith [hC₀, hπ0]
  rw [hKr] at hb1 hb2 hb3
  refine ⟨T₁, T₂, ?_, ?_, ?_⟩
  · refine le_trans hb1 ?_
    have h1 : 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
        ≤ CC * Real.exp (-c₁ * Real.sqrt (Lnorm n)) := by
      calc 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
          = 3 * C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := by ring
        _ ≤ CC * Real.exp (-c₁ * Real.sqrt (Lnorm n)) :=
            mul_le_mul hcoef1 hE1 (Real.exp_pos _).le hCC0.le
    calc (Lnorm n) ^ (D * (r : ℝ))
          * (3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))))
        ≤ (Lnorm n) ^ (D * (r : ℝ))
          * (CC * Real.exp (-c₁ * Real.sqrt (Lnorm n))) :=
          mul_le_mul_of_nonneg_left h1 hX0
      _ = CC * (Lnorm n) ^ (D * (r : ℝ))
          * Real.exp (-c₁ * Real.sqrt (Lnorm n)) := by ring
  · refine le_trans hb2 ?_
    have p1 : (8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2) * Real.exp (-Hscale n)
        ≤ CC * Real.exp (-c₁ * Hscale n) :=
      mul_le_mul hcoef2 hE2 (Real.exp_pos _).le hCC0.le
    have p2 : 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ ⌊100 * Hscale n⌋₊
        ≤ CC * ρu ^ (c₁ * Hscale n) := by
      have h1 : ρu ^ ⌊100 * Hscale n⌋₊ ≤ ρu ^ (c₁ * Hscale n) / ρu := by
        refine le_trans hρfloor ?_
        gcongr
      calc 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ ⌊100 * Hscale n⌋₊
          ≤ 2 ^ (2 * r + 1) * Real.log 2 * Cu * (ρu ^ (c₁ * Hscale n) / ρu) := by
            refine mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 ^ (2 * r + 1) * Real.log 2 * Cu / ρu) * ρu ^ (c₁ * Hscale n) := by
            field_simp
        _ ≤ CC * ρu ^ (c₁ * Hscale n) :=
            mul_le_mul_of_nonneg_right hcoef3 hE30
    have p3 : C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))
        ≤ CC * Real.exp (-c₁ * Real.sqrt (Lnorm n)) :=
      mul_le_mul hcoefC₀ hE1 (Real.exp_pos _).le hCC0.le
    have hsum : (8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2)
          * Real.exp (-Hscale n)
        + 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ ⌊100 * Hscale n⌋₊
        + C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))
        ≤ CC * (Real.exp (-c₁ * Real.sqrt (Lnorm n))
            + Real.exp (-c₁ * Hscale n) + ρu ^ (c₁ * Hscale n)) := by
      nlinarith [p1, p2, p3]
    calc (Lnorm n) ^ (D * (r : ℝ)) *
          ((8 * Real.pi + 2 ^ (2 * r + 1) * Real.log 2) * Real.exp (-Hscale n)
            + 2 ^ (2 * r + 1) * Real.log 2 * Cu * ρu ^ ⌊100 * Hscale n⌋₊
            + C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
        ≤ (Lnorm n) ^ (D * (r : ℝ)) *
          (CC * (Real.exp (-c₁ * Real.sqrt (Lnorm n))
            + Real.exp (-c₁ * Hscale n) + ρu ^ (c₁ * Hscale n))) :=
          mul_le_mul_of_nonneg_left hsum hX0
      _ = CC * (Lnorm n) ^ (D * (r : ℝ)) *
          (Real.exp (-c₁ * Real.sqrt (Lnorm n))
            + Real.exp (-c₁ * Hscale n) + ρu ^ (c₁ * Hscale n)) := by ring
  · refine le_trans hb3 ?_
    have h1 : (14 : ℝ) * Real.exp (-Hscale n) ≤ CC * Real.exp (-c₁ * Hscale n) :=
      mul_le_mul hcoef4 hE2 (Real.exp_pos _).le hCC0.le
    calc (Lnorm n) ^ (D * (r : ℝ)) * (14 * Real.exp (-Hscale n))
        ≤ (Lnorm n) ^ (D * (r : ℝ)) * (CC * Real.exp (-c₁ * Hscale n)) :=
          mul_le_mul_of_nonneg_left h1 hX0
      _ = CC * (Lnorm n) ^ (D * (r : ℝ)) * Real.exp (-c₁ * Hscale n) := by ring
end

end NonzeroMode

end Kwon1002
