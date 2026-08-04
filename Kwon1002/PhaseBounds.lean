import Kwon1002.P42Cases
import Kwon1002.Prop41Final

/-!
# PhaseBounds, scratch file (agent `monocore`)

TARGETS: `MonomialCore.zeroMode_gauss_mixing`, `MonomialCore.laterMode_phase_bound`,
`MonomialCore.earlierMode_phase_bound`, `P42Cases.zeroMode_cylinder_mixing`.

## What is achieved

**Case 1 of Kwon's proof of Proposition 4.2 is proved**, down to a single
statement that contains no dynamics at all.  Both
`MonomialCore.zeroMode_gauss_mixing` and `P42Cases.zeroMode_cylinder_mixing`
are reproduced token-identically (§6, diffed byte-for-byte against
`MonomialCore.lean` 371-379 and `P42Cases.lean` 201-208, only the name primed)
and **proved** from exactly one new sorried input, `natExt_marginal`.

The two obstructions `P42Cases` §2 records for case 1 are handled as follows.

* *"Two-sided Gauss mixing for cylinder indicators"*, **removed**.
  `lebesgue_two_block` (§1) is that statement, proved outright: two BV
  observables at times `t₀ < t₁` separated by `M`, Lebesgue outer measure on
  `(0,1)`, Gauss stationary means, error `C ρ^M K²`.  It is assembled from
  `MixingBV.lem_3_2_conditional_multiblock_mixing'` at the trivial prefix
  (`cylinder_zero`), `Erdos1002.integral_comp_gaussOrbit` (invariance) and
  `Prop41Final.lebesgue_sub_gauss_le` (Gauss-Kuzmin).  The existing tree has
  only `Prop41Final.lebesgue_multiblock`, which is restricted to **good
  tuples** and therefore does not apply to `p.1 − R`, `p.2 − R`.
  The missing BV input is also supplied here: §2 proves that a digit cylinder
  is **order-convex** (`digit_between`, `ordConnected_cylSet`), that the
  indicator of any order-convex set has variation `≤ 2`
  (`eVariationOn_indicator_ordConnected`, via a Jordan decomposition into two
  up-set indicators, Mathlib has the monotone case only), hence
  `cylObs_bv : BVBoundedBy 2 (cylObs R w)`.  `Bridge.bv_of_firstDigit_step`
  covers only depth `1`, so this is new.
* *"Identification of the `μ̂₀`-marginal `cylProb R w` with the Gauss measure of
  the `2R`-cylinder"*, **remains**, as `natExt_marginal` (§4), with the index
  matching machine-checked against `cylObs_windowWord` and the reduction to a
  two-dimensional integral spelled out.  This is the one genuinely absent piece.

## Sorried results consumed

`natExt_marginal` (new here) only.  Nothing else sorried is used: the
`P42Cases` results quoted (`zeroMode_norm_eq`, `measurableSet_cyl`,
`tendsto_Hscale`) and the `MonomialCore` results quoted
(`mem_bulkPairs_fst`, `mem_bulkPairs_lt`) are all axiom-clean, as are
`MixingBV.lem_3_2_conditional_multiblock_mixing'`,
`Prop41Final.lebesgue_sub_gauss_le`, `Prop41Final.gaussMeasure_Ioo_eq_one`,
`Prop41Final.gaussMeasure_restrict_Ioo`, `Prop41Final.gaussMeasure_ae_Ioo`,
`Prop41Final.gaussIter_add`, `BVLasotaYorke.eVariationOn_add_le`,
`MixingBV.eVariationOn_const_mul_le`, `Prop42.measurable_digitNat`.

## Axiom audit

`#print axioms` was run on all twenty-two results proved outright here
(`cylinder_zero`, `lebesgue_two_block`, `gaussIter_zero_left`,
`digit_zero_left`, `digit_succ`, `one_lt_inv_of_mem`, `digit_zero_floor`,
`one_le_digit_zero`, `gaussMap_eq_sub`, `digit_between`, `ordConnected_cylSet`,
`eVariationOn_indicator_up`, `eVariationOn_indicator_ordConnected`,
`wordSet_inter_Ioo`, `measurableSet_wordSet`, `measurable_cylObs`,
`cylObs_bound`, `cylObs_bv`, `digit_gaussIter`, `cylObs_windowWord`,
`integral_cylObs_mul`, `integral_cylObs_gauss`): each depends on exactly
`[propext, Classical.choice, Quot.sound]`.  `zeroMode_cylinder_mixing'` and
`zeroMode_gauss_mixing'` depend additionally on `sorryAx`, and only through
`natExt_marginal`.  The audit block has been removed.

## The two phase bounds: no progress, and why (finding, independently confirmed)

`laterMode_phase_bound` and `earlierMode_phase_bound` are **not** attempted.
Re-reading the manuscript's proof of 4.2 (full text lines ≈ 411-470) against
the current tree confirms the correction `P42Cases` §4 already records, the
`MonomialCore` docstring's stated obstruction (display (22) missing) is stale,
since `Display22.descendant_cylinder_estimate` is proved, and confirms its
replacement: **display (20)**, the Lévy large-deviation bound
`e^{λj−δH} ≤ q_j ≤ e^{λj+δH}` off a set of mass `O(e^{−c√L})`, is absent from
`Kwon1002/` and from the 35-module Wang substrate alike, and is used *four*
times in cases 2 and 3 (the `hqt`/`hqk` hypotheses of
`Prop42.retained_descendant_exponent` in both `t₋` branches; the lower bound
`q_{t₊} ≥ e^{λt₊−δH}` of the `t₊` branch; and it is the sole source of the
`e^{−cL^{1/2}}` summand of the error bracket of (34)).  Note that the
`k > t₀ + 100H` branch of case 3 also asks for "conditional Gauss mixing …
applied on each cylinder and summed by cylinder mass"; the *unconditional*
two-block form of that is now available as `lebesgue_two_block` above, and the
conditional form as `MixingBV.lem_3_2_conditional_multiblock_mixing'`, so (20)
is the only remaining analytic gap in those two cases.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace PhaseBounds

noncomputable section

/-! ## 1. Two-block Gauss mixing with the Lebesgue outer measure -/

lemma cylinder_zero (w : ℕ → ℕ) : Prop41.cylinder 0 w = Ioo (0 : ℝ) 1 := by
  ext y
  simp [Prop41.cylinder]

/-- **"Ordinary two-sided Gauss mixing"**, in the form the zero-mode case of
Kwon's proof of Proposition 4.2 needs: two BV observables read at times
`t₀ < t₁`, both separated by `M` (from the origin and from each other), with
the *Lebesgue* outer measure on `(0,1)` and the *Gauss* stationary means. -/
theorem lebesgue_two_block :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (M t₀ t₁ : ℕ) (g₀ g₁ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
        Measurable g₀ → Measurable g₁ →
        (∀ x, |g₀ x| ≤ K) → (∀ x, |g₁ x| ≤ K) →
        Prop41.BVBoundedBy K g₀ → Prop41.BVBoundedBy K g₁ →
        M ≤ t₀ → t₀ + M ≤ t₁ →
        |(∫ α in Ioo (0 : ℝ) 1, g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁))
            - (∫ x, g₀ x ∂Erdos1002.gaussMeasure) * (∫ x, g₁ x ∂Erdos1002.gaussMeasure)|
          ≤ C * ρ ^ M * K ^ 2 := by
  classical
  obtain ⟨C, ρ, hC, hρ0, hρ1, hmix⟩ := MixingBV.lem_3_2_conditional_multiblock_mixing' 2
  refine ⟨C + Real.log 2, max ρ (527 / 540 : ℝ),
    by positivity, lt_of_lt_of_le hρ0 (le_max_left _ _),
    max_lt hρ1 (by norm_num), ?_⟩
  intro M t₀ t₁ g₀ g₁ K hK hm₀ hm₁ hb₀ hb₁ hbv₀ hbv₁ hMt₀ hMt₁
  set ρ' : ℝ := max ρ (527 / 540 : ℝ) with hρ'def
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le hρ0 (le_max_left _ _)
  have hK2 : (0 : ℝ) ≤ K ^ 2 := by positivity
  set g : ℕ → ℝ → ℝ := fun i => if i = 0 then g₀ else g₁ with hgdef
  set t : ℕ → ℕ := fun i => if i = 0 then t₀ else t₁ with htdef
  have hprod : ∀ α : ℝ, (∏ i ∈ Finset.range 2, g i (gaussIter α (t i)))
      = g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁) := by
    intro α
    rw [Finset.prod_range_succ, Finset.prod_range_one]
    simp [hgdef, htdef]
  have hmeanprod : (∏ i ∈ Finset.range 2, ∫ x, g i x ∂Erdos1002.gaussMeasure)
      = (∫ x, g₀ x ∂Erdos1002.gaussMeasure) * (∫ x, g₁ x ∂Erdos1002.gaussMeasure) := by
    rw [Finset.prod_range_succ, Finset.prod_range_one]
    simp [hgdef]
  -- the composite observable, read at time `t₀`
  set G : ℝ → ℝ := fun y => g₀ y * g₁ (gaussIter y (t₁ - t₀)) with hGdef
  have hGm : ∀ α : ℝ, G (gaussIter α t₀) = g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁) := by
    intro α
    have hit : gaussIter (gaussIter α t₀) (t₁ - t₀) = gaussIter α t₁ := by
      rw [Prop41Final.gaussIter_add]
      congr 1
      omega
    show g₀ (gaussIter α t₀) * g₁ (gaussIter (gaussIter α t₀) (t₁ - t₀)) = _
    rw [hit]
  have hGmeas : Measurable G :=
    hm₀.mul (hm₁.comp (measurable_gaussIter (t₁ - t₀)))
  have hGbd : ∀ y : ℝ, |G y| ≤ K ^ 2 := by
    intro y
    rw [hGdef, abs_mul, sq]
    exact mul_le_mul (hb₀ y) (hb₁ _) (abs_nonneg _) hK
  -- (i) Gauss-Kuzmin
  have hGK : |(∫ α in Ioo (0 : ℝ) 1, g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁))
        - ∫ y, G y ∂Erdos1002.gaussMeasure|
      ≤ (527 / 540 : ℝ) ^ t₀ * Real.log 2 * K ^ 2 := by
    have h := Prop41Final.lebesgue_sub_gauss_le G hGmeas (K ^ 2) hK2 (fun y _ => hGbd y) t₀
    have hrw : (∫ α in Ioo (0 : ℝ) 1, G (gaussIter α t₀))
        = ∫ α in Ioo (0 : ℝ) 1, g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁) :=
      setIntegral_congr_fun measurableSet_Ioo (fun α _ => hGm α)
    rwa [hrw] at h
  -- (ii) invariance
  have hinv : (∫ y, G y ∂Erdos1002.gaussMeasure)
      = ∫ α in Ioo (0 : ℝ) 1,
          (g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁)) ∂Erdos1002.gaussMeasure := by
    rw [Prop41Final.gaussMeasure_restrict_Ioo,
      ← Erdos1002.integral_comp_gaussOrbit G hGmeas t₀]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun α => hGm α))
  -- (iii) conditional multi-block mixing at the trivial prefix
  have hbvg : ∀ i, i < 2 → Prop41.BVBoundedBy K (g i) := by
    intro i hi
    interval_cases i
    · simpa [hgdef] using hbv₀
    · simpa [hgdef] using hbv₁
  have hpos : 0 < (Erdos1002.gaussMeasure (Prop41.cylinder 0 (fun _ => 0))).toReal := by
    rw [cylinder_zero, Prop41Final.gaussMeasure_Ioo_eq_one]
    norm_num
  have hmixj := hmix 0 M (fun _ => 0) t g K hK hbvg (by simpa using hMt₀)
    (by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa [htdef] using hMt₁) hpos
  rw [cylinder_zero, Prop41Final.gaussMeasure_Ioo_eq_one, div_one] at hmixj
  simp only [hprod, hmeanprod] at hmixj
  -- assemble
  have hstep1 : (527 / 540 : ℝ) ^ t₀ ≤ ρ' ^ M := by
    calc (527 / 540 : ℝ) ^ t₀ ≤ (527 / 540 : ℝ) ^ M :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hMt₀
      _ ≤ ρ' ^ M := pow_le_pow_left₀ (by norm_num) (le_max_right _ _) M
  have hstep2 : ρ ^ M ≤ ρ' ^ M := pow_le_pow_left₀ hρ0.le (le_max_left _ _) M
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hρ'M : (0 : ℝ) ≤ ρ' ^ M := pow_nonneg hρ'0.le M
  have hA : |(∫ α in Ioo (0 : ℝ) 1, g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁))
        - ∫ y, G y ∂Erdos1002.gaussMeasure| ≤ Real.log 2 * (ρ' ^ M * K ^ 2) := by
    refine le_trans hGK ?_
    have h1 : (527 / 540 : ℝ) ^ t₀ * Real.log 2 ≤ ρ' ^ M * Real.log 2 :=
      mul_le_mul_of_nonneg_right hstep1 hlog2
    calc (527 / 540 : ℝ) ^ t₀ * Real.log 2 * K ^ 2
        ≤ ρ' ^ M * Real.log 2 * K ^ 2 := mul_le_mul_of_nonneg_right h1 hK2
      _ = Real.log 2 * (ρ' ^ M * K ^ 2) := by ring
  have hB : |(∫ α in Ioo (0 : ℝ) 1,
          (g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁)) ∂Erdos1002.gaussMeasure)
        - (∫ x, g₀ x ∂Erdos1002.gaussMeasure) * (∫ x, g₁ x ∂Erdos1002.gaussMeasure)|
      ≤ C * (ρ' ^ M * K ^ 2) := by
    refine le_trans hmixj ?_
    have h1 : C * ρ ^ M ≤ C * ρ' ^ M := mul_le_mul_of_nonneg_left hstep2 hC.le
    calc C * ρ ^ M * K ^ 2 ≤ C * ρ' ^ M * K ^ 2 := mul_le_mul_of_nonneg_right h1 hK2
      _ = C * (ρ' ^ M * K ^ 2) := by ring
  rw [← hinv] at hB
  have hsplit : (∫ α in Ioo (0 : ℝ) 1, g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁))
      - (∫ x, g₀ x ∂Erdos1002.gaussMeasure) * (∫ x, g₁ x ∂Erdos1002.gaussMeasure)
      = ((∫ α in Ioo (0 : ℝ) 1, g₀ (gaussIter α t₀) * g₁ (gaussIter α t₁))
          - ∫ y, G y ∂Erdos1002.gaussMeasure)
        + ((∫ y, G y ∂Erdos1002.gaussMeasure)
          - (∫ x, g₀ x ∂Erdos1002.gaussMeasure) * (∫ x, g₁ x ∂Erdos1002.gaussMeasure)) := by
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  exact le_trans (add_le_add hA hB) (le_of_eq (by ring))

/-! ## 2. Digit cylinders are order-convex, hence their indicators are BV -/

lemma gaussIter_zero_left (i : ℕ) : gaussIter (0 : ℝ) i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      show gaussMap^[i + 1] (0 : ℝ) = 0
      rw [Function.iterate_succ_apply']
      show gaussMap (gaussIter (0 : ℝ) i) = 0
      rw [ih]
      simp [gaussMap, Int.fract]

lemma digit_zero_left (i : ℕ) : digit (0 : ℝ) i = 0 := by
  show ⌊(gaussIter (0 : ℝ) i)⁻¹⌋.toNat = 0
  rw [gaussIter_zero_left]
  simp

lemma digit_succ (y : ℝ) (i : ℕ) : digit y (i + 1) = digit (gaussMap y) i := by
  show ⌊(gaussIter y (i + 1))⁻¹⌋.toNat = ⌊(gaussIter (gaussMap y) i)⁻¹⌋.toNat
  have h : gaussIter y (i + 1) = gaussIter (gaussMap y) i := by
    show gaussMap^[i + 1] y = gaussMap^[i] (gaussMap y)
    rw [Function.iterate_succ_apply]
  rw [h]

lemma one_lt_inv_of_mem {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 1 < y⁻¹ := by
  have hpos : 0 < y⁻¹ := inv_pos.2 hy.1
  have hmul : y * y⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hy.1)
  nlinarith [hy.1, hy.2]

lemma digit_zero_floor {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ((digit y 0 : ℕ) : ℤ) = ⌊y⁻¹⌋ := by
  have h1 : (1 : ℤ) ≤ ⌊y⁻¹⌋ := by
    have := one_lt_inv_of_mem hy
    exact Int.le_floor.2 (by exact_mod_cast this.le)
  show ((⌊(gaussIter y 0)⁻¹⌋.toNat : ℕ) : ℤ) = ⌊y⁻¹⌋
  have hg : gaussIter y 0 = y := rfl
  rw [hg]
  exact Int.toNat_of_nonneg (by omega)

lemma one_le_digit_zero {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 1 ≤ digit y 0 := by
  have h := digit_zero_floor hy
  have h1 : (1 : ℤ) ≤ ⌊y⁻¹⌋ := by
    have := one_lt_inv_of_mem hy
    exact Int.le_floor.2 (by exact_mod_cast this.le)
  omega

lemma gaussMap_eq_sub {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    gaussMap y = y⁻¹ - ((digit y 0 : ℕ) : ℝ) := by
  have h := digit_zero_floor hy
  show Int.fract y⁻¹ = _
  rw [Int.fract]
  congr 1
  exact_mod_cast h.symm

lemma gaussMap_nonneg (y : ℝ) : 0 ≤ gaussMap y := Int.fract_nonneg _

lemma gaussMap_lt_one (y : ℝ) : gaussMap y < 1 := Int.fract_lt_one _

/-- **Digit cylinders are order-convex.**  If `y ≤ z ≤ y'` with `y, y'` in the
unit interval sharing their first `d` continued-fraction digits, then `z`
shares them too. -/
lemma digit_between : ∀ (d : ℕ) (y z y' : ℝ), y ∈ Ioo (0 : ℝ) 1 → y' ∈ Ioo (0 : ℝ) 1 →
    y ≤ z → z ≤ y' → (∀ i, i < d → digit y i = digit y' i) →
    ∀ i, i < d → digit z i = digit y i := by
  intro d
  induction d with
  | zero => intro y z y' _ _ _ _ _ i hi; omega
  | succ d ih =>
      intro y z y' hy hy' h1 h2 h i hi
      have hz : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hy.1 h1, lt_of_le_of_lt h2 hy'.2⟩
      -- the inverses are ordered the other way round
      have hiv1 : z⁻¹ ≤ y⁻¹ := by
        have hy0 := hy.1
        gcongr
      have hiv2 : y'⁻¹ ≤ z⁻¹ := by
        have hz0 := hz.1
        gcongr
      have hfy : ((digit y 0 : ℕ) : ℤ) = ⌊y⁻¹⌋ := digit_zero_floor hy
      have hfy' : ((digit y' 0 : ℕ) : ℤ) = ⌊y'⁻¹⌋ := digit_zero_floor hy'
      have hfz : ((digit z 0 : ℕ) : ℤ) = ⌊z⁻¹⌋ := digit_zero_floor hz
      have heq0 : digit y 0 = digit y' 0 := h 0 (by omega)
      have hfl1 : ⌊z⁻¹⌋ ≤ ⌊y⁻¹⌋ := Int.floor_mono hiv1
      have hfl2 : ⌊y'⁻¹⌋ ≤ ⌊z⁻¹⌋ := Int.floor_mono hiv2
      have hq : digit z 0 = digit y 0 := by
        have hyy' : ⌊y'⁻¹⌋ = ⌊y⁻¹⌋ := by rw [← hfy, ← hfy', heq0]
        omega
      -- the images under the Gauss map are ordered
      have hgy : gaussMap y = y⁻¹ - ((digit y 0 : ℕ) : ℝ) := gaussMap_eq_sub hy
      have hgz : gaussMap z = z⁻¹ - ((digit y 0 : ℕ) : ℝ) := by
        rw [gaussMap_eq_sub hz, hq]
      have hgy' : gaussMap y' = y'⁻¹ - ((digit y 0 : ℕ) : ℝ) := by
        rw [gaussMap_eq_sub hy', ← heq0]
      have hord1 : gaussMap z ≤ gaussMap y := by rw [hgy, hgz]; linarith
      have hord2 : gaussMap y' ≤ gaussMap z := by rw [hgz, hgy']; linarith
      -- the two cases
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact hq
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hi' : i' < d := by omega
        rw [digit_succ, digit_succ]
        by_cases hgy0 : gaussMap y = 0
        · have hz0 : gaussMap z = 0 :=
            le_antisymm (by rw [← hgy0]; exact hord1) (gaussMap_nonneg z)
          rw [hz0, hgy0]
        · have hyIoo : gaussMap y ∈ Ioo (0 : ℝ) 1 :=
            ⟨lt_of_le_of_ne (gaussMap_nonneg y) (Ne.symm hgy0), gaussMap_lt_one y⟩
          by_cases hgy'0 : gaussMap y' = 0
          · exfalso
            have h1d : digit y 1 = digit y' 1 := h 1 (by omega)
            rw [digit_succ, digit_succ, hgy'0, digit_zero_left] at h1d
            have := one_le_digit_zero hyIoo
            omega
          · have hy'Ioo : gaussMap y' ∈ Ioo (0 : ℝ) 1 :=
              ⟨lt_of_le_of_ne (gaussMap_nonneg y') (Ne.symm hgy'0), gaussMap_lt_one y'⟩
            have hstep : ∀ k, k < d → digit (gaussMap y') k = digit (gaussMap y) k := by
              intro k hk
              rw [← digit_succ, ← digit_succ]
              exact (h (k + 1) (by omega)).symm
            have := ih (gaussMap y') (gaussMap z) (gaussMap y) hy'Ioo hyIoo
              hord2 hord1 hstep i' hi'
            rw [this]
            exact hstep i' hi'

/-- The digit cylinder as a subset of the open unit interval. -/
def cylSet (d : ℕ) (v : ℕ → ℕ) : Set ℝ :=
  {y ∈ Ioo (0 : ℝ) 1 | ∀ i, i < d → digit y i = v i}

lemma ordConnected_cylSet (d : ℕ) (v : ℕ → ℕ) : (cylSet d v).OrdConnected := by
  constructor
  intro y hy y' hy' z hz
  refine ⟨⟨lt_of_lt_of_le hy.1.1 hz.1, lt_of_le_of_lt hz.2 hy'.1.2⟩, ?_⟩
  intro i hi
  have hbetw := digit_between d y z y' hy.1 hy'.1 hz.1 hz.2
    (fun k hk => by rw [hy.2 k hk, hy'.2 k hk]) i hi
  rw [hbetw]
  exact hy.2 i hi

/-! ### The variation of the indicator of an order-convex set -/

lemma eVariationOn_indicator_up {U : Set ℝ} (hU : ∀ x y : ℝ, x ≤ y → x ∈ U → y ∈ U) :
    eVariationOn (U.indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
  have hval : ∀ x : ℝ, U.indicator (fun _ => (1 : ℝ)) x = 0
      ∨ U.indicator (fun _ => (1 : ℝ)) x = 1 := by
    intro x
    by_cases hx : x ∈ U
    · exact Or.inr (Set.indicator_of_mem hx _)
    · exact Or.inl (Set.indicator_of_notMem hx _)
  have hmono : MonotoneOn (U.indicator (fun _ => (1 : ℝ))) (Icc (0 : ℝ) 1) := by
    intro x _ y _ hxy
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hU x y hxy hx)]
    · rw [Set.indicator_of_notMem hx]
      rcases hval y with h | h
      · rw [h]
      · rw [h]; norm_num
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hle := hmono.eVariationOn_le h0 h1
  rw [Set.inter_self] at hle
  refine le_trans (le_trans (eVariationOn.mono _ Ioo_subset_Icc_self) hle)
    (ENNReal.ofReal_le_ofReal ?_)
  rcases hval 1 with ha | ha <;> rcases hval 0 with hb | hb <;> rw [ha, hb] <;> norm_num

/-- **The indicator of an order-convex set has variation at most `2`.**
Mathlib has the monotone case only; the Jordan decomposition used here is
`1_S = 1_{↑S} − 1_{↑S ∖ S}`, both summands being indicators of up-sets. -/
lemma eVariationOn_indicator_ordConnected {S : Set ℝ} (hS : S.OrdConnected) :
    eVariationOn (S.indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal 2 := by
  classical
  set U : Set ℝ := {x | ∃ s ∈ S, s ≤ x} with hUdef
  set V : Set ℝ := {x | (∃ s ∈ S, s < x) ∧ x ∉ S} with hVdef
  have hUup : ∀ x y : ℝ, x ≤ y → x ∈ U → y ∈ U := by
    rintro x y hxy ⟨s, hs, hsx⟩
    exact ⟨s, hs, le_trans hsx hxy⟩
  have hVup : ∀ x y : ℝ, x ≤ y → x ∈ V → y ∈ V := by
    rintro x y hxy ⟨⟨s, hs, hsx⟩, hxS⟩
    refine ⟨⟨s, hs, lt_of_lt_of_le hsx hxy⟩, ?_⟩
    intro hyS
    exact hxS (hS.out hs hyS ⟨le_of_lt hsx, hxy⟩)
  have hpt : ∀ x : ℝ, S.indicator (fun _ => (1 : ℝ)) x
      = U.indicator (fun _ => (1 : ℝ)) x + (-1) * V.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem (show x ∈ U from ⟨x, hxS, le_rfl⟩),
        Set.indicator_of_notMem (show x ∉ V from fun hv => hv.2 hxS)]
      ring
    · rw [Set.indicator_of_notMem hxS]
      by_cases hxU : x ∈ U
      · obtain ⟨s, hs, hsx⟩ := hxU
        have hsx' : s < x := lt_of_le_of_ne hsx (fun he => hxS (he ▸ hs))
        rw [Set.indicator_of_mem (show x ∈ U from ⟨s, hs, hsx⟩),
          Set.indicator_of_mem (show x ∈ V from ⟨⟨s, hs, hsx'⟩, hxS⟩)]
        ring
      · have hxV : x ∉ V := by
          rintro ⟨⟨s, hs, hsx⟩, -⟩
          exact hxU ⟨s, hs, le_of_lt hsx⟩
        rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxV]
        ring
  have heq : eVariationOn (S.indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1)
      = eVariationOn (fun x => U.indicator (fun _ => (1 : ℝ)) x
          + (-1) * V.indicator (fun _ => (1 : ℝ)) x) (Ioo (0 : ℝ) 1) :=
    eVariationOn.eq_of_eqOn (fun x _ => hpt x)
  rw [heq]
  refine le_trans (BVLasotaYorke.eVariationOn_add_le _ _ _) ?_
  have hB : eVariationOn (fun x => (-1 : ℝ) * V.indicator (fun _ => (1 : ℝ)) x)
      (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
    refine le_trans (MixingBV.eVariationOn_const_mul_le (-1) _ _) ?_
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs, ENNReal.ofReal_one, one_mul]
    simpa using eVariationOn_indicator_up hVup
  calc eVariationOn (U.indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1)
        + eVariationOn (fun x => (-1 : ℝ) * V.indicator (fun _ => (1 : ℝ)) x)
            (Ioo (0 : ℝ) 1)
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 :=
        add_le_add (eVariationOn_indicator_up hUup) hB
    _ = ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

/-! ## 3. The zero-mode digit observable -/

/-- The radius-`R` word as a function `ℕ → ℕ` (padded by `0`). -/
def wordFn (R : ℕ) (w : Fin (2 * R) → ℕ) : ℕ → ℕ :=
  fun i => if h : i < 2 * R then w ⟨i, h⟩ else 0

/-- The depth-`2R` digit cylinder of `w`, as a subset of `ℝ` (no unit-interval
restriction: this is what makes the reindexing identity below exact). -/
def wordSet (R : ℕ) (w : Fin (2 * R) → ℕ) : Set ℝ :=
  {y : ℝ | ∀ i, i < 2 * R → digit y i = wordFn R w i}

/-- The zero-mode observable of §4: the indicator of a depth-`2R` digit
cylinder. -/
def cylObs (R : ℕ) (w : Fin (2 * R) → ℕ) : ℝ → ℝ :=
  (wordSet R w).indicator (fun _ => (1 : ℝ))

lemma wordSet_inter_Ioo (R : ℕ) (w : Fin (2 * R) → ℕ) :
    ∀ y ∈ Ioo (0 : ℝ) 1, (y ∈ wordSet R w ↔ y ∈ Prop41.cylinder (2 * R) (wordFn R w)) := by
  intro y hy
  constructor
  · intro h; exact ⟨hy, h⟩
  · intro h; exact h.2

lemma measurableSet_wordSet (R : ℕ) (w : Fin (2 * R) → ℕ) :
    MeasurableSet (wordSet R w) := by
  have h : wordSet R w
      = ⋂ i ∈ (Set.Iio (2 * R)), {y : ℝ | digit y i = wordFn R w i} := by
    ext y
    simp [wordSet]
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun i _ => Prop42.measurable_digitNat i (measurableSet_singleton _))

lemma measurable_cylObs (R : ℕ) (w : Fin (2 * R) → ℕ) : Measurable (cylObs R w) :=
  (measurable_const.indicator (measurableSet_wordSet R w))

lemma cylObs_bound (R : ℕ) (w : Fin (2 * R) → ℕ) (y : ℝ) : |cylObs R w y| ≤ 2 := by
  unfold cylObs
  by_cases h : y ∈ wordSet R w
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

lemma cylObs_bv (R : ℕ) (w : Fin (2 * R) → ℕ) :
    Prop41.BVBoundedBy 2 (cylObs R w) := by
  refine ⟨fun x _ => cylObs_bound R w x, ?_⟩
  have heq : eVariationOn (cylObs R w) (Ioo (0 : ℝ) 1)
      = eVariationOn ((Prop41.cylinder (2 * R) (wordFn R w)).indicator (fun _ => (1 : ℝ)))
          (Ioo (0 : ℝ) 1) := by
    refine eVariationOn.eq_of_eqOn (fun x hx => ?_)
    unfold cylObs
    by_cases h : x ∈ wordSet R w
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem ((wordSet_inter_Ioo R w x hx).1 h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (fun hc => h ((wordSet_inter_Ioo R w x hx).2 hc))]
  rw [heq]
  exact eVariationOn_indicator_ordConnected (ordConnected_cylSet (2 * R) (wordFn R w))

lemma digit_gaussIter (α : ℝ) (m i : ℕ) : digit (gaussIter α m) i = digit α (m + i) := by
  show ⌊(gaussIter (gaussIter α m) i)⁻¹⌋.toNat = ⌊(gaussIter α (m + i))⁻¹⌋.toNat
  rw [Prop41Final.gaussIter_add]

/-- **The window cylinder of §4, read as an observable along the orbit.** -/
lemma cylObs_windowWord (R j : ℕ) (hj : R ≤ j) (w : Fin (2 * R) → ℕ) (α : ℝ) :
    cylObs R w (gaussIter α (j - R))
      = (P42Cases.cyl R w j).indicator (fun _ => (1 : ℝ)) α := by
  have hmem : gaussIter α (j - R) ∈ wordSet R w ↔ α ∈ P42Cases.cyl R w j := by
    constructor
    · intro h
      show windowWord R α j = w
      funext t
      have ht := h (t : ℕ) t.isLt
      rw [digit_gaussIter] at ht
      show digit α (j + (t : ℕ) - R) = w t
      have hidx : j + (t : ℕ) - R = (j - R) + (t : ℕ) := by omega
      rw [hidx, ht]
      simp [wordFn, t.isLt]
    · intro h
      have hw : windowWord R α j = w := h
      intro i hi
      rw [digit_gaussIter]
      have hidx : (j - R) + i = j + i - R := by omega
      rw [hidx]
      have := congrFun hw ⟨i, hi⟩
      rw [show digit α (j + i - R) = windowWord R α j ⟨i, hi⟩ from rfl, this]
      simp [wordFn, hi]
  unfold cylObs
  by_cases h : α ∈ P42Cases.cyl R w j
  · rw [Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hc => h (hmem.1 hc)), Set.indicator_of_notMem h]

lemma integral_cylObs_mul (R j k : ℕ) (hj : R ≤ j) (hk : R ≤ k)
    (w w' : Fin (2 * R) → ℕ) :
    (∫ α in Ioo (0 : ℝ) 1,
        cylObs R w (gaussIter α (j - R)) * cylObs R w' (gaussIter α (k - R)))
      = volume.real (Ioo (0 : ℝ) 1 ∩ (P42Cases.cyl R w j ∩ P42Cases.cyl R w' k)) := by
  classical
  have hmA := P42Cases.measurableSet_cyl R w j
  have hmB := P42Cases.measurableSet_cyl R w' k
  have hpt : ∀ α : ℝ, cylObs R w (gaussIter α (j - R)) * cylObs R w' (gaussIter α (k - R))
      = (P42Cases.cyl R w j ∩ P42Cases.cyl R w' k).indicator (fun _ => (1 : ℝ)) α := by
    intro α
    rw [cylObs_windowWord R j hj, cylObs_windowWord R k hk,
      Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    by_cases h1 : α ∈ P42Cases.cyl R w j <;> by_cases h2 : α ∈ P42Cases.cyl R w' k <;>
      simp [h1, h2]
  simp only [hpt]
  rw [MeasureTheory.integral_indicator_const _ (hmA.inter hmB),
    measureReal_restrict_apply (hmA.inter hmB)]
  rw [Set.inter_comm (P42Cases.cyl R w j ∩ P42Cases.cyl R w' k) (Ioo (0 : ℝ) 1)]
  simp

lemma integral_cylObs_gauss (R : ℕ) (w : Fin (2 * R) → ℕ) :
    (∫ x, cylObs R w x ∂Erdos1002.gaussMeasure)
      = (Erdos1002.gaussMeasure (Prop41.cylinder (2 * R) (wordFn R w))).toReal := by
  have hset : Erdos1002.gaussMeasure (wordSet R w)
      = Erdos1002.gaussMeasure (Prop41.cylinder (2 * R) (wordFn R w)) := by
    refine measure_congr ?_
    rw [Filter.eventuallyEq_set]
    filter_upwards [Prop41Final.gaussMeasure_ae_Ioo] with y hy
    exact wordSet_inter_Ioo R w y hy
  rw [cylObs, MeasureTheory.integral_indicator_const _ (measurableSet_wordSet R w),
    smul_eq_mul, mul_one]
  show (Erdos1002.gaussMeasure (wordSet R w)).toReal = _
  rw [hset]

/-! ## 4. The one remaining input: the natural-extension marginal

`P42Cases.cylProb R w` is the `μ̂₀`-mass of the *natural-extension* cylinder
`{(x,y) : natExtWord R (x,y) = w}` (times the full Haar mass of `T²`), i.e.

`∫∫_{E_y × E_x} dx dy / (log 2 (1 + xy)²)`,

where `E_x` is the depth-`R` future cylinder of `(w_R,…,w_{2R−1})` and `E_y`
the depth-`R` past cylinder of `(w_{R−1},…,w_0)` read in reverse.  Kwon uses
without comment that this equals the Gauss measure of the *joint* depth-`2R`
cylinder of `w`; that is the defining property of the natural extension.

It is TRUE, and the index matching has been checked here: `natExtWord`'s
future half (`t ≥ R`) reads `digit x (t−R)`, i.e. `w_R,…,w_{2R−1} = a₁(x),…,a_R(x)`,
and its past half (`t < R`) reads `digit y (R−1−t)`, i.e.
`w_0,…,w_{R−1} = a_R(y),…,a₁(y)`; under the two-sided stationary model these are
`a_{1−R},…,a_0,a_1,…,a_R`, one consecutive block of length `2R`, whose law is the
law of `a_1,…,a_{2R}` under `ν`.  This is also exactly the indexing of
`windowWord R α j` (`cylObs_windowWord` above), so nothing is off by one.

REDUCTION (not carried out here).  `{z | natExtWord R z.1 = w}` factorises as
`(F_x ×ˢ F_y) ×ˢ univ` with `F_x` the depth-`R` cylinder of `(w_R,…,w_{2R−1})` and
`F_y` the depth-`R` cylinder of `(w_{R−1},…,w_0)`, and the `T²` factor has full
mass, so Fubini turns `cylProb R w` into the plain two-dimensional integral above.

OBSTRUCTION.  No natural-extension marginal theory exists in this tree:
`natExtWord` occurs only in `Section4.lean`, `Prop42.lean`, `MonomialCore.lean`
and `P42Cases.lean`, and the 35-module Wang substrate has no two-sided Gauss
model.  The computation needed is the classical one, with
`E_y = [a,a']`, `E_x = [b,b']`,
`∫∫ dx dy/(1+xy)² = log((1+b'a')(1+ba)) − log((1+ba')(1+b'a))`,
which must be matched against `∫_{C_w} du/(1+u)` through the continuant
identities of `AntiConcentration` (`quad`, `quad_det`, `quad_reverse`,
`gaussInverseWord_eq_quad`).  Everything else in case 1 of Kwon's proof of
Proposition 4.2 is proved outright below. -/

theorem natExt_marginal (R : ℕ) (w : Fin (2 * R) → ℕ) :
    P42Cases.cylProb R w
      = (Erdos1002.gaussMeasure (Prop41.cylinder (2 * R) (wordFn R w))).toReal := by
  sorry

/-! ## 5. Case 1 of the proof of Proposition 4.2 -/

/-- Token-identical restatement of `Kwon1002.P42Cases.zeroMode_cylinder_mixing`,
now **proved** from `lebesgue_two_block` and `natExt_marginal`. -/
theorem zeroMode_cylinder_mixing' (R : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ w' ∈ Wv, ∀ p ∈ bulkPairs n,
        C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        |volume.real (Ioo (0 : ℝ) 1 ∩ (P42Cases.cyl R w p.1 ∩ P42Cases.cyl R w' p.2))
            - P42Cases.cylProb R w * P42Cases.cylProb R w'|
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  classical
  obtain ⟨C₀, ρ₀, hC₀, hρ₀0, hρ₀1, hmix⟩ := lebesgue_two_block
  refine ⟨max 1 (4 * C₀ / ρ₀), 1, ρ₀, lt_of_lt_of_le one_pos (le_max_left _ _),
    one_pos, hρ₀0, hρ₀1, ?_⟩
  set C : ℝ := max 1 (4 * C₀ / ρ₀) with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCbig : 4 * C₀ / ρ₀ ≤ C := le_max_right _ _
  filter_upwards [P42Cases.tendsto_Hscale.eventually_ge_atTop 1,
    (P42Cases.tendsto_Hscale.const_mul_atTop
      (by norm_num : (0 : ℝ) < 199)).eventually_ge_atTop (R : ℝ)] with n hH1 hHR
  intro w hw w' hw' p hp hgap
  have hH0 : (0 : ℝ) ≤ Hscale n := by linarith
  set H : ℝ := Hscale n with hHdef
  set M : ℕ := ⌊H⌋₊ with hMdef
  have hMle : (M : ℝ) ≤ H := Nat.floor_le hH0
  have hMge : H - 1 < (M : ℝ) := by
    have := Nat.lt_floor_add_one H
    push_cast at this ⊢
    linarith
  -- the two block times lie in the bulk
  have hp1 : p.1 ∈ bulkJ n := MonomialCore.mem_bulkPairs_fst hp
  have hbulk : 200 * H ≤ (p.1 : ℝ) := ((Finset.mem_filter.1 hp1).2).1
  have hlt : p.1 < p.2 := MonomialCore.mem_bulkPairs_lt hp
  have hRp1 : R ≤ p.1 := by
    have : (R : ℝ) ≤ (p.1 : ℝ) := by linarith
    exact_mod_cast this
  have hRp2 : R ≤ p.2 := le_trans hRp1 hlt.le
  -- the separation hypotheses of `lebesgue_two_block`
  have hsep0 : M ≤ p.1 - R := by
    have hcast : ((p.1 - R : ℕ) : ℝ) = (p.1 : ℝ) - (R : ℝ) := by
      push_cast [Nat.cast_sub hRp1]; ring
    have : (M : ℝ) ≤ ((p.1 - R : ℕ) : ℝ) := by rw [hcast]; linarith
    exact_mod_cast this
  have hsep1 : (p.1 - R) + M ≤ p.2 - R := by
    have hcast2 : ((p.2 - p.1 : ℕ) : ℝ) = (p.2 : ℝ) - (p.1 : ℝ) := by
      push_cast [Nat.cast_sub hlt.le]; ring
    have hMlt : (M : ℝ) ≤ ((p.2 - p.1 : ℕ) : ℝ) := by
      rw [hcast2]
      nlinarith [hgap, hMle, hH0, hC1]
    have hMn : M ≤ p.2 - p.1 := by exact_mod_cast hMlt
    omega
  -- the mixing estimate
  have hkey := hmix M (p.1 - R) (p.2 - R) (cylObs R w) (cylObs R w') 2 (by norm_num)
    (measurable_cylObs R w) (measurable_cylObs R w')
    (cylObs_bound R w) (cylObs_bound R w') (cylObs_bv R w) (cylObs_bv R w') hsep0 hsep1
  rw [integral_cylObs_mul R p.1 p.2 hRp1 hRp2 w w',
    integral_cylObs_gauss, integral_cylObs_gauss,
    ← natExt_marginal R w, ← natExt_marginal R w'] at hkey
  refine le_trans hkey ?_
  -- the error shape
  have hrpow : ρ₀ ^ M = ρ₀ ^ ((M : ℕ) : ℝ) := (Real.rpow_natCast ρ₀ M).symm
  have hstep : ρ₀ ^ ((M : ℕ) : ℝ) ≤ ρ₀ ^ (H - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hρ₀0 hρ₀1.le (by linarith)
  have hsplit : ρ₀ ^ (H - 1) = ρ₀ ^ H / ρ₀ := by
    rw [Real.rpow_sub hρ₀0, Real.rpow_one]
  have hHpow : (0 : ℝ) < ρ₀ ^ H := Real.rpow_pos_of_pos hρ₀0 H
  have hmain : C₀ * ρ₀ ^ M * (2 : ℝ) ^ 2 ≤ C * ρ₀ ^ (1 * H) := by
    rw [one_mul, hrpow]
    have h1 : C₀ * ρ₀ ^ ((M : ℕ) : ℝ) * (2 : ℝ) ^ 2 ≤ C₀ * (ρ₀ ^ H / ρ₀) * 4 := by
      have := le_trans hstep (le_of_eq hsplit)
      nlinarith [hC₀, Real.rpow_pos_of_pos hρ₀0 ((M : ℕ) : ℝ)]
    refine le_trans h1 ?_
    have h2 : C₀ * (ρ₀ ^ H / ρ₀) * 4 = (4 * C₀ / ρ₀) * ρ₀ ^ H := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right hCbig hHpow.le
  have hpos1 : (0 : ℝ) < Real.exp (-1 * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have hpos2 : (0 : ℝ) < Real.exp (-1 * H) := Real.exp_pos _
  have hC0' : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  nlinarith [hmain, hpos1, hpos2, hC0']

/-- Token-identical restatement of `Kwon1002.MonomialCore.zeroMode_gauss_mixing`
(case 1 of Kwon's proof of Proposition 4.2), now **proved**. -/
theorem zeroMode_gauss_mixing' (R : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ w' ∈ Wv, ∀ p ∈ bulkPairs n,
        C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w 0 0 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)
            - Prop42.monoStationary R w 0 0 * Prop42.monoStationary R w' 0 0‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  obtain ⟨C, c, ρ, hC, hc, hρ0, hρ1, hmix⟩ := zeroMode_cylinder_mixing' R Wu Wv
  refine ⟨C, c, ρ, hC, hc, hρ0, hρ1, ?_⟩
  filter_upwards [hmix] with n hn
  intro w hw w' hw' p hp hgap
  rw [P42Cases.zeroMode_norm_eq]
  exact hn w hw w' hw' p hp hgap

end

end PhaseBounds

/-! ## 6. Token-identical restatements

Both blocks below are byte-for-byte copies of their targets, `zeroMode_gauss_mixing`
of `Kwon1002/MonomialCore.lean` (lines 371-379) and `zeroMode_cylinder_mixing` of
`Kwon1002/P42Cases.lean` (lines 201-208), with only the theorem *name* primed, placed
inside the target's own namespace so that `cyl`, `cylProb`, `bulkPairs`, `Hscale`,
`Lnorm`, `Prop42.monoAt`, `Prop42.monoStationary` resolve exactly as they do there. -/

namespace MonomialCore

noncomputable section

theorem zeroMode_gauss_mixing' (R : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ w' ∈ Wv, ∀ p ∈ bulkPairs n,
        C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w 0 0 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)
            - Prop42.monoStationary R w 0 0 * Prop42.monoStationary R w' 0 0‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) :=
  PhaseBounds.zeroMode_gauss_mixing' R Wu Wv

end

end MonomialCore

namespace P42Cases

noncomputable section

theorem zeroMode_cylinder_mixing' (R : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ w' ∈ Wv, ∀ p ∈ bulkPairs n,
        C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        |volume.real (Ioo (0 : ℝ) 1 ∩ (cyl R w p.1 ∩ cyl R w' p.2))
            - cylProb R w * cylProb R w'|
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) :=
  PhaseBounds.zeroMode_cylinder_mixing' R Wu Wv

end

end P42Cases

end Kwon1002
