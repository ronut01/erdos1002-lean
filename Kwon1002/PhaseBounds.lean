import Kwon1002.P42Cases
import Kwon1002.Prop41Final
import Kwon1002.NatExtMixing
import Kwon1002.CharacterReduction
import Kwon1002.CylinderPhase

/-!
# PhaseBounds, scratch file (agent `monocore`)

TARGETS: `MonomialCore.zeroMode_gauss_mixing`, `MonomialCore.laterMode_phase_bound`,
`MonomialCore.earlierMode_phase_bound`, `P42Cases.zeroMode_cylinder_mixing`.

## What is achieved

**Case 1 of Kwon's proof of Proposition 4.2 is proved, outright.**  Both
`MonomialCore.zeroMode_gauss_mixing` and `P42Cases.zeroMode_cylinder_mixing`
are reproduced token-identically (§8, diffed byte-for-byte against
`MonomialCore.lean` 371-379 and `P42Cases.lean` 201-208, only the name primed)
and **proved with no sorried input**: the one statement this file used to
assume, `natExt_marginal`, is now proved in §4 from the natural-extension
layer (`hatMu0_eq_prod`, `natExtMap_measurePreserving`, `hatNu_fst_marginal`,
`gaussMarginal_eq_gaussMeasure`) by pushing the two-sided digit window into
the future coordinate with `R` applications of the measure-preserving
natural-extension map — no density integral and no continuant identity is
needed.

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
  the `2R`-cylinder"*, **removed**: `natExt_marginal` (§4) is proved.  The
  obstruction this file originally recorded ("no natural-extension marginal
  theory exists in the tree") was retired by `NatExtMeasure.lean`,
  `NatExtInvariance.lean` and `NatExtMixing.lean`; the marginal follows from
  invariance alone (see §4's docstring for the four-step route), plus the
  digit bookkeeping of §4a, which is new here.

## Sorried results consumed

**None.**  Nothing sorried is used: the
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
`[propext, Classical.choice, Quot.sound]`.  The same audit was re-run after
§4 was proved, on all twelve new results (`branchPoint_mem`,
`digit_branchPoint_zero`, `gaussMap_branchPoint`, `digit_branchPoint_succ`,
`natExtIter_snd`, `natExtWord_iterate`, `natExtMap_iterate_mem_word_iff`,
`measurableSet_natExtWordBase`, `ae_irrational_fst`, `natExt_marginal`) and
on `zeroMode_cylinder_mixing'` and `zeroMode_gauss_mixing'`: each now depends
on exactly `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`
anywhere in this file**.  The audit block has been removed.

## The two phase bounds: sub-steps proved, (20)-shaped residual (finding)

`laterMode_phase_bound` and `earlierMode_phase_bound` remain open; §§6-7
below now prove, outright, their (20)-free named sub-steps — the
depth-ordering side conditions of the v8 prefix refinement, the pair
oscillatory form of the two-block integrand, the frequency freezing, the
explicit-`O(1)` exponent identities at both cuts, and both retained-set
`q²`-vs-`n|Q|` inequalities — see the §7 header for the exact residual.
The original finding stands and is kept verbatim below.
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

/-! ## 4. The natural-extension marginal, proved

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

PROOF ROUTE (the one carried out below).  The OBSTRUCTION this section used
to record — "no natural-extension marginal theory exists in this tree" — is
obsolete: the natural-extension layer has since been built
(`NatExtMeasure.lean`, `NatExtInvariance.lean`, `NatExtMixing.lean`), and it
lets the marginal be computed **without any density integral at all**:

1. `hatMu0_eq_prod` integrates the `T²` factor out (`Measure.map_fst_prod`,
   the fibre is a probability measure), so `cylProb R w = ν̂(S)` with
   `S = {(x,y) : natExtWord R (x,y) = w}`.
2. `NatExtInvariance.natExtMap_measurePreserving`, iterated `R` times, gives
   `ν̂(S) = ν̂(σ^{-R} S)`.
3. The digit bookkeeping (§4a below): for `x ∈ (0,1)` irrational and
   `y ∈ (0,1)`, the `R`-th image `σ^R(x,y)` has past digits
   `a_R(x), …, a_1(x)` and future digits `a_{R+1}(x), a_{R+2}(x), …`, so
   `natExtWord R (σ^R(x,y)) = w ↔ x ∈ wordSet R w`, with `y` unconstrained.
   Hence `σ^{-R} S =ᵐ[ν̂] wordSet R w ×ˢ univ` (a.e. because the bookkeeping
   needs `x` irrational, which holds `ν̂`-a.e., `ν̂ ≪ Leb`).
4. `NatExtMeasure.hatNu_fst_marginal` + `NatExtMixing.gaussMarginal_eq_gaussMeasure`
   turn `ν̂(wordSet R w ×ˢ univ)` into `γ(wordSet R w)`, and
   `gaussMeasure_ae_Ioo` + `wordSet_inter_Ioo` into `γ` of the `Prop41`
   cylinder.

This is the classical proof that the marginal of the natural extension at a
consecutive block is the stationary one-sided law: push the two-sided window
into the future coordinate by invariance.  No continuant identity and no
evaluation of `∫∫ dx dy/(1+xy)²` is needed. -/

/-! ### 4a. Digit bookkeeping for the iterated natural-extension map -/

/-- One inverse-branch point of the Gauss map: for `1 ≤ d` and `Y ∈ (0,1)`,
the point `(d + Y)⁻¹` lies in `(0,1)`. -/
lemma branchPoint_mem {d : ℕ} (hd : 1 ≤ d) {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ((d : ℝ) + Y)⁻¹ ∈ Ioo (0 : ℝ) 1 := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (d : ℝ) + Y := by linarith [hY.1]
  have h1 : (1 : ℝ) < (d : ℝ) + Y := by linarith [hY.1]
  exact ⟨inv_pos.2 hpos, (inv_lt_one₀ hpos).2 h1⟩

/-- The first digit of the branch point `(d + Y)⁻¹` is `d`. -/
lemma digit_branchPoint_zero (d : ℕ) {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    digit ((d : ℝ) + Y)⁻¹ 0 = d := by
  have hfl : ⌊(d : ℝ) + Y⌋ = (d : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast; linarith [hY.1]
    · push_cast; linarith [hY.2]
  show ⌊(gaussIter ((d : ℝ) + Y)⁻¹ 0)⁻¹⌋.toNat = d
  rw [gaussIter_zero, inv_inv, hfl, Int.toNat_natCast]

/-- The Gauss map sends the branch point `(d + Y)⁻¹` back to `Y`. -/
lemma gaussMap_branchPoint (d : ℕ) {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    gaussMap ((d : ℝ) + Y)⁻¹ = Y := by
  show Int.fract (((d : ℝ) + Y)⁻¹)⁻¹ = Y
  rw [inv_inv, add_comm, Int.fract_add_natCast]
  exact Int.fract_eq_self.2 ⟨hY.1.le, hY.2⟩

/-- Later digits of the branch point are the digits of `Y`. -/
lemma digit_branchPoint_succ (d : ℕ) {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    digit ((d : ℝ) + Y)⁻¹ (k + 1) = digit Y k := by
  rw [digit_succ, gaussMap_branchPoint d hY]

/-- **The past coordinate of the iterated natural-extension map.**  Starting
from an irrational future `x ∈ (0,1)` and any past `y ∈ (0,1)`, after `m`
steps the past coordinate is again in `(0,1)` and its first `m` digits are
`a_m(x), a_{m-1}(x), …, a_1(x)`, i.e. the consumed digits of `x` in reverse
order (deeper digits of the past would read `y`, which stays unconstrained). -/
lemma natExtIter_snd {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hirr : Irrational x)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∀ m : ℕ, (natExtMap^[m] (x, y)).2 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k, k < m → digit (natExtMap^[m] (x, y)).2 k = digit x (m - 1 - k) := by
  intro m
  induction m with
  | zero => exact ⟨hy, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ m ih =>
    obtain ⟨hmem, hdig⟩ := ih
    have hstep : (natExtMap^[m + 1] (x, y)).2
        = ((digit x m : ℝ) + (natExtMap^[m] (x, y)).2)⁻¹ := by
      rw [Function.iterate_succ_apply']
      show ((digit (natExtMap^[m] (x, y)).1 0 : ℝ) + (natExtMap^[m] (x, y)).2)⁻¹ = _
      rw [NatExtMixing.natExtMap_iterate_fst m (x, y)]
      norm_num [digit_gaussIter]
    have hd1 : 1 ≤ digit x m := one_le_digit hx hirr m
    refine ⟨?_, ?_⟩
    · rw [hstep]; exact branchPoint_mem hd1 hmem
    · intro k hk
      rw [hstep]
      cases k with
      | zero =>
        rw [digit_branchPoint_zero (digit x m) hmem]
        rfl
      | succ k =>
        rw [digit_branchPoint_succ (digit x m) hmem, hdig k (by omega)]
        congr 1
        omega

/-- After `R` steps of the natural-extension map, the radius-`R` word of the
image point reads exactly the first `2R` digits of the future coordinate:
the past half of `natExtWord` (`t < R`, read in reverse) recovers
`a_1(x), …, a_R(x)` and the future half (`t ≥ R`) reads
`a_{R+1}(x), …, a_{2R}(x)`. -/
lemma natExtWord_iterate {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hirr : Irrational x)
    (hy : y ∈ Ioo (0 : ℝ) 1) (R : ℕ) (t : Fin (2 * R)) :
    natExtWord R (natExtMap^[R] (x, y)) t = digit x (t : ℕ) := by
  obtain ⟨_, hdig⟩ := natExtIter_snd hx hirr hy R
  show (if (t : ℕ) < R then digit (natExtMap^[R] (x, y)).2 (R - 1 - (t : ℕ))
      else digit (natExtMap^[R] (x, y)).1 ((t : ℕ) - R)) = digit x (t : ℕ)
  by_cases ht : (t : ℕ) < R
  · rw [if_pos ht, hdig (R - 1 - (t : ℕ)) (by omega)]
    congr 1
    omega
  · rw [if_neg ht, NatExtMixing.natExtMap_iterate_fst R (x, y), digit_gaussIter]
    congr 1
    omega

/-- Membership form: `σ^R(x,y)` lies in the `natExtWord`-cylinder of `w` iff
`x` lies in the depth-`2R` digit cylinder of `w` — the past coordinate `y`
is unconstrained. -/
lemma natExtMap_iterate_mem_word_iff {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational x) (hy : y ∈ Ioo (0 : ℝ) 1) (R : ℕ) (w : Fin (2 * R) → ℕ) :
    natExtWord R (natExtMap^[R] (x, y)) = w ↔ x ∈ wordSet R w := by
  constructor
  · intro h i hi
    have hcf := congrFun h ⟨i, hi⟩
    rw [natExtWord_iterate hx hirr hy R ⟨i, hi⟩] at hcf
    rw [hcf]
    simp [wordFn, hi]
  · intro h
    funext t
    rw [natExtWord_iterate hx hirr hy R t]
    have := h (t : ℕ) t.isLt
    rw [this]
    simp [wordFn, t.isLt]

/-- The base-level word cylinder is measurable (the `(ℝ × ℝ)`-level analogue
of `Prop42.measurableSet_natExtWord_eq`). -/
lemma measurableSet_natExtWordBase (R : ℕ) (w : Fin (2 * R) → ℕ) :
    MeasurableSet {p : ℝ × ℝ | natExtWord R p = w} := by
  have h : {p : ℝ × ℝ | natExtWord R p = w}
      = ⋂ t : Fin (2 * R), {p : ℝ × ℝ |
          (if (t : ℕ) < R then digit p.2 (R - 1 - (t : ℕ)) else digit p.1 ((t : ℕ) - R))
            = w t} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, natExtWord, funext_iff]
  rw [h]
  refine MeasurableSet.iInter fun t => ?_
  by_cases ht : (t : ℕ) < R
  · simp only [ht, if_true]
    exact ((Prop42.measurable_digitNat (R - 1 - (t : ℕ))).comp measurable_snd)
      (measurableSet_singleton (w t))
  · simp only [ht, if_false]
    exact ((Prop42.measurable_digitNat ((t : ℕ) - R)).comp measurable_fst)
      (measurableSet_singleton (w t))

/-- Almost every point of the unit square has irrational first coordinate. -/
lemma ae_irrational_fst :
    ∀ᵐ p : ℝ × ℝ ∂((volume : Measure (ℝ × ℝ)).restrict
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)), Irrational p.1 := by
  refine ae_restrict_of_ae ?_
  have h0 : (volume : Measure (ℝ × ℝ))
      (Set.range ((↑) : ℚ → ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod,
      (Set.countable_range _).measure_zero (volume : Measure ℝ), zero_mul]
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) h0
  simp only [Set.mem_setOf_eq, Irrational] at hp
  exact ⟨not_not.mp hp, Set.mem_univ _⟩

/-! ### 4b. The marginal identity -/

/-- **The natural-extension marginal.**  The `μ̂₀`-mass of the two-sided word
cylinder `{natExtWord R · = w}` equals the Gauss measure of the one-sided
depth-`2R` cylinder of `w`.  Proof: integrate out the `T²` fibre
(`hatMu0_eq_prod`), push the two-sided window into the future coordinate with
`R` applications of the measure-preserving `natExtMap` (§4a: the preimage of
the window cylinder is, up to a `ν̂`-null set, `wordSet R w ×ˢ univ`), then
read off the future marginal (`hatNu_fst_marginal`,
`gaussMarginal_eq_gaussMeasure`). -/
theorem natExt_marginal (R : ℕ) (w : Fin (2 * R) → ℕ) :
    P42Cases.cylProb R w
      = (Erdos1002.gaussMeasure (Prop41.cylinder (2 * R) (wordFn R w))).toReal := by
  classical
  set S : Set (ℝ × ℝ) := {p | natExtWord R p = w} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_natExtWordBase R w
  -- step 1: the `T²` fibre integrates out
  have h1 : hatMu0 {z : (ℝ × ℝ) × ℝ × ℝ | natExtWord R z.1 = w} = hatNu S := by
    have hpre : {z : (ℝ × ℝ) × ℝ × ℝ | natExtWord R z.1 = w}
        = Prod.fst ⁻¹' S := rfl
    rw [hpre, ← Measure.map_apply measurable_fst hSmeas, hatMu0_eq_prod,
      Measure.map_fst_prod, measure_univ, one_smul]
  -- step 2: invariance under `R` steps of the natural-extension map
  have h2 : hatNu S = hatNu (natExtMap^[R] ⁻¹' S) :=
    ((NatExtInvariance.natExtMap_measurePreserving.iterate R).measure_preimage
      hSmeas.nullMeasurableSet).symm
  -- step 3: identify the preimage a.e. as `wordSet R w ×ˢ univ`
  have h3 : hatNu (natExtMap^[R] ⁻¹' S) = hatNu (Prod.fst ⁻¹' wordSet R w) := by
    refine measure_congr ?_
    have habs : hatNu ≪ (volume : Measure (ℝ × ℝ)).restrict
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
      have : hatNu = ((volume : Measure (ℝ × ℝ)).restrict
          (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)).withDensity
            (fun p => ENNReal.ofReal (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2))) := rfl
      rw [this]
      exact withDensity_absolutelyContinuous _ _
    have hev : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure (ℝ × ℝ)).restrict
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)),
        p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∧ Irrational p.1 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo),
        ae_irrational_fst] with p h1' h2'
      exact ⟨h1', h2'⟩
    have hev' : ∀ᵐ p : ℝ × ℝ ∂hatNu,
        p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∧ Irrational p.1 := by
      rw [ae_iff] at hev ⊢
      exact habs hev
    rw [Filter.eventuallyEq_set]
    filter_upwards [hev'] with p hp
    obtain ⟨⟨hx, hy⟩, hirr⟩ := hp
    show natExtMap^[R] p ∈ S ↔ p.1 ∈ wordSet R w
    exact natExtMap_iterate_mem_word_iff hx hirr hy R w
  -- step 4: the future marginal is the Gauss measure
  have h4 : hatNu (Prod.fst ⁻¹' wordSet R w) = Erdos1002.gaussMeasure (wordSet R w) := by
    rw [← Measure.map_apply measurable_fst (measurableSet_wordSet R w),
      NatExtMeasure.hatNu_fst_marginal, NatExtMixing.gaussMarginal_eq_gaussMeasure]
  -- step 5: pass to the `Prop41` cylinder
  have h5 : Erdos1002.gaussMeasure (wordSet R w)
      = Erdos1002.gaussMeasure (Prop41.cylinder (2 * R) (wordFn R w)) := by
    refine measure_congr ?_
    rw [Filter.eventuallyEq_set]
    filter_upwards [Prop41Final.gaussMeasure_ae_Ioo] with y hy
    exact wordSet_inter_Ioo R w y hy
  show (hatMu0 {z : (ℝ × ℝ) × ℝ × ℝ | natExtWord R z.1 = w}).toReal = _
  rw [h1, h2, h3, h4, h5]

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

/-! ## 6. The depth-ordering side conditions of the v8 prefix refinement

v8's proof of Proposition 4.2 refines the retained cylinders into complete
prefixes — of depth `k+R` in case 2 and in the `k < t₀ − 100H` branch of
case 3, of depth `j+R` in the `k > t₀ + 100H` branch — before applying the
descendant estimate (display (22)) at descendant depth `t₋`; the §4-body
chain (`ZeroMode.nonzero_mode_three_step`, step 3) likewise feeds (22) with
prefix depth `j_s + 1` and descendant depth `k₋`.  Display (22)
(`descendant_cylinder_estimate`) requires the strict ordering
`prefix depth < descendant depth`.  The reconciliation record
(`RECONCILIATION_V8.md`, section 4) notes that each of these side conditions
"holds with room to spare from (19) but none of which is stated".  They are
stated and proved here.

The common source is display (19): a bulk index `j` satisfies
`j ≤ m_n − 200H`, so the resonance time `t₀ = (m_n + j)/2` sits at least
`100H` above `j`, and the cut `t₋ = kMinus n j = ⌊t₀ − 40H⌋` sits at least
`60H − 1` above `j` (`lt_kMinus_of_bulk`).  Hence `j + R < t₋` for every
window radius `R ≤ 60H − 1` — i.e. with `≈ 60H − R − 1` to spare — and
`j + 1 < t₋` a fortiori.  Case 2 consumes this at the *later* index of the
pair (`t₋ = kMinus n k`, prefix depth `k + R`); case 3 at the *earlier* one
(`t₋ = kMinus n j`, prefix depths `j + R`, and `k + R` with
`k < t₀ − 100H`, for which see `subResonance_prefix_lt_kMinus`).  The
`toNat` forms are the ones display (22)'s `d < k : ℕ` interface consumes,
and the `≤ 2 m_n` bounds are the range conditions under which
`P42Cases.Display20` can be instantiated at the cut depths. -/

lemma hscale_nonneg (n : ℕ) : 0 ≤ Hscale n := by
  have hL : (0 : ℝ) ≤ Lnorm n := by
    show (0 : ℝ) ≤ Real.log n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  exact Real.rpow_nonneg hL _

/-- The second component of a bulk pair is a bulk index (mirror of
`MonomialCore.mem_bulkPairs_fst`). -/
lemma mem_bulkPairs_snd {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ bulkPairs n) :
    p.2 ∈ bulkJ n :=
  (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2

/-- The floor bound `t₋ ≤ t₀ − 40H`. -/
lemma kMinus_le_sub (n j : ℕ) :
    ((Prop41.kMinus n j : ℤ) : ℝ) ≤ Prop41.resonanceTime n j - 40 * Hscale n :=
  Int.floor_le _

/-- The floor bound `t₊ ≤ t₀ + 40H`. -/
lemma kPlus_le_add (n j : ℕ) :
    ((Prop41.kPlus n j : ℤ) : ℝ) ≤ Prop41.resonanceTime n j + 40 * Hscale n :=
  Int.floor_le _

/-- **Display (19) pushes the resonance cut `60H − 1` above the bulk
index**: for `j ∈ J_n`, `j + 60H − 1 < t₋ = ⌊(m_n + j)/2 − 40H⌋`. -/
lemma lt_kMinus_of_bulk {n j : ℕ} (hj : j ∈ bulkJ n) :
    (j : ℝ) + 60 * Hscale n - 1 < ((Prop41.kMinus n j : ℤ) : ℝ) := by
  have hup : (j : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n :=
    ((Finset.mem_filter.1 hj).2).2
  have hfl : Prop41.resonanceTime n j - 40 * Hscale n - 1
      < ((Prop41.kMinus n j : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have hres : (j : ℝ) + 100 * Hscale n ≤ Prop41.resonanceTime n j := by
    show (j : ℝ) + 100 * Hscale n ≤ ((mIndex n : ℝ) + (j : ℝ)) / 2
    linarith
  linarith

/-- **`j + R < t₋`**: the complete-prefix depth of the v8 refinement sits
strictly below the descendant cut, for every window radius `R ≤ 60H − 1`. -/
lemma prefix_lt_kMinus_of_bulk {n j R : ℕ} (hj : j ∈ bulkJ n)
    (hR : (R : ℝ) + 1 ≤ 60 * Hscale n) :
    ((j + R : ℕ) : ℝ) < ((Prop41.kMinus n j : ℤ) : ℝ) := by
  have := lt_kMinus_of_bulk hj
  push_cast
  linarith

/-- `toNat` form of `prefix_lt_kMinus_of_bulk`, the shape display (22)'s
`d < k` interface consumes. -/
lemma prefix_lt_kMinus_toNat_of_bulk {n j R : ℕ} (hj : j ∈ bulkJ n)
    (hR : (R : ℝ) + 1 ≤ 60 * Hscale n) :
    j + R < (Prop41.kMinus n j).toNat := by
  rw [Int.lt_toNat]
  exact_mod_cast prefix_lt_kMinus_of_bulk hj hR

/-- **`j_s + 1 < k₋`**: the prefix depth of the §4-body oscillatory kill
(step 3 of `nonzero_mode_three_step`, `d = j_s + 1`, `k = k₋`) sits below
the cut, for every bulk index once `H ≥ 1/30`. -/
lemma succ_lt_kMinus_toNat_of_bulk {n j : ℕ} (hj : j ∈ bulkJ n)
    (hH : (1 : ℝ) ≤ 30 * Hscale n) :
    j + 1 < (Prop41.kMinus n j).toNat :=
  prefix_lt_kMinus_toNat_of_bulk (R := 1) hj (by push_cast; linarith)

/-- **`k + R < t₋` in the `k < t₀ − 100H` branch of case 3**: below the
resonance window the *later* prefix depth also clears the earlier cut, again
with `60H − R − 1` to spare.  (No bulk hypothesis is needed: the sub-resonance
hypothesis alone supplies the room.) -/
lemma subResonance_prefix_lt_kMinus {n j k R : ℕ}
    (hk : (k : ℝ) < Prop41.resonanceTime n j - 100 * Hscale n)
    (hR : (R : ℝ) + 1 ≤ 60 * Hscale n) :
    ((k + R : ℕ) : ℝ) < ((Prop41.kMinus n j : ℤ) : ℝ) := by
  have hfl : Prop41.resonanceTime n j - 40 * Hscale n - 1
      < ((Prop41.kMinus n j : ℤ) : ℝ) := Int.sub_one_lt_floor _
  push_cast
  linarith

/-- `toNat` form of `subResonance_prefix_lt_kMinus`. -/
lemma subResonance_prefix_lt_kMinus_toNat {n j k R : ℕ}
    (hk : (k : ℝ) < Prop41.resonanceTime n j - 100 * Hscale n)
    (hR : (R : ℝ) + 1 ≤ 60 * Hscale n) :
    k + R < (Prop41.kMinus n j).toNat := by
  rw [Int.lt_toNat]
  exact_mod_cast subResonance_prefix_lt_kMinus hk hR

/-- **Eventual form over bulk pairs**, ready for the `∀ᶠ n` shape of the
case lemmas: for every fixed window radius `R`, eventually every bulk pair
`(j, k)` satisfies both `j + R < kMinus n j` and `k + R < kMinus n k` (in
`toNat` form). -/
lemma eventually_prefix_lt_kMinus (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ bulkPairs n,
      p.1 + R < (Prop41.kMinus n p.1).toNat ∧
        p.2 + R < (Prop41.kMinus n p.2).toNat := by
  filter_upwards [(P42Cases.tendsto_Hscale.const_mul_atTop
    (by norm_num : (0 : ℝ) < 60)).eventually_ge_atTop ((R : ℝ) + 1)] with n hH
  intro p hp
  exact ⟨prefix_lt_kMinus_toNat_of_bulk (MonomialCore.mem_bulkPairs_fst hp) hH,
    prefix_lt_kMinus_toNat_of_bulk (mem_bulkPairs_snd hp) hH⟩

/-- **The cuts stay inside display (20)'s range.**  For a bulk index `j`,
both `t₋` and `t₊` are at most `2 m_n`, which is the index range over which
`P42Cases.Display20` quantifies; so (20) may be instantiated at the cut
depths with no further largeness hypothesis. -/
lemma kMinus_toNat_le_two_mIndex_of_bulk {n j : ℕ} (hj : j ∈ bulkJ n) :
    (Prop41.kMinus n j).toNat ≤ 2 * mIndex n := by
  have hjm : j ≤ mIndex n :=
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
  have hH := hscale_nonneg n
  have hle := kMinus_le_sub n j
  have hres : Prop41.resonanceTime n j ≤ (mIndex n : ℝ) := by
    show ((mIndex n : ℝ) + (j : ℝ)) / 2 ≤ (mIndex n : ℝ)
    have : (j : ℝ) ≤ (mIndex n : ℝ) := by exact_mod_cast hjm
    linarith
  have h2 : ((Prop41.kMinus n j : ℤ) : ℝ) ≤ ((2 * mIndex n : ℕ) : ℝ) := by
    push_cast
    linarith
  have h3 : Prop41.kMinus n j ≤ ((2 * mIndex n : ℕ) : ℤ) := by exact_mod_cast h2
  exact_mod_cast Int.toNat_le.2 h3

/-- `t₊ ≤ 2 m_n` for a bulk index (the bulk hypothesis supplies
`m_n ≥ 400H ≥ 40H`, which absorbs the `+40H` of the cut). -/
lemma kPlus_toNat_le_two_mIndex_of_bulk {n j : ℕ} (hj : j ∈ bulkJ n) :
    (Prop41.kPlus n j).toNat ≤ 2 * mIndex n := by
  have hjm : j ≤ mIndex n :=
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
  have hmem := Finset.mem_filter.1 hj
  have hlo : 200 * Hscale n ≤ (j : ℝ) := hmem.2.1
  have hup : (j : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n := hmem.2.2
  have hH := hscale_nonneg n
  -- `m_n ≥ 400H`, so `t₀ + 40H ≤ m_n + 40H ≤ 2 m_n`
  have hm : 400 * Hscale n ≤ (mIndex n : ℝ) := by linarith
  have hle := kPlus_le_add n j
  have hres : Prop41.resonanceTime n j ≤ (mIndex n : ℝ) := by
    show ((mIndex n : ℝ) + (j : ℝ)) / 2 ≤ (mIndex n : ℝ)
    have : (j : ℝ) ≤ (mIndex n : ℝ) := by exact_mod_cast hjm
    linarith
  have h2 : ((Prop41.kPlus n j : ℤ) : ℝ) ≤ ((2 * mIndex n : ℕ) : ℝ) := by
    push_cast
    linarith
  have h3 : Prop41.kPlus n j ≤ ((2 * mIndex n : ℕ) : ℤ) := by exact_mod_cast h2
  exact_mod_cast Int.toNat_le.2 h3

/-! ## 7. Toward the two phase bounds: the pair oscillatory form and the
exponent identities of cases 2 and 3

`MonomialCore.laterMode_phase_bound` and `earlierMode_phase_bound` remain
open, and `P42Cases` §4's finding stands: display (20) (`P42Cases.Display20`)
has no proved instance anywhere in the tree, so any complete treatment of
cases 2 and 3 is conditional on it.  This section proves, outright, the
named sub-steps of those cases that do **not** pass through (20):

* `Qpair` / `monoAt_mul_oscillatory`: display (33) *for a monomial pair* —
  the two-block integrand is the indicator of the two-window intersection
  times the pure phase `e(Q n α)` at the combined integer frequency
  `Q = (−1)^j Q_j(r₁,s₁) + (−1)^k Q_k(r₂,s₂)`.  This is the entry point of
  both case lemmas (the pair analogue of `ZeroMode.modeTerm_eq_oscillatory`).
* `Qfreq_congr` / `Qpair_congr`: the combined frequency is **frozen at depth
  `max j k`**, hence constant on the complete depth-`(k+R)` prefixes of the
  v8 refinement — "On each depth-`(k+R)` cylinder, the integer `Q` … is
  fixed".
* `lyapunov_mIndex_bounds`, `kMinus_exponent_identity`,
  `kPlus_exponent_identity`: the manuscript's `2λt₋ = L + λk − 80λH + O(1)`
  and `2λt₊ = L + λj + 80λH + O(1)` with the `O(1)` **explicit**
  (`A ∈ (−3λ, 0]`), in exactly the `ht` shape that
  `Prop42.retained_descendant_exponent` / `retained_descendant_at_compat`
  consume.
* `retained_descendant_bound_at_cut`: the manuscript's "every retained
  descendant satisfies `q_{t₋}² ≤ e^{−cH} n|Q|`" verbatim at the cut
  `t₋ = kMinus n k`, with absolute constant `2` (the `e^A ≤ 1` of the
  identity absorbs the `O(1)`).  Its `hqt`/`hqk` hypotheses are the two
  Lévy bounds — exactly what `Display20` supplies on the retained set, at
  depths that §6's range lemmas (`kMinus_toNat_le_two_mIndex_of_bulk`,
  `kPlus_toNat_le_two_mIndex_of_bulk`) place inside (20)'s quantifier.

**Exact residual for the case lemmas** (recorded, not assumed): with the
above, `descendant_cylinder_estimate` (22), `shrinking_anti_concentration`
(Lemma 3.3), `later_frequency_dominates`, `lebesgue_two_block` (§1) and
`MixingBV.lem_3_2_conditional_multiblock_mixing'` all proved, what separates
a `Display20`-conditional `laterMode_phase_bound` from this file is the
*cylinder summation glue*: partitioning `(0,1)` into complete depth-`(k+R)`
prefix cylinders, selecting the retained words by (20) + Lemma 3.3 (union
bound over the ≤ 3 bad sets), transporting the window indicators to
per-cylinder constants (the `List`-word analogue of `cylObs_windowWord`),
and summing (22) by prefix-cylinder mass — the pair analogue of the §9
bookkeeping `ZeroMode.lean` built for `modeTerm`, which is `GoodTuple`-shaped
and does not directly apply to a `bulkPairs` pair.  The `k > t₀ + 100H`
branch of case 3 additionally needs the stationary-mean replacement on each
retained depth-`t₊` cylinder (Lemma 3.2 conditioned on a cylinder, under the
*Lebesgue* measure) and the v8 restore step, which consumes (20) once more.
-/

/-- **The combined frequency of a monomial pair**: `(−1)^j Q_j(r₁,s₁) +
(−1)^k Q_k(r₂,s₂)`, the integer `Q` of cases 2 and 3 of the proof of
Proposition 4.2. -/
def Qpair (α : ℝ) (j k : ℕ) (r₁ s₁ r₂ s₂ : ℤ) : ℤ :=
  (-1) ^ j * Qfreq α j r₁ s₁ + (-1) ^ k * Qfreq α k r₂ s₂

/-- **The two-block integrand in oscillatory form** (display (33) for a
monomial pair): at irrational `α ∈ (0,1)` and times `1 ≤ j`, `1 ≤ k`, the
product of two cylinder-torus monomials is the indicator of the two-window
intersection times the pure phase `e(Q n α)` at the combined frequency. -/
lemma monoAt_mul_oscillatory {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (R : ℕ) (w w' : Fin (2 * R) → ℕ) (r₁ s₁ r₂ s₂ : ℤ)
    (n : ℕ) {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    Prop42.monoAt R w r₁ s₁ α n j * Prop42.monoAt R w' r₂ s₂ α n k
      = (P42Cases.cyl R w j ∩ P42Cases.cyl R w' k).indicator (fun _ => (1 : ℂ)) α
          * torusChar (((Qpair α j k r₁ s₁ r₂ s₂ : ℤ) : ℝ) * (n : ℝ) * α) := by
  classical
  have hphase : torusChar ((-1 : ℝ) ^ j * ((Qfreq α j r₁ s₁ : ℤ) : ℝ) * (n : ℝ) * α)
      * torusChar ((-1 : ℝ) ^ k * ((Qfreq α k r₂ s₂ : ℤ) : ℝ) * (n : ℝ) * α)
      = torusChar (((Qpair α j k r₁ s₁ r₂ s₂ : ℤ) : ℝ) * (n : ℝ) * α) := by
    rw [← MonomialCore.torusChar_add]
    congr 1
    unfold Qpair
    push_cast
    ring
  simp only [Prop42.monoAt]
  rw [torusChar_monomial_frequency' hα hirr n j hj r₁ s₁,
    torusChar_monomial_frequency' hα hirr n k hk r₂ s₂]
  simp only [Set.indicator_apply, Set.mem_inter_iff]
  by_cases h1 : windowWord R α j = w <;> by_cases h2 : windowWord R α k = w'
  · have hm1 : α ∈ P42Cases.cyl R w j := h1
    have hm2 : α ∈ P42Cases.cyl R w' k := h2
    rw [if_pos h1, if_pos h2, if_pos ⟨hm1, hm2⟩, one_mul, one_mul, one_mul, hphase]
  · rw [if_pos h1, if_neg h2,
      if_neg (fun hc : α ∈ P42Cases.cyl R w j ∧ α ∈ P42Cases.cyl R w' k => h2 hc.2)]
    ring
  · rw [if_neg h1, if_pos h2,
      if_neg (fun hc : α ∈ P42Cases.cyl R w j ∧ α ∈ P42Cases.cyl R w' k => h1 hc.1)]
    ring
  · rw [if_neg h1, if_neg h2,
      if_neg (fun hc : α ∈ P42Cases.cyl R w j ∧ α ∈ P42Cases.cyl R w' k => h1 hc.1)]
    ring

/-- **A single frequency is frozen at depth `j`**: `Q_j(r,s)` reads only the
digits below `j`. -/
lemma Qfreq_congr {α α' : ℝ} {j d : ℕ} (hj : j ≤ d)
    (hdig : ∀ i, i < d → digit α i = digit α' i) (r s : ℤ) :
    Qfreq α j r s = Qfreq α' j r s := by
  have h1 : denom α j = denom α' j :=
    (cf_congr α α' j (fun i hi => hdig i (lt_of_lt_of_le hi hj))).1
  have h2 : denom α (j - 1) = denom α' (j - 1) :=
    (cf_congr α α' (j - 1) (fun i hi => hdig i (by omega))).1
  unfold Qfreq
  rw [h1, h2]

/-- **The combined frequency is frozen at depth `max j k`**, hence constant
on every complete prefix cylinder of any depth `d ≥ max j k` — in particular
on the depth-`(k+R)` prefixes of the v8 refinement.  This is "on each
depth-`(k+R)` cylinder, the integer `Q` … is fixed". -/
lemma Qpair_congr {α α' : ℝ} {j k d : ℕ} (hj : j ≤ d) (hk : k ≤ d)
    (hdig : ∀ i, i < d → digit α i = digit α' i) (r₁ s₁ r₂ s₂ : ℤ) :
    Qpair α j k r₁ s₁ r₂ s₂ = Qpair α' j k r₁ s₁ r₂ s₂ := by
  unfold Qpair
  rw [Qfreq_congr hj hdig r₁ s₁, Qfreq_congr hk hdig r₂ s₂]

/-- `λ m_n ∈ (L − λ, L]`: the floor in `m_n = ⌊L/λ⌋` costs less than one
`λ`. -/
lemma lyapunov_mIndex_bounds (n : ℕ) :
    Lnorm n - lyapunov < lyapunov * (mIndex n : ℝ) ∧
      lyapunov * (mIndex n : ℝ) ≤ Lnorm n := by
  have hlyap := Prop42.lyapunov_pos
  have hL : (0 : ℝ) ≤ Lnorm n := by
    show (0 : ℝ) ≤ Real.log n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hdiv : (0 : ℝ) ≤ Lnorm n / lyapunov := div_nonneg hL hlyap.le
  constructor
  · have h2 : Lnorm n / lyapunov < (mIndex n : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (Lnorm n / lyapunov)
      exact_mod_cast this
    have h3 : Lnorm n < ((mIndex n : ℝ) + 1) * lyapunov := (div_lt_iff₀ hlyap).1 h2
    nlinarith
  · have h2 : (mIndex n : ℝ) ≤ Lnorm n / lyapunov := by
      have := Nat.floor_le hdiv
      exact_mod_cast this
    have h3 : (mIndex n : ℝ) * lyapunov ≤ Lnorm n := (le_div_iff₀ hlyap).1 h2
    nlinarith

/-- **`2λt₋ = L + λk − 80λH + O(1)`, with the `O(1)` explicit.**  For a bulk
index `k`, the cut `t₋ = (kMinus n k).toNat` satisfies the exponent identity
with defect `A ∈ (−3λ, 0]` — precisely the `ht` hypothesis of
`Prop42.retained_descendant_exponent` and
`P42Cases.retained_descendant_at_compat`, with `e^A ≤ 1`. -/
lemma kMinus_exponent_identity {n k : ℕ} (hk : k ∈ bulkJ n) :
    ∃ A : ℝ, 2 * (lyapunov * (((Prop41.kMinus n k).toNat : ℕ) : ℝ))
        = Lnorm n + lyapunov * (k : ℝ) - 80 * lyapunov * Hscale n + A
      ∧ -3 * lyapunov < A ∧ A ≤ 0 := by
  have hlyap := Prop42.lyapunov_pos
  have hH := hscale_nonneg n
  obtain ⟨hmb1, hmb2⟩ := lyapunov_mIndex_bounds n
  have hlo : 200 * Hscale n ≤ (k : ℝ) := (Finset.mem_filter.1 hk).2.1
  have hpos : (0 : ℤ) ≤ Prop41.kMinus n k := by
    have h := lt_kMinus_of_bulk hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hgt : (-1 : ℝ) < ((Prop41.kMinus n k : ℤ) : ℝ) := by linarith
    have hgt' : (-1 : ℤ) < Prop41.kMinus n k := by exact_mod_cast hgt
    omega
  have htR : (((Prop41.kMinus n k).toNat : ℕ) : ℝ) = ((Prop41.kMinus n k : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hpos)
  set t : ℝ := ((Prop41.kMinus n k : ℤ) : ℝ) with htdef
  have hub : t ≤ Prop41.resonanceTime n k - 40 * Hscale n := Int.floor_le _
  have hlb : Prop41.resonanceTime n k - 40 * Hscale n - 1 < t := Int.sub_one_lt_floor _
  have hres : Prop41.resonanceTime n k = ((mIndex n : ℝ) + (k : ℝ)) / 2 := rfl
  rw [hres] at hub hlb
  refine ⟨2 * (lyapunov * t)
    - (Lnorm n + lyapunov * (k : ℝ) - 80 * lyapunov * Hscale n), ?_, ?_, ?_⟩
  · rw [htR]; ring
  · have h1 : (mIndex n : ℝ) + (k : ℝ) - 80 * Hscale n - 2 < 2 * t := by linarith
    have h2 : lyapunov * ((mIndex n : ℝ) + (k : ℝ) - 80 * Hscale n - 2)
        < lyapunov * (2 * t) := by
      exact mul_lt_mul_of_pos_left h1 hlyap
    nlinarith
  · have h1 : 2 * t ≤ (mIndex n : ℝ) + (k : ℝ) - 80 * Hscale n := by linarith
    have h2 : lyapunov * (2 * t)
        ≤ lyapunov * ((mIndex n : ℝ) + (k : ℝ) - 80 * Hscale n) :=
      mul_le_mul_of_nonneg_left h1 hlyap.le
    nlinarith

/-- **`2λt₊ = L + λj + 80λH + O(1)`, with the `O(1)` explicit** — the `t₊`
mirror of `kMinus_exponent_identity`, for the `k > t₀ + 100H` branch of
case 3. -/
lemma kPlus_exponent_identity {n j : ℕ} (hj : j ∈ bulkJ n) :
    ∃ A : ℝ, 2 * (lyapunov * (((Prop41.kPlus n j).toNat : ℕ) : ℝ))
        = Lnorm n + lyapunov * (j : ℝ) + 80 * lyapunov * Hscale n + A
      ∧ -3 * lyapunov < A ∧ A ≤ 0 := by
  have hlyap := Prop42.lyapunov_pos
  have hH := hscale_nonneg n
  obtain ⟨hmb1, hmb2⟩ := lyapunov_mIndex_bounds n
  have hlo : 200 * Hscale n ≤ (j : ℝ) := (Finset.mem_filter.1 hj).2.1
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hm0 : (0 : ℝ) ≤ (mIndex n : ℝ) := Nat.cast_nonneg _
  have hres : Prop41.resonanceTime n j = ((mIndex n : ℝ) + (j : ℝ)) / 2 := rfl
  have hub : ((Prop41.kPlus n j : ℤ) : ℝ)
      ≤ ((mIndex n : ℝ) + (j : ℝ)) / 2 + 40 * Hscale n := by
    have := kPlus_le_add n j
    rw [hres] at this
    exact this
  have hlb : ((mIndex n : ℝ) + (j : ℝ)) / 2 + 40 * Hscale n - 1
      < ((Prop41.kPlus n j : ℤ) : ℝ) := by
    have h := Int.sub_one_lt_floor (Prop41.resonanceTime n j + 40 * Hscale n)
    rw [hres] at h
    exact h
  have hpos : (0 : ℤ) ≤ Prop41.kPlus n j := by
    have hgt : (-1 : ℝ) < ((Prop41.kPlus n j : ℤ) : ℝ) := by linarith
    have hgt' : (-1 : ℤ) < Prop41.kPlus n j := by exact_mod_cast hgt
    omega
  have htR : (((Prop41.kPlus n j).toNat : ℕ) : ℝ) = ((Prop41.kPlus n j : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hpos)
  set t : ℝ := ((Prop41.kPlus n j : ℤ) : ℝ) with htdef
  refine ⟨2 * (lyapunov * t)
    - (Lnorm n + lyapunov * (j : ℝ) + 80 * lyapunov * Hscale n), ?_, ?_, ?_⟩
  · rw [htR]; ring
  · have h1 : (mIndex n : ℝ) + (j : ℝ) + 80 * Hscale n - 2 < 2 * t := by linarith
    have h2 : lyapunov * ((mIndex n : ℝ) + (j : ℝ) + 80 * Hscale n - 2)
        < lyapunov * (2 * t) := mul_lt_mul_of_pos_left h1 hlyap
    nlinarith
  · have h1 : 2 * t ≤ (mIndex n : ℝ) + (j : ℝ) + 80 * Hscale n := by linarith
    have h2 : lyapunov * (2 * t)
        ≤ lyapunov * ((mIndex n : ℝ) + (j : ℝ) + 80 * Hscale n) :=
      mul_le_mul_of_nonneg_left h1 hlyap.le
    nlinarith

/-- **"Every retained descendant satisfies `q_{t₋}² ≤ e^{−cH} n|Q|`"**,
verbatim at the cut `t₋ = kMinus n k`, with absolute constant `2`.  The
hypotheses `hqt`/`hqk` are the two Lévy bounds of display (20) at depths
`t₋` and `k` — on the (20)-retained set they hold by definition, and §6's
range lemmas place both depths inside (20)'s quantifier.  `hQ` is the
conclusion of `Prop42.later_frequency_dominates` on the Lemma 3.3-retained
set, and `hnn` is `n = e^L` itself. -/
lemma retained_descendant_bound_at_cut {n k : ℕ} (hk : k ∈ bulkJ n)
    {del cc qt qk Q nn : ℝ}
    (hled : 2 * cc + 3 * del < 80 * lyapunov)
    (hqt0 : 0 ≤ qt)
    (hqt : qt ≤ Real.exp (lyapunov * (((Prop41.kMinus n k).toNat : ℕ) : ℝ)
      + del * Hscale n))
    (hqk : Real.exp (lyapunov * (k : ℝ) - del * Hscale n) ≤ qk)
    (hQ : (1 / 2) * Real.exp (-cc * Hscale n) * qk ≤ Q)
    (hnn : Real.exp (Lnorm n) ≤ nn) :
    qt ^ 2 ≤ 2 * Real.exp (-cc * Hscale n) * (nn * Q) := by
  obtain ⟨A, hA, _, hA0⟩ := kMinus_exponent_identity hk
  have hbase := P42Cases.retained_descendant_at_compat (hscale_nonneg n) hled
    hqt0 hqt hqk hQ hnn hA
  have hexp : Real.exp A ≤ 1 := by
    have := Real.exp_le_exp.2 hA0
    simpa using this
  have hqk0 : (0 : ℝ) ≤ qk := (Real.exp_pos _).le.trans hqk
  have hQ0 : (0 : ℝ) ≤ Q :=
    le_trans (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hqk0) hQ
  have hnn0 : (0 : ℝ) ≤ nn := (Real.exp_pos _).le.trans hnn
  nlinarith [hbase, hexp,
    mul_nonneg (Real.exp_pos (-cc * Hscale n)).le (mul_nonneg hnn0 hQ0)]

/-- **The `t₊` branch of case 3: `q_{t₊}² ≥ e^{γ₊H/2} n|Q_j|`** with
`γ₊/2 = 40λ − (3/2)δ`, for all large `n`, verbatim from the manuscript's
"Using the upper bound `|Q_j| ≤ C_{r₁,s₁} q_j` gives
`log(q_{t₊}²/(n|Q_j|)) ≥ (80λ−3δ)H + O(1)`".  The hypotheses are: the (20)
lower bound at the cut `t₊` (`hqt`), the (20) upper bound at `j` (`hqj`),
the deterministic frequency bound `|Q| ≤ C q_j` (`Prop42.abs_Qfreq_le`,
`hQle`), and `n ≤ e^L` (`hnn`, an identity).  The largeness threshold
absorbs both the `O(1)` defect (`> −3λ`) and the constant `C`. -/
lemma ascended_descendant_bound_at_cut {Kc del : ℝ} (hKc : 1 ≤ Kc)
    (hpos : 0 < 80 * lyapunov - 3 * del) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n, ∀ qt qj Q nn : ℝ,
      0 ≤ Q →
      Real.exp (lyapunov * (((Prop41.kPlus n j).toNat : ℕ) : ℝ)
        - del * Hscale n) ≤ qt →
      qj ≤ Real.exp (lyapunov * (j : ℝ) + del * Hscale n) →
      Q ≤ Kc * qj →
      nn ≤ Real.exp (Lnorm n) →
      Real.exp ((40 * lyapunov - 3 / 2 * del) * Hscale n) * (nn * Q) ≤ qt ^ 2 := by
  have hhalf : (0 : ℝ) < 40 * lyapunov - 3 / 2 * del := by linarith
  have hKc0 : (0 : ℝ) < Kc := lt_of_lt_of_le one_pos hKc
  filter_upwards [(P42Cases.tendsto_Hscale.const_mul_atTop hhalf).eventually_ge_atTop
    (3 * lyapunov + Real.log Kc)] with n hthr
  intro j hj qt qj Q nn hQ0 hqt hqj hQle hnn
  obtain ⟨A, hA, hAlo, _⟩ := kPlus_exponent_identity hj
  set H : ℝ := Hscale n
  set t : ℝ := (((Prop41.kPlus n j).toNat : ℕ) : ℝ)
  -- square the lower bound at the cut
  have hqt0 : (0 : ℝ) ≤ Real.exp (lyapunov * t - del * H) := (Real.exp_pos _).le
  have hsq : Real.exp (2 * (lyapunov * t) - 2 * (del * H)) ≤ qt ^ 2 := by
    have h := mul_le_mul hqt hqt hqt0 (le_trans hqt0 hqt)
    calc Real.exp (2 * (lyapunov * t) - 2 * (del * H))
        = Real.exp (lyapunov * t - del * H) * Real.exp (lyapunov * t - del * H) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ qt * qt := h
      _ = qt ^ 2 := by ring
  -- bound the mass side
  have hmass : nn * Q ≤ Kc * Real.exp (Lnorm n + lyapunov * (j : ℝ) + del * H) := by
    have h1 : nn * Q ≤ Real.exp (Lnorm n) * Q :=
      mul_le_mul_of_nonneg_right hnn hQ0
    have h2 : Real.exp (Lnorm n) * Q ≤ Real.exp (Lnorm n) * (Kc * qj) :=
      mul_le_mul_of_nonneg_left hQle (Real.exp_pos _).le
    have hqj0 : (0 : ℝ) ≤ qj := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have h3 : Real.exp (Lnorm n) * (Kc * qj)
        ≤ Real.exp (Lnorm n) * (Kc * Real.exp (lyapunov * (j : ℝ) + del * H)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hqj hKc0.le
    calc nn * Q ≤ Real.exp (Lnorm n) * (Kc * Real.exp (lyapunov * (j : ℝ) + del * H)) :=
          le_trans h1 (le_trans h2 h3)
      _ = Kc * Real.exp (Lnorm n + lyapunov * (j : ℝ) + del * H) := by
          simp only [Real.exp_add]
          ring
  -- the exponent margin: `(40λ − 3δ/2)H + A ≥ log Kc` at the threshold
  have hmargin : Real.log Kc
      ≤ (2 * (lyapunov * t) - 2 * (del * H))
        - ((40 * lyapunov - 3 / 2 * del) * H + (Lnorm n + lyapunov * (j : ℝ) + del * H)) := by
    have : (2 * (lyapunov * t) - 2 * (del * H))
        - ((40 * lyapunov - 3 / 2 * del) * H + (Lnorm n + lyapunov * (j : ℝ) + del * H))
        = (40 * lyapunov - 3 / 2 * del) * H + A := by
      rw [hA]; ring
    rw [this]
    linarith
  -- assemble
  calc Real.exp ((40 * lyapunov - 3 / 2 * del) * H) * (nn * Q)
      ≤ Real.exp ((40 * lyapunov - 3 / 2 * del) * H)
          * (Kc * Real.exp (Lnorm n + lyapunov * (j : ℝ) + del * H)) :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = Real.exp (Real.log Kc
          + ((40 * lyapunov - 3 / 2 * del) * H
            + (Lnorm n + lyapunov * (j : ℝ) + del * H))) := by
        simp only [Real.exp_add, Real.exp_log hKc0]
        ring
    _ ≤ Real.exp (2 * (lyapunov * t) - 2 * (del * H)) := by
        refine Real.exp_le_exp.2 ?_
        linarith
    _ ≤ qt ^ 2 := hsq

end

end PhaseBounds

/-! ## 8. Token-identical restatements

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
