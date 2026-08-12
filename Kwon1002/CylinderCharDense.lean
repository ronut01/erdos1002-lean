import Kwon1002.NatExtMeasure
import Kwon1002.Section6Skeleton
import Kwon1002.MonomialCore
import Kwon1002.DigitTail
import Kwon1002.Prop41
import Kwon1002.Prop42
import Kwon1002.AntiConcentration
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Density of Kwon1002.Prop41.cylinder-times-character observables in `L²(μ̂₀)`

Target: `Kwon1002.Lemma62.cylinderChar_dense_L2` (v5 line 1149): every
`f ∈ L²(μ̂₀)` is approximated by the evaluation of a window symbol, i.e.
by a finite linear combination of products

  `1[natExtWord R z.1 = w] · e(r θ' + s θ)`

of a digit-Kwon1002.Prop41.cylinder indicator on the two-sided Gauss block and a torus
character on the `T²` block.

## Architecture

`μ̂₀ = ν̂ ⊗ m` (`hatMu0_eq_prod`) is a product of probability measures, so
the proof is three applications of one abstract principle plus a
representation step:

1. `indicator_prod_dense`: if indicators of measurable sets are
   `L²`-approximable by the span of a class `S` on the first factor and of
   a class `T` on the second, the same holds on the product for the span
   of the pointwise products `S ⊗ T`.  Dynkin's lemma
   (`MeasurableSpace.induction_on_inter`) over the rectangle π-system,
   with the `L²` norm factorizing on rectangles (`eLpNorm_prodMul`).
2. On a torus factor, characters `θ ↦ e(rθ)` approximate indicators:
   Lebesgue on `(0,1)` is carried to Haar on `AddCircle 1` by the quotient
   map, indicators are approximated by continuous functions vanishing at
   the seam (regularity plus Urysohn), and those by trigonometric
   polynomials (`span_fourier_closure_eq_top`).  The `[0,1)`-seam is a
   Lebesgue-null set, so nothing is lost in the round trip.
3. On a Gauss factor, digit-Kwon1002.Prop41.cylinder indicators approximate indicators:
   every open set of `(0,1)` is, up to the (null) rationals, a countable
   union of digit cylinders, because the closed Kwon1002.Prop41.cylinder of depth `d`
   containing an irrational has diameter `≤ (1/4)^(d/2)`
   (`Erdos1002.dist_le_of_mem_closedGaussPrefixCylinder`); outer
   regularity finishes.  The comparison `ν̂ ≤ 2·Leb` on the square moves
   the Lebesgue statement to `ν̂`.
4. `MemLp.induction_dense` upgrades indicator approximation to all of
   `L²`, and a padding step (`digit_tail_product` controls the digits
   beyond the Kwon1002.Prop41.cylinder depths) rewrites a finite combination of
   mixed-depth Kwon1002.Prop41.cylinder monomials as the evaluation of a single
   `WindowSymbol` of one radius, up to arbitrarily small `L²` error.

Everything here is proved outright: no `sorry`, no new axioms.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace CylinderCharDense

noncomputable section

/-! ## `L²` generalities -/

/-- `eLpNorm` at `p = 2` as an explicit `lintegral`. -/
lemma eLpNorm_two_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  norm_num

/-- The `L²` norm of a product of functions of the two coordinates of a
product measure factorizes. -/
lemma eLpNorm_prodMul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {u : X → ℂ} {v : Y → ℂ} (hu : Measurable u) (hv : Measurable v) :
    eLpNorm (fun p : X × Y => u p.1 * v p.2) 2 (μ.prod ν)
      = eLpNorm u 2 μ * eLpNorm v 2 ν := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq, eLpNorm_two_eq]
  have h : ∀ p : X × Y,
      ‖u p.1 * v p.2‖ₑ ^ (2 : ℝ) = ‖u p.1‖ₑ ^ (2 : ℝ) * ‖v p.2‖ₑ ^ (2 : ℝ) := by
    intro p
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp only [h]
  rw [lintegral_prod_mul (hu.enorm.pow_const _).aemeasurable
    (hv.enorm.pow_const _).aemeasurable,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

/-- The complex indicator of a set. -/
def indC {X : Type*} (s : Set X) : X → ℂ := s.indicator fun _ => (1 : ℂ)

lemma measurable_indC {X : Type*} [MeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) : Measurable (indC s) :=
  (measurable_const.indicator hs)

lemma eLpNorm_indC {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : Set X}
    (hs : MeasurableSet s) : eLpNorm (indC s) 2 μ = μ s ^ (1 / 2 : ℝ) := by
  rw [indC, eLpNorm_indicator_const hs (by norm_num) (by norm_num)]
  simp

/-- Difference of nested complex indicators. -/
lemma indC_sub_indC {X : Type*} {s t : Set X} (hst : s ⊆ t) :
    indC t - indC s = indC (t \ s) := by
  funext x
  by_cases hx : x ∈ s
  · simp [indC, Set.indicator_apply, hx, hst hx]
  · by_cases hxt : x ∈ t <;> simp [indC, Set.indicator_apply, hx, hxt]

/-- Every member of the span of a set of measurable functions is
measurable. -/
lemma measurable_of_mem_span {X : Type*} [MeasurableSpace X] {D : Set (X → ℂ)}
    (hD : ∀ g ∈ D, Measurable g) {g : X → ℂ} (hg : g ∈ Submodule.span ℂ D) :
    Measurable g := by
  induction hg using Submodule.span_induction with
  | mem f hf => exact hD f hf
  | zero => exact measurable_const
  | add f₁ f₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c f _ h => exact h.const_smul c

/-- If the span of a measurable class `D` approximates indicators in
`L²(μ)`, it approximates every `MemLp` function. -/
theorem span_dense_of_indicator_dense {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {D : Set (X → ℂ)}
    (hDm : ∀ g ∈ D, Measurable g)
    (hInd : ∀ s : Set X, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ D,
        eLpNorm (indC s - g) 2 μ < ENNReal.ofReal ε)
    {f : X → ℂ} (hf : MemLp f 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℂ D, eLpNorm (f - g) 2 μ < ENNReal.ofReal ε := by
  have h0P : ∀ (c : ℂ) ⦃s : Set X⦄, MeasurableSet s → μ s < ∞ →
      ∀ {η : ℝ≥0∞}, η ≠ 0 →
        ∃ g : X → ℂ, eLpNorm (g - s.indicator fun _ => c) 2 μ ≤ η ∧
          g ∈ Submodule.span ℂ D := by
    intro c s hs _ η hη
    -- a positive real below `η`
    obtain ⟨η', hη'0, hη'le⟩ : ∃ η' : ℝ, 0 < η' ∧ ENNReal.ofReal η' ≤ η := by
      rcases eq_or_ne η ⊤ with rfl | hηt
      · exact ⟨1, one_pos, le_top⟩
      · have hpos : 0 < η.toReal := ENNReal.toReal_pos hη hηt
        refine ⟨η.toReal / 2, by positivity, ?_⟩
        calc ENNReal.ofReal (η.toReal / 2)
            ≤ ENNReal.ofReal η.toReal := ENNReal.ofReal_le_ofReal (by linarith)
          _ = η := ENNReal.ofReal_toReal hηt
    obtain ⟨g₀, hg₀, hg₀ε⟩ := hInd s hs (η' / (‖c‖ + 1)) (by positivity)
    refine ⟨c • g₀, ?_, Submodule.smul_mem _ c hg₀⟩
    have hset : (s.indicator fun _ => c) = c • indC s := by
      funext x; by_cases hx : x ∈ s <;> simp [indC, Set.indicator_apply, hx]
    have hkey : (c • g₀ - s.indicator fun _ => c) = c • (g₀ - indC s) := by
      rw [hset, smul_sub]
    rw [hkey, eLpNorm_const_smul, eLpNorm_sub_comm]
    calc ‖c‖ₑ * eLpNorm (indC s - g₀) 2 μ
        ≤ ENNReal.ofReal ‖c‖ * ENNReal.ofReal (η' / (‖c‖ + 1)) := by
          rw [← ofReal_norm_eq_enorm c]
          exact mul_le_mul' le_rfl hg₀ε.le
      _ = ENNReal.ofReal (‖c‖ * (η' / (‖c‖ + 1))) :=
          (ENNReal.ofReal_mul (norm_nonneg c)).symm
      _ ≤ ENNReal.ofReal η' := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg c, hη'0.le]
      _ ≤ η := hη'le
  have h1P : ∀ f g : X → ℂ, f ∈ Submodule.span ℂ D → g ∈ Submodule.span ℂ D →
      f + g ∈ Submodule.span ℂ D := fun f g hf hg => Submodule.add_mem _ hf hg
  have h2P : ∀ g : X → ℂ, g ∈ Submodule.span ℂ D → AEStronglyMeasurable g μ :=
    fun g hg => (measurable_of_mem_span hDm hg).aestronglyMeasurable
  obtain ⟨g, hg, hgspan⟩ := hf.induction_dense (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun g => g ∈ Submodule.span ℂ D) h0P h1P h2P
    (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  exact ⟨g, hgspan, lt_of_le_of_lt hg
    (ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (half_lt_self hε))⟩

/-! ## Density on a product of probability spaces -/

/-- The pointwise products of a class on `X` and a class on `Y`, as
functions on `X × Y`. -/
def mulProd {X Y : Type*} (S : Set (X → ℂ)) (T : Set (Y → ℂ)) :
    Set (X × Y → ℂ) :=
  Set.image2 (fun s t => fun p : X × Y => s p.1 * t p.2) S T

lemma measurable_of_mem_mulProd {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {S : Set (X → ℂ)} {T : Set (Y → ℂ)}
    (hSm : ∀ g ∈ S, Measurable g) (hTm : ∀ g ∈ T, Measurable g) :
    ∀ g ∈ mulProd S T, Measurable g := by
  rintro g ⟨s, hs, t, ht, rfl⟩
  exact ((hSm s hs).comp measurable_fst).mul ((hTm t ht).comp measurable_snd)

/-- Products of span members lie in the span of the products. -/
lemma mem_span_mulProd {X Y : Type*} {S : Set (X → ℂ)} {T : Set (Y → ℂ)}
    {g : X → ℂ} {h : Y → ℂ} (hg : g ∈ Submodule.span ℂ S)
    (hh : h ∈ Submodule.span ℂ T) :
    (fun p : X × Y => g p.1 * h p.2) ∈ Submodule.span ℂ (mulProd S T) := by
  induction hg using Submodule.span_induction with
  | mem s hs =>
      induction hh using Submodule.span_induction with
      | mem t ht => exact Submodule.subset_span (Set.mem_image2_of_mem hs ht)
      | zero =>
          have h0 : (fun p : X × Y => s p.1 * (0 : Y → ℂ) p.2)
              = (0 : X × Y → ℂ) := by funext p; simp
          rw [h0]; exact Submodule.zero_mem _
      | add t₁ t₂ _ _ h₁ h₂ =>
          have : (fun p : X × Y => s p.1 * (t₁ + t₂) p.2)
              = (fun p : X × Y => s p.1 * t₁ p.2) + fun p : X × Y => s p.1 * t₂ p.2 := by
            funext p; simp [mul_add]
          rw [this]; exact Submodule.add_mem _ h₁ h₂
      | smul c t _ h₁ =>
          have : (fun p : X × Y => s p.1 * (c • t) p.2)
              = c • fun p : X × Y => s p.1 * t p.2 := by
            funext p; simp [mul_comm, mul_assoc, mul_left_comm]
          rw [this]; exact Submodule.smul_mem _ c h₁
  | zero =>
      have h0 : (fun p : X × Y => (0 : X → ℂ) p.1 * h p.2)
          = (0 : X × Y → ℂ) := by funext p; simp
      rw [h0]; exact Submodule.zero_mem _
  | add g₁ g₂ _ _ h₁ h₂ =>
      have : (fun p : X × Y => (g₁ + g₂) p.1 * h p.2)
          = (fun p : X × Y => g₁ p.1 * h p.2) + fun p : X × Y => g₂ p.1 * h p.2 := by
        funext p; simp [add_mul]
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul c g₁ _ h₁ =>
      have : (fun p : X × Y => (c • g₁) p.1 * h p.2)
          = c • fun p : X × Y => g₁ p.1 * h p.2 := by
        funext p; simp [mul_assoc]
      rw [this]; exact Submodule.smul_mem _ c h₁

/-- Indicator of a disjoint union splits. -/
lemma indC_union_of_disjoint {X : Type*} {s t : Set X} (hst : Disjoint s t) :
    indC (s ∪ t) = fun x => indC s x + indC t x := by
  funext x
  by_cases hs : x ∈ s
  · have ht : x ∉ t := fun ht => (Set.disjoint_left.mp hst hs) ht
    simp [indC, Set.indicator_apply, hs, ht]
  · by_cases ht : x ∈ t <;> simp [indC, Set.indicator_apply, hs, ht]

/-- Indicator of a finite union of pairwise disjoint sets is the sum of the
indicators. -/
lemma indC_finset_biUnion {X ι : Type*} [DecidableEq ι] (F : Finset ι)
    (f : ι → Set X)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (f i) (f j)) :
    indC (⋃ i ∈ F, f i) = fun x => ∑ i ∈ F, indC (f i) x := by
  induction F using Finset.induction_on with
  | empty => funext x; simp [indC]
  | insert a F ha ih =>
      have hd : Disjoint (f a) (⋃ i ∈ F, f i) := by
        refine Set.disjoint_iUnion_right.mpr fun i => Set.disjoint_iUnion_right.mpr fun hi => ?_
        exact hdisj a (Finset.mem_insert_self a F) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      have hrest : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (f i) (f j) := fun i hi j hj hij =>
        hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      funext x
      rw [Finset.set_biUnion_insert, indC_union_of_disjoint hd, ih hrest,
        Finset.sum_insert ha]

section ProdDense

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- The elementary rectangle estimate: on a product of probability spaces,
the indicator of a measurable rectangle is approximated by a product of
span approximants of the two factor indicators. -/
lemma indicator_rect_approx [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set (X → ℂ)} {T : Set (Y → ℂ)}
    (hSm : ∀ g ∈ S, Measurable g) (hTm : ∀ g ∈ T, Measurable g)
    (hS : ∀ s : Set X, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ S, eLpNorm (indC s - g) 2 μ < ENNReal.ofReal ε)
    (hT : ∀ s : Set Y, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ T, eLpNorm (indC s - g) 2 ν < ENNReal.ofReal ε)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℂ (mulProd S T),
      eLpNorm (indC (A ×ˢ B) - g) 2 (μ.prod ν) < ENNReal.ofReal ε := by
  set δ : ℝ := min 1 (ε / 4) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  obtain ⟨g, hgspan, hg⟩ := hS A hA δ hδ0
  obtain ⟨h, hhspan, hh⟩ := hT B hB δ hδ0
  have hgm : Measurable g := measurable_of_mem_span hSm hgspan
  have hhm : Measurable h := measurable_of_mem_span hTm hhspan
  refine ⟨fun p => g p.1 * h p.2, mem_span_mulProd hgspan hhspan, ?_⟩
  have hg' : eLpNorm (fun x => indC A x - g x) 2 μ < ENNReal.ofReal δ := hg
  have hh' : eLpNorm (fun y => indC B y - h y) 2 ν < ENNReal.ofReal δ := hh
  have hgm' : Measurable fun x => indC A x - g x := (measurable_indC hA).sub hgm
  have hhm' : Measurable fun y => indC B y - h y := (measurable_indC hB).sub hhm
  have hpt : (indC (A ×ˢ B) - fun p : X × Y => g p.1 * h p.2)
      = (fun p : X × Y => (indC A p.1 - g p.1) * indC B p.2)
        + fun p : X × Y => g p.1 * (indC B p.2 - h p.2) := by
    funext p
    have hAB : indC (A ×ˢ B) p = indC A p.1 * indC B p.2 := by
      by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
        simp [indC, Set.indicator_apply, Set.mem_prod, h1, h2]
    simp only [Pi.add_apply, Pi.sub_apply, hAB]
    ring
  rw [hpt]
  have hm1 : AEStronglyMeasurable
      (fun p : X × Y => (indC A p.1 - g p.1) * indC B p.2) (μ.prod ν) :=
    ((hgm'.comp measurable_fst).mul
      ((measurable_indC hB).comp measurable_snd)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable
      (fun p : X × Y => g p.1 * (indC B p.2 - h p.2)) (μ.prod ν) :=
    ((hgm.comp measurable_fst).mul
      (hhm'.comp measurable_snd)).aestronglyMeasurable
  have hpiece1 : eLpNorm (fun p : X × Y => (indC A p.1 - g p.1) * indC B p.2) 2
      (μ.prod ν) < ENNReal.ofReal δ := by
    rw [eLpNorm_prodMul μ ν hgm' (measurable_indC hB)]
    calc eLpNorm (fun x => indC A x - g x) 2 μ * eLpNorm (indC B) 2 ν
        ≤ eLpNorm (fun x => indC A x - g x) 2 μ * 1 := by
          refine mul_le_mul' le_rfl ?_
          rw [eLpNorm_indC ν hB]
          exact ENNReal.rpow_le_one prob_le_one (by norm_num)
      _ = eLpNorm (fun x => indC A x - g x) 2 μ := mul_one _
      _ < ENNReal.ofReal δ := hg'
  have hgnorm : eLpNorm g 2 μ ≤ 2 := by
    have hgeq : g = fun x => indC A x - (indC A x - g x) := by funext x; ring
    calc eLpNorm g 2 μ
        = eLpNorm (fun x => indC A x - (indC A x - g x)) 2 μ := by rw [← hgeq]
      _ ≤ eLpNorm (indC A) 2 μ + eLpNorm (fun x => indC A x - g x) 2 μ :=
          eLpNorm_sub_le (measurable_indC hA).aestronglyMeasurable
            hgm'.aestronglyMeasurable one_le_two
      _ ≤ 1 + 1 := by
          refine add_le_add ?_ ?_
          · rw [eLpNorm_indC μ hA]
            exact ENNReal.rpow_le_one prob_le_one (by norm_num)
          · refine hg'.le.trans ?_
            calc ENNReal.ofReal δ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hδ1
              _ = 1 := ENNReal.ofReal_one
      _ = 2 := one_add_one_eq_two
  have hpiece2 : eLpNorm (fun p : X × Y => g p.1 * (indC B p.2 - h p.2)) 2
      (μ.prod ν) ≤ ENNReal.ofReal (2 * δ) := by
    rw [eLpNorm_prodMul μ ν hgm hhm']
    calc eLpNorm g 2 μ * eLpNorm (fun y => indC B y - h y) 2 ν
        ≤ 2 * ENNReal.ofReal δ := mul_le_mul' hgnorm hh'.le
      _ = ENNReal.ofReal (2 * δ) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
  calc eLpNorm ((fun p : X × Y => (indC A p.1 - g p.1) * indC B p.2)
          + fun p : X × Y => g p.1 * (indC B p.2 - h p.2)) 2 (μ.prod ν)
      ≤ eLpNorm (fun p : X × Y => (indC A p.1 - g p.1) * indC B p.2) 2 (μ.prod ν)
        + eLpNorm (fun p : X × Y => g p.1 * (indC B p.2 - h p.2)) 2 (μ.prod ν) :=
        eLpNorm_add_le hm1 hm2 one_le_two
    _ ≤ eLpNorm (fun p : X × Y => (indC A p.1 - g p.1) * indC B p.2) 2 (μ.prod ν)
        + ENNReal.ofReal (2 * δ) := add_le_add le_rfl hpiece2
    _ < ENNReal.ofReal δ + ENNReal.ofReal (2 * δ) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hpiece1
    _ = ENNReal.ofReal (3 * δ) := by
        rw [← ENNReal.ofReal_add hδ0.le (by positivity)]
        ring_nf
    _ < ENNReal.ofReal ε := by
        refine ENNReal.ofReal_lt_ofReal_iff hε |>.mpr ?_
        nlinarith

/-- **Density on a product of probability spaces.**  If the spans of `S`
and `T` approximate indicators of measurable sets in `L²(μ)` and `L²(ν)`
respectively, the span of the pointwise products approximates indicators
of arbitrary measurable sets of the product in `L²(μ ⊗ ν)`.  Dynkin's
lemma over the rectangle π-system. -/
theorem indicator_prod_dense [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set (X → ℂ)} {T : Set (Y → ℂ)}
    (hSm : ∀ g ∈ S, Measurable g) (hTm : ∀ g ∈ T, Measurable g)
    (hS : ∀ s : Set X, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ S, eLpNorm (indC s - g) 2 μ < ENNReal.ofReal ε)
    (hT : ∀ s : Set Y, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ T, eLpNorm (indC s - g) 2 ν < ENNReal.ofReal ε) :
    ∀ E : Set (X × Y), MeasurableSet E → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ (mulProd S T),
        eLpNorm (indC E - g) 2 (μ.prod ν) < ENNReal.ofReal ε := by
  have hPm : ∀ g ∈ mulProd S T, Measurable g := measurable_of_mem_mulProd hSm hTm
  intro E hE
  induction E, hE using MeasurableSpace.induction_on_inter
    (h_eq := generateFrom_prod.symm) (h_inter := isPiSystem_prod) with
  | empty =>
      intro ε hε
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have h0 : indC (∅ : Set (X × Y)) - 0 = 0 := by
        funext p; simp [indC]
      rw [h0]
      simpa using ENNReal.ofReal_pos.mpr hε
  | basic t ht =>
      obtain ⟨A, hA, B, hB, rfl⟩ := ht
      exact fun ε hε => indicator_rect_approx hSm hTm hS hT hA hB hε
  | compl t htm iht =>
      intro ε hε
      have huniv : ((univ : Set X) ×ˢ (univ : Set Y)) = (univ : Set (X × Y)) :=
        Set.univ_prod_univ
      obtain ⟨gu, hgu, hguε⟩ :=
        indicator_rect_approx hSm hTm hS hT MeasurableSet.univ MeasurableSet.univ
          (half_pos hε) (A := univ) (B := univ)
      obtain ⟨gt, hgt, hgtε⟩ := iht (ε / 2) (half_pos hε)
      refine ⟨gu - gt, Submodule.sub_mem _ hgu hgt, ?_⟩
      have hpt : indC tᶜ - (gu - gt)
          = (indC ((univ : Set X) ×ˢ (univ : Set Y)) - gu) - (indC t - gt) := by
        funext p
        have h1 : indC tᶜ p = indC ((univ : Set X) ×ˢ (univ : Set Y)) p - indC t p := by
          rw [huniv]
          by_cases hp : p ∈ t <;> simp [indC, Set.indicator_apply, hp]
        simp only [Pi.sub_apply, h1]
        ring
      rw [hpt]
      have hmu : AEStronglyMeasurable
          (indC ((univ : Set X) ×ˢ (univ : Set Y)) - gu) (μ.prod ν) :=
        ((measurable_indC (MeasurableSet.univ.prod MeasurableSet.univ)).sub
          (measurable_of_mem_span hPm hgu)).aestronglyMeasurable
      have hmt : AEStronglyMeasurable (indC t - gt) (μ.prod ν) :=
        ((measurable_indC htm).sub
          (measurable_of_mem_span hPm hgt)).aestronglyMeasurable
      calc eLpNorm ((indC ((univ : Set X) ×ˢ (univ : Set Y)) - gu) - (indC t - gt)) 2
            (μ.prod ν)
          ≤ eLpNorm (indC ((univ : Set X) ×ˢ (univ : Set Y)) - gu) 2 (μ.prod ν)
            + eLpNorm (indC t - gt) 2 (μ.prod ν) :=
            eLpNorm_sub_le hmu hmt one_le_two
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
            ENNReal.add_lt_add hguε hgtε
        _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            norm_num
  | iUnion f hdisj hfm ihf =>
      intro ε hε
      have hηpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) :=
        ENNReal.ofReal_pos.mpr (half_pos hε)
      set η : ℝ≥0∞ := ENNReal.ofReal (ε / 2) ^ (2 : ℕ) with hηdef
      have hη0 : η ≠ 0 := pow_ne_zero _ hηpos.ne'
      have hηt : η ≠ ⊤ := by
        simp [hηdef]
      -- the partial unions exhaust the union in measure
      have hsubN : ∀ n : ℕ, Set.accumulate f n ⊆ ⋃ i, f i := fun n => by
        rw [← Set.iUnion_accumulate]
        exact Set.subset_iUnion _ n
      have hmeasacc : ∀ n : ℕ, MeasurableSet (Set.accumulate f n) := fun n => by
        rw [Set.accumulate_def]
        exact MeasurableSet.biUnion (Set.to_countable _) fun i _ => hfm i
      obtain ⟨N, hN⟩ : ∃ N : ℕ, (μ.prod ν) ((⋃ i, f i) \ Set.accumulate f N) < η := by
        set m := (μ.prod ν) (⋃ i, f i) with hmdef
        have hmt : m ≠ ⊤ := measure_ne_top _ _
        have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη0
        rcases le_or_gt m (η / 2) with hm | hm
        · refine ⟨0, lt_of_le_of_lt (le_trans (measure_mono Set.diff_subset) hm) ?_⟩
          exact ENNReal.half_lt_self hη0 hηt
        · have hm0 : m ≠ 0 := (hη2.trans hm).ne'
          have hacc : Tendsto (fun n : ℕ => (μ.prod ν) (Set.accumulate f n)) atTop
              (𝓝 m) := tendsto_measure_iUnion_accumulate
          have hlt : m - η / 2 < m := ENNReal.sub_lt_self hmt hm0 hη2.ne'
          obtain ⟨N, hN⟩ := (hacc.eventually (lt_mem_nhds hlt)).exists
          refine ⟨N, ?_⟩
          have h1 : m ≤ (μ.prod ν) (Set.accumulate f N) + η / 2 := by
            have := hN.le
            rwa [tsub_le_iff_right] at this
          have h2 : m - (μ.prod ν) (Set.accumulate f N) ≤ η / 2 :=
            tsub_le_iff_left.mpr h1
          have h3 : (μ.prod ν) ((⋃ i, f i) \ Set.accumulate f N)
              = m - (μ.prod ν) (Set.accumulate f N) :=
            measure_diff (hsubN N) (hmeasacc N).nullMeasurableSet (measure_ne_top _ _)
          rw [h3]
          exact lt_of_le_of_lt h2 (ENNReal.half_lt_self hη0 hηt)
      -- the head: the tail of the union is small
      have hhead : eLpNorm (indC (⋃ i, f i) - indC (Set.accumulate f N)) 2 (μ.prod ν)
          < ENNReal.ofReal (ε / 2) := by
        rw [indC_sub_indC (hsubN N),
          eLpNorm_indC _ (MeasurableSet.iUnion hfm |>.diff (hmeasacc N))]
        have h4 : ENNReal.ofReal (ε / 2)
            = (η : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
          rw [hηdef, ← ENNReal.rpow_natCast (ENNReal.ofReal (ε / 2)) 2,
            ← ENNReal.rpow_mul]
          norm_num
        rw [h4]
        exact ENNReal.rpow_lt_rpow hN (by norm_num)
      -- the body: approximate each piece of the partial union
      have haccN : Set.accumulate f N = ⋃ i ∈ Finset.range (N + 1), f i := by
        ext x
        simp [Set.accumulate_def, Nat.lt_succ_iff]
      set δ : ℝ := ε / (2 * (N + 1)) with hδdef
      have hδ0 : 0 < δ := by positivity
      have hchoice : ∀ i : ℕ, ∃ g ∈ Submodule.span ℂ (mulProd S T),
          eLpNorm (indC (f i) - g) 2 (μ.prod ν) < ENNReal.ofReal δ :=
        fun i => ihf i δ hδ0
      choose gs hgsspan hgsε using hchoice
      refine ⟨∑ i ∈ Finset.range (N + 1), gs i,
        Submodule.sum_mem _ fun i _ => hgsspan i, ?_⟩
      have hsplit : indC (⋃ i, f i) - ∑ i ∈ Finset.range (N + 1), gs i
          = (indC (⋃ i, f i) - indC (Set.accumulate f N))
            + ∑ i ∈ Finset.range (N + 1), (indC (f i) - gs i) := by
        funext p
        have hacc' : indC (Set.accumulate f N) p
            = ∑ i ∈ Finset.range (N + 1), indC (f i) p := by
          rw [haccN, indC_finset_biUnion _ f
            (fun i _ j _ hij => hdisj hij)]
        simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Finset.sum_sub_distrib,
          hacc']
        ring
      rw [hsplit]
      have hmhead : AEStronglyMeasurable
          (indC (⋃ i, f i) - indC (Set.accumulate f N)) (μ.prod ν) :=
        ((measurable_indC (MeasurableSet.iUnion hfm)).sub
          (measurable_indC (hmeasacc N))).aestronglyMeasurable
      have hmbody : AEStronglyMeasurable
          (∑ i ∈ Finset.range (N + 1), (indC (f i) - gs i)) (μ.prod ν) := by
        refine Finset.aestronglyMeasurable_sum _ fun i _ => ?_
        exact ((measurable_indC (hfm i)).sub
          (measurable_of_mem_span hPm (hgsspan i))).aestronglyMeasurable
      have hbody : eLpNorm (∑ i ∈ Finset.range (N + 1), (indC (f i) - gs i)) 2
          (μ.prod ν) ≤ ENNReal.ofReal (ε / 2) := by
        calc eLpNorm (∑ i ∈ Finset.range (N + 1), (indC (f i) - gs i)) 2 (μ.prod ν)
            ≤ ∑ i ∈ Finset.range (N + 1),
                eLpNorm (indC (f i) - gs i) 2 (μ.prod ν) :=
              eLpNorm_sum_le (fun i _ => ((measurable_indC (hfm i)).sub
                (measurable_of_mem_span hPm (hgsspan i))).aestronglyMeasurable)
                one_le_two
          _ ≤ ∑ _i ∈ Finset.range (N + 1), ENNReal.ofReal δ :=
              Finset.sum_le_sum fun i _ => (hgsε i).le
          _ = (N + 1) * ENNReal.ofReal δ := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
          _ = ENNReal.ofReal (ε / 2) := by
              rw [show ((N : ℝ≥0∞) + 1) = ENNReal.ofReal ((N : ℝ) + 1) by
                  rw [ENNReal.ofReal_add (by positivity) zero_le_one]
                  simp,
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [hδdef]
              field_simp
      calc eLpNorm ((indC (⋃ i, f i) - indC (Set.accumulate f N))
              + ∑ i ∈ Finset.range (N + 1), (indC (f i) - gs i)) 2 (μ.prod ν)
          ≤ eLpNorm (indC (⋃ i, f i) - indC (Set.accumulate f N)) 2 (μ.prod ν)
            + eLpNorm (∑ i ∈ Finset.range (N + 1), (indC (f i) - gs i)) 2 (μ.prod ν) :=
            eLpNorm_add_le hmhead hmbody one_le_two
        _ ≤ eLpNorm (indC (⋃ i, f i) - indC (Set.accumulate f N)) 2 (μ.prod ν)
            + ENNReal.ofReal (ε / 2) := add_le_add le_rfl hbody
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
            ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hhead
        _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            norm_num

end ProdDense

/-! ## Characters approximate indicators in `L²((0,1))` -/

section TorusFactor

/-- Lebesgue on `(0,1)` is a probability measure. -/
instance : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  simp [Real.volume_Ioo]

/-- The one-dimensional characters `θ ↦ e(rθ)`. -/
def charSet : Set (ℝ → ℂ) := {g | ∃ r : ℤ, g = fun θ : ℝ => torusChar ((r : ℝ) * θ)}

lemma measurable_of_mem_charSet : ∀ g ∈ charSet, Measurable g := by
  rintro g ⟨r, rfl⟩
  exact (Prop42.continuous_torusChar.comp
    (continuous_const.mul continuous_id)).measurable

local instance fact_zero_lt_one : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The mathlib Fourier monomial on `AddCircle 1`, read on `[0,1)`
representatives, is the character `torusChar (rθ)`. -/
lemma fourier_mk_eq_torusChar (r : ℤ) (θ : ℝ) :
    fourier r ((θ : ℝ) : AddCircle (1:ℝ)) = torusChar ((r : ℝ) * θ) := by
  rw [fourier_coe_apply, torusChar]
  congr 1
  push_cast
  ring

/-- Pulling back a trigonometric polynomial along `ℝ → AddCircle 1` lands
in the span of the characters. -/
lemma comp_mk_mem_span_charSet {P : C(AddCircle (1:ℝ), ℂ)}
    (hP : P ∈ Submodule.span ℂ (Set.range (@fourier (1:ℝ)))) :
    (fun θ : ℝ => P ((θ : ℝ) : AddCircle (1:ℝ))) ∈ Submodule.span ℂ charSet := by
  induction hP using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨r, rfl⟩ := hg
      have h : (fun θ : ℝ => (fourier r) ((θ : ℝ) : AddCircle (1:ℝ)))
          = fun θ : ℝ => torusChar ((r : ℝ) * θ) := by
        funext θ; exact fourier_mk_eq_torusChar r θ
      rw [h]
      exact Submodule.subset_span ⟨r, rfl⟩
  | zero =>
      have h : (fun θ : ℝ => (0 : C(AddCircle (1:ℝ), ℂ)) ((θ : ℝ) : AddCircle (1:ℝ)))
          = (0 : ℝ → ℂ) := by funext θ; simp
      rw [h]; exact Submodule.zero_mem _
  | add P₁ P₂ _ _ h₁ h₂ =>
      have h : (fun θ : ℝ => (P₁ + P₂) ((θ : ℝ) : AddCircle (1:ℝ)))
          = (fun θ : ℝ => P₁ ((θ : ℝ) : AddCircle (1:ℝ)))
            + fun θ : ℝ => P₂ ((θ : ℝ) : AddCircle (1:ℝ)) := by
        funext θ; simp
      rw [h]; exact Submodule.add_mem _ h₁ h₂
  | smul c P₁ _ h₁ =>
      have h : (fun θ : ℝ => (c • P₁) ((θ : ℝ) : AddCircle (1:ℝ)))
          = c • fun θ : ℝ => P₁ ((θ : ℝ) : AddCircle (1:ℝ)) := by
        funext θ; simp
      rw [h]; exact Submodule.smul_mem _ c h₁

/-- **Characters approximate indicators on `(0,1)`.**  Regularity and
Urysohn approximate the indicator by a continuous function supported away
from the seam `{0,1}`; the periodic lift is continuous on `AddCircle 1`
and is uniformly approximated by a trigonometric polynomial
(`span_fourier_closure_eq_top`), which pulls back to a member of the span
of `charSet`. -/
theorem charSet_indicator_dense :
    ∀ s : Set ℝ, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ charSet,
        eLpNorm (indC s - g) 2 ((volume : Measure ℝ).restrict (Ioo 0 1))
          < ENNReal.ofReal ε := by
  intro s hs ε hε
  set μ₁ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo 0 1) with hμ₁def
  set s' : Set ℝ := s ∩ Ioo 0 1 with hs'def
  have hs'm : MeasurableSet s' := hs.inter measurableSet_Ioo
  have hs'sub : s' ⊆ Ioo 0 1 := Set.inter_subset_right
  have hs'vol : volume s' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hs'sub)
    simp [Real.volume_Ioo]
  -- the ae-reduction to `s'`
  have hae : ∀ g : ℝ → ℂ, eLpNorm (indC s - g) 2 μ₁ = eLpNorm (indC s' - g) 2 μ₁ := by
    intro g
    refine eLpNorm_congr_ae (Filter.EventuallyEq.sub ?_ Filter.EventuallyEq.rfl)
    rw [hμ₁def]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    by_cases hxs : x ∈ s <;>
      simp [indC, hs'def, Set.indicator_apply, Set.mem_inter_iff, hxs, hx]
  -- the geometric data
  set η : ℝ≥0∞ := ENNReal.ofReal (ε / 4) ^ (2 : ℕ) with hηdef
  have hη0 : η ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hη2 : η / 2 ≠ 0 := (ENNReal.half_pos hη0).ne'
  obtain ⟨U', hU'sub, hU'open, hU'vol, hU'diff⟩ :=
    hs'm.exists_isOpen_diff_lt hs'vol hη2
  set U : Set ℝ := U' ∩ Ioo 0 1 with hUdef
  have hUopen : IsOpen U := hU'open.inter isOpen_Ioo
  have hUsub : s' ⊆ U := Set.subset_inter hU'sub hs'sub
  have hUIoo : U ⊆ Ioo 0 1 := Set.inter_subset_right
  have hUdiff : volume (U \ s') < η / 2 :=
    lt_of_le_of_lt (measure_mono (Set.diff_subset_diff_left Set.inter_subset_left))
      hU'diff
  obtain ⟨K, hKsub, hKcomp, hKvol⟩ :=
    hs'm.exists_isCompact_lt_add hs'vol hη2
  have hKdiff : volume (s' \ K) < η / 2 :=
    measure_diff_lt_of_lt_add hKcomp.isClosed.measurableSet.nullMeasurableSet
      hKsub (ne_top_of_le_ne_top hs'vol (measure_mono hKsub)) hKvol
  have hUK : volume (U \ K) < η := by
    have hsplit : U \ K ⊆ (U \ s') ∪ (s' \ K) := by
      intro x hx
      by_cases hxs : x ∈ s'
      · exact Or.inr ⟨hxs, hx.2⟩
      · exact Or.inl ⟨hx.1, hxs⟩
    calc volume (U \ K) ≤ volume ((U \ s') ∪ (s' \ K)) := measure_mono hsplit
      _ ≤ volume (U \ s') + volume (s' \ K) := measure_union_le _ _
      _ < η / 2 + η / 2 := ENNReal.add_lt_add hUdiff hKdiff
      _ = η := ENNReal.add_halves η
  -- Urysohn
  have hdisj : Disjoint K Uᶜ :=
    Set.disjoint_left.mpr fun x hxK hxU => hxU (hUsub.trans' hKsub hxK)
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_continuous_zero_one_of_isCompact hKcomp hUopen.isClosed_compl hdisj
  set φ : ℝ → ℝ := fun x => 1 - f x with hφdef
  have hφcont : Continuous φ := continuous_const.sub f.continuous
  have hφK : ∀ x ∈ K, φ x = 1 := by
    intro x hx; simp [hφdef, hf0 hx]
  have hφU : ∀ x ∉ U, φ x = 0 := by
    intro x hx; simp [hφdef, hf1 (Set.mem_compl hx)]
  have hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1 := by
    intro x
    have := hf01 x
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  set φC : ℝ → ℂ := fun x => (φ x : ℂ) with hφCdef
  have hφCcont : Continuous φC := Complex.continuous_ofReal.comp hφcont
  -- the indicator is close to `φC`
  have hφclose : eLpNorm (indC s' - φC) 2 μ₁ < ENNReal.ofReal (ε / 4) := by
    have hpt : ∀ x, ‖(indC s' - φC) x‖ ≤ (U \ K).indicator (fun _ => (1:ℝ)) x := by
      intro x
      by_cases hxK : x ∈ K
      · have h1 : indC s' x = 1 := by simp [indC, Set.indicator_apply, hKsub hxK]
        have h2 : φC x = 1 := by simp [hφCdef, hφK x hxK]
        have h3 : ‖(indC s' - φC) x‖ = 0 := by
          rw [Pi.sub_apply, h1, h2]; simp
        rw [h3]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
      · by_cases hxU : x ∈ U
        · have hxUK : x ∈ U \ K := ⟨hxU, hxK⟩
          have hb : ‖(indC s' - φC) x‖ ≤ 1 := by
            have h01 := hφ01 x
            have hind : ∃ a : ℝ, indC s' x = (a : ℂ) ∧ 0 ≤ a ∧ a ≤ 1 := by
              by_cases hxs : x ∈ s'
              · exact ⟨1, by simp [indC, Set.indicator_apply, hxs], zero_le_one, le_rfl⟩
              · exact ⟨0, by simp [indC, Set.indicator_apply, hxs], le_rfl, zero_le_one⟩
            obtain ⟨a, ha, ha0, ha1⟩ := hind
            rw [Pi.sub_apply, ha, hφCdef,
              show ((a : ℂ) - ((φ x : ℝ) : ℂ)) = (((a - φ x : ℝ)) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [h01.2], by linarith [h01.1]⟩
          simpa [Set.indicator_apply, hxUK] using hb
        · have hxs : x ∉ s' := fun h => hxU (hUsub h)
          have h1 : indC s' x = 0 := by simp [indC, Set.indicator_apply, hxs]
          have h2 : φC x = 0 := by simp [hφCdef, hφU x hxU]
          have h3 : ‖(indC s' - φC) x‖ = 0 := by
            rw [Pi.sub_apply, h1, h2]; simp
          rw [h3]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    calc eLpNorm (indC s' - φC) 2 μ₁
        ≤ eLpNorm ((U \ K).indicator (fun _ => (1:ℝ))) 2 μ₁ :=
          eLpNorm_mono_real hpt
      _ = (μ₁ (U \ K)) ^ (1/2 : ℝ) := by
          rw [eLpNorm_indicator_const (hUopen.measurableSet.diff
            hKcomp.isClosed.measurableSet) (by norm_num) (by norm_num)]
          simp
      _ ≤ (volume (U \ K)) ^ (1/2 : ℝ) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [hμ₁def, Measure.restrict_apply (hUopen.measurableSet.diff
            hKcomp.isClosed.measurableSet)]
          exact measure_mono Set.inter_subset_left
      _ < η ^ (1/2 : ℝ) := ENNReal.rpow_lt_rpow hUK (by norm_num)
      _ = ENNReal.ofReal (ε / 4) := by
          rw [hηdef, ← ENNReal.rpow_natCast (ENNReal.ofReal (ε / 4)) 2,
            ← ENNReal.rpow_mul]
          norm_num
  -- the periodic lift and its trigonometric approximation
  have hφ0 : φC 0 = φC (0 + 1) := by
    have h0 : (0:ℝ) ∉ U := fun h => absurd (hUIoo h).1 (lt_irrefl 0)
    have h1 : (1:ℝ) ∉ U := fun h => absurd (hUIoo h).2 (lt_irrefl 1)
    rw [zero_add]
    simp [hφCdef, hφU _ h0, hφU _ h1]
  set G : C(AddCircle (1:ℝ), ℂ) :=
    ⟨AddCircle.liftIco 1 0 φC,
      AddCircle.liftIco_continuous hφ0 hφCcont.continuousOn⟩ with hGdef
  have hGmk : ∀ θ : ℝ, θ ∈ Ico (0:ℝ) 1 → G ((θ : ℝ) : AddCircle (1:ℝ)) = φC θ := by
    intro θ hθ
    have hθ' : θ ∈ Ico (0:ℝ) (0 + 1) := by simpa using hθ
    show AddCircle.liftIco 1 0 φC ((θ : ℝ) : AddCircle (1:ℝ)) = φC θ
    exact AddCircle.liftIco_coe_apply hθ'
  have hGclosure : (G : C(AddCircle (1:ℝ), ℂ))
      ∈ closure ((Submodule.span ℂ (Set.range (@fourier (1:ℝ)))) :
        Set C(AddCircle (1:ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  rw [Metric.mem_closure_iff] at hGclosure
  obtain ⟨P, hPspan, hPd⟩ := hGclosure (ε / 4) (by positivity)
  rw [SetLike.mem_coe] at hPspan
  set Q : ℝ → ℂ := fun θ : ℝ => P ((θ : ℝ) : AddCircle (1:ℝ)) with hQdef
  have hQspan : Q ∈ Submodule.span ℂ charSet := comp_mk_mem_span_charSet hPspan
  have hQclose : eLpNorm (φC - Q) 2 μ₁ ≤ ENNReal.ofReal (ε / 4) := by
    have hbd : ∀ᵐ x ∂μ₁, ‖(φC - Q) x‖ ≤ ε / 4 := by
      rw [hμ₁def]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx' : x ∈ Ico (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have h1 : (φC - Q) x = G ((x : ℝ) : AddCircle (1:ℝ))
          - P ((x : ℝ) : AddCircle (1:ℝ)) := by
        simp [Pi.sub_apply, hQdef, hGmk x hx']
      rw [h1, ← dist_eq_norm]
      exact le_of_lt (lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist _) hPd)
    calc eLpNorm (φC - Q) 2 μ₁
        ≤ μ₁ Set.univ ^ (2:ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (ε / 4) :=
          eLpNorm_le_of_ae_bound hbd
      _ = ENNReal.ofReal (ε / 4) := by
          rw [measure_univ]
          simp
  -- assemble
  refine ⟨Q, hQspan, ?_⟩
  rw [hae Q]
  have hsplit : indC s' - Q = (indC s' - φC) + (φC - Q) := by ring
  rw [hsplit]
  have hm1 : AEStronglyMeasurable (indC s' - φC) μ₁ :=
    ((measurable_indC hs'm).sub hφCcont.measurable).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (φC - Q) μ₁ :=
    (hφCcont.sub (P.continuous.comp (AddCircle.continuous_mk' 1))).aestronglyMeasurable
  calc eLpNorm ((indC s' - φC) + (φC - Q)) 2 μ₁
      ≤ eLpNorm (indC s' - φC) 2 μ₁ + eLpNorm (φC - Q) 2 μ₁ :=
        eLpNorm_add_le hm1 hm2 one_le_two
    _ ≤ eLpNorm (indC s' - φC) 2 μ₁ + ENNReal.ofReal (ε / 4) := add_le_add le_rfl hQclose
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hφclose
    _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ < ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith)

end TorusFactor

/-! ## Digit cylinders approximate indicators in `L²((0,1))` -/

section GaussFactor

/-- Digit cylinders are measurable. -/
lemma measurableSet_cylinder (d : ℕ) (w : ℕ → ℕ) :
    MeasurableSet (Kwon1002.Prop41.cylinder d w) := by
  have heq : Kwon1002.Prop41.cylinder d w
      = Ioo (0:ℝ) 1 ∩ ⋂ i ∈ Finset.range d, {α : ℝ | (digit α i : ℝ) = (w i : ℝ)} := by
    ext α
    simp only [Kwon1002.Prop41.cylinder, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi => by exact_mod_cast congrArg (Nat.cast (R := ℝ)) (h2 i hi)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi => by exact_mod_cast h2 i hi⟩
  rw [heq]
  refine measurableSet_Ioo.inter ?_
  refine MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_
  exact (measurable_digit_real i) (measurableSet_singleton ((w i : ℝ)))

/-- The empty set is a Kwon1002.Prop41.cylinder: no point of `(0,1)` has leading digit `0`. -/
lemma cylinder_digitZero_empty : Kwon1002.Prop41.cylinder 1 (fun _ => 0) = (∅ : Set ℝ) := by
  ext α
  simp only [Kwon1002.Prop41.cylinder, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hα h
  have h0 := h 0 one_pos
  have hinv : (1:ℝ) < α⁻¹ := by
    rw [lt_inv_comm₀ one_pos hα.1]
    simpa using hα.2
  have hfl : (1:ℤ) ≤ ⌊α⁻¹⌋ := Int.le_floor.mpr (by exact_mod_cast hinv.le)
  have : 1 ≤ digit α 0 := by
    have : digit α 0 = ⌊α⁻¹⌋.toNat := by simp [digit, gaussIter]
    rw [this]
    omega
  omega

/-- The family of Kwon1002.Prop41.cylinder sets. -/
def cylSet : Set (Set ℝ) := {C | ∃ (d : ℕ) (w : ℕ → ℕ), C = Kwon1002.Prop41.cylinder d w}

lemma empty_mem_cylSet : (∅ : Set ℝ) ∈ cylSet :=
  ⟨1, fun _ => 0, cylinder_digitZero_empty.symm⟩

/-- Cylinders are closed under intersection: two cylinders are nested or
disjoint. -/
lemma inter_mem_cylSet {C₁ C₂ : Set ℝ} (h₁ : C₁ ∈ cylSet) (h₂ : C₂ ∈ cylSet) :
    C₁ ∩ C₂ ∈ cylSet := by
  have key : ∀ (d d' : ℕ) (w w' : ℕ → ℕ), d ≤ d' →
      Kwon1002.Prop41.cylinder d w ∩ Kwon1002.Prop41.cylinder d' w' ∈ cylSet := by
    intro d d' w w' hdd
    by_cases hcomp : ∀ i, i < d → w i = w' i
    · refine ⟨d', w', ?_⟩
      ext α
      simp only [Set.mem_inter_iff, Kwon1002.Prop41.cylinder, Set.mem_sep_iff]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨hα, h⟩
        exact ⟨⟨hα, fun i hi => by rw [h i (lt_of_lt_of_le hi hdd), hcomp i hi]⟩, hα, h⟩
    · push_neg at hcomp
      obtain ⟨i₀, hi₀, hne⟩ := hcomp
      refine ⟨1, fun _ => 0, ?_⟩
      rw [cylinder_digitZero_empty]
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro α ⟨⟨_, h₁'⟩, ⟨_, h₂'⟩⟩
      exact hne ((h₁' i₀ hi₀).symm.trans (h₂' i₀ (lt_of_lt_of_le hi₀ hdd)))
  obtain ⟨d, w, rfl⟩ := h₁
  obtain ⟨d', w', rfl⟩ := h₂
  rcases le_total d d' with h | h
  · exact key d d' w w' h
  · rw [Set.inter_comm]; exact key d' d w' w h

/-- The Kwon1002.Prop41.cylinder indicators, as a function class. -/
def cylFunSet : Set (ℝ → ℂ) :=
  {g | ∃ (d : ℕ) (w : ℕ → ℕ), g = indC (Kwon1002.Prop41.cylinder d w)}

lemma measurable_of_mem_cylFunSet : ∀ g ∈ cylFunSet, Measurable g := by
  rintro g ⟨d, w, rfl⟩
  exact measurable_indC (measurableSet_cylinder d w)

lemma indC_mem_span_of_mem_cylSet {C : Set ℝ} (hC : C ∈ cylSet) :
    indC C ∈ Submodule.span ℂ cylFunSet := by
  obtain ⟨d, w, rfl⟩ := hC
  exact Submodule.subset_span ⟨d, w, rfl⟩

/-- Inclusion–exclusion: indicator of a binary union. -/
lemma indC_union_eq {X : Type*} (A B : Set X) :
    indC (A ∪ B) = indC A + indC B - indC (A ∩ B) := by
  funext x
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
    simp [indC, Set.indicator_apply, hA, hB]

/-- Distributing an intersection over a folded union. -/
lemma inter_foldr {X : Type*} (C : Set X) (l : List (Set X)) :
    C ∩ l.foldr (· ∪ ·) ∅ = (l.map (C ∩ ·)).foldr (· ∪ ·) ∅ := by
  induction l with
  | nil => simp
  | cons A l ih => simp [Set.inter_union_distrib_left, ih]

/-- The indicator of a finite union of cylinders lies in the span of the
Kwon1002.Prop41.cylinder indicators (inclusion–exclusion, using that the family is closed
under intersections). -/
lemma indC_foldr_mem_span :
    ∀ (n : ℕ) (l : List (Set ℝ)), l.length = n → (∀ C ∈ l, C ∈ cylSet) →
      indC (l.foldr (· ∪ ·) ∅) ∈ Submodule.span ℂ cylFunSet := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro l hlen hl
      match l, hlen with
      | [], _ =>
          have h0 : indC (([] : List (Set ℝ)).foldr (· ∪ ·) ∅) = (0 : ℝ → ℂ) := by
            funext x; simp [indC]
          rw [h0]; exact Submodule.zero_mem _
      | C :: l', hlen =>
          have hlen' : l'.length + 1 = n := by simpa using hlen
          have hC : C ∈ cylSet := hl C List.mem_cons_self
          have hl' : ∀ D ∈ l', D ∈ cylSet := fun D hD => hl D (List.mem_cons_of_mem C hD)
          have hstep : (C :: l').foldr (· ∪ ·) ∅ = C ∪ l'.foldr (· ∪ ·) ∅ := rfl
          rw [hstep, indC_union_eq, inter_foldr]
          have h1 : indC C ∈ Submodule.span ℂ cylFunSet := indC_mem_span_of_mem_cylSet hC
          have h2 : indC (l'.foldr (· ∪ ·) ∅) ∈ Submodule.span ℂ cylFunSet :=
            ih l'.length (by omega) l' rfl hl'
          have h3 : indC ((l'.map (C ∩ ·)).foldr (· ∪ ·) ∅)
              ∈ Submodule.span ℂ cylFunSet := by
            refine ih (l'.map (C ∩ ·)).length (by simp; omega) _ rfl ?_
            intro D hD
            rw [List.mem_map] at hD
            obtain ⟨D₀, hD₀, rfl⟩ := hD
            exact inter_mem_cylSet hC (hl' D₀ hD₀)
          exact Submodule.sub_mem _ (Submodule.add_mem _ h1 h2) h3

/-- On `(0,1)`, matching positive digits down to depth `d` traps the point
in the closed prefix Kwon1002.Prop41.cylinder of the digit word. -/
lemma cylinder_subset_closedGaussPrefixCylinder {d : ℕ} {w : ℕ → ℕ}
    (hw : ∀ i, i < d → 1 ≤ w i) :
    Kwon1002.Prop41.cylinder d w
      ⊆ Erdos1002.closedGaussPrefixCylinder (List.ofFn fun i : Fin d => w i) := by
  rintro β ⟨hβ, hdig⟩
  -- iterates stay in `(0,1)` strictly below depth `d`
  have hiter : ∀ j, j < d → gaussIter β j ∈ Ioo (0:ℝ) 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using hβ
    | succ j ih =>
        intro hj
        have hjd : j < d := Nat.lt_of_succ_lt hj
        have hprev := ih hjd
        have hfr : gaussIter β (j+1) = Int.fract (gaussIter β j)⁻¹ := by
          rw [gaussIter_succ]; rfl
        refine ⟨?_, by rw [hfr]; exact Int.fract_lt_one _⟩
        rcases (Int.fract_nonneg ((gaussIter β j)⁻¹)).lt_or_eq with h | h
        · rw [hfr]; exact h
        · exfalso
          have hzero : gaussIter β (j+1) = 0 := by rw [hfr, ← h]
          have hd0 : digit β (j+1) = 0 := by
            simp [digit, hzero]
          have := hdig (j+1) hj
          have := hw (j+1) hj
          omega
  -- the recovery identity, by peeling suffixes
  have hkey : ∀ k, k ≤ d →
      Erdos1002.gaussInverseWord (List.ofFn fun i : Fin k => w (d - k + i))
        (gaussIter β d) = gaussIter β (d - k) := by
    intro k
    induction k with
    | zero => intro _; simp [Erdos1002.gaussInverseWord]
    | succ k ih =>
        intro hk
        have hk' : k ≤ d := Nat.le_of_succ_le hk
        have hofn : (List.ofFn fun i : Fin (k+1) => w (d - (k+1) + i))
            = w (d - (k+1)) :: List.ofFn (fun i : Fin k => w (d - k + i)) := by
          rw [List.ofFn_succ]
          congr 1
          refine congrArg List.ofFn ?_
          funext i
          congr 1
          simp only [Fin.val_succ]
          omega
        rw [hofn]
        show Erdos1002.gaussInverseBranch (w (d - (k+1)))
            (Erdos1002.gaussInverseWord
              (List.ofFn fun i : Fin k => w (d - k + i)) (gaussIter β d))
          = gaussIter β (d - (k+1))
        rw [ih hk']
        set j := d - (k + 1) with hjdef
        have hjd : j < d := by omega
        have hjj : d - k = j + 1 := by omega
        rw [hjj]
        -- the one-branch identity at level `j`
        have hx := hiter j hjd
        have hdigj : digit β j = w j := hdig j hjd
        have hinv1 : (1:ℝ) < (gaussIter β j)⁻¹ := by
          rw [lt_inv_comm₀ one_pos hx.1]
          simpa using hx.2
        have hfl1 : (1:ℤ) ≤ ⌊(gaussIter β j)⁻¹⌋ :=
          Int.le_floor.mpr (by exact_mod_cast hinv1.le)
        have hwj : (w j : ℤ) = ⌊(gaussIter β j)⁻¹⌋ := by
          have h1 : digit β j = ⌊(gaussIter β j)⁻¹⌋.toNat := rfl
          rw [← hdigj, h1]
          omega
        have hdigcast : (w j : ℝ) = (⌊(gaussIter β j)⁻¹⌋ : ℝ) := by
          exact_mod_cast hwj
        have hfr : gaussIter β (j+1)
            = (gaussIter β j)⁻¹ - (⌊(gaussIter β j)⁻¹⌋ : ℝ) := by
          rw [gaussIter_succ]; rfl
        rw [Erdos1002.gaussInverseBranch, hfr, hdigcast]
        have hsum : (⌊(gaussIter β j)⁻¹⌋ : ℝ)
            + ((gaussIter β j)⁻¹ - (⌊(gaussIter β j)⁻¹⌋ : ℝ))
            = (gaussIter β j)⁻¹ := by ring
        rw [hsum, one_div, inv_inv]
  have hfinal := hkey d le_rfl
  simp only [Nat.sub_self] at hfinal
  refine ⟨gaussIter β d, ?_, ?_⟩
  · cases d with
    | zero => exact ⟨hβ.1.le, hβ.2.le⟩
    | succ d' =>
        rw [gaussIter_succ]
        exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · have hfn : (List.ofFn fun i : Fin d => w (0 + i))
        = List.ofFn fun i : Fin d => w i := by
      congr 1
      funext i
      congr 1
      omega
    rw [← hfn, hfinal]
    simp [gaussIter]

/-- Cylinders indexed by digit lists; the family is countable this way. -/
def cylOfList (l : List ℕ) : Set ℝ :=
  Kwon1002.Prop41.cylinder l.length (fun i => l.getD i 0)

lemma cylOfList_mem_cylSet (l : List ℕ) : cylOfList l ∈ cylSet :=
  ⟨l.length, fun i => l.getD i 0, rfl⟩

lemma cylOfList_subset_Ioo (l : List ℕ) : cylOfList l ⊆ Ioo (0:ℝ) 1 :=
  fun _ hβ => hβ.1

/-- Two points of a cylinder with positive entries are `(1/4)^(d/2)`-close:
they both lie in the closed prefix cylinder of the word. -/
lemma dist_le_of_mem_cylOfList {l : List ℕ}
    (hpos : ∀ i, i < l.length → 1 ≤ l.getD i 0)
    {x β : ℝ} (hx : x ∈ cylOfList l) (hβ : β ∈ cylOfList l) :
    dist β x ≤ (1/4 : ℝ) ^ (l.length / 2) := by
  have hofn : (List.ofFn fun i : Fin l.length => l.getD (i : ℕ) 0) = l := by
    have h1 : (fun i : Fin l.length => l.getD (i : ℕ) 0)
        = fun i : Fin l.length => l[(i : ℕ)] := by
      funext i
      exact List.getD_eq_getElem l 0 i.isLt
    rw [h1, List.ofFn_getElem]
  have hsub := cylinder_subset_closedGaussPrefixCylinder
    (d := l.length) (w := fun i => l.getD i 0) hpos
  rw [hofn] at hsub
  have hql : ∀ q ∈ l, 0 < q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have := hpos i hi
    rw [List.getD_eq_getElem l 0 hi] at this
    omega
  exact Erdos1002.dist_le_of_mem_closedGaussPrefixCylinder hql (hsub hβ) (hsub hx)

/-- Folded unions of prefix lists of a sequence of sets. -/
lemma foldr_ofFn_union : ∀ (n : ℕ) (f : ℕ → Set ℝ),
    (List.ofFn fun i : Fin n => f i).foldr (· ∪ ·) ∅
      = ⋃ i ∈ Finset.range n, f i := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ihn =>
      intro f
      rw [List.ofFn_succ]
      have htail : (List.ofFn fun i : Fin n => f (i.succ : ℕ))
          = List.ofFn fun i : Fin n => f ((i : ℕ) + 1) := by
        refine congrArg List.ofFn ?_
        funext i
        simp [Fin.val_succ]
      show f 0 ∪ (List.ofFn fun i : Fin n => f ((i.succ : Fin (n+1)) : ℕ)).foldr (· ∪ ·) ∅
          = ⋃ i ∈ Finset.range (n + 1), f i
      rw [htail, ihn (fun k => f (k + 1))]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro (hx | ⟨i, hi, hx⟩)
        · exact ⟨0, Nat.succ_pos n, hx⟩
        · exact ⟨i + 1, by omega, hx⟩
      · rintro ⟨i, hi, hx⟩
        cases i with
        | zero => exact Or.inl hx
        | succ i => exact Or.inr ⟨i, by omega, hx⟩

lemma accumulate_eq_biUnion (f : ℕ → Set ℝ) (N : ℕ) :
    Set.accumulate f N = ⋃ i ∈ Finset.range (N+1), f i := by
  ext x
  simp [Set.accumulate_def, Nat.lt_succ_iff]

/-- **Open sets are approximated by finite unions of cylinders.**  Every
irrational of an open `u ∩ (0,1)` lies in a cylinder of arbitrarily small
diameter contained in `u`; the leftover is a subset of the rationals,
hence null. -/
lemma open_indicator_approx (u : Set ℝ) (hu : IsOpen u) :
    ∀ ε : ℝ, 0 < ε → ∃ g ∈ Submodule.span ℂ cylFunSet,
      eLpNorm (indC u - g) 2 ((volume : Measure ℝ).restrict (Ioo 0 1))
        < ENNReal.ofReal ε := by
  classical
  intro ε hε
  set μ₁ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo 0 1) with hμ₁def
  set eqv : List ℕ ≃ ℕ := Denumerable.eqv (List ℕ) with heqvdef
  set gfam : ℕ → Set ℝ := fun n =>
    if cylOfList (eqv.symm n) ⊆ u then cylOfList (eqv.symm n) else ∅ with hgfamdef
  have hgcyl : ∀ n, gfam n ∈ cylSet := by
    intro n
    by_cases h : cylOfList (eqv.symm n) ⊆ u <;>
      simp [hgfamdef, h, cylOfList_mem_cylSet, empty_mem_cylSet]
  have hgsubu : ∀ n, gfam n ⊆ u := by
    intro n
    by_cases h : cylOfList (eqv.symm n) ⊆ u <;> simp [hgfamdef, h]
  have hgsubIoo : ∀ n, gfam n ⊆ Ioo (0:ℝ) 1 := by
    intro n
    by_cases h : cylOfList (eqv.symm n) ⊆ u <;>
      simp [hgfamdef, h, cylOfList_subset_Ioo]
  have hgmeas : ∀ n, MeasurableSet (gfam n) := by
    intro n
    obtain ⟨d, w, hdw⟩ := hgcyl n
    rw [hdw]
    exact measurableSet_cylinder d w
  set V : Set ℝ := ⋃ n, gfam n with hVdef
  have hVmeas : MeasurableSet V := MeasurableSet.iUnion hgmeas
  have hVsub : V ⊆ u ∩ Ioo (0:ℝ) 1 := by
    rintro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨hgsubu n hn, hgsubIoo n hn⟩
  -- the covering claim
  have hcover : ∀ x, x ∈ u → x ∈ Ioo (0:ℝ) 1 → Irrational x → x ∈ V := by
    intro x hxu hxIoo hxirr
    obtain ⟨δ, hδ0, hball⟩ := Metric.isOpen_iff.mp hu x hxu
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0 (by norm_num : (1/4 : ℝ) < 1)
    set d : ℕ := 2 * k with hddef
    set l : List ℕ := List.ofFn (fun i : Fin d => digit x i) with hldef
    have hllen : l.length = d := by simp [hldef]
    have hlget : ∀ i, i < l.length → l.getD i 0 = digit x i := by
      intro i hi
      rw [List.getD_eq_getElem l 0 hi]
      simp [hldef]
    have hlpos : ∀ i, i < l.length → 1 ≤ l.getD i 0 := by
      intro i hi
      rw [hlget i hi]
      exact one_le_digit hxIoo hxirr i
    have hxmem : x ∈ cylOfList l := by
      refine ⟨hxIoo, ?_⟩
      intro i hi
      exact (hlget i hi).symm
    have hsubu : cylOfList l ⊆ u := by
      intro β hβ
      have hd := dist_le_of_mem_cylOfList hlpos hxmem hβ
      have hlen2 : l.length / 2 = k := by rw [hllen, hddef]; omega
      rw [hlen2] at hd
      exact hball (show β ∈ Metric.ball x δ from
        lt_of_le_of_lt hd hk)
    refine Set.mem_iUnion.mpr ⟨eqv l, ?_⟩
    have hsymm : eqv.symm (eqv l) = l := Equiv.symm_apply_apply _ _
    simp only [hgfamdef, hsymm, if_pos hsubu]
    exact hxmem
  -- the leftover is null
  have hnull : volume ((u ∩ Ioo (0:ℝ) 1) \ V) = 0 := by
    have hsub2 : (u ∩ Ioo (0:ℝ) 1) \ V ⊆ {x : ℝ | ¬ Irrational x} := by
      rintro x ⟨⟨hxu, hxIoo⟩, hxV⟩
      exact fun hirr => hxV (hcover x hxu hxIoo hirr)
    have hcnt : volume {x : ℝ | ¬ Irrational x} = 0 := by
      have hrange : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
        ext x; simp [Irrational]
      rw [hrange]
      exact (Set.countable_range _).measure_zero volume
    exact measure_mono_null hsub2 hcnt
  -- `indC u` agrees with `indC V` almost everywhere for `μ₁`
  have hbadmeas : MeasurableSet ((u ∩ Ioo (0:ℝ) 1) \ V) :=
    ((hu.measurableSet.inter measurableSet_Ioo).diff hVmeas)
  have haeV : indC u =ᵐ[μ₁] indC V := by
    have hae0 : ∀ᵐ x ∂μ₁, x ∉ (u ∩ Ioo (0:ℝ) 1) \ V := by
      rw [ae_iff]
      have hset : {x : ℝ | ¬ x ∉ (u ∩ Ioo (0:ℝ) 1) \ V}
          = (u ∩ Ioo (0:ℝ) 1) \ V := by
        ext x
        simp only [Set.mem_setOf_eq, not_not]
      rw [hset, hμ₁def, Measure.restrict_apply hbadmeas]
      exact measure_mono_null Set.inter_subset_left hnull
    rw [hμ₁def]
    have hIoo : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 1)), x ∈ Ioo (0:ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioo
    rw [← hμ₁def]
    filter_upwards [hIoo, hae0] with x hx hxb
    by_cases hxV : x ∈ V
    · have hxu : x ∈ u := (hVsub hxV).1
      simp [indC, Set.indicator_apply, hxu, hxV]
    · have hxu : x ∉ u := fun hxu => hxb ⟨⟨hxu, hx⟩, hxV⟩
      simp [indC, Set.indicator_apply, hxu, hxV]
  -- choose a partial union with small tail
  set η : ℝ≥0∞ := ENNReal.ofReal (ε / 2) ^ (2 : ℕ) with hηdef
  have hη0 : η ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  have hηt : η ≠ ⊤ := by simp [hηdef]
  have hsubN : ∀ n : ℕ, Set.accumulate gfam n ⊆ V := fun n => by
    rw [hVdef, ← Set.iUnion_accumulate]
    exact Set.subset_iUnion _ n
  have hmeasacc : ∀ n : ℕ, MeasurableSet (Set.accumulate gfam n) := fun n => by
    rw [Set.accumulate_def]
    exact MeasurableSet.biUnion (Set.to_countable _) fun i _ => hgmeas i
  obtain ⟨N, hN⟩ : ∃ N : ℕ, μ₁ (V \ Set.accumulate gfam N) < η := by
    set m := μ₁ V with hmdef
    have hmt : m ≠ ⊤ := measure_ne_top _ _
    have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη0
    rcases le_or_gt m (η / 2) with hm | hm
    · refine ⟨0, lt_of_le_of_lt (le_trans (measure_mono Set.diff_subset) hm) ?_⟩
      exact ENNReal.half_lt_self hη0 hηt
    · have hm0 : m ≠ 0 := (hη2.trans hm).ne'
      have hacc : Tendsto (fun n : ℕ => μ₁ (Set.accumulate gfam n)) atTop (𝓝 m) :=
        tendsto_measure_iUnion_accumulate
      have hlt : m - η / 2 < m := ENNReal.sub_lt_self hmt hm0 hη2.ne'
      obtain ⟨N, hN⟩ := (hacc.eventually (lt_mem_nhds hlt)).exists
      refine ⟨N, ?_⟩
      have h1 : m ≤ μ₁ (Set.accumulate gfam N) + η / 2 :=
        tsub_le_iff_right.mp hN.le
      have h2 : m - μ₁ (Set.accumulate gfam N) ≤ η / 2 :=
        tsub_le_iff_left.mpr h1
      have h3 : μ₁ (V \ Set.accumulate gfam N) = m - μ₁ (Set.accumulate gfam N) :=
        measure_diff (hsubN N) (hmeasacc N).nullMeasurableSet (measure_ne_top _ _)
      rw [h3]
      exact lt_of_le_of_lt h2 (ENNReal.half_lt_self hη0 hηt)
  -- the partial union is a span member
  have hspan : indC (Set.accumulate gfam N) ∈ Submodule.span ℂ cylFunSet := by
    rw [accumulate_eq_biUnion, ← foldr_ofFn_union (N + 1) gfam]
    refine indC_foldr_mem_span (List.ofFn fun i : Fin (N+1) => gfam i).length _ rfl ?_
    intro C hC
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hC
    exact hi ▸ hgcyl i
  refine ⟨indC (Set.accumulate gfam N), hspan, ?_⟩
  have hcongr : eLpNorm (indC u - indC (Set.accumulate gfam N)) 2 μ₁
      = eLpNorm (indC V - indC (Set.accumulate gfam N)) 2 μ₁ :=
    eLpNorm_congr_ae (haeV.sub Filter.EventuallyEq.rfl)
  rw [hcongr, indC_sub_indC (hsubN N), eLpNorm_indC _ (hVmeas.diff (hmeasacc N))]
  have h4 : ENNReal.ofReal (ε / 2) = η ^ (1 / 2 : ℝ) := by
    rw [hηdef, ← ENNReal.rpow_natCast (ENNReal.ofReal (ε / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  calc μ₁ (V \ Set.accumulate gfam N) ^ (1/2 : ℝ)
      < η ^ (1/2 : ℝ) := ENNReal.rpow_lt_rpow hN (by norm_num)
    _ = ENNReal.ofReal (ε / 2) := h4.symm
    _ < ENNReal.ofReal ε :=
        ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith)

/-- **Cylinder indicators approximate indicators on `(0,1)`.** -/
theorem cylFunSet_indicator_dense :
    ∀ s : Set ℝ, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ cylFunSet,
        eLpNorm (indC s - g) 2 ((volume : Measure ℝ).restrict (Ioo 0 1))
          < ENNReal.ofReal ε := by
  intro s hs ε hε
  set μ₁ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo 0 1) with hμ₁def
  set s' : Set ℝ := s ∩ Ioo 0 1 with hs'def
  have hs'm : MeasurableSet s' := hs.inter measurableSet_Ioo
  have hs'vol : volume s' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    simp [Real.volume_Ioo]
  have hae : ∀ g : ℝ → ℂ, eLpNorm (indC s - g) 2 μ₁ = eLpNorm (indC s' - g) 2 μ₁ := by
    intro g
    refine eLpNorm_congr_ae (Filter.EventuallyEq.sub ?_ Filter.EventuallyEq.rfl)
    rw [hμ₁def]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    by_cases hxs : x ∈ s <;>
      simp [indC, hs'def, Set.indicator_apply, Set.mem_inter_iff, hxs, hx]
  set η : ℝ≥0∞ := ENNReal.ofReal (ε / 4) ^ (2 : ℕ) with hηdef
  have hη0 : η ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  obtain ⟨u, husub, huopen, _, hudiff⟩ := hs'm.exists_isOpen_diff_lt hs'vol hη0
  obtain ⟨g, hgspan, hg⟩ := open_indicator_approx u huopen (ε / 2) (half_pos hε)
  refine ⟨g, hgspan, ?_⟩
  rw [hae g]
  have hsplit : indC s' - g = (indC s' - indC u) + (indC u - g) := by ring
  rw [hsplit]
  have hgm : Measurable g := measurable_of_mem_span measurable_of_mem_cylFunSet hgspan
  have hm1 : AEStronglyMeasurable (indC s' - indC u) μ₁ :=
    ((measurable_indC hs'm).sub (measurable_indC huopen.measurableSet)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (indC u - g) μ₁ :=
    ((measurable_indC huopen.measurableSet).sub hgm).aestronglyMeasurable
  have hpiece1 : eLpNorm (indC s' - indC u) 2 μ₁ < ENNReal.ofReal (ε / 4) := by
    rw [eLpNorm_sub_comm, indC_sub_indC husub,
      eLpNorm_indC _ (huopen.measurableSet.diff hs'm)]
    have hle : μ₁ (u \ s') ≤ volume (u \ s') := by
      rw [hμ₁def, Measure.restrict_apply (huopen.measurableSet.diff hs'm)]
      exact measure_mono Set.inter_subset_left
    have h4 : ENNReal.ofReal (ε / 4) = η ^ (1 / 2 : ℝ) := by
      rw [hηdef, ← ENNReal.rpow_natCast (ENNReal.ofReal (ε / 4)) 2, ← ENNReal.rpow_mul]
      norm_num
    rw [h4]
    exact ENNReal.rpow_lt_rpow (lt_of_le_of_lt hle hudiff) (by norm_num)
  calc eLpNorm ((indC s' - indC u) + (indC u - g)) 2 μ₁
      ≤ eLpNorm (indC s' - indC u) 2 μ₁ + eLpNorm (indC u - g) 2 μ₁ :=
        eLpNorm_add_le hm1 hm2 one_le_two
    _ ≤ eLpNorm (indC s' - indC u) 2 μ₁ + ENNReal.ofReal (ε / 2) :=
        add_le_add le_rfl hg.le
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hpiece1
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ < ENNReal.ofReal ε :=
        ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith)

end GaussFactor

/-! ## The two-dimensional factors and the top-level density -/

section Assembly

/-- Products of two one-dimensional cylinder indicators. -/
def cylFunSet₂ : Set (ℝ × ℝ → ℂ) := mulProd (X := ℝ) (Y := ℝ) cylFunSet cylFunSet

/-- Products of two one-dimensional characters. -/
def charSet₂ : Set (ℝ × ℝ → ℂ) := mulProd (X := ℝ) (Y := ℝ) charSet charSet

/-- The monomials: a two-coordinate cylinder indicator on the Gauss block
times a two-mode character on the torus block. -/
def monoSet : Set (NatExtTorus → ℂ) :=
  mulProd (X := ℝ × ℝ) (Y := ℝ × ℝ) cylFunSet₂ charSet₂

lemma measurable_of_mem_cylFunSet₂ : ∀ g ∈ cylFunSet₂, Measurable g :=
  measurable_of_mem_mulProd (X := ℝ) (Y := ℝ)
    measurable_of_mem_cylFunSet measurable_of_mem_cylFunSet

lemma measurable_of_mem_charSet₂ : ∀ g ∈ charSet₂, Measurable g :=
  measurable_of_mem_mulProd (X := ℝ) (Y := ℝ)
    measurable_of_mem_charSet measurable_of_mem_charSet

lemma measurable_of_mem_monoSet : ∀ g ∈ monoSet, Measurable g :=
  measurable_of_mem_mulProd (X := ℝ × ℝ) (Y := ℝ × ℝ)
    measurable_of_mem_cylFunSet₂ measurable_of_mem_charSet₂

/-- Cylinder rectangles approximate indicators on the square, Lebesgue. -/
theorem cylFunSet₂_indicator_dense :
    ∀ E : Set (ℝ × ℝ), MeasurableSet E → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ cylFunSet₂,
        eLpNorm (indC E - g) 2
          ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1))
          < ENNReal.ofReal ε := by
  intro E hE ε hε
  have h := indicator_prod_dense
    (μ := (volume : Measure ℝ).restrict (Ioo 0 1))
    (ν := (volume : Measure ℝ).restrict (Ioo 0 1))
    measurable_of_mem_cylFunSet measurable_of_mem_cylFunSet
    cylFunSet_indicator_dense cylFunSet_indicator_dense E hE ε hε
  rwa [← NatExtMeasure.restrict_unitSq_eq_prod] at h

/-- Character rectangles approximate indicators on the square, Lebesgue. -/
theorem charSet₂_indicator_dense :
    ∀ E : Set (ℝ × ℝ), MeasurableSet E → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ charSet₂,
        eLpNorm (indC E - g) 2
          ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1))
          < ENNReal.ofReal ε := by
  intro E hE ε hε
  have h := indicator_prod_dense
    (μ := (volume : Measure ℝ).restrict (Ioo 0 1))
    (ν := (volume : Measure ℝ).restrict (Ioo 0 1))
    measurable_of_mem_charSet measurable_of_mem_charSet
    charSet_indicator_dense charSet_indicator_dense E hE ε hε
  rwa [← NatExtMeasure.restrict_unitSq_eq_prod] at h

/-- The `ν̂`-density is bounded by `2` on the square, so `L²(ν̂)` norms are
controlled by twice the Lebesgue ones. -/
lemma eLpNorm_hatNu_le_two_mul (f : ℝ × ℝ → ℂ) (hf : Measurable f) :
    eLpNorm f 2 hatNu
      ≤ 2 * eLpNorm f 2
          ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) := by
  set m₂ : Measure (ℝ × ℝ) :=
    (volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) with hm₂def
  rw [eLpNorm_two_eq, eLpNorm_two_eq]
  have hint : ∫⁻ p, ‖f p‖ₑ ^ (2:ℝ) ∂hatNu
      ≤ 2 * ∫⁻ p, ‖f p‖ₑ ^ (2:ℝ) ∂m₂ := by
    rw [hatNu, lintegral_withDensity_eq_lintegral_mul _
      NatExtMeasure.measurable_hatNuDensity (hf.enorm.pow_const _)]
    rw [← lintegral_const_mul _ (hf.enorm.pow_const _)]
    refine lintegral_mono_ae ?_
    rw [← hm₂def]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    have hbound : ENNReal.ofReal (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2))
        ≤ 2 := by
      have hx := hp.1
      have hy := hp.2
      have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hxy : 0 < p.1 * p.2 := mul_pos hx.1 hy.1
      have h1 : (1:ℝ) ≤ (1 + p.1 * p.2) ^ 2 := by nlinarith
      have h2 : 1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2) ≤ 2 := by
        rw [div_le_iff₀ (by nlinarith)]
        nlinarith
      calc ENNReal.ofReal (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2))
          ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h2
        _ = 2 := by norm_num
    exact mul_le_mul' hbound le_rfl
  calc (∫⁻ p, ‖f p‖ₑ ^ (2:ℝ) ∂hatNu) ^ (1/2 : ℝ)
      ≤ (2 * ∫⁻ p, ‖f p‖ₑ ^ (2:ℝ) ∂m₂) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = (2:ℝ≥0∞) ^ (1/2 : ℝ) * (∫⁻ p, ‖f p‖ₑ ^ (2:ℝ) ∂m₂) ^ (1/2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ 2 * (∫⁻ p, ‖f p‖ₑ ^ (2:ℝ) ∂m₂) ^ (1/2 : ℝ) := by
        refine mul_le_mul' ?_ le_rfl
        calc (2:ℝ≥0∞) ^ (1/2 : ℝ) ≤ (2:ℝ≥0∞) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := ENNReal.rpow_one 2

/-- Cylinder rectangles approximate indicators in `L²(ν̂)`. -/
theorem hatNu_indicator_dense :
    ∀ E : Set (ℝ × ℝ), MeasurableSet E → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Submodule.span ℂ cylFunSet₂,
        eLpNorm (indC E - g) 2 hatNu < ENNReal.ofReal ε := by
  intro E hE ε hε
  obtain ⟨g, hgspan, hg⟩ := cylFunSet₂_indicator_dense E hE (ε / 4) (by positivity)
  refine ⟨g, hgspan, ?_⟩
  have hgm : Measurable g := measurable_of_mem_span measurable_of_mem_cylFunSet₂ hgspan
  calc eLpNorm (indC E - g) 2 hatNu
      ≤ 2 * eLpNorm (indC E - g) 2
          ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) :=
        eLpNorm_hatNu_le_two_mul _ ((measurable_indC hE).sub hgm)
    _ < 2 * ENNReal.ofReal (ε / 4) :=
        ENNReal.mul_lt_mul_left' (by norm_num) (by norm_num) hg
    _ = ENNReal.ofReal (ε / 2) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
    _ < ENNReal.ofReal ε :=
        ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith)

/-- **The span of the monomials is dense in `L²(μ̂₀)`.** -/
theorem monoSet_span_dense {f : NatExtTorus → ℂ} (hf : MemLp f 2 hatMu0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℂ monoSet,
      eLpNorm (f - g) 2 hatMu0 < ENNReal.ofReal ε := by
  have hInd : ∀ E : Set NatExtTorus, MeasurableSet E → ∀ δ : ℝ, 0 < δ →
      ∃ g ∈ Submodule.span ℂ monoSet,
        eLpNorm (indC E - g) 2 hatMu0 < ENNReal.ofReal δ := by
    intro E hE δ hδ
    have h := indicator_prod_dense
      (μ := hatNu)
      (ν := (volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1))
      measurable_of_mem_cylFunSet₂ measurable_of_mem_charSet₂
      hatNu_indicator_dense charSet₂_indicator_dense E hE δ hδ
    rwa [← hatMu0_eq_prod] at h
  exact span_dense_of_indicator_dense measurable_of_mem_monoSet hInd hf hε

end Assembly

/-! ## Refining cylinders to a common radius -/

section Padding

/-- The cylinder of a `Fin R`-indexed digit word. -/
def cylW {R : ℕ} (u : Fin R → ℕ) : Set ℝ :=
  Kwon1002.Prop41.cylinder R fun i => if h : i < R then u ⟨i, h⟩ else 0

lemma mem_cylW {R : ℕ} (u : Fin R → ℕ) (β : ℝ) :
    β ∈ cylW u ↔ β ∈ Ioo (0:ℝ) 1 ∧ ∀ i : Fin R, digit β i = u i := by
  constructor
  · rintro ⟨hβ, h⟩
    refine ⟨hβ, fun i => ?_⟩
    have h2 := h i i.isLt
    have h3 : (fun j => if h : j < R then u ⟨j, h⟩ else 0) (i : ℕ) = u i := by
      simp [dif_pos i.isLt]
    rwa [h3] at h2
  · rintro ⟨hβ, h⟩
    refine ⟨hβ, fun i hi => ?_⟩
    show digit β i = if h : i < R then u ⟨i, h⟩ else 0
    rw [dif_pos hi]
    exact h ⟨i, hi⟩

lemma cylW_subset_Ioo {R : ℕ} (u : Fin R → ℕ) : cylW u ⊆ Ioo (0:ℝ) 1 :=
  fun _ hβ => hβ.1

lemma cylW_disjoint {R : ℕ} {u v : Fin R → ℕ} (huv : u ≠ v) :
    Disjoint (cylW u) (cylW v) := by
  rw [Set.disjoint_left]
  intro β hu hv
  refine absurd ?_ huv
  funext i
  rw [← ((mem_cylW u β).mp hu).2 i, ← ((mem_cylW v β).mp hv).2 i]

lemma measurableSet_cylW {R : ℕ} (u : Fin R → ℕ) : MeasurableSet (cylW u) :=
  measurableSet_cylinder _ _

lemma indC_cylW_mem_cylFunSet {R : ℕ} (u : Fin R → ℕ) :
    indC (cylW u) ∈ cylFunSet := ⟨R, _, rfl⟩

/-- **Refinement with a digit cap**: a depth-`d` cylinder is, up to
arbitrarily small Lebesgue measure, a finite disjoint union of depth-`R`
cylinders.  The tail is controlled by the single-level digit bound of
`digit_tail_product`. -/
lemma exists_cylinder_refinement (d : ℕ) (w : ℕ → ℕ) (R : ℕ) (hdR : d ≤ R)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset (Fin R → ℕ),
      (∀ u ∈ F, cylW u ⊆ Kwon1002.Prop41.cylinder d w) ∧
      volume (Kwon1002.Prop41.cylinder d w \ ⋃ u ∈ F, cylW u)
        < ENNReal.ofReal δ := by
  classical
  obtain ⟨C, hC0, hCtail⟩ := digit_tail_product
  obtain ⟨M, hM⟩ := exists_nat_gt ((R : ℝ) * C / δ)
  set B : ℕ := max ((Finset.range d).sup w) M with hBdef
  have hBw : ∀ i, i < d → w i ≤ B := by
    intro i hi
    exact le_trans (Finset.le_sup (f := w) (Finset.mem_range.mpr hi)) (le_max_left _ _)
  have hBM : (R : ℝ) * C / δ < (B : ℝ) + 1 := by
    have h1 : (M : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  set F : Finset (Fin R → ℕ) :=
    (Fintype.piFinset fun _ : Fin R => Finset.range (B+1)).filter
      (fun u => ∀ i : Fin R, (i : ℕ) < d → u i = w i) with hFdef
  have hFsub : ∀ u ∈ F, cylW u ⊆ Kwon1002.Prop41.cylinder d w := by
    intro u hu β hβ
    obtain ⟨hβIoo, hβdig⟩ := (mem_cylW u β).mp hβ
    have hcond := (Finset.mem_filter.mp hu).2
    refine ⟨hβIoo, fun i hi => ?_⟩
    have hiR : i < R := lt_of_lt_of_le hi hdR
    rw [hβdig ⟨i, hiR⟩]
    exact hcond ⟨i, hiR⟩ hi
  refine ⟨F, hFsub, ?_⟩
  -- the single-level tail sets
  set S : ℕ → Set ℝ := fun j => {β : ℝ | β ∈ Ioo (0:ℝ) 1 ∧ ((B:ℝ)+1) ≤ (digit β j : ℝ)}
    with hSdef
  have hsub : Kwon1002.Prop41.cylinder d w \ ⋃ u ∈ F, cylW u
      ⊆ ⋃ j ∈ Finset.Ico d R, S j := by
    rintro β ⟨hβcyl, hβnot⟩
    by_contra hno
    have hno' : ∀ j, j ∈ Finset.Ico d R → β ∉ S j := fun j hj hSj =>
      hno (Set.mem_biUnion hj hSj)
    have hcap : ∀ j, d ≤ j → j < R → digit β j ≤ B := by
      intro j hj1 hj2
      by_contra hcap'
      push_neg at hcap'
      refine hno' j (Finset.mem_Ico.mpr ⟨hj1, hj2⟩) ?_
      rw [hSdef]
      refine ⟨hβcyl.1, ?_⟩
      have h5 : (B:ℕ) + 1 ≤ digit β j := hcap'
      exact_mod_cast h5
    set u₀ : Fin R → ℕ := fun i => digit β i with hu₀def
    have hu₀F : u₀ ∈ F := by
      rw [hFdef, Finset.mem_filter]
      constructor
      · rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_range]
        rcases lt_or_ge (i : ℕ) d with hid | hid
        · have := hβcyl.2 i hid
          rw [hu₀def]
          simp only []
          rw [this]
          exact Nat.lt_succ_of_le (hBw i hid)
        · exact Nat.lt_succ_of_le (hcap i hid i.isLt)
      · intro i hi
        rw [hu₀def]
        exact hβcyl.2 i hi
    refine hβnot (Set.mem_biUnion hu₀F ?_)
    rw [mem_cylW]
    exact ⟨hβcyl.1, fun i => rfl⟩
  have hStail : ∀ j : ℕ, volume (S j) ≤ ENNReal.ofReal (C / ((B:ℝ)+1)) := by
    intro j
    have hB1 : (1:ℝ) ≤ (B:ℝ)+1 := by
      have h0 : (0:ℝ) ≤ (B:ℝ) := Nat.cast_nonneg B
      linarith
    have h1 := hCtail 1 (fun _ => j) (fun _ => (B:ℝ)+1)
      (fun a b _ => Subsingleton.elim a b) (fun _ => hB1)
    have hset : {α : ℝ | α ∈ Set.Ioo (0:ℝ) 1 ∧
        ∀ i : Fin 1, ((B:ℝ)+1) ≤ (digit α ((fun _ => j) i) : ℝ)} = S j := by
      ext α
      simp [hSdef, Fin.forall_fin_one]
    rw [hset] at h1
    have hSne : volume (S j) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (fun β hβ => hβ.1))
      simp [Real.volume_Ioo]
    have hrhs : C ^ 1 * ∏ _i : Fin 1, ((B:ℝ)+1)⁻¹ = C / ((B:ℝ)+1) := by
      simp [pow_one, div_eq_mul_inv]
    rw [hrhs] at h1
    exact (ENNReal.le_ofReal_iff_toReal_le hSne (by positivity)).mpr h1
  calc volume (Kwon1002.Prop41.cylinder d w \ ⋃ u ∈ F, cylW u)
      ≤ volume (⋃ j ∈ Finset.Ico d R, S j) := measure_mono hsub
    _ ≤ ∑ j ∈ Finset.Ico d R, volume (S j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.Ico d R, ENNReal.ofReal (C / ((B:ℝ)+1)) :=
        Finset.sum_le_sum fun j _ => hStail j
    _ = (R - d) • ENNReal.ofReal (C / ((B:ℝ)+1)) := by
        rw [Finset.sum_const, Nat.card_Ico]
    _ ≤ ENNReal.ofReal ((R:ℝ) * (C / ((B:ℝ)+1))) := by
        rw [nsmul_eq_mul,
          show ((R - d : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((R - d : ℕ) : ℝ) by
            simp [ENNReal.ofReal_natCast],
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hcast : ((R - d : ℕ) : ℝ) ≤ (R : ℝ) := by
          have : (R - d : ℕ) ≤ R := Nat.sub_le _ _
          exact_mod_cast this
        have hnn : (0:ℝ) ≤ C / ((B:ℝ)+1) := by positivity
        nlinarith
    _ < ENNReal.ofReal δ := by
        refine ENNReal.ofReal_lt_ofReal_iff hδ |>.mpr ?_
        have h6 : (R:ℝ) * C < ((B:ℝ)+1) * δ := (div_lt_iff₀ hδ).mp hBM
        have hB1 : (0:ℝ) < (B:ℝ) + 1 := by positivity
        rw [← mul_div_assoc, div_lt_iff₀ hB1]
        linarith

/-- The refinement remainder as an indicator identity. -/
lemma indC_sub_sum_cylW {R d : ℕ} {w : ℕ → ℕ} (F : Finset (Fin R → ℕ))
    (hFsub : ∀ u ∈ F, cylW u ⊆ Kwon1002.Prop41.cylinder d w) :
    (fun x => indC (Kwon1002.Prop41.cylinder d w) x - ∑ u ∈ F, indC (cylW u) x)
      = indC (Kwon1002.Prop41.cylinder d w \ ⋃ u ∈ F, cylW u) := by
  have hsum : (fun x => ∑ u ∈ F, indC (cylW u) x) = indC (⋃ u ∈ F, cylW u) :=
    (indC_finset_biUnion F cylW fun u _ v _ huv => cylW_disjoint huv).symm
  funext x
  rw [congrFun hsum x]
  have hsub : (⋃ u ∈ F, cylW u) ⊆ Kwon1002.Prop41.cylinder d w :=
    Set.iUnion₂_subset hFsub
  exact congrFun (indC_sub_indC hsub) x

end Padding

/-! ## From monomials to window symbols -/

section SymbolConversion

/-- `ν̂` lives on the open square. -/
lemma hatNu_ae_sq :
    ∀ᵐ p ∂hatNu, p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1 := by
  have hac : hatNu ≪ (volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := by
    rw [hatNu]
    exact withDensity_absolutelyContinuous _ _
  refine hac.ae_le ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  exact ⟨hp.1, hp.2⟩

/-- The `2R`-word whose past half is `v` reversed and future half is `u`:
the word `natExtWord` reads off a point of `cylW u ×ˢ cylW v`. -/
def pairWord (R : ℕ) (u v : Fin R → ℕ) : Fin (2 * R) → ℕ := fun t =>
  if h : (t : ℕ) < R then v ⟨R - 1 - (t : ℕ), by omega⟩
  else u ⟨(t : ℕ) - R, by have := t.isLt; omega⟩

lemma pairWord_apply_lt {R : ℕ} (u v : Fin R → ℕ) (t : Fin (2 * R))
    (h : (t : ℕ) < R) :
    pairWord R u v t = v ⟨R - 1 - (t : ℕ), by omega⟩ := dif_pos h

lemma pairWord_apply_ge {R : ℕ} (u v : Fin R → ℕ) (t : Fin (2 * R))
    (h : ¬ ((t : ℕ) < R)) :
    pairWord R u v t = u ⟨(t : ℕ) - R, by have := t.isLt; omega⟩ := dif_neg h

lemma natExtWord_apply_lt (R : ℕ) (p : ℝ × ℝ) (t : Fin (2 * R))
    (h : (t : ℕ) < R) :
    natExtWord R p t = digit p.2 (R - 1 - (t : ℕ)) := if_pos h

lemma natExtWord_apply_ge (R : ℕ) (p : ℝ × ℝ) (t : Fin (2 * R))
    (h : ¬ ((t : ℕ) < R)) :
    natExtWord R p t = digit p.1 ((t : ℕ) - R) := if_neg h

lemma pairWord_at_future {R : ℕ} (u v : Fin R → ℕ) (i : Fin R) :
    pairWord R u v ⟨R + (i : ℕ), by have := i.isLt; omega⟩ = u i := by
  rw [pairWord_apply_ge u v _ (by simp)]
  congr 1
  refine Fin.ext ?_
  simp

lemma pairWord_at_past {R : ℕ} (u v : Fin R → ℕ) (i : Fin R) :
    pairWord R u v ⟨R - 1 - (i : ℕ), by have := i.isLt; omega⟩ = v i := by
  rw [pairWord_apply_lt u v _ (by have := i.isLt; simp; omega)]
  congr 1
  refine Fin.ext ?_
  have := i.isLt
  simp only []
  omega

lemma natExtWord_at_future {R : ℕ} (p : ℝ × ℝ) (i : Fin R) :
    natExtWord R p ⟨R + (i : ℕ), by have := i.isLt; omega⟩ = digit p.1 i := by
  rw [natExtWord_apply_ge R p _ (by simp)]
  congr 1
  simp

lemma natExtWord_at_past {R : ℕ} (p : ℝ × ℝ) (i : Fin R) :
    natExtWord R p ⟨R - 1 - (i : ℕ), by have := i.isLt; omega⟩ = digit p.2 i := by
  rw [natExtWord_apply_lt R p _ (by have := i.isLt; simp; omega)]
  congr 1
  have := i.isLt
  simp only []
  omega

lemma natExtWord_eq_pairWord_iff {R : ℕ} (u v : Fin R → ℕ) (p : ℝ × ℝ) :
    natExtWord R p = pairWord R u v
      ↔ (∀ i : Fin R, digit p.1 i = u i) ∧ (∀ i : Fin R, digit p.2 i = v i) := by
  constructor
  · intro h
    constructor
    · intro i
      have ht := congrFun h ⟨R + (i : ℕ), by have := i.isLt; omega⟩
      rwa [natExtWord_at_future p i, pairWord_at_future u v i] at ht
    · intro i
      have ht := congrFun h ⟨R - 1 - (i : ℕ), by have := i.isLt; omega⟩
      rwa [natExtWord_at_past p i, pairWord_at_past u v i] at ht
  · rintro ⟨hu, hv⟩
    funext t
    by_cases h : (t : ℕ) < R
    · rw [natExtWord_apply_lt R p t h, pairWord_apply_lt u v t h]
      exact hv ⟨R - 1 - (t : ℕ), by omega⟩
    · rw [natExtWord_apply_ge R p t h, pairWord_apply_ge u v t h]
      exact hu ⟨(t : ℕ) - R, by have := t.isLt; omega⟩

lemma pairWord_injective (R : ℕ) :
    Function.Injective (fun uv : (Fin R → ℕ) × (Fin R → ℕ) =>
      pairWord R uv.1 uv.2) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have h' : pairWord R u v = pairWord R u' v' := h
  simp only [Prod.mk.injEq]
  constructor
  · funext i
    have ht := congrFun h' ⟨R + (i : ℕ), by have := i.isLt; omega⟩
    rwa [pairWord_at_future u v i, pairWord_at_future u' v' i] at ht
  · funext i
    have ht := congrFun h' ⟨R - 1 - (i : ℕ), by have := i.isLt; omega⟩
    rwa [pairWord_at_past u v i, pairWord_at_past u' v' i] at ht

/-- Splitting the joined-word indicator over a rectangle of refinements. -/
lemma sum_pairWord_indicator {R : ℕ} (F₁ F₂ : Finset (Fin R → ℕ)) (p : ℝ × ℝ)
    (hp1 : p.1 ∈ Ioo (0:ℝ) 1) (hp2 : p.2 ∈ Ioo (0:ℝ) 1) :
    ∑ uv ∈ F₁ ×ˢ F₂, indC {q : ℝ × ℝ | natExtWord R q = pairWord R uv.1 uv.2} p
      = (∑ u ∈ F₁, indC (cylW u) p.1) * ∑ v ∈ F₂, indC (cylW v) p.2 := by
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases h : natExtWord R p = pairWord R u v
  · obtain ⟨hu, hv⟩ := (natExtWord_eq_pairWord_iff u v p).mp h
    have hu' : p.1 ∈ cylW u := (mem_cylW _ _).mpr ⟨hp1, hu⟩
    have hv' : p.2 ∈ cylW v := (mem_cylW _ _).mpr ⟨hp2, hv⟩
    simp [indC, Set.indicator_apply, h, hu', hv']
  · have hnot : ¬ (p.1 ∈ cylW u ∧ p.2 ∈ cylW v) := by
      rintro ⟨hu', hv'⟩
      exact h ((natExtWord_eq_pairWord_iff u v p).mpr
        ⟨((mem_cylW u p.1).mp hu').2, ((mem_cylW v p.2).mp hv').2⟩)
    by_cases hu' : p.1 ∈ cylW u
    · have hv' : p.2 ∉ cylW v := fun hv' => hnot ⟨hu', hv'⟩
      simp [indC, Set.indicator_apply, h, hu', hv']
    · simp [indC, Set.indicator_apply, h, hu']

/-- The window symbol of a single mode `(r,s)` supported on a finite set of
refinement word pairs, with unit coefficients. -/
def monoSymbol (R K : ℕ) (W : Finset ((Fin R → ℕ) × (Fin R → ℕ))) (r s : ℤ) :
    WindowSymbol R K where
  coeff := fun w' r' s' =>
    if w' ∈ W.image (fun uv => pairWord R uv.1 uv.2) ∧ r' = r ∧ s' = s
      ∧ r.natAbs + s.natAbs ≤ K then 1 else 0
  words := W.image (fun uv => pairWord R uv.1 uv.2)
  coeff_support := by
    intro w' r' s' hw'
    rw [if_neg]
    rintro ⟨h1, -⟩
    exact hw' h1
  mode_cap := by
    intro w' r' s' hcap
    rw [if_neg]
    rintro ⟨-, rfl, rfl, hK⟩
    omega

lemma monoSymbol_coeff (R K : ℕ) (W : Finset ((Fin R → ℕ) × (Fin R → ℕ)))
    (r s : ℤ) (w' : Fin (2 * R) → ℕ) (r' s' : ℤ) :
    (monoSymbol R K W r s).coeff w' r' s'
      = if w' ∈ W.image (fun uv => pairWord R uv.1 uv.2) ∧ r' = r ∧ s' = s
          ∧ r.natAbs + s.natAbs ≤ K then 1 else 0 := rfl

/-- Evaluation of `monoSymbol`: the double mode sum collapses to the single
retained mode, and the word test expands over the pair set. -/
lemma monoSymbol_eval (R K : ℕ) (W : Finset ((Fin R → ℕ) × (Fin R → ℕ)))
    (r s : ℤ) (hK : r.natAbs + s.natAbs ≤ K) (z : NatExtTorus) :
    (monoSymbol R K W r s).eval z
      = (∑ uv ∈ W, indC {q : ℝ × ℝ | natExtWord R q = pairWord R uv.1 uv.2} z.1)
          * torusChar ((r : ℝ) * z.2.1 + (s : ℝ) * z.2.2) := by
  have hrK : r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  have hsK : s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  have hczero : ∀ r' s', ¬ (r' = r ∧ s' = s) →
      (monoSymbol R K W r s).coeff (natExtWord R z.1) r' s' = 0 := by
    intro r' s' hne
    rw [monoSymbol_coeff]
    rw [if_neg]
    rintro ⟨-, h2, h3, -⟩
    exact hne ⟨h2, h3⟩
  rw [WindowSymbol.eval]
  rw [Finset.sum_eq_single r
    (fun r' _ hr' => Finset.sum_eq_zero fun s' _ => by
      rw [hczero r' s' (fun hc => hr' hc.1), zero_mul])
    (fun hr => absurd hrK hr)]
  rw [Finset.sum_eq_single s
    (fun s' _ hs' => by
      rw [hczero r s' (fun hc => hs' hc.2), zero_mul])
    (fun hs => absurd hsK hs)]
  have hcoeff : (monoSymbol R K W r s).coeff (natExtWord R z.1) r s
      = if natExtWord R z.1 ∈ W.image (fun uv => pairWord R uv.1 uv.2)
          then (1:ℂ) else 0 := by
    rw [monoSymbol_coeff]
    by_cases h1 : natExtWord R z.1 ∈ W.image (fun uv => pairWord R uv.1 uv.2)
    · rw [if_pos ⟨h1, rfl, rfl, hK⟩, if_pos h1]
    · rw [if_neg (fun hc => h1 hc.1), if_neg h1]
  rw [hcoeff]
  congr 1
  by_cases h1 : natExtWord R z.1 ∈ W.image (fun uv => pairWord R uv.1 uv.2)
  · rw [if_pos h1]
    obtain ⟨uv₀, huv₀, heq⟩ := Finset.mem_image.mp h1
    rw [Finset.sum_eq_single uv₀
      (fun uv huv hne => by
        have hne' : natExtWord R z.1 ≠ pairWord R uv.1 uv.2 := by
          intro hcontra
          refine hne (pairWord_injective R ?_)
          show pairWord R uv.1 uv.2 = pairWord R uv₀.1 uv₀.2
          rw [← hcontra, heq]
        simp [indC, Set.indicator_apply, hne'])
      (fun h => absurd huv₀ h)]
    have heq' : natExtWord R z.1 = pairWord R uv₀.1 uv₀.2 := heq.symm
    simp [indC, Set.indicator_apply, heq']
  · rw [if_neg h1]
    refine (Finset.sum_eq_zero fun uv huv => ?_).symm
    have hne : natExtWord R z.1 ≠ pairWord R uv.1 uv.2 := by
      intro hcontra
      exact h1 (Finset.mem_image.mpr ⟨uv, huv, hcontra.symm⟩)
    simp [indC, Set.indicator_apply, hne]

/-- Symbol evaluations are measurable: the coefficient factor takes
finitely many values on measurable word events. -/
lemma measurable_eval {R K : ℕ} (U : WindowSymbol R K) : Measurable U.eval := by
  show Measurable fun z : NatExtTorus =>
    ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      U.coeff (natExtWord R z.1) r s * torusChar ((r : ℝ) * z.2.1 + (s : ℝ) * z.2.2)
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ => ?_
  refine Measurable.mul ?_ ?_
  · have hrw : (fun z : NatExtTorus => U.coeff (natExtWord R z.1) r s)
        = fun z => ∑ w ∈ U.words, if natExtWord R z.1 = w then U.coeff w r s else 0 := by
      funext z
      rw [Finset.sum_ite_eq U.words (natExtWord R z.1) (fun w => U.coeff w r s)]
      by_cases h : natExtWord R z.1 ∈ U.words
      · rw [if_pos h]
      · rw [if_neg h, U.coeff_support _ _ _ h]
    rw [hrw]
    refine Finset.measurable_sum _ fun w _ => ?_
    exact Measurable.ite (Prop42.measurableSet_natExtWord_eq R w)
      measurable_const measurable_const
  · exact Prop42.continuous_torusChar.measurable.comp
      ((measurable_const.mul (measurable_fst.comp measurable_snd)).add
        (measurable_const.mul (measurable_snd.comp measurable_snd)))

/-- The zero symbol. -/
def symZero (R K : ℕ) : WindowSymbol R K :=
  ⟨fun _ _ _ => 0, ∅, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

lemma symZero_eval (R K : ℕ) (z : NatExtTorus) : (symZero R K).eval z = 0 := by
  simp [WindowSymbol.eval, symZero]

/-- The sum of two symbols of the same radius and cap.  (`Prop64.symAdd`
is the identical construction, but that module sits above `Lemma62` in the
import order, so it cannot be used here.) -/
def symAdd {R K : ℕ} (U V : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := U.coeff w r s + V.coeff w r s
  words := U.words ∪ V.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w r s (fun h => hw (Finset.mem_union_left _ h)),
      V.coeff_support w r s (fun h => hw (Finset.mem_union_right _ h)), add_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w r s h, V.mode_cap w r s h, add_zero]

/-- A scalar multiple of a symbol; mirror of `Prop64.symSmul`. -/
def symSmul {R K : ℕ} (c : ℂ) (U : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := c * U.coeff w r s
  words := U.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w r s hw, mul_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w r s h, mul_zero]

@[simp] lemma symAdd_coeff {R K : ℕ} (U V : WindowSymbol R K)
    (w : Fin (2 * R) → ℕ) (r s : ℤ) :
    (symAdd U V).coeff w r s = U.coeff w r s + V.coeff w r s := rfl

@[simp] lemma symSmul_coeff {R K : ℕ} (c : ℂ) (U : WindowSymbol R K)
    (w : Fin (2 * R) → ℕ) (r s : ℤ) :
    (symSmul c U).coeff w r s = c * U.coeff w r s := rfl

lemma symAdd_eval {R K : ℕ} (U V : WindowSymbol R K) (z : NatExtTorus) :
    (symAdd U V).eval z = U.eval z + V.eval z := by
  simp only [WindowSymbol.eval, symAdd_coeff, add_mul, Finset.sum_add_distrib]

lemma symSmul_eval {R K : ℕ} (c : ℂ) (U : WindowSymbol R K) (z : NatExtTorus) :
    (symSmul c U).eval z = c * U.eval z := by
  simp only [WindowSymbol.eval, symSmul_coeff, mul_assoc, Finset.mul_sum]

/-- Finite sums of symbols of a common radius and cap are symbols. -/
lemma exists_symbol_sum {R K : ℕ} :
    ∀ (n : ℕ) (V : Fin n → WindowSymbol R K),
      ∃ U : WindowSymbol R K, ∀ z, U.eval z = ∑ i, (V i).eval z := by
  intro n
  induction n with
  | zero => exact fun V => ⟨symZero R K, fun z => by simp [symZero_eval]⟩
  | succ n ihn =>
      intro V
      obtain ⟨U', hU'⟩ := ihn (fun i => V i.succ)
      refine ⟨symAdd (V 0) U', fun z => ?_⟩
      rw [symAdd_eval, hU', Fin.sum_univ_succ]

/-- **A monomial is approximated by a window symbol** of any radius
dominating both cylinder depths and any cap dominating the mode. -/
lemma mono_symbol_approx (d₁ d₂ : ℕ) (w₁ w₂ : ℕ → ℕ) (r s : ℤ) (R K : ℕ)
    (h1 : d₁ ≤ R) (h2 : d₂ ≤ R) (hK : r.natAbs + s.natAbs ≤ K)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ U : WindowSymbol R K,
      eLpNorm ((fun z : NatExtTorus =>
          (indC (Kwon1002.Prop41.cylinder d₁ w₁) z.1.1
            * indC (Kwon1002.Prop41.cylinder d₂ w₂) z.1.2)
          * (torusChar ((r:ℝ) * z.2.1) * torusChar ((s:ℝ) * z.2.2)))
        - U.eval) 2 hatMu0 < ENNReal.ofReal δ := by
  set δ' : ℝ := (δ/8)^2 with hδ'def
  obtain ⟨F₁, hF₁sub, hF₁vol⟩ :=
    exists_cylinder_refinement d₁ w₁ R h1 δ' (by positivity)
  obtain ⟨F₂, hF₂sub, hF₂vol⟩ :=
    exists_cylinder_refinement d₂ w₂ R h2 δ' (by positivity)
  refine ⟨monoSymbol R K (F₁ ×ˢ F₂) r s, ?_⟩
  set χ : ℝ × ℝ → ℂ := fun q => torusChar ((r:ℝ) * q.1) * torusChar ((s:ℝ) * q.2)
    with hχdef
  set a : ℝ → ℂ := indC (Kwon1002.Prop41.cylinder d₁ w₁) with hadef
  set b : ℝ → ℂ := indC (Kwon1002.Prop41.cylinder d₂ w₂) with hbdef
  set a' : ℝ → ℂ := fun x => ∑ u ∈ F₁, indC (cylW u) x with ha'def
  set b' : ℝ → ℂ := fun y => ∑ v ∈ F₂, indC (cylW v) y with hb'def
  set G : ℝ × ℝ → ℂ := fun p => a p.1 * b p.2 - a' p.1 * b' p.2 with hGdef
  -- almost-everywhere identification of the difference
  have haemu : ∀ᵐ z : NatExtTorus ∂hatMu0,
      z.1.1 ∈ Ioo (0:ℝ) 1 ∧ z.1.2 ∈ Ioo (0:ℝ) 1 := by
    rw [hatMu0_eq_prod, ae_iff]
    have hset : {z : NatExtTorus |
        ¬ (z.1.1 ∈ Ioo (0:ℝ) 1 ∧ z.1.2 ∈ Ioo (0:ℝ) 1)}
        = {p : ℝ × ℝ | ¬ (p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1)}
            ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
      ext z
      simp [Set.mem_prod]
    rw [hset, Measure.prod_prod]
    have h0 : hatNu {p : ℝ × ℝ | ¬ (p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1)} = 0 :=
      ae_iff.mp hatNu_ae_sq
    rw [h0, zero_mul]
  have hae : (fun z : NatExtTorus => (a z.1.1 * b z.1.2) * χ z.2)
        - (monoSymbol R K (F₁ ×ˢ F₂) r s).eval
      =ᵐ[hatMu0] fun z => G z.1 * χ z.2 := by
    filter_upwards [haemu] with z hz
    have heval := monoSymbol_eval R K (F₁ ×ˢ F₂) r s hK z
    have hsum := sum_pairWord_indicator F₁ F₂ z.1 hz.1 hz.2
    have hchar : torusChar ((r:ℝ) * z.2.1 + (s:ℝ) * z.2.2) = χ z.2 :=
      MonomialCore.torusChar_add _ _
    simp only [Pi.sub_apply]
    rw [heval, hsum, hchar, hGdef]
    ring
  rw [eLpNorm_congr_ae hae]
  -- measurability
  have hameas : Measurable a := measurable_indC (measurableSet_cylinder _ _)
  have hbmeas : Measurable b := measurable_indC (measurableSet_cylinder _ _)
  have ha'meas : Measurable a' :=
    Finset.measurable_sum _ fun u _ => measurable_indC (measurableSet_cylW u)
  have hb'meas : Measurable b' :=
    Finset.measurable_sum _ fun v _ => measurable_indC (measurableSet_cylW v)
  have hGmeas : Measurable G :=
    ((hameas.comp measurable_fst).mul (hbmeas.comp measurable_snd)).sub
      ((ha'meas.comp measurable_fst).mul (hb'meas.comp measurable_snd))
  have hχmeas : Measurable χ :=
    ((Prop42.continuous_torusChar.measurable).comp
        (measurable_const.mul measurable_fst)).mul
      ((Prop42.continuous_torusChar.measurable).comp
        (measurable_const.mul measurable_snd))
  -- factorize
  rw [hatMu0_eq_prod, eLpNorm_prodMul _ _ hGmeas hχmeas]
  -- the torus factor has norm at most one
  have hχnorm : eLpNorm χ 2
      ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) ≤ 1 := by
    have hbd : ∀ᵐ q ∂((volume : Measure (ℝ × ℝ)).restrict
        (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)), ‖χ q‖ ≤ 1 := by
      refine Filter.Eventually.of_forall fun q => ?_
      rw [hχdef]
      simp only [norm_mul, Prop42.norm_torusChar, mul_one]
      exact le_rfl
    have h := eLpNorm_le_of_ae_bound (p := (2:ℝ≥0∞)) hbd
    rw [measure_univ] at h
    simpa using h
  -- the Gauss factor: comparison and bilinear split
  set μ₁ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo 0 1) with hμ₁def
  have hdiffa : eLpNorm (fun x => a x - a' x) 2 μ₁ ≤ ENNReal.ofReal (δ/8) := by
    have hfun : (fun x => a x - a' x)
        = indC (Kwon1002.Prop41.cylinder d₁ w₁ \ ⋃ u ∈ F₁, cylW u) := by
      funext x
      exact congrFun (indC_sub_sum_cylW F₁ hF₁sub) x
    rw [hfun]
    rw [eLpNorm_indC _ ((measurableSet_cylinder d₁ w₁).diff
      (F₁.measurableSet_biUnion fun u _ => measurableSet_cylW u))]
    have hle : μ₁ (Kwon1002.Prop41.cylinder d₁ w₁ \ ⋃ u ∈ F₁, cylW u)
        ≤ ENNReal.ofReal δ' := by
      refine le_trans ?_ hF₁vol.le
      rw [hμ₁def, Measure.restrict_apply ((measurableSet_cylinder d₁ w₁).diff
        (F₁.measurableSet_biUnion fun u _ => measurableSet_cylW u))]
      exact measure_mono Set.inter_subset_left
    calc μ₁ (Kwon1002.Prop41.cylinder d₁ w₁ \ ⋃ u ∈ F₁, cylW u) ^ (1/2 : ℝ)
        ≤ (ENNReal.ofReal δ') ^ (1/2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
      _ = ENNReal.ofReal (δ/8) := by
          rw [hδ'def, ENNReal.ofReal_pow (by positivity),
            ← ENNReal.rpow_natCast (ENNReal.ofReal (δ/8)) 2, ← ENNReal.rpow_mul]
          norm_num
  have hdiffb : eLpNorm (fun y => b y - b' y) 2 μ₁ ≤ ENNReal.ofReal (δ/8) := by
    have hfun : (fun y => b y - b' y)
        = indC (Kwon1002.Prop41.cylinder d₂ w₂ \ ⋃ v ∈ F₂, cylW v) := by
      funext y
      exact congrFun (indC_sub_sum_cylW F₂ hF₂sub) y
    rw [hfun]
    rw [eLpNorm_indC _ ((measurableSet_cylinder d₂ w₂).diff
      (F₂.measurableSet_biUnion fun v _ => measurableSet_cylW v))]
    have hle : μ₁ (Kwon1002.Prop41.cylinder d₂ w₂ \ ⋃ v ∈ F₂, cylW v)
        ≤ ENNReal.ofReal δ' := by
      refine le_trans ?_ hF₂vol.le
      rw [hμ₁def, Measure.restrict_apply ((measurableSet_cylinder d₂ w₂).diff
        (F₂.measurableSet_biUnion fun v _ => measurableSet_cylW v))]
      exact measure_mono Set.inter_subset_left
    calc μ₁ (Kwon1002.Prop41.cylinder d₂ w₂ \ ⋃ v ∈ F₂, cylW v) ^ (1/2 : ℝ)
        ≤ (ENNReal.ofReal δ') ^ (1/2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
      _ = ENNReal.ofReal (δ/8) := by
          rw [hδ'def, ENNReal.ofReal_pow (by positivity),
            ← ENNReal.rpow_natCast (ENNReal.ofReal (δ/8)) 2, ← ENNReal.rpow_mul]
          norm_num
  have hbnorm : eLpNorm b 2 μ₁ ≤ 1 := by
    rw [hbdef, eLpNorm_indC _ (measurableSet_cylinder d₂ w₂)]
    exact ENNReal.rpow_le_one prob_le_one (by norm_num)
  have ha'norm : eLpNorm a' 2 μ₁ ≤ 1 := by
    have ha'ind : a' = indC (⋃ u ∈ F₁, cylW u) := by
      rw [ha'def, indC_finset_biUnion F₁ cylW fun u _ v _ huv => cylW_disjoint huv]
    rw [ha'ind, eLpNorm_indC _
      (F₁.measurableSet_biUnion fun u _ => measurableSet_cylW u)]
    exact ENNReal.rpow_le_one prob_le_one (by norm_num)
  have hGleb : eLpNorm G 2
      ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1))
      ≤ ENNReal.ofReal (δ/4) := by
    have hsplit : G = (fun p : ℝ × ℝ => (a p.1 - a' p.1) * b p.2)
        + fun p : ℝ × ℝ => a' p.1 * (b p.2 - b' p.2) := by
      funext p
      simp only [hGdef, Pi.add_apply]
      ring
    rw [hsplit, NatExtMeasure.restrict_unitSq_eq_prod]
    have hm1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (a p.1 - a' p.1) * b p.2) (μ₁.prod μ₁) :=
      (((hameas.sub ha'meas).comp measurable_fst).mul
        (hbmeas.comp measurable_snd)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => a' p.1 * (b p.2 - b' p.2)) (μ₁.prod μ₁) :=
      ((ha'meas.comp measurable_fst).mul
        ((hbmeas.sub hb'meas).comp measurable_snd)).aestronglyMeasurable
    calc eLpNorm ((fun p : ℝ × ℝ => (a p.1 - a' p.1) * b p.2)
            + fun p : ℝ × ℝ => a' p.1 * (b p.2 - b' p.2)) 2 (μ₁.prod μ₁)
        ≤ eLpNorm (fun p : ℝ × ℝ => (a p.1 - a' p.1) * b p.2) 2 (μ₁.prod μ₁)
          + eLpNorm (fun p : ℝ × ℝ => a' p.1 * (b p.2 - b' p.2)) 2 (μ₁.prod μ₁) :=
          eLpNorm_add_le hm1 hm2 one_le_two
      _ = eLpNorm (fun x => a x - a' x) 2 μ₁ * eLpNorm b 2 μ₁
          + eLpNorm a' 2 μ₁ * eLpNorm (fun y => b y - b' y) 2 μ₁ := by
          rw [eLpNorm_prodMul μ₁ μ₁ (hameas.sub ha'meas) hbmeas,
            eLpNorm_prodMul μ₁ μ₁ ha'meas (hbmeas.sub hb'meas)]
      _ ≤ ENNReal.ofReal (δ/8) * 1 + 1 * ENNReal.ofReal (δ/8) := by
          exact add_le_add (mul_le_mul' hdiffa hbnorm) (mul_le_mul' ha'norm hdiffb)
      _ = ENNReal.ofReal (δ/4) := by
          rw [mul_one, one_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  calc eLpNorm G 2 hatNu * eLpNorm χ 2
        ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1))
      ≤ eLpNorm G 2 hatNu * 1 := mul_le_mul' le_rfl hχnorm
    _ = eLpNorm G 2 hatNu := mul_one _
    _ ≤ 2 * eLpNorm G 2
        ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) :=
        eLpNorm_hatNu_le_two_mul G hGmeas
    _ ≤ 2 * ENNReal.ofReal (δ/4) := mul_le_mul' le_rfl hGleb
    _ = ENNReal.ofReal (δ/2) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
    _ < ENNReal.ofReal δ :=
        ENNReal.ofReal_lt_ofReal_iff hδ |>.mpr (by linarith)

/-- **Density of window-symbol evaluations in `L²(μ̂₀)`**: the statement
`Lemma62.cylinderChar_dense_L2` delegates to.  A span element of the
monomial class is converted into one window symbol: pad every cylinder to
the common radius (`mono_symbol_approx`), then add the symbols. -/
theorem cylinderChar_dense_L2_core (f : NatExtTorus → ℂ) (hf : MemLp f 2 hatMu0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (R K : ℕ) (U : WindowSymbol R K),
      eLpNorm (fun z => f z - U.eval z) 2 hatMu0 < ENNReal.ofReal ε := by
  obtain ⟨g, hgspan, hg⟩ := monoSet_span_dense hf (half_pos hε)
  obtain ⟨n, c, m, hrep⟩ := Submodule.mem_span_set'.mp hgspan
  -- the monomials in normal form
  have hmono : ∀ i : Fin n, ∃ (d₁ d₂ : ℕ) (w₁ w₂ : ℕ → ℕ) (r s : ℤ),
      (m i : NatExtTorus → ℂ) = fun z =>
        (indC (Kwon1002.Prop41.cylinder d₁ w₁) z.1.1
          * indC (Kwon1002.Prop41.cylinder d₂ w₂) z.1.2)
        * (torusChar ((r:ℝ) * z.2.1) * torusChar ((s:ℝ) * z.2.2)) := by
    intro i
    obtain ⟨s₂, hs₂, t₂, ht₂, hst⟩ := (m i).2
    obtain ⟨c₁, hc₁, c₂, hc₂, hcc⟩ := hs₂
    obtain ⟨χ₁, hχ₁, χ₂, hχ₂, hχχ⟩ := ht₂
    obtain ⟨d₁, w₁, rfl⟩ := hc₁
    obtain ⟨d₂, w₂, rfl⟩ := hc₂
    obtain ⟨r, rfl⟩ := hχ₁
    obtain ⟨sm, rfl⟩ := hχ₂
    exact ⟨d₁, d₂, w₁, w₂, r, sm, by rw [← hst, ← hcc, ← hχχ]⟩
  choose dd₁ dd₂ ww₁ ww₂ rr ss hmi using hmono
  set R : ℕ := Finset.univ.sup fun i => max (dd₁ i) (dd₂ i) with hRdef
  set K : ℕ := Finset.univ.sup fun i => (rr i).natAbs + (ss i).natAbs with hKdef
  have hR1 : ∀ i, dd₁ i ≤ R := fun i =>
    le_trans (le_max_left _ _)
      (Finset.le_sup (f := fun i => max (dd₁ i) (dd₂ i)) (Finset.mem_univ i))
  have hR2 : ∀ i, dd₂ i ≤ R := fun i =>
    le_trans (le_max_right _ _)
      (Finset.le_sup (f := fun i => max (dd₁ i) (dd₂ i)) (Finset.mem_univ i))
  have hKi : ∀ i, (rr i).natAbs + (ss i).natAbs ≤ K := fun i =>
    Finset.le_sup (f := fun i => (rr i).natAbs + (ss i).natAbs) (Finset.mem_univ i)
  set δ : ℝ := ε / 2 / (n + 1) with hδdef
  have hδ0 : 0 < δ := by positivity
  -- per-monomial symbols
  have hchoice : ∀ i : Fin n, ∃ U : WindowSymbol R K,
      eLpNorm ((m i : NatExtTorus → ℂ) - U.eval) 2 hatMu0
        < ENNReal.ofReal (δ / (‖c i‖ + 1)) := by
    intro i
    obtain ⟨U, hU⟩ := mono_symbol_approx (dd₁ i) (dd₂ i) (ww₁ i) (ww₂ i)
      (rr i) (ss i) R K (hR1 i) (hR2 i) (hKi i) (δ / (‖c i‖ + 1)) (by positivity)
    refine ⟨U, ?_⟩
    rw [hmi i]
    exact hU
  choose Us hUs using hchoice
  obtain ⟨U, hUeval⟩ := exists_symbol_sum n fun i => symSmul (c i) (Us i)
  refine ⟨R, K, U, ?_⟩
  have hUeval' : ∀ z, U.eval z = ∑ i, c i * (Us i).eval z := fun z => by
    rw [hUeval z]
    exact Finset.sum_congr rfl fun i _ => symSmul_eval _ _ _
  -- the span element is close to the symbol
  have hgU : eLpNorm (fun z => g z - U.eval z) 2 hatMu0 ≤ ENNReal.ofReal (ε/2) := by
    have hfun : (fun z => g z - U.eval z)
        = ∑ i, fun z => c i * ((m i : NatExtTorus → ℂ) z - (Us i).eval z) := by
      funext z
      rw [Finset.sum_apply]
      rw [hUeval' z, ← hrep]
      rw [Finset.sum_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    have hmim : ∀ i : Fin n, Measurable (m i : NatExtTorus → ℂ) := fun i =>
      measurable_of_mem_monoSet _ (m i).2
    have haesm : ∀ i : Fin n, AEStronglyMeasurable
        (fun z => c i * ((m i : NatExtTorus → ℂ) z - (Us i).eval z)) hatMu0 :=
      fun i => (measurable_const.mul
        ((hmim i).sub (measurable_eval (Us i)))).aestronglyMeasurable
    calc eLpNorm (∑ i, fun z => c i * ((m i : NatExtTorus → ℂ) z - (Us i).eval z))
          2 hatMu0
        ≤ ∑ i, eLpNorm (fun z => c i * ((m i : NatExtTorus → ℂ) z - (Us i).eval z))
            2 hatMu0 :=
          eLpNorm_sum_le (fun i _ => haesm i) one_le_two
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal δ := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hsm : (fun z => c i * ((m i : NatExtTorus → ℂ) z - (Us i).eval z))
              = c i • ((m i : NatExtTorus → ℂ) - (Us i).eval) := by
            funext z
            simp [smul_eq_mul]
          rw [hsm, eLpNorm_const_smul]
          calc ‖c i‖ₑ * eLpNorm ((m i : NatExtTorus → ℂ) - (Us i).eval) 2 hatMu0
              ≤ ENNReal.ofReal ‖c i‖ * ENNReal.ofReal (δ / (‖c i‖ + 1)) := by
                rw [← ofReal_norm_eq_enorm (c i)]
                exact mul_le_mul' le_rfl (hUs i).le
            _ = ENNReal.ofReal (‖c i‖ * (δ / (‖c i‖ + 1))) :=
                (ENNReal.ofReal_mul (norm_nonneg _)).symm
            _ ≤ ENNReal.ofReal δ := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [mul_div_assoc']
                rw [div_le_iff₀ (by positivity)]
                nlinarith [norm_nonneg (c i), hδ0.le]
      _ = n * ENNReal.ofReal δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (ε / 2) := by
          rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) by
              simp [ENNReal.ofReal_natCast],
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hn1 : (n : ℝ) / (n + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith
          calc (n : ℝ) * (ε / 2 / (n + 1)) = ((n : ℝ) / (n + 1)) * (ε / 2) := by ring
            _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right hn1 (by positivity)
            _ = ε / 2 := one_mul _
  -- assemble
  have hsplit : (fun z => f z - U.eval z) = (f - g) + fun z => g z - U.eval z := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  have hgm : Measurable g := measurable_of_mem_span measurable_of_mem_monoSet hgspan
  have hm1 : AEStronglyMeasurable (f - g) hatMu0 :=
    hf.aestronglyMeasurable.sub hgm.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun z => g z - U.eval z) hatMu0 :=
    (hgm.sub (measurable_eval U)).aestronglyMeasurable
  calc eLpNorm ((f - g) + fun z => g z - U.eval z) 2 hatMu0
      ≤ eLpNorm (f - g) 2 hatMu0 + eLpNorm (fun z => g z - U.eval z) 2 hatMu0 :=
        eLpNorm_add_le hm1 hm2 one_le_two
    _ ≤ eLpNorm (f - g) 2 hatMu0 + ENNReal.ofReal (ε/2) := add_le_add le_rfl hgU
    _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hg
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num

end SymbolConversion

end

end CylinderCharDense

end Kwon1002
