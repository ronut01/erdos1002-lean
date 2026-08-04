/-
Scratch file (BV-approximation agent): Kwon §3/§4.

GOAL.  Transfer the *Lipschitz* conditional multi-block mixing estimate
`Kwon1002.TransferIdentity.lemma_3_2'` (which rests on Wang's Lasota-Yorke
contraction `Erdos1002.gaussTransfer_strict_lipschitz_contraction`, rate
`527/540`, and is proved only for the Lipschitz seminorm) to the class
`BV(0,1)` that §4 actually feeds in.

ROUTE (attack (b): two-step / approximation).  We do *not* reprove the
contraction.  Instead, for each `δ > 0` we produce from a `BV(0,1)`
observable `g` an explicit Lipschitz observable `bvApprox δ g` with

* the same sup bound,
* Lipschitz constant `≤ 2K/δ`,
* `L¹(ν)` error `≤ 100 K δ`,

and interpolate: the Lipschitz estimate costs `ρ^M · (2K/δ)` while the
replacement costs `δ`, so `δ := ρ^{M/2}/2` balances them and yields BV
mixing at the rate `√(527/540)`, a genuine spectral gap, with the
constant depending on the BV norm exactly as Kwon's (17) says.
-/
import Kwon1002.TransferIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped ENNReal

namespace Kwon1002.BVMixing

open Erdos1002 Kwon1002.Transfer

noncomputable section

/-! ## 0. Kwon's BV class

`BVBoundedBy` below is reproduced **token-identically** from
`Kwon1002.Prop41.BVBoundedBy` (and from `TransferIdentity.BVBoundedBy'`);
`Kwon1002.Prop41` is not imported, for the same namespace reason recorded
in `TransferIdentity` §13. -/

def BVBoundedBy (K : ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ K) ∧
    eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K

/-! ## 1. Comparing `ν` with Lebesgue measure on `(0,1]`

`dν/dLeb = 1/(log 2 · (1+x)) ≤ 1/log 2`, so `ν ≤ (1/log 2) · Leb|_{(0,1]}`. -/

theorem gaussMeasure_le_smul_restrict :
    gaussMeasure ≤ ENNReal.ofReal (1 / Real.log 2) • volume.restrict (Ioc (0 : ℝ) 1) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hind : Measurable ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Ioc
  have hkey : ∀ x : ℝ, gaussDensity x ≤
      (ENNReal.ofReal (1 / Real.log 2) •
        ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞))) x := by
    intro x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [gaussDensity_eq_ofReal_on_unit hx]
      simp only [Pi.smul_apply, Set.indicator_of_mem hx, Pi.one_apply, smul_eq_mul, mul_one]
      apply ENNReal.ofReal_le_ofReal
      exact one_div_le_one_div_of_le hlog (by nlinarith [hx.1])
    · simp [gaussDensity, Set.indicator_of_notMem hx]
  calc gaussMeasure = volume.withDensity gaussDensity := gaussMeasure_eq_volume_withDensity
    _ ≤ volume.withDensity (ENNReal.ofReal (1 / Real.log 2) •
          ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞))) :=
        withDensity_mono (Filter.Eventually.of_forall hkey)
    _ = ENNReal.ofReal (1 / Real.log 2) •
          volume.withDensity ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞)) :=
        withDensity_smul _ hind
    _ = ENNReal.ofReal (1 / Real.log 2) • volume.restrict (Ioc (0 : ℝ) 1) := by
        rw [withDensity_indicator_one measurableSet_Ioc]

theorem integral_gaussMeasure_le_lebesgue {F : ℝ → ℝ} (hF0 : ∀ x, 0 ≤ F x)
    (hFi : IntegrableOn F (Ioc (0 : ℝ) 1) volume) :
    (∫ x, F x ∂gaussMeasure) ≤ (1 / Real.log 2) * ∫ x in Ioc (0 : ℝ) 1, F x := by
  have hc : ENNReal.ofReal (1 / Real.log 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hInt : Integrable F (ENNReal.ofReal (1 / Real.log 2) • volume.restrict (Ioc (0 : ℝ) 1)) :=
    hFi.smul_measure hc
  have h := integral_mono_measure gaussMeasure_le_smul_restrict
    (Filter.Eventually.of_forall hF0) hInt
  rw [integral_smul_measure] at h
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
  rwa [ENNReal.toReal_ofReal hpos, smul_eq_mul] at h

/-! ## 2. The approximation operator

`clampAt δ` folds `ℝ` onto `[δ, 1-δ] ⊆ (0,1)`; `bvApprox δ g` is the
`δ`-forward average of `g ∘ clampAt δ`, truncated at `0`. -/

def clampAt (δ t : ℝ) : ℝ := max δ (min (1 - δ) t)

def bvApprox (δ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  max 0 ((1 / δ) * ∫ t in x..(x + δ), g (clampAt δ t))

theorem clampAt_mem {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (t : ℝ) :
    clampAt δ t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact lt_of_lt_of_le hδ (le_max_left _ _)
  · rcases le_total (1 - δ) t with h | h
    · rw [clampAt, min_eq_left h, max_eq_right (by linarith)]; linarith
    · rw [clampAt, min_eq_right h]
      rcases le_total δ t with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; linarith

theorem clampAt_mem_Icc {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (t : ℝ) :
    clampAt δ t ∈ Icc (0 : ℝ) 1 :=
  Ioo_subset_Icc_self (clampAt_mem hδ hδ2 t)

theorem clampAt_monotone {δ : ℝ} : Monotone (clampAt δ) := by
  intro s t hst
  exact max_le_max le_rfl (min_le_min le_rfl hst)

theorem clampAt_eq_self {δ t : ℝ} (h1 : δ ≤ t) (h2 : t ≤ 1 - δ) : clampAt δ t = t := by
  rw [clampAt, min_eq_right h2, max_eq_right h1]

/-! ### The monotone decomposition used to run the estimates -/

def bvP (g : ℝ → ℝ) : ℝ → ℝ := variationOnFromTo g (Ioo (0 : ℝ) 1) (1 / 2)

def bvQ (g : ℝ → ℝ) : ℝ → ℝ := bvP g - g

theorem bvP_sub_bvQ (g : ℝ → ℝ) (x : ℝ) : bvP g x - bvQ g x = g x := by
  simp [bvQ]

theorem half_mem : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num

theorem locallyBV_of_le {K : ℝ} {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K) :
    LocallyBoundedVariationOn g (Ioo (0 : ℝ) 1) := by
  have : BoundedVariationOn g (Ioo (0 : ℝ) 1) :=
    ne_of_lt (lt_of_le_of_lt hV ENNReal.ofReal_lt_top)
  exact this.locallyBoundedVariationOn

theorem bvP_monotoneOn {K : ℝ} {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K) :
    MonotoneOn (bvP g) (Ioo (0 : ℝ) 1) :=
  variationOnFromTo.monotoneOn (locallyBV_of_le hV) half_mem

theorem bvQ_monotoneOn {K : ℝ} {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K) :
    MonotoneOn (bvQ g) (Ioo (0 : ℝ) 1) :=
  variationOnFromTo.sub_self_monotoneOn (locallyBV_of_le hV) half_mem

theorem abs_bvP_le {K : ℝ} (hK : 0 ≤ K) {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : |bvP g x| ≤ K := by
  have hmain : ∀ a b : ℝ, a ≤ b →
      (eVariationOn g (Ioo (0 : ℝ) 1 ∩ Icc a b)).toReal ≤ K := by
    intro a b _
    have h1 : eVariationOn g (Ioo (0 : ℝ) 1 ∩ Icc a b) ≤ ENNReal.ofReal K :=
      le_trans (eVariationOn.mono g inter_subset_left) hV
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal hK] at h2
  rcases le_total (1 / 2 : ℝ) x with h | h
  · rw [bvP, variationOnFromTo.eq_of_le _ _ h, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hmain _ _ h
  · rw [bvP, variationOnFromTo.eq_of_ge _ _ h, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hmain _ _ h

theorem abs_bvQ_le {K : ℝ} (hK : 0 ≤ K) {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K)
    (hsup : ∀ y ∈ Ioo (0 : ℝ) 1, |g y| ≤ K) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : |bvQ g x| ≤ 2 * K := by
  have h1 := abs_bvP_le hK hV hx
  have h2 := hsup x hx
  have : bvQ g x = bvP g x - g x := rfl
  rw [this]
  calc |bvP g x - g x| ≤ |bvP g x| + |g x| := abs_sub _ _
    _ ≤ K + K := add_le_add h1 h2
    _ = 2 * K := by ring

/-! ### Global monotone extensions -/

theorem monotone_comp_clampAt {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ioo (0 : ℝ) 1)) : Monotone (fun t => f (clampAt δ t)) := by
  intro s t hst
  exact hf (clampAt_mem hδ hδ2 s) (clampAt_mem hδ hδ2 t) (clampAt_monotone hst)

theorem intervalIntegrable_comp_clampAt {δ K : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {g : ℝ → ℝ} (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K) (a b : ℝ) :
    IntervalIntegrable (fun t => g (clampAt δ t)) volume a b := by
  have hP := (monotone_comp_clampAt hδ hδ2 (bvP_monotoneOn hV)).intervalIntegrable
    (μ := volume) (a := a) (b := b)
  have hQ := (monotone_comp_clampAt hδ hδ2 (bvQ_monotoneOn hV)).intervalIntegrable
    (μ := volume) (a := a) (b := b)
  have heq : (fun t => g (clampAt δ t))
      = fun t => bvP g (clampAt δ t) - bvQ g (clampAt δ t) := by
    funext t
    exact (bvP_sub_bvQ g (clampAt δ t)).symm
  rw [heq]
  exact hP.sub hQ

/-! ### The three easy properties of `bvApprox` -/

theorem bvApprox_nonneg (δ : ℝ) (g : ℝ → ℝ) (x : ℝ) : 0 ≤ bvApprox δ g x := le_max_left _ _

theorem abs_mollify_le {δ K : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K)
    (hsup : ∀ y ∈ Ioo (0 : ℝ) 1, |g y| ≤ K) (x : ℝ) :
    |(1 / δ) * ∫ t in x..(x + δ), g (clampAt δ t)| ≤ K := by
  have hbd : ∀ t ∈ uIoc x (x + δ), ‖g (clampAt δ t)‖ ≤ K := by
    intro t _
    exact hsup _ (clampAt_mem hδ hδ2 t)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / δ)]
  have hxd : |x + δ - x| = δ := by
    rw [show x + δ - x = δ by ring, abs_of_pos hδ]
  rw [Real.norm_eq_abs, hxd] at h
  calc (1 / δ) * |∫ t in x..(x + δ), g (clampAt δ t)| ≤ (1 / δ) * (K * δ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = K := by field_simp

theorem bvApprox_le {δ K : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hK : 0 ≤ K) {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K)
    (hsup : ∀ y ∈ Ioo (0 : ℝ) 1, |g y| ≤ K) (x : ℝ) : bvApprox δ g x ≤ K := by
  have h := abs_mollify_le hδ hδ2 hV hsup x
  exact max_le hK ((le_abs_self _).trans h)

theorem bvApprox_lipschitz {δ K : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K)
    (hsup : ∀ y ∈ Ioo (0 : ℝ) 1, |g y| ≤ K) (x y : ℝ) :
    |bvApprox δ g x - bvApprox δ g y| ≤ (2 * K / δ) * |x - y| := by
  set f : ℝ → ℝ := fun t => g (clampAt δ t) with hf
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    intervalIntegrable_comp_clampAt hδ hδ2 hV a b
  have hbd : ∀ t : ℝ, ‖f t‖ ≤ K := fun t => hsup _ (clampAt_mem hδ hδ2 t)
  have hsplit : (∫ t in x..(x + δ), f t) - (∫ t in y..(y + δ), f t)
      = (∫ t in x..y, f t) + (∫ t in (y + δ)..(x + δ), f t) := by
    have h1 : (∫ t in x..y, f t) + (∫ t in y..(y + δ), f t) + (∫ t in (y + δ)..(x + δ), f t)
        = ∫ t in x..(x + δ), f t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hii x y) (hii y (y + δ)),
        intervalIntegral.integral_add_adjacent_intervals (hii x (y + δ)) (hii (y + δ) (x + δ))]
    linarith [h1]
  have hb1 : |∫ t in x..y, f t| ≤ K * |x - y| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := f) (a := x) (b := y) (C := K) (fun t _ => hbd t)
    rw [Real.norm_eq_abs] at this
    calc |∫ t in x..y, f t| ≤ K * |y - x| := this
      _ = K * |x - y| := by rw [abs_sub_comm]
  have hb2 : |∫ t in (y + δ)..(x + δ), f t| ≤ K * |x - y| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := f) (a := y + δ) (b := x + δ) (C := K) (fun t _ => hbd t)
    rw [Real.norm_eq_abs] at this
    calc |∫ t in (y + δ)..(x + δ), f t| ≤ K * |x + δ - (y + δ)| := this
      _ = K * |x - y| := by ring_nf
  have hmain : |(1 / δ) * (∫ t in x..(x + δ), f t) - (1 / δ) * (∫ t in y..(y + δ), f t)|
      ≤ (2 * K / δ) * |x - y| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / δ), hsplit]
    have h3 : |(∫ t in x..y, f t) + (∫ t in (y + δ)..(x + δ), f t)| ≤ 2 * K * |x - y| := by
      calc |(∫ t in x..y, f t) + (∫ t in (y + δ)..(x + δ), f t)|
          ≤ |∫ t in x..y, f t| + |∫ t in (y + δ)..(x + δ), f t| := abs_add_le _ _
        _ ≤ K * |x - y| + K * |x - y| := add_le_add hb1 hb2
        _ = 2 * K * |x - y| := by ring
    calc (1 / δ) * |(∫ t in x..y, f t) + (∫ t in (y + δ)..(x + δ), f t)|
        ≤ (1 / δ) * (2 * K * |x - y|) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (2 * K / δ) * |x - y| := by field_simp
  have hlip : |max 0 ((1 / δ) * ∫ t in x..(x + δ), f t)
      - max 0 ((1 / δ) * ∫ t in y..(y + δ), f t)|
      ≤ |(1 / δ) * (∫ t in x..(x + δ), f t) - (1 / δ) * (∫ t in y..(y + δ), f t)| := by
    rw [max_comm 0 ((1 / δ) * ∫ t in x..(x + δ), f t),
      max_comm 0 ((1 / δ) * ∫ t in y..(y + δ), f t)]
    exact abs_max_sub_max_le_abs _ _ _
  exact hlip.trans hmain

theorem bvApprox_measurable {δ K : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {g : ℝ → ℝ}
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K)
    (hsup : ∀ y ∈ Ioo (0 : ℝ) 1, |g y| ≤ K) : Measurable (bvApprox δ g) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hsup _ half_mem)
  have hL : LipschitzWith (Real.toNNReal (2 * K / δ)) (bvApprox δ g) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      exact bvApprox_lipschitz hδ hδ2 hV hsup x y)
  exact hL.continuous.measurable

/-! ### The `L¹` estimate, the only place the variation bound is used -/

theorem interval_integral_le_const {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hb : ∀ x, f x ≤ C) :
    (∫ x in a..b, f x) ≤ (b - a) * C := by
  have h := intervalIntegral.integral_mono_on hab hf intervalIntegrable_const
    (fun x _ => hb x)
  rwa [intervalIntegral.integral_const, smul_eq_mul] at h

theorem const_le_interval_integral {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hb : ∀ x, C ≤ f x) :
    (b - a) * C ≤ ∫ x in a..b, f x := by
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hf
    (fun x _ => hb x)
  rwa [intervalIntegral.integral_const, smul_eq_mul] at h

theorem intervalIntegrable_of_unit_bound {h : ℝ → ℝ} {C : ℝ} (hm : Measurable h)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ‖h x‖ ≤ C) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb' : b ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable h volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := C) ?_ hm.aestronglyMeasurable ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    refine hb x ⟨?_, ?_⟩
    · exact le_trans (le_min ha.1 hb'.1) (le_of_lt hx.1)
    · exact le_trans hx.2 (max_le ha.2 hb'.2)

theorem log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2⁻¹ by norm_num)
  rw [Real.log_inv] at h
  linarith

theorem bvApprox_L1 {δ K : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hK : 1 ≤ K) {g : ℝ → ℝ}
    (hgm : Measurable g)
    (h0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ g y) (hub : ∀ y ∈ Icc (0 : ℝ) 1, g y ≤ K)
    (hV : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K) :
    (∫ y, |g y - bvApprox δ g y| ∂gaussMeasure) ≤ 100 * K * δ := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hsup : ∀ y ∈ Ioo (0 : ℝ) 1, |g y| ≤ K := by
    intro y hy
    have hy' : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
    rw [abs_of_nonneg (h0 y hy')]; exact hub y hy'
  set P : ℝ → ℝ := fun t => bvP g (clampAt δ t) with hPdef
  set Q : ℝ → ℝ := fun t => bvQ g (clampAt δ t) with hQdef
  have hPmono : Monotone P := monotone_comp_clampAt hδ hδ2 (bvP_monotoneOn hV)
  have hQmono : Monotone Q := monotone_comp_clampAt hδ hδ2 (bvQ_monotoneOn hV)
  have hPb : ∀ t, |P t| ≤ K := fun t => abs_bvP_le hK0 hV (clampAt_mem hδ hδ2 t)
  have hQb : ∀ t, |Q t| ≤ 2 * K := fun t => abs_bvQ_le hK0 hV hsup (clampAt_mem hδ hδ2 t)
  have hgc : ∀ t, g (clampAt δ t) = P t - Q t := fun t => (bvP_sub_bvQ g (clampAt δ t)).symm
  set D : ℝ → ℝ := fun x => (P (x + δ) - P x) + (Q (x + δ) - Q x) with hDdef
  have hD0 : ∀ x, 0 ≤ D x := by
    intro x
    have h1 : P x ≤ P (x + δ) := hPmono (by linarith)
    have h2 : Q x ≤ Q (x + δ) := hQmono (by linarith)
    simp only [hDdef]; linarith
  have hPsm : Monotone (fun x : ℝ => P (x + δ)) := fun u v h => hPmono (by linarith)
  have hQsm : Monotone (fun x : ℝ => Q (x + δ)) := fun u v h => hQmono (by linarith)
  have hPii : ∀ a b : ℝ, IntervalIntegrable P volume a b := fun a b =>
    hPmono.intervalIntegrable (μ := volume)
  have hQii : ∀ a b : ℝ, IntervalIntegrable Q volume a b := fun a b =>
    hQmono.intervalIntegrable (μ := volume)
  have hPsii : ∀ a b : ℝ, IntervalIntegrable (fun x => P (x + δ)) volume a b := fun a b =>
    hPsm.intervalIntegrable (μ := volume)
  have hQsii : ∀ a b : ℝ, IntervalIntegrable (fun x => Q (x + δ)) volume a b := fun a b =>
    hQsm.intervalIntegrable (μ := volume)
  have hDii : ∀ a b : ℝ, IntervalIntegrable D volume a b := fun a b =>
    ((hPsii a b).sub (hPii a b)).add ((hQsii a b).sub (hQii a b))
  -- (i) the shift estimate for a bounded monotone function
  have hshift : ∀ (R : ℝ → ℝ) (C : ℝ), Monotone R → (∀ t, |R t| ≤ C) →
      (∀ a b : ℝ, IntervalIntegrable R volume a b) →
      (∫ x in (0 : ℝ)..1, (R (x + δ) - R x)) ≤ 2 * C * δ := by
    intro R C hRm hRb hRii
    have hRsm : Monotone (fun x : ℝ => R (x + δ)) := fun u v h => hRm (by linarith)
    have e1 : (∫ x in (0 : ℝ)..1, (R (x + δ) - R x))
        = (∫ x in (0 : ℝ)..1, R (x + δ)) - ∫ x in (0 : ℝ)..1, R x :=
      intervalIntegral.integral_sub (hRsm.intervalIntegrable (μ := volume)) (hRii 0 1)
    have e2 : (∫ x in (0 : ℝ)..1, R (x + δ)) = ∫ x in (0 + δ)..(1 + δ), R x :=
      intervalIntegral.integral_comp_add_right R δ
    have e3 : (∫ x in (0 + δ : ℝ)..(1 + δ), R x)
        = (∫ x in (0 + δ : ℝ)..1, R x) + ∫ x in (1 : ℝ)..(1 + δ), R x :=
      (intervalIntegral.integral_add_adjacent_intervals (hRii _ _) (hRii _ _)).symm
    have e4 : (∫ x in (0 : ℝ)..1, R x)
        = (∫ x in (0 : ℝ)..(0 + δ), R x) + ∫ x in (0 + δ : ℝ)..1, R x :=
      (intervalIntegral.integral_add_adjacent_intervals (hRii _ _) (hRii _ _)).symm
    have b1 : (∫ x in (1 : ℝ)..(1 + δ), R x) ≤ (1 + δ - 1) * C :=
      interval_integral_le_const (by linarith) (hRii _ _)
        (fun x => (le_abs_self _).trans (hRb x))
    have b2 : (0 + δ - 0) * (-C) ≤ ∫ x in (0 : ℝ)..(0 + δ), R x :=
      const_le_interval_integral (by linarith) (hRii _ _)
        (fun x => neg_le_of_abs_le (hRb x))
    rw [e1, e2, e3, e4]
    nlinarith [b1, b2]
  have hDint : (∫ x in (0 : ℝ)..1, D x) ≤ 6 * K * δ := by
    have hsplit : (∫ x in (0 : ℝ)..1, D x)
        = (∫ x in (0 : ℝ)..1, (P (x + δ) - P x)) + ∫ x in (0 : ℝ)..1, (Q (x + δ) - Q x) := by
      rw [← intervalIntegral.integral_add ((hPsii 0 1).sub (hPii 0 1))
        ((hQsii 0 1).sub (hQii 0 1))]
    have h1 := hshift P K hPmono hPb hPii
    have h2 := hshift Q (2 * K) hQmono hQb hQii
    rw [hsplit]
    nlinarith [h1, h2]
  -- (ii) the pointwise estimate away from the two end zones
  have hmid : ∀ y ∈ Icc (2 * δ) (1 - 2 * δ), |g y - bvApprox δ g y| ≤ D y := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hδy : δ ≤ y := by linarith
    have hy1' : y ≤ 1 - δ := by linarith
    have hclampy : clampAt δ y = y := clampAt_eq_self hδy hy1'
    have hgy : g y = P y - Q y := by
      have h := hgc y
      rwa [hclampy] at h
    have hval : ∀ t ∈ Icc y (y + δ), |g (clampAt δ t) - g y| ≤ D y := by
      intro t ht
      rw [hgc t, hgy]
      have h1 : P y ≤ P t := hPmono ht.1
      have h2 : P t ≤ P (y + δ) := hPmono ht.2
      have h3 : Q y ≤ Q t := hQmono ht.1
      have h4 : Q t ≤ Q (y + δ) := hQmono ht.2
      have hre : P t - Q t - (P y - Q y) = (P t - P y) - (Q t - Q y) := by ring
      rw [hre, abs_le]
      simp only [hDdef]
      constructor <;> linarith
    have hsub : (∫ t in y..(y + δ), (g (clampAt δ t) - g y))
        = (∫ t in y..(y + δ), g (clampAt δ t)) - δ * g y := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_comp_clampAt hδ hδ2 hV _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
      congr 2
      ring
    have hbnd : |(∫ t in y..(y + δ), g (clampAt δ t)) - δ * g y| ≤ D y * δ := by
      rw [← hsub]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => g (clampAt δ t) - g y) (a := y) (b := y + δ) (C := D y)
        (fun t ht => by
          rw [uIoc_of_le (by linarith)] at ht
          exact hval t ⟨ht.1.le, ht.2⟩)
      rw [Real.norm_eq_abs] at h
      calc |∫ t in y..(y + δ), (g (clampAt δ t) - g y)| ≤ D y * |y + δ - y| := h
        _ = D y * δ := by rw [show y + δ - y = δ by ring, abs_of_pos hδ]
    have hmnn : 0 ≤ (1 / δ) * ∫ t in y..(y + δ), g (clampAt δ t) := by
      refine mul_nonneg (by positivity) ?_
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => h0 _ (clampAt_mem_Icc hδ hδ2 t))
    have happ : bvApprox δ g y = (1 / δ) * ∫ t in y..(y + δ), g (clampAt δ t) := by
      rw [bvApprox, max_eq_right hmnn]
    rw [happ]
    have hre2 : g y - (1 / δ) * (∫ t in y..(y + δ), g (clampAt δ t))
        = -((1 / δ) * ((∫ t in y..(y + δ), g (clampAt δ t)) - δ * g y)) := by
      field_simp
      ring
    rw [hre2, abs_neg, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / δ by positivity)]
    calc (1 / δ) * |(∫ t in y..(y + δ), g (clampAt δ t)) - δ * g y| ≤ (1 / δ) * (D y * δ) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ = D y := by field_simp
  -- (iii) the global sup bound
  have hFm : Measurable (fun y => |g y - bvApprox δ g y|) :=
    (hgm.sub (bvApprox_measurable hδ hδ2 hV hsup)).abs
  have hF0 : ∀ y, 0 ≤ |g y - bvApprox δ g y| := fun _ => abs_nonneg _
  have hFb : ∀ y ∈ Icc (0 : ℝ) 1, ‖|g y - bvApprox δ g y|‖ ≤ 2 * K := by
    intro y hy
    rw [Real.norm_eq_abs, abs_abs]
    have e1 : |g y| ≤ K := by rw [abs_of_nonneg (h0 y hy)]; exact hub y hy
    have e2 : |bvApprox δ g y| ≤ K := by
      rw [abs_of_nonneg (bvApprox_nonneg δ g y)]
      exact bvApprox_le hδ hδ2 hK0 hV hsup y
    calc |g y - bvApprox δ g y| ≤ |g y| + |bvApprox δ g y| := by
          have := abs_add_le (g y) (-(bvApprox δ g y))
          simpa [sub_eq_add_neg] using this
      _ ≤ K + K := add_le_add e1 e2
      _ = 2 * K := by ring
  have hFii : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      IntervalIntegrable (fun y => |g y - bvApprox δ g y|) volume a b := fun a b ha hb =>
    intervalIntegrable_of_unit_bound hFm hFb ha hb
  -- (iv) assemble on `(0,1]`
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hmem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hmem2 : (2 * δ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmem3 : (1 - 2 * δ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hlebesgue : (∫ y in Ioc (0 : ℝ) 1, |g y - bvApprox δ g y|) ≤ 14 * K * δ := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have e1 : (∫ y in (0 : ℝ)..1, |g y - bvApprox δ g y|)
        = ((∫ y in (0 : ℝ)..(2 * δ), |g y - bvApprox δ g y|)
            + ∫ y in (2 * δ)..(1 - 2 * δ), |g y - bvApprox δ g y|)
          + ∫ y in (1 - 2 * δ)..1, |g y - bvApprox δ g y| := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hFii _ _ hmem0 hmem2) (hFii _ _ hmem2 hmem3),
        intervalIntegral.integral_add_adjacent_intervals
        (hFii _ _ hmem0 hmem3) (hFii _ _ hmem3 hmem1)]
    have b1 : (∫ y in (0 : ℝ)..(2 * δ), |g y - bvApprox δ g y|) ≤ 4 * K * δ := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun y => |g y - bvApprox δ g y|) (a := (0 : ℝ)) (b := 2 * δ) (C := 2 * K)
        (fun t ht => by
          rw [uIoc_of_le (by linarith)] at ht
          exact hFb t ⟨ht.1.le, by linarith [ht.2]⟩)
      rw [Real.norm_eq_abs] at h
      have h2 : (∫ y in (0 : ℝ)..(2 * δ), |g y - bvApprox δ g y|) ≤ 2 * K * |2 * δ - 0| :=
        le_trans (le_abs_self _) h
      rw [show (2 : ℝ) * δ - 0 = 2 * δ by ring, abs_of_pos (by linarith : (0 : ℝ) < 2 * δ)] at h2
      linarith
    have b3 : (∫ y in (1 - 2 * δ)..1, |g y - bvApprox δ g y|) ≤ 4 * K * δ := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun y => |g y - bvApprox δ g y|) (a := 1 - 2 * δ) (b := (1 : ℝ)) (C := 2 * K)
        (fun t ht => by
          rw [uIoc_of_le (by linarith)] at ht
          exact hFb t ⟨by linarith [ht.1], ht.2⟩)
      rw [Real.norm_eq_abs] at h
      have h2 : (∫ y in (1 - 2 * δ)..(1 : ℝ), |g y - bvApprox δ g y|)
          ≤ 2 * K * |1 - (1 - 2 * δ)| := le_trans (le_abs_self _) h
      rw [show (1 : ℝ) - (1 - 2 * δ) = 2 * δ by ring,
        abs_of_pos (by linarith : (0 : ℝ) < 2 * δ)] at h2
      linarith
    have b2 : (∫ y in (2 * δ)..(1 - 2 * δ), |g y - bvApprox δ g y|) ≤ 6 * K * δ := by
      rcases le_total (2 * δ) (1 - 2 * δ) with hc | hc
      · have hmono := intervalIntegral.integral_mono_on hc
          (hFii _ _ hmem2 hmem3) (hDii _ _) (fun y hy => hmid y hy)
        have hext : (∫ y in (2 * δ)..(1 - 2 * δ), D y) ≤ ∫ y in (0 : ℝ)..1, D y := by
          have e2 : (∫ y in (0 : ℝ)..1, D y)
              = ((∫ y in (0 : ℝ)..(2 * δ), D y) + ∫ y in (2 * δ)..(1 - 2 * δ), D y)
                + ∫ y in (1 - 2 * δ)..1, D y := by
            rw [intervalIntegral.integral_add_adjacent_intervals (hDii _ _) (hDii _ _),
              intervalIntegral.integral_add_adjacent_intervals (hDii _ _) (hDii _ _)]
          have p1 : 0 ≤ ∫ y in (0 : ℝ)..(2 * δ), D y :=
            intervalIntegral.integral_nonneg (by linarith) (fun t _ => hD0 t)
          have p2 : 0 ≤ ∫ y in (1 - 2 * δ)..1, D y :=
            intervalIntegral.integral_nonneg (by linarith) (fun t _ => hD0 t)
          rw [e2]; linarith
        linarith [hmono, hext, hDint]
      · have hsym : (∫ y in (2 * δ)..(1 - 2 * δ), |g y - bvApprox δ g y|)
            = -∫ y in (1 - 2 * δ)..(2 * δ), |g y - bvApprox δ g y| :=
          intervalIntegral.integral_symm (1 - 2 * δ) (2 * δ)
        have hnn : (0 : ℝ) ≤ ∫ y in (1 - 2 * δ)..(2 * δ), |g y - bvApprox δ g y| :=
          intervalIntegral.integral_nonneg hc (fun t _ => hF0 t)
        have hpos : (0 : ℝ) ≤ 6 * K * δ := by positivity
        rw [hsym]
        linarith
    rw [e1]; linarith
  -- (v) transfer to `ν`
  have hIntOn : IntegrableOn (fun y => |g y - bvApprox δ g y|) (Ioc (0 : ℝ) 1) volume := by
    refine Measure.integrableOn_of_bounded (M := 2 * K) (by simp) hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact hFb y ⟨hy.1.le, hy.2⟩
  have hstep := integral_gaussMeasure_le_lebesgue hF0 hIntOn
  have hlog : (1 : ℝ) / Real.log 2 ≤ 2 := by
    have h := log_two_ge_half
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hnn : (0 : ℝ) ≤ ∫ y in Ioc (0 : ℝ) 1, |g y - bvApprox δ g y| :=
    integral_nonneg (fun _ => hF0 _)
  calc (∫ y, |g y - bvApprox δ g y| ∂gaussMeasure)
      ≤ (1 / Real.log 2) * ∫ y in Ioc (0 : ℝ) 1, |g y - bvApprox δ g y| := hstep
    _ ≤ 2 * (14 * K * δ) := by
        have hpos : (0 : ℝ) < 1 / Real.log 2 := by
          have := log_two_ge_half; positivity
        nlinarith [hlebesgue, hnn, hlog, hpos]
    _ ≤ 100 * K * δ := by nlinarith [hK0, hδ.le]

/-! ## 3. Replacing the observables in a block list

Everything here is exact bookkeeping: a multilinear telescoping of
`blockProduct` and of `blockMean`, plus the `ν`-invariance of the Gauss
orbit (`Erdos1002.integral_comp_gaussOrbit`) which converts each
`∫ |gᵢ - hᵢ| ∘ T^{tᵢ}` into `∫ |gᵢ - hᵢ|`. -/

def mapObs (F : (ℝ → ℝ) → ℝ → ℝ) (bs : List (ℕ × (ℝ → ℝ))) : List (ℕ × (ℝ → ℝ)) :=
  bs.map (fun p => (p.1, F p.2))

theorem mapObs_length (F : (ℝ → ℝ) → ℝ → ℝ) (bs : List (ℕ × (ℝ → ℝ))) :
    (mapObs F bs).length = bs.length := by simp [mapObs]

theorem mem_mapObs {F : (ℝ → ℝ) → ℝ → ℝ} {bs : List (ℕ × (ℝ → ℝ))} {q : ℕ × (ℝ → ℝ)}
    (h : q ∈ mapObs F bs) : ∃ p ∈ bs, q = (p.1, F p.2) := by
  obtain ⟨p, hp, hq⟩ := List.mem_map.1 h
  exact ⟨p, hp, hq.symm⟩

def l1Sum (F : (ℝ → ℝ) → ℝ → ℝ) (bs : List (ℕ × (ℝ → ℝ))) : ℝ :=
  (bs.map (fun p => ∫ y, |p.2 y - F p.2 y| ∂gaussMeasure)).sum

theorem l1Sum_nonneg (F : (ℝ → ℝ) → ℝ → ℝ) (bs : List (ℕ × (ℝ → ℝ))) : 0 ≤ l1Sum F bs := by
  refine List.sum_nonneg ?_
  intro z hz
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hz
  exact integral_nonneg (fun _ => abs_nonneg _)

theorem integrable_of_unit_bound {f : ℝ → ℝ} {C : ℝ} (hm : Measurable f)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ C) : Integrable f gaussMeasure := by
  refine Integrable.of_bound hm.aestronglyMeasurable C ?_
  filter_upwards [gaussMeasure_unit_ae] with x hx
  rw [Real.norm_eq_abs]
  exact hb x ⟨hx.1.le, hx.2⟩

theorem integral_unit_bounds {A : ℝ} {f : ℝ → ℝ} (hm : Measurable f)
    (h0 : GaussUnitNonnegative f) (hub : GaussUnitUpperBound A f) :
    0 ≤ (∫ y, f y ∂gaussMeasure) ∧ (∫ y, f y ∂gaussMeasure) ≤ A := by
  have hint : Integrable f gaussMeasure :=
    integrable_of_unit_bound hm (fun x hx => by
      rw [abs_of_nonneg (h0 hx)]; exact hub hx)
  constructor
  · refine integral_nonneg_of_ae ?_
    filter_upwards [gaussMeasure_unit_ae] with x hx
    exact h0 ⟨hx.1.le, hx.2⟩
  · have hae : ∀ᵐ x ∂gaussMeasure, f x ≤ A := by
      filter_upwards [gaussMeasure_unit_ae] with x hx
      exact hub ⟨hx.1.le, hx.2⟩
    simpa using integral_mono_ae hint (integrable_const A) hae

theorem blockMean_bounds {A : ℝ} (bs : List (ℕ × (ℝ → ℝ)))
    (hm : ∀ p ∈ bs, Measurable p.2)
    (h0 : ∀ p ∈ bs, GaussUnitNonnegative p.2)
    (hub : ∀ p ∈ bs, GaussUnitUpperBound A p.2) :
    0 ≤ blockMean bs ∧ blockMean bs ≤ A ^ bs.length := by
  induction bs with
  | nil => simp
  | cons p rest ih =>
      have hrm : ∀ q ∈ rest, Measurable q.2 := fun q hq => hm q (by simp [hq])
      have hr0 : ∀ q ∈ rest, GaussUnitNonnegative q.2 := fun q hq => h0 q (by simp [hq])
      have hrub : ∀ q ∈ rest, GaussUnitUpperBound A q.2 := fun q hq => hub q (by simp [hq])
      obtain ⟨hB0, hBA⟩ := ih hrm hr0 hrub
      obtain ⟨ha0, haA⟩ := integral_unit_bounds (hm p (by simp)) (h0 p (by simp)) (hub p (by simp))
      constructor
      · rw [blockMean_cons]; exact mul_nonneg ha0 hB0
      · rw [blockMean_cons]
        calc (∫ x, p.2 x ∂gaussMeasure) * blockMean rest ≤ A * A ^ rest.length :=
              mul_le_mul haA hBA hB0 (ha0.trans haA)
          _ = A ^ (rest.length + 1) := by ring

theorem integral_abs_blockProduct_sub_le (F : (ℝ → ℝ) → ℝ → ℝ) {A : ℝ} (hA : 1 ≤ A) :
    ∀ bs : List (ℕ × (ℝ → ℝ)),
      (∀ p ∈ bs, Measurable p.2) → (∀ p ∈ bs, Measurable (F p.2)) →
      (∀ p ∈ bs, GaussUnitNonnegative p.2) → (∀ p ∈ bs, GaussUnitUpperBound A p.2) →
      (∀ p ∈ bs, GaussUnitNonnegative (F p.2)) → (∀ p ∈ bs, GaussUnitUpperBound A (F p.2)) →
      (∫ x, |blockProduct bs x - blockProduct (mapObs F bs) x| ∂gaussMeasure)
        ≤ A ^ bs.length * l1Sum F bs := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  intro bs
  induction bs with
  | nil => intro _ _ _ _ _ _; simp [mapObs, l1Sum]
  | cons p rest ih =>
    intro hm hFm h0 hub hF0 hFub
    have hrm : ∀ q ∈ rest, Measurable q.2 := fun q hq => hm q (by simp [hq])
    have hrFm : ∀ q ∈ rest, Measurable (F q.2) := fun q hq => hFm q (by simp [hq])
    have hr0 : ∀ q ∈ rest, GaussUnitNonnegative q.2 := fun q hq => h0 q (by simp [hq])
    have hrub : ∀ q ∈ rest, GaussUnitUpperBound A q.2 := fun q hq => hub q (by simp [hq])
    have hrF0 : ∀ q ∈ rest, GaussUnitNonnegative (F q.2) := fun q hq => hF0 q (by simp [hq])
    have hrFub : ∀ q ∈ rest, GaussUnitUpperBound A (F q.2) := fun q hq => hFub q (by simp [hq])
    have hIH := ih hrm hrFm hr0 hrub hrF0 hrFub
    -- the mapped tail hypotheses, in the form the `blockProduct` lemmas want
    have hmap0 : ∀ q ∈ mapObs F rest, GaussUnitNonnegative q.2 := by
      intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hrF0 u hu
    have hmapub : ∀ q ∈ mapObs F rest, GaussUnitUpperBound A q.2 := by
      intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hrFub u hu
    have hmapm : ∀ q ∈ mapObs F rest, Measurable q.2 := by
      intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hrFm u hu
    set n := rest.length with hn
    set G : ℝ → ℝ := fun y =>
      A ^ n * |p.2 y - F p.2 y| +
        A * |blockProduct rest y - blockProduct (mapObs F rest) y| with hGdef
    have hGm : Measurable G := by
      refine Measurable.add ?_ ?_
      · exact ((hm p (by simp)).sub (hFm p (by simp))).abs.const_mul _
      · exact (((measurable_blockProduct rest hrm).sub
          (measurable_blockProduct (mapObs F rest) hmapm)).abs).const_mul _
    -- pointwise domination
    have hpt : ∀ x ∈ Icc (0 : ℝ) 1,
        |blockProduct (p :: rest) x - blockProduct (mapObs F (p :: rest)) x|
          ≤ G (gaussOrbit p.1 x) := by
      intro x hx
      have ho : gaussOrbit p.1 x ∈ Icc (0 : ℝ) 1 := gaussOrbit_mem_Icc _ hx
      set o := gaussOrbit p.1 x with hodef
      have hP0 : 0 ≤ blockProduct rest o := blockProduct_nonneg rest hr0 ho
      have hPA : blockProduct rest o ≤ A ^ n := blockProduct_le rest hr0 hrub ho
      have hA' : 0 ≤ F p.2 o := hF0 p (by simp) ho
      have hA'' : F p.2 o ≤ A := hFub p (by simp) ho
      have hsplit : p.2 o * blockProduct rest o
            - F p.2 o * blockProduct (mapObs F rest) o
          = (p.2 o - F p.2 o) * blockProduct rest o
            + F p.2 o * (blockProduct rest o - blockProduct (mapObs F rest) o) := by ring
      have hmapeq : blockProduct (mapObs F (p :: rest)) x
          = F p.2 o * blockProduct (mapObs F rest) o := rfl
      rw [blockProduct_cons, hmapeq, hsplit]
      calc |(p.2 o - F p.2 o) * blockProduct rest o
              + F p.2 o * (blockProduct rest o - blockProduct (mapObs F rest) o)|
          ≤ |(p.2 o - F p.2 o) * blockProduct rest o|
              + |F p.2 o * (blockProduct rest o - blockProduct (mapObs F rest) o)| :=
            abs_add_le _ _
        _ = |p.2 o - F p.2 o| * blockProduct rest o
              + F p.2 o * |blockProduct rest o - blockProduct (mapObs F rest) o| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hA']
        _ ≤ A ^ n * |p.2 o - F p.2 o|
              + A * |blockProduct rest o - blockProduct (mapObs F rest) o| := by
            have h1 : |p.2 o - F p.2 o| * blockProduct rest o ≤ A ^ n * |p.2 o - F p.2 o| := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hPA (abs_nonneg _)
            have h2 : F p.2 o * |blockProduct rest o - blockProduct (mapObs F rest) o|
                ≤ A * |blockProduct rest o - blockProduct (mapObs F rest) o| :=
              mul_le_mul_of_nonneg_right hA'' (abs_nonneg _)
            linarith
    -- integrability bookkeeping
    have hLm : Measurable
        (fun x => |blockProduct (p :: rest) x - blockProduct (mapObs F (p :: rest)) x|) := by
      refine (Measurable.sub ?_ ?_).abs
      · exact measurable_blockProduct (p :: rest) hm
      · refine measurable_blockProduct _ ?_
        intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hFm u hu
    have hGb : ∀ y ∈ Icc (0 : ℝ) 1, |G y| ≤ A ^ n * (2 * A) + A * (2 * A ^ n) := by
      intro y hy
      have h1 : |p.2 y - F p.2 y| ≤ 2 * A := by
        have e1 : |p.2 y| ≤ A := by rw [abs_of_nonneg (h0 p (by simp) hy)]; exact hub p (by simp) hy
        have e2 : |F p.2 y| ≤ A := by
          rw [abs_of_nonneg (hF0 p (by simp) hy)]; exact hFub p (by simp) hy
        calc |p.2 y - F p.2 y| ≤ |p.2 y| + |F p.2 y| := by
              have := abs_add_le (p.2 y) (-(F p.2 y))
              simpa [sub_eq_add_neg] using this
          _ ≤ A + A := add_le_add e1 e2
          _ = 2 * A := by ring
      have h2 : |blockProduct rest y - blockProduct (mapObs F rest) y| ≤ 2 * A ^ n := by
        have e1 : |blockProduct rest y| ≤ A ^ n := by
          rw [abs_of_nonneg (blockProduct_nonneg rest hr0 hy)]
          exact blockProduct_le rest hr0 hrub hy
        have e2 : |blockProduct (mapObs F rest) y| ≤ A ^ n := by
          rw [abs_of_nonneg (blockProduct_nonneg _ hmap0 hy)]
          have := blockProduct_le (mapObs F rest) hmap0 hmapub hy
          rwa [mapObs_length] at this
        calc |blockProduct rest y - blockProduct (mapObs F rest) y|
            ≤ |blockProduct rest y| + |blockProduct (mapObs F rest) y| := by
              have := abs_add_le (blockProduct rest y) (-(blockProduct (mapObs F rest) y))
              simpa [sub_eq_add_neg] using this
          _ ≤ A ^ n + A ^ n := add_le_add e1 e2
          _ = 2 * A ^ n := by ring
      have hAn : (0 : ℝ) ≤ A ^ n := pow_nonneg hA0 n
      set u1 := |p.2 y - F p.2 y| with hu1def
      set u2 := |blockProduct rest y - blockProduct (mapObs F rest) y| with hu2def
      have hu10 : (0 : ℝ) ≤ u1 := abs_nonneg _
      have hu20 : (0 : ℝ) ≤ u2 := abs_nonneg _
      have hGy : G y = A ^ n * u1 + A * u2 := rfl
      rw [hGy, abs_of_nonneg (add_nonneg (mul_nonneg hAn hu10) (mul_nonneg hA0 hu20))]
      have e1 := mul_le_mul_of_nonneg_left h1 hAn
      have e2 := mul_le_mul_of_nonneg_left h2 hA0
      linarith
    have hLb : ∀ x ∈ Icc (0 : ℝ) 1,
        |blockProduct (p :: rest) x - blockProduct (mapObs F (p :: rest)) x|
          ≤ A ^ n * (2 * A) + A * (2 * A ^ n) := by
      intro x hx
      exact (hpt x hx).trans ((le_abs_self _).trans (hGb _ (gaussOrbit_mem_Icc _ hx)))
    have hLint : Integrable
        (fun x => |blockProduct (p :: rest) x - blockProduct (mapObs F (p :: rest)) x|)
        gaussMeasure := by
      refine integrable_of_unit_bound (C := A ^ n * (2 * A) + A * (2 * A ^ n)) hLm ?_
      intro x hx
      rw [abs_abs]
      exact hLb x hx
    have hGcompInt : Integrable (fun x => G (gaussOrbit p.1 x)) gaussMeasure :=
      integrable_of_unit_bound (hGm.comp (measurable_gaussOrbit p.1))
        (fun x hx => hGb _ (gaussOrbit_mem_Icc _ hx))
    have hstep1 : (∫ x, |blockProduct (p :: rest) x
          - blockProduct (mapObs F (p :: rest)) x| ∂gaussMeasure)
        ≤ ∫ x, G (gaussOrbit p.1 x) ∂gaussMeasure := by
      refine integral_mono_ae hLint hGcompInt ?_
      filter_upwards [gaussMeasure_unit_ae] with x hx
      exact hpt x ⟨hx.1.le, hx.2⟩
    have hstep2 : (∫ x, G (gaussOrbit p.1 x) ∂gaussMeasure) = ∫ y, G y ∂gaussMeasure :=
      integral_comp_gaussOrbit G hGm p.1
    have hdiffInt : Integrable (fun y => |p.2 y - F p.2 y|) gaussMeasure := by
      refine integrable_of_unit_bound (C := 2 * A)
        (((hm p (by simp)).sub (hFm p (by simp))).abs) ?_
      intro y hy
      have e1 : |p.2 y| ≤ A := by rw [abs_of_nonneg (h0 p (by simp) hy)]; exact hub p (by simp) hy
      have e2 : |F p.2 y| ≤ A := by
        rw [abs_of_nonneg (hF0 p (by simp) hy)]; exact hFub p (by simp) hy
      rw [abs_abs]
      calc |p.2 y - F p.2 y| ≤ |p.2 y| + |F p.2 y| := by
            have := abs_add_le (p.2 y) (-(F p.2 y))
            simpa [sub_eq_add_neg] using this
        _ ≤ A + A := add_le_add e1 e2
        _ ≤ 2 * A := by linarith
    have hbpInt : Integrable
        (fun y => |blockProduct rest y - blockProduct (mapObs F rest) y|) gaussMeasure := by
      refine integrable_of_unit_bound (C := 2 * A ^ n)
        (((measurable_blockProduct rest hrm).sub
          (measurable_blockProduct (mapObs F rest) hmapm)).abs) ?_
      intro y hy
      have e1 : |blockProduct rest y| ≤ A ^ n := by
        rw [abs_of_nonneg (blockProduct_nonneg rest hr0 hy)]
        exact blockProduct_le rest hr0 hrub hy
      have e2 : |blockProduct (mapObs F rest) y| ≤ A ^ n := by
        rw [abs_of_nonneg (blockProduct_nonneg _ hmap0 hy)]
        have := blockProduct_le (mapObs F rest) hmap0 hmapub hy
        rwa [mapObs_length] at this
      rw [abs_abs]
      calc |blockProduct rest y - blockProduct (mapObs F rest) y|
          ≤ |blockProduct rest y| + |blockProduct (mapObs F rest) y| := by
            have := abs_add_le (blockProduct rest y) (-(blockProduct (mapObs F rest) y))
            simpa [sub_eq_add_neg] using this
        _ ≤ A ^ n + A ^ n := add_le_add e1 e2
        _ ≤ 2 * A ^ n := by linarith
    have hstep3 : (∫ y, G y ∂gaussMeasure)
        = A ^ n * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure)
          + A * ∫ y, |blockProduct rest y - blockProduct (mapObs F rest) y| ∂gaussMeasure := by
      rw [hGdef, integral_add (hdiffInt.const_mul _) (hbpInt.const_mul _),
        integral_const_mul, integral_const_mul]
    have hd0 : 0 ≤ ∫ y, |p.2 y - F p.2 y| ∂gaussMeasure :=
      integral_nonneg (fun _ => abs_nonneg _)
    have hAn : (0 : ℝ) ≤ A ^ n := pow_nonneg hA0 n
    have hl1 : l1Sum F (p :: rest) = (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) + l1Sum F rest := by
      simp [l1Sum]
    have hlen : (p :: rest).length = n + 1 := rfl
    rw [hlen, hl1, pow_succ]
    have hmono : A ^ n ≤ A ^ n * A := by nlinarith
    calc (∫ x, |blockProduct (p :: rest) x
            - blockProduct (mapObs F (p :: rest)) x| ∂gaussMeasure)
        ≤ ∫ x, G (gaussOrbit p.1 x) ∂gaussMeasure := hstep1
      _ = ∫ y, G y ∂gaussMeasure := hstep2
      _ = A ^ n * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure)
            + A * ∫ y, |blockProduct rest y
              - blockProduct (mapObs F rest) y| ∂gaussMeasure := hstep3
      _ ≤ A ^ n * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) + A * (A ^ n * l1Sum F rest) := by
          have := mul_le_mul_of_nonneg_left hIH hA0
          linarith
      _ ≤ A ^ n * A * ((∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) + l1Sum F rest) := by
          have e1 : A ^ n * A * ((∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) + l1Sum F rest)
              = A ^ n * A * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure)
                + A * (A ^ n * l1Sum F rest) := by ring
          have e2 : A ^ n * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure)
              ≤ A ^ n * A * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) := by
            have hprod : 0 ≤ (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) * A ^ n * (A - 1) :=
              mul_nonneg (mul_nonneg hd0 hAn) (by linarith)
            nlinarith [hprod]
          rw [e1]; linarith

theorem abs_blockMean_sub_le (F : (ℝ → ℝ) → ℝ → ℝ) {A : ℝ} (hA : 1 ≤ A) :
    ∀ bs : List (ℕ × (ℝ → ℝ)),
      (∀ p ∈ bs, Measurable p.2) → (∀ p ∈ bs, Measurable (F p.2)) →
      (∀ p ∈ bs, GaussUnitNonnegative p.2) → (∀ p ∈ bs, GaussUnitUpperBound A p.2) →
      (∀ p ∈ bs, GaussUnitNonnegative (F p.2)) → (∀ p ∈ bs, GaussUnitUpperBound A (F p.2)) →
      |blockMean bs - blockMean (mapObs F bs)| ≤ A ^ bs.length * l1Sum F bs := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  intro bs
  induction bs with
  | nil => intro _ _ _ _ _ _; simp [mapObs, l1Sum]
  | cons p rest ih =>
    intro hm hFm h0 hub hF0 hFub
    have hrm : ∀ q ∈ rest, Measurable q.2 := fun q hq => hm q (by simp [hq])
    have hrFm : ∀ q ∈ rest, Measurable (F q.2) := fun q hq => hFm q (by simp [hq])
    have hr0 : ∀ q ∈ rest, GaussUnitNonnegative q.2 := fun q hq => h0 q (by simp [hq])
    have hrub : ∀ q ∈ rest, GaussUnitUpperBound A q.2 := fun q hq => hub q (by simp [hq])
    have hrF0 : ∀ q ∈ rest, GaussUnitNonnegative (F q.2) := fun q hq => hF0 q (by simp [hq])
    have hrFub : ∀ q ∈ rest, GaussUnitUpperBound A (F q.2) := fun q hq => hFub q (by simp [hq])
    have hIH := ih hrm hrFm hr0 hrub hrF0 hrFub
    have hmap0 : ∀ q ∈ mapObs F rest, GaussUnitNonnegative q.2 := by
      intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hrF0 u hu
    have hmapub : ∀ q ∈ mapObs F rest, GaussUnitUpperBound A q.2 := by
      intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hrFub u hu
    have hmapm : ∀ q ∈ mapObs F rest, Measurable q.2 := by
      intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hrFm u hu
    set n := rest.length with hn
    obtain ⟨hB0, hBA⟩ := blockMean_bounds (A := A) rest hrm hr0 hrub
    obtain ⟨hB0', hBA'⟩ := blockMean_bounds (A := A) (mapObs F rest) hmapm hmap0 hmapub
    rw [mapObs_length] at hBA'
    obtain ⟨ha0, haA⟩ := integral_unit_bounds (hm p (by simp)) (h0 p (by simp)) (hub p (by simp))
    obtain ⟨ha0', haA'⟩ :=
      integral_unit_bounds (hFm p (by simp)) (hF0 p (by simp)) (hFub p (by simp))
    have hpint : Integrable p.2 gaussMeasure :=
      integrable_of_unit_bound (hm p (by simp))
        (fun x hx => by rw [abs_of_nonneg (h0 p (by simp) hx)]; exact hub p (by simp) hx)
    have hFpint : Integrable (F p.2) gaussMeasure :=
      integrable_of_unit_bound (hFm p (by simp))
        (fun x hx => by rw [abs_of_nonneg (hF0 p (by simp) hx)]; exact hFub p (by simp) hx)
    have hda : |(∫ y, p.2 y ∂gaussMeasure) - ∫ y, F p.2 y ∂gaussMeasure|
        ≤ ∫ y, |p.2 y - F p.2 y| ∂gaussMeasure := by
      rw [← integral_sub hpint hFpint]
      exact abs_integral_le_integral_abs
    have hd0 : 0 ≤ ∫ y, |p.2 y - F p.2 y| ∂gaussMeasure :=
      integral_nonneg (fun _ => abs_nonneg _)
    have hAn : (0 : ℝ) ≤ A ^ n := pow_nonneg hA0 n
    have hkey : |blockMean (p :: rest) - blockMean (mapObs F (p :: rest))|
        ≤ (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) * A ^ n + A * (A ^ n * l1Sum F rest) := by
      have hmapcons : blockMean (mapObs F (p :: rest))
          = (∫ y, F p.2 y ∂gaussMeasure) * blockMean (mapObs F rest) := rfl
      rw [blockMean_cons, hmapcons]
      have hsplit : (∫ y, p.2 y ∂gaussMeasure) * blockMean rest
            - (∫ y, F p.2 y ∂gaussMeasure) * blockMean (mapObs F rest)
          = ((∫ y, p.2 y ∂gaussMeasure) - ∫ y, F p.2 y ∂gaussMeasure) * blockMean rest
            + (∫ y, F p.2 y ∂gaussMeasure) * (blockMean rest - blockMean (mapObs F rest)) := by
        ring
      rw [hsplit]
      calc |((∫ y, p.2 y ∂gaussMeasure) - ∫ y, F p.2 y ∂gaussMeasure) * blockMean rest
              + (∫ y, F p.2 y ∂gaussMeasure) * (blockMean rest - blockMean (mapObs F rest))|
          ≤ |((∫ y, p.2 y ∂gaussMeasure) - ∫ y, F p.2 y ∂gaussMeasure) * blockMean rest|
              + |(∫ y, F p.2 y ∂gaussMeasure)
                * (blockMean rest - blockMean (mapObs F rest))| := abs_add_le _ _
        _ = |(∫ y, p.2 y ∂gaussMeasure) - ∫ y, F p.2 y ∂gaussMeasure| * blockMean rest
              + (∫ y, F p.2 y ∂gaussMeasure)
                * |blockMean rest - blockMean (mapObs F rest)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg ha0']
        _ ≤ (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) * A ^ n + A * (A ^ n * l1Sum F rest) := by
            have h1 : |(∫ y, p.2 y ∂gaussMeasure) - ∫ y, F p.2 y ∂gaussMeasure| * blockMean rest
                ≤ (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) * A ^ n :=
              mul_le_mul hda hBA hB0 hd0
            have h2 : (∫ y, F p.2 y ∂gaussMeasure) * |blockMean rest - blockMean (mapObs F rest)|
                ≤ A * (A ^ n * l1Sum F rest) :=
              mul_le_mul haA' hIH (abs_nonneg _) hA0
            linarith
    have hl1 : l1Sum F (p :: rest) = (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) + l1Sum F rest := by
      simp [l1Sum]
    have hlen : (p :: rest).length = n + 1 := rfl
    rw [hlen, hl1, pow_succ]
    refine hkey.trans ?_
    have e1 : A ^ n * A * ((∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) + l1Sum F rest)
        = A ^ n * A * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure)
          + A * (A ^ n * l1Sum F rest) := by ring
    have e2 : (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) * A ^ n
        ≤ A ^ n * A * (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) := by
      have hprod : 0 ≤ (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) * A ^ n * (A - 1) :=
        mul_nonneg (mul_nonneg hd0 hAn) (by linarith)
      nlinarith [hprod]
    rw [e1]; linarith

/-! ## 4. The BV multi-block mixing estimate

This is `TransferIdentity.lemma_3_2'` with the Lipschitz hypothesis on the
observables replaced by Kwon's `BV(0,1)`, at the cost of replacing the rate
`527/540` by its square root.  No statement is weakened anywhere: the
Lipschitz estimate is used as a black box, and everything added is an
inequality in the same direction. -/

set_option maxHeartbeats 1600000 in
theorem lemma_3_2_BV (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal)
    (K : ℝ) (hK : 1 ≤ K) (M : ℕ)
    (bs : List (ℕ × (ℝ → ℝ)))
    (hme : ∀ p ∈ bs, Measurable p.2)
    (h0 : ∀ p ∈ bs, GaussUnitNonnegative p.2)
    (hub : ∀ p ∈ bs, GaussUnitUpperBound K p.2)
    (hvar : ∀ p ∈ bs, eVariationOn p.2 (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K)
    (hgap : ∀ p ∈ bs, M ≤ p.1) :
    |condMean (gaussHalfOpenPrefixCylinder w)
        (fun α => blockProduct bs (gaussOrbit w.length α)) - blockMean bs|
      ≤ 478 * ((bs.length : ℝ) + 1) * (8 * K) ^ bs.length * K
          * Real.sqrt (527 / 540) ^ M := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt (527 / 540) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.2 (by norm_num)
  have hr1 : r < 1 := by
    have h : Real.sqrt (527 / 540) < Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_one] at h
    rw [hrdef]; exact h
  have hrsq : r ^ 2 = 527 / 540 := by rw [hrdef]; exact Real.sq_sqrt (by norm_num)
  have hX0 : (0 : ℝ) < r ^ M := pow_pos hr0 M
  have hX1 : r ^ M ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hXne : (r : ℝ) ^ M ≠ 0 := ne_of_gt hX0
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 8 * K := ⟨_, rfl⟩
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  rw [← hrdef, ← hAdef]
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = r ^ M / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 24 + 2 * K / δ := ⟨_, rfl⟩
  have hL24 : (24 : ℝ) ≤ L := by
    rw [hLdef]
    have h : (0 : ℝ) ≤ 2 * K / δ := div_nonneg (by linarith) hδ.le
    linarith
  obtain ⟨F, hFdef⟩ : ∃ F : (ℝ → ℝ) → ℝ → ℝ, F = bvApprox δ := ⟨_, rfl⟩
  set s := bs.length with hs
  set bs' := mapObs F bs with hbs'
  -- properties of the observables and of their Lipschitz approximants
  have hsupIoo : ∀ p ∈ bs, ∀ y ∈ Ioo (0 : ℝ) 1, |p.2 y| ≤ K := by
    intro p hp y hy
    have hy' : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
    rw [abs_of_nonneg (h0 p hp hy')]
    exact hub p hp hy'
  have hFm : ∀ p ∈ bs, Measurable (F p.2) := by
    intro p hp
    rw [hFdef]
    exact bvApprox_measurable hδ hδ2 (hvar p hp) (hsupIoo p hp)
  have hF0 : ∀ p ∈ bs, GaussUnitNonnegative (F p.2) := by
    intro p _ x _
    rw [hFdef]
    exact bvApprox_nonneg _ _ _
  have hFK : ∀ p ∈ bs, GaussUnitUpperBound K (F p.2) := by
    intro p hp x _
    rw [hFdef]
    exact bvApprox_le hδ hδ2 hK0 (hvar p hp) (hsupIoo p hp) x
  have hFA : ∀ p ∈ bs, GaussUnitUpperBound A (F p.2) := fun p hp x hx =>
    (hFK p hp hx).trans (by rw [hAdef]; linarith)
  have hubA : ∀ p ∈ bs, GaussUnitUpperBound A p.2 := fun p hp x hx =>
    (hub p hp hx).trans (by rw [hAdef]; linarith)
  have hFlip : ∀ p ∈ bs, GaussUnitLipschitzBound L (F p.2) := by
    intro p hp x _ y _
    rw [hFdef]
    have h := bvApprox_lipschitz hδ hδ2 (hvar p hp) (hsupIoo p hp) x y
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    rw [hLdef]
    linarith
  have hFL1 : ∀ p ∈ bs, (∫ y, |p.2 y - F p.2 y| ∂gaussMeasure) ≤ 100 * K * δ := by
    intro p hp
    rw [hFdef]
    exact bvApprox_L1 hδ hδ2 hK (hme p hp) (h0 p hp) (hub p hp) (hvar p hp)
  have hΛ : l1Sum F bs ≤ (s : ℝ) * (100 * K * δ) := by
    have hcard := List.sum_le_card_nsmul (bs.map (fun p => ∫ y, |p.2 y - F p.2 y| ∂gaussMeasure))
      (100 * K * δ) (by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
        exact hFL1 p hp)
    simpa [l1Sum, hs, nsmul_eq_mul] using hcard
  have hΛ0 : 0 ≤ l1Sum F bs := l1Sum_nonneg F bs
  -- (a) the conditional-density representation
  obtain ⟨a, b, ha, hb, hrep⟩ := Kwon1002.TransferIdentity.exists_cylinder_condDensity' w hw hpos
  set φ : ℝ → ℝ := kwonDensity a b with hφ
  have hbsm : Measurable (blockProduct bs) := measurable_blockProduct bs hme
  have hbs'mem : ∀ q ∈ bs', Measurable q.2 := by
    intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hFm u hu
  have hbs'0 : ∀ q ∈ bs', GaussUnitNonnegative q.2 := by
    intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hF0 u hu
  have hbs'A : ∀ q ∈ bs', GaussUnitUpperBound A q.2 := by
    intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hFA u hu
  have hbs'lip : ∀ q ∈ bs', GaussUnitLipschitzBound L q.2 := by
    intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hFlip u hu
  have hbs'gap : ∀ q ∈ bs', M ≤ q.1 := by
    intro q hq; obtain ⟨u, hu, rfl⟩ := mem_mapObs hq; exact hgap u hu
  have hbs'm : Measurable (blockProduct bs') := measurable_blockProduct bs' hbs'mem
  -- E1: the replacement error, seen through the conditional density
  have hφ0 : GaussUnitNonnegative φ := kwonDensity_nonneg ha hb
  have hφ8 : GaussUnitUpperBound 8 φ := kwonDensity_le ha hb
  have hφm : Measurable φ := measurable_kwonDensity a b
  have hprodInt : ∀ (u : List (ℕ × (ℝ → ℝ))), (∀ q ∈ u, Measurable q.2) →
      (∀ q ∈ u, GaussUnitNonnegative q.2) → (∀ q ∈ u, GaussUnitUpperBound A q.2) →
      Integrable (fun y => φ y * blockProduct u y) gaussMeasure := by
    intro u hum hu0 huA
    refine integrable_of_unit_bound (C := 8 * A ^ u.length)
      (hφm.mul (measurable_blockProduct u hum)) ?_
    intro y hy
    rw [abs_mul, abs_of_nonneg (hφ0 hy), abs_of_nonneg (blockProduct_nonneg u hu0 hy)]
    exact mul_le_mul (hφ8 hy) (blockProduct_le u hu0 huA hy)
      (blockProduct_nonneg u hu0 hy) (by norm_num)
  have hE1 : |condMean (gaussHalfOpenPrefixCylinder w)
        (fun α => blockProduct bs (gaussOrbit w.length α))
      - condMean (gaussHalfOpenPrefixCylinder w)
        (fun α => blockProduct bs' (gaussOrbit w.length α))|
      ≤ 8 * (A ^ s * l1Sum F bs) := by
    rw [hrep (blockProduct bs) hbsm, hrep (blockProduct bs') hbs'm,
      ← integral_sub (hprodInt bs hme h0 hubA) (hprodInt bs' hbs'mem hbs'0 hbs'A)]
    have hbound : ∀ y ∈ Icc (0 : ℝ) 1,
        |φ y * blockProduct bs y - φ y * blockProduct bs' y|
          ≤ 8 * |blockProduct bs y - blockProduct bs' y| := by
      intro y hy
      rw [← mul_sub, abs_mul, abs_of_nonneg (hφ0 hy)]
      exact mul_le_mul_of_nonneg_right (hφ8 hy) (abs_nonneg _)
    have habs : |∫ y, (φ y * blockProduct bs y - φ y * blockProduct bs' y) ∂gaussMeasure|
        ≤ ∫ y, |φ y * blockProduct bs y - φ y * blockProduct bs' y| ∂gaussMeasure :=
      abs_integral_le_integral_abs
    refine habs.trans ?_
    have hint1 : Integrable
        (fun y => |φ y * blockProduct bs y - φ y * blockProduct bs' y|) gaussMeasure :=
      ((hprodInt bs hme h0 hubA).sub (hprodInt bs' hbs'mem hbs'0 hbs'A)).abs
    have hdiffm : Measurable (fun y => |blockProduct bs y - blockProduct bs' y|) :=
      (hbsm.sub hbs'm).abs
    have hint2 : Integrable
        (fun y => 8 * |blockProduct bs y - blockProduct bs' y|) gaussMeasure := by
      refine (integrable_of_unit_bound (C := 2 * A ^ s) hdiffm ?_).const_mul 8
      intro y hy
      rw [abs_abs]
      have e1 : |blockProduct bs y| ≤ A ^ s := by
        rw [abs_of_nonneg (blockProduct_nonneg bs h0 hy)]
        exact blockProduct_le bs h0 hubA hy
      have e2 : |blockProduct bs' y| ≤ A ^ s := by
        rw [abs_of_nonneg (blockProduct_nonneg bs' hbs'0 hy)]
        have h := blockProduct_le bs' hbs'0 hbs'A hy
        rwa [hbs', mapObs_length, ← hs] at h
      calc |blockProduct bs y - blockProduct bs' y|
          ≤ |blockProduct bs y| + |blockProduct bs' y| := by
            have := abs_add_le (blockProduct bs y) (-(blockProduct bs' y))
            simpa [sub_eq_add_neg] using this
        _ ≤ A ^ s + A ^ s := add_le_add e1 e2
        _ ≤ 2 * A ^ s := by linarith
    have hmono : (∫ y, |φ y * blockProduct bs y - φ y * blockProduct bs' y| ∂gaussMeasure)
        ≤ ∫ y, 8 * |blockProduct bs y - blockProduct bs' y| ∂gaussMeasure := by
      refine integral_mono_ae hint1 hint2 ?_
      filter_upwards [gaussMeasure_unit_ae] with y hy
      exact hbound y ⟨hy.1.le, hy.2⟩
    refine hmono.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact integral_abs_blockProduct_sub_le F hA1 bs hme hFm h0 hubA hF0 hFA
  -- (b) the Lipschitz mixing estimate on the approximants
  have hLip := Kwon1002.TransferIdentity.lemma_3_2' w hw hpos A L
    (by rw [hAdef]; linarith) hL24 M bs'
    hbs'mem hbs'0 hbs'A hbs'lip hbs'gap
  rw [hbs', mapObs_length, ← hs] at hLip
  -- (c) the mean replacement error
  have hE2 : |blockMean bs - blockMean bs'| ≤ A ^ s * l1Sum F bs :=
    abs_blockMean_sub_le F hA1 bs hme hFm h0 hubA hF0 hFA
  -- assemble
  have htri : |condMean (gaussHalfOpenPrefixCylinder w)
        (fun α => blockProduct bs (gaussOrbit w.length α)) - blockMean bs|
      ≤ 8 * (A ^ s * l1Sum F bs)
        + (s : ℝ) * ((527 / 540 : ℝ) ^ M * L * A ^ s)
        + A ^ s * l1Sum F bs := by
    have h1 : |condMean (gaussHalfOpenPrefixCylinder w)
          (fun α => blockProduct bs (gaussOrbit w.length α)) - blockMean bs|
        ≤ |condMean (gaussHalfOpenPrefixCylinder w)
            (fun α => blockProduct bs (gaussOrbit w.length α))
          - condMean (gaussHalfOpenPrefixCylinder w)
            (fun α => blockProduct bs' (gaussOrbit w.length α))|
          + |condMean (gaussHalfOpenPrefixCylinder w)
            (fun α => blockProduct bs' (gaussOrbit w.length α)) - blockMean bs'|
          + |blockMean bs' - blockMean bs| := by
      have := abs_sub_le (condMean (gaussHalfOpenPrefixCylinder w)
          (fun α => blockProduct bs (gaussOrbit w.length α)))
        (condMean (gaussHalfOpenPrefixCylinder w)
          (fun α => blockProduct bs' (gaussOrbit w.length α))) (blockMean bs)
      have h2 := abs_sub_le (condMean (gaussHalfOpenPrefixCylinder w)
          (fun α => blockProduct bs' (gaussOrbit w.length α))) (blockMean bs') (blockMean bs)
      linarith
    have h3 : |blockMean bs' - blockMean bs| = |blockMean bs - blockMean bs'| := abs_sub_comm _ _
    rw [h3] at h1
    linarith [hE1, hLip, hE2]
  refine htri.trans ?_
  -- the arithmetic: `δ = ρ^{M/2}/2` balances `ρ^M/δ` against `δ`
  have hPX : (527 / 540 : ℝ) ^ M = (r ^ M) ^ 2 := by
    rw [← hrsq, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hPL : (527 / 540 : ℝ) ^ M * L = 24 * (r ^ M) ^ 2 + 4 * K * r ^ M := by
    rw [hPX, hLdef, hδdef]
    field_simp
    ring
  have hXsq : (r ^ M) ^ 2 ≤ r ^ M := by nlinarith
  have hAs : (0 : ℝ) ≤ A ^ s := pow_nonneg hA0 s
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hb1 : 8 * (A ^ s * l1Sum F bs) + A ^ s * l1Sum F bs
      ≤ 450 * (s : ℝ) * K * r ^ M * A ^ s := by
    have h1 : l1Sum F bs ≤ (s : ℝ) * (100 * K * δ) := hΛ
    have h2 : (s : ℝ) * (100 * K * δ) = 50 * (s : ℝ) * K * r ^ M := by
      rw [hδdef]; ring
    rw [h2] at h1
    nlinarith [hAs, hΛ0]
  have hb2 : (s : ℝ) * ((527 / 540 : ℝ) ^ M * L * A ^ s)
      ≤ 28 * (s : ℝ) * K * r ^ M * A ^ s := by
    have h1 : (527 / 540 : ℝ) ^ M * L ≤ 28 * K * r ^ M := by
      rw [hPL]
      nlinarith [hXsq, hX0, hK]
    nlinarith [hAs, hs0, mul_nonneg hs0 hAs]
  have hfinal : 478 * (s : ℝ) * K * r ^ M * A ^ s
      ≤ 478 * ((s : ℝ) + 1) * A ^ s * K * r ^ M := by
    have hnn : (0 : ℝ) ≤ A ^ s * K * r ^ M :=
      mul_nonneg (mul_nonneg hAs hK0) hX0.le
    nlinarith [hnn]
  calc 8 * (A ^ s * l1Sum F bs) + (s : ℝ) * ((527 / 540 : ℝ) ^ M * L * A ^ s)
        + A ^ s * l1Sum F bs
      ≤ 450 * (s : ℝ) * K * r ^ M * A ^ s + 28 * (s : ℝ) * K * r ^ M * A ^ s := by linarith
    _ = 478 * (s : ℝ) * K * r ^ M * A ^ s := by ring
    _ ≤ 478 * ((s : ℝ) + 1) * A ^ s * K * r ^ M := hfinal

/-! ## 5. Kwon's (17) shape, and the endpoint reconciliation

`lemma_3_2_BV` is Lemma 3.2 of the manuscript for **nonnegative** `BV(0,1)`
observables, the class §4 actually feeds in (digit indicators, manuscript
lines ≈ 334 and 369; `TransferIdentity.firstDigitIndicator_bv` and
`TransferIdentity.firstDigitIndicator_not_lipschitz` show that class is BV
and is *not* Lipschitz, i.e. it is outside what `lemma_3_2'` accepts).

The rate degrades from `527/540` to `√(527/540)`.  That is harmless for §4:
`Prop41.deltaScaleR_le_rpow_neg` and `Prop41.eventually_rpow_mul_deltaScale_le`
are quantified over *every* `ρ ∈ (0,1)`, so any spectral gap serves. -/

/-- Reconciling the two sup-norm conventions.  `Prop41.BVBoundedBy` bounds
`|g|` on the **open** interval; the substrate's `GaussUnitUpperBound` bounds
`g` on the **closed** one.  For a nonnegative observable the two differ only
at `0` and `1`. -/
theorem gaussUnitUpperBound_of_BVBoundedBy {K : ℝ} {g : ℝ → ℝ}
    (hbv : BVBoundedBy K g) (he0 : g 0 ≤ K) (he1 : g 1 ≤ K) :
    GaussUnitUpperBound K g := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; exact he0
  · rcases eq_or_lt_of_le hx.2 with h' | h'
    · rw [h']; exact he1
    · exact le_trans (le_abs_self _) (hbv.1 x ⟨h, h'⟩)

/-- **Lemma 3.2 for `BV(0,1)` observables, in Kwon's (17) shape.**

`|E(∏ᵢ gᵢ(T^{tᵢ}α) | I_w) - ∏ᵢ ∫ gᵢ dν| ≤ C_s ρ^M ∏ᵢ ‖gᵢ‖_BV`, with
`C_s` and `ρ ∈ (0,1)` uniform in the cylinder `I_w`, in the gaps, and in the
observables.  Here `ρ = √(527/540)` and `C_s = 478 (s+1) 8^s`. -/
theorem lemma_3_2_BV_kwon_shape (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (w : List ℕ), (∀ q ∈ w, 0 < q) →
        0 < (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal →
        ∀ (K : ℝ), 1 ≤ K → ∀ (M : ℕ) (bs : List (ℕ × (ℝ → ℝ))), bs.length = s →
          (∀ p ∈ bs, Measurable p.2) →
          (∀ p ∈ bs, GaussUnitNonnegative p.2) →
          (∀ p ∈ bs, GaussUnitUpperBound K p.2) →
          (∀ p ∈ bs, eVariationOn p.2 (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K) →
          (∀ p ∈ bs, M ≤ p.1) →
          |condMean (gaussHalfOpenPrefixCylinder w)
              (fun α => blockProduct bs (gaussOrbit w.length α)) - blockMean bs|
            ≤ C * ρ ^ M * K ^ (s + 1) := by
  refine ⟨478 * ((s : ℝ) + 1) * 8 ^ s, Real.sqrt (527 / 540), by positivity,
    Real.sqrt_pos.2 (by norm_num), ?_, ?_⟩
  · have h : Real.sqrt (527 / 540) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at h
  · intro w hw hpos K hK M bs hlen hme h0 hub hvar hgap
    have h := lemma_3_2_BV w hw hpos K hK M bs hme h0 hub hvar hgap
    rw [hlen] at h
    refine h.trans (le_of_eq ?_)
    rw [mul_pow]
    ring

/-! ## 6. What is still between this and `Prop41.lem_3_2_conditional_multiblock_mixing`

`lemma_3_2_BV_kwon_shape` is Kwon's (17) for the class §4 uses, with the
constants uniform in the cylinder.  Three gaps remain to the *literal*
statement of `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing`, and
none of them is an analytic gap:

1. **Sign.**  `Prop41.BVBoundedBy K g` asks only `|g| ≤ K`; the estimate
   above is for `0 ≤ g ≤ K`.  Wang's contraction is applied through
   `Erdos1002.integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate`, whose
   hypotheses are `GaussUnitNonnegative` + `GaussUnitUpperBound`, and the
   induction of `Transfer.multiblock_mixing` promotes each observable to the
   density of the next stage, so nonnegativity is used, not decorative.
   The standard fix is the multilinear expansion of `∏ (gᵢ + K) `over
   sublists (`2^s` terms, each a sub-product mixing error with the gaps
   merged, which only makes them larger); this changes `C_s` by `2^s` and
   nothing else.  It is list bookkeeping, not analysis.

2. **Indexing.**  `Prop41` writes the conditioning event as
   `Prop41.cylinder d w = {α ∈ Ioo 0 1 | ∀ i < d, digit α i = w i}` and the
   product as `∏ i ∈ Finset.range s, g i (gaussIter α (t i))`, whereas the
   substrate (and hence `lemma_3_2'` and everything above) uses
   `Erdos1002.gaussHalfOpenPrefixCylinder`, `Erdos1002.gaussOrbit`, and the
   gap-list form `blockProduct`.  Translating needs a dictionary
   `digit ↔ gaussFirstDigit`, `gaussIter = gaussOrbit`, and
   `tᵢ = m₁ + ⋯ + mᵢ`; again bookkeeping.

3. **The exponent `K ^ s` rather than `K ^ (s+1)`.**  The interpolation
   costs one extra factor of the BV norm (it enters through the Lipschitz
   constant `2K/δ` of the approximant).  Kwon's `K ^ s` follows by
   homogeneity: both sides of (17) are homogeneous of degree `s` in the
   `gᵢ`, so applying the `K = 1` case to `gᵢ / K` and multiplying by `K ^ s`
   restores the exact exponent.  In the list formalism this is the pair of
   one-line inductions
   `blockProduct (mapObs (· / K) bs) = blockProduct bs / K ^ s` and the same
   for `blockMean`.

Nothing above is weakened relative to Kwon: the hypotheses used are
*stronger* than his (nonnegativity, measurability) and the conclusion is
his, with `ρ = √(527/540)` in place of an unspecified `ρ < 1`. -/

/-! ## 7. The gap is closed on §4's actual observable

`TransferIdentity` §13 pins the gap down on a concrete function: the
first-digit indicator is `BV(0,1)` (`firstDigitIndicator_bv`) and is *not*
Lipschitz for any constant (`firstDigitIndicator_not_lipschitz`), so
`lemma_3_2'` cannot accept it.  It satisfies every hypothesis of
`lemma_3_2_BV` with `K = 1`. -/

theorem firstDigitIndicator_hyps :
    Measurable ((firstDigitCylinder 1).indicator (fun _ => (1 : ℝ))) ∧
      GaussUnitNonnegative ((firstDigitCylinder 1).indicator (fun _ => (1 : ℝ))) ∧
      GaussUnitUpperBound 1 ((firstDigitCylinder 1).indicator (fun _ => (1 : ℝ))) ∧
      eVariationOn ((firstDigitCylinder 1).indicator (fun _ => (1 : ℝ)))
          (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
  refine ⟨?_, ?_, ?_, (Kwon1002.TransferIdentity.firstDigitIndicator_bv).2⟩
  · rw [Kwon1002.TransferIdentity.firstDigitCylinder_one_eq]
    exact measurable_const.indicator measurableSet_Ioc
  · intro x _
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  · intro x _
    by_cases hx : x ∈ firstDigitCylinder 1
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]

/-- **BV mixing for the digit observable of §4.**  Every block is the
first-digit indicator, the very function `lemma_3_2'` cannot take, and the
conditional multi-block factorization still holds, at rate `√(527/540)`,
uniformly in the conditioning cylinder. -/
theorem lemma_3_2_BV_firstDigit (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal)
    (M : ℕ) (bs : List (ℕ × (ℝ → ℝ)))
    (hall : ∀ p ∈ bs, p.2 = (firstDigitCylinder 1).indicator (fun _ => (1 : ℝ)))
    (hgap : ∀ p ∈ bs, M ≤ p.1) :
    |condMean (gaussHalfOpenPrefixCylinder w)
        (fun α => blockProduct bs (gaussOrbit w.length α)) - blockMean bs|
      ≤ 478 * ((bs.length : ℝ) + 1) * (8 * 1) ^ bs.length * 1
          * Real.sqrt (527 / 540) ^ M := by
  obtain ⟨hm, h0, hub, hvar⟩ := firstDigitIndicator_hyps
  refine lemma_3_2_BV w hw hpos 1 le_rfl M bs ?_ ?_ ?_ ?_ hgap
  · intro p hp; rw [hall p hp]; exact hm
  · intro p hp; rw [hall p hp]; exact h0
  · intro p hp; rw [hall p hp]; exact hub
  · intro p hp; rw [hall p hp]; exact hvar

end

end Kwon1002.BVMixing


