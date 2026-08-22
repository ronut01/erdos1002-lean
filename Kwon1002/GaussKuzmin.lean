import Kwon1002.TupleInputs
import Kwon1002.DigitLocalLaw
import Kwon1002.SmallJumps

/-!
# The Gauss-Kuzmin normalisation of display (35)

This module closes the arithmetic core of display (35): the identification of
the **stationary mean of the mark indicator** with the Lévy intensity `Λ` of
display (37), constant included.

## What is proved

Write `markTailMean M` for the stationary mass of `{(x,θ) : a₁(x)·W(θ) > M}`
under `γ ⊗ Leb` — that is, `Section5Join.stationaryMeanR` of the symbol
`(a,θ) ↦ 1[M < a·W θ]`, definitionally (an `example … := rfl` in
`Kwon1002/Section5Join.lean` witnesses this).  Then:

* `markTailMean_bounds`, **quantitative and two-sided**, for every `M > 0`:

    `(1/12 − 1/(32M))/log 2  ≤  M · markTailMean M  ≤  (1/12)/log 2`;

* `tendsto_markTailMean`: `M · markTailMean M → 1/(12 log 2)`;
* `levyIntensity_Ioi`: `Λ((u,∞)) = 1/(2π²u)`, exactly;
* `two_lyapunov_levy_Ioi`: `2λ·Λ((u,∞)) = 1/(12 u log 2)`;
* `tendsto_scaled_markTailMean`: `L · markTailMean (u·L) → 2λ·Λ((u,∞))`,
  and `tendsto_scaled_markTailMean_nat` along `L = log n`;
* `tendsto_scaled_markBandMean`: the same on a band, `L · (markTailMean (uL) −
  markTailMean (vL)) → 2λ·Λ((u,v])`.

All of these are `#print axioms`-clean (`propext`, `Classical.choice`,
`Quot.sound`).

## The route, and why it is not the one the file's brief suggested

The obvious route computes the `θ`-integral in closed form first —
`IntervalClass.volume_W_gt` gives `vol{θ : W θ > s} = √(1−8s)` exactly — and
then sums `∑_{a > 8M} γ(a₁ = a)·√(1 − 8M/a)` against the exact `a^{-2}` digit
law.  That sum is a Riemann sum for `∫₁^∞ y^{-2}√(1−1/y) dy = 2/3` in the
variable `a/M`, and it does give the right constant; but a Riemann sum for an
improper integral is a substantial formalisation.

**Swapping the two integrals removes the Riemann sum entirely.**  At a fixed
phase `θ` with `w = W θ > 0`, the digits contributing are exactly
`a ≥ ⌊M/w⌋ + 1` (`mark_gt_iff`), so the inner mass is the *exact* Gauss-Kuzmin
tail `γ{a₁ ≥ K} = log(1 + 1/K)/log 2`
(`DigitLocalLaw.gaussMeasure_real_digit_zero_ge`) at `K = ⌊M/w⌋+1`.  Since
`M/w < K ≤ M/w + 1`, the elementary two-sided bound

  `x/(1+x) ≤ log(1+x) ≤ x`

— both halves instances of `Real.log_le_sub_one_of_pos` — pins
`M·log(1+1/K)/log 2` between `(w − 1/(32M))/log 2` and `w/log 2`, *uniformly in
the phase* (`slice_bounds`; `w ≤ 1/8` is what makes the error uniform).
Integrating that over the cell and using `∫₀¹ W = 1/12`
(`TupleInputs.integral_W_unit`) gives `markTailMean_bounds` with no limit
interchange, no dominated convergence and no Riemann sum: the `1/12` enters as
`∫ W` and the `log 2` as the Gauss normalisation, which is exactly the
manuscript's bookkeeping `E[W]/(u log 2)`.

Only `MeasureTheory.integral_integral_swap` is used, on a bounded measurable
integrand over a product of finite measures.  `IntervalClass.volume_W_gt` is
**not** needed on this route.

## The constant, and the record it corrects

`Kwon1002/TupleInputs.lean` records, in the docstring of
`perLevel_constant_check`, that `Λ((u,∞)) = ∫_u^∞ (2π²x²)^{-1} dx = (2π²u)^{-1}`
is "the one arithmetic step **not** machine-checked here ... used only in the
commentary, never in a proof".  `levyIntensity_Ioi` machine-checks it, so that
sentence is now stale; the docstring there has been corrected.

The numbers come out as the manuscript predicts, with nothing left free:

  `M·markTailMean M → 1/(12 log 2)`,  `2λ·Λ((u,∞)) = 1/(12 u log 2)`,

and the two agree after the scaling `M = uL`.  The check was run before the
proof was built and is recorded here because it constrains nothing else: a
different constant on either side would have been a finding about the
manuscript.

## What this does *not* close

`TupleInputs.oneLevel_gaussKuzmin_intensity` is stated for an **arbitrary
measurable** `B` bounded away from `0` and bounded, and against the level-`j`
law under **Lebesgue in `α`**, not the stationary law.  This module supplies
the stationary side at half-lines and at bands, i.e. on the interval class —
which is exactly the class `Section5Join.stationaryMeanR_gap_le` and the
Selberg bracket can reach.  Two things stood between that and the
residual as stated when this module was written.  **Both records are now
stale, and both are corrected here.**

1. The passage from the stationary mean to the level-`j` Lebesgue average,
   i.e. `Section5Join.oneLevel_indicator_sandwich` plus a choice of the bracket
   parameters `(Acut, N, δ)` against `L` together with the digit-cut tails.
   **Closed**: `Section5Join.sched_admissible` and
   `Section5Join.oneLevel_transfer` make the choice explicit
   (`δ = L^{-2}`, `N = ⌈L^6⌉`, `Acut = ⌈L^2⌉`, against `D = 11`, `A = 2`) and
   prove the resulting error is `o(1/L)` uniformly over the bulk.
2. The passage from the interval class to an arbitrary measurable `B`.  This
   half of the record stands, and is now isolated as
   `TupleInputs.oneLevel_gaussKuzmin_intensity_to_measurable`.  The sentence
   "the `θ`-sections `W^{-1}(L·B/a)` are not finite unions of intervals" and the
   need for a uniform-in-`L` density bound `≍ x^{-2}` are both correct and both
   unchanged.

What the old record got wrong is the *scope* of item 2.  It said the interval
class is where the argument stops.  It stops strictly later:
`Section5Join.oneLevel_gaussKuzmin_intensity_truncation` proves the residual's
conclusion **outright**, unconditionally and `#print axioms` clean, at
`B = {x : ε < |x| ∧ |x| ≤ R}` — the truncation window that
`IntervalClass.isUnionOfIntervals_truncation` shows is a union of two intervals
and that the tree records as the only shape `B` ever takes below Proposition
5.1.  What is missing between that window and the general interval class is not
a density bound but a decomposition: an arbitrary `IsUnionOfIntervals` family
must be rewritten as a *disjoint* union of bands with endpoints before
`tendsto_scaled_markBandMean` can be summed over it.

Recorded, not hidden.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace GaussKuzmin

noncomputable section

/-- The smallest digit whose mark at phase level `w` exceeds `M`. -/
def digitCut (M w : ℝ) : ℕ := ⌊M / w⌋₊ + 1

lemma one_le_digitCut (M w : ℝ) : 1 ≤ digitCut M w := Nat.le_add_left 1 _

lemma mark_gt_iff {M w : ℝ} (hM : 0 ≤ M) (hw : 0 < w) (a : ℕ) :
    M < (a : ℝ) * w ↔ digitCut M w ≤ a := by
  rw [digitCut, Nat.add_one_le_iff, Nat.floor_lt (by positivity), div_lt_iff₀ hw]

lemma digitCut_gt (M w : ℝ) : M / w < (digitCut M w : ℝ) := by
  have := Nat.lt_floor_add_one (M / w)
  simpa [digitCut] using this

lemma digitCut_le {M w : ℝ} (hM : 0 ≤ M) (hw : 0 < w) :
    ((digitCut M w : ℕ) : ℝ) ≤ M / w + 1 := by
  have _ := hM
  have _ := hw
  have := Nat.floor_le (show (0:ℝ) ≤ M / w by positivity)
  simp only [digitCut, Nat.cast_add, Nat.cast_one]
  linarith

/-- The `γ`-slice at a fixed phase: the digits that put the mark above `M`. -/
def slice (M θ : ℝ) : Set ℝ := {x : ℝ | M < (digit x 0 : ℝ) * W θ}

lemma slice_eq {M θ : ℝ} (hM : 0 ≤ M) (hw : 0 < W θ) :
    slice M θ = {x : ℝ | digitCut M (W θ) ≤ digit x 0} := by
  ext x
  simp only [slice, Set.mem_setOf_eq]
  exact mark_gt_iff hM hw _

/-- **The exact slice mass.**  At a phase where `W θ > 0`, the Gauss mass of the
digits that put the mark above `M` is the exact Gauss-Kuzmin tail. -/
theorem gauss_slice_real {M θ : ℝ} (hM : 0 ≤ M) (hw : 0 < W θ) :
    (Erdos1002.gaussMeasure (slice M θ)).toReal
      = Real.log (1 + 1 / (digitCut M (W θ) : ℝ)) / Real.log 2 := by
  rw [slice_eq hM hw]
  exact DigitLocalLaw.gaussMeasure_real_digit_zero_ge (one_le_digitCut _ _)

/-! ### The two-sided bound on the slice mass -/

lemma log_one_add_le {x : ℝ} (hx : 0 < x) : Real.log (1 + x) ≤ x := by
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + x by linarith)
  linarith

lemma le_log_one_add {x : ℝ} (hx : 0 < x) : x / (1 + x) ≤ Real.log (1 + x) := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + x)⁻¹ by positivity)
  rw [Real.log_inv] at this
  have h2 : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
  rw [h2] at this
  linarith

/-- **The slice mass, two-sided, with an explicit error.**  For every phase in
the open cell and every threshold `M > 0`,
`(W θ − 1/(32M))/log 2 ≤ M·γ(slice) ≤ W θ/log 2`. -/
theorem slice_bounds {M θ : ℝ} (hM : 0 < M) (hw0 : 0 < W θ) :
    (W θ - 1 / (32 * M)) / Real.log 2
        ≤ M * (Erdos1002.gaussMeasure (slice M θ)).toReal
      ∧ M * (Erdos1002.gaussMeasure (slice M θ)).toReal ≤ W θ / Real.log 2 := by
  have hw8 : W θ ≤ 1 / 8 := W_le_eighth θ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set w : ℝ := W θ with hwdef
  set K : ℝ := ((digitCut M w : ℕ) : ℝ) with hK
  have hKgt : M / w < K := digitCut_gt M w
  have hKle : K ≤ M / w + 1 := digitCut_le hM.le hw0
  have hKpos : 0 < K := lt_of_le_of_lt (by positivity) hKgt
  have hval := gauss_slice_real (M := M) (θ := θ) hM.le hw0
  rw [← hwdef, ← hK] at hval
  rw [hval]
  have hinv : 0 < 1 / K := by positivity
  constructor
  · -- lower bound
    have hlow : (1 / K) / (1 + 1 / K) ≤ Real.log (1 + 1 / K) := le_log_one_add hinv
    have hid : (1 / K) / (1 + 1 / K) = 1 / (K + 1) := by
      field_simp
    rw [hid] at hlow
    have hK1 : K + 1 ≤ M / w + 2 := by linarith
    have hMw : (0:ℝ) < M + 2 * w := by linarith
    have hsplit : M / w + 2 = (M + 2 * w) / w := by field_simp
    rw [hsplit] at hK1
    have hstep : M * w / (M + 2 * w) ≤ M / (K + 1) := by
      have h := div_le_div_of_nonneg_left hM.le (by linarith : (0:ℝ) < K + 1) hK1
      have he : M / ((M + 2 * w) / w) = M * w / (M + 2 * w) := by
        rw [div_div_eq_mul_div]
      rwa [he] at h
    have hkey : w - 1 / (32 * M) ≤ M * w / (M + 2 * w) := by
      rw [le_div_iff₀ hMw]
      have e : (w - 1 / (32 * M)) * (M + 2 * w)
          = w * M + 2 * w ^ 2 - (1 / 32 + w / (16 * M)) := by
        field_simp; ring
      rw [e]
      have h1 : 2 * w ^ 2 ≤ 1 / 32 := by nlinarith
      have h2 : (0:ℝ) ≤ w / (16 * M) := by positivity
      linarith
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hlog]
    calc w - 1 / (32 * M) ≤ M * w / (M + 2 * w) := hkey
      _ ≤ M / (K + 1) := hstep
      _ = M * (1 / (K + 1)) := by ring
      _ ≤ M * Real.log (1 + 1 / K) := mul_le_mul_of_nonneg_left hlow hM.le
  · -- upper bound
    have hup : Real.log (1 + 1 / K) ≤ 1 / K := log_one_add_le hinv
    have hKinv : 1 / K ≤ w / M := by
      rw [div_le_div_iff₀ hKpos hM]
      have := (div_lt_iff₀ hw0).mp hKgt
      linarith
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hlog]
    calc M * Real.log (1 + 1 / K) ≤ M * (1 / K) := mul_le_mul_of_nonneg_left hup hM.le
      _ ≤ M * (w / M) := mul_le_mul_of_nonneg_left hKinv hM.le
      _ = w := by field_simp

/-! ### The stationary mean, and the swap -/

/-- The stationary mean of the mark-tail indicator: the `γ ⊗ Leb` mass of
`{(x, θ) : a₁(x)·W(θ) > M}`.  This is `Section5Join.stationaryMeanR` of the
symbol `(a, θ) ↦ 1[M < a·W θ]`, by definition. -/
def markTailMean (M : ℝ) : ℝ :=
  ∫ x, (∫ θ in Ioo (0:ℝ) 1, (if M < (digit x 0 : ℝ) * W θ then (1:ℝ) else 0))
    ∂Erdos1002.gaussMeasure

lemma measurableSet_slice (M θ : ℝ) : MeasurableSet (slice M θ) := by
  have h : Measurable fun x : ℝ => (digit x 0 : ℝ) * W θ :=
    (measurable_digitCast 0).mul_const _
  exact measurableSet_lt measurable_const h

lemma measurable_pairMark (M : ℝ) :
    Measurable fun p : ℝ × ℝ => (if M < (digit p.1 0 : ℝ) * W p.2 then (1:ℝ) else 0) := by
  have h : Measurable fun p : ℝ × ℝ => (digit p.1 0 : ℝ) * W p.2 :=
    ((measurable_digitCast 0).comp measurable_fst).mul
      (measurable_W.comp measurable_snd)
  exact (measurable_const.ite (measurableSet_lt measurable_const h) measurable_const)

lemma integrable_pairMark (M : ℝ) :
    Integrable (fun p : ℝ × ℝ => (if M < (digit p.1 0 : ℝ) * W p.2 then (1:ℝ) else 0))
      (Erdos1002.gaussMeasure.prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  refine Integrable.mono' (integrable_const (1:ℝ))
    (measurable_pairMark M).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  split_ifs <;> norm_num

lemma indicator_form (M θ : ℝ) :
    (fun x : ℝ => (if M < (digit x 0 : ℝ) * W θ then (1:ℝ) else 0))
      = Set.indicator (slice M θ) (fun _ => (1:ℝ)) := by
  funext x
  by_cases hx : M < (digit x 0 : ℝ) * W θ
  · rw [if_pos hx, Set.indicator_of_mem (show x ∈ slice M θ from hx)]
  · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ slice M θ from hx)]

/-- **The swap.**  The stationary mean of the mark-tail indicator is the phase
average of the exact Gauss-Kuzmin digit tail. -/
theorem markTailMean_eq (M : ℝ) :
    markTailMean M
      = ∫ θ in Ioo (0:ℝ) 1, (Erdos1002.gaussMeasure (slice M θ)).toReal := by
  rw [markTailMean, integral_integral_swap (integrable_pairMark M)]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  rw [indicator_form M θ, integral_indicator_const (1:ℝ) (measurableSet_slice M θ)]
  simp [Measure.real]

lemma integrable_sliceMass (M : ℝ) :
    IntegrableOn (fun θ : ℝ => (Erdos1002.gaussMeasure (slice M θ)).toReal)
      (Ioo (0:ℝ) 1) := by
  have h := (integrable_pairMark M).integral_prod_right
  refine h.congr (Filter.Eventually.of_forall fun θ => ?_)
  show (∫ x, (if M < (digit x 0 : ℝ) * W θ then (1:ℝ) else 0) ∂Erdos1002.gaussMeasure) = _
  rw [indicator_form M θ, integral_indicator_const (1:ℝ) (measurableSet_slice M θ)]
  simp [Measure.real]

/-- `∫_{(0,1)} W = 1/12`, the `Ioo` form of `TupleInputs.integral_W_unit`. -/
theorem integral_W_Ioo : (∫ θ in Ioo (0:ℝ) 1, W θ) = 1 / 12 := by
  have h := TupleInputs.integral_W_unit
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
  rwa [MeasureTheory.integral_Ioc_eq_integral_Ioo] at h

/-! ### The normalisation -/

lemma W_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) 1) : 0 < W θ := by
  rw [IntervalClass.W_eq_of_mem_Ico ⟨hθ.1.le, hθ.2⟩]
  have := hθ.1
  have := hθ.2
  nlinarith

lemma integrableOn_W : IntegrableOn W (Ioo (0:ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := 1/8) (by simp [Real.volume_Ioo])
    measurable_W.aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (W_nonneg θ)]
  exact W_le_eighth θ

/-- **The Gauss-Kuzmin normalisation, quantitative.**  For every threshold
`M > 0` the stationary mark-tail mass satisfies
`(1/12 − 1/(32M))/log 2 ≤ M·markTailMean M ≤ (1/12)/log 2`.

The upper bound is `log(1+x) ≤ x`; the lower bound is `log(1+x) ≥ x/(1+x)`,
both instances of `Real.log_le_sub_one_of_pos`.  The `1/12` is `∫₀¹ W`
(`TupleInputs.integral_W_unit`) and the `log 2` is the exact Gauss-Kuzmin tail
`γ{a₁ ≥ K} = log(1 + 1/K)/log 2`
(`DigitLocalLaw.gaussMeasure_real_digit_zero_ge`). -/
theorem markTailMean_bounds {M : ℝ} (hM : 0 < M) :
    (1 / 12 - 1 / (32 * M)) / Real.log 2 ≤ M * markTailMean M
      ∧ M * markTailMean M ≤ (1 / 12) / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvol : (∫ _θ in Ioo (0:ℝ) 1, (1:ℝ)) = 1 := by
    rw [MeasureTheory.setIntegral_const]
    simp
  have hIc : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Ioo (0:ℝ) 1) := fun c => by
    refine Measure.integrableOn_of_bounded (M := |c|) (by simp [Real.volume_Ioo])
      measurable_const.aestronglyMeasurable (Filter.Eventually.of_forall fun _ => ?_)
    rw [Real.norm_eq_abs]
  have hIs := integrable_sliceMass M
  have hIW := integrableOn_W
  have hIup : IntegrableOn (fun θ : ℝ => W θ / Real.log 2) (Ioo (0:ℝ) 1) :=
    hIW.div_const _
  have hIlow : IntegrableOn (fun θ : ℝ => (W θ - 1 / (32 * M)) / Real.log 2)
      (Ioo (0:ℝ) 1) := (hIW.sub (hIc (1 / (32 * M)))).div_const _
  have hEq : M * markTailMean M
      = ∫ θ in Ioo (0:ℝ) 1, M * (Erdos1002.gaussMeasure (slice M θ)).toReal := by
    rw [markTailMean_eq, MeasureTheory.integral_const_mul]
  have hupval : (∫ θ in Ioo (0:ℝ) 1, W θ / Real.log 2) = (1 / 12) / Real.log 2 := by
    rw [MeasureTheory.integral_div, integral_W_Ioo]
  have hlowval : (∫ θ in Ioo (0:ℝ) 1, (W θ - 1 / (32 * M)) / Real.log 2)
      = (1 / 12 - 1 / (32 * M)) / Real.log 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_sub hIW (hIc (1 / (32 * M))),
      integral_W_Ioo, MeasureTheory.setIntegral_const]
    simp
  constructor
  · rw [hEq, ← hlowval]
    refine setIntegral_mono_on hIlow (hIs.const_mul M) measurableSet_Ioo fun θ hθ => ?_
    exact (slice_bounds hM (W_pos_of_mem_Ioo hθ)).1
  · rw [hEq, ← hupval]
    refine setIntegral_mono_on (hIs.const_mul M) hIup measurableSet_Ioo fun θ hθ => ?_
    exact (slice_bounds hM (W_pos_of_mem_Ioo hθ)).2

/-- **The Gauss-Kuzmin normalisation.**  `M · markTailMean M → 1/(12 log 2)`. -/
theorem tendsto_markTailMean :
    Tendsto (fun M : ℝ => M * markTailMean M) atTop (𝓝 (1 / (12 * Real.log 2))) := by
  have hval : (1 / 12 : ℝ) / Real.log 2 = 1 / (12 * Real.log 2) := by rw [div_div]
  rw [← hval]
  have h1 : Tendsto (fun M : ℝ => (1:ℝ) / (32 * M)) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 32) tendsto_id) 1
  have hlow : Tendsto (fun M : ℝ => (1 / 12 - 1 / (32 * M)) / Real.log 2) atTop
      (𝓝 ((1 / 12 : ℝ) / Real.log 2)) := by
    have h2 := ((tendsto_const_nhds (x := (1 / 12 : ℝ)) (f := atTop (α := ℝ))).sub
      h1).div_const (Real.log 2)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with M hM
    exact (markTailMean_bounds hM).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with M hM
    exact (markTailMean_bounds hM).2

/-! ### The Lévy intensity of a half-line, and the constant

`Kwon1002/TupleInputs.lean` records `Λ((u,∞)) = 1/(2π²u)` as "the one
arithmetic step **not** machine-checked here ... used only in the commentary".
It is machine-checked here, and the record above is corrected. -/

lemma rpow_neg_two {x : ℝ} (hx : 0 < x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]

lemma levyIntensityDensity_eq {x : ℝ} (hx : 0 < x) :
    levyIntensityDensity x = (1 / (2 * Real.pi ^ 2)) * x ^ (-2 : ℝ) := by
  rw [levyIntensityDensity, rpow_neg_two hx]
  field_simp

lemma integrableOn_levyIntensityDensity {u : ℝ} (hu : 0 < u) :
    IntegrableOn levyIntensityDensity (Ioi u) := by
  have h : IntegrableOn (fun x : ℝ => (1 / (2 * Real.pi ^ 2)) * x ^ (-2 : ℝ)) (Ioi u) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hu).const_mul _
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  exact (levyIntensityDensity_eq (lt_trans hu hx)).symm

lemma integral_levyIntensityDensity_Ioi {u : ℝ} (hu : 0 < u) :
    (∫ x in Ioi u, levyIntensityDensity x) = 1 / (2 * Real.pi ^ 2 * u) := by
  have hcongr : (∫ x in Ioi u, levyIntensityDensity x)
      = ∫ x in Ioi u, (1 / (2 * Real.pi ^ 2)) * x ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    exact levyIntensityDensity_eq (lt_trans hu hx)
  rw [hcongr, MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hu]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hu' : u ≠ 0 := ne_of_gt hu
  rw [show (-2 : ℝ) + 1 = -1 by norm_num,
    show u ^ (-1 : ℝ) = u⁻¹ by
      rw [show (-1 : ℝ) = -((1 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu.le, Real.rpow_natCast]
      norm_num]
  field_simp

/-- **`Λ((u,∞)) = 1/(2π²u)`**, machine-checked. -/
theorem levyIntensity_Ioi {u : ℝ} (hu : 0 < u) :
    levyIntensity (Ioi u) = ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * u)) := by
  rw [levyIntensity, withDensity_apply _ measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_levyIntensityDensity hu)
      (Filter.Eventually.of_forall fun x => by
        rw [levyIntensityDensity]; positivity),
    integral_levyIntensityDensity_Ioi hu]

theorem levyIntensity_Ioi_toReal {u : ℝ} (hu : 0 < u) :
    (levyIntensity (Ioi u)).toReal = 1 / (2 * Real.pi ^ 2 * u) := by
  rw [levyIntensity_Ioi hu, ENNReal.toReal_ofReal (by positivity)]

/-- **The constant, closed.**  `2λ·Λ((u,∞)) = 1/(12 u log 2)`: the Gauss-Kuzmin
normalisation of `markTailMean` is exactly the manuscript's `2λ·Λ`. -/
theorem two_lyapunov_levy_Ioi {u : ℝ} (hu : 0 < u) :
    2 * lyapunov * (levyIntensity (Ioi u)).toReal = 1 / (12 * u * Real.log 2) := by
  rw [levyIntensity_Ioi_toReal hu, lyapunov]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hu' : u ≠ 0 := ne_of_gt hu
  field_simp

/-! ### The normalisation, in the form display (35) asks for -/

/-- **The Gauss-Kuzmin normalisation against the Lévy intensity.**  For every
`u > 0`, the scale-`L` stationary mark-tail mass satisfies

  `L · markTailMean (u·L) → 2λ · Λ((u,∞))`

as `L → ∞`.  This is display (35) at a half-line, with the manuscript's own
constant, and with `Λ((u,∞)) = 1/(2π²u)` machine-checked rather than
substituted. -/
theorem tendsto_scaled_markTailMean {u : ℝ} (hu : 0 < u) :
    Tendsto (fun L : ℝ => L * markTailMean (u * L)) atTop
      (𝓝 (2 * lyapunov * (levyIntensity (Ioi u)).toReal)) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hMtop : Tendsto (fun L : ℝ => u * L) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hu tendsto_id
  have h := (tendsto_markTailMean.comp hMtop).div_const u
  have hlim : (1 / (12 * Real.log 2)) / u = 1 / (12 * u * Real.log 2) := by
    rw [div_div]; ring_nf
  rw [two_lyapunov_levy_Ioi hu, ← hlim]
  refine Tendsto.congr (fun L => ?_) h
  simp only [Function.comp_apply]
  field_simp

/-- The same, along the scale `L = log n` of the problem. -/
theorem tendsto_scaled_markTailMean_nat {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => Lnorm n * markTailMean (u * Lnorm n)) atTop
      (𝓝 (2 * lyapunov * (levyIntensity (Ioi u)).toReal)) :=
  (tendsto_scaled_markTailMean hu).comp TupleMeasure.tendsto_Lnorm_atTop

/-! ### The band, and with it the interval class

The stationary mark law is determined on the interval class by the half-lines,
by additivity.  This is the form `Section5Join.stationaryMeanR_gap_le` and the
Selberg bracket can consume. -/

lemma levyIntensity_Ioi_lt_top {u : ℝ} (hu : 0 < u) : levyIntensity (Ioi u) ≠ ⊤ := by
  rw [levyIntensity_Ioi hu]
  exact ENNReal.ofReal_ne_top

/-- `Λ((u,v]) = Λ((u,∞)) − Λ((v,∞))`. -/
theorem levyIntensity_Ioc_toReal {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (levyIntensity (Ioc u v)).toReal
      = (levyIntensity (Ioi u)).toReal - (levyIntensity (Ioi v)).toReal := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hunion : Ioi u = Ioc u v ∪ Ioi v := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      rcases le_or_gt x v with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, -⟩ | hx)
      · exact hx
      · exact lt_of_le_of_lt huv hx
  have hdisj : Disjoint (Ioc u v) (Ioi v) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd hx3 (not_lt.mpr hx2)
  have hsplit : levyIntensity (Ioi u) = levyIntensity (Ioc u v) + levyIntensity (Ioi v) := by
    conv_lhs => rw [hunion]
    exact measure_union hdisj measurableSet_Ioi
  have hfin : levyIntensity (Ioc u v) ≠ ⊤ :=
    ne_top_of_le_ne_top (levyIntensity_Ioi_lt_top hu)
      (measure_mono (fun x hx => hx.1))
  rw [hsplit, ENNReal.toReal_add hfin (levyIntensity_Ioi_lt_top hv)]
  ring

/-- **The normalisation on a band.**  `L·(markTailMean(uL) − markTailMean(vL))
→ 2λ·Λ((u,v])`: display (35) on an interval, hence on the whole interval class
by additivity. -/
theorem tendsto_scaled_markBandMean {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Tendsto (fun L : ℝ => L * (markTailMean (u * L) - markTailMean (v * L))) atTop
      (𝓝 (2 * lyapunov * (levyIntensity (Ioc u v)).toReal)) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h := (tendsto_scaled_markTailMean hu).sub (tendsto_scaled_markTailMean hv)
  rw [levyIntensity_Ioc_toReal hu huv, mul_sub]
  exact h.congr fun L => by ring

end

end GaussKuzmin

end Kwon1002
