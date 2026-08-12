import Kwon1002.Section4

/-!
# Layer 0 of the natural extension: the base measure `ν̂` and `μ̂₀ = ν̂ ⊗ m_{T²}`

`Kwon1002.hatMu0` (`Section4.lean`) is the stationary measure of the
Gauss natural extension times Haar on `T²`.  Until now its base factor,
the measure

`ν̂ = 1/(log 2 (1+xy)²) dx dy` on `(0,1)²`,

had no name: it was written out inline at each of the three places in
`Kwon1002/Lemma62.lean` that needed it.  This file names it `hatNu`,
computes its total mass, and records the factorization
`μ̂₀ = ν̂ ⊗ (Lebesgue on (0,1)²)`.

## What is proved

* `hatNu_univ`, `ν̂((0,1)²) = 1`, hence `isProbabilityMeasure_hatNu`.
  The computation is the one in §3 of the manuscript: the inner integral
  `∫₀¹ dy/(1+xy)² = 1/(1+x)` (antiderivative `y/(1+xy)`, which avoids the
  `1/x` that the partial-fraction antiderivative would introduce and so
  needs no case split at `x = 0`), and then `∫₀¹ dx/(1+x) = log 2`, which
  the `1/log 2` normalisation cancels exactly.
* `hatMu0_eq_prod`, `μ̂₀ = ν̂ ⊗ m` with `m` Lebesgue on `(0,1)²`.  This is
  the shape `MeasureTheory.MeasurePreserving.skew_product` needs in order
  to assemble `hatS` out of `natExtMap` on the base and the fibre map on
  `T²`, so it is a prerequisite for `hatS_measurePreserving`.
* `isProbabilityMeasure_hatMu0`.  Only `isFiniteMeasure_hatMu0`
  (`Kwon1002/Prop42.lean`) was available before; every ergodic and
  recurrence statement above this layer needs the total mass to be `1`,
  not merely finite.
* `hatNu_fst_marginal`, the future-coordinate marginal: `(Prod.fst)_* ν̂`
  is the Gauss measure `gaussMarginal` with density `1/(log 2 (1+x))` on
  `(0,1)`.  The fibre computation it rests on, `∫₀¹ dy/(1+xy)² = 1/(1+x)`,
  is the inner half of `hatNu_univ`, refactored out as
  `lintegral_hatNuDensity_slice`.  The past-coordinate mirror is
  `hatNu_snd_marginal` in `Kwon1002/NatExtInvariance.lean`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

noncomputable section

/-- The unit square `(0,1)²`, the state space of the Gauss natural
extension and (as `T²` in the `Int.fract` representation) of the torus
fibre. -/
def unitSq : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

lemma measurableSet_unitSq : MeasurableSet unitSq :=
  measurableSet_Ioo.prod measurableSet_Ioo

lemma volume_unitSq : volume unitSq = 1 := by
  simp [unitSq, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]

/-- **`ν̂`**, the stationary measure of the Gauss natural extension:
Lebesgue on `(0,1)²` with density `1/(log 2 (1+xy)²)` (§3, in the proof of
Lemma 3.3).  This is the base factor of `hatMu0`. -/
def hatNu : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)).withDensity
    (fun p => ENNReal.ofReal (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2)))

/-- Statement identity, type check only: `hatNu` is exactly the measure
that `Kwon1002/Lemma62.lean` used to write out inline.  If the definition
above drifts, this breaks. -/
example : hatNu = (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)).withDensity
    (fun p => ENNReal.ofReal (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2))) := rfl

/-- **The Gauss measure `γ`** on `(0,1)`: Lebesgue with density
`1/(log 2 (1+x))`.  It is the common marginal of `ν̂` in each of its two
coordinates (`NatExtMeasure.hatNu_fst_marginal` below and
`NatExtMeasure.hatNu_snd_marginal` in `Kwon1002/NatExtInvariance.lean`),
hence the stationary law of the future coordinate of the natural
extension. -/
def gaussMarginal : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (1 / (Real.log 2 * (1 + x))))

namespace NatExtMeasure

/-- The density of `ν̂` is measurable. -/
lemma measurable_hatNuDensity :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2))) := by
  refine ENNReal.measurable_ofReal.comp ?_
  fun_prop

lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- `∫₀¹ dy/(1+xy)² = 1/(1+x)` for `x ≥ 0`, via the antiderivative
`y ↦ y/(1+xy)`. -/
theorem integral_inv_one_add_mul_sq (x : ℝ) (hx : 0 ≤ x) :
    ∫ y in (0:ℝ)..1, 1 / (1 + x * y) ^ 2 = 1 / (1 + x) := by
  have hpos : ∀ y ∈ uIcc (0:ℝ) 1, (0:ℝ) < 1 + x * y := by
    intro y hy
    rw [uIcc_of_le (by norm_num)] at hy
    nlinarith [hy.1, hy.2]
  have hderiv : ∀ y ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => t / (1 + x * t)) (1 / (1 + x * y) ^ 2) y := by
    intro y hy
    have hne : (1 + x * y) ≠ 0 := (hpos y hy).ne'
    have h1 : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have h2 : HasDerivAt (fun t : ℝ => 1 + x * t) x y := by
      simpa using ((hasDerivAt_id y).const_mul x).const_add (1:ℝ)
    have hq := h1.div h2 hne
    convert hq using 1
    ring
  have hint : IntervalIntegrable (fun y : ℝ => 1 / (1 + x * y) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro y hy; exact pow_ne_zero _ (hpos y hy).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- `∫₀¹ dx/(1+x) = log 2`. -/
theorem integral_inv_one_add : ∫ x in (0:ℝ)..1, 1 / (1 + x) = Real.log 2 := by
  have hpos : ∀ y ∈ uIcc (0:ℝ) 1, (0:ℝ) < 1 + y := by
    intro y hy
    rw [uIcc_of_le (by norm_num)] at hy
    linarith [hy.1]
  have hderiv : ∀ y ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + y)) y := by
    intro y hy
    have h2 : HasDerivAt (fun t : ℝ => 1 + t) 1 y := by
      simpa using (hasDerivAt_id y).const_add (1:ℝ)
    exact h2.log (hpos y hy).ne'
  have hint : IntervalIntegrable (fun y : ℝ => 1 / (1 + y)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro y hy; exact (hpos y hy).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- A nonnegative function continuous on `[0,1]` has the same `(0,1)`
lower integral as its `ofReal`-ed interval integral. -/
theorem lintegral_Ioo_ofReal_eq {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hnn : ∀ y ∈ Icc (0:ℝ) 1, 0 ≤ f y) :
    ∫⁻ y in Ioo (0:ℝ) 1, ENNReal.ofReal (f y)
      = ENNReal.ofReal (∫ y in (0:ℝ)..1, f y) := by
  have hIcc : IntegrableOn f (Icc (0:ℝ) 1) volume := hf.integrableOn_Icc
  have hIoo : IntegrableOn f (Ioo (0:ℝ) 1) volume := hIcc.mono_set Ioo_subset_Icc_self
  have hnn' : (0 : ℝ → ℝ) ≤ᶠ[ae (volume.restrict (Ioo (0:ℝ) 1))] f := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) 1))] with y hy
    exact hnn y (Ioo_subset_Icc_self hy)
  rw [← ofReal_integral_eq_lintegral_ofReal hIoo hnn']
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The fibre slice of the `ν̂` density**: for `x ≥ 0`,
`∫₀¹ dy/(log 2 (1+xy)²) = 1/(log 2 (1+x))`, via the antiderivative
`y ↦ y/(1+xy)` of `integral_inv_one_add_mul_sq`.  This used to be the inner
half of the proof of `hatNu_univ`, written inline there; it is refactored
out because it is also the density identity behind the first-coordinate
marginal `hatNu_fst_marginal`. -/
theorem lintegral_hatNuDensity_slice {x : ℝ} (hx : 0 ≤ x) :
    (∫⁻ y in Ioo (0:ℝ) 1, ENNReal.ofReal (1 / (Real.log 2 * (1 + x * y) ^ 2)))
      = ENNReal.ofReal (1 / (Real.log 2 * (1 + x))) := by
  have hl := log_two_pos
  have hpos : ∀ y ∈ Icc (0:ℝ) 1, (0:ℝ) < 1 + x * y := by
    intro y hy; nlinarith [hy.1, hy.2]
  rw [lintegral_Ioo_ofReal_eq (f := fun y => 1 / (Real.log 2 * (1 + x * y) ^ 2))]
  · congr 1
    have hsplit : (fun y : ℝ => 1 / (Real.log 2 * (1 + x * y) ^ 2))
        = fun y : ℝ => (Real.log 2)⁻¹ * (1 / (1 + x * y) ^ 2) := by
      funext y; field_simp
    rw [hsplit, intervalIntegral.integral_const_mul,
      integral_inv_one_add_mul_sq x hx]
    field_simp
  · apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro y hy
      exact mul_ne_zero hl.ne' (pow_ne_zero _ (hpos y hy).ne')
  · intro y hy
    positivity

/-- Lebesgue on the square, as a product of Lebesgue on the factors. -/
theorem restrict_unitSq_eq_prod :
    (volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)
      = ((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)).prod
          ((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- Lebesgue on the four-dimensional box, as a product of two copies of
Lebesgue on the square. -/
theorem restrict_box_eq_prod :
    (volume : Measure ((ℝ × ℝ) × ℝ × ℝ)).restrict
        ((Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) ×ˢ (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1))
      = ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)).prod
          ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- **The future-coordinate marginal of `ν̂` is the Gauss measure**:
`(Prod.fst)_* ν̂ = γ`.  Fubini over the square reduces the claim on a test
set `A` to the fibre computation `lintegral_hatNuDensity_slice`.  The
mirror statement for the past coordinate is `hatNu_snd_marginal` in
`Kwon1002/NatExtInvariance.lean`, where the swap symmetry of the density
is available. -/
theorem hatNu_fst_marginal : hatNu.map Prod.fst = gaussMarginal := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply measurable_fst hA, hatNu, gaussMarginal,
    withDensity_apply _ (measurable_fst hA), withDensity_apply _ hA,
    restrict_unitSq_eq_prod, ← Set.prod_univ, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ measurable_hatNuDensity.aemeasurable,
    Measure.restrict_restrict hA]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem (hA.inter measurableSet_Ioo)] with x hx
  exact lintegral_hatNuDensity_slice hx.2.1.le

/-! ### Haar on the torus in the `Int.fract` representation

Throughout this development `T = ℝ/ℤ` is carried as `(0,1)` with
`Int.fract` performing the reduction, rather than as Mathlib's
`AddCircle 1`.  The one fact that representation needs is that a rotation
is measure preserving, and it is elementary in this form: `r ↦ {r + c}`
cuts `[0,1)` at `1 - {c}` and translates the two pieces by `{c}` and by
`{c} - 1`, so it is a bijection assembled from two translations, each of
which preserves Lebesgue measure. -/

/-- **Rotation of the circle, in the `Int.fract` representation.**
`r ↦ {r + c}` preserves Lebesgue measure on `[0,1)`. -/
theorem map_fract_add_Ico (c : ℝ) :
    Measure.map (fun r : ℝ => Int.fract (r + c)) (volume.restrict (Ico (0:ℝ) 1))
      = volume.restrict (Ico (0:ℝ) 1) := by
  set β := Int.fract c with hβdef
  have hβ0 : (0:ℝ) ≤ β := Int.fract_nonneg c
  have hβ1 : β < 1 := Int.fract_lt_one c
  have hmeas : Measurable (fun r : ℝ => Int.fract (r + c)) := (measurable_id.add_const c).fract
  have hfeq : ∀ r : ℝ, Int.fract (r + c) = Int.fract (r + β) := by
    intro r
    have h : r + c = (r + β) + ((⌊c⌋ : ℤ) : ℝ) := by
      rw [hβdef, Int.fract]; ring
    rw [h, Int.fract_add_intCast]
  ext S hS
  rw [Measure.map_apply hmeas hS, Measure.restrict_apply (hmeas hS), Measure.restrict_apply hS]
  set P : Set ℝ := (fun r : ℝ => Int.fract (r + c)) ⁻¹' S with hP
  have hsplit : Ico (0:ℝ) 1 = Ico (0:ℝ) (1 - β) ∪ Ico (1 - β) 1 :=
    (Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)).symm
  -- the lower piece is translated by `β` onto `[β, 1)`
  have hA : P ∩ Ico (0:ℝ) (1 - β) = (fun r : ℝ => r + β) ⁻¹' (S ∩ Ico β 1) := by
    ext r
    simp only [hP, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico]
    constructor
    · rintro ⟨hs, hr0, hr1⟩
      have hval : Int.fract (r + c) = r + β := by
        rw [hfeq]; exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hval] at hs
      exact ⟨hs, by linarith, by linarith⟩
    · rintro ⟨hs, hr0, hr1⟩
      have hr0' : (0:ℝ) ≤ r := by linarith
      have hr1' : r < 1 - β := by linarith
      have hval : Int.fract (r + c) = r + β := by
        rw [hfeq]; exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      exact ⟨by rw [hval]; exact hs, hr0', hr1'⟩
  -- the upper piece is translated by `β - 1` onto `[0, β)`
  have hB : P ∩ Ico (1 - β) 1 = (fun r : ℝ => r + (β - 1)) ⁻¹' (S ∩ Ico 0 β) := by
    ext r
    simp only [hP, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico]
    have hval : ∀ r : ℝ, 1 - β ≤ r → r < 1 → Int.fract (r + c) = r + (β - 1) := by
      intro r h1 h2
      rw [hfeq]
      have he : r + β = (r + (β - 1)) + 1 := by ring
      rw [he, Int.fract_add_one]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    constructor
    · rintro ⟨hs, hr0, hr1⟩
      rw [hval r hr0 hr1] at hs
      exact ⟨hs, by linarith, by linarith⟩
    · rintro ⟨hs, hr0, hr1⟩
      have hr0' : 1 - β ≤ r := by linarith
      have hr1' : r < 1 := by linarith
      exact ⟨by rw [hval r hr0' hr1']; exact hs, hr0', hr1'⟩
  have hdisj : Disjoint (P ∩ Ico (0:ℝ) (1 - β)) (P ∩ Ico (1 - β) 1) :=
    Disjoint.mono inter_subset_right inter_subset_right Set.Ico_disjoint_Ico_same
  have hmB : MeasurableSet (P ∩ Ico (1 - β) 1) := (hmeas hS).inter measurableSet_Ico
  have hunion : P ∩ Ico (0:ℝ) 1
      = (P ∩ Ico (0:ℝ) (1 - β)) ∪ (P ∩ Ico (1 - β) 1) := by
    rw [hsplit, Set.inter_union_distrib_left]
  rw [hunion, measure_union hdisj hmB, hA, hB,
    measure_preimage_add_right, measure_preimage_add_right]
  have hSdisj : Disjoint (S ∩ Ico β 1) (S ∩ Ico (0:ℝ) β) :=
    Disjoint.mono inter_subset_right inter_subset_right Set.Ico_disjoint_Ico_same.symm
  have hSunion : S ∩ Ico (0:ℝ) 1 = (S ∩ Ico β 1) ∪ (S ∩ Ico (0:ℝ) β) := by
    rw [← Set.inter_union_distrib_left, Set.union_comm,
      Set.Ico_union_Ico_eq_Ico hβ0 hβ1.le]
  rw [hSunion, measure_union hSdisj (hS.inter measurableSet_Ico)]

/-- `(0,1)` and `[0,1)` carry the same restricted Lebesgue measure; the
endpoint is a null set. -/
theorem restrict_Ioo_eq_Ico :
    (volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)
      = (volume : Measure ℝ).restrict (Ico (0:ℝ) 1) :=
  Measure.restrict_congr_set Ioo_ae_eq_Ico

/-- The form the torus fibre map needs: `r ↦ {r - c}` preserves Lebesgue
measure on `(0,1)`. -/
theorem map_fract_sub_Ioo (c : ℝ) :
    Measure.map (fun r : ℝ => Int.fract (r - c)) (volume.restrict (Ioo (0:ℝ) 1))
      = volume.restrict (Ioo (0:ℝ) 1) := by
  have hfun : (fun r : ℝ => Int.fract (r - c)) = fun r : ℝ => Int.fract (r + (-c)) := by
    funext r; rw [sub_eq_add_neg]
  rw [hfun, restrict_Ioo_eq_Ico]
  exact map_fract_add_Ico (-c)

end NatExtMeasure

open NatExtMeasure in
/-- **`ν̂` is a probability measure**: `∫∫ dx dy/(log 2 (1+xy)²) = 1` over
`(0,1)²`.  The inner integral is `1/(log 2 (1+x))` and the outer one is
`(log 2)⁻¹ log 2 = 1`. -/
theorem hatNu_univ : hatNu Set.univ = 1 := by
  have hl := log_two_pos
  rw [hatNu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    restrict_unitSq_eq_prod, lintegral_prod _ measurable_hatNuDensity.aemeasurable]
  rw [setLIntegral_congr_fun measurableSet_Ioo
      (fun x hx => lintegral_hatNuDensity_slice hx.1.le),
    lintegral_Ioo_ofReal_eq (f := fun x => 1 / (Real.log 2 * (1 + x)))]
  · have hsplit : (fun x : ℝ => 1 / (Real.log 2 * (1 + x)))
        = fun x : ℝ => (Real.log 2)⁻¹ * (1 / (1 + x)) := by
      funext x; field_simp
    rw [hsplit, intervalIntegral.integral_const_mul, integral_inv_one_add,
      inv_mul_cancel₀ hl.ne']
    simp
  · apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro y hy
      have hy1 : (0:ℝ) < 1 + y := by linarith [hy.1]
      exact mul_ne_zero hl.ne' hy1.ne'
  · intro y hy
    have hy1 : (0:ℝ) < 1 + y := by linarith [hy.1]
    positivity

instance isProbabilityMeasure_hatNu : IsProbabilityMeasure hatNu := ⟨hatNu_univ⟩

instance isProbabilityMeasure_restrict_unitSq :
    IsProbabilityMeasure ((volume : Measure (ℝ × ℝ)).restrict
      (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  simpa [unitSq] using volume_unitSq

/-- **The factorization `μ̂₀ = ν̂ ⊗ m_{T²}`.**  The density of `μ̂₀` depends
only on the base coordinate `z.1`, so `μ̂₀` is the `withDensity` of a
product with a density pulled back from the left factor, which is exactly
`Measure.prod_withDensity_left`.  This is the shape
`MeasureTheory.MeasurePreserving.skew_product` consumes. -/
theorem hatMu0_eq_prod :
    hatMu0 = hatNu.prod ((volume : Measure (ℝ × ℝ)).restrict
      (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) := by
  rw [hatMu0, NatExtMeasure.restrict_box_eq_prod, hatNu,
    MeasureTheory.prod_withDensity_left NatExtMeasure.measurable_hatNuDensity]

/-- **`μ̂₀` is a probability measure.**  `Kwon1002/Prop42.lean` records only
`isFiniteMeasure_hatMu0`; every ergodic and recurrence statement above
this layer needs the mass to be exactly `1`. -/
instance isProbabilityMeasure_hatMu0 : IsProbabilityMeasure hatMu0 := by
  rw [hatMu0_eq_prod]
  infer_instance

end

end Kwon1002
