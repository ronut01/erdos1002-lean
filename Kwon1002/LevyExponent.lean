import Kwon1002.CauchyLaw
import Kwon1002.FourierPairs
import Erdos1002.FactorialEventExpansion

/-!
# Scratch (agent `levy`), the Lévy exponent and the factorial moments

Two sorried targets of `Kwon1002.CauchyLaw` are attacked here.

* `levy_exponent_limit_raw` is **proved**, from the single classical input
  `Kwon1002.integral_one_sub_cos_div_sq` (`∫_ℝ (1-cos u) u⁻² du = π`, which is
  a separate sorried theorem of `CauchyLaw.lean`, not one of my targets).
  Everything else, integrability of the Lévy integrand, the substitution
  `u = t x`, the symmetric truncation limit and the arithmetic of the
  constant, is proved outright here.
* `factorialMoment_convergence` is **reduced** to the ordered-tuple
  probabilities of display (39), i.e. to the §4 quasi-independence input.
  The whole measure-theoretic bookkeeping (random index set, the
  `descFactorial` ↔ ordered-tuple combinatorics, the push-forward) is proved.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal Real

namespace Kwon1002

namespace LevyExponent

noncomputable section

/-! ## Part I, the Lévy exponent -/

/-- `φ(u) = (1 - cos u)/u²`, the kernel of `integral_one_sub_cos_div_sq`. -/
def cosKernel (u : ℝ) : ℝ := (1 - Real.cos u) / u ^ 2

lemma measurable_cosKernel : Measurable cosKernel :=
  (measurable_const.sub Real.measurable_cos).div (measurable_id.pow_const 2)

lemma cosKernel_nonneg (u : ℝ) : 0 ≤ cosKernel u :=
  div_nonneg (by linarith [Real.cos_le_one u]) (sq_nonneg u)

/-- The uniform envelope `(1-cos u)/u² ≤ 3/(1+u²)`: near `0` use
`1 - cos u ≤ u²/2`, far out use `1 - cos u ≤ 2`. -/
lemma cosKernel_le (u : ℝ) : cosKernel u ≤ 3 * (1 + u ^ 2)⁻¹ := by
  have hb1 : 1 - Real.cos u ≤ u ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := u)
    linarith
  have hb2 : 1 - Real.cos u ≤ 2 := by linarith [Real.neg_one_le_cos u]
  have hpos : (0 : ℝ) < 1 + u ^ 2 := by positivity
  rcases eq_or_ne u 0 with rfl | hu
  · norm_num [cosKernel]
  · have hu2 : (0 : ℝ) < u ^ 2 := by positivity
    have h3 : (1 - Real.cos u) * u ^ 2 ≤ 2 * u ^ 2 :=
      mul_le_mul_of_nonneg_right hb2 (sq_nonneg u)
    have hrw : (3 : ℝ) * (1 + u ^ 2)⁻¹ * u ^ 2 = 3 * u ^ 2 / (1 + u ^ 2) := by
      field_simp
    rw [cosKernel, div_le_iff₀ hu2, hrw, le_div_iff₀ hpos]
    nlinarith [hb1, h3, hu2]

lemma integrable_cosKernel : Integrable cosKernel := by
  refine Integrable.mono' (g := fun u : ℝ => 3 * (1 + u ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 3) measurable_cosKernel.aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (cosKernel_nonneg u)]
  exact cosKernel_le u

/-- The Lévy integrand of display (37), rewritten as a rescaled copy of
`cosKernel`.  Lean's `x / 0 = 0` convention makes this an identity for **all**
`t` and `x`, including the excluded point `x = 0`. -/
lemma levyIntegrand_eq (t x : ℝ) :
    (Real.cos (t * x) - 1) * levyIntensityDensity x
      = -(1 / (2 * Real.pi ^ 2)) * (t ^ 2 * cosKernel (t * x)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [cosKernel]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [levyIntensityDensity, cosKernel]
  · have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have htx : t * x ≠ 0 := mul_ne_zero ht hx
    unfold levyIntensityDensity cosKernel
    field_simp
    ring

lemma integrable_levyIntegrand (t : ℝ) :
    Integrable (fun x : ℝ => (Real.cos (t * x) - 1) * levyIntensityDensity x) := by
  rcases eq_or_ne t 0 with rfl | ht
  · have h : (fun x : ℝ => (Real.cos (0 * x) - 1) * levyIntensityDensity x)
        = fun _ : ℝ => (0 : ℝ) := by
      funext x; simp
    rw [h]
    exact integrable_zero ℝ ℝ volume
  · simp_rw [levyIntegrand_eq t]
    exact (((integrable_comp_mul_left_iff cosKernel ht).2
      integrable_cosKernel).const_mul (t ^ 2)).const_mul _

/-- The full-line Lévy exponent.  **The constant is computed, not assumed**:
`∫_ℝ (cos(tx) - 1) dΛ(x) = -(π · levyConst · |t|)`, and
`π · levyConst = 1/(2π)` by `Kwon1002.cauchyScale_eq`. -/
lemma integral_levyIntegrand (t : ℝ) :
    (∫ x : ℝ, (Real.cos (t * x) - 1) * levyIntensityDensity x)
      = -(Real.pi * levyConst * |t|) := by
  have hD : (∫ u : ℝ, cosKernel u) = Real.pi :=
    Kwon1002.FourierPairs.integral_one_sub_cos_div_sq
  have habs : t ^ 2 * |t⁻¹| = |t| := by
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · have h : |t| ≠ 0 := abs_ne_zero.mpr ht
      rw [abs_inv, ← sq_abs t, pow_two, mul_assoc, mul_inv_cancel₀ h, mul_one]
  simp_rw [levyIntegrand_eq t]
  rw [integral_const_mul, integral_const_mul, Measure.integral_comp_mul_left cosKernel t,
    hD, smul_eq_mul, levyConst,
    show t ^ 2 * (|t⁻¹| * Real.pi) = t ^ 2 * |t⁻¹| * Real.pi from by ring, habs]
  ring

lemma levyTrunc_measurableSet (k : ℕ) : MeasurableSet {x : ℝ | 1 / (k + 1 : ℝ) < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

lemma levyTrunc_monotone : Monotone (fun k : ℕ => {x : ℝ | 1 / (k + 1 : ℝ) < |x|}) := by
  intro k m hkm x hx
  simp only [mem_setOf_eq] at hx ⊢
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : ((k : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
    have : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hkm
    linarith
  calc 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le h1 h2
    _ < |x| := hx

lemma levyTrunc_iUnion :
    (⋃ k : ℕ, {x : ℝ | 1 / (k + 1 : ℝ) < |x|}) = {x : ℝ | x ≠ 0} := by
  ext x
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨k, hk⟩ h
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [h, abs_zero] at hk
    linarith
  · intro hx
    exact exists_nat_one_div_lt (abs_pos.mpr hx)

/-- **Target 1 (proved).**  Token-identical restatement of
`Kwon1002.levy_exponent_limit_raw`. -/
theorem levy_exponent_limit_raw (t : ℝ) :
    Tendsto (fun k : ℕ =>
        ∫ x in {x : ℝ | 1 / (k + 1 : ℝ) < |x|},
          (Real.cos (t * x) - 1) * levyIntensityDensity x)
      atTop (𝓝 (-(Real.pi * levyConst * |t|))) := by
  have hint := integrable_levyIntegrand t
  have hiO : IntegrableOn (fun x : ℝ => (Real.cos (t * x) - 1) * levyIntensityDensity x)
      (⋃ k : ℕ, {x : ℝ | 1 / (k + 1 : ℝ) < |x|}) volume := hint.integrableOn
  have key := tendsto_setIntegral_of_monotone
    (f := fun x : ℝ => (Real.cos (t * x) - 1) * levyIntensityDensity x)
    (μ := volume) levyTrunc_measurableSet levyTrunc_monotone hiO
  rw [levyTrunc_iUnion] at key
  have hae : {x : ℝ | x ≠ 0} =ᵐ[volume] (univ : Set ℝ) := by
    rw [ae_eq_univ]
    have hc : {x : ℝ | x ≠ 0}ᶜ = ({0} : Set ℝ) := by ext x; simp
    rw [hc]
    exact measure_singleton 0
  rw [setIntegral_congr_set hae, setIntegral_univ, integral_levyIntegrand t] at key
  exact key

/-! ## Part II, the factorial moments -/

section Counts

/-- The event that level `j` is a bulk level of `α` and its normalized signed
mark lands in `B`. -/
def bulkMarkEvent (c : ℝ) (n : ℕ) (B : Set ℝ) (j : ℕ) : Set ℝ :=
  {α : ℝ | j ∈ bulkIndices c α n ∧ signedMark α n j ∈ B}

lemma measurableSet_bulkMarkEvent (c : ℝ) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B)
    (j : ℕ) : MeasurableSet (bulkMarkEvent c n B j) := by
  have h : bulkMarkEvent c n B j
      = {α : ℝ | j ∈ bulkIndices c α n} ∩ ((fun α : ℝ => signedMark α n j) ⁻¹' B) := rfl
  rw [h]
  exact (measurableSet_mem_bulkIndices c n j).inter ((measurable_signedMark n j) hB)

lemma ae_irrational : ∀ᵐ α : ℝ, Irrational α := by
  rw [ae_iff]
  have h : {a : ℝ | ¬ Irrational a} = Set.range ((↑) : ℚ → ℝ) := by
    ext a; simp [Irrational]
  rw [h]
  exact (Set.countable_range _).measure_zero volume

/-- The random index set is a.e. contained in `{0,…,n}` (because
`τ_n(α) ≤ n` for irrational `α ∈ (0,1)`), so the point count of `Ξ_n` is a
count of a **deterministic** family of events. -/
lemma pointCount_eq_finiteEventCount (c : ℝ) (B : Set ℝ) (n : ℕ) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    pointCount c α n B
      = Erdos1002.finiteEventCount (Finset.range (n + 1)) (bulkMarkEvent c n B) α := by
  classical
  have hsub := bulkIndices_subset_range c α hα hirr n
  have h1 : ∀ j ∈ bulkIndices c α n,
      (if α ∈ bulkMarkEvent c n B j then (1 : ℕ) else 0)
        = (if signedMark α n j ∈ B then (1 : ℕ) else 0) := by
    intro j hj
    simp [bulkMarkEvent, hj]
  have h2 : ∀ j ∈ Finset.range (n + 1), j ∉ bulkIndices c α n →
      (if α ∈ bulkMarkEvent c n B j then (1 : ℕ) else 0) = 0 := by
    intro j _ hj
    simp [bulkMarkEvent, hj]
  calc pointCount c α n B
      = ∑ j ∈ bulkIndices c α n, (if α ∈ bulkMarkEvent c n B j then (1 : ℕ) else 0) :=
        (Finset.sum_congr rfl h1).symm
    _ = ∑ j ∈ Finset.range (n + 1),
          (if α ∈ bulkMarkEvent c n B j then (1 : ℕ) else 0) :=
        Finset.sum_subset hsub h2
    _ = Erdos1002.finiteEventCount (Finset.range (n + 1)) (bulkMarkEvent c n B) α := rfl

lemma measurable_bulkCount (c : ℝ) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable fun α : ℝ =>
      Erdos1002.finiteEventCount (Finset.range (n + 1)) (bulkMarkEvent c n B) α := by
  classical
  have h : ∀ α : ℝ,
      Erdos1002.finiteEventCount (Finset.range (n + 1)) (bulkMarkEvent c n B) α
        = ∑ j ∈ Finset.range (n + 1),
            (bulkMarkEvent c n B j).indicator (fun _ => (1 : ℕ)) α := by
    intro α
    simp [Erdos1002.finiteEventCount, Set.indicator_apply]
  simp only [h]
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.indicator (measurableSet_bulkMarkEvent c n hB j)

lemma countLaw_eq_map (c : ℝ) (n : ℕ) (B : Set ℝ) :
    countLaw c n B
      = unifIoo.map (fun α : ℝ =>
          Erdos1002.finiteEventCount (Finset.range (n + 1)) (bulkMarkEvent c n B) α) := by
  have h1 : ∀ᵐ α ∂unifIoo, α ∈ Ioo (0 : ℝ) 1 := by
    simp only [unifIoo]
    exact ae_restrict_mem measurableSet_Ioo
  have h2 : ∀ᵐ α ∂unifIoo, Irrational α := by
    simp only [unifIoo]
    exact ae_restrict_of_ae ae_irrational
  rw [countLaw]
  refine Measure.map_congr ?_
  filter_upwards [h1, h2] with α hα hirr
  exact pointCount_eq_finiteEventCount c B n hα hirr

/-- **Display (38), unpacked.**  The `k`-th factorial moment of the count
`N_n(B)` is *exactly* the sum of the probabilities of the ordered distinct
`k`-tuples of bulk levels whose marks all land in `B`.  This is Wang's
`integral_finiteEventCount_descFactorial` applied to our point process, and it
is proved with no diagonal or multiplicity convention left implicit. -/
lemma factorialMoment_eq_tupleSum (c : ℝ) {B : Set ℝ} (hB : MeasurableSet B)
    (νs : ℕ → ProbabilityMeasure ℕ) (hlaw : ∀ n, (νs n : Measure ℕ) = countLaw c n B)
    (n k : ℕ) :
    Erdos1002.FactorialMomentMethod.factorialMoment (νs n) k
      = ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
          unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f) := by
  unfold Erdos1002.FactorialMomentMethod.factorialMoment
  rw [hlaw n, countLaw_eq_map,
    integral_map (measurable_bulkCount c n hB).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  exact Erdos1002.integral_finiteEventCount_descFactorial (Finset.range (n + 1))
    (bulkMarkEvent c n B) k unifIoo (fun j _ => measurableSet_bulkMarkEvent c n hB j)

/-- **The remaining obstruction (sorried): displays (39)-(40).**  The ordered
`k`-tuple probabilities factorize asymptotically into `Λ(B)^k`.  This is the
§4 quasi-independence input (Prop 4.1) together with the tuple bookkeeping of
(39): Jackson approximation of `φ ∘ mark`, the `a ≤ L^D` digit cut, the
`O(L^{r-1}H)` bad-tuple count and the parity/ordering partition.  Nothing
below this line is assumed. -/
theorem tuple_measure_convergence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  sorry

/-- **Target 2 (reduced).**  Token-identical restatement of
`Kwon1002.factorialMoment_convergence`, derived from
`tuple_measure_convergence`. -/
theorem factorialMoment_convergence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (νs : ℕ → ProbabilityMeasure ℕ) (_hlaw : ∀ n, (νs n : Measure ℕ) = countLaw c n B)
    (k : ℕ) :
    Tendsto (fun n => Erdos1002.FactorialMomentMethod.factorialMoment (νs n) k)
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  have h : (fun n => Erdos1002.FactorialMomentMethod.factorialMoment (νs n) k)
      = fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
          unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f) := by
    funext n
    exact factorialMoment_eq_tupleSum c _hB νs _hlaw n k
  rw [h]
  exact tuple_measure_convergence c B _hB _hB0 _hBbd k

/-! ### The integrability hypothesis of `poisson_count_limit`, discharged

`Kwon1002.poisson_count_limit` currently *assumes* `hInt`.  It is in fact free:
`N_n(B)` counts a family of `n+1` events, so it is bounded by `n+1`
pointwise, and every function is integrable against a law supported on a
bounded set of integers. -/

lemma finiteEventCount_le (c : ℝ) (n : ℕ) (B : Set ℝ) (α : ℝ) :
    Erdos1002.finiteEventCount (Finset.range (n + 1)) (bulkMarkEvent c n B) α ≤ n + 1 := by
  classical
  have h : Erdos1002.finiteEventCount (Finset.range (n + 1)) (bulkMarkEvent c n B) α
      ≤ ∑ _j ∈ Finset.range (n + 1), 1 := by
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs <;> simp
  simpa using h

lemma ae_le_of_countLaw (c : ℝ) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    ∀ᵐ m ∂(countLaw c n B), m ≤ n + 1 := by
  rw [countLaw_eq_map,
    ae_map_iff (measurable_bulkCount c n hB).aemeasurable ((Set.to_countable _).measurableSet)]
  filter_upwards with α
  exact finiteEventCount_le c n B α

/-- Hypothesis `hInt` of `Kwon1002.poisson_count_limit`, **proved**. -/
theorem integrable_descFactorial_countLaw (c : ℝ) {B : Set ℝ} (hB : MeasurableSet B)
    (νs : ℕ → ProbabilityMeasure ℕ) (hlaw : ∀ n, (νs n : Measure ℕ) = countLaw c n B)
    (n k : ℕ) :
    Integrable (fun m : ℕ => (m.descFactorial k : ℝ)) (νs n : Measure ℕ) := by
  have hae : ∀ᵐ m ∂((νs n : Measure ℕ)),
      ‖(m.descFactorial k : ℝ)‖ ≤ (((n + 1) ^ k : ℕ) : ℝ) := by
    rw [hlaw n]
    filter_upwards [ae_le_of_countLaw c n hB] with m hm
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast le_trans (Nat.descFactorial_le_pow m k) (Nat.pow_le_pow_left hm k)
  exact Integrable.mono' (integrable_const _)
    (measurable_of_countable _).aestronglyMeasurable hae

/-- **Proposition 5.1, counting form, with only the §4 input left.**  This is
`Kwon1002.poisson_count_limit` with *both* of its analytic hypotheses
discharged: integrability is proved above, and display (38) is reduced to
`tuple_measure_convergence`. -/
theorem poisson_count_limit_of_tuple (c : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (νs : ℕ → ProbabilityMeasure ℕ) (r : ℝ≥0)
    (hlaw : ∀ n, (νs n : Measure ℕ) = countLaw c n B)
    (hrate : (r : ℝ) = (levyIntensity B).toReal) :
    Tendsto νs atTop
      (𝓝 (Erdos1002.FactorialMomentMethod.poissonProbabilityMeasure r)) := by
  refine Erdos1002.FactorialMomentMethod.tendsto_poisson_of_factorialMoments νs r
    (integrable_descFactorial_countLaw c hB νs hlaw) fun k => ?_
  rw [hrate]
  exact factorialMoment_convergence c B hB hB0 hBbd νs hlaw k

end Counts

end

end LevyExponent

end Kwon1002
