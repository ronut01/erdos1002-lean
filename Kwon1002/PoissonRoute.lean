import Kwon1002.Assembly5
import Kwon1002.LevyExponent
import Erdos1002.ContinuousCompoundPoisson

/-!
# Scratch (agent `poisson`), the Proposition 5.1 route

Targets: `Kwon1002.CauchyLaw.factorialMoment_convergence` (display (38)) and
`Kwon1002.Assembly5.largeJump_weak_limit` (Proposition 5.1 + continuous
mapping).  Both statements are reproduced **token-identically** below.

## The point process is built, and it is used

The audit's warning about `CauchyLaw.poisson_count_limit` is real: that
theorem's hypotheses `_hlaw` (the law of the counts is the law of `N_n(B)`)
and `_hrate` (`r = Λ(B)`) are *unused*, so it is Wang's abstract
factorial-moment theorem with the manuscript's objects merely decorating the
statement.  Nothing here routes through it.

Instead `Ξ_n` itself is built as a measure and made to carry the mathematics:

* `xiMeasure c α n = ∑_{j ∈ J_n} δ_{X_{n,j}}`, the manuscript's `Ξ_n`
  (display (36)/(37)), a genuine random point measure on `ℝ`.
* `xiMeasure_apply` (**proved**), `Ξ_n(B) = N_n(B)`, the count that
  Proposition 5.1 is about, so `countLaw` really is the law of `Ξ_n(B)`.
* `largeSum_eq_xi_setIntegral` (**proved**), the *identity that makes the
  continuous-mapping step meaningful*:
  `largeSum c ε α n = ∫_{|x| > ε} x dΞ_n(α)`.
  The manuscript's large-jump part is exactly the linear functional
  `Ξ ↦ ∫_{|x|>ε} x dΞ` evaluated at `Ξ_n`, for **every** `n` and `α`
  (including the degenerate `n ≤ 1`, where `L = log n = 0`).
* `xi_count_poisson_limit` (**proved from the §4 input only**) -
  Proposition 5.1 in counting form, stated for the counts of `Ξ_n` and with
  *both* hypotheses used: it is `LevyExponent.poisson_count_limit_of_tuple`
  transported along `xiMeasure_apply`.

## The truncated Lévy measure is constructed, not assumed

`exists_levy_truncation_data` (**proved**): for `ε > 0` there are `r : ℝ≥0`
and a probability measure `ν` with `r = Λ{|x| > ε}` and
`r · ν = Λ|_{{|x| > ε}}`.  This needs `0 < Λ{|x|>ε} < ∞`, both proved here
(`levyIntensity_truncSet_ne_top`, `levyIntensity_truncSet_ne_zero`) from an
explicit Poisson-kernel domination.  So the limit law of Proposition 5.1 is
*exhibited*, not merely quantified over.  These are exactly the two
hypotheses of `CompoundCauchy.charFun_compoundPoisson_levy`, so the `ε ↓ 0`
argument of that file plugs into this data unchanged; and
`largeJump_limit_compoundPoisson` (its only sorried input, reproduced
token-identically at the end of this file) is discharged here.

## The one sorried input

`xi_largeIntegral_weak_limit`, display (37) plus the continuous mapping
theorem for the functional `Ξ ↦ ∫_{|x|>ε} x dΞ`: the laws of
`∫_{|x|>ε} x dΞ_n` converge weakly to the compound-Poisson law `CP(r, ν)`
with `r · ν = Λ|_{{|x|>ε}}`.  It is stated in point-process currency (the
`hμs` hypothesis is about `Ξ_n`, not about `largeSum`), and every hypothesis
is used in the derivation of the targets.

Obstruction: this is precisely the step the manuscript performs in the proof
of Cor. 5.3, "Proposition 5.1 and the continuous mapping theorem give
convergence of the large-jump part", legitimate because `Λ{|x| = ε} = 0` and
because the tails `|x| > R` may be removed first by the uniform bound
`sup_n E Ξ_n{|x| > R} ≤ C/R`.  Formalizing it needs the vague topology on
Radon point measures on `ℝ \ {0}` (no substrate module supplies it) together
with the joint/multivariate Poisson limit for counts on finitely many
disjoint continuity sets, the module the task brief calls
`MultivariatePoisson` **does not exist** in `wang_substrate` (the substrate
has the one-dimensional `PoissonFactorialConvergence` only).

## Consumed sorried inputs

* `Kwon1002.LevyExponent.tuple_measure_convergence` (displays (39)-(40)) -
  used for `factorialMoment_convergence` and `xi_count_poisson_limit`.
* `xi_largeIntegral_weak_limit` (stated and sorried here), used for
  `largeJump_weak_limit` and `largeJump_limit_compoundPoisson`.

Nothing else is assumed; in particular no sorried theorem of `CauchyLaw.lean`
or `Assembly5.lean` is used.

## Two remarks on faithfulness

* `Ξ_n` as built here lives on all of `ℝ` and may carry atoms at `0` (levels
  with digit `0`, or the degenerate `n ≤ 1`).  That is harmless and it is why
  the sorried input is phrased only through `∫_{|x|>ε} x dΞ_n`: display (37)
  is a statement in the vague topology on `ℝ \ {0}` (`Λ` is infinite near
  `0`), and no global weak convergence of `Ξ_n` on `ℝ` is claimed anywhere.
* The repository truncates hard (`truncatedMark`), the manuscript smoothly
  (`χ`).  For the large-jump limit this is immaterial exactly because
  `Λ{|x| = ε} = 0`, which is the same continuity-set condition the manuscript
  invokes for its continuous-mapping step.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal Real

namespace Kwon1002

namespace PoissonRoute

open Assembly5

noncomputable section

local instance scrPoissonPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Part A, the point process `Ξ_n` of display (36) -/

/-- The truncation set `{|x| > ε}` of the manuscript's `ε`-splitting. -/
def truncSet (ε : ℝ) : Set ℝ := {x : ℝ | ε < |x|}

lemma measurableSet_truncSet (ε : ℝ) : MeasurableSet (truncSet ε) :=
  measurableSet_lt measurable_const continuous_abs.measurable

/-- **The point process `Ξ_n`**, `Ξ_n = ∑_{j ∈ J_n} δ_{X_{n,j}}` with
`X_{n,j} = (-1)^j Z_{n,j}/L` the normalized signed mark, as a measure on `ℝ`. -/
def xiMeasure (c α : ℝ) (n : ℕ) : Measure ℝ :=
  ∑ j ∈ bulkIndices c α n, Measure.dirac (signedMark α n j)

/-- **`Ξ_n(B) = N_n(B)` (proved).**  The measure of a Borel set under the
point process is the point count `CauchyLaw.pointCount` that Proposition 5.1
is stated for. -/
lemma xiMeasure_apply (c α : ℝ) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    xiMeasure c α n B = (pointCount c α n B : ℝ≥0∞) := by
  classical
  have hcast : ((pointCount c α n B : ℕ) : ℝ≥0∞)
      = ∑ j ∈ bulkIndices c α n, (if signedMark α n j ∈ B then (1 : ℝ≥0∞) else 0) := by
    rw [pointCount, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : signedMark α n j ∈ B <;> simp [h]
  rw [hcast, xiMeasure, Measure.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.dirac_apply' _ hB]
  by_cases h : signedMark α n j ∈ B <;> simp [h]

/-- Integration of the identity against `Ξ_n` over a Borel set: the integral
is the sum of the points lying in the set. -/
lemma setIntegral_id_xiMeasure (c α : ℝ) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ x in S, x ∂(xiMeasure c α n))
      = ∑ j ∈ bulkIndices c α n,
          (if signedMark α n j ∈ S then signedMark α n j else 0) := by
  classical
  rw [← integral_indicator hS, xiMeasure,
    integral_finset_sum_measure (fun j _ =>
      integrable_dirac (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_lt_top))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_dirac]
  by_cases h : signedMark α n j ∈ S <;> simp [h]

/-- **The large-jump sum is a functional of `Ξ_n` (proved).**
`largeSum c ε α n = ∫_{|x| > ε} x dΞ_n(α)`.

This is the identity that gives the continuous-mapping step of Cor. 5.3 its
content: the manuscript's `L⁻¹ ∑_{j∈J_n} (-1)^j (Z_{n,j} - Z^{(ε)}_{n,j})` is
the linear functional `Ξ ↦ ∫_{|x|>ε} x dΞ` evaluated at `Ξ_n`.  It holds for
every `n`, including `n ≤ 1`, where `L = log n = 0` degenerates both sides
to `0`. -/
lemma largeSum_eq_xi_setIntegral (c ε : ℝ) (hε : 0 ≤ ε) (α : ℝ) (n : ℕ) :
    largeSum c ε α n = ∫ x in truncSet ε, x ∂(xiMeasure c α n) := by
  classical
  rw [setIntegral_id_xiMeasure c α n (measurableSet_truncSet ε), largeSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hL := Lnorm_nonneg n
  have hm := mark_nonneg α n j
  have habs : |signedMark α n j| = mark α n j / Lnorm n := by
    rw [signedMark, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hm, abs_of_nonneg hL]
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · have h0 : Lnorm n = 0 := hL0.symm
    have hnot : signedMark α n j ∉ truncSet ε := by
      simp only [truncSet, mem_setOf_eq, habs, h0, div_zero, not_lt]
      exact hε
    rw [if_neg hnot, h0, div_zero]
  · by_cases hcase : mark α n j ≤ ε * Lnorm n
    · have ht : truncatedMark ε α n j = mark α n j := by
        unfold truncatedMark; exact if_pos hcase
      have hnot : signedMark α n j ∉ truncSet ε := by
        simp only [truncSet, mem_setOf_eq, habs, not_lt, div_le_iff₀ hLpos]
        exact hcase
      rw [if_neg hnot, ht, sub_self, mul_zero, zero_div]
    · have ht : truncatedMark ε α n j = 0 := by
        unfold truncatedMark; exact if_neg hcase
      have hmem : signedMark α n j ∈ truncSet ε := by
        simp only [truncSet, mem_setOf_eq, habs, lt_div_iff₀ hLpos]
        exact not_le.mp hcase
      rw [if_pos hmem, ht, signedMark]
      ring

/-! ## Part B, the truncated Lévy measure `Λ|_{{|x|>ε}}` is constructed -/

lemma measurable_levyIntensityDensity : Measurable levyIntensityDensity := by
  unfold levyIntensityDensity
  exact measurable_const.div (measurable_const.mul (measurable_id.pow_const 2))

lemma levyIntensityDensity_nonneg (x : ℝ) : 0 ≤ levyIntensityDensity x := by
  unfold levyIntensityDensity; positivity

/-- Off `{|x| ≤ ε}` the Lévy density is dominated by a multiple of the
Poisson kernel. -/
lemma levyIntensityDensity_le_of_mem {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ truncSet ε) :
    levyIntensityDensity x ≤ ((1 + 1 / ε ^ 2) / (2 * Real.pi ^ 2)) * (1 + x ^ 2)⁻¹ := by
  have hxa : ε < |x| := hx
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hx2 : ε ^ 2 < x ^ 2 := by
    have h := sq_abs x
    nlinarith [abs_nonneg x]
  have hx2pos : (0 : ℝ) < x ^ 2 := lt_trans hε2 hx2
  have hpi : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  have hsum : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hkey : (1 : ℝ) + x ^ 2 ≤ (1 + 1 / ε ^ 2) * x ^ 2 := by
    have h1 : (1 : ℝ) ≤ x ^ 2 / ε ^ 2 := by
      rw [le_div_iff₀ hε2]; nlinarith
    have h2 : x ^ 2 / ε ^ 2 = (1 / ε ^ 2) * x ^ 2 := by ring
    nlinarith
  unfold levyIntensityDensity
  rw [← one_div, div_mul_div_comm, mul_one,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, hpi]

lemma integrableOn_levyIntensityDensity_truncSet {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn levyIntensityDensity (truncSet ε) volume := by
  have hg : Integrable
      (fun x : ℝ => ((1 + 1 / ε ^ 2) / (2 * Real.pi ^ 2)) * (1 + x ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg.restrict
    measurable_levyIntensityDensity.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem (measurableSet_truncSet ε)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (levyIntensityDensity_nonneg x)]
  exact levyIntensityDensity_le_of_mem hε hx

lemma levyIntensity_apply {S : Set ℝ} (hS : MeasurableSet S) :
    levyIntensity S = ∫⁻ x in S, ENNReal.ofReal (levyIntensityDensity x) :=
  withDensity_apply _ hS

/-- `Λ{|x| > ε} < ∞`. -/
lemma levyIntensity_truncSet_ne_top {ε : ℝ} (hε : 0 < ε) :
    levyIntensity (truncSet ε) ≠ ⊤ := by
  have hfin := (integrableOn_levyIntensityDensity_truncSet hε).2
  rw [levyIntensity_apply (measurableSet_truncSet ε)]
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hfin)
  refine setLIntegral_congr_fun (measurableSet_truncSet ε) fun x _ => ?_
  exact (Real.enorm_eq_ofReal (levyIntensityDensity_nonneg x)).symm

/-- `Λ{|x| > ε} > 0`. -/
lemma levyIntensity_truncSet_ne_zero {ε : ℝ} (hε : 0 < ε) :
    levyIntensity (truncSet ε) ≠ 0 := by
  have hsub : Ioo ε (ε + 1) ⊆ truncSet ε := by
    intro x hx
    have h1 : ε < x := hx.1
    have h2 : (0 : ℝ) < x := lt_trans hε h1
    simpa [truncSet, abs_of_pos h2] using h1
  have hmono : levyIntensity (Ioo ε (ε + 1)) ≤ levyIntensity (truncSet ε) :=
    measure_mono hsub
  have hlow : ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * (ε + 1) ^ 2))
      ≤ levyIntensity (Ioo ε (ε + 1)) := by
    rw [levyIntensity_apply measurableSet_Ioo]
    have hbound : ∀ x ∈ Ioo ε (ε + 1),
        ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * (ε + 1) ^ 2))
          ≤ ENNReal.ofReal (levyIntensityDensity x) := by
      intro x hx
      have h2 : (0 : ℝ) < x := lt_trans hε hx.1
      have hle : x ^ 2 ≤ (ε + 1) ^ 2 := by nlinarith [hx.2, h2]
      refine ENNReal.ofReal_le_ofReal ?_
      unfold levyIntensityDensity
      have hden : (0 : ℝ) < 2 * Real.pi ^ 2 * x ^ 2 := by positivity
      have hden2 : (0 : ℝ) < 2 * Real.pi ^ 2 * (ε + 1) ^ 2 := by positivity
      rw [div_le_div_iff₀ hden2 hden]
      nlinarith [Real.pi_pos, hle]
    calc ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * (ε + 1) ^ 2))
        = ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * (ε + 1) ^ 2))
            * volume (Ioo ε (ε + 1)) := by
          rw [Real.volume_Ioo]
          simp
      _ = ∫⁻ _ in Ioo ε (ε + 1), ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * (ε + 1) ^ 2)) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in Ioo ε (ε + 1), ENNReal.ofReal (levyIntensityDensity x) :=
          setLIntegral_mono' measurableSet_Ioo hbound
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * (ε + 1) ^ 2)) := by
    rw [ENNReal.ofReal_pos]
    have : (0 : ℝ) < 2 * Real.pi ^ 2 * (ε + 1) ^ 2 := by positivity
    positivity
  exact ne_of_gt (lt_of_lt_of_le hpos (le_trans hlow hmono))

/-- **The limit law of Proposition 5.1 is exhibited (proved).**  For `ε > 0`
there is a rate `r = Λ{|x| > ε}` and a jump distribution `ν` with
`r · ν = Λ|_{{|x| > ε}}`, the data of the compound-Poisson law that the
large jumps converge to. -/
theorem exists_levy_truncation_data {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity (truncSet ε) ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (truncSet ε) := by
  set S := truncSet ε with hS
  have htop : levyIntensity S ≠ ⊤ := levyIntensity_truncSet_ne_top hε
  have hzero : levyIntensity S ≠ 0 := levyIntensity_truncSet_ne_zero hε
  refine ⟨(levyIntensity S).toNNReal, ?_⟩
  have hrate : ((levyIntensity S).toNNReal : ℝ≥0∞) = levyIntensity S :=
    ENNReal.coe_toNNReal htop
  have hr0 : ((levyIntensity S).toNNReal : ℝ≥0∞) ≠ 0 := by rw [hrate]; exact hzero
  have hrtop : ((levyIntensity S).toNNReal : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hprob : IsProbabilityMeasure
      ((((levyIntensity S).toNNReal : ℝ≥0∞))⁻¹ • levyIntensity.restrict S) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, ← hrate]
    exact ENNReal.inv_mul_cancel hr0 hrtop
  refine ⟨⟨(((levyIntensity S).toNNReal : ℝ≥0∞))⁻¹ • levyIntensity.restrict S, hprob⟩,
    hrate, ?_⟩
  show ((levyIntensity S).toNNReal : ℝ≥0∞) •
      ((((levyIntensity S).toNNReal : ℝ≥0∞))⁻¹ • levyIntensity.restrict S)
      = levyIntensity.restrict S
  rw [smul_smul, ENNReal.mul_inv_cancel hr0 hrtop, one_smul]

/-! ## Part C, Proposition 5.1, in counting form, for the counts of `Ξ_n` -/

/-- **Proposition 5.1, counting form, stated for `Ξ_n` (proved from the §4
input alone).**  If `νs n` is the law of the count `Ξ_n(B)` of the point
process, and `r = Λ(B)`, then `νs ⇒ Poisson(r)`.

All three hypotheses are used: `hK` and `hlaw` through `xiMeasure_apply` (they
are what make `νs` the law of the counts of `Ξ_n`) and `hrate` to identify the
parameter.  This is `LevyExponent.poisson_count_limit_of_tuple`, i.e. Wang's
factorial-moment criterion fed by display (38); it is **not**
`CauchyLaw.poisson_count_limit`, whose corresponding hypotheses are inert. -/
theorem xi_count_poisson_limit (c : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (νs : ℕ → ProbabilityMeasure ℕ) (r : ℝ≥0) (K : ℕ → ℝ → ℕ)
    (hK : ∀ n α, (K n α : ℝ≥0∞) = xiMeasure c α n B)
    (hlaw : ∀ n, (νs n : Measure ℕ) = unifIoo.map (K n))
    (hrate : (r : ℝ) = (levyIntensity B).toReal) :
    Tendsto νs atTop
      (𝓝 (Erdos1002.FactorialMomentMethod.poissonProbabilityMeasure r)) := by
  refine LevyExponent.poisson_count_limit_of_tuple c B hB hB0 hBbd νs r ?_ hrate
  intro n
  have hfun : K n = fun α => pointCount c α n B := by
    funext α
    have h := hK n α
    rw [xiMeasure_apply c α n hB] at h
    exact_mod_cast h
  rw [hlaw n, countLaw, hfun]

/-! ## Part D, Target 1: display (38) -/

/-- **Target 1.**  `Kwon1002.factorialMoment_convergence` (`CauchyLaw.lean`
line 484), reproduced token-identically (diffed against the source).

Proved from `LevyExponent.factorialMoment_eq_tupleSum` (Wang's
factorial-moment expansion applied to the events `{j ∈ J_n, X_{n,j} ∈ B}`,
itself proved) and the single sorried §4 input
`LevyExponent.tuple_measure_convergence` (displays (39)-(40)). -/
theorem factorialMoment_convergence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (νs : ℕ → ProbabilityMeasure ℕ) (_hlaw : ∀ n, (νs n : Measure ℕ) = countLaw c n B)
    (k : ℕ) :
    Tendsto (fun n => Erdos1002.FactorialMomentMethod.factorialMoment (νs n) k)
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  have h : (fun n => Erdos1002.FactorialMomentMethod.factorialMoment (νs n) k)
      = fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
          unifIoo.real (Erdos1002.tupleEvent (LevyExponent.bulkMarkEvent c n B) f) := by
    funext n
    exact LevyExponent.factorialMoment_eq_tupleSum c _hB νs _hlaw n k
  rw [h]
  exact LevyExponent.tuple_measure_convergence c B _hB _hB0 _hBbd k

/-- The `k = 0` case of the §4 input, **proved unconditionally**: the empty
tuple contributes exactly `1 = Λ(B)^0`.  (Recorded because it is the base of
display (39) and needs none of Proposition 4.1.) -/
theorem tuple_measure_convergence_zero (c : ℝ) (B : Set ℝ) :
    Tendsto (fun n : ℕ => ∑ f : Fin 0 ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (LevyExponent.bulkMarkEvent c n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ 0)) := by
  classical
  have h : ∀ n : ℕ, (∑ f : Fin 0 ↪ (Finset.range (n + 1) : Finset ℕ),
      unifIoo.real (Erdos1002.tupleEvent (LevyExponent.bulkMarkEvent c n B) f)) = 1 := by
    intro n
    have hterm : ∀ f : Fin 0 ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (LevyExponent.bulkMarkEvent c n B) f) = 1 := by
      intro f
      have huniv : Erdos1002.tupleEvent (LevyExponent.bulkMarkEvent c n B) f
          = (univ : Set ℝ) := by
        simp [Erdos1002.tupleEvent]
      rw [huniv, Measure.real, measure_univ, ENNReal.toReal_one]
    rw [Finset.sum_congr rfl fun f _ => hterm f, Finset.sum_const, Finset.card_univ,
      Erdos1002.card_orderedDistinctTuples]
    simp
  simp only [h, pow_zero]
  exact tendsto_const_nhds

/-! ## Part E, Target 2: Proposition 5.1 + continuous mapping -/

/-- **THE ONE SORRIED INPUT, display (37) plus the continuous mapping
theorem, in point-process currency.**

If `μs n` is the law of `∫_{|x| > ε} x dΞ_n`, the large-jump functional of
the manuscript's point process, and `(r, ν)` is the truncated Lévy data
(`r = Λ{|x|>ε}`, `r · ν = Λ|_{{|x|>ε}}`), then `μs ⇒ CP(r, ν)`.

**Obstruction.**  This is the sentence "Proposition 5.1 and the continuous
mapping theorem give convergence of the large-jump part" in the proof of
Cor. 5.3, with the tails `|x| > R` removed first by `sup_n E Ξ_n{|x|>R} ≤
C/R` and with `Λ{|x| = ε} = 0`.  Formalizing it requires (i) the vague
topology on Radon point measures on `ℝ \ {0}` in which (37) is stated, no
substrate module supplies it, and (ii) the *joint* Poisson limit for the
counts on finitely many disjoint continuity sets, which is what upgrades the
one-dimensional criterion of `Erdos1002.PoissonFactorialConvergence` (used in
`xi_count_poisson_limit` above) to the point-process statement.  The
substrate has no multivariate Poisson module.

Note what is **not** assumed: the limit object is not quantified over, `r`
and `ν` are produced by `exists_levy_truncation_data`, and `CP` is Wang's
compound-Poisson law. -/
theorem xi_largeIntegral_weak_limit (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1)
    (r : ℝ≥0) (ν : ProbabilityMeasure ℝ)
    (_hrate : (r : ℝ≥0∞) = levyIntensity (truncSet ε))
    (_hjump : (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (truncSet ε))
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n))) :
    Tendsto μs atTop (𝓝 (Erdos1002.continuousCompoundPoissonProbability r ν)) := by
  sorry

/-- The large-jump law *is* the law of the point-process functional
`∫_{|x|>ε} x dΞ_n` (proved). -/
lemma largeProb_eq_xi_law (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (largeProb c ε n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n)) := by
  show unifIoo.map (fun α => largeSum c ε α n)
      = unifIoo.map (fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n))
  have hfun : (fun α => largeSum c ε α n)
      = fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n) :=
    funext fun α => largeSum_eq_xi_setIntegral c ε hε α n
  rw [hfun]

/-- **Target 2, with the limit identified.**  For fixed `ε` the large-jump
laws converge to the compound-Poisson law with Lévy measure `Λ|_{{|x|>ε}}`. -/
theorem largeJump_tendsto_compoundPoisson (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity (truncSet ε) ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (truncSet ε) ∧
      Tendsto (fun n => largeProb c ε n) atTop
        (𝓝 (Erdos1002.continuousCompoundPoissonProbability r ν)) := by
  obtain ⟨r, ν, hrate, hjump⟩ := exists_levy_truncation_data hε0
  exact ⟨r, ν, hrate, hjump,
    xi_largeIntegral_weak_limit c ε hε0 hε1 r ν hrate hjump (fun n => largeProb c ε n)
      (fun n => largeProb_eq_xi_law c ε hε0.le n)⟩

/-- **Target 2.**  `Kwon1002.Assembly5.largeJump_weak_limit` (`Assembly5.lean`
line 344), reproduced token-identically (diffed against the source). -/
theorem largeJump_weak_limit (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) := by
  obtain ⟨r, ν, _, _, hconv⟩ := largeJump_tendsto_compoundPoisson c ε _hε0 _hε1
  exact ⟨Erdos1002.continuousCompoundPoissonProbability r ν, hconv⟩

/-- **Bonus: the sorried input of `Kwon1002.CompoundCauchy` (line 254),
reproduced token-identically and discharged here.**  Any weak limit `ρ` of
the large-jump laws *is* the compound-Poisson law with Lévy measure
`Λ|_{{|x|>ε}}`, by uniqueness of limits in the (Hausdorff) topology of
convergence in distribution.  So the `ε ↓ 0` analysis of `CompoundCauchy`
consumes exactly `xi_largeIntegral_weak_limit` and nothing more. -/
theorem largeJump_limit_compoundPoisson (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ρ : ProbabilityMeasure ℝ)
    (hρ : Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ)) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity {x : ℝ | ε < |x|} ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict {x : ℝ | ε < |x|} ∧
      (ρ : Measure ℝ) = Erdos1002.continuousCompoundPoissonMeasure r ν := by
  obtain ⟨r, ν, hrate, hjump, hconv⟩ := largeJump_tendsto_compoundPoisson c ε hε0 hε1
  have huniq : ρ = Erdos1002.continuousCompoundPoissonProbability r ν :=
    tendsto_nhds_unique hρ hconv
  exact ⟨r, ν, hrate, hjump,
    by rw [huniq, Erdos1002.continuousCompoundPoissonProbability_toMeasure]⟩

end

end PoissonRoute

end Kwon1002

