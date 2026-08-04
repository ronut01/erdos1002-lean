import Kwon1002.PoissonLimit
import Kwon1002.SmallJumps
import Erdos1002.LevyContinuity
import Erdos1002.ContinuousCompoundPoisson
import Erdos1002.PoissonFactorialConvergence

/-!
# C53, Corollary 5.3 (principal Cauchy law): decomposition

Working file for the reduction of `Kwon1002.principal_cauchy_law`
(Kwon, Cor. 5.3, display (43)) to the §5 analytic inputs.

Part A of this file is unconditional: the limit law is built as an honest
probability measure on `ℝ` and its distribution function is *computed* and
shown to be exactly `cauchyLimitCDF`, i.e. the scale `1/(2π)` is verified
inside Lean, not assumed.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal Real

namespace Kwon1002

noncomputable section

/-! ## A. The limit law `Cauchy(0, 1/(2π))` as a measure

The Cauchy law is not in mathlib, so it is constructed here as the push-forward
of the uniform law on the arc `(-π/2, π/2)` under `θ ↦ γ tan θ`.  This makes
`IsProbabilityMeasure` free and turns the distribution function into a
computation with `arctan` rather than an improper integral. -/

/-- Uniform probability measure on the arc `(-π/2, π/2)`. -/
def arcMeasure : Measure ℝ :=
  (ENNReal.ofReal Real.pi)⁻¹ • volume.restrict (Ioo (-(Real.pi / 2)) (Real.pi / 2))

lemma volume_arc :
    volume (Ioo (-(Real.pi / 2)) (Real.pi / 2)) = ENNReal.ofReal Real.pi := by
  rw [Real.volume_Ioo]
  congr 1
  ring

lemma ofReal_pi_ne_zero : ENNReal.ofReal Real.pi ≠ 0 :=
  (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'

instance arcMeasure.isProbabilityMeasure : IsProbabilityMeasure arcMeasure := by
  constructor
  rw [arcMeasure, Measure.smul_apply, Measure.restrict_apply_univ, volume_arc, smul_eq_mul]
  exact ENNReal.inv_mul_cancel ofReal_pi_ne_zero ENNReal.ofReal_ne_top

lemma measurable_tan : Measurable Real.tan := by
  have h : Real.tan = fun x => Real.sin x / Real.cos x := by
    funext x; rw [Real.tan_eq_sin_div_cos]
  rw [h]
  exact Real.measurable_sin.div Real.measurable_cos

lemma measurable_gammaTan (γ : ℝ) : Measurable (fun θ : ℝ => γ * Real.tan θ) :=
  measurable_tan.const_mul γ

/-- The centered Cauchy law of scale `γ`. -/
def cauchyMeasure (γ : ℝ) : Measure ℝ := arcMeasure.map (fun θ => γ * Real.tan θ)

instance cauchyMeasure.isProbabilityMeasure (γ : ℝ) :
    IsProbabilityMeasure (cauchyMeasure γ) :=
  Measure.isProbabilityMeasure_map (measurable_gammaTan γ).aemeasurable

/-- The arc-slice of a lower half-line under `θ ↦ γ tan θ` is an interval. -/
lemma cauchy_preimage_Iic {γ : ℝ} (hγ : 0 < γ) (x : ℝ) :
    ((fun θ : ℝ => γ * Real.tan θ) ⁻¹' (Iic x)) ∩ Ioo (-(Real.pi / 2)) (Real.pi / 2)
      = Ioc (-(Real.pi / 2)) (Real.arctan (x / γ)) := by
  have hcancel : γ * (x / γ) = x := by field_simp
  ext θ
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, mem_Ioc]
  constructor
  · rintro ⟨hle, h1, h2⟩
    refine ⟨h1, ?_⟩
    have htan : Real.tan θ ≤ x / γ := by
      rw [le_div_iff₀ hγ, mul_comm]
      exact hle
    calc θ = Real.arctan (Real.tan θ) := (Real.arctan_tan h1 h2).symm
      _ ≤ Real.arctan (x / γ) := Real.arctan_mono htan
  · rintro ⟨h1, h2⟩
    have hlt : Real.arctan (x / γ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have h2' : θ < Real.pi / 2 := lt_of_le_of_lt h2 hlt
    have htan : Real.tan θ ≤ x / γ := by
      rw [← Real.arctan_le_arctan_iff, Real.arctan_tan h1 h2']
      exact h2
    refine ⟨?_, h1, h2'⟩
    calc γ * Real.tan θ ≤ γ * (x / γ) := by
          exact mul_le_mul_of_nonneg_left htan hγ.le
      _ = x := hcancel

/-- The distribution function of `cauchyMeasure γ`, in `ℝ≥0∞`. -/
lemma cauchyMeasure_Iic {γ : ℝ} (hγ : 0 < γ) (x : ℝ) :
    cauchyMeasure γ (Iic x)
      = (ENNReal.ofReal Real.pi)⁻¹ *
          ENNReal.ofReal (Real.arctan (x / γ) + Real.pi / 2) := by
  have hpre : MeasurableSet ((fun θ : ℝ => γ * Real.tan θ) ⁻¹' (Iic x)) :=
    (measurable_gammaTan γ) measurableSet_Iic
  rw [cauchyMeasure, Measure.map_apply (measurable_gammaTan γ) measurableSet_Iic,
    arcMeasure, Measure.smul_apply, Measure.restrict_apply hpre,
    cauchy_preimage_Iic hγ, Real.volume_Ioc, smul_eq_mul]
  congr 2
  ring

/-- The distribution function of `cauchyMeasure γ`, as a real number. -/
lemma cauchyMeasure_Iic_toReal {γ : ℝ} (hγ : 0 < γ) (x : ℝ) :
    (cauchyMeasure γ (Iic x)).toReal
      = 1 / 2 + (1 / Real.pi) * Real.arctan (x / γ) := by
  have hnn : 0 ≤ Real.arctan (x / γ) + Real.pi / 2 := by
    have := Real.neg_pi_div_two_lt_arctan (x / γ)
    linarith
  rw [cauchyMeasure_Iic hγ, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal Real.pi_pos.le, ENNReal.toReal_ofReal hnn]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Constant check.**  The distribution function of the scale-`1/(2π)`
Cauchy law built here is *exactly* `cauchyLimitCDF` from `Statement.lean`.
This is the formal verification of the constant `1/(2π)`. -/
theorem cauchyMeasure_Iic_toReal_eq_cauchyLimitCDF (x : ℝ) :
    (cauchyMeasure (1 / (2 * Real.pi)) (Iic x)).toReal = cauchyLimitCDF x := by
  have hpos : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  rw [cauchyMeasure_Iic_toReal hpos]
  unfold cauchyLimitCDF
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  congr 2
  field_simp

/-- The Cauchy law has no atoms, needed to run portmanteau at every real
threshold, so that the CDF convergence holds at *every* `x`. -/
lemma cauchyMeasure_singleton {γ : ℝ} (hγ : 0 < γ) (x : ℝ) :
    cauchyMeasure γ {x} = 0 := by
  have hpre : MeasurableSet ((fun θ : ℝ => γ * Real.tan θ) ⁻¹' ({x} : Set ℝ)) :=
    (measurable_gammaTan γ) (measurableSet_singleton x)
  have hsub :
      ((fun θ : ℝ => γ * Real.tan θ) ⁻¹' ({x} : Set ℝ)) ∩
          Ioo (-(Real.pi / 2)) (Real.pi / 2)
        ⊆ {Real.arctan (x / γ)} := by
    rintro θ ⟨hθ, h1, h2⟩
    simp only [mem_preimage, mem_singleton_iff] at hθ ⊢
    have : Real.tan θ = x / γ := by
      field_simp
      linarith [hθ]
    calc θ = Real.arctan (Real.tan θ) := (Real.arctan_tan h1 h2).symm
      _ = Real.arctan (x / γ) := by rw [this]
  rw [cauchyMeasure, Measure.map_apply (measurable_gammaTan γ) (measurableSet_singleton x),
    arcMeasure, Measure.smul_apply, Measure.restrict_apply hpre, smul_eq_mul]
  rw [measure_mono_null hsub (measure_singleton _), mul_zero]

/-- The limit law of Corollary 5.3, packaged for the weak-convergence API. -/
def cauchyProb : ProbabilityMeasure ℝ :=
  ⟨cauchyMeasure (1 / (2 * Real.pi)), inferInstance⟩

/-! ## B. The constants

Two independent routes to the scale, both computed here.

* the manuscript's: `c₀ / (2λ)` with `c₀ = 1/(12 log 2)` (display (35)) and
  `λ = π²/(12 log 2)` the Lévy constant, giving the Lévy density
  `1/(2π²)`; then the characteristic exponent multiplies by `π`.
* the referee route: `π · (1/ζ(2)) · E|V|` with `ζ(2) = π²/6` and
  `E|V| = ∫₀¹ W = 1/12`.

Both give `1/(2π)`, and `∫₀¹ W = 1/12` is proved outright below. -/

/-- `c₀` of display (35). -/
def cZero : ℝ := 1 / (12 * Real.log 2)

/-- The Lévy constant `λ = π²/(12 log 2)`. -/
def lambdaLevy : ℝ := Real.pi ^ 2 / (12 * Real.log 2)

/-- The Lévy density constant of display (37): `dΛ(x) = levyConst · |x|⁻² dx`. -/
def levyConst : ℝ := 1 / (2 * Real.pi ^ 2)

lemma log_two_ne_zero : Real.log 2 ≠ 0 := by
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact this.ne'

/-- Display (37)'s constant is `c₀/(2λ)`; the `log 2` cancels. -/
theorem levyConst_eq_cZero_div : cZero / (2 * lambdaLevy) = levyConst := by
  have h2 := log_two_ne_zero
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold cZero lambdaLevy levyConst
  field_simp

/-- The same constant in the `1/ζ(2)` form: `c₀/(2λ) = E|V| / ζ(2)`,
with `ζ(2) = π²/6` and `E|V| = 1/12`. -/
theorem levyConst_eq_zeta_form :
    cZero / (2 * lambdaLevy) = (1 / 12) / (Real.pi ^ 2 / 6) := by
  have h2 := log_two_ne_zero
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold cZero lambdaLevy
  field_simp
  ring

/-- The characteristic exponent picks up a factor `π` (from
`∫_ℝ (1 - cos u) u⁻² du = π`), and the scale comes out at exactly `1/(2π)`. -/
theorem cauchyScale_eq : Real.pi * levyConst = 1 / (2 * Real.pi) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold levyConst
  field_simp

/-- Referee route, end to end: `π · (1/ζ(2)) · E|V| = 1/(2π)`. -/
theorem cauchyScale_eq_referee_route :
    Real.pi * (1 / (Real.pi ^ 2 / 6)) * (1 / 12) = 1 / (2 * Real.pi) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `E|V| = ∫₀¹ W(θ) dθ = 1/12`, with `W(t) = {t}(1-{t})/2` the fixed-start
mark of §2.  Proved outright. -/
theorem integral_W_unit : (∫ θ in Ioo (0 : ℝ) 1, W θ) = 1 / 12 := by
  have hEq : ∀ θ ∈ Set.uIcc (0 : ℝ) 1, W θ = (θ - θ ^ 2) / 2 := by
    intro θ hθ
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
    obtain ⟨h0, h1⟩ := hθ
    rcases eq_or_lt_of_le h1 with h | h
    · subst h
      simp [W, Int.fract_one]
    · rw [W, Int.fract_eq_self.mpr ⟨h0, h⟩]
      ring
  have h1 : (∫ θ in Ioo (0 : ℝ) 1, W θ) = ∫ θ in (0 : ℝ)..1, W θ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [h1, intervalIntegral.integral_congr hEq]
  simp only [sub_div]
  rw [intervalIntegral.integral_sub]
  · simp [intervalIntegral.integral_div, integral_id, integral_pow]
    norm_num
  · exact (intervalIntegral.intervalIntegrable_id).div_const 2
  · exact ((intervalIntegral.intervalIntegrable_pow 2)).div_const 2

/-! ## C. The laws in play

`unifIoo` is the uniform law on `(0,1)`, the manuscript's `P`. -/

/-- Lebesgue measure on `(0,1)`: the probability space of the problem. -/
def unifIoo : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

instance unifIoo.isProbabilityMeasure : IsProbabilityMeasure unifIoo := by
  constructor
  rw [unifIoo, Measure.restrict_apply_univ, Real.volume_Ioo]
  simp

/-- The law of the centered bulk sum `L⁻¹ ∑_{j ∈ J_n} (-1)^j Z_{n,j} - b n`. -/
def bulkLaw (c : ℝ) (b : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  unifIoo.map (fun α => bulkSum c α n - b n)

/-! ### Measurability of the bulk sum

Not §5 mathematics, but needed for the bulk sum to *have* a law at all.
Everything in sight is built from `Int.fract`, `Int.floor` and iterates of the
Gauss map; the only real step is the stopping time, whose level sets are
described through `Nat.sInf`. -/

lemma measurable_gaussMap : Measurable gaussMap := by
  unfold gaussMap
  exact measurable_id.inv.fract


lemma measurable_digit (j : ℕ) : Measurable (fun α : ℝ => digit α j) := by
  unfold digit
  exact (measurable_of_countable Int.toNat).comp ((measurable_gaussIter j).inv.floor)

lemma measurable_natCastReal : Measurable (fun m : ℕ => (m : ℝ)) :=
  measurable_of_countable _



lemma measurable_signedMark (n j : ℕ) :
    Measurable (fun α : ℝ => signedMark α n j) := by
  unfold signedMark
  exact (measurable_const.mul (measurable_mark n j)).div_const _


lemma measurableSet_heightSeq_zero (n j : ℕ) :
    MeasurableSet {α : ℝ | heightSeq α n j = 0} :=
  (measurable_heightSeq n j) (measurableSet_singleton 0)


lemma measurable_bulkPartial (c : ℝ) (n M : ℕ) :
    Measurable (fun α : ℝ => ∑ j ∈ Finset.range M,
      if j ∈ bulkIndices c α n then signedMark α n j else 0) :=
  Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_mem_bulkIndices c n j)
      (measurable_signedMark n j) measurable_const

/-- Measurability of the bulk sum in `α`: proved. -/
theorem measurable_bulkSum (c : ℝ) (n : ℕ) :
    Measurable (fun α : ℝ => bulkSum c α n) := by
  refine measurable_of_tendsto_metrizable
    (f := fun M α => ∑ j ∈ Finset.range M,
      if j ∈ bulkIndices c α n then signedMark α n j else 0)
    (fun M => measurable_bulkPartial c n M) ?_
  rw [tendsto_pi_nhds]
  intro α
  refine tendsto_atTop_of_eventually_const (i₀ := stoppingTime α n) ?_
  intro M hM
  have hsub : bulkIndices c α n ⊆ Finset.range M := by
    intro i hi
    have h1 : i ∈ Finset.range (stoppingTime α n) := Finset.filter_subset _ _ hi
    simp only [Finset.mem_range] at h1 ⊢
    omega
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  rfl

/-- The distribution function of `bulkLaw` is literally the Lebesgue measure
appearing in the statement of `principal_cauchy_law`. -/
lemma bulkLaw_Iic (c : ℝ) (b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    bulkLaw c b n (Iic x)
      = volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x} := by
  have hm : Measurable (fun α : ℝ => bulkSum c α n - b n) :=
    (measurable_bulkSum c n).sub_const _
  rw [bulkLaw, Measure.map_apply hm measurableSet_Iic, unifIoo,
    Measure.restrict_apply (hm measurableSet_Iic)]
  congr 1
  ext α
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_setOf_eq]
  tauto

/-! ## D. Corollary 5.3 reduced to weak convergence, and to characteristic
functions

Both steps below are *proved*: portmanteau plus the atomlessness of the limit
gives convergence of the distribution functions at every real threshold, and
Wang's Lévy continuity theorem supplies weak convergence from characteristic
functions. -/

/-- Step 1 (proved): weak convergence to `Cauchy(0,1/(2π))` gives exactly the
conclusion of `principal_cauchy_law`.  Every `x` is a continuity point because
the Cauchy law has no atoms. -/
theorem cdf_tendsto_of_weak_convergence
    (c : ℝ) (b : ℕ → ℝ) (μs : ℕ → ProbabilityMeasure ℝ)
    (hlaw : ∀ n, (μs n : Measure ℝ) = bulkLaw c b n)
    (hweak : Tendsto μs atTop (𝓝 cauchyProb)) (x : ℝ) :
    Tendsto (fun n : ℕ =>
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
      atTop (𝓝 (cauchyLimitCDF x)) := by
  have hfront : (cauchyProb : Measure ℝ) (frontier (Iic x)) = 0 := by
    rw [frontier_Iic]
    exact cauchyMeasure_singleton (by positivity) x
  have key :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (μs_lim := hweak) (E := Iic x) hfront
  have key2 :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (cauchyProb : Measure ℝ) (Iic x))).comp key
  have hfun : (fun n : ℕ => ((μs n : Measure ℝ) (Iic x)).toReal)
      = fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal := by
    funext n
    rw [hlaw n, bulkLaw_Iic c b n x]
  have hlim : ((cauchyProb : Measure ℝ) (Iic x)).toReal = cauchyLimitCDF x :=
    cauchyMeasure_Iic_toReal_eq_cauchyLimitCDF x
  rw [← hfun, ← hlim]
  simpa only [Function.comp_def] using key2

/-- Step 2 (proved): pointwise convergence of characteristic functions to that
of `Cauchy(0,1/(2π))` gives the conclusion of `principal_cauchy_law`. -/
theorem principal_cauchy_law_of_charFun
    (c : ℝ) (b : ℕ → ℝ) (μs : ℕ → ProbabilityMeasure ℝ)
    (hlaw : ∀ n, (μs n : Measure ℝ) = bulkLaw c b n)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop
        (𝓝 (charFun (cauchyProb : Measure ℝ) t))) (x : ℝ) :
    Tendsto (fun n : ℕ =>
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
      atTop (𝓝 (cauchyLimitCDF x)) :=
  cdf_tendsto_of_weak_convergence c b μs hlaw
    (Erdos1002.levy_continuity_real μs cauchyProb hchar) x

/-! ### The ε-splitting of the manuscript's proof of Cor 5.3

The proof of (43) is a double limit: for each fixed `ε` the large-jump part
converges (Prop 5.1 + continuous mapping), the small-jump part is uniformly
`O(ε)` after centering (Lem 5.2), and the compound-Poisson limits converge as
`ε ↓ 0` to the Cauchy law.  The following ε/3 argument is the exact shape of
that reasoning, and it is proved. -/

/-- A double-limit interchange: if `f k n → g k` in `n` for each `k`,
`g k → L`, and `F` is uniformly approximated by `f k` for large `k`, then
`F n → L`. -/
lemma tendsto_of_eventually_uniform_approx
    {F : ℕ → ℂ} {f : ℕ → ℕ → ℂ} {g : ℕ → ℂ} {L : ℂ}
    (hf : ∀ k, Tendsto (f k) atTop (𝓝 (g k)))
    (hg : Tendsto g atTop (𝓝 L))
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᶠ n in atTop, ‖F n - f k n‖ ≤ ε) :
    Tendsto F atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨k, hk1, hk2⟩ :=
    ((happrox (ε / 3) h3).and (Metric.tendsto_nhds.mp hg (ε / 3) h3)).exists
  filter_upwards [hk1, Metric.tendsto_nhds.mp (hf k) (ε / 3) h3] with n hn1 hn2
  have hd1 : dist (F n) (f k n) ≤ ε / 3 := by rwa [dist_eq_norm]
  calc dist (F n) L
      ≤ dist (F n) (f k n) + dist (f k n) (g k) + dist (g k) L :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- **Corollary 5.3, reduced.**  The principal Cauchy law follows from the
three §5 inputs, in the exact form the manuscript uses them.  `k` indexes the
truncation level `ε = ε_k ↓ 0`; `approx k n` is the law of the `ε_k`-large-jump
part of the centered bulk sum and `compound k` its compound-Poisson limit.

This theorem is proved: it is the whole architecture of the proof of (43),
with the three analytic inputs as hypotheses. -/
theorem principal_cauchy_law_reduction
    (c : ℝ) (b : ℕ → ℝ) (μs : ℕ → ProbabilityMeasure ℝ)
    (approx : ℕ → ℕ → ProbabilityMeasure ℝ) (compound : ℕ → ProbabilityMeasure ℝ)
    (hlaw : ∀ n, (μs n : Measure ℝ) = bulkLaw c b n)
    -- (I) Prop 5.1 + continuous mapping: for fixed `ε`, the large jumps converge
    (hlarge : ∀ k t, Tendsto (fun n => charFun (approx k n : Measure ℝ) t) atTop
      (𝓝 (charFun (compound k : Measure ℝ) t)))
    -- (II) Lem 5.2 + the centering `b_{n,ε}`: small jumps are uniformly negligible
    (hsmall : ∀ t : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      ‖charFun (μs n : Measure ℝ) t - charFun (approx k n : Measure ℝ) t‖ ≤ ε)
    -- (III) the compound-Poisson exponents converge to the Cauchy exponent
    (hcompound : ∀ t, Tendsto (fun k => charFun (compound k : Measure ℝ) t) atTop
      (𝓝 (charFun (cauchyProb : Measure ℝ) t))) (x : ℝ) :
    Tendsto (fun n : ℕ =>
        (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
      atTop (𝓝 (cauchyLimitCDF x)) :=
  principal_cauchy_law_of_charFun c b μs hlaw
    (fun t => tendsto_of_eventually_uniform_approx
      (fun k => hlarge k t) (hcompound t) (hsmall t)) x

/-! ## E. Proposition 5.1 against Wang's factorial-moment interface

`Ξ_n` of (36) is a finite point process; the only thing Cor 5.3 consumes is
that its counts converge to Poisson counts.  Wang's
`tendsto_poisson_of_factorialMoments` takes exactly the manuscript's input
(display (38)) and produces exactly that. -/

section Counts

local instance c53PropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- `N_n(B)`, the number of points of `Ξ_n` in `B`. -/
def pointCount (c α : ℝ) (n : ℕ) (B : Set ℝ) : ℕ :=
  ∑ j ∈ bulkIndices c α n, if signedMark α n j ∈ B then 1 else 0

/-- The law of the count `N_n(B)` under the uniform measure on `(0,1)`. -/
def countLaw (c : ℝ) (n : ℕ) (B : Set ℝ) : Measure ℕ :=
  unifIoo.map (fun α => pointCount c α n B)

/-- The intensity density of display (37): `dΛ(x) = |x|⁻² dx / (2π²)`.
At `x = 0` Lean's total division returns `0`, which is the correct convention
on `ℝ \ {0}` and makes the definition harmless at the excluded point. -/
def levyIntensityDensity (x : ℝ) : ℝ := 1 / (2 * Real.pi ^ 2 * x ^ 2)

/-- The Lévy intensity `Λ` of display (37). -/
def levyIntensity : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (levyIntensityDensity x))

/-- **Proposition 5.1, counting form** (proved, given the factorial-moment
input): the counts of `Ξ_n` on a set `B` converge in law to `Poisson(Λ(B))`.

This is a thin wrapper, and that is the point: the manuscript's display (38)
is precisely the hypothesis `hFac` of Wang's theorem, so no new limit theory
is needed on top of the substrate. -/
theorem poisson_count_limit (c : ℝ) (B : Set ℝ)
    (νs : ℕ → ProbabilityMeasure ℕ) (r : ℝ≥0)
    (_hlaw : ∀ n, (νs n : Measure ℕ) = countLaw c n B)
    (_hrate : (r : ℝ) = (levyIntensity B).toReal)
    (hInt : ∀ n k, Integrable (fun m : ℕ => (m.descFactorial k : ℝ)) (νs n : Measure ℕ))
    (hFac : ∀ k, Tendsto
      (fun n => Erdos1002.FactorialMomentMethod.factorialMoment (νs n) k) atTop
      (𝓝 ((r : ℝ) ^ k))) :
    Tendsto νs atTop
      (𝓝 (Erdos1002.FactorialMomentMethod.poissonProbabilityMeasure r)) :=
  Erdos1002.FactorialMomentMethod.tendsto_poisson_of_factorialMoments νs r hInt hFac

/-- **Display (38)**, the ordered factorial-moment computation, the analytic
heart of Prop 5.1.

Remaining obstruction: this is the full §4 quasi-independence input (Prop 4.1)
plus the tuple bookkeeping of (39), Jackson approximation of `φ ∘ mark`, the
`a ≤ L^D` digit cut, the `O(L^{r-1}H)` bad-tuple count and the parity/ordering
partition.  Nothing in the substrate states it; `GaussFactorialTupleReplacement`
and `RareEventMixing` are the substrate modules that would feed it. -/
theorem factorialMoment_convergence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (νs : ℕ → ProbabilityMeasure ℕ) (_hlaw : ∀ n, (νs n : Measure ℕ) = countLaw c n B)
    (k : ℕ) :
    Tendsto (fun n => Erdos1002.FactorialMomentMethod.factorialMoment (νs n) k)
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  sorry

end Counts

/-! ## F. The three remaining analytic inputs, stated precisely -/

/-- The one classical integral the constant rests on: `∫_ℝ (1-cos u) u⁻² du = π`.
Not in mathlib and not in the substrate. -/
theorem integral_one_sub_cos_div_sq :
    (∫ u : ℝ, (1 - Real.cos u) / u ^ 2) = Real.pi := by
  sorry

/-- **Input (III), raw form.**  The compensated large-jump exponent of the
manuscript's proof of (43): as `ε ↓ 0`,
`∫_{|x|>ε} (cos(tx) - 1) dΛ(x) → -(π · levyConst · |t|)`.

The `π` is `∫_ℝ (1-cos u) u⁻² du` (above) and `levyConst = 1/(2π²)` is the
density constant of display (37); the substitution `u = tx` and the symmetric
truncation are the only remaining analytic steps.  Note the *constant is not
assumed here*: it is carried as `π · levyConst` and evaluated in the corollary
below by `cauchyScale_eq`, which is proved. -/
theorem levy_exponent_limit_raw (t : ℝ) :
    Tendsto (fun k : ℕ =>
        ∫ x in {x : ℝ | 1 / (k + 1 : ℝ) < |x|},
          (Real.cos (t * x) - 1) * levyIntensityDensity x)
      atTop (𝓝 (-(Real.pi * levyConst * |t|))) := by
  sorry

/-- **The constant, evaluated (proved from `levy_exponent_limit_raw`).**  The
limiting characteristic exponent is `-|t|/(2π)`, i.e. the limit law is Cauchy
of scale exactly `1/(2π)`, matching `cauchyLimitCDF`. -/
theorem levy_exponent_limit (t : ℝ) :
    Tendsto (fun k : ℕ =>
        ∫ x in {x : ℝ | 1 / (k + 1 : ℝ) < |x|},
          (Real.cos (t * x) - 1) * levyIntensityDensity x)
      atTop (𝓝 (-(|t| / (2 * Real.pi)))) := by
  have h : Real.pi * levyConst * |t| = |t| / (2 * Real.pi) := by
    rw [cauchyScale_eq]; ring
  rw [← h]
  exact levy_exponent_limit_raw t

/-- The characteristic function of the constructed Cauchy law.  Classical
(Fourier transform of the Poisson kernel); not in mathlib, and not implied by
anything in the substrate. -/
theorem charFun_cauchyProb (t : ℝ) :
    charFun (cauchyProb : Measure ℝ) t
      = (Real.exp (-(|t| / (2 * Real.pi))) : ℂ) := by
  sorry

/-- Input (III) of `principal_cauchy_law_reduction`, made concrete against
Wang's compound-Poisson law: once the compound-Poisson *exponents*
`r_k (φ_k(t) - 1)` converge to the Lévy exponent `-|t|/(2π)`, the
characteristic functions converge to that of `Cauchy(0,1/(2π))`.

Proved, using `Erdos1002.charFun_continuousCompoundPoissonProbability`. -/
theorem tendsto_charFun_compound_of_exponent
    (rates : ℕ → ℝ≥0) (jumps : ℕ → ProbabilityMeasure ℝ) (t : ℝ)
    (hexp : Tendsto
      (fun k => (rates k : ℂ) * (charFun (jumps k : Measure ℝ) t - 1)) atTop
      (𝓝 (((-(|t| / (2 * Real.pi))) : ℝ) : ℂ))) :
    Tendsto (fun k => charFun
        (Erdos1002.continuousCompoundPoissonProbability (rates k) (jumps k) : Measure ℝ) t)
      atTop (𝓝 (charFun (cauchyProb : Measure ℝ) t)) := by
  have hE : Tendsto
      (fun k => Complex.exp ((rates k : ℂ) * (charFun (jumps k : Measure ℝ) t - 1)))
      atTop (𝓝 (Complex.exp (((-(|t| / (2 * Real.pi))) : ℝ) : ℂ))) := by
    simpa only [Function.comp_def] using (Complex.continuous_exp.tendsto _).comp hexp
  have hval : Complex.exp (((-(|t| / (2 * Real.pi))) : ℝ) : ℂ)
      = charFun (cauchyProb : Measure ℝ) t := by
    rw [charFun_cauchyProb t]
    exact (Complex.ofReal_exp _).symm
  rw [← hval]
  simpa only [Erdos1002.charFun_continuousCompoundPoissonProbability] using hE

/-! ## G. The target statement, reduced

`principal_cauchy_law` in `PoissonLimit.lean` asks for deterministic centerings
`b n` making the centered bulk sum converge to `Cauchy(0,1/(2π))`.  The
following theorem closes that target from a *single* hypothesis: the existence
of a centering for which the characteristic functions converge.  Everything
else, the limit law, its distribution function, the constant `1/(2π)`,
measurability, portmanteau, Lévy continuity, is discharged above. -/

theorem principal_cauchy_law_of_charFun_target (c : ℝ)
    (h : ∃ (b : ℕ → ℝ) (μs : ℕ → ProbabilityMeasure ℝ),
      (∀ n, (μs n : Measure ℝ) = bulkLaw c b n) ∧
      ∀ t : ℝ, Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop
        (𝓝 (charFun (cauchyProb : Measure ℝ) t))) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  obtain ⟨b, μs, hlaw, hchar⟩ := h
  exact ⟨b, fun x => principal_cauchy_law_of_charFun c b μs hlaw hchar x⟩

end

end Kwon1002
