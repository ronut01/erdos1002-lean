import Kwon1002.Assembly5
import Kwon1002.FourierPairs
import Kwon1002.LevyExponent

/-!
# Scratch (agent `cpcauchy`), `Assembly5.compound_tendsto_cauchy`

Target: `Kwon1002.Assembly5.compound_tendsto_cauchy` (Assembly5.lean ~378),
the third §5 input of Corollary 5.3: as `ε ↓ 0` the compound-Poisson limit
laws of the large-jump parts converge to `Cauchy(0, 1/(2π))`.

The statement is reproduced **token-identically** below.

## What is proved here (unconditionally)

* `integrableOn_levyIntensityDensity_trunc`, `Λ` is a finite measure off any
  neighbourhood of `0`: `∫_{|x|>ε} dx/(2π²x²) < ∞`.
* `integral_sin_mul_levyIntensityDensity_trunc`, **the imaginary part of the
  compound-Poisson exponent vanishes**: `∫_{|x|>ε} sin(tx) dΛ(x) = 0`, because
  `Λ` is symmetric.  (This is the manuscript's "symmetry kills the imaginary
  part".)
* `levyExponent_complex_eq_real`, consequently the compound-Poisson exponent
  `∫_{|x|>ε} (e^{itx} - 1) dΛ(x)` is the *real* number
  `∫_{|x|>ε} (cos(tx) - 1) dΛ(x)`.
* `tendsto_levyExponent_trunc`, **the `ε ↓ 0` exponent limit along an
  arbitrary null sequence** `ε_k ↓ 0` (not just the reciprocal sequence of
  `LevyExponent.levy_exponent_limit_raw`):
  `∫_{|x|>ε_k} (cos(tx)-1) dΛ(x) → -|t|/(2π)`.  Proved by dominated
  convergence against the (proved, unconditional)
  `LevyExponent.integrable_levyIntegrand` / `LevyExponent.integral_levyIntegrand`,
  with the constant evaluated by the (proved) `Kwon1002.cauchyScale_eq`.
* `compound_tendsto_cauchy` itself, from the single input below: the exponent
  limit is fed through `FourierPairs.charFun_cauchyProb` (proved) and Wang's
  `Erdos1002.levy_continuity_real`.

* `charFun_compoundPoisson_levy`, **the compound-Poisson calculus against
  Wang's interface**: if `ρ = CP(r, ν)` with `r · ν = Λ|_{|x|>ε}` then
  `charFun ρ t = exp(∫_{|x|>ε}(e^{itx}-1) dΛ(x))`.  Proved from
  `Erdos1002.charFun_continuousCompoundPoissonProbability`; **no Wang-interface
  mismatch** was found.

## The single sorried input

`largeJump_limit_compoundPoisson`, the identification, for **fixed** `ε`, of
the weak limit `ρ` of `largeProb c ε n` as the compound-Poisson law with rate
`Λ{|x|>ε}` and jump measure `Λ|_{|x|>ε}` normalized.  It is stated at the
level of *measures*, i.e. in the currency Proposition 5.1 produces; the
characteristic-function form used by the `ε ↓ 0` argument is *derived* from it
by `charFun_compoundPoisson_levy`.

This is *exactly* the gap named in the docstring of the target ("what is
missing is the identification of `ρ k` as the compound-Poisson law with those
exponents").  It is `Assembly5.largeJump_weak_limit` / Proposition 5.1
(display (37), `Ξ_n ⇒ PRM(Λ)`) plus the continuous-mapping step for
`x ↦ ∑ x·1{|x|>ε}`, i.e. §5 content upstream of this file, *not* the `ε ↓ 0`
analysis this file is about.  Nothing else is assumed: in particular
`CauchyLaw.charFun_cauchyProb`, `CauchyLaw.integral_one_sub_cos_div_sq` and
`CauchyLaw.levy_exponent_limit_raw` (all sorried in `CauchyLaw.lean`) are
**not** used, the proved copies in `FourierPairs.lean` / `LevyExponent.lean`
are used instead.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal Real

namespace Kwon1002

namespace CompoundCauchy

open Assembly5

noncomputable section

/-! ## Part 0, the truncated Lévy measure -/

/-- The truncation set `{|x| > ε}` of display (42). -/
lemma measurableSet_trunc (ε : ℝ) : MeasurableSet {x : ℝ | ε < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

lemma measurable_levyIntensityDensity : Measurable levyIntensityDensity := by
  unfold levyIntensityDensity
  exact measurable_const.div (measurable_const.mul (measurable_id.pow_const 2))

lemma levyIntensityDensity_nonneg (x : ℝ) : 0 ≤ levyIntensityDensity x := by
  unfold levyIntensityDensity
  positivity

lemma levyIntensityDensity_neg (x : ℝ) :
    levyIntensityDensity (-x) = levyIntensityDensity x := by
  unfold levyIntensityDensity
  rw [neg_pow_two]

/-- Off a neighbourhood of the origin the Lévy density is dominated by a
multiple of the Poisson kernel `(1+x²)⁻¹`. -/
lemma levyIntensityDensity_le_of_lt_abs {ε x : ℝ} (hε : 0 < ε) (hx : ε < |x|) :
    levyIntensityDensity x ≤ ((1 / ε ^ 2 + 1) / (2 * Real.pi ^ 2)) * (1 + x ^ 2)⁻¹ := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hx2 : ε ^ 2 < x ^ 2 := by
    have h := hx
    have habs : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x]
  have hx2pos : (0 : ℝ) < x ^ 2 := lt_trans hε2 hx2
  have hone : (1 : ℝ) ≤ x ^ 2 / ε ^ 2 := by
    rw [le_div_iff₀ hε2]
    nlinarith
  have hpi : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  have hden : (0 : ℝ) < 2 * Real.pi ^ 2 * x ^ 2 := by positivity
  have hsum : (0 : ℝ) < 1 + x ^ 2 := by positivity
  unfold levyIntensityDensity
  rw [← one_div, div_mul_div_comm, mul_one, div_le_div_iff₀ hden (by positivity)]
  have key : (1 : ℝ) + x ^ 2 ≤ (1 / ε ^ 2 + 1) * x ^ 2 := by
    have : x ^ 2 / ε ^ 2 = (1 / ε ^ 2) * x ^ 2 := by ring
    nlinarith [hone]
  nlinarith [key, hpi]

/-- `Λ` is finite off `{|x| ≤ ε}`. -/
lemma integrableOn_levyIntensityDensity_trunc {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn levyIntensityDensity {x : ℝ | ε < |x|} volume := by
  have hg : Integrable
      (fun x : ℝ => ((1 / ε ^ 2 + 1) / (2 * Real.pi ^ 2)) * (1 + x ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' (hg.integrableOn (s := {x : ℝ | ε < |x|}))
    measurable_levyIntensityDensity.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem (measurableSet_trunc ε)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (levyIntensityDensity_nonneg x)]
  exact levyIntensityDensity_le_of_lt_abs hε hx

lemma integrableOn_sin_mul_levyIntensityDensity_trunc {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn (fun x : ℝ => Real.sin (t * x) * levyIntensityDensity x)
      {x : ℝ | ε < |x|} volume := by
  refine Integrable.mono' (integrableOn_levyIntensityDensity_trunc hε)
    ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).mul
      measurable_levyIntensityDensity).aestronglyMeasurable.restrict ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (levyIntensityDensity_nonneg x)]
  have h1 : |Real.sin (t * x)| ≤ 1 := Real.abs_sin_le_one _
  nlinarith [levyIntensityDensity_nonneg x, abs_nonneg (Real.sin (t * x))]

/-! ## Part 1, symmetry kills the imaginary part -/

/-- **`Λ` is symmetric**, so the imaginary part of the compound-Poisson
exponent vanishes: `∫_{|x|>ε} sin(tx) dΛ(x) = 0`. -/
lemma integral_sin_mul_levyIntensityDensity_trunc (ε t : ℝ) :
    (∫ x in {x : ℝ | ε < |x|}, Real.sin (t * x) * levyIntensityDensity x) = 0 := by
  rw [← integral_indicator (measurableSet_trunc ε)]
  refine FourierPairs.integral_eq_zero_of_odd ?_
  intro x
  simp only [Set.indicator_apply, Set.mem_setOf_eq, abs_neg]
  by_cases hx : ε < |x|
  · rw [if_pos hx, if_pos hx]
    rw [levyIntensityDensity_neg, mul_neg, Real.sin_neg, neg_mul]
  · rw [if_neg hx, if_neg hx, neg_zero]

/-- The compound-Poisson exponent `∫_{|x|>ε}(e^{itx}-1) dΛ(x)` is the real
number `∫_{|x|>ε}(cos(tx)-1) dΛ(x)`. -/
lemma levyExponent_complex_eq_real {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ x in {x : ℝ | ε < |x|},
        (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1) * (levyIntensityDensity x : ℂ))
      = (((∫ x in {x : ℝ | ε < |x|},
          (Real.cos (t * x) - 1) * levyIntensityDensity x) : ℝ) : ℂ) := by
  have hcos : IntegrableOn
      (fun x : ℝ => (Real.cos (t * x) - 1) * levyIntensityDensity x)
      {x : ℝ | ε < |x|} volume := (LevyExponent.integrable_levyIntegrand t).integrableOn
  have hsin := integrableOn_sin_mul_levyIntensityDensity_trunc hε t
  have hfun : ∀ x : ℝ,
      (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1) * (levyIntensityDensity x : ℂ)
        = (((Real.cos (t * x) - 1) * levyIntensityDensity x : ℝ) : ℂ)
          + (((Real.sin (t * x) * levyIntensityDensity x : ℝ) : ℂ)) * Complex.I := by
    intro x
    have hmul : ((t : ℂ) * (x : ℂ)) = ((t * x : ℝ) : ℂ) := by push_cast; ring
    rw [hmul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hcosC : Integrable
      (fun x : ℝ => ((((Real.cos (t * x) - 1) * levyIntensityDensity x) : ℝ) : ℂ))
      (volume.restrict {x : ℝ | ε < |x|}) := hcos.ofReal
  have hsinC : Integrable
      (fun x : ℝ => (((Real.sin (t * x) * levyIntensityDensity x) : ℝ) : ℂ))
      (volume.restrict {x : ℝ | ε < |x|}) := hsin.ofReal
  rw [setIntegral_congr_fun (measurableSet_trunc ε) (fun x _ => hfun x)]
  rw [integral_add hcosC (hsinC.mul_const Complex.I),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_sin_mul_levyIntensityDensity_trunc ε t]
  simp

/-! ## Part 2, the `ε ↓ 0` exponent limit, along an arbitrary null sequence -/

/-- **The `ε ↓ 0` limit of the compound-Poisson exponents.**  For *any*
sequence `ε_k ↓ 0` of positive truncation levels,
`∫_{|x|>ε_k}(cos(tx)-1) dΛ(x) → -|t|/(2π)`.

`LevyExponent.levy_exponent_limit_raw` is the special case `ε_k = 1/(k+1)`;
here the same conclusion is obtained for an arbitrary null sequence by
dominated convergence, since `Cor. 5.3` supplies the truncation scale
`ε_k` from the *variance* bound of Lemma 5.2 and not from a reciprocal
sequence. -/
theorem tendsto_levyExponent_trunc (t : ℝ) (e : ℕ → ℝ) (_he0 : ∀ k, 0 < e k)
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k : ℕ =>
        ∫ x in {x : ℝ | e k < |x|}, (Real.cos (t * x) - 1) * levyIntensityDensity x)
      atTop (𝓝 (-(|t| / (2 * Real.pi)))) := by
  set f : ℝ → ℝ := fun x => (Real.cos (t * x) - 1) * levyIntensityDensity x with hf
  have hint : Integrable f volume := LevyExponent.integrable_levyIntegrand t
  have hindic : ∀ k : ℕ,
      (∫ x in {x : ℝ | e k < |x|}, f x)
        = ∫ x : ℝ, Set.indicator {x : ℝ | e k < |x|} f x := fun k =>
    (integral_indicator (measurableSet_trunc (e k))).symm
  have hval : (∫ x : ℝ, f x) = -(|t| / (2 * Real.pi)) := by
    have h := LevyExponent.integral_levyIntegrand t
    rw [hf, h, cauchyScale_eq]
    ring
  simp only [hindic]
  rw [← hval]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun k => (hint.aestronglyMeasurable.indicator (measurableSet_trunc (e k))))
    hint.norm ?_ ?_
  · intro k
    filter_upwards with x
    exact norm_indicator_le_norm_self f x
  · have hae : ∀ᵐ x : ℝ, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hae] with x hx
    have hx0 : (0 : ℝ) < |x| := abs_pos.mpr hx
    have hev : (fun k : ℕ => Set.indicator {x : ℝ | e k < |x|} f x)
        =ᶠ[atTop] (fun _ : ℕ => f x) := by
      filter_upwards [he.eventually_lt_const hx0] with k hk
      exact Set.indicator_of_mem (by exact hk) f
    exact Tendsto.congr' hev.symm tendsto_const_nhds

/-! ## Part 3, the single input, and the target -/

/-- **THE ONE SORRIED INPUT, the identification of the fixed-`ε` limit law
(Proposition 5.1 + continuous mapping).**  For fixed `ε > 0` the weak limit
`ρ` of the large-jump laws `largeProb c ε n` is the compound-Poisson law
whose Lévy measure is `Λ` restricted to `{|x| > ε}`: there is a rate
`r = Λ{|x| > ε}` and a jump distribution `ν` with `r · ν = Λ|_{|x|>ε}` such
that `ρ` is Wang's compound-Poisson law `CP(r, ν)`.

**Obstruction.**  This is display (37), `Ξ_n ⇒ PRM(Λ)`, together with the
continuous-mapping step for the functional `x ↦ ∑ x·1{|x|>ε}` (legitimate
because `Λ{|x| = ε} = 0` and the tails `|x| > R` can be removed by the
uniform `C/R` bound).  In this repository it sits upstream of the present
file: `Assembly5.largeJump_weak_limit` produces the limit `ρ` but not its
identity, and Prop. 5.1 itself rests on `CauchyLaw.factorialMoment_convergence`
(display (38)) via `LevyExponent.tuple_measure_convergence`.

**No Wang-interface mismatch.**  The compound-Poisson *calculus* needed
downstream is entirely available: `charFun_compoundPoisson_levy` below turns
this measure-level identification into the exponent
`∫_{|x|>ε}(e^{itx}-1) dΛ(x)` using only Wang's
`charFun_continuousCompoundPoissonProbability`, and that is all the `ε ↓ 0`
argument consumes. -/
theorem largeJump_limit_compoundPoisson (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ρ : ProbabilityMeasure ℝ)
    (hρ : Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ)) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity {x : ℝ | ε < |x|} ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict {x : ℝ | ε < |x|} ∧
      (ρ : Measure ℝ) = Erdos1002.continuousCompoundPoissonMeasure r ν := by
  sorry

/-- **The compound-Poisson exponent (proved).**  If `ρ = CP(r, ν)` with
`r · ν = Λ|_{|x|>ε}`, then
`charFun ρ t = exp(∫_{|x|>ε}(e^{itx}-1) dΛ(x))`.

Only `hjump` is used (with `ν` a probability measure it already forces
`r = Λ{|x|>ε}`); `hrate` is carried in the statement of the input above
because it is what Prop. 5.1 actually produces. -/
theorem charFun_compoundPoisson_levy {ε : ℝ} (hε : 0 < ε) (t : ℝ)
    (ρ : ProbabilityMeasure ℝ) (r : ℝ≥0) (ν : ProbabilityMeasure ℝ)
    (hjump : (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict {x : ℝ | ε < |x|})
    (hcp : (ρ : Measure ℝ) = Erdos1002.continuousCompoundPoissonMeasure r ν) :
    charFun (ρ : Measure ℝ) t
      = Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)) := by
  have hSm : MeasurableSet {x : ℝ | ε < |x|} := measurableSet_trunc ε
  have hdens : Measurable (fun x : ℝ => ENNReal.ofReal (levyIntensityDensity x)) :=
    measurable_levyIntensityDensity.ennreal_ofReal
  -- transfer of an integral against `Λ` to an integral against Lebesgue measure
  have htransfer : ∀ φ : ℝ → ℂ, (∫ x in {x : ℝ | ε < |x|}, φ x ∂levyIntensity)
      = ∫ x in {x : ℝ | ε < |x|}, (levyIntensityDensity x : ℂ) * φ x := by
    intro φ
    rw [levyIntensity, setIntegral_withDensity_eq_setIntegral_toReal_smul hdens
      (by filter_upwards with x; exact ENNReal.ofReal_lt_top) φ hSm]
    refine setIntegral_congr_fun hSm (fun x _ => ?_)
    rw [ENNReal.toReal_ofReal (levyIntensityDensity_nonneg x), Complex.real_smul]
  -- `r · ν = Λ|_S` in the form of integrals
  have key : ∀ φ : ℝ → ℂ, ((r : ℝ) : ℂ) * (∫ x, φ x ∂(ν : Measure ℝ))
      = ∫ x in {x : ℝ | ε < |x|}, (levyIntensityDensity x : ℂ) * φ x := by
    intro φ
    have h := integral_smul_measure (μ := (ν : Measure ℝ)) φ (r : ℝ≥0∞)
    rw [hjump, htransfer φ] at h
    rw [h, ENNReal.coe_toReal, Complex.real_smul]
  -- the two instances of `key` that occur in the exponent
  have hg := key fun x => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
  have h1 := key fun _ => (1 : ℂ)
  have hν1 : (∫ _x : ℝ, (1 : ℂ) ∂(ν : Measure ℝ)) = 1 := by simp
  rw [hν1, mul_one] at h1
  -- integrability of the two pieces on the truncation set
  have hI2 : IntegrableOn (fun x : ℝ => ((levyIntensityDensity x : ℝ) : ℂ) * 1)
      {x : ℝ | ε < |x|} volume := by
    simpa using (integrableOn_levyIntensityDensity_trunc hε).ofReal (𝕜 := ℂ)
  have hI1 : IntegrableOn
      (fun x : ℝ => ((levyIntensityDensity x : ℝ) : ℂ)
        * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) {x : ℝ | ε < |x|} volume := by
    refine Integrable.mono' (integrableOn_levyIntensityDensity_trunc hε)
      (((Complex.measurable_ofReal.comp measurable_levyIntensityDensity).mul
        (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul, Complex.norm_exp]
    simp [abs_of_nonneg (levyIntensityDensity_nonneg x)]
  rw [hcp, ← Erdos1002.continuousCompoundPoissonProbability_toMeasure,
    Erdos1002.charFun_continuousCompoundPoissonProbability, charFun_apply_real]
  congr 1
  rw [mul_sub, mul_one, hg, h1, ← integral_sub hI1 hI2]
  refine setIntegral_congr_fun hSm (fun x _ => ?_)
  ring

/-- The characteristic function of the fixed-`ε` limit law, in the form the
`ε ↓ 0` argument consumes.  Proved from the single input above. -/
theorem charFun_largeJump_limit (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ρ : ProbabilityMeasure ℝ)
    (hρ : Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ)) (t : ℝ) :
    charFun (ρ : Measure ℝ) t
      = Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)) := by
  obtain ⟨r, ν, _hrate, hjump, hcp⟩ := largeJump_limit_compoundPoisson c ε hε0 hε1 ρ hρ
  exact charFun_compoundPoisson_levy hε0 t ρ r ν hjump hcp

/-- **Target, `Kwon1002.Assembly5.compound_tendsto_cauchy`, reproduced
token-identically** (Assembly5.lean lines 373-378).

Proved from `charFun_largeJump_limit` (the fixed-`ε` identification, above)
and from nothing else sorried: the `ε ↓ 0` exponent limit, the vanishing of
the imaginary part, the value `-|t|/(2π)` of the exponent, the characteristic
function of `Cauchy(0,1/(2π))` (`FourierPairs.charFun_cauchyProb`) and Lévy
continuity (`Erdos1002.levy_continuity_real`) are all proved. -/
theorem compound_tendsto_cauchy (c : ℝ) (e : ℕ → ℝ)
    (_he0 : ∀ k, 0 < e k) (_he1 : ∀ k, e k < 1) (_he : Tendsto e atTop (𝓝 0))
    (ρ : ℕ → ProbabilityMeasure ℝ)
    (_hρ : ∀ k, Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 (ρ k))) :
    Tendsto ρ atTop (𝓝 cauchyProb) := by
  refine Erdos1002.levy_continuity_real ρ cauchyProb (fun t => ?_)
  have hid : ∀ k : ℕ, charFun (ρ k : Measure ℝ) t
      = ((Real.exp (∫ x in {x : ℝ | e k < |x|},
          (Real.cos (t * x) - 1) * levyIntensityDensity x) : ℝ) : ℂ) := by
    intro k
    rw [charFun_largeJump_limit c (e k) (_he0 k) (_he1 k) (ρ k) (_hρ k) t,
      levyExponent_complex_eq_real (_he0 k) t, ← Complex.ofReal_exp]
  have hlim := tendsto_levyExponent_trunc t e _he0 _he
  have hR : Tendsto (fun k : ℕ => Real.exp
      (∫ x in {x : ℝ | e k < |x|}, (Real.cos (t * x) - 1) * levyIntensityDensity x))
      atTop (𝓝 (Real.exp (-(|t| / (2 * Real.pi))))) :=
    (Real.continuous_exp.tendsto _).comp hlim
  have hC : Tendsto (fun k : ℕ => ((Real.exp
      (∫ x in {x : ℝ | e k < |x|},
        (Real.cos (t * x) - 1) * levyIntensityDensity x) : ℝ) : ℂ))
      atTop (𝓝 ((Real.exp (-(|t| / (2 * Real.pi))) : ℝ) : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto _).comp hR
  simp only [hid]
  rw [FourierPairs.charFun_cauchyProb t]
  exact hC

end

end CompoundCauchy

end Kwon1002


/- **Token-identity check.**  The statement above is byte-identical to
`Assembly5.lean` lines 373-377 (verified by `diff`); the following `example`
verifies inside Lean that the two statements are the *same type*, i.e. that
`largeProb` and `cauchyProb` resolve to the same constants here as there.
(It mentions the still-sorried `Assembly5` declaration, so it is an
anonymous `example` and nothing proved above depends on it.) -/
example : @Kwon1002.Assembly5.compound_tendsto_cauchy
    = @Kwon1002.CompoundCauchy.compound_tendsto_cauchy := rfl
