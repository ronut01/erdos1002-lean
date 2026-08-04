import Kwon1002.CauchyLaw

/-!
# FourierPairs, the two classical analytic inputs of `CauchyLaw.lean`

Working file closing the two sorried classical-analysis statements

* `Kwon1002.integral_one_sub_cos_div_sq` : `∫_ℝ (1 - cos u) u⁻² du = π`
* `Kwon1002.charFun_cauchyProb` : the characteristic function of the
  constructed `Cauchy(0, 1/(2π))` law is `exp (-|t|/(2π))`.

Both are proved from mathlib's Fourier inversion theorem, applied to two
explicit Fourier pairs:

* the tent function `max (1 - |x|) 0`, whose transform is `2·(1-cos)/u²`
  rescaled, this gives the first integral;
* the two-sided exponential `exp (-|x|)`, whose transform is the Poisson
  kernel `2/(1+4π²w²)`, this gives the second.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal Real FourierTransform

namespace Kwon1002
namespace FourierPairs

noncomputable section

/-! ## §0 Generic helpers -/

/-- Lebesgue measure on `ℝ` is invariant under `x ↦ -x`. -/
lemma integral_comp_neg_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding f

/-- The integral of an odd function over `ℝ` vanishes (no integrability needed). -/
lemma integral_eq_zero_of_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) :
    (∫ x : ℝ, f x) = 0 := by
  have h := integral_comp_neg_full f
  simp_rw [hf] at h
  rw [integral_neg] at h
  linarith

/-! ## §1 The tent function -/

/-- The tent (triangle) function `max (1 - |x|) 0`. -/
def tent (x : ℝ) : ℝ := max (1 - |x|) 0

lemma tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_right _ _

lemma tent_zero : tent 0 = 1 := by simp [tent]

lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp [tent]

lemma tent_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 :=
  max_eq_right (by linarith)

@[fun_prop]
lemma continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

lemma hasCompactSupport_tent : HasCompactSupport tent := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  have h : ¬ (|x| ≤ 1) := fun h => hx (mem_Icc.mpr (abs_le.mp h))
  exact tent_eq_zero_of_one_le (le_of_lt (not_le.mp h))

lemma integrable_tent : Integrable tent :=
  continuous_tent.integrable_of_hasCompactSupport hasCompactSupport_tent

lemma integrable_cos_mul_tent (b : ℝ) :
    Integrable (fun v : ℝ => Real.cos (b * v) * tent v) := by
  refine Integrable.mono' integrable_tent (by fun_prop) (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tent_nonneg v)]
  calc |Real.cos (b * v)| * tent v ≤ 1 * tent v :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (tent_nonneg v)
    _ = tent v := one_mul _

lemma integrable_sin_mul_tent (b : ℝ) :
    Integrable (fun v : ℝ => Real.sin (b * v) * tent v) := by
  refine Integrable.mono' integrable_tent (by fun_prop) (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tent_nonneg v)]
  calc |Real.sin (b * v)| * tent v ≤ 1 * tent v :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (tent_nonneg v)
    _ = tent v := one_mul _

lemma integral_sin_mul_tent (b : ℝ) : (∫ v : ℝ, Real.sin (b * v) * tent v) = 0 := by
  refine integral_eq_zero_of_odd fun x => ?_
  rw [tent_neg, mul_neg, Real.sin_neg, neg_mul]

/-- The cosine transform of the tent function, computed by the fundamental theorem
of calculus on `[-1,0]` and `[0,1]`. -/
lemma integral_cos_mul_tent (b : ℝ) (hb : b ≠ 0) :
    (∫ v : ℝ, Real.cos (b * v) * tent v) = 2 * (1 - Real.cos b) / b ^ 2 := by
  have hb2 : (b : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hb
  -- the antiderivative on `[-1, 0]`
  have hF : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => (1 + y) * Real.sin (b * y) / b + Real.cos (b * y) / b ^ 2)
      (Real.cos (b * x) * (1 + x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => b * y) b x := by
      simpa using (hasDerivAt_id x).const_mul b
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (b * y)) (Real.cos (b * x) * b) x := h1.sin
    have h3 : HasDerivAt (fun y : ℝ => Real.cos (b * y)) (-Real.sin (b * x) * b) x := h1.cos
    have h4 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h5 := ((h4.mul h2).div_const b).add (h3.div_const (b ^ 2))
    convert h5 using 1
    field_simp
    ring
  -- the antiderivative on `[0, 1]`
  have hG : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => (1 - y) * Real.sin (b * y) / b - Real.cos (b * y) / b ^ 2)
      (Real.cos (b * x) * (1 - x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => b * y) b x := by
      simpa using (hasDerivAt_id x).const_mul b
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (b * y)) (Real.cos (b * x) * b) x := h1.sin
    have h3 : HasDerivAt (fun y : ℝ => Real.cos (b * y)) (-Real.sin (b * x) * b) x := h1.cos
    have h4 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h5 := ((h4.mul h2).div_const b).sub (h3.div_const (b ^ 2))
    convert h5 using 1
    field_simp
    ring
  -- localise the integral to `[-1, 1]`
  have hzero : ∀ v : ℝ, v ∉ Ioc (-1 : ℝ) 1 → Real.cos (b * v) * tent v = 0 := by
    intro v hv
    have hv1 : 1 ≤ |v| := by
      rcases le_or_gt v (-1) with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have h1 : 1 < v := by
          by_contra hc
          exact hv (mem_Ioc.mpr ⟨h, not_lt.mp hc⟩)
        rw [abs_of_nonneg (by linarith)]; linarith
    rw [tent_eq_zero_of_one_le hv1, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (a := (-1 : ℝ)) (b := (0 : ℝ)) (c := (1 : ℝ))
      ((by fun_prop : Continuous fun v : ℝ => Real.cos (b * v) * tent v).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun v : ℝ => Real.cos (b * v) * tent v).intervalIntegrable _ _)]
  have e1 : (∫ v in (-1 : ℝ)..0, Real.cos (b * v) * tent v)
      = ∫ v in (-1 : ℝ)..0, Real.cos (b * v) * (1 + v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
    have hval : tent v = 1 + v := by
      rw [tent, abs_of_nonpos hv.2, max_eq_left (by linarith [hv.1])]
      ring
    rw [hval]
  have e2 : (∫ v in (0 : ℝ)..1, Real.cos (b * v) * tent v)
      = ∫ v in (0 : ℝ)..1, Real.cos (b * v) * (1 - v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have hval : tent v = 1 - v := by
      rw [tent, abs_of_nonneg hv.1, max_eq_left (by linarith [hv.2])]
    rw [hval]
  rw [e1, e2,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
      ((by fun_prop : Continuous fun x : ℝ => Real.cos (b * x) * (1 + x)).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x)
      ((by fun_prop : Continuous fun x : ℝ => Real.cos (b * x) * (1 - x)).intervalIntegrable _ _)]
  simp only [Real.sin_zero, Real.cos_zero, mul_zero, mul_one, add_zero, sub_zero, zero_add,
    sub_self, zero_mul, zero_div, Real.cos_neg, Real.sin_neg, mul_neg]
  field_simp
  ring

/-! ## §2 The kernel `(1 - cos u)/u²` -/

/-- The integrand of the target integral. -/
def sawKernel (u : ℝ) : ℝ := (1 - Real.cos u) / u ^ 2

lemma sawKernel_nonneg (u : ℝ) : 0 ≤ sawKernel u := by
  unfold sawKernel
  exact div_nonneg (by linarith [Real.cos_le_one u]) (sq_nonneg u)

lemma sawKernel_le (u : ℝ) : sawKernel u ≤ 4 * (1 + u ^ 2)⁻¹ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [sawKernel]
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  have hden : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hcos1 : Real.cos u ≤ 1 := Real.cos_le_one u
  have hcos2 : (-1 : ℝ) ≤ Real.cos u := Real.neg_one_le_cos u
  have hquad : 1 - u ^ 2 / 2 ≤ Real.cos u := Real.one_sub_sq_div_two_le_cos
  have key : (1 - Real.cos u) * (1 + u ^ 2) ≤ 4 * u ^ 2 := by
    rcases le_or_gt (u ^ 2) 2 with h | h
    · nlinarith
    · nlinarith
  have hrw : 4 * (1 + u ^ 2)⁻¹ = 4 / (1 + u ^ 2) := by
    rw [div_eq_mul_inv]
  rw [sawKernel, hrw, div_le_div_iff₀ hu2 hden]
  linarith [key]

lemma measurable_sawKernel : Measurable sawKernel := by
  unfold sawKernel
  fun_prop

lemma integrable_sawKernel : Integrable sawKernel := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 4)
    measurable_sawKernel.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sawKernel_nonneg u)]
  exact sawKernel_le u

/-! ## §3 The Fourier transform of the tent function -/

lemma fourier_tent (w : ℝ) (hw : w ≠ 0) :
    𝓕 (fun x : ℝ => (tent x : ℂ)) w = ((2 * sawKernel (2 * Real.pi * w) : ℝ) : ℂ) := by
  have hb : (2 * Real.pi * w) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hw
  set b : ℝ := 2 * Real.pi * w with hbdef
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpoint : ∀ v : ℝ,
      (Complex.exp ((↑(-2 * Real.pi * v * w) : ℂ) * Complex.I) • ((tent v : ℝ) : ℂ))
        = ((Real.cos (b * v) * tent v : ℝ) : ℂ)
          - ((Real.sin (b * v) * tent v : ℝ) : ℂ) * Complex.I := by
    intro v
    have hrw : (-2 * Real.pi * v * w : ℝ) = -(b * v) := by rw [hbdef]; ring
    rw [hrw, smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have h1 : Integrable (fun v : ℝ => ((Real.cos (b * v) * tent v : ℝ) : ℂ)) :=
    (integrable_cos_mul_tent b).ofReal
  have h2 : Integrable (fun v : ℝ => ((Real.sin (b * v) * tent v : ℝ) : ℂ) * Complex.I) :=
    ((integrable_sin_mul_tent b).ofReal).mul_const Complex.I
  have hc1 : (∫ v : ℝ, ((Real.cos (b * v) * tent v : ℝ) : ℂ))
      = ((∫ v : ℝ, Real.cos (b * v) * tent v : ℝ) : ℂ) := integral_complex_ofReal
  have hc2 : (∫ v : ℝ, ((Real.sin (b * v) * tent v : ℝ) : ℂ))
      = ((∫ v : ℝ, Real.sin (b * v) * tent v : ℝ) : ℂ) := integral_complex_ofReal
  simp_rw [hpoint]
  rw [integral_sub h1 h2, integral_mul_const, hc1, hc2,
    integral_cos_mul_tent b hb, integral_sin_mul_tent b]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  norm_cast
  rw [sawKernel]
  ring

lemma ae_ne_zero : ∀ᵐ w : ℝ, w ≠ 0 := by
  rw [ae_iff]
  simp

lemma integrable_fourier_tent : Integrable (𝓕 fun x : ℝ => (tent x : ℂ)) := by
  have hae : ∀ᵐ w : ℝ, (((2 * sawKernel (2 * Real.pi * w) : ℝ) : ℂ))
      = 𝓕 (fun x : ℝ => (tent x : ℂ)) w := by
    filter_upwards [ae_ne_zero] with w hw using (fourier_tent w hw).symm
  refine Integrable.congr ?_ hae
  exact ((integrable_sawKernel.comp_mul_left'
    (mul_ne_zero two_ne_zero Real.pi_ne_zero)).const_mul 2).ofReal

/-! ## §4 Target 1 -/

lemma integral_sawKernel : (∫ u : ℝ, sawKernel u) = Real.pi := by
  have hinv : 𝓕⁻ (𝓕 fun x : ℝ => (tent x : ℂ)) 0 = ((tent 0 : ℝ) : ℂ) :=
    (integrable_tent.ofReal).fourierInv_fourier_eq integrable_fourier_tent
      (Complex.continuous_ofReal.comp continuous_tent).continuousAt
  rw [Real.fourierInv_eq] at hinv
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, tent_zero,
    Complex.ofReal_one] at hinv
  have hae : ∀ᵐ w : ℝ, 𝓕 (fun x : ℝ => (tent x : ℂ)) w
      = (((2 * sawKernel (2 * Real.pi * w) : ℝ) : ℂ)) := by
    filter_upwards [ae_ne_zero] with w hw using fourier_tent w hw
  have hcast : (∫ w : ℝ, ((2 * sawKernel (2 * Real.pi * w) : ℝ) : ℂ))
      = ((∫ w : ℝ, 2 * sawKernel (2 * Real.pi * w) : ℝ) : ℂ) := integral_complex_ofReal
  rw [integral_congr_ae hae, hcast] at hinv
  have hreal : (∫ w : ℝ, 2 * sawKernel (2 * Real.pi * w)) = 1 := by exact_mod_cast hinv
  rw [integral_const_mul, Measure.integral_comp_mul_left sawKernel (2 * Real.pi)] at hreal
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_of_pos (inv_pos.mpr hpi), smul_eq_mul] at hreal
  field_simp at hreal
  linarith

theorem integral_one_sub_cos_div_sq :
    (∫ u : ℝ, (1 - Real.cos u) / u ^ 2) = Real.pi := integral_sawKernel

/-! ## §5 The two-sided exponential -/

lemma integrable_expNegAbs : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine integrableOn_union.mpr ⟨?_, ?_⟩
  · refine (integrableOn_exp_Iic (0 : ℝ)).congr_fun (fun x hx => ?_) measurableSet_Iic
    show Real.exp x = Real.exp (-|x|)
    rw [abs_of_nonpos hx, neg_neg]
  · refine (integrableOn_exp_neg_Ioi (0 : ℝ)).congr_fun (fun x hx => ?_) measurableSet_Ioi
    show Real.exp (-x) = Real.exp (-|x|)
    rw [abs_of_nonneg (le_of_lt hx)]

lemma integral_Ioi_cos_mul_exp_neg (b : ℝ) :
    (∫ x in Ioi (0 : ℝ), Real.cos (b * x) * Real.exp (-x)) = 1 / (1 + b ^ 2) := by
  have hd : (0 : ℝ) < 1 + b ^ 2 := by positivity
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => Real.exp (-y) * (b * Real.sin (b * y) - Real.cos (b * y)) / (1 + b ^ 2))
      (Real.cos (b * x) * Real.exp (-x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_neg' x).exp
    have h2 : HasDerivAt (fun y : ℝ => b * y) b x := by
      simpa using (hasDerivAt_id x).const_mul b
    have h3 : HasDerivAt (fun y : ℝ => Real.sin (b * y)) (Real.cos (b * x) * b) x := h2.sin
    have h4 : HasDerivAt (fun y : ℝ => Real.cos (b * y)) (-Real.sin (b * x) * b) x := h2.cos
    have h5 := ((h1.mul ((h3.const_mul b).sub h4)).div_const (1 + b ^ 2))
    convert h5 using 1
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => Real.cos (b * x) * Real.exp (-x)) (Ioi 0) := by
    refine Integrable.mono' (integrableOn_exp_neg_Ioi (0 : ℝ)) (by fun_prop)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc |Real.cos (b * x)| * Real.exp (-x) ≤ 1 * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-x) := one_mul _
  have htend : Tendsto
      (fun y : ℝ => Real.exp (-y) * (b * Real.sin (b * y) - Real.cos (b * y)) / (1 + b ^ 2))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun y => ?_)
      (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const ((|b| + 1) / (1 + b ^ 2)))
    have h1 : |b * Real.sin (b * y)| ≤ |b| := by
      rw [abs_mul]
      calc |b| * |Real.sin (b * y)| ≤ |b| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg b)
        _ = |b| := mul_one _
    have h2 : |Real.cos (b * y)| ≤ 1 := Real.abs_cos_le_one _
    have h3 := abs_add_le (b * Real.sin (b * y)) (-Real.cos (b * y))
    rw [← sub_eq_add_neg, abs_neg] at h3
    have hnum : |b * Real.sin (b * y) - Real.cos (b * y)| ≤ |b| + 1 := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_pos hd, mul_div_assoc]
    gcongr
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hmain]
  norm_num
  rw [neg_div, neg_neg, one_div]

lemma integral_cos_mul_expNegAbs (b : ℝ) :
    (∫ x : ℝ, Real.cos (b * x) * Real.exp (-|x|)) = 2 / (1 + b ^ 2) := by
  have hcongr : (∫ x : ℝ, Real.cos (b * x) * Real.exp (-|x|))
      = ∫ x : ℝ, Real.cos (b * |x|) * Real.exp (-|x|) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.cos (b * x) * Real.exp (-|x|) = Real.cos (b * |x|) * Real.exp (-|x|)
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cos_neg]
  have habs : (∫ x : ℝ, Real.cos (b * |x|) * Real.exp (-|x|))
      = 2 * ∫ x in Ioi (0 : ℝ), Real.cos (b * x) * Real.exp (-x) :=
    integral_comp_abs (f := fun y : ℝ => Real.cos (b * y) * Real.exp (-y))
  rw [hcongr, habs, integral_Ioi_cos_mul_exp_neg b]
  ring

lemma integrable_cos_mul_expNegAbs (b : ℝ) :
    Integrable (fun v : ℝ => Real.cos (b * v) * Real.exp (-|v|)) := by
  refine Integrable.mono' integrable_expNegAbs (by fun_prop) (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc |Real.cos (b * v)| * Real.exp (-|v|) ≤ 1 * Real.exp (-|v|) :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ = Real.exp (-|v|) := one_mul _

lemma integrable_sin_mul_expNegAbs (b : ℝ) :
    Integrable (fun v : ℝ => Real.sin (b * v) * Real.exp (-|v|)) := by
  refine Integrable.mono' integrable_expNegAbs (by fun_prop) (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc |Real.sin (b * v)| * Real.exp (-|v|) ≤ 1 * Real.exp (-|v|) :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (Real.exp_pos _).le
    _ = Real.exp (-|v|) := one_mul _

lemma integral_sin_mul_expNegAbs (b : ℝ) :
    (∫ v : ℝ, Real.sin (b * v) * Real.exp (-|v|)) = 0 := by
  refine integral_eq_zero_of_odd fun x => ?_
  rw [abs_neg, mul_neg, Real.sin_neg, neg_mul]

/-! ## §6 The Fourier transform of `exp (-|x|)` (the Poisson kernel) -/

lemma fourier_expNegAbs (w : ℝ) :
    𝓕 (fun x : ℝ => ((Real.exp (-|x|) : ℝ) : ℂ)) w
      = ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
  set b : ℝ := 2 * Real.pi * w with hbdef
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpoint : ∀ v : ℝ,
      (Complex.exp ((↑(-2 * Real.pi * v * w) : ℂ) * Complex.I)
          • ((Real.exp (-|v|) : ℝ) : ℂ))
        = ((Real.cos (b * v) * Real.exp (-|v|) : ℝ) : ℂ)
          - ((Real.sin (b * v) * Real.exp (-|v|) : ℝ) : ℂ) * Complex.I := by
    intro v
    have hrw : (-2 * Real.pi * v * w : ℝ) = -(b * v) := by rw [hbdef]; ring
    rw [hrw, smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have h1 : Integrable (fun v : ℝ => ((Real.cos (b * v) * Real.exp (-|v|) : ℝ) : ℂ)) :=
    (integrable_cos_mul_expNegAbs b).ofReal
  have h2 : Integrable
      (fun v : ℝ => ((Real.sin (b * v) * Real.exp (-|v|) : ℝ) : ℂ) * Complex.I) :=
    ((integrable_sin_mul_expNegAbs b).ofReal).mul_const Complex.I
  have hc1 : (∫ v : ℝ, ((Real.cos (b * v) * Real.exp (-|v|) : ℝ) : ℂ))
      = ((∫ v : ℝ, Real.cos (b * v) * Real.exp (-|v|) : ℝ) : ℂ) := integral_complex_ofReal
  have hc2 : (∫ v : ℝ, ((Real.sin (b * v) * Real.exp (-|v|) : ℝ) : ℂ))
      = ((∫ v : ℝ, Real.sin (b * v) * Real.exp (-|v|) : ℝ) : ℂ) := integral_complex_ofReal
  simp_rw [hpoint]
  rw [integral_sub h1 h2, integral_mul_const, hc1, hc2,
    integral_cos_mul_expNegAbs b, integral_sin_mul_expNegAbs b]
  simp

lemma integrable_poissonKernel :
    Integrable (fun w : ℝ => (2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ)) := by
  have h2pi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  refine (((integrable_inv_one_add_sq.comp_mul_left' h2pi)).const_mul 2).congr
    (Filter.Eventually.of_forall fun w => ?_)
  show (2 : ℝ) * (1 + (2 * Real.pi * w) ^ 2)⁻¹ = 2 / (1 + (2 * Real.pi * w) ^ 2)
  rw [← div_eq_mul_inv]

lemma integrable_fourier_expNegAbs :
    Integrable (𝓕 fun x : ℝ => ((Real.exp (-|x|) : ℝ) : ℂ)) := by
  have heq : (𝓕 fun x : ℝ => ((Real.exp (-|x|) : ℝ) : ℂ))
      = fun w : ℝ => ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) :=
    funext fourier_expNegAbs
  rw [heq]
  exact integrable_poissonKernel.ofReal

/-- Fourier inversion applied to `exp (-|x|)`. -/
lemma inversion_expNegAbs (v : ℝ) :
    (∫ w : ℝ, Complex.exp ((↑(2 * Real.pi * w * v) : ℂ) * Complex.I)
        * ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ))
      = ((Real.exp (-|v|) : ℝ) : ℂ) := by
  have hinv : 𝓕⁻ (𝓕 fun x : ℝ => ((Real.exp (-|x|) : ℝ) : ℂ)) v
      = ((Real.exp (-|v|) : ℝ) : ℂ) :=
    (integrable_expNegAbs.ofReal).fourierInv_fourier_eq integrable_fourier_expNegAbs
      ((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_abs.neg)).continuousAt)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  rw [← hinv]
  have hrw : ∀ u : ℝ, (-2 * Real.pi * u * -v : ℝ) = 2 * Real.pi * u * v := fun u => by ring
  simp_rw [hrw, fourier_expNegAbs, smul_eq_mul]

/-- The Fourier transform of the Cauchy density: `∫ e^{ixv}/(1+x²) dx = π e^{-|v|}`. -/
lemma integral_cexp_mul_inv_one_add_sq (v : ℝ) :
    (∫ x : ℝ, Complex.exp ((↑v : ℂ) * (↑x : ℂ) * Complex.I)
        * (((1 + x ^ 2)⁻¹ : ℝ) : ℂ))
      = ((Real.pi * Real.exp (-|v|) : ℝ) : ℂ) := by
  have h2pi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hchange := Measure.integral_comp_inv_mul_left
    (fun w : ℝ => Complex.exp ((↑(2 * Real.pi * w * v) : ℂ) * Complex.I)
      * ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)) (2 * Real.pi)
  rw [inversion_expNegAbs v] at hchange
  have hpt : ∀ x : ℝ,
      Complex.exp ((↑(2 * Real.pi * ((2 * Real.pi)⁻¹ * x) * v) : ℂ) * Complex.I)
        * ((2 / (1 + (2 * Real.pi * ((2 * Real.pi)⁻¹ * x)) ^ 2) : ℝ) : ℂ)
      = 2 * (Complex.exp ((↑v : ℂ) * (↑x : ℂ) * Complex.I)
        * (((1 + x ^ 2)⁻¹ : ℝ) : ℂ)) := by
    intro x
    have h1 : (2 * Real.pi * ((2 * Real.pi)⁻¹ * x) : ℝ) = x := by field_simp
    have h2 : ((↑(x * v) : ℂ)) = (↑v : ℂ) * (↑x : ℂ) := by push_cast; ring
    rw [h1, h2]
    push_cast
    ring
  simp_rw [hpt] at hchange
  rw [integral_const_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    Complex.real_smul] at hchange
  rw [← mul_right_inj' (two_ne_zero : (2 : ℂ) ≠ 0), hchange]
  push_cast
  ring

/-! ## §7 The standard Cauchy law as a density, and its characteristic function -/

/-- The density of the standard Cauchy law. -/
def cauchyDensity (x : ℝ) : ℝ := Real.pi⁻¹ * (1 + x ^ 2)⁻¹

lemma cauchyDensity_nonneg (x : ℝ) : 0 ≤ cauchyDensity x := by
  unfold cauchyDensity
  positivity

lemma measurable_cauchyDensity : Measurable cauchyDensity := by
  unfold cauchyDensity
  fun_prop

lemma integrable_cauchyDensity : Integrable cauchyDensity :=
  integrable_inv_one_add_sq.const_mul _

/-- The `γ = 1` Cauchy measure built in `CauchyLaw.lean` is the measure with the
standard Cauchy density.  Proved by comparing distribution functions. -/
lemma cauchyMeasure_one_eq_withDensity :
    cauchyMeasure 1 = volume.withDensity (fun x => ENNReal.ofReal (cauchyDensity x)) := by
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [cauchyMeasure_Iic (by norm_num : (0 : ℝ) < 1) a,
    withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal integrable_cauchyDensity.integrableOn
      (ae_of_all _ cauchyDensity_nonneg)]
  have hI : (∫ x in Iic a, cauchyDensity x) = Real.pi⁻¹ * (Real.arctan a + Real.pi / 2) := by
    unfold cauchyDensity
    rw [integral_const_mul, integral_Iic_inv_one_add_sq]
  rw [hI, div_one, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos Real.pi_pos]

lemma charFun_cauchyMeasure_one (t : ℝ) :
    charFun (cauchyMeasure 1) t = ((Real.exp (-|t|) : ℝ) : ℂ) := by
  have hpine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (cauchyDensity x)) :=
    ENNReal.measurable_ofReal.comp measurable_cauchyDensity
  rw [charFun_apply_real, cauchyMeasure_one_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have hpt : ∀ x : ℝ,
      (ENNReal.ofReal (cauchyDensity x)).toReal • Complex.exp ((↑t : ℂ) * (↑x : ℂ) * Complex.I)
        = ((Real.pi⁻¹ : ℝ) : ℂ)
          * (Complex.exp ((↑t : ℂ) * (↑x : ℂ) * Complex.I) * (((1 + x ^ 2)⁻¹ : ℝ) : ℂ)) := by
    intro x
    rw [ENNReal.toReal_ofReal (cauchyDensity_nonneg x), Complex.real_smul, cauchyDensity]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_cexp_mul_inv_one_add_sq t]
  push_cast
  field_simp

/-! ## §8 Target 2 -/

lemma cauchyMeasure_eq_map (γ : ℝ) :
    cauchyMeasure γ = (cauchyMeasure 1).map (fun x : ℝ => γ * x) := by
  have hm : Measurable (fun x : ℝ => γ * x) := measurable_id.const_mul γ
  unfold cauchyMeasure
  rw [Measure.map_map hm (measurable_gammaTan 1)]
  congr 1
  funext θ
  simp [Function.comp]

lemma charFun_cauchyMeasure (γ t : ℝ) :
    charFun (cauchyMeasure γ) t = ((Real.exp (-|γ * t|) : ℝ) : ℂ) := by
  rw [cauchyMeasure_eq_map γ, charFun_map_mul, charFun_cauchyMeasure_one]

theorem charFun_cauchyProb (t : ℝ) :
    charFun (cauchyProb : Measure ℝ) t
      = (Real.exp (-(|t| / (2 * Real.pi))) : ℂ) := by
  have h : (cauchyProb : Measure ℝ) = cauchyMeasure (1 / (2 * Real.pi)) := rfl
  rw [h, charFun_cauchyMeasure]
  have hval : (-|1 / (2 * Real.pi) * t| : ℝ) = -(|t| / (2 * Real.pi)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    ring
  rw [hval]

end

end FourierPairs
end Kwon1002
