import Kwon1002.NatExtMixing
import Kwon1002.LDObservable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Dist

/-!
# Large deviations, stage A5: covariance decay and block second moments

`|Cov(g_u(x_0), g_u(x_q))| ≤ C e^{−κ q}` **uniformly in the cap** `u ≥ 0`,
and consequently `E[(Σ_{i<ℓ} ḡ_u(x_{t+i}))²] ≤ C₀ ℓ` for every block.

Route: for the pair at distance `q`, split the cap at `w = qκ'`
(`κ' = log(540/527)/2`).  The part capped at `w` is Lipschitz with
constant `e^{w+λ} = ρ₀^{−q/2} e^λ`, so `gauss_correlation_le`
(`NatExtMixing`) gives decay `ρ₀^q · e^{w+λ} (w + 2λ) ≲ ρ₀^{q/2} (q+1)`;
the difference of caps is supported on `(0, e^{−(w+λ)})` and has second
moment `≲ e^{−w/2} = ρ₀^{q/4}` by `log²(1/x) ≤ 16/√x` and
`∫₀^ε x^{−1/2} dx = 2√ε`; cross terms are handled by Cauchy–Schwarz and
stationarity.  Everything is elementary except the single input
`gauss_correlation_le`.
-/

open Set MeasureTheory

namespace Kwon1002

namespace LargeDeviation

noncomputable section

local notation "γ" => Erdos1002.gaussMeasure
local notation "T" => Erdos1002.gaussOrbit

/-! ### Generic facts: a.e. membership, triangle helpers -/

private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

private lemma ae_orbit_mem (q : ℕ) :
    ∀ᵐ x ∂γ, T q x ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [ae_gauss_unit_irrational] with x hx
  rw [← gaussIter_eq_gaussOrbit]
  exact gaussIter_mem_Ioo hx.1 hx.2 q

/-! ### Pointwise elementary bound `log² x ≤ 16 x^{-1/2}` on `(0,1]` -/

private lemma sq_log_le_rpow {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (Real.log x) ^ 2 ≤ 16 * x ^ (-(1 / 2) : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (-(1 / 4) : ℝ))
  rw [Real.log_rpow hx0] at h
  have hp : (0 : ℝ) < x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hneg : -Real.log x ≤ 4 * x ^ (-(1 / 4) : ℝ) := by linarith
  have hl : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx0.le hx1)
  have hsq : (x ^ (-(1 / 4) : ℝ)) ^ 2 = x ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast (x ^ (-(1 / 4) : ℝ)) 2, ← Real.rpow_mul hx0.le]
    norm_num
  have hmul : (-Real.log x) * (-Real.log x)
      ≤ (4 * x ^ (-(1 / 4) : ℝ)) * (4 * x ^ (-(1 / 4) : ℝ)) :=
    mul_le_mul hneg hneg hl (by positivity)
  calc (Real.log x) ^ 2 = (-Real.log x) * (-Real.log x) := by ring
    _ ≤ (4 * x ^ (-(1 / 4) : ℝ)) * (4 * x ^ (-(1 / 4) : ℝ)) := hmul
    _ = 16 * (x ^ (-(1 / 4) : ℝ)) ^ 2 := by ring
    _ = 16 * x ^ (-(1 / 2) : ℝ) := by rw [hsq]

/-! ### Lebesgue-side integrals -/

private lemma integrableOn_rpow_half {ε : ℝ} (hε0 : 0 < ε) :
    IntegrableOn (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (Ioc (0 : ℝ) ε) volume :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hε0.le).mp
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

private lemma integrableOn_sq_log_unit :
    IntegrableOn (fun x : ℝ => (Real.log x) ^ 2) (Ioc (0 : ℝ) 1) volume := by
  apply Integrable.mono' ((integrableOn_rpow_half one_pos).const_mul 16)
    ((Real.measurable_log.pow_const 2).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_log_le_rpow hx.1 hx.2

private lemma integral_rpow_Ioc {ε : ℝ} (hε0 : 0 < ε) :
    ∫ x in Ioc (0 : ℝ) ε, x ^ (-(1 / 2) : ℝ) = 2 * Real.sqrt ε := by
  rw [← intervalIntegral.integral_of_le hε0.le]
  rw [integral_rpow (Or.inl (by norm_num))]
  have h1 : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
  rw [h1, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.sqrt_eq_rpow]
  ring

private lemma setIntegral_sq_log_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ x in Ioc (0 : ℝ) ε, (Real.log x) ^ 2 ≤ 32 * Real.sqrt ε := by
  have hint1 : IntegrableOn (fun x : ℝ => (Real.log x) ^ 2) (Ioc (0 : ℝ) ε) volume :=
    integrableOn_sq_log_unit.mono_set (Ioc_subset_Ioc_right hε1)
  have hint2 : IntegrableOn (fun x : ℝ => 16 * x ^ (-(1 / 2) : ℝ)) (Ioc (0 : ℝ) ε) volume :=
    (integrableOn_rpow_half hε0).const_mul 16
  calc ∫ x in Ioc (0 : ℝ) ε, (Real.log x) ^ 2
      ≤ ∫ x in Ioc (0 : ℝ) ε, 16 * x ^ (-(1 / 2) : ℝ) := by
        refine setIntegral_mono_on hint1 hint2 measurableSet_Ioc fun x hx => ?_
        exact sq_log_le_rpow hx.1 (le_trans hx.2 hε1)
    _ = 16 * ∫ x in Ioc (0 : ℝ) ε, x ^ (-(1 / 2) : ℝ) := integral_const_mul 16 _
    _ = 16 * (2 * Real.sqrt ε) := by rw [integral_rpow_Ioc hε0]
    _ = 32 * Real.sqrt ε := by ring

/-! ### The Gauss measure is dominated by `(3/2) · Leb` on `(0,1]` -/

private lemma gaussMeasure_le_smul :
    Erdos1002.gaussMeasure
      ≤ ENNReal.ofReal (3 / 2) • volume.restrict (Ioc (0 : ℝ) 1) := by
  rw [Erdos1002.gaussMeasure_eq_volume_withDensity,
    show Erdos1002.gaussDensity
        = (Ioc (0 : ℝ) 1).indicator Erdos1002.gaussDensityCore from rfl,
    withDensity_indicator measurableSet_Ioc]
  calc (volume.restrict (Ioc (0 : ℝ) 1)).withDensity Erdos1002.gaussDensityCore
      ≤ (volume.restrict (Ioc (0 : ℝ) 1)).withDensity
          (fun _ => ENNReal.ofReal (3 / 2)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        show Erdos1002.gaussDensityCore x ≤ ENNReal.ofReal (3 / 2)
        rw [show Erdos1002.gaussDensityCore x
            = ENNReal.ofReal (1 / (Real.log 2 * (1 + x))) from rfl]
        apply ENNReal.ofReal_le_ofReal
        have hl := Real.log_two_gt_d9
        have hd : (2 : ℝ) / 3 ≤ Real.log 2 * (1 + x) := by nlinarith [hx.1, hx.2]
        calc 1 / (Real.log 2 * (1 + x)) ≤ 1 / ((2 : ℝ) / 3) :=
              one_div_le_one_div_of_le (by norm_num) hd
          _ = 3 / 2 := by norm_num
    _ = ENNReal.ofReal (3 / 2) • volume.restrict (Ioc (0 : ℝ) 1) :=
        withDensity_const _

private lemma integrable_gauss {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioc (0 : ℝ) 1) volume) :
    Integrable f Erdos1002.gaussMeasure :=
  Integrable.of_measure_le_smul ENNReal.ofReal_ne_top gaussMeasure_le_smul hf

private lemma integral_gauss_le {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioc (0 : ℝ) 1) volume)
    (h0 : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ f x) :
    ∫ x, f x ∂γ ≤ (3 / 2) * ∫ x in Ioc (0 : ℝ) 1, f x := by
  have h0' : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ h0)
  calc ∫ x, f x ∂γ
      ≤ ∫ x, f x ∂(ENNReal.ofReal (3 / 2) • volume.restrict (Ioc (0 : ℝ) 1)) :=
        integral_mono_measure gaussMeasure_le_smul (Measure.ae_smul_measure h0' _)
          (hf.smul_measure ENNReal.ofReal_ne_top)
    _ = (3 / 2) * ∫ x in Ioc (0 : ℝ) 1, f x := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]

private lemma integral_gauss_sq_log_le : ∫ x, (Real.log x) ^ 2 ∂γ ≤ 48 := by
  calc ∫ x, (Real.log x) ^ 2 ∂γ
      ≤ (3 / 2) * ∫ x in Ioc (0 : ℝ) 1, (Real.log x) ^ 2 :=
        integral_gauss_le integrableOn_sq_log_unit (fun x _ => sq_nonneg _)
    _ ≤ (3 / 2) * (32 * Real.sqrt 1) :=
        mul_le_mul_of_nonneg_left (setIntegral_sq_log_le one_pos le_rfl) (by norm_num)
    _ = 48 := by rw [Real.sqrt_one]; norm_num

private lemma integral_gauss_indicator_sq_log_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ x, (Ioc (0 : ℝ) ε).indicator (fun y => (Real.log y) ^ 2) x ∂γ
      ≤ 48 * Real.sqrt ε := by
  have hind : IntegrableOn ((Ioc (0 : ℝ) ε).indicator fun y => (Real.log y) ^ 2)
      (Ioc (0 : ℝ) 1) volume :=
    integrableOn_sq_log_unit.indicator measurableSet_Ioc
  have h0 : ∀ x ∈ Ioc (0 : ℝ) 1,
      0 ≤ (Ioc (0 : ℝ) ε).indicator (fun y => (Real.log y) ^ 2) x :=
    fun x _ => indicator_nonneg (fun y _ => sq_nonneg _) x
  calc ∫ x, (Ioc (0 : ℝ) ε).indicator (fun y => (Real.log y) ^ 2) x ∂γ
      ≤ (3 / 2) * ∫ x in Ioc (0 : ℝ) 1,
          (Ioc (0 : ℝ) ε).indicator (fun y => (Real.log y) ^ 2) x :=
        integral_gauss_le hind h0
    _ = (3 / 2) * ∫ x in Ioc (0 : ℝ) 1 ∩ Ioc (0 : ℝ) ε, (Real.log x) ^ 2 := by
        rw [setIntegral_indicator measurableSet_Ioc]
    _ = (3 / 2) * ∫ x in Ioc (0 : ℝ) ε, (Real.log x) ^ 2 := by
        rw [inter_eq_self_of_subset_right (Ioc_subset_Ioc_right hε1)]
    _ ≤ (3 / 2) * (32 * Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left (setIntegral_sq_log_le hε0 hε1) (by norm_num)
    _ = 48 * Real.sqrt ε := by ring

/-! ### Integrability boilerplate on the probability space `γ` -/

private lemma integrable_of_unit_bound {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ B) : Integrable f γ := by
  refine (integrable_const B).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_gauss_unit_irrational] with x hx
  rw [Real.norm_eq_abs]
  exact hb x hx.1

private lemma integrable_comp_orbit {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ B) (q : ℕ) :
    Integrable (fun x => f (T q x)) γ := by
  refine (integrable_const B).mono'
    ((hm.comp (Erdos1002.measurable_gaussOrbit q)).aestronglyMeasurable) ?_
  filter_upwards [ae_orbit_mem q] with x hx
  rw [Real.norm_eq_abs]
  exact hb _ hx

private lemma integrable_mul_orbit {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {Bf Bg : ℝ} (hbf : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ Bf)
    (hbg : ∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ Bg) (q : ℕ) :
    Integrable (fun x => f x * g (T q x)) γ := by
  have hBf : 0 ≤ Bf := le_trans (abs_nonneg _) (hbf (1 / 2) (by norm_num))
  refine (integrable_const (Bf * Bg)).mono'
    ((hfm.mul (hgm.comp (Erdos1002.measurable_gaussOrbit q))).aestronglyMeasurable) ?_
  filter_upwards [ae_gauss_unit_irrational, ae_orbit_mem q] with x hx hTx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hbf x hx.1) (hbg _ hTx) (abs_nonneg _) hBf

private lemma integrable_orbit_mul_orbit {f : ℝ → ℝ} (hfm : Measurable f)
    {B : ℝ} (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ B) (a b : ℕ) :
    Integrable (fun x => f (T a x) * f (T b x)) γ := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb (1 / 2) (by norm_num))
  refine (integrable_const (B * B)).mono'
    (((hfm.comp (Erdos1002.measurable_gaussOrbit a)).mul
      (hfm.comp (Erdos1002.measurable_gaussOrbit b))).aestronglyMeasurable) ?_
  filter_upwards [ae_orbit_mem a, ae_orbit_mem b] with x ha hb'
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hb _ ha) (hb _ hb') (abs_nonneg _) hB

/-! ### Stationarity wrappers -/

private lemma integral_comp_orbit_eq (f : ℝ → ℝ) (hm : Measurable f) (q : ℕ) :
    ∫ x, f (T q x) ∂γ = ∫ x, f x ∂γ :=
  integral_comp_gaussOrbit q f hm.aestronglyMeasurable

private lemma integral_sq_comp_orbit (g : ℝ → ℝ) (hgm : Measurable g) (q : ℕ) :
    ∫ x, g (T q x) ^ 2 ∂γ = ∫ x, g x ^ 2 ∂γ :=
  integral_comp_gaussOrbit q (fun y => g y ^ 2) ((hgm.pow_const 2).aestronglyMeasurable)

/-! ### AM–GM with a free parameter, and its two integral consequences -/

private lemma amgm {t : ℝ} (ht : 0 < t) {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    a * b ≤ (t * a ^ 2 + (1 / t) * b ^ 2) / 2 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h1 : 0 ≤ (1 / t) * (t * a - b) ^ 2 := by positivity
  have h2 : (1 / t) * (t * a - b) ^ 2 = t * a ^ 2 + (1 / t) * b ^ 2 - 2 * (a * b) := by
    field_simp
    ring
  linarith

private lemma abs_integral_le_amgm {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ B) {t : ℝ} (ht : 0 < t) :
    |∫ x, f x ∂γ| ≤ (t * ∫ x, f x ^ 2 ∂γ + 1 / t) / 2 := by
  have hint : Integrable f γ := integrable_of_unit_bound hm hb
  have hint2 : Integrable (fun x => f x ^ 2) γ := by
    refine integrable_of_unit_bound (hm.pow_const 2) (B := B ^ 2) fun x hx => ?_
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith [abs_nonneg (f x), hb x hx]
  calc |∫ x, f x ∂γ| ≤ ∫ x, |f x| ∂γ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (t * f x ^ 2 + 1 / t) / 2 ∂γ := by
        refine integral_mono hint.abs
          (((hint2.const_mul t).add (integrable_const _)).div_const 2) fun x => ?_
        have h := amgm ht (abs_nonneg (f x)) (zero_le_one)
        rw [mul_one, one_pow, mul_one, sq_abs] at h
        exact h
    _ = (t * ∫ x, f x ^ 2 ∂γ + 1 / t) / 2 := by
        rw [integral_div, integral_add (hint2.const_mul t) (integrable_const _),
          integral_const_mul, integral_const]
        simp

private lemma abs_integral_mul_orbit_le {f g : ℝ → ℝ} (hfm : Measurable f)
    (hgm : Measurable g) {Bf Bg : ℝ} (hbf : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ Bf)
    (hbg : ∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ Bg) (q : ℕ) {t : ℝ} (ht : 0 < t) :
    |∫ x, f x * g (T q x) ∂γ|
      ≤ (t * ∫ x, f x ^ 2 ∂γ + (1 / t) * ∫ x, g x ^ 2 ∂γ) / 2 := by
  have hIfg : Integrable (fun x => f x * g (T q x)) γ :=
    integrable_mul_orbit hfm hgm hbf hbg q
  have hIf2 : Integrable (fun x => f x ^ 2) γ := by
    refine integrable_of_unit_bound (hfm.pow_const 2) (B := Bf ^ 2) fun x hx => ?_
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith [abs_nonneg (f x), hbf x hx]
  have hbg2 : ∀ x ∈ Ioo (0 : ℝ) 1, |g x ^ 2| ≤ Bg ^ 2 := fun x hx => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith [abs_nonneg (g x), hbg x hx]
  have hIg2T : Integrable (fun x => g (T q x) ^ 2) γ :=
    integrable_comp_orbit (hgm.pow_const 2) hbg2 q
  calc |∫ x, f x * g (T q x) ∂γ|
      ≤ ∫ x, |f x * g (T q x)| ∂γ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (t * f x ^ 2 + (1 / t) * g (T q x) ^ 2) / 2 ∂γ := by
        refine integral_mono hIfg.abs
          (((hIf2.const_mul t).add (hIg2T.const_mul (1 / t))).div_const 2) fun x => ?_
        have h := amgm ht (abs_nonneg (f x)) (abs_nonneg (g (T q x)))
        rw [sq_abs, sq_abs] at h
        calc |f x * g (T q x)| = |f x| * |g (T q x)| := abs_mul _ _
          _ ≤ _ := h
    _ = (t * ∫ x, f x ^ 2 ∂γ + (1 / t) * ∫ x, g (T q x) ^ 2 ∂γ) / 2 := by
        rw [integral_div, integral_add (hIf2.const_mul t) (hIg2T.const_mul (1 / t)),
          integral_const_mul, integral_const_mul]
    _ = (t * ∫ x, f x ^ 2 ∂γ + (1 / t) * ∫ x, g x ^ 2 ∂γ) / 2 := by
        rw [integral_sq_comp_orbit g hgm q]

/-! ### The uniform second moment (theorem 1) -/

/-- Uniform second-moment bound for the capped observable:
`∫ capLog u ² dν ≤ 128` for every `u ≥ 0`. -/
theorem integral_capLog_sq_le (u : ℝ) (hu : 0 ≤ u) :
    ∫ x, (capLog u x) ^ 2 ∂Erdos1002.gaussMeasure ≤ 128 := by
  have hlam2 : lyapunov < 2 := lyapunov_lt_two
  have hlam0 : 0 < lyapunov := lyapunov_pos'
  have hcap_int : Integrable (fun x => (capLog u x) ^ 2) γ := by
    refine integrable_of_unit_bound ((measurable_capLog u).pow_const 2)
      (B := (u + 2) ^ 2) fun x hx => ?_
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h := le_trans (abs_capLog_le hu hx.2.le) (by linarith : u + lyapunov ≤ u + 2)
    nlinarith [abs_nonneg (capLog u x)]
  have hlog_int : Integrable (fun x => (Real.log x) ^ 2) γ :=
    integrable_gauss integrableOn_sq_log_unit
  have hpt : ∀ᵐ x ∂γ, (capLog u x) ^ 2 ≤ 8 + 2 * (Real.log x) ^ 2 := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
    have h1 : -lyapunov ≤ capLog u x := neg_lyapunov_le_capLog hu hx.2
    have h2 : capLog u x ≤ flog x := capLog_le_flog hx.1
    have h3 : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2
    unfold flog at h2
    have hf1 : 0 ≤ 2 - Real.log x - capLog u x := by linarith
    have hf2 : 0 ≤ 2 - Real.log x + capLog u x := by linarith
    nlinarith [mul_nonneg hf1 hf2, sq_nonneg (2 + Real.log x)]
  calc ∫ x, (capLog u x) ^ 2 ∂γ
      ≤ ∫ x, (8 + 2 * (Real.log x) ^ 2) ∂γ :=
        integral_mono_ae hcap_int ((integrable_const 8).add (hlog_int.const_mul 2)) hpt
    _ = 8 + 2 * ∫ x, (Real.log x) ^ 2 ∂γ := by
        rw [integral_add (integrable_const _) (hlog_int.const_mul 2),
          integral_const_mul, integral_const]
        simp
    _ ≤ 8 + 2 * 48 := by
        have h := integral_gauss_sq_log_le
        linarith
    _ ≤ 128 := by norm_num

/-! ### The clamped observable: globally bounded and Lipschitz -/

private lemma abs_min_one_sub_min_one (x y : ℝ) : |min x 1 - min y 1| ≤ |x - y| := by
  rcases le_total x 1 with hx | hx <;> rcases le_total y 1 with hy | hy
  · rw [min_eq_left hx, min_eq_left hy]
  · rw [min_eq_left hx, min_eq_right hy, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_right hx, min_eq_left hy, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right hx, min_eq_right hy]
    simp

private def capC (w x : ℝ) : ℝ := capLog w (min x 1)

private lemma measurable_capC (w : ℝ) : Measurable (capC w) :=
  (measurable_capLog w).comp (measurable_id.min measurable_const)

private lemma capC_eq {w x : ℝ} (hx : x ≤ 1) : capC w x = capLog w x := by
  unfold capC
  rw [min_eq_left hx]

private lemma abs_capC_le {w : ℝ} (hw : 0 ≤ w) (x : ℝ) : |capC w x| ≤ w + lyapunov :=
  abs_capLog_le hw (min_le_right x 1)

private lemma neg_lyapunov_le_capC {w : ℝ} (hw : 0 ≤ w) (x : ℝ) :
    -lyapunov ≤ capC w x :=
  neg_lyapunov_le_capLog hw (min_le_right x 1)

private lemma capC_le_cap (w x : ℝ) : capC w x ≤ w := capLog_le_cap w _

private lemma abs_capC_sub_capC_le (w x y : ℝ) :
    |capC w x - capC w y| ≤ Real.exp (w + lyapunov) * |x - y| :=
  le_trans (abs_capLog_sub_capLog_le w _ _)
    (mul_le_mul_of_nonneg_left (abs_min_one_sub_min_one x y) (Real.exp_pos _).le)

private def capF (w x : ℝ) : ℝ := capC w x + lyapunov

/-! ### Covariance bound for the Lipschitz cap -/

private lemma cov_capLog_le {w : ℝ} (hw : 0 ≤ w) (q : ℕ) :
    |(∫ x, capLog w x * capLog w (T q x) ∂γ) - (∫ x, capLog w x ∂γ) ^ 2|
      ≤ (527 / 540 : ℝ) ^ q * (Real.exp (w + lyapunov) * (w + 2)) := by
  have hlam2 : lyapunov < 2 := lyapunov_lt_two
  have hlam0 : 0 < lyapunov := lyapunov_pos'
  have hGb : ∀ x, |capC w x| ≤ w + 2 := fun x =>
    le_trans (abs_capC_le hw x) (by linarith)
  have hFm : Measurable (capF w) := (measurable_capC w).add measurable_const
  have hF0 : Erdos1002.GaussUnitNonnegative (capF w) := by
    intro x _
    unfold capF
    linarith [neg_lyapunov_le_capC hw x]
  have hFA : Erdos1002.GaussUnitUpperBound (w + 4) (capF w) := by
    intro x _
    unfold capF
    linarith [capC_le_cap w x]
  have hFL : Erdos1002.GaussUnitLipschitzBound (Real.exp (w + lyapunov)) (capF w) := by
    intro x _ y _
    have he : capF w x - capF w y = capC w x - capC w y := by unfold capF; ring
    rw [he]
    exact abs_capC_sub_capC_le w x y
  have hcorr := NatExtMixing.gauss_correlation_le (Real.exp_pos (w + lyapunov)).le
    hFm hF0 hFA hFL (measurable_capC w) hGb q
  have hbC : ∀ x ∈ Ioo (0 : ℝ) 1, |capC w x| ≤ w + 2 := fun x _ => hGb x
  have hintC : Integrable (capC w) γ := integrable_of_unit_bound (measurable_capC w) hbC
  have hintCT : Integrable (fun x => capC w (T q x)) γ :=
    integrable_comp_orbit (measurable_capC w) hbC q
  have hintCC : Integrable (fun x => capC w x * capC w (T q x)) γ :=
    integrable_mul_orbit (measurable_capC w) (measurable_capC w) hbC hbC q
  have hstat : ∫ x, capC w (T q x) ∂γ = ∫ x, capC w x ∂γ :=
    integral_comp_orbit_eq (capC w) (measurable_capC w) q
  have hFsplit : ∫ x, capF w x * capC w (T q x) ∂γ
      = (∫ x, capC w x * capC w (T q x) ∂γ) + lyapunov * ∫ x, capC w x ∂γ := by
    rw [show (fun x => capF w x * capC w (T q x))
        = fun x => capC w x * capC w (T q x) + lyapunov * capC w (T q x) from
      funext fun x => by unfold capF; ring]
    rw [integral_add hintCC (hintCT.const_mul lyapunov), integral_const_mul, hstat]
  have hFint : ∫ x, capF w x ∂γ = (∫ x, capC w x ∂γ) + lyapunov := by
    rw [show (fun x => capF w x) = fun x => capC w x + lyapunov from
      funext fun x => rfl]
    rw [integral_add hintC (integrable_const _), integral_const]
    simp
  have hswap1 : ∫ x, capLog w x * capLog w (T q x) ∂γ
      = ∫ x, capC w x * capC w (T q x) ∂γ := by
    refine integral_congr_ae ?_
    filter_upwards [Erdos1002.gaussMeasure_unit_ae, ae_orbit_mem q] with x hx hTx
    rw [capC_eq hx.2, capC_eq hTx.2.le]
  have hswap2 : ∫ x, capLog w x ∂γ = ∫ x, capC w x ∂γ := by
    refine integral_congr_ae ?_
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
    rw [capC_eq hx.2]
  calc |(∫ x, capLog w x * capLog w (T q x) ∂γ) - (∫ x, capLog w x ∂γ) ^ 2|
      = |(∫ x, capF w x * capC w (T q x) ∂γ)
          - (∫ x, capF w x ∂γ) * ∫ x, capC w x ∂γ| := by
        rw [hswap1, hswap2, hFsplit, hFint]
        congr 1
        ring
    _ ≤ (527 / 540 : ℝ) ^ q * Real.exp (w + lyapunov) * (w + 2) := hcorr
    _ = (527 / 540 : ℝ) ^ q * (Real.exp (w + lyapunov) * (w + 2)) := mul_assoc _ _ _

/-! ### The difference of caps: small second moment -/

private def dcap (u w x : ℝ) : ℝ := capLog u x - capLog w x

private lemma measurable_dcap (u w : ℝ) : Measurable (dcap u w) :=
  (measurable_capLog u).sub (measurable_capLog w)

private lemma integral_sq_dcap_le {u w : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) :
    ∫ x, dcap u w x ^ 2 ∂γ ≤ 48 * Real.exp (-(w / 2)) := by
  have hlam0 : 0 < lyapunov := lyapunov_pos'
  have hlam2 : lyapunov < 2 := lyapunov_lt_two
  set ε := Real.exp (-(w + lyapunov)) with hε_def
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hε_def]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hpt : ∀ᵐ x ∂γ, dcap u w x ^ 2
      ≤ (Ioc (0 : ℝ) ε).indicator (fun y => (Real.log y) ^ 2) x := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
    by_cases hxε : x ≤ ε
    · have hmem : x ∈ Ioc (0 : ℝ) ε := ⟨hx.1, hxε⟩
      rw [Set.indicator_of_mem hmem]
      have h1 : capLog w x ≤ capLog u x := capLog_mono_cap hwu x
      have h2 : capLog u x ≤ flog x := capLog_le_flog hx.1
      have h3 : -lyapunov ≤ capLog w x := neg_lyapunov_le_capLog hw hx.2
      have h5 : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2
      unfold flog at h2
      have h4 : dcap u w x ≤ -Real.log x := by unfold dcap; linarith
      have h6 : 0 ≤ dcap u w x := by unfold dcap; linarith
      calc dcap u w x ^ 2 ≤ (-Real.log x) ^ 2 := by nlinarith
        _ = (Real.log x) ^ 2 := by ring
    · push_neg at hxε
      rw [Set.indicator_of_notMem (fun h => (not_le.mpr hxε) h.2)]
      have hlogx : -(w + lyapunov) ≤ Real.log x := by
        have h := Real.log_le_log hε0 hxε.le
        rwa [hε_def, Real.log_exp] at h
      have hflog : flog x ≤ w := by unfold flog; linarith
      have hzero : dcap u w x = 0 := by
        unfold dcap
        rw [capLog_eq_min hx.1, capLog_eq_min hx.1,
          min_eq_left (le_trans hflog hwu), min_eq_left hflog, sub_self]
      rw [hzero]
      norm_num
  have hd_int : Integrable (fun x => dcap u w x ^ 2) γ := by
    refine integrable_of_unit_bound ((measurable_dcap u w).pow_const 2)
      (B := ((u + 2) + (w + 2)) ^ 2) fun x hx => ?_
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have habs : |dcap u w x| ≤ (u + 2) + (w + 2) := by
      unfold dcap
      refine le_trans (abs_sub_le_abs_add_abs _ _) (add_le_add ?_ ?_)
      · exact le_trans (abs_capLog_le (le_trans hw hwu) hx.2.le) (by linarith)
      · exact le_trans (abs_capLog_le hw hx.2.le) (by linarith)
    nlinarith [abs_nonneg (dcap u w x)]
  have hind_int : Integrable ((Ioc (0 : ℝ) ε).indicator fun y => (Real.log y) ^ 2) γ :=
    integrable_gauss (integrableOn_sq_log_unit.indicator measurableSet_Ioc)
  calc ∫ x, dcap u w x ^ 2 ∂γ
      ≤ ∫ x, (Ioc (0 : ℝ) ε).indicator (fun y => (Real.log y) ^ 2) x ∂γ :=
        integral_mono_ae hd_int hind_int hpt
    _ ≤ 48 * Real.sqrt ε := integral_gauss_indicator_sq_log_le hε0 hε1
    _ ≤ 48 * Real.exp (-(w / 2)) := by
        have hsq : Real.sqrt ε = Real.exp (-((w + lyapunov) / 2)) := by
          rw [hε_def, Real.sqrt_eq_rpow, ← Real.exp_mul]
          congr 1
          ring
        rw [hsq]
        have h := Real.exp_le_exp.mpr (show -((w + lyapunov) / 2) ≤ -(w / 2) by linarith)
        linarith

/-! ### The exponential-decay arithmetic -/

private lemma exp_decay_bound {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) (hva : v ≤ a / 2) :
    Real.exp (-a) * (Real.exp (v + lyapunov) * (v + 2))
      ≤ 15 * Real.exp (-(a / 8)) := by
  have hlam2 : lyapunov < 2 := lyapunov_lt_two
  have h1 : Real.exp (v + lyapunov) ≤ Real.exp (a / 2 + 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : v + 2 ≤ 2 * Real.exp (a / 4) := by
    have h := Real.add_one_le_exp (a / 4)
    linarith
  have h3 : Real.exp (-a) * (Real.exp (v + lyapunov) * (v + 2))
      ≤ Real.exp (-a) * (Real.exp (a / 2 + 2) * (2 * Real.exp (a / 4))) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact mul_le_mul h1 h2 (by linarith) (Real.exp_pos _).le
  have e1 : Real.exp (-a) * Real.exp (a / 2 + 2) * Real.exp (a / 4)
      = Real.exp (-a + (a / 2 + 2) + a / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
  have e2 : Real.exp 2 * Real.exp (-(a / 4)) = Real.exp (2 + -(a / 4)) := by
    rw [← Real.exp_add]
  have e3 : -a + (a / 2 + 2) + a / 4 = 2 + -(a / 4) := by ring
  have h4 : Real.exp (-a) * (Real.exp (a / 2 + 2) * (2 * Real.exp (a / 4)))
      = 2 * Real.exp 2 * Real.exp (-(a / 4)) := by
    calc Real.exp (-a) * (Real.exp (a / 2 + 2) * (2 * Real.exp (a / 4)))
        = 2 * (Real.exp (-a) * Real.exp (a / 2 + 2) * Real.exp (a / 4)) := by ring
      _ = 2 * Real.exp (2 + -(a / 4)) := by rw [e1, e3]
      _ = 2 * (Real.exp 2 * Real.exp (-(a / 4))) := by rw [e2]
      _ = 2 * Real.exp 2 * Real.exp (-(a / 4)) := by ring
  have hexp2 : Real.exp 2 ≤ 7.4 := by
    have h := Real.exp_one_lt_d9
    have hpos := Real.exp_pos 1
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith
  have h5 : Real.exp (-(a / 4)) ≤ Real.exp (-(a / 8)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (-a) * (Real.exp (v + lyapunov) * (v + 2))
      ≤ Real.exp (-a) * (Real.exp (a / 2 + 2) * (2 * Real.exp (a / 4))) := h3
    _ = 2 * Real.exp 2 * Real.exp (-(a / 4)) := h4
    _ ≤ 15 * Real.exp (-(a / 8)) := by
        have h6 : 2 * Real.exp 2 ≤ 15 := by linarith
        exact mul_le_mul h6 h5 (Real.exp_pos _).le (by norm_num)

/-! ### Covariance decay, uniform in the cap (theorem 2) -/

/-- **Covariance decay, uniform in the cap.** -/
theorem exists_capLog_cov_decay :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ u : ℝ, 0 ≤ u → ∀ q : ℕ,
      |(∫ x, capLog u x * capLog u (Erdos1002.gaussOrbit q x)
            ∂Erdos1002.gaussMeasure)
          - (∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2|
        ≤ C * Real.exp (-κ * q) := by
  have hc : 0 < Real.log (540 / 527) := Real.log_pos (by norm_num)
  refine ⟨4200, Real.log (540 / 527) / 8, by norm_num, div_pos hc (by norm_num), ?_⟩
  intro u hu q
  set c := Real.log (540 / 527) with hc_def
  have h527 : Real.exp (-c) = 527 / 540 := by
    rw [hc_def, ← Real.log_inv, Real.exp_log (by norm_num)]
    norm_num
  have hρ : ((527 : ℝ) / 540) ^ q = Real.exp (-(c * (q : ℝ))) := by
    rw [← h527, ← Real.exp_nat_mul]
    congr 1
    ring
  have hlam2 : lyapunov < 2 := lyapunov_lt_two
  rcases le_or_gt u (c * (q : ℝ) / 2) with hcase | hcase
  · -- small cap: apply the Lipschitz covariance bound directly at cap `u`
    calc |(∫ x, capLog u x * capLog u (T q x) ∂γ) - (∫ x, capLog u x ∂γ) ^ 2|
        ≤ (527 / 540 : ℝ) ^ q * (Real.exp (u + lyapunov) * (u + 2)) :=
          cov_capLog_le hu q
      _ = Real.exp (-(c * (q : ℝ))) * (Real.exp (u + lyapunov) * (u + 2)) := by
          rw [hρ]
      _ ≤ 15 * Real.exp (-(c * (q : ℝ) / 8)) :=
          exp_decay_bound (mul_nonneg hc.le (Nat.cast_nonneg q)) hu hcase
      _ ≤ 4200 * Real.exp (-(c / 8) * (q : ℝ)) := by
          have h1 : Real.exp (-(c * (q : ℝ) / 8)) = Real.exp (-(c / 8) * (q : ℝ)) := by
            congr 1
            ring
          rw [h1]
          have h2 := Real.exp_pos (-(c / 8) * (q : ℝ))
          linarith
  · -- large cap: split at `w = c q / 2`
    set w := c * (q : ℝ) / 2 with hw_def
    have hw0 : 0 ≤ w := by
      rw [hw_def]
      exact div_nonneg (mul_nonneg hc.le (Nat.cast_nonneg q)) (by norm_num)
    have hwu : w ≤ u := hcase.le
    set E := Real.exp (-(c / 8) * (q : ℝ)) with hE_def
    have hE0 : 0 < E := Real.exp_pos _
    have hE1 : E ≤ 1 := by
      rw [hE_def]
      apply Real.exp_le_one_iff.mpr
      have h0 : 0 ≤ c * (q : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg q)
      linarith
    have hEsq : Real.exp (-(w / 2)) = E ^ 2 := by
      rw [hE_def, hw_def, pow_two, ← Real.exp_add]
      congr 1
      ring
    have hgwm : Measurable (capLog w) := measurable_capLog w
    have hdm : Measurable (dcap u w) := measurable_dcap u w
    have hbw : ∀ x ∈ Ioo (0 : ℝ) 1, |capLog w x| ≤ w + 2 := fun x hx =>
      le_trans (abs_capLog_le hw0 hx.2.le) (by linarith)
    have hbu' : ∀ x ∈ Ioo (0 : ℝ) 1, |capLog u x| ≤ u + 2 := fun x hx =>
      le_trans (abs_capLog_le hu hx.2.le) (by linarith)
    have hbd : ∀ x ∈ Ioo (0 : ℝ) 1, |dcap u w x| ≤ (u + 2) + (w + 2) := fun x hx => by
      unfold dcap
      exact le_trans (abs_sub_le_abs_add_abs _ _) (add_le_add (hbu' x hx) (hbw x hx))
    have hI1 : Integrable (fun x => capLog w x * capLog w (T q x)) γ :=
      integrable_mul_orbit hgwm hgwm hbw hbw q
    have hI2 : Integrable (fun x => capLog w x * dcap u w (T q x)) γ :=
      integrable_mul_orbit hgwm hdm hbw hbd q
    have hI3 : Integrable (fun x => dcap u w x * capLog w (T q x)) γ :=
      integrable_mul_orbit hdm hgwm hbd hbw q
    have hI4 : Integrable (fun x => dcap u w x * dcap u w (T q x)) γ :=
      integrable_mul_orbit hdm hdm hbd hbd q
    have hPexp : ∫ x, capLog u x * capLog u (T q x) ∂γ
        = (∫ x, capLog w x * capLog w (T q x) ∂γ)
          + ((∫ x, capLog w x * dcap u w (T q x) ∂γ)
            + ((∫ x, dcap u w x * capLog w (T q x) ∂γ)
              + ∫ x, dcap u w x * dcap u w (T q x) ∂γ)) := by
      rw [show (fun x => capLog u x * capLog u (T q x))
          = fun x => capLog w x * capLog w (T q x)
            + (capLog w x * dcap u w (T q x)
              + (dcap u w x * capLog w (T q x)
                + dcap u w x * dcap u w (T q x))) from
        funext fun x => by unfold dcap; ring]
      have hI34 : Integrable (fun x => dcap u w x * capLog w (T q x)
          + dcap u w x * dcap u w (T q x)) γ := hI3.add hI4
      have hI234 : Integrable (fun x => capLog w x * dcap u w (T q x)
          + (dcap u w x * capLog w (T q x) + dcap u w x * dcap u w (T q x))) γ :=
        hI2.add hI34
      rw [integral_add hI1 hI234, integral_add hI2 hI34, integral_add hI3 hI4]
    have hIw' : Integrable (capLog w) γ := integrable_of_unit_bound hgwm hbw
    have hId' : Integrable (dcap u w) γ := integrable_of_unit_bound hdm hbd
    have hmexp : ∫ x, capLog u x ∂γ
        = (∫ x, capLog w x ∂γ) + ∫ x, dcap u w x ∂γ := by
      rw [show (fun x => capLog u x) = fun x => capLog w x + dcap u w x from
        funext fun x => by unfold dcap; ring]
      exact integral_add hIw' hId'
    have hIw128 : ∫ x, capLog w x ^ 2 ∂γ ≤ 128 := integral_capLog_sq_le w hw0
    have hIwnn : 0 ≤ ∫ x, capLog w x ^ 2 ∂γ := integral_nonneg fun x => sq_nonneg _
    have hId48 : ∫ x, dcap u w x ^ 2 ∂γ ≤ 48 * E ^ 2 := by
      have h := integral_sq_dcap_le hw0 hwu
      rwa [hEsq] at h
    have hIdnn : 0 ≤ ∫ x, dcap u w x ^ 2 ∂γ := integral_nonneg fun x => sq_nonneg _
    have hB2 := abs_integral_mul_orbit_le (t := E) hgwm hdm hbw hbd q hE0
    have hB3 := abs_integral_mul_orbit_le (t := 1 / E) hdm hgwm hbd hbw q (by positivity)
    have hB4 := abs_integral_mul_orbit_le (t := 1) hdm hdm hbd hbd q one_pos
    have hmw := abs_integral_le_amgm (t := 1) hgwm hbw one_pos
    have hmd := abs_integral_le_amgm (t := 1 / E) hdm hbd (by positivity)
    rw [one_div_one_div] at hB3 hmd
    have hfrac : (1 / E) * (∫ x, dcap u w x ^ 2 ∂γ) ≤ 48 * E := by
      have h := mul_le_mul_of_nonneg_left hId48 (le_of_lt (by positivity : (0 : ℝ) < 1 / E))
      have he : (1 / E) * (48 * E ^ 2) = 48 * E := by
        field_simp
      rw [he] at h
      exact h
    have hEw : E * (∫ x, capLog w x ^ 2 ∂γ) ≤ 128 * E := by
      have h := mul_le_mul_of_nonneg_left hIw128 hE0.le
      linarith
    have hP2 : |∫ x, capLog w x * dcap u w (T q x) ∂γ| ≤ 88 * E := by
      refine le_trans hB2 ?_
      linarith
    have hP3 : |∫ x, dcap u w x * capLog w (T q x) ∂γ| ≤ 88 * E := by
      refine le_trans hB3 ?_
      linarith
    have hE2E : E ^ 2 ≤ E := by nlinarith
    have hP4 : |∫ x, dcap u w x * dcap u w (T q x) ∂γ| ≤ 48 * E := by
      refine le_trans hB4 ?_
      have h : (1 * (∫ x, dcap u w x ^ 2 ∂γ) + (1 / 1) * ∫ x, dcap u w x ^ 2 ∂γ) / 2
          = ∫ x, dcap u w x ^ 2 ∂γ := by ring
      rw [h]
      linarith
    have hmw' : |∫ x, capLog w x ∂γ| ≤ 65 := by
      refine le_trans hmw ?_
      linarith
    have hmd' : |∫ x, dcap u w x ∂γ| ≤ 25 * E := by
      refine le_trans hmd ?_
      linarith
    have hprod : |(∫ x, capLog w x ∂γ) * ∫ x, dcap u w x ∂γ| ≤ 1625 * E := by
      rw [abs_mul]
      calc |∫ x, capLog w x ∂γ| * |∫ x, dcap u w x ∂γ| ≤ 65 * (25 * E) :=
            mul_le_mul hmw' hmd' (abs_nonneg _) (by norm_num)
        _ = 1625 * E := by ring
    have hmd2 : (∫ x, dcap u w x ∂γ) ^ 2 ≤ 625 * E := by
      nlinarith [hmd', abs_nonneg (∫ x, dcap u w x ∂γ),
        sq_abs (∫ x, dcap u w x ∂γ), hE2E, hE0.le]
    have hDw : |(∫ x, capLog w x * capLog w (T q x) ∂γ)
        - (∫ x, capLog w x ∂γ) ^ 2| ≤ 15 * E := by
      refine le_trans (cov_capLog_le hw0 q) ?_
      rw [hρ]
      have h15 := exp_decay_bound (a := c * (q : ℝ)) (v := w)
        (mul_nonneg hc.le (Nat.cast_nonneg q)) hw0 (le_of_eq hw_def)
      have hEeq : Real.exp (-(c * (q : ℝ) / 8)) = E := by
        rw [hE_def]
        congr 1
        ring
      rw [hEeq] at h15
      exact h15
    have hkey : (∫ x, capLog u x * capLog u (T q x) ∂γ)
        - (∫ x, capLog u x ∂γ) ^ 2
        = ((∫ x, capLog w x * capLog w (T q x) ∂γ) - (∫ x, capLog w x ∂γ) ^ 2)
          + (((∫ x, capLog w x * dcap u w (T q x) ∂γ)
              - (∫ x, capLog w x ∂γ) * ∫ x, dcap u w x ∂γ)
            + (((∫ x, dcap u w x * capLog w (T q x) ∂γ)
                - (∫ x, capLog w x ∂γ) * ∫ x, dcap u w x ∂γ)
              + ((∫ x, dcap u w x * dcap u w (T q x) ∂γ)
                - (∫ x, dcap u w x ∂γ) ^ 2))) := by
      rw [hPexp, hmexp]
      ring
    rw [hkey, abs_le]
    obtain ⟨h1l, h1u⟩ := abs_le.mp hDw
    obtain ⟨h2l, h2u⟩ := abs_le.mp hP2
    obtain ⟨h3l, h3u⟩ := abs_le.mp hP3
    obtain ⟨h4l, h4u⟩ := abs_le.mp hP4
    obtain ⟨h5l, h5u⟩ := abs_le.mp hprod
    have h6l : 0 ≤ (∫ x, dcap u w x ∂γ) ^ 2 := sq_nonneg _
    constructor
    · linarith
    · linarith

/-! ### Block second moments (theorem 3) -/

/-- **Block second moments are linear in the block length, uniformly in the
cap and the block position.** -/
theorem exists_block_sq_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ u : ℝ, 0 ≤ u → ∀ t ℓ : ℕ,
      ∫ x, (∑ i ∈ Finset.range ℓ,
            (capLog u (Erdos1002.gaussOrbit (t + i) x)
              - ∫ y, capLog u y ∂Erdos1002.gaussMeasure)) ^ 2
          ∂Erdos1002.gaussMeasure
        ≤ C₀ * ℓ := by
  obtain ⟨C, κ, hC, hκ, hcov⟩ := exists_capLog_cov_decay
  set r := Real.exp (-κ) with hr_def
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr_def, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h1r : 0 < 1 - r := by linarith
  have hC₀ : 0 < C * (2 / (1 - r)) + 1 := by
    have h := mul_pos hC (div_pos (by norm_num : (0 : ℝ) < 2) h1r)
    linarith
  refine ⟨C * (2 / (1 - r)) + 1, hC₀, ?_⟩
  intro u hu t ℓ
  have hlam2 : lyapunov < 2 := lyapunov_lt_two
  set m := ∫ y, capLog u y ∂Erdos1002.gaussMeasure with hm_def
  have hbu : ∀ x ∈ Ioo (0 : ℝ) 1, |capLog u x| ≤ u + 2 := fun x hx =>
    le_trans (abs_capLog_le hu hx.2.le) (by linarith)
  have hbm : ∀ x ∈ Ioo (0 : ℝ) 1, |capLog u x - m| ≤ (u + 2) + |m| := fun x hx =>
    le_trans (abs_sub_le_abs_add_abs _ _) (add_le_add (hbu x hx) le_rfl)
  have hgm : Measurable (fun y => capLog u y - m) :=
    (measurable_capLog u).sub measurable_const
  -- geometric sums
  have hgeom : ∀ n : ℕ, (∑ d ∈ Finset.range n, r ^ d) ≤ 1 / (1 - r) := by
    intro n
    rw [le_div_iff₀ h1r]
    have h := geom_sum_mul r n
    have hrn : 0 ≤ r ^ n := pow_nonneg hr0.le n
    nlinarith [h, hrn]
  -- inner sums over distances
  have hinner : ∀ i ∈ Finset.range ℓ,
      (∑ j ∈ Finset.range ℓ, r ^ Nat.dist i j) ≤ 2 / (1 - r) := by
    intro i _
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range ℓ) (fun j => j ≤ i)]
    have hs1 : (∑ j ∈ (Finset.range ℓ).filter (fun j => j ≤ i), r ^ Nat.dist i j)
        ≤ 1 / (1 - r) := by
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hj).2])]
      have hinj : Set.InjOn (fun j => i - j)
          ((Finset.range ℓ).filter (fun j => j ≤ i)) := by
        intro x hx y hy hxy
        have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
        simp only at hxy
        omega
      have himg : ∑ d ∈ ((Finset.range ℓ).filter (fun j => j ≤ i)).image
            (fun j => i - j), r ^ d
          = ∑ j ∈ (Finset.range ℓ).filter (fun j => j ≤ i), r ^ (i - j) :=
        Finset.sum_image hinj
      rw [← himg]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun d _ _ => pow_nonneg hr0.le d)) (hgeom (i + 1))
      intro d hd
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨j, ⟨_, _⟩, rfl⟩ := hd
      exact Finset.mem_range.mpr (by omega)
    have hs2 : (∑ j ∈ (Finset.range ℓ).filter (fun j => ¬j ≤ i), r ^ Nat.dist i j)
        ≤ 1 / (1 - r) := by
      rw [Finset.sum_congr rfl (fun j hj => by
        have hj' := (Finset.mem_filter.mp hj).2
        rw [Nat.dist_eq_sub_of_le (by omega : i ≤ j)])]
      have hinj : Set.InjOn (fun j => j - i)
          ((Finset.range ℓ).filter (fun j => ¬j ≤ i)) := by
        intro x hx y hy hxy
        have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
        simp only at hxy
        omega
      have himg : ∑ d ∈ ((Finset.range ℓ).filter (fun j => ¬j ≤ i)).image
            (fun j => j - i), r ^ d
          = ∑ j ∈ (Finset.range ℓ).filter (fun j => ¬j ≤ i), r ^ (j - i) :=
        Finset.sum_image hinj
      rw [← himg]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun d _ _ => pow_nonneg hr0.le d)) (hgeom ℓ)
      intro d hd
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨j, ⟨hj, _⟩, rfl⟩ := hd
      exact Finset.mem_range.mpr (by omega)
    calc (∑ j ∈ (Finset.range ℓ).filter (fun j => j ≤ i), r ^ Nat.dist i j)
          + ∑ j ∈ (Finset.range ℓ).filter (fun j => ¬j ≤ i), r ^ Nat.dist i j
        ≤ 1 / (1 - r) + 1 / (1 - r) := add_le_add hs1 hs2
      _ = 2 / (1 - r) := by ring
  -- stationarity: the pair at positions (s, s+d) has the distance-d covariance
  have hpair : ∀ s d : ℕ,
      ∫ x, (capLog u (T s x) - m) * (capLog u (T (s + d) x) - m) ∂γ
        = (∫ x, capLog u x * capLog u (T d x) ∂γ) - m ^ 2 := by
    intro s d
    have hφm : Measurable (fun y => (capLog u y - m) * (capLog u (T d y) - m)) :=
      ((measurable_capLog u).sub measurable_const).mul
        (((measurable_capLog u).comp (Erdos1002.measurable_gaussOrbit d)).sub
          measurable_const)
    have horb : ∀ x, T (s + d) x = T d (T s x) := fun x => by
      rw [add_comm s d]
      exact gaussOrbit_add d s x
    have h1 : ∫ x, (capLog u (T s x) - m) * (capLog u (T (s + d) x) - m) ∂γ
        = ∫ x, (fun y => (capLog u y - m) * (capLog u (T d y) - m)) (T s x) ∂γ := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (capLog u (T s x) - m) * (capLog u (T (s + d) x) - m)
          = (capLog u (T s x) - m) * (capLog u (T d (T s x)) - m)
      rw [horb x]
    rw [h1, integral_comp_gaussOrbit s _ hφm.aestronglyMeasurable]
    have hint1 : Integrable (fun y => capLog u y * capLog u (T d y)) γ :=
      integrable_mul_orbit (measurable_capLog u) (measurable_capLog u) hbu hbu d
    have hint2 : Integrable (fun y => capLog u (T d y)) γ :=
      integrable_comp_orbit (measurable_capLog u) hbu d
    have hint3 : Integrable (capLog u) γ := integrable_of_unit_bound (measurable_capLog u) hbu
    have hexp : (fun y => (capLog u y - m) * (capLog u (T d y) - m))
        = fun y => (capLog u y * capLog u (T d y) + m ^ 2)
            - (m * capLog u (T d y) + m * capLog u y) := funext fun y => by ring
    have hconst : ∫ (_x : ℝ), m ^ 2 ∂γ = m ^ 2 := by simp
    have hintA : Integrable (fun y => capLog u y * capLog u (T d y) + m ^ 2) γ :=
      hint1.add (integrable_const _)
    have hintB : Integrable (fun y => m * capLog u (T d y) + m * capLog u y) γ :=
      (hint2.const_mul m).add (hint3.const_mul m)
    rw [hexp, integral_sub hintA hintB,
      integral_add hint1 (integrable_const _),
      integral_add (hint2.const_mul m) (hint3.const_mul m),
      integral_const_mul, integral_const_mul, hconst,
      integral_comp_orbit_eq (capLog u) (measurable_capLog u) d]
    rw [← hm_def]
    ring
  -- the per-pair covariance bound
  have hpairbound : ∀ i j : ℕ,
      |∫ x, (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m) ∂γ|
        ≤ C * r ^ Nat.dist i j := by
    have haux : ∀ i j : ℕ, i ≤ j →
        |∫ x, (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m) ∂γ|
          ≤ C * r ^ (j - i) := by
      intro i j hij
      have hj : t + j = (t + i) + (j - i) := by omega
      rw [hj, hpair (t + i) (j - i)]
      have hcov' := hcov u hu (j - i)
      rw [← hm_def] at hcov'
      refine le_trans hcov' (le_of_eq ?_)
      have hre : Real.exp (-κ * ((j - i : ℕ) : ℝ)) = r ^ (j - i) := by
        rw [hr_def, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [hre]
    intro i j
    rcases le_total i j with hij | hij
    · rw [Nat.dist_eq_sub_of_le hij]
      exact haux i j hij
    · rw [Nat.dist_eq_sub_of_le_right hij]
      rw [show (fun x => (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m))
          = fun x => (capLog u (T (t + j) x) - m) * (capLog u (T (t + i) x) - m) from
        funext fun x => mul_comm _ _]
      exact haux j i hij
  -- assemble
  have hIij : ∀ i j : ℕ, Integrable
      (fun x => (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m)) γ :=
    fun i j => integrable_orbit_mul_orbit hgm hbm (t + i) (t + j)
  have hsq : ∀ x : ℝ, (∑ i ∈ Finset.range ℓ, (capLog u (T (t + i) x) - m)) ^ 2
      = ∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range ℓ,
          (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m) := fun x => by
    rw [pow_two, Finset.sum_mul_sum]
  calc ∫ x, (∑ i ∈ Finset.range ℓ, (capLog u (T (t + i) x) - m)) ^ 2 ∂γ
      = ∫ x, (∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range ℓ,
          (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m)) ∂γ :=
        integral_congr_ae (ae_of_all _ hsq)
    _ = ∑ i ∈ Finset.range ℓ, ∫ x, (∑ j ∈ Finset.range ℓ,
          (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m)) ∂γ :=
        integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hIij i j
    _ = ∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range ℓ, ∫ x,
          (capLog u (T (t + i) x) - m) * (capLog u (T (t + j) x) - m) ∂γ :=
        Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => hIij i j
    _ ≤ ∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range ℓ, C * r ^ Nat.dist i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          le_trans (le_abs_self _) (hpairbound i j)
    _ = ∑ i ∈ Finset.range ℓ, C * ∑ j ∈ Finset.range ℓ, r ^ Nat.dist i j :=
        Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i ∈ Finset.range ℓ, C * (2 / (1 - r)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hinner i hi) hC.le
    _ = C * (2 / (1 - r)) * ℓ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ (C * (2 / (1 - r)) + 1) * ℓ := by
        have h0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
        nlinarith

end

end LargeDeviation

end Kwon1002
