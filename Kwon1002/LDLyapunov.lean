import Kwon1002.LDObservable
import Mathlib.NumberTheory.ZetaValues

/-!
# Large deviations, stage A2: the Lévy constant is the Gauss mean of `−log`

`∫ (−log x) dν = π²/(12 log 2) = lyapunov` for the Gauss measure `ν`
(density `1/((1+x) log 2)` on `(0,1]`).  Route: on `(0,1)`,
`(−log x)/(1+x) = Σ_{k≥0} (−log x)(1 − x) x^{2k}` with **nonnegative**
terms, `∫₀¹ (−log x) x^n dx = 1/(n+1)²`, and
`Σ_k [1/(2k+1)² − 1/(2k+2)²] = π²/12` from `hasSum_zeta_two`.

Also: the second moment `∫ log² dν ≤ 48` and its tail
`∫_{(0,e^{−t})} log² dν ≤ 48 e^{−t/2}` (via `log²(1/x) ≤ 16/√x`), the
capped-mean bracket `−e^{−u} ≤ ∫ capLog u dν ≤ 0`, and the excess mean
`∫ (flog − capLog u) dν ≤ e^{−u}`.
-/

open Set MeasureTheory

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-! ### Pointwise elementary bounds -/

private lemma neg_log_le_rpow {x : ℝ} (hx0 : 0 < x) :
    -Real.log x ≤ 4 * x ^ (-(1 / 4) : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (-(1 / 4) : ℝ))
  rw [Real.log_rpow hx0] at h
  have hp : (0 : ℝ) < x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
  linarith

private lemma sq_log_le_rpow {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (Real.log x) ^ 2 ≤ 16 * x ^ (-(1 / 2) : ℝ) := by
  have h := neg_log_le_rpow hx0
  have hl : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx0.le hx1)
  have hsq : (x ^ (-(1 / 4) : ℝ)) ^ 2 = x ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast (x ^ (-(1 / 4) : ℝ)) 2, ← Real.rpow_mul hx0.le]
    norm_num
  have hmul : (-Real.log x) * (-Real.log x)
      ≤ (4 * x ^ (-(1 / 4) : ℝ)) * (4 * x ^ (-(1 / 4) : ℝ)) :=
    mul_le_mul h h hl (by positivity)
  calc (Real.log x) ^ 2 = (-Real.log x) * (-Real.log x) := by ring
    _ ≤ (4 * x ^ (-(1 / 4) : ℝ)) * (4 * x ^ (-(1 / 4) : ℝ)) := hmul
    _ = 16 * (x ^ (-(1 / 4) : ℝ)) ^ 2 := by ring
    _ = 16 * x ^ (-(1 / 2) : ℝ) := by rw [hsq]

/-! ### Lebesgue integrability on the unit interval -/

private lemma integrableOn_rpow_unit {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun x : ℝ => x ^ r) (Ioc (0 : ℝ) 1) volume :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)

private lemma integrableOn_neg_log_unit :
    IntegrableOn (fun x : ℝ => -Real.log x) (Ioc (0 : ℝ) 1) volume := by
  have h : IntegrableOn Real.log (Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      intervalIntegral.intervalIntegrable_log'
  exact h.neg

private lemma integrableOn_sq_log_unit :
    IntegrableOn (fun x : ℝ => (Real.log x) ^ 2) (Ioc (0 : ℝ) 1) volume := by
  apply Integrable.mono'
    ((integrableOn_rpow_unit (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul 16)
    ((Real.measurable_log.pow_const 2).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_log_le_rpow hx.1 hx.2

private lemma integrableOn_neg_log_mul_pow (n : ℕ) :
    IntegrableOn (fun x : ℝ => (-Real.log x) * x ^ n) (Ioc (0 : ℝ) 1) volume := by
  apply Integrable.mono' integrableOn_neg_log_unit
    ((by fun_prop : Measurable fun x : ℝ => (-Real.log x) * x ^ n).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hl : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)
  have hp0 : 0 ≤ x ^ n := pow_nonneg hx.1.le n
  have hp1 : x ^ n ≤ 1 := pow_le_one₀ hx.1.le hx.2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hl, abs_of_nonneg hp0]
  nlinarith

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

/-- `−log` is Gauss-integrable. -/
theorem integrable_neg_log_gauss :
    Integrable (fun x => -Real.log x) Erdos1002.gaussMeasure :=
  integrable_gauss integrableOn_neg_log_unit

/-- `log²` is Gauss-integrable. -/
theorem integrable_sq_log_gauss :
    Integrable (fun x => (Real.log x) ^ 2) Erdos1002.gaussMeasure :=
  integrable_gauss integrableOn_sq_log_unit

/-! ### The moment integrals `∫₀¹ (−log x)·xⁿ dx = 1/(n+1)²` -/

private lemma moment_integral (n : ℕ) :
    ∫ x in Ioo (0 : ℝ) 1, (-Real.log x) * x ^ n = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun y : ℝ => y ^ (n + 1) * (-Real.log y) / ((n : ℝ) + 1)
        + y ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      ((-Real.log x) * x ^ n) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 : HasDerivAt (fun y : ℝ => y ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
      have h := hasDerivAt_pow (n + 1) x
      push_cast at h
      simpa using h
    have h2 : HasDerivAt (fun y : ℝ => -Real.log y) (-x⁻¹) x :=
      (Real.hasDerivAt_log hx0).neg
    have h5 := ((h1.mul h2).div_const ((n : ℝ) + 1)).add
      (h1.div_const (((n : ℝ) + 1) ^ 2))
    convert h5 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun y : ℝ => (-Real.log y) * y ^ n) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrableOn_neg_log_mul_pow n
  have ht0 : Filter.Tendsto
      (fun y : ℝ => y ^ (n + 1) * (-Real.log y) / ((n : ℝ) + 1)
        + y ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hpow : Filter.Tendsto (fun y : ℝ => Real.log y * y ^ (n + 1))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hrp := tendsto_log_mul_rpow_nhdsGT_zero
        (r := (n : ℝ) + 1) (by positivity)
      apply hrp.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have hterm1 : Filter.Tendsto
        (fun y : ℝ => y ^ (n + 1) * (-Real.log y) / ((n : ℝ) + 1))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h := (hpow.neg).div_const ((n : ℝ) + 1)
      simp only [neg_zero, zero_div] at h
      exact h.congr fun y => by ring
    have hterm2 : Filter.Tendsto
        (fun y : ℝ => y ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hc : Continuous (fun y : ℝ => y ^ (n + 1) / ((n : ℝ) + 1) ^ 2) := by
        fun_prop
      have h := hc.tendsto 0
      have h0 : (0 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 2 = 0 := by
        rw [zero_pow (Nat.succ_ne_zero n), zero_div]
      rw [h0] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    simpa using hterm1.add hterm2
  have ht1 : Filter.Tendsto
      (fun y : ℝ => y ^ (n + 1) * (-Real.log y) / ((n : ℝ) + 1)
        + y ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (nhdsWithin 1 (Iio 1)) (nhds (1 / ((n : ℝ) + 1) ^ 2)) := by
    have hpow : ContinuousAt (fun y : ℝ => y ^ (n + 1)) 1 :=
      (continuous_pow (n + 1)).continuousAt
    have hlog : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    have hc : ContinuousAt
        (fun y : ℝ => y ^ (n + 1) * (-Real.log y) / ((n : ℝ) + 1)
          + y ^ (n + 1) / ((n : ℝ) + 1) ^ 2) 1 :=
      ((hpow.mul hlog.neg).div_const _).add (hpow.div_const _)
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa [Real.log_one] using hc.tendsto
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    zero_lt_one hderiv hint ht0 ht1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    key, sub_zero]

/-! ### The series `Σ [1/(2k+1)² − 1/(2k+2)²] = π²/12` -/

private lemma inv_sq_diff_nonneg (k : ℕ) :
    0 ≤ 1 / (2 * (k : ℝ) + 1) ^ 2 - 1 / (2 * (k : ℝ) + 2) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (0 : ℝ) < (2 * (k : ℝ) + 1) ^ 2 := by positivity
  have h3 : (2 * (k : ℝ) + 1) ^ 2 ≤ (2 * (k : ℝ) + 2) ^ 2 := by nlinarith
  have := one_div_le_one_div_of_le h1 h3
  linarith

private lemma hasSum_inv_sq_diff :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2 - 1 / (2 * (k : ℝ) + 2) ^ 2)
      (Real.pi ^ 2 / 12) := by
  have h6 : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
    hasSum_zeta_two
  have hg : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 24) := by
    have h := h6.mul_left (1 / 4)
    have hfun : (fun k : ℕ => (1 / 4) * ((1 : ℝ) / (k : ℝ) ^ 2))
        = fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2 := by
      funext k; push_cast; ring
    have hval : (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 24 := by ring
    rw [hfun, hval] at h
    exact h
  have hodd_sum : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by
      dsimp only at hab
      omega
    exact h6.summable.comp_injective hi
  obtain ⟨T, hT⟩ := hodd_sum
  have hcomb : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 24 + T) :=
    HasSum.even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) hg hT
  have hTval : T = Real.pi ^ 2 / 6 - Real.pi ^ 2 / 24 := by
    have := h6.unique hcomb
    linarith
  have he2 : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * (k + 1) : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 24) := by
    have h := (hasSum_nat_add_iff'
      (f := fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) 1).mpr hg
    simpa using h
  have hodd : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 6 - Real.pi ^ 2 / 24) := hTval ▸ hT
  have hdiff := hodd.sub he2
  have hfun : (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2
        - (1 : ℝ) / ((2 * (k + 1) : ℕ) : ℝ) ^ 2)
      = fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2 - 1 / (2 * (k : ℝ) + 2) ^ 2 := by
    funext k; push_cast; ring
  have hval : Real.pi ^ 2 / 6 - Real.pi ^ 2 / 24 - Real.pi ^ 2 / 24
      = Real.pi ^ 2 / 12 := by ring
  rw [hfun, hval] at hdiff
  exact hdiff

/-! ### The pointwise geometric expansion of `(−log x)/(1+x)` -/

private lemma hasSum_pointwise {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => (-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1))
      ((-Real.log x) / (1 + x)) := by
  have hsq0 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hsq1 : x ^ 2 < 1 := by nlinarith
  have h := (hasSum_geometric_of_lt_one hsq0 hsq1).mul_left ((-Real.log x) * (1 - x))
  have hfun : (fun k : ℕ => ((-Real.log x) * (1 - x)) * (x ^ 2) ^ k)
      = fun k : ℕ => (-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1) := by
    funext k
    rw [← pow_mul]
    ring
  have hne1 : (1 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
  have hne2 : (1 : ℝ) + x ≠ 0 := ne_of_gt (by linarith)
  have hval : ((-Real.log x) * (1 - x)) * ((1 : ℝ) - x ^ 2)⁻¹
      = (-Real.log x) / (1 + x) := by
    rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring]
    field_simp
  rw [hfun, hval] at h
  exact h

/-! ### The Gauss lintegral of `−log` -/

private lemma lintegral_neg_log_gauss :
    ∫⁻ x, ENNReal.ofReal (-Real.log x) ∂Erdos1002.gaussMeasure
      = ENNReal.ofReal lyapunov := by
  have hmg : Measurable fun x : ℝ => ENNReal.ofReal (-Real.log x) :=
    Real.measurable_log.neg.ennreal_ofReal
  rw [Erdos1002.gaussMeasure_eq_volume_withDensity,
    lintegral_withDensity_eq_lintegral_mul volume Erdos1002.measurable_gaussDensity hmg]
  have hind : (Erdos1002.gaussDensity * fun x => ENNReal.ofReal (-Real.log x))
      = (Ioc (0 : ℝ) 1).indicator
          (fun x => Erdos1002.gaussDensityCore x * ENNReal.ofReal (-Real.log x)) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp only [Pi.mul_apply, Erdos1002.gaussDensity, Set.indicator_of_mem hx]
    · simp only [Pi.mul_apply, Erdos1002.gaussDensity, Set.indicator_of_notMem hx,
        zero_mul]
  rw [hind, lintegral_indicator measurableSet_Ioc,
    setLIntegral_congr ((Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1)).symm)]
  have hpt : EqOn
      (fun x => Erdos1002.gaussDensityCore x * ENNReal.ofReal (-Real.log x))
      (fun x => ENNReal.ofReal (1 / Real.log 2) * ∑' k : ℕ,
        ENNReal.ofReal ((-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1)))
      (Ioo (0 : ℝ) 1) := by
    intro x hx
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1x : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have hl : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2.le)
    have hden : (0 : ℝ) ≤ 1 / (Real.log 2 * (1 + x)) :=
      div_nonneg zero_le_one (by positivity)
    have hs := hasSum_pointwise hx.1 hx.2
    have hnn : ∀ k : ℕ,
        0 ≤ (-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1) := by
      intro k
      have hp : x ^ (2 * k + 1) ≤ x ^ (2 * k) :=
        pow_le_pow_of_le_one hx.1.le hx.2.le (Nat.le_succ (2 * k))
      nlinarith [mul_nonneg hl (sub_nonneg.mpr hp)]
    calc Erdos1002.gaussDensityCore x * ENNReal.ofReal (-Real.log x)
        = ENNReal.ofReal (1 / (Real.log 2 * (1 + x)) * (-Real.log x)) := by
          rw [show Erdos1002.gaussDensityCore x
              = ENNReal.ofReal (1 / (Real.log 2 * (1 + x))) from rfl,
            ← ENNReal.ofReal_mul hden]
      _ = ENNReal.ofReal (1 / Real.log 2 * ((-Real.log x) / (1 + x))) := by
          congr 1
          field_simp
      _ = ENNReal.ofReal (1 / Real.log 2) * ENNReal.ofReal ((-Real.log x) / (1 + x)) :=
          ENNReal.ofReal_mul (div_nonneg zero_le_one hlog2.le)
      _ = ENNReal.ofReal (1 / Real.log 2) * ∑' k : ℕ,
            ENNReal.ofReal ((-Real.log x) * x ^ (2 * k)
              - (-Real.log x) * x ^ (2 * k + 1)) := by
          rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hs.summable]
  rw [setLIntegral_congr_fun measurableSet_Ioo hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_tsum (fun k : ℕ =>
      ((by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal
        ((-Real.log x) * x ^ (2 * k)
          - (-Real.log x) * x ^ (2 * k + 1)))).aemeasurable)]
  have hterm : ∀ k : ℕ,
      ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal
          ((-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1))
        = ENNReal.ofReal (1 / (2 * (k : ℝ) + 1) ^ 2 - 1 / (2 * (k : ℝ) + 2) ^ 2) := by
    intro k
    have hint1 : IntegrableOn (fun x : ℝ => (-Real.log x) * x ^ (2 * k))
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_neg_log_mul_pow (2 * k)).mono_set Ioo_subset_Ioc_self
    have hint2 : IntegrableOn (fun x : ℝ => (-Real.log x) * x ^ (2 * k + 1))
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_neg_log_mul_pow (2 * k + 1)).mono_set Ioo_subset_Ioc_self
    have hnn' : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x => (-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hl : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2.le)
      have hp : x ^ (2 * k + 1) ≤ x ^ (2 * k) :=
        pow_le_pow_of_le_one hx.1.le hx.2.le (Nat.le_succ (2 * k))
      simp only [Pi.zero_apply]
      nlinarith [mul_nonneg hl (sub_nonneg.mpr hp)]
    have hintd : IntegrableOn
        (fun x : ℝ => (-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1))
        (Ioo (0 : ℝ) 1) volume := hint1.sub hint2
    rw [← ofReal_integral_eq_lintegral_ofReal hintd hnn']
    congr 1
    rw [integral_sub hint1 hint2, moment_integral (2 * k), moment_integral (2 * k + 1)]
    push_cast
    ring
  rw [tsum_congr hterm,
    ← ENNReal.ofReal_tsum_of_nonneg inv_sq_diff_nonneg hasSum_inv_sq_diff.summable,
    hasSum_inv_sq_diff.tsum_eq,
    ← ENNReal.ofReal_mul (div_nonneg zero_le_one (Real.log_pos (by norm_num)).le)]
  congr 1
  rw [lyapunov]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-- **The Lévy constant is the Gauss mean of `−log`.** -/
theorem integral_neg_log_gauss :
    ∫ x, -Real.log x ∂Erdos1002.gaussMeasure = lyapunov := by
  have hnn : 0 ≤ᵐ[Erdos1002.gaussMeasure] fun x => -Real.log x := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
    exact neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
      Real.measurable_log.neg.aestronglyMeasurable,
    lintegral_neg_log_gauss, ENNReal.toReal_ofReal lyapunov_pos'.le]

/-- Second moment bound. -/
theorem integral_sq_log_gauss_le :
    ∫ x, (Real.log x) ^ 2 ∂Erdos1002.gaussMeasure ≤ 48 := by
  have h1 : ∫ x, (Real.log x) ^ 2 ∂Erdos1002.gaussMeasure
      ≤ ∫ x, (Real.log x) ^ 2
          ∂(ENNReal.ofReal (3 / 2) • volume.restrict (Ioc (0 : ℝ) 1)) :=
    integral_mono_measure gaussMeasure_le_smul
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (integrableOn_sq_log_unit.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    smul_eq_mul] at h1
  have h2 : ∫ x in Ioc (0 : ℝ) 1, (Real.log x) ^ 2
      ≤ ∫ x in Ioc (0 : ℝ) 1, 16 * x ^ (-(1 / 2) : ℝ) := by
    apply setIntegral_mono_on integrableOn_sq_log_unit
      ((integrableOn_rpow_unit (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul 16)
      measurableSet_Ioc
    intro x hx
    exact sq_log_le_rpow hx.1 hx.2
  have h3 : ∫ x in Ioc (0 : ℝ) 1, 16 * x ^ (-(1 / 2) : ℝ) = 32 := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      Real.one_rpow, Real.zero_rpow (by norm_num : (-(1 / 2) + 1 : ℝ) ≠ 0)]
    norm_num
  linarith

/-- Second-moment tail: `∫_{(0,e^{−t})} log² dν ≤ 48 e^{−t/2}`. -/
theorem integral_sq_log_tail_le (t : ℝ) (ht : 0 ≤ t) :
    ∫ x in Ioo (0 : ℝ) (Real.exp (-t)), (Real.log x) ^ 2 ∂Erdos1002.gaussMeasure
      ≤ 48 * Real.exp (-t / 2) := by
  set ε := Real.exp (-t) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hε, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsub : Ioo (0 : ℝ) ε ⊆ Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨hx.1, (le_of_lt hx.2).trans hε1⟩
  have hOn : IntegrableOn (fun x : ℝ => (Real.log x) ^ 2) (Ioo (0 : ℝ) ε) volume :=
    integrableOn_sq_log_unit.mono_set hsub
  have hrOn : IntegrableOn (fun x : ℝ => 16 * x ^ (-(1 / 2) : ℝ))
      (Ioo (0 : ℝ) ε) volume := by
    have hc : IntegrableOn (fun x : ℝ => 16 * x ^ (-(1 / 2) : ℝ))
        (Ioc (0 : ℝ) 1) volume :=
      (integrableOn_rpow_unit (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul 16
    exact hc.mono_set hsub
  have hle : Erdos1002.gaussMeasure.restrict (Ioo (0 : ℝ) ε)
      ≤ ENNReal.ofReal (3 / 2) • volume.restrict (Ioo (0 : ℝ) ε) := by
    have h := Measure.restrict_mono (subset_refl (Ioo (0 : ℝ) ε)) gaussMeasure_le_smul
    rwa [Measure.restrict_smul, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr hsub] at h
  have h1 : ∫ x in Ioo (0 : ℝ) ε, (Real.log x) ^ 2 ∂Erdos1002.gaussMeasure
      ≤ ∫ x, (Real.log x) ^ 2
          ∂(ENNReal.ofReal (3 / 2) • volume.restrict (Ioo (0 : ℝ) ε)) :=
    integral_mono_measure hle (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hOn.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    smul_eq_mul] at h1
  have h2 : ∫ x in Ioo (0 : ℝ) ε, (Real.log x) ^ 2
      ≤ ∫ x in Ioo (0 : ℝ) ε, 16 * x ^ (-(1 / 2) : ℝ) := by
    apply setIntegral_mono_on hOn hrOn measurableSet_Ioo
    intro x hx
    exact sq_log_le_rpow hx.1 ((le_of_lt hx.2).trans hε1)
  have h3 : ∫ x in Ioo (0 : ℝ) ε, 16 * x ^ (-(1 / 2) : ℝ) = 32 * Real.exp (-t / 2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε0.le,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    have hεr : ε ^ (-(1 / 2) + 1 : ℝ) = Real.exp (-t / 2) := by
      rw [hε, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [hεr, Real.zero_rpow (by norm_num : (-(1 / 2) + 1 : ℝ) ≠ 0)]
    ring
  linarith

/-! ### The centered observable -/

private lemma integrable_flog_gauss : Integrable flog Erdos1002.gaussMeasure := by
  have h : Integrable (fun x : ℝ => -Real.log x - lyapunov) Erdos1002.gaussMeasure :=
    integrable_neg_log_gauss.sub (integrable_const _)
  exact h

/-- The centered observable has Gauss mean zero. -/
theorem integral_flog_gauss :
    ∫ x, flog x ∂Erdos1002.gaussMeasure = 0 := by
  have h : ∫ x, flog x ∂Erdos1002.gaussMeasure
      = ∫ x, (-Real.log x - lyapunov) ∂Erdos1002.gaussMeasure := rfl
  rw [h, integral_sub integrable_neg_log_gauss (integrable_const _),
    integral_neg_log_gauss, integral_const]
  simp

/-- The capped observable is Gauss-integrable. -/
theorem integrable_capLog_gauss (u : ℝ) :
    Integrable (capLog u) Erdos1002.gaussMeasure := by
  apply Integrable.mono' (integrable_flog_gauss.abs.add (integrable_const |u|))
    ((measurable_capLog u).aestronglyMeasurable)
  filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
  rw [Real.norm_eq_abs, capLog_eq_min hx.1]
  simp only [Pi.add_apply]
  rcases min_choice (flog x) u with h | h <;> rw [h]
  · linarith [abs_nonneg u]
  · linarith [abs_nonneg (flog x), le_abs_self u]

/-- Mean of the excess `flog − capLog u = (flog − u)⁺`:
at cap `u ≥ 0` it is at most `e^{−u/2}`. -/
theorem integral_excess_le (u : ℝ) (hu : 0 ≤ u) :
    ∫ x, (flog x - capLog u x) ∂Erdos1002.gaussMeasure ≤ Real.exp (-u / 2) := by
  have hlyap := lyapunov_pos'
  set ε := Real.exp (-(u + lyapunov)) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε < 1 := by
    rw [hε, Real.exp_lt_one_iff]
    linarith
  have hlogε : Real.log ε = -(u + lyapunov) := by rw [hε, Real.log_exp]
  have hsub : Ioo (0 : ℝ) ε ⊆ Ioc (0 : ℝ) 1 :=
    fun x hx => ⟨hx.1, le_of_lt (lt_trans hx.2 hε1)⟩
  -- the dominating indicator function
  have hgb : ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖(Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y) x‖
        ≤ (u + lyapunov) + (-Real.log x) := by
    intro x hx
    have hlx : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2
    by_cases hmem : x ∈ Ioo (0 : ℝ) ε
    · rw [Set.indicator_of_mem hmem]
      have hlt : Real.log x < -(u + lyapunov) := by
        rw [← hlogε]
        exact Real.log_lt_log hmem.1 hmem.2
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      linarith
  have hgOn : IntegrableOn
      ((Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y))
      (Ioc (0 : ℝ) 1) volume := by
    have hconst : IntegrableOn (fun _ : ℝ => u + lyapunov) (Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        intervalIntegrable_const
    apply Integrable.mono' (hconst.add integrableOn_neg_log_unit)
      (((measurable_const.sub Real.measurable_log).indicator
        measurableSet_Ioo).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hgb x hx
  have hgγ : Integrable
      ((Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y))
      Erdos1002.gaussMeasure := integrable_gauss hgOn
  have hnn : ∀ x : ℝ,
      0 ≤ (Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y) x := by
    intro x
    apply Set.indicator_nonneg
    intro y hy
    have hlt : Real.log y < -(u + lyapunov) := by
      rw [← hlogε]
      exact Real.log_lt_log hy.1 hy.2
    linarith
  -- step 1: pointwise domination γ-a.e.
  have h1 : ∫ x, (flog x - capLog u x) ∂Erdos1002.gaussMeasure
      ≤ ∫ x, (Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y) x
          ∂Erdos1002.gaussMeasure := by
    have hfc : Integrable (fun x => flog x - capLog u x) Erdos1002.gaussMeasure :=
      integrable_flog_gauss.sub (integrable_capLog_gauss u)
    apply integral_mono_ae hfc hgγ
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
    rw [capLog_eq_min hx.1]
    rcases lt_or_ge x ε with hxe | hxe
    · have hmem : x ∈ Ioo (0 : ℝ) ε := ⟨hx.1, hxe⟩
      rw [Set.indicator_of_mem hmem]
      have hlt : Real.log x < -(u + lyapunov) := by
        rw [← hlogε]
        exact Real.log_lt_log hx.1 hxe
      have hfl : u ≤ flog x := by
        simp only [flog]
        linarith
      rw [min_eq_right hfl]
      simp only [flog]
      linarith
    · have hge : -(u + lyapunov) ≤ Real.log x := by
        rw [← hlogε]
        exact Real.log_le_log hε0 hxe
      have hfl : flog x ≤ u := by
        simp only [flog]
        linarith
      have hmem : x ∉ Ioo (0 : ℝ) ε := fun hmem => absurd hmem.2 (not_lt.mpr hxe)
      rw [min_eq_left hfl, sub_self, Set.indicator_of_notMem hmem]
  -- step 2: pass to the dominating measure
  have h2 : ∫ x, (Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y) x
        ∂Erdos1002.gaussMeasure
      ≤ ∫ x, (Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y) x
          ∂(ENNReal.ofReal (3 / 2) • volume.restrict (Ioc (0 : ℝ) 1)) :=
    integral_mono_measure gaussMeasure_le_smul (Filter.Eventually.of_forall hnn)
      (hgOn.smul_measure ENNReal.ofReal_ne_top)
  -- step 3: evaluate the Lebesgue integral exactly
  have h3 : ∫ x, (Ioo (0 : ℝ) ε).indicator (fun y => -(u + lyapunov) - Real.log y) x
        ∂(ENNReal.ofReal (3 / 2) • volume.restrict (Ioc (0 : ℝ) 1)) = 3 / 2 * ε := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
      smul_eq_mul, integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε0.le,
      intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_log',
      intervalIntegral.integral_const, integral_log, hlogε]
    simp only [smul_eq_mul]
    ring
  -- step 4: numerics
  have h4 : (3 : ℝ) / 2 * ε ≤ Real.exp (-u / 2) := by
    have e1 : ε = Real.exp (-u) * Real.exp (-lyapunov) := by
      rw [hε, ← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-lyapunov) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith [one_lt_lyapunov])
    have e3 : Real.exp (-1) ≤ 2 / 3 := by
      rw [Real.exp_neg]
      have ha : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hi : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr (Real.exp_pos 1)
      have hmul : Real.exp 1 * (Real.exp 1)⁻¹ = 1 :=
        mul_inv_cancel₀ (Real.exp_pos 1).ne'
      nlinarith
    have e4 : Real.exp (-u) ≤ Real.exp (-u / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have e5 : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
    have e6 : Real.exp (-u) * Real.exp (-lyapunov) ≤ Real.exp (-u) * (2 / 3) :=
      mul_le_mul_of_nonneg_left (e2.trans e3) e5.le
    calc (3 : ℝ) / 2 * ε = 3 / 2 * (Real.exp (-u) * Real.exp (-lyapunov)) := by
          rw [e1]
      _ ≤ 3 / 2 * (Real.exp (-u) * (2 / 3)) := by linarith
      _ = Real.exp (-u) := by ring
      _ ≤ Real.exp (-u / 2) := e4
  linarith

/-- The capped mean is nonpositive. -/
theorem integral_capLog_nonpos (u : ℝ) (hu : 0 ≤ u) :
    ∫ x, capLog u x ∂Erdos1002.gaussMeasure ≤ 0 := by
  have hae : capLog u ≤ᵐ[Erdos1002.gaussMeasure] flog := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
    exact capLog_le_flog hx.1
  have h := integral_mono_ae (integrable_capLog_gauss u) integrable_flog_gauss hae
  rwa [integral_flog_gauss] at h

/-- The capped mean is at least `−e^{−u/2}`. -/
theorem neg_exp_le_integral_capLog (u : ℝ) (hu : 0 ≤ u) :
    -Real.exp (-u / 2) ≤ ∫ x, capLog u x ∂Erdos1002.gaussMeasure := by
  have h8 := integral_excess_le u hu
  rw [integral_sub integrable_flog_gauss (integrable_capLog_gauss u),
    integral_flog_gauss] at h8
  linarith

end

end LargeDeviation

end Kwon1002

