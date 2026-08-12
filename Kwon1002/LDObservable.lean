import Kwon1002.Section4
import Erdos1002.GaussLebesgueTransfer
import Erdos1002.GaussPrefixCylinderPartition
import Erdos1002.GaussApproximationCoordinate
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Large deviations for continuants, shared vocabulary (display (16), stage 0)

This module opens the self-contained route to display (16) of the
manuscript — the large-deviation bound
`P(|log q_r − λ r| > v) ≤ C exp(−c·min(v²/r, v/(1+log(r+1))²))` —
agreed with the author as an admissible replacement for the
perturbed-operator argument (see README).  It fixes the observables and
the measure-theoretic bridges every later stage uses.

## The route (constant discipline, worked out before formalising)

Write `x_i = T^i α` (Gauss map), `f(x) = −log x − λ` with
`λ = lyapunov = π²/(12 log 2)`, and `S_r = Σ_{i<r} f(x_i)`.

* **Spine** (`LDSpine`): `log q_r ≤ Σ_{i<r} (−log x_i) ≤ log q_r + log 2`
  for irrational `α ∈ (0,1)`, from `β_k = (−1)^k (q_k α − p_k)` and
  `q_{k+1} β_k + q_k β_{k+1} = 1`.  Hence
  `|log q_r − λ r| ≤ |S_r| + log 2`.
* **Centering** (`LDLyapunov`): `∫ (−log x) dν = λ` (Gauss measure `ν`),
  via `(−log x)/(1+x) = Σ_k (−log x)(1−x)x^{2k}` (nonnegative terms) and
  `Σ 1/n² = π²/6`; second moment `∫ f² dν ≤ 3`, and the tail bound
  `∫_{(0,e^{−t})} log² dν ≤ 30 e^{−t/2}`.
* **Truncation**: `g_u = capLog u = min(f, u)` (cap at level `u`,
  implemented by clamping the argument, so the cap is globally Lipschitz
  with constant `e^{u+λ}`); the excess `Σ (f(x_i) − u)^+` is controlled
  at cap `u ≥ 4 log(r+1)` by a dyadic-rank union bound over
  `digit_tail_product` (`LDExcess`), at rate `exp(−w/(8(log(r+1)+2)))`.
* **Variance** (`LDVariance`): `|Cov(g_u(x_0), g_u(x_q))| ≤ C e^{−κq}`
  uniformly in `u`, by `gauss_correlation_le` at distance-dependent cap
  `min(u, qκ')` plus the tail bound for the difference of caps; hence
  block second moments `E[(Σ_{i<ℓ} ḡ(x_{t+i}))²] ≤ C₀ ℓ`.
* **Factorization** (`LDPsi`): conditional on any positive depth-`D`
  cylinder, the future beyond a gap `M` decouples *relatively*:
  `E[Φ ∘ T^{D+M} | I_w] ≤ (1 + 24 (527/540)^M) E[Φ]` for arbitrary
  nonnegative bounded measurable `Φ`, from the in-tree conditional
  density `kwonDensity` (bounded by 8, Lipschitz by 24) and the sup-norm
  transfer contraction.  Iterated over the countable depth-`D` cylinder
  partition this factorizes products of separated digit-window blocks.
* **Blocks and Chernoff** (`LDBlocks`, `LDMain`): windows of length
  `W ≍ 100(log(r+1)+1)` approximate `g_u(x_i)` by digit words to total
  error ≤ 1 (cylinder diameter `4^{−⌊W/2⌋}`); blocks of length `2W`,
  alternating parities (Cauchy–Schwarz), gaps `W`; per-block Taylor
  `E[e^{2sĜ_b}] ≤ 1 + 2sE[Ĝ_b] + 4s²E[Ĝ_b²]` valid for
  `s ≤ s₀ = 1/(16ℓ(u+2))`; assembly gives
  `E[e^{±sĜ_r}] ≤ C₂ e^{4C₁ s² r}` and Chernoff yields the min of the
  quadratic branch `v²/r` and the clamped branch `s₀·v ≍ v/log²r`.

The final exponent `min(v²/r, v/(1+log(r+1))²)` is weaker than the
manuscript's `min(v²/r, v)` only in the regime `v ≫ r/log² r`, which no
consumer in this development uses: display (20) consumes `v = δH ≍ L^{3/4}`
at `r ≤ 2m_n ≍ L`, where `v²/r ≍ δ²√L` and `v/log²r ≫ √L`.  The verbatim
linear branch is a genuine spectral-gap fact and is *not* claimed here.
-/

open Set MeasureTheory Filter

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-! ## Numerical bounds on the Lévy constant -/

lemma one_lt_lyapunov : 1 < lyapunov := by
  have hpi : 3.141592 < Real.pi := Real.pi_gt_d6
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [lyapunov, lt_div_iff₀ (by positivity)]
  nlinarith

lemma lyapunov_lt_two : lyapunov < 2 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [lyapunov, div_lt_iff₀ (by positivity)]
  nlinarith

lemma lyapunov_pos' : 0 < lyapunov := lt_trans one_pos one_lt_lyapunov

/-! ## The observable and its cap -/

/-- The centered Birkhoff observable `f(x) = −log x − λ`. -/
def flog (x : ℝ) : ℝ := -Real.log x - lyapunov

/-- The cap of `flog` at level `u`, implemented by clamping the argument at
`e^{−(u+λ)}`; on `(0,1)` this is exactly `min (flog x) u`, and globally it is
Lipschitz with constant `e^{u+λ}`. -/
def capLog (u x : ℝ) : ℝ :=
  -Real.log (max x (Real.exp (-(u + lyapunov)))) - lyapunov

lemma measurable_flog : Measurable flog := by
  unfold flog; fun_prop

lemma measurable_capLog (u : ℝ) : Measurable (capLog u) := by
  have h : Measurable fun x : ℝ => max x (Real.exp (-(u + lyapunov))) :=
    measurable_id.max measurable_const
  exact (h.log.neg).sub measurable_const

lemma capLog_eq_min {u x : ℝ} (hx : 0 < x) : capLog u x = min (flog x) u := by
  rcases le_total (Real.exp (-(u + lyapunov))) x with h | h
  · have hle : Real.exp (-(u + lyapunov)) ≤ x := h
    have hlog : -(u + lyapunov) ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hle
      rwa [Real.log_exp] at this
    simp only [capLog, flog, max_eq_left hle]
    rw [min_eq_left]
    linarith
  · have hlog : Real.log x ≤ -(u + lyapunov) := by
      have := Real.log_le_log hx h
      rwa [Real.log_exp] at this
    simp only [capLog, flog, max_eq_right h, Real.log_exp]
    rw [min_eq_right]
    · ring
    · linarith

lemma capLog_le_cap (u x : ℝ) : capLog u x ≤ u := by
  have h : Real.exp (-(u + lyapunov)) ≤ max x (Real.exp (-(u + lyapunov))) :=
    le_max_right _ _
  have := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp] at this
  unfold capLog
  linarith

lemma capLog_le_flog {u x : ℝ} (hx : 0 < x) : capLog u x ≤ flog x := by
  rw [capLog_eq_min hx]; exact min_le_left _ _

lemma neg_lyapunov_le_capLog {u : ℝ} (hu : 0 ≤ u) {x : ℝ} (hx : x ≤ 1) :
    -lyapunov ≤ capLog u x := by
  have hexp : Real.exp (-(u + lyapunov)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := lyapunov_pos'
    linarith
  have hmax : max x (Real.exp (-(u + lyapunov))) ≤ 1 := max_le hx hexp
  have hpos : 0 < max x (Real.exp (-(u + lyapunov))) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  have := Real.log_nonpos hpos.le hmax
  unfold capLog
  linarith

lemma abs_capLog_le {u : ℝ} (hu : 0 ≤ u) {x : ℝ} (hx : x ≤ 1) :
    |capLog u x| ≤ u + lyapunov := by
  rw [abs_le]
  constructor
  · have := neg_lyapunov_le_capLog hu hx
    linarith
  · have := capLog_le_cap u x
    have := lyapunov_pos'
    linarith

/-- Global Lipschitz bound for the cap: the argument clamp keeps the
logarithm away from `0`. -/
lemma abs_capLog_sub_capLog_le (u : ℝ) (x y : ℝ) :
    |capLog u x - capLog u y| ≤ Real.exp (u + lyapunov) * |x - y| := by
  set t : ℝ := Real.exp (-(u + lyapunov)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have hax : t ≤ max x t := le_max_right _ _
  have hay : t ≤ max y t := le_max_right _ _
  have hxpos : 0 < max x t := lt_of_lt_of_le ht0 hax
  have hypos : 0 < max y t := lt_of_lt_of_le ht0 hay
  have hkey : ∀ a b : ℝ, t ≤ a → t ≤ b → b ≤ a →
      Real.log a - Real.log b ≤ (a - b) / t := by
    intro a b hta htb hba
    have hb0 : 0 < b := lt_of_lt_of_le ht0 htb
    have ha0 : 0 < a := lt_of_lt_of_le ht0 hta
    have hdiv : Real.log a - Real.log b = Real.log (a / b) :=
      (Real.log_div (ne_of_gt ha0) (ne_of_gt hb0)).symm
    rw [hdiv]
    have h1 : Real.log (a / b) ≤ a / b - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : a / b - 1 = (a - b) / b := by field_simp
    have h3 : (a - b) / b ≤ (a - b) / t := by
      gcongr
      linarith
    linarith
  have hmax : |max x t - max y t| ≤ |x - y| := abs_max_sub_max_le_abs x y t
  have habs : |Real.log (max x t) - Real.log (max y t)| ≤ |max x t - max y t| / t := by
    rcases le_total (max y t) (max x t) with hc | hc
    · rw [abs_of_nonneg (by
        have := Real.log_le_log hypos hc
        linarith), abs_of_nonneg (by linarith)]
      exact hkey _ _ hax hay hc
    · rw [abs_sub_comm, abs_sub_comm (max x t)]
      rw [abs_of_nonneg (by
        have := Real.log_le_log hxpos hc
        linarith), abs_of_nonneg (by linarith)]
      exact hkey _ _ hay hax hc
  have hcap : capLog u x - capLog u y
      = -(Real.log (max x t) - Real.log (max y t)) := by
    unfold capLog
    rw [← ht]
    ring
  rw [hcap, abs_neg]
  have hinv : (1 : ℝ) / t = Real.exp (u + lyapunov) := by
    rw [ht, Real.exp_neg, one_div, inv_inv]
  calc |Real.log (max x t) - Real.log (max y t)|
      ≤ |max x t - max y t| / t := habs
    _ ≤ |x - y| / t := by gcongr
    _ = Real.exp (u + lyapunov) * |x - y| := by
        rw [div_eq_mul_inv, mul_comm, ← one_div, hinv]

/-- Raising the cap raises the observable. -/
lemma capLog_mono_cap {u u' : ℝ} (h : u ≤ u') (x : ℝ) :
    capLog u x ≤ capLog u' x := by
  have hexp : Real.exp (-(u' + lyapunov)) ≤ Real.exp (-(u + lyapunov)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmax : max x (Real.exp (-(u' + lyapunov))) ≤ max x (Real.exp (-(u + lyapunov))) :=
    max_le_max le_rfl hexp
  have hpos : 0 < max x (Real.exp (-(u' + lyapunov))) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  have := Real.log_le_log hpos hmax
  unfold capLog
  linarith

/-! ## Bridges between our coordinates and the substrate -/

lemma gaussIter_eq_gaussOrbit (α : ℝ) (j : ℕ) :
    gaussIter α j = Erdos1002.gaussOrbit j α := rfl

lemma gaussOrbit_add (m n : ℕ) (x : ℝ) :
    Erdos1002.gaussOrbit (m + n) x
      = Erdos1002.gaussOrbit m (Erdos1002.gaussOrbit n x) := by
  unfold Erdos1002.gaussOrbit
  rw [Function.iterate_add_apply]

/-! ## Measure bridges -/

/-- Gauss measure is absolutely continuous with respect to Lebesgue. -/
lemma gaussMeasure_absCont : Erdos1002.gaussMeasure ≪ (volume : Measure ℝ) := by
  rw [Erdos1002.gaussMeasure_eq_volume_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- Almost every real is irrational (Lebesgue). -/
lemma ae_irrational_volume : ∀ᵐ x : ℝ ∂volume, Irrational x := by
  rw [ae_iff]
  have h : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
    ext x
    simp [Irrational]
  rw [h]
  exact (Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume

/-- Almost every point for Gauss measure is an irrational of `(0,1)`. -/
lemma ae_gauss_unit_irrational :
    ∀ᵐ x ∂Erdos1002.gaussMeasure, x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x := by
  have h1 : ∀ᵐ x ∂Erdos1002.gaussMeasure, x ∈ Ioc (0 : ℝ) 1 :=
    Erdos1002.gaussMeasure_unit_ae
  have h2 : ∀ᵐ x ∂Erdos1002.gaussMeasure, Irrational x :=
    gaussMeasure_absCont.ae_le ae_irrational_volume
  filter_upwards [h1, h2] with x hx hirr
  refine ⟨⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩, hirr⟩
  intro h1eq
  exact hirr.ne_int 1 (by simpa using h1eq)

/-- Almost every point of `(0,1)` for Lebesgue measure is irrational. -/
lemma ae_volume_irrational :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), Irrational x :=
  ae_restrict_of_ae ae_irrational_volume

/-- Lebesgue is at most twice Gauss on measurable subsets of `(0,1)`:
`dLeb/dν = log 2 · (1+x) ≤ 2 log 2 < 2`. -/
lemma volume_le_two_gaussMeasure {E : Set ℝ} (hEM : MeasurableSet E)
    (hEsub : E ⊆ Ioo (0 : ℝ) 1) :
    volume E ≤ 2 * Erdos1002.gaussMeasure E := by
  have hae : ∀ᵐ x ∂(Erdos1002.gaussMeasure.restrict E),
      Erdos1002.lebesgueOverGaussDensity x ≤ 2 := by
    refine (ae_restrict_iff' hEM).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx1 : x ∈ Icc (0 : ℝ) 1 := ⟨(hEsub hx).1.le, (hEsub hx).2.le⟩
    have hb := (Erdos1002.lebesgueOverGaussDensityReal_bounds hx1).2
    have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    calc Erdos1002.lebesgueOverGaussDensity x
        = ENNReal.ofReal (Erdos1002.lebesgueOverGaussDensityReal x) := rfl
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith)
      _ = 2 := by simp
  have h1 : volume E = (volume.restrict (Ioc (0 : ℝ) 1)) E := by
    rw [Measure.restrict_apply hEM,
      inter_eq_self_of_subset_left (hEsub.trans Ioo_subset_Ioc_self)]
  rw [h1, ← Erdos1002.gaussMeasure_withDensity_lebesgueOverGaussDensity,
    withDensity_apply _ hEM]
  calc ∫⁻ x in E, Erdos1002.lebesgueOverGaussDensity x ∂Erdos1002.gaussMeasure
      ≤ ∫⁻ _ in E, 2 ∂Erdos1002.gaussMeasure := lintegral_mono_ae hae
    _ = 2 * Erdos1002.gaussMeasure E := setLIntegral_const _ _

/-- Integrals against Gauss measure are invariant under composition with the
Gauss orbit (stationarity). -/
lemma integral_comp_gaussOrbit (q : ℕ) (φ : ℝ → ℝ)
    (hφ : AEStronglyMeasurable φ Erdos1002.gaussMeasure) :
    ∫ x, φ (Erdos1002.gaussOrbit q x) ∂Erdos1002.gaussMeasure
      = ∫ x, φ x ∂Erdos1002.gaussMeasure := by
  have hmap : Measure.map (Erdos1002.gaussOrbit q) Erdos1002.gaussMeasure
      = Erdos1002.gaussMeasure := Erdos1002.map_gaussMap_iterate_gaussMeasure q
  calc ∫ x, φ (Erdos1002.gaussOrbit q x) ∂Erdos1002.gaussMeasure
      = ∫ y, φ y ∂(Measure.map (Erdos1002.gaussOrbit q) Erdos1002.gaussMeasure) := by
        rw [integral_map (Erdos1002.measurable_gaussOrbit q).aemeasurable
          (by rwa [hmap])]
    _ = ∫ x, φ x ∂Erdos1002.gaussMeasure := by rw [hmap]

end

end LargeDeviation

end Kwon1002
