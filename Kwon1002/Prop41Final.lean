/-
Scratch file (agent `p41`).

ASSIGNED TARGETS
  * `Kwon1002.Prop41.prop_4_1_error_shape`            (display (30))
  * `Kwon1002.prop_4_1_marked_factorization`          (display (27))

Both are reproduced TOKEN-IDENTICALLY below (`prop_4_1_error_shape_f`,
`prop_4_1_marked_factorization_f`), diffed mechanically against
`Kwon1002/Prop41.lean` lines 303-310 and `Kwon1002/Section4.lean` lines
137-144; only the theorem name carries the suffix.  Nothing is weakened.
-/
import Kwon1002.Bridge
import Erdos1002.GaussTransferCorrelation
import Erdos1002.GaussLebesgueTransfer

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace Prop41Final

open Prop41 ErrorShape

noncomputable section

/-! ## 1. The recorded finding: the implicit upper constraint on `c` in (30)

The manuscript's zero-mode branch produces the error `ρ^{200H}` (from (25)),
whereas display (30) writes the bracket as
`e^{-cL^{1/2}} + e^{-cH} + ρ^{cH}`.  `Kwon1002/ErrorShape.lean` records the
sufficient constraint `c ≤ 200` (hypothesis `hc200` of
`zero_branch_le_deltaScale`) and calls it "the implicit upper constraint".

This section settles the finding completely, and *corrects* it in one
direction.  Three statements, all proved:

* `zero_branch_le_deltaScale_log`, a **sharper sufficient** constraint,
  `c ≤ 200·(−log ρ)`, obtained from the *middle* term `e^{-cH}` rather than
  from `ρ^{cH}`.  Together with `ErrorShape.zero_branch_le_deltaScale` the
  sufficient region is `c ≤ max (200) (200·(−log ρ))`.
* `eventually_zero_branch_le_deltaScale`, **the constraint is not needed
  at all** once (18) is read as the manuscript writes it, `H = L^{3/4}`:
  for *every* `c > 0` and every `ρ ∈ (0,1)`, `ρ^{200H} ≤ δ_n` for all large
  `n`, because `H = L^{3/4}` makes `ρ^{200H} = e^{-200|log ρ| L^{3/4}}`
  eventually smaller than the bracket's own first term `e^{-cL^{1/2}}`.
  So the "implicit upper constraint on `c`" as recorded is an artefact of
  demanding the inequality at every `n` rather than eventually.
* `deltaBracket_lt_zero_branch`, **but the constraint is genuinely needed
  under the weaker reading of (18)** that the proof of 4.1 actually uses,
  namely `H ≍ L^{1/2}` (see `Kwon1002/Prop41.lean`, module docstring: the
  only property of `H` consumed is `H ≥ L^{1/2}`).  At `H = L^{1/2}` the
  three terms of the bracket are `e^{-cH}`, `e^{-cH}`, `ρ^{cH}`, and if
  both `c > 200` and `c > 200·(−log ρ)` then the whole bracket is
  *strictly smaller* than `ρ^{200H}` for all large `L`: display (30) then
  fails to contain the zero-mode error it is supposed to contain.

Net finding, in the form a referee can use: **(30) is correct as stated
only because (18) pins `H = L^{3/4} ≫ L^{1/2}`.  If `H` is allowed the
whole window `L^{1/2} ≤ H ≪ L` that the proof of 4.1 otherwise permits,
the display carries the unstated side condition
`c ≤ max (200) (200·(−log ρ))`.** -/

/-- The bracket of (30) as a function of the two scales `L`, `H`, with the
tie `H = L^{3/4}` of (18) *not* imposed. -/
def deltaBracket (c ρ L H : ℝ) : ℝ :=
  Real.exp (-c * Real.sqrt L) + Real.exp (-c * H) + ρ ^ (c * H)

theorem deltaScale_eq_bracket (c ρ : ℝ) (n : ℕ) :
    deltaScale c ρ n = deltaBracket c ρ (Lnorm n) (Hscale n) := rfl

/-- **Sharper sufficient constraint.**  The zero-mode error `ρ^{200H}` sits
under the *middle* term of (30) as soon as `c ≤ 200·(−log ρ)`.  This is
independent of `ErrorShape.zero_branch_le_deltaScale`, which uses the third
term and needs `c ≤ 200`. -/
theorem zero_branch_le_deltaScale_log {c ρ : ℝ} (n : ℕ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : c ≤ 200 * (-Real.log ρ)) (hH : 0 ≤ Hscale n) :
    ρ ^ (200 * Hscale n) ≤ deltaScale c ρ n := by
  have hmid : ρ ^ (200 * Hscale n) ≤ Real.exp (-c * Hscale n) := by
    rw [Real.rpow_def_of_pos hρ0]
    apply Real.exp_le_exp.2
    nlinarith
  have h1 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have h3 : (0 : ℝ) < ρ ^ (c * Hscale n) := Real.rpow_pos_of_pos hρ0 _
  unfold deltaScale
  linarith

/-- **The constraint is unnecessary under (18) as written.**  With
`H = L^{3/4}` the zero-mode error `ρ^{200H}` is eventually dominated by the
*first* term of (30)'s bracket, for every `c > 0` and every `ρ ∈ (0,1)`.
No upper constraint on `c` at all. -/
theorem eventually_zero_branch_le_deltaScale (c ρ : ℝ)
    (hc : 0 < c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ρ ^ (200 * Hscale n) ≤ deltaScale c ρ n := by
  have hlogρ : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  set b : ℝ := 200 * (-Real.log ρ) with hbdef
  have hb : 0 < b := by rw [hbdef]; nlinarith
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have key : ∀ᶠ L : ℝ in atTop,
      ρ ^ (200 * L ^ (3 / 4 : ℝ)) ≤ Real.exp (-c * Real.sqrt L) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop ((c / b) ^ (4 : ℕ))] with L hL1 hLc
    have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
    -- `√L ≤ (c/b)⁻¹ · L^{3/4}` once `L ≥ (c/b)^4`
    have hq : (c / b) ≤ L ^ (1 / 4 : ℝ) := by
      have hcb : (0 : ℝ) ≤ c / b := le_of_lt (div_pos hc hb)
      have h4 : ((c / b) ^ (4 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = c / b := by
        rw [← Real.rpow_natCast (c / b) 4, ← Real.rpow_mul hcb]
        norm_num
      calc (c / b) = ((c / b) ^ (4 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := h4.symm
        _ ≤ L ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hLc (by norm_num)
    have hsplit : L ^ (3 / 4 : ℝ) = L ^ (1 / 4 : ℝ) * Real.sqrt L := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hL1)]
      norm_num
    have hs0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hstep : c * Real.sqrt L ≤ b * L ^ (3 / 4 : ℝ) := by
      rw [hsplit]
      have hmul : c / b * Real.sqrt L ≤ L ^ (1 / 4 : ℝ) * Real.sqrt L :=
        mul_le_mul_of_nonneg_right hq hs0
      have h2 : b * (c / b * Real.sqrt L) ≤ b * (L ^ (1 / 4 : ℝ) * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hmul hb.le
      have h3 : b * (c / b * Real.sqrt L) = c * Real.sqrt L := by
        field_simp
      rw [← h3]
      exact h2
    rw [Real.rpow_def_of_pos hρ0]
    apply Real.exp_le_exp.2
    have hkey : Real.log ρ * (200 * L ^ (3 / 4 : ℝ)) = -(b * L ^ (3 / 4 : ℝ)) := by
      rw [hbdef]; ring
    rw [hkey]
    linarith
  filter_upwards [hLtend.eventually key] with n hn
  have h2 : (0 : ℝ) < Real.exp (-c * Hscale n) := Real.exp_pos _
  have h3 : (0 : ℝ) < ρ ^ (c * Hscale n) := Real.rpow_pos_of_pos hρ0 _
  have hHn : Hscale n = (Lnorm n) ^ (3 / 4 : ℝ) := rfl
  rw [hHn]
  unfold deltaScale
  rw [hHn] at h2 h3 ⊢
  linarith

/-- **The constraint is necessary under the weak reading of (18).**  At
`H = L^{1/2}`, the only property of `H` that the proof of Proposition 4.1
consumes, a constant `c` violating **both** sufficient constraints makes
the whole bracket of (30) strictly smaller than the zero-mode error
`ρ^{200H}` it must dominate. -/
theorem deltaBracket_lt_zero_branch (c ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hc200 : 200 < c) (hclog : 200 * (-Real.log ρ) < c) :
    ∀ᶠ L : ℝ in atTop,
      deltaBracket c ρ L (Real.sqrt L) < ρ ^ (200 * Real.sqrt L) := by
  have hlogρ : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hnl : 0 < -Real.log ρ := neg_pos.2 hlogρ
  set b : ℝ := 200 * (-Real.log ρ) with hbdef
  have hb : 0 < b := by rw [hbdef]; nlinarith
  set a : ℝ := min c (c * (-Real.log ρ)) with hadef
  have hca : 0 < c := lt_trans (by norm_num) hc200
  have ha : 0 < a := lt_min hca (mul_pos hca hnl)
  have hab : b < a := by
    refine lt_min hclog ?_
    rw [hbdef]
    nlinarith
  have hS : ∀ᶠ L : ℝ in atTop, Real.log 3 / (a - b) < Real.sqrt L :=
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hS, eventually_ge_atTop (0 : ℝ)] with L hLS hL0
  set s : ℝ := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg L
  -- each of the three terms is at most `e^{-a s}`
  have e1 : Real.exp (-c * s) ≤ Real.exp (-a * s) := by
    apply Real.exp_le_exp.2
    have : a ≤ c := min_le_left _ _
    nlinarith
  have e3 : ρ ^ (c * s) ≤ Real.exp (-a * s) := by
    rw [Real.rpow_def_of_pos hρ0]
    apply Real.exp_le_exp.2
    have : a ≤ c * (-Real.log ρ) := min_le_right _ _
    nlinarith
  have hrhs : ρ ^ (200 * s) = Real.exp (-b * s) := by
    rw [Real.rpow_def_of_pos hρ0, hbdef]
    congr 1
    ring
  -- and `3 e^{-a s} < e^{-b s}`
  have hgap : (3 : ℝ) * Real.exp (-a * s) < Real.exp (-b * s) := by
    have hpos : (0 : ℝ) < Real.exp (-a * s) := Real.exp_pos _
    have hs : Real.log 3 < (a - b) * s := by
      have hd : 0 < a - b := by linarith
      calc Real.log 3 = Real.log 3 / (a - b) * (a - b) := by field_simp
        _ < s * (a - b) := by
            exact mul_lt_mul_of_pos_right hLS hd
        _ = (a - b) * s := by ring
    have h3 : (3 : ℝ) < Real.exp ((a - b) * s) := by
      have := Real.exp_lt_exp.2 hs
      rwa [Real.exp_log (by norm_num : (0:ℝ) < 3)] at this
    calc (3 : ℝ) * Real.exp (-a * s) < Real.exp ((a - b) * s) * Real.exp (-a * s) :=
          mul_lt_mul_of_pos_right h3 hpos
      _ = Real.exp (-b * s) := by rw [← Real.exp_add]; congr 1; ring
  rw [hrhs]
  unfold deltaBracket
  rw [← hsdef]
  linarith

/-! ## 2. Gauss-Kuzmin: `dα` on the left of (27) versus `dν` in (17)

`Kwon1002/Prop4Final.lean` (`zero_mode_defect_eq`) and
`Kwon1002/ErrorShape.lean` (`zero_mode_factorization`) both list

> the outer measure: `dα` on the left of (27) versus `dν` in (17), a
> `ρ^{200H}` change by Gauss-Kuzmin, since `j_1 ≥ 200H`

as an outstanding gap.  This section closes it, in the sharp form: the
Lebesgue mean of `g ∘ T^m` differs from the Gauss mean of `g` by at most
`(527/540)^m · log 2 · ‖g‖_∞`, with the substrate's own contraction rate.

The route is the Perron-Frobenius adjoint, not an approximation: the
Radon-Nikodym weight `w = dλ/dν = log 2 · (1+x)` is Lipschitz with constant
`log 2` and mean `1`, so `∫ g(T^m α) dα = ∫ (L^m w) g dν` and `L^m w → 1`
uniformly at rate `(527/540)^m`. -/

/-- `w(x) = log 2 · (1+x)`, the Radon-Nikodym weight `dλ/dν` on `(0,1]`. -/
def wGL (x : ℝ) : ℝ := Erdos1002.lebesgueOverGaussDensityReal x

theorem measurable_wGL : Measurable wGL :=
  Erdos1002.measurable_lebesgueOverGaussDensityReal

theorem wGL_nonneg : Erdos1002.GaussUnitNonnegative wGL := by
  intro x hx
  have h := (Erdos1002.lebesgueOverGaussDensityReal_bounds hx).1
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  show (0 : ℝ) ≤ Erdos1002.lebesgueOverGaussDensityReal x
  linarith

theorem wGL_le : Erdos1002.GaussUnitUpperBound (2 * Real.log 2) wGL :=
  fun _ hx => (Erdos1002.lebesgueOverGaussDensityReal_bounds hx).2

theorem wGL_lip : Erdos1002.GaussUnitLipschitzBound (Real.log 2) wGL := by
  intro x _ y _
  have hrw : wGL x - wGL y = Real.log 2 * (x - y) := by
    show Erdos1002.lebesgueOverGaussDensityReal x
        - Erdos1002.lebesgueOverGaussDensityReal y = _
    unfold Erdos1002.lebesgueOverGaussDensityReal
    ring
  rw [hrw, abs_mul, abs_of_nonneg (Real.log_nonneg (by norm_num))]

/-- **Change of measure.**  `∫_{(0,1]} G dλ = ∫ w·G dν`, from the
substrate's `gaussMeasure.withDensity (dλ/dν) = λ|_{(0,1]}`. -/
theorem integral_Ioc_eq_gauss_mul (G : ℝ → ℝ) :
    (∫ α in Ioc (0 : ℝ) 1, G α)
      = ∫ α, wGL α * G α ∂Erdos1002.gaussMeasure := by
  have hmeas : Measurable Erdos1002.lebesgueOverGaussDensity :=
    Erdos1002.measurable_lebesgueOverGaussDensity
  have hlt : ∀ᵐ x ∂Erdos1002.gaussMeasure,
      Erdos1002.lebesgueOverGaussDensity x < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  calc (∫ α in Ioc (0 : ℝ) 1, G α)
      = ∫ α, G α
          ∂(Erdos1002.gaussMeasure.withDensity Erdos1002.lebesgueOverGaussDensity) := by
        rw [Erdos1002.gaussMeasure_withDensity_lebesgueOverGaussDensity]
    _ = ∫ α, (Erdos1002.lebesgueOverGaussDensity α).toReal • G α
          ∂Erdos1002.gaussMeasure :=
        integral_withDensity_eq_integral_toReal_smul hmeas hlt G
    _ = ∫ α, wGL α * G α ∂Erdos1002.gaussMeasure := by
        refine integral_congr_ae ?_
        filter_upwards [Erdos1002.gaussMeasure_unit_ae] with α hα
        have hcc : α ∈ Icc (0 : ℝ) 1 := ⟨hα.1.le, hα.2⟩
        have h0 : (0 : ℝ) ≤ wGL α := wGL_nonneg hcc
        show (ENNReal.ofReal (wGL α)).toReal • G α = wGL α * G α
        rw [smul_eq_mul, ENNReal.toReal_ofReal h0]

/-- The weight has Gauss mean `1`. -/
theorem integral_wGL : (∫ α, wGL α ∂Erdos1002.gaussMeasure) = 1 := by
  have h := integral_Ioc_eq_gauss_mul (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [← h, setIntegral_const]
  simp

/-- **The Gauss-Kuzmin transfer, in the form §4 needs.**  For measurable `g`
bounded by `B` on the unit interval,

`|∫₀¹ g(T^m α) dα − ∫ g dν| ≤ (527/540)^m · log 2 · B`.

At `m = j_1 ≥ 200H` this is exactly the `ρ^{200H}` change the manuscript
asserts, with an explicit `ρ`. -/
theorem lebesgue_sub_gauss_le (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ y ∈ Icc (0 : ℝ) 1, |g y| ≤ B) (m : ℕ) :
    |(∫ α in Ioo (0 : ℝ) 1, g (gaussIter α m))
        - ∫ y, g y ∂Erdos1002.gaussMeasure|
      ≤ (527 / 540 : ℝ) ^ m * Real.log 2 * B := by
  set P : ℝ → ℝ := (Erdos1002.gaussTransfer^[m]) wGL with hPdef
  have hcontr : (0 : ℝ) ≤ (527 / 540 : ℝ) ^ m := by positivity
  -- the a.e. bound on `g`
  have hgae : ∀ᵐ y ∂Erdos1002.gaussMeasure, ‖g y‖ ≤ B := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    rw [Real.norm_eq_abs]
    exact hB y ⟨hy.1.le, hy.2⟩
  have hgint : Integrable g Erdos1002.gaussMeasure :=
    Integrable.of_bound hg.aestronglyMeasurable B hgae
  have hPint : Integrable P Erdos1002.gaussMeasure :=
    Erdos1002.integrable_gaussTransfer_iterate_of_unit_bounds
      measurable_wGL wGL_nonneg wGL_le m
  have hPbd : ∀ᵐ y ∂Erdos1002.gaussMeasure, ‖P y‖ ≤ 2 * Real.log 2 := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hcc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    have hb := Erdos1002.gaussTransfer_iterate_unit_bounds wGL_nonneg wGL_le m
    rw [Real.norm_eq_abs, abs_of_nonneg (hb.1 hcc)]
    exact hb.2 hcc
  have hprod : Integrable (fun y => P y * g y) Erdos1002.gaussMeasure :=
    hgint.bdd_mul hPint.aestronglyMeasurable hPbd
  -- step 1: `Ioo` versus `Ioc`
  have hIoo : (∫ α in Ioo (0 : ℝ) 1, g (gaussIter α m))
      = ∫ α in Ioc (0 : ℝ) 1, g (gaussIter α m) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  -- step 2 and 3: change of measure, then the adjoint identity
  have hadj : (∫ α in Ioc (0 : ℝ) 1, g (gaussIter α m))
      = ∫ y, P y * g y ∂Erdos1002.gaussMeasure := by
    rw [integral_Ioc_eq_gauss_mul]
    exact Erdos1002.integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate
      measurable_wGL hg wGL_nonneg wGL_le m
  -- step 4: `L^m w` is uniformly within `(527/540)^m log 2` of `1`
  have hclose : ∀ y ∈ Icc (0 : ℝ) 1,
      |P y - 1| ≤ (527 / 540 : ℝ) ^ m * Real.log 2 := by
    intro y hy
    have h := Erdos1002.abs_gaussTransfer_iterate_sub_integral_le
      (K := Real.log 2) (Real.log_nonneg (by norm_num)) measurable_wGL
      wGL_nonneg wGL_le wGL_lip m hy
    rwa [integral_wGL] at h
  have hpt : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      ‖P y * g y - g y‖ ≤ (527 / 540 : ℝ) ^ m * Real.log 2 * B := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hcc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    have hfac : P y * g y - g y = (P y - 1) * g y := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul]
    exact mul_le_mul (hclose y hcc) (hB y hcc) (abs_nonneg _)
      (by positivity)
  rw [hIoo, hadj, ← integral_sub hprod hgint]
  have hfin : ‖∫ y, (P y * g y - g y) ∂Erdos1002.gaussMeasure‖
      ≤ (527 / 540 : ℝ) ^ m * Real.log 2 * B := by
    simpa using norm_integral_le_of_norm_le_const hpt
  rwa [Real.norm_eq_abs] at hfin

/-! ## 3. `ν` is carried by `(0,1)`, and the conditioning of (17) at `d = 0`
is trivial -/

theorem gaussMeasure_singleton_one : Erdos1002.gaussMeasure {(1 : ℝ)} = 0 := by
  rw [Erdos1002.gaussMeasure_eq_volume_withDensity,
    withDensity_apply _ (measurableSet_singleton (1 : ℝ))]
  have hz : (volume.restrict ({(1 : ℝ)} : Set ℝ)) = 0 := by
    rw [Measure.restrict_eq_zero]
    exact Real.volume_singleton
  rw [hz]
  simp

theorem gaussMeasure_ae_Ioo : ∀ᵐ x ∂Erdos1002.gaussMeasure, x ∈ Ioo (0 : ℝ) 1 := by
  have hne : ∀ᵐ x ∂Erdos1002.gaussMeasure, x ≠ 1 := by
    rw [ae_iff]
    simpa using gaussMeasure_singleton_one
  filter_upwards [Erdos1002.gaussMeasure_unit_ae, hne] with x hx hx1
  exact ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

theorem gaussMeasure_Ioo_eq_one :
    (Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1)).toReal = 1 := by
  have h : Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1) = Erdos1002.gaussMeasure univ := by
    refine measure_congr ?_
    filter_upwards [gaussMeasure_ae_Ioo] with x hx
    exact propext (iff_of_true hx trivial)
  rw [h, measure_univ, ENNReal.toReal_one]

theorem gaussMeasure_restrict_Ioo :
    Erdos1002.gaussMeasure.restrict (Ioo (0 : ℝ) 1) = Erdos1002.gaussMeasure :=
  Measure.restrict_eq_self_of_ae_mem gaussMeasure_ae_Ioo

/-! ## 4. The real multi-block estimate, with the Lebesgue outer measure

`Bridge.good_tuple_multiblock_mixing'` is Kwon's (17) at a good tuple,
with the **Gauss** outer measure.  Combining it with §2 puts the *Lebesgue*
outer measure of (27) in front, which is what §4 actually integrates
against. -/

theorem gaussIter_add (α : ℝ) (a b : ℕ) :
    gaussIter (gaussIter α a) b = gaussIter α (a + b) := by
  show Kwon1002.gaussMap^[b] (Kwon1002.gaussMap^[a] α) = Kwon1002.gaussMap^[a + b] α
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- **Real multi-block factorization at a good tuple, `dα` outside.**

`|∫₀¹ ∏ᵢ gᵢ(T^{jᵢ}α) dα − ∏ᵢ ∫ gᵢ dν| ≤ C ρ^{⌊200H⌋} K^r`,

uniformly in `n` and in the good tuple.  The two error sources are Kwon's
(17) (mixing) and §2 (Gauss-Kuzmin); both decay at a geometric rate in
`⌊200H⌋`, so a single `ρ` carries them. -/
theorem lebesgue_multiblock (r : ℕ) (hr : 0 < r) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (j : ℕ → ℕ), GoodTuple n r j →
      ∀ (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < r → Measurable (g i)) →
        (∀ i, i < r → ∀ x, |g i x| ≤ K) →
        (∀ i, i < r → BVBoundedBy K (g i)) →
        |(∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i)))
            - ∏ i ∈ Finset.range r, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ (⌊200 * Hscale n⌋₊) * K ^ r := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hmix⟩ := Bridge.good_tuple_multiblock_mixing' r hr
  refine ⟨C + Real.log 2, max ρ (527 / 540 : ℝ),
    by positivity, lt_of_lt_of_le hρ0 (le_max_left _ _),
    max_lt hρ1 (by norm_num), ?_⟩
  intro n j hj g K hK hgm hgbd hgbv
  set M : ℕ := ⌊200 * Hscale n⌋₊ with hMdef
  set ρ' : ℝ := max ρ (527 / 540 : ℝ) with hρ'def
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le hρ0 (le_max_left _ _)
  have hKr : (0 : ℝ) ≤ K ^ r := pow_nonneg hK r
  -- `j 0 ≥ M`, exactly as in `Bridge`
  have hmemJ : j 0 ∈ bulkJ n := hj.1.2.2 0 hr
  have hge : 200 * Hscale n ≤ ((j 0 : ℕ) : ℝ) := ((Finset.mem_filter.1 hmemJ).2).1
  have hstart : M ≤ j 0 := by
    have h1 : ⌊200 * Hscale n⌋₊ ≤ ⌊((j 0 : ℕ) : ℝ)⌋₊ := Nat.floor_mono hge
    rw [Nat.floor_natCast] at h1
    exact h1
  -- `j 0 ≤ j i` for `i < r`
  have hmono : ∀ i, i < r → j 0 ≤ j i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact le_rfl
    · exact le_of_lt (hj.1.2.1 0 i hi0 hi)
  -- the composite observable, read at time `j 0`
  set G : ℝ → ℝ := fun y => ∏ i ∈ Finset.range r, g i (gaussIter y (j i - j 0)) with hGdef
  have hGm : ∀ α : ℝ, G (gaussIter α (j 0))
      = ∏ i ∈ Finset.range r, g i (gaussIter α (j i)) := by
    intro α
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [gaussIter_add]
    congr 2
    have := hmono i (Finset.mem_range.1 hi)
    omega
  have hGmeas : Measurable G := by
    refine Finset.measurable_prod _ ?_
    intro i hi
    exact (hgm i (Finset.mem_range.1 hi)).comp (measurable_gaussIter (j i - j 0))
  have hGbd : ∀ y : ℝ, |G y| ≤ K ^ r := by
    intro y
    rw [hGdef]
    calc |∏ i ∈ Finset.range r, g i (gaussIter y (j i - j 0))|
        = ∏ i ∈ Finset.range r, |g i (gaussIter y (j i - j 0))| := by
          rw [Finset.abs_prod]
      _ ≤ ∏ _i ∈ Finset.range r, K :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _)
            (fun i hi => hgbd i (Finset.mem_range.1 hi) _)
      _ = K ^ r := by rw [Finset.prod_const, Finset.card_range]
  -- (i) Gauss-Kuzmin: the Lebesgue integral versus the Gauss integral
  have hGK : |(∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i)))
        - ∫ y, G y ∂Erdos1002.gaussMeasure|
      ≤ (527 / 540 : ℝ) ^ (j 0) * Real.log 2 * K ^ r := by
    have h := lebesgue_sub_gauss_le G hGmeas (K ^ r) hKr
      (fun y _ => hGbd y) (j 0)
    have hrw : (∫ α in Ioo (0 : ℝ) 1, G (gaussIter α (j 0)))
        = ∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i)) := by
      exact setIntegral_congr_fun measurableSet_Ioo (fun α _ => hGm α)
    rwa [hrw] at h
  -- (ii) invariance: `∫ G dν = ∫ ∏ᵢ gᵢ(T^{jᵢ}α) dν(α)`
  have hinv : (∫ y, G y ∂Erdos1002.gaussMeasure)
      = ∫ α in Ioo (0 : ℝ) 1,
          (∏ i ∈ Finset.range r, g i (gaussIter α (j i))) ∂Erdos1002.gaussMeasure := by
    rw [gaussMeasure_restrict_Ioo]
    rw [← Erdos1002.integral_comp_gaussOrbit G hGmeas (j 0)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun α => hGm α))
  -- (iii) Kwon's (17) at the good tuple
  have hmixj := hmix n j hj g K hK hgbv
  rw [gaussMeasure_Ioo_eq_one, div_one] at hmixj
  -- assemble
  have hstep1 : (527 / 540 : ℝ) ^ (j 0) ≤ ρ' ^ M := by
    calc (527 / 540 : ℝ) ^ (j 0) ≤ (527 / 540 : ℝ) ^ M :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hstart
      _ ≤ ρ' ^ M := pow_le_pow_left₀ (by norm_num) (le_max_right _ _) M
  have hstep2 : ρ ^ M ≤ ρ' ^ M := pow_le_pow_left₀ hρ0.le (le_max_left _ _) M
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hρ'M : (0 : ℝ) ≤ ρ' ^ M := pow_nonneg hρ'0.le M
  have hA : |(∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i)))
        - ∫ y, G y ∂Erdos1002.gaussMeasure| ≤ Real.log 2 * (ρ' ^ M * K ^ r) := by
    refine le_trans hGK ?_
    have : (527 / 540 : ℝ) ^ (j 0) * Real.log 2 * K ^ r
        ≤ ρ' ^ M * Real.log 2 * K ^ r := by
      have h1 : (527 / 540 : ℝ) ^ (j 0) * Real.log 2 ≤ ρ' ^ M * Real.log 2 :=
        mul_le_mul_of_nonneg_right hstep1 hlog2
      exact mul_le_mul_of_nonneg_right h1 hKr
    calc (527 / 540 : ℝ) ^ (j 0) * Real.log 2 * K ^ r
        ≤ ρ' ^ M * Real.log 2 * K ^ r := this
      _ = Real.log 2 * (ρ' ^ M * K ^ r) := by ring
  have hB : |(∫ α in Ioo (0 : ℝ) 1,
          (∏ i ∈ Finset.range r, g i (gaussIter α (j i))) ∂Erdos1002.gaussMeasure)
        - ∏ i ∈ Finset.range r, ∫ x, g i x ∂Erdos1002.gaussMeasure|
      ≤ C * (ρ' ^ M * K ^ r) := by
    refine le_trans hmixj ?_
    have h1 : C * ρ ^ M ≤ C * ρ' ^ M := mul_le_mul_of_nonneg_left hstep2 hC.le
    calc C * ρ ^ M * K ^ r ≤ C * ρ' ^ M * K ^ r := mul_le_mul_of_nonneg_right h1 hKr
      _ = C * (ρ' ^ M * K ^ r) := by ring
  rw [← hinv] at hB
  have hsplit : (∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i)))
      - ∏ i ∈ Finset.range r, ∫ x, g i x ∂Erdos1002.gaussMeasure
      = ((∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i)))
          - ∫ y, G y ∂Erdos1002.gaussMeasure)
        + ((∫ y, G y ∂Erdos1002.gaussMeasure)
          - ∏ i ∈ Finset.range r, ∫ x, g i x ∂Erdos1002.gaussMeasure) := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  exact le_trans (add_le_add hA hB) (le_of_eq (by ring))

/-! ## 5. Complex observables: the `2^r` real/imaginary expansion

Kwon's (17) is a statement about **real** observables; the zero-mode
integrand of §4 is `∏_ℓ c_ℓ(a_{j_ℓ+1}, 0)`, which is complex.  This section
supplies the reduction that `ErrorShape.zero_mode_factorization` lists as
its second outstanding gap ("complex versus real observables … a factor
`2^r` in `C`"), in the exact form the gap describes. -/

/-- A product of complex numbers, expanded over the `2^{card}` choices of a
real or an imaginary component in each slot. -/
theorem prod_eq_sum_reim (s : Finset ℕ) (u v : ℕ → ℝ) :
    ∏ i ∈ s, ((u i : ℂ) + (v i : ℂ) * Complex.I)
      = ∑ t ∈ s.powerset,
          Complex.I ^ ((s \ t).card) *
            (((∏ i ∈ s, if i ∈ t then u i else v i : ℝ)) : ℂ) := by
  classical
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have hts : t ⊆ s := Finset.mem_powerset.1 ht
  have h1 : ∏ i ∈ s \ t, ((v i : ℂ) * Complex.I)
      = (∏ i ∈ s \ t, (v i : ℂ)) * Complex.I ^ ((s \ t).card) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have h2 : (((∏ i ∈ s, if i ∈ t then u i else v i : ℝ)) : ℂ)
      = (∏ i ∈ s \ t, (v i : ℂ)) * ∏ i ∈ t, (u i : ℂ) := by
    rw [Complex.ofReal_prod, ← Finset.prod_sdiff hts]
    congr 1
    · exact Finset.prod_congr rfl (fun i hi => by
        rw [if_neg (Finset.mem_sdiff.1 hi).2])
    · exact Finset.prod_congr rfl (fun i hi => by rw [if_pos hi])
  rw [h1, h2]
  ring

/-- **Complex multi-block factorization at a good tuple, `dα` outside.**

The complex observables are presented split, `h = u + i v`, which is how the
zero-mode branch produces them (`Complex.re_add_im`).  The constant is
`2^r` times the real one of `lebesgue_multiblock`, exactly the loss the
manuscript's bookkeeping predicts. -/
theorem lebesgue_multiblock_complex (r : ℕ) (hr : 0 < r) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (j : ℕ → ℕ), GoodTuple n r j →
      ∀ (h : ℕ → ℝ → ℂ) (u v : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < r → ∀ x, h i x = (u i x : ℂ) + (v i x : ℂ) * Complex.I) →
        (∀ i, i < r → Measurable (u i)) → (∀ i, i < r → Measurable (v i)) →
        (∀ i, i < r → ∀ x, |u i x| ≤ K) → (∀ i, i < r → ∀ x, |v i x| ≤ K) →
        (∀ i, i < r → BVBoundedBy K (u i)) → (∀ i, i < r → BVBoundedBy K (v i)) →
        ‖(∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, h i (gaussIter α (j i)))
            - ∏ i ∈ Finset.range r, ∫ x, h i x ∂Erdos1002.gaussMeasure‖
          ≤ C * ρ ^ (⌊200 * Hscale n⌋₊) * K ^ r := by
  classical
  obtain ⟨C₀, ρ, hC₀, hρ0, hρ1, hreal⟩ := lebesgue_multiblock r hr
  refine ⟨2 ^ r * C₀, ρ, by positivity, hρ0, hρ1, ?_⟩
  intro n j hj h u v K hK hsp hum hvm hub hvb hubv hvbv
  set s : Finset ℕ := Finset.range r with hsdef
  set M : ℕ := ⌊200 * Hscale n⌋₊ with hMdef
  set G : Finset ℕ → ℕ → ℝ → ℝ := fun t i x => if i ∈ t then u i x else v i x with hGdef
  have hGfun : ∀ (t : Finset ℕ) (i : ℕ), G t i = if i ∈ t then u i else v i := by
    intro t i
    funext x
    by_cases hmem : i ∈ t
    · simp only [hGdef, if_pos hmem]
    · simp only [hGdef, if_neg hmem]
  have hGm : ∀ (t : Finset ℕ) (i : ℕ), i < r → Measurable (G t i) := by
    intro t i hi
    rw [hGfun]
    by_cases hmem : i ∈ t
    · rw [if_pos hmem]; exact hum i hi
    · rw [if_neg hmem]; exact hvm i hi
  have hGbd : ∀ (t : Finset ℕ) (i : ℕ), i < r → ∀ x, |G t i x| ≤ K := by
    intro t i hi x
    by_cases hmem : i ∈ t
    · simp only [hGdef, if_pos hmem]; exact hub i hi x
    · simp only [hGdef, if_neg hmem]; exact hvb i hi x
  have hGbv : ∀ (t : Finset ℕ) (i : ℕ), i < r → BVBoundedBy K (G t i) := by
    intro t i hi
    rw [hGfun]
    by_cases hmem : i ∈ t
    · rw [if_pos hmem]; exact hubv i hi
    · rw [if_neg hmem]; exact hvbv i hi
  set Ft : Finset ℕ → ℝ → ℝ :=
    fun t α => ∏ i ∈ s, G t i (gaussIter α (j i)) with hFtdef
  have hFtmeas : ∀ t : Finset ℕ, Measurable (Ft t) := by
    intro t
    refine Finset.measurable_prod _ ?_
    intro i hi
    exact (hGm t i (Finset.mem_range.1 hi)).comp (measurable_gaussIter (j i))
  have hFtbd : ∀ (t : Finset ℕ) (α : ℝ), |Ft t α| ≤ K ^ r := by
    intro t α
    calc |Ft t α| = ∏ i ∈ s, |G t i (gaussIter α (j i))| := by
          rw [hFtdef, Finset.abs_prod]
      _ ≤ ∏ _i ∈ s, K :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _)
            (fun i hi => hGbd t i (Finset.mem_range.1 hi) _)
      _ = K ^ r := by rw [Finset.prod_const, hsdef, Finset.card_range]
  -- the two sides, expanded
  set X : Finset ℕ → ℝ := fun t => ∫ α in Ioo (0 : ℝ) 1, Ft t α with hXdef
  set Y : Finset ℕ → ℝ :=
    fun t => ∏ i ∈ s, ∫ x, G t i x ∂Erdos1002.gaussMeasure with hYdef
  have hLHS : (∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ s, h i (gaussIter α (j i)))
      = ∑ t ∈ s.powerset, Complex.I ^ ((s \ t).card) * ((X t : ℝ) : ℂ) := by
    have hpt : ∀ α : ℝ, ∏ i ∈ s, h i (gaussIter α (j i))
        = ∑ t ∈ s.powerset, Complex.I ^ ((s \ t).card) * ((Ft t α : ℝ) : ℂ) := by
      intro α
      have h1 : ∏ i ∈ s, h i (gaussIter α (j i))
          = ∏ i ∈ s, ((u i (gaussIter α (j i)) : ℂ)
              + (v i (gaussIter α (j i)) : ℂ) * Complex.I) :=
        Finset.prod_congr rfl (fun i hi => hsp i (Finset.mem_range.1 hi) _)
      rw [h1, prod_eq_sum_reim s (fun i => u i (gaussIter α (j i)))
        (fun i => v i (gaussIter α (j i)))]
    have hint : ∀ t ∈ s.powerset,
        IntegrableOn (fun α : ℝ => Complex.I ^ ((s \ t).card) * ((Ft t α : ℝ) : ℂ))
          (Ioo (0 : ℝ) 1) volume := by
      intro t _
      refine Measure.integrableOn_of_bounded (M := K ^ r) (by simp [Real.volume_Ioo])
        ((measurable_const.mul
          (Complex.measurable_ofReal.comp (hFtmeas t))).aestronglyMeasurable) ?_
      filter_upwards with α
      rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact hFtbd t α
    rw [setIntegral_congr_fun measurableSet_Ioo (fun α _ => hpt α),
      integral_finset_sum _ hint]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [integral_const_mul, integral_complex_ofReal]
  have hRHS : (∏ i ∈ s, ∫ x, h i x ∂Erdos1002.gaussMeasure)
      = ∑ t ∈ s.powerset, Complex.I ^ ((s \ t).card) * ((Y t : ℝ) : ℂ) := by
    have hIu : ∀ i, i < r → Integrable (fun x => ((u i x : ℝ) : ℂ))
        Erdos1002.gaussMeasure := by
      intro i hi
      refine Integrable.of_bound
        (Complex.measurable_ofReal.comp (hum i hi)).aestronglyMeasurable K ?_
      filter_upwards with x
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hub i hi x
    have hIv : ∀ i, i < r → Integrable (fun x => ((v i x : ℝ) : ℂ))
        Erdos1002.gaussMeasure := by
      intro i hi
      refine Integrable.of_bound
        (Complex.measurable_ofReal.comp (hvm i hi)).aestronglyMeasurable K ?_
      filter_upwards with x
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hvb i hi x
    have hsplitint : ∀ i, i < r → (∫ x, h i x ∂Erdos1002.gaussMeasure)
        = (((∫ x, u i x ∂Erdos1002.gaussMeasure) : ℝ) : ℂ)
          + (((∫ x, v i x ∂Erdos1002.gaussMeasure) : ℝ) : ℂ) * Complex.I := by
      intro i hi
      have hcong : (∫ x, h i x ∂Erdos1002.gaussMeasure)
          = ∫ x, ((u i x : ℂ) + (v i x : ℂ) * Complex.I) ∂Erdos1002.gaussMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => hsp i hi x))
      rw [hcong, integral_add (hIu i hi) ((hIv i hi).mul_const Complex.I),
        integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
    have h1 : (∏ i ∈ s, ∫ x, h i x ∂Erdos1002.gaussMeasure)
        = ∏ i ∈ s, ((((∫ x, u i x ∂Erdos1002.gaussMeasure) : ℝ) : ℂ)
            + (((∫ x, v i x ∂Erdos1002.gaussMeasure) : ℝ) : ℂ) * Complex.I) :=
      Finset.prod_congr rfl (fun i hi => hsplitint i (Finset.mem_range.1 hi))
    rw [h1, prod_eq_sum_reim s (fun i => ∫ x, u i x ∂Erdos1002.gaussMeasure)
      (fun i => ∫ x, v i x ∂Erdos1002.gaussMeasure)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    congr 2
    rw [hYdef]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hmem : i ∈ t
    · rw [if_pos hmem]
      exact congrArg _ (by rw [hGfun, if_pos hmem])
    · rw [if_neg hmem]
      exact congrArg _ (by rw [hGfun, if_neg hmem])
  -- the real estimate, slot by slot
  have hdef : ∀ t : Finset ℕ, |X t - Y t| ≤ C₀ * ρ ^ M * K ^ r := by
    intro t
    exact hreal n j hj (G t) K hK (fun i hi => hGm t i hi)
      (fun i hi => hGbd t i hi) (fun i hi => hGbv t i hi)
  rw [hLHS, hRHS, ← Finset.sum_sub_distrib]
  have hcomb : ∀ t ∈ s.powerset,
      Complex.I ^ ((s \ t).card) * ((X t : ℝ) : ℂ)
          - Complex.I ^ ((s \ t).card) * ((Y t : ℝ) : ℂ)
        = Complex.I ^ ((s \ t).card) * (((X t - Y t : ℝ)) : ℂ) := by
    intro t _
    push_cast
    ring
  rw [Finset.sum_congr rfl hcomb]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ t ∈ s.powerset,
      ‖Complex.I ^ ((s \ t).card) * (((X t - Y t : ℝ)) : ℂ)‖ ≤ C₀ * ρ ^ M * K ^ r := by
    intro t _
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact hdef t
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
  rw [nsmul_eq_mul, Finset.card_powerset, hsdef, Finset.card_range]
  have hnn : (0 : ℝ) ≤ C₀ * ρ ^ M * K ^ r := by positivity
  push_cast
  exact le_of_eq (by ring)

/-! ## 6. Step 2 of the §4 body: the zero mode, PROVED

`ErrorShape.zero_mode_factorization` is the manuscript's

> If every `v_ℓ = 0`, the integrand is a product of digit functions.
> Repeated use of Lemma 3.2 and (25) factors its mean with error
> `L^{O_{r,D}(1)} ρ^{200H}`.

Its docstring lists three obstructions; all three are now discharged:

* the `BV(0,1)` bound on `g_ℓ`, `Bridge.digitObs_re_bv` / `_im_bv`;
* complex versus real observables, §5 above (`lebesgue_multiblock_complex`);
* `dα` versus `dν`, §2 above (`lebesgue_sub_gauss_le`).

The statement is reproduced **token-identically** from
`Kwon1002/ErrorShape.lean` lines 216-222 (only the name carries the
suffix), and is proved outright: no `sorry`, and the only inputs are
sorry-free. -/
theorem zero_mode_factorization_f (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
        ‖modeTerm n r j c 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (D * r) * ρ ^ (200 * Hscale n) := by
  classical
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- `r = 0`: both sides of (27) are the empty product `1`, defect `0`
    refine ⟨1, 1 / 2, one_pos, by norm_num, by norm_num, ?_⟩
    filter_upwards with n
    intro j hj F c hc
    have h1 : modeTerm n 0 j c 0 = 1 := by
      unfold modeTerm
      simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, one_mul]
      rw [Prop4Final.torusChar_zero, setIntegral_const]
      simp
    have hz : (Lnorm n) ^ (D * ((0 : ℕ) : ℝ)) = 1 := by
      rw [Nat.cast_zero, mul_zero, Real.rpow_zero]
    rw [h1, Finset.range_zero, Finset.prod_empty, sub_self, norm_zero, hz]
    positivity
  obtain ⟨C₁, ρ₁, hC₁, hρ₁0, hρ₁1, hmb⟩ := lebesgue_multiblock_complex r hr
  refine ⟨C₁ * 2 ^ r / ρ₁, ρ₁, by positivity, hρ₁0, hρ₁1, ?_⟩
  filter_upwards [hLtend.eventually (eventually_ge_atTop (1 : ℝ))] with n hL1
  intro j hj F c hc
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hLD1 : (1 : ℝ) ≤ (Lnorm n) ^ D := Real.one_le_rpow hL1 hD.le
  have hLD0 : (0 : ℝ) ≤ (Lnorm n) ^ D := le_trans zero_le_one hLD1
  set K : ℝ := 2 * (Lnorm n) ^ D with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hdm : ∀ i : ℕ, Measurable (Prop4Final.digitObs c i) := by
    intro i
    exact (measurable_from_top (f := fun a : ℕ => c i a 0)).comp
      (Prop42.measurable_digitNat 0)
  have hnorm : ∀ i, i < r → ∀ x : ℝ, ‖Prop4Final.digitObs c i x‖ ≤ (Lnorm n) ^ D :=
    fun i hi x => Prop4Final.norm_digitObs_le r D (Lnorm n) F c hc i hi x
  have happ := hmb n j hj (Prop4Final.digitObs c)
    (fun i x => (Prop4Final.digitObs c i x).re)
    (fun i x => (Prop4Final.digitObs c i x).im) K hK0
    (fun i _ x => (Complex.re_add_im _).symm)
    (fun i _ => Complex.measurable_re.comp (hdm i))
    (fun i _ => Complex.measurable_im.comp (hdm i))
    (fun i hi x => le_trans (Complex.abs_re_le_norm _)
      (le_trans (hnorm i hi x) (by rw [hKdef]; linarith)))
    (fun i hi x => le_trans (Complex.abs_im_le_norm _)
      (le_trans (hnorm i hi x) (by rw [hKdef]; linarith)))
    (fun i hi => Bridge.digitObs_re_bv r D (Lnorm n) hLD0 F c hc i hi)
    (fun i hi => Bridge.digitObs_im_bv r D (Lnorm n) hLD0 F c hc i hi)
  -- the zero-mode defect *is* the multi-block defect (`Prop4Final`)
  rw [Prop4Final.zero_mode_defect_eq n r D j F c hc]
  have hp1 : ∀ α : ℝ, (∏ ℓ : Fin r, Prop4Final.digitObs c ℓ (gaussIter α (j ℓ)))
      = ∏ i ∈ Finset.range r, Prop4Final.digitObs c i (gaussIter α (j i)) :=
    fun α => Fin.prod_univ_eq_prod_range
      (fun ℓ => Prop4Final.digitObs c ℓ (gaussIter α (j ℓ))) r
  have hp2 : (∏ ℓ : Fin r, ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure)
      = ∏ i ∈ Finset.range r, ∫ x, Prop4Final.digitObs c i x ∂Erdos1002.gaussMeasure :=
    Fin.prod_univ_eq_prod_range
      (fun ℓ => ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure) r
  rw [setIntegral_congr_fun measurableSet_Ioo (fun α _ => hp1 α), hp2]
  refine le_trans happ ?_
  -- `K^r = 2^r L^{Dr}`
  have hKr : K ^ r = 2 ^ r * (Lnorm n) ^ (D * (r : ℝ)) := by
    rw [hKdef, mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((Lnorm n) ^ D) r, ← Real.rpow_mul hL0.le]
  -- `ρ^{⌊200H⌋} ≤ ρ^{200H}/ρ`
  have hfloor : 200 * Hscale n - 1 ≤ ((⌊200 * Hscale n⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (200 * Hscale n)
    linarith
  have hpow : ρ₁ ^ (⌊200 * Hscale n⌋₊) ≤ ρ₁ ^ (200 * Hscale n) / ρ₁ := by
    have h1 : ρ₁ ^ (((⌊200 * Hscale n⌋₊ : ℕ)) : ℝ) ≤ ρ₁ ^ (200 * Hscale n - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hρ₁0 hρ₁1.le hfloor
    have h2 : ρ₁ ^ (200 * Hscale n - 1) = ρ₁ ^ (200 * Hscale n) / ρ₁ := by
      rw [Real.rpow_sub hρ₁0, Real.rpow_one]
    rw [← Real.rpow_natCast ρ₁ (⌊200 * Hscale n⌋₊)]
    rw [h2] at h1
    exact h1
  have hLrpow : (0 : ℝ) < (Lnorm n) ^ (D * (r : ℝ)) := Real.rpow_pos_of_pos hL0 _
  calc C₁ * ρ₁ ^ (⌊200 * Hscale n⌋₊) * K ^ r
      ≤ C₁ * (ρ₁ ^ (200 * Hscale n) / ρ₁) * (2 ^ r * (Lnorm n) ^ (D * (r : ℝ))) := by
        rw [hKr]
        have hb : (0 : ℝ) ≤ 2 ^ r * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC₁.le) hb
    _ = C₁ * 2 ^ r / ρ₁ * (Lnorm n) ^ (D * (r : ℝ)) * ρ₁ ^ (200 * Hscale n) := by
        field_simp

/-! ## 7. The two assigned targets

`prop_4_1_error_shape_f` is `Kwon1002.Prop41.prop_4_1_error_shape`
(display (30)) reproduced token-identically, and
`prop_4_1_marked_factorization_f` is `Kwon1002.prop_4_1_marked_factorization`
(display (27), the canonical §4 statement of `Kwon1002/Section4.lean`),
also token-identical.

The assembly is `ErrorShape.prop_4_1_error_shape'` / 
`Prop4Final.prop_4_1_error_shape''` with **two** of its three inputs now
proved rather than assumed:

* step 1, `integral_eq_sum_modeTerm`, proved in `Prop4Final`;
* step 2, `zero_mode_factorization`, proved above;
* step 3, `nonzero_mode_small`, **the single remaining sorried input**,
  consumed here by name as `ErrorShape.nonzero_mode_small`.

So display (30), and with it Proposition 4.1, now rests on exactly one
unproved statement, the `v_s ≠ 0` branch of §4. -/
theorem prop_4_1_error_shape_of_nonzero (r : ℕ) (D : ℝ) (hD : 0 < D)
    (hnz : ∃ C c₀ ρ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
      ∀ v ∈ modeTuples r D (Lnorm n), v ≠ 0 →
        ‖modeTerm n r j c v‖
          ≤ C * (Lnorm n) ^ (D * r) *
              (Real.exp (-c₀ * Real.sqrt (Lnorm n)) + Real.exp (-c₀ * Hscale n)
                + ρ ^ (c₀ * Hscale n))) :
    ∃ B C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ B * deltaScale c ρ n := by
  classical
  obtain ⟨C₂, ρ₂, hC₂, hρ₂0, hρ₂1, h2⟩ := zero_mode_factorization_f r D hD
  obtain ⟨C₃, c₃, ρ₃, hC₃, hc₃, hρ₃0, hρ₃1, h3⟩ := hnz
  have hc0 : (0 : ℝ) < min c₃ 200 := lt_min hc₃ (by norm_num)
  have hr0 : (0 : ℝ) < max ρ₂ ρ₃ := lt_of_lt_of_le hρ₂0 (le_max_left _ _)
  have hr1 : max ρ₂ ρ₃ < 1 := max_lt hρ₂1 hρ₃1
  refine ⟨2 * D * r, C₂ + 3 ^ r * C₃, min c₃ 200, max ρ₂ ρ₃,
    add_pos hC₂ (mul_pos (by positivity) hC₃), hc0, hr0, hr1, ?_⟩
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h2, h3, hLtend.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn2 hn3 hL1
  intro j hj F hF
  obtain ⟨cc, hcc⟩ := exists_representsPD r D (Lnorm n) F hF
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hH1 : (1 : ℝ) ≤ Hscale n := by
    rw [Hscale]; exact Real.one_le_rpow hL1 (by norm_num)
  have hH0 : (0 : ℝ) ≤ Hscale n := le_trans zero_le_one hH1
  have hX1 : (1 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) :=
    Real.one_le_rpow hL1 (by positivity)
  have hX0 : (0 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) := le_trans zero_le_one hX1
  have hY : (Lnorm n) ^ (2 * D * (r : ℝ))
      = (Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  have hδ0 : (0 : ℝ) ≤ deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := deltaScale_nonneg hr0 n
  have hA : ‖modeTerm n r j cc 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C₂ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    refine le_trans (hn2 j hj F cc hcc) ?_
    have hbr := zero_branch_le_deltaScale (c := min c₃ 200) (ρ := max ρ₂ ρ₃) (ρ₂ := ρ₂)
      n hρ₂0 hρ₂1 (le_max_left _ _) hc0 (min_le_right _ _) hH0
    have hpos : (0 : ℝ) ≤ C₂ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hbr hpos
  have hBnd : ∀ v ∈ (modeTuples r D (Lnorm n)).erase 0,
      ‖modeTerm n r j cc v‖
        ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    intro v hv
    rcases Finset.mem_erase.1 hv with ⟨hv0, hvmem⟩
    refine le_trans (hn3 j hj F cc hcc v hvmem hv0) ?_
    have hbr := nonzero_branch_le_deltaScale (c := min c₃ 200) (ρ := max ρ₂ ρ₃)
      (c₃ := c₃) (ρ₃ := ρ₃) n hr0 hr1 hρ₃0 (le_max_right _ _) hc0 (min_le_left _ _) hH0
    have hpos : (0 : ℝ) ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hbr hpos
  have hcardS : (((modeTuples r D (Lnorm n)).erase 0).card : ℝ)
      ≤ 3 ^ r * (Lnorm n) ^ (D * (r : ℝ)) := by
    refine le_trans ?_ (card_modeTuples_le r D (Lnorm n) hL1 hD.le)
    exact_mod_cast Finset.card_erase_le
  have hsum : ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, ‖modeTerm n r j cc v‖
      ≤ (3 ^ r * (Lnorm n) ^ (D * (r : ℝ))) *
          (C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hBnd) ?_
    rw [nsmul_eq_mul]
    have hb0 : (0 : ℝ)
        ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
      have hpp : (0 : ℝ) ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
      exact mul_nonneg hpp hδ0
    exact mul_le_mul_of_nonneg_right hcardS hb0
  have h0mem : (0 : Fin r → ℤ) ∈ modeTuples r D (Lnorm n) := by
    rw [modeTuples, Fintype.mem_piFinset]
    intro i
    have hzero : (0 : Fin r → ℤ) i = 0 := rfl
    rw [hzero, modeBox, Finset.mem_Icc]
    exact ⟨neg_nonpos.2 (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  rw [Prop4Final.integral_eq_sum_modeTerm' n r D j F cc hcc,
    ← Finset.add_sum_erase _ (modeTerm n r j cc) h0mem]
  have hrw : (modeTerm n r j cc 0
        + ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, modeTerm n r j cc v)
      - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)
      = (modeTerm n r j cc 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ))
        + ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, modeTerm n r j cc v := by
    ring
  rw [hrw]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add le_rfl (norm_sum_le _ _)) ?_
  refine le_trans (add_le_add hA hsum) ?_
  rw [hY]
  have hXX : (Lnorm n) ^ (D * (r : ℝ))
      ≤ (Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)) := by
    nlinarith
  have hstep : C₂ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n
      ≤ C₂ * ((Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)))
          * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    have h1 : C₂ * (Lnorm n) ^ (D * (r : ℝ))
        ≤ C₂ * ((Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ))) :=
      mul_le_mul_of_nonneg_left hXX hC₂.le
    exact mul_le_mul_of_nonneg_right h1 hδ0
  nlinarith [hδ0, hX0, hC₃.le]

/-- **Display (30)**, reproduced token-identically from
`Kwon1002.Prop41.prop_4_1_error_shape` (only the name carries the suffix;
diffed).  It is `prop_4_1_error_shape_of_nonzero` fed with the one
remaining sorried input of the §4 body, `ErrorShape.nonzero_mode_small`
(the `v_s ≠ 0` branch).  That `prop_4_1_error_shape_of_nonzero` is itself
axiom-clean is the machine-checked form of "this is the *only* debt". -/
theorem prop_4_1_error_shape_f (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ B C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ B * deltaScale c ρ n :=
  prop_4_1_error_shape_of_nonzero r D hD (nonzero_mode_small r D hD)

end

end Prop41Final

/-! ## 8. Proposition 4.1 in `Kwon1002`'s own namespace

Reproduced token-identically from `Kwon1002/Section4.lean` lines 137-144;
placing it in `namespace Kwon1002` makes every identifier resolve exactly
as it does there. -/

theorem prop_4_1_marked_factorization_f (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨B, C, c, ρ, hC, hc, hρ0, hρ1, hbd⟩ := Prop41Final.prop_4_1_error_shape_f r D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbd, Prop41.eventually_rpow_mul_deltaScale_le A B c ρ hc hρ0 hρ1]
    with n hn harith j hj F hF
  calc ‖(∫ α in Ioo (0 : ℝ) 1,
            ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C * (Lnorm n) ^ B * Prop41.deltaScale c ρ n := hn j hj F hF
    _ = C * ((Lnorm n) ^ B * Prop41.deltaScale c ρ n) := by ring
    _ ≤ C * (Lnorm n) ^ (-A) := mul_le_mul_of_nonneg_left harith hC.le

end Kwon1002

/-
## Summary

TARGETS, both reproduced TOKEN-IDENTICALLY (mechanical line diff run; the
only difference is the theorem name):

  `Kwon1002.Prop41Final.prop_4_1_error_shape_f`
      = `Kwon1002.Prop41.prop_4_1_error_shape`      (Prop41.lean 303-310)
  `Kwon1002.prop_4_1_marked_factorization_f`
      = `Kwon1002.prop_4_1_marked_factorization`    (Section4.lean 137-144)

and, on the way,

  `Kwon1002.Prop41Final.zero_mode_factorization_f`
      = `Kwon1002.ErrorShape.zero_mode_factorization` (ErrorShape.lean 216-222)

PROVED OUTRIGHT.  Axioms machine-checked on every theorem below; each is
exactly `[propext, Classical.choice, Quot.sound]`.  The `#print axioms`
lines were then removed.

  §1  `deltaScale_eq_bracket`, `zero_branch_le_deltaScale_log`,
      `eventually_zero_branch_le_deltaScale`, `deltaBracket_lt_zero_branch`
  §2  `measurable_wGL`, `wGL_nonneg`, `wGL_le`, `wGL_lip`,
      `integral_Ioc_eq_gauss_mul`, `integral_wGL`, `lebesgue_sub_gauss_le`
  §3  `gaussMeasure_singleton_one`, `gaussMeasure_ae_Ioo`,
      `gaussMeasure_Ioo_eq_one`, `gaussMeasure_restrict_Ioo`
  §4  `gaussIter_add`, `lebesgue_multiblock`
  §5  `prod_eq_sum_reim`, `lebesgue_multiblock_complex`
  §6  `zero_mode_factorization_f`                    <- step 2 of the §4 body
  §7  `prop_4_1_error_shape_of_nonzero`              <- (30) minus one input

SORRIED RESULTS CONSUMED: exactly one,

  `Kwon1002.ErrorShape.nonzero_mode_small`  (the `v_s ≠ 0` branch of §4).

That it is the only one is itself machine-checked, not asserted:
`prop_4_1_error_shape_of_nonzero` takes the nonzero-mode bound as an
explicit hypothesis and is axiom-clean, and `prop_4_1_error_shape_f` is
literally `prop_4_1_error_shape_of_nonzero r D hD (nonzero_mode_small r D hD)`
- so the hypothesis is also definitionally the sorried statement, no
paraphrase.  `prop_4_1_error_shape_f` and
`prop_4_1_marked_factorization_f` therefore carry axioms
`[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` coming
from that one branch and nothing else.

STATE OF §4 AFTER THIS FILE.  `ErrorShape`'s three-step decomposition of
the manuscript's proof of Proposition 4.1 was 0/3 proved; `Prop4Final`
closed step 1; this file closes step 2.  One of three remains.

CONSUMED FROM OTHER FILES (all sorry-free):
  `Kwon1002.Bridge`, `good_tuple_multiblock_mixing'` (the discharged
    Wave-1 mixing input, consumed by name), `digitObs_re_bv`,
    `digitObs_im_bv`;
  `Kwon1002.Prop4Final`, `integral_eq_sum_modeTerm'`, `zero_mode_defect_eq`,
    `digitObs`, `norm_digitObs_le`, `torusChar_zero`;
  `Kwon1002.ErrorShape`, `RepresentsPD`, `modeBox`, `modeTuples`,
    `card_modeTuples_le`, `exists_representsPD`, `deltaScale_nonneg`,
    `zero_branch_le_deltaScale`, `nonzero_branch_le_deltaScale`;
  `Kwon1002.Prop41`, `BVBoundedBy`, `deltaScale`,
    `eventually_rpow_mul_deltaScale_le`;
  `Kwon1002.Prop42`, `measurable_digitNat`;
  `Kwon1002`, `measurable_gaussIter`, `gaussIter`, `digit`, `Lnorm`, `Hscale`;
  `Erdos1002` (Wang substrate, MIT), `gaussMeasure`,
    `gaussMeasure_eq_volume_withDensity`,
    `gaussMeasure_withDensity_lebesgueOverGaussDensity`,
    `lebesgueOverGaussDensityReal(_bounds)`, `gaussMeasure_unit_ae`,
    `integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate`,
    `integrable_gaussTransfer_iterate_of_unit_bounds`,
    `gaussTransfer_iterate_unit_bounds`,
    `abs_gaussTransfer_iterate_sub_integral_le`, `integral_comp_gaussOrbit`.

## Findings

**F1 (the assigned finding, settled, and the recorded form is too
strong).**  `ErrorShape` records "display (30) carries an implicit upper
constraint on `c`", namely `c ≤ 200`, needed so that the zero-mode error
`ρ^{200H}` fits under the bracket's third term `ρ^{cH}`.  Three machine-
checked statements settle it (§1):

  (a) `zero_branch_le_deltaScale_log`, the *middle* term gives a second,
      independent sufficient constraint `c ≤ 200·(−log ρ)`; so the true
      sufficient region is `c ≤ max (200) (200·(−log ρ))`, not `c ≤ 200`.
  (b) `eventually_zero_branch_le_deltaScale`, under (18) **as the
      manuscript writes it**, `H = L^{3/4}`, there is *no* constraint at
      all: for every `c > 0` and every `ρ ∈ (0,1)`, `ρ^{200H} ≤ δ_n` for
      all large `n`, because `ρ^{200H} = e^{-200|log ρ|L^{3/4}}` is
      eventually below the bracket's own first term `e^{-cL^{1/2}}`.  The
      recorded constraint is an artefact of asking for the inequality at
      every `n` instead of eventually.
  (c) `deltaBracket_lt_zero_branch`, but it is genuinely needed under the
      **weaker** reading of (18) that the proof of 4.1 otherwise permits
      and that `Kwon1002/Prop41.lean`'s own docstring identifies as all
      that is consumed, `H ≥ L^{1/2}`.  At `H = L^{1/2}`, if both
      `c > 200` and `c > 200·(−log ρ)`, the whole bracket of (30) is
      *strictly smaller* than `ρ^{200H}` for all large `L`.

  Net, for the referee report: (30) is sound as printed, but only because
  (18) pins `H = L^{3/4} ≫ L^{1/2}`.  The display and the sentence above
  it are stated as if any admissible `H` would do; if `H` is allowed the
  window `L^{1/2} ≤ H ≪ L`, (30) needs the unstated side condition
  `c ≤ max (200) (200·(−log ρ))`.  Two lines of the manuscript are
  therefore coupled in a way it does not say.

**F2 (the `dα`-versus-`dν` gap is not a `ρ^{200H}` estimate, it is
free).**  `Prop4Final.zero_mode_defect_eq` and
`ErrorShape.zero_mode_factorization` both describe the outer-measure
mismatch as "a `ρ^{200H}` change by Gauss-Kuzmin", i.e. as an application
of the mixing input.  It is not: the Radon-Nikodym weight
`w = dλ/dν = log 2·(1+x)` is *Lipschitz* with constant `log 2` and mean
`1`, so the Perron-Frobenius adjoint gives the change of measure directly
from Wang's contraction (`lebesgue_sub_gauss_le`, §2), with the explicit
constant `(527/540)^{j_1}·log 2·‖g‖_∞` and no mixing lemma at all.  The
route matters: the block-list mixing machinery of `MixingBV` requires
every block gap to be `≥ M`, and a weight sitting at time `0` has gap `0`,
so the mismatch could **not** in fact have been discharged the way both
docstrings propose.

**F3 (Kwon's (17) is applied at `s = r`, not `s = r + 1`).**  Related to
F2 and worth stating positively: because the weight is handled by the
adjoint rather than as an extra block, the zero-mode branch uses Lemma 3.2
with exactly the `r` blocks of the good tuple.  The constant of (30)
consequently loses only `2^r` (complex → real, §5) and `1/ρ` (the floor
`⌊200H⌋ ≥ 200H − 1`), not an extra factor of `K`.

**F4 (`r = 0` is not vacuous in (30)).**  `zero_mode_factorization` is
quantified over all `r : ℕ`, and every multi-block input needs `0 < r`
(`Bridge.good_tuple_multiblock_mixing'` reads `j 0`).  `r = 0` is true
but for an unrelated reason, both sides of (27) are the empty product -
and is proved here as a separate branch.  A `0 < r` hypothesis on the §4
statements would be closer to the manuscript, which writes `j_1 < ⋯ < j_r`.
-/
