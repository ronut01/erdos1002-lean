import Kwon1002.Bridge
import Kwon1002.Prop42

/-!
# Scratch (`errorshape`): the three §4-body inputs of `Kwon1002/ErrorShape.lean`

Targets, all three reproduced **token-identically** (diffed line-by-line
against `Kwon1002/ErrorShape.lean` lines 190-195, 216-222 and 240-249; the
only difference found was the proof delimiter `:= by` versus `:=`):

* `integral_eq_sum_modeTerm`, **PROVED** (it is
  `Prop4Final.integral_eq_sum_modeTerm'`, already available).
* `zero_mode_factorization`, **PROVED OUTRIGHT**, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.
* `nonzero_mode_small`, **PROVED from one sorried input**,
  `nonzero_mode_three_step`, which is the manuscript's own three-step chain
  for the `v_s ≠ 0` branch with its obstruction named term by term.

## What closes the zero mode

`Bridge` proved the two things `zero_mode_factorization`'s docstring listed
as missing dynamics: the `BV(0,1)` bound on the digit observable
(`Bridge.digitObs_re_bv` / `digitObs_im_bv`, via display (24)'s `ℓ¹` mass -
*not* via the jump count, which only gives `O(L^{2D})`) and the good-tuple
mixing (`Bridge.good_tuple_multiblock_mixing'`).  Two bookkeeping gaps were
left.  Both are closed here:

* **complex versus real** (§§2,3,5).  `prod_complex_expand` writes
  `∏_ℓ (u_ℓ + i v_ℓ)` as `∑_{t ⊆ [r]} i^{|[r]∖t|} ∏_ℓ (real selector)` by
  `Finset.prod_add`, and `defect_expand` shows that the *same* expansion of
  the integral and of the product of means turns the zero-mode defect of
  (27) into `2^r` signed **real** multi-block defects.  The cost is the
  advertised `2^r` in the constant; each selected observable is `BV(0,1)`
  with norm `2L^D` (`selObs_bv`) and globally bounded by `L^D`
  (`abs_selObs_le`).
* **Lebesgue `dα` versus Gauss `dν`** (§6).  This is the one place where
  new dynamics were needed, and it is *not* a Gauss-Kuzmin black box: the
  Radon-Nikodym weight `dLeb/dν = log 2 · (1+x)` is nonnegative, bounded by
  `2 log 2` and Lipschitz with constant `log 2` on the state interval, so
  Wang's `abs_gaussTransfer_iterate_sub_integral_le` moves `L^m w` to the
  constant `1 = ∫ w dν` (`gauss_mean_density_eq_one`) at rate
  `(527/540)^m`, and the correlation identity
  `integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate` converts the
  change of measure into exactly that error (`lebesgue_sub_gauss_le`).

**Finding (the transfer depth is free).**  The natural worry is that the
`dα → dν` transfer eats into the mixing budget: the transfer wants depth
`m` and the mixing wants a start gap `M`, and `(19)` only supplies
`j_1 ≥ 200H` once.  It does not.  The transfer is applied with `m = j_1`
itself, to the *shifted* product `Ĝ(y) = ∏_ℓ g_ℓ(T^{j_ℓ - j_1} y)`, whose
own gap structure is irrelevant to `lebesgue_sub_gauss_le`
(`prodSel_lebesgue_sub_gauss`); the mixing is then applied to the original
times `j` with the full `M = ⌊200H⌋`.  Invariance of `ν`
(`Erdos1002.map_gaussMap_iterate_gaussMeasure`) is what makes the two
`ν`-means agree.  So no splitting of the `200H` budget is needed, and the
rate produced is `ρ^{200H}` with `ρ = max(ρ_mix, 527/540)` exactly as (27)
asserts, with `C = 2^r(log 2 + 2^r C_mix)/ρ`.

## Sorried results consumed

Exactly one, stated in this file: `nonzero_mode_three_step`.
`ErrorShape`'s own `integral_eq_sum_modeTerm`, `zero_mode_factorization`
and `nonzero_mode_small` are **not** consumed, they are re-proved here.

Everything imported from `Bridge`, `MixingBV`, `Prop4Final`, `Display22`,
`AntiConcentration` and the Wang substrate is sorry-free.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace ZeroMode

open Prop41 ErrorShape

noncomputable section

/-! ## 1. Step 1 of the §4 body: the digit-Fourier expansion -/

theorem integral_eq_sum_modeTerm (n r : ℕ) (D : ℝ) (j : ℕ → ℕ)
    (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D (Lnorm n) F c) :
    (∫ α in Ioo (0 : ℝ) 1,
        ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      = ∑ v ∈ modeTuples r D (Lnorm n), modeTerm n r j c v :=
  Prop4Final.integral_eq_sum_modeTerm' n r D j F c hc

/-! ## 2. The `2^r` real observable families -/

/-- The real observable selected by the subset `t`: the real part at the
places of `t`, the imaginary part elsewhere. -/
def selObs (c : ℕ → ℕ → ℤ → ℂ) (t : Finset ℕ) (ℓ : ℕ) (x : ℝ) : ℝ :=
  if ℓ ∈ t then (Prop4Final.digitObs c ℓ x).re else (Prop4Final.digitObs c ℓ x).im

theorem selObs_eq_re {c : ℕ → ℕ → ℤ → ℂ} {t : Finset ℕ} {ℓ : ℕ} (h : ℓ ∈ t) :
    selObs c t ℓ = fun x => (Prop4Final.digitObs c ℓ x).re := by
  funext x; simp only [selObs, if_pos h]

theorem selObs_eq_im {c : ℕ → ℕ → ℤ → ℂ} {t : Finset ℕ} {ℓ : ℕ} (h : ℓ ∉ t) :
    selObs c t ℓ = fun x => (Prop4Final.digitObs c ℓ x).im := by
  funext x; simp only [selObs, if_neg h]

theorem measurable_selObs (c : ℕ → ℕ → ℤ → ℂ) (t : Finset ℕ) (ℓ : ℕ) :
    Measurable (selObs c t ℓ) := by
  classical
  have hd : Measurable fun x : ℝ => digit x 0 := Prop42.measurable_digitNat 0
  by_cases h : ℓ ∈ t
  · rw [selObs_eq_re h]
    exact (measurable_from_top (f := fun a : ℕ => (c ℓ a 0).re)).comp hd
  · rw [selObs_eq_im h]
    exact (measurable_from_top (f := fun a : ℕ => (c ℓ a 0).im)).comp hd

/-- Every selected observable is globally bounded by the `ℓ¹` mass `L^D`. -/
theorem abs_selObs_le (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D L F c) (t : Finset ℕ) (ℓ : ℕ) (hℓ : ℓ < r) (x : ℝ) :
    |selObs c t ℓ x| ≤ L ^ D := by
  have hb := Prop4Final.norm_digitObs_le r D L F c hc ℓ hℓ x
  unfold selObs
  split
  · exact le_trans (Complex.abs_re_le_norm _) hb
  · exact le_trans (Complex.abs_im_le_norm _) hb

/-- Every selected observable lies in `BV(0,1)` with norm `2 L^D`; this is
`Bridge.digitObs_re_bv` / `Bridge.digitObs_im_bv`. -/
theorem selObs_bv (r : ℕ) (D L : ℝ) (hL : 0 ≤ L ^ D) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (t : Finset ℕ) (ℓ : ℕ)
    (hℓ : ℓ < r) : BVBoundedBy (2 * L ^ D) (selObs c t ℓ) := by
  classical
  by_cases h : ℓ ∈ t
  · rw [selObs_eq_re h]
    exact Bridge.digitObs_re_bv r D L hL F c hc ℓ hℓ
  · rw [selObs_eq_im h]
    exact Bridge.digitObs_im_bv r D L hL F c hc ℓ hℓ

/-! ## 3. The `2^r` expansion of a complex product -/

/-- `∏ (u + i v)` expands into `2^r` signed real products. -/
theorem prod_complex_expand (r : ℕ) (z : ℕ → ℂ) :
    ∏ ℓ ∈ Finset.range r, z ℓ
      = ∑ t ∈ (Finset.range r).powerset,
          Complex.I ^ ((Finset.range r) \ t).card *
            ((∏ ℓ ∈ Finset.range r,
                (if ℓ ∈ t then (z ℓ).re else (z ℓ).im) : ℝ) : ℂ) := by
  classical
  calc ∏ ℓ ∈ Finset.range r, z ℓ
      = ∏ ℓ ∈ Finset.range r, (((z ℓ).re : ℂ) + ((z ℓ).im : ℂ) * Complex.I) :=
        Finset.prod_congr rfl (fun ℓ _ => (Complex.re_add_im (z ℓ)).symm)
    _ = ∑ t ∈ (Finset.range r).powerset,
          (∏ ℓ ∈ t, ((z ℓ).re : ℂ)) *
            ∏ ℓ ∈ (Finset.range r) \ t, (((z ℓ).im : ℂ) * Complex.I) :=
        Finset.prod_add _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        rw [Finset.mem_powerset] at ht
        have hreal : (∏ ℓ ∈ Finset.range r, (if ℓ ∈ t then (z ℓ).re else (z ℓ).im))
            = (∏ ℓ ∈ (Finset.range r) \ t, (z ℓ).im) * (∏ ℓ ∈ t, (z ℓ).re) := by
          rw [← Finset.prod_sdiff ht]
          congr 1
          · exact Finset.prod_congr rfl
              (fun ℓ hℓ => by rw [if_neg (Finset.mem_sdiff.1 hℓ).2])
          · exact Finset.prod_congr rfl (fun ℓ hℓ => by rw [if_pos hℓ])
        rw [hreal, Finset.prod_mul_distrib, Finset.prod_const]
        push_cast
        ring

/-! ## 4. Measurability and boundedness bookkeeping -/

theorem measurable_gaussIter (k : ℕ) : Measurable (fun α : ℝ => gaussIter α k) :=
  Erdos1002.measurable_gaussOrbit k

theorem measurable_digitObs (c : ℕ → ℕ → ℤ → ℂ) (ℓ : ℕ) :
    Measurable (Prop4Final.digitObs c ℓ) :=
  (measurable_from_top (f := fun a : ℕ => c ℓ a 0)).comp (Prop42.measurable_digitNat 0)

theorem integrable_digitObs (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) :
    Integrable (Prop4Final.digitObs c ℓ) Erdos1002.gaussMeasure :=
  Integrable.of_bound (measurable_digitObs c ℓ).aestronglyMeasurable (L ^ D)
    (Eventually.of_forall (fun x => Prop4Final.norm_digitObs_le r D L F c hc ℓ hℓ x))

theorem re_integral_eq (f : ℝ → ℂ) (hf : Integrable f Erdos1002.gaussMeasure) :
    (∫ x, f x ∂Erdos1002.gaussMeasure).re
      = ∫ x, (f x).re ∂Erdos1002.gaussMeasure := by
  simpa using (Complex.reCLM.integral_comp_comm hf).symm

theorem im_integral_eq (f : ℝ → ℂ) (hf : Integrable f Erdos1002.gaussMeasure) :
    (∫ x, f x ∂Erdos1002.gaussMeasure).im
      = ∫ x, (f x).im ∂Erdos1002.gaussMeasure := by
  simpa using (Complex.imCLM.integral_comp_comm hf).symm

theorem measurable_prodSel (r : ℕ) (c : ℕ → ℕ → ℤ → ℂ) (t : Finset ℕ) (j : ℕ → ℕ) :
    Measurable
      (fun α : ℝ => ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ))) :=
  Finset.measurable_prod _
    (fun ℓ _ => (measurable_selObs c t ℓ).comp (measurable_gaussIter (j ℓ)))

theorem abs_prodSel_le (r : ℕ) (D L : ℝ) (_hL : 0 ≤ L ^ D) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (t : Finset ℕ) (j : ℕ → ℕ)
    (α : ℝ) :
    |∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ))| ≤ (L ^ D) ^ r := by
  rw [Finset.abs_prod]
  calc ∏ ℓ ∈ Finset.range r, |selObs c t ℓ (gaussIter α (j ℓ))|
      ≤ ∏ _ℓ ∈ Finset.range r, L ^ D :=
        Finset.prod_le_prod (fun ℓ _ => abs_nonneg _)
          (fun ℓ hℓ => abs_selObs_le r D L F c hc t ℓ (Finset.mem_range.1 hℓ) _)
    _ = (L ^ D) ^ r := by simp

/-! ## 5. The zero-mode defect, expanded into `2^r` real defects -/

theorem defect_expand (n r : ℕ) (D : ℝ) (hL : 0 ≤ (Lnorm n) ^ D) (j : ℕ → ℕ)
    (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D (Lnorm n) F c) :
    modeTerm n r j c 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)
      = ∑ t ∈ (Finset.range r).powerset,
          Complex.I ^ ((Finset.range r) \ t).card *
            (((∫ α in Ioo (0 : ℝ) 1,
                  ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)))
                - ∏ ℓ ∈ Finset.range r,
                    ∫ x, selObs c t ℓ x ∂Erdos1002.gaussMeasure : ℝ) : ℂ) := by
  classical
  rw [Prop4Final.zero_mode_defect_eq n r D j F c hc]
  -- the integrand, expanded pointwise
  have hIpt : ∀ α : ℝ,
      (∏ ℓ : Fin r, Prop4Final.digitObs c ℓ (gaussIter α (j ℓ)))
        = ∑ t ∈ (Finset.range r).powerset,
            Complex.I ^ ((Finset.range r) \ t).card *
              ((∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)) : ℝ) : ℂ) := by
    intro α
    rw [Fin.prod_univ_eq_prod_range
      (fun ℓ => Prop4Final.digitObs c ℓ (gaussIter α (j ℓ))) r]
    simpa only [selObs] using
      prod_complex_expand r (fun ℓ => Prop4Final.digitObs c ℓ (gaussIter α (j ℓ)))
  have hcong : (∫ α in Ioo (0 : ℝ) 1, ∏ ℓ : Fin r, Prop4Final.digitObs c ℓ (gaussIter α (j ℓ)))
      = ∫ α in Ioo (0 : ℝ) 1, ∑ t ∈ (Finset.range r).powerset,
          Complex.I ^ ((Finset.range r) \ t).card *
            ((∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)) : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioo (fun α _ => hIpt α)
  have hint : ∀ t ∈ (Finset.range r).powerset,
      IntegrableOn (fun α : ℝ => Complex.I ^ ((Finset.range r) \ t).card *
        ((∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)) : ℝ) : ℂ))
        (Ioo (0 : ℝ) 1) volume := by
    intro t _
    refine Measure.integrableOn_of_bounded (M := ((Lnorm n) ^ D) ^ r)
      (by simp [Real.volume_Ioo]) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp
        (measurable_prodSel r c t j)).const_mul _).aestronglyMeasurable
    · filter_upwards with α
      rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact abs_prodSel_le r D (Lnorm n) hL F c hc t j α
  have hsplit : (∫ α in Ioo (0 : ℝ) 1, ∑ t ∈ (Finset.range r).powerset,
        Complex.I ^ ((Finset.range r) \ t).card *
          ((∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)) : ℝ) : ℂ))
      = ∑ t ∈ (Finset.range r).powerset,
          Complex.I ^ ((Finset.range r) \ t).card *
            ((∫ α in Ioo (0 : ℝ) 1,
                ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)) : ℝ) : ℂ) := by
    rw [integral_finset_sum _ hint]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [integral_const_mul, integral_complex_ofReal]
  -- the means, expanded
  have hprodeq : ∀ t : Finset ℕ,
      (∏ ℓ ∈ Finset.range r,
          (if ℓ ∈ t then (∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure).re
            else (∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure).im))
        = ∏ ℓ ∈ Finset.range r, ∫ x, selObs c t ℓ x ∂Erdos1002.gaussMeasure := by
    intro t
    refine Finset.prod_congr rfl (fun ℓ hℓ => ?_)
    have hi := integrable_digitObs r D (Lnorm n) F c hc ℓ (Finset.mem_range.1 hℓ)
    by_cases h : ℓ ∈ t
    · rw [if_pos h]
      rw [re_integral_eq _ hi]
      exact integral_congr_ae (Eventually.of_forall
        (fun x => by simp only [selObs, if_pos h]))
    · rw [if_neg h]
      rw [im_integral_eq _ hi]
      exact integral_congr_ae (Eventually.of_forall
        (fun x => by simp only [selObs, if_neg h]))
  have hmean : (∏ ℓ : Fin r, ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure)
      = ∑ t ∈ (Finset.range r).powerset,
          Complex.I ^ ((Finset.range r) \ t).card *
            ((∏ ℓ ∈ Finset.range r,
                ∫ x, selObs c t ℓ x ∂Erdos1002.gaussMeasure : ℝ) : ℂ) := by
    rw [Fin.prod_univ_eq_prod_range
      (fun ℓ => ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure) r,
      prod_complex_expand r (fun ℓ => ∫ x, Prop4Final.digitObs c ℓ x ∂Erdos1002.gaussMeasure)]
    exact Finset.sum_congr rfl (fun t _ => by rw [hprodeq t])
  rw [hcong, hsplit, hmean, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  push_cast
  ring

/-! ## 6. Lebesgue `dα` on `(0,1)` versus Gauss `dν`

The outer measure of Kwon's (27) is Lebesgue, while Lemma 3.2 is a
`ν`-statement.  `dLeb/dν = log 2 · (1+x)` is bounded, nonnegative and
Lipschitz on the state interval, so Wang's transfer contraction moves it to
the constant `1` at the rate `(527/540)^m`; the correlation identity then
converts the change of measure into that error. -/

theorem integral_Ioc_eq_gauss (G : ℝ → ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, G x)
      = ∫ x, Erdos1002.lebesgueOverGaussDensityReal x * G x
          ∂Erdos1002.gaussMeasure := by
  rw [← Erdos1002.gaussMeasure_withDensity_lebesgueOverGaussDensity,
    integral_withDensity_eq_integral_toReal_smul
      Erdos1002.measurable_lebesgueOverGaussDensity
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) G]
  refine integral_congr_ae ?_
  filter_upwards [Erdos1002.gaussMeasure_unit_ae] with x hx
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ Erdos1002.lebesgueOverGaussDensityReal x :=
    le_trans hlog.le
      (Erdos1002.lebesgueOverGaussDensityReal_bounds ⟨hx.1.le, hx.2⟩).1
  simp only [Erdos1002.lebesgueOverGaussDensity, smul_eq_mul,
    ENNReal.toReal_ofReal h0]

theorem gauss_mean_density_eq_one :
    (∫ x, Erdos1002.lebesgueOverGaussDensityReal x ∂Erdos1002.gaussMeasure) = 1 := by
  have h := integral_Ioc_eq_gauss (fun _ => (1 : ℝ))
  simp only [mul_one, setIntegral_const, smul_eq_mul] at h
  rw [← h, measureReal_def, Real.volume_Ioc]
  norm_num

theorem gaussUnitNonnegative_density :
    Erdos1002.GaussUnitNonnegative Erdos1002.lebesgueOverGaussDensityReal := fun _ hx =>
  le_trans (Real.log_pos (by norm_num)).le
    (Erdos1002.lebesgueOverGaussDensityReal_bounds hx).1

theorem gaussUnitUpperBound_density :
    Erdos1002.GaussUnitUpperBound (2 * Real.log 2)
      Erdos1002.lebesgueOverGaussDensityReal := fun _ hx =>
  (Erdos1002.lebesgueOverGaussDensityReal_bounds hx).2

theorem gaussUnitLipschitz_density :
    Erdos1002.GaussUnitLipschitzBound (Real.log 2)
      Erdos1002.lebesgueOverGaussDensityReal := by
  intro x _ y _
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : Erdos1002.lebesgueOverGaussDensityReal x
      - Erdos1002.lebesgueOverGaussDensityReal y = Real.log 2 * (x - y) := by
    simp only [Erdos1002.lebesgueOverGaussDensityReal]; ring
  rw [hsub, abs_mul, abs_of_pos hlog]

/-- **The change of measure on the outside of (27).**  A bounded measurable
observable evaluated `m` steps down the orbit has the same Lebesgue mean on
`(0,1)` as Gauss mean, up to `(527/540)^m · log 2 · ‖G‖_∞`. -/
theorem lebesgue_sub_gauss_le (m : ℕ) (G : ℝ → ℝ) (hGm : Measurable G) (M : ℝ)
    (hM : ∀ x, |G x| ≤ M) :
    |(∫ α in Ioo (0 : ℝ) 1, G (gaussIter α m))
        - ∫ y, G y ∂Erdos1002.gaussMeasure|
      ≤ ((527 / 540 : ℝ) ^ m * Real.log 2) * M := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hwM : Measurable Erdos1002.lebesgueOverGaussDensityReal :=
    Erdos1002.measurable_lebesgueOverGaussDensityReal
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hIntT : Integrable
      ((Erdos1002.gaussTransfer^[m]) Erdos1002.lebesgueOverGaussDensityReal)
      Erdos1002.gaussMeasure :=
    Erdos1002.integrable_gaussTransfer_iterate_of_unit_bounds hwM
      gaussUnitNonnegative_density gaussUnitUpperBound_density m
  have hb := Erdos1002.gaussTransfer_iterate_unit_bounds
    gaussUnitNonnegative_density gaussUnitUpperBound_density m
  have hkey : ∀ y ∈ Icc (0 : ℝ) 1,
      |(Erdos1002.gaussTransfer^[m]) Erdos1002.lebesgueOverGaussDensityReal y - 1|
        ≤ (527 / 540 : ℝ) ^ m * Real.log 2 := by
    intro y hy
    have h := Erdos1002.abs_gaussTransfer_iterate_sub_integral_le hlog.le hwM
      gaussUnitNonnegative_density gaussUnitUpperBound_density
      gaussUnitLipschitz_density m hy
    rwa [gauss_mean_density_eq_one] at h
  have hGint : Integrable G Erdos1002.gaussMeasure :=
    Integrable.of_bound hGm.aestronglyMeasurable M
      (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hM x))
  have hprodint : Integrable
      (fun y => (Erdos1002.gaussTransfer^[m]) Erdos1002.lebesgueOverGaussDensityReal y * G y)
      Erdos1002.gaussMeasure := by
    refine Integrable.of_bound
      (hIntT.aestronglyMeasurable.mul hGm.aestronglyMeasurable)
      ((2 * Real.log 2) * M) ?_
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (hM y) (abs_nonneg _) (by positivity)
    rw [abs_of_nonneg (hb.1 hycc)]
    exact hb.2 hycc
  have hchain : (∫ α in Ioo (0 : ℝ) 1, G (gaussIter α m))
      = ∫ y, (Erdos1002.gaussTransfer^[m]) Erdos1002.lebesgueOverGaussDensityReal y
          * G y ∂Erdos1002.gaussMeasure := by
    have h1 : (∫ α in Ioo (0 : ℝ) 1, G (gaussIter α m))
        = ∫ α in Ioc (0 : ℝ) 1, G (gaussIter α m) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [h1, integral_Ioc_eq_gauss (fun α => G (gaussIter α m))]
    exact Erdos1002.integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate hwM hGm
      gaussUnitNonnegative_density gaussUnitUpperBound_density m
  have hdiff : (∫ y, (Erdos1002.gaussTransfer^[m])
          Erdos1002.lebesgueOverGaussDensityReal y * G y ∂Erdos1002.gaussMeasure)
        - ∫ y, G y ∂Erdos1002.gaussMeasure
      = ∫ y, ((Erdos1002.gaussTransfer^[m])
          Erdos1002.lebesgueOverGaussDensityReal y - 1) * G y ∂Erdos1002.gaussMeasure := by
    rw [← integral_sub hprodint hGint]
    exact integral_congr_ae (Eventually.of_forall (fun y => by ring))
  rw [hchain, hdiff, ← Real.norm_eq_abs]
  have hcst : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      ‖((Erdos1002.gaussTransfer^[m]) Erdos1002.lebesgueOverGaussDensityReal y - 1)
          * G y‖ ≤ ((527 / 540 : ℝ) ^ m * Real.log 2) * M := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hkey y hycc) (hM y) (abs_nonneg _) (by positivity)
  simpa using norm_integral_le_of_norm_le_const hcst

/-! ## 7. The `ν`-mean is the mean of the shifted product, and `ν(0,1) = 1` -/

theorem gaussMeasure_Ioo_eq_one : Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1) = 1 := by
  have h := Measure.restrict_eq_self_of_ae_mem
    (μ := Erdos1002.gaussMeasure) Kwon1002.Transfer.gaussMeasure_ae_Ioo
  have h2 : Erdos1002.gaussMeasure.restrict (Ioo (0 : ℝ) 1) univ
      = Erdos1002.gaussMeasure univ := by rw [h]
  rwa [Measure.restrict_apply_univ, measure_univ] at h2

theorem restrict_gauss_Ioo :
    Erdos1002.gaussMeasure.restrict (Ioo (0 : ℝ) 1) = Erdos1002.gaussMeasure :=
  Measure.restrict_eq_self_of_ae_mem Kwon1002.Transfer.gaussMeasure_ae_Ioo

/-- The Lebesgue mean of the zero-mode multi-block product over `(0,1)`
differs from its Gauss mean by at most `(527/540)^{j_1} · log 2 · ‖·‖_∞`. -/
theorem prodSel_lebesgue_sub_gauss (r : ℕ) (D L : ℝ) (hL : 0 ≤ L ^ D)
    (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c)
    (t : Finset ℕ) (j : ℕ → ℕ) (hmono : ∀ ℓ, ℓ < r → j 0 ≤ j ℓ) :
    |(∫ α in Ioo (0 : ℝ) 1, ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)))
        - ∫ α, (∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)))
            ∂Erdos1002.gaussMeasure|
      ≤ ((527 / 540 : ℝ) ^ (j 0) * Real.log 2) * (L ^ D) ^ r := by
  classical
  have hcomp : ∀ α : ℝ,
      (∏ ℓ ∈ Finset.range r,
          selObs c t ℓ (gaussIter (gaussIter α (j 0)) (j ℓ - j 0)))
        = ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)) := by
    intro α
    refine Finset.prod_congr rfl (fun ℓ hℓ => ?_)
    have h := MixingBV.gaussOrbit_add (j ℓ - j 0) (j 0) α
    rw [Nat.sub_add_cancel (hmono ℓ (Finset.mem_range.1 hℓ))] at h
    rw [show gaussIter (gaussIter α (j 0)) (j ℓ - j 0) = gaussIter α (j ℓ) from h]
  have h1 := lebesgue_sub_gauss_le (j 0)
    (fun y => ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter y (j ℓ - j 0)))
    (measurable_prodSel r c t (fun ℓ => j ℓ - j 0)) ((L ^ D) ^ r)
    (abs_prodSel_le r D L hL F c hc t (fun ℓ => j ℓ - j 0))
  have hinv0 : (∫ α, (∏ ℓ ∈ Finset.range r,
        selObs c t ℓ (gaussIter (gaussIter α (j 0)) (j ℓ - j 0)))
          ∂Erdos1002.gaussMeasure)
      = ∫ y, (∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter y (j ℓ - j 0)))
          ∂Erdos1002.gaussMeasure := by
    have hmap : Measure.map (fun α : ℝ => gaussIter α (j 0)) Erdos1002.gaussMeasure
        = Erdos1002.gaussMeasure := Erdos1002.map_gaussMap_iterate_gaussMeasure (j 0)
    have hmm := integral_map (μ := Erdos1002.gaussMeasure)
      (φ := fun α : ℝ => gaussIter α (j 0))
      (f := fun y => ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter y (j ℓ - j 0)))
      (measurable_gaussIter (j 0)).aemeasurable
      (measurable_prodSel r c t (fun ℓ => j ℓ - j 0)).aestronglyMeasurable
    rw [hmap] at hmm
    exact hmm.symm
  have e1 : (∫ α in Ioo (0 : ℝ) 1, ∏ ℓ ∈ Finset.range r,
        selObs c t ℓ (gaussIter (gaussIter α (j 0)) (j ℓ - j 0)))
      = ∫ α in Ioo (0 : ℝ) 1, ∏ ℓ ∈ Finset.range r,
          selObs c t ℓ (gaussIter α (j ℓ)) :=
    integral_congr_ae (Eventually.of_forall hcomp)
  have e2 : (∫ y, (∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter y (j ℓ - j 0)))
        ∂Erdos1002.gaussMeasure)
      = ∫ α, (∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)))
          ∂Erdos1002.gaussMeasure := by
    rw [← hinv0]
    exact integral_congr_ae (Eventually.of_forall hcomp)
  rw [← e1, ← e2]
  exact h1

/-- `ρ^{⌊h⌋} ≤ ρ^h / ρ` for `0 < ρ < 1` and `h ≥ 0`. -/
theorem pow_floor_le_rpow_div (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (h : ℝ) :
    ρ ^ (⌊h⌋₊) ≤ ρ ^ h / ρ := by
  have hfl : h - 1 ≤ ((⌊h⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one h
    linarith
  have e1 : ρ ^ (⌊h⌋₊ : ℕ) = ρ ^ ((⌊h⌋₊ : ℕ) : ℝ) := (Real.rpow_natCast ρ _).symm
  have e2 : ρ ^ ((⌊h⌋₊ : ℕ) : ℝ) ≤ ρ ^ (h - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le hfl
  have e3 : ρ ^ (h - 1) = ρ ^ h / ρ := by
    rw [Real.rpow_sub hρ0, Real.rpow_one]
  rw [e1, ← e3]
  exact e2

/-! ## 8. Step 2 of the §4 body: the zero mode -/

theorem zero_mode_factorization (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
        ‖modeTerm n r j c 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (D * r) * ρ ^ (200 * Hscale n) := by
  classical
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · subst hr0
    refine ⟨1, 1 / 2, one_pos, by norm_num, by norm_num, ?_⟩
    filter_upwards [hLtend.eventually (eventually_ge_atTop (1 : ℝ))] with n hL1 j hj F c hc
    have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
    have h1 : modeTerm n 0 j c 0 = 1 := by
      unfold modeTerm
      simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty,
        Prop4Final.torusChar_zero, one_mul]
      rw [setIntegral_const, measureReal_def, Real.volume_Ioo]
      norm_num
    rw [h1]
    simp only [Finset.range_zero, Finset.prod_empty, sub_self, norm_zero]
    have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ (200 * Hscale n) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0 : ℝ) ≤ (Lnorm n) ^ (D * ((0 : ℕ) : ℝ)) := Real.rpow_nonneg hL0.le _
    exact mul_nonneg (mul_nonneg zero_le_one h3) h2.le
  obtain ⟨Cm, ρm, hCm, hρm0, hρm1, hmix⟩ := Bridge.good_tuple_multiblock_mixing' r hr
  have hρ0 : 0 < max ρm (527 / 540 : ℝ) := lt_of_lt_of_le hρm0 (le_max_left _ _)
  have hρ1 : max ρm (527 / 540 : ℝ) < 1 := max_lt hρm1 (by norm_num)
  have hnum : (0 : ℝ) < 2 ^ r * (Real.log 2 + Cm * 2 ^ r) := by
    have h2 : (0 : ℝ) < Cm * (2 : ℝ) ^ r := mul_pos hCm (by positivity)
    exact mul_pos (by positivity) (by linarith)
  refine ⟨2 ^ r * (Real.log 2 + Cm * 2 ^ r) / max ρm (527 / 540 : ℝ),
    max ρm (527 / 540 : ℝ), div_pos hnum hρ0, hρ0, hρ1, ?_⟩
  filter_upwards [hLtend.eventually (eventually_ge_atTop (1 : ℝ))] with n hL1 j hj F c hc
  set ρ : ℝ := max ρm (527 / 540 : ℝ) with hρdef
  set M : ℕ := ⌊200 * Hscale n⌋₊ with hMdef
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hKnn : (0 : ℝ) ≤ (Lnorm n) ^ D := Real.rpow_nonneg hL0.le D
  have hKr : (0 : ℝ) ≤ ((Lnorm n) ^ D) ^ r := pow_nonneg hKnn r
  have hH1 : (1 : ℝ) ≤ Hscale n := by
    rw [Hscale]; exact Real.one_le_rpow hL1 (by norm_num)
  -- the start condition (19) and the monotonicity of the tuple
  have hmemJ : j 0 ∈ bulkJ n := hj.1.2.2 0 hr
  have hge : 200 * Hscale n ≤ ((j 0 : ℕ) : ℝ) := ((Finset.mem_filter.1 hmemJ).2).1
  have hMle : M ≤ j 0 := by
    have h1 : ⌊200 * Hscale n⌋₊ ≤ ⌊((j 0 : ℕ) : ℝ)⌋₊ := Nat.floor_mono hge
    rw [Nat.floor_natCast] at h1
    exact h1
  have hmono : ∀ ℓ, ℓ < r → j 0 ≤ j ℓ := by
    intro ℓ hℓ
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h; exact le_rfl
    · exact (hj.1.2.1 0 ℓ h hℓ).le
  -- the two elementary comparisons of the rates
  have hcmp1 : (527 / 540 : ℝ) ^ (j 0) ≤ ρ ^ M := by
    have ha : (527 / 540 : ℝ) ^ (j 0) ≤ (527 / 540 : ℝ) ^ M :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hMle
    have hb : (527 / 540 : ℝ) ^ M ≤ ρ ^ M :=
      pow_le_pow_left₀ (by norm_num) (le_max_right _ _) M
    linarith
  have hcmp2 : ρm ^ M ≤ ρ ^ M := pow_le_pow_left₀ hρm0.le (le_max_left _ _) M
  have hρM0 : (0 : ℝ) ≤ ρ ^ M := pow_nonneg hρ0.le M
  -- the bound on each of the `2^r` real defects
  have hbd : ∀ t ∈ (Finset.range r).powerset,
      ‖Complex.I ^ ((Finset.range r \ t).card) *
          (((∫ α in Ioo (0 : ℝ) 1,
                ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)))
              - ∏ ℓ ∈ Finset.range r,
                  ∫ x, selObs c t ℓ x ∂Erdos1002.gaussMeasure : ℝ) : ℂ)‖
        ≤ (Real.log 2 + Cm * 2 ^ r) * (ρ ^ M * ((Lnorm n) ^ D) ^ r) := by
    intro t _
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have hA := prodSel_lebesgue_sub_gauss r D (Lnorm n) hKnn F c hc t j hmono
    have hB : |(∫ α, (∏ i ∈ Finset.range r, selObs c t i (gaussIter α (j i)))
            ∂Erdos1002.gaussMeasure)
          - ∏ i ∈ Finset.range r, ∫ x, selObs c t i x ∂Erdos1002.gaussMeasure|
        ≤ Cm * ρm ^ M * (2 * (Lnorm n) ^ D) ^ r := by
      have h := hmix n j hj (selObs c t) (2 * (Lnorm n) ^ D) (by positivity)
        (fun i hi => selObs_bv r D (Lnorm n) hKnn F c hc t i hi)
      rwa [restrict_gauss_Ioo, gaussMeasure_Ioo_eq_one, ENNReal.toReal_one, div_one] at h
    have hstep := abs_sub_le
      (∫ α in Ioo (0 : ℝ) 1, ∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)))
      (∫ α, (∏ ℓ ∈ Finset.range r, selObs c t ℓ (gaussIter α (j ℓ)))
          ∂Erdos1002.gaussMeasure)
      (∏ ℓ ∈ Finset.range r, ∫ x, selObs c t ℓ x ∂Erdos1002.gaussMeasure)
    have hpow : (2 * (Lnorm n) ^ D) ^ r = 2 ^ r * ((Lnorm n) ^ D) ^ r := mul_pow _ _ _
    rw [hpow] at hB
    have hfin1 : ((527 / 540 : ℝ) ^ (j 0) * Real.log 2) * ((Lnorm n) ^ D) ^ r
        ≤ (Real.log 2 * ρ ^ M) * ((Lnorm n) ^ D) ^ r := by
      refine mul_le_mul_of_nonneg_right ?_ hKr
      nlinarith [hlog2.le, hcmp1]
    have hfin2 : Cm * ρm ^ M * (2 ^ r * ((Lnorm n) ^ D) ^ r)
        ≤ Cm * ρ ^ M * (2 ^ r * ((Lnorm n) ^ D) ^ r) := by
      have h2r : (0 : ℝ) ≤ 2 ^ r * ((Lnorm n) ^ D) ^ r := by positivity
      refine mul_le_mul_of_nonneg_right ?_ h2r
      exact mul_le_mul_of_nonneg_left hcmp2 hCm.le
    have := add_le_add hA hB
    nlinarith [hstep, this, hfin1, hfin2]
  -- assemble
  rw [defect_expand n r D hKnn j F c hc]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _
    ((Real.log 2 + Cm * 2 ^ r) * (ρ ^ M * ((Lnorm n) ^ D) ^ r)) hbd) ?_
  rw [Finset.card_powerset, Finset.card_range, nsmul_eq_mul]
  have hKrpow : ((Lnorm n) ^ D) ^ r = (Lnorm n) ^ (D * (r : ℝ)) := by
    rw [← Real.rpow_natCast ((Lnorm n) ^ D) r, ← Real.rpow_mul hL0.le]
  have hfloor : ρ ^ M ≤ ρ ^ (200 * Hscale n) / ρ :=
    pow_floor_le_rpow_div ρ hρ0 hρ1 (200 * Hscale n)
  have hNnn : (0 : ℝ) ≤ (2 : ℝ) ^ r * (Real.log 2 + Cm * 2 ^ r) := by positivity
  calc ((2 ^ r : ℕ) : ℝ) * ((Real.log 2 + Cm * 2 ^ r) * (ρ ^ M * ((Lnorm n) ^ D) ^ r))
      = ((2 : ℝ) ^ r * (Real.log 2 + Cm * 2 ^ r)) * (((Lnorm n) ^ D) ^ r * ρ ^ M) := by
        push_cast; ring
    _ ≤ ((2 : ℝ) ^ r * (Real.log 2 + Cm * 2 ^ r)) *
          (((Lnorm n) ^ D) ^ r * (ρ ^ (200 * Hscale n) / ρ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hNnn
        exact mul_le_mul_of_nonneg_left hfloor hKr
    _ = (2 ^ r * (Real.log 2 + Cm * 2 ^ r) / ρ) * (Lnorm n) ^ (D * (r : ℝ))
          * ρ ^ (200 * Hscale n) := by
        rw [hKrpow]
        field_simp

/-! ## 9. Step 3 of the §4 body: a nonzero mode

The manuscript's `v_s ≠ 0` branch (lines ≈ 337-383) is a *chain of three
replacements*, and its three error terms are exactly the three summands of
the bracket of (30).  Writing `T₁` for the integral after the three local
complete-cylinder cuts at depths `j_s`, `k_-`, `k_+` have been made, and
`T₂` for what is left after the post-resonance digit factors have been
replaced by their stationary means:

1. **Cutting and restoring** (manuscript: "By (20), the total discarded mass
   is `O(e^{-cL^{1/2}})`" and "extend the stationary-mean replacement to the
   discarded depth-`k_+` cylinders and restore them … this costs at most
   `L^{O_{r,D}(1)} e^{-cL^{1/2}}`") bounds `‖modeTerm − T₁‖`.
2. **The stationary-mean replacement** ("the conditional density of the
   future has uniformly bounded variation, so Lemma 3.2 replaces all
   post-resonance digit factors by their stationary means, with total error
   `L^{O(1)}(e^{-cH} + ρ^{cH})`"; the `100H` clearance is
   `Prop41.good_avoids_resonance_window`) bounds `‖T₁ − T₂‖`.
3. **The oscillatory kill** ("On each depth-`(j_s+1)` prefix the integer `Q`
   is fixed.  The first inequality in (29) and Lemma 3.4 give a contribution
   `O(e^{-cH})`") bounds `‖T₂‖`.

`nonzero_mode_three_step` states exactly that chain, and
`nonzero_mode_small` is derived from it **outright** below: the derivation
is the triangle inequality plus the arithmetic that merges the three
constants into the single bracket of (30).

**Obstruction of `nonzero_mode_three_step`** (it is the substantive half of
§4, and it is the one place where the two §3 oscillatory inputs enter):

* step 1 needs the large-deviation estimate (20) for `log q_j`, the
  statement `q_j ∈ [e^{λj−δH}, e^{λj+δH}]` off a set of measure
  `O(e^{-cL^{1/2}})`, which no module of `Kwon1002/` yet supplies, and the
  deterministic frequency bound (28) `q_{j_s}/2 ≤ |Q| ≤ 2L^D q_{j_s}`, which
  needs the Fibonacci lower bound on continuants together with `|v_ℓ| ≤ L^D`
  and the separation (25);
* step 2 is `MixingBV.lem_3_2_conditional_multiblock_mixing'` (available)
  applied at the clearance `Prop41.good_avoids_resonance_window` provides,
  but conditioned on a depth-`k_+` cylinder rather than on `(0,1)`; the
  conditional-density BV bound the manuscript invokes there is *not* the
  zero-mode BV bound of `Bridge.bv_of_firstDigit_step`;
* step 3 is `Kwon1002.descendant_cylinder_estimate` (display (22), proved)
  fed with `d = j_s + 1`, `k = k_-`, `Q_w` the fixed integer of (28) and
  `R_w = q_{k_-}`, whose hypothesis `R_w² ≤ ε n |Q_w|` is the first
  inequality of (29); `Kwon1002.shrinking_anti_concentration` (Lemma 3.3,
  proved) is what makes the frequency non-degenerate on the retained set.
  Both are available; what is missing is the cylinder bookkeeping that puts
  `modeTerm` into the shape `∑_w ‖∑_v c_{w,v} ∫ e(nQ_wα)‖` those lemmas
  consume. -/
theorem nonzero_mode_three_step (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C c₀ ρ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
      ∀ v ∈ modeTuples r D (Lnorm n), v ≠ 0 →
        ∃ T₁ T₂ : ℂ,
          ‖modeTerm n r j c v - T₁‖
              ≤ C * (Lnorm n) ^ (D * r) * Real.exp (-c₀ * Real.sqrt (Lnorm n)) ∧
            ‖T₁ - T₂‖
              ≤ C * (Lnorm n) ^ (D * r) *
                  (Real.exp (-c₀ * Hscale n) + ρ ^ (c₀ * Hscale n)) ∧
            ‖T₂‖ ≤ C * (Lnorm n) ^ (D * r) * Real.exp (-c₀ * Hscale n) := by
  sorry

/-- **Step 3 of the §4 body.**  Statement reproduced token-identically from
`Kwon1002.ErrorShape.nonzero_mode_small`; proved outright from
`nonzero_mode_three_step`. -/
theorem nonzero_mode_small (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C c₀ ρ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
      ∀ v ∈ modeTuples r D (Lnorm n), v ≠ 0 →
        ‖modeTerm n r j c v‖
          ≤ C * (Lnorm n) ^ (D * r) *
              (Real.exp (-c₀ * Real.sqrt (Lnorm n)) + Real.exp (-c₀ * Hscale n)
                + ρ ^ (c₀ * Hscale n)) := by
  obtain ⟨C, c₀, ρ, hC, hc₀, hρ0, hρ1, hbd⟩ := nonzero_mode_three_step r D hD
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨3 * C, c₀, ρ, by linarith, hc₀, hρ0, hρ1, ?_⟩
  filter_upwards [hbd, hLtend.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hL1 j hj F c hc v hv hv0
  obtain ⟨T₁, T₂, h1, h2, h3⟩ := hn j hj F c hc v hv hv0
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hX : (0 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) := Real.rpow_nonneg hL0.le _
  have e1 : (0 : ℝ) < Real.exp (-c₀ * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have e2 : (0 : ℝ) < Real.exp (-c₀ * Hscale n) := Real.exp_pos _
  have e3 : (0 : ℝ) < ρ ^ (c₀ * Hscale n) := Real.rpow_pos_of_pos hρ0 _
  have htri : ‖modeTerm n r j c v‖ ≤ ‖modeTerm n r j c v - T₁‖ + ‖T₁ - T₂‖ + ‖T₂‖ := by
    calc ‖modeTerm n r j c v‖
        = ‖(modeTerm n r j c v - T₁) + ((T₁ - T₂) + T₂)‖ := by ring_nf
      _ ≤ ‖modeTerm n r j c v - T₁‖ + ‖(T₁ - T₂) + T₂‖ := norm_add_le _ _
      _ ≤ ‖modeTerm n r j c v - T₁‖ + (‖T₁ - T₂‖ + ‖T₂‖) :=
          add_le_add le_rfl (norm_add_le _ _)
      _ = ‖modeTerm n r j c v - T₁‖ + ‖T₁ - T₂‖ + ‖T₂‖ := by ring
  refine le_trans htri ?_
  have hsum := add_le_add (add_le_add h1 h2) h3
  refine le_trans hsum ?_
  nlinarith [hX, e1.le, e2.le, e3.le, hC.le,
    mul_nonneg hX e1.le, mul_nonneg hX e2.le, mul_nonneg hX e3.le]

end

end ZeroMode

end Kwon1002
