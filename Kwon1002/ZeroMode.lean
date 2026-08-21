import Kwon1002.Bridge
import Kwon1002.Prop42
import Kwon1002.Prop41Canon
import Kwon1002.CharacterReduction
import Kwon1002.CylinderPhase
import Kwon1002.Display22

/-!
# Scratch (`errorshape`): the three §4-body inputs of `Kwon1002/ErrorShape.lean`

Targets, all three reproduced **token-identically** (diffed line-by-line
against `Kwon1002/ErrorShape.lean` lines 190-195, 216-222 and 240-249; the
only difference found was the proof delimiter `:= by` versus `:=`):

* `integral_eq_sum_modeTerm`, **PROVED** (it is
  `Prop4Final.integral_eq_sum_modeTerm'`, already available).
* `zero_mode_factorization`, **PROVED OUTRIGHT**, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.
* `nonzero_mode_small`, proved from `nonzero_mode_three_step`, the
  manuscript's own three-step chain (both declared in
  `Kwon1002/NonzeroMode.lean`, which proves the chain)
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

## The nonzero-mode bookkeeping (§9, all proved)

The obstruction note of `nonzero_mode_three_step` recorded that the missing
piece was "the cylinder bookkeeping that puts `modeTerm` into the shape
`∑_w ‖∑_v c_{w,v} ∫ e(nQ_wα)‖`" display (22) consumes.  Section 9 builds
that bookkeeping outright: the frequency extraction
(`modeTerm_eq_oscillatory`, via (8)), the frozen per-cylinder frequency
(`exists_frozen_freqQ`, "on `I_w` the integer `Q` is fixed"), the
retained/discarded split and step 1 conditional on the discarded mass
(`nonzero_mode_cut_of_retained`, constant `C = 1`), and step 3 in retained
form (`nonzero_mode_kill_of_retained`, from display (22)).  What separates
these from an unconditional `nonzero_mode_three_step` is exactly:

* **display (20)** (Lévy large deviations for `log q_j`, recorded as the
  predicate `P42Cases.Display20`), which selects the retained words and
  bounds the discarded mass by `O(e^{-cL^{1/2}})` and supplies both
  inequalities of (29); no instance of it is proved in `Kwon1002/` or the
  Wang substrate (see `PhaseBounds`, `P42Cases` §4); and
* **step 2**, the stationary-mean replacement on depth-`k₊` cylinders,
  which needs Lemma 3.2's conditional mixing transported from the Gauss
  conditional measure (`MixingBV.lem_3_2_conditional_multiblock_mixing'`)
  to the *Lebesgue* measure conditioned on a cylinder, plus the v8
  restoration of the discarded cylinders (again (20)).

## Sorried results consumed

**None.**  The one that used to be stated here, `nonzero_mode_three_step`, is
declared in `Kwon1002/NonzeroMode.lean`, which proves it.
`ErrorShape`'s own `integral_eq_sum_modeTerm`, `zero_mode_factorization`
and `nonzero_mode_small` are **not** consumed, they are re-proved here.

Everything imported from `Bridge`, `MixingBV`, `Prop4Final`, `Display22`,
`Prop41Canon` sections 1-3, `CharacterReduction`, `CylinderPhase`,
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

/-! ## 9. Nonzero-mode bookkeeping: frequency extraction and the retained cut

The obstruction note of `nonzero_mode_three_step` below records that both §3
oscillatory inputs (displays (22) and (23)) are proved, and that "what is
missing is the cylinder bookkeeping that puts `modeTerm` into the shape
`∑_w ‖∑_v c_{w,v} ∫ e(nQ_wα)‖` those lemmas consume."  This section builds
that bookkeeping:

* `exists_top_mode_index`: every nonzero mode tuple has a top nonzero
  index `s`, the manuscript's "let `s` be maximal with `v_s ≠ 0`".
* `modeChar_eq_freqQ` / `modeTerm_eq_oscillatory`: **the frequency
  extraction.**  By (8) (`theta_eq_mod`), on irrational `α` the pure phase
  of the mode `v` is `e(nQα)` with `Q = Σ_{ℓ≤s} v_ℓ (-1)^{j_ℓ} q_{j_ℓ}` the
  integer `Prop41Canon.freqQ` of display (28); `modeTerm` becomes the
  oscillatory integral `∫ (∏_ℓ c_ℓ(a_{j_ℓ+1}, v_ℓ)) e(nQ(α)α) dα`.
* `freqQ_congr`: the frequency is **frozen at depth `j_s + 1`**: it depends
  on `α` only through the digits below `max_{ℓ≤s} j_ℓ`, so it is constant
  on every depth-`(j_s+1)` prefix cylinder — this is what makes each `Q_w`
  of display (22) "fixed on `I_w`".
* `integral_Ioo_eq_retained_add_remainder`: the **retained/discarded
  split**: for any finite family `W` of positive depth-`d` words, the unit
  integral is the sum of the integrals over the retained cylinders plus the
  integral over the discarded set.
* `nonzero_mode_cut_of_retained`: **step 1 of the three-step chain,
  conditional form**: if the discarded mass is at most `η`, then `modeTerm`
  differs from its retained-cylinder truncation by at most `(L^D)^r · η`.
  With `W` the set of depth-`k₊` words retained by display (20) — whose
  discarded mass is `O(e^{-cL^{1/2}})` — this is exactly the first bound of
  `nonzero_mode_three_step`, with constant `C = 1`.  Display (20) is the
  single input this conditional form waits on; it is absent from the whole
  tree (see `PhaseBounds` §"no progress" and `P42Cases` §4). -/

/-- The mode tuple `v : Fin r → ℤ` extended to `ℕ` by zero; the shape
`Prop41Canon.freqQ` consumes. -/
def modeExt (r : ℕ) (v : Fin r → ℤ) : ℕ → ℤ :=
  fun ℓ => if h : ℓ < r then v ⟨ℓ, h⟩ else 0

theorem modeExt_lt (r : ℕ) (v : Fin r → ℤ) (ℓ : ℕ) (h : ℓ < r) :
    modeExt r v ℓ = v ⟨ℓ, h⟩ := dif_pos h

theorem modeExt_fin (r : ℕ) (v : Fin r → ℤ) (ℓ : Fin r) :
    modeExt r v (ℓ : ℕ) = v ℓ := by
  rw [modeExt_lt r v ℓ ℓ.isLt]

/-- **"Let `s` be maximal with `v_s ≠ 0`."**  Every nonzero mode tuple has a
top nonzero index. -/
theorem exists_top_mode_index {r : ℕ} {v : Fin r → ℤ} (hv : v ≠ 0) :
    ∃ s : Fin r, v s ≠ 0 ∧ ∀ ℓ : Fin r, s < ℓ → v ℓ = 0 := by
  classical
  have hne : (Finset.univ.filter (fun ℓ : Fin r => v ℓ ≠ 0)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    refine hv (funext fun ℓ => ?_)
    by_contra hℓ
    exact absurd hℓ (h (Finset.mem_univ ℓ))
  refine ⟨(Finset.univ.filter (fun ℓ : Fin r => v ℓ ≠ 0)).max' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  · intro ℓ hℓ
    by_contra hne0
    exact absurd (Finset.le_max' _ ℓ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne0⟩))
      (not_le.mpr hℓ)

/-! ### Measurability of the frozen frequency -/

theorem measurable_denom : ∀ k : ℕ, Measurable fun α : ℝ => denom α k
  | 0 => measurable_const
  | 1 => Prop42.measurable_digitNat 0
  | (k + 2) => by
      have h : (fun α : ℝ => denom α (k + 2))
          = fun α : ℝ => digit α (k + 1) * denom α (k + 1) + denom α k := rfl
      rw [h]
      exact ((Prop42.measurable_digitNat (k + 1)).mul
        (measurable_denom (k + 1))).add (measurable_denom k)

theorem measurable_freqQ (j : ℕ → ℕ) (v : ℕ → ℤ) (s : ℕ) :
    Measurable fun α : ℝ => Prop41Canon.freqQ α j v s := by
  refine Finset.measurable_sum _ (fun ℓ _ => ?_)
  exact measurable_const.mul
    ((measurable_from_top (f := fun q : ℕ => (q : ℤ))).comp (measurable_denom (j ℓ)))

theorem continuous_torusChar : Continuous torusChar := by
  unfold torusChar
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem measurable_modeOsc (n : ℕ) (j : ℕ → ℕ) (v : ℕ → ℤ) (s : ℕ) :
    Measurable fun α : ℝ =>
      torusChar ((n : ℝ) * ((Prop41Canon.freqQ α j v s : ℤ) : ℝ) * α) := by
  have h1 : Measurable fun α : ℝ => ((Prop41Canon.freqQ α j v s : ℤ) : ℝ) :=
    (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp (measurable_freqQ j v s)
  exact continuous_torusChar.measurable.comp
    ((measurable_const.mul h1).mul measurable_id)

theorem measurable_modeAmp (r : ℕ) (j : ℕ → ℕ) (c : ℕ → ℕ → ℤ → ℂ) (v : Fin r → ℤ) :
    Measurable fun α : ℝ => ∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ) :=
  Finset.measurable_prod _ (fun ℓ _ =>
    (measurable_from_top (f := fun a : ℕ => c (ℓ : ℕ) a (v ℓ))).comp
      (Prop42.measurable_digitNat (j ℓ)))

/-- The scalar amplitude of a mode is bounded by `(L^D)^r`: each coefficient
is bounded by the `ℓ¹` mass `L^D` of (24). -/
theorem norm_modeAmp_le (n r : ℕ) (D : ℝ) (j : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D (Lnorm n) F c) (v : Fin r → ℤ)
    (α : ℝ) :
    ‖∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)‖ ≤ ((Lnorm n) ^ D) ^ r := by
  rw [norm_prod]
  have h : ∀ ℓ : Fin r, ‖c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)‖ ≤ (Lnorm n) ^ D :=
    fun ℓ => Prop4Final.coeff_norm_le r D (Lnorm n) F c hc ℓ ℓ.isLt _ _
  calc ∏ ℓ : Fin r, ‖c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)‖
      ≤ ∏ _ℓ : Fin r, (Lnorm n) ^ D :=
        Finset.prod_le_prod (fun ℓ _ => norm_nonneg _) (fun ℓ _ => h ℓ)
    _ = ((Lnorm n) ^ D) ^ r := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The frequency extraction -/

/-- **The phase of a nonzero mode is `e(nQα)`.**  By (8) (`theta_eq_mod`),
on irrational `α ∈ (0,1)` the pure phase `e(Σ_ℓ v_ℓ θ_{j_ℓ})` of the mode
`v` with top nonzero index `s` equals `e(nQα)` with
`Q = Σ_{ℓ≤s} v_ℓ (-1)^{j_ℓ} q_{j_ℓ}` the integer of display (28). -/
theorem modeChar_eq_freqQ {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n r : ℕ) (j : ℕ → ℕ) (v : Fin r → ℤ) (s : ℕ) (hs : s < r)
    (htop : ∀ ℓ : Fin r, s < (ℓ : ℕ) → v ℓ = 0) :
    torusChar (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ))
      = torusChar ((n : ℝ) * ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α) := by
  classical
  choose m hm using fun ℓ : Fin r => theta_eq_mod hα hirr n (j (ℓ : ℕ))
  -- the frequency, extended from `range (s+1)` to `range r`
  have hQr : Prop41Canon.freqQ α j (modeExt r v) s
      = ∑ ℓ ∈ Finset.range r, modeExt r v ℓ * (-1) ^ (j ℓ) * (denom α (j ℓ) : ℤ) := by
    rw [Prop41Canon.freqQ]
    refine Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr
        (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)) hs))
      (fun ℓ hℓr hℓs => ?_)
    have h1 : ℓ < r := Finset.mem_range.mp hℓr
    have h2 : s < ℓ := by
      rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hℓs
      exact hℓs
    rw [modeExt_lt r v ℓ h1, htop ⟨ℓ, h1⟩ h2, zero_mul, zero_mul]
  -- its real cast, as a `Fin r` sum
  have hQcast : ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ)
      = ∑ ℓ : Fin r, (v ℓ : ℝ) * (-1 : ℝ) ^ (j (ℓ : ℕ)) * (denom α (j (ℓ : ℕ)) : ℝ) := by
    rw [hQr, ← Fin.sum_univ_eq_sum_range
      (fun ℓ => modeExt r v ℓ * (-1) ^ (j ℓ) * (denom α (j ℓ) : ℤ)) r]
    push_cast
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [modeExt_fin r v ℓ]
  -- the phase sum, decomposed through (8)
  have hsum : (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ))
      = (n : ℝ) * ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α
        + ((∑ ℓ : Fin r, v ℓ * m ℓ : ℤ) : ℝ) := by
    have h1 : (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ))
        = ∑ ℓ : Fin r,
            ((v ℓ : ℝ) * ((-1 : ℝ) ^ (j (ℓ : ℕ)) * (denom α (j (ℓ : ℕ)) : ℝ) * (n : ℝ) * α)
              + (v ℓ : ℝ) * ((m ℓ : ℤ) : ℝ)) := by
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [hm ℓ]
      ring
    rw [h1, Finset.sum_add_distrib, hQcast, Finset.mul_sum, Finset.sum_mul]
    push_cast
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl (fun ℓ _ => by ring)) rfl
  rw [hsum, torusChar_add_int]

/-- **`modeTerm` as an oscillatory integral.**  The first half of the
missing bookkeeping: the digit-Fourier term of a nonzero mode is
`∫ (∏_ℓ c_ℓ(a_{j_ℓ+1}, v_ℓ)) e(nQ(α)α) dα` with `Q` the frozen integer
frequency of (28). -/
theorem modeTerm_eq_oscillatory (n r : ℕ) (j : ℕ → ℕ) (c : ℕ → ℕ → ℤ → ℂ)
    (v : Fin r → ℤ) (s : ℕ) (hs : s < r)
    (htop : ∀ ℓ : Fin r, s < (ℓ : ℕ) → v ℓ = 0) :
    modeTerm n r j c v
      = ∫ α in Ioo (0 : ℝ) 1,
          (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
            torusChar ((n : ℝ) * ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α) := by
  rw [ErrorShape.modeTerm]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
    with α hα hirr
  rw [modeChar_eq_freqQ hα hirr n r j v s hs htop]

/-! ### The frequency is frozen at depth `j_s + 1` -/

/-- The frequency `Q` depends on `α` only through the digits below
`max_{ℓ ≤ s} j_ℓ`: two points whose first `d` digits agree, where
`j ℓ ≤ d` for every `ℓ ≤ s`, have the same frequency.  In particular `Q`
is constant on every depth-`(j_s+1)` prefix cylinder of a monotone tuple,
which is display (22)'s "on `I_w` the integer `Q_w` is fixed". -/
theorem freqQ_congr {α α' : ℝ} (j : ℕ → ℕ) (v : ℕ → ℤ) (s d : ℕ)
    (hjd : ∀ ℓ, ℓ ≤ s → j ℓ ≤ d) (hdig : ∀ i, i < d → digit α i = digit α' i) :
    Prop41Canon.freqQ α j v s = Prop41Canon.freqQ α' j v s := by
  unfold Prop41Canon.freqQ
  refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
  have hℓs : ℓ ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  have hden := (cf_congr α α' (j ℓ)
    (fun i hi => hdig i (lt_of_lt_of_le hi (hjd ℓ hℓs)))).1
  rw [hden]

/-! ### The retained/discarded split -/

/-- A nonempty positive half-open prefix cylinder lies in `(0, 1]`. -/
theorem halfOpenCylinder_subset_Ioc {w : List ℕ} (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) :
    Erdos1002.gaussHalfOpenPrefixCylinder w ⊆ Ioc (0 : ℝ) 1 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons q qs =>
      intro x hx
      have hq : 0 < q := hpos q (by simp)
      have h1 : x ∈ Erdos1002.firstDigitCylinder q := hx.1
      rw [Erdos1002.firstDigitCylinder] at h1
      have hq1 : (0 : ℝ) < 1 / ((q + 1 : ℕ) : ℝ) := by positivity
      have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      refine ⟨lt_trans hq1 h1.1, le_trans h1.2 ?_⟩
      rw [div_le_one (by linarith)]
      exact hqR

/-- **The retained/discarded split.**  For a bounded measurable `f` and any
finite family `W` of positive depth-`d` words, the unit integral is the sum
over the retained cylinders plus the integral over the discarded set.  This
is the manuscript's tacit "partition into complete depth-`d` cylinders and
retain those where (20) holds". -/
theorem integral_Ioo_eq_retained_add_remainder (f : ℝ → ℂ) (B : ℝ)
    (hfm : Measurable f) (hfb : ∀ α, ‖f α‖ ≤ B)
    (W : Finset (List ℕ)) (d : ℕ) (hd : 0 < d)
    (hW : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) :
    ∫ α in Ioo (0 : ℝ) 1, f α
      = (∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α)
        + ∫ α in Ioo (0 : ℝ) 1 \
            (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w), f α := by
  classical
  set U : Set ℝ := ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w with hU
  have hwne : ∀ w ∈ W, w ≠ [] := by
    intro w hw hnil
    have := (hW w hw).1
    rw [hnil] at this
    simp at this
    omega
  have hsub : ∀ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w ⊆ Ioc (0 : ℝ) 1 :=
    fun w hw => halfOpenCylinder_subset_Ioc (hwne w hw) (hW w hw).2
  have hmw : ∀ w ∈ W, MeasurableSet (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hmU : MeasurableSet U := Finset.measurableSet_biUnion _ hmw
  -- integrability of `f` on any measurable subset of `(0, 1]`
  have hint : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioc (0 : ℝ) 1 → IntegrableOn f s := by
    intro s hms hss
    have hfin : IsFiniteMeasure (volume.restrict s) := by
      constructor
      rw [Measure.restrict_apply_univ]
      calc volume s ≤ volume (Ioc (0 : ℝ) 1) := measure_mono hss
        _ < ⊤ := by rw [Real.volume_Ioc]; norm_num
    exact Integrable.of_bound hfm.aestronglyMeasurable B (Eventually.of_forall hfb)
  have hintIoo : IntegrableOn f (Ioo (0 : ℝ) 1) :=
    hint _ measurableSet_Ioo (fun x hx => ⟨hx.1, hx.2.le⟩)
  -- split `Ioo` into `Ioo ∩ U` and `Ioo \ U`
  have hsplit := integral_inter_add_diff (μ := volume) (s := Ioo (0 : ℝ) 1)
    (t := U) (f := f) hmU hintIoo
  -- `Ioo ∩ U =ᵐ U`, the difference being at most `{1}`
  have hUsub : U ⊆ Ioc (0 : ℝ) 1 := by
    rw [hU]
    exact Set.iUnion₂_subset hsub
  have hae : (Ioo (0 : ℝ) 1 ∩ U : Set ℝ) =ᵐ[volume] U := by
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · rw [Set.diff_eq_empty.mpr Set.inter_subset_right]
      exact measure_empty
    · refine measure_mono_null (fun x hx => ?_) (measure_singleton (1 : ℝ))
      rcases hx with ⟨hxU, hxn⟩
      have hxIoc := hUsub hxU
      have : x ∉ Ioo (0 : ℝ) 1 := fun hxo => hxn ⟨hxo, hxU⟩
      rw [Set.mem_singleton_iff]
      rcases lt_or_eq_of_le hxIoc.2 with hlt | heq
      · exact absurd ⟨hxIoc.1, hlt⟩ this
      · exact heq
  have hIU : ∫ α in Ioo (0 : ℝ) 1 ∩ U, f α = ∫ α in U, f α :=
    setIntegral_congr_set hae
  -- the integral over `U` is the sum over the disjoint retained cylinders
  have hdisj : (W : Set (List ℕ)).PairwiseDisjoint
      (fun w => Erdos1002.gaussHalfOpenPrefixCylinder w) := by
    intro x hx y hy hxy
    exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
      (by rw [(hW x hx).1, (hW y hy).1]) ((hW x hx).2) ((hW y hy).2) hxy
  have hUsum : ∫ α in U, f α
      = ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α := by
    rw [hU]
    exact integral_biUnion_finset W hmw hdisj (fun w hw => hint _ (hmw w hw) (hsub w hw))
  rw [← hsplit, hIU, hUsum]

/-! ### Step 1 of the three-step chain, conditional form -/

/-- **The retained-cylinder cut (step 1 of `nonzero_mode_three_step`,
conditional on the discarded mass).**  If the discarded set of the depth-`d`
partition has Lebesgue mass at most `η`, then `modeTerm` differs from its
retained-cylinder truncation

`T₁ = Σ_{w ∈ W} ∫_{I_w} (∏_ℓ c_ℓ(a_{j_ℓ+1}, v_ℓ)) e(nQ(α)α) dα`

by at most `(L^D)^r · η`.  Display (20) — the Lévy large-deviation bound
for `log q_j`, absent from the tree — is exactly what supplies a `W` (the
depth-`k₊` words retained at `j_s`, `k₋`, `k₊`) with `η = O(e^{-cL^{1/2}})`;
with that input this is the first bound of `nonzero_mode_three_step` with
constant `C = 1`. -/
theorem nonzero_mode_cut_of_retained (n r : ℕ) (D : ℝ) (j : ℕ → ℕ)
    (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D (Lnorm n) F c)
    (v : Fin r → ℤ) (s : ℕ) (hs : s < r)
    (htop : ∀ ℓ : Fin r, s < (ℓ : ℕ) → v ℓ = 0)
    (W : Finset (List ℕ)) (d : ℕ) (hd : 0 < d)
    (hW : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) (η : ℝ)
    (hmass : (volume (Ioo (0 : ℝ) 1 \
        (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w))).toReal ≤ η) :
    ‖modeTerm n r j c v
        - ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
            (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
              torusChar ((n : ℝ) * ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α)‖
      ≤ ((Lnorm n) ^ D) ^ r * η := by
  classical
  have hB0 : (0 : ℝ) ≤ ((Lnorm n) ^ D) ^ r :=
    le_trans (norm_nonneg _) (norm_modeAmp_le n r D j F c hc v (1 / 2))
  have hgb : ∀ α : ℝ,
      ‖(∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
          torusChar ((n : ℝ) * ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α)‖
        ≤ ((Lnorm n) ^ D) ^ r := by
    intro α
    simp only [norm_mul, Prop42.norm_torusChar, mul_one]
    exact norm_modeAmp_le n r D j F c hc v α
  have hgm : Measurable (fun α : ℝ =>
      (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
        torusChar ((n : ℝ) * ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α)) :=
    (measurable_modeAmp r j c v).mul (measurable_modeOsc n j (modeExt r v) s)
  rw [modeTerm_eq_oscillatory n r j c v s hs htop,
    integral_Ioo_eq_retained_add_remainder _ (((Lnorm n) ^ D) ^ r) hgm hgb W d hd hW,
    add_sub_cancel_left]
  refine le_trans (norm_setIntegral_le_of_norm_le_const ?_ (fun x _ => hgb x)) ?_
  · calc volume (Ioo (0 : ℝ) 1 \
          (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w))
        ≤ volume (Ioo (0 : ℝ) 1) := measure_mono Set.diff_subset
      _ < ⊤ := by rw [Real.volume_Ioo]; norm_num
  · exact mul_le_mul_of_nonneg_left hmass hB0

/-! ### The frequency is an attribute of the retained cylinder

Display (22) requires "on `I_w`, `Q_w ∈ ℤ` is fixed".  The three lemmas
below deliver exactly that for the retained integrals of
`nonzero_mode_cut_of_retained`: every positive word `w` deep enough to
determine the digits read by `Q` carries a single frozen integer `Q_w`,
shared by all irrational points of its cylinder, and on the cylinder the
integrand's phase is the pure oscillation `e(nQ_w α)` of (22). -/

/-- An irrational point of a positive nonempty half-open prefix cylinder
lies in the open unit interval. -/
theorem mem_Ioo_of_mem_halfOpen {w : List ℕ} {α : ℝ} (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a)
    (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w) (hirr : Irrational α) :
    α ∈ Ioo (0 : ℝ) 1 := by
  have h := halfOpenCylinder_subset_Ioc hw hpos hα
  refine ⟨h.1, lt_of_le_of_ne h.2 ?_⟩
  intro h1
  exact hirr ⟨1, by rw [h1]; norm_num⟩

/-- An irrational point of a positive half-open prefix cylinder reads the
word off digit by digit. -/
theorem digit_eq_of_mem_halfOpen {w : List ℕ} {α : ℝ}
    (hαIoo : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w) :
    ∀ i (h : i < w.length), digit α i = w[i]'h := by
  have horb : ∀ k : ℕ, Erdos1002.gaussOrbit k α ∈ Ioo (0 : ℝ) 1 := by
    intro k
    rw [← MixingBV.gaussIter_eq_gaussOrbit]
    exact gaussIter_mem_Ioo hαIoo hirr k
  intro i h
  rw [MixingBV.digit_eq_gaussDigitAt]
  exact (MixingBV.mem_halfOpen_iff w α horb).1 hα i h

/-- **"On `I_w` the integer `Q` is fixed."**  All irrational points of the
cylinder of a positive word `w` with `j ℓ ≤ |w|` for `ℓ ≤ s` share one
frozen frequency. -/
theorem exists_frozen_freqQ (r : ℕ) (v : Fin r → ℤ) (j : ℕ → ℕ) (s : ℕ)
    (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a)
    (hjd : ∀ ℓ, ℓ ≤ s → j ℓ ≤ w.length) :
    ∃ Q : ℤ, ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α →
      Prop41Canon.freqQ α j (modeExt r v) s = Q := by
  classical
  by_cases hex : ∃ α₀, α₀ ∈ Erdos1002.gaussHalfOpenPrefixCylinder w ∧ Irrational α₀
  · obtain ⟨α₀, hα₀, hirr₀⟩ := hex
    refine ⟨Prop41Canon.freqQ α₀ j (modeExt r v) s, ?_⟩
    intro α hα hirr
    refine freqQ_congr j (modeExt r v) s w.length hjd (fun i hi => ?_)
    rw [digit_eq_of_mem_halfOpen (mem_Ioo_of_mem_halfOpen hw hpos hα hirr) hirr hα i hi,
      digit_eq_of_mem_halfOpen (mem_Ioo_of_mem_halfOpen hw hpos hα₀ hirr₀) hirr₀ hα₀ i hi]
  · exact ⟨0, fun α hα hirr => absurd ⟨α, hα, hirr⟩ hex⟩

/-- `e(t)` at `t = Kx` is the oscillatory phase of the Wang substrate; this
is the notational bridge between the §4 torus character and the phase of
display (22). -/
theorem torusChar_eq_oscillatoryPhase (K x : ℝ) :
    torusChar (K * x) = Erdos1002.oscillatoryPhase K x := by
  unfold torusChar Erdos1002.oscillatoryPhase
  congr 1
  push_cast
  ring

/-- **The retained integrals are display (22)-shaped.**  On the cylinder of
each retained word the phase freezes to the pure oscillation `e(nQ_w α)`,
so each summand of the `T₁` of `nonzero_mode_cut_of_retained` is literally
of the form `∫_{I_w} e(2πi n Q_w α) A(α) dα` that
`Kwon1002.descendant_cylinder_estimate` (display (22)) consumes.  This
completes the reduction of `modeTerm` to the shape
`Σ_w ∫_{I_w} e(nQ_wα)·(amplitude)`; what remains between this and the
three-step chain is (i) display (20) selecting the retained words with
small discarded mass, and (ii) the conditional stationary-mean replacement
of step 2. -/
theorem retained_integral_oscillatory_form (n r : ℕ) (j : ℕ → ℕ)
    (c : ℕ → ℕ → ℤ → ℂ) (v : Fin r → ℤ) (s : ℕ)
    (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a)
    (hjd : ∀ ℓ, ℓ ≤ s → j ℓ ≤ w.length) :
    ∃ Q : ℤ,
      (∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α →
        Prop41Canon.freqQ α j (modeExt r v) s = Q) ∧
      (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
          (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
            torusChar ((n : ℝ) * ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α))
        = ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
            Erdos1002.oscillatoryPhase ((n : ℝ) * (Q : ℝ)) α *
              (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) := by
  obtain ⟨Q, hQ⟩ := exists_frozen_freqQ r v j s w hw hpos hjd
  refine ⟨Q, hQ, ?_⟩
  have hairr : ∀ᵐ α ∂(volume : Measure ℝ), Irrational α := by
    rw [ae_iff]
    have hc : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
    have hset : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
      ext x
      simp [Irrational]
    rw [hset]
    exact hc.measure_zero volume
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem
    (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w),
    ae_restrict_of_ae hairr] with α hα hirr
  rw [hQ α hα hirr, mul_comm]
  congr 1
  rw [← torusChar_eq_oscillatoryPhase]

/-! ### Step 3 of the three-step chain, retained form -/

/-- A positive half-open prefix cylinder and its closed version agree up to
a Lebesgue-null set: the two conventions of `nonzero_mode_cut_of_retained`
(half-open, disjoint) and display (22) (closed) are interchangeable inside
every integral. -/
theorem halfOpen_ae_eq_closed {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    Erdos1002.gaussHalfOpenPrefixCylinder w
      =ᵐ[volume] Erdos1002.closedGaussPrefixCylinder w := by
  have hsub := Erdos1002.gaussHalfOpenPrefixCylinder_subset_closed hpos
  refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
  · rw [Set.diff_eq_empty.mpr hsub]
    exact measure_empty
  · have hfin : volume (Erdos1002.gaussHalfOpenPrefixCylinder w) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (by simp : volume (Icc (0 : ℝ) 1) ≠ ⊤) ?_
      exact measure_mono (hsub.trans
        (Erdos1002.closedGaussPrefixCylinder_subset_unit hpos))
    rw [measure_diff hsub
        (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w).nullMeasurableSet hfin,
      volume_closedCylinder_eq_halfOpen hpos, tsub_self]

/-! ## The three-step chain and step 3

`Kwon1002.ZeroMode.nonzero_mode_three_step` and
`Kwon1002.ZeroMode.nonzero_mode_small` are **declared in
`Kwon1002/NonzeroMode.lean`**, not here.  The chain's own proof is assembled
there, above this module, so declarations placed here could never lose their
`sorry`; the obstruction note that used to sit on the chain is reproduced at
its declaration site.  Everything the chain consumes from this module is
proved above. -/

end

end ZeroMode

end Kwon1002
