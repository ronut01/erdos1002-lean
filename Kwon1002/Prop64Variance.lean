import Kwon1002.Prop42Unconditional
import Kwon1002.TupleInputs
import Kwon1002.StoppingWindow

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002.Prop64Variance

noncomputable section

/-- The centered alternating average used by the polynomial variance estimate. -/
def varianceCenteredAvg (L : ℝ) (s : Finset ℕ) (Z : ℕ → ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / L) * ∑ j ∈ s, (-1 : ℝ) ^ j *
    (Z j α - ∫ β in Ioo (0 : ℝ) 1, Z j β)

private lemma sum_Icc_neg {K : ℕ} (f : ℤ → ℂ) :
    ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f (-r)
      = ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f r := by
  refine Finset.sum_nbij' (fun r => -r) (fun r => -r) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a _; exact neg_neg a
  · intro a _; exact neg_neg a
  · intro a _; rfl

private lemma torusChar_conj (t : ℝ) :
    (starRingEnd ℂ) (torusChar t) = torusChar (-t) := by
  simp only [torusChar, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

private def varianceSymConj {R K : ℕ} (U : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := (starRingEnd ℂ) (U.coeff w (-r) (-s))
  words := U.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w (-r) (-s) hw, map_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w (-r) (-s) (by simpa using h), map_zero]

private def varianceSymAdd {R K : ℕ} (U V : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := U.coeff w r s + V.coeff w r s
  words := U.words ∪ V.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w r s (fun h => hw (Finset.mem_union_left _ h)),
      V.coeff_support w r s (fun h => hw (Finset.mem_union_right _ h)), add_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w r s h, V.mode_cap w r s h, add_zero]

private def varianceSymSmul {R K : ℕ} (c : ℂ) (U : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := c * U.coeff w r s
  words := U.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w r s hw, mul_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w r s h, mul_zero]

private lemma evalWindow_varianceSymAdd {R K : ℕ} (U V : WindowSymbol R K)
    (w : WindowSpace R) :
    (varianceSymAdd U V).evalWindow w = U.evalWindow w + V.evalWindow w := by
  simp only [WindowSymbol.evalWindow, varianceSymAdd, add_mul, Finset.sum_add_distrib]

private lemma evalWindow_varianceSymSmul {R K : ℕ} (c : ℂ) (U : WindowSymbol R K)
    (w : WindowSpace R) :
    (varianceSymSmul c U).evalWindow w = c * U.evalWindow w := by
  simp only [WindowSymbol.evalWindow, varianceSymSmul, mul_assoc, Finset.mul_sum]

private lemma evalWindow_varianceSymConj {R K : ℕ} (U : WindowSymbol R K)
    (w : WindowSpace R) :
    (varianceSymConj U).evalWindow w = (starRingEnd ℂ) (U.evalWindow w) := by
  have key : ∀ G : ℤ → ℤ → ℂ,
      ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), G r s
        = ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), G (-r) (-s) := by
    intro G
    rw [← sum_Icc_neg (fun r => ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), G r s)]
    exact Finset.sum_congr rfl fun r _ => (sum_Icc_neg (fun s => G (-r) s)).symm
  have hstar : (starRingEnd ℂ) (U.evalWindow w)
      = ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (starRingEnd ℂ) (U.coeff (windowWordOf R w) r s) *
            torusChar (-((r : ℝ) * wTh w (-1) + (s : ℝ) * wTh w 0)) := by
    simp only [WindowSymbol.evalWindow, map_sum, map_mul, torusChar_conj]
  rw [hstar, key (fun r s => (starRingEnd ℂ) (U.coeff (windowWordOf R w) r s) *
      torusChar (-((r : ℝ) * wTh w (-1) + (s : ℝ) * wTh w 0)))]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [varianceSymConj]
  congr 2
  push_cast
  ring

private def varianceSymRe {R K : ℕ} (U : WindowSymbol R K) : WindowSymbol R K :=
  varianceSymSmul (1 / 2) (varianceSymAdd U (varianceSymConj U))

private lemma evalWindow_varianceSymRe {R K : ℕ} (U : WindowSymbol R K)
    (w : WindowSpace R) :
    (varianceSymRe U).evalWindow w = ((U.evalWindow w).re : ℂ) := by
  rw [varianceSymRe, evalWindow_varianceSymSmul, evalWindow_varianceSymAdd,
    evalWindow_varianceSymConj, Complex.add_conj]
  push_cast
  ring

private lemma varianceMeasurableSymbolAt {R K : ℕ} (P : WindowSymbol R K) (n j : ℕ) :
    Measurable fun α : ℝ => P.at α n j := by
  unfold WindowSymbol.at
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ =>
    Measurable.mul ?_ ?_
  · exact (Measurable.of_discrete (f := fun v : Fin (2 * R) → ℕ => P.coeff v r s)).comp
      (measurable_pi_lambda _ fun _ => Prop42.measurable_digitNat _)
  · exact Prop42.continuous_torusChar.measurable.comp
      (((Prop42.measurable_thetaPred n j).const_mul _).add
        ((measurable_theta n j).const_mul _))

private lemma varianceNormSymbolAtLe {R K : ℕ} (P : WindowSymbol R K)
    (α : ℝ) (n j : ℕ) :
    ‖P.at α n j‖
      ≤ ∑ w ∈ P.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖ := by
  classical
  have hstep : ‖P.at α n j‖
      ≤ ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ‖P.coeff (windowWord R α j) r s‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, Prop42.norm_torusChar, mul_one]
  refine hstep.trans ?_
  by_cases hw : windowWord R α j ∈ P.words
  · exact Finset.single_le_sum
      (f := fun w => ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖)
      (fun w _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hw
  · have hzero : ∀ r s : ℤ, P.coeff (windowWord R α j) r s = 0 :=
      fun r s => P.coeff_support _ r s hw
    simp only [hzero, norm_zero, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma varianceMemLpSymbolAt {R K : ℕ} (P : WindowSymbol R K) (n j : ℕ) :
    MemLp (fun α => (P.at α n j).re) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  classical
  refine MemLp.of_bound
    ((Complex.measurable_re.comp (varianceMeasurableSymbolAt P n j)).aestronglyMeasurable)
    (∑ w ∈ P.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖)
    (Filter.Eventually.of_forall fun α => ?_)
  refine le_trans ?_ (varianceNormSymbolAtLe P α n j)
  rw [Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _


private abbrev prob : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

private def rawAvg {R' K : ℕ} (P : WindowSymbol R' K) (n : ℕ) (α : ℝ) : ℝ :=
  (1 / Lnorm n) * ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j * (P.at α n j).re

private lemma integrable_rawAvg {R' K : ℕ} (P : WindowSymbol R' K) (n : ℕ) :
    Integrable (rawAvg P n) prob := by
  refine Integrable.const_mul (integrable_finset_sum _ fun j _ => ?_) _
  exact (varianceMemLpSymbolAt P n j).integrable (by norm_num) |>.const_mul _

private lemma memLp_rawAvg {R' K : ℕ} (P : WindowSymbol R' K) (n : ℕ) :
    MemLp (rawAvg P n) 2 prob := by
  refine (memLp_finset_sum (s := bulkJ n) fun j _ =>
    (varianceMemLpSymbolAt P n j).const_mul ((-1 : ℝ) ^ j)).const_mul (1 / Lnorm n)

private lemma varianceCenteredAvg_eq_raw_sub_mean {R M K : ℕ} (P : WindowSymbol (R + M) K)
    (n : ℕ) :
    varianceCenteredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)
      = fun α => rawAvg P n α - ∫ β, rawAvg P n β ∂prob := by
  funext α
  unfold varianceCenteredAvg rawAvg
  rw [integral_const_mul,
    integral_finset_sum _ fun j _ => (varianceMemLpSymbolAt P n j).integrable (by norm_num) |>.const_mul _]
  simp only [integral_const_mul]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 2
  funext j
  ring

private lemma integral_sub_mean_sq_le {X : Type*} [MeasurableSpace X] {mu : Measure X}
    [IsProbabilityMeasure mu] {f : X → ℝ} (hf : Integrable f mu) (b : ℝ)
    (hsq : Integrable (fun x => (f x - b) ^ 2) mu) :
    ∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu ≤ ∫ x, (f x - b) ^ 2 ∂mu := by
  set m := ∫ x, f x ∂mu with hm
  have hconst : ∀ r : ℝ, ∫ _x : X, r ∂mu = r := by intro r; rw [integral_const]; simp
  have hfb := hf.sub (integrable_const b)
  have hlin : Integrable (fun x => 2 * (m - b) * (f x - b)) mu := hfb.const_mul _
  have hint2 : Integrable (fun x => (f x - b) ^ 2 - 2 * (m - b) * (f x - b)) mu :=
    hsq.sub hlin
  have hint1 : ∫ x, (f x - b) ∂mu = m - b := by
    rw [integral_sub hf (integrable_const b), hconst, hm]
  have key : ∫ x, (f x - m) ^ 2 ∂mu
      = (∫ x, (f x - b) ^ 2 ∂mu) - 2 * (m - b) * (m - b) + (m - b) ^ 2 := by
    have e1 : ∫ x, (f x - m) ^ 2 ∂mu
        = ∫ x, ((f x - b) ^ 2 - 2 * (m - b) * (f x - b) + (m - b) ^ 2) ∂mu := by
      congr 1; funext x; ring
    rw [e1, integral_add hint2 (integrable_const _), hconst,
      integral_sub hsq hlin, integral_const_mul, hint1]
  rw [key]
  nlinarith [sq_nonneg (m - b)]

private lemma memLp_centered {R M K : ℕ} (P : WindowSymbol (R + M) K) (n : ℕ) :
    MemLp (varianceCenteredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)) 2 prob := by
  rw [varianceCenteredAvg_eq_raw_sub_mean P n]
  exact (memLp_finset_sum (s := bulkJ n) fun j _ =>
    ((varianceMemLpSymbolAt P n j).const_mul ((-1 : ℝ) ^ j))).const_mul (1 / Lnorm n) |>.sub
      (memLp_const _)

private lemma eLpNorm_two_eq {f : ℝ → ℝ} (hf : MemLp f 2 prob) :
    eLpNorm f 2 prob = ENNReal.ofReal (Real.sqrt (∫ x, (f x) ^ 2 ∂prob)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 2
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp [sq]

private lemma target_of_raw_second_moment {R M K : ℕ} (P : WindowSymbol (R + M) K)
    (hraw : Tendsto (fun n : ℕ => ∫ α, (rawAvg P n α) ^ 2 ∂prob) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm
        (varianceCenteredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)) 2 prob)
      atTop (𝓝 0) := by
  have hsecond : Tendsto (fun n : ℕ =>
      ∫ α, (varianceCenteredAvg (Lnorm n) (bulkJ n)
        (fun j α => (P.at α n j).re) α) ^ 2 ∂prob) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hraw
    · filter_upwards [] with n; exact integral_nonneg fun α => sq_nonneg _
    · filter_upwards [] with n
      rw [varianceCenteredAvg_eq_raw_sub_mean P n]
      simpa only [sub_zero] using integral_sub_mean_sq_le (integrable_rawAvg P n) 0
        (by simpa [sq] using (memLp_rawAvg P n).integrable_mul (memLp_rawAvg P n))
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsecond
  have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  simpa [eLpNorm_two_eq (memLp_centered P _)] using hofReal

private lemma eventually_bulk_radius (R' : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n, R' + 1 ≤ j := by
  filter_upwards [P42Cases.tendsto_Hscale.eventually_ge_atTop ((R' + 1 : ℝ) / 200)] with n hn
  intro j hj
  rw [bulkJ, Finset.mem_filter] at hj
  have hlo := hj.2.1
  have hcast : (R' + 1 : ℝ) ≤ 200 * Hscale n := by
    nlinarith
  exact_mod_cast (hcast.trans hlo)

private lemma varianceSymRe_at_eq_re {R' K : ℕ} (P : WindowSymbol R' K) (n j : ℕ)
    (hj : R' + 1 ≤ j) (α : ℝ) : (varianceSymRe P).at α n j = ((P.at α n j).re : ℂ) := by
  rw [← WindowSymbol.evalWindow_actualWindow (varianceSymRe P) α n j hj,
    evalWindow_varianceSymRe, WindowSymbol.evalWindow_actualWindow P α n j hj]

private lemma varianceSymRe_at_re {R' K : ℕ} (P : WindowSymbol R' K) (n j : ℕ)
    (hj : R' + 1 ≤ j) (α : ℝ) : ((varianceSymRe P).at α n j).re = (P.at α n j).re := by
  rw [varianceSymRe_at_eq_re P n j hj]
  simp

private lemma rawAvg_varianceSymRe_eq {R M K : ℕ} (P : WindowSymbol (R + M) K) (n : ℕ)
    (hn : ∀ j ∈ bulkJ n, R + M + 1 ≤ j) : rawAvg (varianceSymRe P) n = rawAvg P n := by
  funext α
  unfold rawAvg
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [varianceSymRe_at_re P n j (hn j hj)]

private lemma sum_lt_eq_bulkPairs (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n, (if j < k then F j k else 0)
      = ∑ p ∈ bulkPairs n, F p.1 p.2 := by
  simp [bulkPairs, Finset.sum_filter, Finset.sum_product]

private lemma sum_offdiag_eq_two_bulkPairs (n : ℕ) (F : ℕ → ℕ → ℝ)
    (hsym : ∀ j k, F j k = F k j) :
    ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n, (if j = k then 0 else F j k)
      = 2 * ∑ p ∈ bulkPairs n, F p.1 p.2 := by
  have hsplit : ∀ j k : ℕ, (if j = k then 0 else F j k)
      = (if j < k then F j k else 0) + (if k < j then F j k else 0) := by
    intro j k
    by_cases h : j = k
    · simp [h]
    · rcases lt_or_gt_of_ne h with hlt | hgt
      · simp [h, hlt, Nat.not_lt_of_ge hlt.le]
      · simp [h, hgt, Nat.not_lt_of_ge hgt.le]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [sum_lt_eq_bulkPairs n F]
  have hrev :
      (∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n, (if k < j then F j k else 0))
        = ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n, (if j < k then F j k else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym]
  rw [hrev, sum_lt_eq_bulkPairs n F]
  ring

private lemma sum_le_bad_good {s : Finset (ℕ × ℕ)} (F : (ℕ × ℕ) → ℝ)
    (bad : Finset (ℕ × ℕ)) (D δ : ℝ)
    (hF0 : ∀ p, 0 ≤ F p) (hD0 : 0 ≤ D) (hδ0 : 0 ≤ δ) (hD : ∀ p ∈ s, F p ≤ D)
    (hgood : ∀ p ∈ s, p ∉ bad → F p ≤ δ) :
    ∑ p ∈ s, F p ≤ (bad.card : ℝ) * D + (s.card : ℝ) * δ := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun p => p ∈ bad)]
  calc
    ∑ p ∈ s.filter (fun p => p ∈ bad), F p
        + ∑ p ∈ s.filter (fun p => ¬ p ∈ bad), F p
      ≤ ((s.filter (fun p => p ∈ bad)).card : ℝ) * D
          + ((s.filter (fun p => ¬ p ∈ bad)).card : ℝ) * δ := by
        gcongr
        · calc
            ∑ p ∈ s.filter (fun p => p ∈ bad), F p
                ≤ ∑ _p ∈ s.filter (fun p => p ∈ bad), D := by
                  gcongr with p hp
                  exact hD p (Finset.mem_filter.mp hp).1
            _ = ((s.filter (fun p => p ∈ bad)).card : ℝ) * D := by
                  rw [Finset.sum_const, nsmul_eq_mul]
        · calc
            ∑ p ∈ s.filter (fun p => ¬ p ∈ bad), F p
                ≤ ∑ _p ∈ s.filter (fun p => ¬ p ∈ bad), δ := by
                  gcongr with p hp
                  exact hgood p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
            _ = ((s.filter (fun p => ¬ p ∈ bad)).card : ℝ) * δ := by
                  rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (bad.card : ℝ) * D + (s.card : ℝ) * δ := by
      have hb : ((s.filter (fun p => p ∈ bad)).card : ℝ) ≤ bad.card := by
        exact_mod_cast Finset.card_le_card (by intro p hp; simp_all)
      have hs : ((s.filter (fun p => ¬ p ∈ bad)).card : ℝ) ≤ s.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      exact add_le_add (mul_le_mul_of_nonneg_right hb hD0)
        (mul_le_mul_of_nonneg_right hs hδ0)

private def pairErr {R' K : ℕ} (Q : WindowSymbol R' K) (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  ‖(∫ α in Ioo (0 : ℝ) 1, Q.at α n p.1 * Q.at α n p.2)
      - Q.stationaryIntegral * Q.stationaryIntegral‖

private def symbolMass {R' K : ℕ} (Q : WindowSymbol R' K) : ℝ :=
  ∑ w ∈ Q.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖Q.coeff w r s‖

private lemma pairErr_nonneg {R' K : ℕ} (Q : WindowSymbol R' K) (n : ℕ) (p : ℕ × ℕ) :
    0 ≤ pairErr Q n p := norm_nonneg _

private lemma pairErr_symm {R' K : ℕ} (Q : WindowSymbol R' K) (n j k : ℕ) :
    pairErr Q n (j, k) = pairErr Q n (k, j) := by
  unfold pairErr
  congr 2
  apply integral_congr_ae
  filter_upwards [] with α
  ring

private lemma norm_integral_symbol_mul_le {R' K : ℕ} (Q : WindowSymbol R' K)
    (n j k : ℕ) :
    ‖∫ α in Ioo (0 : ℝ) 1, Q.at α n j * Q.at α n k‖ ≤ (symbolMass Q) ^ 2 := by
  have h := norm_integral_le_of_norm_le_const
    (μ := prob) (C := (symbolMass Q) ^ 2)
    (f := fun α : ℝ => Q.at α n j * Q.at α n k)
    (Eventually.of_forall fun α => by
      rw [norm_mul]
      have hjb : ‖Q.at α n j‖ ≤ symbolMass Q := by
        simpa [symbolMass] using varianceNormSymbolAtLe Q α n j
      have hkb : ‖Q.at α n k‖ ≤ symbolMass Q := by
        simpa [symbolMass] using varianceNormSymbolAtLe Q α n k
      rw [sq]
      exact mul_le_mul hjb hkb (norm_nonneg _) (by
        exact le_trans (norm_nonneg _) hjb))
  simpa [symbolMass, sq] using h

private lemma pairErr_le_uniform {R' K : ℕ} (Q : WindowSymbol R' K)
    (n : ℕ) (p : ℕ × ℕ) :
    pairErr Q n p ≤ (symbolMass Q) ^ 2 + ‖Q.stationaryIntegral * Q.stationaryIntegral‖ := by
  exact (norm_sub_le _ _).trans (add_le_add (norm_integral_symbol_mul_le Q n p.1 p.2) le_rfl)

private theorem pairErr_normalized_tendsto_zero {R' K : ℕ} (Q : WindowSymbol R' K) :
    Tendsto (fun n : ℕ => (1 / Lnorm n) ^ 2 * ∑ p ∈ bulkPairs n, pairErr Q n p)
      atTop (𝓝 0) := by
  obtain ⟨C, c, rho, hC, hc, hr0, hr1, hfac⟩ :=
    Kwon1002.prop_4_2_two_block_factorization Q Q
  let D : ℝ := (symbolMass Q) ^ 2 + ‖Q.stationaryIntegral * Q.stationaryIntegral‖
  let A : ℝ := 1 / lyapunov + 1
  let E : ℕ → ℝ := fun n => Real.exp (-c * Real.sqrt (Lnorm n))
      + Real.exp (-c * Hscale n) + rho ^ (c * Hscale n)
  have hE : Tendsto E atTop (𝓝 0) := by
    have h1 := StopWin.tendsto_exp_neg_sqrt_Lnorm hc
    have hH : Tendsto (fun n : ℕ => c * Hscale n) atTop atTop :=
      P42Cases.tendsto_Hscale.const_mul_atTop hc
    have h2 : Tendsto (fun n : ℕ => Real.exp (-c * Hscale n)) atTop (𝓝 0) := by
      have hn : Tendsto (fun x : ℝ => -x) atTop atBot := tendsto_neg_atTop_atBot
      have ht := Real.tendsto_exp_atBot.comp (hn.comp hH)
      simpa only [Function.comp_apply, neg_mul] using ht
    have h3 : Tendsto (fun n : ℕ => rho ^ (c * Hscale n)) atTop (𝓝 0) :=
      (tendsto_rpow_atTop_of_base_lt_one rho (by linarith) hr1).comp hH
    change Tendsto (fun n : ℕ => Real.exp (-c * Real.sqrt (Lnorm n))
      + Real.exp (-c * Hscale n) + rho ^ (c * Hscale n)) atTop (𝓝 0)
    simpa using (h1.add h2).add h3
  have hmaj : Tendsto (fun n : ℕ => D * C * (Hscale n / Lnorm n) + A ^ 2 * C * E n)
      atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => D * C * (Hscale n / Lnorm n) + A ^ 2 * C *
      (Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n)
        + rho ^ (c * Hscale n))) atTop (𝓝 0)
    simpa using ((StopWin.tendsto_Hscale_div_Lnorm.const_mul (D * C)).add
      (hE.const_mul (A ^ 2 * C)))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [] with n
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun p _ => pairErr_nonneg Q n p)
  · filter_upwards [hfac, TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop (1 : ℝ),
      TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hn hL1 hL
    let bad := (bulkPairs n).filter (fun p => ¬ pairErr Q n p ≤ C * E n)
    have hbad : ((bad.card : ℕ) : ℝ) ≤ C * Lnorm n * Hscale n := by
      rw [show bad = (bulkPairs n).filter (fun p => ¬ pairErr Q n p ≤ C * E n) from rfl,
        ← Set.ncard_coe_finset, Finset.coe_filter]
      simpa [pairErr, E] using hn
    have hsum : ∑ p ∈ bulkPairs n, pairErr Q n p
        ≤ (bad.card : ℝ) * D + ((bulkPairs n).card : ℝ) * (C * E n) := by
      exact sum_le_bad_good (s := bulkPairs n) (F := pairErr Q n) bad D (C * E n)
        (pairErr_nonneg Q n) (by dsimp [D]; positivity) (by dsimp [E]; positivity)
        (fun p hp => pairErr_le_uniform Q n p)
        (fun p hp hpb => by
          by_contra hnot
          apply hpb
          change p ∈ (bulkPairs n).filter (fun p => ¬ pairErr Q n p ≤ C * E n)
          exact Finset.mem_filter.mpr ⟨hp, hnot⟩)
    have hJ := MonomialCore.card_bulkJ_le n hL1
    have hpair : (((bulkPairs n).card : ℕ) : ℝ) ≤ (A * Lnorm n) ^ 2 := by
      have hcNat : (bulkPairs n).card ≤ (bulkJ n ×ˢ bulkJ n).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_product.mpr
          ⟨MonomialCore.mem_bulkPairs_fst hp, PhaseBounds.mem_bulkPairs_snd hp⟩
      have hcMul : ((bulkPairs n).card : ℝ) ≤
          ((bulkJ n).card : ℝ) * ((bulkJ n).card : ℝ) := by
        rw [Finset.card_product] at hcNat
        exact_mod_cast hcNat
      have hc : ((bulkPairs n).card : ℝ) ≤ ((bulkJ n).card : ℝ) ^ 2 := by
        simpa [sq] using hcMul
      calc
        ((bulkPairs n).card : ℝ) ≤ ((bulkJ n).card : ℝ) ^ 2 := hc
        _ ≤ (A * Lnorm n) ^ 2 :=
          (sq_le_sq₀ (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hJ)).2 hJ
    have hsum' := hsum.trans (add_le_add (mul_le_mul_of_nonneg_right hbad (by positivity))
      (mul_le_mul_of_nonneg_right hpair (by positivity)))
    calc
      (1 / Lnorm n) ^ 2 * ∑ p ∈ bulkPairs n, pairErr Q n p
          ≤ (1 / Lnorm n) ^ 2 *
            ((C * Lnorm n * Hscale n) * D + (A * Lnorm n) ^ 2 * (C * E n)) := by
              gcongr
      _ = D * C * (Hscale n / Lnorm n) + A ^ 2 * C * E n := by
            field_simp

private def realMoment {R' K : ℕ} (Q : WindowSymbol R' K) (n j k : ℕ) : ℝ :=
  ∫ α in Ioo (0 : ℝ) 1, (Q.at α n j).re * (Q.at α n k).re

private lemma varianceMemLpSymbolAt_complex {R' K : ℕ} (Q : WindowSymbol R' K) (n j : ℕ) :
    MemLp (fun α : ℝ => Q.at α n j) 2 prob := by
  refine MemLp.of_bound (varianceMeasurableSymbolAt Q n j).aestronglyMeasurable (symbolMass Q) ?_
  filter_upwards [] with α
  simpa [symbolMass] using varianceNormSymbolAtLe Q α n j

private lemma realMoment_symm {R' K : ℕ} (Q : WindowSymbol R' K) (n j k : ℕ) :
    realMoment Q n j k = realMoment Q n k j := by
  apply integral_congr_ae
  filter_upwards [] with α
  ring

private lemma realMoment_sub_stationary_le_pairErr {R' K : ℕ} (Q : WindowSymbol R' K)
    (n j k : ℕ) (hj : R' + 1 ≤ j) (hk : R' + 1 ≤ k)
    (hreal : ∀ α, Q.at α n j = (((Q.at α n j).re : ℝ) : ℂ) ∧
      Q.at α n k = (((Q.at α n k).re : ℝ) : ℂ)) :
    |realMoment Q n j k - (Q.stationaryIntegral * Q.stationaryIntegral).re|
      ≤ pairErr Q n (j, k) := by
  have hint : (∫ α in Ioo (0 : ℝ) 1, Q.at α n j * Q.at α n k).re
      = realMoment Q n j k := by
    change (∫ α, Q.at α n j * Q.at α n k ∂prob).re = _
    have hi : Integrable (fun α : ℝ => Q.at α n j * Q.at α n k) prob :=
      (varianceMemLpSymbolAt_complex Q n j).integrable_mul (varianceMemLpSymbolAt_complex Q n k)
    calc
      (∫ α, Q.at α n j * Q.at α n k ∂prob).re
          = ∫ α, (Q.at α n j * Q.at α n k).re ∂prob :=
            (integral_re (𝕜 := ℂ) hi).symm
      _ = realMoment Q n j k := by
        unfold realMoment
        apply integral_congr_ae
        filter_upwards [] with α
        rw [(hreal α).1, (hreal α).2]
        simp
  rw [← hint]
  change |((∫ α in Ioo (0 : ℝ) 1, Q.at α n j * Q.at α n k)
      - Q.stationaryIntegral * Q.stationaryIntegral).re| ≤ _
  exact Complex.abs_re_le_norm _

private lemma raw_second_moment_expand {R' K : ℕ} (Q : WindowSymbol R' K) (n : ℕ) :
    ∫ α, (rawAvg Q n α) ^ 2 ∂prob
      = (1 / Lnorm n) ^ 2 * ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * realMoment Q n j k := by
  unfold rawAvg
  have hp : ∀ α : ℝ,
      ((1 / Lnorm n) * ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j * (Q.at α n j).re) ^ 2
        = (1 / Lnorm n) ^ 2 * ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
            (((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) *
              ((Q.at α n j).re * (Q.at α n k).re)) := by
    intro α
    calc
      ((1 / Lnorm n) * ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j * (Q.at α n j).re) ^ 2
          = (1 / Lnorm n) ^ 2 *
            ((∑ j ∈ bulkJ n, (-1 : ℝ) ^ j * (Q.at α n j).re) *
              ∑ k ∈ bulkJ n, (-1 : ℝ) ^ k * (Q.at α n k).re) := by ring
      _ = _ := by
        rw [Finset.sum_mul_sum]
        ring
  rw [integral_congr_ae (Eventually.of_forall hp), integral_const_mul]
  congr 1
  change (∫ a, ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
    (-1 : ℝ) ^ j * (-1 : ℝ) ^ k * ((Q.at a n j).re * (Q.at a n k).re) ∂prob) = _
  have hterm (j k : ℕ) : Integrable (fun a : ℝ =>
      (-1 : ℝ) ^ j * (-1 : ℝ) ^ k * ((Q.at a n j).re * (Q.at a n k).re)) prob :=
    ((varianceMemLpSymbolAt Q n j).integrable_mul (varianceMemLpSymbolAt Q n k)).const_mul _
  rw [MeasureTheory.integral_finset_sum (μ := prob) (bulkJ n)
    (fun j _ => integrable_finset_sum (bulkJ n) (fun k _ => hterm j k))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MeasureTheory.integral_finset_sum (μ := prob) (bulkJ n) (fun k _ => hterm j k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  rfl

private theorem raw_second_moment_tendsto_zero {R M K : ℕ}
    (P : WindowSymbol (R + M) K) :
    Tendsto (fun n : ℕ => ∫ α, (rawAvg P n α) ^ 2 ∂prob) atTop (𝓝 0) := by
  let Q := varianceSymRe P
  let D : ℝ := (symbolMass Q) ^ 2 + ‖Q.stationaryIntegral * Q.stationaryIntegral‖
  let q : ℝ := (Q.stationaryIntegral * Q.stationaryIntegral).re
  let A : ℝ := 1 / lyapunov + 1
  have hpairs := pairErr_normalized_tendsto_zero Q
  have halt : Tendsto (fun n : ℕ => |∑ j ∈ bulkJ n, (-1 : ℝ) ^ j| / Lnorm n)
      atTop (𝓝 0) := by
    simpa [abs_div, abs_of_nonneg (Lnorm_nonneg _)] using TupleInputs.tendsto_alt_div.abs
  have hdiag : Tendsto (fun n : ℕ => D * A * (1 / Lnorm n)) atTop (𝓝 0) :=
    by simpa using TupleFinal.tendsto_one_div_L.const_mul (D * A)
  have hmaj : Tendsto (fun n : ℕ => |q| *
        (|∑ j ∈ bulkJ n, (-1 : ℝ) ^ j| / Lnorm n) ^ 2
        + D * A * (1 / Lnorm n)
        + 2 * ((1 / Lnorm n) ^ 2 * ∑ p ∈ bulkPairs n, pairErr Q n p))
      atTop (𝓝 0) := by
    simpa using (((halt.pow 2).const_mul |q|).add hdiag |>.add (hpairs.const_mul 2))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [] with n
    exact integral_nonneg fun α => sq_nonneg _
  · filter_upwards [eventually_bulk_radius (R + M),
      TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop (1 : ℝ),
      TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hn hL1 hL
    rw [← rawAvg_varianceSymRe_eq P n hn, raw_second_moment_expand Q n]
    have herr : ∀ j ∈ bulkJ n, ∀ k ∈ bulkJ n,
        |realMoment Q n j k - q| ≤ pairErr Q n (j, k) := by
      intro j hj k hk
      apply realMoment_sub_stationary_le_pairErr Q n j k (hn j hj) (hn k hk)
      intro α
      constructor <;> rw [show Q = varianceSymRe P from rfl, varianceSymRe_at_eq_re P n _ (hn _ (by assumption))]
      <;> simp
    have hsum :
        ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n, |realMoment Q n j k - q|
          ≤ (bulkJ n).card * D + 2 * ∑ p ∈ bulkPairs n, pairErr Q n p := by
      have hoff := sum_offdiag_eq_two_bulkPairs n
        (fun j k => |realMoment Q n j k - q|)
        (fun j k => by
          simpa only using congrArg (fun x => |x - q|) (realMoment_symm Q n j k))
      calc
        ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n, |realMoment Q n j k - q|
            = (∑ j ∈ bulkJ n, |realMoment Q n j j - q|) +
              ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
                (if j = k then 0 else |realMoment Q n j k - q|) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro j hj
                  calc
                    ∑ k ∈ bulkJ n, |realMoment Q n j k - q| =
                        ∑ k ∈ bulkJ n,
                          ((if j = k then |realMoment Q n j j - q| else 0) +
                            (if j = k then 0 else |realMoment Q n j k - q|)) := by
                              apply Finset.sum_congr rfl
                              intro k hk
                              by_cases h : j = k <;> simp [h]
                    _ = |realMoment Q n j j - q| +
                        ∑ k ∈ bulkJ n,
                          (if j = k then 0 else |realMoment Q n j k - q|) := by
                            rw [Finset.sum_add_distrib]
                            simp [hj]
          _ ≤ (bulkJ n).card * D + 2 * ∑ p ∈ bulkPairs n, pairErr Q n p := by
                rw [hoff]
                apply add_le_add
                · calc
                    ∑ j ∈ bulkJ n, |realMoment Q n j j - q| ≤ ∑ _j ∈ bulkJ n, D := by
                      gcongr with j hj
                      exact (herr j hj j hj).trans (pairErr_le_uniform Q n (j, j))
                    _ = (bulkJ n).card * D := by rw [Finset.sum_const, nsmul_eq_mul]
                · apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  gcongr with p hp
                  exact herr p.1 (MonomialCore.mem_bulkPairs_fst hp)
                    p.2 (PhaseBounds.mem_bulkPairs_snd hp)
    have hJ := MonomialCore.card_bulkJ_le n hL1
    have hmain :
        ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
            ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * realMoment Q n j k
          ≤ |q| * (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) ^ 2
            + (bulkJ n).card * D + 2 * ∑ p ∈ bulkPairs n, pairErr Q n p := by
      have hdecomp :
          ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
              ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * realMoment Q n j k =
            q * (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) ^ 2 +
              ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
                ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * (realMoment Q n j k - q) := by
        rw [sq, Finset.sum_mul_sum]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hdecomp]
      have herrsum :
          ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
              ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * (realMoment Q n j k - q)
              ≤ (bulkJ n).card * D + 2 * ∑ p ∈ bulkPairs n, pairErr Q n p := by
        calc
          _ ≤ ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
                |realMoment Q n j k - q| := by
                  gcongr with j hj k hk
                  calc
                    ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * (realMoment Q n j k - q)
                        ≤ |(((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) *
                          (realMoment Q n j k - q))| := le_abs_self _
                    _ = |realMoment Q n j k - q| := by simp [abs_mul, abs_pow]
          _ ≤ _ := hsum
      calc
        q * (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) ^ 2 +
              ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
                ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * (realMoment Q n j k - q)
            ≤ |q| * (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) ^ 2 +
                ((bulkJ n).card * D + 2 * ∑ p ∈ bulkPairs n, pairErr Q n p) :=
              add_le_add (mul_le_mul_of_nonneg_right (le_abs_self q) (sq_nonneg _)) herrsum
        _ = _ := by ring
    calc
      (1 / Lnorm n) ^ 2 * ∑ j ∈ bulkJ n, ∑ k ∈ bulkJ n,
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * realMoment Q n j k
        ≤ (1 / Lnorm n) ^ 2 *
          (|q| * (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) ^ 2 +
            (A * Lnorm n) * D + 2 * ∑ p ∈ bulkPairs n, pairErr Q n p) := by
              gcongr
              exact hmain.trans (by gcongr)
      _ = |q| * (|∑ j ∈ bulkJ n, (-1 : ℝ) ^ j| / Lnorm n) ^ 2
          + D * A * (1 / Lnorm n)
          + 2 * ((1 / Lnorm n) ^ 2 * ∑ p ∈ bulkPairs n, pairErr Q n p) := by
            rw [show (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) ^ 2 =
              |∑ j ∈ bulkJ n, (-1 : ℝ) ^ j| ^ 2 by simp [sq]]
            field_simp [ne_of_gt hL] <;> ring

theorem poly_centered_avg_L2_tendsto_zero (R M K : ℕ)
    (P : WindowSymbol (R + M) K) :
    Tendsto (fun n : ℕ => eLpNorm
        (varianceCenteredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)) 2
        (volume.restrict (Ioo (0 : ℝ) 1))) atTop (𝓝 0) := by
  exact target_of_raw_second_moment P (raw_second_moment_tendsto_zero P)

end

end Kwon1002.Prop64Variance

#print axioms Kwon1002.Prop64Variance.poly_centered_avg_L2_tendsto_zero

open Lean Elab Command in
run_cmd do
  let axioms ← collectAxioms ``Kwon1002.Prop64Variance.poly_centered_avg_L2_tendsto_zero
  if axioms.contains ``sorryAx then
    throwError "unexpected sorryAx dependency in poly_centered_avg_L2_tendsto_zero"
