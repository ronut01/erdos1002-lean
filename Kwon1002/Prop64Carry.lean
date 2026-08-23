import Kwon1002.Prop64

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Kwon1002.Prop64Carry

noncomputable section

local instance carryPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-!
# The `D = 9` carry truncation used in Proposition 6.4

This is the carry step of manuscript v9, lines 1393--1403.  The argument is
specialized throughout to the proved absolute carry bound `D = 9`; it does
not use, or assert, the over-general arbitrary-`D` skeleton statement.

The only analytic input is `NoResetIndicatorTransfer9 R`, the Lemma 6.3
specialization for the radius-`R` no-reset indicator.  Everything after that
input is deterministic coalescence and `L²` bookkeeping.
-/

def actualResetAt9 (α : ℝ) (n k : ℕ) : Prop :=
  ((gaussIter α k, 0), (theta α n (k - 1), theta α n k)) ∈ resetSet 9

def actualNoReset9 (R : ℕ) (α : ℝ) (n j : ℕ) : Prop :=
  ∀ t < R, ¬ actualResetAt9 α n (j - R + t)

def windowResetAt9 {R : ℕ} (w : WindowSpace R) (t : ℕ) : Prop :=
  (((wX w (-(R : ℤ) + (t : ℤ)), 0),
      (wTh w (-(R : ℤ) + (t : ℤ) - 1),
       wTh w (-(R : ℤ) + (t : ℤ)))) : NatExtTorus) ∈ resetSet 9

def windowNoResetSet9 (R : ℕ) : Set (WindowSpace R) :=
  {w | ∀ t < R, ¬ windowResetAt9 w t}

def noResetIndicator9 (R : ℕ) (w : WindowSpace R) : ℂ :=
  (windowNoResetSet9 R).indicator (fun _ ↦ (1 : ℂ)) w

lemma actual_windowNoResetSet9_iff (R n j : ℕ) (hj : R + 1 ≤ j) (α : ℝ) :
    actualWindow R α n j ∈ windowNoResetSet9 R ↔ actualNoReset9 R α n j := by
  constructor
  · intro h t ht hreset
    apply h t ht
    unfold windowResetAt9
    rw [wX_actualWindow R α n j (by omega) (t := -(R : ℤ) + (t : ℤ))
        (by omega) (by omega),
      wTh_actualWindow R α n j hj (t := -(R : ℤ) + (t : ℤ) - 1)
        (by omega) (by omega),
      wTh_actualWindow R α n j hj (t := -(R : ℤ) + (t : ℤ))
        (by omega) (by omega)]
    have hk : ((j : ℤ) + (-(R : ℤ) + (t : ℤ))).toNat = j - R + t := by omega
    have hkprev : ((j : ℤ) + (-(R : ℤ) + (t : ℤ) - 1)).toNat =
        j - R + t - 1 := by omega
    rw [hk, hkprev]
    exact hreset
  · intro h t ht hreset
    apply h t ht
    unfold actualResetAt9 at *
    unfold windowResetAt9 at hreset
    rw [wX_actualWindow R α n j (by omega) (t := -(R : ℤ) + (t : ℤ))
        (by omega) (by omega),
      wTh_actualWindow R α n j hj (t := -(R : ℤ) + (t : ℤ) - 1)
        (by omega) (by omega),
      wTh_actualWindow R α n j hj (t := -(R : ℤ) + (t : ℤ))
        (by omega) (by omega)] at hreset
    have hk : ((j : ℤ) + (-(R : ℤ) + (t : ℤ))).toNat = j - R + t := by omega
    have hkprev : ((j : ℤ) + (-(R : ℤ) + (t : ℤ) - 1)).toNat =
        j - R + t - 1 := by omega
    rw [hk, hkprev] at hreset
    exact hreset

lemma measurableSet_windowNoResetSet9 (R : ℕ) :
    MeasurableSet (windowNoResetSet9 R) := by
  rw [show windowNoResetSet9 R = ⋂ t : ℕ, ⋂ (_ : t < R),
      (fun w : WindowSpace R =>
        (((wX w (-(R : ℤ) + (t : ℤ)), 0),
          (wTh w (-(R : ℤ) + (t : ℤ) - 1),
           wTh w (-(R : ℤ) + (t : ℤ)))) : NatExtTorus)) ⁻¹' (resetSet 9)ᶜ by
    ext w
    simp [windowNoResetSet9, windowResetAt9]]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
    (Measurable.prodMk
      ((measurable_wX R (-(R : ℤ) + (t : ℤ))).prodMk measurable_const)
      ((measurable_wTh R (-(R : ℤ) + (t : ℤ) - 1)).prodMk
        (measurable_wTh R (-(R : ℤ) + (t : ℤ)))))
      (CarryGraph.measurableSet_resetSet 9).compl

lemma measurable_noResetIndicator9 (R : ℕ) : Measurable (noResetIndicator9 R) :=
  measurable_const.indicator (measurableSet_windowNoResetSet9 R)

lemma integral_noResetIndicator9_actual (R n j : ℕ) :
    ∫ w, noResetIndicator9 R w ∂(actualWindowLaw R n j) =
      (((volume.restrict (Ioo (0 : ℝ) 1)).real
        ((fun α => actualWindow R α n j) ⁻¹' windowNoResetSet9 R) : ℝ) : ℂ) := by
  rw [actualWindowLaw,
    integral_map (measurable_actualWindow R n j).aemeasurable
      (measurable_noResetIndicator9 R).aestronglyMeasurable]
  have hfun : (fun α => noResetIndicator9 R (actualWindow R α n j)) =
      ((fun α => actualWindow R α n j) ⁻¹' windowNoResetSet9 R).indicator
        (fun _ => (1 : ℂ)) := by
    funext α
    simp only [noResetIndicator9, Set.indicator_apply, Set.mem_preimage]
  rw [hfun, integral_indicator_const (1 : ℂ)
    ((measurable_actualWindow R n j) (measurableSet_windowNoResetSet9 R))]
  simp

lemma stationary_windowNoResetSet9_iff {R : ℕ} {z : NatExtTorus}
    (hz : z ∈ CarryGraph.GoodT) :
    stationaryWindow R z ∈ windowNoResetSet9 R ↔
      hatSinv^[R] z ∈ noResetSet 9 R := by
  have hstate : ∀ t < R,
      hatS^[t] (hatSinv^[R] z) = hatSzpow (-(R : ℤ) + (t : ℤ)) z := by
    intro t ht
    rw [CarryGraph.hatS_iterate_hatSinv_iterate hz t R (by omega),
      hatSzpow, if_neg (by omega)]
    congr 2
    omega
  constructor
  · intro h t ht hreset
    apply h t ht
    unfold windowResetAt9
    rw [wX_stationaryWindow R z (t := -(R : ℤ) + (t : ℤ)) (by omega) (by omega),
      wTh_stationaryWindow R z (t := -(R : ℤ) + (t : ℤ) - 1)
        (by omega) (by omega),
      wTh_stationaryWindow R z (t := -(R : ℤ) + (t : ℤ)) (by omega) (by omega),
      ← StationaryIdentity31.hatSzpow_fst_torus hz (-(R : ℤ) + (t : ℤ)),
      ← hstate t ht]
    exact hreset
  · intro h t ht hreset
    apply h t ht
    rw [hstate t ht]
    unfold windowResetAt9 at hreset
    rw [wX_stationaryWindow R z (t := -(R : ℤ) + (t : ℤ)) (by omega) (by omega),
      wTh_stationaryWindow R z (t := -(R : ℤ) + (t : ℤ) - 1)
        (by omega) (by omega),
      wTh_stationaryWindow R z (t := -(R : ℤ) + (t : ℤ)) (by omega) (by omega),
      ← StationaryIdentity31.hatSzpow_fst_torus hz (-(R : ℤ) + (t : ℤ))] at hreset
    exact hreset

lemma windowLaw_windowNoResetSet9 (R : ℕ) :
    windowLaw R (windowNoResetSet9 R) = hatMu0 (noResetSet 9 R) := by
  rw [windowLaw, Measure.map_apply (measurable_stationaryWindow R)
    (measurableSet_windowNoResetSet9 R)]
  calc
    hatMu0 (stationaryWindow R ⁻¹' windowNoResetSet9 R)
        = hatMu0 ((hatSinv^[R]) ⁻¹' noResetSet 9 R) := by
            apply measure_congr
            filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz
            exact propext (stationary_windowNoResetSet9_iff hz)
    _ = hatMu0 (noResetSet 9 R) :=
      (hatSinv_measurePreserving.iterate R).measure_preimage
        (CarryGraph.measurableSet_noResetSet 9 R).nullMeasurableSet

lemma integral_noResetIndicator9_stationary (R : ℕ) :
    ∫ w, noResetIndicator9 R w ∂(windowLaw R) = (noResetProb 9 R : ℂ) := by
  have hi := integral_indicator_const (μ := windowLaw R) (1 : ℂ)
    (measurableSet_windowNoResetSet9 R)
  rw [show (∫ w, noResetIndicator9 R w ∂(windowLaw R)) =
      (((windowLaw R).real (windowNoResetSet9 R) : ℝ) : ℂ) by
        simpa [noResetIndicator9] using hi]
  change (((windowLaw R (windowNoResetSet9 R)).toReal : ℝ) : ℂ) = _
  rw [windowLaw_windowNoResetSet9]
  rfl

/-- The exact finite-boundary specialization of Lemma 6.3 needed here. -/
def NoResetIndicatorTransfer9 (R : ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
    ‖(∫ w, noResetIndicator9 R w ∂(actualWindowLaw R n j)) -
        ∫ w, noResetIndicator9 R w ∂(windowLaw R)‖ < ε

lemma actual_noReset_measure_eq_integral (R n j : ℕ) (hj : R + 1 ≤ j) :
    (((volume.restrict (Ioo (0 : ℝ) 1)).real
      {α | actualNoReset9 R α n j} : ℝ) : ℂ) =
      ∫ w, noResetIndicator9 R w ∂(actualWindowLaw R n j) := by
  rw [integral_noResetIndicator9_actual]
  congr 2
  ext α
  exact (actual_windowNoResetSet9_iff R n j hj α).symm

private lemma eventually_bulk_radius (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n, R + 1 ≤ j := by
  filter_upwards [P42Cases.tendsto_Hscale.eventually_ge_atTop ((R + 1 : ℝ) / 200)] with n hn
  intro j hj
  rw [bulkJ, Finset.mem_filter] at hj
  have hlo := hj.2.1
  have hcast : (R + 1 : ℝ) ≤ 200 * Hscale n := by
    nlinarith
  exact_mod_cast (hcast.trans hlo)

/-- A reset in `[j-R,j)` coalesces the actual and zero-started carries.
This is the deterministic part of display (57), specifically at `D=9`. -/
theorem mismatch_implies_actualNoReset9 {R n j : ℕ} {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (hj : R + 1 ≤ j)
    (hne : actualCarry α n j ≠ carryTrunc α n R j) :
    actualNoReset9 R α n j := by
  intro t ht hreset
  set i := j - R with hi
  have hiR : i + R = j := by simp only [i]; omega
  have hi1 : 1 ≤ i := by simp only [i]; omega
  have hactual_bounds : ∀ k, 0 ≤ actualCarry α n k ∧ actualCarry α n k ≤ 9 := by
    intro k
    have hE := heightError_mem_Icc α hα hirr n k
    constructor
    · exact Int.floor_nonneg.mpr hE.1
    · have h9 : heightError α n k ≤ 9 :=
        le_trans hE.2 (le_trans Estar_le_nine_halves (by norm_num))
      have hf : ((⌊heightError α n k⌋ : ℤ) : ℝ) ≤ 9 := le_trans (Int.floor_le _) h9
      exact_mod_cast hf
  have hreset' :
      ((gaussIter α (i + t), 0),
        (thetaPred α n (i + t), theta α n (i + t))) ∈ resetSet 9 := by
    unfold actualResetAt9 at hreset
    have hpred : thetaPred α n (i + t) = theta α n (i + t - 1) := by
      cases hsum : i + t with
      | zero => omega
      | succ k => rfl
    simpa [hi, hpred] using hreset
  have hactual0 : actualCarry α n (i + (t + 1)) = 0 := by
    rw [show i + (t + 1) = (i + t) + 1 by omega,
      actualCarry_succ α n (i + t) hα hirr]
    exact carryMap_eq_zero_of_mem_resetSet 9
      ((gaussIter α (i + t), 0), (thetaPred α n (i + t), theta α n (i + t)))
      hreset' (gaussIter_mem_Ioo hα hirr (i + t)).1.le
      (Prop64.thetaPred_mem_Ico α n (i + t)).1
      (Prop64.thetaPred_mem_Ico α n (i + t)).2
      (actualCarry α n (i + t)) (hactual_bounds (i + t)).1
      (hactual_bounds (i + t)).2
  have htrunc0 : carryFrom α n i (t + 1) = 0 := by
    rw [carryFrom]
    exact carryMap_eq_zero_of_mem_resetSet 9
      ((gaussIter α (i + t), 0), (thetaPred α n (i + t), theta α n (i + t)))
      hreset' (gaussIter_mem_Ioo hα hirr (i + t)).1.le
      (Prop64.thetaPred_mem_Ico α n (i + t)).1
      (Prop64.thetaPred_mem_Ico α n (i + t)).2
      (carryFrom α n i t) (Prop64.carryFrom_bounds hα hirr n i t).1
      (Prop64.carryFrom_bounds hα hirr n i t).2
  have heq : ∀ k, t + 1 ≤ k → k ≤ R →
      actualCarry α n (i + k) = carryFrom α n i k := by
    intro k htk hkR
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hbase : k = t
        · subst k
          rw [hactual0, htrunc0]
        · have htk' : t + 1 ≤ k := by omega
          have hkR' : k ≤ R := by omega
          rw [show i + (k + 1) = (i + k) + 1 by omega,
            actualCarry_succ α n (i + k) hα hirr, carryFrom, ih htk' hkR']
  apply hne
  rw [carryTrunc, ← hiR, show i + R - R = i by omega]
  exact heq R (by omega) le_rfl

/-- Display (57), conditional only on the one no-reset indicator transfer. -/
theorem carry_coupling9_of_transfer (R : ℕ) (htransfer : NoResetIndicatorTransfer9 R) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      (volume.restrict (Ioo (0 : ℝ) 1)).real
          {α | actualCarry α n j ≠ carryTrunc α n R j}
        ≤ noResetProb 9 R + ε := by
  intro ε hε
  filter_upwards [htransfer ε hε, eventually_bulk_radius R] with n hn hnroom
  intro j hj
  have hsub : (volume.restrict (Ioo (0 : ℝ) 1)).real
      {α | actualCarry α n j ≠ carryTrunc α n R j}
      ≤ (volume.restrict (Ioo (0 : ℝ) 1)).real
          {α | actualNoReset9 R α n j} := by
    have hmono : volume.restrict (Ioo (0 : ℝ) 1)
        {α | actualCarry α n j ≠ carryTrunc α n R j}
        ≤ volume.restrict (Ioo (0 : ℝ) 1) {α | actualNoReset9 R α n j} := by
      apply measure_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
        with α hα hirr hne
      exact mismatch_implies_actualNoReset9 hα hirr (hnroom j hj) hne
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmono
  apply hsub.trans
  have hnorm := hn j hj
  rw [← actual_noReset_measure_eq_integral R n j (hnroom j hj),
    integral_noResetIndicator9_stationary] at hnorm
  have hcast :
      (((volume.restrict (Ioo (0 : ℝ) 1)).real
          {α | actualNoReset9 R α n j} : ℝ) : ℂ) -
        ((noResetProb 9 R : ℝ) : ℂ) =
      ((((volume.restrict (Ioo (0 : ℝ) 1)).real
          {α | actualNoReset9 R α n j} - noResetProb 9 R : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hnorm
  linarith [le_abs_self
    ((volume.restrict (Ioo (0 : ℝ) 1)).real {α | actualNoReset9 R α n j} -
      noResetProb 9 R)]

private lemma Bremainder_eq_BremainderTrunc_of_carry_eq {α : ℝ} {n R j : ℕ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (hcarry : actualCarry α n j = carryTrunc α n R j) :
    Bremainder α n j = BremainderTrunc α n R j := by
  rw [Bremainder, BremainderTrunc, carry_eq_carryU α n j hα hirr, hcarry]

private lemma abs_Bremainder_sub_BremainderTrunc_le_nine {α : ℝ} {n R j : ℕ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    |Bremainder α n j - BremainderTrunc α n R j| ≤ 9 := by
  have hB : |Bremainder α n j| ≤ Czero := by
    simpa [Bremainder] using principal_term α hα hirr n j
  have hBR := Prop64.abs_BremainderTrunc_le hα hirr n R j
  have hC : Czero ≤ 23 / 8 := by
    rw [Czero]
    nlinarith [Estar_le_nine_halves]
  calc
    |Bremainder α n j - BremainderTrunc α n R j|
        ≤ |Bremainder α n j| + |BremainderTrunc α n R j| := abs_sub _ _
    _ ≤ Czero + 45 / 8 := add_le_add hB hBR
    _ ≤ 9 := by linarith

private lemma eLpNorm_carry_difference_le_of_measure_le {ε : ℝ} (hε : 0 < ε)
    {R n j : ℕ}
    (hmeasure : (volume.restrict (Ioo (0 : ℝ) 1)).real
      {α | actualCarry α n j ≠ carryTrunc α n R j} ≤ (ε / 9) ^ 2) :
    eLpNorm (fun α => Bremainder α n j - BremainderTrunc α n R j) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let bad : Set ℝ := {α | actualCarry α n j ≠ carryTrunc α n R j}
  have hmono : eLpNorm (fun α => Bremainder α n j - BremainderTrunc α n R j) 2 μ
      ≤ eLpNorm (bad.indicator (fun _ : ℝ => (9 : ℝ))) 2 μ := by
    apply eLpNorm_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
      with α hα hirr
    by_cases hbad : α ∈ bad
    · rw [Set.indicator_of_mem hbad]
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)] using
        (abs_Bremainder_sub_BremainderTrunc_le_nine hα hirr)
    · have heq : actualCarry α n j = carryTrunc α n R j := by
        simpa [bad] using hbad
      rw [Set.indicator_of_notMem hbad,
        Bremainder_eq_BremainderTrunc_of_carry_eq hα hirr heq, sub_self]
  have hindicator : eLpNorm (bad.indicator (fun _ : ℝ => (9 : ℝ))) 2 μ
      ≤ ENNReal.ofReal 9 * μ bad ^ (1 / (2 : ℝ≥0∞).toReal) := by
    have h := eLpNorm_indicator_const_le (μ := μ) (s := bad) (c := (9 : ℝ))
      (p := (2 : ℝ≥0∞))
    simpa only [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)] using h
  have hμ : μ bad ≤ ENNReal.ofReal ((ε / 9) ^ 2) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ bad)]
    exact ENNReal.ofReal_le_ofReal (by simpa [μ, bad] using hmeasure)
  calc
    eLpNorm (fun α => Bremainder α n j - BremainderTrunc α n R j) 2 μ
        ≤ eLpNorm (bad.indicator (fun _ : ℝ => (9 : ℝ))) 2 μ := hmono
    _ ≤ ENNReal.ofReal 9 * μ bad ^ (1 / (2 : ℝ≥0∞).toReal) := hindicator
    _ ≤ ENNReal.ofReal 9 * (ENNReal.ofReal ((ε / 9) ^ 2)) ^
          (1 / (2 : ℝ≥0∞).toReal) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg (ε / 9)) (by norm_num)]
      rw [show (1 / (2 : ℝ)) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (x := ε / 9) (n := 2) (by positivity) (by norm_num)]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
      congr 1
      ring

/-- The carry-truncation `L²` conclusion consumed by Proposition 6.4.

Its single upstream hypothesis says that Lemma 6.3 transfers the finite
no-reset indicator for every radius. -/
theorem carry_truncation_L2_small_of_noResetIndicatorTransfer9
    (htransfer : ∀ R, NoResetIndicatorTransfer9 R) :
    ∀ ε > 0, ∃ R : ℕ, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      eLpNorm (fun α => Bremainder α n j - BremainderTrunc α n R j) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let q : ℝ := (ε / 9) ^ 2
  have hq : 0 < q := by simp only [q]; positivity
  have hp : ∀ᶠ R : ℕ in atTop, noResetProb 9 R < q / 2 :=
    (tendsto_order.1 (CarryGraph.noResetProb_tendsto_zero 9)).2 _ (by linarith)
  obtain ⟨R, hR⟩ := hp.exists
  refine ⟨R, ?_⟩
  filter_upwards [carry_coupling9_of_transfer R (htransfer R) (q / 2) (by linarith)]
    with n hn
  intro j hj
  apply eLpNorm_carry_difference_le_of_measure_le hε
  have hm := hn j hj
  change (volume.restrict (Ioo (0 : ℝ) 1)).real
      {α | actualCarry α n j ≠ carryTrunc α n R j} ≤ q
  linarith

assert_no_sorry actual_windowNoResetSet9_iff
assert_no_sorry stationary_windowNoResetSet9_iff
assert_no_sorry carry_coupling9_of_transfer
assert_no_sorry carry_truncation_L2_small_of_noResetIndicatorTransfer9

end

end Kwon1002.Prop64Carry
