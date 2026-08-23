import Kwon1002.P42Super
import Mathlib.Util.AssertNoSorry

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

noncomputable section

/-!
Proof of the finite cylinder--character one-block step in manuscript
v9, Lemma 6.3.  The statement is uniform over the deterministic bulk and is
specialized to the already-defined `WindowSymbol R K` class.
-/

set_option maxHeartbeats 1600000 in
lemma nonzero_mono_bound (R : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ bulkJ n, ∀ w : Fin (2 * R) → ℕ, ∀ r s : ℤ, (r, s) ≠ (0, 0) →
        ‖∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w r s α n j‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n)) := by
  classical
  obtain ⟨C20, c20, hC20, hc20, h20⟩ := LargeDeviation.display20_of_pos 1 one_pos
  obtain ⟨C3, c3, hc3, hAC⟩ := Kwon1002.shrinking_anti_concentration
  set C3' : ℝ := max C3 0
  have hC3'0 : (0 : ℝ) ≤ C3' := le_max_right _ _
  have hC3C3' : C3 ≤ C3' := le_max_left _ _
  set c : ℝ := min 1 (min c20 (200 * c3))
  have hc0 : 0 < c := lt_min one_pos (lt_min hc20 (by linarith))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcc20 : c ≤ c20 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcc3 : c ≤ 200 * c3 := le_trans (min_le_right _ _) (min_le_right _ _)
  set C : ℝ := max 1 (max (3 * C20) (2 * C3' + 28))
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hC0 : 0 < C := by linarith
  have hCA : 3 * C20 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCB : 2 * C3' + 28 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, c, hC0, hc0, ?_⟩
  filter_upwards [h20,
    (P42Cases.tendsto_Hscale.const_mul_atTop
      (by norm_num : (0 : ℝ) < 60)).eventually_ge_atTop ((R : ℝ) + 1),
    P42Cases.tendsto_Hscale.eventually_ge_atTop (max 1 ((R : ℝ) / 200)),
    eventually_ge_atTop 1] with n h20n hH60 hHM hn1
  intro j hjb w r s hrs
  set H : ℝ := Hscale n
  have hH1 : (1 : ℝ) ≤ H := le_trans (le_max_left _ _) hHM
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hHR : (R : ℝ) / 200 ≤ H := le_trans (le_max_right _ _) hHM
  have hjlo : 200 * H ≤ (j : ℝ) := ((Finset.mem_filter.1 hjb).2).1
  have hRj : R ≤ j := by
    have : (R : ℝ) ≤ (j : ℝ) := by linarith
    exact_mod_cast this
  have hj1 : 1 ≤ j := by
    have : (1 : ℝ) ≤ (j : ℝ) := by linarith
    exact_mod_cast this
  have hη0 : (0 : ℝ) < Real.exp (-H) := Real.exp_pos _
  have hη2 : Real.exp (-H) < 1 / 2 := by
    have h1 : Real.exp (-H) ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.2 (by linarith)
    have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp' : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
    have hid : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hacn := hAC r s hrs j hj1 (Real.exp (-H)) hη0 hη2
  have hdt : j + R < (Prop41.kMinus n j).toNat :=
    PhaseBounds.prefix_lt_kMinus_toNat_of_bulk hjb hH60
  have hmain := P42Super.oscillatory_single_bound hn1 hjb hj1 hRj w hdt
    (C₀ := C20) (c₀ := c20) h20n
    (Cac := C3 * (Real.exp (-H) + Real.exp (-c3 * (j : ℝ)))) hacn
  refine le_trans hmain ?_
  have hLsq : (0 : ℝ) ≤ Real.sqrt (Lnorm n) := Real.sqrt_nonneg _
  have e1 : Real.exp (-c20 * Real.sqrt (Lnorm n))
      ≤ Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-H) ≤ Real.exp (-c * H) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-c3 * (j : ℝ)) ≤ Real.exp (-c * H) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hp1 : (0 : ℝ) < Real.exp (-H) := Real.exp_pos _
  have hp2 : (0 : ℝ) < Real.exp (-c3 * (j : ℝ)) := Real.exp_pos _
  have hp3 : (0 : ℝ) < Real.exp (-c * H) := Real.exp_pos _
  have hp4 : (0 : ℝ) < Real.exp (-c20 * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have hp5 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have hC3b : C3 * (Real.exp (-H) + Real.exp (-c3 * (j : ℝ)))
      ≤ 2 * C3' * Real.exp (-c * H) := by
    have ha := mul_le_mul_of_nonneg_right hC3C3' (by linarith :
      0 ≤ Real.exp (-H) + Real.exp (-c3 * (j : ℝ)))
    have hb := mul_le_mul_of_nonneg_left (by linarith [e2, e3] :
      Real.exp (-H) + Real.exp (-c3 * (j : ℝ)) ≤ 2 * Real.exp (-c * H)) hC3'0
    linarith
  have hAterm : 3 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
      ≤ C * Real.exp (-c * Real.sqrt (Lnorm n)) := by
    have h1 : 3 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
        ≤ 3 * (C20 * Real.exp (-c * Real.sqrt (Lnorm n))) := by nlinarith
    nlinarith
  have hBterm : 2 * C3' * Real.exp (-c * H) + 28 * Real.exp (-H)
      ≤ C * Real.exp (-c * H) := by nlinarith
  nlinarith [hAterm, hBterm, hC3b]

lemma tendsto_nonzero_error {C c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => C *
      (Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n)))
      atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (Lnorm n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have h1 : Tendsto (fun n : ℕ => Real.exp (-c * Real.sqrt (Lnorm n))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hsqrt.const_mul_atTop_of_neg (by linarith))
  have h2 : Tendsto (fun n : ℕ => Real.exp (-c * Hscale n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (P42Cases.tendsto_Hscale.const_mul_atTop_of_neg (by linarith))
  simpa using (h1.add h2).const_mul C

lemma zero_mono_bound {n R j : ℕ} (hRj : R ≤ j) (w : Fin (2 * R) → ℕ) :
    ‖(∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w 0 0 α n j)
        - Prop42.monoStationary R w 0 0‖
      ≤ (527 / 540 : ℝ) ^ (j - R) * Real.log 2 * 2 := by
  have hact : (∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w 0 0 α n j)
      = ((∫ α in Ioo (0 : ℝ) 1,
          PhaseBounds.cylObs R w (gaussIter α (j - R)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro α _
    exact P42Super.monoAt_zeroMode_eq_cylObs hRj w α n
  have hstat : Prop42.monoStationary R w 0 0
      = ((∫ y, PhaseBounds.cylObs R w y ∂Erdos1002.gaussMeasure : ℝ) : ℂ) := by
    rw [P42Cases.monoStationary_zeroMode, PhaseBounds.natExt_marginal,
      ← PhaseBounds.integral_cylObs_gauss]
  have hleb := Prop41Final.lebesgue_sub_gauss_le
    (PhaseBounds.cylObs R w) (PhaseBounds.measurable_cylObs R w) 2 (by norm_num)
    (fun y _ => PhaseBounds.cylObs_bound R w y) (j - R)
  rw [hact, hstat, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hleb

/-- Uniform one-block convergence for every cylinder--character monomial of
fixed radius.  The quantification over `w,r,s` is stronger than needed for a
fixed symbol and makes the finite-sum assembly immediate. -/
theorem mono_oneblock (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n, ∀ w : Fin (2 * R) → ℕ, ∀ r s : ℤ,
      ‖(∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w r s α n j)
          - Prop42.monoStationary R w r s‖ < ε := by
  obtain ⟨C, c, hC, hc, hnonzero⟩ := nonzero_mono_bound R
  have herr := tendsto_nonzero_error (C := C) hc
  have herrSmall : ∀ᶠ n : ℕ in atTop,
      C * (Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n)) < ε :=
    Filter.Tendsto.eventually_lt_const hε herr
  have hpow : Tendsto (fun M : ℕ =>
      (527 / 540 : ℝ) ^ M * Real.log 2 * 2) atTop (𝓝 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 527 / 540) (by norm_num : (527 / 540 : ℝ) < 1)).const_mul
        (Real.log 2 * 2))
  have hpowSmall : ∀ᶠ M : ℕ in atTop,
      (527 / 540 : ℝ) ^ M * Real.log 2 * 2 < ε :=
    Filter.Tendsto.eventually_lt_const hε hpow
  obtain ⟨M, hM⟩ := hpowSmall.exists
  filter_upwards [hnonzero, herrSmall,
    P42Cases.tendsto_Hscale.eventually_ge_atTop (((R + M : ℕ) : ℝ) / 200)]
      with n hn herrn hHM
  intro j hj w r s
  have hjlo : 200 * Hscale n ≤ (j : ℝ) := ((Finset.mem_filter.1 hj).2).1
  have hRj : R ≤ j := by
    have : ((R : ℕ) : ℝ) ≤ (j : ℝ) := by
      have hRM : (((R + M : ℕ) : ℝ)) ≤ (j : ℝ) := by nlinarith
      exact le_trans (by exact_mod_cast Nat.le_add_right R M) hRM
    exact_mod_cast this
  by_cases hrs : (r, s) = (0, 0)
  · have hr : r = 0 := by simpa using congrArg Prod.fst hrs
    have hs : s = 0 := by simpa using congrArg Prod.snd hrs
    subst r; subst s
    have hRMj : R + M ≤ j := by
      have : (((R + M : ℕ) : ℝ)) ≤ (j : ℝ) := by nlinarith
      exact_mod_cast this
    refine lt_of_le_of_lt (zero_mono_bound hRj w) ?_
    have hpowle : (527 / 540 : ℝ) ^ (j - R) ≤ (527 / 540 : ℝ) ^ M :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hpowlog := mul_le_mul_of_nonneg_right hpowle hlog
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpowlog (by norm_num)) hM
  · rw [MonomialCore.monoStationary_eq_zero R w hrs, sub_zero]
    exact lt_of_le_of_lt (hn j hj w r s hrs) herrn

lemma integrableOn_monoAt (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) (n j : ℕ) :
    IntegrableOn (fun α => Prop42.monoAt R w r s α n j) (Ioo (0 : ℝ) 1) volume := by
  refine memLp_one_iff_integrable.mp (MemLp.of_bound
    (Prop42.measurable_monoAt R w r s n j).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun α => Prop42.norm_monoAt_le R w r s α n j))

/-- The common finite-cylinder/finite-character part of manuscript v9,
Lemma 6.3: a fixed `WindowSymbol` has its actual one-time mean converging to
its stationary mean, uniformly over `j ∈ J_n`. -/
theorem windowSymbol_oneblock {R K : ℕ} (U : WindowSymbol R K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n j) - U.stationaryIntegral‖ < ε := by
  classical
  let A : ℝ := ∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hη : 0 < ε / (A + 1) := div_pos hε (by linarith)
  filter_upwards [mono_oneblock R (ε / (A + 1)) hη] with n hn
  intro j hj
  have hat : (fun α => U.at α n j) = fun α =>
      ∑ t ∈ Prop42.symIdx U,
        U.coeff t.1 t.2.1 t.2.2 * Prop42.monoAt R t.1 t.2.1 t.2.2 α n j := by
    funext α
    exact Prop42.at_eq_sum U α n j
  rw [hat, Prop42.stationaryIntegral_eq_sum]
  rw [integral_finset_sum _ fun t _ =>
    (integrableOn_monoAt R t.1 t.2.1 t.2.2 n j).const_mul _]
  simp_rw [integral_const_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ t ∈ Prop42.symIdx U, (
        U.coeff t.1 t.2.1 t.2.2 * (∫ α in Ioo (0 : ℝ) 1,
          Prop42.monoAt R t.1 t.2.1 t.2.2 α n j)
          - U.coeff t.1 t.2.1 t.2.2 * Prop42.monoStationary R t.1 t.2.1 t.2.2)‖
        ≤ ∑ t ∈ Prop42.symIdx U,
          ‖U.coeff t.1 t.2.1 t.2.2‖ * (ε / (A + 1)) := by
            refine le_trans (norm_sum_le _ _) ?_
            refine Finset.sum_le_sum fun t ht => ?_
            rw [← mul_sub, norm_mul]
            exact mul_le_mul_of_nonneg_left (le_of_lt (hn j hj t.1 t.2.1 t.2.2)) (norm_nonneg _)
    _ = A * (ε / (A + 1)) := by
      dsimp [A]
      rw [Finset.sum_mul]
    _ < ε := by
      have hden : 0 < A + 1 := by linarith
      rw [mul_div]
      exact (div_lt_iff₀ hden).2 (by nlinarith [hA0, hε])

assert_no_sorry windowSymbol_oneblock

end
end Kwon1002
