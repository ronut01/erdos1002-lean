import Kwon1002.Prop64

/-!
# The display-(56) squared-error specialization

This file isolates the last implication in the manuscript's route from
display (55) to the polynomial approximation used in Proposition 6.4.
The sole analytic input is convergence, uniformly over the bulk, of the
one squared-error observable occurring in display (56).  The remaining
argument is the `L²` bookkeeping from displays (55)--(56).

Neither the placeholder `Lemma63` transfer theorem nor the placeholder
`Prop64.actual_L2_transfer` is used.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002.Prop64SquaredError

noncomputable section

/-- The exact special-function input from Lemma 6.3 needed in display (56). -/
def SquaredErrorBulkTransfer (R M K : ℕ) (P : WindowSymbol (R + M) K)
    (δRM : ℝ) : Prop :=
  ∀ η > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
    |(∫ α in Ioo (0 : ℝ) 1,
        ‖((BremainderTrunc α n R j : ℂ)) - P.at α n j‖ ^ 2) - δRM ^ 2| < η

/-- A provider for the sole analytic input.  Its hypotheses identify `δRM`
with the stationary `L²` error from display (55). -/
def SquaredErrorBulkTransferProvider : Prop :=
  ∀ (R M K : ℕ) (P : WindowSymbol (R + M) K) (δRM : ℝ),
    0 ≤ δRM →
    eLpNorm
        (fun w : WindowSpace (R + M) =>
          ((BwindowRep R (windowProj (Nat.le_add_right R M) w) : ℂ) -
            P.evalWindow w))
        2 (windowLaw (R + M)) = ENNReal.ofReal δRM →
    SquaredErrorBulkTransfer R M K P δRM

/-- Display (56), exposed without using the canonical placeholder theorem. -/
theorem actual_L2_transfer_of_squaredErrorBulkTransfer
    (R M K : ℕ) (P : WindowSymbol (R + M) K) (δRM : ℝ)
    (htransfer : SquaredErrorBulkTransfer R M K P δRM) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      |(∫ α in Ioo (0 : ℝ) 1,
          ‖((BremainderTrunc α n R j : ℂ)) - P.at α n j‖ ^ 2) - δRM ^ 2| < ε :=
  htransfer

private theorem eventually_bulk_radius (R' : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n, R' + 1 ≤ j := by
  filter_upwards [P42Cases.tendsto_Hscale.eventually_ge_atTop ((R' + 1 : ℝ) / 200)]
    with n hn
  intro j hj
  rw [bulkJ, Finset.mem_filter] at hj
  have hlo := hj.2.1
  have hcast : (R' + 1 : ℝ) ≤ 200 * Hscale n := by
    nlinarith
  exact_mod_cast (hcast.trans hlo)

private lemma eLpNorm_two_eq {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, (f x) ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 2
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp [sq]

private lemma eLpNorm_le_of_integral_sq_lt {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) {ε : ℝ} (hε : 0 < ε)
    (hint : (∫ x, (f x) ^ 2 ∂μ) < ε ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal ε := by
  rw [eLpNorm_two_eq hf]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.sqrt_le_iff]
  constructor
  · exact hε.le
  · exact hint.le

/-- Displays (55)--(56): the squared-error bulk transfer converts the
stationary monomial approximation into the uniform actual `L²` bound needed
by Proposition 6.4. -/
theorem trunc_poly_L2_small_of_squaredErrorBulkTransfer
    (htransfer : SquaredErrorBulkTransferProvider) (R : ℕ) :
    ∀ ε > 0, ∃ M K : ℕ, ∃ P : WindowSymbol (R + M) K,
      (∀ w : WindowSpace (R + M), (P.evalWindow w).im = 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        eLpNorm (fun α => BremainderTrunc α n R j - (P.at α n j).re) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨M, K, P, hPreal, hP⟩ :=
    Kwon1002.Prop64.display_55_monomial_approximation R (ε / 2) (by linarith)
  let F : WindowSpace (R + M) → ℂ := fun w =>
    ((BwindowRep R (windowProj (Nat.le_add_right R M) w) : ℂ) - P.evalWindow w)
  let δRM : ℝ := (eLpNorm F 2 (windowLaw (R + M))).toReal
  have hfinite : eLpNorm F 2 (windowLaw (R + M)) ≠ ∞ := by
    exact ne_top_of_lt (hP.trans_le (le_refl _))
  have hδ : eLpNorm F 2 (windowLaw (R + M)) = ENNReal.ofReal δRM := by
    dsimp only [δRM]
    exact (ENNReal.ofReal_toReal hfinite).symm
  have hδnonneg : 0 ≤ δRM := ENNReal.toReal_nonneg
  have hδlt : δRM < ε / 2 := by
    have := (ENNReal.toReal_lt_toReal hfinite (by simp)).2 hP
    simpa [δRM, ENNReal.toReal_ofReal (by linarith : 0 ≤ ε / 2)] using this
  have hgap : 0 < ε ^ 2 - δRM ^ 2 := by
    nlinarith [sq_nonneg (ε / 2 - δRM), hδnonneg]
  have hbulk := htransfer R M K P δRM hδnonneg hδ (ε ^ 2 - δRM ^ 2) hgap
  refine ⟨M, K, P, hPreal, ?_⟩
  filter_upwards [hbulk, eventually_bulk_radius (R + M)] with n hn hradius
  intro j hj
  have hjradius : R + M + 1 ≤ j := hradius j hj
  have hsq : ∀ α : ℝ,
      (BremainderTrunc α n R j - (P.at α n j).re) ^ 2 =
        ‖((BremainderTrunc α n R j : ℂ)) - P.at α n j‖ ^ 2 := by
    intro α
    have him : (P.at α n j).im = 0 := by
      rw [← WindowSymbol.evalWindow_actualWindow P α n j hjradius]
      exact hPreal _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      zero_sub, him, neg_zero, mul_zero, add_zero]
    ring
  have hintcomplex :
      (∫ α in Ioo (0 : ℝ) 1,
        ‖((BremainderTrunc α n R j : ℂ)) - P.at α n j‖ ^ 2) < ε ^ 2 := by
    have habs := (abs_lt.mp (hn j hj)).2
    linarith
  have hintreal :
      (∫ α in Ioo (0 : ℝ) 1,
        (BremainderTrunc α n R j - (P.at α n j).re) ^ 2) < ε ^ 2 := by
    simpa only [hsq] using hintcomplex
  exact eLpNorm_le_of_integral_sq_lt
    ((Kwon1002.Prop64.memLp_BremainderTrunc R n j).sub
      (Kwon1002.Prop64.memLp_symbolAt P n j)) hε hintreal

assert_no_sorry actual_L2_transfer_of_squaredErrorBulkTransfer
assert_no_sorry trunc_poly_L2_small_of_squaredErrorBulkTransfer

end

end Kwon1002.Prop64SquaredError
