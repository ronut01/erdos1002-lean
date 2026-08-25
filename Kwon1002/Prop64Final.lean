import Kwon1002.Prop64SpecialTransfers
import Kwon1002.Prop64Carry
import Kwon1002.Prop64SquaredError
import Mathlib.Util.AssertNoSorry

/-!
# Proposition 6.4, with all manuscript inputs discharged

This module reruns the final centered-Minkowski assembly of Proposition 6.4
using the proved `D = 9` carry coupling, the full-state squared-error transfer,
and the unconditional two-block variance estimate.  It does not use either of
the placeholder inputs in `Kwon1002.Prop64`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002.Prop64

noncomputable section

/-- The canonical carry-truncation input, placed after its proved transfer
provider to avoid the old import-direction placeholder. -/
theorem carry_truncation_L2_small :
    ∀ ε > 0, ∃ R : ℕ, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      eLpNorm (fun α => Bremainder α n j - BremainderTrunc α n R j) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε :=
  Prop64Carry.carry_truncation_L2_small_of_noResetIndicatorTransfer9
    Prop64SpecialTransfers.noResetIndicatorTransfer9

/-- The canonical display-(55)--(56) polynomial input, placed after its
proved squared-error transfer provider. -/
theorem trunc_poly_L2_small (R : ℕ) :
    ∀ ε > 0, ∃ M K : ℕ, ∃ P : WindowSymbol (R + M) K,
      (∀ w : WindowSpace (R + M), (P.evalWindow w).im = 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        eLpNorm (fun α => BremainderTrunc α n R j - (P.at α n j).re) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε :=
  Prop64SquaredError.trunc_poly_L2_small_of_squaredErrorBulkTransfer
    Prop64SpecialTransfers.squaredErrorBulkTransferProvider R

assert_no_sorry carry_truncation_L2_small
assert_no_sorry trunc_poly_L2_small

end

end Kwon1002.Prop64

namespace Kwon1002.Prop64Final

noncomputable section

open Prop64

theorem carry_truncation_L2_small_clean :
    ∀ ε > 0, ∃ R : ℕ, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      eLpNorm (fun α => Bremainder α n j - BremainderTrunc α n R j) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε :=
  Prop64.carry_truncation_L2_small

theorem trunc_poly_L2_small_clean (R : ℕ) :
    ∀ ε > 0, ∃ M K : ℕ, ∃ P : WindowSymbol (R + M) K,
      (∀ w : WindowSpace (R + M), (P.evalWindow w).im = 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        eLpNorm (fun α => BremainderTrunc α n R j - (P.at α n j).re) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε :=
  Prop64.trunc_poly_L2_small R

/-- The manuscript's three limits, in the order `n → ∞`, then `M → ∞`,
then `R → ∞`, with every input now machine-checked. -/
theorem remainderAvg_eLpNorm_small_clean :
    ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      eLpNorm (centeredAvg (Lnorm n) (bulkJ n) (fun j α => Bremainder α n j)) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal η := by
  intro η hη
  have hlp : 0 < 1 / lyapunov := one_div_pos.mpr lyapunov_pos
  obtain ⟨A, hApos, hA⟩ : ∃ A : ℝ, 0 < A ∧ (1 : ℝ) / lyapunov + 1 = A :=
    ⟨1 / lyapunov + 1, by linarith, rfl⟩
  set b : ℝ := η / (3 * (2 * A)) with hbdef
  have hbpos : 0 < b := by
    rw [hbdef]
    apply div_pos hη
    linarith
  obtain ⟨R, hR⟩ := carry_truncation_L2_small_clean b hbpos
  obtain ⟨M, K, P, _hPim, hP⟩ := trunc_poly_L2_small_clean R b hbpos
  have hvar : ∀ᶠ n : ℕ in atTop,
      eLpNorm (centeredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal (η / 3) :=
    ENNReal.tendsto_nhds_zero.mp
      (Prop64.poly_centered_avg_L2_tendsto_zero R M K P)
      (ENNReal.ofReal (η / 3)) (by simp [ENNReal.ofReal_pos]; linarith)
  filter_upwards [hR, hP, hvar, eventually_ge_atTop 3] with n h1 h2 h3 hn3
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  set L : ℝ := Lnorm n with hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (Prop64.one_le_Lnorm hn3)
  have hL1 : 1 ≤ L := Prop64.one_le_Lnorm hn3
  set s : Finset ℕ := bulkJ n with hs
  set ZB : ℕ → ℝ → ℝ := fun j α => Bremainder α n j with hZB
  set ZT : ℕ → ℝ → ℝ := fun j α => BremainderTrunc α n R j with hZT
  set ZP : ℕ → ℝ → ℝ := fun j α => (P.at α n j).re with hZP
  set D1 : ℕ → ℝ → ℝ := fun j α => ZB j α - ZT j α with hD1
  set D2 : ℕ → ℝ → ℝ := fun j α => ZT j α - ZP j α with hD2
  have hcard : (2 / L) * s.card * b ≤ η / 3 := by
    have hc := Prop64.card_bulkJ_le n
    rw [← hs, ← hL] at hc
    have hLinv : 1 / L ≤ 1 := by
      rw [div_le_one hLpos]
      exact hL1
    have hstep : (1 / L) * (s.card : ℝ) ≤ A := by
      have hmul : (1 / L) * (s.card : ℝ) ≤ (1 / L) * (L / lyapunov + 1) := by
        apply mul_le_mul_of_nonneg_left hc
        positivity
      have hexp : (1 / L) * (L / lyapunov + 1) = 1 / lyapunov + 1 / L := by
        field_simp
      rw [hexp] at hmul
      rw [← hA]
      linarith
    have heq : (2 / L) * (s.card : ℝ) * b =
        2 * ((1 / L) * (s.card : ℝ)) * b := by ring
    rw [heq]
    have hbb : 2 * ((1 / L) * (s.card : ℝ)) * b ≤ 2 * A * b := by
      apply mul_le_mul_of_nonneg_right _ hbpos.le
      linarith
    have hfin : 2 * A * b = η / 3 := by
      rw [hbdef]
      field_simp
    linarith
  have hmB : ∀ j ∈ s, MemLp (ZB j) 2 μ :=
    fun j _ => Prop64.memLp_Bremainder n j
  have hmT : ∀ j ∈ s, MemLp (ZT j) 2 μ :=
    fun j _ => Prop64.memLp_BremainderTrunc R n j
  have hmP : ∀ j ∈ s, MemLp (ZP j) 2 μ :=
    fun j _ => Prop64.memLp_symbolAt P n j
  have hiB : ∀ j ∈ s, Integrable (ZB j) μ :=
    fun j hj => (hmB j hj).integrable (by norm_num)
  have hiT : ∀ j ∈ s, Integrable (ZT j) μ :=
    fun j hj => (hmT j hj).integrable (by norm_num)
  have hiP : ∀ j ∈ s, Integrable (ZP j) μ :=
    fun j hj => (hmP j hj).integrable (by norm_num)
  have hb1 : eLpNorm (centeredAvg L s D1) 2 μ ≤ ENNReal.ofReal (η / 3) := by
    refine le_trans (Prop64.eLpNorm_centeredAvg_le hLpos hbpos.le
      (fun j hj => (hmB j hj).sub (hmT j hj)) (fun j hj => h1 j hj)) ?_
    exact ENNReal.ofReal_le_ofReal hcard
  have hb2 : eLpNorm (centeredAvg L s D2) 2 μ ≤ ENNReal.ofReal (η / 3) := by
    refine le_trans (Prop64.eLpNorm_centeredAvg_le hLpos hbpos.le
      (fun j hj => (hmT j hj).sub (hmP j hj)) (fun j hj => h2 j hj)) ?_
    exact ENNReal.ofReal_le_ofReal hcard
  have hdec : centeredAvg L s ZB = fun α =>
      (centeredAvg L s D1 α + centeredAvg L s D2 α) + centeredAvg L s ZP α := by
    funext α
    have e1 := Prop64.centeredAvg_sub (L := L) (s := s) hiB hiT α
    have e2 := Prop64.centeredAvg_sub (L := L) (s := s) hiT hiP α
    rw [← hD1] at e1
    rw [← hD2] at e2
    linarith
  have hm1 : AEStronglyMeasurable (centeredAvg L s D1) μ :=
    Prop64.aestronglyMeasurable_centeredAvg
      (fun j hj => ((hmB j hj).sub (hmT j hj)).1)
  have hm2 : AEStronglyMeasurable (centeredAvg L s D2) μ :=
    Prop64.aestronglyMeasurable_centeredAvg
      (fun j hj => ((hmT j hj).sub (hmP j hj)).1)
  have hm3 : AEStronglyMeasurable (centeredAvg L s ZP) μ :=
    Prop64.aestronglyMeasurable_centeredAvg (fun j hj => (hmP j hj).1)
  rw [hdec]
  have htri1 : eLpNorm (fun α => (centeredAvg L s D1 α + centeredAvg L s D2 α)
        + centeredAvg L s ZP α) 2 μ
      ≤ eLpNorm (fun α => centeredAvg L s D1 α + centeredAvg L s D2 α) 2 μ
        + eLpNorm (centeredAvg L s ZP) 2 μ :=
    eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)
  have htri2 : eLpNorm (fun α => centeredAvg L s D1 α + centeredAvg L s D2 α) 2 μ
      ≤ eLpNorm (centeredAvg L s D1) 2 μ + eLpNorm (centeredAvg L s D2) 2 μ :=
    eLpNorm_add_le hm1 hm2 (by norm_num)
  calc
    eLpNorm (fun α => (centeredAvg L s D1 α + centeredAvg L s D2 α)
        + centeredAvg L s ZP α) 2 μ
        ≤ (eLpNorm (centeredAvg L s D1) 2 μ + eLpNorm (centeredAvg L s D2) 2 μ)
          + eLpNorm (centeredAvg L s ZP) 2 μ := le_trans htri1 (by gcongr)
    _ ≤ (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) +
          ENNReal.ofReal (η / 3) := by gcongr
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

/-- Proposition 6.4, the bounded-remainder weak law, proved from the
manuscript route with no placeholder input. -/
theorem prop_6_4_bounded_remainder_weak_law :
    ∀ ε > 0,
      Tendsto
        (fun n : ℕ => (volume.restrict (Ioo (0 : ℝ) 1)).real
          {α : ℝ | ε ≤ |(1 / Lnorm n) *
            ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j *
              (Bremainder α n j - ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j)|})
        atTop (𝓝 0) := by
  intro ε hε
  exact Prop64.tendsto_measReal_of_eLpNorm
    (f := fun n => centeredAvg (Lnorm n) (bulkJ n) (fun j α => Bremainder α n j))
    (fun n => Prop64.aestronglyMeasurable_centeredAvg
      (fun j _ => (Prop64.memLp_Bremainder n j).1))
    remainderAvg_eLpNorm_small_clean hε

/-- Statement-drift guard against the canonical Proposition 6.4. -/
example : @_root_.Kwon1002.prop_6_4_bounded_remainder_weak_law =
    @prop_6_4_bounded_remainder_weak_law := rfl

assert_no_sorry carry_truncation_L2_small_clean
assert_no_sorry trunc_poly_L2_small_clean
assert_no_sorry remainderAvg_eLpNorm_small_clean
assert_no_sorry prop_6_4_bounded_remainder_weak_law

end

end Kwon1002.Prop64Final

namespace Kwon1002.Prop64

noncomputable section

/-- The canonical `L²` assembly, now declared after both proved analytic
inputs rather than above them with placeholders. -/
theorem remainderAvg_eLpNorm_small :
    ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      eLpNorm (centeredAvg (Lnorm n) (bulkJ n) (fun j α => Bremainder α n j)) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal η :=
  Prop64Final.remainderAvg_eLpNorm_small_clean

/-- The canonical Proposition 6.4 declaration, with the import-direction
artifact removed. -/
theorem prop_6_4_bounded_remainder_weak_law :
    ∀ ε > 0,
      Tendsto
        (fun n : ℕ => (volume.restrict (Ioo (0 : ℝ) 1)).real
          {α : ℝ | ε ≤ |(1 / Lnorm n) *
            ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j *
              (Bremainder α n j - ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j)|})
        atTop (𝓝 0) :=
  Prop64Final.prop_6_4_bounded_remainder_weak_law

/-- The relocated canonical declaration still has exactly the manuscript
statement from `Section6Skeleton`. -/
example : @_root_.Kwon1002.prop_6_4_bounded_remainder_weak_law =
    @prop_6_4_bounded_remainder_weak_law := rfl

assert_no_sorry remainderAvg_eLpNorm_small
assert_no_sorry prop_6_4_bounded_remainder_weak_law

end


end Kwon1002.Prop64
