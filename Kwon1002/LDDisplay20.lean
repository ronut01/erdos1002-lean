import Kwon1002.P42Cases
import Kwon1002.LDObservable

/-!
# Large deviations, stage C: display (16) instantiates display (20)

`display20_of_deviation`: given the self-contained large-deviation bound
(display (16) in the form proved by `LDDeviation.continuant_large_deviation`,
taken here as a hypothesis to keep this file independent of the assembly),
every window constant `δ > 0` admits `C, c > 0` with
`P42Cases.Display20 C δ c`.

The instantiation is `v := δH`, `r := j ≤ 2m_n`: the quadratic branch gives
`v²/j ≥ δ²L^{3/2}/(2L) = (δ²/2)√L`, and the clamped branch gives
`v/(1+log(j+1))² ≥ δL^{3/4}/(2500 L^{1/8}) ≥ √L` once
`L ≥ (2500/δ)^8` (using `log y ≤ 16 y^{1/16}`), so the bad-set mass is
`≤ C·exp(−c·min(δ²/2,1)·√L)` for every `j ≤ 2m_n` simultaneously.  The
index `j = 0` is vacuous: `q_0 = 1` sits inside the window.
-/

open Set MeasureTheory Filter

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-- Continuant denominators are at least `1` on all of `(0,1)` (no
irrationality needed): `q_0 = 1`, `q_1 = a_1 ≥ 1`, and the recursion is
monotone in steps of two. -/
lemma one_le_denom_of_mem_Ioo {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (j : ℕ) :
    1 ≤ denom α j := by
  have hd0 : 1 ≤ digit α 0 := by
    have h1 : (1 : ℝ) < α⁻¹ := by
      rw [lt_inv_comm₀ one_pos hα.1]
      simpa using hα.2
    have hfl : (1 : ℤ) ≤ ⌊α⁻¹⌋ :=
      Int.le_floor.mpr (by exact_mod_cast h1.le)
    have hd : digit α 0 = ⌊α⁻¹⌋.toNat := rfl
    rw [hd]
    omega
  have key : ∀ j : ℕ, 1 ≤ denom α j ∧ 1 ≤ denom α (j + 1) := by
    intro j
    induction j with
    | zero =>
      exact ⟨le_refl _, by rw [show denom α 1 = digit α 0 from rfl]; exact hd0⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have h : denom α (j + 2) = digit α (j + 1) * denom α (j + 1) + denom α j := rfl
      rw [h]
      exact le_trans ih.1 (Nat.le_add_left _ _)
  exact (key j).1

/-- `log y ≤ 16 · y^{1/16}` for `y ≥ 1`. -/
private lemma log_le_rpow_sixteenth {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ 16 * y ^ ((1 : ℝ) / 16) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hr0 : 0 < y ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos hy0 _
  have h1 : Real.log (y ^ ((1 : ℝ) / 16)) ≤ y ^ ((1 : ℝ) / 16) - 1 :=
    Real.log_le_sub_one_of_pos hr0
  have h2 : Real.log (y ^ ((1 : ℝ) / 16)) = (1 / 16) * Real.log y :=
    Real.log_rpow hy0 _
  nlinarith

/-- **Display (20) from display (16).**  The large-deviation bound for the
continuants (hypothesis, in the exact form of
`LDDeviation.continuant_large_deviation`) yields, for every `δ > 0`,
constants `C, c > 0` with `P42Cases.Display20 C δ c`. -/
theorem display20_of_deviation
    (hLD : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ v : ℝ, 0 < v →
      (volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
          v < |Real.log (denom α r : ℝ) - lyapunov * r|}).toReal
        ≤ C * Real.exp (-c * min (v ^ 2 / r) (v / (1 + Real.log (r + 1)) ^ 2)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ P42Cases.Display20 C δ c := by
  obtain ⟨C, c, hC, hc, hbound⟩ := hLD
  refine ⟨C, c * min (δ ^ 2 / 2) 1, hC, by positivity, ?_⟩
  unfold P42Cases.Display20
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, max 1 ((2500 / δ) ^ (8 : ℕ)) ≤ Lnorm n :=
    hLtend.eventually_ge_atTop _
  filter_upwards [hev] with n hLn
  have hL1 : 1 ≤ Lnorm n := le_trans (le_max_left _ _) hLn
  have hL0 : 0 < Lnorm n := lt_of_lt_of_le one_pos hL1
  have hLth : (2500 / δ) ^ (8 : ℕ) ≤ Lnorm n := le_trans (le_max_right _ _) hLn
  have hHval : Hscale n = Lnorm n ^ ((3 : ℝ) / 4) := rfl
  have hH0 : 0 < Hscale n := by
    rw [hHval]; exact Real.rpow_pos_of_pos hL0 _
  have hsqrt : Real.sqrt (Lnorm n) = Lnorm n ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow (Lnorm n)
  have hsqrt0 : 0 < Real.sqrt (Lnorm n) := Real.sqrt_pos.mpr hL0
  intro j hj
  have hm : (mIndex n : ℝ) ≤ Lnorm n := by
    have h1 : (mIndex n : ℝ) ≤ Lnorm n / lyapunov := by
      rw [show mIndex n = ⌊Lnorm n / lyapunov⌋₊ from rfl]
      exact Nat.floor_le (div_nonneg hL0.le lyapunov_pos'.le)
    have h2 : Lnorm n / lyapunov ≤ Lnorm n := by
      rw [div_le_iff₀ lyapunov_pos']
      nlinarith [one_lt_lyapunov]
    exact le_trans h1 h2
  have hjL : (j : ℝ) ≤ 2 * Lnorm n := by
    have h1 : (j : ℝ) ≤ 2 * (mIndex n : ℝ) := by exact_mod_cast hj
    linarith
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · -- `j = 0`: the window contains `q_0 = 1`, the bad set is empty
    have hδH : 0 ≤ δ * Hscale n := by positivity
    have h0 : ∀ α : ℝ, α ∈ Ioo (0 : ℝ) 1 →
        (Real.exp (lyapunov * ((0 : ℕ) : ℝ) - δ * Hscale n) ≤ (denom α 0 : ℝ)
          ∧ (denom α 0 : ℝ) ≤ Real.exp (lyapunov * ((0 : ℕ) : ℝ) + δ * Hscale n)) := by
      intro α _
      have hd : (denom α 0 : ℝ) = 1 := by
        rw [show denom α 0 = 1 from rfl]; norm_num
      rw [hd]
      constructor
      · rw [Real.exp_le_one_iff]
        simp only [Nat.cast_zero, mul_zero, zero_sub]
        linarith
      · rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
        apply Real.exp_le_exp.mpr
        simp only [Nat.cast_zero, mul_zero, zero_add]
        linarith
    refine le_trans (le_of_eq ?_) (by positivity)
    rw [measureReal_def,
      measure_mono_null (fun α hα => (hα.2 (h0 α hα.1)).elim) measure_empty]
    simp
  · -- `j ≥ 1`: instantiate the deviation bound at `v = δH`
    have hv0 : 0 < δ * Hscale n := mul_pos hδ hH0
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    -- containment of the bad set in the deviation set
    have hsub : {α ∈ Ioo (0 : ℝ) 1 |
        ¬ (Real.exp (lyapunov * (j : ℝ) - δ * Hscale n) ≤ (denom α j : ℝ)
            ∧ (denom α j : ℝ) ≤ Real.exp (lyapunov * (j : ℝ) + δ * Hscale n))}
        ⊆ {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
            δ * Hscale n < |Real.log (denom α j : ℝ) - lyapunov * j|} := by
      intro α hα
      obtain ⟨hαI, hnot⟩ := hα
      refine ⟨hαI, ?_⟩
      have hq1 : (1 : ℝ) ≤ (denom α j : ℝ) := by
        exact_mod_cast one_le_denom_of_mem_Ioo hαI j
      have hq0 : (0 : ℝ) < (denom α j : ℝ) := lt_of_lt_of_le one_pos hq1
      rw [not_and_or] at hnot
      rw [lt_abs]
      rcases hnot with h | h
      · push_neg at h
        have hlog : Real.log (denom α j : ℝ) < lyapunov * (j : ℝ) - δ * Hscale n := by
          have h2 := (Real.log_lt_log_iff hq0 (Real.exp_pos _)).mpr h
          rwa [Real.log_exp] at h2
        right
        linarith
      · push_neg at h
        have hlog : lyapunov * (j : ℝ) + δ * Hscale n < Real.log (denom α j : ℝ) := by
          have h2 := (Real.log_lt_log_iff (Real.exp_pos _) hq0).mpr h
          rwa [Real.log_exp] at h2
        left
        linarith
    -- branch 1: the quadratic exponent dominates `(δ²/2)√L`
    have hL32 : Lnorm n ^ ((3 : ℝ) / 2) = Lnorm n * Real.sqrt (Lnorm n) := by
      rw [hsqrt, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hL0,
        Real.rpow_one]
    have hv2 : (δ * Hscale n) ^ 2 = δ ^ 2 * (Lnorm n * Real.sqrt (Lnorm n)) := by
      rw [mul_pow, hHval, ← Real.rpow_natCast (Lnorm n ^ ((3 : ℝ) / 4)) 2,
        ← Real.rpow_mul hL0.le, ← hL32]
      norm_num
    have hbranch1 : (δ ^ 2 / 2) * Real.sqrt (Lnorm n)
        ≤ (δ * Hscale n) ^ 2 / (j : ℝ) := by
      rw [le_div_iff₀ hj0, hv2]
      calc δ ^ 2 / 2 * Real.sqrt (Lnorm n) * (j : ℝ)
          ≤ δ ^ 2 / 2 * Real.sqrt (Lnorm n) * (2 * Lnorm n) :=
            mul_le_mul_of_nonneg_left hjL (by positivity)
        _ = δ ^ 2 * (Lnorm n * Real.sqrt (Lnorm n)) := by ring
    -- branch 2: the clamped exponent dominates `√L`
    have hbranch2 : Real.sqrt (Lnorm n)
        ≤ (δ * Hscale n) / (1 + Real.log ((j : ℝ) + 1)) ^ 2 := by
      have hlog0 : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by linarith)
      have hden0 : 0 < (1 + Real.log ((j : ℝ) + 1)) ^ 2 := by positivity
      rw [le_div_iff₀ hden0]
      have h3L1 : (1 : ℝ) ≤ 3 * Lnorm n := by linarith
      have hlogle : Real.log ((j : ℝ) + 1) ≤ Real.log (3 * Lnorm n) :=
        Real.log_le_log (by linarith) (by linarith)
      have hlog3L : Real.log (3 * Lnorm n) ≤ 16 * (3 * Lnorm n) ^ ((1 : ℝ) / 16) :=
        log_le_rpow_sixteenth h3L1
      have hL16pos : 0 < Lnorm n ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos hL0 _
      have h316 : (3 * Lnorm n) ^ ((1 : ℝ) / 16) ≤ 3 * Lnorm n ^ ((1 : ℝ) / 16) := by
        rw [Real.mul_rpow (by norm_num) hL0.le]
        have h3 : (3 : ℝ) ^ ((1 : ℝ) / 16) ≤ 3 := by
          calc (3 : ℝ) ^ ((1 : ℝ) / 16)
              ≤ (3 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 3 := Real.rpow_one 3
        nlinarith
      have hL16one : (1 : ℝ) ≤ Lnorm n ^ ((1 : ℝ) / 16) := by
        have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL1
          (by norm_num : (0:ℝ) ≤ 1/16)
        rwa [Real.one_rpow] at h
      have hsq : (1 + Real.log ((j : ℝ) + 1)) ^ 2 ≤ 2500 * Lnorm n ^ ((1 : ℝ) / 8) := by
        have hup : 1 + Real.log ((j : ℝ) + 1) ≤ 50 * Lnorm n ^ ((1 : ℝ) / 16) := by
          calc 1 + Real.log ((j : ℝ) + 1)
              ≤ 1 + Real.log (3 * Lnorm n) := by linarith
            _ ≤ 1 + 16 * (3 * Lnorm n) ^ ((1 : ℝ) / 16) := by linarith
            _ ≤ 1 + 48 * Lnorm n ^ ((1 : ℝ) / 16) := by linarith
            _ ≤ 50 * Lnorm n ^ ((1 : ℝ) / 16) := by linarith
        have hL8 : (Lnorm n ^ ((1 : ℝ) / 16)) ^ 2 = Lnorm n ^ ((1 : ℝ) / 8) := by
          rw [← Real.rpow_natCast (Lnorm n ^ ((1 : ℝ) / 16)) 2,
            ← Real.rpow_mul hL0.le]
          norm_num
        calc (1 + Real.log ((j : ℝ) + 1)) ^ 2
            ≤ (50 * Lnorm n ^ ((1 : ℝ) / 16)) ^ 2 := by nlinarith
          _ = 2500 * Lnorm n ^ ((1 : ℝ) / 8) := by rw [mul_pow, hL8]; norm_num
      have hth : 2500 ≤ δ * Lnorm n ^ ((1 : ℝ) / 8) := by
        have h8 : 2500 / δ ≤ Lnorm n ^ ((1 : ℝ) / 8) := by
          have hpos : (0 : ℝ) ≤ 2500 / δ := by positivity
          have h := Real.rpow_le_rpow (by positivity) hLth
            (by norm_num : (0:ℝ) ≤ 1/8)
          rwa [← Real.rpow_natCast ((2500 / δ)) 8, ← Real.rpow_mul hpos,
            show ((8 : ℕ) : ℝ) * (1 / 8) = 1 by norm_num, Real.rpow_one] at h
        rw [div_le_iff₀ hδ] at h8
        linarith
      have e1 : Real.sqrt (Lnorm n) * (2500 * Lnorm n ^ ((1 : ℝ) / 8))
          = 2500 * Lnorm n ^ ((5 : ℝ) / 8) := by
        rw [hsqrt, show (5 : ℝ) / 8 = 1 / 2 + 1 / 8 by norm_num,
          Real.rpow_add hL0]
        ring
      have e2 : δ * Hscale n = (δ * Lnorm n ^ ((1 : ℝ) / 8)) * Lnorm n ^ ((5 : ℝ) / 8) := by
        rw [hHval, show (3 : ℝ) / 4 = 1 / 8 + 5 / 8 by norm_num, Real.rpow_add hL0]
        ring
      calc Real.sqrt (Lnorm n) * (1 + Real.log ((j : ℝ) + 1)) ^ 2
          ≤ Real.sqrt (Lnorm n) * (2500 * Lnorm n ^ ((1 : ℝ) / 8)) :=
            mul_le_mul_of_nonneg_left hsq hsqrt0.le
        _ = 2500 * Lnorm n ^ ((5 : ℝ) / 8) := e1
        _ ≤ (δ * Lnorm n ^ ((1 : ℝ) / 8)) * Lnorm n ^ ((5 : ℝ) / 8) :=
            mul_le_mul_of_nonneg_right hth (Real.rpow_pos_of_pos hL0 _).le
        _ = δ * Hscale n := e2.symm
    -- assemble
    have hmin : (c * min (δ ^ 2 / 2) 1) * Real.sqrt (Lnorm n)
        ≤ c * min ((δ * Hscale n) ^ 2 / (j : ℝ))
            ((δ * Hscale n) / (1 + Real.log ((j : ℝ) + 1)) ^ 2) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hc.le
      apply le_min
      · calc min (δ ^ 2 / 2) 1 * Real.sqrt (Lnorm n)
            ≤ (δ ^ 2 / 2) * Real.sqrt (Lnorm n) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hsqrt0.le
          _ ≤ (δ * Hscale n) ^ 2 / (j : ℝ) := hbranch1
      · calc min (δ ^ 2 / 2) 1 * Real.sqrt (Lnorm n)
            ≤ 1 * Real.sqrt (Lnorm n) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hsqrt0.le
          _ = Real.sqrt (Lnorm n) := one_mul _
          _ ≤ (δ * Hscale n) / (1 + Real.log ((j : ℝ) + 1)) ^ 2 := hbranch2
    have hfin := hbound j hj1 (δ * Hscale n) hv0
    calc volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (j : ℝ) - δ * Hscale n) ≤ (denom α j : ℝ)
              ∧ (denom α j : ℝ) ≤ Real.exp (lyapunov * (j : ℝ) + δ * Hscale n))}
        ≤ (volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
            δ * Hscale n < |Real.log (denom α j : ℝ) - lyapunov * j|}).toReal := by
          rw [measureReal_def]
          apply ENNReal.toReal_mono
          · refine ne_of_lt (lt_of_le_of_lt
              (measure_mono (fun α hα => hα.1)) ?_)
            rw [Real.volume_Ioo]
            norm_num
          · exact measure_mono hsub
      _ ≤ C * Real.exp (-c * min ((δ * Hscale n) ^ 2 / (j : ℝ))
            ((δ * Hscale n) / (1 + Real.log ((j : ℝ) + 1)) ^ 2)) := hfin
      _ ≤ C * Real.exp (-(c * min (δ ^ 2 / 2) 1) * Real.sqrt (Lnorm n)) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply Real.exp_le_exp.mpr
          nlinarith [hmin]

end

end LargeDeviation

end Kwon1002
