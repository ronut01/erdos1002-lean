import Kwon1002.LDSpine
import Kwon1002.LDExcess
import Kwon1002.LDBlocks

/-!
# Large deviations, stage B′: display (16) assembled

`continuant_large_deviation`: for all `r ≥ 1` and `v > 0`,

`Leb{α ∈ (0,1) : |log q_r − λr| > v}
   ≤ C exp(−c·min(v²/r, v/(1+log(r+1))²))`.

Chain: the spine turns the event into `|S_r| > v − log 2`; the Birkhoff sum
splits as `S_r = T_r + E_r` (capped part plus excess) with
`T_r − 1 ≤ hatSum ≤ T_r + 1` after windowing; the excess tail is
`LDExcess.excess_tail`; the capped windowed sum obeys the two-sided
exponential-moment bound `LDBlocks.exists_hatSum_mgf`, and Markov at
`σ = min(z/(4C₁r), 1/(8W(u+3)))` produces the two Chernoff branches.

Parameter ledger, given `r ≥ 1`: `u := log C_E + 4 log(r+1)`,
`W := ⌈K(log(r+1)+1)⌉` with `K := 200(1 + log C_E)`, where `C_E ≥ 1` is the
excess-tail threshold constant.  The mixing smallness `24ρ₀^W r ≤ 1` holds
since `W·log(540/527) ≥ (W/50) ≥ 4(log(r+1)+1) ≥ log(24r)`; the windowing
smallness `r·e^{u+λ}·2·(1/2)^W ≤ 1` since
`W log 2 ≥ 138(1+log C_E)(log(r+1)+1)` dominates
`log(2r) + u + λ ≤ 5 log(r+1) + log C_E + 4`.
-/

open Set MeasureTheory Filter

namespace Kwon1002

namespace LargeDeviation

noncomputable section

set_option maxHeartbeats 2000000

/-! ### Elementary helpers -/

private lemma flog_split (u : ℝ) {x : ℝ} (hx : 0 < x) :
    flog x = capLog u x + max (flog x - u) 0 := by
  rw [capLog_eq_min hx]
  rcases le_total (flog x) u with h | h
  · rw [min_eq_left h, max_eq_right (by linarith : flog x - u ≤ 0)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ flog x - u)]
    ring

private lemma min_mul_min_le {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min a b * min x y ≤ min (a * x) (b * y) := by
  refine le_min ?_ ?_
  · exact mul_le_mul (min_le_left a b) (min_le_left x y) (le_min hx hy) ha
  · exact mul_le_mul (min_le_right a b) (min_le_right x y) (le_min hx hy) hb

private lemma div_le_div'' {a b c d : ℝ} (hc : 0 ≤ c) (hac : a ≤ c)
    (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d := by
  have hb : 0 < b := lt_of_lt_of_le hd hdb
  rw [div_le_div_iff₀ hb hd]
  calc a * d ≤ c * d := mul_le_mul_of_nonneg_right hac hd.le
    _ ≤ c * b := mul_le_mul_of_nonneg_left hdb hc

/-- Global bound on the windowed capped sum: each site sits in `[−λ, u]`. -/
private lemma abs_hatSum_le {u : ℝ} (hu : 0 ≤ u) (W r : ℕ) (α : ℝ) :
    |hatSum u W r α| ≤ (r : ℝ) * (u + 2) := by
  have hsite : ∀ y : ℝ, |hatSite u W y| ≤ u + 2 := by
    intro y
    rw [abs_le]
    constructor
    · have h1 := neg_lyapunov_le_hatSite hu W y
      have h2 := lyapunov_lt_two
      linarith
    · have h1 := hatSite_le_cap u W y
      linarith
  calc |hatSum u W r α|
      = |∑ i ∈ Finset.range r, hatSite u W (Erdos1002.gaussOrbit i α)| := rfl
    _ ≤ ∑ i ∈ Finset.range r, |hatSite u W (Erdos1002.gaussOrbit i α)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range r, (u + 2) :=
        Finset.sum_le_sum fun i _ => hsite _
    _ = (r : ℝ) * (u + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Chernoff/Markov step over the Gauss measure, for a uniformly bounded
measurable observable. -/
private lemma chernoff {X : ℝ → ℝ} (hX : Measurable X) {b : ℝ}
    (hb : ∀ α, |X α| ≤ b) {σ : ℝ} (hσ : 0 ≤ σ) (z : ℝ) :
    (Erdos1002.gaussMeasure {α : ℝ | z < X α}).toReal
      ≤ Real.exp (-(σ * z)) * ∫ α, Real.exp (σ * X α) ∂Erdos1002.gaussMeasure := by
  have hE : MeasurableSet {α : ℝ | z < X α} := measurableSet_lt measurable_const hX
  have hmeas : Measurable fun α => Real.exp (σ * X α) :=
    Real.measurable_exp.comp (hX.const_mul σ)
  have hint : Integrable (fun α => Real.exp (σ * X α)) Erdos1002.gaussMeasure := by
    refine Integrable.mono' (integrable_const (Real.exp (σ * b)))
      hmeas.aestronglyMeasurable ?_
    refine Eventually.of_forall fun α => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb α)) hσ)
  have h1 : Real.exp (σ * z) * (Erdos1002.gaussMeasure {α : ℝ | z < X α}).toReal
      ≤ ∫ α, Real.exp (σ * X α) ∂Erdos1002.gaussMeasure := by
    have h2 : Real.exp (σ * z) * Erdos1002.gaussMeasure.real {α : ℝ | z < X α}
        ≤ ∫ α in {α : ℝ | z < X α}, Real.exp (σ * X α) ∂Erdos1002.gaussMeasure := by
      refine setIntegral_ge_of_const_le_real hE (measure_ne_top _ _)
        (fun α hα => ?_) hint.integrableOn
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hα) hσ)
    have h3 : ∫ α in {α : ℝ | z < X α}, Real.exp (σ * X α) ∂Erdos1002.gaussMeasure
        ≤ ∫ α, Real.exp (σ * X α) ∂Erdos1002.gaussMeasure :=
      setIntegral_le_integral hint (Eventually.of_forall fun α => (Real.exp_pos _).le)
    rw [measureReal_def] at h2
    linarith
  have hpos : (0:ℝ) < Real.exp (σ * z) := Real.exp_pos _
  have h4 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
  calc (Erdos1002.gaussMeasure {α : ℝ | z < X α}).toReal
      = (Real.exp (σ * z))⁻¹
          * (Real.exp (σ * z) * (Erdos1002.gaussMeasure {α : ℝ | z < X α}).toReal) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ (Real.exp (σ * z))⁻¹ * ∫ α, Real.exp (σ * X α) ∂Erdos1002.gaussMeasure := h4
    _ = Real.exp (-(σ * z)) * ∫ α, Real.exp (σ * X α) ∂Erdos1002.gaussMeasure := by
        rw [Real.exp_neg]

/-! ### The two Chernoff tails for `hatSum` -/

private lemma tail_upper {C₁ : ℝ} (hC₁ : 1 ≤ C₁) {u : ℝ} (hu : 0 ≤ u)
    {r W : ℕ} (hr : 1 ≤ r) (hW : 1 ≤ W)
    (hmgf : ∀ σ : ℝ, 0 ≤ σ → σ * (4 * W * (u + 3)) ≤ 1 / 2 →
      ∫ α, Real.exp (σ * hatSum u W r α) ∂Erdos1002.gaussMeasure
        ≤ Real.exp (C₁ * (1 + σ ^ 2 * r)))
    {z : ℝ} (hz : 0 < z) :
    (Erdos1002.gaussMeasure {α : ℝ | z < hatSum u W r α}).toReal
      ≤ Real.exp C₁ *
        Real.exp (-(3 / 4) * min (z ^ 2 / (4 * C₁ * r)) (z / (8 * W * (u + 3)))) := by
  have hC₁0 : (0:ℝ) < C₁ := lt_of_lt_of_le one_pos hC₁
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hW1' : (1:ℝ) ≤ (W:ℝ) := by exact_mod_cast hW
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hW0 : (0:ℝ) < (W:ℝ) := by linarith
  have hu3 : (0:ℝ) < u + 3 := by linarith
  have h4Cr : (0:ℝ) < 4 * C₁ * r := by positivity
  have h8W : (0:ℝ) < 8 * (W:ℝ) * (u + 3) := mul_pos (mul_pos (by norm_num) hW0) hu3
  set σ : ℝ := min (z / (4 * C₁ * r)) (1 / (8 * W * (u + 3))) with hσdef
  have hσ0 : 0 < σ := lt_min (div_pos hz h4Cr) (div_pos one_pos h8W)
  have hσcap : σ * (4 * W * (u + 3)) ≤ 1 / 2 := by
    have h1 : σ ≤ 1 / (8 * W * (u + 3)) := min_le_right _ _
    have h4W : (0:ℝ) < 4 * (W:ℝ) * (u + 3) := mul_pos (mul_pos (by norm_num) hW0) hu3
    have h2 : σ * (4 * W * (u + 3)) ≤ 1 / (8 * W * (u + 3)) * (4 * W * (u + 3)) :=
      mul_le_mul_of_nonneg_right h1 h4W.le
    have h3 : 1 / (8 * (W:ℝ) * (u + 3)) * (4 * W * (u + 3)) = 1 / 2 := by
      field_simp
      ring
    linarith
  have hmoment := hmgf σ hσ0.le hσcap
  have habs : ∀ α : ℝ, |hatSum u W r α| ≤ (r:ℝ) * (u + 2) :=
    fun α => abs_hatSum_le hu W r α
  have hcher := chernoff (measurable_hatSum u W r) habs hσ0.le z
  have hquad : C₁ * σ ^ 2 * r ≤ σ * z / 4 := by
    have h1 : σ ≤ z / (4 * C₁ * r) := min_le_left _ _
    have h2 : σ * (4 * C₁ * r) ≤ z / (4 * C₁ * r) * (4 * C₁ * r) :=
      mul_le_mul_of_nonneg_right h1 h4Cr.le
    have h4 : σ * (4 * C₁ * r) ≤ z := by
      calc σ * (4 * C₁ * r) ≤ z / (4 * C₁ * r) * (4 * C₁ * r) := h2
        _ = z := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h4 hσ0.le]
  have hσz : min (z ^ 2 / (4 * C₁ * r)) (z / (8 * W * (u + 3))) ≤ σ * z := by
    rcases le_total (z / (4 * C₁ * (r:ℝ))) (1 / (8 * (W:ℝ) * (u + 3))) with h | h
    · have hσeq : σ = z / (4 * C₁ * r) := by rw [hσdef]; exact min_eq_left h
      rw [hσeq]
      have he : z / (4 * C₁ * (r:ℝ)) * z = z ^ 2 / (4 * C₁ * r) := by ring
      rw [he]
      exact min_le_left _ _
    · have hσeq : σ = 1 / (8 * W * (u + 3)) := by rw [hσdef]; exact min_eq_right h
      rw [hσeq]
      have he : 1 / (8 * (W:ℝ) * (u + 3)) * z = z / (8 * W * (u + 3)) := by ring
      rw [he]
      exact min_le_right _ _
  calc (Erdos1002.gaussMeasure {α : ℝ | z < hatSum u W r α}).toReal
      ≤ Real.exp (-(σ * z))
          * ∫ α, Real.exp (σ * hatSum u W r α) ∂Erdos1002.gaussMeasure := hcher
    _ ≤ Real.exp (-(σ * z)) * Real.exp (C₁ * (1 + σ ^ 2 * r)) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
    _ = Real.exp (C₁ + (C₁ * σ ^ 2 * r - σ * z)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (C₁ + -(3 / 4) * (σ * z)) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = Real.exp C₁ * Real.exp (-(3 / 4) * (σ * z)) := by rw [← Real.exp_add]
    _ ≤ Real.exp C₁ *
          Real.exp (-(3 / 4) * min (z ^ 2 / (4 * C₁ * r)) (z / (8 * W * (u + 3)))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        linarith

private lemma tail_lower {C₁ : ℝ} (hC₁ : 1 ≤ C₁) {u : ℝ} (hu : 0 ≤ u)
    {r W : ℕ} (hr : 1 ≤ r) (hW : 1 ≤ W)
    (hre : (r:ℝ) * Real.exp (-u / 2) ≤ 1)
    (hmgf : ∀ σ : ℝ, 0 ≤ σ → σ * (4 * W * (u + 3)) ≤ 1 / 2 →
      ∫ α, Real.exp (-(σ * hatSum u W r α)) ∂Erdos1002.gaussMeasure
        ≤ Real.exp (C₁ * (1 + σ ^ 2 * r + σ * r * Real.exp (-u / 2))))
    {z : ℝ} (hz : 0 < z) :
    (Erdos1002.gaussMeasure {α : ℝ | z < -(hatSum u W r α)}).toReal
      ≤ Real.exp (2 * C₁) *
        Real.exp (-(3 / 4) * min (z ^ 2 / (4 * C₁ * r)) (z / (8 * W * (u + 3)))) := by
  have hC₁0 : (0:ℝ) < C₁ := lt_of_lt_of_le one_pos hC₁
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hW1' : (1:ℝ) ≤ (W:ℝ) := by exact_mod_cast hW
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hW0 : (0:ℝ) < (W:ℝ) := by linarith
  have hu3 : (0:ℝ) < u + 3 := by linarith
  have h4Cr : (0:ℝ) < 4 * C₁ * r := by positivity
  have h8W : (0:ℝ) < 8 * (W:ℝ) * (u + 3) := mul_pos (mul_pos (by norm_num) hW0) hu3
  set σ : ℝ := min (z / (4 * C₁ * r)) (1 / (8 * W * (u + 3))) with hσdef
  have hσ0 : 0 < σ := lt_min (div_pos hz h4Cr) (div_pos one_pos h8W)
  have hσcap : σ * (4 * W * (u + 3)) ≤ 1 / 2 := by
    have h1 : σ ≤ 1 / (8 * W * (u + 3)) := min_le_right _ _
    have h4W : (0:ℝ) < 4 * (W:ℝ) * (u + 3) := mul_pos (mul_pos (by norm_num) hW0) hu3
    have h2 : σ * (4 * W * (u + 3)) ≤ 1 / (8 * W * (u + 3)) * (4 * W * (u + 3)) :=
      mul_le_mul_of_nonneg_right h1 h4W.le
    have h3 : 1 / (8 * (W:ℝ) * (u + 3)) * (4 * W * (u + 3)) = 1 / 2 := by
      field_simp
      ring
    linarith
  have hσ1 : σ ≤ 1 := by
    have h1 : σ ≤ 1 / (8 * W * (u + 3)) := min_le_right _ _
    have h2 : (24:ℝ) ≤ 8 * W * (u + 3) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (W:ℝ)) hu]
    have h3 : 1 / (8 * (W:ℝ) * (u + 3)) ≤ 1 / 24 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
    linarith
  have hprod : σ * ((r:ℝ) * Real.exp (-u / 2)) ≤ 1 := by
    have h1 : (0:ℝ) ≤ (r:ℝ) * Real.exp (-u / 2) :=
      mul_nonneg hr0.le (Real.exp_pos _).le
    have h2 := mul_le_mul hσ1 hre h1 (by norm_num : (0:ℝ) ≤ 1)
    linarith
  have hexp_bound : C₁ * (1 + σ ^ 2 * r + σ * r * Real.exp (-u / 2))
      ≤ 2 * C₁ + C₁ * σ ^ 2 * r := by
    have h1 : C₁ * (σ * ((r:ℝ) * Real.exp (-u / 2))) ≤ C₁ * 1 :=
      mul_le_mul_of_nonneg_left hprod hC₁0.le
    nlinarith [h1]
  have hmoment := hmgf σ hσ0.le hσcap
  have habs : ∀ α : ℝ, |-(hatSum u W r α)| ≤ (r:ℝ) * (u + 2) := fun α => by
    rw [abs_neg]; exact abs_hatSum_le hu W r α
  have hcher := chernoff ((measurable_hatSum u W r).neg) habs hσ0.le z
  simp only [mul_neg] at hcher
  have hquad : C₁ * σ ^ 2 * r ≤ σ * z / 4 := by
    have h1 : σ ≤ z / (4 * C₁ * r) := min_le_left _ _
    have h2 : σ * (4 * C₁ * r) ≤ z / (4 * C₁ * r) * (4 * C₁ * r) :=
      mul_le_mul_of_nonneg_right h1 h4Cr.le
    have h4 : σ * (4 * C₁ * r) ≤ z := by
      calc σ * (4 * C₁ * r) ≤ z / (4 * C₁ * r) * (4 * C₁ * r) := h2
        _ = z := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h4 hσ0.le]
  have hσz : min (z ^ 2 / (4 * C₁ * r)) (z / (8 * W * (u + 3))) ≤ σ * z := by
    rcases le_total (z / (4 * C₁ * (r:ℝ))) (1 / (8 * (W:ℝ) * (u + 3))) with h | h
    · have hσeq : σ = z / (4 * C₁ * r) := by rw [hσdef]; exact min_eq_left h
      rw [hσeq]
      have he : z / (4 * C₁ * (r:ℝ)) * z = z ^ 2 / (4 * C₁ * r) := by ring
      rw [he]
      exact min_le_left _ _
    · have hσeq : σ = 1 / (8 * W * (u + 3)) := by rw [hσdef]; exact min_eq_right h
      rw [hσeq]
      have he : 1 / (8 * (W:ℝ) * (u + 3)) * z = z / (8 * W * (u + 3)) := by ring
      rw [he]
      exact min_le_right _ _
  calc (Erdos1002.gaussMeasure {α : ℝ | z < -(hatSum u W r α)}).toReal
      ≤ Real.exp (-(σ * z))
          * ∫ α, Real.exp (-(σ * hatSum u W r α)) ∂Erdos1002.gaussMeasure := hcher
    _ ≤ Real.exp (-(σ * z))
          * Real.exp (C₁ * (1 + σ ^ 2 * r + σ * r * Real.exp (-u / 2))) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
    _ ≤ Real.exp (-(σ * z)) * Real.exp (2 * C₁ + C₁ * σ ^ 2 * r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_bound) (Real.exp_pos _).le
    _ = Real.exp (2 * C₁ + (C₁ * σ ^ 2 * r - σ * z)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * C₁ + -(3 / 4) * (σ * z)) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = Real.exp (2 * C₁) * Real.exp (-(3 / 4) * (σ * z)) := by rw [← Real.exp_add]
    _ ≤ Real.exp (2 * C₁) *
          Real.exp (-(3 / 4) * min (z ^ 2 / (4 * C₁ * r)) (z / (8 * W * (u + 3)))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        linarith

/-! ### The pointwise trichotomy -/

private lemma pointwise_split {v u : ℝ} {r W : ℕ}
    (hwin : (r:ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) ≤ 1)
    {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α)
    (hbad : v < |Real.log (denom α r : ℝ) - lyapunov * r|) :
    (v - 3) / 2 < hatSum u W r α
      ∨ (v - 1) / 2 < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0
      ∨ v - 2 < -(hatSum u W r α) := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hspine := abs_log_denom_sub_lyapunov_le hα hirr r
  have hS : v - 1 < |∑ i ∈ Finset.range r, flog (gaussIter α i)| := by linarith
  have hposIter : ∀ i : ℕ, 0 < gaussIter α i :=
    fun i => (gaussIter_mem_Ioo hα hirr i).1
  have hsplit : ∑ i ∈ Finset.range r, flog (gaussIter α i)
      = (∑ i ∈ Finset.range r, capLog u (gaussIter α i))
        + ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => flog_split u (hposIter i)
  have hhat : |hatSum u W r α - ∑ i ∈ Finset.range r, capLog u (gaussIter α i)| ≤ 1 :=
    le_trans (abs_hatSum_sub_capSum_le u W r hα hirr) hwin
  rw [abs_le] at hhat
  rcases abs_cases (∑ i ∈ Finset.range r, flog (gaussIter α i)) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at hS
    rcases le_or_gt (∑ i ∈ Finset.range r, capLog u (gaussIter α i)) ((v - 1) / 2)
      with hT | hT
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inl (by linarith [hhat.1])
  · rw [heq] at hS
    have hTS : (∑ i ∈ Finset.range r, capLog u (gaussIter α i))
        ≤ ∑ i ∈ Finset.range r, flog (gaussIter α i) :=
      Finset.sum_le_sum fun i _ => capLog_le_flog (hposIter i)
    exact Or.inr (Or.inr (by linarith [hhat.2]))

/-! ### The theorem -/

/-- **Display (16), self-contained form.**  The Lebesgue measure of the set
where the log-continuant deviates from `λr` by more than `v` is at most
`C exp(−c·min(v²/r, v/(1+log(r+1))²))`. -/
theorem continuant_large_deviation :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ v : ℝ, 0 < v →
      (volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
          v < |Real.log (denom α r : ℝ) - lyapunov * r|}).toReal
        ≤ C * Real.exp (-c * min (v ^ 2 / r) (v / (1 + Real.log (r + 1)) ^ 2)) := by
  obtain ⟨CE, hCE1, hexc⟩ := excess_tail
  obtain ⟨C₁, hC₁1, hmgf⟩ := exists_hatSum_mgf
  have hC₁0 : (0:ℝ) < C₁ := lt_of_lt_of_le one_pos hC₁1
  have hlCE0 : (0:ℝ) ≤ Real.log CE := Real.log_nonneg hCE1
  set lCE : ℝ := Real.log CE with hlCEdef
  set K : ℝ := 200 * (1 + lCE) with hKdef
  have hK200 : (200:ℝ) ≤ K := by rw [hKdef]; linarith
  set K₂ : ℝ := 8 * (K + 1) * (lCE + 7) with hK₂def
  have hK₂pos : (0:ℝ) < K₂ := by rw [hK₂def]; nlinarith
  set c₀ : ℝ := min (1 / (64 * C₁)) (1 / (4 * K₂)) with hc₀def
  have hc₀pos : (0:ℝ) < c₀ :=
    lt_min (div_pos one_pos (by linarith)) (div_pos one_pos (by linarith))
  set c : ℝ := min ((3 / 4) * c₀) (1 / 64) with hcdef
  set C : ℝ := 4 * Real.exp (2 * C₁) + 3 + Real.exp 64 with hCdef
  have hcpos : 0 < c := lt_min (mul_pos (by norm_num) hc₀pos) (by norm_num)
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hc64 : c ≤ 1 / 64 := min_le_right _ _
  refine ⟨C, c, hCpos, hcpos, ?_⟩
  intro r hr v hv
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  set L : ℝ := Real.log ((r:ℝ) + 1) with hLdef
  have hL0 : (0:ℝ) ≤ L := by rw [hLdef]; exact Real.log_nonneg (by linarith)
  set m : ℝ := min (v ^ 2 / (r:ℝ)) (v / (1 + L) ^ 2) with hmdef
  have hm0 : 0 ≤ m := by
    rw [hmdef]
    exact le_min (by positivity) (div_nonneg hv.le (by positivity))
  rcases le_or_gt v 8 with hv8 | hv8
  · -- easy regime: the whole interval has measure 1 and the bound is ≥ 1
    have hsub : {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        v < |Real.log (denom α r : ℝ) - lyapunov * r|} ⊆ Set.Ioo (0:ℝ) 1 :=
      fun α hα => hα.1
    have hvol : (volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        v < |Real.log (denom α r : ℝ) - lyapunov * r|}).toReal ≤ 1 := by
      have h1 : volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
          v < |Real.log (denom α r : ℝ) - lyapunov * r|}
          ≤ volume (Set.Ioo (0:ℝ) 1) := measure_mono hsub
      rw [Real.volume_Ioo] at h1
      have h2 := ENNReal.toReal_mono (by simp) h1
      simpa using h2
    have hm64 : m ≤ 64 := by
      rw [hmdef]
      refine (min_le_left _ _).trans ?_
      have h1 : v ^ 2 / (r:ℝ) ≤ v ^ 2 := div_le_self (sq_nonneg v) hrR
      nlinarith
    have hcm : c * m ≤ 1 := by
      nlinarith [mul_le_mul hc64 hm64 hm0 (by norm_num : (0:ℝ) ≤ 1 / 64)]
    have h3 : Real.exp 64 * Real.exp (-1 : ℝ) ≤ C * Real.exp (-c * m) := by
      have hC64 : Real.exp 64 ≤ C := by
        rw [hCdef]
        have h := Real.exp_pos (2 * C₁)
        linarith
      have hee : Real.exp (-1 : ℝ) ≤ Real.exp (-c * m) :=
        Real.exp_le_exp.mpr (by linarith)
      exact mul_le_mul hC64 hee (Real.exp_pos _).le hCpos.le
    have h4 : (1:ℝ) ≤ Real.exp 64 * Real.exp (-1 : ℝ) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by norm_num)
    linarith
  · -- main regime: v > 8
    set u : ℝ := lCE + 4 * L with hudef
    have hu0 : (0:ℝ) ≤ u := by rw [hudef]; linarith
    have hKL1 : (0:ℝ) < K * (L + 1) := by nlinarith
    set W : ℕ := ⌈K * (L + 1)⌉₊ with hWdef
    have hW1 : 1 ≤ W := by rw [hWdef]; exact Nat.one_le_ceil_iff.mpr hKL1
    have hWlo : K * (L + 1) ≤ (W:ℝ) := by rw [hWdef]; exact Nat.le_ceil _
    have hWhi : (W:ℝ) ≤ K * (L + 1) + 1 := by
      rw [hWdef]; exact (Nat.ceil_lt_add_one hKL1.le).le
    have hWR1 : (1:ℝ) ≤ (W:ℝ) := by exact_mod_cast hW1
    -- log facts
    have hlogr : Real.log (r:ℝ) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log (by linarith) (by linarith)
    -- smallness (m1): mixing
    have hlog5427 : (1:ℝ) / 50 ≤ Real.log (540 / 527) := by
      have h1 : Real.log ((527:ℝ) / 540) ≤ 527 / 540 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      have h2 : Real.log ((540:ℝ) / 527) = -Real.log ((527:ℝ) / 540) := by
        rw [← Real.log_inv]
        norm_num
      rw [h2]
      linarith
    have hlog24 : Real.log 24 ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h2 : (7:ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
      have h4 : (24:ℝ) ≤ Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
        nlinarith
      have hexp4 : Real.exp (4:ℝ)
          = Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      rw [hexp4]
      exact h4
    have hm1 : (r:ℝ) * (24 * (527 / 540 : ℝ) ^ W) ≤ 1 := by
      have hWover : 4 * (L + 1) ≤ (W:ℝ) / 50 := by
        have h1 : 200 * (L + 1) ≤ K * (L + 1) :=
          mul_le_mul_of_nonneg_right hK200 (by linarith)
        linarith
      have h24r : (24:ℝ) * r ≤ Real.exp ((W:ℝ) / 50) := by
        have hpos : (0:ℝ) < 24 * (r:ℝ) := by linarith
        rw [← Real.exp_log hpos]
        apply Real.exp_le_exp.mpr
        rw [Real.log_mul (by norm_num) (ne_of_gt hrpos)]
        linarith
      have hpow : (527 / 540 : ℝ) ^ W ≤ Real.exp (-((W:ℝ) / 50)) := by
        have h1 : (527 / 540 : ℝ) ^ W = Real.exp ((W:ℝ) * Real.log (527 / 540)) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 527 / 540)]
        rw [h1]
        apply Real.exp_le_exp.mpr
        have h2 : Real.log ((527:ℝ) / 540) = -Real.log ((540:ℝ) / 527) := by
          rw [← Real.log_inv]
          norm_num
        rw [h2, mul_neg]
        have h3 : (W:ℝ) / 50 ≤ (W:ℝ) * Real.log (540 / 527) := by
          have h4 := mul_le_mul_of_nonneg_left hlog5427
            (by positivity : (0:ℝ) ≤ (W:ℝ))
          calc (W:ℝ) / 50 = (W:ℝ) * (1 / 50) := by ring
            _ ≤ (W:ℝ) * Real.log (540 / 527) := h4
        linarith
      calc (r:ℝ) * (24 * (527 / 540 : ℝ) ^ W)
          = 24 * (r:ℝ) * (527 / 540 : ℝ) ^ W := by ring
        _ ≤ Real.exp ((W:ℝ) / 50) * Real.exp (-((W:ℝ) / 50)) :=
            mul_le_mul h24r hpow (by positivity) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    -- smallness (m2): windowing
    have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlog2gt : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hm2 : (r:ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) ≤ 1 := by
      have hhalf : (1 / 2 : ℝ) ^ W = Real.exp (-((W:ℝ) * Real.log 2)) := by
        have h0 : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
          norm_num
        rw [h0, ← Real.exp_nat_mul, mul_neg]
      have hlyap2 : lyapunov < 2 := lyapunov_lt_two
      have hlyap0 : 0 < lyapunov := lyapunov_pos'
      have hkey : Real.log 2 + Real.log (r:ℝ) + u + lyapunov ≤ (W:ℝ) * Real.log 2 := by
        have hW2 : K * (L + 1) * Real.log 2 ≤ (W:ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hWlo (by linarith)
        have hKgeq : 200 + 200 * lCE ≤ K := by rw [hKdef]; linarith
        have hKL : 200 * L ≤ K * L := mul_le_mul_of_nonneg_right hK200 hL0
        have h069 : K * (L + 1) * 0.69 ≤ K * (L + 1) * Real.log 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hKL1.le
        have hlow : 138 * (L + 1) + 138 * lCE ≤ K * (L + 1) * Real.log 2 := by
          nlinarith [h069, hKL, hKgeq]
        linarith
      have hpos2r : (0:ℝ) < 2 * (r:ℝ) * Real.exp (u + lyapunov) := by positivity
      calc (r:ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))
          = 2 * (r:ℝ) * Real.exp (u + lyapunov) * (1 / 2 : ℝ) ^ W := by ring
        _ = 2 * (r:ℝ) * Real.exp (u + lyapunov)
              * Real.exp (-((W:ℝ) * Real.log 2)) := by rw [hhalf]
        _ = Real.exp (Real.log (2 * (r:ℝ) * Real.exp (u + lyapunov)))
              * Real.exp (-((W:ℝ) * Real.log 2)) := by
            rw [Real.exp_log hpos2r]
        _ ≤ 1 := by
            rw [← Real.exp_add]
            have hlog2r : Real.log (2 * (r:ℝ) * Real.exp (u + lyapunov))
                = Real.log 2 + Real.log (r:ℝ) + (u + lyapunov) := by
              rw [Real.log_mul (by linarith : (2:ℝ) * (r:ℝ) ≠ 0) (Real.exp_pos _).ne',
                Real.log_mul (by norm_num) (ne_of_gt hrpos), Real.log_exp]
            calc Real.exp (Real.log (2 * (r:ℝ) * Real.exp (u + lyapunov))
                    + -((W:ℝ) * Real.log 2))
                ≤ Real.exp 0 := by
                  apply Real.exp_le_exp.mpr
                  rw [hlog2r]
                  linarith
              _ = 1 := Real.exp_zero
    -- residual exponential smallness for the lower tail
    have hre : (r:ℝ) * Real.exp (-u / 2) ≤ 1 := by
      have h1 : Real.exp (-u / 2) ≤ Real.exp (-(2 * L)) := by
        apply Real.exp_le_exp.mpr
        rw [hudef]
        linarith
      have h2 : Real.exp (-(2 * L)) = (((r:ℝ) + 1) ^ 2)⁻¹ := by
        rw [Real.exp_neg]
        congr 1
        rw [two_mul, Real.exp_add, hLdef,
          Real.exp_log (by linarith : (0:ℝ) < (r:ℝ) + 1)]
        ring
      have h3 : (r:ℝ) * (((r:ℝ) + 1) ^ 2)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        nlinarith
      calc (r:ℝ) * Real.exp (-u / 2)
          ≤ (r:ℝ) * Real.exp (-(2 * L)) :=
            mul_le_mul_of_nonneg_left h1 hrpos.le
        _ = (r:ℝ) * (((r:ℝ) + 1) ^ 2)⁻¹ := by rw [h2]
        _ ≤ 1 := h3
    -- excess-tail threshold
    have hthresh : Real.log (CE * ((r + 1 : ℕ) : ℝ)) ≤ u := by
      have hcast : ((r + 1 : ℕ) : ℝ) = (r:ℝ) + 1 := by push_cast; ring
      rw [hcast, Real.log_mul (by linarith : CE ≠ 0)
        (by linarith : (r:ℝ) + 1 ≠ 0)]
      rw [hudef, hlCEdef, hLdef]
      have : (0:ℝ) ≤ Real.log ((r:ℝ) + 1) := Real.log_nonneg (by linarith)
      linarith
    -- instantiate the mgf
    have hmgfrW := hmgf u hu0 r W hr hW1 hm1 hm2
    have hz₁pos : (0:ℝ) < (v - 3) / 2 := by linarith
    have hz₃pos : (0:ℝ) < v - 2 := by linarith
    have htail₁ := tail_upper hC₁1 hu0 hr hW1
      (fun σ hσ hσc => (hmgfrW σ hσ hσc).1) hz₁pos
    have htail₃ := tail_lower hC₁1 hu0 hr hW1 hre
      (fun σ hσ hσc => (hmgfrW σ hσ hσc).2) hz₃pos
    have hB₂bound := hexc r hr u ((v - 1) / 2) hthresh (by linarith)
    -- measurability
    have hirrMeas : MeasurableSet {α : ℝ | Irrational α} := by
      have h : {α : ℝ | Irrational α} = (Set.range ((↑) : ℚ → ℝ))ᶜ := by
        ext x
        simp [Irrational]
      rw [h]
      exact (Set.countable_range _).measurableSet.compl
    have hmeasHat₁ : MeasurableSet {α : ℝ | (v - 3) / 2 < hatSum u W r α} :=
      measurableSet_lt measurable_const (measurable_hatSum u W r)
    have hmeasHat₃ : MeasurableSet {α : ℝ | v - 2 < -(hatSum u W r α)} :=
      measurableSet_lt measurable_const (measurable_hatSum u W r).neg
    have hB₁meas : MeasurableSet {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        (v - 3) / 2 < hatSum u W r α} := by
      have h : {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧ (v - 3) / 2 < hatSum u W r α}
          = Ioo (0:ℝ) 1 ∩ ({α : ℝ | Irrational α}
            ∩ {α : ℝ | (v - 3) / 2 < hatSum u W r α}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioo]
      rw [h]
      exact measurableSet_Ioo.inter (hirrMeas.inter hmeasHat₁)
    have hB₃meas : MeasurableSet {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        v - 2 < -(hatSum u W r α)} := by
      have h : {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧ v - 2 < -(hatSum u W r α)}
          = Ioo (0:ℝ) 1 ∩ ({α : ℝ | Irrational α}
            ∩ {α : ℝ | v - 2 < -(hatSum u W r α)}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioo]
      rw [h]
      exact measurableSet_Ioo.inter (hirrMeas.inter hmeasHat₃)
    -- null rationals
    have hnull : volume {α : ℝ | ¬ Irrational α} = 0 := by
      have h := ae_irrational_volume
      rw [ae_iff] at h
      exact h
    -- subset decomposition
    have hsubset : {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        v < |Real.log (denom α r : ℝ) - lyapunov * r|}
        ⊆ (({α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧ (v - 3) / 2 < hatSum u W r α}
            ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                (v - 1) / 2 < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0})
          ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧ v - 2 < -(hatSum u W r α)})
          ∪ {α : ℝ | ¬ Irrational α} := by
      intro α hα
      by_cases hirr : Irrational α
      · simp only [Set.mem_union, Set.mem_setOf_eq]
        rcases pointwise_split hm2 hα.1 hirr hα.2 with h | h | h
        · exact Or.inl (Or.inl (Or.inl ⟨hα.1, hirr, h⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hα.1, hirr, h⟩))
        · exact Or.inl (Or.inr ⟨hα.1, hirr, h⟩)
      · simp only [Set.mem_union, Set.mem_setOf_eq]
        exact Or.inr hirr
    -- finiteness on subsets of the unit interval
    have hfin : ∀ E : Set ℝ, E ⊆ Ioo (0:ℝ) 1 → volume E ≠ ⊤ := by
      intro E hE
      have h1 : volume E ≤ volume (Ioo (0:ℝ) 1) := measure_mono hE
      rw [Real.volume_Ioo] at h1
      exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne
    have hB₁sub : {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        (v - 3) / 2 < hatSum u W r α} ⊆ Ioo (0:ℝ) 1 := fun α hα => hα.1
    have hB₂sub : {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        (v - 1) / 2 < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0}
        ⊆ Ioo (0:ℝ) 1 := fun α hα => hα.1
    have hB₃sub : {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        v - 2 < -(hatSum u W r α)} ⊆ Ioo (0:ℝ) 1 := fun α hα => hα.1
    -- toReal splitting
    have htoReal : (volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        v < |Real.log (denom α r : ℝ) - lyapunov * r|}).toReal
        ≤ (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              (v - 3) / 2 < hatSum u W r α}).toReal
          + (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              (v - 1) / 2 < ∑ i ∈ Finset.range r,
                max (flog (gaussIter α i) - u) 0}).toReal
          + (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              v - 2 < -(hatSum u W r α)}).toReal := by
      have hne₁ := hfin _ hB₁sub
      have hne₂ := hfin _ hB₂sub
      have hne₃ := hfin _ hB₃sub
      have h1 : volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
          v < |Real.log (denom α r : ℝ) - lyapunov * r|}
          ≤ volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              (v - 3) / 2 < hatSum u W r α}
            + volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              (v - 1) / 2 < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0}
            + volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              v - 2 < -(hatSum u W r α)} := by
        calc volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
            v < |Real.log (denom α r : ℝ) - lyapunov * r|}
            ≤ volume ((({α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  (v - 3) / 2 < hatSum u W r α}
                ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                    (v - 1) / 2 < ∑ i ∈ Finset.range r,
                      max (flog (gaussIter α i) - u) 0})
              ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  v - 2 < -(hatSum u W r α)})
              ∪ {α : ℝ | ¬ Irrational α}) := measure_mono hsubset
          _ ≤ volume ((({α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  (v - 3) / 2 < hatSum u W r α}
                ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                    (v - 1) / 2 < ∑ i ∈ Finset.range r,
                      max (flog (gaussIter α i) - u) 0})
              ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  v - 2 < -(hatSum u W r α)}))
              + volume {α : ℝ | ¬ Irrational α} := measure_union_le _ _
          _ = volume ((({α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  (v - 3) / 2 < hatSum u W r α}
                ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                    (v - 1) / 2 < ∑ i ∈ Finset.range r,
                      max (flog (gaussIter α i) - u) 0})
              ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  v - 2 < -(hatSum u W r α)})) := by
              rw [hnull, add_zero]
          _ ≤ volume ({α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  (v - 3) / 2 < hatSum u W r α}
                ∪ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                    (v - 1) / 2 < ∑ i ∈ Finset.range r,
                      max (flog (gaussIter α i) - u) 0})
              + volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  v - 2 < -(hatSum u W r α)} := measure_union_le _ _
          _ ≤ volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  (v - 3) / 2 < hatSum u W r α}
              + volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  (v - 1) / 2 < ∑ i ∈ Finset.range r,
                    max (flog (gaussIter α i) - u) 0}
              + volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
                  v - 2 < -(hatSum u W r α)} :=
              add_le_add (measure_union_le _ _) le_rfl
      have h2 := ENNReal.toReal_mono
        (by
          exact ENNReal.add_ne_top.mpr
            ⟨ENNReal.add_ne_top.mpr ⟨hne₁, hne₂⟩, hne₃⟩) h1
      rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hne₁, hne₂⟩) hne₃,
        ENNReal.toReal_add hne₁ hne₂] at h2
    -- transfer B₁, B₃ to the Gauss measure
    have hB₁γ : (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        (v - 3) / 2 < hatSum u W r α}).toReal
        ≤ 2 * (Erdos1002.gaussMeasure
            {α : ℝ | (v - 3) / 2 < hatSum u W r α}).toReal := by
      have h1 := volume_le_two_gaussMeasure hB₁meas hB₁sub
      have h2 : (2 : ENNReal) * Erdos1002.gaussMeasure {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧
          Irrational α ∧ (v - 3) / 2 < hatSum u W r α}
          ≤ 2 * Erdos1002.gaussMeasure {α : ℝ | (v - 3) / 2 < hatSum u W r α} :=
        mul_le_mul_right (measure_mono fun α hα => hα.2.2) _
      have h3 := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (le_trans h1 h2)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h3
    have hB₃γ : (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        v - 2 < -(hatSum u W r α)}).toReal
        ≤ 2 * (Erdos1002.gaussMeasure
            {α : ℝ | v - 2 < -(hatSum u W r α)}).toReal := by
      have h1 := volume_le_two_gaussMeasure hB₃meas hB₃sub
      have h2 : (2 : ENNReal) * Erdos1002.gaussMeasure {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧
          Irrational α ∧ v - 2 < -(hatSum u W r α)}
          ≤ 2 * Erdos1002.gaussMeasure {α : ℝ | v - 2 < -(hatSum u W r α)} :=
        mul_le_mul_right (measure_mono fun α hα => hα.2.2) _
      have h3 := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (le_trans h1 h2)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h3
    -- exponent comparisons
    have hC₁ne : C₁ ≠ 0 := ne_of_gt hC₁0
    have hrne : (r:ℝ) ≠ 0 := ne_of_gt hrpos
    have hWpos : (0:ℝ) < (W:ℝ) := by linarith
    have hu3 : (0:ℝ) < u + 3 := by linarith
    have h8W : (0:ℝ) < 8 * (W:ℝ) * (u + 3) :=
      mul_pos (mul_pos (by norm_num) hWpos) hu3
    have hexp_gen : ∀ z : ℝ, 0 < z → v / 4 ≤ z →
        c * m ≤ (3 / 4) * min (z ^ 2 / (4 * C₁ * (r:ℝ)))
          (z / (8 * (W:ℝ) * (u + 3))) := by
      intro z hz hz4
      have hA : (1 / (64 * C₁)) * (v ^ 2 / (r:ℝ)) ≤ z ^ 2 / (4 * C₁ * (r:ℝ)) := by
        have hsq : (v / 4) ^ 2 ≤ z ^ 2 := by nlinarith
        have h1 : (v / 4) ^ 2 / (4 * C₁ * (r:ℝ)) ≤ z ^ 2 / (4 * C₁ * (r:ℝ)) :=
          div_le_div_of_nonneg_right hsq (by positivity)
        have h2 : (1 / (64 * C₁)) * (v ^ 2 / (r:ℝ))
            = (v / 4) ^ 2 / (4 * C₁ * (r:ℝ)) := by
          field_simp
          ring
        rw [h2]
        exact h1
      have hB : (1 / (4 * K₂)) * (v / (1 + L) ^ 2)
          ≤ z / (8 * (W:ℝ) * (u + 3)) := by
        have hup : 8 * (W:ℝ) * (u + 3) ≤ K₂ * (1 + L) ^ 2 := by
          have hW' : (W:ℝ) ≤ (K + 1) * (L + 1) := by nlinarith
          have hu' : u + 3 ≤ (lCE + 7) * (L + 1) := by
            rw [hudef]
            nlinarith [mul_nonneg hlCE0 hL0]
          have hKLpos : (0:ℝ) ≤ 8 * ((K + 1) * (L + 1)) := by nlinarith
          have h8 : 8 * (W:ℝ) * (u + 3)
              ≤ 8 * ((K + 1) * (L + 1)) * ((lCE + 7) * (L + 1)) := by
            have h1 : 8 * (W:ℝ) ≤ 8 * ((K + 1) * (L + 1)) := by linarith
            exact mul_le_mul h1 hu' hu3.le hKLpos
          calc 8 * (W:ℝ) * (u + 3)
              ≤ 8 * ((K + 1) * (L + 1)) * ((lCE + 7) * (L + 1)) := h8
            _ = K₂ * (1 + L) ^ 2 := by rw [hK₂def]; ring
        have heq : (1 / (4 * K₂)) * (v / (1 + L) ^ 2)
            = (v / 4) / (K₂ * (1 + L) ^ 2) := by
          field_simp
        rw [heq]
        exact div_le_div'' hz.le hz4 h8W hup
      have hminmin : c₀ * m ≤ min (z ^ 2 / (4 * C₁ * (r:ℝ)))
          (z / (8 * (W:ℝ) * (u + 3))) := by
        have h1 := min_mul_min_le
          (le_of_lt (div_pos one_pos (by linarith : (0:ℝ) < 64 * C₁)))
          (le_of_lt (div_pos one_pos (by linarith : (0:ℝ) < 4 * K₂)))
          (by positivity : (0:ℝ) ≤ v ^ 2 / (r:ℝ))
          (div_nonneg hv.le (by positivity : (0:ℝ) ≤ (1 + L) ^ 2))
        rw [hc₀def, hmdef]
        exact le_trans h1 (min_le_min hA hB)
      have hc34 : c ≤ (3 / 4) * c₀ := min_le_left _ _
      calc c * m ≤ ((3 / 4) * c₀) * m := mul_le_mul_of_nonneg_right hc34 hm0
        _ = (3 / 4) * (c₀ * m) := by ring
        _ ≤ (3 / 4) * min (z ^ 2 / (4 * C₁ * (r:ℝ)))
            (z / (8 * (W:ℝ) * (u + 3))) := by linarith
    have hexp₁ : -(3 / 4) * min (((v - 3) / 2) ^ 2 / (4 * C₁ * (r:ℝ)))
        (((v - 3) / 2) / (8 * (W:ℝ) * (u + 3))) ≤ -c * m := by
      have h := hexp_gen ((v - 3) / 2) hz₁pos (by linarith)
      linarith
    have hexp₃ : -(3 / 4) * min ((v - 2) ^ 2 / (4 * C₁ * (r:ℝ)))
        ((v - 2) / (8 * (W:ℝ) * (u + 3))) ≤ -c * m := by
      have h := hexp_gen (v - 2) hz₃pos (by linarith)
      linarith
    have hcastlog : Real.log (((r + 1 : ℕ)) : ℝ) = L := by
      have hcast : ((r + 1 : ℕ) : ℝ) = (r:ℝ) + 1 := by push_cast; ring
      rw [hcast, hLdef]
    have hexp₂ : -((v - 1) / 2) / (8 * (Real.log ((r + 1 : ℕ)) + 2)) ≤ -c * m := by
      rw [hcastlog]
      have hden : 8 * (L + 2) ≤ 16 * (1 + L) ^ 2 := by nlinarith [sq_nonneg L]
      have hdenpos : (0:ℝ) < 8 * (L + 2) := by nlinarith
      have h1 : (1 / 64 : ℝ) * (v / (1 + L) ^ 2) ≤ ((v - 1) / 2) / (8 * (L + 2)) := by
        have heq : (1 / 64 : ℝ) * (v / (1 + L) ^ 2)
            = (v / 4) / (16 * (1 + L) ^ 2) := by
          field_simp
          ring
        rw [heq]
        exact div_le_div'' (by linarith) (by linarith) hdenpos hden
      have h2 : c * m ≤ (1 / 64 : ℝ) * (v / (1 + L) ^ 2) := by
        have h3 : m ≤ v / (1 + L) ^ 2 := by rw [hmdef]; exact min_le_right _ _
        have h4 : c * m ≤ (1 / 64 : ℝ) * m := mul_le_mul_of_nonneg_right hc64 hm0
        linarith
      have h6 : c * m ≤ ((v - 1) / 2) / (8 * (L + 2)) := le_trans h2 h1
      have heqneg : -((v - 1) / 2) / (8 * (L + 2))
          = -(((v - 1) / 2) / (8 * (L + 2))) := by ring
      rw [heqneg]
      linarith
    -- final per-set bounds
    have hB₁final : (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        (v - 3) / 2 < hatSum u W r α}).toReal
        ≤ 2 * Real.exp C₁ * Real.exp (-c * m) := by
      calc (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
          (v - 3) / 2 < hatSum u W r α}).toReal
          ≤ 2 * (Erdos1002.gaussMeasure
              {α : ℝ | (v - 3) / 2 < hatSum u W r α}).toReal := hB₁γ
        _ ≤ 2 * (Real.exp C₁ *
              Real.exp (-(3 / 4) * min (((v - 3) / 2) ^ 2 / (4 * C₁ * (r:ℝ)))
                (((v - 3) / 2) / (8 * (W:ℝ) * (u + 3))))) :=
            mul_le_mul_of_nonneg_left htail₁ (by norm_num)
        _ ≤ 2 * (Real.exp C₁ * Real.exp (-c * m)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp₁)
                (Real.exp_pos C₁).le)
              (by norm_num)
        _ = 2 * Real.exp C₁ * Real.exp (-c * m) := by ring
    have hB₃final : (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        v - 2 < -(hatSum u W r α)}).toReal
        ≤ 2 * Real.exp (2 * C₁) * Real.exp (-c * m) := by
      calc (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
          v - 2 < -(hatSum u W r α)}).toReal
          ≤ 2 * (Erdos1002.gaussMeasure
              {α : ℝ | v - 2 < -(hatSum u W r α)}).toReal := hB₃γ
        _ ≤ 2 * (Real.exp (2 * C₁) *
              Real.exp (-(3 / 4) * min ((v - 2) ^ 2 / (4 * C₁ * (r:ℝ)))
                ((v - 2) / (8 * (W:ℝ) * (u + 3))))) :=
            mul_le_mul_of_nonneg_left htail₃ (by norm_num)
        _ ≤ 2 * (Real.exp (2 * C₁) * Real.exp (-c * m)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp₃)
                (Real.exp_pos (2 * C₁)).le)
              (by norm_num)
        _ = 2 * Real.exp (2 * C₁) * Real.exp (-c * m) := by ring
    have hB₂final : (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
        (v - 1) / 2 < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0}).toReal
        ≤ 3 * Real.exp (-c * m) := by
      calc (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
          (v - 1) / 2 < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0}).toReal
          ≤ 3 * Real.exp (-((v - 1) / 2) / (8 * (Real.log ((r + 1 : ℕ)) + 2))) :=
            hB₂bound
        _ ≤ 3 * Real.exp (-c * m) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp₂) (by norm_num)
    -- assemble
    calc (volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        v < |Real.log (denom α r : ℝ) - lyapunov * r|}).toReal
        ≤ (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              (v - 3) / 2 < hatSum u W r α}).toReal
          + (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              (v - 1) / 2 < ∑ i ∈ Finset.range r,
                max (flog (gaussIter α i) - u) 0}).toReal
          + (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Irrational α ∧
              v - 2 < -(hatSum u W r α)}).toReal := htoReal
      _ ≤ 2 * Real.exp C₁ * Real.exp (-c * m) + 3 * Real.exp (-c * m)
          + 2 * Real.exp (2 * C₁) * Real.exp (-c * m) := by
          linarith [hB₁final, hB₂final, hB₃final]
      _ = (2 * Real.exp C₁ + 3 + 2 * Real.exp (2 * C₁)) * Real.exp (-c * m) := by
          ring
      _ ≤ C * Real.exp (-c * m) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have h1 : Real.exp C₁ ≤ Real.exp (2 * C₁) :=
            Real.exp_le_exp.mpr (by linarith)
          have h2 : (0:ℝ) < Real.exp 64 := Real.exp_pos _
          rw [hCdef]
          linarith

end

end LargeDeviation

end Kwon1002
