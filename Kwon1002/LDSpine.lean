import Kwon1002.CharacterReduction
import Kwon1002.LDObservable

/-!
# Large deviations, stage A1: the spine `log q_r = Σ (−log x_i) + O(log 2)`

`betaProd α k = x_0 ⋯ x_k = |q_k α − p_k|` (via
`CharacterReduction.betaProd_eq_convergent`), and the classical exact
identity `q_{k+1} β_k + q_k β_{k+1} = 1` (from the continuant determinant
`p_{k+1} q_k − p_k q_{k+1} = (−1)^k`) sandwiches
`1/(2 q_{k+1}) ≤ β_k ≤ 1/q_{k+1}`.  Taking logarithms turns the continuant
into a Birkhoff sum with additive error exactly `log 2`:

`log q_r ≤ Σ_{i<r} (−log x_i) ≤ log q_r + log 2`,

whence `|log q_r − λ r| ≤ |Σ_{i<r} flog x_i| + log 2`.
-/

open Set

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-- The continuant determinant identity `p_{k+1} q_k − p_k q_{k+1} = (−1)^k`
(pure recursion, no hypotheses on `α`). -/
lemma numer_denom_det (α : ℝ) (k : ℕ) :
    (numer α (k + 1) : ℤ) * (denom α k : ℤ)
      - (numer α k : ℤ) * (denom α (k + 1) : ℤ) = (-1) ^ k := by
  induction k with
  | zero =>
    show (numer α 1 : ℤ) * (denom α 0 : ℤ)
        - (numer α 0 : ℤ) * (denom α 1 : ℤ) = (-1) ^ 0
    have h1 : numer α 1 = 1 := rfl
    have h0 : numer α 0 = 0 := rfl
    have hd0 : denom α 0 = 1 := rfl
    rw [h1, h0, hd0]
    norm_num
  | succ k ih =>
    show (numer α (k + 2) : ℤ) * (denom α (k + 1) : ℤ)
        - (numer α (k + 1) : ℤ) * (denom α (k + 2) : ℤ) = (-1) ^ (k + 1)
    have hn : numer α (k + 2) = digit α (k + 1) * numer α (k + 1) + numer α k := rfl
    have hd : denom α (k + 2) = digit α (k + 1) * denom α (k + 1) + denom α k := rfl
    rw [hn, hd]
    push_cast
    linear_combination (-1 : ℤ) * ih

/-- Continuant denominators are at least `1` along irrational orbits. -/
lemma one_le_denom {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (j : ℕ) : 1 ≤ denom α j := by
  have key : ∀ j : ℕ, 1 ≤ denom α j ∧ 1 ≤ denom α (j + 1) := by
    intro j
    induction j with
    | zero =>
      refine ⟨(rfl : denom α 0 = 1).ge, ?_⟩
      have h1 : denom α 1 = digit α 0 := rfl
      rw [h1]
      exact one_le_digit hα hirr 0
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      show 1 ≤ denom α (j + 2)
      have h : denom α (j + 2) = digit α (j + 1) * denom α (j + 1) + denom α j := rfl
      rw [h]
      exact le_trans ih.1 (Nat.le_add_left _ _)
  exact (key j).1

/-- Continuant denominators are monotone along irrational orbits. -/
lemma denom_le_denom_succ {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (j : ℕ) : denom α j ≤ denom α (j + 1) := by
  cases j with
  | zero =>
    show denom α 0 ≤ denom α 1
    have h0 : denom α 0 = 1 := rfl
    have h1 : denom α 1 = digit α 0 := rfl
    rw [h0, h1]
    exact one_le_digit hα hirr 0
  | succ j =>
    show denom α (j + 1) ≤ denom α (j + 2)
    have h : denom α (j + 2) = digit α (j + 1) * denom α (j + 1) + denom α j := rfl
    rw [h]
    have ha := one_le_digit hα hirr (j + 1)
    exact le_trans (le_mul_of_one_le_left (Nat.zero_le _) ha) (Nat.le_add_right _ _)

/-- `β_k = x_0 ⋯ x_k > 0`. -/
lemma betaProd_pos {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (k : ℕ) : 0 < betaProd α k := by
  have h : betaProd α k = ∏ i ∈ Finset.range (k + 1), gaussIter α i := rfl
  rw [h]
  exact Finset.prod_pos fun i _ => (gaussIter_mem_Ioo hα hirr i).1

/-- The exact classical identity `q_{k+1} β_k + q_k β_{k+1} = 1`. -/
lemma denom_mul_betaProd_identity {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (k : ℕ) :
    (denom α (k + 1) : ℝ) * betaProd α k
      + (denom α k : ℝ) * betaProd α (k + 1) = 1 := by
  have hb1 := betaProd_eq_convergent hα hirr k
  have hb2 := betaProd_eq_convergent hα hirr (k + 1)
  have hdetR : (numer α (k + 1) : ℝ) * (denom α k : ℝ)
      - (numer α k : ℝ) * (denom α (k + 1) : ℝ) = (-1) ^ k := by
    exact_mod_cast numer_denom_det α k
  have hpow : ((-1 : ℝ)) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hb1, hb2]
  linear_combination ((-1 : ℝ)) ^ k * hdetR + hpow

/-- Upper half of the sandwich: `β_k ≤ 1/q_{k+1}`. -/
lemma betaProd_le_inv_denom {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (k : ℕ) :
    betaProd α k ≤ 1 / (denom α (k + 1) : ℝ) := by
  have hid := denom_mul_betaProd_identity hα hirr k
  have hq1 : (1 : ℝ) ≤ (denom α (k + 1) : ℝ) := by
    exact_mod_cast one_le_denom hα hirr (k + 1)
  have hqpos : (0 : ℝ) < (denom α (k + 1) : ℝ) := lt_of_lt_of_le one_pos hq1
  have hnn : 0 ≤ (denom α k : ℝ) * betaProd α (k + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (betaProd_pos hα hirr (k + 1)).le
  rw [le_div_iff₀ hqpos]
  nlinarith [hid, hnn]

/-- Lower half of the sandwich: `1/(2 q_{k+1}) ≤ β_k`. -/
lemma inv_denom_le_betaProd {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (k : ℕ) :
    1 / (2 * (denom α (k + 1) : ℝ)) ≤ betaProd α k := by
  have hid := denom_mul_betaProd_identity hα hirr k
  have hq1 : (1 : ℝ) ≤ (denom α (k + 1) : ℝ) := by
    exact_mod_cast one_le_denom hα hirr (k + 1)
  have hqpos : (0 : ℝ) < (denom α (k + 1) : ℝ) := lt_of_lt_of_le one_pos hq1
  have hqle : (denom α k : ℝ) ≤ (denom α (k + 1) : ℝ) := by
    exact_mod_cast denom_le_denom_succ hα hirr k
  have hbpos := betaProd_pos hα hirr k
  have hx := gaussIter_mem_Ioo hα hirr (k + 1)
  have hble : betaProd α (k + 1) ≤ betaProd α k := by
    rw [betaProd_succ α k]
    nlinarith [hx.2, hbpos]
  have h2 : 1 ≤ 2 * (denom α (k + 1) : ℝ) * betaProd α k := by
    nlinarith [hid, mul_nonneg (sub_nonneg.mpr hqle) hbpos.le,
      mul_nonneg (by positivity : (0 : ℝ) ≤ (denom α k : ℝ)) (sub_nonneg.mpr hble)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h2]

/-- **The spine.**  For `r ≥ 1`, the log-continuant is the Birkhoff sum of
`−log x_i` up to an additive error in `[−log 2, 0]`:
`log q_r ≤ Σ_{i<r} (−log x_i) ≤ log q_r + log 2`. -/
theorem log_denom_birkhoff_sandwich {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (r : ℕ) (hr : 1 ≤ r) :
    Real.log (denom α r : ℝ)
        ≤ ∑ i ∈ Finset.range r, (-Real.log (gaussIter α i))
      ∧ ∑ i ∈ Finset.range r, (-Real.log (gaussIter α i))
        ≤ Real.log (denom α r : ℝ) + Real.log 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hne : ∀ i ∈ Finset.range (k + 1), gaussIter α i ≠ 0 := fun i _ =>
    (gaussIter_mem_Ioo hα hirr i).1.ne'
  have hlogprod : Real.log (betaProd α k)
      = ∑ i ∈ Finset.range (k + 1), Real.log (gaussIter α i) := by
    have hprod : betaProd α k = ∏ i ∈ Finset.range (k + 1), gaussIter α i := rfl
    rw [hprod, Real.log_prod hne]
  have hsum : ∑ i ∈ Finset.range (k + 1), (-Real.log (gaussIter α i))
      = -Real.log (betaProd α k) := by
    rw [Finset.sum_neg_distrib, hlogprod]
  have hq1 : (1 : ℝ) ≤ (denom α (k + 1) : ℝ) := by
    exact_mod_cast one_le_denom hα hirr (k + 1)
  have hqpos : (0 : ℝ) < (denom α (k + 1) : ℝ) := lt_of_lt_of_le one_pos hq1
  have hbpos := betaProd_pos hα hirr k
  have h1 : Real.log (betaProd α k) ≤ Real.log (1 / (denom α (k + 1) : ℝ)) :=
    Real.log_le_log hbpos (betaProd_le_inv_denom hα hirr k)
  have h2 : Real.log (1 / (2 * (denom α (k + 1) : ℝ))) ≤ Real.log (betaProd α k) :=
    Real.log_le_log (by positivity) (inv_denom_le_betaProd hα hirr k)
  have e1 : Real.log (1 / (denom α (k + 1) : ℝ)) = -Real.log (denom α (k + 1) : ℝ) := by
    rw [one_div, Real.log_inv]
  have e2 : Real.log (1 / (2 * (denom α (k + 1) : ℝ)))
      = -(Real.log 2 + Real.log (denom α (k + 1) : ℝ)) := by
    rw [one_div, Real.log_inv, Real.log_mul two_ne_zero (ne_of_gt hqpos)]
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨by rw [hsum]; linarith, by rw [hsum]; linarith⟩

/-- **The spine, centered.**  `|log q_r − λ r| ≤ |Σ_{i<r} flog x_i| + log 2`
for every `r` (including `r = 0`). -/
theorem abs_log_denom_sub_lyapunov_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (r : ℕ) :
    |Real.log (denom α r : ℝ) - lyapunov * r|
      ≤ |∑ i ∈ Finset.range r, flog (gaussIter α i)| + Real.log 2 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    have hd : denom α 0 = 1 := rfl
    simp [hd]
    exact hlog2
  · obtain ⟨hs1, hs2⟩ := log_denom_birkhoff_sandwich hα hirr r hrpos
    have hF : ∑ i ∈ Finset.range r, flog (gaussIter α i)
        = (∑ i ∈ Finset.range r, (-Real.log (gaussIter α i))) - lyapunov * (r : ℝ) := by
      simp only [flog]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hF]
    have h1 := le_abs_self
      ((∑ i ∈ Finset.range r, (-Real.log (gaussIter α i))) - lyapunov * (r : ℝ))
    have h2 := neg_le_abs
      ((∑ i ∈ Finset.range r, (-Real.log (gaussIter α i))) - lyapunov * (r : ℝ))
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith

end

end LargeDeviation

end Kwon1002
