import Kwon1002.GaussEstimates

/-!
# L34, Lemma 3.4, converse half (display (23))

Target: `descendant_phase_small` of `Kwon1002/GaussEstimates.lean`,
reproduced verbatim as `descendant_phase_small`.

The proof is the standard cylinder-diameter bound, proved here from the
continuant recursion `denom` itself (no library bridge needed):

* `cfNum` is the numerator recursion matching `denom` (`p_0 = 0`,
  `p_1 = 1`, `p_{j+2} = a_{j+2} p_{j+1} + p_j`), and `cfNumPrev`,
  `cfDenPrev` are the shifted (`k-1`) versions, so that the `-1` index is
  available without integer subtraction.
* `cfRep`: the Möbius representation `α = (p_k + p_{k-1} x_k) /
  (q_k + q_{k-1} x_k)`, in cleared-denominator form.
* `cfDet`: `p_k q_{k-1} - p_{k-1} q_k = (-1)^{k+1}`.
* `cf_congr`: the continuants at level `k` depend only on digits `< k`.
* `abs_sub_mul_denom_sq_le_one`: `|α - α'| · q_k² ≤ 1` for two irrationals
  sharing the first `k` digits, the depth-`k` cylinder diameter bound.

Then `|nQ(α-α')| = n|Q| · |α-α'| ≤ (ε q_k²)|α-α'| ≤ ε`, so the constant
`C = 1` works.
-/

open Set

namespace Kwon1002

noncomputable section

/-- Continuant numerators for the same recursion as `denom`:
`p_{-1} = 1`, `p_0 = 0`, `p_{j+1} = a_{j+1} p_j + p_{j-1}`. -/
def cfNum (α : ℝ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => digit α (j + 1) * cfNum α (j + 1) + cfNum α j

/-- `q_{k-1}`, with `q_{-1} = 0`. -/
def cfDenPrev (α : ℝ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => denom α k

/-- `p_{k-1}`, with `p_{-1} = 1`. -/
def cfNumPrev (α : ℝ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => cfNum α k

lemma cfDen_succ (α : ℝ) (k : ℕ) :
    denom α (k + 1) = digit α k * denom α k + cfDenPrev α k := by
  cases k with
  | zero => simp [denom, cfDenPrev]
  | succ j => rfl

lemma cfNum_succ (α : ℝ) (k : ℕ) :
    cfNum α (k + 1) = digit α k * cfNum α k + cfNumPrev α k := by
  cases k with
  | zero => simp [cfNum, cfNumPrev]
  | succ j => rfl

@[simp] lemma cfDenPrev_succ (α : ℝ) (k : ℕ) :
    cfDenPrev α (k + 1) = denom α k := rfl

@[simp] lemma cfNumPrev_succ (α : ℝ) (k : ℕ) :
    cfNumPrev α (k + 1) = cfNum α k := rfl

/-- Continuant denominators are positive. -/
lemma denom_pos {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (k : ℕ) : 0 < denom α k := by
  induction k with
  | zero => simp [denom]
  | succ k ih =>
    rw [cfDen_succ]
    have h1 : 1 ≤ digit α k := one_le_digit hα hirr k
    calc 0 < 1 * 1 := by norm_num
      _ ≤ digit α k * denom α k := Nat.mul_le_mul h1 ih
      _ ≤ digit α k * denom α k + cfDenPrev α k := Nat.le_add_right _ _

/-- **Möbius representation.**  `α = (p_k + p_{k-1} x_k)/(q_k + q_{k-1} x_k)`,
written with the denominator cleared. -/
lemma cfRep {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (k : ℕ) :
    α * ((denom α k : ℝ) + (cfDenPrev α k : ℝ) * gaussIter α k)
      = (cfNum α k : ℝ) + (cfNumPrev α k : ℝ) * gaussIter α k := by
  induction k with
  | zero => norm_num [denom, cfNum, cfDenPrev, cfNumPrev]
  | succ k ih =>
    have hy := gaussIter_mem_Ioo hα hirr k
    have hy0 : gaussIter α k ≠ 0 := ne_of_gt hy.1
    have hyeq : gaussIter α k
        * ((digit α k : ℝ) + gaussIter α (k + 1)) = 1 := by
      rw [← inv_gaussIter_eq hα hirr k]
      field_simp
    rw [cfDen_succ, cfNum_succ, cfDenPrev_succ, cfNumPrev_succ]
    push_cast
    linear_combination ((digit α k : ℝ) + gaussIter α (k + 1)) * ih
      + ((cfNumPrev α k : ℝ) - α * (cfDenPrev α k : ℝ)) * hyeq

/-- **Determinant identity.** `p_k q_{k-1} - p_{k-1} q_k = (-1)^{k+1}`. -/
lemma cfDet (α : ℝ) (k : ℕ) :
    (cfNum α k : ℤ) * (cfDenPrev α k : ℤ)
      - (cfNumPrev α k : ℤ) * (denom α k : ℤ) = (-1) ^ (k + 1) := by
  induction k with
  | zero => simp [denom, cfNum, cfDenPrev, cfNumPrev]
  | succ k ih =>
    rw [cfDen_succ, cfNum_succ, cfDenPrev_succ, cfNumPrev_succ]
    push_cast
    linear_combination -ih

/-- The level-`k` continuants depend only on the digits `< k`. -/
lemma cf_congr (α α' : ℝ) :
    ∀ k : ℕ, (∀ i, i < k → digit α i = digit α' i) →
      denom α k = denom α' k ∧ cfNum α k = cfNum α' k
        ∧ cfDenPrev α k = cfDenPrev α' k ∧ cfNumPrev α k = cfNumPrev α' k := by
  intro k
  induction k with
  | zero => intro _; simp [denom, cfNum, cfDenPrev, cfNumPrev]
  | succ k ih =>
    intro hd
    obtain ⟨h1, h2, h3, h4⟩ := ih fun i hi => hd i (Nat.lt_succ_of_lt hi)
    have hdk : digit α k = digit α' k := hd k (Nat.lt_succ_self k)
    refine ⟨?_, ?_, by simpa using h1, by simpa using h2⟩
    · rw [cfDen_succ, cfDen_succ, h1, hdk, h3]
    · rw [cfNum_succ, cfNum_succ, h2, hdk, h4]

/-- **Cylinder-diameter bound.**  Two irrationals of `(0,1)` sharing the
first `k` continued-fraction digits lie in a common depth-`k` cylinder,
whose length is at most `q_k^{-2}`. -/
lemma abs_sub_mul_denom_sq_le_one {α α' : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hα' : α' ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (hirr' : Irrational α') (k : ℕ)
    (hd : ∀ i, i < k → digit α i = digit α' i) :
    |α - α'| * (denom α k : ℝ) ^ 2 ≤ 1 := by
  obtain ⟨hq, hp, hqp, hpp⟩ := cf_congr α α' k hd
  set q : ℝ := (denom α k : ℝ) with hqdef
  set Q : ℝ := (cfDenPrev α k : ℝ) with hQdef
  set p : ℝ := (cfNum α k : ℝ) with hpdef
  set P : ℝ := (cfNumPrev α k : ℝ) with hPdef
  have hx := gaussIter_mem_Ioo hα hirr k
  have hx' := gaussIter_mem_Ioo hα' hirr' k
  set x : ℝ := gaussIter α k
  set x' : ℝ := gaussIter α' k
  have hrep : α * (q + Q * x) = p + P * x := cfRep hα hirr k
  have hrep' : α' * (q + Q * x') = p + P * x' := by
    have h := cfRep hα' hirr' k
    rw [← hq, ← hp, ← hqp, ← hpp] at h
    exact h
  -- the exact difference identity
  have key : (α - α') * ((q + Q * x) * (q + Q * x'))
      = (x - x') * (P * q - p * Q) := by
    linear_combination (q + Q * x') * hrep - (q + Q * x) * hrep'
  -- the determinant is ±1
  have hdet : P * q - p * Q = -((-1 : ℝ) ^ (k + 1)) := by
    have h := cfDet α k
    have h' : (cfNum α k : ℝ) * (cfDenPrev α k : ℝ)
        - (cfNumPrev α k : ℝ) * (denom α k : ℝ) = (-1 : ℝ) ^ (k + 1) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
    rw [hPdef, hqdef, hpdef, hQdef]
    linarith [h']
  have hdet1 : |P * q - p * Q| = 1 := by
    rw [hdet, abs_neg, abs_pow, abs_neg, abs_one, one_pow]
  -- positivity of the denominators
  have hq1 : (1 : ℝ) ≤ q := by
    rw [hqdef]
    exact_mod_cast denom_pos hα hirr k
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hfacpos : 0 < (q + Q * x) * (q + Q * x') := by
    have h1 : 0 < q + Q * x := by nlinarith [hx.1, hx.2]
    have h2 : 0 < q + Q * x' := by nlinarith [hx'.1, hx'.2]
    exact mul_pos h1 h2
  have hfac : q ^ 2 ≤ (q + Q * x) * (q + Q * x') := by
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hxn : (0 : ℝ) ≤ x := hx.1.le
    have hxn' : (0 : ℝ) ≤ x' := hx'.1.le
    have hexp : (q + Q * x) * (q + Q * x') - q ^ 2
        = q * (Q * x') + (Q * x) * q + (Q * Q) * (x * x') := by ring
    have t1 : 0 ≤ q * (Q * x') := mul_nonneg hq0 (mul_nonneg hQ0 hxn')
    have t2 : 0 ≤ (Q * x) * q := mul_nonneg (mul_nonneg hQ0 hxn) hq0
    have t3 : 0 ≤ (Q * Q) * (x * x') :=
      mul_nonneg (mul_nonneg hQ0 hQ0) (mul_nonneg hxn hxn')
    linarith
  -- take absolute values in `key`
  have habs : |α - α'| * ((q + Q * x) * (q + Q * x')) = |x - x'| := by
    have h := congrArg abs key
    rw [abs_mul (α - α') ((q + Q * x) * (q + Q * x')), abs_of_pos hfacpos,
      abs_mul (x - x') (P * q - p * Q), hdet1, mul_one] at h
    exact h
  have hxx : |x - x'| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hx.1, hx.2, hx'.1, hx'.2],
      by linarith [hx.1, hx.2, hx'.1, hx'.2]⟩
  nlinarith [abs_nonneg (α - α'), hfac, habs, hxx]

/-- **Lemma 3.4, converse half, display (23).**

Hypothesis is agreement of the first `k` digits `a_1 … a_k`, i.e. membership
in a common depth-`k` cylinder, which is exactly the setting of (23): the
bound involves `q_k`, which depends only on those digits. (An earlier
version fixed one extra digit; that was gratuitous, the proof never used
it, as the call to `abs_sub_mul_denom_sq_le_one` below shows.) -/
theorem descendant_phase_small :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (Q : ℤ) (k : ℕ) (α α' : ℝ),
      α ∈ Set.Ioo (0 : ℝ) 1 → α' ∈ Set.Ioo (0 : ℝ) 1 →
      Irrational α → Irrational α' →
      (∀ i < k, digit α i = digit α' i) →
      (ε⁻¹ * (n : ℝ) * |(Q : ℝ)| ≤ (denom α k : ℝ) ^ 2) →
      |(n : ℝ) * (Q : ℝ) * (α - α')| ≤ C * ε := by
  refine ⟨1, one_pos, ?_⟩
  intro ε hε n Q k α α' hα hα' hirr hirr' hdig hbound
  have hdiam : |α - α'| * (denom α k : ℝ) ^ 2 ≤ 1 :=
    abs_sub_mul_denom_sq_le_one hα hα' hirr hirr' k hdig
  have hb : (n : ℝ) * |(Q : ℝ)| ≤ ε * (denom α k : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hbound hε.le
    calc (n : ℝ) * |(Q : ℝ)| = ε * (ε⁻¹ * (n : ℝ) * |(Q : ℝ)|) := by
          field_simp
      _ ≤ ε * (denom α k : ℝ) ^ 2 := h
  have hrw : |(n : ℝ) * (Q : ℝ) * (α - α')|
      = (n : ℝ) * |(Q : ℝ)| * |α - α'| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  rw [hrw]
  calc (n : ℝ) * |(Q : ℝ)| * |α - α'|
      ≤ (ε * (denom α k : ℝ) ^ 2) * |α - α'| :=
        mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = ε * (|α - α'| * (denom α k : ℝ) ^ 2) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hdiam hε.le
    _ = 1 * ε := by ring

end

end Kwon1002
