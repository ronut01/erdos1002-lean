import Kwon1002.Master
import Kwon1002.LDMain
import Kwon1002.OneLevelLaw

/-!
# §7, the index-set bridge: `τ_n = m_n + O(H)`, and `Section7EndTerms` closed

`Kwon1002/Master.lean` reduced the third hypothesis of the master theorem to
`Master.Section7Bridge c`, the passage between the *random* §7 bulk
`Marks.bulkIndices c α n = {j < τ_n : c·H ≤ j}` and the *deterministic* §4 bulk
`Section4.bulkJ n = {j : 200H ≤ j ≤ m_n − 200H}` of display (19).  This module
proves it, so **hypothesis 3 of the master theorem is discharged**
(`section7EndTerms_holds`, `erdos1002Conclusion_of_principal_and_prop64`).

## The argument

The two index sets disagree only near their two boundaries.

* At the **bottom** they disagree over at most `max(⌈c·H⌉, ⌈200H⌉)` levels: one
  set trims at `c·H`, the other at `200H`.  This is deterministic.
* At the **top** they disagree over the levels between `m_n − 200H` and `τ_n`.
  This is where the stopping time enters, and it is the only probabilistic
  input.

Part B makes the top boundary deterministic *on a large event*.  The height
recursion (2) and display (7) give `N_j = nβ_{j−1} − E_j` with `0 ≤ E_j ≤ E*`,
and the classical sandwich `1/(2q_j) ≤ β_{j−1} ≤ 1/q_j` (`LDSpine`) turns that
into a two-sided bracket for the hitting time `τ_n = min{j : N_j = 0}`:

* `q_j > n ⟹ N_j ≤ n/q_j < 1 ⟹ N_j = 0`, so `τ_n ≤ j`;
* `N_j = 0 ⟹ nβ_{j−1} ≤ E* ⟹ q_j ≥ n/(2E*)`, so `q_j < n/(2E*) ⟹ τ_n > j`.

Reading those at the two deterministic indices `m_n ± A_n`, with
`A_n = ⌈(H + log 2E* + 2λ)/λ⌉ = H + O(1)`, and feeding in the Lévy window
`e^{λj ± H}` of display (20) — `LargeDeviation.display20_of_pos`, **proved** —
gives `m_n − A_n < τ_n ≤ m_n + A_n` off a set of measure `≤ 2C e^{−c√L}`.

Part C confines the symmetric difference of the two index sets to a
deterministic window of `2D_n + 2A_n + 1` levels (`D_n` the longer bottom trim),
Part D caps every summand by Proposition 2.2's absolute constant
`C₀ = E*/2 + 5/8` (`Kwon1002.principal_term`), and Part E shows the resulting
bound `C₀·(2D_n + 2A_n + 1)/L = O(H/L) = O(L^{−1/4})` is `o(1)`.  Part F
assembles the three into convergence in probability.

## What is *not* used

No property of `B_j` beyond the uniform bound of Proposition 2.2, and no
input from §§4-6: in particular this module is independent of Proposition 6.4,
of Corollary 5.3, and of the two residuals of `CorFinal`.  Everything below is
proved outright; `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]` on every declaration in this file.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace Section7

noncomputable section

/-! ## Part A, the stopping time as a hitting time -/

/-- The height sequence vanishes at every time at or after the stopping time. -/
lemma heightSeq_eq_zero_of_stoppingTime_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (h : stoppingTime α n ≤ j) :
    heightSeq α n j = 0 := by
  have hne : {j | heightSeq α n j = 0}.Nonempty :=
    ⟨n, heightSeq_self_eq_zero α hα hirr n⟩
  have hmem : heightSeq α n (stoppingTime α n) = 0 := Nat.sInf_mem hne
  have key : ∀ k : ℕ, heightSeq α n (stoppingTime α n + k) = 0 := by
    intro k
    induction k with
    | zero => simpa using hmem
    | succ k ih =>
      have : stoppingTime α n + (k + 1) = (stoppingTime α n + k) + 1 := by omega
      rw [this]
      exact heightSeq_succ_of_eq_zero α n _ ih
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact key k

/-- `1 ≤ E*`: the reciprocal-Fibonacci sum contains the term `1/F_1 = 1`. -/
lemma one_le_Estar : (1 : ℝ) ≤ Estar := by
  have h := partial_le_EstarD 1
  simpa using h

lemma Estar_pos : (0 : ℝ) < Estar := lt_of_lt_of_le one_pos one_le_Estar

/-- **Upper bracket.**  Once the continuant `q_j` has passed `n`, the height
`N_j = nβ_{j-1} − E_j ≤ n/q_j` is below `1`, hence zero. -/
lemma heightSeq_eq_zero_of_lt_denom {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hj : 1 ≤ j) (h : (n : ℝ) < (denom α j : ℝ)) :
    heightSeq α n j = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hq1 : (1 : ℝ) ≤ (denom α (k + 1) : ℝ) := by
    exact_mod_cast LargeDeviation.one_le_denom hα hirr (k + 1)
  have hqpos : (0 : ℝ) < (denom α (k + 1) : ℝ) := lt_of_lt_of_le one_pos hq1
  have hE : 0 ≤ heightError α n (k + 1) :=
    (Set.mem_Icc.mp (heightError_mem_Icc α hα hirr n (k + 1))).1
  have hrec : heightError α n (k + 1)
      = (n : ℝ) * betaProd α k - (heightSeq α n (k + 1) : ℝ) := heightError_succ_eq α n k
  have hbeta : betaProd α k ≤ 1 / (denom α (k + 1) : ℝ) :=
    LargeDeviation.betaProd_le_inv_denom hα hirr k
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hlt : (heightSeq α n (k + 1) : ℝ) < 1 := by
    have h1 : (heightSeq α n (k + 1) : ℝ) ≤ (n : ℝ) * betaProd α k := by linarith
    have h2 : (n : ℝ) * betaProd α k ≤ (n : ℝ) * (1 / (denom α (k + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left hbeta hnnn
    have h3 : (n : ℝ) * (1 / (denom α (k + 1) : ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one hqpos]; exact h
    linarith
  have : heightSeq α n (k + 1) < 1 := by exact_mod_cast hlt
  omega

/-- **Lower bracket.**  If the height has already vanished at time `j ≥ 1` then
`nβ_{j-1} ≤ E*`, and `β_{j-1} ≥ 1/(2q_j)` forces `q_j ≥ n/(2E*)`. -/
lemma le_denom_of_heightSeq_eq_zero {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hj : 1 ≤ j) (h : heightSeq α n j = 0) :
    (n : ℝ) ≤ 2 * Estar * (denom α j : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hq1 : (1 : ℝ) ≤ (denom α (k + 1) : ℝ) := by
    exact_mod_cast LargeDeviation.one_le_denom hα hirr (k + 1)
  have hqpos : (0 : ℝ) < (denom α (k + 1) : ℝ) := lt_of_lt_of_le one_pos hq1
  have hE : heightError α n (k + 1) ≤ Estar :=
    (Set.mem_Icc.mp (heightError_mem_Icc α hα hirr n (k + 1))).2
  have hrec : heightError α n (k + 1)
      = (n : ℝ) * betaProd α k - (heightSeq α n (k + 1) : ℝ) := heightError_succ_eq α n k
  have hzero : (heightSeq α n (k + 1) : ℝ) = 0 := by rw [h]; norm_num
  have hnb : (n : ℝ) * betaProd α k ≤ Estar := by rw [hrec, hzero] at hE; linarith
  have hbeta : 1 / (2 * (denom α (k + 1) : ℝ)) ≤ betaProd α k :=
    LargeDeviation.inv_denom_le_betaProd hα hirr k
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have h2 : (n : ℝ) * (1 / (2 * (denom α (k + 1) : ℝ))) ≤ Estar :=
    le_trans (mul_le_mul_of_nonneg_left hbeta hnnn) hnb
  rw [mul_one_div, div_le_iff₀ (by positivity)] at h2
  linarith

/-! ## Part B, the deterministic sandwich `m_n − A_n < τ_n ≤ m_n + A_n` -/

/-- `A_n = ⌈(H + log(2E*) + 2λ)/λ⌉`, the deviation the two brackets need.  It is
`H + O(1)`, so `A_n/L → 0`. -/
def trimAmt (n : ℕ) : ℕ :=
  ⌈(Hscale n + Real.log (2 * Estar) + 2 * lyapunov) / lyapunov⌉₊

lemma log_two_Estar_pos : 0 < Real.log (2 * Estar) := by
  have h := one_le_Estar
  exact Real.log_pos (by linarith)

lemma log_two_Estar_le : Real.log (2 * Estar) ≤ 8 := by
  have h1 : Estar ≤ 9 / 2 := Estar_le_nine_halves
  have h2 : Real.log (2 * Estar) ≤ 2 * Estar - 1 :=
    Real.log_le_sub_one_of_pos (by linarith [Estar_pos])
  linarith

lemma one_le_trimAmt (n : ℕ) (hH : 0 ≤ Hscale n) : 1 ≤ trimAmt n := by
  have hlam := LargeDeviation.lyapunov_pos'
  have hpos : 0 < (Hscale n + Real.log (2 * Estar) + 2 * lyapunov) / lyapunov := by
    have := log_two_Estar_pos
    positivity
  exact Nat.ceil_pos.mpr hpos

lemma le_lyapunov_mul_trimAmt (n : ℕ) :
    Hscale n + Real.log (2 * Estar) + 2 * lyapunov ≤ lyapunov * (trimAmt n : ℝ) := by
  have hlam := LargeDeviation.lyapunov_pos'
  have h := Nat.le_ceil ((Hscale n + Real.log (2 * Estar) + 2 * lyapunov) / lyapunov)
  rw [← trimAmt] at h
  rw [mul_comm lyapunov ((trimAmt n : ℕ) : ℝ)]
  exact (div_le_iff₀ hlam).mp h

lemma trimAmt_le (n : ℕ) (hH : 0 ≤ Hscale n) : (trimAmt n : ℝ) ≤ Hscale n + 13 := by
  have hlam1 := LargeDeviation.one_lt_lyapunov
  have hlam2 := LargeDeviation.lyapunov_lt_two
  have hlam := LargeDeviation.lyapunov_pos'
  have hE := log_two_Estar_le
  have hE0 := log_two_Estar_pos
  have hnum : 0 ≤ Hscale n + Real.log (2 * Estar) + 2 * lyapunov := by linarith
  have hdiv : (Hscale n + Real.log (2 * Estar) + 2 * lyapunov) / lyapunov
      ≤ Hscale n + Real.log (2 * Estar) + 2 * lyapunov := by
    rw [div_le_iff₀ hlam]
    nlinarith
  have hceil : (trimAmt n : ℝ)
      < (Hscale n + Real.log (2 * Estar) + 2 * lyapunov) / lyapunov + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

/-- **The sandwich.**  With the Lévy window at the two deterministic indices
`m_n ± A_n`, the §7 stopping time sits within `A_n` of `m_n`. -/
theorem stoppingTime_sandwich {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    {n : ℕ} (hn : 1 ≤ n) (hA : trimAmt n ≤ mIndex n) (hone : 1 ≤ mIndex n - trimAmt n)
    (hup : Real.exp (lyapunov * ((mIndex n + trimAmt n : ℕ) : ℝ) - 1 * Hscale n)
        ≤ (denom α (mIndex n + trimAmt n) : ℝ))
    (hdown : (denom α (mIndex n - trimAmt n) : ℝ)
        ≤ Real.exp (lyapunov * ((mIndex n - trimAmt n : ℕ) : ℝ) + 1 * Hscale n)) :
    mIndex n - trimAmt n < stoppingTime α n ∧ stoppingTime α n ≤ mIndex n + trimAmt n := by
  have hlam := LargeDeviation.lyapunov_pos'
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hexpL : Real.exp (Lnorm n) = (n : ℝ) := Real.exp_log hn0
  have hL0 : 0 ≤ Lnorm n := Real.log_nonneg hnR
  have hEc := le_lyapunov_mul_trimAmt n
  have hEc0 := log_two_Estar_pos
  -- `λ m_n` brackets `L`
  have hmle : lyapunov * (mIndex n : ℝ) ≤ Lnorm n := by
    have h : (mIndex n : ℝ) ≤ Lnorm n / lyapunov :=
      Nat.floor_le (div_nonneg hL0 hlam.le)
    rw [← le_div_iff₀' hlam]; exact h
  have hmgt : Lnorm n - lyapunov < lyapunov * (mIndex n : ℝ) := by
    have h : Lnorm n / lyapunov < (mIndex n : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hlam] at h
    nlinarith
  constructor
  · -- lower bracket
    by_contra hcon
    push_neg at hcon
    have hz : heightSeq α n (mIndex n - trimAmt n) = 0 :=
      heightSeq_eq_zero_of_stoppingTime_le hα hirr n _ hcon
    have hkey := le_denom_of_heightSeq_eq_zero hα hirr n _ hone hz
    have hcast : ((mIndex n - trimAmt n : ℕ) : ℝ) = (mIndex n : ℝ) - (trimAmt n : ℝ) :=
      Nat.cast_sub hA
    have hchain : lyapunov * ((mIndex n - trimAmt n : ℕ) : ℝ) + 1 * Hscale n
        ≤ Lnorm n - Real.log (2 * Estar) - 2 * lyapunov := by
      rw [hcast, mul_sub]
      nlinarith
    have hq : (denom α (mIndex n - trimAmt n) : ℝ)
        ≤ Real.exp (Lnorm n - Real.log (2 * Estar) - 2 * lyapunov) :=
      le_trans hdown (Real.exp_le_exp.mpr hchain)
    have hEpos : (0 : ℝ) < 2 * Estar := by linarith [Estar_pos]
    have hexpE : Real.exp (Real.log (2 * Estar)) = 2 * Estar := Real.exp_log hEpos
    have hfinal : 2 * Estar * (denom α (mIndex n - trimAmt n) : ℝ)
        ≤ Real.exp (Lnorm n - 2 * lyapunov) := by
      calc 2 * Estar * (denom α (mIndex n - trimAmt n) : ℝ)
          ≤ 2 * Estar * Real.exp (Lnorm n - Real.log (2 * Estar) - 2 * lyapunov) :=
            mul_le_mul_of_nonneg_left hq hEpos.le
        _ = Real.exp (Real.log (2 * Estar))
              * Real.exp (Lnorm n - Real.log (2 * Estar) - 2 * lyapunov) := by rw [hexpE]
        _ = Real.exp (Lnorm n - 2 * lyapunov) := by rw [← Real.exp_add]; ring_nf
    have hlt : Real.exp (Lnorm n - 2 * lyapunov) < (n : ℝ) := by
      rw [← hexpL]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  · -- upper bracket
    have hcast : ((mIndex n + trimAmt n : ℕ) : ℝ) = (mIndex n : ℝ) + (trimAmt n : ℝ) := by
      push_cast; ring
    have hchain : Lnorm n
        < lyapunov * ((mIndex n + trimAmt n : ℕ) : ℝ) - 1 * Hscale n := by
      rw [hcast, mul_add]
      nlinarith
    have hbig : (n : ℝ) < (denom α (mIndex n + trimAmt n) : ℝ) := by
      refine lt_of_lt_of_le ?_ hup
      rw [← hexpL]
      exact Real.exp_lt_exp.mpr hchain
    have h1 : 1 ≤ mIndex n + trimAmt n := by omega
    exact Nat.sInf_le (heightSeq_eq_zero_of_lt_denom hα hirr n _ h1 hbig)

/-! ## Part C, the symmetric difference of the two index sets -/

/-- The length of the two lower boundaries: the §7 trim `c·H` and the §4 trim
`200H`, whichever is longer. -/
def bdryLen (c : ℝ) (n : ℕ) : ℕ := max ⌈c * Hscale n⌉₊ ⌈200 * Hscale n⌉₊

/-- The deterministic window that contains the symmetric difference: the two
lower boundaries, and a window of radius `A_n + D_n` around `m_n`. -/
def diffWindow (c : ℝ) (n : ℕ) : Finset ℕ :=
  Finset.range (bdryLen c n)
    ∪ Finset.Ico (mIndex n - (trimAmt n + bdryLen c n)) (mIndex n + trimAmt n + 1)

lemma card_diffWindow_le (c : ℝ) (n : ℕ) :
    (diffWindow c n).card ≤ 2 * bdryLen c n + 2 * trimAmt n + 1 := by
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_range, Nat.card_Ico]
  omega

private lemma nat_sub_le_of_cast_lt {M D j : ℕ} (h : (M : ℝ) - (D : ℝ) < (j : ℝ)) :
    M - D ≤ j := by
  have h1 : (M : ℝ) < (j : ℝ) + (D : ℝ) := by linarith
  have h2 : M < j + D := by exact_mod_cast h1
  omega

/-- **The symmetric difference is confined to the window.**  Everything the two
index sets disagree about lies below the longer of the two lower trims, or
within `A_n + D_n` of `m_n`. -/
theorem sdiff_subset_diffWindow {α : ℝ} (c : ℝ) (n : ℕ) (hH : 0 ≤ Hscale n)
    (hlow : mIndex n - trimAmt n < stoppingTime α n)
    (hhigh : stoppingTime α n ≤ mIndex n + trimAmt n) :
    bulkIndices c α n \ bulkJ n ⊆ diffWindow c n
      ∧ bulkJ n \ bulkIndices c α n ⊆ diffWindow c n := by
  classical
  have hc200 : ⌈200 * Hscale n⌉₊ ≤ bdryLen c n := le_max_right _ _
  have hcc : ⌈c * Hscale n⌉₊ ≤ bdryLen c n := le_max_left _ _
  have h200R : 200 * Hscale n ≤ (bdryLen c n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hc200)
  constructor
  · intro j hj
    rw [Finset.mem_sdiff, bulkIndices, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨⟨hjt, hjc⟩, hjQ⟩ := hj
    rw [diffWindow, Finset.mem_union]
    by_cases hlt : (j : ℝ) < 200 * Hscale n
    · left
      rw [Finset.mem_range]
      have : (j : ℝ) < (bdryLen c n : ℝ) := lt_of_lt_of_le hlt h200R
      exact_mod_cast this
    · right
      push_neg at hlt
      rw [bulkJ, Finset.mem_filter, Finset.mem_range] at hjQ
      push_neg at hjQ
      have hgt : (mIndex n : ℝ) - 200 * Hscale n < (j : ℝ) := by
        by_cases hjm : j < mIndex n + 1
        · exact hjQ hjm hlt
        · have : (mIndex n : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.not_lt.mp hjm
          linarith
      have hge : mIndex n - bdryLen c n ≤ j :=
        nat_sub_le_of_cast_lt (by linarith)
      rw [Finset.mem_Ico]
      have hle : j ≤ mIndex n + trimAmt n := by omega
      omega
  · intro j hj
    rw [Finset.mem_sdiff, bulkJ, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨⟨hjm, _h200, hjup⟩, hjP⟩ := hj
    rw [diffWindow, Finset.mem_union]
    by_cases hlt : (j : ℝ) < c * Hscale n
    · left
      rw [Finset.mem_range]
      have hcR : c * Hscale n ≤ (bdryLen c n : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hcc)
      have : (j : ℝ) < (bdryLen c n : ℝ) := lt_of_lt_of_le hlt hcR
      exact_mod_cast this
    · right
      push_neg at hlt
      rw [bulkIndices, Finset.mem_filter, Finset.mem_range] at hjP
      push_neg at hjP
      have hjt : stoppingTime α n ≤ j :=
        Nat.not_lt.mp (fun h => absurd (hjP h) (not_lt.mpr hlt))
      rw [Finset.mem_Ico]
      omega

/-! ## Part D, the bridge estimate on the good event -/

lemma Czero_nonneg : (0 : ℝ) ≤ Czero := by
  have := Estar_pos
  rw [Czero]; linarith

/-- **The bridge estimate.**  On the event that the sandwich holds, the two
remainder sums differ by at most `C₀·|Δ|/L`, and `|Δ| = O(H)`. -/
theorem abs_remainderSum_diff_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (c : ℝ) (n : ℕ) (hH : 0 ≤ Hscale n) (hL : 0 < Lnorm n)
    (hlow : mIndex n - trimAmt n < stoppingTime α n)
    (hhigh : stoppingTime α n ≤ mIndex n + trimAmt n) :
    |Master.randRemainderSum c α n - Master.detRemainderSum α n|
      ≤ (1 / Lnorm n) * (2 * Czero * (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1)) := by
  classical
  set g : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * Bremainder α n j with hg
  set P : Finset ℕ := bulkIndices c α n with hP
  set Q : Finset ℕ := bulkJ n with hQ
  obtain ⟨hPQ, hQP⟩ := sdiff_subset_diffWindow (α := α) c n hH hlow hhigh
  have hgb : ∀ j : ℕ, |g j| ≤ Czero := by
    intro j
    rw [hg]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    simpa [Bremainder] using principal_term α hα hirr n j
  have hbound : ∀ S : Finset ℕ, S ⊆ diffWindow c n →
      |∑ j ∈ S, g j| ≤ Czero * (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1) := by
    intro S hS
    have h1 : |∑ j ∈ S, g j| ≤ ∑ j ∈ S, |g j| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ j ∈ S, |g j| ≤ (S.card : ℝ) * Czero := by
      calc ∑ j ∈ S, |g j| ≤ ∑ _j ∈ S, Czero := Finset.sum_le_sum fun j _ => hgb j
        _ = (S.card : ℝ) * Czero := by rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : S.card ≤ 2 * bdryLen c n + 2 * trimAmt n + 1 :=
      le_trans (Finset.card_le_card hS) (card_diffWindow_le c n)
    have h4 : (S.card : ℝ) ≤ 2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1 := by
      exact_mod_cast h3
    have h5 : (S.card : ℝ) * Czero
        ≤ (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1) * Czero :=
      mul_le_mul_of_nonneg_right h4 Czero_nonneg
    calc |∑ j ∈ S, g j| ≤ (S.card : ℝ) * Czero := le_trans h1 h2
      _ ≤ (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1) * Czero := h5
      _ = Czero * (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1) := by ring
  have hsplit : ∑ j ∈ P, g j - ∑ j ∈ Q, g j
      = ∑ j ∈ P \ Q, g j - ∑ j ∈ Q \ P, g j := by
    have h1 := Finset.sum_inter_add_sum_diff P Q g
    have h2 := Finset.sum_inter_add_sum_diff Q P g
    rw [Finset.inter_comm Q P] at h2
    linarith
  have hdiff : Master.randRemainderSum c α n - Master.detRemainderSum α n
      = (1 / Lnorm n) * (∑ j ∈ P, g j - ∑ j ∈ Q, g j) := by
    simp only [Master.randRemainderSum, Master.detRemainderSum, hP, hQ, hg]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Lnorm n)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [hsplit]
  have hA := abs_le.mp (hbound _ hPQ)
  have hB := abs_le.mp (hbound _ hQP)
  rw [abs_le]
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

/-! ## Part E, the deterministic smallness of the bridge bound -/

private lemma cast_ceil_le (x : ℝ) : (⌈x⌉₊ : ℝ) ≤ |x| + 1 := by
  by_cases hx : 0 ≤ x
  · have h := Nat.ceil_lt_add_one hx
    have : |x| = x := abs_of_nonneg hx
    linarith
  · push_neg at hx
    have : ⌈x⌉₊ = 0 := by
      rw [Nat.ceil_eq_zero]; exact hx.le
    rw [this]
    have := abs_nonneg x
    simp only [Nat.cast_zero]
    linarith

lemma bdryLen_le (c : ℝ) (n : ℕ) (hH : 0 ≤ Hscale n) :
    (bdryLen c n : ℝ) ≤ (|c| + 200) * Hscale n + 1 := by
  have h1 : (⌈c * Hscale n⌉₊ : ℝ) ≤ |c| * Hscale n + 1 := by
    refine le_trans (cast_ceil_le _) ?_
    rw [abs_mul, abs_of_nonneg hH]
  have h2 : (⌈200 * Hscale n⌉₊ : ℝ) ≤ 200 * Hscale n + 1 := by
    refine le_trans (cast_ceil_le _) ?_
    rw [abs_mul, abs_of_nonneg hH]
    norm_num
  have habs : (0 : ℝ) ≤ |c| := abs_nonneg c
  rw [bdryLen, Nat.cast_max]
  refine max_le ?_ ?_ <;> nlinarith

lemma tendsto_inv_Lnorm : Tendsto (fun n : ℕ => 1 / Lnorm n) atTop (𝓝 0) := by
  simpa using Master.tendsto_Lnorm_atTop.inv_tendsto_atTop

lemma tendsto_Hscale_div_Lnorm :
    Tendsto (fun n : ℕ => Hscale n / Lnorm n) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ Master.tendsto_Hscale_log_div_Lnorm
  · filter_upwards [Master.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hL
    have : 0 ≤ Hscale n := by rw [Hscale]; exact Real.rpow_nonneg hL.le _
    positivity
  · filter_upwards [Master.tendsto_Lnorm_atTop.eventually_ge_atTop (8 : ℝ)] with n hL
    have hL0 : (0 : ℝ) < Lnorm n := by linarith
    have hH0 : 0 ≤ Hscale n := by rw [Hscale]; exact Real.rpow_nonneg hL0.le _
    have hlogL : (1 : ℝ) ≤ Real.log (Lnorm n) := by
      have he : Real.exp 1 ≤ Lnorm n :=
        le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      exact (Real.le_log_iff_exp_le hL0).mpr he
    rw [div_le_div_iff_of_pos_right hL0]
    nlinarith

/-- **The bridge bound is `o(1)`.**  `C₀·(2D_n + 2A_n + 1)/L = O(H/L) = O(L^{-1/4})`. -/
theorem tendsto_bridgeBound (c : ℝ) :
    Tendsto (fun n : ℕ =>
        (1 / Lnorm n) * (2 * Czero * (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1)))
      atTop (𝓝 0) := by
  set K1 : ℝ := 2 * Czero * (2 * |c| + 402) with hK1
  set K2 : ℝ := 2 * Czero * 29 with hK2
  have hmaj : Tendsto (fun n : ℕ => K1 * (Hscale n / Lnorm n) + K2 * (1 / Lnorm n))
      atTop (𝓝 0) := by
    simpa using (tendsto_Hscale_div_Lnorm.const_mul K1).add (tendsto_inv_Lnorm.const_mul K2)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Master.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hL
    have hC := Czero_nonneg
    positivity
  · filter_upwards [Master.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hL
    have hH0 : (0 : ℝ) ≤ Hscale n := by rw [Hscale]; exact Real.rpow_nonneg hL.le _
    have hC := Czero_nonneg
    have hD := bdryLen_le c n hH0
    have hA := trimAmt_le n hH0
    have hkey : 2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1
        ≤ (2 * |c| + 402) * Hscale n + 29 := by
      have := abs_nonneg c
      nlinarith
    have hstep : 2 * Czero * (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1)
        ≤ K1 * Hscale n + K2 := by
      rw [hK1, hK2]
      nlinarith
    have hnn : (0 : ℝ) ≤ 1 / Lnorm n := by positivity
    have hfinal : (1 / Lnorm n) * (2 * Czero * (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1))
        ≤ (1 / Lnorm n) * (K1 * Hscale n + K2) := mul_le_mul_of_nonneg_left hstep hnn
    have hexp : (1 / Lnorm n) * (K1 * Hscale n + K2)
        = K1 * (Hscale n / Lnorm n) + K2 * (1 / Lnorm n) := by field_simp
    linarith [hfinal, hexp.le, hexp.ge]

/-- All the deterministic side conditions of the sandwich, together with the
smallness of the bridge bound, hold eventually. -/
lemma eventually_bridge_setup (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 0 < Lnorm n ∧ 0 ≤ Hscale n
      ∧ trimAmt n ≤ mIndex n ∧ 1 ≤ mIndex n - trimAmt n
      ∧ mIndex n + trimAmt n ≤ 2 * mIndex n
      ∧ (1 / Lnorm n)
          * (2 * Czero * (2 * (bdryLen c n : ℝ) + 2 * (trimAmt n : ℝ) + 1)) < ε := by
  filter_upwards [OneLevelLaw.eventually_trim_le, eventually_ge_atTop 1,
    (tendsto_bridgeBound c).eventually (gt_mem_nhds hε)] with n htrim hn hsmall
  obtain ⟨hL0, htrim⟩ := htrim
  have hlam := LargeDeviation.lyapunov_pos'
  have hlam2 := LargeDeviation.lyapunov_lt_two
  have hH0 : (0 : ℝ) ≤ Hscale n := by rw [Hscale]; exact Real.rpow_nonneg hL0.le _
  have hL1 : (1 : ℝ) ≤ Lnorm n := by linarith
  have hH1 : (1 : ℝ) ≤ Hscale n := by
    have h := Real.rpow_le_rpow zero_le_one hL1 (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rwa [Real.one_rpow, ← Hscale] at h
  have hA := trimAmt_le n hH0
  have hm : Lnorm n / lyapunov - 1 < (mIndex n : ℝ) := by
    have h : Lnorm n / lyapunov < (mIndex n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hhalf : Lnorm n / 2 ≤ Lnorm n / lyapunov := by
    apply div_le_div_of_nonneg_left hL0.le hlam
    linarith
  have hkey : (trimAmt n : ℝ) + 1 ≤ (mIndex n : ℝ) := by
    have h1 : (trimAmt n : ℝ) + 1 ≤ Hscale n + 14 := by linarith
    have h2 : Hscale n + 15 ≤ Lnorm n / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    linarith
  have hcast : trimAmt n + 1 ≤ mIndex n := by exact_mod_cast hkey
  exact ⟨hn, hL0, hH0, by omega, by omega, by omega, hsmall⟩

/-! ## Part F, the bridge -/

lemma tendsto_exp_neg_sqrt_Lnorm {cd : ℝ} (hcd : 0 < cd) (K : ℝ) :
    Tendsto (fun n : ℕ => K * Real.exp (-cd * Real.sqrt (Lnorm n))) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (Lnorm n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Master.tendsto_Lnorm_atTop
  have hbot : Tendsto (fun n : ℕ => -cd * Real.sqrt (Lnorm n)) atTop atBot :=
    hsq.const_mul_atTop_of_neg (by linarith)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-cd * Real.sqrt (Lnorm n))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hbot
  simpa using hexp.const_mul K

/-- **The §7/§4 index-set bridge, proved.**  For every trimming constant `c`,
`(1/L)·[∑_{j ∈ Marks.bulkIndices c α n} − ∑_{j ∈ Section4.bulkJ n}] (−1)^j B_j → 0`
in probability under Lebesgue measure on `(0,1)`.

The two index sets differ only near their two boundaries: below the longer of
the trims `c·H` and `200H`, and within `A_n = H + O(1)` of `m_n`, the latter
because display (20) puts the §7 stopping time inside `m_n ± A_n` off a set of
measure `O(e^{−c√L})`.  Proposition 2.2 caps each summand by the absolute
constant `C₀`, so the whole difference is `O(H/L) = O(L^{−1/4})` off that
set. -/
theorem section7Bridge_holds (c : ℝ) : Master.Section7Bridge c := by
  classical
  intro ε hε
  obtain ⟨Cd, cd, hCd, hcd, h20⟩ := LargeDeviation.display20_of_pos 1 one_pos
  refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_
    (tendsto_exp_neg_sqrt_Lnorm hcd (2 * Cd))
  filter_upwards [h20, eventually_bridge_setup c hε] with n h20n hset
  obtain ⟨hn, hL0, hH0, hAm, hone, hle2m, hsmall⟩ := hset
  set jd : ℕ := mIndex n - trimAmt n with hjd
  set ju : ℕ := mIndex n + trimAmt n with hju
  set Bd : Set ℝ := {α ∈ Ioo (0 : ℝ) 1 |
      ¬ (Real.exp (lyapunov * (jd : ℝ) - 1 * Hscale n) ≤ (denom α jd : ℝ)
          ∧ (denom α jd : ℝ) ≤ Real.exp (lyapunov * (jd : ℝ) + 1 * Hscale n))} with hBd
  set Bu : Set ℝ := {α ∈ Ioo (0 : ℝ) 1 |
      ¬ (Real.exp (lyapunov * (ju : ℝ) - 1 * Hscale n) ≤ (denom α ju : ℝ)
          ∧ (denom α ju : ℝ) ≤ Real.exp (lyapunov * (ju : ℝ) + 1 * Hscale n))} with hBu
  have hBdle : (volume Bd).toReal ≤ Cd * Real.exp (-cd * Real.sqrt (Lnorm n)) :=
    h20n jd (by omega)
  have hBule : (volume Bu).toReal ≤ Cd * Real.exp (-cd * Real.sqrt (Lnorm n)) :=
    h20n ju (by omega)
  have hsub : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      ε ≤ |Master.randRemainderSum c α n - Master.detRemainderSum α n|}
      ⊆ Bd ∪ Bu ∪ {x : ℝ | ¬ Irrational x} := by
    rintro α ⟨hα, hbig⟩
    by_cases hirr : Irrational α
    · by_cases hd : α ∈ Bd
      · exact Or.inl (Or.inl hd)
      · by_cases hu : α ∈ Bu
        · exact Or.inl (Or.inr hu)
        · exfalso
          have hwd : Real.exp (lyapunov * (jd : ℝ) - 1 * Hscale n) ≤ (denom α jd : ℝ)
              ∧ (denom α jd : ℝ) ≤ Real.exp (lyapunov * (jd : ℝ) + 1 * Hscale n) := by
            by_contra hcon
            exact hd ⟨hα, hcon⟩
          have hwu : Real.exp (lyapunov * (ju : ℝ) - 1 * Hscale n) ≤ (denom α ju : ℝ)
              ∧ (denom α ju : ℝ) ≤ Real.exp (lyapunov * (ju : ℝ) + 1 * Hscale n) := by
            by_contra hcon
            exact hu ⟨hα, hcon⟩
          obtain ⟨hlow, hhigh⟩ :=
            stoppingTime_sandwich hα hirr hn hAm hone hwu.1 hwd.2
          have := abs_remainderSum_diff_le hα hirr c n hH0 hL0 hlow hhigh
          linarith
    · exact Or.inr hirr
  have hBdfin : volume Bd ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hBufin : volume Bu ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hmeas : volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      ε ≤ |Master.randRemainderSum c α n - Master.detRemainderSum α n|}
      ≤ volume Bd + volume Bu := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [Master.vol_nonIrrational_zero, add_zero]
    exact measure_union_le _ _
  calc (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        ε ≤ |Master.randRemainderSum c α n - Master.detRemainderSum α n|}).toReal
      ≤ (volume Bd + volume Bu).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBdfin, hBufin⟩) hmeas
    _ = (volume Bd).toReal + (volume Bu).toReal := ENNReal.toReal_add hBdfin hBufin
    _ ≤ 2 * Cd * Real.exp (-cd * Real.sqrt (Lnorm n)) := by linarith

/-! ## Part G, hypothesis 3 of the master theorem, discharged -/

/-- **`Section7EndTerms` holds.**  Its `O(H)` trimming half is
`Master.tendsto_endTerms_prob` and its index-set half is
`section7Bridge_holds`; the third hypothesis of the master theorem is therefore
no longer a hypothesis. -/
theorem section7EndTerms_holds (c : ℝ) (hc : 0 ≤ c) : Master.Section7EndTerms c :=
  Master.section7EndTerms_of_bridge c hc (section7Bridge_holds c)

/-- **Kwon's Theorem 1.1 from two inputs.**  All of §7 is now proved, so the
master theorem carries only Corollary 5.3 and Proposition 6.4. -/
theorem erdos1002Conclusion_of_principal_and_prop64 (c : ℝ) (hc : 0 ≤ c)
    (hprincipal : Master.PrincipalCauchyLaw c) (hprop64 : Master.Prop64Statement) :
    Erdos1002Conclusion :=
  Master.erdos1002Conclusion_of c hprincipal hprop64 (section7EndTerms_holds c hc)

/-- The official (existential) form, from the same two inputs. -/
theorem erdos1002Official_of_principal_and_prop64 (c : ℝ) (hc : 0 ≤ c)
    (hprincipal : Master.PrincipalCauchyLaw c) (hprop64 : Master.Prop64Statement) :
    Erdos1002Official :=
  Master.erdos1002Official_of c hprincipal hprop64 (section7EndTerms_holds c hc)

end

end Section7

end Kwon1002
