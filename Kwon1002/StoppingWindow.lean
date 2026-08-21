import Kwon1002.LDDeviation
import Kwon1002.LDDisplay20
import Kwon1002.TupleMeasure
import Kwon1002.L2Estimate

/-!
# The §7 stopping-time window: `τ_n = m_n + O(H)` off a set of measure `O(e^{−c√L})`

The §7 stopping time `τ_n = min{j : N_j = 0}` and the deterministic index
`m_n = ⌊L/λ⌋` of display (18) are within `A_n = H + O(1)` of one another, off a
set of Lebesgue measure `O(e^{−c√L})`.  Consequently the *random* §7 bulk
`Marks.bulkIndices c α n = {j < τ_n : c·H ≤ j}` and the *deterministic* §4 bulk
`Section4.bulkJ n = {j : 200H ≤ j ≤ m_n − 200H}` of display (19) agree outside a
deterministic window `diffWindow c n` of `O(H)` levels
(`mem_bulkIndices_iff`).

This is the input §5 and §7 both need and neither had: `Kwon1002/FiveFinal.lean`
consumes it for the one-level index-set bridge and
`Kwon1002/Section7Bridge.lean` for the bounded-remainder bridge.

## The brackets

The height recursion (2) and display (7) give `N_j = nβ_{j−1} − E_j` with
`0 ≤ E_j ≤ E*`, and the classical sandwich `1/(2q_j) ≤ β_{j−1} ≤ 1/q_j`
(`LDSpine.betaProd_le_inv_denom`, `LDSpine.inv_denom_le_betaProd`) turns that
into a two-sided bracket for the hitting time:

* `q_j > n ⟹ N_j ≤ n/q_j < 1 ⟹ N_j = 0`, so `τ_n ≤ j`
  (`heightSeq_eq_zero_of_lt_denom`);
* `N_j = 0 ⟹ nβ_{j−1} ≤ E* ⟹ q_j ≥ n/(2E*)`, so `q_j < n/(2E*) ⟹ τ_n > j`
  (`le_denom_of_heightSeq_eq_zero`).

Reading those at the two deterministic indices `m_n ± A_n` and feeding in the
Lévy window `e^{λj ± H}` of display (20) — `LargeDeviation.display20_of_pos`,
proved — gives `m_n − A_n < τ_n ≤ m_n + A_n` off a set of measure
`≤ 2C e^{−c√L}` (`stopBad_measure_le`).

Everything here is proved outright; `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]` on every declaration.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace StopWin

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

/-- The absolute constant the deviation `A_n` carries beyond `H`. -/
def trimConst : ℝ := Real.log (2 * Estar) + 2 * lyapunov + 1

lemma trimConst_pos : 0 < trimConst := by
  have := log_two_Estar_pos
  have := LargeDeviation.lyapunov_pos'
  rw [trimConst]; linarith

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

lemma trimAmt_le (n : ℕ) (hH : 0 ≤ Hscale n) :
    (trimAmt n : ℝ) ≤ Hscale n + trimConst := by
  have hlam1 := LargeDeviation.one_lt_lyapunov
  have hlam := LargeDeviation.lyapunov_pos'
  have hE0 := log_two_Estar_pos
  have hnum : 0 ≤ Hscale n + Real.log (2 * Estar) + 2 * lyapunov := by linarith
  have hdiv : (Hscale n + Real.log (2 * Estar) + 2 * lyapunov) / lyapunov
      ≤ Hscale n + Real.log (2 * Estar) + 2 * lyapunov := by
    rw [div_le_iff₀ hlam]
    nlinarith
  have hceil : (trimAmt n : ℝ)
      < (Hscale n + Real.log (2 * Estar) + 2 * lyapunov) / lyapunov + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  rw [trimConst]
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
  simpa using TupleMeasure.tendsto_Lnorm_atTop.inv_tendsto_atTop

lemma tendsto_Hscale_div_Lnorm :
    Tendsto (fun n : ℕ => Hscale n / Lnorm n) atTop (𝓝 0) := by
  have hrpow : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 4))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  refine (hrpow.comp TupleMeasure.tendsto_Lnorm_atTop).congr' ?_
  filter_upwards [TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hL
  simp only [Function.comp_apply]
  have h1 : Lnorm n ^ ((3 : ℝ) / 4) / Lnorm n ^ ((1 : ℝ)) = Lnorm n ^ ((3 : ℝ) / 4 - 1) :=
    (Real.rpow_sub hL _ _).symm
  rw [Real.rpow_one] at h1
  rw [Hscale, h1]
  norm_num

/-! ## Part F, room, and the exceptional set -/

/-- Every deterministic side condition of the sandwich holds eventually:
`A_n = H + O(1)` and `m_n ≥ L/2 − 1`. -/
lemma eventually_stop_room : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 0 < Lnorm n ∧ 0 ≤ Hscale n
    ∧ trimAmt n ≤ mIndex n ∧ 1 ≤ mIndex n - trimAmt n
    ∧ mIndex n + trimAmt n ≤ 2 * mIndex n := by
  have hzero : Tendsto (fun n : ℕ =>
      Hscale n / Lnorm n + (trimConst + 2) * (1 / Lnorm n)) atTop (𝓝 0) := by
    simpa using tendsto_Hscale_div_Lnorm.add (tendsto_inv_Lnorm.const_mul (trimConst + 2))
  filter_upwards [eventually_ge_atTop 1,
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ),
    hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn hL0 hsmall
  have hlam := LargeDeviation.lyapunov_pos'
  have hlam2 := LargeDeviation.lyapunov_lt_two
  have hH0 : (0 : ℝ) ≤ Hscale n := by rw [Hscale]; exact Real.rpow_nonneg hL0.le _
  have hA := trimAmt_le n hH0
  have hroom : Hscale n + (trimConst + 2) < Lnorm n / 2 := by
    have h1 : (Hscale n / Lnorm n + (trimConst + 2) * (1 / Lnorm n)) * Lnorm n
        = Hscale n + (trimConst + 2) := by field_simp
    nlinarith [mul_lt_mul_of_pos_right hsmall hL0]
  have hm : Lnorm n / lyapunov - 1 < (mIndex n : ℝ) := by
    have h : Lnorm n / lyapunov < (mIndex n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hhalf : Lnorm n / 2 ≤ Lnorm n / lyapunov :=
    div_le_div_of_nonneg_left hL0.le hlam (by linarith)
  have hkey : (trimAmt n : ℝ) + 1 ≤ (mIndex n : ℝ) := by linarith
  have hcast : trimAmt n + 1 ≤ mIndex n := by exact_mod_cast hkey
  exact ⟨hn, hL0, hH0, by omega, by omega, by omega⟩

/-- **The exceptional set of the stopping-time window.**  Off it the sandwich
`m_n − A_n < τ_n ≤ m_n + A_n` holds and `α` is irrational. -/
def stopBad (n : ℕ) : Set ℝ :=
  {α ∈ Ioo (0 : ℝ) 1 | ¬ (Irrational α ∧
      (mIndex n - trimAmt n < stoppingTime α n ∧ stoppingTime α n ≤ mIndex n + trimAmt n))}

/-- **The window holds off a set of measure `O(e^{−c√L})`.**  This is display
(20) read at the two deterministic indices `m_n ± A_n`. -/
theorem stopBad_measure_le :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop,
      (volume (stopBad n)).toReal ≤ C * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := by
  classical
  obtain ⟨Cd, cd, hCd, hcd, h20⟩ :=
    LargeDeviation.display20_of_deviation LargeDeviation.continuant_large_deviation 1 one_pos
  refine ⟨2 * Cd, cd, by linarith, hcd, ?_⟩
  filter_upwards [h20, eventually_stop_room] with n h20n hroom
  obtain ⟨hn, hL0, hH0, hAm, hone, hle2m⟩ := hroom
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
  have hsub : stopBad n ⊆ Bd ∪ Bu ∪ {x : ℝ | ¬ Irrational x} := by
    rintro α ⟨hα, hbad⟩
    by_cases hirr : Irrational α
    · by_cases hd : α ∈ Bd
      · exact Or.inl (Or.inl hd)
      · by_cases hu : α ∈ Bu
        · exact Or.inl (Or.inr hu)
        · exfalso
          have hwd : Real.exp (lyapunov * (jd : ℝ) - 1 * Hscale n) ≤ (denom α jd : ℝ)
              ∧ (denom α jd : ℝ) ≤ Real.exp (lyapunov * (jd : ℝ) + 1 * Hscale n) := by
            by_contra hcon; exact hd ⟨hα, hcon⟩
          have hwu : Real.exp (lyapunov * (ju : ℝ) - 1 * Hscale n) ≤ (denom α ju : ℝ)
              ∧ (denom α ju : ℝ) ≤ Real.exp (lyapunov * (ju : ℝ) + 1 * Hscale n) := by
            by_contra hcon; exact hu ⟨hα, hcon⟩
          exact hbad ⟨hirr, stoppingTime_sandwich hα hirr hn hAm hone hwu.1 hwd.2⟩
    · exact Or.inr hirr
  have hBdfin : volume Bd ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hBufin : volume Bu ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hmeas : volume (stopBad n) ≤ volume Bd + volume Bu := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    have hQnull : volume {x : ℝ | ¬ Irrational x} = 0 := by
      have hset : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
        ext x; simp [Irrational]
      rw [hset]
      exact (Set.countable_range _).measure_zero _
    rw [hQnull, add_zero]
    exact measure_union_le _ _
  calc (volume (stopBad n)).toReal
      ≤ (volume Bd + volume Bu).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBdfin, hBufin⟩) hmeas
    _ = (volume Bd).toReal + (volume Bu).toReal := ENNReal.toReal_add hBdfin hBufin
    _ ≤ 2 * Cd * Real.exp (-cd * Real.sqrt (Lnorm n)) := by linarith

/-- **The two index sets agree off `diffWindow`.**  This is the form both §5 and
§7 consume. -/
theorem mem_bulkIndices_iff (c : ℝ) (n : ℕ) (hH : 0 ≤ Hscale n) {α : ℝ}
    (hgood : α ∉ stopBad n) (hα : α ∈ Ioo (0 : ℝ) 1) {j : ℕ} (hj : j ∉ diffWindow c n) :
    j ∈ bulkIndices c α n ↔ j ∈ bulkJ n := by
  classical
  have hsand : Irrational α ∧
      (mIndex n - trimAmt n < stoppingTime α n
        ∧ stoppingTime α n ≤ mIndex n + trimAmt n) := by
    by_contra hcon
    exact hgood ⟨hα, hcon⟩
  obtain ⟨hPQ, hQP⟩ :=
    sdiff_subset_diffWindow (α := α) c n hH hsand.2.1 hsand.2.2
  constructor
  · intro hjP
    by_contra hjQ
    exact hj (hPQ (Finset.mem_sdiff.mpr ⟨hjP, hjQ⟩))
  · intro hjQ
    by_contra hjP
    exact hj (hQP (Finset.mem_sdiff.mpr ⟨hjQ, hjP⟩))

end

end StopWin

end Kwon1002
