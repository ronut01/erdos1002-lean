import Kwon1002.Master
import Kwon1002.StoppingWindow

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

/-! ## Part D, the bridge estimate on the good event -/

lemma Czero_nonneg : (0 : ℝ) ≤ Czero := by
  have := StopWin.Estar_pos
  rw [Czero]; linarith

/-- **The bridge estimate.**  On the event that the sandwich holds, the two
remainder sums differ by at most `C₀·|Δ|/L`, and `|Δ| = O(H)`. -/
theorem abs_remainderSum_diff_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (c : ℝ) (n : ℕ) (hH : 0 ≤ Hscale n) (hL : 0 < Lnorm n)
    (hlow : mIndex n - StopWin.trimAmt n < stoppingTime α n)
    (hhigh : stoppingTime α n ≤ mIndex n + StopWin.trimAmt n) :
    |Master.randRemainderSum c α n - Master.detRemainderSum α n|
      ≤ (1 / Lnorm n) * (2 * Czero * (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)) := by
  classical
  set g : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * Bremainder α n j with hg
  set P : Finset ℕ := bulkIndices c α n with hP
  set Q : Finset ℕ := bulkJ n with hQ
  obtain ⟨hPQ, hQP⟩ := StopWin.sdiff_subset_diffWindow (α := α) c n hH hlow hhigh
  have hgb : ∀ j : ℕ, |g j| ≤ Czero := by
    intro j
    rw [hg]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    simpa [Bremainder] using principal_term α hα hirr n j
  have hbound : ∀ S : Finset ℕ, S ⊆ StopWin.diffWindow c n →
      |∑ j ∈ S, g j| ≤ Czero * (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1) := by
    intro S hS
    have h1 : |∑ j ∈ S, g j| ≤ ∑ j ∈ S, |g j| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ j ∈ S, |g j| ≤ (S.card : ℝ) * Czero := by
      calc ∑ j ∈ S, |g j| ≤ ∑ _j ∈ S, Czero := Finset.sum_le_sum fun j _ => hgb j
        _ = (S.card : ℝ) * Czero := by rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : S.card ≤ 2 * StopWin.bdryLen c n + 2 * StopWin.trimAmt n + 1 :=
      le_trans (Finset.card_le_card hS) (StopWin.card_diffWindow_le c n)
    have h4 : (S.card : ℝ) ≤ 2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1 := by
      exact_mod_cast h3
    have h5 : (S.card : ℝ) * Czero
        ≤ (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1) * Czero :=
      mul_le_mul_of_nonneg_right h4 Czero_nonneg
    calc |∑ j ∈ S, g j| ≤ (S.card : ℝ) * Czero := le_trans h1 h2
      _ ≤ (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1) * Czero := h5
      _ = Czero * (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1) := by ring
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

/-- **The bridge bound is `o(1)`.**  `C₀·(2D_n + 2A_n + 1)/L = O(H/L) = O(L^{-1/4})`. -/
theorem tendsto_bridgeBound (c : ℝ) :
    Tendsto (fun n : ℕ =>
        (1 / Lnorm n) * (2 * Czero * (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)))
      atTop (𝓝 0) := by
  set K1 : ℝ := 2 * Czero * (2 * |c| + 402) with hK1
  set K2 : ℝ := 2 * Czero * (3 + 2 * StopWin.trimConst) with hK2
  have hmaj : Tendsto (fun n : ℕ => K1 * (Hscale n / Lnorm n) + K2 * (1 / Lnorm n))
      atTop (𝓝 0) := by
    simpa using (StopWin.tendsto_Hscale_div_Lnorm.const_mul K1).add (StopWin.tendsto_inv_Lnorm.const_mul K2)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Master.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hL
    have hC := Czero_nonneg
    positivity
  · filter_upwards [Master.tendsto_Lnorm_atTop.eventually_gt_atTop (0 : ℝ)] with n hL
    have hH0 : (0 : ℝ) ≤ Hscale n := by rw [Hscale]; exact Real.rpow_nonneg hL.le _
    have hC := Czero_nonneg
    have hD := StopWin.bdryLen_le c n hH0
    have hA := StopWin.trimAmt_le n hH0
    have hkey : 2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1
        ≤ (2 * |c| + 402) * Hscale n + (3 + 2 * StopWin.trimConst) := by
      have := abs_nonneg c
      nlinarith
    have hstep : 2 * Czero * (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)
        ≤ K1 * Hscale n + K2 := by
      rw [hK1, hK2]
      nlinarith
    have hnn : (0 : ℝ) ≤ 1 / Lnorm n := by positivity
    have hfinal : (1 / Lnorm n) * (2 * Czero * (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1))
        ≤ (1 / Lnorm n) * (K1 * Hscale n + K2) := mul_le_mul_of_nonneg_left hstep hnn
    have hexp : (1 / Lnorm n) * (K1 * Hscale n + K2)
        = K1 * (Hscale n / Lnorm n) + K2 * (1 / Lnorm n) := by field_simp
    linarith [hfinal, hexp.le, hexp.ge]

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
because `StopWin.stopBad_measure_le` puts the §7 stopping time inside
`m_n ± A_n` off a set of measure `O(e^{−c√L})`.  Proposition 2.2 caps each
summand by the absolute constant `C₀`, so the whole difference is
`O(H/L) = O(L^{−1/4})` off that set. -/
theorem section7Bridge_holds (c : ℝ) : Master.Section7Bridge c := by
  classical
  intro ε hε
  obtain ⟨Cs, cs, hCs, hcs, hbad⟩ := StopWin.stopBad_measure_le
  refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_
    (tendsto_exp_neg_sqrt_Lnorm hcs Cs)
  filter_upwards [hbad, StopWin.eventually_stop_room,
    (tendsto_bridgeBound c).eventually (gt_mem_nhds hε)] with n hbadn hroom hsmall
  obtain ⟨hn, hL0, hH0, hAm, hone, hle2m⟩ := hroom
  have hsub : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      ε ≤ |Master.randRemainderSum c α n - Master.detRemainderSum α n|}
      ⊆ StopWin.stopBad n := by
    rintro α ⟨hα, hbig⟩
    by_contra hgood
    have hsand : Irrational α ∧
        (mIndex n - StopWin.trimAmt n < stoppingTime α n
          ∧ stoppingTime α n ≤ mIndex n + StopWin.trimAmt n) := by
      by_contra hcon
      exact hgood ⟨hα, hcon⟩
    have hle := abs_remainderSum_diff_le hα hsand.1 c n hH0 hL0 hsand.2.1 hsand.2.2
    linarith
  have hfin : volume (StopWin.stopBad n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  exact le_trans (ENNReal.toReal_mono hfin (measure_mono hsub)) hbadn

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
