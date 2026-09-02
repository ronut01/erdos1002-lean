import Kwon1002.CauchyJoin
import Kwon1002.TailTransferJoin

/-!
# The endgame: Kwon's Theorem 1.1 modulo Proposition 6.4 alone

`Kwon1002/TailTransferJoin.lean` **proves** §5's last open input:
`TailTransferJoin.bulk_offdiagonal_abs_far_sharp_proved` carries the statement
of `Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` token for token (an
anonymous `example` at the foot of that file closes the canonical type by the
theorem proved there), and `#print axioms` on it reports exactly
`[propext, Classical.choice, Quot.sound]`.

As with the six earlier instances, that proof cannot be installed where the
canonical declaration stands: `Kwon1002/CorFinal.lean` sits strictly **below**
every module that supplies §4, so the `sorry` at
`Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` survives in the import
closure of everything that consumes the name — including
`CorFinal.bulk_offdiagonal_abs_input`, `CorFinal.bulkTerm_covariance_bound_F`,
`CorFinal.signed_small_jumps_variance_F`, and through them
`CauchyJoin.principal_cauchy_law_J` and `CauchyJoin.erdos1002Conclusion_final`.
So the affected chain is restated and re-proved here, in a module importing both
sides, with `rfl` guards against every canonical name.

## What is re-proved here, and against what

The four-step chain, re-run with the proved residual in place of the sorried
`CorFinal.bulk_offdiagonal_abs_far_sharp`:

  `bulk_offdiagonal_abs_input_T` → `bulkTerm_covariance_bound_T`
    → `signed_small_jumps_variance_T` → `principal_cauchy_law_T`.

Every proof body is the author's, transcribed from `Kwon1002/CorFinal.lean` and
`Kwon1002/CauchyJoin.lean` unchanged apart from the names of its inputs; the
statements are byte-identical and are checked against the canonical names by the
anonymous `example`s at the foot of this file.

`bulk_offdiagonal_abs_input_T` consumes `CorFinal.diagonal_covariance_sum_bound_F`
and `CorFinal.near_pair_decay_sharp` **as they stand**: both are already
sorry-free, so nothing is gained by restating them.

## The effect on the closure

`CauchyJoin.erdos1002Conclusion_final` retains the historical leaf
`{CorFinal.bulk_offdiagonal_abs_far_sharp}`.  The theorem
`erdos1002Conclusion_final_T` below replaces that leaf with the proved transfer
and consumes the completed canonical Proposition 6.4, so its closure is empty.

`Kwon1002/CorFinal.lean` and `Kwon1002/CauchyJoin.lean` are deliberately **not**
edited.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal Real

namespace Kwon1002

namespace TailTransferCauchy

open Assembly5 CorFinal

noncomputable section

/-! ## Part I, the covariance core, on the proved residual -/

theorem bulk_offdiagonal_abs_input_T (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            |∫ α in Ioo (0 : ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|) ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hpair⟩ := OffDiag.bulkTermCentered_offdiag_bound c
  obtain ⟨κ, hκ, hfar⟩ := TailTransferJoin.bulk_offdiagonal_abs_far_sharp_proved c
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hfar ε hε hε1
  obtain ⟨N₂, hN₂⟩ := near_pair_decay_sharp κ Cp (ε / 2) hκ hCp (by positivity)
  refine ⟨max (max N₁ N₂) 3, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨B, hBcard, hBfar⟩ := hN₁ n hn1
  rw [sum_offdiagAbs_eq c ε n]
  set P : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hP
  have hsplit : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagAbsTerm c ε n p)
      + ∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagAbsTerm c ε n p
      = ∑ p ∈ P, offdiagAbsTerm c ε n p :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ∈ B) _
  have hnotB : P.filter (fun p => ¬ p ∈ B) = P \ B := (Finset.sdiff_eq_filter P B).symm
  have hQ0 : (0:ℝ) ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by positivity
  have hbound : ∀ p ∈ P.filter (fun p => p ∈ B),
      offdiagAbsTerm c ε n p ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by
    intro p _
    simp only [offdiagAbsTerm]
    by_cases hpq : p.1 = p.2
    · rw [if_pos hpq]
      exact hQ0
    · rw [if_neg hpq]
      exact hpair ε hε hε1 n p.1 p.2 hpq hL
  have hnear : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagAbsTerm c ε n p) ≤ ε / 2 := by
    have hb := Finset.sum_le_card_nsmul (P.filter (fun p => p ∈ B)) (offdiagAbsTerm c ε n)
      (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) hbound
    rw [nsmul_eq_mul] at hb
    refine le_trans hb ?_
    have hcard : (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ)
        ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3 := by
      refine le_trans ?_ hBcard
      exact_mod_cast Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).2)
    calc (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2)
        ≤ (κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard hQ0
      _ ≤ ε / 2 := hN₂ n hn2
  have hfarsum : (∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagAbsTerm c ε n p) ≤ ε / 2 := by
    rw [hnotB]
    exact hBfar
  linarith [hsplit, hnear, hfarsum]

/-- **Proved, unconditionally**: the diagonal of the covariance sum is `O(ε)`,
out of `L2Estimate.bulk_window_input` (only `O(L)` levels matter, the Lamé
bound), `L2Estimate.truncatedMark_second_moment` (display (42), first half)
and `L2Estimate.diagonal_le_second_moment`. -/

theorem bulkTerm_covariance_bound_T (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            |∫ α in Ioo (0 : ℝ) 1,
                bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|)
          ≤ C * ε := by
  classical
  obtain ⟨D, hD, hdiag⟩ := CorFinal.diagonal_covariance_sum_bound_F c
  refine ⟨D + 1, by linarith, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hdiag ε hε hε1
  obtain ⟨N₂, hN₂⟩ := bulk_offdiagonal_abs_input_T c ε hε hε1
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  rw [L2Estimate.sum_split_diag (n + 1) (fun j k =>
    |∫ α in Ioo (0 : ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|)]
  have hdiagabs : ∀ j : ℕ,
      |∫ α in Ioo (0 : ℝ) 1,
          bulkTermCentered c ε α n j * bulkTermCentered c ε α n j|
        = ∫ α in Ioo (0 : ℝ) 1,
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n j :=
    fun j => abs_of_nonneg (integral_nonneg fun α => mul_self_nonneg _)
  have hdsum : (∑ j ∈ Finset.range (n + 1),
      |∫ α in Ioo (0 : ℝ) 1,
        bulkTermCentered c ε α n j * bulkTermCentered c ε α n j|)
      = ∑ j ∈ Finset.range (n + 1),
          ∫ α in Ioo (0 : ℝ) 1,
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n j :=
    Finset.sum_congr rfl fun j _ => hdiagabs j
  rw [hdsum]
  have hfinal : D * ε + ε ≤ (D + 1) * ε := le_of_eq (by ring)
  linarith [hN₁ n hn1, hN₂ n hn2, hfinal]


theorem signed_small_jumps_variance_T (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo) ≤ C * ε := by
  obtain ⟨C, hC, hcov⟩ := bulkTerm_covariance_bound_T c
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨N, hN⟩ := hcov ε hε hε1
  refine ⟨N, fun n hn => ?_⟩
  have hrw : (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo)
      = ∫ α in Ioo (0 : ℝ) 1, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 := by
    simp only [unifIoo]
  rw [hrw, Finale.integral_signedSmallSum_centered_sq c ε hε.le n]
  refine le_trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_) (hN n hn)
  have habs : |((-1 : ℝ) ^ j * (-1 : ℝ) ^ k)| = 1 := by
    rw [abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_pow, one_mul]
  calc ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) *
        ∫ α in Ioo (0 : ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k
      ≤ |((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) *
          ∫ α in Ioo (0 : ℝ) 1,
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n k| := le_abs_self _
    _ = |∫ α in Ioo (0 : ℝ) 1,
          bulkTermCentered c ε α n j * bulkTermCentered c ε α n k| := by
        rw [abs_mul, habs, one_mul]


theorem principal_cauchy_law_T (c : ℝ) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  classical
  obtain ⟨C, hC, hvar⟩ := signed_small_jumps_variance_T c
  -- the truncation scale, tuned so that `C · e k ≤ (dseq k)³`
  set dseq : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with hdseq
  set e : ℕ → ℝ := fun k => dseq k ^ 3 / (C + 1) with he
  have hd0 : ∀ k, 0 < dseq k := fun k => by
    simp only [hdseq]; positivity
  have hd1 : ∀ k, dseq k ≤ 1 / 2 := fun k => by
    simp only [hdseq]
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have he0 : ∀ k, 0 < e k := fun k => by
    simp only [he]
    have := hd0 k
    positivity
  have he1 : ∀ k, e k < 1 := fun k => by
    have h1 : dseq k ^ 3 ≤ 1 := by
      have h2 := hd1 k
      have h3 := (hd0 k).le
      calc dseq k ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by gcongr
        _ ≤ 1 := by norm_num
    have : e k ≤ 1 / (C + 1) := by
      simp only [he]
      exact div_le_div_of_nonneg_right h1 (by linarith)
    have hlt : 1 / (C + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have hdlim : Tendsto dseq atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, hdseq]
    push_cast
    ring_nf
  have helim : Tendsto e atTop (𝓝 0) := by
    have h3 : Tendsto (fun k => dseq k ^ 3) atTop (𝓝 0) := by
      simpa using hdlim.pow 3
    simpa [he] using h3.div_const (C + 1)
  -- the limit laws of the large-jump parts, and their Cauchy limit
  have hlarge : ∀ k : ℕ, ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 ρ) := fun k =>
    CauchyJoin.largeJump_weak_limit_J c (e k) (he0 k) (he1 k)
  choose ρ hρ using hlarge
  have hcauchy : Tendsto ρ atTop (𝓝 cauchyProb) :=
    CauchyJoin.compound_tendsto_cauchy_J c e he0 he1 helim ρ hρ
  -- pass to the Lévy-Prokhorov metric, which metrizes convergence in distribution
  set Φ : ProbabilityMeasure ℝ → LevyProkhorov (ProbabilityMeasure ℝ) :=
    LevyProkhorov.ofMeasure with hΦ
  have hΦcont : Continuous Φ := LevyProkhorov.continuous_ofMeasure_probabilityMeasure
  set z : LevyProkhorov (ProbabilityMeasure ℝ) := Φ cauchyProb with hz
  set Pk : ℕ → ℕ → LevyProkhorov (ProbabilityMeasure ℝ) :=
    fun k n => Φ (centeredBulkProb c (e k) n) with hPk
  set η : ℕ → ℝ := fun k => dseq k + dseq k + dist (Φ (ρ k)) z with hη
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have hdist : Tendsto (fun k => dist (Φ (ρ k)) z) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => Φ (ρ k)) atTop (𝓝 z) := by
        simpa [hz] using (hΦcont.tendsto cauchyProb).comp hcauchy
      have h2 := h1.dist (tendsto_const_nhds (x := z) (f := atTop))
      simpa using h2
    have := (hdlim.add hdlim).add hdist
    simpa [hη] using this
  have hPkclose : ∀ k, ∀ᶠ n in atTop, dist (Pk k n) z ≤ η k := by
    intro k
    obtain ⟨N, hN⟩ := hvar (e k) (he0 k) (he1 k)
    have hlp : Tendsto (fun n => Φ (largeProb c (e k) n)) atTop (𝓝 (Φ (ρ k))) :=
      (hΦcont.tendsto (ρ k)).comp (hρ k)
    have hev := Metric.tendsto_nhds.mp hlp (dseq k) (hd0 k)
    filter_upwards [eventually_ge_atTop N, hev] with n hn hnd
    have h1 : dist (Pk k n) (Φ (largeProb c (e k) n)) ≤ dseq k := by
      refine dist_centeredBulk_largeProb_le c (e k) (he0 k).le n (hd0 k).le ?_
      refine (hN n hn).trans ?_
      have hpos : (0 : ℝ) < C + 1 := by linarith
      have hcube : (0 : ℝ) ≤ dseq k ^ 3 := pow_nonneg (hd0 k).le 3
      simp only [he]
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith [hcube]
    calc dist (Pk k n) z
        ≤ dist (Pk k n) (Φ (largeProb c (e k) n)) + dist (Φ (largeProb c (e k) n)) z :=
          dist_triangle _ _ _
      _ ≤ dist (Pk k n) (Φ (largeProb c (e k) n))
            + (dist (Φ (largeProb c (e k) n)) (Φ (ρ k)) + dist (Φ (ρ k)) z) := by
          gcongr
          exact dist_triangle _ _ _
      _ ≤ dseq k + (dseq k + dist (Φ (ρ k)) z) :=
          add_le_add h1 (add_le_add hnd.le le_rfl)
      _ = η k := by simp only [hη]; ring
  obtain ⟨κ, hκ⟩ := exists_diagonal_tendsto Pk z η hηlim hPkclose
  -- transfer back to convergence in distribution
  have hweak : Tendsto (fun n => centeredBulkProb c (e (κ n)) n) atTop (𝓝 cauchyProb) := by
    have hcont : Continuous
        (LevyProkhorov.toMeasure (α := ProbabilityMeasure ℝ)) :=
      LevyProkhorov.continuous_toMeasure_probabilityMeasure
    have h := (hcont.tendsto z).comp hκ
    simpa [hPk, hΦ, hz, Function.comp_def] using h
  refine ⟨fun n => smallCenter c (e (κ n)) n, fun x => ?_⟩
  exact cdf_tendsto_of_weak_convergence c (fun n => smallCenter c (e (κ n)) n)
    (fun n => centeredBulkProb c (e (κ n)) n) (fun n => rfl) hweak x


/-! ## Part II, the master theorem -/

/-- `Kwon1002.Master.erdos1002Conclusion_of_section7`, reproduced token for
token, with hypothesis 1 fed from the axiom-clean
`principal_cauchy_law_T` and Proposition 6.4 fed from its completed canonical
declaration. -/
theorem erdos1002Conclusion_of_section7_T (c : ℝ) (hstop : Master.Section7EndTerms c) :
    Erdos1002Conclusion :=
  Master.erdos1002Conclusion_of c (principal_cauchy_law_T c)
    prop_6_4_bounded_remainder_weak_law hstop

/-- **Kwon's Theorem 1.1 from Proposition 6.4 alone**, with §5 now closed.  §7 is
proved (`Section7.section7EndTerms_holds`), Corollary 5.3 is
`principal_cauchy_law_T`, so Proposition 6.4 is the single remaining
hypothesis — and it is now the single remaining *hypothesis*, not one of two. -/
theorem erdos1002Conclusion_of_prop64_T (hprop64 : Master.Prop64Statement) :
    Erdos1002Conclusion :=
  Section7.erdos1002Conclusion_of_principal_and_prop64 0 le_rfl
    (principal_cauchy_law_T 0) hprop64

/-- The official (existential) form Erdős asked for, from Proposition 6.4
alone. -/
theorem erdos1002Official_of_prop64_T (hprop64 : Master.Prop64Statement) :
    Erdos1002Official :=
  Section7.erdos1002Official_of_principal_and_prop64 0 le_rfl
    (principal_cauchy_law_T 0) hprop64

/-- **The endgame.**  Kwon's Theorem 1.1, with Proposition 6.4 fed from its
completed canonical name.  This declaration is axiom-clean. -/
theorem erdos1002Conclusion_final_T : Erdos1002Conclusion :=
  erdos1002Conclusion_of_prop64_T prop_6_4_bounded_remainder_weak_law

/-- The official form, likewise axiom-clean. -/
theorem erdos1002Official_final_T : Erdos1002Official :=
  erdos1002Official_of_prop64_T prop_6_4_bounded_remainder_weak_law

end

end TailTransferCauchy

end Kwon1002

/- **Token-identity checks.**  Each `example` forces the statement above to be
the *same type* as its canonical target (`rfl` then closes it by proof
irrelevance).  They mention sorried declarations, so they are anonymous and
nothing proved above depends on them. -/
example : @Kwon1002.CorFinal.bulk_offdiagonal_abs_input
    = @Kwon1002.TailTransferCauchy.bulk_offdiagonal_abs_input_T := rfl

example : @Kwon1002.Finale.bulkTerm_covariance_bound
    = @Kwon1002.TailTransferCauchy.bulkTerm_covariance_bound_T := rfl

example : @Kwon1002.CorFinal.bulkTerm_covariance_bound_F
    = @Kwon1002.TailTransferCauchy.bulkTerm_covariance_bound_T := rfl

example : @Kwon1002.Assembly5.signed_small_jumps_variance
    = @Kwon1002.TailTransferCauchy.signed_small_jumps_variance_T := rfl

example : @Kwon1002.CorFinal.signed_small_jumps_variance_F
    = @Kwon1002.TailTransferCauchy.signed_small_jumps_variance_T := rfl

example : @Kwon1002.principal_cauchy_law
    = @Kwon1002.TailTransferCauchy.principal_cauchy_law_T := rfl

example : @Kwon1002.Assembly5.principal_cauchy_law
    = @Kwon1002.TailTransferCauchy.principal_cauchy_law_T := rfl

example : @Kwon1002.CorFinal.principal_cauchy_law_F
    = @Kwon1002.TailTransferCauchy.principal_cauchy_law_T := rfl

example : @Kwon1002.CauchyJoin.principal_cauchy_law_J
    = @Kwon1002.TailTransferCauchy.principal_cauchy_law_T := rfl

example : @Kwon1002.Master.erdos1002Conclusion_of_section7
    = @Kwon1002.TailTransferCauchy.erdos1002Conclusion_of_section7_T := rfl

example : @Kwon1002.CauchyJoin.erdos1002Conclusion_final
    = @Kwon1002.TailTransferCauchy.erdos1002Conclusion_final_T := rfl

example : @Kwon1002.CauchyJoin.erdos1002Official_final
    = @Kwon1002.TailTransferCauchy.erdos1002Official_final_T := rfl
