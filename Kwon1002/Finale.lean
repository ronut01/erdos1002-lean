import Kwon1002.CompoundCauchy

/-!
# Scratch (agent `finale`), `Kwon1002.principal_cauchy_law` (Cor. 5.3, display (43))

Target: `Kwon1002.principal_cauchy_law` of `Kwon1002/PoissonLimit.lean`,
reproduced **token-identically** below as `Kwon1002.Finale.principal_cauchy_law`
(the `example`s at the very bottom check this inside Lean, by `rfl`).

This file closes the §5 assembly down to **two** sorried inputs.  Before it,
Corollary 5.3 rested on four (`Assembly5.largeJump_weak_limit`,
`Assembly5.signed_small_jumps_variance`, `Assembly5.compound_tendsto_cauchy`
- itself reduced by `CompoundCauchy` to `CompoundCauchy.largeJump_limit_compoundPoisson`
- and, feeding the second, `SmallJumps.truncatedBulkSum_centered_L2`).

## The two remaining inputs (and only these)

1. `bulkTerm_covariance_bound`, Lemma 5.2's analytic core, display (42) plus
   the pair count, stated **sign-free**: the *absolute* covariances of the
   truncated bulk terms sum to `O(ε)`,
   `∑_{j,k ≤ n} |Cov(g_j, g_k)| ≤ Cε`.
2. `largeJump_weak_limit_compoundPoisson`, Proposition 5.1 (display (37),
   `Ξ_n ⇒ PRM(Λ)`, via display (38)) together with the continuous-mapping step
   for `x ↦ ∑ x·1{|x| > ε}`, in the single form Cor. 5.3 consumes: for fixed
   `ε` the large-jump laws converge, **and** the limit is the compound-Poisson
   law with Lévy measure `Λ|_{|x|>ε}`.

Nothing else sorried is used.  In particular
`SmallJumps.truncatedBulkSum_centered_L2`, `SmallJumps.small_jumps_variance`,
`Assembly5.largeJump_weak_limit`, `Assembly5.signed_small_jumps_variance`,
`Assembly5.compound_tendsto_cauchy`, `CompoundCauchy.largeJump_limit_compoundPoisson`,
`CauchyLaw.factorialMoment_convergence`, `CauchyLaw.integral_one_sub_cos_div_sq`,
`CauchyLaw.levy_exponent_limit_raw`, `CauchyLaw.charFun_cauchyProb` and
`LevyExponent.tuple_measure_convergence` are **not** consumed.  All four
of `Assembly5`'s named inputs are *re-proved* here from the two above
(token-identically restated and checked by `rfl`).

## Manuscript / repository finding, the sign cannot be bookkept away

`Assembly5.signed_small_jumps_variance` (display (41), with the manuscript's
`U^{(ε)}_{n,j} = (-1)^j Z_{n,j} χ(·)`) is **not** derivable from
`SmallJumps.small_jumps_variance` (the same display with the *unsigned*
`Z^{(ε)}_{n,j}`).  A variance is not monotone under a sign pattern in either
direction: with `g_0 = Y`, `g_1 = 1 - Y` (both in `[0,1]`) one has
`Var(g_0 + g_1) = 0` while `Var(g_0 - g_1) = 4 Var(Y)`.  So "the `(-1)^j`
squares away in a variance" is true only on the *diagonal*; the off-diagonal
terms carry `(-1)^{j+k}` and the unsigned statement gives no control over
them.  The correct common core is therefore taken one level lower, at the
covariance sum with absolute values (input 1), which is manifestly
sign-invariant.  That this is the right factorization is *proved* here, not
asserted: input 1 yields both the signed statement
(`Finale.signed_small_jumps_variance`, token-identical to `Assembly5`'s)
and the unsigned one (`Finale.small_jumps_variance`, token-identical to
`SmallJumps`').

## Consumed from elsewhere (all proved, no sorries)

`SmallJumps`: `bulkTerm`, `bulkTermCentered`, `measurable_bulkTerm`,
`abs_bulkTerm_le`, `integrable_of_bound`, `integrable_bulkTermCentered_mul`,
`bulkIndices_subset_range`, `ae_irrational_restrict`,
`isProbabilityMeasure_restrict_Ioo`, `integral_sub_mean_sq_le`,
`integral_centered_eq`, `centered_second_moment_expand`,
`truncatedBulkSum_memLp`.
`Assembly5`: `signedSmallSum`, `smallCenter`, `largeProb`, `centeredBulkProb`,
`dist_centeredBulk_largeProb_le`, `exists_diagonal_tendsto`.
`CompoundCauchy`: `charFun_compoundPoisson_levy`, `levyExponent_complex_eq_real`,
`tendsto_levyExponent_trunc`.
`CauchyLaw`: `cdf_tendsto_of_weak_convergence`.
`FourierPairs`: `charFun_cauchyProb`.
Wang: `Erdos1002.levy_continuity_real`, `Erdos1002.continuousCompoundPoissonMeasure`.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal Real

namespace Kwon1002

namespace Finale

open Assembly5

noncomputable section

/-! ## Part 1, Lemma 5.2 with the alternating sign

The manuscript's small-jump sum is `L⁻¹ ∑_j U^{(ε)}_{n,j}` with
`U^{(ε)}_{n,j} = (-1)^j Z_{n,j} χ(Z_{n,j}/(εL))`.  Over the deterministic
range `{0,…,n}` (legitimate a.e., since `τ_n(α) ≤ n`) it is
`∑_{j ≤ n} (-1)^j g_j` with `g_j = bulkTerm`, so its centred second moment is
the *signed* covariance sum `∑_{j,k} (-1)^{j+k} Cov(g_j,g_k)`, which the
absolute covariance sum dominates. -/

lemma integrable_bulkTerm (c ε : ℝ) (hε : 0 ≤ ε) (n j : ℕ) :
    Integrable (fun α : ℝ => bulkTerm c ε α n j) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  integrable_of_bound (measurable_bulkTerm c ε n j) fun α => abs_bulkTerm_le c ε hε α n j

/-- The signed small-jump sum over the deterministic range `{0,…,n}`. -/
lemma signedSmallSum_eq_range (c ε α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n : ℕ) :
    signedSmallSum c ε α n
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * bulkTerm c ε α n j := by
  have h : ∀ j : ℕ, (-1 : ℝ) ^ j * bulkTerm c ε α n j
      = if j ∈ bulkIndices c α n then
          (-1 : ℝ) ^ j * truncatedMark ε α n j / Lnorm n else 0 := by
    intro j
    simp only [bulkTerm, mul_ite, mul_zero, mul_div_assoc]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (bulkIndices_subset_range c α hα hirr n)]
  rfl

/-- The manuscript's centering `b_{n,ε} = L⁻¹ ∑_j E U^{(ε)}_{n,j}`, expanded. -/
lemma smallCenter_eq (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    smallCenter c ε n
      = ∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * ∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j := by
  have h1 : smallCenter c ε n
      = ∫ α in Ioo (0 : ℝ) 1,
          ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * bulkTerm c ε α n j := by
    simp only [smallCenter, unifIoo]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict] with α hα hirr
    exact signedSmallSum_eq_range c ε α hα hirr n
  rw [h1, integral_finset_sum _ fun j _ => (integrable_bulkTerm c ε hε n j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

lemma signedSmallSum_sub_center_eq (c ε : ℝ) (hε : 0 ≤ ε) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n : ℕ) :
    signedSmallSum c ε α n - smallCenter c ε n
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * bulkTermCentered c ε α n j := by
  rw [signedSmallSum_eq_range c ε α hα hirr n, smallCenter_eq c ε hε n,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [bulkTermCentered]
  ring

/-- **The signed covariance expansion.**  The centred second moment of the
manuscript's small-jump sum is `∑_{j,k} (-1)^{j+k} Cov(g_j, g_k)`. -/
lemma integral_signedSmallSum_centered_sq (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (∫ α in Ioo (0 : ℝ) 1, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2)
      = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) *
            ∫ α in Ioo (0 : ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k := by
  have hpt : ∀ᵐ α ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      (signedSmallSum c ε α n - smallCenter c ε n) ^ 2
        = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) *
              (bulkTermCentered c ε α n j * bulkTermCentered c ε α n k) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict] with α hα hirr
    rw [signedSmallSum_sub_center_eq c ε hε hα hirr n, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [integral_congr_ae hpt,
    integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      (integrable_bulkTermCentered_mul c ε hε n j k).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finset_sum _ fun k _ =>
    (integrable_bulkTermCentered_mul c ε hε n j k).const_mul _]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

/-- **INPUT 1 (sorried)**, Lemma 5.2's analytic core, display (42) together
with the pair count, in **sign-free** form: the absolute covariances of the
truncated bulk terms sum to `O(ε)`, uniformly in `n`.

`g_j = bulkTerm c ε · n j = Z^{(ε)}_{n,j}/L · 1{j ∈ J_n}` and
`bulkTermCentered = g_j - E g_j`.

**Obstruction** (unchanged from `SmallJumps.truncatedBulkSum_centered_L2`,
whose statement this one refines): the diagonal `E|U^{(ε)}_{n,j}|² ≤ CεL` by
layer-cake integration of the uniform tail `P(Z_{n,j} > t) ≤ C/(1+t)`
(Lem 3.1(ii), `digit_tail_product`, with `W ≤ 1/8` =
`mark_le_digit_div_eight`), contributing `O(εL²)`; the overlapping, `H`-near
and resonance-near pairs, `O(LH log²L) = o(L²)`; and the remaining
covariances, killed by the digit cut at `A_L = L^D` (`D > 2`), Jackson
approximation and Proposition 4.1 (`Prop41.prop_4_1_error_shape`).

**Why this, and not `SmallJumps.truncatedBulkSum_centered_L2`.**  The
manuscript's (40)-(41) carries the alternating sign `(-1)^j`, and Cor. 5.3
needs it (the quantity it must kill is `bulkSum - largeSum`, which is signed).
A variance is *not* monotone under a sign pattern, see the header, so the
unsigned statement cannot produce the signed one.  Both follow from this one,
which is where the manuscript's own proof of (41) actually lives: it bounds
`|Cov(g_j,g_k)|` term by term. -/
theorem bulkTerm_covariance_bound (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            |∫ α in Ioo (0 : ℝ) 1,
                bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|)
          ≤ C * ε := by
  sorry

/-- **Lemma 5.2 with the sign**, the statement of
`Kwon1002.Assembly5.signed_small_jumps_variance`, reproduced token-identically.
Proved from `bulkTerm_covariance_bound` and nothing else sorried. -/
theorem signed_small_jumps_variance (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo) ≤ C * ε := by
  obtain ⟨C, hC, hcov⟩ := bulkTerm_covariance_bound c
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨N, hN⟩ := hcov ε hε hε1
  refine ⟨N, fun n hn => ?_⟩
  have hrw : (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo)
      = ∫ α in Ioo (0 : ℝ) 1, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 := by
    simp only [unifIoo]
  rw [hrw, integral_signedSmallSum_centered_sq c ε hε.le n]
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

/-- **Lemma 5.2, unsigned**, the statement of `Kwon1002.small_jumps_variance`
(`SmallJumps.lean`), reproduced token-identically.  Proved from the *same*
input `bulkTerm_covariance_bound`.

This is the formal content of the claim that the proof of (41) is insensitive
to the sign pattern: one sign-free hypothesis gives both displays. -/
theorem small_jumps_variance (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫ α in Ioo (0 : ℝ) 1,
            (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n
              - ∫ β in Ioo (0 : ℝ) 1,
                  ∑ j ∈ bulkIndices c β n, truncatedMark ε β n j / Lnorm n) ^ 2)
          ≤ C * ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C, hC, hcov⟩ := bulkTerm_covariance_bound c
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨N, hN⟩ := hcov ε hε hε1
  refine ⟨N, fun n hn => ?_⟩
  set b : ℝ := ∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0 : ℝ) 1, bulkTerm c ε β n j with hb
  have hmem := truncatedBulkSum_memLp c ε hε.le n
  have hf : Integrable
      (fun α : ℝ => ∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n)
      (volume.restrict (Ioo (0 : ℝ) 1)) := hmem.integrable one_le_two
  have hsq : Integrable
      (fun α : ℝ => (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have h := (hmem.sub (memLp_const b)).integrable_sq
    simpa using h
  refine le_trans (integral_sub_mean_sq_le hf b hsq) ?_
  rw [integral_centered_eq c ε b n, hb, centered_second_moment_expand c ε hε.le n]
  exact le_trans
    (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => le_abs_self _) (hN n hn)

/-! ## Part 2, Proposition 5.1, and the `ε ↓ 0` limit

`CompoundCauchy` proved the whole `ε ↓ 0` analysis from a fixed-`ε`
*identification* of the limit law.  Here that identification is merged with
the fixed-`ε` *existence* statement into a single input, which is what
Prop. 5.1 plus the continuous mapping theorem actually delivers, and both
`Assembly5.largeJump_weak_limit` and `Assembly5.compound_tendsto_cauchy` are
derived from it. -/

/-- The `ε ↓ 0` limit, from a compound-Poisson identification of each `ρ k`.
Fully proved: no sorried input. -/
theorem compound_tendsto_cauchy_of_identification (e : ℕ → ℝ) (he0 : ∀ k, 0 < e k)
    (he : Tendsto e atTop (𝓝 0)) (ρ : ℕ → ProbabilityMeasure ℝ)
    (hid : ∀ k : ℕ, ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict {x : ℝ | e k < |x|} ∧
      (ρ k : Measure ℝ) = Erdos1002.continuousCompoundPoissonMeasure r ν) :
    Tendsto ρ atTop (𝓝 cauchyProb) := by
  refine Erdos1002.levy_continuity_real ρ cauchyProb fun t => ?_
  have hchar : ∀ k : ℕ, charFun (ρ k : Measure ℝ) t
      = ((Real.exp (∫ x in {x : ℝ | e k < |x|},
          (Real.cos (t * x) - 1) * levyIntensityDensity x) : ℝ) : ℂ) := by
    intro k
    obtain ⟨r, ν, hjump, hcp⟩ := hid k
    rw [CompoundCauchy.charFun_compoundPoisson_levy (he0 k) t (ρ k) r ν hjump hcp,
      CompoundCauchy.levyExponent_complex_eq_real (he0 k) t, ← Complex.ofReal_exp]
  have hlim := CompoundCauchy.tendsto_levyExponent_trunc t e he0 he
  have hR : Tendsto (fun k : ℕ => Real.exp
      (∫ x in {x : ℝ | e k < |x|}, (Real.cos (t * x) - 1) * levyIntensityDensity x))
      atTop (𝓝 (Real.exp (-(|t| / (2 * Real.pi))))) :=
    (Real.continuous_exp.tendsto _).comp hlim
  have hC : Tendsto (fun k : ℕ => ((Real.exp
      (∫ x in {x : ℝ | e k < |x|},
        (Real.cos (t * x) - 1) * levyIntensityDensity x) : ℝ) : ℂ))
      atTop (𝓝 ((Real.exp (-(|t| / (2 * Real.pi))) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hR
  simp only [hchar]
  rw [FourierPairs.charFun_cauchyProb t]
  exact hC

/-- **INPUT 2 (sorried)**, Proposition 5.1 (display (37), `Ξ_n ⇒ PRM(Λ)` with
`dΛ(x) = |x|⁻²dx/(2π²)`) together with the continuous-mapping step for the
functional `x ↦ ∑ x·1{|x| > ε}`, in the single form Corollary 5.3 consumes:
for fixed `ε ∈ (0,1)` the large-jump laws `largeProb c ε n` converge, and the
limit is the compound-Poisson law `CP(r, ν)` with `r = Λ{|x|>ε}` and
`r·ν = Λ|_{|x|>ε}`.

**Obstruction.**  Display (37) rests on the factorial-moment computation of
display (38) (`CauchyLaw.factorialMoment_convergence`, fed by
`LevyExponent.tuple_measure_convergence` and Prop. 4.1); Wang's
`FactorialMomentMethod.tendsto_poisson_of_factorialMoments` turns (38) into
Poisson counts (`CauchyLaw.poisson_count_limit`, already proved modulo (38)).
The continuous-mapping step is legitimate because `Λ{|x| = ε} = 0` and the
tails `|x| > R` may be removed first by the uniform bound
`sup_n E Ξ_n{|x| > R} ≤ C/R`.

This is `Assembly5.largeJump_weak_limit` and
`CompoundCauchy.largeJump_limit_compoundPoisson` fused: they are two halves of
one statement, and separating them costs a limit-uniqueness argument for no
mathematical gain. -/
theorem largeJump_weak_limit_compoundPoisson (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (ρ : ProbabilityMeasure ℝ) (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) ∧
      (r : ℝ≥0∞) = levyIntensity {x : ℝ | ε < |x|} ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict {x : ℝ | ε < |x|} ∧
      (ρ : Measure ℝ) = Erdos1002.continuousCompoundPoissonMeasure r ν := by
  sorry

/-- The statement of `Kwon1002.Assembly5.largeJump_weak_limit`, reproduced
token-identically; derived from input 2. -/
theorem largeJump_weak_limit (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) := by
  obtain ⟨ρ, _r, _ν, hlim, _, _, _⟩ := largeJump_weak_limit_compoundPoisson c ε _hε0 _hε1
  exact ⟨ρ, hlim⟩

/-- The statement of `Kwon1002.Assembly5.compound_tendsto_cauchy`, reproduced
token-identically; derived from input 2 and
`compound_tendsto_cauchy_of_identification` (weak limits in
`ProbabilityMeasure ℝ` are unique, so the `ρ k` given here *is* the law input 2
identifies). -/
theorem compound_tendsto_cauchy (c : ℝ) (e : ℕ → ℝ)
    (_he0 : ∀ k, 0 < e k) (_he1 : ∀ k, e k < 1) (_he : Tendsto e atTop (𝓝 0))
    (ρ : ℕ → ProbabilityMeasure ℝ)
    (_hρ : ∀ k, Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 (ρ k))) :
    Tendsto ρ atTop (𝓝 cauchyProb) := by
  refine compound_tendsto_cauchy_of_identification e _he0 _he ρ fun k => ?_
  obtain ⟨ρ', r, ν, hlim, _hrate, hjump, hcp⟩ :=
    largeJump_weak_limit_compoundPoisson c (e k) (_he0 k) (_he1 k)
  have heq : ρ k = ρ' := tendsto_nhds_unique (_hρ k) hlim
  exact ⟨r, ν, hjump, by rw [heq]; exact hcp⟩

/-! ## Part 3, Corollary 5.3

The ε/3 assembly of `Assembly5`, re-run against the two inputs above. -/

/-- **Corollary 5.3** (Principal Cauchy law), display (43), the statement of
`Kwon1002.principal_cauchy_law`, reproduced token-identically.

Proved from exactly two sorried inputs: `bulkTerm_covariance_bound`
(Lemma 5.2's covariance core) and `largeJump_weak_limit_compoundPoisson`
(Prop. 5.1 + continuous mapping + compound-Poisson identification). -/
theorem principal_cauchy_law (c : ℝ) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  classical
  obtain ⟨C, hC, hvar⟩ := Finale.signed_small_jumps_variance c
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
    Finale.largeJump_weak_limit c (e k) (he0 k) (he1 k)
  choose ρ hρ using hlarge
  have hcauchy : Tendsto ρ atTop (𝓝 cauchyProb) :=
    Finale.compound_tendsto_cauchy c e he0 he1 helim ρ hρ
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

end

end Finale

end Kwon1002

/- **Token-identity checks.**  Each `example` forces the statement above to be
the *same type* as the shared-file target (and `rfl` closes it by proof
irrelevance).  They mention sorried declarations, so they are anonymous and
nothing proved above depends on them. -/
example : @Kwon1002.Assembly5.signed_small_jumps_variance
    = @Kwon1002.Finale.signed_small_jumps_variance := rfl

example : @Kwon1002.small_jumps_variance
    = @Kwon1002.Finale.small_jumps_variance := rfl

example : @Kwon1002.Assembly5.largeJump_weak_limit
    = @Kwon1002.Finale.largeJump_weak_limit := rfl

example : @Kwon1002.Assembly5.compound_tendsto_cauchy
    = @Kwon1002.Finale.compound_tendsto_cauchy := rfl

example : @Kwon1002.Assembly5.principal_cauchy_law
    = @Kwon1002.Finale.principal_cauchy_law := rfl

example : @Kwon1002.principal_cauchy_law
    = @Kwon1002.Finale.principal_cauchy_law := rfl

/- **Axiom check** (`#print axioms`, run and then removed, per the fleet
contract).  Everything proved outright here, in particular
`compound_tendsto_cauchy_of_identification`,
`integral_signedSmallSum_centered_sq`, `signedSmallSum_eq_range`,
`smallCenter_eq`, reports exactly
`[propext, Classical.choice, Quot.sound]`.  `principal_cauchy_law`,
`signed_small_jumps_variance` and `small_jumps_variance` additionally report
`sorryAx`, from the two declared inputs of this file and from nothing else. -/
