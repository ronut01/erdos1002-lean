import Kwon1002.Finale
import Kwon1002.FiveFinal

/-!
# Scratch (agent `finale-F`), the two §5 endpoints, on a two-element debt

Targets, both reproduced **token for token** (textually diffed against the
sources; each carries a trailing `_F` so the source name stays reachable
through the `open`s, and each is checked *inside Lean* by an
`example … := rfl` at the very bottom):

* `signed_small_jumps_variance_F`
    = `Kwon1002.Assembly5.signed_small_jumps_variance`
      (`Kwon1002/Assembly5.lean` line 356);
* `principal_cauchy_law_F`
    = `Kwon1002.principal_cauchy_law`
      (`Kwon1002/PoissonLimit.lean` line 46).

Neither closes outright: both sit below Proposition 4.1, which is only
*stated* in this development.  What this file delivers is the assembly of
both from a **two-element** named input set, together with two things that
were previously commentary rather than theorems.

## THE REMAINING DEBT (exactly two statements, both declared here)

1. `largeSum_charFun_limit`, the fixed-`ε` large-jump limit, as a limit of
   complex numbers attached to an explicit finite sum of reals:
   `∫_{(0,1)} exp(i t · largeSum c ε α n) dα → exp(∫_{|x|>ε}(e^{itx}−1) dΛ)`.
   No measure, no point process, no probability measure occurs in it.
2. `bulk_offdiagonal_abs_far_sharp`, Proposition 4.1 for **pairs**, with
   absolute values, with a bad set of pairs allowed to have cardinality
   `κ·L²/(1+log(2+L))³`.

Nothing else sorried is consumed.  In particular
`Kwon1002.xi_charFun_limit`, `Kwon1002.bulk_offdiagonal_far_sharp`,
`Kwon1002.bulk_offdiagonal_far'`, `OffDiag.bulk_offdiagonal_far`,
`L2Estimate.bulk_offdiagonal_input`, `SmallJumps.truncatedBulkSum_centered_L2`,
`SmallJumps.small_jumps_variance`, `Assembly5.largeJump_weak_limit`,
`Assembly5.signed_small_jumps_variance`, `Assembly5.compound_tendsto_cauchy`,
`Finale.bulkTerm_covariance_bound`,
`Finale.largeJump_weak_limit_compoundPoisson`,
`CompoundCauchy.largeJump_limit_compoundPoisson`,
`PoissonRoute.xi_largeIntegral_weak_limit`,
`LevyExponent.tuple_measure_convergence`,
`CauchyLaw.factorialMoment_convergence`, `CauchyLaw.levy_exponent_limit_raw`,
`CauchyLaw.integral_one_sub_cos_div_sq` and `CauchyLaw.charFun_cauchyProb`
are **not** consumed.

## What is new here, beyond re-assembling

**(a) The `L·H → L²/log³` sharpening is now machine-checked, not asserted.**
`Kwon1002/FiveFinal.lean` records, as *the only claim in its commentary that
is not machine-checked*, that the manuscript-shaped far-pair hypothesis (bad
set `O(L·H) = O(L^{7/4})`) implies the sharpened one (bad set
`κ·L²/(1+log(2+L))³`).  `abs_far_sharp_of_abs_far` below **proves** exactly
that implication for the absolute-value form, via the proved arithmetic
lemma `card_sharpen` (`κ·L·H·(1+log(2+L))³ ≤ 35937·κ·L²` for `L ≥ 1`).  So
input 2 above is a *strictly weaker* hypothesis than the manuscript's own,
and that is now a theorem of this file rather than a remark: whoever
discharges §4 may throw away almost `L` times more pairs than the manuscript
does.

**(b) The sign finding is machine-checked.**  The recorded finding is that
`Assembly5.signed_small_jumps_variance` (display (41), with the manuscript's
`U^{(ε)}_{n,j} = (−1)^j Z_{n,j} χ(·)`) is **not** derivable from
`Kwon1002.small_jumps_variance` (the same display, unsigned) by "the sign
squares away": that is true only on the diagonal, and the off-diagonal terms
carry `(−1)^{j+k}`.  `variance_not_monotone_under_sign` below is a
**proved counterexample** to the general principle the derivation would
need: two `[0,1]`-valued observables on `(0,1)` whose *unsigned* centred
second moment is `0` while their *signed* one is `1`.  Hence no bound of the
form "signed ≤ f(unsigned)" with `f 0 = 0` can exist, and the reduction taken
here, down to the sign-free absolute covariance sum, is not a matter of
taste.

## Consumed from elsewhere (all proved where they live, no sorries)

`Assembly5`: `signedSmallSum`, `smallCenter`, `largeProb`, `centeredBulkProb`,
`measurable_largeSum`, `dist_centeredBulk_largeProb_le`,
`exists_diagonal_tendsto`.
`Finale`: `integral_signedSmallSum_centered_sq`,
`compound_tendsto_cauchy_of_identification`.
`FiveFinal`: `near_pair_decay_sharp`.
`OffDiag`: `bulkTermCentered_offdiag_bound`.
`L2Estimate`: `truncatedMark_second_moment`, `bulk_window_input`,
`bulkTerm_sq_integral_le`, `diagonal_le_second_moment`, `sum_split_diag`.
`PoissonRoute`: `largeSum_eq_xi_setIntegral`, `largeProb_eq_xi_law`,
`exists_levy_truncation_data`, `truncSet`, `xiMeasure`.
`CompoundCauchy`: `charFun_compoundPoisson_levy`.
`CauchyLaw`: `cdf_tendsto_of_weak_convergence`.
Wang: `Erdos1002.levy_continuity_real`,
`Erdos1002.continuousCompoundPoissonProbability(_toMeasure)`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal Real

namespace Kwon1002

namespace CorFinal

open Assembly5

noncomputable section

/-! ## Part 0, a machine-checked counterexample to "the sign squares away"

The general principle a derivation of the *signed* display (41) from the
*unsigned* one would need is: a bound on the centred second moment of
`∑_j g_j` bounds that of `∑_j (−1)^j g_j`.  It is false, already for two
`[0,1]`-valued observables. -/

/-- `g 0 = 1_{(−∞,1/2)}`, `g 1 = 1 − g 0`, `g j = 0` for `j ≥ 2`. -/
def signWitness (j : ℕ) (α : ℝ) : ℝ :=
  if j = 0 then (if α < 1 / 2 then (1 : ℝ) else 0)
  else if j = 1 then (if α < 1 / 2 then (0 : ℝ) else 1) else 0

lemma signWitness_mem (j : ℕ) (α : ℝ) : signWitness j α ∈ Icc (0 : ℝ) 1 := by
  unfold signWitness
  split_ifs <;> norm_num

lemma signWitness_zero (α : ℝ) :
    signWitness 0 α = if α < 1 / 2 then (1 : ℝ) else 0 := rfl

lemma signWitness_one (α : ℝ) :
    signWitness 1 α = if α < 1 / 2 then (0 : ℝ) else 1 := rfl

lemma signWitness_sum (α : ℝ) : ∑ j ∈ Finset.range 2, signWitness j α = 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one, signWitness_zero, signWitness_one]
  split_ifs <;> norm_num

lemma signWitness_signedSum (α : ℝ) :
    ∑ j ∈ Finset.range 2, (-1 : ℝ) ^ j * signWitness j α
      = if α < 1 / 2 then (1 : ℝ) else -1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one, signWitness_zero, signWitness_one]
  split_ifs <;> norm_num

lemma integral_one_Ioo :
    (∫ _α in Ioo (0 : ℝ) 1, (1 : ℝ)) = 1 := by
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by norm_num)]
  norm_num

lemma integral_signWitness_signedSum :
    (∫ α in Ioo (0 : ℝ) 1, (if α < 1 / 2 then (1 : ℝ) else -1)) = 0 := by
  have hset : Iio (1 / 2 : ℝ) ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) (1 / 2) := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  have hfun : (fun α : ℝ => if α < 1 / 2 then (1 : ℝ) else -1)
      = fun α : ℝ => -1 + 2 * Set.indicator (Iio (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) α := by
    funext α
    simp only [Set.indicator_apply, mem_Iio]
    split_ifs <;> norm_num
  have hind : (∫ α in Ioo (0 : ℝ) 1,
      Set.indicator (Iio (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) α) = 1 / 2 := by
    rw [MeasureTheory.integral_indicator measurableSet_Iio, setIntegral_const,
      measureReal_restrict_apply measurableSet_Iio, hset,
      Real.volume_real_Ioo_of_le (by norm_num)]
    norm_num
  have hintind : Integrable
      (fun α : ℝ => Set.indicator (Iio (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) α)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine Integrable.indicator ?_ measurableSet_Iio
    exact integrable_const _
  rw [hfun, integral_add (integrable_const _) (hintind.const_mul 2),
    integral_const_mul, hind, setIntegral_const,
    Real.volume_real_Ioo_of_le (by norm_num)]
  norm_num

/-- **The sign cannot be bookkept away.**  Two observables with values in
`[0,1]` on `(0,1)` whose *unsigned* centred second moment vanishes while the
*signed* one equals `1`.

Consequently no inequality of the form "signed centred second moment
`≤ f(unsigned centred second moment)`" with `f 0 = 0`, in particular no
version of "the `(−1)^j` squares away", can hold; the derivation of
`Assembly5.signed_small_jumps_variance` from `Kwon1002.small_jumps_variance`
is impossible, and the common core must be taken one level lower, at the
sign-free absolute covariance sum.  That is what `bulkTerm_covariance_bound_F`
below is. -/
theorem variance_not_monotone_under_sign :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ j α, g j α ∈ Icc (0 : ℝ) 1) ∧
      (∫ α in Ioo (0 : ℝ) 1,
          (∑ j ∈ Finset.range 2, g j α
            - ∫ β in Ioo (0 : ℝ) 1, ∑ j ∈ Finset.range 2, g j β) ^ 2) = 0 ∧
      (∫ α in Ioo (0 : ℝ) 1,
          (∑ j ∈ Finset.range 2, (-1 : ℝ) ^ j * g j α
            - ∫ β in Ioo (0 : ℝ) 1, ∑ j ∈ Finset.range 2, (-1 : ℝ) ^ j * g j β) ^ 2)
        = 1 := by
  refine ⟨signWitness, signWitness_mem, ?_, ?_⟩
  · have hmean : (∫ β in Ioo (0 : ℝ) 1, ∑ j ∈ Finset.range 2, signWitness j β) = 1 := by
      simp only [signWitness_sum]
      exact integral_one_Ioo
    rw [hmean]
    have hpt : ∀ α : ℝ, (∑ j ∈ Finset.range 2, signWitness j α - 1) ^ 2 = 0 := by
      intro α
      rw [signWitness_sum]
      norm_num
    simp only [hpt]
    simp
  · have hmean : (∫ β in Ioo (0 : ℝ) 1,
        ∑ j ∈ Finset.range 2, (-1 : ℝ) ^ j * signWitness j β) = 0 := by
      simp only [signWitness_signedSum]
      exact integral_signWitness_signedSum
    rw [hmean]
    have hpt : ∀ α : ℝ,
        (∑ j ∈ Finset.range 2, (-1 : ℝ) ^ j * signWitness j α - 0) ^ 2 = 1 := by
      intro α
      rw [signWitness_signedSum, sub_zero]
      split_ifs <;> norm_num
    simp only [hpt]
    exact integral_one_Ioo

/-! ## Part I, the fixed-`ε` large-jump limit, with no measure in the residual

`Ξ_n` is `PoissonRoute.xiMeasure`, `truncSet ε = {x | ε < |x|}`, and
`largeSum c ε α n = ∫_{|x|>ε} x dΞ_n(α)` by the proved
`PoissonRoute.largeSum_eq_xi_setIntegral`. -/

/-- **Proved: the point-process layer is inessential.**  If `μ` is the law of
the large-jump functional `∫_{|x|>ε} x dΞ_n`, its characteristic function is
the plain oscillatory integral of the *explicit* finite sum `largeSum c ε · n`
over `α ∈ (0,1)`. -/
lemma charFun_largeSum_law (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (t : ℝ)
    (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in PoissonRoute.truncSet ε, x ∂(PoissonRoute.xiMeasure c α n))) :
    charFun (μ : Measure ℝ) t
      = ∫ α in Ioo (0 : ℝ) 1,
          Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I) := by
  have hfun : (fun α : ℝ => ∫ x in PoissonRoute.truncSet ε, x ∂(PoissonRoute.xiMeasure c α n))
      = fun α : ℝ => largeSum c ε α n :=
    funext fun α => (PoissonRoute.largeSum_eq_xi_setIntegral c ε hε α n).symm
  have hcont : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    fun_prop
  rw [hμ, hfun, charFun_apply_real,
    integral_map (measurable_largeSum c ε n).aemeasurable hcont.aestronglyMeasurable]
  simp only [unifIoo]

/-- **DEBT 1.**  The characteristic function of the manuscript's large-jump
sum converges to the compound-Poisson exponent of the truncated Lévy measure:

`∫_{(0,1)} exp(i t · L⁻¹ ∑_{j∈J_n} (−1)^j (Z_{n,j} − Z^{(ε)}_{n,j})) dα
   →  exp(∫_{|x|>ε} (e^{itx} − 1) dΛ(x))`.

**Obstruction.**  A limit of complex numbers attached to an explicit finite
sum of real random variables on `(0,1)`; it needs neither the vague topology
on Radon point measures on `ℝ∖{0}` nor a multivariate Poisson limit (the two
obstructions named in `PoissonRoute.xi_largeIntegral_weak_limit`), both of
which Lévy continuity and `charFun_largeSum_law` remove.  Writing
`h_j(α) = exp(i t X_{n,j}) − 1` on `{j ∈ J_n, |X_{n,j}| > ε}` and `0`
elsewhere, `Finset.prod_add` turns the left side into
`∑_{S ⊆ {0,…,n}} ∫ ∏_{j∈S} h_j`, whose `|S| = k` layer is `1/k!` times a §4
tuple sum for the bounded complex symbol `x ↦ (e^{itx}−1)·1{|x|>ε}`; the
uniform-in-`n` domination is available from the proved
`TupleMeasure.tuple_measure_le` and `L2Estimate.stoppingTime_le_log`.  What is
missing is the tuple limit for a complex symbol, Proposition 4.1. -/
theorem largeSum_charFun_limit (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ α in Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I)) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) := by
  sorry

/-- `Kwon1002.xi_charFun_limit` (the residual of `Kwon1002/FiveFinal.lean`),
reproduced token for token and **proved** from `largeSum_charFun_limit`. -/
theorem xi_charFun_limit_F (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) (t : ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in PoissonRoute.truncSet ε, x ∂(PoissonRoute.xiMeasure c α n))) :
    Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) := by
  have h : ∀ n : ℕ, charFun (μs n : Measure ℝ) t
      = ∫ α in Ioo (0 : ℝ) 1,
          Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I) :=
    fun n => charFun_largeSum_law c ε _hε0.le n t (μs n) (_hμs n)
  simp only [h]
  exact largeSum_charFun_limit c ε _hε0 _hε1 t

/-- `Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit`, reproduced token for
token and **proved** from `largeSum_charFun_limit`, by Lévy continuity
(`Erdos1002.levy_continuity_real`) and the compound-Poisson exponent identity
(`CompoundCauchy.charFun_compoundPoisson_levy`). -/
theorem xi_largeIntegral_weak_limit_F (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1)
    (r : ℝ≥0) (ν : ProbabilityMeasure ℝ)
    (_hrate : (r : ℝ≥0∞) = levyIntensity (PoissonRoute.truncSet ε))
    (_hjump : (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (PoissonRoute.truncSet ε))
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in PoissonRoute.truncSet ε, x ∂(PoissonRoute.xiMeasure c α n))) :
    Tendsto μs atTop (𝓝 (Erdos1002.continuousCompoundPoissonProbability r ν)) := by
  refine Erdos1002.levy_continuity_real μs _ (fun t => ?_)
  have hjump' : (r : ℝ≥0∞) • (ν : Measure ℝ)
      = levyIntensity.restrict {x : ℝ | ε < |x|} := _hjump
  have hcp : ((Erdos1002.continuousCompoundPoissonProbability r ν :
        ProbabilityMeasure ℝ) : Measure ℝ)
      = Erdos1002.continuousCompoundPoissonMeasure r ν :=
    Erdos1002.continuousCompoundPoissonProbability_toMeasure r ν
  rw [CompoundCauchy.charFun_compoundPoisson_levy _hε0 t
    (Erdos1002.continuousCompoundPoissonProbability r ν) r ν hjump' hcp]
  exact xi_charFun_limit_F c ε _hε0 _hε1 t μs _hμs

/-- The fixed-`ε` large-jump limit with the limit law **exhibited**. -/
theorem largeJump_tendsto_compoundPoisson_F (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity (PoissonRoute.truncSet ε) ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (PoissonRoute.truncSet ε) ∧
      Tendsto (fun n => largeProb c ε n) atTop
        (𝓝 (Erdos1002.continuousCompoundPoissonProbability r ν)) := by
  obtain ⟨r, ν, hrate, hjump⟩ := PoissonRoute.exists_levy_truncation_data hε0
  exact ⟨r, ν, hrate, hjump,
    xi_largeIntegral_weak_limit_F c ε hε0 hε1 r ν hrate hjump (fun n => largeProb c ε n)
      (fun n => PoissonRoute.largeProb_eq_xi_law c ε hε0.le n)⟩

/-- `Kwon1002.Assembly5.largeJump_weak_limit`, reproduced token for token. -/
theorem largeJump_weak_limit_F (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) := by
  obtain ⟨r, ν, -, -, hconv⟩ := largeJump_tendsto_compoundPoisson_F c ε _hε0 _hε1
  exact ⟨Erdos1002.continuousCompoundPoissonProbability r ν, hconv⟩

/-- `Kwon1002.Assembly5.compound_tendsto_cauchy`, reproduced token for token;
proved from `largeSum_charFun_limit` and the *proved*
`Finale.compound_tendsto_cauchy_of_identification`. -/
theorem compound_tendsto_cauchy_F (c : ℝ) (e : ℕ → ℝ)
    (_he0 : ∀ k, 0 < e k) (_he1 : ∀ k, e k < 1) (_he : Tendsto e atTop (𝓝 0))
    (ρ : ℕ → ProbabilityMeasure ℝ)
    (_hρ : ∀ k, Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 (ρ k))) :
    Tendsto ρ atTop (𝓝 cauchyProb) := by
  refine Finale.compound_tendsto_cauchy_of_identification e _he0 _he ρ fun k => ?_
  obtain ⟨r, ν, -, hjump, hconv⟩ :=
    largeJump_tendsto_compoundPoisson_F c (e k) (_he0 k) (_he1 k)
  have heq : ρ k = Erdos1002.continuousCompoundPoissonProbability r ν :=
    tendsto_nhds_unique (_hρ k) hconv
  refine ⟨r, ν, hjump, ?_⟩
  rw [heq, Erdos1002.continuousCompoundPoissonProbability_toMeasure]

/-! ## Part II, the covariance core, on a sharpened far-pair residual -/

/-- The absolute `(j,k)` summand of the off-diagonal double sum of (41). -/
def offdiagAbsTerm (c ε : ℝ) (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 = p.2 then 0 else
    |∫ α in Ioo (0 : ℝ) 1,
      bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2|

lemma sum_offdiagAbs_eq (c ε : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        (if j = k then 0 else
          |∫ α in Ioo (0 : ℝ) 1,
            bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|)
      = ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), offdiagAbsTerm c ε n p := by
  rw [Finset.sum_product]
  simp only [offdiagAbsTerm]

/-- **DEBT 2.**  Proposition 4.1 for **pairs**, with absolute values, with the
*sharpened* bad set: outside a set of pairs of cardinality
`κ·L²/(1+log(2+L))³` the absolute covariances sum to at most `ε/2`.

**Obstruction.**  Proposition 4.1 is only stated in this development
(`Kwon1002.prop_4_1_marked_factorization`, display (30), and
`Kwon1002.Prop41.prop_4_1_error_shape`).  The manuscript's route: cut each
digit at `A_L = L^D` with `D > 2`, Jackson-approximate the Lipschitz
truncation, and apply Proposition 4.1 with `A` so large that
`L²·O_A(L^{-A}) = o(1)`.

**Why the absolute values are the honest currency.**  Proposition 4.1 bounds
the *error* in each individual covariance, hence `|Cov(g_j,g_k)|` pair by
pair, never a cancellation between pairs; and only an absolute bound can
produce the manuscript's *signed* display (41), see
`variance_not_monotone_under_sign` above.

**Why the bad set is the sharp one.**  `abs_far_sharp_of_abs_far` below
*proves* that the manuscript-shaped hypothesis (bad set `κ·L·H = κ·L^{7/4}`)
implies this one, so this is a strictly weaker ask.

**Scope caveat, inherited.**  The sum runs over the deterministic range
`{0,…,n}` (with `bulkTerm` extended by `0` off the bulk), so this is
Proposition 4.1 for pairs *plus* the off-diagonal window tail: pairs with an
index beyond the stopping time still contribute `−E g_j · E g_k`.  The
diagonal analogue of that tail is discharged by the proved
`L2Estimate.bulk_window_input`, used in `diagonal_covariance_sum_bound_F`;
its off-diagonal analogue is **not** part of Proposition 4.1 and is folded
into this residual rather than hidden. -/
theorem bulk_offdiagonal_abs_far_sharp (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagAbsTerm c ε n p ≤ ε / 2 := by
  sorry

/-! ### The sharpening, machine-checked

`Kwon1002/FiveFinal.lean` records the implication "manuscript-shaped far-pair
hypothesis ⟹ sharpened one" as the single claim in its commentary that is not
machine-checked.  It is proved here. -/

/-- `1 + log(2+L) ≤ 33·L^{1/16}` for `L ≥ 1`.  (The estimate appears inline
inside the proof of `OffDiag.near_pair_decay`; it is isolated here.) -/
lemma logFactor_le_rpow {L : ℝ} (hL : 1 ≤ L) :
    1 + Real.log (2 + L) ≤ 33 * L ^ (1 / 16 : ℝ) := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  set v : ℝ := L ^ (1 / 16 : ℝ) with hv
  have hv0 : (0 : ℝ) < v := Real.rpow_pos_of_pos hL0 _
  have hv1 : (1 : ℝ) ≤ v := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL (by norm_num : (0:ℝ) ≤ 1/16)
    simpa [Real.one_rpow, hv] using h
  have hlog := Real.log_le_rpow_div (x := 2 + L) (by linarith)
    (show (0:ℝ) < 1/16 by norm_num)
  have hdiv : (2 + L) ^ (1/16:ℝ) / (1/16:ℝ) = 16 * (2 + L) ^ (1/16:ℝ) := by ring
  rw [hdiv] at hlog
  have h3L : (2:ℝ) + L ≤ 3 * L := by linarith
  have hmono : (2 + L) ^ (1/16:ℝ) ≤ (3 * L) ^ (1/16:ℝ) :=
    Real.rpow_le_rpow (by linarith) h3L (by norm_num)
  have hsplit : (3 * L) ^ (1/16:ℝ) = (3:ℝ) ^ (1/16:ℝ) * v := by
    rw [Real.mul_rpow (by norm_num) hL0.le, hv]
  have h3 : (3:ℝ) ^ (1/16:ℝ) ≤ 2 := by
    have h65 : (3:ℝ) ≤ 65536 := by norm_num
    have hle := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 3) h65
      (by norm_num : (0:ℝ) ≤ 1/16)
    have he : (65536:ℝ) ^ (1/16:ℝ) = 2 := by
      rw [show (65536:ℝ) = (2:ℝ) ^ (16:ℕ) by norm_num,
        ← Real.rpow_natCast (2:ℝ) 16, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [he] at hle
    exact hle
  have step2 : 16 * (2 + L) ^ (1/16:ℝ) ≤ 16 * ((3:ℝ) ^ (1/16:ℝ) * v) := by
    rw [← hsplit]; linarith
  have step3 : 16 * ((3:ℝ) ^ (1/16:ℝ) * v) ≤ 32 * v := by nlinarith [hv0.le]
  linarith

/-- **Proved arithmetic**: `κ·L·H ≤ 35937·κ·L²/(1+log(2+L))³` whenever
`L = Lnorm n ≥ 1`, where `H = Hscale n = L^{3/4}`.  In `v = L^{1/16}`:
`L = v¹⁶`, `H = v¹²`, `(1+log(2+L))³ ≤ 33³v³`, and `v³¹ ≤ v³²`. -/
lemma card_sharpen (κ : ℝ) (hκ : 0 ≤ κ) (n : ℕ) (hL : 1 ≤ Lnorm n) :
    κ * Lnorm n * Hscale n
      ≤ (35937 * κ) * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3 := by
  set L : ℝ := Lnorm n with hLdef
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  set U : ℝ := 1 + Real.log (2 + L) with hUdef
  have hU1 : (1 : ℝ) ≤ U := by
    have : (0 : ℝ) ≤ Real.log (2 + L) := Real.log_nonneg (by linarith)
    simp only [hUdef]; linarith
  have hUpos : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU1
  set v : ℝ := L ^ (1 / 16 : ℝ) with hv
  have hv0 : (0 : ℝ) < v := Real.rpow_pos_of_pos hL0 _
  have hv1 : (1 : ℝ) ≤ v := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL (by norm_num : (0:ℝ) ≤ 1/16)
    simpa [Real.one_rpow, hv] using h
  have hLv : L = v ^ (16 : ℕ) := by
    rw [hv, ← Real.rpow_natCast (L ^ (1/16:ℝ)) 16, ← Real.rpow_mul hL0.le]
    norm_num
  have hHv : Hscale n = v ^ (12 : ℕ) := by
    rw [Hscale, ← hLdef, hv, ← Real.rpow_natCast (L ^ (1/16:ℝ)) 12, ← Real.rpow_mul hL0.le]
    norm_num
  have hU33 : U ≤ 33 * v := by
    simpa [hUdef, hv] using logFactor_le_rpow hL
  have hcube : U ^ 3 ≤ 35937 * v ^ 3 := by
    have h := pow_le_pow_left₀ (le_trans zero_le_one hU1) hU33 3
    calc U ^ 3 ≤ (33 * v) ^ 3 := h
      _ = 35937 * v ^ 3 := by ring
  rw [le_div_iff₀ (by positivity)]
  have hv31 : v ^ (31 : ℕ) ≤ v ^ (32 : ℕ) := by
    have : v ^ (31 : ℕ) * 1 ≤ v ^ (31 : ℕ) * v :=
      mul_le_mul_of_nonneg_left hv1 (by positivity)
    calc v ^ (31 : ℕ) = v ^ (31 : ℕ) * 1 := by ring
      _ ≤ v ^ (31 : ℕ) * v := this
      _ = v ^ (32 : ℕ) := by ring
  calc κ * L * Hscale n * U ^ 3
      = (κ * v ^ (28 : ℕ)) * U ^ 3 := by rw [hHv, hLv]; ring
    _ ≤ (κ * v ^ (28 : ℕ)) * (35937 * v ^ 3) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 35937 * κ * v ^ (31 : ℕ) := by ring
    _ ≤ 35937 * κ * v ^ (32 : ℕ) := by
        refine mul_le_mul_of_nonneg_left hv31 (by positivity)
    _ = 35937 * κ * L ^ 2 := by rw [hLv]; ring

/-- **The sharpening, proved.**  The manuscript-shaped absolute far-pair
hypothesis (bad set `κ·L·H`) implies the sharpened one (bad set
`κ'·L²/(1+log(2+L))³`) of `bulk_offdiagonal_abs_far_sharp`.  So DEBT 2 is a
*strictly weaker* statement than Proposition 4.1 for pairs in the
manuscript's own shape, and this is now a theorem, not a remark. -/
theorem abs_far_sharp_of_abs_far (c : ℝ)
    (h : ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagAbsTerm c ε n p ≤ ε / 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagAbsTerm c ε n p ≤ ε / 2 := by
  obtain ⟨κ, hκ, hfar⟩ := h
  refine ⟨35937 * κ, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨N, hN⟩ := hfar ε hε hε1
  refine ⟨max N 3, fun n hn => ?_⟩
  obtain ⟨B, hBcard, hBfar⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL : (1 : ℝ) ≤ Lnorm n := by
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hexp : Real.exp 1 ≤ (n : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    simp only [Lnorm]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  exact ⟨B, le_trans hBcard (card_sharpen κ hκ.le n hL), hBfar⟩

/-- **Proved from `bulk_offdiagonal_abs_far_sharp`**: the absolute
off-diagonal double sum is `≤ ε` for all large `n`.  Proof body:
`Kwon1002.bulk_offdiagonal_input''` of `FiveFinal.lean`, with absolute values
(which *simplifies* it: `OffDiag.bulkTermCentered_offdiag_bound` is already a
bound on `|Cov|`). -/
theorem bulk_offdiagonal_abs_input (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            |∫ α in Ioo (0 : ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|) ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hpair⟩ := OffDiag.bulkTermCentered_offdiag_bound c
  obtain ⟨κ, hκ, hfar⟩ := bulk_offdiagonal_abs_far_sharp c
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
lemma diagonal_covariance_sum_bound_F (c : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∑ j ∈ Finset.range (n + 1),
            ∫ α in Ioo (0 : ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
          ≤ D * ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C₂, hC₂, hsm⟩ := L2Estimate.truncatedMark_second_moment
  obtain ⟨κ, hκ, hwin⟩ := L2Estimate.bulk_window_input c
  refine ⟨κ * C₂ + 1, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hwin ε hε hε1
  refine ⟨max N₁ 2, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨S, hSsub, hScard, hStail⟩ := hN₁ n hn1
  have hdiagterm : ∀ j : ℕ,
      (∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2 :=
    fun j => L2Estimate.diagonal_le_second_moment c ε hε n j
  have hSbound : (∑ j ∈ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε := by
    calc (∑ j ∈ S,
        ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∑ _j ∈ S, (C₂ * ε / Lnorm n) := by
          refine Finset.sum_le_sum fun j _ => le_trans (hdiagterm j) ?_
          exact L2Estimate.bulkTerm_sq_integral_le c ε hε n j hL C₂ (hsm ε hε.le n j)
      _ = (S.card : ℝ) * (C₂ * ε / Lnorm n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (κ * Lnorm n) * (C₂ * ε / Lnorm n) := by
          refine mul_le_mul_of_nonneg_right hScard ?_
          have : (0:ℝ) ≤ C₂ * ε := by positivity
          positivity
      _ = κ * C₂ * ε := by field_simp
  have hRestBound : (∑ j ∈ Finset.range (n + 1) \ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ ε :=
    le_trans (Finset.sum_le_sum fun j _ => hdiagterm j) hStail
  rw [← Finset.sum_sdiff hSsub]
  have hfinal : κ * C₂ * ε + ε ≤ (κ * C₂ + 1) * ε := le_of_eq (by ring)
  linarith [hSbound, hRestBound, hfinal]

/-- `Kwon1002.Finale.bulkTerm_covariance_bound`, reproduced token for token
and **proved** from `bulk_offdiagonal_abs_far_sharp` alone. -/
theorem bulkTerm_covariance_bound_F (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            |∫ α in Ioo (0 : ℝ) 1,
                bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|)
          ≤ C * ε := by
  classical
  obtain ⟨D, hD, hdiag⟩ := diagonal_covariance_sum_bound_F c
  refine ⟨D + 1, by linarith, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hdiag ε hε hε1
  obtain ⟨N₂, hN₂⟩ := bulk_offdiagonal_abs_input c ε hε hε1
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

/-! ## Part III, TARGET 1: Lemma 5.2 with the alternating sign -/

/-- **TARGET 1**, `Kwon1002.Assembly5.signed_small_jumps_variance`
(`Kwon1002/Assembly5.lean` line 356), display (41), reproduced token for
token.  Proved from `bulk_offdiagonal_abs_far_sharp` and nothing else
sorried.

The route is forced: by `variance_not_monotone_under_sign` the signed
statement does **not** follow from the unsigned `Kwon1002.small_jumps_variance`,
so the common core is taken at the sign-free absolute covariance sum
`bulkTerm_covariance_bound_F`, which dominates the signed covariance
expansion `∑_{j,k}(−1)^{j+k}Cov(g_j,g_k)` term by term. -/
theorem signed_small_jumps_variance_F (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo) ≤ C * ε := by
  obtain ⟨C, hC, hcov⟩ := bulkTerm_covariance_bound_F c
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

/-! ## Part IV, TARGET 2: Corollary 5.3

The ε/3 assembly of `Assembly5`/`Finale`, re-run against the two debts. -/

/-- **TARGET 2**, `Kwon1002.principal_cauchy_law` (`Kwon1002/PoissonLimit.lean`
line 46), Corollary 5.3, display (43), reproduced token for token.

Proved from exactly two sorried statements, both declared in this file:
`largeSum_charFun_limit` and `bulk_offdiagonal_abs_far_sharp`. -/
theorem principal_cauchy_law_F (c : ℝ) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  classical
  obtain ⟨C, hC, hvar⟩ := signed_small_jumps_variance_F c
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
    largeJump_weak_limit_F c (e k) (he0 k) (he1 k)
  choose ρ hρ using hlarge
  have hcauchy : Tendsto ρ atTop (𝓝 cauchyProb) :=
    compound_tendsto_cauchy_F c e he0 he1 helim ρ hρ
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

end CorFinal

end Kwon1002

/- **Token-identity checks.**  Each `example` forces the statement above to be
the *same type* as its shared-file target (`rfl` then closes it by proof
irrelevance).  They mention sorried declarations, so they are anonymous and
nothing proved above depends on them. -/
example : @Kwon1002.Assembly5.signed_small_jumps_variance
    = @Kwon1002.CorFinal.signed_small_jumps_variance_F := rfl

example : @Kwon1002.principal_cauchy_law
    = @Kwon1002.CorFinal.principal_cauchy_law_F := rfl

example : @Kwon1002.Assembly5.principal_cauchy_law
    = @Kwon1002.CorFinal.principal_cauchy_law_F := rfl

example : @Kwon1002.Assembly5.largeJump_weak_limit
    = @Kwon1002.CorFinal.largeJump_weak_limit_F := rfl

example : @Kwon1002.Assembly5.compound_tendsto_cauchy
    = @Kwon1002.CorFinal.compound_tendsto_cauchy_F := rfl

example : @Kwon1002.xi_charFun_limit
    = @Kwon1002.CorFinal.xi_charFun_limit_F := rfl

example : @Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit
    = @Kwon1002.CorFinal.xi_largeIntegral_weak_limit_F := rfl

example : @Kwon1002.Finale.bulkTerm_covariance_bound
    = @Kwon1002.CorFinal.bulkTerm_covariance_bound_F := rfl

/- **Axiom check** (`#print axioms`, run and then removed, per the fleet
contract).  Everything proved outright here, `signWitness_mem`,
`signWitness_sum`, `signWitness_signedSum`, `integral_one_Ioo`,
`integral_signWitness_signedSum`, `variance_not_monotone_under_sign`,
`charFun_largeSum_law`, `logFactor_le_rpow`, `card_sharpen`,
`abs_far_sharp_of_abs_far`, `sum_offdiagAbs_eq`,
`diagonal_covariance_sum_bound_F`, reports exactly
`[propext, Classical.choice, Quot.sound]`.  Everything else
(`xi_charFun_limit_F`, `xi_largeIntegral_weak_limit_F`,
`largeJump_tendsto_compoundPoisson_F`, `largeJump_weak_limit_F`,
`compound_tendsto_cauchy_F`, `bulk_offdiagonal_abs_input`,
`bulkTerm_covariance_bound_F`, `signed_small_jumps_variance_F`,
`principal_cauchy_law_F`) reports those three plus `sorryAx`, coming from the
two residuals declared in this file (`largeSum_charFun_limit`,
`bulk_offdiagonal_abs_far_sharp`) and from nothing else: a name-level scan of
the whole tree confirms that no other sorried declaration is mentioned
anywhere in this file's body. -/
