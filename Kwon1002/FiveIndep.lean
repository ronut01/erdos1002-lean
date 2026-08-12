import Kwon1002.PoissonRoute
import Kwon1002.OffDiagonal
import Kwon1002.Finale
import Kwon1002.FiveFinal

/-!
# Scratch (agent `five-A`), the three §5 targets

Targets, all three reproduced **token for token** (diffed against the sources;
each carries a prime so that the source name stays reachable through the
`open`s at the head of the file, and each is checked inside Lean by an
`example … := rfl` at the very bottom):

* `largeJump_limit_compoundPoisson'`
    = `Kwon1002.CompoundCauchy.largeJump_limit_compoundPoisson`
      (`Kwon1002/CompoundCauchy.lean` line 254);
* `xi_largeIntegral_weak_limit'`
    = `Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit`
      (`Kwon1002/PoissonRoute.lean` line 409);
* `bulkTerm_covariance_bound'`
    = `Kwon1002.Finale.bulkTerm_covariance_bound`
      (`Kwon1002/Finale.lean` line 183).

None of the three closes outright: each sits below Proposition 4.1, which is
only *stated* in this development.  What this file delivers is, for each, a
strictly tighter reduction, together with the residual stated in the currency
the discharging argument actually produces.

## Part I, targets 1 and 2: a residual with no measures in it

`Kwon1002/FiveFinal.lean` already reduced both to one scalar limit,
`Kwon1002.xi_charFun_limit`, using Lévy continuity.  That residual is still
phrased through a *family of laws* `μs` constrained by a hypothesis about the
point process `Ξ_n`.  Here it is pushed one step further, to

  `largeSum_charFun_limit` :
      `∫_{(0,1)} exp(i t · largeSum c ε α n) dα  →  exp(∫_{|x|>ε}(e^{itx}-1) dΛ)`,

a limit of complex numbers attached to an **explicit finite sum of reals**
(`Assembly5.largeSum c ε α n = L⁻¹ ∑_{j ∈ J_n} (-1)^j (Z_{n,j} − Z^{(ε)}_{n,j})`)
integrated over `α ∈ (0,1)`.  No measure, no point process, no probability
measure appears in the residual: the whole `μs`/`Ξ_n` layer is *discharged*
here by `charFun_largeSum_law` (proved), which identifies
`charFun (μs n) t` with that oscillatory integral via the proved
`PoissonRoute.largeSum_eq_xi_setIntegral` and `integral_map`.

That the new residual is at least as strong as the previous one is
machine-checked: `xi_charFun_limit'` below reproduces
`Kwon1002.xi_charFun_limit` token for token (checked by `rfl`) and is
**proved** from `largeSum_charFun_limit`.

## Part II, target 3: the diagonal is discharged, the residual is off-diagonal

`Finale.bulkTerm_covariance_bound` is `∑_{j,k ≤ n} |Cov(g_j,g_k)| ≤ Cε`.
It is proved here from a single input,

  `bulk_offdiagonal_abs_far`, Proposition 4.1 *for pairs, with absolute
  values*: outside a bad set of pairs of the manuscript's own cardinality
  `O(L·H)`, the **absolute** covariances sum to `≤ ε/2`,

and nothing else sorried.  Everything else is proved here:

* the diagonal `∑_j Cov(g_j,g_j) ≤ (κC₂+1)ε` (`diagonal_covariance_sum_bound`),
  out of the proved `L2Estimate.bulk_window_input` (itself out of the Lamé
  bound `stoppingTime_le_log`), `L2Estimate.truncatedMark_second_moment`
  (display (42)'s first half) and `L2Estimate.diagonal_le_second_moment`;
* the near-pair half of the off-diagonal, out of the proved
  `OffDiag.bulkTermCentered_offdiag_bound` (display (42)'s second half, note
  it is *already* an absolute-value bound, which is why the absolute
  formulation costs nothing on the near pairs) and `OffDiag.near_pair_decay`;
* the diagonal/off-diagonal split with absolute values
  (`sum_offdiagAbs_eq`, `L2Estimate.sum_split_diag`), using that the diagonal
  covariance is a variance, hence already nonnegative.

**Honest comparison with `OffDiag.bulk_offdiagonal_far`.**
`bulk_offdiagonal_abs_far` is *strictly stronger* than
`OffDiag.bulk_offdiagonal_far` (absolute values inside the far-pair sum).  It
is not a weakening dressed up: it is the currency the manuscript's own
argument produces, since Proposition 4.1 bounds the *error* in each individual
covariance and therefore controls `|Cov(g_j,g_k)|` pair by pair, never a
cancellation between pairs.  It is also the only currency from which the
*signed* display (41) can follow, see the finding recorded in the header of
`Kwon1002/Finale.lean`, and Part III below.  The bad set is kept at the
manuscript's `O(L·H)`; `Kwon1002.bulk_offdiagonal_far_sharp` of
`Kwon1002/FiveFinal.lean` shows it could be enlarged to
`κL²/(1+log(2+L))³`, and the same relaxation applies verbatim here (only
`OffDiag.near_pair_decay` would be swapped for
`Kwon1002.near_pair_decay_sharp`).

## Part III, the whole of §5 on two residuals

`principal_cauchy_law'` (Corollary 5.3, display (43), reproduced token for
token) is proved here from **exactly two** sorried statements:
`largeSum_charFun_limit` (Part I) and `bulk_offdiagonal_abs_far` (Part II).
The proof bodies of `Kwon1002/Finale.lean` are reused verbatim with its two
declared inputs replaced by the reductions above.

## Sorried results consumed

* **None** beyond the two residuals stated in this file
  (`largeSum_charFun_limit`, `bulk_offdiagonal_abs_far`).

In particular `LevyExponent.tuple_measure_convergence`,
`OffDiag.bulk_offdiagonal_far`, `L2Estimate.bulk_offdiagonal_input`,
`SmallJumps.truncatedBulkSum_centered_L2`, `SmallJumps.small_jumps_variance`,
`Assembly5.largeJump_weak_limit`, `Assembly5.signed_small_jumps_variance`,
`Assembly5.compound_tendsto_cauchy`,
`CompoundCauchy.largeJump_limit_compoundPoisson`,
`PoissonRoute.xi_largeIntegral_weak_limit`,
`Finale.bulkTerm_covariance_bound`,
`Finale.largeJump_weak_limit_compoundPoisson`,
`Kwon1002.xi_charFun_limit`, `CauchyLaw.factorialMoment_convergence`,
`CauchyLaw.charFun_cauchyProb`, `CauchyLaw.levy_exponent_limit_raw` and
`CauchyLaw.integral_one_sub_cos_div_sq` are **not** consumed.

## Checks actually run

* Every reproduced statement was **textually diffed** against its source
  (identical modulo the trailing prime on the name), and each is additionally
  checked *inside Lean* by an `example … := rfl` at the bottom of the file, so
  the elaborated `Prop`s coincide, not merely the surface syntax.
* `#print axioms` was run on every declaration and then removed.
  `charFun_largeSum_law`, `sum_offdiagAbs_eq` and
  `diagonal_covariance_sum_bound`, everything proved outright, report exactly
  `[propext, Classical.choice, Quot.sound]`.  Everything else reports those
  three plus `sorryAx`, coming from the two residuals declared in this file and
  from nothing else.

## One inherited caveat, stated rather than hidden

The double sums of `bulkTerm_covariance_bound` run over the *deterministic*
range `{0,…,n}` (with `bulkTerm` extended by `0` off the bulk), whereas the
manuscript's (41) sums over the random `J_n`.  Pairs `(j,k)` with `j` or `k`
beyond the stopping time therefore still contribute `−E g_j · E g_k`, and
controlling them is *not* part of Proposition 4.1: it is the off-diagonal
analogue of the already-proved `L2Estimate.bulk_window_input` (which does that
job for the diagonal, and is used here).  As in
`OffDiag.bulk_offdiagonal_far`, that bookkeeping is folded into
`bulk_offdiagonal_abs_far` rather than isolated, so that residual is
Proposition 4.1 for pairs **plus** the off-diagonal window tail.  Splitting it
is the natural next refinement; the diagonal half of the split is what
`diagonal_covariance_sum_bound` below discharges.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal Real

namespace Kwon1002

namespace FiveIndep

open Assembly5 PoissonRoute OffDiag

noncomputable section

/-! ## Part I, the fixed-`ε` large-jump limit

`Ξ_n` is `PoissonRoute.xiMeasure`, `truncSet ε = {x | ε < |x|}`, and
`largeSum c ε α n = ∫_{|x|>ε} x dΞ_n(α)` by the proved
`PoissonRoute.largeSum_eq_xi_setIntegral`. -/

/-- **Proved: the point-process layer is inessential.**  If `μ` is the law of
the large-jump functional `∫_{|x|>ε} x dΞ_n` of the point process, then its
characteristic function is the plain oscillatory integral of the *explicit*
finite sum `largeSum c ε · n` over `α ∈ (0,1)`.

This is what lets the residual of Part I be stated with no measure in it. -/
lemma charFun_largeSum_law (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (t : ℝ)
    (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n))) :
    charFun (μ : Measure ℝ) t
      = ∫ α in Ioo (0 : ℝ) 1,
          Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I) := by
  have hfun : (fun α : ℝ => ∫ x in truncSet ε, x ∂(xiMeasure c α n))
      = fun α : ℝ => largeSum c ε α n :=
    funext fun α => (largeSum_eq_xi_setIntegral c ε hε α n).symm
  have hcont : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    fun_prop
  rw [hμ, hfun, charFun_apply_real,
    integral_map (measurable_largeSum c ε n).aemeasurable hcont.aestronglyMeasurable]
  simp only [unifIoo]

/-- **THE RESIDUAL OF PART I.**  The characteristic function of the
manuscript's large-jump sum converges to the compound-Poisson exponent of the
truncated Lévy measure:

`∫_{(0,1)} exp(i t · L⁻¹ ∑_{j∈J_n} (-1)^j (Z_{n,j} − Z^{(ε)}_{n,j})) dα
   →  exp(∫_{|x|>ε} (e^{itx} − 1) dΛ(x))`.

**Why this is the right residual.**  It is a limit of complex numbers attached
to an explicit finite sum of real random variables on `(0,1)`, so it needs
neither the vague topology on Radon point measures on `ℝ∖{0}` nor a
multivariate Poisson limit, the two obstructions named in the docstring of
`PoissonRoute.xi_largeIntegral_weak_limit`.  Lévy continuity
(`Erdos1002.levy_continuity_real`, proved in the substrate) removes them, and
`charFun_largeSum_law` above removes the point-process layer as well.

**How far it can be pushed with what is already proved.**  Writing
`h_j(α) = exp(i t X_{n,j}) − 1` on `{j ∈ J_n, |X_{n,j}| > ε}` and `0`
elsewhere, one has `exp(i t · largeSum) = ∏_{j ≤ n}(1 + h_j)` pointwise a.e.
(`bulkIndices_subset_range`, proved), hence by `Finset.prod_add`

  `∫ exp(i t · largeSum) = ∑_{S ⊆ {0,…,n}} ∫ ∏_{j ∈ S} h_j`,

and the `|S| = k` layer is `1/k!` times a §4 tuple sum for the bounded complex
symbol `x ↦ (e^{itx} − 1)·1{|x| > ε}`, the currency of
`LevyExponent.tuple_measure_convergence`, with `Λ(B)` replaced by
`∫(e^{itx}−1) dΛ`.  The uniform-in-`n` domination needed to interchange the
`k`-sum with `n → ∞` is available from the proved
`TupleMeasure.tuple_measure_le` together with the Lamé bound
`L2Estimate.stoppingTime_le_log`.  What is missing is the tuple limit itself
for a complex symbol, i.e. Proposition 4.1; reducing further would only trade
this statement for §4 again. -/
theorem largeSum_charFun_limit (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ α in Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I)) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) := by
  sorry

/-- `Kwon1002.xi_charFun_limit` (the residual of `Kwon1002/FiveFinal.lean`),
reproduced token for token and **proved** from `largeSum_charFun_limit`.  So
the residual of this file is at least as strong as the previous best one; the
converse holds too, by the same `charFun_largeSum_law` read right to left. -/
theorem xi_charFun_limit' (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) (t : ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n))) :
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

/-- **Target 2**, `Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit`
(`Kwon1002/PoissonRoute.lean` line 409), reproduced token for token and
**proved** from `largeSum_charFun_limit`.

Ingredients, both proved: Lévy's continuity theorem on `ℝ`
(`Erdos1002.levy_continuity_real`) and the compound-Poisson exponent identity
`charFun CP(r,ν) t = exp(∫_{|x|>ε}(e^{itx}−1) dΛ)` for `r·ν = Λ|_{|x|>ε}`
(`CompoundCauchy.charFun_compoundPoisson_levy`).  Only `_hjump` is used of the
two Lévy-data hypotheses, exactly as recorded there. -/
theorem xi_largeIntegral_weak_limit' (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1)
    (r : ℝ≥0) (ν : ProbabilityMeasure ℝ)
    (_hrate : (r : ℝ≥0∞) = levyIntensity (truncSet ε))
    (_hjump : (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (truncSet ε))
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n))) :
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
  exact xi_charFun_limit' c ε _hε0 _hε1 t μs _hμs

/-- The fixed-`ε` large-jump limit with the limit law **exhibited**: the
truncated Lévy data is produced by `PoissonRoute.exists_levy_truncation_data`
(proved), not quantified over. -/
theorem largeJump_tendsto_compoundPoisson' (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity (truncSet ε) ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (truncSet ε) ∧
      Tendsto (fun n => largeProb c ε n) atTop
        (𝓝 (Erdos1002.continuousCompoundPoissonProbability r ν)) := by
  obtain ⟨r, ν, hrate, hjump⟩ := PoissonRoute.exists_levy_truncation_data hε0
  exact ⟨r, ν, hrate, hjump,
    xi_largeIntegral_weak_limit' c ε hε0 hε1 r ν hrate hjump (fun n => largeProb c ε n)
      (fun n => PoissonRoute.largeProb_eq_xi_law c ε hε0.le n)⟩

/-- **Target 1**, `Kwon1002.CompoundCauchy.largeJump_limit_compoundPoisson`
(`Kwon1002/CompoundCauchy.lean` line 254), reproduced token for token and
**proved** from `largeSum_charFun_limit` alone: weak limits in
`ProbabilityMeasure ℝ` are unique, and `largeJump_tendsto_compoundPoisson'`
identifies the limit. -/
theorem largeJump_limit_compoundPoisson' (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ρ : ProbabilityMeasure ℝ)
    (hρ : Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ)) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity {x : ℝ | ε < |x|} ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict {x : ℝ | ε < |x|} ∧
      (ρ : Measure ℝ) = Erdos1002.continuousCompoundPoissonMeasure r ν := by
  obtain ⟨r, ν, hrate, hjump, hconv⟩ := largeJump_tendsto_compoundPoisson' c ε hε0 hε1
  have huniq : ρ = Erdos1002.continuousCompoundPoissonProbability r ν :=
    tendsto_nhds_unique hρ hconv
  exact ⟨r, ν, hrate, hjump,
    by rw [huniq, Erdos1002.continuousCompoundPoissonProbability_toMeasure]⟩

/-! ## Part II, target 3: `∑_{j,k} |Cov(g_j,g_k)| ≤ Cε` -/

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

/-- **THE RESIDUAL OF PART II**, Proposition 4.1 for pairs, *with absolute
values*.  Outside a bad set of pairs of the manuscript's own cardinality
`O(L·H)` (the overlapping, `H`-near and resonance-near pairs), the absolute
covariances sum to at most `ε/2`.

**Obstruction.**  Proposition 4.1 is itself only stated in this development
(`Kwon1002.prop_4_1_marked_factorization`, display (30), and
`Kwon1002.Prop41.prop_4_1_error_shape`).  The manuscript's route: cut each
digit at `A_L = L^D` with `D > 2`, Jackson-approximate the Lipschitz
truncation, and apply Proposition 4.1 with `A` so large that
`L²·O_A(L^{-A}) = o(1)`.

**Relation to `OffDiag.bulk_offdiagonal_far`.**  Strictly stronger, the
absolute values sit inside the far-pair sum.  It is nevertheless the honest
currency: Proposition 4.1 delivers an error bound on each individual
covariance, hence on each `|Cov(g_j,g_k)|`, and never a cancellation between
pairs; and only an absolute bound can produce the manuscript's *signed*
display (41), whose `(−1)^{j+k}` off-diagonal factors are not controlled by
any unsigned variance statement (the finding recorded in the header of
`Kwon1002/Finale.lean`).

**Room to spare.**  The bad set may be enlarged from `κ·L·H = κ·L^{7/4}` to
`κ·L²/(1+log(2+L))³` at no cost: replace `OffDiag.near_pair_decay` below by
the proved `Kwon1002.near_pair_decay_sharp`.

**Scope caveat, inherited from `OffDiag.bulk_offdiagonal_far`.**  The sum runs
over the deterministic range, so this statement is Proposition 4.1 for pairs
*plus* the off-diagonal window tail (pairs with an index beyond the stopping
time, contributing `−E g_j · E g_k`).  See the header. -/
theorem bulk_offdiagonal_abs_far (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagAbsTerm c ε n p ≤ ε / 2 := by
  sorry

/-- **Proved from `bulk_offdiagonal_abs_far`**: the absolute off-diagonal
double sum is `≤ ε` for all large `n`.  This is
`Kwon1002.L2Estimate.bulk_offdiagonal_input` with absolute values; the proof
body is `OffDiag.bulk_offdiagonal_input'` verbatim, and it *simplifies*,
because `OffDiag.bulkTermCentered_offdiag_bound` (display (42), proved) is
already a bound on `|Cov|`. -/
theorem bulk_offdiagonal_abs_input (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            |∫ α in Ioo (0 : ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|) ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hpair⟩ := bulkTermCentered_offdiag_bound c
  obtain ⟨κ, hκ, hfar⟩ := bulk_offdiagonal_abs_far c
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hfar ε hε hε1
  obtain ⟨N₂, hN₂⟩ := near_pair_decay κ Cp (ε / 2) hκ hCp (by positivity)
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
    have hcard : (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ) ≤ κ * Lnorm n * Hscale n := by
      refine le_trans ?_ hBcard
      exact_mod_cast Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).2)
    calc (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2)
        ≤ (κ * Lnorm n * Hscale n)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard hQ0
      _ ≤ ε / 2 := hN₂ n hn2
  have hfarsum : (∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagAbsTerm c ε n p) ≤ ε / 2 := by
    rw [hnotB]
    exact hBfar
  linarith [hsplit, hnear, hfarsum]

/-- **Proved, unconditionally**: the diagonal of the covariance sum is `O(ε)`.

`∑_{j ≤ n} Cov(g_j,g_j) ≤ (κC₂)ε + ε`, out of the proved
`L2Estimate.bulk_window_input` (only `O(L)` levels matter, the Lamé bound
`stoppingTime_le_log`), `L2Estimate.truncatedMark_second_moment` (display
(42), first half: `E|Z^{(ε)}_{n,j}|² ≤ C ε L`, itself from the uniform tail
`digit_tail_product` of Lem 3.1(ii)) and
`L2Estimate.diagonal_le_second_moment`. -/
lemma diagonal_covariance_sum_bound (c : ℝ) :
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

/-- **Target 3**, `Kwon1002.Finale.bulkTerm_covariance_bound`
(`Kwon1002/Finale.lean` line 183), reproduced token for token and **proved**
from `bulk_offdiagonal_abs_far` alone.

The split is `∑_{j,k}|Cov| = ∑_j Cov(g_j,g_j) + ∑_{j≠k}|Cov(g_j,g_k)|`, using
that the diagonal covariance is a variance (so its absolute value is itself);
the first sum is `diagonal_covariance_sum_bound` (proved), the second is
`bulk_offdiagonal_abs_input`. -/
theorem bulkTerm_covariance_bound' (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            |∫ α in Ioo (0 : ℝ) 1,
                bulkTermCentered c ε α n j * bulkTermCentered c ε α n k|)
          ≤ C * ε := by
  classical
  obtain ⟨D, hD, hdiag⟩ := diagonal_covariance_sum_bound c
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

/-! ## Part III, the whole of §5 on the two residuals

Everything from here on is `Kwon1002/Finale.lean`'s assembly re-run against
the two reductions above, so that Corollary 5.3 rests on
`largeSum_charFun_limit` and `bulk_offdiagonal_abs_far` and on nothing else
sorried.  `Finale.integral_signedSmallSum_centered_sq` and
`Finale.compound_tendsto_cauchy_of_identification` are used as-is: both are
proved outright there. -/

/-- **Lemma 5.2 with the sign**, `Kwon1002.Assembly5.signed_small_jumps_variance`,
reproduced token for token; proof body `Finale.signed_small_jumps_variance`
verbatim, fed by `bulkTerm_covariance_bound'`. -/
theorem signed_small_jumps_variance' (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo) ≤ C * ε := by
  obtain ⟨C, hC, hcov⟩ := bulkTerm_covariance_bound' c
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

/-- `Kwon1002.Finale.largeJump_weak_limit_compoundPoisson` (its input 2),
reproduced token for token and **proved** from `largeSum_charFun_limit`. -/
theorem largeJump_weak_limit_compoundPoisson' (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (ρ : ProbabilityMeasure ℝ) (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) ∧
      (r : ℝ≥0∞) = levyIntensity {x : ℝ | ε < |x|} ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict {x : ℝ | ε < |x|} ∧
      (ρ : Measure ℝ) = Erdos1002.continuousCompoundPoissonMeasure r ν := by
  obtain ⟨r, ν, hrate, hjump, hconv⟩ := largeJump_tendsto_compoundPoisson' c ε hε0 hε1
  exact ⟨Erdos1002.continuousCompoundPoissonProbability r ν, r, ν, hconv, hrate, hjump,
    Erdos1002.continuousCompoundPoissonProbability_toMeasure r ν⟩

/-- `Kwon1002.Assembly5.largeJump_weak_limit`, reproduced token for token. -/
theorem largeJump_weak_limit' (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) := by
  obtain ⟨ρ, _r, _ν, hlim, _, _, _⟩ := largeJump_weak_limit_compoundPoisson' c ε _hε0 _hε1
  exact ⟨ρ, hlim⟩

/-- `Kwon1002.Assembly5.compound_tendsto_cauchy`, reproduced token for token;
proof body `Finale.compound_tendsto_cauchy` verbatim. -/
theorem compound_tendsto_cauchy' (c : ℝ) (e : ℕ → ℝ)
    (_he0 : ∀ k, 0 < e k) (_he1 : ∀ k, e k < 1) (_he : Tendsto e atTop (𝓝 0))
    (ρ : ℕ → ProbabilityMeasure ℝ)
    (_hρ : ∀ k, Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 (ρ k))) :
    Tendsto ρ atTop (𝓝 cauchyProb) := by
  refine Finale.compound_tendsto_cauchy_of_identification e _he0 _he ρ fun k => ?_
  obtain ⟨ρ', r, ν, hlim, _hrate, hjump, hcp⟩ :=
    largeJump_weak_limit_compoundPoisson' c (e k) (_he0 k) (_he1 k)
  have heq : ρ k = ρ' := tendsto_nhds_unique (_hρ k) hlim
  exact ⟨r, ν, hjump, by rw [heq]; exact hcp⟩

/-- **Corollary 5.3** (Principal Cauchy law), display (43) -
`Kwon1002.principal_cauchy_law`, reproduced token for token.

Proved from exactly two sorried statements, both declared in this file:
`largeSum_charFun_limit` and `bulk_offdiagonal_abs_far`.  Proof body:
`Finale.principal_cauchy_law` verbatim, with its two inputs replaced. -/
theorem principal_cauchy_law' (c : ℝ) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  classical
  obtain ⟨C, hC, hvar⟩ := signed_small_jumps_variance' c
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
  have hlarge : ∀ k : ℕ, ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 ρ) := fun k =>
    largeJump_weak_limit' c (e k) (he0 k) (he1 k)
  choose ρ hρ using hlarge
  have hcauchy : Tendsto ρ atTop (𝓝 cauchyProb) :=
    compound_tendsto_cauchy' c e he0 he1 helim ρ hρ
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

end FiveIndep

end Kwon1002

/- **Token-identity checks.**  Each `example` forces the statement above to be
the *same type* as its shared-file target (`rfl` then closes it by proof
irrelevance).  They mention sorried declarations, so they are anonymous and
nothing proved above depends on them. -/
example : @Kwon1002.CompoundCauchy.largeJump_limit_compoundPoisson
    = @Kwon1002.FiveIndep.largeJump_limit_compoundPoisson' := rfl

example : @Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit
    = @Kwon1002.FiveIndep.xi_largeIntegral_weak_limit' := rfl

example : @Kwon1002.Finale.bulkTerm_covariance_bound
    = @Kwon1002.FiveIndep.bulkTerm_covariance_bound' := rfl

example : @Kwon1002.xi_charFun_limit
    = @Kwon1002.FiveIndep.xi_charFun_limit' := rfl

example : @Kwon1002.Assembly5.signed_small_jumps_variance
    = @Kwon1002.FiveIndep.signed_small_jumps_variance' := rfl

example : @Kwon1002.Finale.largeJump_weak_limit_compoundPoisson
    = @Kwon1002.FiveIndep.largeJump_weak_limit_compoundPoisson' := rfl

example : @Kwon1002.Assembly5.largeJump_weak_limit
    = @Kwon1002.FiveIndep.largeJump_weak_limit' := rfl

example : @Kwon1002.Assembly5.compound_tendsto_cauchy
    = @Kwon1002.FiveIndep.compound_tendsto_cauchy' := rfl

example : @Kwon1002.principal_cauchy_law
    = @Kwon1002.FiveIndep.principal_cauchy_law' := rfl
