import Kwon1002.TupleMeasure
import Kwon1002.OffDiagonal
import Kwon1002.PoissonRoute
import Kwon1002.CompoundCauchy
import Kwon1002.StoppingWindow

/-!
# Scratch (agent `five`), the three §5 bottlenecks, reduced

Five targets, all reproduced **token for token** (diffed against the sources;
each carries a prime so that the source name stays reachable through the
`open`s at the top of the file):

* `oneLevel_intensity_limit'`  = `Kwon1002.TupleMeasure.oneLevel_intensity_limit`
  (`Kwon1002/TupleMeasure.lean` line 544);
* `tuple_quasi_independence'`  = `Kwon1002.TupleMeasure.tuple_quasi_independence`
  (line 570);
* `bulk_offdiagonal_far'`      = `Kwon1002.OffDiag.bulk_offdiagonal_far`
  (`Kwon1002/OffDiagonal.lean` line 870);
* `xi_largeIntegral_weak_limit'` = `Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit`
  (`Kwon1002/PoissonRoute.lean` line 409);
* `largeJump_limit_compoundPoisson'` =
  `Kwon1002.CompoundCauchy.largeJump_limit_compoundPoisson`
  (`Kwon1002/CompoundCauchy.lean` line 254).

Of the two `TupleMeasure` inputs the index-set bridge is now **closed
outright** (`bulk_window_bridge_oneLevel`, axiom-clean); the five targets
themselves still sit below Proposition
4.1, which is only *stated* in this development (`Kwon1002/Section4.lean`).
What this pass delivers is, for each of them, a strictly tighter reduction,
with the residual input named and stated in the currency the discharging
argument will actually produce.

## 1. The large-jump limit (targets 4 and 5): a scalar residual

`PoissonRoute.xi_largeIntegral_weak_limit` is currently obstructed by two
things its own docstring names as absent from the substrate: *the vague
topology on Radon point measures on* `ℝ∖{0}`, and *the multivariate Poisson
limit for counts on finitely many disjoint continuity sets*.

**Both are removed here.**  `xi_largeIntegral_weak_limit'` is *proved* from a
single scalar statement,

  `xi_charFun_limit` :  `∀ t, E exp(i t ∫_{|x|>ε} x dΞ_n) →
                              exp(∫_{|x|>ε} (e^{itx} - 1) dΛ(x))`,

using Lévy's continuity theorem (`Erdos1002.levy_continuity_real`, proved in
the substrate) and the compound-Poisson exponent calculus
(`Kwon1002.CompoundCauchy.charFun_compoundPoisson_levy`, proved).  In
particular the limit object is still *exhibited*, not quantified over, and
`largeJump_limit_compoundPoisson'`, the sorried input of
`Kwon1002/CompoundCauchy.lean`, follows, token for token, with no further
assumption.

So the whole of the fixed-`ε` large-jump analysis now rests on one limit of
complex numbers.  See the note after `xi_charFun_limit` for how far the
product expansion of that limit can be pushed with what is already proved
in-tree, and for the one estimate it still needs.

## 2. The two `TupleMeasure` inputs (targets 1 and 2)

* `oneLevel_intensity_limit'` is proved from **two** inputs that split it
  exactly along the manuscript's own seam:
  - `bulk_window_bridge_oneLevel`, the §7 bridge between the *random*
    index set `bulkIndices c α n` of `bulkMarkEvent` and the *deterministic*
    `bulkJ n` of display (19).  This is the gap the `TupleMeasure` docstring
    flags ("a bridge that the manuscript never states"), here isolated as a
    statement of its own instead of being bundled with the analysis.
    **It is now proved**, from `Kwon1002/StoppingWindow.lean`: the two index
    sets agree outside a deterministic `O(H)` window off a set of measure
    `O(e^{−c√L})`, and the Lamé cap keeps the number of charged levels at
    `O(L)`, so the difference is `O(H/L) + O(L e^{−c√L}) = o(1)`;
  - `deterministic_oneLevel_intensity`, display (35) proper, on the
    deterministic bulk: a purely §4/Gauss statement, with no stopping time in
    it.
  The assembly is a two-line triangle inequality, proved.

* `tuple_quasi_independence'` is proved from
  `Kwon1002.LevyExponent.tuple_measure_convergence` (displays (39)-(40),
  sorried in-tree, **consumed, and named**) together with
  `oneLevel_intensity_limit'` and the *proved* combinatorics of
  `Kwon1002.TupleMeasure` (`sum_emb_prod_le`, `sum_emb_prod_ge`, packaged as
  `tendsto_emb_sum_of_inputs`).

  Read with `TupleMeasure.tuple_measure_convergence` (which goes the other
  way), this says the pair of inputs (I), (II) is *equivalent* to (39)-(40)
  given the proved parts: input (II) is **not** an extra ask beyond (39)-(40)
  and (I).  Whoever discharges §4 therefore has exactly two things to prove,
  not three, and the second of them is the manuscript's own display.

## 3. The off-diagonal input (target 3): a weaker hypothesis suffices

`OffDiag.bulk_offdiagonal_far` asks for a bad set of pairs of size `O(L·H)
= O(L^{7/4})`.  The near-pair bound it is paired with,
`OffDiag.bulkTermCentered_offdiag_bound` (display (42), **proved**), is
`C(1+log(2+L))²/L²` per pair, so the assembly can afford a bad set of size
`κ L² / (1+log(2+L))³`, larger than `O(L·H)` by almost a full power of `L`,
and within a single logarithm of the largest bad set any argument of this
shape could tolerate.

`bulk_offdiagonal_far_sharp` is that weaker hypothesis, and
`bulk_offdiagonal_input''` (= `Kwon1002.L2Estimate.bulk_offdiagonal_input`,
token for token) and `truncatedBulkSum_centered_L2''`
(= `Kwon1002.truncatedBulkSum_centered_L2`, token for token) are proved from
it, via the proved `near_pair_decay_sharp`.  The point is not cosmetic: the
§4/§7 discharge may now throw away *every* pair at distance `≤ L^{0.9}` from
the diagonal or from a resonance, instead of only `≤ H = L^{0.75}`.

`bulk_offdiagonal_far'` (the manuscript-shaped statement) is reproduced as a
target and left sorried; it implies `bulk_offdiagonal_far_sharp` for large
`n` because `L·H·(1+log(2+L))³ = o(L²)`, which is *not* formalized here (it is
the only claim in this file's commentary that is not machine-checked).

## Sorried results consumed

* `Kwon1002.LevyExponent.tuple_measure_convergence`, displays (39)-(40); used
  once, for `tuple_quasi_independence'`.
* Nothing else.  `TupleMeasure.singleLevel_measure_le`,
  `TupleMeasure.tendsto_emb_sum_of_inputs`, `TupleMeasure.sum_emb_prod_le/ge`,
  `OffDiag.bulkTermCentered_offdiag_bound`, `L2Estimate.bulk_window_input`,
  `L2Estimate.truncatedMark_second_moment`, `L2Estimate.diagonal_le_second_moment`,
  `PoissonRoute.exists_levy_truncation_data`, `PoissonRoute.largeProb_eq_xi_law`,
  `CompoundCauchy.charFun_compoundPoisson_levy` and
  `Erdos1002.levy_continuity_real` are all **proved** where they live.

The four statements introduced as inputs here, `xi_charFun_limit`,
`bulk_window_bridge_oneLevel`, `deterministic_oneLevel_intensity`,
`bulk_offdiagonal_far_sharp`, are each strictly weaker than, or a named
component of, the target they replace.  No target is weakened.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal Real

namespace Kwon1002

open LevyExponent TupleMeasure OffDiag PoissonRoute Assembly5

noncomputable section

/-! ## Part I, the large-jump limit: a scalar residual

`Ξ_n` is `PoissonRoute.xiMeasure`, and `truncSet ε = {x | ε < |x|}`. -/

/-- **The one residual input of the fixed-`ε` large-jump analysis.**

The characteristic functions of the large-jump functional
`∫_{|x| > ε} x dΞ_n` of the point process converge pointwise to the
compound-Poisson exponent of the truncated Lévy measure:

`E exp(i t ∫_{|x|>ε} x dΞ_n)  →  exp(∫_{|x|>ε} (e^{itx} - 1) dΛ(x))`.

**Why this is the right residual.**  It is a limit of *complex numbers*, so it
needs neither the vague topology on Radon point measures on `ℝ∖{0}` (which no
substrate module supplies) nor a multivariate Poisson limit (ditto): those two
were the stated obstructions of `PoissonRoute.xi_largeIntegral_weak_limit`,
and Lévy continuity removes them, see `xi_largeIntegral_weak_limit'` below.

**How far it can be pushed with what is already proved.**  Writing
`h_j(α) = exp(i t X_{n,j}) - 1` on `{j ∈ J_n, |X_{n,j}| > ε}` and `0`
elsewhere, one has `exp(i t ∫_{|x|>ε} x dΞ_n) = ∏_{j ≤ n} (1 + h_j)`
pointwise a.e. (because `J_n ⊆ {0,…,n}` a.e.), hence, by `Finset.prod_add`,

  `E exp(i t ∫ …) = ∑_{S ⊆ {0,…,n}} E ∏_{j ∈ S} h_j`,

and the `|S| = k` layer is exactly `(1/k!)` times a §4 tuple sum for the
bounded complex symbol `x ↦ (e^{itx} - 1)·1{|x| > ε}`, the same currency as
`Kwon1002.LevyExponent.tuple_measure_convergence`, with `Λ(B)` replaced by
`∫(e^{itx}-1) dΛ`.  Two of the three ingredients of that route are already
available in-tree: the *uniform-in-`n`* domination `∑_{|S| = k} E ∏_{j∈S}|h_j|
≤ M^k/k!` needed to interchange the `k`-sum with `n → ∞` follows from
`Kwon1002.TupleMeasure.tuple_measure_le` (proved: every ordered distinct
`k`-tuple has probability `≤ (C/L)^k`) together with the Lamé bound
`Kwon1002.L2Estimate.stoppingTime_le_log` (proved: `τ_n = O(L)`, so only
`O(L)` levels are ever charged), and `Finset.prod_add` is mathlib's.  What is
missing is the tuple limit itself for a complex symbol, i.e. §4, and the
`k!`-bookkeeping between subsets of size `k` and embeddings `Fin k ↪ {0,…,n}`.
That is why this is stated as one clean limit rather than reduced further: the
reduction would only trade it for §4 again. -/
theorem xi_charFun_limit (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) (t : ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in truncSet ε, x ∂(xiMeasure c α n))) :
    Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) := by
  sorry

/-- **Target 4**, `Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit`
(`Kwon1002/PoissonRoute.lean` line 409), reproduced token for token and
**proved** from `xi_charFun_limit`.

The two ingredients are Lévy's continuity theorem on `ℝ`
(`Erdos1002.levy_continuity_real`, proved in the substrate) and the identity
`charFun CP(r,ν) t = exp(∫_{|x|>ε}(e^{itx}-1) dΛ)` for `r·ν = Λ|_{|x|>ε}`
(`Kwon1002.CompoundCauchy.charFun_compoundPoisson_levy`, proved).  Only
`_hjump` is used of the two Lévy-data hypotheses, which is exactly the
situation already recorded in `charFun_compoundPoisson_levy`. -/
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
  exact xi_charFun_limit c ε _hε0 _hε1 t μs _hμs

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

/-- **Target 5**, `Kwon1002.CompoundCauchy.largeJump_limit_compoundPoisson`
(`Kwon1002/CompoundCauchy.lean` line 254), reproduced token for token and
**proved** from `xi_charFun_limit` alone: the weak limit is unique, and
`largeJump_tendsto_compoundPoisson'` identifies it. -/
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

/-! ## Part II, the two `TupleMeasure` inputs -/

/-- The **deterministic** one-level event: the normalized signed mark at level
`j` lands in `B`, with no reference to the stopping time.  (`bulkMarkEvent` is
this event intersected with `{j ∈ J_n}` for the *random* `J_n` of §7.) -/
def oneLevelEvent (n : ℕ) (B : Set ℝ) (j : ℕ) : Set ℝ :=
  {α : ℝ | signedMark α n j ∈ B}

/-- **Display (15) at one level, with no index constraint.**  The analogue of
`TupleMeasure.singleLevel_measure_le` for `oneLevelEvent`: a level whose
normalized signed mark is at distance `≥ δ` from the origin has digit
`≥ 8δL`, and `Kwon1002.digit_tail_product` caps that at `O(1/L)`. -/
theorem oneLevelEvent_measure_le (B : Set ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hB0 : ∀ x ∈ B, δ ≤ |x|) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      unifIoo.real (oneLevelEvent n B j) ≤ C / Lnorm n := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) TupleMeasure.tendsto_Lnorm_atTop
    exact this.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 j
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin 1, (fun _ : Fin 1 => 8 * δ * Lnorm n) i ≤ (digit α ((fun _ : Fin 1 => j) i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ 1 * ∏ _i : Fin 1, (8 * δ * Lnorm n)⁻¹ :=
    hC 1 (fun _ => j) (fun _ => 8 * δ * Lnorm n)
      (fun a b _ => Subsingleton.elim a b) (fun _ => hn1)
  have hsub : oneLevelEvent n B j ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hmark, hα⟩
    refine ⟨hα, fun _ => ?_⟩
    have hδle : δ ≤ |signedMark α n j| := hB0 _ hmark
    have hWnn : 0 ≤ W (theta α n j) := W_nonneg _
    have hprodnn : (0 : ℝ) ≤ (digit α j : ℝ) * W (theta α n j) :=
      mul_nonneg (Nat.cast_nonneg _) hWnn
    have habs : |signedMark α n j| = (digit α j : ℝ) * W (theta α n j) / Lnorm n := by
      rw [signedMark, mark, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg hn2.le, abs_of_nonneg hprodnn]
    rw [habs, le_div_iff₀ hn2] at hδle
    have hW8 : W (theta α n j) ≤ 1 / 8 := W_le_eighth _
    have hbnd : (digit α j : ℝ) * W (theta α n j) ≤ (digit α j : ℝ) * (1 / 8) :=
      mul_le_mul_of_nonneg_left hW8 (Nat.cast_nonneg _)
    simp only
    linarith
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (oneLevelEvent n B j) ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound ?_)
  rw [pow_one, Fin.prod_univ_one, div_div, ← div_eq_mul_inv]

/-- **Input (I.a): the §7 index-set bridge, one level at a time.**

Summed over levels, the probabilities attached to the *random* bulk
`bulkIndices c α n` (§7, built from the stopping time `τ_n`) and to the
*deterministic* bulk `bulkJ n` of display (19) differ by `o(1)`.

This is precisely the step §5 of the manuscript performs silently: (19) and
(38) quantify over different index sets, and no module in `Kwon1002/` states
the comparison.  Isolating it here means the analytic input
(`deterministic_oneLevel_intensity`) is a clean §4 statement.

**PROVED**, from `Kwon1002/StoppingWindow.lean`.  The two index sets differ
only inside `StopWin.diffWindow c n`, a deterministic window of
`2D_n + 2A_n + 1 = O(H)` levels, off the exceptional set `StopWin.stopBad n`
of measure `O(e^{-c√L})`; above the Lamé cap `StopWin.Tcap n = O(L)` both
sides vanish.  So the difference is at most
`|diffWindow|·2C/L + Tcap·O(e^{-c√L}) = O(H/L) + O(L e^{-c√L}) = o(1)`,
the first term by `oneLevelEvent_measure_le` (display (15) at one level) and
the second because the Lamé bound keeps the number of charged levels at
`O(L)`. -/
theorem bulk_window_bridge_oneLevel (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ =>
        (∑ j ∈ Finset.range (n + 1), unifIoo.real (bulkMarkEvent c n B j))
          - ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)) atTop (𝓝 0) := by
  classical
  obtain ⟨δ, hδ, hB0⟩ := _hB0
  obtain ⟨C, hCpos, hCle⟩ := oneLevelEvent_measure_le B hδ hB0
  obtain ⟨Cs, cs, hCs, hcs, hbad⟩ := StopWin.stopBad_measure_le
  have hmajzero : Tendsto (fun n : ℕ =>
      (2 * C) * ((2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1) / Lnorm n)
        + ((3 * Cs) * (Lnorm n * Real.exp (-cs * Real.sqrt (Lnorm n)))
            + (3 * Cs) * Real.exp (-cs * Real.sqrt (Lnorm n)))) atTop (𝓝 0) := by
    simpa using ((StopWin.tendsto_windowCard_div_Lnorm c).const_mul (2 * C)).add
      (((StopWin.tendsto_Lnorm_mul_exp_neg_sqrt hcs).const_mul (3 * Cs)).add
        ((StopWin.tendsto_exp_neg_sqrt_Lnorm hcs).const_mul (3 * Cs)))
  refine squeeze_zero_norm' ?_ hmajzero
  filter_upwards [hCle, hbad, StopWin.eventually_stop_room] with n hCn hbadn hroom
  obtain ⟨hn, hL0, hH0, hAm, hone, hle2m⟩ := hroom
  set a : ℕ → ℝ := fun j => unifIoo.real (bulkMarkEvent c n B j) with ha
  set b : ℕ → ℝ := fun j =>
    if j ∈ bulkJ n then unifIoo.real (oneLevelEvent n B j) else 0 with hb
  set P : ℝ := unifIoo.real (StopWin.stopBad n) with hPdef
  have hPnn : 0 ≤ P := measureReal_nonneg
  have hCL : 0 ≤ C / Lnorm n := by positivity
  -- the exceptional mass
  have hPle : P ≤ Cs * Real.exp (-cs * Real.sqrt (Lnorm n)) := by
    refine le_trans ?_ hbadn
    have hfin : volume (StopWin.stopBad n) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    rw [hPdef, Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono Set.inter_subset_left)
  -- Step A: the deterministic sum, as a sum over `{0,…,n}`
  have hstepA : ∑ j ∈ Finset.range (n + 1), b j
      = ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j) := by
    rw [hb, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (StopWin.bulkJ_subset_range n)]
  -- Step B: the difference, termwise
  have hdiff : (∑ j ∈ Finset.range (n + 1), a j)
        - ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)
      = ∑ j ∈ Finset.range (n + 1), (a j - b j) := by
    rw [← hstepA, Finset.sum_sub_distrib]
  -- Step C: above the Lamé cap both sides vanish
  have hvan : ∀ j, StopWin.Tcap n ≤ j → a j - b j = 0 := by
    intro j hj
    have h1 : a j = 0 := StopWin.unifIoo_bulkMarkEvent_eq_zero c B hn hj
    have h2 : b j = 0 := by
      rw [hb]
      simp only
      rw [if_neg (StopWin.not_mem_bulkJ_of_Tcap_le hL0 hj)]
    rw [h1, h2]; ring
  -- Step D: the termwise estimate
  have hptw : ∀ j, |a j - b j|
      ≤ (if j ∈ StopWin.diffWindow c n then 2 * (C / Lnorm n) else 0) + P := by
    intro j
    have hann : 0 ≤ a j := measureReal_nonneg
    by_cases hjw : j ∈ StopWin.diffWindow c n
    · rw [if_pos hjw]
      have hsubEv : bulkMarkEvent c n B j ⊆ oneLevelEvent n B j := fun α hα => hα.2
      have haj : a j ≤ C / Lnorm n := le_trans (measureReal_mono hsubEv) (hCn j)
      have hbj : b j ≤ C / Lnorm n := by
        rw [hb]; simp only; split_ifs with h
        · exact hCn j
        · exact hCL
      have hbnn : 0 ≤ b j := by
        rw [hb]; simp only; split_ifs with h
        · exact measureReal_nonneg
        · exact le_refl 0
      rw [abs_le]; constructor <;> linarith
    · rw [if_neg hjw, zero_add]
      set D : Set ℝ := {α : ℝ | j ∈ bulkJ n ∧ signedMark α n j ∈ B} with hD
      have hbD : b j = unifIoo.real D := by
        rw [hb, hD]
        simp only
        split_ifs with h
        · congr 1
          ext α; simp [oneLevelEvent, h]
        · rw [show {α : ℝ | j ∈ bulkJ n ∧ signedMark α n j ∈ B} = (∅ : Set ℝ) by
            ext α; simp [h]]
          simp
      have hAD : bulkMarkEvent c n B j
          ⊆ D ∪ StopWin.stopBad n ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := by
        intro α hαmem
        by_cases hα : α ∈ Ioo (0 : ℝ) 1
        · by_cases hg : α ∈ StopWin.stopBad n
          · exact Or.inl (Or.inr hg)
          · exact Or.inl (Or.inl
              ⟨(StopWin.mem_bulkIndices_iff c n hH0 hg hα hjw).mp hαmem.1, hαmem.2⟩)
        · exact Or.inr hα
      have hDA : D ⊆ bulkMarkEvent c n B j
          ∪ StopWin.stopBad n ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := by
        intro α hαmem
        by_cases hα : α ∈ Ioo (0 : ℝ) 1
        · by_cases hg : α ∈ StopWin.stopBad n
          · exact Or.inl (Or.inr hg)
          · exact Or.inl (Or.inl
              ⟨(StopWin.mem_bulkIndices_iff c n hH0 hg hα hjw).mpr hαmem.1, hαmem.2⟩)
        · exact Or.inr hα
      have hstep : ∀ (S T : Set ℝ), S ⊆ T ∪ StopWin.stopBad n ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1} →
          unifIoo.real S ≤ unifIoo.real T + P := by
        intro S T hST
        calc unifIoo.real S
            ≤ unifIoo.real (T ∪ StopWin.stopBad n ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1}) :=
              measureReal_mono hST
          _ ≤ unifIoo.real (T ∪ StopWin.stopBad n)
                + unifIoo.real {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := measureReal_union_le _ _
          _ ≤ (unifIoo.real T + unifIoo.real (StopWin.stopBad n))
                + unifIoo.real {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := by
              gcongr; exact measureReal_union_le _ _
          _ = unifIoo.real T + P := by
              rw [StopWin.unifIoo_real_not_mem_Ioo, hPdef]; ring
      have h1 : a j ≤ unifIoo.real D + P := hstep _ _ hAD
      have h2 : unifIoo.real D ≤ a j + P := hstep _ _ hDA
      rw [hbD, abs_le]
      constructor <;> linarith
  -- Step E: summation
  have hTcap : ∑ j ∈ Finset.range (n + 1), |a j - b j|
      ≤ ∑ j ∈ Finset.range (StopWin.Tcap n), |a j - b j| := by
    have heq : ∑ j ∈ Finset.range (n + 1) ∩ Finset.range (StopWin.Tcap n), |a j - b j|
        = ∑ j ∈ Finset.range (n + 1), |a j - b j| := by
      refine Finset.sum_subset Finset.inter_subset_left ?_
      intro x hx hnx
      have hx2 : x ∉ Finset.range (StopWin.Tcap n) := fun hc =>
        hnx (Finset.mem_inter.mpr ⟨hx, hc⟩)
      rw [Finset.mem_range, not_lt] at hx2
      rw [hvan x hx2, abs_zero]
    rw [← heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => abs_nonneg _)
  have hsum : ∑ j ∈ Finset.range (StopWin.Tcap n), |a j - b j|
      ≤ ((StopWin.diffWindow c n).card : ℝ) * (2 * (C / Lnorm n))
        + (StopWin.Tcap n : ℝ) * P := by
    calc ∑ j ∈ Finset.range (StopWin.Tcap n), |a j - b j|
        ≤ ∑ j ∈ Finset.range (StopWin.Tcap n),
            ((if j ∈ StopWin.diffWindow c n then 2 * (C / Lnorm n) else 0) + P) :=
          Finset.sum_le_sum fun j _ => hptw j
      _ = (∑ j ∈ Finset.range (StopWin.Tcap n),
            (if j ∈ StopWin.diffWindow c n then 2 * (C / Lnorm n) else 0))
          + (StopWin.Tcap n : ℝ) * P := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((StopWin.diffWindow c n).card : ℝ) * (2 * (C / Lnorm n))
          + (StopWin.Tcap n : ℝ) * P := by
          have hcard : (∑ j ∈ Finset.range (StopWin.Tcap n),
              (if j ∈ StopWin.diffWindow c n then 2 * (C / Lnorm n) else 0))
              ≤ ((StopWin.diffWindow c n).card : ℝ) * (2 * (C / Lnorm n)) := by
            rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
            have : ((Finset.range (StopWin.Tcap n) ∩ StopWin.diffWindow c n).card : ℝ)
                ≤ ((StopWin.diffWindow c n).card : ℝ) := by
              exact_mod_cast Finset.card_le_card Finset.inter_subset_right
            nlinarith [hCL]
          linarith
  -- assembly
  have hcardle : ((StopWin.diffWindow c n).card : ℝ)
      ≤ 2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1 := by
    exact_mod_cast StopWin.card_diffWindow_le c n
  have hTle : (StopWin.Tcap n : ℝ) ≤ 3 * Lnorm n + 3 := StopWin.Tcap_le n hL0.le
  have hfinal : ((StopWin.diffWindow c n).card : ℝ) * (2 * (C / Lnorm n))
        + (StopWin.Tcap n : ℝ) * P
      ≤ (2 * C) * ((2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)
            / Lnorm n)
        + ((3 * Cs) * (Lnorm n * Real.exp (-cs * Real.sqrt (Lnorm n)))
            + (3 * Cs) * Real.exp (-cs * Real.sqrt (Lnorm n))) := by
    have hE : (0 : ℝ) < Real.exp (-cs * Real.sqrt (Lnorm n)) := Real.exp_pos _
    have h2CL : (0 : ℝ) ≤ 2 * (C / Lnorm n) := by positivity
    have h1 : ((StopWin.diffWindow c n).card : ℝ) * (2 * (C / Lnorm n))
        ≤ (2 * C) * ((2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)
            / Lnorm n) := by
      calc ((StopWin.diffWindow c n).card : ℝ) * (2 * (C / Lnorm n))
          ≤ (2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)
              * (2 * (C / Lnorm n)) := mul_le_mul_of_nonneg_right hcardle h2CL
        _ = (2 * C) * ((2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)
              / Lnorm n) := by field_simp
    have h2 : (StopWin.Tcap n : ℝ) * P
        ≤ (3 * Cs) * (Lnorm n * Real.exp (-cs * Real.sqrt (Lnorm n)))
          + (3 * Cs) * Real.exp (-cs * Real.sqrt (Lnorm n)) := by
      have hTnn : (0 : ℝ) ≤ (StopWin.Tcap n : ℝ) := Nat.cast_nonneg _
      nlinarith [hPle, hTle, hPnn, hE.le, hCs.le]
    linarith
  rw [Real.norm_eq_abs, hdiff]
  calc |∑ j ∈ Finset.range (n + 1), (a j - b j)|
      ≤ ∑ j ∈ Finset.range (n + 1), |a j - b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (StopWin.Tcap n), |a j - b j| := hTcap
    _ ≤ ((StopWin.diffWindow c n).card : ℝ) * (2 * (C / Lnorm n))
          + (StopWin.Tcap n : ℝ) * P := hsum
    _ ≤ _ := hfinal

/-- **Input (I.b): display (35) on the deterministic bulk.**

`∑_{j ∈ J_n} P(X_{n,j} ∈ B) → Λ(B)`, with `J_n` the deterministic bulk of
(19).  This is the manuscript's `L·P(a W(Θ)/L ∈ dx) ⇒ c₀ x^{-2} dx` combined
with `#J_n = (1+o(1)) L/λ`, read against an indicator rather than against
`φ ∈ C_c^1` (see the `TupleMeasure` docstring for why the indicator form is
the one `poisson_count_limit` consumes).

**Obstruction.**  Two classical ingredients, neither in the substrate: the
Gauss-measure digit tail `P(a > s) ~ 1/(s log 2)` in *asymptotic* (not merely
`O`) form, and the equidistribution of `θ_j`, which together give the
per-level intensity `E[W]/(u L log 2) = 1/(12 u L log 2)`; against
`#J_n ≈ 12 L log 2/π²` and the parity factor `1/2` this reproduces
`Λ{x > u} = 1/(2π² u)` exactly, so the normalization of `levyIntensity` is
consistent with this statement (checked by hand, not machine-checked). -/
theorem deterministic_oneLevel_intensity (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) := by
  sorry

/-- **Target 1**, `Kwon1002.TupleMeasure.oneLevel_intensity_limit`
(`Kwon1002/TupleMeasure.lean` line 544), reproduced token for token and
**proved** from the two inputs above. -/
theorem oneLevel_intensity_limit' (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        unifIoo.real (bulkMarkEvent c n B j)) atTop (𝓝 ((levyIntensity B).toReal)) := by
  have h := (bulk_window_bridge_oneLevel c B _hB _hB0 _hBbd).add
    (deterministic_oneLevel_intensity B _hB _hB0 _hBbd)
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-- The `∑_f ∏_ℓ w` half of display (39), as a limit: if the one-level weights
sum to `Λ` and are uniformly `o(1)`, the ordered-distinct-tuple sum of their
products tends to `Λ^k`.

Proved by feeding `Kwon1002.TupleMeasure.tendsto_emb_sum_of_inputs` (proved
there, out of `sum_emb_prod_le` and `sum_emb_prod_ge`) with `T` equal to the
very sum in question, so that its factorization hypothesis is trivial. -/
theorem tendsto_emb_prod_sum (k : ℕ) (u : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (Λ : ℝ) (M : ℕ → ℝ)
    (hw0 : ∀ n j, 0 ≤ w n j) (hM0 : ∀ n, 0 ≤ M n)
    (hwM : ∀ᶠ n in atTop, ∀ j ∈ u n, w n j ≤ M n)
    (hMlim : Tendsto M atTop (𝓝 0))
    (hS : Tendsto (fun n => ∑ j ∈ u n, w n j) atTop (𝓝 Λ)) :
    Tendsto (fun n => ∑ f : Fin k ↪ (u n : Finset ℕ), ∏ ℓ, w n (f ℓ))
      atTop (𝓝 (Λ ^ k)) := by
  refine TupleMeasure.tendsto_emb_sum_of_inputs k u w
    (fun n => ∑ f : Fin k ↪ (u n : Finset ℕ), ∏ ℓ, w n (f ℓ)) Λ M
    hw0 hM0 hwM hMlim hS ?_
  have hzero : ∀ n : ℕ, (∑ f : Fin k ↪ (u n : Finset ℕ), ∏ ℓ, w n (f ℓ))
      - ∑ f : Fin k ↪ (u n : Finset ℕ), ∏ ℓ, w n (TupleMeasure.embTuple f ℓ) = 0 :=
    fun n => sub_self _
  exact Filter.Tendsto.congr (fun n => (hzero n).symm) tendsto_const_nhds

/-- **Target 2**, `Kwon1002.TupleMeasure.tuple_quasi_independence`
(`Kwon1002/TupleMeasure.lean` line 570), reproduced token for token and
**proved** from `Kwon1002.LevyExponent.tuple_measure_convergence` (displays
(39)-(40), sorried in-tree, the one sorried result consumed in this file),
`oneLevel_intensity_limit'`, and the proved
`TupleMeasure.singleLevel_measure_le`.

Since `TupleMeasure.tuple_measure_convergence` derives (39)-(40) *from* inputs
(I) and (II), this closes the loop: **(I) + (II) ⟺ (39)-(40) + (I)**.  Input
(II) is therefore not an independent obligation, and the §4 discharge has
exactly two things to prove: the one-level intensity (I) and the manuscript's
own (39)-(40). -/
theorem tuple_quasi_independence' (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (bulkMarkEvent c n B (f ℓ)))
      atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hBδ⟩ := _hB0
  obtain ⟨C, hC, hCle⟩ := TupleMeasure.singleLevel_measure_le c B hδ hBδ
  have hT := LevyExponent.tuple_measure_convergence c B _hB ⟨δ, hδ, hBδ⟩ _hBbd k
  have hP := tendsto_emb_prod_sum k (fun n => Finset.range (n + 1))
      (fun n j => unifIoo.real (bulkMarkEvent c n B j)) ((levyIntensity B).toReal)
      (fun n => C / Lnorm n)
      (fun n j => measureReal_nonneg) (fun n => div_nonneg hC.le (Lnorm_nonneg n))
      (by filter_upwards [hCle] with n hn j _ using hn j)
      (Filter.Tendsto.div_atTop tendsto_const_nhds TupleMeasure.tendsto_Lnorm_atTop)
      (oneLevel_intensity_limit' c B _hB ⟨δ, hδ, hBδ⟩ _hBbd)
  have hsub := hT.sub hP
  rw [sub_self] at hsub
  exact hsub

/-! ## Part III, the off-diagonal input, from a weaker bad-set hypothesis -/

/-- **Target 3**, `Kwon1002.OffDiag.bulk_offdiagonal_far`
(`Kwon1002/OffDiagonal.lean` line 870), reproduced token for token.  Left
sorried; it is Proposition 4.1 for pairs, and Proposition 4.1 is only stated
in this development.  It is recorded here because
`bulk_offdiagonal_far_sharp` below is a **weaker** hypothesis (larger bad
set), so anything discharging this discharges that. -/
theorem bulk_offdiagonal_far' (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagTerm c ε n p ≤ ε / 2 := by
  sorry

/-- **The weakened far-pair input.**  Identical to `bulk_offdiagonal_far'`
except that the discarded set of pairs may have cardinality
`κ L²/(1+log(2+L))³` instead of `κ L H = κ L^{7/4}`.

This is the largest bad set the near-pair bound of display (42) can pay for,
up to one logarithm: `OffDiag.bulkTermCentered_offdiag_bound` (**proved**)
gives `Cp (1+log(2+L))²/L²` per pair, so a bad set of size
`κ L²/(1+log(2+L))³` contributes `κ Cp/(1+log(2+L)) → 0`
(`near_pair_decay_sharp`, **proved** below), while a bad set of size
`c L²/(1+log(2+L))²` would contribute a constant. -/
theorem bulk_offdiagonal_far_sharp (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagTerm c ε n p ≤ ε / 2 := by
  sorry

/-- **Proved.**  The sharpened near-pair contribution is `o(1)`:
`(κ L²/(1+log(2+L))³) · (Cp (1+log(2+L))²/L²) = κ Cp/(1+log(2+L)) → 0`.

Compare `OffDiag.near_pair_decay`, which proves the same for the smaller bad
set `κ L H` and needs the `rpow` estimate `log x ≤ 16 x^{1/16}`; here no power
of `L` is spent at all, only the divergence of `log(2+L)`. -/
theorem near_pair_decay_sharp (κ Cp δ : ℝ) (hκ : 0 < κ) (hCp : 0 < Cp) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3)
          * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) ≤ δ := by
  have hLtop : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2L : Tendsto (fun n : ℕ => 2 + Lnorm n) atTop atTop :=
    tendsto_atTop_add_const_left _ 2 hLtop
  have hU : Tendsto (fun n : ℕ => 1 + Real.log (2 + Lnorm n)) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp h2L)
  have hev : ∀ᶠ n : ℕ in atTop,
      (max 1 (κ * Cp / δ) ≤ 1 + Real.log (2 + Lnorm n)) ∧ 0 < Lnorm n :=
    (hU.eventually_ge_atTop (max 1 (κ * Cp / δ))).and (hLtop.eventually_gt_atTop 0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hUge, hLpos⟩ := hN n hn
  have hU1 : (1 : ℝ) ≤ 1 + Real.log (2 + Lnorm n) := le_trans (le_max_left _ _) hUge
  have hUpos : (0 : ℝ) < 1 + Real.log (2 + Lnorm n) := lt_of_lt_of_le one_pos hU1
  have hLne : (Lnorm n) ≠ 0 := ne_of_gt hLpos
  have hUne : (1 + Real.log (2 + Lnorm n)) ≠ 0 := ne_of_gt hUpos
  have hkey : (κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3)
        * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2)
      = κ * Cp / (1 + Real.log (2 + Lnorm n)) := by
    field_simp
  rw [hkey, div_le_iff₀ hUpos]
  have hquot : κ * Cp / δ ≤ 1 + Real.log (2 + Lnorm n) :=
    le_trans (le_max_right _ _) hUge
  rw [div_le_iff₀ hδ] at hquot
  nlinarith [hquot, hδ, hUpos]

/-- **Proved from `bulk_offdiagonal_far_sharp`**: the target
`Kwon1002.L2Estimate.bulk_offdiagonal_input` (line 577), reproduced token for
token.  Proof body: `Kwon1002.OffDiag.bulk_offdiagonal_input'` verbatim, with
`bulk_offdiagonal_far`/`near_pair_decay` replaced by their sharpened forms. -/
theorem bulk_offdiagonal_input'' (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            ∫ α in Ioo (0:ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k) ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hpair⟩ := bulkTermCentered_offdiag_bound c
  obtain ⟨κ, hκ, hfar⟩ := bulk_offdiagonal_far_sharp c
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
  rw [sum_offdiag_eq c ε n]
  set P : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hP
  have hsplit : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagTerm c ε n p)
      + ∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagTerm c ε n p
      = ∑ p ∈ P, offdiagTerm c ε n p :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ∈ B) _
  have hnotB : P.filter (fun p => ¬ p ∈ B) = P \ B := (Finset.sdiff_eq_filter P B).symm
  have hQ0 : (0:ℝ) ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by positivity
  have hbound : ∀ p ∈ P.filter (fun p => p ∈ B),
      offdiagTerm c ε n p ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by
    intro p _
    simp only [offdiagTerm]
    by_cases hpq : p.1 = p.2
    · rw [if_pos hpq]
      exact hQ0
    · rw [if_neg hpq]
      exact le_trans (le_abs_self _) (hpair ε hε hε1 n p.1 p.2 hpq hL)
  have hnear : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagTerm c ε n p) ≤ ε / 2 := by
    have hb := Finset.sum_le_card_nsmul (P.filter (fun p => p ∈ B)) (offdiagTerm c ε n)
      (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) hbound
    rw [nsmul_eq_mul] at hb
    refine le_trans hb ?_
    have hcard : (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3 := by
      refine le_trans ?_ hBcard
      exact_mod_cast Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).2)
    calc (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2)
        ≤ (κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard hQ0
      _ ≤ ε / 2 := hN₂ n hn2
  have hfarsum : (∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagTerm c ε n p) ≤ ε / 2 := by
    rw [hnotB]
    exact hBfar
  linarith [hsplit, hnear, hfarsum]

/-- **Consequence**: `Kwon1002.truncatedBulkSum_centered_L2`, reproduced token
for token (line 504 of `Kwon1002/SmallJumps.lean`), now resting only on
`bulk_offdiagonal_far_sharp`, i.e. on Proposition 4.1 for pairs with a bad
set allowed to be almost `L` times larger than the manuscript's `O(L H)`.
Proof body: `Kwon1002.OffDiag.truncatedBulkSum_centered_L2'` verbatim, with
its off-diagonal input replaced by `bulk_offdiagonal_input''`. -/
theorem truncatedBulkSum_centered_L2'' (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ b : ℝ,
        (∫ α in Ioo (0 : ℝ) 1,
            (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
          ≤ C * ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C₂, hC₂, hsm⟩ := L2Estimate.truncatedMark_second_moment
  obtain ⟨κ, hκ, hwin⟩ := L2Estimate.bulk_window_input c
  refine ⟨κ * C₂ + 2, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hwin ε hε hε1
  obtain ⟨N₂, hN₂⟩ := bulk_offdiagonal_input'' c ε hε hε1
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨S, hSsub, hScard, hStail⟩ := hN₁ n hn1
  refine ⟨∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0:ℝ) 1, bulkTerm c ε β n j, ?_⟩
  rw [integral_centered_eq, centered_second_moment_expand c ε hε.le n]
  refine le_trans (le_of_eq (L2Estimate.sum_split_diag (n + 1) (fun j k =>
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k))) ?_
  have hoff := hN₂ n hn2
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
  have hdiag : (∑ j ∈ Finset.range (n + 1),
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε + ε := by
    rw [← Finset.sum_sdiff hSsub]
    linarith [hSbound, hRestBound]
  have hfinal : κ * C₂ * ε + ε + ε ≤ (κ * C₂ + 2) * ε := le_of_eq (by ring)
  linarith [hdiag, hoff, hfinal]

end

end Kwon1002
