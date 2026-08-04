import Kwon1002.CauchyLaw

/-!
# Assembly5, Corollary 5.3 (principal Cauchy law), display (43)

Target: `Kwon1002.principal_cauchy_law` of `Kwon1002/PoissonLimit.lean`,
reproduced token-identically below as
`Kwon1002.Assembly5.principal_cauchy_law`.

This file is the **assembly of §5**: the manuscript's proof of (43) is a
double limit (fixed `ε` large jumps ⇒ compound Poisson, small jumps
uniformly `O(ε)` after centering, compound Poisson ⇒ Cauchy as `ε ↓ 0`,
then a diagonal choice `ε_n ↓ 0`).  Everything that is *bookkeeping* in
that argument is proved here; what is left sorried is exactly three
statements of §5, named and stated in the form the manuscript proves
them.

## What is proved

* `bulkSum_eq_large_add_small`, the exact `ε`-splitting
  `x = x·1{|x| ≤ ε} + x·1{|x| > ε}` of the bulk sum into the signed
  small-jump sum and the signed large-jump sum (manuscript: "split
  `x = xχ(|x|/ε) + x(1-χ(|x|/ε))`").
* `measurable_signedSmallSum`, `measurable_largeSum`,
  `memLp_signedSmallSum`, both halves are genuine random variables with
  finite second moment (the index set `J_n` is random, so this is not
  automatic; the argument reuses `bulkIndices_subset_range`).
* `meas_ge_le_of_sq_integral_le`, Chebyshev in the form needed.
* `levyProkhorovDist_map_le`, **an `L²` bound transfers to a bound on
  the Lévy-Prokhorov distance of the two laws**: if
  `E[(X-Y)²] ≤ δ³` then `d_LP(law X, law Y) ≤ δ`.  This is the step that
  converts Lemma 5.2 into a statement about *distributions*, which is
  what the ε/3 argument needs.
* `exists_diagonal_tendsto`, **the diagonal extraction**: the
  manuscript's one-line "a diagonal choice `ε_n ↓ 0` gives a
  deterministic sequence `b_n^{(0)}`", proved as a statement about
  metric spaces.  It is applied in the Lévy-Prokhorov metric on
  `ProbabilityMeasure ℝ`, which metrizes convergence in distribution
  (`MeasureTheory.LevyProkhorov`).
* `principal_cauchy_law` itself, from the three inputs below.

## The three sorried inputs (and only these)

1. `largeJump_weak_limit`, Proposition 5.1 (`Ξ_n ⇒ PRM(Λ)`, display
   (37)) together with the continuous mapping theorem and the uniform
   tail estimate `sup_n E Ξ_n{|x| > R} ≤ C/R`, in the only form Cor. 5.3
   consumes it: for each fixed `ε` the large-jump sum converges in
   distribution.
2. `signed_small_jumps_variance`, display (41), Lemma 5.2, **with the
   sign `(-1)^j`** (see the manuscript note below).
3. `compound_tendsto_cauchy`, the `ε ↓ 0` limit of the compensated
   large-jump exponents: the compound-Poisson limits converge to
   `Cauchy(0, 1/(2π))`.  (`CauchyLaw.levy_exponent_limit` already
   *computes* the exponent `-|t|/(2π)` from
   `levy_exponent_limit_raw`; this input is the statement that the
   compound-Poisson laws follow it.)

No other sorried result is used.  In particular `CauchyLaw`'s
`factorialMoment_convergence`, `integral_one_sub_cos_div_sq`,
`levy_exponent_limit_raw` and `charFun_cauchyProb` are *not* invoked
here: they are the intended proofs of inputs 1 and 3, cited but not
consumed.  From `SmallJumps` only proved lemmas are used
(`bulkIndices_subset_range`, `truncatedMark_*`, `Lnorm_nonneg`,
`ae_irrational_restrict`); `truncatedBulkSum_centered_L2` is **not**
used.

## Manuscript note, a defect in the shared statement of (41)

`Kwon1002.small_jumps_variance` (in `SmallJumps.lean`) controls
`Var(∑_j Z^{(ε)}_{n,j}/L)` with the **unsigned** truncated mark, whereas
the manuscript's (40)-(41) is about
`U^{(ε)}_{n,j} = (-1)^j Z_{n,j} χ(Z_{n,j}/(εL))`, which carries the
alternating sign.  The unsigned form is *not usable* by Corollary 5.3:
the quantity that has to be negligible there is the difference
`bulkSum - largeSum`, and that difference carries the sign.  The proof
of (41) is indeed insensitive to the sign pattern (it bounds the
diagonal by `E|U|²` and the off-diagonal by `|Cov|`), so this is a
statement-level, not a proof-level, gap, but a formalization that keeps
the unsigned statement cannot close §5.  Input 2 below is therefore
stated with the sign, i.e. literally (41).
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace Kwon1002

namespace Assembly5

noncomputable section

/-! ## Part 0, two general tools

Neither is about §5; both are the glue the manuscript uses implicitly. -/

section Tools

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Chebyshev's inequality in the exact shape needed: a second-moment
bound controls the probability of a large deviation. -/
lemma meas_ge_le_of_sq_integral_le {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hint : Integrable (fun ω => f ω ^ 2) P)
    {M : ℝ} (hM : (∫ ω, f ω ^ 2 ∂P) ≤ M) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |f ω|} ≤ ENNReal.ofReal (M / ε ^ 2) := by
  have hset : {ω | ε ≤ |f ω|} = {ω | ε ^ 2 ≤ f ω ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      nlinarith [sq_abs (f ω), abs_nonneg (f ω)]
    · intro h
      by_contra hcon
      push_neg at hcon
      nlinarith [sq_abs (f ω), abs_nonneg (f ω)]
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => f ω ^ 2)
      (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω)) hint (ε ^ 2)
  have hreal : P.real {ω | ε ^ 2 ≤ f ω ^ 2} ≤ M / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hmk, hM]
  have h1 : P {ω | ε ^ 2 ≤ f ω ^ 2}
      = ENNReal.ofReal (P.real {ω | ε ^ 2 ≤ f ω ^ 2}) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
  rw [hset, h1]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **`L²`-closeness implies closeness in distribution.**  If two random
variables on the same probability space satisfy `E[(X-Y)²] ≤ δ³` then
their laws are within `δ` in the Lévy-Prokhorov metric.  This is the step
that turns Lemma 5.2 (an `L²` statement) into an estimate between the
*laws* appearing in Cor. 5.3. -/
lemma levyProkhorovDist_map_le {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hint : Integrable (fun ω => (X ω - Y ω) ^ 2) P)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbd : (∫ ω, (X ω - Y ω) ^ 2 ∂P) ≤ δ ^ 3) :
    levyProkhorovDist (P.map X) (P.map Y) ≤ δ := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  refine levyProkhorovDist_le_of_forall_le _ _ hδ ?_
  intro ε B hεδ hB
  have hε0 : 0 < ε := lt_of_le_of_lt hδ hεδ
  have hcube : δ ^ 3 / ε ^ 2 ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hεδ.le)
      (by positivity : (0:ℝ) ≤ ε ^ 2 + ε * δ + δ ^ 2)]
  have htail : P {ω | ε ≤ |X ω - Y ω|} ≤ ENNReal.ofReal ε :=
    (meas_ge_le_of_sq_integral_le hint hbd hε0).trans (ENNReal.ofReal_le_ofReal hcube)
  rw [Measure.map_apply hX hB]
  have hsub : X ⁻¹' B ⊆ Y ⁻¹' (Metric.thickening ε B) ∪ {ω | ε ≤ |X ω - Y ω|} := by
    intro ω hω
    by_cases hd : ε ≤ |X ω - Y ω|
    · exact Or.inr hd
    · refine Or.inl ?_
      simp only [Set.mem_preimage]
      rw [Metric.mem_thickening_iff]
      refine ⟨X ω, hω, ?_⟩
      rw [Real.dist_eq, abs_sub_comm]
      exact not_le.mp hd
  calc P (X ⁻¹' B)
      ≤ P (Y ⁻¹' (Metric.thickening ε B) ∪ {ω | ε ≤ |X ω - Y ω|}) := measure_mono hsub
    _ ≤ P (Y ⁻¹' (Metric.thickening ε B)) + P {ω | ε ≤ |X ω - Y ω|} := measure_union_le _ _
    _ ≤ (P.map Y) (Metric.thickening ε B) + ENNReal.ofReal ε := by
        rw [Measure.map_apply hY Metric.isOpen_thickening.measurableSet]
        exact add_le_add le_rfl htail

end Tools

/-- **The diagonal extraction.**  This is the manuscript's closing
sentence, "a diagonal choice `ε_n ↓ 0` gives a deterministic sequence
`b_n^{(0)}` for which (43) holds", as a statement about metric spaces.

If for each `k` the sequence `n ↦ P k n` is eventually within `η k` of
`z`, and `η k → 0`, then some diagonal `n ↦ P (κ n) n` converges to `z`.
Note that no convergence of `n ↦ P k n` itself is assumed: only the
asymptotic `η k`-closeness, which is what §5 supplies. -/
lemma exists_diagonal_tendsto {X : Type*} [PseudoMetricSpace X]
    (P : ℕ → ℕ → X) (z : X) (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hP : ∀ k, ∀ᶠ n in atTop, dist (P k n) z ≤ η k) :
    ∃ κ : ℕ → ℕ, Tendsto (fun n => P (κ n) n) atTop (𝓝 z) := by
  classical
  have key : ∀ m : ℕ, ∃ kN : ℕ × ℕ, ∀ n : ℕ, kN.2 ≤ n →
      dist (P kN.1 n) z ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    have hm : (0:ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨k, hk⟩ := (Metric.tendsto_nhds.mp hη _ hm).exists
    rw [Real.dist_eq, sub_zero] at hk
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hP k)
    exact ⟨(k, N), fun n hn => (hN n hn).trans ((le_abs_self _).trans hk.le)⟩
  choose kN hkN using key
  set M : ℕ → ℕ := fun m => (kN m).2 + m with hM
  have hex : ∀ n : ℕ, ∃ m : ℕ, n < M m := by
    intro n
    refine ⟨n + 1, ?_⟩
    simp only [hM]
    omega
  refine ⟨fun n => (kN (Nat.find (hex n) - 1)).1, ?_⟩
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine eventually_atTop.mpr ⟨(Finset.range (m + 1)).sup M, fun n hn => ?_⟩
  have hmlt : m < Nat.find (hex n) := by
    rw [Nat.lt_find_iff]
    intro i hi
    have hMi : M i ≤ n :=
      le_trans (Finset.le_sup (f := M) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) hn
    omega
  set j := Nat.find (hex n) with hj
  have hstep : M (j - 1) ≤ n :=
    Nat.not_lt.mp (Nat.find_min (hex n) (show j - 1 < j by omega))
  have hMeq : M (j - 1) = (kN (j - 1)).2 + (j - 1) := rfl
  have hN2 : (kN (j - 1)).2 ≤ n := by omega
  have hd := hkN (j - 1) n hN2
  have hmj : m ≤ j - 1 := by omega
  have hfinal : 1 / (((j - 1 : ℕ) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (m : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hmj
    linarith
  calc dist (P (kN (j - 1)).1 n) z ≤ 1 / (((j - 1 : ℕ) : ℝ) + 1) := hd
    _ ≤ 1 / ((m : ℝ) + 1) := hfinal
    _ < δ := hm

/-! ## Part 1, the `ε`-splitting of the bulk sum

The manuscript splits `x = xχ(|x|/ε) + x(1-χ(|x|/ε))`.  With the shared
file's hard truncation `truncatedMark` this is the split at
`|X_{n,j}| ≤ ε`, since `|X_{n,j}| = Z_{n,j}/L` and
`truncatedMark` keeps exactly the levels with `Z_{n,j} ≤ εL`. -/

/-- The signed small-jump sum `L⁻¹ ∑_{j∈J_n} (-1)^j Z^{(ε)}_{n,j}`: the
manuscript's `L⁻¹ ∑ U^{(ε)}_{n,j}` of (40), with the hard cutoff in place
of `χ`. -/
def signedSmallSum (c ε : ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ bulkIndices c α n, (-1 : ℝ) ^ j * truncatedMark ε α n j / Lnorm n

/-- The signed large-jump sum: the levels with `Z_{n,j} > εL`, i.e. the
points of `Ξ_n` outside `[-ε, ε]`.  This is the part Proposition 5.1 and
the continuous mapping theorem control. -/
def largeSum (c ε : ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ bulkIndices c α n, (-1 : ℝ) ^ j * (mark α n j - truncatedMark ε α n j) / Lnorm n

/-- **The splitting**, proved: the bulk sum is exactly large plus small. -/
theorem bulkSum_eq_large_add_small (c ε α : ℝ) (n : ℕ) :
    bulkSum c α n = largeSum c ε α n + signedSmallSum c ε α n := by
  simp only [bulkSum, largeSum, signedSmallSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [signedMark]
  ring

lemma measurable_signedSmallSum (c ε : ℝ) (n : ℕ) :
    Measurable (fun α : ℝ => signedSmallSum c ε α n) := by
  refine measurable_of_tendsto_metrizable
    (f := fun M α => ∑ j ∈ Finset.range M,
      if j ∈ bulkIndices c α n then (-1 : ℝ) ^ j * truncatedMark ε α n j / Lnorm n else 0)
    (fun M => Finset.measurable_sum _ fun j _ =>
      Measurable.ite (measurableSet_mem_bulkIndices c n j)
        (((measurable_truncatedMark ε n j).const_mul ((-1 : ℝ) ^ j)).div_const _)
        measurable_const) ?_
  rw [tendsto_pi_nhds]
  intro α
  refine tendsto_atTop_of_eventually_const (i₀ := stoppingTime α n) ?_
  intro M hM
  have hsub : bulkIndices c α n ⊆ Finset.range M := by
    intro i hi
    have h1 : i ∈ Finset.range (stoppingTime α n) := Finset.filter_subset _ _ hi
    simp only [Finset.mem_range] at h1 ⊢
    omega
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  rfl

lemma measurable_largeSum (c ε : ℝ) (n : ℕ) :
    Measurable (fun α : ℝ => largeSum c ε α n) := by
  have h : (fun α : ℝ => largeSum c ε α n)
      = fun α : ℝ => bulkSum c α n - signedSmallSum c ε α n := by
    funext α
    rw [bulkSum_eq_large_add_small c ε α n]
    ring
  rw [h]
  exact (measurable_bulkSum c n).sub (measurable_signedSmallSum c ε n)

/-- The small-jump sum is bounded by `(n+1)ε` almost surely: the random
index set `J_n` sits inside `{0,…,n}` for irrational `α ∈ (0,1)`. -/
lemma abs_signedSmallSum_le_ae (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    ∀ᵐ α ∂unifIoo, |signedSmallSum c ε α n| ≤ ((n : ℝ) + 1) * ε := by
  simp only [unifIoo]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict] with α hα hirr
  have hsub := bulkIndices_subset_range c α hα hirr n
  have hterm : ∀ j : ℕ, |(-1 : ℝ) ^ j * truncatedMark ε α n j / Lnorm n| ≤ ε := by
    intro j
    have habs : |(-1 : ℝ) ^ j * truncatedMark ε α n j / Lnorm n|
        = truncatedMark ε α n j / Lnorm n := by
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (truncatedMark_nonneg ε α n j), abs_of_nonneg (Lnorm_nonneg n)]
    rw [habs]
    exact truncatedMark_div_le ε hε α n j
  calc |signedSmallSum c ε α n|
      ≤ ∑ j ∈ bulkIndices c α n, |(-1 : ℝ) ^ j * truncatedMark ε α n j / Lnorm n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ bulkIndices c α n, ε := Finset.sum_le_sum fun j _ => hterm j
    _ ≤ ∑ _j ∈ Finset.range (n + 1), ε :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hε
    _ = ((n : ℝ) + 1) * ε := by
        simp [Finset.sum_const, Finset.card_range]

lemma memLp_signedSmallSum (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    MemLp (fun α : ℝ => signedSmallSum c ε α n) 2 unifIoo :=
  MemLp.of_bound (measurable_signedSmallSum c ε n).aestronglyMeasurable (((n : ℝ) + 1) * ε)
    (by
      filter_upwards [abs_signedSmallSum_le_ae c ε hε n] with α h
      rwa [Real.norm_eq_abs])

lemma integrable_sq_signedSmallSum_sub (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (b : ℝ) :
    Integrable (fun α : ℝ => (signedSmallSum c ε α n - b) ^ 2) unifIoo := by
  have h := ((memLp_signedSmallSum c ε hε n).sub (memLp_const b)).integrable_sq
  simpa using h

/-- The manuscript's centering `b_{n,ε} = L⁻¹ ∑_{j ∈ J_n} E U^{(ε)}_{n,j}`. -/
def smallCenter (c ε : ℝ) (n : ℕ) : ℝ := ∫ α, signedSmallSum c ε α n ∂unifIoo

/-- The law of the `ε`-centered bulk sum: what (43) is about. -/
def centeredBulkProb (c ε : ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨unifIoo.map (fun α => bulkSum c α n - smallCenter c ε n),
    Measure.isProbabilityMeasure_map ((measurable_bulkSum c n).sub_const _).aemeasurable⟩

/-- The law of the large-jump sum: what Proposition 5.1 controls. -/
def largeProb (c ε : ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨unifIoo.map (fun α => largeSum c ε α n),
    Measure.isProbabilityMeasure_map (measurable_largeSum c ε n).aemeasurable⟩

/-! ## Part 2, the three §5 inputs -/

/-- **Input 1**, Proposition 5.1 (display (37): `Ξ_n ⇒ PRM(Λ)` with
`dΛ(x) = |x|⁻²dx/(2π²)`) plus the continuous mapping theorem and the
uniform tail bound `sup_n E Ξ_n{|x| > R} ≤ C/R`, in the form Cor. 5.3
consumes: for fixed `ε` the large-jump sum has a limit law (the
compensated compound Poisson law of the manuscript).

Route: `CauchyLaw.poisson_count_limit` is already the counting form of
Prop. 5.1 modulo `CauchyLaw.factorialMoment_convergence` (display (38));
`Erdos1002.ContinuousCompoundPoisson` supplies the limit object.  The
remaining work is the continuous-mapping step for the functional
`x ↦ ∑ x·1{|x| > ε}` (legitimate because `Λ{|x| = ε} = 0` and because the
tails `|x| > R` may be removed first, by the `C/R` bound). -/
theorem largeJump_weak_limit (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) := by
  sorry

/-- **Input 2**, Lemma 5.2, display (41), *with the alternating sign*:
the compensated small jumps have variance `O(ε)` after normalization.

This is `Kwon1002.small_jumps_variance` with `U^{(ε)}_{n,j}` in place of
`Z^{(ε)}_{n,j}`, i.e. literally (40)-(41).  See the manuscript note in
the header: the unsigned form proved in `SmallJumps.lean` cannot be used
here, and the proof of (41) is insensitive to the sign. -/
theorem signed_small_jumps_variance (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo) ≤ C * ε := by
  sorry

/-- **Input 3**, the `ε ↓ 0` limit: the compound-Poisson limits of the
large-jump parts converge to `Cauchy(0, 1/(2π))`.

This is the last display of the proof of Cor. 5.3: symmetry kills the
imaginary part and dominated convergence gives
`∫ (cos(tx) - 1) dx/(2π²x²) = -|t|/(2π)`.  The exponent itself is already
*computed* in `CauchyLaw.levy_exponent_limit` (from
`levy_exponent_limit_raw`), and `CauchyLaw.tendsto_charFun_compound_of_exponent`
already converts exponent convergence into characteristic-function
convergence; what is missing is the identification of `ρ k` as the
compound-Poisson law with those exponents. -/
theorem compound_tendsto_cauchy (c : ℝ) (e : ℕ → ℝ)
    (_he0 : ∀ k, 0 < e k) (_he1 : ∀ k, e k < 1) (_he : Tendsto e atTop (𝓝 0))
    (ρ : ℕ → ProbabilityMeasure ℝ)
    (_hρ : ∀ k, Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 (ρ k))) :
    Tendsto ρ atTop (𝓝 cauchyProb) := by
  sorry

/-! ## Part 3, the assembly -/

/-- The `L²` estimate of Lemma 5.2, transported to the Lévy-Prokhorov
distance between the centered bulk law and the large-jump law.  Proved. -/
lemma dist_centeredBulk_largeProb_le (c ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hvar : (∫ α, (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 ∂unifIoo) ≤ δ ^ 3) :
    dist (LevyProkhorov.ofMeasure (centeredBulkProb c ε n))
        (LevyProkhorov.ofMeasure (largeProb c ε n)) ≤ δ := by
  have hXY : ∀ α : ℝ,
      ((fun α : ℝ => bulkSum c α n - smallCenter c ε n) α - (fun α : ℝ => largeSum c ε α n) α) ^ 2
        = (signedSmallSum c ε α n - smallCenter c ε n) ^ 2 := by
    intro α
    simp only
    rw [bulkSum_eq_large_add_small c ε α n]
    ring_nf
  have hint : Integrable (fun α : ℝ =>
      ((bulkSum c α n - smallCenter c ε n) - largeSum c ε α n) ^ 2) unifIoo := by
    refine (integrable_sq_signedSmallSum_sub c ε hε n (smallCenter c ε n)).congr ?_
    filter_upwards with α
    exact (hXY α).symm
  have hbd : (∫ α, ((bulkSum c α n - smallCenter c ε n) - largeSum c ε α n) ^ 2 ∂unifIoo)
      ≤ δ ^ 3 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hXY)]
    exact hvar
  rw [LevyProkhorov.dist_probabilityMeasure_def]
  exact levyProkhorovDist_map_le ((measurable_bulkSum c n).sub_const _)
    (measurable_largeSum c ε n) hint hδ hbd

/-- **Corollary 5.3** (Principal Cauchy law), display (43), the statement
of `Kwon1002.principal_cauchy_law`, reproduced token-identically.

Proved from `largeJump_weak_limit` (Prop. 5.1 + continuous mapping),
`signed_small_jumps_variance` (Lem. 5.2) and `compound_tendsto_cauchy`
(the `ε ↓ 0` exponent limit), and from nothing else. -/
theorem principal_cauchy_law (c : ℝ) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  classical
  obtain ⟨C, hC, hvar⟩ := signed_small_jumps_variance c
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
    largeJump_weak_limit c (e k) (he0 k) (he1 k)
  choose ρ hρ using hlarge
  have hcauchy : Tendsto ρ atTop (𝓝 cauchyProb) :=
    compound_tendsto_cauchy c e he0 he1 helim ρ hρ
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

end Assembly5

end Kwon1002
