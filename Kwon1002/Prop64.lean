import Kwon1002.Section6Skeleton
import Kwon1002.Prop64Variance
import Kwon1002.WindowLaws
import Kwon1002.WindowMarginal
import Kwon1002.DigitLaw
import Kwon1002.CarryGraph
import Kwon1002.StationaryIdentity31
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Proposition 6.4 of v5: the bounded-remainder weak law, reduced to named inputs

This file carries out the assembly step of Section 6 of manuscript v5
(`manuscript/erdos1002_cauchy_limit_revision_v5.tex`, lines 1295-1463) and
of the revision note `manuscript/proposition_6_4_revision_note.pdf`.

Two targets of `Kwon1002.Section6Skeleton` are reproduced here verbatim,
`display_55_monomial_approximation` and
`prop_6_4_bounded_remainder_weak_law`, and both are *proved* from a short
list of explicitly named inputs.  The inputs are the analytic facts of the
section; everything that is bookkeeping (Minkowski, Chebyshev, the change
of variables along `π_{R+M,R}`, the passage from a complex to a real
combination of monomials, the order of the three limits) is carried out.

## What is proved outright

* A small `L²` toolkit: Chebyshev in the form the last line of the proof
  needs, the centering bound `‖Z - E Z‖₂ ≤ 2‖Z‖₂`, and the Minkowski
  estimate for the alternating normalised averages, displays (58) and (59)
  of v5.
* `card_bulkJ_le`: `|J_n| ≤ L/λ + 1`, which is what turns the per-index
  `L²` bounds into a bound on the average with an absolute constant.
* The window-symbol algebra `symConj`, `symAdd`, `symSmul`, `symRe` and the
  identity `(symRe U).evalWindow w = ((U.evalWindow w).re : ℂ)`.  This
  is the step "adjoining the conjugate monomials shows that `Re P` is
  again a finite linear combination of monomials".
* `display_55_monomial_approximation` from the four chain steps of the
  revision note, `B^{(R)} → G → G_M → G_M 1_E → P_{R,M}`, including the
  identity `‖f ∘ π_{R+M,R}‖_{L²(μ_{R+M})} = ‖f‖_{L²(μ_R)}` coming from
  `windowProj_map_windowLaw`.
* `prop_6_4_bounded_remainder_weak_law` from the three `L²` inputs
  (carry truncation, polynomial approximation, polynomial variance), with
  the limits taken in the order `n → ∞`, then `M → ∞`, then `R → ∞`.

## Inputs left sorried

Each is stated in this file with the manuscript step it corresponds to and
the obstruction that prevents closing it here.  None of them is a
restatement of a target; each is a strictly smaller analytic fact.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate ENNReal BoundedContinuousFunction

namespace Kwon1002

namespace Prop64

noncomputable section

/-! ## The probability space `((0,1), Lebesgue)` -/

instance isProbabilityMeasure_restrict_Ioo :
    IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  simp

/-! ## An `L²` toolkit -/

/-- Chebyshev's inequality in the shape used to close Proposition 6.4:
an `L²` bound `t` on `f` bounds the measure of `{|f| ≥ ε}` by `(t/ε)²`. -/
theorem measReal_ge_le_of_eLpNorm_le {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t)
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal t) :
    μ.real {α : ℝ | ε ≤ |f α|} ≤ (t / ε) ^ 2 := by
  have hset : {α : ℝ | ε ≤ |f α|} = {α : ℝ | ENNReal.ofReal ε ≤ ‖f α‖ₑ} := by
    ext α
    simp only [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).symm
  have hne0 : ENNReal.ofReal ε ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hε]
  have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm μ (p := 2) (f := f)
      (by norm_num) (by norm_num) hf hne0 (fun h => absurd h ENNReal.ofReal_ne_top)
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  rw [h2] at hcheb
  have hstep : μ {α : ℝ | ε ≤ |f α|} ≤ ENNReal.ofReal ((t / ε) ^ 2) := by
    rw [hset]
    refine hcheb.trans ?_
    have hmono : eLpNorm f 2 μ ^ (2 : ℝ) ≤ (ENNReal.ofReal t) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    refine (mul_le_mul_left' hmono _).trans ?_
    have hinv : (ENNReal.ofReal ε)⁻¹ = ENNReal.ofReal ε⁻¹ :=
      (ENNReal.ofReal_inv_of_pos hε).symm
    rw [hinv]
    have e1 : (ENNReal.ofReal ε⁻¹) ^ (2 : ℝ) = ENNReal.ofReal ((ε⁻¹) ^ 2) := by
      rw [ENNReal.ofReal_pow (by positivity)]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    have e2 : (ENNReal.ofReal t) ^ (2 : ℝ) = ENNReal.ofReal (t ^ 2) := by
      rw [ENNReal.ofReal_pow ht]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rw [e1, e2, ← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    field_simp
  have hle := ENNReal.toReal_mono (by simp) hstep
  rwa [ENNReal.toReal_ofReal (by positivity)] at hle

/-- Convergence in probability from convergence in `L²`, the final step of
the proof of Proposition 6.4. -/
theorem tendsto_measReal_of_eLpNorm {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal η)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => μ.real {α : ℝ | ε ≤ |f n α|}) atTop (𝓝 0) := by
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro η hη
  have hspos : 0 < Real.sqrt (η / 2) := Real.sqrt_pos.mpr (by linarith)
  have ht : 0 < ε * Real.sqrt (η / 2) := by positivity
  filter_upwards [h (ε * Real.sqrt (η / 2)) ht] with n hn
  have hb := measReal_ge_le_of_eLpNorm_le (hf n) hε ht.le hn
  have hdiv : (ε * Real.sqrt (η / 2)) / ε = Real.sqrt (η / 2) := by
    field_simp
  rw [hdiv, Real.sq_sqrt (by linarith)] at hb
  have hnn : 0 ≤ μ.real {α : ℝ | ε ≤ |f n α|} := measureReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith

/-- `‖Z - E Z‖₂ ≤ 2‖Z‖₂` on a probability space. -/
theorem eLpNorm_center_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {Z : ℝ → ℝ}
    (hZ : MemLp Z 2 μ) :
    eLpNorm (fun α => Z α - ∫ β, Z β ∂μ) 2 μ ≤ 2 * eLpNorm Z 2 μ := by
  have h1 : eLpNorm (fun α => Z α - ∫ β, Z β ∂μ) 2 μ
      ≤ eLpNorm Z 2 μ + eLpNorm (fun _ : ℝ => ∫ β, Z β ∂μ) 2 μ :=
    eLpNorm_sub_le hZ.1 aestronglyMeasurable_const (by norm_num)
  have h2 : eLpNorm (fun _ : ℝ => ∫ β, Z β ∂μ) 2 μ = ‖∫ β, Z β ∂μ‖ₑ := by
    rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
    simp
  have h3 : ‖∫ β, Z β ∂μ‖ₑ ≤ eLpNorm Z 2 μ := by
    calc ‖∫ β, Z β ∂μ‖ₑ ≤ ∫⁻ β, ‖Z β‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm Z 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm Z 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hZ.1
  rw [h2] at h1
  calc eLpNorm (fun α => Z α - ∫ β, Z β ∂μ) 2 μ ≤ eLpNorm Z 2 μ + eLpNorm Z 2 μ := by
        exact h1.trans (by gcongr)
    _ = 2 * eLpNorm Z 2 μ := (two_mul _).symm

/-! ## The alternating normalised average of §6 -/

/-- `(1/L) Σ_{j ∈ s} (-1)^j (Z_j - E Z_j)`, the quantity of (54) and of
displays (58) and (59). -/
def centeredAvg (L : ℝ) (s : Finset ℕ) (Z : ℕ → ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / L) * ∑ j ∈ s, (-1 : ℝ) ^ j * (Z j α - ∫ β in Ioo (0 : ℝ) 1, Z j β)

theorem aestronglyMeasurable_centeredAvg {L : ℝ} {s : Finset ℕ} {Z : ℕ → ℝ → ℝ}
    (hZ : ∀ j ∈ s, AEStronglyMeasurable (Z j) (volume.restrict (Ioo (0 : ℝ) 1))) :
    AEStronglyMeasurable (centeredAvg L s Z) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine AEStronglyMeasurable.const_mul ?_ _
  refine Finset.aestronglyMeasurable_fun_sum _ ?_
  intro j hj
  exact ((hZ j hj).sub aestronglyMeasurable_const).const_mul _

/-- The average is additive: this is the linearity that lets the three
`L²` errors of the proof be combined. -/
theorem centeredAvg_sub {L : ℝ} {s : Finset ℕ} {Z Y : ℕ → ℝ → ℝ}
    (hZ : ∀ j ∈ s, Integrable (Z j) (volume.restrict (Ioo (0 : ℝ) 1)))
    (hY : ∀ j ∈ s, Integrable (Y j) (volume.restrict (Ioo (0 : ℝ) 1))) (α : ℝ) :
    centeredAvg L s Z α - centeredAvg L s Y α
      = centeredAvg L s (fun j α => Z j α - Y j α) α := by
  simp only [centeredAvg, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_sub (hZ j hj) (hY j hj)]
  ring

/-- **Minkowski for the alternating average**, displays (58) and (59) of
v5: a uniform per-index `L²` bound `b` gives the bound
`(2/L)|s| b` for the centered average. -/
theorem eLpNorm_centeredAvg_le {L b : ℝ} {s : Finset ℕ} {Z : ℕ → ℝ → ℝ}
    (hL : 0 < L) (hb : 0 ≤ b)
    (hZ : ∀ j ∈ s, MemLp (Z j) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hbd : ∀ j ∈ s, eLpNorm (Z j) 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal b) :
    eLpNorm (centeredAvg L s Z) 2 (volume.restrict (Ioo (0 : ℝ) 1))
      ≤ ENNReal.ofReal ((2 / L) * s.card * b) := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  set g : ℕ → ℝ → ℝ := fun j α => (-1 : ℝ) ^ j * (Z j α - ∫ β, Z j β ∂μ) with hg
  have hgmeas : ∀ j ∈ s, AEStronglyMeasurable (g j) μ := by
    intro j hj
    exact (((hZ j hj).1).sub aestronglyMeasurable_const).const_mul _
  have hkey : ∀ j ∈ s, eLpNorm (g j) 2 μ ≤ 2 * ENNReal.ofReal b := by
    intro j hj
    have hsm : g j = ((-1 : ℝ) ^ j) • (fun α => Z j α - ∫ β, Z j β ∂μ) := rfl
    have hone : ‖((-1 : ℝ) ^ j)‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_pow, abs_neg, abs_one, one_pow, ENNReal.ofReal_one]
    have h1 : eLpNorm (g j) 2 μ = eLpNorm (fun α => Z j α - ∫ β, Z j β ∂μ) 2 μ := by
      rw [hsm, eLpNorm_const_smul, hone, one_mul]
    rw [h1]
    calc eLpNorm (fun α => Z j α - ∫ β, Z j β ∂μ) 2 μ ≤ 2 * eLpNorm (Z j) 2 μ :=
          eLpNorm_center_le (hZ j hj)
      _ ≤ 2 * ENNReal.ofReal b := by gcongr; exact hbd j hj
  have hcs : centeredAvg L s Z = (1 / L) • (fun α => ∑ j ∈ s, g j α) := rfl
  have hLn : ‖(1 / L)‖ₑ = ENNReal.ofReal (1 / L) := Real.enorm_eq_ofReal (by positivity)
  have hsum : eLpNorm (fun α => ∑ j ∈ s, g j α) 2 μ ≤ ∑ j ∈ s, eLpNorm (g j) 2 μ := by
    have hfun : (fun α => ∑ j ∈ s, g j α) = ∑ j ∈ s, g j := by
      funext α; simp
    rw [hfun]
    exact eLpNorm_sum_le (μ := μ) (p := 2) (f := g) (s := s) hgmeas (by norm_num)
  rw [hcs, eLpNorm_const_smul, hLn]
  calc ENNReal.ofReal (1 / L) * eLpNorm (fun α => ∑ j ∈ s, g j α) 2 μ
      ≤ ENNReal.ofReal (1 / L) * ∑ j ∈ s, eLpNorm (g j) 2 μ := by gcongr
    _ ≤ ENNReal.ofReal (1 / L) * ∑ _j ∈ s, (2 * ENNReal.ofReal b) := by
        gcongr with j hj
        exact hkey j hj
    _ = ENNReal.ofReal (1 / L) * ((s.card : ℝ≥0∞) * (2 * ENNReal.ofReal b)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((2 / L) * s.card * b) := by
        rw [show ((s.card : ℝ≥0∞)) = ENNReal.ofReal (s.card : ℝ) from
              (ENNReal.ofReal_natCast _).symm,
            show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 from by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / L)]
        congr 1
        field_simp <;> ring

/-! ## The size of the bulk index set -/

theorem lyapunov_pos : 0 < lyapunov := by
  unfold lyapunov
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < Real.pi ^ 2 := by positivity
  exact div_pos hp (by linarith)

theorem Lnorm_nonneg (n : ℕ) : 0 ≤ Lnorm n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [Lnorm, h]
  · exact Real.log_nonneg (by exact_mod_cast h)

theorem one_le_Lnorm {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Lnorm n := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) :=
    le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) h3
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  rw [Lnorm, Real.le_log_iff_exp_le hpos]
  exact he

/-- `|J_n| ≤ L/λ + 1`: the bulk index set sits inside `{0, …, m_n}` and
`m_n = ⌊L/λ⌋`. -/
theorem card_bulkJ_le (n : ℕ) : ((bulkJ n).card : ℝ) ≤ Lnorm n / lyapunov + 1 := by
  have hsub : bulkJ n ⊆ Finset.range (mIndex n + 1) := Finset.filter_subset _ _
  have hcard : (bulkJ n).card ≤ mIndex n + 1 := by
    simpa using Finset.card_le_card hsub
  have hnn : 0 ≤ Lnorm n / lyapunov := div_nonneg (Lnorm_nonneg n) lyapunov_pos.le
  have hfl : ((mIndex n : ℕ) : ℝ) ≤ Lnorm n / lyapunov := by
    rw [mIndex]
    exact Nat.floor_le hnn
  calc ((bulkJ n).card : ℝ) ≤ ((mIndex n + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (mIndex n : ℝ) + 1 := by push_cast; ring
    _ ≤ Lnorm n / lyapunov + 1 := by linarith

/-! ## Named inputs for Proposition 6.4

The three `L²` facts the proof of Proposition 6.4 consumes, together with
the `L²` membership of the three families of random variables. -/

/-- **Input (carry truncation).**  v5 (57) together with the boundedness of
`Φ` and `W` and `p_R → 0`: for every accuracy `ε` there is a truncation
radius `R` for which the bounded remainder and its carry-truncated version
are within `ε` in `L²`, uniformly over the bulk, for all large `n`.

Consumes `Section6Skeleton.carry_coupling` (57),
`Section6Skeleton.exists_absolute_carry_bound`,
`Section6Skeleton.noResetProb_tendsto_zero`, and the boundedness of the
integrand.  **Obstruction.**  `carry_coupling` is Lemma 6.3-gated and
still sorried in the skeleton.  The other inputs are now in the tree:
`exists_absolute_carry_bound` is proved there, `noResetProb_tendsto_zero`
is proved as `CarryGraph.noResetProb_tendsto_zero`, and the uniform
bounds `|B_j| ≤ C₀` and `|B_j^{(R)}| ≤ 45/8` are `principal_term` and
`abs_BremainderTrunc_le` below, so once (57) closes this statement is
Chebyshev bookkeeping. -/
theorem carry_truncation_L2_small :
    ∀ ε > 0, ∃ R : ℕ, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      eLpNorm (fun α => Bremainder α n j - BremainderTrunc α n R j) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε := by
  sorry

/-- **Input (polynomial approximation, transferred).**  Display (55) at
radius `R + M` combined with (56): for every accuracy there is a
real-valued finite combination `P` of the monomials (32) whose values at
the actual times `j` approximate the carry-truncated remainder in `L²`,
uniformly over the bulk, for all large `n`.

Consumes `display_55_monomial_approximation` (proved below from the chain
of the revision note) and `Section6Skeleton.actual_L2_transfer`.
**Obstruction.**  `actual_L2_transfer` is sorried, and the present
statement is its `eLpNorm` form: converting the skeleton's
`|∫ ‖·‖² - δ²| < ε` into an `eLpNorm` bound needs the `L²`-membership of
the integrand, which is the content of `memLp_BremainderTrunc` and
`memLp_symbolAt` below. -/
theorem trunc_poly_L2_small (R : ℕ) :
    ∀ ε > 0, ∃ M K : ℕ, ∃ P : WindowSymbol (R + M) K,
      (∀ w : WindowSpace (R + M), (P.evalWindow w).im = 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        eLpNorm (fun α => BremainderTrunc α n R j - (P.at α n j).re) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal ε := by
  sorry

/-- **Input (variance of the polynomial part).**  For a *fixed* finite
combination of monomials the alternating centered average has variance
`o(1)`: v5 lines 1418-1432, the diagonal contributing `O(L)`, the
exceptional pairs `O(LH) = o(L²)`, and every other pair the three decaying
terms of (34).

The covariance bookkeeping and the proved unconditional form of Proposition 4.2
are packaged upstream in `Prop64Variance.poly_centered_avg_L2_tendsto_zero`. -/
theorem poly_centered_avg_L2_tendsto_zero (R M K : ℕ) (P : WindowSymbol (R + M) K) :
    Tendsto (fun n : ℕ => eLpNorm
        (centeredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)) 2
        (volume.restrict (Ioo (0 : ℝ) 1))) atTop (𝓝 0) := by
  simpa [centeredAvg, Prop64Variance.varianceCenteredAvg] using
    Prop64Variance.poly_centered_avg_L2_tendsto_zero R M K P

/-- The §2 carry `u_j = {N_j x_j}` is a measurable function of `α`. -/
theorem measurable_carry (n j : ℕ) : Measurable fun α : ℝ => carry α n j := by
  have hcast : Measurable fun α : ℝ => ((heightSeq α n j : ℕ) : ℝ) :=
    (measurable_from_top (f := fun m : ℕ => (m : ℝ))).comp (measurable_heightSeq n j)
  simpa [carry] using (hcast.mul (measurable_gaussIter j)).fract

/-- `B_j` is a measurable function of `α`: `Φ` is a rational expression in
the (measurable) carry and Gauss iterate, and the principal term is the
measurable mark `a_{j+1} W(θ_j)`. -/
theorem measurable_Bremainder (n j : ℕ) : Measurable fun α : ℝ => Bremainder α n j := by
  have hc := measurable_carry n j
  have hx := measurable_gaussIter j
  have hPhi : Measurable fun α : ℝ => Phi (gaussIter α j) (carry α n j) := by
    unfold Phi
    exact ((hc.mul (measurable_const.sub hc)).div (measurable_const.mul hx)).sub
      (hc.div measurable_const)
  have hmark : Measurable fun α : ℝ => (digit α j : ℝ) * W (theta α n j) :=
    (measurable_digitCast j).mul (measurable_W.comp (measurable_theta n j))
  simpa [Bremainder] using hPhi.sub hmark

/-- **Input (`L²` membership).**  `B_j` is a bounded measurable function
of `α`: measurability is `measurable_Bremainder`, and the pointwise bound
`|B_j| ≤ C₀` on irrationals of `(0,1)` is exactly Proposition 2.2
(`principal_term`). -/
theorem memLp_Bremainder (n j : ℕ) :
    MemLp (fun α => Bremainder α n j) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine MemLp.of_bound (measurable_Bremainder n j).aestronglyMeasurable Czero ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict] with α hα hirr
  rw [Real.norm_eq_abs]
  simpa [Bremainder] using principal_term α hα hirr n j

/-- `θ_{j-1}` lies in `[0,1)`: it is `0` at `j = 0` and a fractional part
otherwise. -/
theorem thetaPred_mem_Ico (α : ℝ) (n j : ℕ) : thetaPred α n j ∈ Ico (0 : ℝ) 1 := by
  cases j with
  | zero =>
      show (0 : ℝ) ∈ Ico (0 : ℝ) 1
      constructor <;> norm_num
  | succ m => exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- `θ_j` lies in `[0,1)`. -/
theorem theta_mem_Ico (α : ℝ) (n j : ℕ) : theta α n j ∈ Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **The absolute bound on the truncated carries** (v5 lines 1253-1258):
started from `0`, the trajectory of the carry map along the actual orbit
stays in `[0, 9]`.  The two-step induction is the one of
`CarryGraph.iterCarry_bounds`: one step gives `c' < x(c+1)+1`, two steps
contract by `x·Tx ≤ 1/2` (`CarryGraph.mul_gaussMap_le_half`), which beats
the additive drift. -/
theorem carryFrom_bounds {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n i : ℕ) : ∀ k, 0 ≤ carryFrom α n i k ∧ carryFrom α n i k ≤ 9 := by
  have hx : ∀ m : ℕ, gaussIter α m ∈ Ioo (0 : ℝ) 1 := gaussIter_mem_Ioo hα hirr
  have hr : ∀ m : ℕ, thetaPred α n m ∈ Ico (0 : ℝ) 1 := thetaPred_mem_Ico α n
  have hs : ∀ m : ℕ, theta α n m ∈ Ico (0 : ℝ) 1 := theta_mem_Ico α n
  have hlow : ∀ k, 0 ≤ carryFrom α n i k → 0 ≤ carryFrom α n i (k + 1) := fun k hk =>
    CarryGraph.carryMap_nonneg (hx (i + k)).1.le (hr (i + k)).1 (hs (i + k)).2 hk
  have hup : ∀ k, (carryFrom α n i (k + 1) : ℝ)
      < gaussIter α (i + k) * ((carryFrom α n i k : ℝ) + 1) + 1 := fun k =>
    CarryGraph.carryMap_lt (hx (i + k)).1 (hr (i + k)).2 (hs (i + k)).1 _
  have hprod : ∀ k : ℕ, gaussIter α (i + (k + 1)) * gaussIter α (i + k) ≤ 1 / 2 := by
    intro k
    have hstep : gaussIter α (i + (k + 1)) = gaussMap (gaussIter α (i + k)) := by
      rw [show i + (k + 1) = (i + k) + 1 from rfl, gaussIter_succ]
    rw [hstep, mul_comm]
    exact CarryGraph.mul_gaussMap_le_half (hx (i + k))
  have hQ : ∀ k, (0 ≤ carryFrom α n i k ∧ carryFrom α n i k ≤ 9)
      ∧ (0 ≤ carryFrom α n i (k + 1) ∧ carryFrom α n i (k + 1) ≤ 9) := by
    intro k
    induction k with
    | zero =>
        have hP0 : 0 ≤ carryFrom α n i 0 ∧ carryFrom α n i 0 ≤ 9 := by
          show (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 9
          norm_num
        refine ⟨hP0, hlow 0 hP0.1, ?_⟩
        have h1 := hup 0
        have hx1 := hx (i + 0)
        have h00 : carryFrom α n i 0 = 0 := rfl
        rw [h00] at h1
        have hlt : (carryFrom α n i (0 + 1) : ℝ) < 2 := by
          push_cast at h1
          nlinarith [hx1.2, hx1.1]
        have hle : carryFrom α n i (0 + 1) < 2 := by exact_mod_cast hlt
        omega
    | succ k ih =>
        obtain ⟨hPk, hPk1⟩ := ih
        refine ⟨hPk1, hlow (k + 1) hPk1.1, ?_⟩
        have h2 := hup (k + 1)
        have hpr := hprod k
        have hx1 := hx (i + k)
        have hx2 := hx (i + (k + 1))
        have hc0 : (0 : ℝ) ≤ (carryFrom α n i k : ℝ) := by exact_mod_cast hPk.1
        have hc9 : (carryFrom α n i k : ℝ) ≤ 9 := by exact_mod_cast hPk.2
        have hc10 : (0 : ℝ) ≤ (carryFrom α n i (k + 1) : ℝ) := by exact_mod_cast hPk1.1
        have hmul1 : gaussIter α (i + (k + 1)) * (carryFrom α n i (k + 1) : ℝ)
            ≤ gaussIter α (i + (k + 1))
              * (gaussIter α (i + k) * ((carryFrom α n i k : ℝ) + 1) + 1) :=
          mul_le_mul_of_nonneg_left (hup k).le hx2.1.le
        have hmul2 : (gaussIter α (i + (k + 1)) * gaussIter α (i + k))
              * ((carryFrom α n i k : ℝ) + 1)
            ≤ (1 / 2) * ((carryFrom α n i k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hpr (by linarith)
        have hfin : (carryFrom α n i (k + 1 + 1) : ℝ) < 8 := by
          nlinarith [h2, hmul1, hmul2, hx2.2, hx2.1.le, hc9]
        have hle7 : carryFrom α n i (k + 1 + 1) < 8 := by exact_mod_cast hfin
        omega
  exact fun k => (hQ k).1

/-- `W` only sees the fractional part. -/
theorem W_fract (t : ℝ) : W (Int.fract t) = W t := by
  unfold W
  rw [Int.fract_fract]

/-- **The uniform bound on the carry-truncated remainder**:
`|B_j^{(R)}| ≤ 45/8` for irrational `α ∈ (0,1)`.  This is the principal
split of Proposition 2.2 run with the *truncated* carry: with
`ũ = {θ_j - x_j(d̃ + θ_{j-1})}` and `0 ≤ d̃ ≤ 9` (`carryFrom_bounds`),
the `W`-Lipschitz estimate gives `|W ũ - W θ_j| ≤ x_j (d̃ + θ_{j-1})/2`,
and `principal_bound` applies with `E = d̃ + θ_{j-1} ≤ 10`. -/
theorem abs_BremainderTrunc_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n R j : ℕ) : |BremainderTrunc α n R j| ≤ 45 / 8 := by
  have hx := gaussIter_mem_Ioo hα hirr j
  have hx' := gaussIter_mem_Ioo hα hirr (j + 1)
  have hd0 : 0 ≤ carryTrunc α n R j := (carryFrom_bounds hα hirr n (j - R) R).1
  have hd9 : carryTrunc α n R j ≤ 9 := (carryFrom_bounds hα hirr n (j - R) R).2
  have hr := thetaPred_mem_Ico α n j
  have hd0' : (0 : ℝ) ≤ (carryTrunc α n R j : ℝ) := by exact_mod_cast hd0
  have hd9' : (carryTrunc α n R j : ℝ) ≤ 9 := by exact_mod_cast hd9
  have hE0 : 0 ≤ (carryTrunc α n R j : ℝ) + thetaPred α n j := by linarith [hr.1]
  have hE10 : (carryTrunc α n R j : ℝ) + thetaPred α n j ≤ 10 := by linarith [hr.2]
  have huf : carryU (gaussIter α j) (thetaPred α n j) (theta α n j) (carryTrunc α n R j)
      = Int.fract (theta α n j
          - gaussIter α j * ((carryTrunc α n R j : ℝ) + thetaPred α n j)) := rfl
  have hu0 : 0 ≤ carryU (gaussIter α j) (thetaPred α n j) (theta α n j)
      (carryTrunc α n R j) := by
    rw [huf]
    exact Int.fract_nonneg _
  have hu1 : carryU (gaussIter α j) (thetaPred α n j) (theta α n j)
      (carryTrunc α n R j) < 1 := by
    rw [huf]
    exact Int.fract_lt_one _
  have hd' : |W (carryU (gaussIter α j) (thetaPred α n j) (theta α n j)
        (carryTrunc α n R j)) - W (theta α n j)|
      ≤ gaussIter α j * ((carryTrunc α n R j : ℝ) + thetaPred α n j) / 2 := by
    rw [huf, W_fract,
      show theta α n j - gaussIter α j * ((carryTrunc α n R j : ℝ) + thetaPred α n j)
          = theta α n j
            + -(gaussIter α j * ((carryTrunc α n R j : ℝ) + thetaPred α n j)) from by ring]
    have h := W_sub_le (theta α n j)
      (-(gaussIter α j * ((carryTrunc α n R j : ℝ) + thetaPred α n j)))
    rwa [abs_neg, abs_of_nonneg (mul_nonneg hx.1.le hE0)] at h
  have hmain := principal_bound (gaussIter α j) (gaussIter α (j + 1))
    (carryU (gaussIter α j) (thetaPred α n j) (theta α n j) (carryTrunc α n R j))
    (theta α n j) (digit α j : ℝ) ((carryTrunc α n R j : ℝ) + thetaPred α n j) 10
    hx.1 hx'.1 hx'.2 hu0 hu1 (Nat.cast_nonneg _)
    (inv_gaussIter_eq hα hirr j) hE0 hE10 (W_eq_of_mem hu0 hu1) hd'
  calc |BremainderTrunc α n R j|
      ≤ 10 / 2 + 5 / 8 := hmain
    _ = 45 / 8 := by norm_num

/-- The truncated carry `d_j^{(R)}` is a measurable function of `α`. -/
theorem measurable_carryFrom (n i : ℕ) : ∀ k, Measurable fun α : ℝ => carryFrom α n i k := by
  intro k
  induction k with
  | zero =>
      simp only [carryFrom]
      exact measurable_const
  | succ k ih =>
      have hcast : Measurable fun α : ℝ => ((carryFrom α n i k : ℤ) : ℝ) :=
        (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp ih
      have hexpr : Measurable fun α : ℝ =>
          gaussIter α (i + k) * (((carryFrom α n i k : ℤ) : ℝ) + thetaPred α n (i + k))
            - theta α n (i + k) :=
        ((measurable_gaussIter (i + k)).mul
          (hcast.add (Prop42.measurable_thetaPred n (i + k)))).sub
          (measurable_theta n (i + k))
      simpa [carryFrom, carryMap] using hexpr.ceil

/-- `B_j^{(R)}` is a measurable function of `α`. -/
theorem measurable_BremainderTrunc (R n j : ℕ) :
    Measurable fun α : ℝ => BremainderTrunc α n R j := by
  have hct : Measurable fun α : ℝ => ((carryTrunc α n R j : ℤ) : ℝ) :=
    (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp (measurable_carryFrom n (j - R) R)
  have hu : Measurable fun α : ℝ =>
      carryU (gaussIter α j) (thetaPred α n j) (theta α n j) (carryTrunc α n R j) := by
    have hexpr : Measurable fun α : ℝ =>
        Int.fract (theta α n j
          - gaussIter α j * (((carryTrunc α n R j : ℤ) : ℝ) + thetaPred α n j)) :=
      ((measurable_theta n j).sub ((measurable_gaussIter j).mul
        (hct.add (Prop42.measurable_thetaPred n j)))).fract
    simpa [carryU] using hexpr
  have hPhi : Measurable fun α : ℝ => Phi (gaussIter α j)
      (carryU (gaussIter α j) (thetaPred α n j) (theta α n j) (carryTrunc α n R j)) := by
    unfold Phi
    exact ((hu.mul (measurable_const.sub hu)).div
        (measurable_const.mul (measurable_gaussIter j))).sub (hu.div measurable_const)
  have hmark : Measurable fun α : ℝ => (digit α j : ℝ) * W (theta α n j) :=
    (measurable_digitCast j).mul (measurable_W.comp (measurable_theta n j))
  simpa [BremainderTrunc] using hPhi.sub hmark

/-- **Input (`L²` membership).**  The carry-truncated remainder is a
bounded measurable function of `α`: `measurable_BremainderTrunc` and the
uniform bound `abs_BremainderTrunc_le`. -/
theorem memLp_BremainderTrunc (R n j : ℕ) :
    MemLp (fun α => BremainderTrunc α n R j) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine MemLp.of_bound (measurable_BremainderTrunc R n j).aestronglyMeasurable (45 / 8) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict] with α hα hirr
  rw [Real.norm_eq_abs]
  exact abs_BremainderTrunc_le hα hirr n R j

/-- A window symbol placed at time `j` is a measurable function of `α`:
the word `w_j(α)` lands in the discrete space `Fin (2R) → ℕ`, so the
coefficient is measurable with no hypothesis, and the character is
continuous in `(θ_{j-1}, θ_j)`. -/
theorem measurable_symbolAt {R K : ℕ} (P : WindowSymbol R K) (n j : ℕ) :
    Measurable fun α : ℝ => P.at α n j := by
  unfold WindowSymbol.at
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ =>
    Measurable.mul ?_ ?_
  · exact (Measurable.of_discrete (f := fun v : Fin (2 * R) → ℕ => P.coeff v r s)).comp
      (measurable_pi_lambda _ fun _ => Prop42.measurable_digitNat _)
  · exact Prop42.continuous_torusChar.measurable.comp
      (((Prop42.measurable_thetaPred n j).const_mul _).add
        ((measurable_theta n j).const_mul _))

/-- A window symbol is bounded by the total mass of its coefficients: each
monomial has modulus `1`, and the coefficients vanish off the finite word
set `P.words`. -/
theorem norm_symbolAt_le {R K : ℕ} (P : WindowSymbol R K) (α : ℝ) (n j : ℕ) :
    ‖P.at α n j‖
      ≤ ∑ w ∈ P.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖ := by
  classical
  have hstep : ‖P.at α n j‖
      ≤ ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ‖P.coeff (windowWord R α j) r s‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, Prop42.norm_torusChar, mul_one]
  refine hstep.trans ?_
  by_cases hw : windowWord R α j ∈ P.words
  · exact Finset.single_le_sum
      (f := fun w => ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖)
      (fun w _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hw
  · have hzero : ∀ r s : ℤ, P.coeff (windowWord R α j) r s = 0 :=
      fun r s => P.coeff_support _ r s hw
    simp only [hzero, norm_zero, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **Input (`L²` membership).**  A window symbol placed at time `j` is a
finite sum of bounded measurable functions of `α`. -/
theorem memLp_symbolAt {R K : ℕ} (P : WindowSymbol R K) (n j : ℕ) :
    MemLp (fun α => (P.at α n j).re) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  classical
  refine MemLp.of_bound
    ((Complex.measurable_re.comp (measurable_symbolAt P n j)).aestronglyMeasurable)
    (∑ w ∈ P.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖)
    (Filter.Eventually.of_forall fun α => ?_)
  refine le_trans ?_ (norm_symbolAt_le P α n j)
  rw [Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

/-! ## Proposition 6.4 -/

/-- The `L²` convergence behind Proposition 6.4: the centered alternating
average of the bounded remainders tends to `0` in `L²(dα)`.  The three
limits are taken in the manuscript's order, `n → ∞` for fixed `R, M`, then
`M → ∞`, then `R → ∞`; here that order is visible as the order in which
the three inputs are invoked, each one fixing data that the next one uses. -/
theorem remainderAvg_eLpNorm_small :
    ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      eLpNorm (centeredAvg (Lnorm n) (bulkJ n) (fun j α => Bremainder α n j)) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal η := by
  intro η hη
  have hlyne : lyapunov ≠ 0 := ne_of_gt lyapunov_pos
  have hlp : 0 < 1 / lyapunov := one_div_pos.mpr lyapunov_pos
  obtain ⟨A, hApos, hA⟩ : ∃ A : ℝ, 0 < A ∧ (1 : ℝ) / lyapunov + 1 = A :=
    ⟨1 / lyapunov + 1, by linarith, rfl⟩
  have hAne : A ≠ 0 := ne_of_gt hApos
  set b : ℝ := η / (3 * (2 * A)) with hbdef
  have hbpos : 0 < b := by
    rw [hbdef]; apply div_pos hη; linarith
  -- Step 1: fix `R` so that the carry truncation costs at most `b` per index.
  obtain ⟨R, hR⟩ := carry_truncation_L2_small b hbpos
  -- Step 2: fix `M, K, P` so that the monomial approximation costs at most `b` per index.
  obtain ⟨M, K, P, _hPim, hP⟩ := trunc_poly_L2_small R b hbpos
  -- Step 3: for these fixed data the polynomial average has vanishing variance.
  have hvar : ∀ᶠ n : ℕ in atTop,
      eLpNorm (centeredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal (η / 3) :=
    ENNReal.tendsto_nhds_zero.mp (poly_centered_avg_L2_tendsto_zero R M K P)
      (ENNReal.ofReal (η / 3)) (by simp [ENNReal.ofReal_pos]; linarith)
  filter_upwards [hR, hP, hvar, eventually_ge_atTop 3] with n h1 h2 h3 hn3
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  set L : ℝ := Lnorm n with hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (one_le_Lnorm hn3)
  have hL1 : 1 ≤ L := one_le_Lnorm hn3
  set s : Finset ℕ := bulkJ n with hs
  set ZB : ℕ → ℝ → ℝ := fun j α => Bremainder α n j with hZB
  set ZT : ℕ → ℝ → ℝ := fun j α => BremainderTrunc α n R j with hZT
  set ZP : ℕ → ℝ → ℝ := fun j α => (P.at α n j).re with hZP
  set D1 : ℕ → ℝ → ℝ := fun j α => ZB j α - ZT j α with hD1
  set D2 : ℕ → ℝ → ℝ := fun j α => ZT j α - ZP j α with hD2
  -- the constant produced by Minkowski plus `|J_n| ≤ L/λ + 1`
  have hcard : (2 / L) * s.card * b ≤ η / 3 := by
    have hc := card_bulkJ_le n
    rw [← hs, ← hL] at hc
    have hLne : L ≠ 0 := ne_of_gt hLpos
    have hLinv : 1 / L ≤ 1 := by
      rw [div_le_one hLpos]; exact hL1
    have h0 : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    have hstep : (1 / L) * (s.card : ℝ) ≤ A := by
      have hmul : (1 / L) * (s.card : ℝ) ≤ (1 / L) * (L / lyapunov + 1) := by
        apply mul_le_mul_of_nonneg_left hc (by positivity)
      have hexp : (1 / L) * (L / lyapunov + 1) = 1 / lyapunov + 1 / L := by
        field_simp <;> ring
      rw [hexp] at hmul
      rw [← hA]
      linarith
    have heq : (2 / L) * (s.card : ℝ) * b = 2 * ((1 / L) * (s.card : ℝ)) * b := by
      ring
    rw [heq]
    have hbb : 2 * ((1 / L) * (s.card : ℝ)) * b ≤ 2 * A * b := by
      apply mul_le_mul_of_nonneg_right _ hbpos.le
      linarith
    have hfin : 2 * A * b = η / 3 := by
      rw [hbdef]
      field_simp <;> ring
    linarith
  -- integrability and `L²` membership
  have hmB : ∀ j ∈ s, MemLp (ZB j) 2 μ := fun j _ => memLp_Bremainder n j
  have hmT : ∀ j ∈ s, MemLp (ZT j) 2 μ := fun j _ => memLp_BremainderTrunc R n j
  have hmP : ∀ j ∈ s, MemLp (ZP j) 2 μ := fun j _ => memLp_symbolAt P n j
  have hiB : ∀ j ∈ s, Integrable (ZB j) μ := fun j hj => (hmB j hj).integrable (by norm_num)
  have hiT : ∀ j ∈ s, Integrable (ZT j) μ := fun j hj => (hmT j hj).integrable (by norm_num)
  have hiP : ∀ j ∈ s, Integrable (ZP j) μ := fun j hj => (hmP j hj).integrable (by norm_num)
  -- the three `L²` bounds
  have hb1 : eLpNorm (centeredAvg L s D1) 2 μ ≤ ENNReal.ofReal (η / 3) := by
    refine le_trans (eLpNorm_centeredAvg_le hLpos hbpos.le
      (fun j hj => (hmB j hj).sub (hmT j hj)) (fun j hj => h1 j hj)) ?_
    exact ENNReal.ofReal_le_ofReal hcard
  have hb2 : eLpNorm (centeredAvg L s D2) 2 μ ≤ ENNReal.ofReal (η / 3) := by
    refine le_trans (eLpNorm_centeredAvg_le hLpos hbpos.le
      (fun j hj => (hmT j hj).sub (hmP j hj)) (fun j hj => h2 j hj)) ?_
    exact ENNReal.ofReal_le_ofReal hcard
  -- the decomposition
  have hdec : centeredAvg L s ZB
      = fun α => (centeredAvg L s D1 α + centeredAvg L s D2 α) + centeredAvg L s ZP α := by
    funext α
    have e1 := centeredAvg_sub (L := L) (s := s) hiB hiT α
    have e2 := centeredAvg_sub (L := L) (s := s) hiT hiP α
    rw [← hD1] at e1
    rw [← hD2] at e2
    linarith
  have hm1 : AEStronglyMeasurable (centeredAvg L s D1) μ :=
    aestronglyMeasurable_centeredAvg (fun j hj => ((hmB j hj).sub (hmT j hj)).1)
  have hm2 : AEStronglyMeasurable (centeredAvg L s D2) μ :=
    aestronglyMeasurable_centeredAvg (fun j hj => ((hmT j hj).sub (hmP j hj)).1)
  have hm3 : AEStronglyMeasurable (centeredAvg L s ZP) μ :=
    aestronglyMeasurable_centeredAvg (fun j hj => (hmP j hj).1)
  rw [hdec]
  have htri1 : eLpNorm (fun α => (centeredAvg L s D1 α + centeredAvg L s D2 α)
        + centeredAvg L s ZP α) 2 μ
      ≤ eLpNorm (fun α => centeredAvg L s D1 α + centeredAvg L s D2 α) 2 μ
        + eLpNorm (centeredAvg L s ZP) 2 μ :=
    eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)
  have htri2 : eLpNorm (fun α => centeredAvg L s D1 α + centeredAvg L s D2 α) 2 μ
      ≤ eLpNorm (centeredAvg L s D1) 2 μ + eLpNorm (centeredAvg L s D2) 2 μ :=
    eLpNorm_add_le hm1 hm2 (by norm_num)
  calc eLpNorm (fun α => (centeredAvg L s D1 α + centeredAvg L s D2 α)
          + centeredAvg L s ZP α) 2 μ
      ≤ (eLpNorm (centeredAvg L s D1) 2 μ + eLpNorm (centeredAvg L s D2) 2 μ)
          + eLpNorm (centeredAvg L s ZP) 2 μ := le_trans htri1 (by gcongr)
    _ ≤ (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) + ENNReal.ofReal (η / 3) := by
        gcongr
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

/-- **Proposition 6.4** (Bounded-remainder weak law), v5 lines 1295-1303,
display (54):
`(1/L) Σ_{j ∈ J_n} (-1)^j (B_j - E B_j) → 0` in probability.

**Reading.**  "In probability" is with respect to Lebesgue `α` on
`(0,1)`, the measure every §4-§6 estimate uses, and `E B_j` is
`∫_0^1 B_j dα`.  The order of limits in the proof is `n → ∞`, then
`M → ∞`, then `R → ∞` (v5 line 1462). -/
theorem prop_6_4_bounded_remainder_weak_law :
    ∀ ε > 0,
      Tendsto
        (fun n : ℕ => (volume.restrict (Ioo (0 : ℝ) 1)).real
          {α : ℝ | ε ≤ |(1 / Lnorm n) *
            ∑ j ∈ bulkJ n, (-1 : ℝ) ^ j *
              (Bremainder α n j - ∫ β in Ioo (0 : ℝ) 1, Bremainder β n j)|})
        atTop (𝓝 0) := by
  intro ε hε
  exact tendsto_measReal_of_eLpNorm
    (f := fun n => centeredAvg (Lnorm n) (bulkJ n) (fun j α => Bremainder α n j))
    (fun n => aestronglyMeasurable_centeredAvg (fun j _ => (memLp_Bremainder n j).1))
    remainderAvg_eLpNorm_small hε

/-! ## The window-symbol algebra

Display (55) produces, through identity (31), a *complex* finite
combination of the monomials (32).  The manuscript then says: "Adjoining
the conjugate monomials shows that `Re P` is again a finite linear
combination of monomials and is real-valued."  That step is carried out
here.  It is a genuine step: it needs the index set
`{(r,s) : |r|,|s| ≤ K}` to be symmetric under negation, which it is. -/

/-- Reindexing `r ↦ -r` on the symmetric mode range of (32). -/
theorem sum_Icc_neg {K : ℕ} (f : ℤ → ℂ) :
    ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f (-r)
      = ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f r := by
  refine Finset.sum_nbij' (fun r => -r) (fun r => -r) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a _; exact neg_neg a
  · intro a _; exact neg_neg a
  · intro a _; rfl

theorem torusChar_conj (t : ℝ) : (starRingEnd ℂ) (torusChar t) = torusChar (-t) := by
  simp only [torusChar, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-- The conjugate symbol: negate the modes and conjugate the coefficients. -/
def symConj {R K : ℕ} (U : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := (starRingEnd ℂ) (U.coeff w (-r) (-s))
  words := U.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w (-r) (-s) hw, map_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w (-r) (-s) (by simpa using h), map_zero]

/-- The sum of two symbols of the same radius and cap. -/
def symAdd {R K : ℕ} (U V : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := U.coeff w r s + V.coeff w r s
  words := U.words ∪ V.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w r s (fun h => hw (Finset.mem_union_left _ h)),
        V.coeff_support w r s (fun h => hw (Finset.mem_union_right _ h)), add_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w r s h, V.mode_cap w r s h, add_zero]

/-- A scalar multiple of a symbol. -/
def symSmul {R K : ℕ} (c : ℂ) (U : WindowSymbol R K) : WindowSymbol R K where
  coeff w r s := c * U.coeff w r s
  words := U.words
  coeff_support := by
    intro w r s hw
    rw [U.coeff_support w r s hw, mul_zero]
  mode_cap := by
    intro w r s h
    rw [U.mode_cap w r s h, mul_zero]

@[simp] theorem symConj_coeff {R K : ℕ} (U : WindowSymbol R K)
    (w : Fin (2 * R) → ℕ) (r s : ℤ) :
    (symConj U).coeff w r s = (starRingEnd ℂ) (U.coeff w (-r) (-s)) := rfl

@[simp] theorem symAdd_coeff {R K : ℕ} (U V : WindowSymbol R K)
    (w : Fin (2 * R) → ℕ) (r s : ℤ) :
    (symAdd U V).coeff w r s = U.coeff w r s + V.coeff w r s := rfl

@[simp] theorem symSmul_coeff {R K : ℕ} (c : ℂ) (U : WindowSymbol R K)
    (w : Fin (2 * R) → ℕ) (r s : ℤ) :
    (symSmul c U).coeff w r s = c * U.coeff w r s := rfl

theorem evalWindow_symAdd {R K : ℕ} (U V : WindowSymbol R K) (w : WindowSpace R) :
    (symAdd U V).evalWindow w = U.evalWindow w + V.evalWindow w := by
  simp only [WindowSymbol.evalWindow, symAdd_coeff, add_mul, Finset.sum_add_distrib]

theorem evalWindow_symSmul {R K : ℕ} (c : ℂ) (U : WindowSymbol R K) (w : WindowSpace R) :
    (symSmul c U).evalWindow w = c * U.evalWindow w := by
  simp only [WindowSymbol.evalWindow, symSmul_coeff, mul_assoc, Finset.mul_sum]

theorem evalWindow_symConj {R K : ℕ} (U : WindowSymbol R K) (w : WindowSpace R) :
    (symConj U).evalWindow w = (starRingEnd ℂ) (U.evalWindow w) := by
  have key : ∀ G : ℤ → ℤ → ℂ,
      ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), G r s
        = ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), G (-r) (-s) := by
    intro G
    rw [← sum_Icc_neg (fun r => ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), G r s)]
    exact Finset.sum_congr rfl fun r _ => (sum_Icc_neg (fun s => G (-r) s)).symm
  have hstar : (starRingEnd ℂ) (U.evalWindow w)
      = ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (starRingEnd ℂ) (U.coeff (windowWordOf R w) r s) *
            torusChar (-((r : ℝ) * wTh w (-1) + (s : ℝ) * wTh w 0)) := by
    simp only [WindowSymbol.evalWindow, map_sum, map_mul, torusChar_conj]
  rw [hstar, key (fun r s => (starRingEnd ℂ) (U.coeff (windowWordOf R w) r s) *
      torusChar (-((r : ℝ) * wTh w (-1) + (s : ℝ) * wTh w 0)))]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [symConj_coeff]
  congr 2
  push_cast
  ring

/-- The real part of a symbol, obtained by adjoining the conjugate
monomials. -/
def symRe {R K : ℕ} (U : WindowSymbol R K) : WindowSymbol R K :=
  symSmul (1 / 2) (symAdd U (symConj U))

theorem evalWindow_symRe {R K : ℕ} (U : WindowSymbol R K) (w : WindowSpace R) :
    (symRe U).evalWindow w = ((U.evalWindow w).re : ℂ) := by
  rw [symRe, evalWindow_symSmul, evalWindow_symAdd, evalWindow_symConj,
    Complex.add_conj]
  push_cast
  ring

theorem evalWindow_symRe_im {R K : ℕ} (U : WindowSymbol R K) (w : WindowSpace R) :
    ((symRe U).evalWindow w).im = 0 := by
  rw [evalWindow_symRe]
  simp

/-- The pointwise inequality behind "because `B^{(R)} ∘ π` is real-valued,
`|B^{(R)} ∘ π - Re P| ≤ |B^{(R)} ∘ π - P|`". -/
theorem norm_sub_re_le (b : ℝ) (z : ℂ) :
    ‖(b : ℂ) - ((z.re : ℝ) : ℂ)‖ ≤ ‖(b : ℂ) - z‖ := by
  have h1 : ((b : ℂ) - ((z.re : ℝ) : ℂ)) = ((b - z.re : ℝ) : ℂ) := by push_cast; ring
  have h2 : b - z.re = ((b : ℂ) - z).re := by simp
  rw [h1, h2, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

/-! ## The four steps of the corrected display (55)

The chain of the revision note is `B^{(R)} → G → G_M → G_M 1_E → P_{R,M}`.
The objects it passes through are named here. -/

/-- The finite continued fraction `[0; a_0, …, a_{M-1}]`, the `M`-digit
truncation of a real coordinate. -/
def cfFinite (a : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | M + 1 => ((a 0 : ℝ) + cfFinite (fun k => a (k + 1)) M)⁻¹

/-- `cfFinite` is nonnegative for *every* digit family, including the
degenerate ones: each step is `(a + u)⁻¹` of a nonnegative quantity, and
Lean's `0⁻¹ = 0` keeps even the empty corner at `0`. -/
theorem cfFinite_nonneg : ∀ (M : ℕ) (a : ℕ → ℕ), 0 ≤ cfFinite a M
  | 0, _ => by simp [cfFinite]
  | M + 1, a => by
      have h := cfFinite_nonneg M (fun k => a (k + 1))
      simp only [cfFinite]
      exact inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg _) h)

/-- If the digits actually read are all `≥ 1` — which
`ae_orbitConsistent` guarantees almost surely, and which fails for an
arbitrary point of `WindowSpace R` (a digit `0` at the top makes
`cfFinite` an unbounded `u⁻¹`) — then `cfFinite a M ≤ 1`. -/
theorem cfFinite_le_one : ∀ (M : ℕ) (a : ℕ → ℕ),
    (∀ k, k < M → 1 ≤ a k) → cfFinite a M ≤ 1
  | 0, _, _ => by simp [cfFinite]
  | M + 1, a, ha => by
      have h0 : (1:ℝ) ≤ (a 0 : ℝ) := by exact_mod_cast ha 0 (Nat.succ_pos M)
      have hnn := cfFinite_nonneg M (fun k => a (k + 1))
      simp only [cfFinite]
      exact inv_le_one_of_one_le₀ (by linarith)

/-- `cfFinite` reads only the first `M` digits. -/
theorem cfFinite_congr : ∀ (M : ℕ) (a b : ℕ → ℕ), (∀ k, k < M → a k = b k) →
    cfFinite a M = cfFinite b M
  | 0, _, _, _ => rfl
  | M + 1, a, b, h => by
      simp only [cfFinite]
      rw [h 0 (Nat.succ_pos M),
        cfFinite_congr M (fun k => a (k + 1)) (fun k => b (k + 1))
          (fun k hk => h (k + 1) (by omega))]

/-- Shifting the digit family by one step is reading the digits of the
Gauss image. -/
theorem digit_succ_eq (x : ℝ) (k : ℕ) : digit x (k + 1) = digit (gaussMap x) k := by
  unfold digit
  rw [gaussIter_shift]

/-- **The continued-fraction contraction, product form**: the `M`-digit
truncation of an irrational `x ∈ (0,1)` approximates `x` to within the
product of its first `M` Gauss iterates.  Each level is the `1`-Lipschitz
map `u ↦ 1/(a+u)` whose contraction factor at the two arguments is
`x_t · (a_t + v)⁻¹ ≤ x_t`; unwinding `M` levels telescopes the factors
into `x_0 x_1 ⋯ x_{M-1}`. -/
theorem abs_sub_cfFinite_le_consecProd (M : ℕ) :
    ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → Irrational x →
      |x - cfFinite (fun k => digit x k) M| ≤ consecProdD x 0 M := by
  induction M with
  | zero =>
      intro x hx _
      show |x - 0| ≤ consecProdD x 0 0
      rw [sub_zero, abs_of_pos hx.1, consecProdD_zeroD]
      exact hx.2.le
  | succ M ih =>
      intro x hx hirr
      have hxg : gaussMap x ∈ Ioo (0 : ℝ) 1 := gaussMap_mem_Ioo hirr
      have hirrg : Irrational (gaussMap x) := gaussMap_irrational hirr
      have ihg := ih hxg hirrg
      have ha1 : (1 : ℝ) ≤ (digit x 0 : ℝ) := by
        exact_mod_cast one_le_digit hx hirr 0
      have hv0 : 0 ≤ cfFinite (fun k => digit (gaussMap x) k) M := cfFinite_nonneg M _
      have hxu : x = ((digit x 0 : ℝ) + gaussMap x)⁻¹ := by
        rw [← inv_eq_digit_add_gaussMap hx, inv_inv]
      have hshift : cfFinite (fun k => digit x (k + 1)) M
          = cfFinite (fun k => digit (gaussMap x) k) M :=
        cfFinite_congr M _ _ (fun k _ => digit_succ_eq x k)
      have hcf : cfFinite (fun k => digit x k) (M + 1)
          = ((digit x 0 : ℝ) + cfFinite (fun k => digit (gaussMap x) k) M)⁻¹ := by
        simp only [cfFinite]
        rw [hshift]
      have hden1 : (0 : ℝ) < (digit x 0 : ℝ) + gaussMap x := by linarith [hxg.1]
      have hden2 : (0 : ℝ) < (digit x 0 : ℝ) + cfFinite (fun k => digit (gaussMap x) k) M := by
        linarith
      have habs : ((digit x 0 : ℝ) + gaussMap x)⁻¹
            - ((digit x 0 : ℝ) + cfFinite (fun k => digit (gaussMap x) k) M)⁻¹
          = (cfFinite (fun k => digit (gaussMap x) k) M - gaussMap x)
            * (((digit x 0 : ℝ) + gaussMap x)⁻¹
              * ((digit x 0 : ℝ) + cfFinite (fun k => digit (gaussMap x) k) M)⁻¹) := by
        field_simp
        ring
      rw [← hxu] at habs
      have hprod : consecProdD x 0 (M + 1) = consecProdD (gaussMap x) 0 M * x := by
        unfold consecProdD
        rw [Finset.prod_range_succ']
        congr 1
      have h1 : |cfFinite (fun k => digit (gaussMap x) k) M - gaussMap x|
          ≤ consecProdD (gaussMap x) 0 M := by
        rw [abs_sub_comm]
        exact ihg
      have h2 : |x * ((digit x 0 : ℝ) + cfFinite (fun k => digit (gaussMap x) k) M)⁻¹|
          ≤ x := by
        rw [abs_of_nonneg (mul_nonneg hx.1.le (inv_pos.mpr hden2).le)]
        calc x * ((digit x 0 : ℝ) + cfFinite (fun k => digit (gaussMap x) k) M)⁻¹
            ≤ x * 1 :=
              mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (by linarith)) hx.1.le
          _ = x := mul_one x
      calc |x - cfFinite (fun k => digit x k) (M + 1)|
          = |cfFinite (fun k => digit (gaussMap x) k) M - gaussMap x|
            * |x * ((digit x 0 : ℝ) + cfFinite (fun k => digit (gaussMap x) k) M)⁻¹| := by
            rw [hcf, habs, abs_mul]
        _ ≤ consecProdD (gaussMap x) 0 M * x :=
            mul_le_mul h1 h2 (abs_nonneg _) (consecProdD_nonnegD (gaussMap x) hxg hirrg 0 M)
        _ = consecProdD x 0 (M + 1) := hprod.symm

/-- **The continued-fraction contraction**: `|x - [0; a_1, …, a_M]| ≤ 1/F_{M+1}`. -/
theorem abs_sub_cfFinite_digit_le (M : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational x) :
    |x - cfFinite (fun k => digit x k) M| ≤ ((Nat.fib (M + 1) : ℝ))⁻¹ :=
  le_trans (abs_sub_cfFinite_le_consecProd M hx hirr)
    (consecProdD_le_inv_fibD x hx hirr 0 M)

/-- The reciprocal Fibonacci numbers go below any positive threshold. -/
theorem exists_fib_inv_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ((Nat.fib (M + 1) : ℝ))⁻¹ < δ := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 2 * δ / 3 by linarith)
    (show (2 : ℝ) / 3 < 1 by norm_num)
  refine ⟨N, lt_of_le_of_lt (inv_fib_le_geomD N) ?_⟩
  have h := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < 3 / 2 by norm_num)
  calc (3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ N < (3 / 2) * (2 * δ / 3) := h
    _ = δ := by ring

/-- The `M`-digit truncation `X_{R+M} → X_R`: keep the digit and torus
coordinates of the radius-`R` sub-window, and replace the real coordinate
at offset `t` by `[0; a_{j+t+1}, …, a_{j+t+M}]`, which is read off the
digits at offsets `t, …, t + M - 1` of the radius-`R+M` window.  This is
exactly why the approximant lives at radius `R + M`: the coordinate at
`t = R` needs digits through offset `R + M - 1`. -/
def digitTruncWindow (R M : ℕ) (w : WindowSpace (R + M)) : WindowSpace R :=
  (fun i => wA w ((i : ℤ) - (R : ℤ)),
   fun i => cfFinite (fun k => wA w ((i : ℤ) - (R : ℤ) + (k : ℤ))) M,
   fun i => wTh w ((i : ℤ) - (R : ℤ) - 1))

/-- **The dense algebra** of v5 lines 1318-1327: a finite sum
`Σ_ℓ D_ℓ(a) g_ℓ(x) exp(2πi Σ_{t=-R-1}^{R} c_{ℓ,t} θ_t)` with `D_ℓ` a
finite digit-cylinder function, `g_ℓ` continuous, and `c_ℓ` integral. -/
structure DenseElt (R : ℕ) where
  /-- The number of summands. -/
  len : ℕ
  /-- The digit-cylinder amplitudes. -/
  D : Fin len → (Fin (2 * R + 1) → ℕ) → ℂ
  /-- The finitely many words each amplitude is supported on. -/
  Dwords : Fin len → Finset (Fin (2 * R + 1) → ℕ)
  D_support : ∀ l w, w ∉ Dwords l → D l w = 0
  /-- The continuous factors on the real block. -/
  g : Fin len → (Fin (2 * R + 1) → ℝ) → ℂ
  g_continuous : ∀ l, Continuous (g l)
  /-- The torus characters, over the full v5 range `-R-1 ≤ t ≤ R`. -/
  c : Fin len → Fin (2 * R + 2) → ℤ

/-- The dense-algebra element as a function on `X_R`. -/
def DenseElt.eval {R : ℕ} (G : DenseElt R) (w : WindowSpace R) : ℂ :=
  ∑ l : Fin G.len, G.D l w.1 * G.g l w.2.1 *
    torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) * w.2.2 t)

/-- **`E_{M,K}`** of v5 lines 1345-1352: every digit in the word
`a_{j-R'+1}, …, a_{j+R'}` is at most `K`. -/
def digitCapEvent (R' K : ℕ) : Set (WindowSpace R') :=
  {w | ∀ i : Fin (2 * R'), w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1)) ≤ K}

theorem measurableSet_digitCapEvent (R' K : ℕ) : MeasurableSet (digitCapEvent R' K) := by
  have hrw : digitCapEvent R' K =
      ⋂ i : Fin (2 * R'), {w : WindowSpace R' | w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1)) ≤ K} := by
    ext w; simp [digitCapEvent]
  rw [hrw]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun w : WindowSpace R' => w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1))) :=
    (measurable_pi_apply (⟨i, by omega⟩ : Fin (2 * R' + 1))).comp measurable_fst
  have hpre : {w : WindowSpace R' | w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1)) ≤ K}
      = (fun w : WindowSpace R' => w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1))) ⁻¹' {n : ℕ | n ≤ K} := rfl
  rw [hpre]
  exact hm MeasurableSet.of_discrete

/-! ### `E_{M,K}` is closed but **not** compact

`Kwon1002/Lemma63.lean` lines 585-589 record, as the obstruction to the
Stone-Weierstrass step of Lemma 6.3, that "`WindowSpace R` is not compact
(the digit block is `ℕ`-valued), so the argument has to run on each compact
digit truncation".  The compact digit truncation the manuscript has in mind
is `X_{R,K}`, and `digitCapEvent` is *not* it.

Capping the digits is not enough.  In the reading fixed by
`Section6Skeleton` (reading 3) the real and torus blocks of `X_R` are
`[0,1]^{2R+1}` and `T^{2R+2}`, but the Lean type `WindowSpace R` carries
them as full copies of `ℝ`, with the interval and the torus reduction
imposed only where a statement needs them.  `digitCapEvent R' K`
constrains the digit block alone, so it contains a whole affine copy of
`ℝ^{2R'+1}` and is unbounded.  `not_isCompact_digitCapEvent` proves this,
and `digitCapCube` supplies the set that *is* compact: the digit cap times
the closed unit cube on the other two blocks. -/

/-- `E_{M,K}` is closed: `{n | n ≤ K}` is clopen in the discrete space `ℕ`
and each digit coordinate reader is continuous. -/
theorem isClosed_digitCapEvent (R' K : ℕ) : IsClosed (digitCapEvent R' K) := by
  have hrw : digitCapEvent R' K
      = ⋂ i : Fin (2 * R'), {w : WindowSpace R' | w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1)) ≤ K} := by
    ext w; simp [digitCapEvent]
  rw [hrw]
  refine isClosed_iInter fun i => ?_
  have hcont : Continuous fun w : WindowSpace R' => w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1)) :=
    (continuous_apply (⟨i, by omega⟩ : Fin (2 * R' + 1))).comp continuous_fst
  have hpre : {w : WindowSpace R' | w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1)) ≤ K}
      = (fun w : WindowSpace R' => w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1))) ⁻¹' {n : ℕ | n ≤ K} := rfl
  rw [hpre]
  exact IsClosed.preimage hcont (isClosed_discrete _)

/-- **`E_{M,K}` is not compact.**  The digit cap says nothing about the real
block, so the image of `digitCapEvent R' K` under the (continuous) reader of
the first real coordinate is all of `ℝ`, which is not bounded above.  Hence
`digitCapEvent` cannot serve as the compact exhaustion `X_{R,K}` asked for at
`Kwon1002/Lemma63.lean` lines 585-589; use `digitCapCube` for that. -/
theorem not_isCompact_digitCapEvent (R' K : ℕ) : ¬ IsCompact (digitCapEvent R' K) := by
  intro hK
  have hcont : Continuous fun w : WindowSpace R' => w.2.1 ⟨0, by omega⟩ :=
    (continuous_apply _).comp (continuous_fst.comp continuous_snd)
  obtain ⟨b, hb⟩ := (hK.image hcont).bddAbove
  have hmem : (b + 1) ∈ (fun w : WindowSpace R' => w.2.1 ⟨0, by omega⟩) '' digitCapEvent R' K := by
    refine ⟨(fun _ => 0, fun _ => b + 1, fun _ => 0), ?_, rfl⟩
    intro i; simp
  have := hb hmem
  linarith

/-- **The compact digit truncation `X_{R,K}`.**  The digit cap of
`digitCapEvent` together with the interval constraint that reading 3 of
`Section6Skeleton` places on the real and torus blocks of `X_R`.  This is
the set the Stone-Weierstrass step of Lemma 6.3 has to run on. -/
def digitCapCube (R' K : ℕ) : Set (WindowSpace R') :=
  {w : Fin (2 * R' + 1) → ℕ | ∀ i, w i ≤ K} ×ˢ
    ((Set.univ.pi fun _ : Fin (2 * R' + 1) => Icc (0 : ℝ) 1) ×ˢ
      (Set.univ.pi fun _ : Fin (2 * R' + 2) => Icc (0 : ℝ) 1))

theorem digitCapCube_subset (R' K : ℕ) : digitCapCube R' K ⊆ digitCapEvent R' K := by
  rintro w ⟨hw, -⟩
  exact fun i => hw (⟨i, by omega⟩ : Fin (2 * R' + 1))

/-- **`X_{R,K}` is compact**: a finite digit block times two closed cubes. -/
theorem isCompact_digitCapCube (R' K : ℕ) : IsCompact (digitCapCube R' K) := by
  refine IsCompact.prod ?_ (IsCompact.prod ?_ ?_)
  · refine Set.Finite.isCompact ?_
    have hrw : {w : Fin (2 * R' + 1) → ℕ | ∀ i, w i ≤ K}
        = Set.univ.pi fun _ : Fin (2 * R' + 1) => Set.Iic K := by
      ext w; simp [Pi.le_def]
    rw [hrw]
    exact Set.Finite.pi fun _ => Set.finite_Iic K
  · exact isCompact_univ_pi fun _ => isCompact_Icc
  · exact isCompact_univ_pi fun _ => isCompact_Icc

theorem measurableSet_digitCapCube (R' K : ℕ) : MeasurableSet (digitCapCube R' K) := by
  refine MeasurableSet.prod MeasurableSet.of_discrete
    (MeasurableSet.prod ?_ ?_) <;>
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- **`Bwindow` is Borel measurable.**  This is the measurable-regularity half
needed by the v9 bounded-representative density bridge. -/
theorem measurable_Bwindow (R : ℕ) : Measurable (Bwindow R) := by
  have hW : Measurable fun w : WindowSpace R => W (wTh w 0) :=
    measurable_W.comp (measurable_wTh R 0)
  have hA : Measurable fun w : WindowSpace R => ((windowCarry R w R : ℤ) : ℝ) :=
    (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp (measurable_windowCarry R R)
  have hcarryU : Measurable fun w : WindowSpace R =>
      carryU (wX w 0) (wTh w (-1)) (wTh w 0) (windowCarry R w R) := by
    have harg : Measurable fun w : WindowSpace R =>
        wTh w 0 - wX w 0 * (((windowCarry R w R : ℤ) : ℝ) + wTh w (-1)) :=
      (measurable_wTh R 0).sub
        ((measurable_wX R 0).mul (hA.add (measurable_wTh R (-1))))
    exact harg.fract
  have hPhi : Measurable fun w : WindowSpace R =>
      Phi (wX w 0) (carryU (wX w 0) (wTh w (-1)) (wTh w 0) (windowCarry R w R)) := by
    unfold Phi
    exact ((hcarryU.mul (measurable_const.sub hcarryU)).div (measurable_const.mul (measurable_wX R 0))).sub
      (hcarryU.div measurable_const)
  have hAreal : Measurable fun w : WindowSpace R => ((wA w 0 : ℕ) : ℝ) :=
    (measurable_from_top (f := fun m : ℕ => (m : ℝ))).comp (measurable_wA R 0)
  have hmark : Measurable fun w : WindowSpace R => ((wA w 0 : ℝ) * W (wTh w 0)) :=
    hAreal.mul hW
  simpa only [Bwindow] using hPhi.sub hmark

/-- `BwindowRep` is Borel measurable. -/
theorem measurable_BwindowRep (R : ℕ) : Measurable (BwindowRep R) := by
  unfold BwindowRep
  exact measurable_const.max (measurable_const.min (measurable_Bwindow R))

/-- `BwindowRep` has global bound `|BwindowRep R w| ≤ 45/8`. -/
theorem abs_BwindowRep_le (R : ℕ) (w : WindowSpace R) : |BwindowRep R w| ≤ 45 / 8 := by
  have hlow : -(45 / 8 : ℝ) ≤ BwindowRep R w := by
    simpa [BwindowRep] using le_max_left (-(45 / 8 : ℝ)) (min (45 / 8 : ℝ) (Bwindow R w))
  have hupp : BwindowRep R w ≤ 45 / 8 := by
    have hmin : min (45 / 8 : ℝ) (Bwindow R w) ≤ (45 / 8 : ℝ) := min_le_left _ _
    have hmax : max (-(45 / 8 : ℝ)) (min (45 / 8 : ℝ) (Bwindow R w)) ≤ 45 / 8 :=
      max_le (by norm_num) hmin
    simpa [BwindowRep] using hmax
  exact abs_le.mpr ⟨hlow, hupp⟩

/-- On actual windows, bounded representative agrees with the truncation:
    using `Bwindow_actualWindow` and `abs_BremainderTrunc_le`. -/
theorem BwindowRep_actualWindow (R : ℕ) (α : ℝ) (n j : ℕ) (hj : R + 1 ≤ j)
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    BwindowRep R (actualWindow R α n j) = BremainderTrunc α n R j := by
  rw [BwindowRep, Bwindow_actualWindow R α n j hj]
  have hbound := abs_BremainderTrunc_le hα hirr n R j
  have hlow : -(45 / 8 : ℝ) ≤ BremainderTrunc α n R j := (abs_le.mp hbound).1
  have hupp : BremainderTrunc α n R j ≤ 45 / 8 := (abs_le.mp hbound).2
  calc
    max (-(45 / 8 : ℝ)) (min (45 / 8 : ℝ) (BremainderTrunc α n R j))
        = max (-(45 / 8 : ℝ)) (BremainderTrunc α n R j) := by
          simp [min_eq_right hupp]
    _ = BremainderTrunc α n R j := by
          exact max_eq_right hlow

/-! ### The bounded representative on the stationary law -/

/-- The carry reconstructed from a stationary radius-`R` window is the
stationary carry started `R` steps in the past. -/
theorem windowCarry_stationaryWindow (R : ℕ) {z : NatExtTorus}
    (hz : z ∈ CarryGraph.GoodT) :
    windowCarry R (stationaryWindow R z) R =
      CarryGraph.iterCarry (hatSinv^[R] z) R := by
  have hstate : ∀ k ≤ R,
      hatS^[k] (hatSinv^[R] z) = hatSzpow (-(R : ℤ) + (k : ℤ)) z := by
    intro k hk
    rw [CarryGraph.hatS_iterate_hatSinv_iterate hz k R hk]
    by_cases hlt : k < R
    · rw [hatSzpow, if_neg (by omega)]
      congr 2
      omega
    · have hkr : k = R := by omega
      subst k
      simp [hatSzpow]
  have hcarry : ∀ k ≤ R,
      windowCarry R (stationaryWindow R z) k =
        CarryGraph.iterCarry (hatSinv^[R] z) k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        have hkR : k ≤ R := by omega
        simp only [windowCarry, CarryGraph.iterCarry]
        rw [ih hkR,
          wX_stationaryWindow R z (t := -(R : ℤ) + (k : ℤ)) (by omega) (by omega),
          wTh_stationaryWindow R z (t := -(R : ℤ) + (k : ℤ) - 1) (by omega) (by omega),
          wTh_stationaryWindow R z (t := -(R : ℤ) + (k : ℤ)) (by omega) (by omega),
          hstate k hkR]
        have htor := StationaryIdentity31.hatSzpow_fst_torus hz
          (-(R : ℤ) + (k : ℤ))
        rw [htor]
  exact hcarry R le_rfl

/-- On every stationary window over the full good set, the raw window
formula already lies in the manuscript interval `[-45/8,45/8]`. -/
theorem abs_Bwindow_stationaryWindow_le (R : ℕ) {z : NatExtTorus}
    (hz : z ∈ CarryGraph.GoodT) :
    |Bwindow R (stationaryWindow R z)| ≤ 45 / 8 := by
  let q : NatExtTorus := hatSinv^[R] z
  let d : ℤ := windowCarry R (stationaryWindow R z) R
  have hq : q ∈ CarryGraph.GoodT := CarryGraph.hatSinv_iterate_mem_goodT hz R
  have hdBounds := CarryGraph.iterCarry_bounds hq R
  have hdEq : d = CarryGraph.iterCarry q R := by
    simpa [q, d] using windowCarry_stationaryWindow R hz
  have hd0 : 0 ≤ d := by rw [hdEq]; exact hdBounds.1
  have hd9 : d ≤ 9 := by rw [hdEq]; exact hdBounds.2
  have hx : z.1.1 ∈ Ioo (0 : ℝ) 1 := hz.1.1
  have hx' : gaussMap z.1.1 ∈ Ioo (0 : ℝ) 1 := by
    exact (CarryGraph.hatS_mem_goodT hz).1.1
  have hr : (hatSinv z).2.2 ∈ Ico (0 : ℝ) 1 :=
    (CarryGraph.hatSinv_mem_goodT hz).2.2
  have hd0' : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  have hd9' : (d : ℝ) ≤ 9 := by exact_mod_cast hd9
  have hE0 : 0 ≤ (d : ℝ) + (hatSinv z).2.2 := by linarith [hr.1]
  have hE10 : (d : ℝ) + (hatSinv z).2.2 ≤ 10 := by linarith [hr.2]
  let u := carryU z.1.1 (hatSinv z).2.2 z.2.2 d
  have hu0 : 0 ≤ u := by
    simp only [u, carryU]
    exact Int.fract_nonneg _
  have hu1 : u < 1 := by
    simp only [u, carryU]
    exact Int.fract_lt_one _
  have hdW : |W u - W z.2.2| ≤
      z.1.1 * ((d : ℝ) + (hatSinv z).2.2) / 2 := by
    simp only [u, carryU]
    rw [W_fract,
      show z.2.2 - z.1.1 * ((d : ℝ) + (hatSinv z).2.2)
          = z.2.2 + -(z.1.1 * ((d : ℝ) + (hatSinv z).2.2)) by ring]
    have h := W_sub_le z.2.2 (-(z.1.1 * ((d : ℝ) + (hatSinv z).2.2)))
    rwa [abs_neg, abs_of_nonneg (mul_nonneg hx.1.le hE0)] at h
  have hmain := principal_bound z.1.1 (gaussMap z.1.1) u z.2.2
    (digit z.1.1 0 : ℝ) ((d : ℝ) + (hatSinv z).2.2) 10
    hx.1 hx'.1 hx'.2 hu0 hu1 (Nat.cast_nonneg _)
    (inv_eq_digit_add_gaussMap hx) hE0 hE10 (W_eq_of_mem hu0 hu1) hdW
  have hB : Bwindow R (stationaryWindow R z)
      = Phi z.1.1 u - (digit z.1.1 0 : ℝ) * W z.2.2 := by
    simp only [Bwindow]
    rw [wX_stationaryWindow R z (t := 0) (by omega) (by omega),
      wTh_stationaryWindow R z (t := -1) (by omega) (by omega),
      wTh_stationaryWindow R z (t := 0) (by omega) (by omega),
      wA_stationaryWindow R z (t := 0) (by omega) (by omega)]
    rw [show hatSzpow 0 z = z by simp [hatSzpow],
      show hatSzpow (-1) z = hatSinv z by simp [hatSzpow],
      windowCarry_stationaryWindow R hz]
    simp only [u, d]
    rw [windowCarry_stationaryWindow R hz]
  rw [hB]
  calc
    |Phi z.1.1 u - (digit z.1.1 0 : ℝ) * W z.2.2| ≤ 10 / 2 + 5 / 8 := hmain
    _ = 45 / 8 := by norm_num

/-- The raw window formula satisfies the same `45/8` bound almost everywhere
under the stationary window law. -/
theorem ae_abs_Bwindow_le (R : ℕ) :
    ∀ᵐ w ∂(windowLaw R), |Bwindow R w| ≤ 45 / 8 := by
  have hs : MeasurableSet {w : WindowSpace R | |Bwindow R w| ≤ 45 / 8} :=
    measurableSet_le (measurable_Bwindow R).abs measurable_const
  rw [windowLaw, ae_map_iff (measurable_stationaryWindow R).aemeasurable hs]
  filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz
  exact abs_Bwindow_stationaryWindow_le R hz

/-- The clamp defining `BwindowRep` is inactive `windowLaw`-almost
everywhere.  This is the stationary-law bridge required before attacking
display (55). -/
theorem ae_BwindowRep_eq_Bwindow (R : ℕ) :
    BwindowRep R =ᵐ[windowLaw R] Bwindow R := by
  filter_upwards [ae_abs_Bwindow_le R] with w hw
  have hb := abs_le.mp hw
  rw [BwindowRep, min_eq_right hb.2, max_eq_right hb.1]

/-- Clamping preserves continuity at every continuity point of the raw
window formula. -/
theorem continuousAt_BwindowRep {R : ℕ} {w : WindowSpace R}
    (h : ContinuousAt (Bwindow R) w) : ContinuousAt (BwindowRep R) w := by
  unfold BwindowRep
  exact continuousAt_const.max (continuousAt_const.min h)

variable {R : ℕ}

/-- The corrected window topology: torus coordinates live in the quotient `ℝ / ℤ`. -/
abbrev QWindow (R : ℕ) :=
  (Fin (2 * R + 1) → ℕ) ×
    (Fin (2 * R + 1) → ℝ) × UnitAddTorus (Fin (2 * R + 2))

/-- Evaluation of the existing algebraic data on the corrected quotient window. -/
def DenseElt.qeval (G : DenseElt R) (w : QWindow R) : ℂ :=
  ∑ l : Fin G.len, G.D l w.1 * G.g l w.2.1 * UnitAddTorus.mFourier (G.c l) w.2.2

private def DenseElt.zero (R : ℕ) : DenseElt R where
  len := 0
  D := Fin.elim0
  Dwords := Fin.elim0
  D_support := by intro l; exact Fin.elim0 l
  g := Fin.elim0
  g_continuous := by intro l; exact Fin.elim0 l
  c := Fin.elim0

private def DenseElt.add (G H : DenseElt R) : DenseElt R where
  len := G.len + H.len
  D := Fin.addCases G.D H.D
  Dwords := Fin.addCases G.Dwords H.Dwords
  D_support := by
    intro l
    induction l using Fin.addCases with
    | left l => simpa using G.D_support l
    | right l => simpa using H.D_support l
  g := Fin.addCases G.g H.g
  g_continuous := by
    intro l
    induction l using Fin.addCases with
    | left l => simpa using G.g_continuous l
    | right l => simpa using H.g_continuous l
  c := Fin.addCases G.c H.c

private def DenseElt.mul (G H : DenseElt R) : DenseElt R where
  len := G.len * H.len
  D l w := G.D (finProdFinEquiv.symm l).1 w * H.D (finProdFinEquiv.symm l).2 w
  Dwords l := G.Dwords (finProdFinEquiv.symm l).1 ∩ H.Dwords (finProdFinEquiv.symm l).2
  D_support := by
    intro l w hw
    simp only [Finset.mem_inter, not_and_or] at hw
    rcases hw with hw | hw
    · rw [G.D_support _ _ hw, zero_mul]
    · rw [H.D_support _ _ hw, mul_zero]
  g l x := G.g (finProdFinEquiv.symm l).1 x * H.g (finProdFinEquiv.symm l).2 x
  g_continuous l :=
    (G.g_continuous (finProdFinEquiv.symm l).1).mul
      (H.g_continuous (finProdFinEquiv.symm l).2)
  c l t := G.c (finProdFinEquiv.symm l).1 t + H.c (finProdFinEquiv.symm l).2 t

private def DenseElt.star (G : DenseElt R) : DenseElt R where
  len := G.len
  D l w := (starRingEnd ℂ) (G.D l w)
  Dwords := G.Dwords
  D_support := by intro l w hw; simp [G.D_support l w hw]
  g l x := (starRingEnd ℂ) (G.g l x)
  g_continuous l := continuous_star.comp (G.g_continuous l)
  c l t := -G.c l t

private theorem qeval_zero (w : QWindow R) : (DenseElt.zero R).qeval w = 0 := by
  simp [DenseElt.qeval, DenseElt.zero]

private theorem qeval_add (G H : DenseElt R) (w : QWindow R) :
    (G.add H).qeval w = G.qeval w + H.qeval w := by
  simp [DenseElt.qeval, DenseElt.add, Fin.sum_univ_add]

private theorem qeval_mul (G H : DenseElt R) (w : QWindow R) :
    (G.mul H).qeval w = G.qeval w * H.qeval w := by
  simp only [DenseElt.qeval, DenseElt.mul]
  have hmf (l : Fin (G.len * H.len)) :
      UnitAddTorus.mFourier
          (fun t => G.c (finProdFinEquiv.symm l).1 t + H.c (finProdFinEquiv.symm l).2 t)
          w.2.2 =
        UnitAddTorus.mFourier (G.c (finProdFinEquiv.symm l).1) w.2.2 *
          UnitAddTorus.mFourier (H.c (finProdFinEquiv.symm l).2) w.2.2 := by
    exact UnitAddTorus.mFourier_add
  simp_rw [hmf]
  rw [(finProdFinEquiv.symm.sum_comp (fun p : Fin G.len × Fin H.len =>
    G.D p.1 w.1 * H.D p.2 w.1 * (G.g p.1 w.2.1 * H.g p.2 w.2.1) *
      (UnitAddTorus.mFourier (G.c p.1) w.2.2 *
        UnitAddTorus.mFourier (H.c p.2) w.2.2)))]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
  simp [mul_assoc, mul_left_comm, mul_comm]

private theorem qeval_star (G : DenseElt R) (w : QWindow R) :
    G.star.qeval w = (starRingEnd ℂ) (G.qeval w) := by
  simp only [DenseElt.qeval, DenseElt.star]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul, map_mul]
  rw [show (fun t => -G.c l t) = -G.c l by rfl, UnitAddTorus.mFourier_neg]

private theorem continuous_qeval (G : DenseElt R) : Continuous G.qeval := by
  unfold DenseElt.qeval
  refine continuous_finset_sum _ fun l _ =>
    ((continuous_of_discreteTopology.comp continuous_fst).mul
      ((G.g_continuous l).comp (continuous_fst.comp continuous_snd))).mul ?_
  exact (UnitAddTorus.mFourier (G.c l)).continuous.comp
    (continuous_snd.comp continuous_snd)

def digitWords (K : Set (QWindow R)) (hK : IsCompact K) :
    Finset (Fin (2 * R + 1) → ℕ) :=
  ((hK.image continuous_fst).finite_of_discrete).toFinset

private theorem fst_mem_digitWords {K : Set (QWindow R)} (hK : IsCompact K)
    {w : QWindow R} (hw : w ∈ K) : w.1 ∈ digitWords K hK := by
  rw [digitWords, Set.Finite.mem_toFinset]
  exact mem_image_of_mem Prod.fst hw

private def DenseElt.ofContinuousOnK (K : Set (QWindow R)) (hK : IsCompact K)
    (g : (Fin (2 * R + 1) → ℝ) → ℂ) (hg : Continuous g) : DenseElt R where
  len := 1
  D _ w := if w ∈ digitWords K hK then 1 else 0
  Dwords _ := digitWords K hK
  D_support := by simp
  g _ := g
  g_continuous _ := hg
  c _ _ := 0

private theorem qeval_ofContinuousOnK (K : Set (QWindow R)) (hK : IsCompact K)
    (g : (Fin (2 * R + 1) → ℝ) → ℂ) (hg : Continuous g)
    {w : QWindow R} (hw : w ∈ K) :
    (DenseElt.ofContinuousOnK K hK g hg).qeval w = g w.2.1 := by
  simp only [DenseElt.qeval, DenseElt.ofContinuousOnK, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, fst_mem_digitWords hK hw, if_pos,
    one_mul]
  rw [show (fun _ : Fin (2 * R + 2) => (0 : ℤ)) = 0 by rfl,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one]

private def DenseElt.monomialOnK (K : Set (QWindow R)) (hK : IsCompact K)
    (g : (Fin (2 * R + 1) → ℝ) → ℂ) (hg : Continuous g)
    (c : Fin (2 * R + 2) → ℤ) : DenseElt R where
  len := 1
  D _ w := if w ∈ digitWords K hK then 1 else 0
  Dwords _ := digitWords K hK
  D_support := by simp
  g _ := g
  g_continuous _ := hg
  c _ := c

private theorem qeval_monomialOnK (K : Set (QWindow R)) (hK : IsCompact K)
    (g : (Fin (2 * R + 1) → ℝ) → ℂ) (hg : Continuous g)
    (c : Fin (2 * R + 2) → ℤ) {w : QWindow R} (hw : w ∈ K) :
    (DenseElt.monomialOnK K hK g hg c).qeval w =
      g w.2.1 * UnitAddTorus.mFourier c w.2.2 := by
  simp [DenseElt.qeval, DenseElt.monomialOnK, fst_mem_digitWords hK hw]

private def DenseElt.digitIndicator (a : Fin (2 * R + 1) → ℕ) : DenseElt R where
  len := 1
  D _ w := if w = a then 1 else 0
  Dwords _ := {a}
  D_support := by simp_all
  g _ _ := 1
  g_continuous _ := continuous_const
  c _ _ := 0

private theorem qeval_digitIndicator (a : Fin (2 * R + 1) → ℕ) (w : QWindow R) :
    (DenseElt.digitIndicator a).qeval w = if w.1 = a then 1 else 0 := by
  simp only [DenseElt.qeval, DenseElt.digitIndicator, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, mul_one]
  rw [show (fun _ : Fin (2 * R + 2) => (0 : ℤ)) = 0 by rfl,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one]

private def restrictQEval {K : Set (QWindow R)} (G : DenseElt R) : C(K, ℂ) :=
  ⟨fun w => G.qeval w.1, (continuous_qeval G).comp continuous_subtype_val⟩

/-- Every digit amplitude vanishes away from the finite digit projection of `K`. -/
def SupportedOnDigitWords (K : Set (QWindow R)) (hK : IsCompact K) (G : DenseElt R) : Prop :=
  ∀ l w, w ∉ digitWords K hK → G.D l w = 0

/-- Restrictions of `DenseElt.qeval` form a unital star subalgebra on every compact `K`.
The compactness is used exactly to make the digit cutoff finite. -/
def denseEltStarSubalgebra (K : Set (QWindow R)) (hK : IsCompact K) :
    StarSubalgebra ℂ C(K, ℂ) where
  carrier := {f | ∃ G : DenseElt R, restrictQEval G = f ∧ SupportedOnDigitWords K hK G}
  zero_mem' := ⟨DenseElt.zero R, by ext w; exact qeval_zero w.1,
    by intro l; exact Fin.elim0 l⟩
  one_mem' := by
    refine ⟨DenseElt.ofContinuousOnK K hK (fun _ => 1) continuous_const, ?_, ?_⟩
    · ext w
      exact qeval_ofContinuousOnK K hK _ continuous_const w.2
    · intro l w hw
      simp [DenseElt.ofContinuousOnK, hw]
  add_mem' := by
    rintro f g ⟨G, rfl, hG⟩ ⟨H, rfl, hH⟩
    refine ⟨G.add H, ?_, ?_⟩
    · ext w
      exact qeval_add G H w.1
    · intro l
      induction l using Fin.addCases with
      | left l => simpa [DenseElt.add] using hG l
      | right l => simpa [DenseElt.add] using hH l
  mul_mem' := by
    rintro f g ⟨G, rfl, hG⟩ ⟨H, rfl, hH⟩
    refine ⟨G.mul H, ?_, ?_⟩
    · ext w
      exact qeval_mul G H w.1
    · intro l w hw
      simp [DenseElt.mul, hG _ _ hw]
  algebraMap_mem' := by
    intro z
    refine ⟨DenseElt.ofContinuousOnK K hK (fun _ => z) continuous_const, ?_, ?_⟩
    · ext w
      simpa using qeval_ofContinuousOnK K hK (fun _ => z) continuous_const w.2
    · intro l w hw
      simp [DenseElt.ofContinuousOnK, hw]
  star_mem' := by
    rintro f ⟨G, rfl, hG⟩
    refine ⟨G.star, ?_, ?_⟩
    · ext w
      exact qeval_star G w.1
    · intro l w hw
      simp [DenseElt.star, hG l w hw]

private theorem denseEltStarSubalgebra_separatesPoints (K : Set (QWindow R))
    (hK : IsCompact K) : (denseEltStarSubalgebra K hK).SeparatesPoints := by
  classical
  intro x y hxy
  by_cases hd : x.1.1 = y.1.1
  · by_cases hr : x.1.2.1 = y.1.2.1
    · have ht : x.1.2.2 ≠ y.1.2.2 := by
        intro he
        apply hxy
        exact Subtype.ext <| Prod.ext hd (Prod.ext hr he)
      rw [Ne, funext_iff, not_forall] at ht
      obtain ⟨i, hi⟩ := ht
      let G := DenseElt.monomialOnK K hK (fun _ => 1) continuous_const (Pi.single i 1)
      refine ⟨_, ⟨restrictQEval G, ⟨G, rfl, ?_⟩, rfl⟩, ?_⟩
      · intro l w hw
        simp [G, DenseElt.monomialOnK, hw]
      have hc : fourier 1 (x.1.2.2 i) ≠ fourier 1 (y.1.2.2 i) := by
        rw [fourier_one, fourier_one, Ne, Subtype.coe_inj]
        contrapose! hi
        exact AddCircle.injective_toCircle one_ne_zero hi
      simpa [restrictQEval, G, qeval_monomialOnK K hK,
        UnitAddTorus.mFourier_single] using hc
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hr
      let G := DenseElt.ofContinuousOnK K hK (fun z => (z i : ℂ)) (by fun_prop)
      refine ⟨_, ⟨restrictQEval G, ⟨G, rfl, ?_⟩, rfl⟩, ?_⟩
      · intro l w hw
        simp [G, DenseElt.ofContinuousOnK, hw]
      simpa [restrictQEval, G, qeval_ofContinuousOnK K hK] using hi
  · let G := DenseElt.digitIndicator x.1.1
    refine ⟨_, ⟨restrictQEval G, ⟨G, rfl, ?_⟩, rfl⟩, ?_⟩
    · intro l w hw
      have hne : w ≠ x.1.1 := by
        intro he
        apply hw
        simpa [he] using fst_mem_digitWords hK x.2
      simp [G, DenseElt.digitIndicator, hne]
    simp [restrictQEval, G, qeval_digitIndicator, Ne.symm hd]

/-- Uniform Stone--Weierstrass approximation on a compact subset of the corrected window. -/
theorem exists_denseElt_uniformly_approximates (K : Set (QWindow R)) (hK : IsCompact K)
    (f : C(K, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : DenseElt R, SupportedOnDigitWords K hK G ∧
      ∀ w : K, ‖restrictQEval G w - f w‖ < ε := by
  let A := denseEltStarSubalgebra K hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hclosure : A.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A
      (denseEltStarSubalgebra_separatesPoints K hK)
  have hf : f ∈ closure (A : Set C(K, ℂ)) := by
    change f ∈ A.topologicalClosure
    rw [hclosure]
    trivial
  obtain ⟨g, hgA, hdist⟩ := (Metric.mem_closure_iff.mp hf) ε hε
  obtain ⟨G, rfl, hG⟩ := hgA
  have hnorm : ‖f - restrictQEval G‖ < ε := by
    simpa [dist_eq_norm] using hdist
  refine ⟨G, hG, fun w => ?_⟩
  have hle := (f - restrictQEval G).norm_coe_le_norm w
  rw [ContinuousMap.sub_apply, norm_sub_rev] at hle
  exact hle.trans_lt hnorm

/-! ## Quotienting the stationary window law -/

def quotientWindow (R : ℕ) (w : WindowSpace R) : QWindow R :=
  (w.1, w.2.1, fun i ↦ (w.2.2 i : UnitAddCircle))

def liftQWindow (R : ℕ) (q : QWindow R) : WindowSpace R :=
  (q.1, q.2.1, fun i ↦ ((AddCircle.measurableEquivIco 1 0) (q.2.2 i)).1)

lemma measurable_quotientWindow (R : ℕ) : Measurable (quotientWindow R) := by
  unfold quotientWindow
  refine Measurable.prodMk measurable_fst (Measurable.prodMk
    (measurable_fst.comp measurable_snd) ?_)
  exact measurable_pi_lambda _ fun i ↦
    AddCircle.measurable_mk'.comp
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))

lemma measurable_liftQWindow (R : ℕ) : Measurable (liftQWindow R) := by
  unfold liftQWindow
  refine Measurable.prodMk measurable_fst (Measurable.prodMk
    (measurable_fst.comp measurable_snd) ?_)
  exact measurable_pi_lambda _ fun i ↦
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable).comp
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))

lemma denseElt_qeval_quotientWindow (G : DenseElt R) (w : WindowSpace R) :
    G.qeval (quotientWindow R w) = G.eval w := by
  unfold DenseElt.qeval DenseElt.eval quotientWindow
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk]
  have hsum (t : Fin (2 * R + 2) → ℝ) :
      torusChar (∑ i, t i) = ∏ i, torusChar (t i) := by
    unfold torusChar
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  rw [hsum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [fourier_coe_apply, torusChar]
  congr 1
  push_cast
  ring

def WindowSupport (R : ℕ) : Set (WindowSpace R) :=
  {w | (∀ i, w.2.1 i ∈ Ioo (0 : ℝ) 1) ∧
    (∀ i, w.2.2 i ∈ Ico (0 : ℝ) 1)}

private theorem hatSzpow_mem_goodT {z : NatExtTorus}
    (hz : z ∈ CarryGraph.GoodT) (t : ℤ) : hatSzpow t z ∈ CarryGraph.GoodT := by
  by_cases ht : (0 : ℤ) ≤ t
  · rw [hatSzpow, if_pos ht]
    exact CarryGraph.hatS_iterate_mem_goodT hz _
  · rw [hatSzpow, if_neg ht]
    exact CarryGraph.hatSinv_iterate_mem_goodT hz _

private theorem stationaryWindow_mem_windowSupport (R : ℕ) {z : NatExtTorus}
    (hz : z ∈ CarryGraph.GoodT) : stationaryWindow R z ∈ WindowSupport R := by
  constructor
  · intro i
    let t : ℤ := (i : ℤ) - (R : ℤ)
    change (hatSzpow t z).1.1 ∈ Ioo (0 : ℝ) 1
    exact (hatSzpow_mem_goodT hz t).1.1
  · intro i
    let t : ℤ := (i : ℤ) - (R : ℤ) - 1
    change (hatSzpow t z).2.2 ∈ Ico (0 : ℝ) 1
    exact (hatSzpow_mem_goodT hz t).2.2

lemma measurableSet_windowSupport (R : ℕ) : MeasurableSet (WindowSupport R) := by
  have hset : WindowSupport R =
      (⋂ i, {w : WindowSpace R | w.2.1 i ∈ Ioo (0 : ℝ) 1}) ∩
      (⋂ i, {w : WindowSpace R | w.2.2 i ∈ Ico (0 : ℝ) 1}) := by
    ext w; simp [WindowSupport]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i ↦ ?_)
    (MeasurableSet.iInter fun i ↦ ?_)
  · exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurableSet_Ioo
  · exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) measurableSet_Ico

lemma windowLaw_ae_mem_windowSupport (R : ℕ) :
    ∀ᵐ w ∂(windowLaw R), w ∈ WindowSupport R := by
  rw [windowLaw]
  apply (ae_map_iff (measurable_stationaryWindow R).aemeasurable
    (measurableSet_windowSupport R)).2
  filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz
  exact stationaryWindow_mem_windowSupport R hz

lemma liftQWindow_quotientWindow_of_mem_support {w : WindowSpace R}
    (hw : w ∈ WindowSupport R) : liftQWindow R (quotientWindow R w) = w := by
  ext i <;> simp only [liftQWindow, quotientWindow]
  change ((AddCircle.equivIco 1 0) (w.2.2 i : UnitAddCircle)).1 = w.2.2 i
  rw [AddCircle.equivIco_coe_eq (by simpa using hw.2 i)]

lemma ae_liftQWindow_quotientWindow (R : ℕ) :
    ∀ᵐ w ∂(windowLaw R), liftQWindow R (quotientWindow R w) = w := by
  filter_upwards [windowLaw_ae_mem_windowSupport R] with w hw
  exact liftQWindow_quotientWindow_of_mem_support hw

def qWindowLaw (R : ℕ) : Measure (QWindow R) :=
  (windowLaw R).map (quotientWindow R)

def qBwindowRep (R : ℕ) (q : QWindow R) : ℂ :=
  (BwindowRep R (liftQWindow R q) : ℂ)

lemma measurable_qBwindowRep (R : ℕ) : Measurable (qBwindowRep R) :=
  Complex.measurable_ofReal.comp ((measurable_BwindowRep R).comp (measurable_liftQWindow R))

lemma ae_qBwindowRep_quotientWindow (R : ℕ) :
    (fun w : WindowSpace R ↦ (BwindowRep R w : ℂ)) =ᵐ[windowLaw R]
      fun w ↦ qBwindowRep R (quotientWindow R w) := by
  filter_upwards [ae_liftQWindow_quotientWindow R] with w hw
  simp [qBwindowRep, hw]

local instance qWindowLaw_isProbabilityMeasure (R : ℕ) :
    IsProbabilityMeasure (qWindowLaw R) := by
  constructor
  rw [qWindowLaw, Measure.map_apply_of_aemeasurable
    (measurable_quotientWindow R).aemeasurable MeasurableSet.univ]
  simp

lemma memLp_qBwindowRep (R : ℕ) : MemLp (qBwindowRep R) 2 (qWindowLaw R) := by
  have hm : AEStronglyMeasurable (qBwindowRep R) (qWindowLaw R) :=
    (measurable_qBwindowRep R).aestronglyMeasurable
  have hb : ∀ᵐ q ∂(qWindowLaw R), ‖qBwindowRep R q‖ ≤ (45 / 8 : ℝ) := by
    filter_upwards [] with q
    simpa [qBwindowRep, Complex.norm_real] using abs_BwindowRep_le R (liftQWindow R q)
  exact (memLp_top_of_bound hm (45 / 8) hb).mono_exponent (by norm_num)

def fullDigitCapQ (R K : ℕ) : Set (QWindow R) := {q | ∀ i, q.1 i ≤ K}

lemma measurableSet_fullDigitCapQ (R K : ℕ) : MeasurableSet (fullDigitCapQ R K) := by
  have hset : fullDigitCapQ R K = ⋂ i, {q : QWindow R | q.1 i ≤ K} := by
    ext q; simp [fullDigitCapQ]
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  change MeasurableSet ((fun q : QWindow R ↦ q.1 i) ⁻¹' {n : ℕ | n ≤ K})
  exact ((measurable_pi_apply i).comp measurable_fst) MeasurableSet.of_discrete

lemma qWindowLaw_fullDigitCapQ_compl_le (R K : ℕ) :
    qWindowLaw R (fullDigitCapQ R K)ᶜ ≤
      ENNReal.ofReal (((2 * R + 1 : ℕ) : ℝ) * (2 / ((K : ℝ) + 1))) := by
  have hpre : quotientWindow R ⁻¹' (fullDigitCapQ R K)ᶜ =
      ⋃ i : Fin (2 * R + 1), {w : WindowSpace R | K + 1 ≤ w.1 i} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_compl_iff, fullDigitCapQ, Set.mem_setOf_eq,
      not_forall, not_le, Set.mem_iUnion, quotientWindow]
    exact exists_congr fun i ↦ Nat.lt_iff_add_one_le
  rw [qWindowLaw, Measure.map_apply (measurable_quotientWindow R)
    (measurableSet_fullDigitCapQ R K).compl, hpre]
  refine le_trans (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine le_trans (Finset.sum_le_sum (fun i _ ↦ windowLaw_digitCoord_tail R i K)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

def fullDigitCubeQ (R K : ℕ) : Set (QWindow R) :=
  {a : Fin (2 * R + 1) → ℕ | ∀ i, a i ≤ K} ×ˢ
    ((Set.univ.pi fun _ : Fin (2 * R + 1) ↦ Icc (0 : ℝ) 1) ×ˢ
      (Set.univ : Set (UnitAddTorus (Fin (2 * R + 2)))))

lemma isCompact_fullDigitCubeQ (R K : ℕ) : IsCompact (fullDigitCubeQ R K) := by
  refine IsCompact.prod ?_ (IsCompact.prod ?_ isCompact_univ)
  · refine Set.Finite.isCompact ?_
    have hrw : {a : Fin (2 * R + 1) → ℕ | ∀ i, a i ≤ K} =
        Set.univ.pi fun _ : Fin (2 * R + 1) ↦ Set.Iic K := by
      ext a; simp [Pi.le_def]
    rw [hrw]
    exact Set.Finite.pi fun _ ↦ Set.finite_Iic K
  · exact isCompact_univ_pi fun _ ↦ isCompact_Icc

lemma quotientWindow_mem_fullDigitCubeQ {K : ℕ} {w : WindowSpace R}
    (hcap : ∀ i, w.1 i ≤ K) (hsupp : w ∈ WindowSupport R) :
    quotientWindow R w ∈ fullDigitCubeQ R K := by
  refine ⟨hcap, ?_, Set.mem_univ _⟩
  intro i _
  exact Ioo_subset_Icc_self (hsupp.1 i)

def qRealSupport (R : ℕ) : Set (QWindow R) :=
  {q | ∀ i, q.2.1 i ∈ Icc (0 : ℝ) 1}

lemma measurableSet_qRealSupport (R : ℕ) : MeasurableSet (qRealSupport R) := by
  have hset : qRealSupport R =
      ⋂ i, {q : QWindow R | q.2.1 i ∈ Icc (0 : ℝ) 1} := by
    ext q; simp [qRealSupport]
  rw [hset]
  exact MeasurableSet.iInter fun i ↦
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurableSet_Icc

lemma qWindowLaw_ae_mem_qRealSupport (R : ℕ) :
    ∀ᵐ q ∂(qWindowLaw R), q ∈ qRealSupport R := by
  rw [qWindowLaw]
  apply (ae_map_iff (measurable_quotientWindow R).aemeasurable
    (measurableSet_qRealSupport R)).2
  filter_upwards [windowLaw_ae_mem_windowSupport R] with w hw
  exact fun i ↦ Ioo_subset_Icc_self (hw.1 i)

lemma digitWords_fullDigitCubeQ_subset (K : ℕ) {a : Fin (2 * R + 1) → ℕ}
    (ha : a ∈ digitWords (fullDigitCubeQ R K) (isCompact_fullDigitCubeQ R K)) :
    ∀ i, a i ≤ K := by
  rw [digitWords, Set.Finite.mem_toFinset] at ha
  obtain ⟨q, hqK, hqa⟩ := ha
  simpa [fullDigitCubeQ, hqa] using hqK.1

lemma qeval_eq_zero_outside_fullDigitCapQ (K : ℕ) {G : DenseElt R}
    (hG : SupportedOnDigitWords (fullDigitCubeQ R K) (isCompact_fullDigitCubeQ R K) G)
    {q : QWindow R} (hq : q ∉ fullDigitCapQ R K) : G.qeval q = 0 := by
  unfold DenseElt.qeval
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rw [hG l q.1]
  · simp
  · intro hword
    apply hq
    exact digitWords_fullDigitCubeQ_subset K hword

theorem qDenseElt_density (R : ℕ) (f : QWindow R → ℂ)
    (hf : MemLp f 2 (qWindowLaw R)) (e : ℝ) (he : 0 < e) :
    ∃ G : DenseElt R, eLpNorm (f - G.qeval) 2 (qWindowLaw R) < ENNReal.ofReal e := by
  letI : Measure.Regular (qWindowLaw R) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (qWindowLaw R)
  obtain ⟨h, hfh, -⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num) (show ENNReal.ofReal (e / 4) ≠ 0 by positivity)
  let C : ℝ := ‖h‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := e / 4 / C
  have hη : 0 < η := by dsimp [η]; positivity
  have hη2 : 0 < η ^ 2 := by positivity
  obtain ⟨K, hKgt⟩ := exists_nat_gt
    (((2 * R + 1 : ℕ) : ℝ) * 2 / η ^ 2)
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hKbound : ((2 * R + 1 : ℕ) : ℝ) * (2 / ((K : ℝ) + 1)) < η ^ 2 := by
    rw [div_lt_iff₀ hη2] at hKgt
    rw [← mul_div_assoc, div_lt_iff₀ hK1]
    nlinarith
  let QK : Set (QWindow R) := fullDigitCubeQ R K
  have hQK : IsCompact QK := isCompact_fullDigitCubeQ R K
  let hKfun : C(QK, ℂ) := ⟨fun q ↦ h q.1, h.continuous.comp continuous_subtype_val⟩
  obtain ⟨G, hGsupport, hGunif⟩ :=
    exists_denseElt_uniformly_approximates QK hQK hKfun (show 0 < e / 4 by positivity)
  refine ⟨G, ?_⟩
  let E : Set (QWindow R) := fullDigitCapQ R K
  have hEm : MeasurableSet E := measurableSet_fullDigitCapQ R K
  have hinside : eLpNorm (E.indicator (fun q ↦ (h q : ℂ) - G.qeval q)) 2 (qWindowLaw R)
      ≤ ENNReal.ofReal (e / 4) := by
    have hbd : ∀ᵐ q ∂(qWindowLaw R),
        ‖E.indicator (fun q ↦ (h q : ℂ) - G.qeval q) q‖ ≤ e / 4 := by
      filter_upwards [qWindowLaw_ae_mem_qRealSupport R] with q hqreal
      by_cases hqE : q ∈ E
      · rw [Set.indicator_of_mem hqE]
        have hqK : q ∈ QK := ⟨hqE, ⟨fun i _ ↦ hqreal i, Set.mem_univ q.2.2⟩⟩
        have hu := hGunif ⟨q, hqK⟩
        simpa [restrictQEval, hKfun, norm_sub_rev] using hu.le
      · rw [Set.indicator_of_notMem hqE, norm_zero]
        exact (div_nonneg he.le (by norm_num))
    have hb := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hbd
    calc
      eLpNorm (E.indicator (fun q ↦ (h q : ℂ) - G.qeval q)) 2 (qWindowLaw R)
          ≤ qWindowLaw R Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (e / 4) := hb
      _ = ENNReal.ofReal (e / 4) := by rw [measure_univ, ENNReal.one_rpow, one_mul]
  have hmeasure : qWindowLaw R Eᶜ < ENNReal.ofReal (η ^ 2) :=
    lt_of_le_of_lt (qWindowLaw_fullDigitCapQ_compl_le R K)
      ((ENNReal.ofReal_lt_ofReal_iff hη2).mpr hKbound)
  have htail : eLpNorm (Eᶜ.indicator fun q ↦ (h q : ℂ)) 2 (qWindowLaw R)
      < ENNReal.ofReal (e / 4) := by
    have hdom : ∀ᵐ q ∂(qWindowLaw R),
        ‖Eᶜ.indicator (fun q ↦ (h q : ℂ)) q‖ ≤
          ‖Eᶜ.indicator (fun _ ↦ (C : ℂ)) q‖ := by
      filter_upwards [] with q
      by_cases hqE : q ∈ Eᶜ
      · rw [Set.indicator_of_mem hqE, Set.indicator_of_mem hqE]
        have hnormC : ‖(C : ℂ)‖ = C := by
          rw [Complex.norm_real, Real.norm_of_nonneg hC.le]
        rw [hnormC]
        exact (h.norm_coe_le_norm q).trans (by dsimp [C]; linarith)
      · simp [Set.indicator_of_notMem hqE]
    refine lt_of_le_of_lt (eLpNorm_mono_ae hdom) ?_
    rw [eLpNorm_indicator_const hEm.compl (by norm_num) (by norm_num)]
    have htwo : (1 : ℝ) / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    rw [htwo, ← ofReal_norm_eq_enorm, Complex.norm_real,
      Real.norm_of_nonneg hC.le]
    have hrpow : (ENNReal.ofReal (η ^ 2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal η := by
      rw [ENNReal.ofReal_pow hη.le, ← ENNReal.rpow_natCast (ENNReal.ofReal η) 2,
        ← ENNReal.rpow_mul]
      norm_num
    have hneC : ENNReal.ofReal C ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hC]
    calc ENNReal.ofReal C * qWindowLaw R Eᶜ ^ ((1 : ℝ) / 2)
        < ENNReal.ofReal C * ENNReal.ofReal η := by
          refine ENNReal.mul_lt_mul_right hneC ENNReal.ofReal_ne_top ?_
          rw [← hrpow]
          exact ENNReal.rpow_lt_rpow hmeasure (by norm_num)
      _ = ENNReal.ofReal (e / 4) := by
          rw [← ENNReal.ofReal_mul hC.le]
          congr 1
          dsimp [η]
          field_simp
  have hsplit : (fun q ↦ (h q : ℂ) - G.qeval q) =ᵐ[qWindowLaw R]
      E.indicator (fun q ↦ (h q : ℂ) - G.qeval q) +
        Eᶜ.indicator (fun q ↦ (h q : ℂ)) := by
    filter_upwards [] with q
    by_cases hqE : q ∈ E
    · simp [hqE]
    · have hG0 : G.qeval q = 0 :=
        qeval_eq_zero_outside_fullDigitCapQ K (by simpa [QK] using hGsupport) hqE
      simp [hqE, hG0]
  have hm1 : AEStronglyMeasurable
      (E.indicator (fun q ↦ (h q : ℂ) - G.qeval q)) (qWindowLaw R) :=
    ((h.continuous.measurable.sub (continuous_qeval G).measurable).indicator hEm).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable
      (Eᶜ.indicator fun q ↦ (h q : ℂ)) (qWindowLaw R) :=
    (h.continuous.measurable.indicator hEm.compl).aestronglyMeasurable
  have hhG : eLpNorm ((fun q ↦ (h q : ℂ)) - G.qeval) 2 (qWindowLaw R)
      < ENNReal.ofReal (e / 2) := by
    change eLpNorm (fun q ↦ (h q : ℂ) - G.qeval q) 2 (qWindowLaw R)
      < ENNReal.ofReal (e / 2)
    rw [eLpNorm_congr_ae hsplit]
    calc eLpNorm
          (E.indicator (fun q ↦ (h q : ℂ) - G.qeval q) +
            Eᶜ.indicator (fun q ↦ (h q : ℂ))) 2 (qWindowLaw R)
        ≤ eLpNorm (E.indicator (fun q ↦ (h q : ℂ) - G.qeval q)) 2 (qWindowLaw R) +
            eLpNorm (Eᶜ.indicator fun q ↦ (h q : ℂ)) 2 (qWindowLaw R) :=
          eLpNorm_add_le hm1 hm2 (by norm_num)
      _ < ENNReal.ofReal (e / 4) + ENNReal.ofReal (e / 4) := by
          exact ENNReal.add_lt_add_of_le_of_lt
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinside) hinside htail
      _ = ENNReal.ofReal (e / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have hdecomp : f - G.qeval = (f - (h : QWindow R → ℂ)) +
      ((h : QWindow R → ℂ) - G.qeval) := by
    funext q
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hdecomp]
  have hmfh : AEStronglyMeasurable (f - (h : QWindow R → ℂ)) (qWindowLaw R) :=
    hf.aestronglyMeasurable.sub h.continuous.measurable.aestronglyMeasurable
  have hmhG : AEStronglyMeasurable ((h : QWindow R → ℂ) - G.qeval) (qWindowLaw R) :=
    h.continuous.measurable.aestronglyMeasurable.sub (continuous_qeval G).measurable.aestronglyMeasurable
  calc eLpNorm ((f - (h : QWindow R → ℂ)) +
        ((h : QWindow R → ℂ) - G.qeval)) 2 (qWindowLaw R)
      ≤ eLpNorm (f - (h : QWindow R → ℂ)) 2 (qWindowLaw R) +
          eLpNorm ((h : QWindow R → ℂ) - G.qeval) 2 (qWindowLaw R) :=
        eLpNorm_add_le hmfh hmhG (by norm_num)
    _ < ENNReal.ofReal (e / 4) + ENNReal.ofReal (e / 2) := by
        exact ENNReal.add_lt_add_of_le_of_lt
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfh) hfh hhG
    _ < ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact (ENNReal.ofReal_lt_ofReal_iff he).mpr (by linarith)

/-! ### Named inputs for display (55) -/

/-- **Step 1, density bridge.**  The bounded measurable representative
`BwindowRep` is approximated in `L²(windowLaw R)` by finite sums
`Σ_ℓ D_ℓ g_ℓ e(Σ c_{ℓ,t} θ_t)`.

The proof passes to `QWindow R`, where torus coordinates live in the genuine
quotient `UnitAddTorus`; Fourier characters then separate points without the
endpoint obstruction of real representatives.  Bounded continuous functions
are dense in `L²(qWindowLaw R)`.  On a full-measure real cube, a finite digit
cap gives a compact set, and Stone-Weierstrass supplies a `DenseElt`; the digit
tail bound controls its complement.  Finally the quotient pushforward and the
almost-everywhere canonical lift transfer the estimate back to `windowLaw R`.

This route uses measurability and the global `45/8` bound of `BwindowRep`; it
does not require `Section6Skeleton.BwindowRep_ae_continuous`. -/
theorem density_bridge (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : DenseElt R,
      eLpNorm (fun w : WindowSpace R => ((BwindowRep R w : ℂ)) - G.eval w) 2 (windowLaw R)
        < ENNReal.ofReal ε := by
  obtain ⟨G, hG⟩ := qDenseElt_density R (qBwindowRep R)
    (memLp_qBwindowRep R) ε hε
  refine ⟨G, ?_⟩
  have hm : AEStronglyMeasurable (fun q ↦ qBwindowRep R q - G.qeval q)
      (qWindowLaw R) :=
    (measurable_qBwindowRep R).aestronglyMeasurable.sub
      (continuous_qeval G).measurable.aestronglyMeasurable
  change eLpNorm (fun q ↦ qBwindowRep R q - G.qeval q) 2 (qWindowLaw R)
      < ENNReal.ofReal ε at hG
  rw [qWindowLaw, eLpNorm_map_measure hm
    (measurable_quotientWindow R).aemeasurable] at hG
  refine (eLpNorm_congr_ae ?_).trans_lt hG
  filter_upwards [ae_qBwindowRep_quotientWindow R] with w hw
  rw [hw]
  change qBwindowRep R (quotientWindow R w) - G.eval w =
    qBwindowRep R (quotientWindow R w) - G.qeval (quotientWindow R w)
  rw [denseElt_qeval_quotientWindow]

/-- The digit block of the truncation agrees with the digit block of the
projection: both read the digits at offsets `-R ≤ t ≤ R`. -/
theorem digitTruncWindow_fst_eq (R M : ℕ) (w : WindowSpace (R + M)) :
    (digitTruncWindow R M w).1 = (windowProj (Nat.le_add_right R M) w).1 := by
  funext i
  have hi := i.isLt
  have hc : 0 ≤ (i : ℤ) - (R : ℤ) + ((R + M : ℕ) : ℤ)
      ∧ (i : ℤ) - (R : ℤ) + ((R + M : ℕ) : ℤ) < 2 * ((R + M : ℕ) : ℤ) + 1 :=
    ⟨by omega, by omega⟩
  simp only [digitTruncWindow, windowProj, wA, dif_pos hc]
  have hidx : ((i : ℤ) - (R : ℤ) + ((R + M : ℕ) : ℤ)).toNat = (i : ℕ) + (R + M - R) := by
    omega
  simp only [hidx]

/-- The torus block of the truncation agrees with the torus block of the
projection. -/
theorem digitTruncWindow_trd_eq (R M : ℕ) (w : WindowSpace (R + M)) :
    (digitTruncWindow R M w).2.2 = (windowProj (Nat.le_add_right R M) w).2.2 := by
  funext i
  have hi := i.isLt
  have hc : 0 ≤ (i : ℤ) - (R : ℤ) - 1 + ((R + M : ℕ) : ℤ) + 1
      ∧ (i : ℤ) - (R : ℤ) - 1 + ((R + M : ℕ) : ℤ) + 1 < 2 * ((R + M : ℕ) : ℤ) + 2 :=
    ⟨by omega, by omega⟩
  simp only [digitTruncWindow, windowProj, wTh, dif_pos hc]
  have hidx : ((i : ℤ) - (R : ℤ) - 1 + ((R + M : ℕ) : ℤ) + 1).toNat
      = (i : ℕ) + (R + M - R) := by
    omega
  simp only [hidx]

/-- The real block of the projection, read through `wX`. -/
theorem windowProj_snd_fst_eq_wX (R M : ℕ) (w : WindowSpace (R + M))
    (i : Fin (2 * R + 1)) :
    (windowProj (Nat.le_add_right R M) w).2.1 i = wX w ((i : ℤ) - (R : ℤ)) := by
  have hi := i.isLt
  have hc : 0 ≤ (i : ℤ) - (R : ℤ) + ((R + M : ℕ) : ℤ)
      ∧ (i : ℤ) - (R : ℤ) + ((R + M : ℕ) : ℤ) < 2 * ((R + M : ℕ) : ℤ) + 1 :=
    ⟨by omega, by omega⟩
  simp only [windowProj, wX, dif_pos hc]
  have hidx : ((i : ℤ) - (R : ℤ) + ((R + M : ℕ) : ℤ)).toNat = (i : ℕ) + (R + M - R) := by
    omega
  simp only [hidx]

/-- On an orbit-consistent window the real coordinates are a Gauss orbit:
`x_{t+k} = T^k x_t` wherever the offsets stay in range. -/
theorem orbitConsistent_gaussIter_wX {R' : ℕ} {w : WindowSpace R'}
    (h : OrbitConsistent R' w) {t : ℤ} (h1 : -(R' : ℤ) ≤ t) (k : ℕ)
    (hk : t + (k : ℤ) ≤ (R' : ℤ)) : gaussIter (wX w t) k = wX w (t + (k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : t + (k : ℤ) ≤ (R' : ℤ) := by push_cast at hk; omega
      rw [gaussIter_succ, ih hk']
      have hstep := h.2 (t + (k : ℤ)) (by omega) (by push_cast at hk; omega)
      rw [← hstep]
      congr 1
      push_cast
      ring

/-- On an orbit-consistent window the digit at offset `t + k` is the
`k`-th continued-fraction digit of the real coordinate at offset `t`. -/
theorem orbitConsistent_wA_eq_digit {R' : ℕ} {w : WindowSpace R'}
    (h : OrbitConsistent R' w) {t : ℤ} (h1 : -(R' : ℤ) ≤ t) (k : ℕ)
    (hk : t + (k : ℤ) + 1 ≤ (R' : ℤ)) :
    wA w (t + (k : ℤ)) = digit (wX w t) k := by
  have hiter := orbitConsistent_gaussIter_wX h h1 k (by omega)
  have hA := (h.1 (t + (k : ℤ)) (by omega) (by omega)).2.2
  rw [hA, ← hiter]
  rfl

/-- **Input (step 2, finite-future replacement), v5 lines 1332-1343 —
closed.**  Replacing `x_{j+t}` by `[0; a_{j+t+1}, …, a_{j+t+M}]` for
`|t| ≤ R` moves each of the finitely many continuous factors `g_ℓ` by
`o(1)` as `M → ∞`, uniformly.

The statement is *not* pointwise true — at an arbitrary
`w : WindowSpace (R + M)` the digit block and the real block are
unrelated — and the proof runs on the law:

1. `ae_orbitConsistent (R + M)` puts almost every window on an
   irrational Gauss orbit, so the digit family that `digitTruncWindow`
   reads at offset `t` is the digit family of `x_t`
   (`OrbitConsistent.wA_eq_digit`), and both real blocks lie in the unit
   cube.
2. The contraction `abs_sub_cfFinite_digit_le` (proved above, avoiding
   Mathlib's continued-fraction machinery: the `M`-fold composition of
   `u ↦ 1/(a+u)` telescopes into the product `x_0 ⋯ x_{M-1} ≤ 1/F_{M+1}`
   by display (6)) makes the two real blocks `1/F_{M+1}`-close in the
   sup metric.
3. Each `g_ℓ` is uniformly continuous on the compact unit cube
   (Heine–Cantor); a single `δ` serves the finitely many `ℓ`, and `M` is
   chosen with `1/F_{M+1} < δ`.  The difference of evaluations is then
   almost everywhere below `ε/2`, and `μ_{R+M}` is a probability
   measure. -/
theorem digit_truncation (R : ℕ) (G : DenseElt R) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      1 ≤ M ∧
      eLpNorm (fun w : WindowSpace (R + M) =>
          G.eval (windowProj (Nat.le_add_right R M) w) - G.eval (digitTruncWindow R M w))
        2 (windowLaw (R + M)) < ENNReal.ofReal ε := by
  classical
  have hA0 : (0 : ℝ) ≤ ∑ l : Fin G.len, ∑ v ∈ G.Dwords l, ‖G.D l v‖ :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun v _ => norm_nonneg _
  set A : ℝ := ∑ l : Fin G.len, ∑ v ∈ G.Dwords l, ‖G.D l v‖ with hAdef
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  set ε' : ℝ := ε / (2 * (A + 1)) with hε'def
  have hε'0 : 0 < ε' := div_pos hε (by linarith)
  set K : Set (Fin (2 * R + 1) → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1 with hK
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ l : Fin G.len, ∀ x ∈ K, ∀ y ∈ K,
      dist x y < δ → dist (G.g l x) (G.g l y) < ε' := by
    have hunif : ∀ l : Fin G.len, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K,
        dist x y < δ → dist (G.g l x) (G.g l y) < ε' := by
      intro l
      have hcomp : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
      have huc : UniformContinuousOn (G.g l) K :=
        hcomp.uniformContinuousOn_of_continuous (G.g_continuous l).continuousOn
      rcases Metric.uniformContinuousOn_iff.mp huc ε' hε'0 with ⟨δ, hδ0, hδ⟩
      exact ⟨δ, hδ0, fun x hx y hy hxy => hδ x hx y hy hxy⟩
    choose δf hδf0 hδf using hunif
    rcases isEmpty_or_nonempty (Fin G.len) with hE | hNE
    · exact ⟨1, one_pos, fun l => (hE.false l).elim⟩
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty δf, ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        exact fun l _ => hδf0 l
      · intro l x hx y hy hxy
        exact hδf l x hx y hy
          (lt_of_lt_of_le hxy (Finset.inf'_le _ (Finset.mem_univ l)))
  obtain ⟨M₀, hM₀⟩ := exists_fib_inv_lt hδ0
  let M := M₀ + 1
  have hMpos : 1 ≤ M := by simp [M]
  have hfib₀ : (0 : ℝ) < Nat.fib (M₀ + 1) := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < M₀ + 1))
  have hfib₁ : (0 : ℝ) < Nat.fib (M₀ + 2) := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < M₀ + 2))
  have hfible : ((Nat.fib (M₀ + 1) : ℕ) : ℝ) ≤ (Nat.fib (M₀ + 2) : ℝ) := by
    exact_mod_cast (Nat.fib_le_fib_succ (n := M₀ + 1))
  have hM : ((Nat.fib (M + 1) : ℝ))⁻¹ < δ := by
    rw [show M + 1 = M₀ + 2 by simp [M]]
    exact lt_of_le_of_lt ((inv_le_inv₀ hfib₁ hfib₀).2 hfible) hM₀
  refine ⟨M, hMpos, ?_⟩
  have hae : ∀ᵐ w ∂(windowLaw (R + M)),
      ‖G.eval (windowProj (Nat.le_add_right R M) w) - G.eval (digitTruncWindow R M w)‖
        ≤ ε / 2 := by
    filter_upwards [ae_orbitConsistent (R + M)] with w hw
    have hfst := digitTruncWindow_fst_eq R M w
    have htrd := digitTruncWindow_trd_eq R M w
    have hdiff : G.eval (windowProj (Nat.le_add_right R M) w)
        - G.eval (digitTruncWindow R M w)
        = ∑ l : Fin G.len,
            G.D l ((windowProj (Nat.le_add_right R M) w).1)
              * (G.g l ((windowProj (Nat.le_add_right R M) w).2.1)
                  - G.g l ((digitTruncWindow R M w).2.1))
              * torusChar (∑ t : Fin (2 * R + 2),
                  (G.c l t : ℝ) * (windowProj (Nat.le_add_right R M) w).2.2 t) := by
      unfold DenseElt.eval
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hfst, htrd]
      ring
    have hproj_mem : (windowProj (Nat.le_add_right R M) w).2.1 ∈ K := by
      intro i _
      rw [windowProj_snd_fst_eq_wX]
      have hi := i.isLt
      have hIoo := (hw.1 ((i : ℤ) - (R : ℤ)) (by push_cast; omega) (by push_cast; omega)).1
      exact ⟨hIoo.1.le, hIoo.2.le⟩
    have htrunc_mem : (digitTruncWindow R M w).2.1 ∈ K := by
      intro i _
      change cfFinite (fun k => wA w ((i : ℤ) - (R : ℤ) + (k : ℤ))) M ∈ Icc (0 : ℝ) 1
      refine ⟨cfFinite_nonneg M _, cfFinite_le_one M _ fun k hk => ?_⟩
      have hi := i.isLt
      have h1 : -(((R + M) : ℕ) : ℤ) ≤ (i : ℤ) - (R : ℤ) + (k : ℤ) := by push_cast; omega
      have h2 : (i : ℤ) - (R : ℤ) + (k : ℤ) ≤ (((R + M) : ℕ) : ℤ) := by push_cast; omega
      obtain ⟨hIoo, hirr, hdig⟩ := hw.1 _ h1 h2
      rw [hdig]
      exact one_le_digit hIoo hirr 0
    have hdist : dist ((windowProj (Nat.le_add_right R M) w).2.1)
        ((digitTruncWindow R M w).2.1) < δ := by
      rw [dist_pi_lt_iff hδ0]
      intro i
      have hi := i.isLt
      have h1 : -(((R + M) : ℕ) : ℤ) ≤ (i : ℤ) - (R : ℤ) := by push_cast; omega
      have h2' : (i : ℤ) - (R : ℤ) ≤ (((R + M) : ℕ) : ℤ) := by push_cast; omega
      obtain ⟨hIoo, hirr, -⟩ := hw.1 ((i : ℤ) - (R : ℤ)) h1 h2'
      have hcf : cfFinite (fun k => wA w ((i : ℤ) - (R : ℤ) + (k : ℤ))) M
          = cfFinite (fun k => digit (wX w ((i : ℤ) - (R : ℤ))) k) M :=
        cfFinite_congr M _ _ (fun k hk =>
          orbitConsistent_wA_eq_digit hw h1 k (by push_cast; omega))
      rw [Real.dist_eq, windowProj_snd_fst_eq_wX]
      show |wX w ((i : ℤ) - (R : ℤ))
          - cfFinite (fun k => wA w ((i : ℤ) - (R : ℤ) + (k : ℤ))) M| < δ
      rw [hcf]
      exact lt_of_le_of_lt (abs_sub_cfFinite_digit_le M hIoo hirr) hM
    rw [hdiff]
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum
      (g := fun l => (∑ v ∈ G.Dwords l, ‖G.D l v‖) * ε') ?_) ?_)
    · intro l _
      rw [norm_mul, norm_mul, Prop42.norm_torusChar, mul_one]
      have hDle : ‖G.D l ((windowProj (Nat.le_add_right R M) w).1)‖
          ≤ ∑ v ∈ G.Dwords l, ‖G.D l v‖ := by
        by_cases hu : (windowProj (Nat.le_add_right R M) w).1 ∈ G.Dwords l
        · exact Finset.single_le_sum (fun v _ => norm_nonneg _) hu
        · rw [G.D_support l _ hu, norm_zero]
          exact Finset.sum_nonneg fun v _ => norm_nonneg _
      have hgle : ‖G.g l ((windowProj (Nat.le_add_right R M) w).2.1)
          - G.g l ((digitTruncWindow R M w).2.1)‖ ≤ ε' := by
        have h := hδ l _ hproj_mem _ htrunc_mem hdist
        rw [dist_eq_norm] at h
        exact h.le
      exact mul_le_mul hDle hgle (norm_nonneg _)
        (Finset.sum_nonneg fun v _ => norm_nonneg _)
    · rw [← Finset.sum_mul, ← hAdef]
      have h2 : A * ε' ≤ ε / 2 := by
        rw [hε'def, ← mul_div_assoc,
          div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (A + 1)) (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      exact h2
  calc eLpNorm (fun w : WindowSpace (R + M) =>
          G.eval (windowProj (Nat.le_add_right R M) w) - G.eval (digitTruncWindow R M w))
        2 (windowLaw (R + M))
      ≤ (windowLaw (R + M)) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (ε / 2) :=
        eLpNorm_le_of_ae_bound hae
    _ = ENNReal.ofReal (ε / 2) := by
        rw [measure_univ, ENNReal.one_rpow, one_mul]
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        linarith

/-- **A dense-algebra element is bounded wherever the real block lies in
the unit cube.**  The digit amplitude is dominated by the sum of its
finitely many nonzero values, the continuous factor by its supremum on the
compact cube, and the character has modulus one.  On all of `X_R` the
`g_ℓ` are unbounded — the cube hypothesis is where
`ae_norm_digitTrunc_le` puts the truncated real block almost surely. -/
theorem denseElt_bound {R : ℕ} (G : DenseElt R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : WindowSpace R,
      (∀ i, v.2.1 i ∈ Icc (0:ℝ) 1) → ‖G.eval v‖ ≤ B := by
  have hD : ∀ (l : Fin G.len) (u : Fin (2 * R + 1) → ℕ),
      ‖G.D l u‖ ≤ ∑ v ∈ G.Dwords l, ‖G.D l v‖ := by
    intro l u
    by_cases hu : u ∈ G.Dwords l
    · exact Finset.single_le_sum (fun v _ => norm_nonneg _) hu
    · rw [G.D_support l u hu, norm_zero]
      exact Finset.sum_nonneg fun v _ => norm_nonneg _
  have hg : ∀ l : Fin G.len, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.univ.pi fun _ : Fin (2 * R + 1) => Icc (0:ℝ) 1, ‖G.g l x‖ ≤ C := by
    intro l
    obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : Fin (2 * R + 1) =>
      isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
      (G.g_continuous l).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx => le_trans (hC x hx) (le_max_left _ _)⟩
  choose Cg hCg0 hCg using hg
  refine ⟨∑ l : Fin G.len, (∑ v ∈ G.Dwords l, ‖G.D l v‖) * Cg l, ?_, ?_⟩
  · exact Finset.sum_nonneg fun l _ =>
      mul_nonneg (Finset.sum_nonneg fun v _ => norm_nonneg _) (hCg0 l)
  · intro v hv
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, norm_mul, Prop42.norm_torusChar, mul_one]
    have hvc : v.2.1 ∈ Set.univ.pi fun _ : Fin (2 * R + 1) => Icc (0:ℝ) 1 :=
      fun i _ => hv i
    exact mul_le_mul (hD l v.1) (hCg l _ hvc) (norm_nonneg _)
      (Finset.sum_nonneg fun u _ => norm_nonneg _)

/-- **`G_M` is almost surely bounded.**  On the orbit-consistent
full-measure event of `ae_orbitConsistent` every digit read by
`digitTruncWindow` is a genuine Gauss digit of an irrational point of
`(0,1)`, hence `≥ 1`, so the truncated real block `cfFinite` lands in
`[0,1]^{2R+1}` (`cfFinite_le_one`), where `denseElt_bound` applies.  The
bound is *not* pointwise: an arbitrary window may carry digit `0`, where
`cfFinite` degenerates to an unbounded `u⁻¹`. -/
theorem ae_norm_digitTrunc_le (R M : ℕ) (G : DenseElt R) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᵐ w ∂(windowLaw (R + M)), ‖G.eval (digitTruncWindow R M w)‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := denseElt_bound G
  refine ⟨B, hB0, ?_⟩
  filter_upwards [ae_orbitConsistent (R + M)] with w hw
  refine hB _ fun i => ?_
  refine ⟨cfFinite_nonneg M _, cfFinite_le_one M _ fun k hk => ?_⟩
  have hi := i.isLt
  have h1 : -(((R + M) : ℕ) : ℤ) ≤ (i:ℤ) - (R:ℤ) + (k:ℤ) := by push_cast; omega
  have h2 : (i:ℤ) - (R:ℤ) + (k:ℤ) ≤ (((R + M) : ℕ) : ℤ) := by push_cast; omega
  obtain ⟨hIoo, hirr, hdig⟩ := hw.1 _ h1 h2
  rw [hdig]
  exact one_le_digit hIoo hirr 0

/-- **The union bound for the digit-cap complement**:
`μ_{R'}(E_{M,K}^c) ≤ (2R') · 2/(K+1)`.  Stationarity has already made
every offset's tail equal to the `t = 0` Gauss tail
(`Kwon1002.windowLaw_digitCoord_tail`, `Kwon1002/DigitLaw.lean`), so the
manuscript's `O_R(M/K)` appears in the explicit form `(2R') · 2/(K+1)`. -/
theorem windowLaw_digitCapEvent_compl_le (R' K : ℕ) :
    windowLaw R' ((digitCapEvent R' K)ᶜ)
      ≤ ENNReal.ofReal ((2 * (R' : ℝ)) * (2 / ((K : ℝ) + 1))) := by
  have hcompl : (digitCapEvent R' K)ᶜ
      = ⋃ i : Fin (2 * R'), {w : WindowSpace R' | K + 1 ≤ w.1 (⟨i, by omega⟩ : Fin (2 * R' + 1))} := by
    ext w
    simp only [digitCapEvent, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le,
      Set.mem_iUnion]
    exact exists_congr fun i => Nat.lt_iff_add_one_le
  rw [hcompl]
  refine le_trans (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine le_trans (Finset.sum_le_sum
      (fun i _ => windowLaw_digitCoord_tail R' (⟨i, by omega⟩ : Fin (2 * R' + 1)) K)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  push_cast
  ring

/-- **Input (step 3, digit truncation)**, v5 lines 1345-1356 — **closed**.
`μ_{R+M}(E_{M,K}^c) = O_R(M/K)` by Lemma 3.1(ii), stationarity and a union
bound, and `G_M` is bounded, so
`‖G_M - G_M 1_{E_{M,K}}‖²_{L²} ≤ ‖G_M‖_∞² μ_{R+M}(E_{M,K}^c)`.

The two halves the earlier obstruction note asked for are now in the tree,
and this proof only assembles them.

1. *The digit-block marginal.*  Stationarity of `μ̂₀` under the cocycle in
   **both** time directions (`Lemma62.hatS_measurePreserving` and the new
   `Kwon1002.hatSinv_measurePreserving`) makes all `2R'` union-bound
   terms equal to the `t = 0` term, and the `t = 0` term is the
   future-coordinate marginal of `ν̂`
   (`NatExtMeasure.hatNu_fst_marginal`) fed through the one-level Gauss
   tail: `μ_{R'}{a_t ≥ K+1} ≤ 2/(K+1)` at every offset
   (`Kwon1002.windowLaw_digitCoord_tail`).  The union bound is
   `windowLaw_digitCapEvent_compl_le` above.
2. *Boundedness of `G_M`.*  Not pointwise — the `g_ℓ` are unbounded on
   the real block — but almost sure, via `ae_orbitConsistent` and
   `cfFinite_le_one` (`ae_norm_digitTrunc_le` above).

With an a.e. bound `B` and the measure bound, the difference is dominated
by `(B+1) 1_{E^c}`, whose `L²` norm is `(B+1) μ(E^c)^{1/2}`; any
`K > 2(2R')(B+1)²/ε²` then wins. -/
theorem event_truncation (R M : ℕ) (G : DenseElt R) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ,
      eLpNorm (fun w : WindowSpace (R + M) =>
          G.eval (digitTruncWindow R M w)
            - (digitCapEvent (R + M) K).indicator
                (fun v => G.eval (digitTruncWindow R M v)) w)
        2 (windowLaw (R + M)) < ENNReal.ofReal ε := by
  obtain ⟨B, hB0, hBae⟩ := ae_norm_digitTrunc_le R M G
  have hB1 : (0:ℝ) < B + 1 := by linarith
  set δ : ℝ := ε / (B + 1) with hδdef
  have hδ : 0 < δ := div_pos hε hB1
  have hδ2 : (0:ℝ) < δ ^ 2 := by positivity
  obtain ⟨K, hKgt⟩ := exists_nat_gt ((2 * ((R + M : ℕ) : ℝ)) * 2 / δ ^ 2)
  have hK1 : (0:ℝ) < (K:ℝ) + 1 := by positivity
  have hKbound : (2 * ((R + M : ℕ) : ℝ)) * (2 / ((K:ℝ) + 1)) < δ ^ 2 := by
    rw [div_lt_iff₀ hδ2] at hKgt
    rw [← mul_div_assoc, div_lt_iff₀ hK1]
    nlinarith
  refine ⟨K, ?_⟩
  -- the difference vanishes on `E` and is the a.e.-bounded `G_M` off it:
  -- dominate it by the constant `B + 1` cut to the complement
  have hdom : ∀ᵐ w ∂(windowLaw (R + M)),
      ‖G.eval (digitTruncWindow R M w)
          - (digitCapEvent (R + M) K).indicator
              (fun v => G.eval (digitTruncWindow R M v)) w‖
        ≤ ‖((digitCapEvent (R + M) K)ᶜ).indicator (fun _ => B + 1) w‖ := by
    filter_upwards [hBae] with w hw
    by_cases hwE : w ∈ digitCapEvent (R + M) K
    · rw [Set.indicator_of_mem hwE, sub_self, norm_zero,
        Set.indicator_of_notMem (by simpa using hwE)]
      simp
    · rw [Set.indicator_of_notMem hwE, sub_zero,
        Set.indicator_of_mem (by simpa using hwE), Real.norm_of_nonneg (by linarith)]
      linarith
  refine lt_of_le_of_lt (eLpNorm_mono_ae hdom) ?_
  rw [eLpNorm_indicator_const (measurableSet_digitCapEvent (R + M) K).compl
    (by norm_num) (by norm_num)]
  have htwo : (1 : ℝ) / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
  rw [htwo, Real.enorm_eq_ofReal (by linarith : (0:ℝ) ≤ B + 1)]
  -- the measure factor is strictly below `δ`, and `(B+1)δ = ε`
  have hmeaslt : windowLaw (R + M) ((digitCapEvent (R + M) K)ᶜ)
      < ENNReal.ofReal (δ ^ 2) :=
    lt_of_le_of_lt (windowLaw_digitCapEvent_compl_le (R + M) K)
      ((ENNReal.ofReal_lt_ofReal_iff hδ2).mpr hKbound)
  have hrpow : (ENNReal.ofReal (δ ^ 2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal δ := by
    rw [ENNReal.ofReal_pow hδ.le, ← ENNReal.rpow_natCast (ENNReal.ofReal δ) 2,
      ← ENNReal.rpow_mul]
    norm_num
  have hne0 : ENNReal.ofReal (B + 1) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hB1]
  calc ENNReal.ofReal (B + 1)
        * windowLaw (R + M) ((digitCapEvent (R + M) K)ᶜ) ^ ((1:ℝ) / 2)
      < ENNReal.ofReal (B + 1) * ENNReal.ofReal δ := by
        refine ENNReal.mul_lt_mul_right hne0 ENNReal.ofReal_ne_top ?_
        rw [← hrpow]
        exact ENNReal.rpow_lt_rpow hmeaslt (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul (by linarith)]
        congr 1
        rw [hδdef]
        field_simp

/-- **Input (step 4, identity (31)).**  v5 lines 1357-1372: on `E_{M,K}`
only finitely many full digit words survive, and on each of them identity
(31) collapses `Σ_{t=-R-1}^{R} c_{ℓ,t} θ_{j+t}` to `A_{ℓ,w} θ_j +
B_{ℓ,w} θ_{j-1}` modulo 1.  Hence `G_M 1_{E_{M,K}}` is *exactly* a finite
linear combination of the monomials (32) at radius `R + M`, with central
modes `(r,s) = (B_{ℓ,w}, A_{ℓ,w})`.

Consumes `Kwon1002.V5Identity31.window_character_reduction_v5` (proved, at
the full v5 range `t = -R-1, …, R`).
The equality is asserted `windowLaw (R+M)`-almost everywhere, exactly as the
manuscript uses it on the orbit-consistent stationary support.  It is false
on arbitrary points of the ambient product `WindowSpace`, whose noncentral
torus coordinates are independent. -/
theorem identity_31_monomial_form (R M K : ℕ) (G : DenseElt R) (hMpos : 1 ≤ M) :
    ∃ K' : ℕ, ∃ P : WindowSymbol (R + M) K',
      ∀ᵐ w ∂(windowLaw (R + M)),
        (digitCapEvent (R + M) K).indicator
            (fun v => G.eval (digitTruncWindow R M v)) w
          = P.evalWindow w := by
  let R' := R + M
  let words : Finset (Fin (2 * R') → ℕ) :=
    Fintype.piFinset (fun _ : Fin (2 * R') => Finset.range (K + 1))
  let coreWord (w : Fin (2 * R') → ℕ) : Fin (2 * R) → ℕ :=
    fun i => w ⟨M + (i : ℕ), by have := i.isLt; dsimp [R']; omega⟩
  let denseDigits (w : Fin (2 * R') → ℕ) : Fin (2 * R + 1) → ℕ :=
    fun i => w ⟨M + (i : ℕ), by have := i.isLt; dsimp [R']; omega⟩
  let truncReals (w : Fin (2 * R') → ℕ) : Fin (2 * R + 1) → ℝ :=
    fun i => cfFinite (fun k => if hk : k < M then
      w ⟨M + (i : ℕ) + k,
        by have := i.isLt; dsimp [R']; omega⟩ else 0) M
  let A (l : Fin G.len) (w : Fin (2 * R') → ℕ) : ℤ :=
    V5Identity31.winA1 R (G.c l) (coreWord w)
  let B (l : Fin G.len) (w : Fin (2 * R') → ℕ) : ℤ :=
    V5Identity31.winB1 R (G.c l) (coreWord w)
  let amp (l : Fin G.len) (w : Fin (2 * R') → ℕ) : ℂ :=
    G.D l (denseDigits w) * G.g l (truncReals w)
  let pairs : Finset (Fin G.len × (Fin (2 * R') → ℕ)) := Finset.univ ×ˢ words
  let K' : ℕ := pairs.sup (fun p => (B p.1 p.2).natAbs + (A p.1 p.2).natAbs)
  let P : WindowSymbol R' K' :=
    { coeff := fun w r s =>
        if w ∈ words then
          ∑ l : Fin G.len, if r = B l w ∧ s = A l w then amp l w else 0
        else 0
      words := words
      coeff_support := by
        intro w r s hw
        simp [hw]
      mode_cap := by
        intro w r s hrs
        by_cases hw : w ∈ words
        · simp only [hw, if_true]
          refine Finset.sum_eq_zero fun l _ => ?_
          by_cases hm : r = B l w ∧ s = A l w
          · have hp : (l, w) ∈ pairs := by simp [pairs, hw]
            have hle : (B l w).natAbs + (A l w).natAbs ≤ K' :=
              Finset.le_sup (f := fun p => (B p.1 p.2).natAbs + (A p.1 p.2).natAbs) hp
            rw [if_pos hm]
            exfalso
            rw [hm.1, hm.2] at hrs
            omega
          · rw [if_neg hm]
        · simp [hw] }
  refine ⟨K', P, ?_⟩
  have hGmeas : Measurable G.eval := by
    unfold DenseElt.eval
    refine Finset.measurable_sum _ fun l _ => Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact (Measurable.of_discrete (f := G.D l)).comp measurable_fst
    · exact ((G.g_continuous l).measurable).comp (measurable_fst.comp measurable_snd)
    · refine Prop42.continuous_torusChar.measurable.comp ?_
      exact Finset.measurable_sum _ fun t _ =>
        ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)).const_mul _
  have hCFmeas : ∀ (m : ℕ) (a : WindowSpace R' → ℕ → ℕ),
      (∀ k, Measurable fun w => a w k) → Measurable fun w => cfFinite (a w) m := by
    intro m
    induction m with
    | zero =>
        intro a _
        simpa only [cfFinite] using (measurable_const : Measurable fun _ : WindowSpace R' => (0 : ℝ))
    | succ m ih =>
        intro a ha
        have h0 : Measurable fun w : WindowSpace R' => ((a w 0 : ℕ) : ℝ) :=
          (measurable_from_top (f := fun q : ℕ => (q : ℝ))).comp (ha 0)
        have h1 : Measurable fun w : WindowSpace R' => cfFinite (fun k => a w (k + 1)) m :=
          ih (fun w k => a w (k + 1)) fun k => ha (k + 1)
        simpa only [cfFinite] using (h0.add h1).inv
  have hTruncMeas : Measurable (digitTruncWindow R M) := by
    unfold digitTruncWindow
    refine Measurable.prodMk (measurable_pi_lambda _ fun _ => measurable_wA _ _)
      (Measurable.prodMk ?_ (measurable_pi_lambda _ fun _ => measurable_wTh _ _))
    exact measurable_pi_lambda _ fun _ =>
      hCFmeas M _ fun _ => measurable_wA _ _
  have hLmeas : Measurable fun w : WindowSpace R' =>
      (digitCapEvent R' K).indicator (fun v => G.eval (digitTruncWindow R M v)) w :=
    Measurable.indicator (hGmeas.comp hTruncMeas) (measurableSet_digitCapEvent R' K)
  have hWordMeas : Measurable (windowWordOf R') :=
    measurable_pi_lambda _ fun _ => measurable_wA R' _
  have hPmeas : Measurable P.evalWindow := by
    unfold WindowSymbol.evalWindow
    refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ =>
      Measurable.mul ?_ ?_
    · exact (Measurable.of_discrete (f := fun v : Fin (2 * R') → ℕ => P.coeff v r s)).comp
        hWordMeas
    · exact Prop42.continuous_torusChar.measurable.comp
        (((measurable_wTh R' (-1)).const_mul _).add ((measurable_wTh R' 0).const_mul _))
  have hEqMeas : MeasurableSet {w : WindowSpace R' |
      (digitCapEvent R' K).indicator (fun v => G.eval (digitTruncWindow R M v)) w
        = P.evalWindow w} := measurableSet_eq_fun hLmeas hPmeas
  rw [windowLaw, ae_map_iff (measurable_stationaryWindow R').aemeasurable hEqMeas]
  filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz
  have hword : windowWordOf R' (stationaryWindow R' z) = natExtWord R' z.1 := by
    funext i
    rw [windowWordOf, wA_stationaryWindow R' z (by omega) (by omega)]
    exact (StationaryIdentity31.wordFn_natExtWord hz R' (i : ℕ) i.isLt).symm.trans (by
      simp [wordFn])
  have hprefix : ∀ i : Fin (2 * R'),
      (stationaryWindow R' z).1 ⟨(i : ℕ), by have := i.isLt; omega⟩ = natExtWord R' z.1 i := by
    intro i
    have hi := congrFun hword i
    have hc : 0 ≤ (i : ℤ) - (R' : ℤ) + (R' : ℤ) ∧
        (i : ℤ) - (R' : ℤ) + (R' : ℤ) < 2 * (R' : ℤ) + 1 := by omega
    have hidx : (⟨((i : ℤ) - (R' : ℤ) + (R' : ℤ)).toNat, by omega⟩ : Fin (2 * R' + 1))
        = ⟨(i : ℕ), by have := i.isLt; omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simpa only [windowWordOf, wA, dif_pos hc, hidx] using hi
  have hmem : stationaryWindow R' z ∈ digitCapEvent R' K ↔ natExtWord R' z.1 ∈ words := by
    rw [Fintype.mem_piFinset]
    simp only [digitCapEvent, Set.mem_setOf_eq, Finset.mem_range]
    constructor
    · intro h i
      have hi := h i
      rw [hprefix i] at hi
      exact Nat.lt_succ_of_le hi
    · intro h i
      have hi := h i
      rw [hprefix i]
      exact Nat.le_of_lt_succ hi
  by_cases hw : natExtWord R' z.1 ∈ words
  · rw [Set.indicator_of_mem (hmem.mpr hw)]
    have hcore : coreWord (natExtWord R' z.1) = natExtWord R z.1 := by
      funext i
      have hbig := StationaryIdentity31.wordFn_natExtWord hz R' (M + (i : ℕ)) (by
        have := i.isLt
        dsimp [R']
        omega)
      have hsmall := StationaryIdentity31.wordFn_natExtWord hz R (i : ℕ) i.isLt
      have hbnd : M + (i : ℕ) < 2 * R' := by have := i.isLt; dsimp [R']; omega
      have hbig' : natExtWord R' z.1 ⟨M + (i : ℕ), hbnd⟩
          = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
        simpa [wordFn, hbnd] using hbig
      have hsmall' : natExtWord R z.1 i
          = digit (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1 0 := by
        simpa [wordFn, i.isLt] using hsmall
      simp only [coreWord]
      calc
        natExtWord R' z.1 ⟨M + (i : ℕ), _⟩
            = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := hbig'
        _ = digit (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1 0 := by
          have hoff : (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ))
              = (i : ℤ) - (R : ℤ) := by
            dsimp [R']
            omega
          rw [hoff]
        _ = natExtWord R z.1 i := hsmall'.symm
    have hdense : (digitTruncWindow R M (stationaryWindow R' z)).1
        = denseDigits (natExtWord R' z.1) := by
      funext i
      simp only [digitTruncWindow, denseDigits]
      rw [wA_stationaryWindow R' z (by dsimp [R']; omega) (by dsimp [R']; omega)]
      have hbig := StationaryIdentity31.wordFn_natExtWord hz R' (M + (i : ℕ)) (by
        have := i.isLt
        dsimp [R']
        omega)
      have hbnd : M + (i : ℕ) < 2 * R' := by have := i.isLt; dsimp [R']; omega
      have hbig' : natExtWord R' z.1 ⟨M + (i : ℕ), hbnd⟩
          = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
        simpa [wordFn, hbnd] using hbig
      calc
        digit (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1 0
            = digit (hatSzpow (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
              have hoff : ((i : ℤ) - (R : ℤ))
                  = (((M + (i : ℕ) : ℕ) : ℤ) - (R' : ℤ)) := by
                dsimp [R']
                omega
              rw [hoff]
        _ = natExtWord R' z.1 ⟨M + (i : ℕ), _⟩ := hbig'.symm
    have htrunc : (digitTruncWindow R M (stationaryWindow R' z)).2.1
        = truncReals (natExtWord R' z.1) := by
      funext i
      simp only [digitTruncWindow, truncReals]
      apply cfFinite_congr
      intro k hk
      rw [dif_pos hk, wA_stationaryWindow R' z (by dsimp [R']; omega)
        (by have := i.isLt; dsimp [R']; omega)]
      have hbig := StationaryIdentity31.wordFn_natExtWord hz R'
        (M + (i : ℕ) + k) (by have := i.isLt; dsimp [R']; omega)
      have hbnd : M + (i : ℕ) + k < 2 * R' := by have := i.isLt; dsimp [R']; omega
      have hbig' : natExtWord R' z.1 ⟨M + (i : ℕ) + k, hbnd⟩
          = digit (hatSzpow (((M + (i : ℕ) + k : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
        simpa [wordFn, hbnd] using hbig
      calc
        digit (hatSzpow ((i : ℤ) - (R : ℤ) + (k : ℤ)) z).1.1 0
            = digit (hatSzpow (((M + (i : ℕ) + k : ℕ) : ℤ) - (R' : ℤ)) z).1.1 0 := by
              have hoff : ((i : ℤ) - (R : ℤ) + (k : ℤ))
                  = (((M + (i : ℕ) + k : ℕ) : ℤ) - (R' : ℤ)) := by
                dsimp [R']
                omega
              rw [hoff]
        _ = natExtWord R' z.1 ⟨M + (i : ℕ) + k, _⟩ := hbig'.symm
    have hchar : ∀ l : Fin G.len,
        torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
            (digitTruncWindow R M (stationaryWindow R' z)).2.2 t)
          = torusChar ((B l (natExtWord R' z.1) : ℝ) *
              wTh (stationaryWindow R' z) (-1)
            + (A l (natExtWord R' z.1) : ℝ) * wTh (stationaryWindow R' z) 0) := by
      intro l
      have hc := StationaryIdentity31.stationary_character_reduction R (G.c l) hz
      simp only [A, B, hcore]
      rw [wTh_stationaryWindow R' z (by dsimp [R']; omega) (by omega),
        wTh_stationaryWindow R' z (by dsimp [R']; omega) (by omega)]
      calc
        torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
            (digitTruncWindow R M (stationaryWindow R' z)).2.2 t)
            = torusChar (∑ t : Fin (2 * R + 2), (G.c l t : ℝ) *
                (hatSzpow ((t : ℤ) - (R : ℤ) - 1) z).2.2) := by
              congr 2
              funext t
              simp only [digitTruncWindow]
              rw [wTh_stationaryWindow R' z (by have := t.isLt; dsimp [R']; omega)
                (by have := t.isLt; dsimp [R']; omega)]
        _ = _ := hc
        _ = _ := by simp [hatSzpow]
    have hmode : ∀ l : Fin G.len,
        B l (natExtWord R' z.1) ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ) ∧
        A l (natExtWord R' z.1) ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ) := by
      intro l
      have hp : (l, natExtWord R' z.1) ∈ pairs := by simp [pairs, hw]
      have hle : (B l (natExtWord R' z.1)).natAbs +
          (A l (natExtWord R' z.1)).natAbs ≤ K' :=
        Finset.le_sup (f := fun p => (B p.1 p.2).natAbs + (A p.1 p.2).natAbs) hp
      have hBabs : |B l (natExtWord R' z.1)| ≤ (K' : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (le_trans (Nat.le_add_right _ _) hle)
      have hAabs : |A l (natExtWord R' z.1)| ≤ (K' : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (le_trans (Nat.le_add_left _ _) hle)
      exact ⟨Finset.mem_Icc.mpr (abs_le.mp hBabs), Finset.mem_Icc.mpr (abs_le.mp hAabs)⟩
    unfold DenseElt.eval WindowSymbol.evalWindow
    simp only [P, hw, if_true, hword]
    rw [hdense, htrunc]
    simp only [amp]
    simp_rw [hchar]
    symm
    simp_rw [Finset.sum_mul]
    calc
      (∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
          ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
            ∑ l : Fin G.len, (if r = B l (natExtWord R' z.1) ∧
                s = A l (natExtWord R' z.1) then amp l (natExtWord R' z.1) else 0) *
              torusChar ((r : ℝ) * wTh (stationaryWindow R' z) (-1) +
                (s : ℝ) * wTh (stationaryWindow R' z) 0))
          = ∑ l : Fin G.len, ∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
              ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
                (if r = B l (natExtWord R' z.1) ∧ s = A l (natExtWord R' z.1)
                  then amp l (natExtWord R' z.1) else 0) *
                torusChar ((r : ℝ) * wTh (stationaryWindow R' z) (-1) +
                  (s : ℝ) * wTh (stationaryWindow R' z) 0) := by
            calc
              _ = ∑ r ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ), ∑ l : Fin G.len,
                    ∑ s ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
                      (if r = B l (natExtWord R' z.1) ∧ s = A l (natExtWord R' z.1)
                        then amp l (natExtWord R' z.1) else 0) *
                      torusChar ((r : ℝ) * wTh (stationaryWindow R' z) (-1) +
                        (s : ℝ) * wTh (stationaryWindow R' z) 0) := by
                          refine Finset.sum_congr rfl fun r _ => ?_
                          rw [Finset.sum_comm]
              _ = _ := by rw [Finset.sum_comm]
      _ = ∑ l : Fin G.len, amp l (natExtWord R' z.1) *
            torusChar ((B l (natExtWord R' z.1) : ℝ) * wTh (stationaryWindow R' z) (-1) +
              (A l (natExtWord R' z.1) : ℝ) * wTh (stationaryWindow R' z) 0) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_eq_single (B l (natExtWord R' z.1))]
        · rw [Finset.sum_eq_single (A l (natExtWord R' z.1))]
          · simp
          · intro s _ hs
            rw [if_neg (by rintro ⟨_, hsl⟩; exact hs hsl)]
            simp
          · intro h
            exact (h (hmode l).2).elim
        · intro r _ hr
          refine Finset.sum_eq_zero fun s _ => ?_
          rw [if_neg (by rintro ⟨hrl, _⟩; exact hr hrl)]
          simp
        · intro h
          exact (h (hmode l).1).elim
      _ = _ := rfl
  · rw [Set.indicator_of_notMem (fun h => hw (hmem.mp h))]
    unfold WindowSymbol.evalWindow
    simp [P, hword, hw]

/-! ### Measurability on the window space

The digit block `Fin (2R+1) → ℕ` of `X_R` is a finite product of countable
discrete spaces, so it carries the discrete measurable structure and *every*
function out of it is measurable.  That is what makes the digit-cylinder
amplitudes `D_ℓ` of `DenseElt` and the word coefficients of a
`WindowSymbol` measurable without any hypothesis on them.  The rest is the
window coordinate readers of `WindowLaws.lean` (`measurable_wA`,
`measurable_wX`, `measurable_wTh`), continuity of `torusChar`, and finite
sums. -/

/-- The full digit word of a window is a measurable function of the window,
into the discrete space `Fin (2R) → ℕ`. -/
theorem measurable_windowWordOf (R : ℕ) : Measurable (windowWordOf R) :=
  measurable_pi_lambda _ fun _ => measurable_wA R _

/-- A finite continued fraction of measurably varying digits is a
measurable function.  The induction is on the depth `M`, with the digit
family generalised because each step shifts it. -/
theorem measurable_cfFinite {X : Type*} [MeasurableSpace X] :
    ∀ (M : ℕ) (a : X → ℕ → ℕ), (∀ k, Measurable fun x => a x k) →
      Measurable fun x => cfFinite (a x) M
  | 0, _, _ => by
      simpa only [cfFinite] using (measurable_const : Measurable fun _ : X => (0 : ℝ))
  | M + 1, a, ha => by
      have h0 : Measurable fun x : X => ((a x 0 : ℕ) : ℝ) :=
        (measurable_from_top (f := fun m : ℕ => (m : ℝ))).comp (ha 0)
      have h1 : Measurable fun x : X => cfFinite (fun k => a x (k + 1)) M :=
        measurable_cfFinite M (fun x k => a x (k + 1)) fun k => ha (k + 1)
      simpa only [cfFinite] using (h0.add h1).inv

/-- **Input (measurability).**  A dense-algebra element is measurable: the
digit factor is a function on a countable discrete block, the `g_ℓ` are
continuous, and the character is continuous. -/
theorem measurable_denseElt {R : ℕ} (G : DenseElt R) : Measurable G.eval := by
  unfold DenseElt.eval
  refine Finset.measurable_sum _ fun l _ => Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact (Measurable.of_discrete (f := G.D l)).comp measurable_fst
  · exact ((G.g_continuous l).measurable).comp (measurable_fst.comp measurable_snd)
  · refine Prop42.continuous_torusChar.measurable.comp ?_
    exact Finset.measurable_sum _ fun t _ =>
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)).const_mul _

/-- **Input (measurability).**  The `M`-digit truncation map is
measurable: the digit and torus blocks are coordinate readers, and the
real block is the finite continued fraction `cfFinite` of finitely many
digit coordinates. -/
theorem measurable_digitTruncWindow (R M : ℕ) : Measurable (digitTruncWindow R M) := by
  unfold digitTruncWindow
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_lambda _ fun _ => measurable_wA _ _
  · exact measurable_pi_lambda _ fun _ =>
      measurable_cfFinite M _ fun _ => measurable_wA _ _
  · exact measurable_pi_lambda _ fun _ => measurable_wTh _ _

/-- **Input (measurability).**  A window symbol is measurable on its own
window space: the coefficient reads the (discrete) window word and the
monomial is a continuous character in the two central torus
coordinates. -/
theorem measurable_evalWindow {R K : ℕ} (P : WindowSymbol R K) :
    Measurable P.evalWindow := by
  unfold WindowSymbol.evalWindow
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ =>
    Measurable.mul ?_ ?_
  · exact (Measurable.of_discrete (f := fun v : Fin (2 * R) → ℕ => P.coeff v r s)).comp
      (measurable_windowWordOf R)
  · exact Prop42.continuous_torusChar.measurable.comp
      (((measurable_wTh R (-1)).const_mul _).add ((measurable_wTh R 0).const_mul _))

/-! ### The change of variables along `π_{R+M,R}` -/

/-- Lifting to the larger radius does not change the `L²` norm: this is
`(π_{R',R})_* μ_{R'} = μ_R`, v5 line 1165, which the skeleton proves. -/
theorem eLpNorm_comp_windowProj {R M : ℕ} (f : WindowSpace R → ℂ) (hf : Measurable f) :
    eLpNorm (fun w : WindowSpace (R + M) => f (windowProj (Nat.le_add_right R M) w)) 2
        (windowLaw (R + M))
      = eLpNorm f 2 (windowLaw R) := by
  rw [← windowProj_map_windowLaw (Nat.le_add_right R M)]
  exact (eLpNorm_map_measure hf.aestronglyMeasurable
    (measurable_windowProj (Nat.le_add_right R M)).aemeasurable).symm

/-! ### Display (55) -/

/-- **Display (55), corrected** (v5 lines 1307-1408, and the revision
note `manuscript/proposition_6_4_revision_note.pdf`).

For every `R` and every `ε > 0` there are `M, K` and a *real-valued*
finite linear combination `P_{R,M}` of the monomials (32) **at radius
`R + M`** with
`‖B^{(R)} ∘ π_{R+M,R} - P_{R,M}‖_{L²(μ_{R+M})} < ε`. -/
theorem display_55_monomial_approximation (R : ℕ) :
    ∀ ε > 0, ∃ M K : ℕ, ∃ P : WindowSymbol (R + M) K,
      (∀ w : WindowSpace (R + M), (P.evalWindow w).im = 0) ∧
      eLpNorm
          (fun w : WindowSpace (R + M) =>
            ((BwindowRep R (windowProj (Nat.le_add_right R M) w) : ℂ) - P.evalWindow w))
          2 (windowLaw (R + M))
        < ENNReal.ofReal ε := by
  intro ε hε
  have hBmeas : Measurable (BwindowRep R) := measurable_BwindowRep R
  obtain ⟨G, hG⟩ := density_bridge R (ε / 4) (by linarith)
  obtain ⟨M, hMpos, hM⟩ := digit_truncation R G (ε / 4) (by linarith)
  obtain ⟨K, hK⟩ := event_truncation R M G (ε / 4) (by linarith)
  obtain ⟨K', P, hP⟩ := identity_31_monomial_form R M K G hMpos
  refine ⟨M, K', (symRe P), fun w => evalWindow_symRe_im P w, ?_⟩
  set ν : Measure (WindowSpace (R + M)) := windowLaw (R + M) with hν
  set π := windowProj (Nat.le_add_right R M) with hπ
  set F0 : WindowSpace (R + M) → ℂ := fun w => ((BwindowRep R (π w) : ℂ)) with hF0
  set F1 : WindowSpace (R + M) → ℂ := fun w => G.eval (π w) with hF1
  set F2 : WindowSpace (R + M) → ℂ := fun w => G.eval (digitTruncWindow R M w) with hF2
  set F3 : WindowSpace (R + M) → ℂ :=
    (digitCapEvent (R + M) K).indicator (fun v => G.eval (digitTruncWindow R M v)) with hF3
  -- measurability of the five functions in play
  have hmF0 : Measurable F0 :=
    Complex.measurable_ofReal.comp (hBmeas.comp (measurable_windowProj _))
  have hmF1 : Measurable F1 := (measurable_denseElt G).comp (measurable_windowProj _)
  have hmF2 : Measurable F2 := (measurable_denseElt G).comp (measurable_digitTruncWindow R M)
  have hmF3 : Measurable F3 :=
    Measurable.indicator hmF2 (measurableSet_digitCapEvent (R + M) K)
  -- the real-part reduction
  have hre : eLpNorm (fun w => F0 w - (symRe P).evalWindow w) 2 ν
      ≤ eLpNorm (fun w => F0 w - P.evalWindow w) 2 ν := by
    refine eLpNorm_mono fun w => ?_
    rw [evalWindow_symRe]
    exact norm_sub_re_le _ _
  -- the chain `B^{(R)} → G → G_M → G_M 1_E → P`
  have hPν : ∀ᵐ w ∂ν, F3 w = P.evalWindow w := by
    simpa only [hν, hF3] using hP
  have hsplit : (fun w => F0 w - P.evalWindow w) =ᵐ[ν]
      fun w => ((F0 w - F1 w) + (F1 w - F2 w)) + (F2 w - F3 w) := by
    filter_upwards [hPν] with w hw
    rw [← hw]
    ring
  have htri1 : eLpNorm (fun w => ((F0 w - F1 w) + (F1 w - F2 w)) + (F2 w - F3 w)) 2 ν
      ≤ eLpNorm (fun w => (F0 w - F1 w) + (F1 w - F2 w)) 2 ν
        + eLpNorm (fun w => F2 w - F3 w) 2 ν :=
    eLpNorm_add_le ((hmF0.sub hmF1).aestronglyMeasurable.add
      (hmF1.sub hmF2).aestronglyMeasurable) (hmF2.sub hmF3).aestronglyMeasurable (by norm_num)
  have htri2 : eLpNorm (fun w => (F0 w - F1 w) + (F1 w - F2 w)) 2 ν
      ≤ eLpNorm (fun w => F0 w - F1 w) 2 ν + eLpNorm (fun w => F1 w - F2 w) 2 ν :=
    eLpNorm_add_le (hmF0.sub hmF1).aestronglyMeasurable
      (hmF1.sub hmF2).aestronglyMeasurable (by norm_num)
  -- the first error is the density-bridge error, transported by `π_{R+M,R}`
  have hlift : eLpNorm (fun w => F0 w - F1 w) 2 ν
      = eLpNorm (fun w : WindowSpace R => ((BwindowRep R w : ℂ)) - G.eval w) 2 (windowLaw R) :=
    eLpNorm_comp_windowProj (M := M)
      (fun w => ((BwindowRep R w : ℂ)) - G.eval w)
      (Complex.measurable_ofReal.comp hBmeas |>.sub (measurable_denseElt G))
  have h1 : eLpNorm (fun w => F0 w - F1 w) 2 ν < ENNReal.ofReal (ε / 4) := by
    rw [hlift]; exact hG
  calc eLpNorm (fun w => F0 w - (symRe P).evalWindow w) 2 ν
      ≤ eLpNorm (fun w => F0 w - P.evalWindow w) 2 ν := hre
    _ = eLpNorm (fun w => ((F0 w - F1 w) + (F1 w - F2 w)) + (F2 w - F3 w)) 2 ν :=
        eLpNorm_congr_ae hsplit
    _ ≤ (eLpNorm (fun w => F0 w - F1 w) 2 ν + eLpNorm (fun w => F1 w - F2 w) 2 ν)
          + eLpNorm (fun w => F2 w - F3 w) 2 ν := le_trans htri1 (by gcongr)
    _ ≤ (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) + ENNReal.ofReal (ε / 4) := by
        gcongr <;>
          first
            | exact h1.le
            | exact hM.le
            | exact hK.le
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-! ## Statement identity against `Section6Skeleton`

`display_55_monomial_approximation` and `prop_6_4_bounded_remainder_weak_law`
are reproduced in this file token for token from
`Kwon1002/Section6Skeleton.lean` and are proved here.  They cannot be merged
into the skeleton by delegation, because this file *imports* the skeleton;
the two `example`s below are the drift guard instead.  Each elaborates the
skeleton's declaration and this file's declaration at the same type, so a
change to either statement breaks the build. -/

/-- Statement identity, type check only. -/
example : @_root_.Kwon1002.display_55_monomial_approximation
    = @display_55_monomial_approximation := rfl

/-- Statement identity, type check only. -/
example : @_root_.Kwon1002.prop_6_4_bounded_remainder_weak_law
    = @prop_6_4_bounded_remainder_weak_law := rfl

end

end Prop64

end Kwon1002
