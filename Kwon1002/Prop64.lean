import Kwon1002.Section6Skeleton
import Kwon1002.WindowLaws

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
open scoped BigOperators Topology ENNReal

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
integrand.  **Obstruction.**  Those three are themselves sorried in the
skeleton, and the passage from the probability bound (57) to the `L²`
bound needs the uniform bound `|B_j| ≤ C` of the principal split, which
has not been formalised. -/
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

Consumes `Section4.prop_4_2_two_block_factorization` (equivalently
`V5Prop42.prop_4_2_v5`) and `Section6Skeleton.lemma_6_3_full_state_transfer`
for the replacement of the stationary means by the actual means.
**Obstruction.**  Proposition 4.2 is sorried, and the covariance
bookkeeping that turns it into a variance bound has not been formalised. -/
theorem poly_centered_avg_L2_tendsto_zero (R M K : ℕ) (P : WindowSymbol (R + M) K) :
    Tendsto (fun n : ℕ => eLpNorm
        (centeredAvg (Lnorm n) (bulkJ n) (fun j α => (P.at α n j).re)) 2
        (volume.restrict (Ioo (0 : ℝ) 1))) atTop (𝓝 0) := by
  sorry

/-- **Input (`L²` membership).**  `B_j` is a bounded measurable function of
`α`.  **Obstruction.**  Measurability in `α` of `gaussIter`, `digit`,
`theta` and `carry` is not in the tree, and the boundedness of `Φ` on the
orbit is exactly the "bounded remainder" statement of the principal
split. -/
theorem memLp_Bremainder (n j : ℕ) :
    MemLp (fun α => Bremainder α n j) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  sorry

/-- **Input (`L²` membership).**  Same for the carry-truncated remainder. -/
theorem memLp_BremainderTrunc (R n j : ℕ) :
    MemLp (fun α => BremainderTrunc α n R j) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  sorry

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

/-- **`E_{M,K}`** of v5 lines 1345-1352: every digit of the full symmetric
radius-`R'` word is at most `K`. -/
def digitCapEvent (R' K : ℕ) : Set (WindowSpace R') :=
  {w | ∀ i : Fin (2 * R' + 1), w.1 i ≤ K}

theorem measurableSet_digitCapEvent (R' K : ℕ) : MeasurableSet (digitCapEvent R' K) := by
  have hrw : digitCapEvent R' K = ⋂ i : Fin (2 * R' + 1), {w : WindowSpace R' | w.1 i ≤ K} := by
    ext w; simp [digitCapEvent]
  rw [hrw]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun w : WindowSpace R' => w.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hpre : {w : WindowSpace R' | w.1 i ≤ K}
      = (fun w : WindowSpace R' => w.1 i) ⁻¹' {n : ℕ | n ≤ K} := rfl
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
      = ⋂ i : Fin (2 * R' + 1), {w : WindowSpace R' | w.1 i ≤ K} := by
    ext w; simp [digitCapEvent]
  rw [hrw]
  refine isClosed_iInter fun i => ?_
  have hcont : Continuous fun w : WindowSpace R' => w.1 i :=
    (continuous_apply i).comp continuous_fst
  have hpre : {w : WindowSpace R' | w.1 i ≤ K}
      = (fun w : WindowSpace R' => w.1 i) ⁻¹' {n : ℕ | n ≤ K} := rfl
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
  exact hw

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

/-! ### Named inputs for display (55) -/

/-- **Input (step 1, density bridge).**  v5 lines 1316-1330: the algebra
of finite sums `Σ_ℓ D_ℓ g_ℓ e(Σ c_{ℓ,t} θ_t)` is dense in `L²(μ_R)`, and
`B^{(R)}` is bounded and `μ_R`-almost-everywhere continuous, so it is
approximated to any accuracy.

Consumes `Section6Skeleton.Bwindow_bounded_and_ae_continuous`.
**Obstruction.**  The density statement itself is the one v5 records
"after Lemma 6.3"; it has not been formalised, and it needs a
Stone-Weierstrass argument on `X_R` together with the regularity of
`μ_R`. -/
theorem density_bridge (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : DenseElt R,
      eLpNorm (fun w : WindowSpace R => ((Bwindow R w : ℂ)) - G.eval w) 2 (windowLaw R)
        < ENNReal.ofReal ε := by
  sorry

/-- **Input (step 2, finite-future replacement).**  v5 lines 1332-1343:
replacing `x_{j+t}` by `[0; a_{j+t+1}, …, a_{j+t+M}]` for `|t| ≤ R` moves
each of the finitely many continuous factors `g_ℓ` by `o(1)` as `M → ∞`,
uniformly, because `max_{|t| ≤ R} |x_{j+t} - x^{[M]}_{j+t}| = O_R(F_M^{-2})`.

**Obstruction, precisely.**  Three inputs are missing, and the first of
them is a structural one rather than an estimate.

1. **The support of `μ_{R+M}`.**  The statement is *not* pointwise true.
   At an arbitrary `w : WindowSpace (R + M)` the digit block `w.1` and the
   real block `w.2.1` are unrelated -- nothing in the type ties `x_t` to
   the digits `a_t, a_{t+1}, …` -- so `digitTruncWindow R M w` need not be
   anywhere near `windowProj _ w`, and `G.eval` of the two can differ by
   as much as `G` varies.  What makes the display true is that
   `windowLaw (R + M)` is `hatMu0` pushed forward along
   `stationaryWindow (R + M)`, and on the image of that map the blocks
   *are* linked: `stationaryWindow` reads `x_i` off `hatSzpow (i - R') z`
   and `a_i = digit x_i 0`, so consecutive real coordinates satisfy
   `x_{i+1} = gaussMap x_i` and hence `x_i = 1/(a_i + x_{i+1})`, which is
   exactly the recursion `cfFinite` unwinds.  That marginal description of
   `windowLaw` is not in the tree; it is the same missing ingredient the
   sibling input `event_truncation` names.
2. **The contraction estimate.**  Given the link of item 1, one needs
   `|x - [0; a_1, …, a_M]| ≤ 1/(q_M q_{M+1}) = O(F_M^{-2})`.  Mathlib's
   `Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean` and
   `ApproximationCorollaries.lean` carry this for `GenContFract.of`, but
   `cfFinite` here is a bare recursion on a digit family and is not yet
   identified with a Mathlib convergent.
3. **Uniform continuity of the `g_ℓ`.**  `DenseElt.g_continuous` gives
   continuity on all of `Fin (2R+1) → ℝ`, which is not compact, so a
   uniform modulus needs the real block confined to a cube -- again item 1,
   and then `isCompact_digitCapCube` above supplies the compact set. -/
theorem digit_truncation (R : ℕ) (G : DenseElt R) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      eLpNorm (fun w : WindowSpace (R + M) =>
          G.eval (windowProj (Nat.le_add_right R M) w) - G.eval (digitTruncWindow R M w))
        2 (windowLaw (R + M)) < ENNReal.ofReal ε := by
  sorry

/-- **Input (step 3, digit truncation).**  v5 lines 1345-1356:
`μ_{R+M}(E_{M,K}^c) = O_R(M/K)` by Lemma 3.1(ii), stationarity and a union
bound, and `G_M` is bounded, so
`‖G_M - G_M 1_{E_{M,K}}‖²_{L²} ≤ ‖G_M‖_∞² μ_{R+M}(E_{M,K}^c)`.

Consumes `Kwon1002.digit_tail_product` (Lemma 3.1(ii), proved).
**Obstruction.**  Transporting the digit-tail bound from Gauss measure to
the stationary window law `μ_{R+M}` requires the marginal identity for
`windowLaw`, which is not in the tree. -/
theorem event_truncation (R M : ℕ) (G : DenseElt R) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ,
      eLpNorm (fun w : WindowSpace (R + M) =>
          G.eval (digitTruncWindow R M w)
            - (digitCapEvent (R + M) K).indicator
                (fun v => G.eval (digitTruncWindow R M v)) w)
        2 (windowLaw (R + M)) < ENNReal.ofReal ε := by
  sorry

/-- **Input (step 4, identity (31)).**  v5 lines 1357-1372: on `E_{M,K}`
only finitely many full digit words survive, and on each of them identity
(31) collapses `Σ_{t=-R-1}^{R} c_{ℓ,t} θ_{j+t}` to `A_{ℓ,w} θ_j +
B_{ℓ,w} θ_{j-1}` modulo 1.  Hence `G_M 1_{E_{M,K}}` is *exactly* a finite
linear combination of the monomials (32) at radius `R + M`, with central
modes `(r,s) = (B_{ℓ,w}, A_{ℓ,w})`.

Consumes `Kwon1002.V5Identity31.window_character_reduction_v5` (proved, at
the full v5 range `t = -R-1, …, R`).
**Obstruction.**  Identity (31) is available along an actual orbit; the
present statement needs its window-space form, i.e. the same reduction
performed on the coordinates of a point of `X_{R+M}` rather than on
`theta α n (j+t)`.  That is a transcription of the same recursion, but it
is a transcription that has not been carried out. -/
theorem identity_31_monomial_form (R M K : ℕ) (G : DenseElt R) :
    ∃ K' : ℕ, ∃ P : WindowSymbol (R + M) K',
      ∀ w : WindowSpace (R + M),
        (digitCapEvent (R + M) K).indicator
            (fun v => G.eval (digitTruncWindow R M v)) w
          = P.evalWindow w := by
  sorry

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
            ((Bwindow R (windowProj (Nat.le_add_right R M) w) : ℂ) - P.evalWindow w))
          2 (windowLaw (R + M))
        < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨CB, _hCB, hBmeas, _hBcont⟩ := Bwindow_bounded_and_ae_continuous R
  obtain ⟨G, hG⟩ := density_bridge R (ε / 4) (by linarith)
  obtain ⟨M, hM⟩ := digit_truncation R G (ε / 4) (by linarith)
  obtain ⟨K, hK⟩ := event_truncation R M G (ε / 4) (by linarith)
  obtain ⟨K', P, hP⟩ := identity_31_monomial_form R M K G
  refine ⟨M, K', (symRe P), fun w => evalWindow_symRe_im P w, ?_⟩
  set ν : Measure (WindowSpace (R + M)) := windowLaw (R + M) with hν
  set π := windowProj (Nat.le_add_right R M) with hπ
  set F0 : WindowSpace (R + M) → ℂ := fun w => ((Bwindow R (π w) : ℂ)) with hF0
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
  have hsplit : (fun w => F0 w - P.evalWindow w)
      = fun w => ((F0 w - F1 w) + (F1 w - F2 w)) + (F2 w - F3 w) := by
    funext w
    rw [← hP w]
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
      = eLpNorm (fun w : WindowSpace R => ((Bwindow R w : ℂ)) - G.eval w) 2 (windowLaw R) :=
    eLpNorm_comp_windowProj (M := M)
      (fun w => ((Bwindow R w : ℂ)) - G.eval w)
      (Complex.measurable_ofReal.comp hBmeas |>.sub (measurable_denseElt G))
  have h1 : eLpNorm (fun w => F0 w - F1 w) 2 ν < ENNReal.ofReal (ε / 4) := by
    rw [hlift]; exact hG
  calc eLpNorm (fun w => F0 w - (symRe P).evalWindow w) 2 ν
      ≤ eLpNorm (fun w => F0 w - P.evalWindow w) 2 ν := hre
    _ = eLpNorm (fun w => ((F0 w - F1 w) + (F1 w - F2 w)) + (F2 w - F3 w)) 2 ν := by
        rw [hsplit]
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
