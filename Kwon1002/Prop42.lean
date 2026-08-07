import Kwon1002.Section4
import Kwon1002.NatExtMeasure
import Kwon1002.SmallJumps

/-!
# P42, Proposition 4.2 (two-block factorization), display (34)

Target: `prop_4_2_two_block_factorization` of `Kwon1002/Section4.lean`,
reproduced here **token-identically** (diffed) and proved from a single
sorried input.

## What is proved outright (all axiom-clean)

* `eighty_lyapunov_bounds` : `94 < 80λ < 95` for `λ = π²/(12 log 2)`, the
  numerical content of referee note 5, machine-checked;
  `acCompatible_of_le_one` : every `c, δ ≤ 1` satisfies `c + 3δ < 80λ`.
* the **monomial decomposition** of a window symbol (32): `at_eq_sum`,
  `eval_eq_sum` (pure algebra, from `WindowSymbol.coeff_support`);
* the measure theory needed to turn that decomposition into a
  decomposition of the two integrals appearing in (34):
  `measurable_monoAt` / `measurable_monoEval` (built on
  `measurableSet_windowWord_eq`, `measurableSet_natExtWord_eq`, the
  cylinder events are measurable), `norm_torusChar` (`|e(t)| = 1`),
  `isFiniteMeasure_hatMu0` (`μ̂₀` really is a finite measure: the
  natural-extension density `1/(log 2 (1+xy)²)` is bounded by `1/log 2`
  on the unit box, whose volume is `1`), hence `integrable_monoEval`,
  `integrable_monoAt_mul`, hence `stationaryIntegral_eq_sum` and
  `integral_at_mul_at`;
* `two_block_bound_of_mono` : the bilinear step, if every monomial pair
  obeys a bound `M`, the pair `(U,V)` obeys `‖c_U‖₁ ‖c_V‖₁ M`;
* `prop_4_2_two_block_factorization` itself, from the monomial core, with
  the exceptional-set bookkeeping done honestly: the exceptional set of
  `(U,V)` is covered by the union of the `|symIdx U| · |symIdx V|`
  monomial exceptional sets, so the `O(LH)` count survives with a
  constant depending only on `U, V`, and one constant `C` serves both the
  error bound and the count (a `max`).

Two genuinely provable *steps of Kwon's argument* are also proved:

* `later_frequency_dominates`, "Fibonacci growth makes the later
  frequency dominate the earlier one": from `q_{j+2} ≥ 2 q_j`
  (`two_mul_denom_le`, `pow_two_mul_denom_le`) and the trivial bound
  `|Q_j(r,s)| ≤ (|r|+|s|) q_j` (`abs_Qfreq_le`), a gap `k - j ≥ 2m` with
  `2^m ≥ 2K/η` gives `|(-1)^j Q_j + (-1)^k Q_k| ≥ ½ η q_k`.  With
  `η = e^{-cH}` this is exactly the manuscript's `k - j ≥ CH`, and it
  pins the constant: `C = 2c/log 2` up to an additive `O_K(1)`.
* `retained_descendant_exponent`, the display "Since
  `2λt₋ = L + λk − 80λH + O(1)`, every retained descendant satisfies
  `q_{t₋}² ≤ e^{−cH} n|Q|`", with the rate left symbolic.  The rate that
  actually comes out is `80λ − 3δ − c`, and `retained_rate_pos_iff` says
  it is positive **iff** `ACCompatible c δ`, i.e. `c + 3δ < 80λ`.

## What is assumed

Exactly one sorried statement, `two_block_monomial_core`: display (34)
for a single pair of monomials, uniformly over two fixed finite word
sets and the mode box.  Its missing ingredient is Lemma 3.2 (conditional
two-sided Gauss mixing across the block gap), which is not yet available
in this development; Lemmas 3.3 and 3.4 that it also uses *are* proved
(`shrinking_anti_concentration`, `descendant_phase_small`).

## Note on the constant `c` (sharpening of referee note 5)

Kwon writes `c` for four different roles inside the proof of 4.2: the
anti-concentration rate in `η = e^{−cH}`, the rate in
`q_{t₋}² ≤ e^{−cH} n|Q|`, the block-gap constant, and the final error
rate.  `retained_descendant_exponent` shows the second is
`80λ − 3δ − c₁` where `c₁` is the first; requiring it to be *the same*
`c` therefore needs `2c + 3δ < 80λ`, one notch stronger than the
`c + 3δ < 80λ` our referee report recorded.  Both hold for the standard
choices (any `c, δ ≤ 1`, by `acCompatible_of_le_one` and
`eighty_lyapunov_bounds`), and the existential quantifier over `c` in the
formal statement absorbs either, so nothing downstream is constrained.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace Prop42

noncomputable section

/-! ## The anti-concentration constant compatibility (referee note 5) -/

/-- The compatibility constraint that the proof of Prop 4.2 uses silently. -/
def ACCompatible (c δ : ℝ) : Prop := c + 3 * δ < 80 * lyapunov

lemma lyapunov_pos : 0 < lyapunov := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  exact div_pos hp (by linarith)

lemma eighty_lyapunov_bounds : 94 < 80 * lyapunov ∧ 80 * lyapunov < 95 := by
  have hpi1 : 3.141592 < Real.pi := Real.pi_gt_d6
  have hpi2 : Real.pi < 3.141593 := Real.pi_lt_d6
  have hl1 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hd : (0 : ℝ) < 12 * Real.log 2 := by linarith
  have hsq1 : (9.8696 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_pos]
  have hsq2 : Real.pi ^ 2 < (9.869607 : ℝ) := by nlinarith [Real.pi_pos]
  have key : 80 * lyapunov = 80 * Real.pi ^ 2 / (12 * Real.log 2) := by
    unfold lyapunov; ring
  rw [key]
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

/-- The compatibility of referee note 5 is *not* a real constraint: any
`c, δ ≤ 1` satisfies it, and the proof is free to shrink `c`. -/
lemma acCompatible_of_le_one {c δ : ℝ} (hc : c ≤ 1) (hδ : δ ≤ 1) : ACCompatible c δ := by
  have := eighty_lyapunov_bounds.1
  unfold ACCompatible
  linarith

/-! ## Monomials -/

/-- A single cylinder-torus monomial (32) with unit coefficient, at time `j`. -/
def monoAt (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) (α : ℝ) (n j : ℕ) : ℂ :=
  (if windowWord R α j = w then (1 : ℂ) else 0) *
    torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j)

/-- The same monomial on the natural extension times `T²`. -/
def monoEval (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) (z : (ℝ × ℝ) × ℝ × ℝ) : ℂ :=
  (if natExtWord R z.1 = w then (1 : ℂ) else 0) *
    torusChar ((r : ℝ) * z.2.1 + (s : ℝ) * z.2.2)

/-- Its `μ̂₀`-mean. -/
def monoStationary (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) : ℂ :=
  ∫ z, monoEval R w r s z ∂hatMu0

/-- The torus modes allowed by the cap `K`. -/
def modeBox (K : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(K : ℤ)) (K : ℤ) ×ˢ Finset.Icc (-(K : ℤ)) (K : ℤ)

/-- The finite index set of monomials making up a window symbol. -/
def symIdx {R K : ℕ} (U : WindowSymbol R K) : Finset ((Fin (2 * R) → ℕ) × ℤ × ℤ) :=
  U.words ×ˢ modeBox K

/-! ### The monomial decomposition (pure algebra) -/

lemma sum_symIdx_mul {R K : ℕ} (U : WindowSymbol R K) (W : Fin (2 * R) → ℕ)
    (τ : ℤ → ℤ → ℂ) :
    ∑ t ∈ symIdx U, U.coeff t.1 t.2.1 t.2.2 *
        ((if W = t.1 then (1 : ℂ) else 0) * τ t.2.1 t.2.2)
      = ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          U.coeff W r s * τ r s := by
  classical
  have inner : ∀ r s : ℤ,
      ∑ w ∈ U.words, U.coeff w r s * ((if W = w then (1 : ℂ) else 0) * τ r s)
        = U.coeff W r s * τ r s := by
    intro r s
    have hcongr : ∀ w ∈ U.words,
        U.coeff w r s * ((if W = w then (1 : ℂ) else 0) * τ r s)
          = if W = w then U.coeff w r s * τ r s else 0 := by
      intro w _
      by_cases h : W = w <;> simp [h]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
    by_cases h : W ∈ U.words
    · simp [h]
    · simp [h, U.coeff_support W r s h]
  rw [symIdx, Finset.sum_product]
  simp only [modeBox, Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => inner r s

lemma at_eq_sum {R K : ℕ} (U : WindowSymbol R K) (α : ℝ) (n j : ℕ) :
    U.at α n j
      = ∑ t ∈ symIdx U, U.coeff t.1 t.2.1 t.2.2 * monoAt R t.1 t.2.1 t.2.2 α n j := by
  exact (sum_symIdx_mul U (windowWord R α j)
    (fun r s => torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j))).symm

lemma eval_eq_sum {R K : ℕ} (U : WindowSymbol R K) (z : (ℝ × ℝ) × ℝ × ℝ) :
    U.eval z
      = ∑ t ∈ symIdx U, U.coeff t.1 t.2.1 t.2.2 * monoEval R t.1 t.2.1 t.2.2 z := by
  exact (sum_symIdx_mul U (natExtWord R z.1)
    (fun r s => torusChar ((r : ℝ) * z.2.1 + (s : ℝ) * z.2.2))).symm

/-! ### The character has modulus one -/

lemma continuous_torusChar : Continuous torusChar := by
  unfold torusChar
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

lemma norm_torusChar (t : ℝ) : ‖torusChar t‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [torusChar, h, Complex.norm_exp_ofReal_mul_I]

/-! ### Measurability -/

lemma measurable_digitNat (j : ℕ) : Measurable fun α : ℝ => digit α j := by
  have h : (fun α : ℝ => digit α j) = Int.toNat ∘ fun α : ℝ => ⌊(gaussIter α j)⁻¹⌋ := by
    funext α; rfl
  rw [h]
  exact (measurable_from_top (f := Int.toNat)).comp ((measurable_gaussIter j).inv.floor)

lemma measurable_thetaPred (n j : ℕ) : Measurable fun α : ℝ => thetaPred α n j := by
  cases j with
  | zero => simp only [thetaPred]; exact measurable_const
  | succ j => simpa [thetaPred] using measurable_theta n j

lemma measurableSet_windowWord_eq (R : ℕ) (w : Fin (2 * R) → ℕ) (j : ℕ) :
    MeasurableSet {α : ℝ | windowWord R α j = w} := by
  have h : {α : ℝ | windowWord R α j = w}
      = ⋂ t : Fin (2 * R), {α : ℝ | digit α (j + (t : ℕ) - R) = w t} := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_iInter, windowWord, funext_iff]
  rw [h]
  exact MeasurableSet.iInter fun t =>
    measurable_digitNat (j + (t : ℕ) - R) (measurableSet_singleton (w t))

lemma measurableSet_natExtWord_eq (R : ℕ) (w : Fin (2 * R) → ℕ) :
    MeasurableSet {z : (ℝ × ℝ) × ℝ × ℝ | natExtWord R z.1 = w} := by
  have h : {z : (ℝ × ℝ) × ℝ × ℝ | natExtWord R z.1 = w}
      = ⋂ t : Fin (2 * R), {z : (ℝ × ℝ) × ℝ × ℝ |
          (if (t : ℕ) < R then digit z.1.2 (R - 1 - (t : ℕ)) else digit z.1.1 ((t : ℕ) - R))
            = w t} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, natExtWord, funext_iff]
  rw [h]
  refine MeasurableSet.iInter fun t => ?_
  by_cases ht : (t : ℕ) < R
  · simp only [ht, if_true]
    exact ((measurable_digitNat (R - 1 - (t : ℕ))).comp measurable_fst.snd)
      (measurableSet_singleton (w t))
  · simp only [ht, if_false]
    exact ((measurable_digitNat ((t : ℕ) - R)).comp measurable_fst.fst)
      (measurableSet_singleton (w t))

lemma measurable_monoAt (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) (n j : ℕ) :
    Measurable fun α : ℝ => monoAt R w r s α n j := by
  unfold monoAt
  refine Measurable.mul ?_ ?_
  · exact Measurable.ite (measurableSet_windowWord_eq R w j) measurable_const measurable_const
  · exact continuous_torusChar.measurable.comp
      (((measurable_thetaPred n j).const_mul _).add ((measurable_theta n j).const_mul _))

lemma measurable_monoEval (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) :
    Measurable fun z : (ℝ × ℝ) × ℝ × ℝ => monoEval R w r s z := by
  unfold monoEval
  refine Measurable.mul ?_ ?_
  · exact Measurable.ite (measurableSet_natExtWord_eq R w) measurable_const measurable_const
  · exact continuous_torusChar.measurable.comp
      ((measurable_snd.fst.const_mul _).add (measurable_snd.snd.const_mul _))

lemma norm_monoAt_le (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) (α : ℝ) (n j : ℕ) :
    ‖monoAt R w r s α n j‖ ≤ 1 := by
  unfold monoAt
  rw [norm_mul, norm_torusChar, mul_one]
  by_cases h : windowWord R α j = w <;> simp [h]

lemma norm_monoEval_le (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) (z : (ℝ × ℝ) × ℝ × ℝ) :
    ‖monoEval R w r s z‖ ≤ 1 := by
  unfold monoEval
  rw [norm_mul, norm_torusChar, mul_one]
  by_cases h : natExtWord R z.1 = w <;> simp [h]

/-! ### `μ̂₀` is a finite measure -/

lemma measurableSet_hatBox :
    MeasurableSet (((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
      Set ((ℝ × ℝ) × ℝ × ℝ)) :=
  (measurableSet_Ioo.prod measurableSet_Ioo).prod (measurableSet_Ioo.prod measurableSet_Ioo)

lemma volume_hatBox :
    volume (((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
      Set ((ℝ × ℝ) × ℝ × ℝ)) = 1 := by
  simp [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]

instance isFiniteMeasure_hatMu0 : IsFiniteMeasure hatMu0 := by
  constructor
  rw [hatMu0, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hbound : ∀ᵐ z ∂(volume.restrict
      (((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
        Set ((ℝ × ℝ) × ℝ × ℝ))),
      ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2))
        ≤ ENNReal.ofReal (1 / Real.log 2) := by
    filter_upwards [ae_restrict_mem measurableSet_hatBox] with z hz
    have hx : z.1.1 ∈ Ioo (0 : ℝ) 1 := hz.1.1
    have hy : z.1.2 ∈ Ioo (0 : ℝ) 1 := hz.1.2
    have hp : (0 : ℝ) < z.1.1 * z.1.2 := mul_pos hx.1 hy.1
    have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (1 : ℝ) ≤ (1 + z.1.1 * z.1.2) ^ 2 := by nlinarith
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ (by nlinarith) hl]
    nlinarith
  calc ∫⁻ z, ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2))
          ∂(volume.restrict (((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ
            (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) : Set ((ℝ × ℝ) × ℝ × ℝ)))
      ≤ ∫⁻ _, ENNReal.ofReal (1 / Real.log 2)
          ∂(volume.restrict (((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ
            (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) : Set ((ℝ × ℝ) × ℝ × ℝ))) :=
        lintegral_mono_ae hbound
    _ = ENNReal.ofReal (1 / Real.log 2) * 1 := by
        rw [lintegral_const, Measure.restrict_apply_univ, volume_hatBox]
    _ < ⊤ := by simp [ENNReal.ofReal_lt_top]

/-! ### Integrability -/

lemma integrable_monoEval (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) :
    Integrable (fun z => monoEval R w r s z) hatMu0 :=
  memLp_one_iff_integrable.mp (MemLp.of_bound
    (measurable_monoEval R w r s).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => norm_monoEval_le R w r s z))

instance isFiniteMeasure_restrict_Ioo :
    IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  simp

lemma integrable_monoAt_mul (R : ℕ) (w w' : Fin (2 * R) → ℕ) (r s r' s' : ℤ) (n j k : ℕ) :
    IntegrableOn
      (fun α => monoAt R w r s α n j * monoAt R w' r' s' α n k) (Ioo (0 : ℝ) 1) volume := by
  refine memLp_one_iff_integrable.mp (MemLp.of_bound
    (((measurable_monoAt R w r s n j).mul
      (measurable_monoAt R w' r' s' n k)).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun α => ?_))
  rw [norm_mul]
  have h1 := norm_monoAt_le R w r s α n j
  have h2 := norm_monoAt_le R w' r' s' α n k
  nlinarith [norm_nonneg (monoAt R w r s α n j), norm_nonneg (monoAt R w' r' s' α n k)]

/-! ### Linearity of the two means -/

lemma stationaryIntegral_eq_sum {R K : ℕ} (U : WindowSymbol R K) :
    U.stationaryIntegral
      = ∑ t ∈ symIdx U, U.coeff t.1 t.2.1 t.2.2 * monoStationary R t.1 t.2.1 t.2.2 := by
  unfold WindowSymbol.stationaryIntegral monoStationary
  simp only [eval_eq_sum U]
  rw [integral_finset_sum _ fun t _ => (integrable_monoEval R t.1 t.2.1 t.2.2).const_mul _]
  exact Finset.sum_congr rfl fun t _ => integral_const_mul _ _

lemma integral_at_mul_at {R K : ℕ} (U V : WindowSymbol R K) (n j k : ℕ) :
    (∫ α in Ioo (0 : ℝ) 1, U.at α n j * V.at α n k)
      = ∑ t ∈ symIdx U, ∑ t' ∈ symIdx V,
          (U.coeff t.1 t.2.1 t.2.2 * V.coeff t'.1 t'.2.1 t'.2.2) *
            ∫ α in Ioo (0 : ℝ) 1,
              monoAt R t.1 t.2.1 t.2.2 α n j * monoAt R t'.1 t'.2.1 t'.2.2 α n k := by
  have hpt : ∀ α : ℝ, U.at α n j * V.at α n k
      = ∑ t ∈ symIdx U, ∑ t' ∈ symIdx V,
          (U.coeff t.1 t.2.1 t.2.2 * V.coeff t'.1 t'.2.1 t'.2.2) *
            (monoAt R t.1 t.2.1 t.2.2 α n j * monoAt R t'.1 t'.2.1 t'.2.2 α n k) := by
    intro α
    rw [at_eq_sum U α n j, at_eq_sum V α n k, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => by ring
  simp only [hpt]
  rw [integral_finset_sum _ fun t _ =>
    integrable_finset_sum _ fun t' _ =>
      (integrable_monoAt_mul R t.1 t'.1 t.2.1 t.2.2 t'.2.1 t'.2.2 n j k).const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_finset_sum _ fun t' _ =>
    (integrable_monoAt_mul R t.1 t'.1 t.2.1 t.2.2 t'.2.1 t'.2.2 n j k).const_mul _]
  exact Finset.sum_congr rfl fun t' _ => integral_const_mul _ _

/-! ### From monomial estimates to the full two-block estimate -/

lemma two_block_bound_of_mono {R K : ℕ} (U V : WindowSymbol R K) (n j k : ℕ) (M : ℝ)
    (h : ∀ t ∈ symIdx U, ∀ t' ∈ symIdx V,
      ‖(∫ α in Ioo (0 : ℝ) 1,
            monoAt R t.1 t.2.1 t.2.2 α n j * monoAt R t'.1 t'.2.1 t'.2.2 α n k)
          - monoStationary R t.1 t.2.1 t.2.2 * monoStationary R t'.1 t'.2.1 t'.2.2‖ ≤ M) :
    ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n j * V.at α n k)
        - U.stationaryIntegral * V.stationaryIntegral‖
      ≤ (∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
          * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * M := by
  have hdiff : (∫ α in Ioo (0 : ℝ) 1, U.at α n j * V.at α n k)
      - U.stationaryIntegral * V.stationaryIntegral
      = ∑ t ∈ symIdx U, ∑ t' ∈ symIdx V,
          (U.coeff t.1 t.2.1 t.2.2 * V.coeff t'.1 t'.2.1 t'.2.2) *
            ((∫ α in Ioo (0 : ℝ) 1,
                monoAt R t.1 t.2.1 t.2.2 α n j * monoAt R t'.1 t'.2.1 t'.2.2 α n k)
              - monoStationary R t.1 t.2.1 t.2.2 * monoStationary R t'.1 t'.2.1 t'.2.2) := by
    rw [integral_at_mul_at U V n j k, stationaryIntegral_eq_sum U, stationaryIntegral_eq_sum V,
      Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t' _ => by ring
  rw [hdiff]
  have key : (∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
        * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * M
      = ∑ t ∈ symIdx U, ∑ t' ∈ symIdx V,
          ‖U.coeff t.1 t.2.1 t.2.2‖ * ‖V.coeff t'.1 t'.2.1 t'.2.2‖ * M := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_mul _ _ _
  rw [key]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun t ht => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun t' ht' => ?_)
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (h t ht t' ht') (by positivity)

/-! ## Two genuinely provable steps inside the core

These are the parts of Kwon's proof of 4.2 that need no mixing input.
-/

/-! ### Continuant growth and frequency domination -/

lemma denom_le_succ {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (j : ℕ) :
    denom α j ≤ denom α (j + 1) := by
  cases j with
  | zero => exact one_le_digit hα hirr 0
  | succ i =>
      have hrec : denom α (i + 2) = digit α (i + 1) * denom α (i + 1) + denom α i := rfl
      have h1 : 1 ≤ digit α (i + 1) := one_le_digit hα hirr (i + 1)
      have h2 : denom α (i + 1) ≤ digit α (i + 1) * denom α (i + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      rw [hrec]
      exact le_trans h2 (Nat.le_add_right _ _)

lemma denom_mono {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    Monotone (denom α) :=
  monotone_nat_of_le_succ (denom_le_succ hα hirr)

/-- The Fibonacci doubling of the continuants: `q_{j+2} ≥ 2 q_j`. -/
lemma two_mul_denom_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (j : ℕ) :
    2 * denom α j ≤ denom α (j + 2) := by
  have hrec : denom α (j + 2) = digit α (j + 1) * denom α (j + 1) + denom α j := rfl
  have h1 : 1 ≤ digit α (j + 1) := one_le_digit hα hirr (j + 1)
  have h2 : denom α j ≤ denom α (j + 1) := denom_le_succ hα hirr j
  have h3 : denom α (j + 1) ≤ digit α (j + 1) * denom α (j + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [hrec]
  omega

lemma pow_two_mul_denom_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (j m : ℕ) : 2 ^ m * denom α j ≤ denom α (j + 2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hidx : j + 2 * (m + 1) = j + 2 * m + 2 := by ring
      rw [hidx]
      calc 2 ^ (m + 1) * denom α j = 2 * (2 ^ m * denom α j) := by ring
        _ ≤ 2 * denom α (j + 2 * m) := Nat.mul_le_mul_left 2 ih
        _ ≤ denom α (j + 2 * m + 2) := two_mul_denom_le hα hirr _

/-- `|Q_j(r,s)| ≤ (|r| + |s|) q_j`, the trivial upper bound on a frequency (33). -/
lemma abs_Qfreq_le {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (j : ℕ) (hj : 1 ≤ j) (r s : ℤ) :
    |((Qfreq α j r s : ℤ) : ℝ)| ≤ (|(r : ℝ)| + |(s : ℝ)|) * (denom α j : ℝ) := by
  have hmono : denom α (j - 1) ≤ denom α j := denom_mono hα hirr (by omega)
  have h1 : ((denom α (j - 1) : ℕ) : ℝ) ≤ ((denom α j : ℕ) : ℝ) := by exact_mod_cast hmono
  have h0 : (0 : ℝ) ≤ ((denom α (j - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ |(r : ℝ)| := abs_nonneg _
  have hs : (0 : ℝ) ≤ |(s : ℝ)| := abs_nonneg _
  unfold Qfreq
  push_cast
  set X : ℝ := ((denom α j : ℕ) : ℝ)
  set Y : ℝ := ((denom α (j - 1) : ℕ) : ℝ)
  calc |(s : ℝ) * X - (r : ℝ) * Y|
      = |(s : ℝ) * X + -((r : ℝ) * Y)| := by ring_nf
    _ ≤ |(s : ℝ) * X| + |-((r : ℝ) * Y)| := abs_add_le _ _
    _ = |(s : ℝ)| * X + |(r : ℝ)| * Y := by
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (le_trans h0 h1), abs_of_nonneg h0]
    _ ≤ (|(r : ℝ)| + |(s : ℝ)|) * X := by nlinarith

/-- **"Fibonacci growth makes the later frequency dominate the earlier one."**
If the later frequency is at least `η q_k` (Lemma 3.3) and the block gap is
`k - j ≥ 2m` with `2^m ≥ 2K/η`, i.e. `k - j ≥ CH` once `η = e^{-cH}`, then
the combined frequency of (33) is at least `½ η q_k`. -/
theorem later_frequency_dominates {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    {j k m : ℕ} (hj : 1 ≤ j) (hgap : j + 2 * m ≤ k)
    {r₁ s₁ r₂ s₂ : ℤ} {Kc η : ℝ}
    (hmode : |(r₁ : ℝ)| + |(s₁ : ℝ)| ≤ Kc)
    (hlow : η * (denom α k : ℝ) ≤ |((Qfreq α k r₂ s₂ : ℤ) : ℝ)|)
    (hm : 2 * Kc ≤ η * 2 ^ m) :
    (1 / 2) * η * (denom α k : ℝ)
      ≤ |(-1 : ℝ) ^ j * ((Qfreq α j r₁ s₁ : ℤ) : ℝ)
          + (-1 : ℝ) ^ k * ((Qfreq α k r₂ s₂ : ℤ) : ℝ)| := by
  have hqj0 : (0 : ℝ) ≤ ((denom α j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqk0 : (0 : ℝ) ≤ ((denom α k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hKc0 : (0 : ℝ) ≤ Kc := le_trans (by positivity) hmode
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hq : (2 : ℝ) ^ m * ((denom α j : ℕ) : ℝ) ≤ ((denom α k : ℕ) : ℝ) := by
    have h := le_trans (pow_two_mul_denom_le hα hirr j m) (denom_mono hα hirr hgap)
    exact_mod_cast h
  have hAbs : |(-1 : ℝ) ^ j * ((Qfreq α j r₁ s₁ : ℤ) : ℝ)| ≤ Kc * ((denom α j : ℕ) : ℝ) := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact le_trans (abs_Qfreq_le hα hirr j hj r₁ s₁) (by nlinarith)
  have hB : η * ((denom α k : ℕ) : ℝ) ≤ |(-1 : ℝ) ^ k * ((Qfreq α k r₂ s₂ : ℤ) : ℝ)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hlow
  have htri : ∀ A B : ℝ, |B| - |A| ≤ |A + B| := by
    intro A B
    have h := abs_add_le (A + B) (-A)
    rw [abs_neg, show A + B + -A = B by ring] at h
    linarith
  have hkey : Kc * ((denom α j : ℕ) : ℝ) ≤ (η / 2) * ((denom α k : ℕ) : ℝ) := by
    have e1 : Kc * ((2 : ℝ) ^ m * ((denom α j : ℕ) : ℝ)) ≤ Kc * ((denom α k : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hq hKc0
    have e2 : 2 * Kc * ((denom α k : ℕ) : ℝ) ≤ (η * 2 ^ m) * ((denom α k : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hm hqk0
    refine le_of_mul_le_mul_left ?_ h2m
    nlinarith
  have := htri ((-1 : ℝ) ^ j * ((Qfreq α j r₁ s₁ : ℤ) : ℝ))
    ((-1 : ℝ) ^ k * ((Qfreq α k r₂ s₂ : ℤ) : ℝ))
  linarith

/-! ### The exponent arithmetic of the retained descendants (referee note 5)

The manuscript's line "Since `2λt₋ = L + λk − 80λH + O(1)`, every retained
descendant satisfies `q_{t₋}² ≤ e^{−cH} n|Q|`" is exactly the computation
below.  It is stated with the rate left symbolic, which is what exposes the
compatibility the manuscript leaves implicit: the rate is `80λ − 3δ − c`,
and it is positive **iff** `c + 3δ < 80λ`.
-/

lemma retained_descendant_exponent
    {L H lam del cc A t k qt qk Q nn : ℝ}
    (hqt0 : 0 ≤ qt)
    (hqt : qt ≤ Real.exp (lam * t + del * H))
    (hqk : Real.exp (lam * k - del * H) ≤ qk)
    (hQ : (1 / 2) * Real.exp (-cc * H) * qk ≤ Q)
    (hnn : Real.exp L ≤ nn)
    (ht : 2 * (lam * t) = L + lam * k - 80 * lam * H + A) :
    qt ^ 2 ≤ 2 * Real.exp A * Real.exp (-(80 * lam - 3 * del - cc) * H) * (nn * Q) := by
  have hqk0 : 0 ≤ qk := le_trans (Real.exp_pos _).le hqk
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
  have hnn0 : 0 ≤ nn := le_trans (Real.exp_pos _).le hnn
  have h1 : qt ^ 2 ≤ Real.exp (L + lam * k - 80 * lam * H + A + 2 * (del * H)) := by
    calc qt ^ 2 ≤ (Real.exp (lam * t + del * H)) ^ 2 := by
          nlinarith [hqt0, hqt, (Real.exp_pos (lam * t + del * H)).le]
      _ = Real.exp ((lam * t + del * H) + (lam * t + del * H)) := by
          rw [pow_two, ← Real.exp_add]
      _ = Real.exp (L + lam * k - 80 * lam * H + A + 2 * (del * H)) := by
          congr 1; linarith
  have h2 : (1 / 2) * Real.exp (L + lam * k - cc * H - del * H) ≤ nn * Q := by
    have hinner : (1 / 2) * Real.exp (-cc * H) * Real.exp (lam * k - del * H)
        ≤ Q := le_trans (mul_le_mul_of_nonneg_left hqk (by positivity)) hQ
    have hsplit : Real.exp (L + lam * k - cc * H - del * H)
        = Real.exp L * Real.exp (-cc * H) * Real.exp (lam * k - del * H) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc (1 / 2) * Real.exp (L + lam * k - cc * H - del * H)
        = Real.exp L * ((1 / 2) * Real.exp (-cc * H) * Real.exp (lam * k - del * H)) := by
          rw [hsplit]; ring
      _ ≤ nn * Q := mul_le_mul hnn hinner (by positivity) hnn0
  have hM : (0 : ℝ) < 2 * Real.exp A * Real.exp (-(80 * lam - 3 * del - cc) * H) := by positivity
  have h4 : 2 * Real.exp A * Real.exp (-(80 * lam - 3 * del - cc) * H)
        * ((1 / 2) * Real.exp (L + lam * k - cc * H - del * H))
      = Real.exp (L + lam * k - 80 * lam * H + A + 2 * (del * H)) := by
    rw [show (2 : ℝ) * Real.exp A * Real.exp (-(80 * lam - 3 * del - cc) * H)
          * ((1 / 2) * Real.exp (L + lam * k - cc * H - del * H))
        = Real.exp A * (Real.exp (-(80 * lam - 3 * del - cc) * H)
          * Real.exp (L + lam * k - cc * H - del * H)) by ring,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc qt ^ 2 ≤ Real.exp (L + lam * k - 80 * lam * H + A + 2 * (del * H)) := h1
    _ = 2 * Real.exp A * Real.exp (-(80 * lam - 3 * del - cc) * H)
          * ((1 / 2) * Real.exp (L + lam * k - cc * H - del * H)) := h4.symm
    _ ≤ 2 * Real.exp A * Real.exp (-(80 * lam - 3 * del - cc) * H) * (nn * Q) :=
        mul_le_mul_of_nonneg_left h2 hM.le

/-- **Referee note 5, made explicit.**  The decay rate produced by
`retained_descendant_exponent` at the Lévy constant `λ` is positive exactly
when the anti-concentration constant `c` and the denominator-deviation
constant `δ` satisfy `c + 3δ < 80λ`. -/
lemma retained_rate_pos_iff {del cc : ℝ} :
    0 < 80 * lyapunov - 3 * del - cc ↔ ACCompatible cc del := by
  unfold ACCompatible
  constructor <;> intro h <;> linarith

/-! ## The single sorried input: the monomial form of (34) -/

/-- **Monomial core of Proposition 4.2.**  This is the content of Kwon's
proof of 4.2 ("It suffices to treat monomials"): the three-case analysis
that uses Lemma 3.3 (`shrinking_anti_concentration`, proved), Lemma 3.4
(`descendant_phase_small`, proved), the denominator deviation (20), and -
the input not yet available in this development, Lemma 3.2's conditional
two-sided Gauss mixing across the block gap.  The constants are allowed to
depend on the radius `R`, the mode cap `K` and the two finite word sets,
exactly as in the manuscript, where `U` and `V` are fixed.

The anti-concentration constant `c` here is the `c` of `η = e^{-cH}`; by
`acCompatible_of_le_one` every `c ≤ 1` meets the compatibility constraint
`c + 3δ < 80λ` of referee note 5, so the existential quantifier over `c`
absorbs it and it constrains nothing downstream. -/
theorem two_block_monomial_core (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ modeBox K,
        (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
            ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
                    monoAt R w m.1 m.2 α n p.1 * monoAt R w' m'.1 m'.2 α n p.2)
                  - monoStationary R w m.1 m.2 * monoStationary R w' m'.1 m'.2‖
                ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                        + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
          ≤ C * Lnorm n * Hscale n := by
  sorry

/-! ## Proposition 4.2 -/

/-- **Proposition 4.2** (Two-block factorization), display (34).
Statement reproduced token-identically from `Kwon1002/Section4.lean`. -/
theorem prop_4_2_two_block_factorization {R K : ℕ} (U V : WindowSymbol R K) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                      + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n := by
  classical
  obtain ⟨C₀, c, ρ, hC₀, hc, hρ0, hρ1, hcore⟩ := two_block_monomial_core R K U.words V.words
  set C : ℝ := max 1 (max
      ((∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
        * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀)
      ((((symIdx U).card * (symIdx V).card : ℕ) : ℝ) * C₀)) with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCA : (∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
      * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀ ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCN : (((symIdx U).card * (symIdx V).card : ℕ) : ℝ) * C₀ ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, c, ρ, by linarith, hc, hρ0, hρ1, ?_⟩
  filter_upwards [hcore, eventually_ge_atTop 1] with n hn hn1
  have hL : (0 : ℝ) ≤ Lnorm n := Real.log_nonneg (by exact_mod_cast hn1)
  have hH : (0 : ℝ) ≤ Hscale n := Real.rpow_nonneg hL _
  set E : ℝ := Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n)
      + ρ ^ (c * Hscale n) with hEdef
  have hEpos : 0 < E := by
    have h1 := Real.exp_pos (-c * Real.sqrt (Lnorm n))
    have h2 := Real.exp_pos (-c * Hscale n)
    have h3 := Real.rpow_pos_of_pos hρ0 (c * Hscale n)
    rw [hEdef]; linarith
  set Bad : (((Fin (2 * R) → ℕ) × ℤ × ℤ) × ((Fin (2 * R) → ℕ) × ℤ × ℤ)) → Finset (ℕ × ℕ) :=
    fun q => (bulkPairs n).filter (fun p =>
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
            monoAt R q.1.1 q.1.2.1 q.1.2.2 α n p.1 * monoAt R q.2.1 q.2.2.1 q.2.2.2 α n p.2)
          - monoStationary R q.1.1 q.1.2.1 q.1.2.2 * monoStationary R q.2.1 q.2.2.1 q.2.2.2‖
        ≤ C₀ * E) with hBad
  -- (a) each monomial pair contributes at most `C₀ L H` exceptional pairs
  have hIdx : ∀ q ∈ symIdx U ×ˢ symIdx V,
      ((Bad q).card : ℝ) ≤ C₀ * Lnorm n * Hscale n := by
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [symIdx, Finset.mem_product] at hq1 hq2
    have hcore' := hn q.1.1 hq1.1 q.1.2 hq1.2 q.2.1 hq2.1 q.2.2 hq2.2
    rw [hBad]
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    exact hcore'
  -- (b) the exceptional set of the pair `(U,V)` is covered by those of the monomials
  have hsub : {p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}
      ⊆ ↑((symIdx U ×ˢ symIdx V).biUnion Bad) := by
    rintro p ⟨hp1, hp2⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    by_contra hcon
    push_neg at hcon
    apply hp2
    have hmono : ∀ t ∈ symIdx U, ∀ t' ∈ symIdx V,
        ‖(∫ α in Ioo (0 : ℝ) 1,
              monoAt R t.1 t.2.1 t.2.2 α n p.1 * monoAt R t'.1 t'.2.1 t'.2.2 α n p.2)
            - monoStationary R t.1 t.2.1 t.2.2 * monoStationary R t'.1 t'.2.1 t'.2.2‖
          ≤ C₀ * E := by
      intro t ht t' ht'
      have hq := hcon (t, t') (Finset.mem_product.mpr ⟨ht, ht'⟩)
      simp only [hBad, Finset.mem_filter, not_and, not_not] at hq
      exact hq (Finset.mem_coe.mp hp1)
    calc ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖
        ≤ (∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * (C₀ * E) :=
          two_block_bound_of_mono U V n p.1 p.2 (C₀ * E) hmono
      _ = ((∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀) * E := by ring
      _ ≤ C * E := mul_le_mul_of_nonneg_right hCA hEpos.le
  -- (c) count
  calc (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}).ncard : ℝ)
      ≤ ((((symIdx U ×ˢ symIdx V).biUnion Bad).card : ℕ) : ℝ) := by
        have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        rw [Set.ncard_coe_finset] at h
        exact_mod_cast h
    _ ≤ ∑ q ∈ symIdx U ×ˢ symIdx V, ((Bad q).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ symIdx U ×ˢ symIdx V, C₀ * Lnorm n * Hscale n := Finset.sum_le_sum hIdx
    _ = (((symIdx U).card * (symIdx V).card : ℕ) : ℝ) * C₀ * (Lnorm n * Hscale n) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ C * (Lnorm n * Hscale n) :=
        mul_le_mul_of_nonneg_right hCN (mul_nonneg hL hH)
    _ = C * Lnorm n * Hscale n := by ring


end

end Prop42

end Kwon1002
