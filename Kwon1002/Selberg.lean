import Kwon1002.Fejer

/-!
# One-sided trigonometric approximants: a majorant/minorant pair

`Kwon1002/Fejer.lean` builds the Fejér kernel and the Fejér mean, and
`Kwon1002/JacksonGate.lean` proves that an *indicator* cannot lie in the symbol
class `P_D(L)` of display (24): members of that class are trigonometric
polynomials, hence continuous, hence constant if two-valued.  The residuals of
§5, however, need the one-level joint law `OneLevelLaw.oneLevel_joint_law`
*at an indicator*.

Fejér means alone do not close that loop.  `Fejer.fejerPoly_L1_error_le`
measures the approximation error in `L¹` of the phase variable **under
Lebesgue measure on the fundamental cell**, whereas the argument has to control
it under the law of `(a_{j+1}(α), θ_j(α))` induced by Lebesgue in `α` — which
is the very object being computed.  What removes the circularity is a pair of
trigonometric polynomials that **bracket** the indicator,

  `S⁻ ≤ 1_B ≤ S⁺`,

because then the unknown law is squeezed between two quantities the one-level
law *can* evaluate, and the error is measured by the single number
`∫(S⁺ − S⁻)` against Lebesgue measure alone.

## The construction

This is the trapezoidal (Vaaler-style) route rather than Beurling–Selberg, and
it is run through the kernel that is already proved, which makes the degree
bookkeeping free: a Fejér mean of degree `N` is a trigonometric polynomial of
degree `N` **by construction** (`Fejer.fejerPoly` is defined by its coefficient
list), so no separate truncation argument is needed.

Fix `δ > 0` and set `η = η(N,δ) = 1/(4(N+1)δ²)` (`farTail`).  Let `u` be the
periodised indicator, `u⁺` its closed `δ`-thickening and `u⁻` its `δ`-erosion.
Then, writing `σ_N` for the Fejér mean,

* `u ≤ σ_N(u⁺) + η`  (`le_realConv_add_farTail`), and
* `σ_N(u⁻) − η ≤ u`  (`realConv_sub_farTail_le`).

The proof is one line of measure theory once the cell is split at distance `δ`
from the origin: on the near part the thickening dominates `u` *pointwise
after translation*, and the kernel has mass `≥ 1 − η` there; on the far part
the kernel has mass `≤ η` and the symbol is trapped in `[0,1]`.  The constant
`η` therefore pays for the whole kernel tail at once, and the estimate needs no
first moment of the kernel — which is exactly the quantity whose logarithmic
divergence costs the Fejér mean its classical rate (see the rate note in
`Kwon1002/Fejer.lean`).

Because `σ_N` is linear and reproduces constants against the unit mass of the
kernel (`realConv_add_const`), the two shifts can be folded into the symbols
themselves: `majSymbol` is `u⁺ + η` and `minSymbol` is `u⁻ − η`, and then

  `σ_N(minSymbol) ≤ u ≤ σ_N(majSymbol)` pointwise, everywhere.

## The three budgets

* **degree** `N`, by construction;
* **`L¹` gap** `∫₀¹(σ_N(majSymbol) − σ_N(minSymbol)) = ∫₀¹(u⁺ − u⁻) + 2η`
  (`integral_realConv`, `bracket_gap`), the first term being the measure of the
  set where membership in `B` is unstable at scale `δ`;
* **`ℓ¹` coefficient mass** `≤ (2N+1)(1+η)` (`l1_majSymbol_le`,
  `l1_minSymbol_le`), which is what display (24) budgets, and which
  `Fejer.isInPD_fejerPoly` converts into membership of `P_D(L)`
  (`isInPD_maj`, `isInPD_min`).

For `B` a union of `m` intervals, `IntervalClass.exists_goodSet` turns the jump
count into the `L¹` gap: `∫₀¹(u⁺ − u⁻) ≤ (4m+2)·2δ` (`bracket_gap_intervals`),
so the pair has gap `≤ (8m+4)δ + 2η` at degree `N`.  Choosing `N ≍ δ^{-3}`
makes both terms `O(δ)`, at coefficient mass `O(N)` — the shape display (24)
budgets by `L^D`.

Nothing here is circular: every statement is an inequality between explicit
functions and Lebesgue integrals over `(0,1)`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002
namespace Selberg

noncomputable section

/-! ## Part 1, splitting the fundamental cell at distance `δ` from the origin -/

/-- The points of the fundamental cell within `δ` of the origin of the circle. -/
def nearSet (δ : ℝ) : Set ℝ := Ioo (0 : ℝ) 1 ∩ {t : ℝ | min t (1 - t) ≤ δ}

/-- The points of the fundamental cell at circle distance more than `δ` from
the origin. -/
def farSet (δ : ℝ) : Set ℝ := Ioo (0 : ℝ) 1 \ {t : ℝ | min t (1 - t) ≤ δ}

/-- The whole mass the Fejér kernel can put outside the `δ`-neighbourhood of
the origin: `η(N,δ) = 1/(4(N+1)δ²)`.

This is the crude form of the concentration bound — the pointwise bound
`Fejer.fejerKernel_le_of_mem` at its worst point, times the mass `1` of the
cell — and it is deliberately crude: the sharp `1/(2(N+1)δ)` would need the
first moment of the kernel, and nothing downstream cares, because `N` is free. -/
def farTail (N : ℕ) (δ : ℝ) : ℝ := 1 / (4 * ((N : ℝ) + 1) * δ ^ 2)

lemma farTail_nonneg (N : ℕ) (δ : ℝ) : 0 ≤ farTail N δ := by
  unfold farTail; positivity

lemma measurableSet_dist_le (δ : ℝ) : MeasurableSet {t : ℝ | min t (1 - t) ≤ δ} :=
  measurableSet_le (measurable_id.min (measurable_const.sub measurable_id)) measurable_const

lemma measurableSet_nearSet (δ : ℝ) : MeasurableSet (nearSet δ) :=
  measurableSet_Ioo.inter (measurableSet_dist_le δ)

lemma measurableSet_farSet (δ : ℝ) : MeasurableSet (farSet δ) :=
  measurableSet_Ioo.diff (measurableSet_dist_le δ)

lemma nearSet_subset (δ : ℝ) : nearSet δ ⊆ Ioo (0 : ℝ) 1 := fun _ h => h.1

lemma farSet_subset (δ : ℝ) : farSet δ ⊆ Ioo (0 : ℝ) 1 := fun _ h => h.1

lemma mem_nearSet {δ t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (h : min t (1 - t) ≤ δ) :
    t ∈ nearSet δ := ⟨ht, h⟩

/-- The far part carries kernel mass at most `η`. -/
theorem integral_fejerKernel_farSet_le (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in farSet δ, Fejer.fejerKernel N t) ≤ farTail N δ := by
  have hint : IntegrableOn (Fejer.fejerKernel N) (farSet δ) :=
    (Fejer.integrableOn_fejerKernel N).mono_set (farSet_subset δ)
  have hle : ∀ t ∈ farSet δ, Fejer.fejerKernel N t ≤ farTail N δ := by
    rintro t ⟨ht, htf⟩
    simp only [Set.mem_setOf_eq, not_le] at htf
    have h := Fejer.fejerKernel_le_of_mem N ht.1 ht.2
    refine h.trans ?_
    unfold farTail
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hd : 0 < min t (1 - t) := lt_min ht.1 (by linarith [ht.2])
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : δ ^ 2 ≤ (min t (1 - t)) ^ 2 := by nlinarith
    nlinarith
  have hvol : (volume (farSet δ)).toReal ≤ 1 := by
    have := measure_mono (farSet_subset δ) (μ := (volume : Measure ℝ))
    have h1 : volume (farSet δ) ≤ 1 := by
      simpa [Real.volume_Ioo] using this
    calc (volume (farSet δ)).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono (by norm_num) h1
      _ = 1 := by simp
  calc (∫ t in farSet δ, Fejer.fejerKernel N t)
      ≤ ∫ _t in farSet δ, farTail N δ := by
        refine setIntegral_mono_on hint ?_ (measurableSet_farSet δ) hle
        exact Fejer.integrableOn_const_of_ne_top
          ((lt_of_le_of_lt (measure_mono (farSet_subset δ)) measure_Ioo_lt_top).ne) _
    _ = (volume (farSet δ)).toReal * farTail N δ := by
        rw [setIntegral_const, smul_eq_mul]; rfl
    _ ≤ 1 * farTail N δ :=
        mul_le_mul_of_nonneg_right hvol (farTail_nonneg N δ)
    _ = farTail N δ := one_mul _

/-- The near and far parts split the kernel's unit mass. -/
theorem integral_fejerKernel_split (N : ℕ) (δ : ℝ) :
    (∫ t in nearSet δ, Fejer.fejerKernel N t) + (∫ t in farSet δ, Fejer.fejerKernel N t) = 1 := by
  have h := MeasureTheory.integral_inter_add_diff
    (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1)
    (t := {t : ℝ | min t (1 - t) ≤ δ}) (f := Fejer.fejerKernel N)
    (measurableSet_dist_le δ) (Fejer.integrableOn_fejerKernel N)
  rw [← Fejer.integral_fejerKernel N]
  exact h

lemma integral_fejerKernel_nearSet_nonneg (N : ℕ) (δ : ℝ) :
    0 ≤ ∫ t in nearSet δ, Fejer.fejerKernel N t := by
  refine setIntegral_nonneg (measurableSet_nearSet δ) fun t _ => Fejer.fejerKernel_nonneg N t

lemma integral_fejerKernel_farSet_nonneg (N : ℕ) (δ : ℝ) :
    0 ≤ ∫ t in farSet δ, Fejer.fejerKernel N t := by
  refine setIntegral_nonneg (measurableSet_farSet δ) fun t _ => Fejer.fejerKernel_nonneg N t

/-- The near part carries kernel mass at least `1 − η`. -/
theorem integral_fejerKernel_nearSet_ge (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    1 - farTail N δ ≤ ∫ t in nearSet δ, Fejer.fejerKernel N t := by
  have hs := integral_fejerKernel_split N δ
  have hf := integral_fejerKernel_farSet_le N hδ
  linarith

/-- The near part carries kernel mass at most `1`. -/
theorem integral_fejerKernel_nearSet_le_one (N : ℕ) (δ : ℝ) :
    (∫ t in nearSet δ, Fejer.fejerKernel N t) ≤ 1 := by
  have hs := integral_fejerKernel_split N δ
  have hf := integral_fejerKernel_farSet_nonneg N δ
  linarith

/-! ## Part 2, the Fejér mean of a real symbol, read as a convolution

`Fejer.fejerPoly` is complex-valued, because display (24)'s class carries
complex coefficients.  The bracketing inequalities are inequalities between
*real* numbers, so the real form of the same object is introduced here and
`fejerPoly_ofReal` identifies the two. -/

/-- A measurable, `1`-periodic, `M`-bounded **real** symbol: the real shadow of
`Fejer.IsPerBdd`. -/
structure IsPerBddR (u : ℝ → ℝ) (M : ℝ) : Prop where
  meas : Measurable u
  per : Function.Periodic u 1
  bdd : ∀ x, |u x| ≤ M

lemma IsPerBddR.nonneg {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) : 0 ≤ M :=
  le_trans (abs_nonneg _) (hu.bdd 0)

/-- The complex form, so that everything proved in `Kwon1002/Fejer.lean`
applies verbatim. -/
lemma IsPerBddR.toC {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) :
    Fejer.IsPerBdd (fun x => ((u x : ℝ) : ℂ)) M where
  meas := Complex.measurable_ofReal.comp hu.meas
  per := by intro x; simp only [hu.per x]
  bdd := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hu.bdd x

/-- The Fejér mean of a real symbol, in real form. -/
def realConv (N : ℕ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, u (θ - t) * Fejer.fejerKernel N t

lemma integrableOn_shift_kernel {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) (N : ℕ) (θ : ℝ)
    {S : Set ℝ} (hS : S ⊆ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun t => u (θ - t) * Fejer.fejerKernel N t) S := by
  refine IntegrableOn.mono_set ?_ hS
  have hmeas : Measurable fun t : ℝ => u (θ - t) * Fejer.fejerKernel N t :=
    (hu.meas.comp (measurable_const.sub measurable_id)).mul
      (Fejer.continuous_fejerKernel N).measurable
  refine Integrable.mono' ((Fejer.integrableOn_fejerKernel N).const_mul M)
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Fejer.fejerKernel_nonneg N t)]
  exact mul_le_mul_of_nonneg_right (hu.bdd _) (Fejer.fejerKernel_nonneg N t)

/-- The near/far split of the convolution. -/
lemma realConv_split {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) (N : ℕ) (δ θ : ℝ) :
    (∫ t in nearSet δ, u (θ - t) * Fejer.fejerKernel N t)
      + (∫ t in farSet δ, u (θ - t) * Fejer.fejerKernel N t) = realConv N u θ :=
  MeasureTheory.integral_inter_add_diff (measurableSet_dist_le δ)
    (integrableOn_shift_kernel hu N θ (le_refl _))

/-- **The majorant inequality.**  If `v` dominates `u θ` after every translation
of circle-size at most `δ`, and `v ≥ 0`, then the Fejér mean of `v` recovers
`u θ` up to the kernel tail `η(N,δ)`. -/
theorem le_realConv_add_farTail (N : ℕ) {δ : ℝ} (hδ : 0 < δ) {u v : ℝ → ℝ} {M : ℝ}
    (hv : IsPerBddR v M) (hv0 : ∀ x, 0 ≤ v x)
    (hu0 : 0 ≤ u) (hu1 : ∀ x, u x ≤ 1) (θ : ℝ)
    (hdom : ∀ t ∈ nearSet δ, u θ ≤ v (θ - t)) :
    u θ ≤ realConv N v θ + farTail N δ := by
  have hnearInt : IntegrableOn (fun t => v (θ - t) * Fejer.fejerKernel N t) (nearSet δ) :=
    integrableOn_shift_kernel hv N θ (nearSet_subset δ)
  have hnearConst : IntegrableOn (fun t => u θ * Fejer.fejerKernel N t) (nearSet δ) :=
    ((Fejer.integrableOn_fejerKernel N).mono_set (nearSet_subset δ)).const_mul _
  have hnear : u θ * (∫ t in nearSet δ, Fejer.fejerKernel N t)
      ≤ ∫ t in nearSet δ, v (θ - t) * Fejer.fejerKernel N t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hnearConst hnearInt (measurableSet_nearSet δ) fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hdom t ht) (Fejer.fejerKernel_nonneg N t)
  have hfar : 0 ≤ ∫ t in farSet δ, v (θ - t) * Fejer.fejerKernel N t := by
    refine setIntegral_nonneg (measurableSet_farSet δ) fun t _ => ?_
    exact mul_nonneg (hv0 _) (Fejer.fejerKernel_nonneg N t)
  have hsplit := realConv_split hv N δ θ
  have hmass := integral_fejerKernel_nearSet_ge N (δ := δ) hδ
  have hu0θ : 0 ≤ u θ := hu0 θ
  have hη := farTail_nonneg N δ
  nlinarith [hu1 θ]

/-- **The minorant inequality.**  If `v` is dominated by `u θ` after every
translation of circle-size at most `δ`, and `v ≤ 1`, then the Fejér mean of `v`
undershoots `u θ` by at most the kernel tail `η(N,δ)`. -/
theorem realConv_sub_farTail_le (N : ℕ) {δ : ℝ} (hδ : 0 < δ) {u v : ℝ → ℝ} {M : ℝ}
    (hv : IsPerBddR v M) (hv1 : ∀ x, v x ≤ 1)
    (hu0 : 0 ≤ u) (θ : ℝ)
    (hdom : ∀ t ∈ nearSet δ, v (θ - t) ≤ u θ) :
    realConv N v θ - farTail N δ ≤ u θ := by
  have hnearInt : IntegrableOn (fun t => v (θ - t) * Fejer.fejerKernel N t) (nearSet δ) :=
    integrableOn_shift_kernel hv N θ (nearSet_subset δ)
  have hnearConst : IntegrableOn (fun t => u θ * Fejer.fejerKernel N t) (nearSet δ) :=
    ((Fejer.integrableOn_fejerKernel N).mono_set (nearSet_subset δ)).const_mul _
  have hnear : (∫ t in nearSet δ, v (θ - t) * Fejer.fejerKernel N t)
      ≤ u θ * (∫ t in nearSet δ, Fejer.fejerKernel N t) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hnearInt hnearConst (measurableSet_nearSet δ) fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hdom t ht) (Fejer.fejerKernel_nonneg N t)
  have hfarInt : IntegrableOn (fun t => v (θ - t) * Fejer.fejerKernel N t) (farSet δ) :=
    integrableOn_shift_kernel hv N θ (farSet_subset δ)
  have hfarConst : IntegrableOn (fun t => Fejer.fejerKernel N t) (farSet δ) :=
    (Fejer.integrableOn_fejerKernel N).mono_set (farSet_subset δ)
  have hfar : (∫ t in farSet δ, v (θ - t) * Fejer.fejerKernel N t)
      ≤ ∫ t in farSet δ, Fejer.fejerKernel N t := by
    refine setIntegral_mono_on hfarInt hfarConst (measurableSet_farSet δ) fun t ht => ?_
    calc v (θ - t) * Fejer.fejerKernel N t ≤ 1 * Fejer.fejerKernel N t :=
          mul_le_mul_of_nonneg_right (hv1 _) (Fejer.fejerKernel_nonneg N t)
      _ = Fejer.fejerKernel N t := one_mul _
  have hsplit := realConv_split hv N δ θ
  have hmass := integral_fejerKernel_nearSet_le_one N δ
  have hmass0 := integral_fejerKernel_nearSet_nonneg N δ
  have hfarle := integral_fejerKernel_farSet_le N (δ := δ) hδ
  have hu0θ : 0 ≤ u θ := hu0 θ
  nlinarith

/-- The Fejér mean reproduces an added constant, because the kernel has unit
mass.  This is what lets the two tail shifts be folded into the symbols. -/
lemma realConv_add_const {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) (N : ℕ) (c θ : ℝ) :
    realConv N (fun x => u x + c) θ = realConv N u θ + c := by
  have hpt : ∀ t : ℝ, (u (θ - t) + c) * Fejer.fejerKernel N t
      = u (θ - t) * Fejer.fejerKernel N t + c * Fejer.fejerKernel N t := by
    intro t; ring
  unfold realConv
  simp only [hpt]
  rw [integral_add (integrableOn_shift_kernel hu N θ (le_refl _))
      ((Fejer.integrableOn_fejerKernel N).const_mul c),
    integral_const_mul, Fejer.integral_fejerKernel, mul_one]

/-! ## Part 3, the real convolution *is* a trigonometric polynomial

Everything above is measure theory.  What makes it usable inside display (24)
is that `realConv N u` is literally `Fejer.fejerPoly N` of the complexified
symbol, hence a trigonometric polynomial of degree `N` with a coefficient list
whose `ℓ¹` mass is already budgeted in `Kwon1002/Fejer.lean`. -/

/-- The real convolution is the Fejér mean of the complexified symbol. -/
theorem fejerPoly_ofReal {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) (N : ℕ) (θ : ℝ) :
    Fejer.fejerPoly N (fun x => ((u x : ℝ) : ℂ)) θ = ((realConv N u θ : ℝ) : ℂ) := by
  rw [Fejer.fejerPoly_eq_conv hu.toC N θ]
  unfold realConv
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  push_cast
  ring

/-- The Fejér mean of a real symbol is continuous, being the real part of a
trigonometric polynomial. -/
theorem continuous_realConv {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) (N : ℕ) :
    Continuous (realConv N u) := by
  have h : realConv N u = fun θ => (Fejer.fejerPoly N (fun x => ((u x : ℝ) : ℂ)) θ).re := by
    funext θ
    rw [fejerPoly_ofReal hu N θ, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp (Fejer.continuous_fejerPoly N _)

/-- The Fejér mean of a real symbol obeys the same bound as the symbol. -/
theorem abs_realConv_le {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) (N : ℕ) (θ : ℝ) :
    |realConv N u θ| ≤ M := by
  have h := Fejer.norm_fejerPoly_le hu.toC N θ
  rw [fejerPoly_ofReal hu N θ, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **The Fejér mean has the same mean as the symbol.**  Integrating the
coefficient list over the fundamental cell kills every nonzero mode and the
weight of the zero mode is `1`. -/
theorem integral_fejerPoly (N : ℕ) (f : ℝ → ℂ) :
    (∫ θ in Ioo (0 : ℝ) 1, Fejer.fejerPoly N f θ) = Fejer.fourierCoeff1 f 0 := by
  unfold Fejer.fejerPoly
  rw [integral_finset_sum _ (fun v _ => Fejer.integrable_mode v _)]
  have hterm : ∀ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (∫ θ in Ioo (0 : ℝ) 1,
          ((Fejer.fejerWeight N v : ℝ) : ℂ) * Fejer.fourierCoeff1 f v * torusChar ((v : ℝ) * θ))
        = if v = 0 then ((Fejer.fejerWeight N v : ℝ) : ℂ) * Fejer.fourierCoeff1 f v else 0 := by
    intro v _
    rw [integral_const_mul, Prop4Final.integral_torusChar_mode]
    by_cases hv : v = 0 <;> simp [hv]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.Icc (-(N : ℤ)) (N : ℤ)) (0 : ℤ)]
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp
  rw [if_pos h0]
  simp [Fejer.fejerWeight]

/-- **The mean is preserved**, in real form: this is the number that measures
the `L¹` gap between the two members of the bracketing pair. -/
theorem integral_realConv {u : ℝ → ℝ} {M : ℝ} (hu : IsPerBddR u M) (N : ℕ) :
    (∫ θ in Ioo (0 : ℝ) 1, realConv N u θ) = ∫ θ in Ioo (0 : ℝ) 1, u θ := by
  have hC : ((∫ θ in Ioo (0 : ℝ) 1, realConv N u θ : ℝ) : ℂ)
      = ((∫ θ in Ioo (0 : ℝ) 1, u θ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    have h1 : (∫ θ in Ioo (0 : ℝ) 1, ((realConv N u θ : ℝ) : ℂ))
        = ∫ θ in Ioo (0 : ℝ) 1, Fejer.fejerPoly N (fun x => ((u x : ℝ) : ℂ)) θ := by
      refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
      rw [fejerPoly_ofReal hu N θ]
    rw [h1, integral_fejerPoly]
    unfold Fejer.fourierCoeff1
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    rw [show -(((0 : ℤ) : ℝ) * t) = 0 by push_cast; ring, Prop4Final.torusChar_zero, mul_one]
  exact_mod_cast hC

/-! ## Part 4, the bracketing pair -/

/-- The majorant symbol: the `δ`-thickened profile, lifted by the kernel tail. -/
def majSymbol (N : ℕ) (δ : ℝ) (v : ℝ → ℝ) : ℝ → ℝ := fun θ => v θ + farTail N δ

/-- The minorant symbol: the `δ`-eroded profile, lowered by the kernel tail. -/
def minSymbol (N : ℕ) (δ : ℝ) (v : ℝ → ℝ) : ℝ → ℝ := fun θ => v θ + -farTail N δ

lemma isPerBddR_majSymbol {v : ℝ → ℝ} {M : ℝ} (hv : IsPerBddR v M) (N : ℕ) (δ : ℝ) :
    IsPerBddR (majSymbol N δ v) (M + farTail N δ) where
  meas := hv.meas.add_const _
  per := by intro x; simp only [majSymbol, hv.per x]
  bdd := by
    intro x
    have h := abs_le.mp (hv.bdd x)
    have hη := farTail_nonneg N δ
    rw [abs_le]
    simp only [majSymbol]
    constructor <;> linarith [h.1, h.2]

lemma isPerBddR_minSymbol {v : ℝ → ℝ} {M : ℝ} (hv : IsPerBddR v M) (N : ℕ) (δ : ℝ) :
    IsPerBddR (minSymbol N δ v) (M + farTail N δ) where
  meas := hv.meas.add_const _
  per := by intro x; simp only [minSymbol, hv.per x]
  bdd := by
    intro x
    have h := abs_le.mp (hv.bdd x)
    have hη := farTail_nonneg N δ
    rw [abs_le]
    simp only [minSymbol]
    constructor <;> linarith [h.1, h.2]

/-- **The majorant.**  `S⁺ = σ_N(u⁺ + η)` dominates `u` **everywhere**, with no
error term left over: the kernel tail has been paid for inside the symbol. -/
theorem le_realConv_majSymbol (N : ℕ) {δ : ℝ} (hδ : 0 < δ) {u v : ℝ → ℝ} {M : ℝ}
    (hv : IsPerBddR v M) (hv0 : ∀ x, 0 ≤ v x)
    (hu0 : 0 ≤ u) (hu1 : ∀ x, u x ≤ 1) (θ : ℝ)
    (hdom : ∀ t ∈ nearSet δ, u θ ≤ v (θ - t)) :
    u θ ≤ realConv N (majSymbol N δ v) θ := by
  have h : realConv N (majSymbol N δ v) θ = realConv N v θ + farTail N δ :=
    realConv_add_const hv N (farTail N δ) θ
  rw [h]
  exact le_realConv_add_farTail N hδ hv hv0 hu0 hu1 θ hdom

/-- **The minorant.**  `S⁻ = σ_N(u⁻ − η)` is dominated by `u` **everywhere**. -/
theorem realConv_minSymbol_le (N : ℕ) {δ : ℝ} (hδ : 0 < δ) {u v : ℝ → ℝ} {M : ℝ}
    (hv : IsPerBddR v M) (hv1 : ∀ x, v x ≤ 1)
    (hu0 : 0 ≤ u) (θ : ℝ)
    (hdom : ∀ t ∈ nearSet δ, v (θ - t) ≤ u θ) :
    realConv N (minSymbol N δ v) θ ≤ u θ := by
  have h : realConv N (minSymbol N δ v) θ = realConv N v θ + -farTail N δ :=
    realConv_add_const hv N (-farTail N δ) θ
  rw [h]
  have := realConv_sub_farTail_le N hδ hv hv1 hu0 θ hdom
  linarith

/-- **The `L¹` gap of the pair.**  The two trigonometric polynomials differ, in
mean over the fundamental cell, by the mean gap of the two profiles plus twice
the kernel tail — and by nothing else.  This is the number that replaces the
circular `L¹` estimate: it is computed against Lebesgue measure alone. -/
theorem integral_bracket_gap {up um : ℝ → ℝ} {M : ℝ}
    (hup : IsPerBddR up M) (hum : IsPerBddR um M) (N : ℕ) (δ : ℝ) :
    (∫ θ in Ioo (0 : ℝ) 1, realConv N (majSymbol N δ up) θ)
        - ∫ θ in Ioo (0 : ℝ) 1, realConv N (minSymbol N δ um) θ
      = ((∫ θ in Ioo (0 : ℝ) 1, up θ) - ∫ θ in Ioo (0 : ℝ) 1, um θ)
        + 2 * farTail N δ := by
  have hI : (volume : Measure ℝ).real (Ioo (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioo]
  have hupI : IntegrableOn up (Ioo (0 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := M) (by simp [Real.volume_Ioo])
      hup.meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hup.bdd x
  have humI : IntegrableOn um (Ioo (0 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := M) (by simp [Real.volume_Ioo])
      hum.meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hum.bdd x
  have hconst : IntegrableOn (fun _ : ℝ => farTail N δ) (Ioo (0 : ℝ) 1) :=
    Fejer.integrableOn_const_of_ne_top measure_Ioo_lt_top.ne _
  have hconst' : IntegrableOn (fun _ : ℝ => -farTail N δ) (Ioo (0 : ℝ) 1) :=
    Fejer.integrableOn_const_of_ne_top measure_Ioo_lt_top.ne _
  rw [integral_realConv (isPerBddR_majSymbol hup N δ) N,
    integral_realConv (isPerBddR_minSymbol hum N δ) N]
  unfold majSymbol minSymbol
  rw [integral_add hupI hconst, integral_add humI hconst',
    setIntegral_const, setIntegral_const, hI, smul_eq_mul, smul_eq_mul, one_mul, one_mul]
  ring

/-! ## Part 5, the two budgets display (24) reads

The degree is `N` by construction.  The coefficient mass and the class
membership are `Kwon1002/Fejer.lean`'s, applied to the bracketing symbols; they
are recorded here so that the pair can be handed to
`OneLevelLaw.oneLevel_joint_law` without reopening `Fejer`. -/

/-- The `ℓ¹` coefficient mass of the majorant, at one digit. -/
theorem l1_majSymbol_le {v : ℝ → ℝ} {M : ℝ} (hv : IsPerBddR v M) (N : ℕ) (δ : ℝ) :
    ∑ w ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖((Fejer.fejerWeight N w : ℝ) : ℂ)
          * Fejer.fourierCoeff1 (fun x => ((majSymbol N δ v x : ℝ) : ℂ)) w‖
      ≤ (2 * (N : ℝ) + 1) * (M + farTail N δ) :=
  Fejer.fejerCoeff_l1_le (isPerBddR_majSymbol hv N δ).toC N

/-- The `ℓ¹` coefficient mass of the minorant, at one digit. -/
theorem l1_minSymbol_le {v : ℝ → ℝ} {M : ℝ} (hv : IsPerBddR v M) (N : ℕ) (δ : ℝ) :
    ∑ w ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖((Fejer.fejerWeight N w : ℝ) : ℂ)
          * Fejer.fourierCoeff1 (fun x => ((minSymbol N δ v x : ℝ) : ℂ)) w‖
      ≤ (2 * (N : ℝ) + 1) * (M + farTail N δ) :=
  Fejer.fejerCoeff_l1_le (isPerBddR_minSymbol hv N δ).toC N

/-- **The majorant family lies in the class of display (24).**  Same three side
conditions as `Fejer.isInPD_fejerPoly`, with the bound of the symbol raised by
the kernel tail. -/
theorem isInPD_majSymbol (D L : ℝ) (A N : ℕ) (δ M : ℝ) (v : ℕ → ℝ → ℝ)
    (hv : ∀ a, IsPerBddR (v a) M)
    (hAle : (A : ℝ) ≤ L ^ D) (hNle : (N : ℝ) ≤ L ^ D)
    (hbudget : ((A : ℝ) + 1) * ((2 * (N : ℝ) + 1) * (M + farTail N δ)) ≤ L ^ D) :
    IsInPD D L (fun a θ => if a ≤ A then
      Fejer.fejerPoly N (fun x => ((majSymbol N δ (v a) x : ℝ) : ℂ)) θ else 0) :=
  Fejer.isInPD_fejerPoly D L A N (M + farTail N δ) _
    (fun a => (isPerBddR_majSymbol (hv a) N δ).toC) hAle hNle hbudget

/-- **The minorant family lies in the class of display (24).** -/
theorem isInPD_minSymbol (D L : ℝ) (A N : ℕ) (δ M : ℝ) (v : ℕ → ℝ → ℝ)
    (hv : ∀ a, IsPerBddR (v a) M)
    (hAle : (A : ℝ) ≤ L ^ D) (hNle : (N : ℝ) ≤ L ^ D)
    (hbudget : ((A : ℝ) + 1) * ((2 * (N : ℝ) + 1) * (M + farTail N δ)) ≤ L ^ D) :
    IsInPD D L (fun a θ => if a ≤ A then
      Fejer.fejerPoly N (fun x => ((minSymbol N δ (v a) x : ℝ) : ℂ)) θ else 0) :=
  Fejer.isInPD_fejerPoly D L A N (M + farTail N δ) _
    (fun a => (isPerBddR_minSymbol (hv a) N δ).toC) hAle hNle hbudget

/-! ## Part 6, the concrete pair for a finite union of intervals

The abstract statements above take the two profiles `u⁺, u⁻` as data.  Here
they are built: `u⁺` is the closed `δ`-thickening of the periodised set and
`u⁻` its `δ`-erosion, and the `L¹` gap between them is read off the jump count
through `IntervalClass.exists_goodSet`, which is already proved.

Wrap-around at the ends of the cell is handled by periodising *first* — the
thickening of a `1`-periodic set is `1`-periodic — so no hypothesis is needed
placing `B` away from `0` and `1`.  The good set is taken at radius `2δ` while
the bracket is built at radius `δ`; the factor `2` is what turns "no point of
the complement is within `2δ`" into the strict separation `infEDist > δ` that
membership in a *closed* thickening requires. -/

/-- The periodisation of `B ⊆ [0,1)` to the line. -/
def perSet (B : Set ℝ) : Set ℝ := Int.fract ⁻¹' B

/-- The periodised indicator of `B`: the function the pair brackets. -/
def perInd (B : Set ℝ) : ℝ → ℝ := (perSet B).indicator (fun _ => 1)

/-- The `δ`-thickening of the periodisation: the majorant profile. -/
def upSet (δ : ℝ) (B : Set ℝ) : Set ℝ := Metric.cthickening δ (perSet B)

/-- The `δ`-erosion of the periodisation: the minorant profile. -/
def downSet (δ : ℝ) (B : Set ℝ) : Set ℝ := (Metric.cthickening δ (perSet B)ᶜ)ᶜ

def upInd (δ : ℝ) (B : Set ℝ) : ℝ → ℝ := (upSet δ B).indicator (fun _ => 1)

def downInd (δ : ℝ) (B : Set ℝ) : ℝ → ℝ := (downSet δ B).indicator (fun _ => 1)

lemma indicator_nonneg_one (S : Set ℝ) (θ : ℝ) : 0 ≤ S.indicator (fun _ => (1 : ℝ)) θ :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) θ

lemma indicator_le_one' (S : Set ℝ) (θ : ℝ) : S.indicator (fun _ => (1 : ℝ)) θ ≤ 1 := by
  by_cases h : θ ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma perInd_nonneg (B : Set ℝ) : 0 ≤ perInd B := fun θ => indicator_nonneg_one _ θ
lemma perInd_le_one (B : Set ℝ) (θ : ℝ) : perInd B θ ≤ 1 := indicator_le_one' _ θ
lemma upInd_nonneg (δ : ℝ) (B : Set ℝ) (θ : ℝ) : 0 ≤ upInd δ B θ := indicator_nonneg_one _ θ
lemma downInd_le_one (δ : ℝ) (B : Set ℝ) (θ : ℝ) : downInd δ B θ ≤ 1 := indicator_le_one' _ θ
lemma downInd_nonneg (δ : ℝ) (B : Set ℝ) (θ : ℝ) : 0 ≤ downInd δ B θ := indicator_nonneg_one _ θ
lemma upInd_le_one (δ : ℝ) (B : Set ℝ) (θ : ℝ) : upInd δ B θ ≤ 1 := indicator_le_one' _ θ

lemma measurableSet_perSet {B : Set ℝ} (hB : MeasurableSet B) : MeasurableSet (perSet B) :=
  hB.preimage measurable_fract

lemma measurable_perInd {B : Set ℝ} (hB : MeasurableSet B) : Measurable (perInd B) :=
  measurable_const.indicator (measurableSet_perSet hB)

lemma measurable_upInd (δ : ℝ) (B : Set ℝ) : Measurable (upInd δ B) :=
  measurable_const.indicator Metric.isClosed_cthickening.measurableSet

lemma measurable_downInd (δ : ℝ) (B : Set ℝ) : Measurable (downInd δ B) :=
  measurable_const.indicator Metric.isClosed_cthickening.measurableSet.compl

lemma mem_perSet_iff {B : Set ℝ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : x ∈ perSet B ↔ x ∈ B := by
  have : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1.le, hx.2⟩
  simp [perSet, this]

lemma perSet_add_one {B : Set ℝ} {x : ℝ} : x + 1 ∈ perSet B ↔ x ∈ perSet B := by
  simp [perSet, Int.fract_add_one]

lemma isometry_shift : Isometry (fun x : ℝ => x + 1) := by
  refine Isometry.of_dist_eq fun x y => ?_
  simp only [Real.dist_eq]
  congr 1
  ring

lemma image_shift_perSet (B : Set ℝ) : (fun x : ℝ => x + 1) '' perSet B = perSet B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact perSet_add_one.2 hx
  · intro hy
    refine ⟨y - 1, ?_, by ring⟩
    refine perSet_add_one.1 ?_
    rwa [sub_add_cancel]

lemma image_shift_compl (B : Set ℝ) :
    (fun x : ℝ => x + 1) '' (perSet B)ᶜ = (perSet B)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact fun h => hx (perSet_add_one.1 h)
  · intro hy
    refine ⟨y - 1, ?_, by ring⟩
    intro h
    have hmem : y ∈ perSet B := by
      have h2 := perSet_add_one.2 h
      rwa [sub_add_cancel] at h2
    exact hy hmem

lemma infEDist_shift {S : Set ℝ} (hS : (fun x : ℝ => x + 1) '' S = S) (x : ℝ) :
    Metric.infEDist (x + 1) S = Metric.infEDist x S := by
  conv_lhs => rw [← hS]
  exact Metric.infEDist_image isometry_shift

lemma mem_cthickening_shift {S : Set ℝ} (hS : (fun x : ℝ => x + 1) '' S = S) (δ x : ℝ) :
    (x + 1 ∈ Metric.cthickening δ S) ↔ (x ∈ Metric.cthickening δ S) := by
  simp only [Metric.mem_cthickening_iff, infEDist_shift hS x]

lemma upInd_periodic (δ : ℝ) (B : Set ℝ) : Function.Periodic (upInd δ B) 1 := by
  intro x
  unfold upInd upSet
  by_cases h : x ∈ Metric.cthickening δ (perSet B)
  · rw [Set.indicator_of_mem ((mem_cthickening_shift (image_shift_perSet B) δ x).2 h),
      Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hc => h ((mem_cthickening_shift
      (image_shift_perSet B) δ x).1 hc)), Set.indicator_of_notMem h]

lemma downInd_periodic (δ : ℝ) (B : Set ℝ) : Function.Periodic (downInd δ B) 1 := by
  intro x
  have hiff := mem_cthickening_shift (image_shift_compl B) δ x
  unfold downInd downSet
  by_cases h : x ∈ Metric.cthickening δ (perSet B)ᶜ
  · have h1 : x + 1 ∉ (Metric.cthickening δ (perSet B)ᶜ)ᶜ := by
      simp only [Set.mem_compl_iff, not_not]; exact hiff.2 h
    have h2 : x ∉ (Metric.cthickening δ (perSet B)ᶜ)ᶜ := by
      simp only [Set.mem_compl_iff, not_not]; exact h
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  · have h1 : x + 1 ∈ (Metric.cthickening δ (perSet B)ᶜ)ᶜ := fun hc => h (hiff.1 hc)
    have h2 : x ∈ (Metric.cthickening δ (perSet B)ᶜ)ᶜ := h
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]

lemma isPerBddR_upInd (δ : ℝ) (B : Set ℝ) : IsPerBddR (upInd δ B) 1 where
  meas := (measurable_const.indicator Metric.isClosed_cthickening.measurableSet)
  per := upInd_periodic δ B
  bdd := fun x => by
    rw [abs_of_nonneg (upInd_nonneg δ B x)]; exact upInd_le_one δ B x

lemma isPerBddR_downInd (δ : ℝ) (B : Set ℝ) : IsPerBddR (downInd δ B) 1 where
  meas := (measurable_const.indicator Metric.isClosed_cthickening.measurableSet.compl)
  per := downInd_periodic δ B
  bdd := fun x => by
    rw [abs_of_nonneg (downInd_nonneg δ B x)]; exact downInd_le_one δ B x

/-! ### The two domination properties -/

lemma near_shift_mem {δ : ℝ} {t : ℝ} (ht : t ∈ nearSet δ) {S : Set ℝ}
    (hS : (fun x : ℝ => x + 1) '' S = S) {θ : ℝ} (hθ : θ ∈ S) :
    θ - t ∈ Metric.cthickening δ S := by
  obtain ⟨htI, htd⟩ := ht
  simp only [Set.mem_setOf_eq] at htd
  rcases le_or_gt t δ with h | h
  · refine Metric.mem_cthickening_of_dist_le (θ - t) θ δ S hθ ?_
    rw [Real.dist_eq, show θ - t - θ = -t by ring, abs_neg, abs_of_nonneg htI.1.le]
    exact h
  · have h1 : 1 - t ≤ δ := by
      rcases min_cases t (1 - t) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he] at htd; linarith
      · rw [he] at htd; exact htd
    have hmem : θ - 1 ∈ S := by
      rw [← hS] at hθ
      obtain ⟨y, hy, hyeq⟩ := hθ
      have hy1 : y = θ - 1 := by simp only at hyeq; linarith
      rwa [← hy1]
    refine Metric.mem_cthickening_of_dist_le (θ - t) (θ - 1) δ S hmem ?_
    rw [Real.dist_eq, show θ - t - (θ - 1) = 1 - t by ring, abs_of_nonneg (by linarith [htI.2])]
    exact h1

/-- **The majorant dominates after every small translation.**  This is
hypothesis `hdom` of `le_realConv_majSymbol`, verified for the thickening. -/
theorem perInd_le_upInd_shift {δ : ℝ} (B : Set ℝ) (θ : ℝ)
    {t : ℝ} (ht : t ∈ nearSet δ) : perInd B θ ≤ upInd δ B (θ - t) := by
  by_cases h : θ ∈ perSet B
  · have : θ - t ∈ upSet δ B := near_shift_mem ht (image_shift_perSet B) h
    rw [perInd, Set.indicator_of_mem h, upInd, Set.indicator_of_mem this]
  · rw [perInd, Set.indicator_of_notMem h]
    exact upInd_nonneg δ B _

/-- **The minorant is dominated after every small translation.**  This is
hypothesis `hdom` of `realConv_minSymbol_le`, verified for the erosion. -/
theorem downInd_shift_le_perInd {δ : ℝ} (B : Set ℝ) (θ : ℝ)
    {t : ℝ} (ht : t ∈ nearSet δ) : downInd δ B (θ - t) ≤ perInd B θ := by
  by_cases h : θ ∈ perSet B
  · rw [perInd, Set.indicator_of_mem h]
    exact downInd_le_one δ B _
  · have hmem : θ - t ∈ Metric.cthickening δ (perSet B)ᶜ :=
      near_shift_mem ht (image_shift_compl B) h
    have : θ - t ∉ downSet δ B := by
      simp only [downSet, Set.mem_compl_iff, not_not]; exact hmem
    rw [downInd, Set.indicator_of_notMem this]
    exact perInd_nonneg B θ

/-! ### The `L¹` gap, from the jump count -/

lemma notMem_cthickening_of_far {S : Set ℝ} {θ δ : ℝ} (hδ : 0 < δ)
    (h : ∀ y ∈ S, 2 * δ < |θ - y|) : θ ∉ Metric.cthickening δ S := by
  intro hc
  rw [Metric.mem_cthickening_iff] at hc
  have hle : ENNReal.ofReal (2 * δ) ≤ Metric.infEDist θ S := by
    rw [Metric.le_infEDist]
    intro y hy
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (h y hy).le
  have hcon : ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal δ := hle.trans hc
  rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at hcon
  linarith

/-- **On the good set the pair is exact.**  At a point of the cell whose
`2δ`-neighbourhood does not meet the boundary of `B`, the thickening and the
erosion agree — with each other and with the indicator. -/
theorem upInd_eq_downInd_of_good {B : Set ℝ} {δ : ℝ} (hδ : 0 < δ) {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hgood : ∀ y : ℝ, |y - θ| ≤ 2 * δ → y ∈ Ioo (0 : ℝ) 1 ∧ (y ∈ B ↔ θ ∈ B)) :
    upInd δ B θ = downInd δ B θ := by
  by_cases hB : θ ∈ B
  · have hp : θ ∈ perSet B := (mem_perSet_iff hθ).2 hB
    have hup : upInd δ B θ = 1 :=
      Set.indicator_of_mem (Metric.self_subset_cthickening (perSet B) hp) _
    have hdown : downInd δ B θ = 1 := by
      refine Set.indicator_of_mem ?_ _
      show θ ∈ (Metric.cthickening δ (perSet B)ᶜ)ᶜ
      refine notMem_cthickening_of_far hδ ?_
      intro y hy
      by_contra hcon
      push_neg at hcon
      have hg := hgood y (by rw [abs_sub_comm]; exact hcon)
      exact hy ((mem_perSet_iff hg.1).2 (hg.2.2 hB))
    rw [hup, hdown]
  · have hp : θ ∉ perSet B := fun h => hB ((mem_perSet_iff hθ).1 h)
    have hdown : downInd δ B θ = 0 := by
      refine Set.indicator_of_notMem ?_ _
      simp only [downSet, Set.mem_compl_iff, not_not]
      exact Metric.self_subset_cthickening ((perSet B)ᶜ) hp
    have hup : upInd δ B θ = 0 := by
      refine Set.indicator_of_notMem ?_ _
      refine notMem_cthickening_of_far hδ ?_
      intro y hy
      by_contra hcon
      push_neg at hcon
      have hg := hgood y (by rw [abs_sub_comm]; exact hcon)
      exact hB (hg.2.1 ((mem_perSet_iff hg.1).1 hy))
    rw [hup, hdown]

lemma integrableOn_indOn {S : Set ℝ} (hS : MeasurableSet S) :
    IntegrableOn (S.indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp [Real.volume_Ioo])
    (measurable_const.indicator hS).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg_one S x)]
  exact indicator_le_one' S x

/-- **The `L¹` gap of the two profiles, from the jump count.**  For a union of
`m` intervals the thickening and the erosion differ, in mean over the
fundamental cell, by at most `(4m+2)·2δ`.  The input is
`IntervalClass.exists_goodSet`, run at radius `2δ`. -/
theorem integral_upInd_sub_downInd_le {m : ℕ} {B : Set ℝ}
    (hB : IntervalClass.IsUnionOfIntervals m B) {δ : ℝ} (hδ : 0 < δ) :
    (∫ θ in Ioo (0 : ℝ) 1, upInd δ B θ) - (∫ θ in Ioo (0 : ℝ) 1, downInd δ B θ)
      ≤ (4 * (m : ℝ) + 2) * (2 * δ) := by
  obtain ⟨G, hGmeas, hGsub, hGgood, hGvol⟩ :=
    IntervalClass.exists_goodSet hB (s := 2 * δ) (by linarith)
  have hupI : IntegrableOn (upInd δ B) (Ioo (0 : ℝ) 1) :=
    integrableOn_indOn Metric.isClosed_cthickening.measurableSet
  have hdownI : IntegrableOn (downInd δ B) (Ioo (0 : ℝ) 1) :=
    integrableOn_indOn Metric.isClosed_cthickening.measurableSet.compl
  have hbadI : IntegrableOn ((Ioo (0 : ℝ) 1 \ G).indicator (fun _ => (1 : ℝ)))
      (Ioo (0 : ℝ) 1) := integrableOn_indOn (measurableSet_Ioo.diff hGmeas)
  have hptw : ∀ θ ∈ Ioo (0 : ℝ) 1,
      upInd δ B θ - downInd δ B θ ≤ (Ioo (0 : ℝ) 1 \ G).indicator (fun _ => (1 : ℝ)) θ := by
    intro θ hθ
    by_cases hG : θ ∈ G
    · have := upInd_eq_downInd_of_good (B := B) hδ hθ (fun y hy => hGgood θ hG y hy)
      rw [this, sub_self]
      exact indicator_nonneg_one _ θ
    · have hmem : θ ∈ Ioo (0 : ℝ) 1 \ G := ⟨hθ, hG⟩
      rw [Set.indicator_of_mem hmem]
      have h1 := upInd_le_one δ B θ
      have h2 := downInd_nonneg δ B θ
      linarith
  have hstep : (∫ θ in Ioo (0 : ℝ) 1, upInd δ B θ) - (∫ θ in Ioo (0 : ℝ) 1, downInd δ B θ)
      ≤ ∫ θ in Ioo (0 : ℝ) 1, (Ioo (0 : ℝ) 1 \ G).indicator (fun _ => (1 : ℝ)) θ := by
    rw [← integral_sub hupI hdownI]
    exact setIntegral_mono_on (hupI.sub hdownI) hbadI measurableSet_Ioo hptw
  refine hstep.trans ?_
  have hval : (∫ θ in Ioo (0 : ℝ) 1, (Ioo (0 : ℝ) 1 \ G).indicator (fun _ => (1 : ℝ)) θ)
      = (volume (Ioo (0 : ℝ) 1 \ G)).toReal := by
    rw [setIntegral_indicator (measurableSet_Ioo.diff hGmeas),
      Set.inter_eq_right.2 (fun x hx => hx.1), setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [hval]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  exact hGvol

/-! ## Part 7, the pair, assembled

This is the deliverable: for a union of `m` intervals and any `δ > 0` and any
degree `N`, two trigonometric polynomials of degree `N` that bracket the
periodised indicator **pointwise everywhere**, with an explicit `L¹` gap and an
explicit `ℓ¹` coefficient mass. -/

/-- **The bracketing pair.**

`S⁻ = σ_N(u⁻ − η) ≤ 1_B ≤ σ_N(u⁺ + η) = S⁺` pointwise on all of `ℝ`, with

`∫₀¹(S⁺ − S⁻) ≤ (4m+2)·2δ + 2η(N,δ)`.

Both members are `Fejer.fejerPoly` of an explicit symbol
(`fejerPoly_ofReal`), hence trigonometric polynomials of degree `N` whose
coefficient list has `ℓ¹` mass at most `(2N+1)(1+η)` (`l1_majSymbol_le`,
`l1_minSymbol_le`) — which is what display (24) budgets. -/
theorem bracket_intervals {m : ℕ} {B : Set ℝ}
    (hB : IntervalClass.IsUnionOfIntervals m B) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    (∀ θ : ℝ, realConv N (minSymbol N δ (downInd δ B)) θ ≤ perInd B θ) ∧
    (∀ θ : ℝ, perInd B θ ≤ realConv N (majSymbol N δ (upInd δ B)) θ) ∧
    ((∫ θ in Ioo (0 : ℝ) 1, realConv N (majSymbol N δ (upInd δ B)) θ)
        - ∫ θ in Ioo (0 : ℝ) 1, realConv N (minSymbol N δ (downInd δ B)) θ)
      ≤ (4 * (m : ℝ) + 2) * (2 * δ) + 2 * farTail N δ := by
  refine ⟨fun θ => ?_, fun θ => ?_, ?_⟩
  · exact realConv_minSymbol_le N hδ (isPerBddR_downInd δ B) (downInd_le_one δ B)
      (perInd_nonneg B) θ (fun t ht => downInd_shift_le_perInd B θ ht)
  · exact le_realConv_majSymbol N hδ (isPerBddR_upInd δ B) (upInd_nonneg δ B)
      (perInd_nonneg B) (perInd_le_one B) θ (fun t ht => perInd_le_upInd_shift B θ ht)
  · rw [integral_bracket_gap (isPerBddR_upInd δ B) (isPerBddR_downInd δ B) N δ]
    have := integral_upInd_sub_downInd_le hB hδ
    linarith

/-- Both members of the pair really are `Fejer.fejerPoly` of a bounded
`1`-periodic symbol, so the degree, the coefficient list and the class
membership are the ones proved in `Kwon1002/Fejer.lean`. -/
theorem majSymbol_eq_fejerPoly (δ : ℝ) (B : Set ℝ) (N : ℕ) (θ : ℝ) :
    Fejer.fejerPoly N (fun x => ((majSymbol N δ (upInd δ B) x : ℝ) : ℂ)) θ
      = ((realConv N (majSymbol N δ (upInd δ B)) θ : ℝ) : ℂ) :=
  fejerPoly_ofReal (isPerBddR_majSymbol (isPerBddR_upInd δ B) N δ) N θ

theorem minSymbol_eq_fejerPoly (δ : ℝ) (B : Set ℝ) (N : ℕ) (θ : ℝ) :
    Fejer.fejerPoly N (fun x => ((minSymbol N δ (downInd δ B) x : ℝ) : ℂ)) θ
      = ((realConv N (minSymbol N δ (downInd δ B)) θ : ℝ) : ℂ) :=
  fejerPoly_ofReal (isPerBddR_minSymbol (isPerBddR_downInd δ B) N δ) N θ

/-- **The pair at an arbitrary precision.**  For every `ε > 0` there are a
scale `δ` and a degree `N` at which the bracketing pair has `L¹` gap at most
`ε`.  Both parameters are produced explicitly: `δ` is linear in `ε` and `N` is
`O(1/(εδ²)) = O(ε^{-3})`. -/
theorem exists_bracket_gap_le {m : ℕ} {B : Set ℝ}
    (hB : IntervalClass.IsUnionOfIntervals m B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (N : ℕ), 0 < δ ∧
      (∀ θ : ℝ, realConv N (minSymbol N δ (downInd δ B)) θ ≤ perInd B θ) ∧
      (∀ θ : ℝ, perInd B θ ≤ realConv N (majSymbol N δ (upInd δ B)) θ) ∧
      ((∫ θ in Ioo (0 : ℝ) 1, realConv N (majSymbol N δ (upInd δ B)) θ)
          - ∫ θ in Ioo (0 : ℝ) 1, realConv N (minSymbol N δ (downInd δ B)) θ) ≤ ε := by
  have hK0 : (0 : ℝ) < (4 * (m : ℝ) + 2) * 2 := by positivity
  have hδ : 0 < ε / (2 * ((4 * (m : ℝ) + 2) * 2)) := by positivity
  set δ : ℝ := ε / (2 * ((4 * (m : ℝ) + 2) * 2)) with hδdef
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (ε * δ ^ 2))
  obtain ⟨h1, h2, h3⟩ := bracket_intervals hB hδ N
  refine ⟨δ, N, hδ, h1, h2, h3.trans ?_⟩
  have hgap1 : (4 * (m : ℝ) + 2) * (2 * δ) = ε / 2 := by
    rw [hδdef]; field_simp
  have hεδ : (0 : ℝ) < ε * δ ^ 2 := by positivity
  have hlin : 1 < (N : ℝ) * (ε * δ ^ 2) := by
    rw [div_lt_iff₀ hεδ] at hN; linarith
  have hden : (0 : ℝ) < 4 * ((N : ℝ) + 1) * δ ^ 2 := by positivity
  have htail : 2 * farTail N δ ≤ ε / 2 := by
    unfold farTail
    rw [mul_one_div, div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hlin, hεδ]
  linarith

end

end Selberg
end Kwon1002
