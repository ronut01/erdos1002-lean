import Kwon1002.Section5Join

/-!
# Display (35) on the interval class

`Kwon1002/Section5Join.lean` proves display (35)
(`TupleInputs.oneLevel_gaussKuzmin_intensity`) at the single truncation window
`B = {x : ε < |x| ≤ R}`.  Two things separated that instance from residual
(35a), `TupleInputs.oneLevel_gaussKuzmin_intensity_intervals`, which asks for
the same conclusion at an arbitrary `IntervalClass.IsFiniteUnionOfIntervals`:

* the decomposition of an arbitrary such family — a `Finset` of possibly
  overlapping `OrdConnected` sets, carrying no endpoints — into bands the
  Gauss-Kuzmin normalisation can be read at, and
* the (true, unstated) nullity of the level sets `{(x,θ) : a₁(x)·W(θ) = c}`,
  needed if the decomposition is performed at the endpoints.

This module closes both, and neither by the route the record anticipated.

## The two moves

**Inclusion-exclusion replaces disjointification.**  Nothing is disjointified.
The stationary functional `markMean L C` is *modular* — `markMean L (A ∪ B) +
markMean L (A ∩ B) = markMean L A + markMean L B` — for the trivial reason that
the identity already holds pointwise between the four indicators, before any
integral is taken (`markMean_union_add_inter`).  `Λ` is modular for the same
reason.  Peeling one set off the `Finset` therefore replaces
`⋃_{I ∈ insert I₀ s} I` by the three families `{I₀}`, `s` and
`(I₀ ∩ ·) '' s`, the last two of which have at most `s.card` members and the
first exactly one.  That is an induction on the cardinality with no ordering of
endpoints anywhere (`tendsto_scaled_markMean_intervals`).

**An `η`-sandwich replaces the nullity.**  The single-interval case is not read
at the endpoints of `I` at all.  For `η > 0`,

  `Ioc (sInf I) (max (sInf I) (sSup I − η)) ⊆ I ⊆ Ioc (sInf I − η) (sSup I)`,

and both brackets are half-open bands, on which the normalisation
`GaussKuzmin.tendsto_scaled_markBandMean` applies verbatim.  The two limits
differ by `O(η/δ²)` because `Λ((u,∞)) = 1/(2π²u)` is *explicit*
(`GaussKuzmin.levyIntensity_Ioi_toReal`), so the sandwich closes as `η → 0`
without ever asking what `Λ` or the level-`j` law does to a point
(`tendsto_scaled_markMean_ordConnected`).  The nullity of
`{(x,θ) : a₁(x)·W(θ) = c}` is true but is not used, and is not needed.

## What is proved

`oneLevel_gaussKuzmin_intensity_intervals`, token for token as
`Kwon1002/TupleInputs.lean` states it, unconditionally.  The `example` at the
foot of the file reproduces that statement and checks the two agree.

## What this does **not** close

`TupleInputs.oneLevel_gaussKuzmin_intensity_to_measurable`, residual (35b), the
passage from finite unions of intervals to an arbitrary measurable `B`.  It is
untouched here, and since `TupleInputs.oneLevel_gaussKuzmin_intensity` is
derived from (35a) **and** (35b), closing (35a) does not close it.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal Real

namespace Kwon1002

namespace Section5Intervals

noncomputable section

open Section5Join

/-! ## A sandwich criterion

The single-interval case produces, for each tolerance, a pair of brackets whose
limits are known and close to the target.  This packages that shape. -/

/-- If `F` is bracketed, at every tolerance, by two sequences whose limits are
known and straddle `T` within that tolerance, then `F → T`. -/
theorem tendsto_of_sandwich {F : ℕ → ℝ} {T : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ Fl Fu : ℕ → ℝ, ∃ Tl Tu : ℝ,
        (∀ n, Fl n ≤ F n) ∧ (∀ n, F n ≤ Fu n) ∧
        Tendsto Fl atTop (𝓝 Tl) ∧ Tendsto Fu atTop (𝓝 Tu) ∧
        Tl ≤ T ∧ T ≤ Tu ∧ Tu - Tl ≤ ε) :
    Tendsto F atTop (𝓝 T) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Fl, Fu, Tl, Tu, hFl, hFu, hTl, hTu, hTlT, hTTu, hgap⟩ := h (ε / 3) (by linarith)
  rw [Metric.tendsto_atTop] at hTl hTu
  obtain ⟨N₁, hN₁⟩ := hTl (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hTu (ε / 3) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hFl n], by linarith [hFu n]⟩

/-! ## The stationary mark law of a scaled set -/

/-- The stationary symbol of the scaled mark event `{a·W(θ)/L ∈ C}`. -/
def markSymb (L : ℝ) (C : Set ℝ) : ℕ → ℝ → ℝ :=
  fun a θ => C.indicator (fun _ => (1 : ℝ)) ((a : ℝ) * W θ / L)

/-- The stationary mass of `{(x,θ) : a₁(x)·W(θ)/L ∈ C}`. -/
def markMean (L : ℝ) (C : Set ℝ) : ℝ := stationaryMeanR (markSymb L C)

open scoped Classical in
lemma markSymb_apply (L : ℝ) (C : Set ℝ) (a : ℕ) (θ : ℝ) :
    markSymb L C a θ = if (a : ℝ) * W θ / L ∈ C then (1 : ℝ) else 0 :=
  Set.indicator_apply _ _ _

lemma measurable_markSymb {C : Set ℝ} (hC : MeasurableSet C) (L : ℝ) (a : ℕ) :
    Measurable (markSymb L C a) :=
  (measurable_const.indicator hC).comp ((measurable_const.mul measurable_W).div_const L)

lemma abs_markSymb_le (L : ℝ) (C : Set ℝ) (a : ℕ) (θ : ℝ) : |markSymb L C a θ| ≤ 1 := by
  rw [markSymb_apply]
  split_ifs <;> simp

lemma markSymb_mono {C D : Set ℝ} (h : C ⊆ D) (L : ℝ) (a : ℕ) (θ : ℝ) :
    markSymb L C a θ ≤ markSymb L D a θ := by
  rw [markSymb_apply, markSymb_apply]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h h1) h2
  · norm_num
  · exact le_rfl

/-! ## Modularity, from a pointwise identity -/

lemma stationaryMeanR_add {f g : ℕ → ℝ → ℝ} {K : ℝ}
    (hf : ∀ a, Measurable (f a)) (hg : ∀ a, Measurable (g a))
    (hfb : ∀ a θ, |f a θ| ≤ K) (hgb : ∀ a θ, |g a θ| ≤ K) :
    stationaryMeanR (fun a θ => f a θ + g a θ) = stationaryMeanR f + stationaryMeanR g := by
  have hinner : ∀ x : ℝ, (∫ θ in Ioo (0:ℝ) 1, (f (digit x 0) θ + g (digit x 0) θ))
      = innerMean f (digit x 0) + innerMean g (digit x 0) := fun x =>
    integral_add (integrableOn_cell (hf _) (hfb _)) (integrableOn_cell (hg _) (hgb _))
  show (∫ x, (∫ θ in Ioo (0:ℝ) 1, (f (digit x 0) θ + g (digit x 0) θ))
      ∂Erdos1002.gaussMeasure) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), stationaryMeanR_eq,
    stationaryMeanR_eq]
  exact integral_add (integrable_innerMean_comp f (abs_innerMean_le_of_bound hfb))
    (integrable_innerMean_comp g (abs_innerMean_le_of_bound hgb))

/-- **The stationary mark law is modular.**  The identity holds pointwise
between the four indicators before any integral is taken. -/
theorem markMean_union_add_inter (L : ℝ) {C D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    markMean L (C ∪ D) + markMean L (C ∩ D) = markMean L C + markMean L D := by
  have hpt : (fun a θ => markSymb L (C ∪ D) a θ + markSymb L (C ∩ D) a θ)
      = fun a θ => markSymb L C a θ + markSymb L D a θ := by
    funext a θ
    rw [markSymb_apply, markSymb_apply, markSymb_apply, markSymb_apply]
    by_cases h1 : (a : ℝ) * W θ / L ∈ C <;> by_cases h2 : (a : ℝ) * W θ / L ∈ D <;>
      simp [h1, h2]
  have hadd1 := stationaryMeanR_add (K := 1) (measurable_markSymb (hC.union hD) L)
    (measurable_markSymb (hC.inter hD) L) (abs_markSymb_le L (C ∪ D)) (abs_markSymb_le L (C ∩ D))
  have hadd2 := stationaryMeanR_add (K := 1) (measurable_markSymb hC L)
    (measurable_markSymb hD L) (abs_markSymb_le L C) (abs_markSymb_le L D)
  rw [markMean, markMean, markMean, markMean, ← hadd1, ← hadd2, hpt]

theorem markMean_mono (L : ℝ) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (h : C ⊆ D) : markMean L C ≤ markMean L D :=
  stationaryMeanR_mono (K := 1) (measurable_markSymb hC L) (measurable_markSymb hD L)
    (abs_markSymb_le L C) (abs_markSymb_le L D) (markSymb_mono h L)

theorem markMean_empty (L : ℝ) : markMean L (∅ : Set ℝ) = 0 := by
  have h : markSymb L (∅ : Set ℝ) = fun _ _ => (0:ℝ) := by
    funext a θ; rw [markSymb_apply]; simp
  rw [markMean, h]
  simp [stationaryMeanR]

/-! ## The bands -/

/-- On a half-open band the stationary mark law is a difference of two
mark tails, which is what `GaussKuzmin` normalises. -/
theorem markMean_Ioc {L u v : ℝ} (hL : 0 < L) (huv : u ≤ v) :
    markMean L (Ioc u v)
      = GaussKuzmin.markTailMean (u * L) - GaussKuzmin.markTailMean (v * L) := by
  have hfun : markSymb L (Ioc u v)
      = fun (a : ℕ) (θ : ℝ) => (if u * L < (a:ℝ) * W θ then (1:ℝ) else 0)
        - (if v * L < (a:ℝ) * W θ then (1:ℝ) else 0) := by
    funext a θ
    rw [markSymb_apply]
    have hiff : (a : ℝ) * W θ / L ∈ Ioc u v
        ↔ (u * L < (a:ℝ) * W θ ∧ (a:ℝ) * W θ ≤ v * L) := by
      rw [Set.mem_Ioc, lt_div_iff₀ hL, div_le_iff₀ hL]
    by_cases h1 : u * L < (a:ℝ) * W θ
    · by_cases h2 : (a:ℝ) * W θ ≤ v * L
      · rw [if_pos (hiff.mpr ⟨h1, h2⟩), if_pos h1, if_neg (not_lt.mpr h2)]; ring
      · rw [if_neg (fun h => h2 (hiff.mp h).2), if_pos h1, if_pos (not_le.mp h2)]; ring
    · have h2 : (a:ℝ) * W θ ≤ v * L :=
        le_trans (not_lt.mp h1) (mul_le_mul_of_nonneg_right huv hL.le)
      rw [if_neg (fun h => h1 (hiff.mp h).1), if_neg h1, if_neg (not_lt.mpr h2)]; ring
  rw [markMean, hfun, stationaryMeanR_sub (K := 1) (measurable_markTailSymbol (u * L))
    (measurable_markTailSymbol (v * L)) (abs_markTailSymbol_le (u * L))
    (abs_markTailSymbol_le (v * L)), markTail_stationaryMeanR, markTail_stationaryMeanR]

lemma Lnorm_nonneg (n : ℕ) : 0 ≤ Lnorm n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [Lnorm, h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- **The normalisation on a band, along `L = log n`.** -/
theorem tendsto_scaled_markMean_Ioc {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Tendsto (fun n : ℕ => Lnorm n * markMean (Lnorm n) (Ioc u v)) atTop
      (𝓝 (2 * lyapunov * (levyIntensity (Ioc u v)).toReal)) := by
  have h := (GaussKuzmin.tendsto_scaled_markBandMean hu huv).comp
    TupleMeasure.tendsto_Lnorm_atTop
  refine h.congr' ?_
  filter_upwards [TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hn
  simp only [Function.comp_apply]
  rw [markMean_Ioc hn huv]

/-! ## `Λ` on the interval class -/

lemma levyIntensity_ne_top_of_ge {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (h : ∀ x ∈ S, δ ≤ x) : levyIntensity S ≠ ⊤ :=
  ne_top_of_le_ne_top (GaussKuzmin.levyIntensity_Ioi_lt_top (u := δ / 2) (by linarith))
    (measure_mono (fun x hx => by
      have := h x hx
      exact Set.mem_Ioi.mpr (by linarith)))

lemma levyIntensity_Ioc_toReal_eq {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (levyIntensity (Ioc u v)).toReal
      = 1 / (2 * Real.pi ^ 2 * u) - 1 / (2 * Real.pi ^ 2 * v) := by
  rw [GaussKuzmin.levyIntensity_Ioc_toReal hu huv,
    GaussKuzmin.levyIntensity_Ioi_toReal hu,
    GaussKuzmin.levyIntensity_Ioi_toReal (lt_of_lt_of_le hu huv)]

lemma measurableSet_of_isUnionOfIntervals {m : ℕ} {C : Set ℝ}
    (h : IntervalClass.IsUnionOfIntervals m C) : MeasurableSet C := by
  obtain ⟨s, -, hoc, hC⟩ := h
  rw [hC]
  exact Finset.measurableSet_biUnion _ (fun I hI => (hoc I hI).measurableSet)


/-! ## The single interval, by an `η`-sandwich

No endpoint of `I` is ever read: `I` is bracketed between two half-open bands
whose ends miss `sInf I` and `sSup I` by `η`, and the explicit form of
`Λ((u,∞)) = 1/(2π²u)` prices the bracket at `O(η/δ²)`. -/

theorem tendsto_scaled_markMean_ordConnected {δ R : ℝ} (hδ : 0 < δ) {I : Set ℝ}
    (hI : I.OrdConnected) (hIδ : ∀ x ∈ I, δ ≤ x) (hIR : ∀ x ∈ I, x ≤ R) :
    Tendsto (fun n : ℕ => Lnorm n * markMean (Lnorm n) I) atTop
      (𝓝 (2 * lyapunov * (levyIntensity I).toReal)) := by
  rcases Set.eq_empty_or_nonempty I with hemp | hne
  · rw [hemp]
    simp [markMean_empty]
  have hIm : MeasurableSet I := hI.measurableSet
  have hbb : BddBelow I := ⟨δ, fun x hx => hIδ x hx⟩
  have hba : BddAbove I := ⟨R, fun x hx => hIR x hx⟩
  have hδa : δ ≤ sInf I := le_csInf hne hIδ
  have hab : sInf I ≤ sSup I := csInf_le_csSup hbb hba hne
  have hapos : (0:ℝ) < sInf I := lt_of_lt_of_le hδ hδa
  have hbpos : (0:ℝ) < sSup I := lt_of_lt_of_le hapos hab
  have hsub1 : Ioo (sInf I) (sSup I) ⊆ I :=
    IsConnected.Ioo_csInf_csSup_subset ⟨hne, hI.isPreconnected⟩ hbb hba
  have hsub2 : I ⊆ Icc (sInf I) (sSup I) := subset_Icc_csInf_csSup hbb hba
  have hlam : (0:ℝ) < lyapunov := OneLevelLaw.lyapunov_pos
  have hfinI : levyIntensity I ≠ ⊤ := levyIntensity_ne_top_of_ge hδ hIδ
  refine tendsto_of_sandwich ?_
  intro ε hε
  set a : ℝ := sInf I
  set b : ℝ := sSup I
  set K : ℝ := 2 * lyapunov * ((1 / (2 * Real.pi ^ 2)) * (3 / δ ^ 2)) with hKdef
  have hKpos : 0 < K := by
    have h1 : (0:ℝ) < 2 * lyapunov := by linarith
    have h2 : (0:ℝ) < (1 / (2 * Real.pi ^ 2)) * (3 / δ ^ 2) := by positivity
    exact mul_pos h1 h2
  set η : ℝ := min (δ / 2) (ε / K) with hηdef
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hηK : K * η ≤ ε := by
    have hle : η ≤ ε / K := min_le_right _ _
    have := mul_le_mul_of_nonneg_left hle hKpos.le
    rw [mul_div_cancel₀ _ (ne_of_gt hKpos)] at this
    exact this
  have hav : a ≤ max a (b - η) := le_max_left _ _
  have hvpos : (0:ℝ) < max a (b - η) := lt_of_lt_of_le hapos hav
  have haη : (0:ℝ) < a - η := by linarith
  have haηb : a - η ≤ b := by linarith
  have hlow : Ioc a (max a (b - η)) ⊆ I := by
    intro x hx
    refine hsub1 ⟨hx.1, ?_⟩
    rcases le_max_iff.mp hx.2 with h | h
    · exact absurd h (not_le.mpr hx.1)
    · linarith
  have hup : I ⊆ Ioc (a - η) b := fun x hx =>
    ⟨by have := (hsub2 hx).1; linarith, (hsub2 hx).2⟩
  have hfinU : levyIntensity (Ioc (a - η) b) ≠ ⊤ :=
    levyIntensity_ne_top_of_ge haη (fun x hx => hx.1.le)
  refine ⟨fun n => Lnorm n * markMean (Lnorm n) (Ioc a (max a (b - η))),
    fun n => Lnorm n * markMean (Lnorm n) (Ioc (a - η) b),
    2 * lyapunov * (levyIntensity (Ioc a (max a (b - η)))).toReal,
    2 * lyapunov * (levyIntensity (Ioc (a - η) b)).toReal,
    fun n => mul_le_mul_of_nonneg_left
      (markMean_mono _ measurableSet_Ioc hIm hlow) (Lnorm_nonneg n),
    fun n => mul_le_mul_of_nonneg_left
      (markMean_mono _ hIm measurableSet_Ioc hup) (Lnorm_nonneg n),
    tendsto_scaled_markMean_Ioc hapos hav,
    tendsto_scaled_markMean_Ioc haη haηb, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hfinI (measure_mono hlow)) (by linarith)
  · exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hfinU (measure_mono hup)) (by linarith)
  · rw [levyIntensity_Ioc_toReal_eq hapos hav, levyIntensity_Ioc_toReal_eq haη haηb]
    have hA : 1 / (2 * Real.pi ^ 2 * (a - η)) - 1 / (2 * Real.pi ^ 2 * a)
        ≤ (1 / (2 * Real.pi ^ 2)) * (2 * η / δ ^ 2) := by
      have he : 1 / (2 * Real.pi ^ 2 * (a - η)) - 1 / (2 * Real.pi ^ 2 * a)
          = (1 / (2 * Real.pi ^ 2)) * (η / (a * (a - η))) := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp
        ring
      rw [he]
      have hprod : δ * (δ / 2) ≤ a * (a - η) :=
        mul_le_mul hδa (by linarith) (by linarith) (by linarith)
      have h2 : η / (a * (a - η)) ≤ 2 * η / δ ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos hapos haη) (by positivity)]
        nlinarith [hprod, hη0.le]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hB : 1 / (2 * Real.pi ^ 2 * max a (b - η)) - 1 / (2 * Real.pi ^ 2 * b)
        ≤ (1 / (2 * Real.pi ^ 2)) * (η / δ ^ 2) := by
      have he : 1 / (2 * Real.pi ^ 2 * max a (b - η)) - 1 / (2 * Real.pi ^ 2 * b)
          = (1 / (2 * Real.pi ^ 2)) * ((b - max a (b - η)) / (max a (b - η) * b)) := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have h1 : max a (b - η) ≠ 0 := ne_of_gt hvpos
        have h2 : b ≠ 0 := ne_of_gt hbpos
        field_simp
      rw [he]
      have hnum : b - max a (b - η) ≤ η := by
        have := le_max_right a (b - η); linarith
      have hden : δ ^ 2 ≤ max a (b - η) * b := by nlinarith [hδa, hav, hab]
      have h2 : (b - max a (b - η)) / (max a (b - η) * b) ≤ η / δ ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos hvpos hbpos) (by positivity)]
        nlinarith [hnum, hden, hη0.le, sq_nonneg δ]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hcomb : 2 * lyapunov * ((1 / (2 * Real.pi ^ 2 * (a - η)) - 1 / (2 * Real.pi ^ 2 * b))
        - (1 / (2 * Real.pi ^ 2 * a) - 1 / (2 * Real.pi ^ 2 * max a (b - η)))) ≤ K * η := by
      have hsum : (1 / (2 * Real.pi ^ 2 * (a - η)) - 1 / (2 * Real.pi ^ 2 * b))
          - (1 / (2 * Real.pi ^ 2 * a) - 1 / (2 * Real.pi ^ 2 * max a (b - η)))
          ≤ (1 / (2 * Real.pi ^ 2)) * (2 * η / δ ^ 2)
            + (1 / (2 * Real.pi ^ 2)) * (η / δ ^ 2) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsum (by linarith : (0:ℝ) ≤ 2 * lyapunov)
      have heq : 2 * lyapunov * ((1 / (2 * Real.pi ^ 2)) * (2 * η / δ ^ 2)
          + (1 / (2 * Real.pi ^ 2)) * (η / δ ^ 2)) = K * η := by rw [hKdef]; ring
      linarith
    nlinarith [hcomb, hηK]

/-! ## The finite union, by inclusion-exclusion on the `Finset`

Nothing is disjointified and nothing is sorted.  Peeling `I₀` off the family
replaces `⋃_{I ∈ s} I` by `I₀`, by `⋃_{I ∈ s.erase I₀} I`, and by
`⋃_{I ∈ s.erase I₀} (I₀ ∩ I)`; the last is again a family of order-convex sets
of no larger cardinality, so the recursion is on the cardinality alone. -/

theorem tendsto_scaled_markMean_intervals :
    ∀ (m : ℕ) {C : Set ℝ} {δ R : ℝ}, 0 < δ → IntervalClass.IsUnionOfIntervals m C →
      (∀ x ∈ C, δ ≤ x) → (∀ x ∈ C, x ≤ R) →
      Tendsto (fun n : ℕ => Lnorm n * markMean (Lnorm n) C) atTop
        (𝓝 (2 * lyapunov * (levyIntensity C).toReal)) := by
  intro m
  induction m with
  | zero =>
    intro C δ R _ hC _ _
    obtain ⟨s, hcard, -, hCeq⟩ := hC
    have hs : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    rw [hCeq, hs]
    simp [markMean_empty]
  | succ m ih =>
    intro C δ R hδ hC hCδ hCR
    classical
    obtain ⟨s, hcard, hoc, hCeq⟩ := hC
    rcases Finset.eq_empty_or_nonempty s with hs | ⟨I₀, hI₀⟩
    · rw [hCeq, hs]
      simp [markMean_empty]
    have hcard' : (s.erase I₀).card ≤ m := by
      have h1 : (s.erase I₀).card = s.card - 1 := Finset.card_erase_of_mem hI₀
      omega
    have hCsplit : C = I₀ ∪ ⋃ I ∈ s.erase I₀, I := by
      rw [hCeq]
      conv_lhs => rw [← Finset.insert_erase hI₀]
      rw [Finset.set_biUnion_insert]
    have hocI₀ : I₀.OrdConnected := hoc I₀ hI₀
    have hC'iu : IntervalClass.IsUnionOfIntervals m (⋃ I ∈ s.erase I₀, I) :=
      ⟨s.erase I₀, hcard', fun I hI => hoc I (Finset.mem_of_mem_erase hI), rfl⟩
    have hDiu : IntervalClass.IsUnionOfIntervals m (I₀ ∩ ⋃ I ∈ s.erase I₀, I) := by
      refine ⟨(s.erase I₀).image (fun I => I₀ ∩ I), Finset.card_image_le.trans hcard', ?_, ?_⟩
      · intro J hJ
        obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
        exact hocI₀.inter (hoc I (Finset.mem_of_mem_erase hI))
      · ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_image, exists_prop,
          exists_exists_and_eq_and]
        tauto
    have hI₀m : MeasurableSet I₀ := hocI₀.measurableSet
    have hC'm : MeasurableSet (⋃ I ∈ s.erase I₀, I) := measurableSet_of_isUnionOfIntervals hC'iu
    have hsubI₀ : I₀ ⊆ C := by rw [hCsplit]; exact Set.subset_union_left
    have hsubC' : (⋃ I ∈ s.erase I₀, I) ⊆ C := by rw [hCsplit]; exact Set.subset_union_right
    have h1 := tendsto_scaled_markMean_ordConnected (δ := δ) (R := R) hδ hocI₀
      (fun x hx => hCδ x (hsubI₀ hx)) (fun x hx => hCR x (hsubI₀ hx))
    have h2 := ih (δ := δ) (R := R) hδ hC'iu (fun x hx => hCδ x (hsubC' hx))
      (fun x hx => hCR x (hsubC' hx))
    have h3 := ih (δ := δ) (R := R) hδ hDiu (fun x hx => hCδ x (hsubI₀ hx.1))
      (fun x hx => hCR x (hsubI₀ hx.1))
    have hmod : ∀ n : ℕ, Lnorm n * markMean (Lnorm n) C
        = Lnorm n * markMean (Lnorm n) I₀ + Lnorm n * markMean (Lnorm n) (⋃ I ∈ s.erase I₀, I)
          - Lnorm n * markMean (Lnorm n) (I₀ ∩ ⋃ I ∈ s.erase I₀, I) := by
      intro n
      have h := congrArg (fun t : ℝ => Lnorm n * t)
        (markMean_union_add_inter (Lnorm n) hI₀m hC'm)
      simp only [mul_add] at h
      rw [hCsplit]
      linarith
    have hTmod : 2 * lyapunov * (levyIntensity C).toReal
        = 2 * lyapunov * (levyIntensity I₀).toReal
          + 2 * lyapunov * (levyIntensity (⋃ I ∈ s.erase I₀, I)).toReal
          - 2 * lyapunov * (levyIntensity (I₀ ∩ ⋃ I ∈ s.erase I₀, I)).toReal := by
      have hfinI : levyIntensity I₀ ≠ ⊤ :=
        levyIntensity_ne_top_of_ge hδ (fun x hx => hCδ x (hsubI₀ hx))
      have hfinC' : levyIntensity (⋃ I ∈ s.erase I₀, I) ≠ ⊤ :=
        levyIntensity_ne_top_of_ge hδ (fun x hx => hCδ x (hsubC' hx))
      have hfinU : levyIntensity (I₀ ∪ ⋃ I ∈ s.erase I₀, I) ≠ ⊤ := by
        rw [← hCsplit]; exact levyIntensity_ne_top_of_ge hδ hCδ
      have hfinD : levyIntensity (I₀ ∩ ⋃ I ∈ s.erase I₀, I) ≠ ⊤ :=
        levyIntensity_ne_top_of_ge hδ (fun x hx => hCδ x (hsubI₀ hx.1))
      have hm := congrArg ENNReal.toReal
        (measure_union_add_inter (μ := levyIntensity) I₀ hC'm)
      rw [ENNReal.toReal_add hfinU hfinD, ENNReal.toReal_add hfinI hfinC'] at hm
      have h := congrArg (fun t : ℝ => 2 * lyapunov * t) hm
      simp only [mul_add] at h
      rw [hCsplit]
      linarith
    rw [hTmod]
    exact ((h1.add h2).sub h3).congr fun n => (hmod n).symm

/-! ## From the stationary law to the level-`j` event

The section family and the identification of the level-`j` event with its
indicator, at a general `B` and at both parities.  This is
`Section5Join.oneLevelEvent_truncWindow` with the sign carried rather than
cancelled. -/

/-- The `θ`-section of the level-`j` mark event at sign `σ`, scale `L` and
digit `a`.  This is the shape `IntervalClass.markSection_signed_isUnionOfIntervals`
bounds. -/
def signedSection (σ L : ℝ) (B : Set ℝ) (a : ℕ) : Set ℝ :=
  {θ : ℝ | θ ∈ Ico (0:ℝ) 1 ∧ σ * (a:ℝ) * W θ / L ∈ B}

lemma measurableSet_signedSection {B : Set ℝ} (hB : MeasurableSet B) (σ L : ℝ) (a : ℕ) :
    MeasurableSet (signedSection σ L B a) :=
  measurableSet_Ico.inter (((measurable_const.mul measurable_W).div_const L) hB)

lemma mem_perSet_signedSection (σ L : ℝ) (B : Set ℝ) (a : ℕ) (θ : ℝ) :
    θ ∈ Selberg.perSet (signedSection σ L B a) ↔ σ * (a:ℝ) * W θ / L ∈ B := by
  unfold Selberg.perSet signedSection
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ico, W_of_fract]
  exact ⟨fun h => h.2, fun h => ⟨⟨Int.fract_nonneg θ, Int.fract_lt_one θ⟩, h⟩⟩

/-- **The `α`-average of the section indicator is the level-`j` event mass**, at
a general `B`.  The sign is carried through `σ = (-1)^j`. -/
theorem oneLevelEvent_section {B : Set ℝ} (hB : MeasurableSet B) (n j : ℕ) :
    unifIoo.real (oneLevelEvent n B j)
      = ∫ α in Ioo (0:ℝ) 1,
          indFull (signedSection ((-1:ℝ) ^ j) (Lnorm n) B) (digit α j) (theta α n j) := by
  have hE : MeasurableSet (oneLevelEvent n B j) := (measurable_signedMark n j) hB
  have hiff : ∀ α : ℝ,
      theta α n j ∈ Selberg.perSet (signedSection ((-1:ℝ) ^ j) (Lnorm n) B (digit α j))
        ↔ α ∈ oneLevelEvent n B j := by
    intro α
    rw [mem_perSet_signedSection]
    have hval : (-1:ℝ) ^ j * (digit α j : ℝ) * W (theta α n j) / Lnorm n
        = signedMark α n j := by
      rw [signedMark, mark]; ring
    rw [hval]
    exact Iff.rfl
  have hind : ∀ α : ℝ,
      indFull (signedSection ((-1:ℝ) ^ j) (Lnorm n) B) (digit α j) (theta α n j)
        = Set.indicator (oneLevelEvent n B j) (fun _ => (1:ℝ)) α := by
    intro α
    unfold indFull Selberg.perInd
    by_cases hc : theta α n j
        ∈ Selberg.perSet (signedSection ((-1:ℝ) ^ j) (Lnorm n) B (digit α j))
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((hiff α).mp hc)]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun h => hc ((hiff α).mpr h))]
  rw [integral_congr_ae (Filter.Eventually.of_forall hind), setIntegral_indicator hE,
    setIntegral_const, smul_eq_mul, mul_one]
  show (unifIoo (oneLevelEvent n B j)).toReal = _
  rw [unifIoo, Measure.restrict_apply hE]
  congr 2
  exact Set.inter_comm _ _

/-! ## The half of `B` a level of a given parity can reach -/

/-- The mark is nonnegative, so a level of sign `σ` sees only
`{x ≥ 0 : σ·x ∈ B}`. -/
def posPart (σ : ℝ) (B : Set ℝ) : Set ℝ := {x : ℝ | 0 ≤ x ∧ σ * x ∈ B}

lemma posPart_eq (σ : ℝ) (B : Set ℝ) :
    posPart σ B = Ici (0:ℝ) ∩ (fun x : ℝ => σ * x) ⁻¹' B := rfl

lemma measurableSet_posPart {B : Set ℝ} (hB : MeasurableSet B) (σ : ℝ) :
    MeasurableSet (posPart σ B) :=
  measurableSet_Ici.inter ((measurable_const.mul measurable_id) hB)

lemma isUnionOfIntervals_posPart {m : ℕ} {B : Set ℝ}
    (hB : IntervalClass.IsUnionOfIntervals m B) (σ : ℝ) :
    IntervalClass.IsUnionOfIntervals m (posPart σ B) := by
  rw [posPart_eq]
  refine hB.inter_preimage ordConnected_Ici ?_
  rcases le_or_gt 0 σ with h | h
  · exact Or.inl fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy h
  · exact Or.inr fun x _ y _ hxy => mul_le_mul_of_nonpos_left hxy h.le

/-- **The stationary side of display (35) at a general `B`.**  The section
indicator averages to the stationary mark law of the reachable half. -/
theorem stationaryMeanR_signedSection {L : ℝ} (hL : 0 < L) (σ : ℝ) (B : Set ℝ) :
    stationaryMeanR (indFull (signedSection σ L B)) = markMean L (posPart σ B) := by
  have hfun : indFull (signedSection σ L B) = markSymb L (posPart σ B) := by
    funext a θ
    have hnn : (0:ℝ) ≤ (a:ℝ) * W θ / L :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg a) (W_nonneg _)) hL.le
    have hval : σ * ((a:ℝ) * W θ / L) = σ * (a:ℝ) * W θ / L := by ring
    have hiff : θ ∈ Selberg.perSet (signedSection σ L B a)
        ↔ (a:ℝ) * W θ / L ∈ posPart σ B := by
      rw [mem_perSet_signedSection]
      constructor
      · intro h
        exact ⟨hnn, by rw [hval]; exact h⟩
      · intro h
        rw [← hval]; exact h.2
    unfold indFull Selberg.perInd
    rw [markSymb_apply]
    by_cases h : θ ∈ Selberg.perSet (signedSection σ L B a)
    · rw [Set.indicator_of_mem h, if_pos (hiff.mp h)]
    · rw [Set.indicator_of_notMem h, if_neg (fun hc => h (hiff.mpr hc))]
  rw [markMean, hfun]

lemma posPart_one {B : Set ℝ} (h0 : (0:ℝ) ∉ B) : posPart 1 B = B ∩ Ioi 0 := by
  ext x
  simp only [posPart, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioi, one_mul]
  constructor
  · rintro ⟨hx0, hxB⟩
    rcases hx0.lt_or_eq with h | h
    · exact ⟨hxB, h⟩
    · rw [← h] at hxB; exact absurd hxB h0
  · rintro ⟨hxB, hx0⟩
    exact ⟨hx0.le, hxB⟩

lemma levyIntensity_posPart_neg {B : Set ℝ} (hB : MeasurableSet B) (h0 : (0:ℝ) ∉ B) :
    levyIntensity (posPart (-1) B) = levyIntensity (B ∩ Iio 0) := by
  have heq : posPart (-1) B = (fun x : ℝ => -x) ⁻¹' (B ∩ Iio 0) := by
    ext x
    simp only [posPart, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Iio,
      neg_one_mul]
    constructor
    · rintro ⟨hx0, hxB⟩
      refine ⟨hxB, ?_⟩
      rcases hx0.lt_or_eq with h | h
      · linarith
      · rw [← h] at hxB
        rw [neg_zero] at hxB
        exact absurd hxB h0
    · rintro ⟨hxB, hx⟩
      exact ⟨by linarith, hxB⟩
  rw [heq, levyIntensity_neg (hB.inter measurableSet_Iio)]

/-! ## Residual (35a), closed -/

/-- **`TupleInputs.oneLevel_gaussKuzmin_intensity_intervals`, proved.**

Display (35) at an arbitrary `IntervalClass.IsFiniteUnionOfIntervals B` bounded
away from the origin and bounded above, unconditionally.  The statement is that
of `Kwon1002/TupleInputs.lean` token for token; the `example` below checks it.

The witnesses are the intended ones: `Λe = Λ(B ∩ (0,∞))`, `Λo = Λ(B ∩ (−∞,0))`,
so the constraint `Λe + Λo = Λ(B)` is `TupleInputs.levyIntensity_split`.

Uniformity in the level is carried entirely by
`Section5Join.oneLevel_transfer`, which is stated for *every* section family of
a fixed interval count; the family here is `signedSection`, of count `2m` by
`IntervalClass.markSection_signed_isUnionOfIntervals`, and the sign `(-1)^j`
enters only through that family and through which half of `B` the level
reaches. -/
theorem oneLevel_gaussKuzmin_intensity_intervals (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (_hint : IntervalClass.IsFiniteUnionOfIntervals B) :
    ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        |Lnorm n * unifIoo.real (oneLevelEvent n B j)
            - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε := by
  obtain ⟨δ, hδ, hBδ⟩ := _hB0
  obtain ⟨R, hBR⟩ := _hBbd
  obtain ⟨m, hm⟩ := _hint
  have h0 : (0:ℝ) ∉ B := by
    intro h
    have := hBδ 0 h
    rw [abs_zero] at this
    linarith
  have hCeδ : ∀ x ∈ posPart 1 B, δ ≤ x := by
    rintro x ⟨hx0, hxB⟩
    rw [one_mul] at hxB
    have := hBδ x hxB
    rwa [abs_of_nonneg hx0] at this
  have hCeR : ∀ x ∈ posPart 1 B, x ≤ R := by
    rintro x ⟨hx0, hxB⟩
    rw [one_mul] at hxB
    have := hBR x hxB
    rwa [abs_of_nonneg hx0] at this
  have hCoδ : ∀ x ∈ posPart (-1) B, δ ≤ x := by
    rintro x ⟨hx0, hxB⟩
    rw [neg_one_mul] at hxB
    have := hBδ (-x) hxB
    rwa [abs_neg, abs_of_nonneg hx0] at this
  have hCoR : ∀ x ∈ posPart (-1) B, x ≤ R := by
    rintro x ⟨hx0, hxB⟩
    rw [neg_one_mul] at hxB
    have := hBR (-x) hxB
    rwa [abs_neg, abs_of_nonneg hx0] at this
  have hfinE : levyIntensity (posPart 1 B) ≠ ⊤ := levyIntensity_ne_top_of_ge hδ hCeδ
  have hfinO : levyIntensity (posPart (-1) B) ≠ ⊤ := levyIntensity_ne_top_of_ge hδ hCoδ
  refine ⟨(levyIntensity (posPart 1 B)).toReal, (levyIntensity (posPart (-1) B)).toReal, ?_, ?_⟩
  · rw [TupleInputs.levyIntensity_split B _hB ⟨δ, hδ, hBδ⟩,
      ← posPart_one h0, ← levyIntensity_posPart_neg _hB h0,
      ENNReal.toReal_add hfinE hfinO]
  intro ε hε
  have hEe : ∀ᶠ n : ℕ in atTop,
      |Lnorm n * markMean (Lnorm n) (posPart 1 B)
        - 2 * lyapunov * (levyIntensity (posPart 1 B)).toReal| ≤ ε / 2 := by
    have hlim := tendsto_scaled_markMean_intervals m hδ (isUnionOfIntervals_posPart hm 1)
      hCeδ hCeR
    have h0' : Tendsto (fun n : ℕ => |Lnorm n * markMean (Lnorm n) (posPart 1 B)
        - 2 * lyapunov * (levyIntensity (posPart 1 B)).toReal|) atTop (𝓝 0) := by
      simpa using (hlim.sub (tendsto_const_nhds
        (x := 2 * lyapunov * (levyIntensity (posPart 1 B)).toReal) (f := atTop))).abs
    exact h0'.eventually_le_const (by linarith)
  have hEo : ∀ᶠ n : ℕ in atTop,
      |Lnorm n * markMean (Lnorm n) (posPart (-1) B)
        - 2 * lyapunov * (levyIntensity (posPart (-1) B)).toReal| ≤ ε / 2 := by
    have hlim := tendsto_scaled_markMean_intervals m hδ (isUnionOfIntervals_posPart hm (-1))
      hCoδ hCoR
    have h0' : Tendsto (fun n : ℕ => |Lnorm n * markMean (Lnorm n) (posPart (-1) B)
        - 2 * lyapunov * (levyIntensity (posPart (-1) B)).toReal|) atTop (𝓝 0) := by
      simpa using (hlim.sub (tendsto_const_nhds
        (x := 2 * lyapunov * (levyIntensity (posPart (-1) B)).toReal) (f := atTop))).abs
    exact h0'.eventually_le_const (by linarith)
  filter_upwards [oneLevel_transfer (2 * m) (half_pos hε), hEe, hEo,
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n htr hen hon hL j hj
  have main : ∀ σ : ℝ, σ = (-1:ℝ) ^ j →
      |Lnorm n * unifIoo.real (oneLevelEvent n B j)
        - Lnorm n * markMean (Lnorm n) (posPart σ B)| ≤ ε / 2 := by
    intro σ hσ
    have hev := htr j hj (signedSection σ (Lnorm n) B)
      (fun a => measurableSet_signedSection _hB σ (Lnorm n) a)
      (fun a => IntervalClass.markSection_signed_isUnionOfIntervals hm σ a (Lnorm n))
    rw [stationaryMeanR_signedSection hL] at hev
    rw [oneLevelEvent_section _hB n j, ← hσ]
    exact hev
  rcases Nat.even_or_odd j with hpar | hpar
  · rw [if_pos hpar]
    have hs : (1:ℝ) = (-1:ℝ) ^ j := (hpar.neg_one_pow).symm
    have h1 := main 1 hs
    have hsplit := abs_sub_le (Lnorm n * unifIoo.real (oneLevelEvent n B j))
      (Lnorm n * markMean (Lnorm n) (posPart 1 B))
      (2 * lyapunov * (levyIntensity (posPart 1 B)).toReal)
    linarith
  · rw [if_neg (Nat.not_even_iff_odd.mpr hpar)]
    have hs : (-1:ℝ) = (-1:ℝ) ^ j := (hpar.neg_one_pow).symm
    have h1 := main (-1) hs
    have hsplit := abs_sub_le (Lnorm n * unifIoo.real (oneLevelEvent n B j))
      (Lnorm n * markMean (Lnorm n) (posPart (-1) B))
      (2 * lyapunov * (levyIntensity (posPart (-1) B)).toReal)
    linarith

/-- **Token-identity check.**  The statement proved above is the canonical
residual `Kwon1002.TupleInputs.oneLevel_gaussKuzmin_intensity_intervals`,
reproduced token for token: this `example` reads the residual's own type and is
discharged by the theorem above. -/
example : ∀ (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) →
    IntervalClass.IsFiniteUnionOfIntervals B →
    ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        |Lnorm n * unifIoo.real (oneLevelEvent n B j)
            - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε :=
  oneLevel_gaussKuzmin_intensity_intervals

/-- The same check in the other direction: `TupleInputs`' declaration has the
type this module's theorem proves. -/
example : ∀ (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) →
    IntervalClass.IsFiniteUnionOfIntervals B →
    ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        |Lnorm n * unifIoo.real (oneLevelEvent n B j)
            - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε :=
  TupleInputs.oneLevel_gaussKuzmin_intensity_intervals

/-! ## The consumer, on the same class

`TupleInputs.deterministic_oneLevel_intensity` is derived from display (35) by
the level count `tendsto_card_div` and the parity balance `tendsto_alt_div`,
both proved.  Since (35) is now proved on the interval class, so is it — the
argument below is `TupleInputs`' own, with the interval hypothesis carried. -/

/-- **`TupleInputs.deterministic_oneLevel_intensity` on the interval class**,
unconditionally.  The only difference from the canonical statement is the added
`IntervalClass.IsFiniteUnionOfIntervals` hypothesis, which is exactly residual
(35b), `TupleInputs.oneLevel_gaussKuzmin_intensity_to_measurable`. -/
theorem deterministic_oneLevel_intensity_intervals (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (_hint : IntervalClass.IsFiniteUnionOfIntervals B) :
    Tendsto (fun n : ℕ => ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) := by
  obtain ⟨Λe, Λo, hsum, hunif⟩ :=
    oneLevel_gaussKuzmin_intensity_intervals B _hB _hB0 _hBbd _hint
  have hlam := OneLevelLaw.lyapunov_pos
  set Λt : ℝ := (levyIntensity B).toReal with hΛt
  set G : ℕ → ℝ := fun n =>
    lyapunov * Λt * (((bulkJ n).card : ℝ) / Lnorm n)
      + lyapunov * (Λe - Λo) * ((∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) / Lnorm n) with hG
  have hlamne : lyapunov ≠ 0 := ne_of_gt hlam
  have hval : lyapunov * Λt * (1 / lyapunov) + lyapunov * (Λe - Λo) * 0 = Λt := by
    rw [mul_zero, add_zero]
    field_simp
  have hGlim : Tendsto G atTop (𝓝 Λt) := by
    rw [← hval]
    exact (TupleInputs.tendsto_card_div.const_mul _).add
      (TupleInputs.tendsto_alt_div.const_mul _)
  have hif : ∀ j : ℕ, 2 * lyapunov * (if Even j then Λe else Λo)
      = lyapunov * (Λe + Λo) + lyapunov * (Λe - Λo) * (-1 : ℝ) ^ j := by
    intro j
    by_cases h : Even j
    · rw [if_pos h, h.neg_one_pow]; ring
    · rw [if_neg h, (Nat.not_even_iff_odd.mp h).neg_one_pow]; ring
  have hSumG : ∀ n : ℕ, (∑ j ∈ bulkJ n, 2 * lyapunov * (if Even j then Λe else Λo))
      = lyapunov * Λt * ((bulkJ n).card : ℝ)
        + lyapunov * (Λe - Λo) * (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) := by
    intro n
    simp_rw [hif]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hsum]
    ring
  have hdiff : Tendsto
      (fun n : ℕ => (∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)) - G n)
      atTop (𝓝 0) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro ε' hε'
    have hεpos : (0 : ℝ) < ε' * lyapunov / 4 := by positivity
    have hcard : ∀ᶠ n : ℕ in atTop, ((bulkJ n).card : ℝ) / Lnorm n ≤ 2 / lyapunov := by
      refine Filter.Tendsto.eventually_le_const ?_ TupleInputs.tendsto_card_div
      rw [div_lt_div_iff₀ hlam hlam]
      nlinarith
    filter_upwards [hunif (ε' * lyapunov / 4) hεpos, hcard,
      TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hn hn2 hL
    have hrw : (∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)) - G n
        = (∑ j ∈ bulkJ n, (Lnorm n * unifIoo.real (oneLevelEvent n B j)
            - 2 * lyapunov * (if Even j then Λe else Λo))) / Lnorm n := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hSumG n, hG]
      field_simp
    have hb : |∑ j ∈ bulkJ n, (Lnorm n * unifIoo.real (oneLevelEvent n B j)
          - 2 * lyapunov * (if Even j then Λe else Λo))|
        ≤ (ε' * lyapunov / 4) * ((bulkJ n).card : ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h := Finset.sum_le_card_nsmul (bulkJ n)
        (fun j => |Lnorm n * unifIoo.real (oneLevelEvent n B j)
          - 2 * lyapunov * (if Even j then Λe else Λo)|)
        (ε' * lyapunov / 4) (fun j hj => hn j hj)
      rw [nsmul_eq_mul] at h
      calc (∑ j ∈ bulkJ n, |Lnorm n * unifIoo.real (oneLevelEvent n B j)
              - 2 * lyapunov * (if Even j then Λe else Λo)|)
          ≤ ((bulkJ n).card : ℝ) * (ε' * lyapunov / 4) := h
        _ = (ε' * lyapunov / 4) * ((bulkJ n).card : ℝ) := by ring
    have hstep : ‖(∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)) - G n‖
        ≤ (ε' * lyapunov / 4) * (((bulkJ n).card : ℝ) / Lnorm n) := by
      rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos hL, div_le_iff₀ hL]
      calc |∑ j ∈ bulkJ n, (Lnorm n * unifIoo.real (oneLevelEvent n B j)
              - 2 * lyapunov * (if Even j then Λe else Λo))|
          ≤ (ε' * lyapunov / 4) * ((bulkJ n).card : ℝ) := hb
        _ = (ε' * lyapunov / 4) * (((bulkJ n).card : ℝ) / Lnorm n) * Lnorm n := by
            field_simp
    refine lt_of_le_of_lt hstep ?_
    have h1 : (ε' * lyapunov / 4) * (((bulkJ n).card : ℝ) / Lnorm n)
        ≤ (ε' * lyapunov / 4) * (2 / lyapunov) :=
      mul_le_mul_of_nonneg_left hn2 hεpos.le
    have h2 : (ε' * lyapunov / 4) * (2 / lyapunov) = ε' / 2 := by field_simp; ring
    rw [h2] at h1
    linarith
  have h := hdiff.add hGlim
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

end

end Section5Intervals

end Kwon1002
