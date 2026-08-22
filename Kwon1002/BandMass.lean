import Kwon1002.Section5Join

/-!
# The band-mass bound: finding (F7), refuted quantitatively

`Kwon1002/CovarianceChain.lean` §9 reduces the `L¹` replacement of the hard
truncation `Z^{(ε)} = Z·1{Z ≤ εL}` by its Lipschitz surrogate to **one**
measure estimate, the hypothesis `hband` of
`CovarianceChain.truncatedMark_sub_lipTrunc_L1_of_band`: a bound on the band
mass

  `vol{α ∈ (0,1) : (1−h)εL < Z_{n,j}(α) ≤ εL}`.

Finding (F7) recorded that no *tail* input can produce it — a law putting its
whole display-(15)-allowed mass just below the cutoff keeps the `L¹` cost at a
constant.  The header of `Kwon1002/Section5Join.lean` records why that
adversary cannot exist here, and this module turns that remark into theorems.

## The two halves, and the gate between them

The mark is `Z_{n,j} = a_{j+1}·W(θ_j)` with `W` the fixed sawtooth average, so
the band is a *geometric* condition on `(a, θ)`, not merely a tail condition on
`Z`:

* the `θ`-half, `IntervalClass.volume_markBand_le`: for **every** digit `a` and
  **every** cutoff `M > 0` the `θ`-section `{θ ∈ [0,1) : (1−h)M < a·W(θ) ≤ M}`
  has measure at most `√(h/(1−h))`;
* the digit half, `Section5Join.markBand_digit_gt`: since `W ≤ 1/8`, the band
  is empty unless `a > 8(1−h)M`, and the Gauss-Kuzmin digit tail
  (`DigitLocalLaw.gaussMeasure_real_digit_zero_ge`, an exact identity) caps
  that at `log(1 + 1/K)/log 2 ≤ 1/(K·log 2)`.

Against the **stationary** law the two multiply, giving band mass
`≤ √(h/(1−h))/(8(1−h)εL·log 2)`.  The gate between the stationary law and the
level-`j` law of `(a_{j+1}(α), θ_j(α))` is `Section5Join.oneLevel_transfer`,
which is proved and is uniform over the deterministic bulk `j ∈ bulkJ n`; the
band's `θ`-sections are unions of two intervals
(`Section5Join.isUnionOfIntervals_truncSection`), which is exactly its
hypothesis.

## What is proved here

* `markBand_mass_le` — the band-mass bound at the level-`j` law, uniform over
  `j ∈ bulkJ n`:
  `L·vol(band) ≤ √(h/(1−h))/(8(1−h)ε·log 2) + ε'`.
* `truncatedMark_sub_lipTrunc_L1_le` — feeding it to the residual interface:
  the `L¹` distance between the hard cutoff and its Lipschitz surrogate is at
  most `√(h/(1−h))/(8(1−h)·log 2) + δ`, uniformly over `j ∈ bulkJ n`.
* `exists_band_width_L1_small` — **the punchline, and the refutation of (F7)'s
  conclusion**: for every `δ > 0` there is a band width `h ∈ (0,1)` making that
  `L¹` distance at most `δ`, eventually in `n` and uniformly over the bulk.
  (F7) asserted this quantity was stuck at a constant; it is not.

## What this does *not* close

`CorFinal.bulk_offdiagonal_abs_far_sharp` needs three things beyond what is
proved here, and only one of them is this one.  See the closing section of
this file for the exact residual.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace BandMass

open Section5Join

noncomputable section

/-! ## Part A, the band as a `truncSection` family -/

/-- The digit threshold of the band: `W ≤ 1/8` puts the band above it. -/
def bandDigit (t : ℝ) : ℕ := ⌊8 * t⌋₊ + 1

lemma one_le_bandDigit (t : ℝ) : 1 ≤ bandDigit t := Nat.le_add_left 1 _

lemma lt_bandDigit (t : ℝ) : 8 * t < (bandDigit t : ℝ) := by
  unfold bandDigit
  push_cast
  exact Nat.lt_floor_add_one (8 * t)

lemma le_of_lt_bandDigit {t : ℝ} (ht : 0 ≤ t) {a : ℕ} (ha : a < bandDigit t) :
    (a : ℝ) ≤ 8 * t := by
  have hle : a ≤ ⌊8 * t⌋₊ := Nat.lt_succ_iff.mp ha
  have h1 : (a : ℝ) ≤ (⌊8 * t⌋₊ : ℝ) := by exact_mod_cast hle
  exact le_trans h1 (Nat.floor_le (by positivity))

/-- **The band is empty below the digit threshold.**  `markBand_digit_gt` at
the level of the `θ`-section family. -/
lemma perSet_truncSection_eq_empty {L ε₁ ε₂ : ℝ} {a : ℕ}
    (ha : (a : ℝ) ≤ 8 * (ε₁ * L)) :
    Selberg.perSet (truncSection L ε₁ ε₂ a) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun θ hθ => ?_
  obtain ⟨hlow, -⟩ := (mem_perSet_truncSection L ε₁ ε₂ a θ).mp hθ
  have hW : W θ ≤ 1 / 8 := W_le_eighth θ
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hbnd : (a : ℝ) * W θ ≤ (a : ℝ) * (1 / 8) := mul_le_mul_of_nonneg_left hW ha0
  linarith

/-- The per-digit mean of a periodised indicator family is the measure of the
periodisation inside the cell. -/
lemma innerMean_indFull_eq {Bs : ℕ → Set ℝ} (hBs : ∀ a, MeasurableSet (Bs a)) (a : ℕ) :
    innerMean (indFull Bs) a
      = (volume (Selberg.perSet (Bs a) ∩ Ioo (0 : ℝ) 1)).toReal := by
  unfold innerMean indFull Selberg.perInd
  rw [setIntegral_indicator (Selberg.measurableSet_perSet (hBs a)), setIntegral_const,
    smul_eq_mul, mul_one, Set.inter_comm (Ioo (0 : ℝ) 1)]
  rfl

/-- **The `θ`-half at the level of `innerMean`.**  For every digit, the
per-digit mean of the band indicator is at most `√(h/(1−h))`. -/
lemma innerMean_indFull_truncSection_le {L ε h : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hh0 : 0 < h) (hh1 : h < 1) (a : ℕ) :
    innerMean (indFull (truncSection L ((1 - h) * ε) ε)) a
      ≤ Real.sqrt (h / (1 - h)) := by
  have hM : (0 : ℝ) < ε * L := by positivity
  rw [innerMean_indFull_eq (fun b => measurableSet_truncSection L ((1 - h) * ε) ε b) a]
  set T : Set ℝ := {θ : ℝ | θ ∈ Ico (0 : ℝ) 1 ∧
      (1 - h) * (ε * L) < (a : ℝ) * W θ ∧ (a : ℝ) * W θ ≤ ε * L} with hT
  have hsub : Selberg.perSet (truncSection L ((1 - h) * ε) ε a) ∩ Ioo (0 : ℝ) 1 ⊆ T := by
    rintro θ ⟨hp, hθ⟩
    obtain ⟨h1, h2⟩ := (mem_perSet_truncSection L ((1 - h) * ε) ε a θ).mp hp
    exact ⟨⟨hθ.1.le, hθ.2⟩, by linarith [mul_assoc (1 - h) ε L], h2⟩
  have hfin : volume T ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun θ hθ => hθ.1))
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  refine le_trans (ENNReal.toReal_mono hfin (measure_mono hsub)) ?_
  exact IntervalClass.volume_markBand_le a hM hh0 hh1

/-! ## Part B, the stationary band mass -/

/-- **The stationary band mass.**  The two halves multiply: the `θ`-section is
capped at `√(h/(1−h))` uniformly in the digit, and the band lives above digit
`8(1−h)εL`, whose exact Gauss-Kuzmin mass is `log(1 + 1/K)/log 2`. -/
theorem stationaryMeanR_band_le {L ε h : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hh0 : 0 < h) (hh1 : h < 1) :
    stationaryMeanR (indFull (truncSection L ((1 - h) * ε) ε))
      ≤ Real.sqrt (h / (1 - h))
          * (Real.log (1 + 1 / ((bandDigit ((1 - h) * ε * L) : ℕ) : ℝ)) / Real.log 2) := by
  classical
  set Bs : ℕ → Set ℝ := truncSection L ((1 - h) * ε) ε with hBs
  set S : ℝ := Real.sqrt (h / (1 - h)) with hS
  have hS0 : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  set K : ℕ := bandDigit ((1 - h) * ε * L) with hK
  have hKt : (0 : ℝ) ≤ (1 - h) * ε * L := by
    have : (0 : ℝ) < 1 - h := by linarith
    positivity
  have hBsm : ∀ a, MeasurableSet (Bs a) := fun a => measurableSet_truncSection L _ _ a
  -- the pointwise majorant
  have hpt : ∀ x : ℝ, innerMean (indFull Bs) (digit x 0)
      ≤ S * (if K ≤ digit x 0 then (1 : ℝ) else 0) := by
    intro x
    by_cases hc : K ≤ digit x 0
    · rw [if_pos hc, mul_one]
      exact innerMean_indFull_truncSection_le hL hε hh0 hh1 _
    · rw [if_neg hc, mul_zero]
      have hsmall : ((digit x 0 : ℕ) : ℝ) ≤ 8 * ((1 - h) * ε * L) :=
        le_of_lt_bandDigit hKt (not_le.mp hc)
      have hempty : Selberg.perSet (Bs (digit x 0)) = ∅ := by
        refine perSet_truncSection_eq_empty ?_
        simpa [mul_assoc] using hsmall
      rw [innerMean_indFull_eq hBsm, hempty]
      simp
  -- integrate
  have hIc : Integrable (fun x : ℝ => innerMean (indFull Bs) (digit x 0))
      Erdos1002.gaussMeasure :=
    integrable_innerMean_comp (indFull Bs) (abs_innerMean_le_of_bound (abs_indFull_le Bs))
  set T : Set ℝ := {x : ℝ | K ≤ digit x 0} with hT
  have hTmeas : MeasurableSet T :=
    (measurable_digit 0) (measurableSet_le measurable_const measurable_id)
  have hind : (fun x : ℝ => (if K ≤ digit x 0 then (1 : ℝ) else 0))
      = Set.indicator T (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : K ≤ digit x 0
    · rw [if_pos hx, Set.indicator_of_mem (show x ∈ T from hx)]
    · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ T from hx)]
  have hIT : Integrable (fun x : ℝ => (if K ≤ digit x 0 then (1 : ℝ) else 0))
      Erdos1002.gaussMeasure := by
    rw [hind]; exact (integrable_const (1 : ℝ)).indicator hTmeas
  have hmono : stationaryMeanR (indFull Bs)
      ≤ ∫ x, S * (if K ≤ digit x 0 then (1 : ℝ) else 0) ∂Erdos1002.gaussMeasure := by
    rw [stationaryMeanR_eq]
    exact integral_mono hIc (hIT.const_mul S) hpt
  refine le_trans hmono (le_of_eq ?_)
  rw [integral_const_mul, hind, integral_indicator_const (1 : ℝ) hTmeas]
  simp only [smul_eq_mul, mul_one]
  refine congrArg (fun t : ℝ => S * t) ?_
  show (Erdos1002.gaussMeasure T).toReal = _
  exact DigitLocalLaw.gaussMeasure_real_digit_zero_ge (one_le_bandDigit _)

/-- The stationary band mass, in the shape the interface consumes:
`L · (stationary band mass) ≤ √(h/(1−h))/(8(1−h)ε·log 2)`. -/
theorem scaled_stationaryMeanR_band_le {L ε h : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hh0 : 0 < h) (hh1 : h < 1) :
    L * stationaryMeanR (indFull (truncSection L ((1 - h) * ε) ε))
      ≤ Real.sqrt (h / (1 - h)) / (8 * (1 - h) * ε * Real.log 2) := by
  set S : ℝ := Real.sqrt (h / (1 - h)) with hS
  have hS0 : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  have hh : (0 : ℝ) < 1 - h := by linarith
  set K : ℕ := bandDigit ((1 - h) * ε * L) with hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : (1 : ℕ) ≤ K := one_le_bandDigit _
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbig : 8 * ((1 - h) * ε * L) < (K : ℝ) := lt_bandDigit _
  have hMpos : (0 : ℝ) < 8 * ((1 - h) * ε * L) := by positivity
  -- `log(1+1/K) ≤ 1/K`
  have hlogle : Real.log (1 + 1 / (K : ℝ)) ≤ 1 / (K : ℝ) := by
    have h1 : (0 : ℝ) < 1 + 1 / (K : ℝ) := by positivity
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hinv : 1 / (K : ℝ) ≤ 1 / (8 * ((1 - h) * ε * L)) :=
    one_div_le_one_div_of_le hMpos hbig.le
  have hstat := stationaryMeanR_band_le (L := L) (ε := ε) (h := h) hL hε hh0 hh1
  have hchain : Real.log (1 + 1 / (K : ℝ)) / Real.log 2
      ≤ (1 / (8 * ((1 - h) * ε * L))) / Real.log 2 := by
    refine div_le_div_of_nonneg_right ?_ hlog2.le
    linarith
  have hstat2 : stationaryMeanR (indFull (truncSection L ((1 - h) * ε) ε))
      ≤ S * ((1 / (8 * ((1 - h) * ε * L))) / Real.log 2) :=
    le_trans hstat (mul_le_mul_of_nonneg_left hchain hS0)
  have hfinal : L * (S * ((1 / (8 * ((1 - h) * ε * L))) / Real.log 2))
      = S / (8 * (1 - h) * ε * Real.log 2) := by
    field_simp
  calc L * stationaryMeanR (indFull (truncSection L ((1 - h) * ε) ε))
      ≤ L * (S * ((1 / (8 * ((1 - h) * ε * L))) / Real.log 2)) :=
        mul_le_mul_of_nonneg_left hstat2 hL.le
    _ = S / (8 * (1 - h) * ε * Real.log 2) := hfinal

/-! ## Part C, the level-`j` band mass -/

/-- The level-`j` `α`-average of the band indicator **is** the band mass. -/
lemma integral_indFull_band_eq (ε h : ℝ) (n j : ℕ) :
    (∫ α in Ioo (0 : ℝ) 1,
        indFull (truncSection (Lnorm n) ((1 - h) * ε) ε) (digit α j) (theta α n j))
      = (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          (1 - h) * (ε * Lnorm n) < mark α n j ∧ mark α n j ≤ ε * Lnorm n}).toReal := by
  classical
  set E : Set ℝ := {α : ℝ |
      (1 - h) * (ε * Lnorm n) < mark α n j ∧ mark α n j ≤ ε * Lnorm n} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const (measurable_mark n j)).inter
      (measurableSet_le (measurable_mark n j) measurable_const)
  have hiff : ∀ α : ℝ,
      theta α n j ∈ Selberg.perSet (truncSection (Lnorm n) ((1 - h) * ε) ε (digit α j))
        ↔ α ∈ E := by
    intro α
    rw [mem_perSet_truncSection]
    have hmk : ((digit α j : ℕ) : ℝ) * W (theta α n j) = mark α n j := rfl
    rw [hmk, hE]
    simp only [Set.mem_setOf_eq]
    rw [mul_assoc]
  have hind : ∀ α : ℝ,
      indFull (truncSection (Lnorm n) ((1 - h) * ε) ε) (digit α j) (theta α n j)
        = Set.indicator E (fun _ => (1 : ℝ)) α := by
    intro α
    unfold indFull Selberg.perInd
    by_cases hc : theta α n j
        ∈ Selberg.perSet (truncSection (Lnorm n) ((1 - h) * ε) ε (digit α j))
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((hiff α).mp hc)]
    · rw [Set.indicator_of_notMem hc,
        Set.indicator_of_notMem (fun hx => hc ((hiff α).mpr hx))]
  rw [integral_congr_ae (Filter.Eventually.of_forall hind), setIntegral_indicator hEm,
    setIntegral_const, smul_eq_mul, mul_one]
  rfl

/-- **The band-mass bound, at the level-`j` law.**  Uniformly over the
deterministic bulk `j ∈ J_n`, and eventually in `n`,

  `L · vol{α : (1−h)εL < Z_{n,j}(α) ≤ εL} ≤ √(h/(1−h))/(8(1−h)ε·log 2) + ε'`.

This is the hypothesis `hband` of
`CovarianceChain.truncatedMark_sub_lipTrunc_L1_of_band`, at the scale the
interface consumes it.  The gate between the stationary law (Part B) and the
level-`j` law is `Section5Join.oneLevel_transfer`, whose interval-class
hypothesis is met by `isUnionOfIntervals_truncSection`. -/
theorem markBand_mass_le {h ε : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (hε : 0 < ε)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      Lnorm n * (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          (1 - h) * (ε * Lnorm n) < mark α n j ∧ mark α n j ≤ ε * Lnorm n}).toReal
        ≤ Real.sqrt (h / (1 - h)) / (8 * (1 - h) * ε * Real.log 2) + ε' := by
  filter_upwards [oneLevel_transfer 2 hε',
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n htr hL j hj
  have hev := htr j hj (truncSection (Lnorm n) ((1 - h) * ε) ε)
    (measurableSet_truncSection (Lnorm n) ((1 - h) * ε) ε)
    (isUnionOfIntervals_truncSection (Lnorm n) ((1 - h) * ε) ε)
  rw [integral_indFull_band_eq ε h n j] at hev
  have hstat := scaled_stationaryMeanR_band_le (L := Lnorm n) (ε := ε) (h := h) hL hε hh0 hh1
  have habs := abs_le.mp hev
  linarith [habs.2, hstat]

/-! ## Part D, the residual interface, discharged -/

/-- **The `L¹` distance to the Lipschitz surrogate, bounded by the band
width.**  `CovarianceChain.truncatedMark_sub_lipTrunc_L1_of_band` fed with
`markBand_mass_le`: uniformly over `j ∈ J_n` and eventually in `n`,

  `E|Z^{(ε)} − lipTrunc(Z)| ≤ √(h/(1−h))/(8(1−h)·log 2) + δ`.

Note the `ε` has cancelled: the bound depends on the band width alone. -/
theorem truncatedMark_sub_lipTrunc_L1_le {h ε : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (hε : 0 < ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      (∫ α in Ioo (0 : ℝ) 1,
          |truncatedMark ε α n j
            - CovarianceChain.lipTrunc (ε * Lnorm n) (h * (ε * Lnorm n)) (mark α n j)|)
        ≤ Real.sqrt (h / (1 - h)) / (8 * (1 - h) * Real.log 2) + δ := by
  have hδε : (0 : ℝ) < δ / ε := by positivity
  filter_upwards [markBand_mass_le hh0 hh1 hε hδε,
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hband hL j hj
  set L : ℝ := Lnorm n with hLdef
  set m : ℝ := (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      (1 - h) * (ε * L) < mark α n j ∧ mark α n j ≤ ε * L}).toReal with hm
  have hmle : L * m ≤ Real.sqrt (h / (1 - h)) / (8 * (1 - h) * ε * Real.log 2) + δ / ε :=
    hband j hj
  have hkey := CovarianceChain.truncatedMark_sub_lipTrunc_L1_of_band ε h m hε hh0 hh1 n j hL
    (le_of_eq rfl)
  refine le_trans hkey ?_
  have hstep : ε * L * m = ε * (L * m) := by ring
  rw [hstep]
  have hmul : ε * (L * m)
      ≤ ε * (Real.sqrt (h / (1 - h)) / (8 * (1 - h) * ε * Real.log 2) + δ / ε) :=
    mul_le_mul_of_nonneg_left hmle hε.le
  refine le_trans hmul (le_of_eq ?_)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hh : (0 : ℝ) < 1 - h := by linarith
  field_simp

/-- **The punchline: finding (F7)'s conclusion is false.**  For every `δ > 0`
there is a band width `h ∈ (0,1)` at which the `L¹` distance between the hard
cutoff and its Lipschitz surrogate is at most `δ`, uniformly over the
deterministic bulk and eventually in `n`.

(F7) argued that this distance is stuck at a constant, because the display-(15)
*tails* permit a law with its whole allowed mass sitting just below the cutoff.
That law cannot exist: the mark is `a·W(θ)` with `W` a fixed sawtooth average,
and `IntervalClass.volume_markBand_le` caps the `θ`-section of the band at
`√(h/(1−h))` for every digit and every cutoff. -/
theorem exists_band_width_L1_small {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        (∫ α in Ioo (0 : ℝ) 1,
            |truncatedMark ε α n j
              - CovarianceChain.lipTrunc (ε * Lnorm n) (h * (ε * Lnorm n)) (mark α n j)|)
          ≤ δ := by
  set h : ℝ := min (1 / 2) (δ ^ 2 / 8) with hhdef
  have hh0 : (0 : ℝ) < h := lt_min (by norm_num) (by positivity)
  have hhalf : h ≤ 1 / 2 := min_le_left _ _
  have hhδ : h ≤ δ ^ 2 / 8 := min_le_right _ _
  have hh1 : h < 1 := by linarith
  have honeh : (1 : ℝ) / 2 ≤ 1 - h := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- `√(h/(1−h)) ≤ δ/2`
  have hquot : h / (1 - h) ≤ δ ^ 2 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg δ]
  have hsqrt : Real.sqrt (h / (1 - h)) ≤ δ / 2 := by
    have hd : Real.sqrt (δ ^ 2 / 4) = δ / 2 := by
      rw [show δ ^ 2 / 4 = (δ / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc Real.sqrt (h / (1 - h)) ≤ Real.sqrt (δ ^ 2 / 4) := Real.sqrt_le_sqrt hquot
      _ = δ / 2 := hd
  have hbnd : Real.sqrt (h / (1 - h)) / (8 * (1 - h) * Real.log 2) ≤ δ / 2 := by
    have hden : (2 : ℝ) ≤ 8 * (1 - h) * Real.log 2 := by nlinarith
    have hden0 : (0 : ℝ) < 8 * (1 - h) * Real.log 2 := by linarith
    rw [div_le_iff₀ hden0]
    nlinarith [hsqrt, hδ.le, Real.sqrt_nonneg (h / (1 - h))]
  refine ⟨h, hh0, hh1, ?_⟩
  filter_upwards [truncatedMark_sub_lipTrunc_L1_le hh0 hh1 hε (half_pos hδ)] with n hn j hj
  exact le_trans (hn j hj) (by linarith)

/-! ## Part E, non-vacuity, and the exact residual that remains -/

/-- **Non-vacuity.**  The bulk `J_n` over which the statements above quantify
is eventually nonempty (`OneLevelLaw.eventually_bulkJ_nonempty`), so none of
them is an empty quantification. -/
theorem exists_band_width_L1_small_nonvacuous {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∀ᶠ n : ℕ in atTop, (bulkJ n).Nonempty ∧
        ∀ j ∈ bulkJ n,
          (∫ α in Ioo (0 : ℝ) 1,
              |truncatedMark ε α n j
                - CovarianceChain.lipTrunc (ε * Lnorm n) (h * (ε * Lnorm n)) (mark α n j)|)
            ≤ δ := by
  obtain ⟨h, hh0, hh1, hev⟩ := exists_band_width_L1_small hε hδ
  refine ⟨h, hh0, hh1, ?_⟩
  filter_upwards [hev, OneLevelLaw.eventually_bulkJ_nonempty] with n hn hne
  exact ⟨hne, hn⟩

/-! ### What still stands between this and `bulk_offdiagonal_abs_far_sharp`

The band-mass estimate above is the input finding (F7) named as missing, and
it is now proved.  It is **not** the whole of
`CorFinal.bulk_offdiagonal_abs_far_sharp`, and the honest list of what is still
owed is short and specific:

1. **Proposition 4.1 at `r = 2` for the Lipschitz surrogate.**
   `Kwon1002.Prop41.prop_4_1_error_shape` and
   `Kwon1002.prop_4_1_marked_factorization` are proved outright
   (`Kwon1002/Prop41Unconditional.lean`), and `CovarianceChain` §3 records that
   they are not reachable from where the residual is declared.  Wiring them to
   the pair covariance in a module importing both sides is mechanical but is a
   piece of work in its own right; nothing in this module does it.

2. **The covariance-currency window bridge, which does not exist in the
   tree.**  `oneLevel_transfer` — and hence everything proved above — is
   uniform only over `j ∈ bulkJ n`, the deterministic bulk of display (19),
   while the off-diagonal sum of `CorFinal.offdiagAbsTerm` runs over
   `range (n+1) ×ˢ range (n+1)`.  The `O(H)` gap at each end is bridged at
   every arity by the proved `TupleFinal.bulk_window_bridge_tuple`, but in the
   wrong currency: that bridge speaks about
   `unifIoo.real (tupleEvent (bulkMarkEvent c n B) f)`, the measure of an
   event, whereas `offdiagAbsTerm` is `|∫ g_j·g_k|` for the *centred*
   observable `g = bulkTermCentered`, which equals `−E g_j` rather than `0`
   off the bulk.  Nothing in this module supplies that analogue, and nothing
   in the tree does either.

   The per-level families now available (`WindowBridgeFamily.exists_window_bridge_family`,
   `DetQuasiFamily.exists_det_quasi_independence_family`) are stated in the same
   event currency, and `PatternSum.sum_emb_pattern_le` converts a per-level
   family bound into a per-position pattern bound *inside that currency*; none
   of them changes the currency, so the analogue is a genuine piece of new
   mathematics rather than a rearrangement of existing statements.

3. **The digit cut and the pair count**, both already proved
   (`CovarianceChain.truncatedMark_digitCut_L1`,
   `CorFinal.card_sharpen`/`abs_far_sharp_of_abs_far`), but again on the other
   side of the module direction.

So `CorFinal.bulk_offdiagonal_abs_far_sharp` remains open, and item 2 above is
the one part of it that is not present in the tree in any currency.
-/

end

end BandMass

end Kwon1002
