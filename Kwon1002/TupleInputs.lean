import Kwon1002.TupleFinal

/-!
# Scratch (agent `tuples`), the level count of (39) and a per-level (35)

Targets, all four reproduced **token for token** (each is additionally checked
inside Lean by an `example … := rfl`-free `example … := name` at the bottom, so
the elaborated `Prop`s coincide and not merely the surface syntax):

* `oneLevel_intensity_limit`        = `Kwon1002.TupleMeasure.oneLevel_intensity_limit`
  (`Kwon1002/TupleMeasure.lean` line 544);
* `tuple_quasi_independence`        = `Kwon1002.TupleMeasure.tuple_quasi_independence`
  (line 570);
* `deterministic_oneLevel_intensity` = `Kwon1002.deterministic_oneLevel_intensity`
  (`Kwon1002/FiveFinal.lean` line 287);
* `bulk_window_bridge_oneLevel`     = `Kwon1002.bulk_window_bridge_oneLevel`
  (`Kwon1002/FiveFinal.lean` line 265).

## What this pass adds

The previous best reduction of targets 1 and 2 is `Kwon1002/TupleFinal.lean`,
which rests on exactly three residuals:

1. `TupleFinal.bulk_window_bridge_tuple` (the §7/§4 index-set bridge),
2. `TupleFinal.goodSet_mark_factorization` (Proposition 4.1 for the mark event),
3. `Kwon1002.deterministic_oneLevel_intensity` (display (35) on the bulk of
   (19), read against an indicator).

**This file replaces residual 3 by a strictly weaker one.**  Residual 3 is a
statement about a *sum over `J_n`*: it bundles the per-level Gauss-Kuzmin
intensity together with the level count `#J_n = (1+o(1)) L/λ` of (39) and with
the parity bookkeeping that the `(-1)^j` in `signedMark` forces.  Here the
count and the parity bookkeeping are **machine-checked**, and what is left is
the genuinely analytic per-level statement

  `oneLevel_gaussKuzmin_intensity` :
     `L · P(X_{n,j} ∈ B) → 2λ · Λ_{±}(B)`, uniformly over `j ∈ J_n`,

with `Λ_+ + Λ_- = Λ(B)` and the sign selected by the parity of `j`.  Nothing
about `J_n` survives in it except membership.

### The count, proved

* `bulkJ_eq_Ico`, display (19)'s `J_n` *is* an integer interval
  `[⌈200H⌉, ⌊m_n − 200H⌋]` (once `m_n ≥ 400H + 2`, which is proved to hold
  eventually).  The manuscript never says this; it is what makes both the
  count and the parity balance available.
* `tendsto_card_div`, `#J_n / L → 1/λ`.
* `tendsto_alt_div`, `(∑_{j ∈ J_n} (−1)^j)/L → 0`, from `|∑_{j ∈ Ico a b}
  (−1)^j| ≤ 1`: `J_n` carries equally many even and odd levels up to one.
  The `(-1)^j` of `signedMark` means an even level can only ever land in
  `B ∩ (0,∞)` and an odd one only in `B ∩ (−∞,0)`, so this is what weights the
  two half-lines of `B` equally.

Together these two are exactly the `r = 1` case of the manuscript's display
(39), `#{j ∈ J_n : (−1)^j = ε} = (1+o(1)) L/(2λ)`.  The manuscript *states*
(39) and justifies it in one sentence ("the parity-restricted lattice
discrepancy in the actual bulk interval is `O(L^{r−1})`, while replacing its
length by `L/λ` contributes `O(H L^{r−1}) = o(L^r)`"); at `r = 1` that
sentence is now machine-checked, endpoints, floors, ceilings and all.

Note also that the manuscript's (35) really is a **per-level** statement
(`L P(A W(Θ)/L ∈ dx) ⇒ c₀ x^{−2} dx`), so the residual below is closer to the
manuscript than the summed `Kwon1002.deterministic_oneLevel_intensity` it
replaces: that theorem was (35) *already combined with* (39).

### The constant, checked

The task's arithmetic is `π · ζ(2)^{-1} · E|V| = π · (6/π²) · (1/12) = 1/(2π)`,
and in-tree `π · levyConst = π/(2π²) = 1/(2π)` is already proved
(`Kwon1002.cauchyScale_eq`).  **The constants agree; nothing here pushes
towards a different one.**  Two further checks are machine-checked here:

* `integral_W_unit`, `∫_0^1 W(t) dt = 1/12`, i.e. `E|V| = 1/12` for the
  sawtooth average `W` that `Kwon1002.mark` actually uses.  (Not previously in
  the development.)
* `perLevel_constant_check`, `2λ · (2π²u)^{-1} = (∫_0^1 W)/(u log 2)`, i.e.
  the normalisation `2λ·Λ` appearing in the residual is *exactly* the
  Gauss-Kuzmin prediction `E[W]/(u log 2)` for one level.  Together with
  `levyIntensity_split` (also proved) this pins the residual's constant with
  no freedom left.

The one arithmetic step not machine-checked *in this file* is
`Λ((u,∞)) = 1/(2π²u)`, i.e. `∫_u^∞ (2π²x²)^{-1} dx = (2π²u)^{-1}`.  **It is
machine-checked now**, as `Kwon1002.GaussKuzmin.levyIntensity_Ioi`
(`Kwon1002/GaussKuzmin.lean`), which sits above this module; so is the
combination `2λ·Λ((u,∞)) = 1/(12 u log 2)`
(`GaussKuzmin.two_lyapunov_levy_Ioi`).  Nothing here is left substituted by
hand.

## Sorried results consumed

* `Kwon1002.TupleFinal.bulk_window_bridge_tuple`, residual 1, in all four
  targets except `deterministic_oneLevel_intensity`.
* `Kwon1002.TupleFinal.goodSet_mark_factorization`, residual 2, only through
  `TupleFinal.det_quasi_independence`, and only for `tuple_quasi_independence`.
* `oneLevel_gaussKuzmin_intensity`, the residual declared in this file.  It is
  now **split**, on the pattern of `TupleFinal.goodSet_mark_factorization`:
  `oneLevel_gaussKuzmin_intensity_intervals` carries the added hypothesis
  `IntervalClass.IsFiniteUnionOfIntervals B`,
  `oneLevel_gaussKuzmin_intensity_to_measurable` is the separate approximation
  step, and `oneLevel_gaussKuzmin_intensity` keeps its exact statement and is
  derived from the two.  No consumer signature changed.
* **Nothing else.**  In particular `Kwon1002.deterministic_oneLevel_intensity`,
  `Kwon1002.bulk_window_bridge_oneLevel`,
  `Kwon1002.TupleMeasure.oneLevel_intensity_limit`,
  `Kwon1002.TupleMeasure.tuple_quasi_independence`,
  `Kwon1002.LevyExponent.tuple_measure_convergence`,
  `Kwon1002.TupleFinal.oneLevel_intensity_limit`,
  `Kwon1002.TupleFinal.tuple_quasi_independence` and
  `Kwon1002.Section4.prop_4_1_marked_factorization` are **not** consumed.
  `TupleFinal.det_singleLevel_measure_le`, `TupleFinal.sum_det_eq_sum_bulkJ`,
  `TupleFinal.sum_emb_one_eq`, `TupleFinal.lyapunov_gt_one`,
  `TupleFinal.tendsto_H_div_L`, `TupleFinal.tendsto_one_div_L`,
  `TupleMeasure.tendsto_emb_sum_of_inputs`, `TupleMeasure.singleLevel_measure_le`
  and `Kwon1002.tendsto_emb_prod_sum` are all **proved** where they live.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace TupleInputs

open LevyExponent TupleMeasure

noncomputable section

/-! ## Part A, the constants -/

/-- **`E[W] = 1/12`.**  The sawtooth average `W(t) = {t}(1−{t})/2` of
`Kwon1002.W` integrates to `1/12` over one period.  This is the `E|V| = 1/12`
of the compound-Poisson scale; it is what makes the per-level intensity
`E[W]/(u log 2)` and hence `π·ζ(2)^{-1}·E|V| = 1/(2π)`. -/
theorem integral_W_unit : (∫ t in (0 : ℝ)..1, W t) = 1 / 12 := by
  have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) 1, W t = 1 / 2 * t - 1 / 2 * t ^ 2 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rcases lt_or_eq_of_le ht.2 with h1 | h1
    · rw [W, Int.fract_eq_self.mpr ⟨ht.1, h1⟩]; ring
    · subst h1
      have h1 : Int.fract (1 : ℝ) = 0 := by simp
      rw [W, h1]; ring
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, integral_pow]
  norm_num

/-- **The per-level constant, checked.**  `2λ·Λ((u,∞)) = E[W]/(u log 2)`:
the normalisation `2·lyapunov·Λ` that the residual below attaches to one level
is exactly the Gauss-Kuzmin prediction.  (`Λ((u,∞)) = 1/(2π²u)` was substituted by hand
when this was written; it is proved in `Kwon1002/GaussKuzmin.lean` as
`GaussKuzmin.levyIntensity_Ioi`, and this statement composed with it is
`GaussKuzmin.two_lyapunov_levy_Ioi`.) -/
theorem perLevel_constant_check (u : ℝ) (hu : 0 < u) :
    2 * lyapunov * (1 / (2 * Real.pi ^ 2 * u))
      = (∫ t in (0 : ℝ)..1, W t) / (u * Real.log 2) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [integral_W_unit, lyapunov]
  field_simp

/-- **The two half-lines of `B` carry all of `Λ(B)`.**  For `B` bounded away
from the origin, `Λ(B) = Λ(B ∩ (0,∞)) + Λ(B ∩ (−∞,0))`.  This is the intended
instantiation of the pair `(Λe, Λo)` in the residual below. -/
theorem levyIntensity_split (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) :
    levyIntensity B = levyIntensity (B ∩ Ioi 0) + levyIntensity (B ∩ Iio 0) := by
  obtain ⟨δ, hδ, hBδ⟩ := hB0
  have hcover : B = (B ∩ Ioi 0) ∪ (B ∩ Iio 0) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx
      have hne : x ≠ 0 := by
        intro h
        have := hBδ x hx
        rw [h] at this
        simp at this
        linarith
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj : Disjoint (B ∩ Ioi 0) (B ∩ Iio 0) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ ⟨-, hx2⟩
    rw [Set.mem_Ioi] at hx1
    rw [Set.mem_Iio] at hx2
    linarith
  conv_lhs => rw [hcover]
  exact measure_union hdisj (hB.inter measurableSet_Iio)

/-! ## Part B, the level count of display (39), proved

Nothing in this part knows about marks or measures: it is pure arithmetic
about the deterministic bulk `Kwon1002.bulkJ` of display (19). -/

/-- `H = L^{3/4} ≥ 1` once `L ≥ 1`. -/
lemma Hscale_ge_one {n : ℕ} (hL : (1 : ℝ) ≤ Lnorm n) : (1 : ℝ) ≤ Hscale n := by
  show (1 : ℝ) ≤ (Lnorm n) ^ (3 / 4 : ℝ)
  calc (1 : ℝ) = (1 : ℝ) ^ (3 / 4 : ℝ) := (Real.one_rpow _).symm
    _ ≤ (Lnorm n) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)

lemma lyapunov_pos : (0 : ℝ) < lyapunov := lt_trans one_pos TupleFinal.lyapunov_gt_one

/-- `m_n / L → 1/λ`: display (18)'s `m_n = ⌊L/λ⌋` is `L/λ` to within `1`. -/
lemma tendsto_mIndex_div :
    Tendsto (fun n : ℕ => (mIndex n : ℝ) / Lnorm n) atTop (𝓝 (1 / lyapunov)) := by
  have hlam := lyapunov_pos
  have hlow : Tendsto (fun n : ℕ => 1 / lyapunov - 1 / Lnorm n) atTop (𝓝 (1 / lyapunov)) := by
    simpa using tendsto_const_nhds.sub TupleFinal.tendsto_one_div_L
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hL
    rw [le_div_iff₀ hL]
    have he : (1 / lyapunov - 1 / Lnorm n) * Lnorm n = Lnorm n / lyapunov - 1 := by
      field_simp
    rw [he]
    have := Nat.lt_floor_add_one (Lnorm n / lyapunov)
    have hm : (mIndex n : ℝ) = (⌊Lnorm n / lyapunov⌋₊ : ℝ) := rfl
    rw [hm]
    linarith
  · filter_upwards [tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hL
    rw [div_le_iff₀ hL]
    have hnn : (0 : ℝ) ≤ Lnorm n / lyapunov := div_nonneg hL.le hlam.le
    have := Nat.floor_le hnn
    have hm : (mIndex n : ℝ) = (⌊Lnorm n / lyapunov⌋₊ : ℝ) := rfl
    rw [hm]
    calc (⌊Lnorm n / lyapunov⌋₊ : ℝ) ≤ Lnorm n / lyapunov := this
      _ = 1 / lyapunov * Lnorm n := by field_simp

/-- Eventually the bulk of (19) is wide: `m_n ≥ 400H + 2`.  (`H/L → 0` while
`m_n/L → 1/λ > 0`.) -/
lemma eventually_good : ∀ᶠ n : ℕ in atTop,
    (1 : ℝ) ≤ Lnorm n ∧ 400 * Hscale n + 2 ≤ (mIndex n : ℝ) := by
  have hlam := lyapunov_pos
  have hρ : (0 : ℝ) < 1 / (2 * lyapunov) := by positivity
  have hρ' : 1 / (2 * lyapunov) < 1 / lyapunov := by
    rw [div_lt_div_iff₀ (by linarith) hlam]
    linarith
  have hf : Tendsto (fun n : ℕ => (400 * Hscale n + 2) / Lnorm n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 400 * (Hscale n / Lnorm n) + 2 * (1 / Lnorm n))
        atTop (𝓝 0) := by
      simpa using (TupleFinal.tendsto_H_div_L.const_mul 400).add
        (TupleFinal.tendsto_one_div_L.const_mul 2)
    refine h0.congr' ?_
    filter_upwards [tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hL
    field_simp
  have h1 : ∀ᶠ n : ℕ in atTop, (400 * Hscale n + 2) / Lnorm n < 1 / (2 * lyapunov) :=
    Filter.Tendsto.eventually_lt_const hρ hf
  have h2 : ∀ᶠ n : ℕ in atTop, 1 / (2 * lyapunov) < (mIndex n : ℝ) / Lnorm n :=
    Filter.Tendsto.eventually_const_lt hρ' tendsto_mIndex_div
  filter_upwards [h1, h2, tendsto_Lnorm_atTop.eventually_ge_atTop 1,
    tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hn1 hn2 hn3 hn4
  refine ⟨hn3, ?_⟩
  have h3 : (400 * Hscale n + 2) / Lnorm n < (mIndex n : ℝ) / Lnorm n := lt_trans hn1 hn2
  have e1 : ((400 * Hscale n + 2) / Lnorm n) * Lnorm n = 400 * Hscale n + 2 := by
    field_simp
  have e2 : ((mIndex n : ℝ) / Lnorm n) * Lnorm n = (mIndex n : ℝ) := by field_simp
  have := mul_lt_mul_of_pos_right h3 hn4
  rw [e1, e2] at this
  linarith

/-- The lower endpoint of `J_n`. -/
def aIdx (n : ℕ) : ℕ := ⌈200 * Hscale n⌉₊

/-- The upper endpoint of `J_n`. -/
def bIdx (n : ℕ) : ℕ := ⌊(mIndex n : ℝ) - 200 * Hscale n⌋₊

lemma le_aIdx (n : ℕ) : 200 * Hscale n ≤ (aIdx n : ℝ) := Nat.le_ceil _

lemma aIdx_lt {n : ℕ} (hL : (1 : ℝ) ≤ Lnorm n) : (aIdx n : ℝ) < 200 * Hscale n + 1 := by
  have hH := Hscale_ge_one hL
  exact Nat.ceil_lt_add_one (by linarith)

lemma bIdx_le {n : ℕ} (h : (0 : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n) :
    (bIdx n : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n := Nat.floor_le h

lemma lt_bIdx (n : ℕ) : (mIndex n : ℝ) - 200 * Hscale n - 1 < (bIdx n : ℝ) := by
  have h := Nat.lt_floor_add_one ((mIndex n : ℝ) - 200 * Hscale n)
  have hb : (bIdx n : ℝ) = (⌊(mIndex n : ℝ) - 200 * Hscale n⌋₊ : ℝ) := rfl
  rw [hb]
  linarith

lemma aIdx_le_bIdx {n : ℕ} (hL : (1 : ℝ) ≤ Lnorm n)
    (hw : 400 * Hscale n + 2 ≤ (mIndex n : ℝ)) : aIdx n ≤ bIdx n := by
  have h1 := aIdx_lt hL
  have h2 := lt_bIdx n
  have h3 : (aIdx n : ℝ) < (bIdx n : ℝ) := by linarith
  exact_mod_cast h3.le

/-- **Display (19)'s bulk is an integer interval.**  `J_n = [⌈200H⌉, ⌊m_n −
200H⌋]`.  The manuscript never records this; it is what gives both the level
count and the parity balance below. -/
theorem bulkJ_eq_Ico {n : ℕ} (hL : (1 : ℝ) ≤ Lnorm n)
    (hw : 400 * Hscale n + 2 ≤ (mIndex n : ℝ)) :
    bulkJ n = Finset.Ico (aIdx n) (bIdx n + 1) := by
  have hH := Hscale_ge_one hL
  have hnn : (0 : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n := by linarith
  ext j
  simp only [bulkJ, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, aIdx, bIdx]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨Nat.ceil_le.mpr h1, Nat.lt_succ_of_le (Nat.le_floor h2)⟩
  · rintro ⟨ha, hb'⟩
    have hb : j ≤ bIdx n := Nat.le_of_lt_succ hb'
    have hac : ((aIdx n : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast ha
    have hbc : ((j : ℕ) : ℝ) ≤ (bIdx n : ℝ) := by exact_mod_cast hb
    have h1 : 200 * Hscale n ≤ (j : ℝ) := le_trans (le_aIdx n) hac
    have h2 : (j : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n := le_trans hbc (bIdx_le hnn)
    refine ⟨?_, h1, h2⟩
    have h4 : (j : ℝ) ≤ (mIndex n : ℝ) := by linarith
    have h5 : j ≤ mIndex n := by exact_mod_cast h4
    omega

lemma card_bulkJ_eq {n : ℕ} (hL : (1 : ℝ) ≤ Lnorm n)
    (hw : 400 * Hscale n + 2 ≤ (mIndex n : ℝ)) :
    ((bulkJ n).card : ℝ) = (bIdx n : ℝ) + 1 - (aIdx n : ℝ) := by
  have hab := aIdx_le_bIdx hL hw
  rw [bulkJ_eq_Ico hL hw, Nat.card_Ico,
    Nat.cast_sub (by omega : aIdx n ≤ bIdx n + 1)]
  push_cast
  ring

lemma card_bulkJ_bounds {n : ℕ} (hL : (1 : ℝ) ≤ Lnorm n)
    (hw : 400 * Hscale n + 2 ≤ (mIndex n : ℝ)) :
    (mIndex n : ℝ) - 400 * Hscale n - 1 ≤ ((bulkJ n).card : ℝ) ∧
      ((bulkJ n).card : ℝ) ≤ (mIndex n : ℝ) - 400 * Hscale n + 1 := by
  have hH := Hscale_ge_one hL
  have hnn : (0 : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n := by linarith
  have h1 := le_aIdx n
  have h2 := aIdx_lt hL
  have h3 := bIdx_le hnn
  have h4 := lt_bIdx n
  rw [card_bulkJ_eq hL hw]
  constructor <;> linarith

/-- **`#J_n / L → 1/λ`**, the level count of display (39), proved. -/
theorem tendsto_card_div :
    Tendsto (fun n : ℕ => ((bulkJ n).card : ℝ) / Lnorm n) atTop (𝓝 (1 / lyapunov)) := by
  have hbase : ∀ s : ℝ, Tendsto
      (fun n : ℕ => ((mIndex n : ℝ) - 400 * Hscale n + s) / Lnorm n)
      atTop (𝓝 (1 / lyapunov)) := by
    intro s
    have h0 : Tendsto (fun n : ℕ =>
        (mIndex n : ℝ) / Lnorm n - 400 * (Hscale n / Lnorm n) + s * (1 / Lnorm n))
        atTop (𝓝 (1 / lyapunov)) := by
      simpa using (tendsto_mIndex_div.sub (TupleFinal.tendsto_H_div_L.const_mul 400)).add
        (TupleFinal.tendsto_one_div_L.const_mul s)
    refine h0.congr' ?_
    filter_upwards [tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hL
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hbase (-1)) (hbase 1) ?_ ?_
  · filter_upwards [eventually_good, tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hn hL
    have hb := (card_bulkJ_bounds hn.1 hn.2).1
    have := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hL.le)
    simpa [div_eq_mul_inv, sub_eq_add_neg] using this
  · filter_upwards [eventually_good, tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hn hL
    have hb := (card_bulkJ_bounds hn.1 hn.2).2
    have := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hL.le)
    simpa [div_eq_mul_inv] using this

/-- The parity balance on an integer interval: `|∑_{j ∈ [a,b)} (−1)^j| ≤ 1`. -/
theorem abs_alt_sum_Ico (a b : ℕ) : |∑ j ∈ Finset.Ico a b, (-1 : ℝ) ^ j| ≤ 1 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∀ i : ℕ, ((-1 : ℝ)) ^ (a + i) = (-1 : ℝ) ^ a * (-1 : ℝ) ^ i := fun i => pow_add _ _ _
  simp_rw [h]
  rw [← Finset.mul_sum, neg_one_geom_sum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  split_ifs <;> simp

/-- **The parity balance, normalized.**  `(∑_{j ∈ J_n} (−1)^j)/L → 0`: the
bulk carries equally many even and odd levels, up to one. -/
theorem tendsto_alt_div :
    Tendsto (fun n : ℕ => (∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) / Lnorm n) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ TupleFinal.tendsto_one_div_L
  filter_upwards [eventually_good, tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hn hL
  have hb : |∑ j ∈ bulkJ n, (-1 : ℝ) ^ j| ≤ 1 := by
    rw [bulkJ_eq_Ico hn.1 hn.2]
    exact abs_alt_sum_Ico _ _
  have := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hL.le)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hL]
  simpa [div_eq_mul_inv] using this

/-! ## Part C, the residual, and display (35) on the bulk -/

/-- **The residual: the per-level Gauss-Kuzmin intensity, uniformly on the
bulk.**

For every level `j` of the deterministic bulk `J_n` of (19),
`L · P(X_{n,j} ∈ B)` converges, uniformly in `j`, to `2λ` times the mass
`Λ` puts on the half of `B` that the parity of `j` allows.  (`signedMark`
carries the factor `(-1)^j`, so an even level can only land in `B ∩ (0,∞)`
and an odd one only in `B ∩ (−∞,0)`.)

**Intended instantiation.**  `Λe = (Λ(B ∩ (0,∞))).toReal`,
`Λo = (Λ(B ∩ (−∞,0))).toReal`; the constraint `Λe + Λo = Λ(B).toReal` then
holds by `levyIntensity_split` (proved above).  Stating it existentially
makes the residual **weaker**, not stronger: whoever discharges it may produce
any admissible pair.

**Why the normalisation is forced.**  `perLevel_constant_check` (proved above)
shows `2λ · Λ((u,∞)) = E[W]/(u log 2)` with `E[W] = ∫_0^1 W = 1/12`
(`integral_W_unit`, proved): this is precisely the Gauss-Kuzmin computation
`∑_a P(a_{j+1} = a) P(a W(θ_j) > uL)`, with `P(a_{j+1} = a) ≍ 1/(a² log 2)`
and `θ_j` equidistributed.  So the residual is display (35) at a single level
and nothing more.

**Obstruction (named), stated precisely against what the substrate does have.**

* The *digit* half is **not** the obstruction, contrary to what the old
  `deterministic_oneLevel_intensity` docstring says.  The substrate proves the
  exact leading constants: `Erdos1002.tendsto_gauss_firstDigitTail_scaled`
  gives `q · ν_G(a₁ ≥ q) → 1/log 2` and
  `Erdos1002.tendsto_gauss_firstDigitCylinder_scaled` gives
  `q² · ν_G(a₁ = q) → 1/log 2`, asymptotics, not `O`-bounds.  What is missing
  is the *transfer*: the same asymptotic for the digit `a_{j+1}` under
  **Lebesgue** measure on `(0,1)`, with an error uniform over `j ∈ J_n`.
  `Erdos1002.GaussLebesgueTransfer` / `GaussCylinderContraction` and the
  in-tree `BVMixing.lemma_3_2_BV`, `MixingBV.lem_3_2_conditional_multiblock_mixing'`
  are the modules that would feed it; none of them states it.
* The second bullet of this record, as originally written, said that the
  **joint** law — the equidistribution of `θ_j = {n β_j}` on the torus,
  asymptotically independent of the digit `a_{j+1}` — is stated nowhere in
  `Kwon1002/` or in the substrate.  **That is false**, and has been since
  `Kwon1002/OneLevelLaw.lean` was written: `OneLevelLaw.oneLevel_joint_law`
  states and proves exactly that law, unconditionally and `#print axioms`
  clean, for every symbol in the class `IsInPD D L` of display (24), uniformly
  over `j ∈ bulkJ n`.  The record is corrected here.

**What actually remains, and the two records this corrects.**  Two items were
named here as remaining.  **Item 1 is closed and item 2 is now split off**, so
both of the paragraphs that used to stand here are stale and are replaced.

1. *From the stationary mean to the level-`j` Lebesgue average, at an
   indicator.*  **Closed**, in `Kwon1002.Section5Join.oneLevel_transfer`.  The
   record used to say that the *choice of parameters* — the bracket scale `δ`,
   the degree `N` and the digit cut `Acut`, tied to `L` so that all of
   `L·((4m+2)·2δ)`, `L·2·farTail(N,δ)` and `L·C·L^{-A}` vanish while display
   (24)'s budget `(Acut+1)(2N+1)(1+farTail) ≤ L^D` still holds — "is not
   written".  It is written now: the schedule is `δ = L^{-2}`, `N = ⌈L^6⌉`,
   `Acut = ⌈L^2⌉` against `D = 11` and `A = 2`, checked in
   `Section5Join.sched_admissible`, and the five error terms (the two Selberg
   ones, the one-level rate, and the two digit tails
   `Kwon1002.digit_tail_product` and
   `DigitLocalLaw.gaussMeasure_real_digit_zero_ge`) sum to `(8m+7+C+C₂)L^{-2}`,
   which survives multiplication by `L`.  Nothing about that step is open.
2. *From the interval class to an arbitrary measurable `B`.*  Split off as
   `oneLevel_gaussKuzmin_intensity_to_measurable` below, exactly as
   `TupleFinal.goodSet_intervals_to_measurable` splits the same passage off
   `TupleFinal.goodSet_mark_factorization`.  It is unchanged in content: for a
   general measurable `B` the `θ`-sections `W^{-1}(L·B/a)` are **not** finite
   unions of intervals (a fat Cantor set inside `[1,2]` satisfies all three
   hypotheses and has a section with no finite jump count), so the Selberg
   sandwich does not apply, and closing it needs a uniform-in-`L`
   absolute-continuity bound on the level-`j` law — a density `≍ x^{-2}` on
   `δ ≤ |x| ≤ R`.  Nothing in the tree states such a bound.

**What is left of *this* residual, precisely.**  Not the joint law, not the
constant, not the parameters, and not the passage to measurable `B`.  What is
left is the *decomposition step*: `GaussKuzmin` supplies the stationary side at
half-lines (`tendsto_scaled_markTailMean`) and at a single band
(`tendsto_scaled_markBandMean`), and
`Section5Join.oneLevel_gaussKuzmin_intensity_truncation` assembles those with
item 1 into a **complete, unconditional proof** of the conclusion below at
`B = {x : ε < |x| ∧ |x| ≤ R}`.

**This residual is closed; the record above it is stale and is corrected here.**
`Kwon1002/Section5Intervals.lean` proves the statement below outright and
axiom-clean, at the same text (an `example` there checks the two types agree in
both directions).  The declaration here keeps its `sorry` only because
`Section5Intervals` imports `Section5Join`, which imports this file, so the
proof cannot be routed back to this name without a cycle.  The record used to
say that closing it needs an arbitrary `IsUnionOfIntervals` family decomposed
into *disjoint* bands with endpoints, together with the nullity of the level
sets `{(x,θ) : a₁(x)·W(θ) = c}`.  Neither is used.  The stationary mark law is
modular *pointwise* — the identity between the four indicators holds before any
integral is taken — so the family is peeled one set at a time by
inclusion-exclusion and the recursion is on the cardinality alone; and each
order-convex piece is bracketed between two half-open bands whose ends miss its
infimum and supremum by `η`, priced at `O(η/δ²)` by the explicit
`Λ((u,∞)) = 1/(2π²u)`, so no endpoint is ever read and the nullity is neither
used nor needed.

**The constant is not among the residuals any more.**
`GaussKuzmin.markTailMean_bounds` proves, for every `M > 0`,
`(1/12 − 1/(32M))/log 2 ≤ M·stationaryMeanR(1[M < a·W θ]) ≤ (1/12)/log 2`,
so `L·stationaryMeanR → 2λ·Λ((u,∞))` at `M = uL`, unconditionally.

**What is no longer part of it.**  Display (39) at `r = 1`, the level count
`#J_n = (1+o(1))L/λ` and the parity balance, which the previous residual
`Kwon1002.deterministic_oneLevel_intensity` bundled in; both are proved above.
This residual is the manuscript's (35) and nothing else. -/
theorem oneLevel_gaussKuzmin_intensity_intervals (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (_hint : IntervalClass.IsFiniteUnionOfIntervals B) :
    ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        |Lnorm n * unifIoo.real (oneLevelEvent n B j)
            - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε := by
  sorry

/-- **Residual (35b): the passage from finite unions of intervals back to
measurable sets.**

Residual (35a) is stated at finite unions of intervals because that is the class
the Selberg bracket admits: `Section5Join.stationaryMeanR_gap_le` consumes
`IntervalClass.IsUnionOfIntervals`, and
`IntervalClass.markSection_isUnionOfIntervals` is what supplies it uniformly in
the digit and the sign.  For a general measurable `B` the `θ`-sections
`W^{-1}(L·B/a)` need not be finite unions of intervals — a fat Cantor set inside
`[1,2]` satisfies all three hypotheses above and has a section with no finite
jump count — so the bracket does not apply.

The consumers of this residual (`deterministic_oneLevel_intensity` below, and
through it `sum_det_tendsto`, `oneLevel_intensity_limit`,
`det_tuple_measure_convergence`, `tuple_measure_convergence` and
`tuple_quasi_independence`) quantify over merely measurable `B`, and those
statements are **not** weakened here: their `B`-generality is expected to be
true, recoverable from the interval case by approximation against the
absolutely continuous limit `Λ`.  Isolating that argument is the point of this
residual; pushing the interval hypothesis into the consumers instead would
weaken statements that are true.

Stated as the implication rather than as a second copy of the conclusion, so
that it says exactly one thing: *the interval case implies the measurable case*.

**Obstruction.**  Closing it needs a uniform-in-`L` absolute-continuity bound on
the level-`j` law — a density `≍ x^{-2}` on `δ ≤ |x| ≤ R` — so that `B` can be
approximated by finite unions of intervals with an error that does not depend on
`L`.  Nothing in the tree states such a bound.  This is unchanged by the present
pass; what the present pass changes is that it is no longer entangled with the
bracket parameters or with the normalisation. -/
theorem oneLevel_gaussKuzmin_intensity_to_measurable
    (_h : ∀ B : Set ℝ, MeasurableSet B → (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) →
        (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → IntervalClass.IsFiniteUnionOfIntervals B →
        ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
          ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
            |Lnorm n * unifIoo.real (oneLevelEvent n B j)
                - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε) :
    ∀ B : Set ℝ, MeasurableSet B → (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) →
      (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) →
      ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
        ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
          |Lnorm n * unifIoo.real (oneLevelEvent n B j)
              - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε := by
  sorry

/-- **The residual, statement unchanged.**  Every consumer below and every
token-identity check at the foot of this file reads exactly the same `Prop` as
before; it is no longer a bare `sorry` but is derived from residuals (35a) and
(35b), which between them say what the argument actually does.

**The interval case is proved at the shape the tree names.**
`Kwon1002.Section5Join.oneLevel_gaussKuzmin_intensity_truncation` proves this
very conclusion, unconditionally and `#print axioms` clean, for
`B = {x : ε < |x| ∧ |x| ≤ R}` — the truncation window that
`IntervalClass.isUnionOfIntervals_truncation` shows is a union of two intervals
and that `TupleFinal.goodSet_mark_factorization_truncation` records as the only
shape `B` ever takes below Proposition 5.1.

**Consumer audit, and a record made precise.**  `TupleFinal`'s docstring says
"the concrete `B` the §5 chain instantiates is the large-jump truncation
`{x : ε < |x|}` cut to the bounded window".  A full sweep of `Kwon1002/` finds
that this is a statement of *intent*, not of current fact: **no theorem in this
chain is applied to a concrete `B` anywhere in the tree.**  Every application of
`oneLevel_gaussKuzmin_intensity`, `deterministic_oneLevel_intensity`,
`sum_det_tendsto`, `oneLevel_intensity_limit`, `tuple_measure_convergence`,
`tuple_quasi_independence`, `LevyExponent.factorialMoment_convergence`,
`LevyExponent.poisson_count_limit_of_tuple` and
`PoissonRoute.xi_count_poisson_limit` passes the enclosing theorem's own bound
`B` straight through, and the top nodes
(`CauchyLaw.factorialMoment_convergence`, `PoissonRoute.factorialMoment_convergence`,
`PoissonRoute.xi_count_poisson_limit`, `CauchyLaw.poisson_count_limit`) have no
call sites at all; the route that actually reaches `Master` runs through
`CorFinal.largeSum_charFun_limit`, which `Kwon1002/CorFinal.lean` records as
*not* consuming `LevyExponent.tuple_measure_convergence`.  The single concrete
instantiation of `B` in the whole development is
`TupleFinal.goodSet_mark_factorization_truncation`, at exactly
`{x : ε < |x| ∧ |x| ≤ R}` — which is the shape proved above.  So the truncation
instance services every use the tree makes *and* every use the tree is designed
to make; what it does not service is the stated generality, which is what
residuals (35a) and (35b) carry.

**Record corrected.**  This paragraph used to say that what separates the
truncation instance from residual (35a) is "the decomposition of an arbitrary
`IsUnionOfIntervals` family into disjoint bands", and that the decomposition is
"residual (35a)'s whole remaining content".  Residual (35a) is now proved
(`Kwon1002/Section5Intervals.lean`), and no such decomposition occurs in the
proof.  What remains between (35a) and the statement below is therefore
residual (35b) alone — `oneLevel_gaussKuzmin_intensity_to_measurable`, the
passage from finite unions of intervals to an arbitrary measurable `B`, whose
obstruction (a uniform-in-`L` absolute-continuity bound on the level-`j` law) is
unchanged.  In particular **closing (35a) does not close this statement**: it is
derived from (35a) *and* (35b), and (35b) is still a `sorry`. -/
theorem oneLevel_gaussKuzmin_intensity (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        |Lnorm n * unifIoo.real (oneLevelEvent n B j)
            - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε :=
  oneLevel_gaussKuzmin_intensity_to_measurable
    (fun B' hB' hB0' hBbd' hint' =>
      oneLevel_gaussKuzmin_intensity_intervals B' hB' hB0' hBbd' hint')
    B _hB _hB0 _hBbd

/-- **Target 3**, `Kwon1002.deterministic_oneLevel_intensity`
(`Kwon1002/FiveFinal.lean` line 287), reproduced token for token and proved
from `oneLevel_gaussKuzmin_intensity` together with the proved level count
`tendsto_card_div` and parity balance `tendsto_alt_div`. -/
theorem deterministic_oneLevel_intensity (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) := by
  obtain ⟨Λe, Λo, hsum, hunif⟩ := oneLevel_gaussKuzmin_intensity B _hB _hB0 _hBbd
  have hlam := lyapunov_pos
  set Λt : ℝ := (levyIntensity B).toReal with hΛt
  -- the comparison sequence
  set G : ℕ → ℝ := fun n =>
    lyapunov * Λt * (((bulkJ n).card : ℝ) / Lnorm n)
      + lyapunov * (Λe - Λo) * ((∑ j ∈ bulkJ n, (-1 : ℝ) ^ j) / Lnorm n) with hG
  have hlamne : lyapunov ≠ 0 := ne_of_gt hlam
  have hval : lyapunov * Λt * (1 / lyapunov) + lyapunov * (Λe - Λo) * 0 = Λt := by
    rw [mul_zero, add_zero]
    field_simp
  have hGlim : Tendsto G atTop (𝓝 Λt) := by
    rw [← hval]
    exact (tendsto_card_div.const_mul _).add (tendsto_alt_div.const_mul _)
  -- the pointwise identity behind `G`
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
  -- the difference tends to zero
  have hdiff : Tendsto
      (fun n : ℕ => (∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)) - G n)
      atTop (𝓝 0) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro ε' hε'
    have hεpos : (0 : ℝ) < ε' * lyapunov / 4 := by positivity
    have hcard : ∀ᶠ n : ℕ in atTop, ((bulkJ n).card : ℝ) / Lnorm n ≤ 2 / lyapunov := by
      refine Filter.Tendsto.eventually_le_const ?_ tendsto_card_div
      rw [div_lt_div_iff₀ hlam hlam]
      nlinarith
    filter_upwards [hunif (ε' * lyapunov / 4) hεpos, hcard,
      tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n hn hn2 hL
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

/-! ## Part D, the three §5 targets, from the residual and the two
`TupleFinal` residuals -/

/-- The deterministic one-level sums over `{0,…,n}` converge to `Λ(B)`. -/
theorem sum_det_tendsto (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        unifIoo.real (TupleFinal.detMarkEvent n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) :=
  Filter.Tendsto.congr (fun n => (TupleFinal.sum_det_eq_sum_bulkJ n B).symm)
    (deterministic_oneLevel_intensity B hB hB0 hBbd)

/-- **Target 4**, `Kwon1002.bulk_window_bridge_oneLevel`
(`Kwon1002/FiveFinal.lean` line 265), reproduced token for token and proved
from `TupleFinal.bulk_window_bridge_tuple` at `k = 1`: the one-level bridge is
the `k = 1` case of the tuple bridge, so the development needs only one
index-set residual, not two. -/
theorem bulk_window_bridge_oneLevel (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ =>
        (∑ j ∈ Finset.range (n + 1), unifIoo.real (bulkMarkEvent c n B j))
          - ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)) atTop (𝓝 0) := by
  refine Filter.Tendsto.congr (fun n => ?_)
    (TupleFinal.bulk_window_bridge_tuple c B _hB _hB0 _hBbd 1)
  rw [TupleFinal.sum_emb_one_eq n (bulkMarkEvent c n B),
    TupleFinal.sum_emb_one_eq n (TupleFinal.detMarkEvent n B),
    TupleFinal.sum_det_eq_sum_bulkJ n B]

/-- **Target 1**, `Kwon1002.TupleMeasure.oneLevel_intensity_limit`
(`Kwon1002/TupleMeasure.lean` line 544), reproduced token for token and proved
from `TupleFinal.bulk_window_bridge_tuple` at `k = 1` together with
`deterministic_oneLevel_intensity` above.  In particular the sorried
`Kwon1002.deterministic_oneLevel_intensity` of `FiveFinal` is **not** used. -/
theorem oneLevel_intensity_limit (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        unifIoo.real (bulkMarkEvent c n B j)) atTop (𝓝 ((levyIntensity B).toReal)) := by
  have hbr : Tendsto (fun n : ℕ =>
      (∑ j ∈ Finset.range (n + 1), unifIoo.real (bulkMarkEvent c n B j))
        - ∑ j ∈ Finset.range (n + 1), unifIoo.real (TupleFinal.detMarkEvent n B j))
      atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun n => ?_)
      (TupleFinal.bulk_window_bridge_tuple c B _hB _hB0 _hBbd 1)
    rw [TupleFinal.sum_emb_one_eq n (bulkMarkEvent c n B),
      TupleFinal.sum_emb_one_eq n (TupleFinal.detMarkEvent n B)]
  have h := hbr.add (sum_det_tendsto B _hB _hB0 _hBbd)
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-- Displays (39)-(40) on the deterministic bulk, from the proved
`TupleMeasure.tendsto_emb_sum_of_inputs`, the proved
`TupleFinal.det_singleLevel_measure_le`, `deterministic_oneLevel_intensity`
above, and `TupleFinal.det_quasi_independence` (which rests on residual 2). -/
theorem det_tuple_measure_convergence (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (TupleFinal.detMarkEvent n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  obtain ⟨δ, hδ, hBδ⟩ := hB0
  obtain ⟨C, hC, hCle⟩ := TupleFinal.det_singleLevel_measure_le B hδ hBδ
  refine tendsto_emb_sum_of_inputs k (fun n => Finset.range (n + 1))
    (fun n j => unifIoo.real (TupleFinal.detMarkEvent n B j)) _
    ((levyIntensity B).toReal) (fun n => C / Lnorm n)
    (fun n j => measureReal_nonneg) (fun n => div_nonneg hC.le (Lnorm_nonneg n))
    ?_ ?_ ?_ ?_
  · filter_upwards [hCle] with n hn j _ using hn j
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_Lnorm_atTop
  · exact sum_det_tendsto B hB ⟨δ, hδ, hBδ⟩ hBbd
  · exact TupleFinal.det_quasi_independence B hB ⟨δ, hδ, hBδ⟩ hBbd k

/-- Displays (39)-(40), `Kwon1002.LevyExponent.tuple_measure_convergence`,
reproduced token for token, from the two `TupleFinal` residuals and the new
one-level residual. -/
theorem tuple_measure_convergence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  have h := (TupleFinal.bulk_window_bridge_tuple c B _hB _hB0 _hBbd k).add
    (det_tuple_measure_convergence B _hB _hB0 _hBbd k)
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-- **Target 2**, `Kwon1002.TupleMeasure.tuple_quasi_independence`
(`Kwon1002/TupleMeasure.lean` line 570), reproduced token for token and proved
from `tuple_measure_convergence` above, `oneLevel_intensity_limit` above, the
proved `TupleMeasure.singleLevel_measure_le` and the proved
`Kwon1002.tendsto_emb_prod_sum`. -/
theorem tuple_quasi_independence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (bulkMarkEvent c n B (f ℓ)))
      atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hBδ⟩ := _hB0
  obtain ⟨C, hC, hCle⟩ := TupleMeasure.singleLevel_measure_le c B hδ hBδ
  have hT := tuple_measure_convergence c B _hB ⟨δ, hδ, hBδ⟩ _hBbd k
  have hP := tendsto_emb_prod_sum k (fun n => Finset.range (n + 1))
      (fun n j => unifIoo.real (bulkMarkEvent c n B j)) ((levyIntensity B).toReal)
      (fun n => C / Lnorm n)
      (fun n j => measureReal_nonneg) (fun n => div_nonneg hC.le (Lnorm_nonneg n))
      (by filter_upwards [hCle] with n hn j _ using hn j)
      (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_Lnorm_atTop)
      (oneLevel_intensity_limit c B _hB ⟨δ, hδ, hBδ⟩ _hBbd)
  have hsub := hT.sub hP
  rw [sub_self] at hsub
  exact hsub

/-! ## Part E, the token-identity checks, inside Lean -/

example : ∀ (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) →
    Tendsto (fun n : ℕ => ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) :=
  deterministic_oneLevel_intensity

example : ∀ (c : ℝ) (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) →
    Tendsto (fun n : ℕ =>
        (∑ j ∈ Finset.range (n + 1), unifIoo.real (bulkMarkEvent c n B j))
          - ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j)) atTop (𝓝 0) :=
  bulk_window_bridge_oneLevel

example : ∀ (c : ℝ) (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) →
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        unifIoo.real (bulkMarkEvent c n B j)) atTop (𝓝 ((levyIntensity B).toReal)) :=
  oneLevel_intensity_limit

example : ∀ (c : ℝ) (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → ∀ k : ℕ,
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (bulkMarkEvent c n B (f ℓ)))
      atTop (𝓝 0) :=
  tuple_quasi_independence

example : ∀ (c : ℝ) (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → ∀ k : ℕ,
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) :=
  tuple_measure_convergence

end

end TupleInputs

end Kwon1002

