import Kwon1002.AntiConcentration
import Erdos1002.ContinuedFractionCylinderCounting

/-!
# Display (22), Lemma 3.4, substantive half (descendant-cylinder estimate)

Manuscript (Kwon, §3, Lemma 3.4, p. 5):

> Let `{I_w}` be cylinders of a fixed depth `d`.  On `I_w` let `Q_w ∈ ℤ \ {0}`
> be fixed.  Let `k > d` and let `A` be constant on every depth-`k` cylinder,
> with `|A| ≤ 1`.  Suppose that, below `I_w`, the support of `A` is a union of
> depth-`k` descendants satisfying `q_k ≤ R_w`, where `R_w² ≤ ε n |Q_w|`.  Then
> `(22)  ∑_w |∫_{I_w} e^{2πi n Q_w α} A(α) dα| ≤ C ε.`

The converse half, display (23), is already in the project
(`Kwon1002.descendant_phase_small` / `CylinderPhase.lean`); display (22) was
missing entirely.  This file supplies it.

## Layout

* `quad_append`, `qC_le_qD`, `cfTerminal_eq_quad`, `tden_mul_le_tden_append`:
  the continuant algebra behind the manuscript's
  `q_k = q(w)Q + q'(w)Q' ≥ q(w)Q`.
* `card_descendant_words_le`: "the number of descendants with `q_k ≤ R_w` is
  `O(R_w²/q(w)²)`", via Wang's `ContinuedFractionCylinderCounting` (distinct
  reduced rationals with bounded denominator).
* `cylinder_length_eq`: display (14), `|I_w| = 1/(q_r(q_r + q_{r-1}))`, and
  `inv_sq_le_two_mul_cylinder_length`: `q(w)^{-2} ≤ 2|I_w|`.
* `sum_cylinder_length_le`: `∑_w |I_w| ≤ 35/8` (the manuscript's `∑|I_w| ≤ 1`,
  with a harmless constant coming from comparing closed to half-open
  cylinders).
* `cylinder_block_bound`: the per-`w` estimate `≤ 3 ε |I_w|`, combining the
  count with Wang's `OscillatoryIntervalSum` bound
  `|∫_J e^{2πinQ_wα} dα| ≤ (π n |Q_w|)^{-1}`.
* `descendant_cylinder_estimate_core`: display (22) in the form in which `A`
  has already been expanded over its (finitely many) retained depth-`k`
  descendant cylinders.
* `closedCylinder_eq_uIcc`, `volume_closedCylinder_eq_halfOpen`,
  `setIntegral_closedCylinder_eq`: cylinder geometry, a cylinder *is* the
  closed interval between its endpoints (the Möbius branch `x ↦ (Ax+B)/(Cx+D)`
  is monotone because `AD - BC = ±1`), closed and half-open cylinders have the
  same measure, and the set integral over a cylinder is the oriented interval
  integral up to the sign `(-1)^{|u|}`.
* `cylinder_integral_decomposition`: the bridge turning a genuine measurable
  amplitude `A` into that expansion.
* `descendant_cylinder_estimate`: **display (22) in manuscript form.**

Everything here is proved outright: no `sorry`, and every result has axioms
exactly `[propext, Classical.choice, Quot.sound]`.  Nothing sorried elsewhere in
the project is consumed.

Cylinders are the substrate's `Erdos1002.closedGaussPrefixCylinder w =
gaussInverseWord w '' [0,1]`; the interval `I_w` carries endpoints
`gaussInverseWord w 0` and `gaussInverseWord w 1`, and the phase is Wang's
`Erdos1002.oscillatoryPhase K x = exp(2πi K x)` at `K = n Q_w`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Kwon1002

noncomputable section

/-! ## 1. Continuant algebra for concatenated words

`quad w` is the matrix `E_{a₁} ⋯ E_{a_r}`, `E_a = !![0,1;1,a]`, so
`quad (w ++ v) = quad w * quad v`.  Its bottom row is `(q_{r-1}, q_r)`. -/

/-- `quad` is multiplicative for concatenation. -/
lemma quad_append (w v : List ℕ) :
    qA (w ++ v) = qA w * qA v + qB w * qC v ∧
      qB (w ++ v) = qA w * qB v + qB w * qD v ∧
      qC (w ++ v) = qC w * qA v + qD w * qC v ∧
      qD (w ++ v) = qC w * qB v + qD w * qD v := by
  induction w with
  | nil => simp
  | cons a u ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        · simp only [List.cons_append, qA_cons, qB_cons, qC_cons, qD_cons,
            h1, h2, h3, h4]
          try ring

private lemma quad_mono_aux {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) (hne : w ≠ []) :
    qA w ≤ qB w ∧ qC w ≤ qD w := by
  induction w with
  | nil => exact absurd rfl hne
  | cons a u ih =>
      have ha : 0 < a := hpos a (by simp)
      have ha1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
      have htail : ∀ b ∈ u, 0 < b := fun b hb => hpos b (by simp [hb])
      rcases eq_or_ne u [] with rfl | hu
      · refine ⟨by simp, ?_⟩
        simp only [qC_cons, qD_cons, qA_nil, qB_nil, qC_nil, qD_nil]
        linarith
      · obtain ⟨h1, h2⟩ := ih htail hu
        refine ⟨by simpa using h2, ?_⟩
        simp only [qC_cons, qD_cons]
        have hstep := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℤ) ≤ (a : ℤ))
        linarith

/-- `q_{r-1} ≤ q_r`: continuant denominators increase. -/
lemma qC_le_qD {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) : qC w ≤ qD w := by
  rcases eq_or_ne w [] with rfl | hne
  · simp
  · exact (quad_mono_aux hpos hne).2

/-- Wang's terminal continuant pair is our `(qB, qD)`. -/
lemma cfTerminal_eq_quad (w : List ℕ) :
    (Erdos1002.cfTerminalNumerator w : ℤ) = qB w ∧
      (Erdos1002.cfTerminalDenominator w : ℤ) = qD w := by
  induction w with
  | nil => simp
  | cons a u ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [Erdos1002.cfTerminalNumerator_cons, qB_cons, h2]
      · rw [Erdos1002.cfTerminalDenominator_cons, qD_cons]
        push_cast
        rw [h1, h2]

/-- **The manuscript's descendant-denominator bound.**  For a continuation `v`
of `w` the final denominator is `q_k = q(w)Q + q'(w)Q' ≥ q(w)Q`. -/
lemma tden_mul_le_tden_append {w v : List ℕ}
    (hw : ∀ a ∈ w, 0 < a) (hv : ∀ a ∈ v, 0 < a) :
    Erdos1002.cfTerminalDenominator w * Erdos1002.cfTerminalDenominator v
      ≤ Erdos1002.cfTerminalDenominator (w ++ v) := by
  have key : (Erdos1002.cfTerminalDenominator w : ℤ)
      * (Erdos1002.cfTerminalDenominator v : ℤ)
      ≤ (Erdos1002.cfTerminalDenominator (w ++ v) : ℤ) := by
    rw [(cfTerminal_eq_quad w).2, (cfTerminal_eq_quad v).2,
      (cfTerminal_eq_quad (w ++ v)).2, (quad_append w v).2.2.2]
    obtain ⟨-, -, hCw, -, -⟩ := quad_bounds hw
    obtain ⟨-, hBv, -, -, -⟩ := quad_bounds hv
    have := mul_nonneg hCw hBv
    linarith
  exact_mod_cast key

/-! ## 2. Counting the descendants with `q_k ≤ R_w`

"The number of descendants with `q_k ≤ R_w` is `O(R_w²/q(w)²)`."  Distinct
positive words of a *common* length with the same reduced terminal pair are
equal (Wang's `eq_of_cfTerminalPair_eq_of_length_mod_two_eq`), so the retained
continuations inject into the pairs `(p, q)` with `q ≤ R_w/q(w)`. -/

lemma card_descendant_words_le {w : List ℕ} (hw : ∀ a ∈ w, 0 < a)
    {m : ℕ} (hm : 0 < m) {Rw : ℝ} {T : Finset (List ℕ)}
    (hT : ∀ v ∈ T, v.length = m ∧ (∀ a ∈ v, 0 < a) ∧
      ((Erdos1002.cfTerminalDenominator (w ++ v) : ℝ) ≤ Rw)) :
    (T.card : ℝ) * (Erdos1002.cfTerminalDenominator w : ℝ) ^ 2 ≤ 4 * Rw ^ 2 := by
  have hDpos : 0 < Erdos1002.cfTerminalDenominator w :=
    Erdos1002.cfTerminalDenominator_pos hw
  have hDR : (0 : ℝ) < (Erdos1002.cfTerminalDenominator w : ℝ) := by
    exact_mod_cast hDpos
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
    positivity
  obtain ⟨v0, hv0⟩ := hne
  -- every retained continuation has small terminal denominator
  have hkey : ∀ v ∈ T, (Erdos1002.cfTerminalDenominator w : ℝ)
      * (Erdos1002.cfTerminalDenominator v : ℝ) ≤ Rw := by
    intro v hv
    obtain ⟨-, hvpos, hle⟩ := hT v hv
    have h1 := tden_mul_le_tden_append hw hvpos
    have h2 : ((Erdos1002.cfTerminalDenominator w
        * Erdos1002.cfTerminalDenominator v : ℕ) : ℝ)
        ≤ (Erdos1002.cfTerminalDenominator (w ++ v) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hvpos1 : ∀ v ∈ T, 1 ≤ Erdos1002.cfTerminalDenominator v := by
    intro v hv
    exact Erdos1002.cfTerminalDenominator_pos (hT v hv).2.1
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊Rw / (Erdos1002.cfTerminalDenominator w : ℝ)⌋₊ :=
    ⟨_, rfl⟩
  have hbound : ∀ v ∈ T, Erdos1002.cfTerminalDenominator v ≤ N := by
    intro v hv
    have h := hkey v hv
    have h' : (Erdos1002.cfTerminalDenominator v : ℝ)
        ≤ Rw / (Erdos1002.cfTerminalDenominator w : ℝ) := by
      rw [le_div_iff₀ hDR]; linarith
    rw [hNdef]
    exact Nat.le_floor (by exact_mod_cast h')
  have hN1 : 1 ≤ N := le_trans (hvpos1 v0 hv0) (hbound v0 hv0)
  -- the injection into reduced pairs with bounded denominator
  have hcard : T.card ≤ (N + 1) * (N + 1) := by
    have hinj := Finset.card_le_card_of_injOn
      (f := fun v => (Erdos1002.cfTerminalNumerator v,
        Erdos1002.cfTerminalDenominator v))
      (s := T) (t := (Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)))
      (by
        intro v hv
        have h1 : Erdos1002.cfTerminalNumerator v < N + 1 :=
          Nat.lt_succ_of_le
            ((Erdos1002.cfTerminalNumerator_le_denominator (hT v hv).2.1).trans
              (hbound v hv))
        have h2 : Erdos1002.cfTerminalDenominator v < N + 1 :=
          Nat.lt_succ_of_le (hbound v hv)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩)
      (by
        intro v hv v' hv' heq
        simp only [Finset.mem_coe] at hv hv'
        have e1 : (Erdos1002.cfTerminalPair v).1 = (Erdos1002.cfTerminalPair v').1 :=
          congrArg Prod.fst heq
        have e2 : (Erdos1002.cfTerminalPair v).2 = (Erdos1002.cfTerminalPair v').2 :=
          congrArg Prod.snd heq
        exact Erdos1002.eq_of_cfTerminalPair_eq_of_length_mod_two_eq
          (hT v hv).2.1 (hT v' hv').2.1 (Prod.ext e1 e2)
          (by rw [(hT v hv).1, (hT v' hv').1]))
    simpa [Finset.card_product] using hinj
  -- arithmetic
  have hRD : (1 : ℝ) ≤ Rw / (Erdos1002.cfTerminalDenominator w : ℝ) := by
    rw [hNdef] at hN1
    exact Nat.one_le_floor_iff _ |>.mp hN1
  have hNR : (N : ℝ) ≤ Rw / (Erdos1002.cfTerminalDenominator w : ℝ) := by
    rw [hNdef]
    exact Nat.floor_le (by linarith)
  have hcardR : (T.card : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
    have h : (T.card : ℝ) ≤ (((N + 1) * (N + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at h
    nlinarith [h]
  have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hstep : ((N : ℝ) + 1) ^ 2
      ≤ 4 * (Rw / (Erdos1002.cfTerminalDenominator w : ℝ)) ^ 2 := by
    have h2 : ((N : ℝ) + 1) ≤ 2 * (Rw / (Erdos1002.cfTerminalDenominator w : ℝ)) := by
      linarith
    have h3 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    nlinarith [mul_self_le_mul_self h3 h2]
  have hfin : (T.card : ℝ)
      ≤ 4 * (Rw / (Erdos1002.cfTerminalDenominator w : ℝ)) ^ 2 :=
    le_trans hcardR hstep
  have hDne : (Erdos1002.cfTerminalDenominator w : ℝ) ≠ 0 := ne_of_gt hDR
  calc (T.card : ℝ) * (Erdos1002.cfTerminalDenominator w : ℝ) ^ 2
      ≤ (4 * (Rw / (Erdos1002.cfTerminalDenominator w : ℝ)) ^ 2)
          * (Erdos1002.cfTerminalDenominator w : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hfin (by positivity)
    _ = 4 * Rw ^ 2 := by field_simp

/-! ## 3. Cylinder lengths: display (14) and `q(w)^{-2} ≤ 2|I_w|` -/

/-- **Display (14).**  `|I_w| = 1/(q_r (q_r + q_{r-1}))`. -/
lemma cylinder_length_eq {w : List ℕ} (hw : ∀ a ∈ w, 0 < a) :
    |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0|
      = 1 / (((qC w : ℝ) + (qD w : ℝ)) * (qD w : ℝ)) := by
  rw [abs_gaussInverseWord_sub_quad hw (by norm_num : (0:ℝ) ≤ 1) (le_refl (0:ℝ))]
  norm_num

/-- `q(w)^{-2} ≤ 2 |I_w|`, the manuscript's use of (14). -/
lemma inv_sq_le_two_mul_cylinder_length {w : List ℕ} (hw : ∀ a ∈ w, 0 < a) :
    1 / (qD w : ℝ) ^ 2
      ≤ 2 * |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0| := by
  obtain ⟨-, -, hC, hD, -⟩ := quad_bounds hw
  have hCR : (0 : ℝ) ≤ (qC w : ℝ) := by exact_mod_cast hC
  have hDR : (0 : ℝ) < (qD w : ℝ) := by exact_mod_cast hD
  have hCDR : (qC w : ℝ) ≤ (qD w : ℝ) := by exact_mod_cast qC_le_qD hw
  rw [cylinder_length_eq hw, mul_one_div,
    div_le_div_iff₀ (pow_pos hDR 2) (mul_pos (by linarith) hDR)]
  nlinarith

/-- `∑_w |I_w| ≤ 35/8` for a family of distinct depth-`d` cylinders.  (The
manuscript says `∑ |I_w| ≤ 1`; the constant here is the price of comparing the
closed cylinder to the half-open one on which disjointness is available.) -/
lemma sum_cylinder_length_le {d : ℕ} (W : Finset (List ℕ))
    (hW : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) :
    ∑ w ∈ W, |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0|
      ≤ 35 / 8 := by
  -- (i) each length is at most `35/8` times the `1/4`-`3/4` gap
  have hstep : ∀ w ∈ W,
      |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0|
        ≤ (35 / 8) * |Erdos1002.gaussInverseWord w (1 / 4)
            - Erdos1002.gaussInverseWord w (3 / 4)| := by
    intro w hw
    have hwpos := (hW w hw).2
    obtain ⟨-, -, hC, hD, -⟩ := quad_bounds hwpos
    have hCR : (0 : ℝ) ≤ (qC w : ℝ) := by exact_mod_cast hC
    have hDR : (0 : ℝ) < (qD w : ℝ) := by exact_mod_cast hD
    have hCDR : (qC w : ℝ) ≤ (qD w : ℝ) := by exact_mod_cast qC_le_qD hwpos
    have e2 : |Erdos1002.gaussInverseWord w (1 / 4)
        - Erdos1002.gaussInverseWord w (3 / 4)|
        = (1 / 2) / (((qC w : ℝ) * (1 / 4) + (qD w : ℝ))
            * ((qC w : ℝ) * (3 / 4) + (qD w : ℝ))) := by
      rw [abs_gaussInverseWord_sub_quad hwpos (by norm_num) (by norm_num)]
      norm_num
    rw [cylinder_length_eq hwpos, e2]
    set X : ℝ := ((qC w : ℝ) + (qD w : ℝ)) * (qD w : ℝ) with hXdef
    set Y : ℝ := ((qC w : ℝ) * (1 / 4) + (qD w : ℝ))
      * ((qC w : ℝ) * (3 / 4) + (qD w : ℝ)) with hYdef
    have hX : (0 : ℝ) < X := by rw [hXdef]; nlinarith
    have hY : (0 : ℝ) < Y := by rw [hYdef]; nlinarith
    have hnum : Y ≤ (35 / 16) * X := by rw [hXdef, hYdef]; nlinarith
    rw [div_le_iff₀ hX]
    have hrw : (35 : ℝ) / 8 * ((1 / 2) / Y) * X = (35 * X) / (16 * Y) := by
      field_simp; ring
    rw [hrw, le_div_iff₀ (by linarith)]
    linarith
  -- (ii) the gaps sum to at most 1, by disjointness of half-open cylinders
  have hdisj : (W : Set (List ℕ)).PairwiseDisjoint
      (fun w => Erdos1002.gaussHalfOpenPrefixCylinder w) := by
    intro x hx y hy hxy
    exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
      (by rw [(hW x hx).1, (hW y hy).1]) (hW x hx).2 (hW y hy).2 hxy
  have hmeas : ∀ w ∈ W, MeasurableSet (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hsub : (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    exact Erdos1002.closedGaussPrefixCylinder_subset_unit (hW w hw).2
      (Erdos1002.gaussHalfOpenPrefixCylinder_subset_closed (hW w hw).2 hxw)
  have hle1 : ∑ w ∈ W, volume (Erdos1002.gaussHalfOpenPrefixCylinder w) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hmeas]
    calc volume (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)
        ≤ volume (Icc (0 : ℝ) 1) := measure_mono hsub
      _ = 1 := by simp
  have hgapsum : ∑ w ∈ W, |Erdos1002.gaussInverseWord w (1 / 4)
      - Erdos1002.gaussInverseWord w (3 / 4)| ≤ 1 := by
    have h1 : ENNReal.ofReal (∑ w ∈ W, |Erdos1002.gaussInverseWord w (1 / 4)
        - Erdos1002.gaussInverseWord w (3 / 4)|) ≤ 1 := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => abs_nonneg _)]
      refine le_trans (Finset.sum_le_sum ?_) hle1
      intro w hw
      exact ofReal_gap_le_volume_halfOpen (hW w hw).2
    have h2 : ENNReal.ofReal (∑ w ∈ W, |Erdos1002.gaussInverseWord w (1 / 4)
        - Erdos1002.gaussInverseWord w (3 / 4)|) ≤ ENNReal.ofReal 1 := by
      simpa using h1
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h2
  calc ∑ w ∈ W, |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0|
      ≤ ∑ w ∈ W, (35 / 8) * |Erdos1002.gaussInverseWord w (1 / 4)
          - Erdos1002.gaussInverseWord w (3 / 4)| := Finset.sum_le_sum hstep
    _ = (35 / 8) * ∑ w ∈ W, |Erdos1002.gaussInverseWord w (1 / 4)
          - Erdos1002.gaussInverseWord w (3 / 4)| := by rw [Finset.mul_sum]
    _ ≤ (35 / 8) * 1 := by
        exact mul_le_mul_of_nonneg_left hgapsum (by norm_num)
    _ = 35 / 8 := by norm_num

/-! ## 4. The per-cylinder estimate -/

private lemma norm_weighted_sum_le {ι : Type*} (T : Finset ι) (c : ι → ℂ)
    (I : ι → ℂ) (B : ℝ) (hc : ∀ i, ‖c i‖ ≤ 1) (hI : ∀ i ∈ T, ‖I i‖ ≤ B) :
    ‖∑ i ∈ T, c i * I i‖ ≤ (T.card : ℝ) * B := by
  refine le_trans (norm_sum_le _ _) ?_
  have hb : ∀ i ∈ T, ‖c i * I i‖ ≤ B := by
    intro i hi
    rw [norm_mul]
    calc ‖c i‖ * ‖I i‖ ≤ 1 * B :=
          mul_le_mul (hc i) (hI i hi) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  calc ∑ i ∈ T, ‖c i * I i‖ ≤ ∑ _i ∈ T, B := Finset.sum_le_sum hb
    _ = (T.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The contribution below one depth-`d` cylinder `I_w` is at most
`C ε |I_w|`.**  This is the manuscript's "the contribution below `w` is at most
`Cε/q(w)²`" together with `q(w)^{-2} ≤ 2|I_w|`. -/
lemma cylinder_block_bound {w : List ℕ} (hw : ∀ a ∈ w, 0 < a)
    {m : ℕ} (hm : 0 < m) {ε Rw : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n)
    {Q : ℤ} (hQ : Q ≠ 0) (hR : Rw ^ 2 ≤ ε * (n : ℝ) * |(Q : ℝ)|)
    {T : Finset (List ℕ)} (c : List ℕ → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (hT : ∀ v ∈ T, v.length = m ∧ (∀ a ∈ v, 0 < a) ∧
        ((Erdos1002.cfTerminalDenominator (w ++ v) : ℝ) ≤ Rw)) :
    ‖∑ v ∈ T, c v *
        ∫ α in (Erdos1002.gaussInverseWord (w ++ v) 0)..
          (Erdos1002.gaussInverseWord (w ++ v) 1),
          Erdos1002.oscillatoryPhase ((n : ℝ) * (Q : ℝ)) α‖
      ≤ 3 * ε * |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0| := by
  have hQR : (0 : ℝ) < |(Q : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hQ)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hK : ((n : ℝ) * (Q : ℝ)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hnR) (Int.cast_ne_zero.mpr hQ)
  have hKabs : |(n : ℝ) * (Q : ℝ)| = (n : ℝ) * |(Q : ℝ)| := by
    rw [abs_mul, abs_of_pos hnR]
  have hnQ : (0 : ℝ) < (n : ℝ) * |(Q : ℝ)| := mul_pos hnR hQR
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Step 1: the oscillatory bound on each complete descendant cylinder
  have step1 := norm_weighted_sum_le T c
    (fun v => ∫ α in (Erdos1002.gaussInverseWord (w ++ v) 0)..
      (Erdos1002.gaussInverseWord (w ++ v) 1),
      Erdos1002.oscillatoryPhase ((n : ℝ) * (Q : ℝ)) α)
    (1 / (Real.pi * ((n : ℝ) * |(Q : ℝ)|))) hc
    (by
      intro v _
      rw [← hKabs]
      exact Erdos1002.norm_intervalIntegral_oscillatoryPhase_le _ _ _ hK)
  refine le_trans step1 ?_
  -- Step 2: the count
  have hDq : (Erdos1002.cfTerminalDenominator w : ℝ) = (qD w : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (cfTerminal_eq_quad w).2
  have hcount := card_descendant_words_le hw hm hT
  rw [hDq] at hcount
  obtain ⟨-, -, -, hD, -⟩ := quad_bounds hw
  have hDR : (0 : ℝ) < (qD w : ℝ) := by exact_mod_cast hD
  have hD2 : (0 : ℝ) < (qD w : ℝ) ^ 2 := pow_pos hDR 2
  have hcard' : (T.card : ℝ) ≤ 4 * (ε * (n : ℝ) * |(Q : ℝ)|) / (qD w : ℝ) ^ 2 := by
    rw [le_div_iff₀ hD2]
    nlinarith [hcount, hR]
  have hinv := inv_sq_le_two_mul_cylinder_length hw
  have hlen0 : (0 : ℝ)
      ≤ |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0| :=
    abs_nonneg _
  have hne1 : ((n : ℝ) * |(Q : ℝ)|) ≠ 0 := ne_of_gt hnQ
  have hne2 : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi0
  have hne3 : ((qD w : ℝ)) ≠ 0 := ne_of_gt hDR
  calc (T.card : ℝ) * (1 / (Real.pi * ((n : ℝ) * |(Q : ℝ)|)))
      ≤ (4 * (ε * (n : ℝ) * |(Q : ℝ)|) / (qD w : ℝ) ^ 2)
          * (1 / (Real.pi * ((n : ℝ) * |(Q : ℝ)|))) := by
        exact mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = (4 * ε / Real.pi) * (1 / (qD w : ℝ) ^ 2) := by field_simp
    _ ≤ (4 * ε / Real.pi)
          * (2 * |Erdos1002.gaussInverseWord w 1
              - Erdos1002.gaussInverseWord w 0|) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ 3 * ε * |Erdos1002.gaussInverseWord w 1
          - Erdos1002.gaussInverseWord w 0| := by
        have h8 : (8 : ℝ) ≤ 3 * Real.pi := by linarith [Real.pi_gt_three]
        have hrw : (4 * ε / Real.pi)
            * (2 * |Erdos1002.gaussInverseWord w 1
                - Erdos1002.gaussInverseWord w 0|)
            = (8 * ε * |Erdos1002.gaussInverseWord w 1
                - Erdos1002.gaussInverseWord w 0|) / Real.pi := by
          field_simp; ring
        rw [hrw, div_le_iff₀ hpi0]
        nlinarith [mul_nonneg hε.le hlen0, h8]

/-! ## 5. Cylinder geometry needed to reduce a genuine amplitude `A`

These are the facts named in the obstruction list of
`cylinder_integral_decomposition`: descendant cylinders sit inside their
ancestor, a cylinder *is* the closed interval between its endpoints (the
Möbius branch is monotone because `AD - BC = ±1`), and closed and half-open
cylinders have the same Lebesgue measure. -/

/-- Inverse branches compose along concatenation. -/
lemma gaussInverseWord_append (w v : List ℕ) (x : ℝ) :
    Erdos1002.gaussInverseWord (w ++ v) x
      = Erdos1002.gaussInverseWord w (Erdos1002.gaussInverseWord v x) := by
  induction w with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, Erdos1002.gaussInverseWord, ih]

/-- A descendant cylinder sits inside its ancestor. -/
lemma closedCylinder_append_subset {w v : List ℕ} (hv : ∀ a ∈ v, 0 < a) :
    Erdos1002.closedGaussPrefixCylinder (w ++ v)
      ⊆ Erdos1002.closedGaussPrefixCylinder w := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨Erdos1002.gaussInverseWord v x, Erdos1002.gaussInverseWord_mem_Icc hv hx,
    (gaussInverseWord_append w v x).symm⟩

/-- **Signed** Möbius difference formula (`abs_gaussInverseWord_sub_quad` keeps
only the magnitude).  The sign `(-1)^{|w|}` is the determinant. -/
lemma gaussInverseWord_sub_quad {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Erdos1002.gaussInverseWord w x - Erdos1002.gaussInverseWord w y
      = ((-1 : ℝ) ^ w.length * (x - y))
          / (((qC w : ℝ) * x + (qD w : ℝ)) * ((qC w : ℝ) * y + (qD w : ℝ))) := by
  obtain ⟨-, -, hC, hD, -⟩ := quad_bounds hpos
  have hCR : (0 : ℝ) ≤ (qC w : ℝ) := by exact_mod_cast hC
  have hDR : (0 : ℝ) < (qD w : ℝ) := by exact_mod_cast hD
  have hdx : (0 : ℝ) < (qC w : ℝ) * x + (qD w : ℝ) := by nlinarith
  have hdy : (0 : ℝ) < (qC w : ℝ) * y + (qD w : ℝ) := by nlinarith
  have hdet : ((qA w : ℝ) * (qD w : ℝ) - (qB w : ℝ) * (qC w : ℝ))
      = (-1 : ℝ) ^ w.length := by
    have h := quad_det w
    have h' : (((qA w * qD w - qB w * qC w : ℤ)) : ℝ)
        = (((-1 : ℤ) ^ w.length : ℤ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  rw [gaussInverseWord_eq_quad hpos hx, gaussInverseWord_eq_quad hpos hy, ← hdet]
  field_simp
  ring

/-- **A cylinder is the closed interval between its endpoints.** -/
lemma closedCylinder_eq_uIcc {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    Erdos1002.closedGaussPrefixCylinder w
      = Set.uIcc (Erdos1002.gaussInverseWord w 0)
          (Erdos1002.gaussInverseWord w 1) := by
  obtain ⟨-, -, hC, hD, -⟩ := quad_bounds hpos
  have hCR : (0 : ℝ) ≤ (qC w : ℝ) := by exact_mod_cast hC
  have hDR : (0 : ℝ) < (qD w : ℝ) := by exact_mod_cast hD
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨x, hx, rfl⟩
    have hdx : (0 : ℝ) < (qC w : ℝ) * x + (qD w : ℝ) := by nlinarith [hx.1]
    have hd0 : (0 : ℝ) < (qC w : ℝ) * 0 + (qD w : ℝ) := by nlinarith
    have hd1 : (0 : ℝ) < (qC w : ℝ) * 1 + (qD w : ℝ) := by nlinarith
    rcases Nat.even_or_odd w.length with he | ho
    · have hs : ((-1 : ℝ)) ^ w.length = 1 := he.neg_one_pow
      refine Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)
      · have h := gaussInverseWord_sub_quad hpos hx.1 (le_refl (0 : ℝ))
        rw [hs] at h
        have : (0 : ℝ) ≤ Erdos1002.gaussInverseWord w x
            - Erdos1002.gaussInverseWord w 0 := by
          rw [h]
          exact div_nonneg (by linarith [hx.1]) (le_of_lt (mul_pos hdx hd0))
        linarith
      · have h := gaussInverseWord_sub_quad hpos (zero_le_one) hx.1
        rw [hs] at h
        have : (0 : ℝ) ≤ Erdos1002.gaussInverseWord w 1
            - Erdos1002.gaussInverseWord w x := by
          rw [h]
          exact div_nonneg (by linarith [hx.2]) (le_of_lt (mul_pos hd1 hdx))
        linarith
    · have hs : ((-1 : ℝ)) ^ w.length = -1 := ho.neg_one_pow
      refine Set.mem_uIcc.mpr (Or.inr ⟨?_, ?_⟩)
      · have h := gaussInverseWord_sub_quad hpos hx.1 (zero_le_one)
        rw [hs] at h
        have : (0 : ℝ) ≤ Erdos1002.gaussInverseWord w x
            - Erdos1002.gaussInverseWord w 1 := by
          rw [h]
          exact div_nonneg (by linarith [hx.2]) (le_of_lt (mul_pos hdx hd1))
        linarith
      · have h := gaussInverseWord_sub_quad hpos (le_refl (0 : ℝ)) hx.1
        rw [hs] at h
        have : (0 : ℝ) ≤ Erdos1002.gaussInverseWord w 0
            - Erdos1002.gaussInverseWord w x := by
          rw [h]
          exact div_nonneg (by linarith [hx.1]) (le_of_lt (mul_pos hd0 hdx))
        linarith
  · have hconn : IsPreconnected (Erdos1002.gaussInverseWord w '' Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image _ (continuousOn_gaussInverseWord hpos)
    exact hconn.ordConnected.uIcc_subset ⟨0, by norm_num, rfl⟩ ⟨1, by norm_num, rfl⟩

/-- Closed and half-open cylinders have the same Lebesgue measure: they differ
inside the two endpoints. -/
lemma volume_closedCylinder_eq_halfOpen {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    volume (Erdos1002.closedGaussPrefixCylinder w)
      = volume (Erdos1002.gaussHalfOpenPrefixCylinder w) := by
  refine le_antisymm ?_
    (measure_mono (Erdos1002.gaussHalfOpenPrefixCylinder_subset_closed hpos))
  have hnull : volume ({Erdos1002.gaussInverseWord w 0,
      Erdos1002.gaussInverseWord w 1} : Set ℝ) = 0 :=
    (Set.toFinite _).measure_zero volume
  have hsub : Erdos1002.closedGaussPrefixCylinder w
      \ {Erdos1002.gaussInverseWord w 0, Erdos1002.gaussInverseWord w 1}
      ⊆ Erdos1002.gaussInverseWord w '' Ioo (0 : ℝ) 1 := by
    rintro z ⟨hz1, hz2⟩
    obtain ⟨x, hx, rfl⟩ := hz1
    have hx0 : x ≠ 0 := by rintro rfl; exact hz2 (by simp)
    have hx1 : x ≠ 1 := by rintro rfl; exact hz2 (by simp)
    exact ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩, rfl⟩
  calc volume (Erdos1002.closedGaussPrefixCylinder w)
      = volume (Erdos1002.closedGaussPrefixCylinder w
          \ {Erdos1002.gaussInverseWord w 0, Erdos1002.gaussInverseWord w 1}) :=
        (measure_diff_null hnull).symm
    _ ≤ volume (Erdos1002.gaussInverseWord w '' Ioo (0 : ℝ) 1) := measure_mono hsub
    _ ≤ volume (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
        measure_mono (image_Ioo_subset_halfOpen hpos)

/-! ## 6. Display (22) -/

/-- **Display (22), core form, proved.**

`{I_w}` are the (distinct) depth-`d` cylinders indexed by `W`; on `I_w` the
integer `Q w ≠ 0` is fixed and `R w` satisfies `R_w² ≤ ε n |Q_w|`.  `S w` lists
the retained depth-`k` descendants of `I_w`, i.e. the continuations `v` of
length `k - d` on which the amplitude `A` is the constant `c w v` (`‖c w v‖ ≤ 1`)
and whose terminal denominator `q_k` is at most `R w`.  Everything outside
`⋃_{v ∈ S w} I_{w·v}` contributes nothing, so the integral over `I_w` is the
displayed finite sum.  Conclusion: display (22) with `C = 14`. -/
theorem descendant_cylinder_estimate_core
    {ε : ℝ} (hε : 0 < ε) {n d k : ℕ} (hn : 0 < n) (hdk : d < k)
    (W : Finset (List ℕ)) (Q : List ℕ → ℤ) (R : List ℕ → ℝ)
    (S : List ℕ → Finset (List ℕ)) (c : List ℕ → List ℕ → ℂ)
    (hW : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a)
    (hQ : ∀ w ∈ W, Q w ≠ 0)
    (hR : ∀ w ∈ W, (R w) ^ 2 ≤ ε * (n : ℝ) * |(Q w : ℝ)|)
    (hS : ∀ w ∈ W, ∀ v ∈ S w, v.length = k - d ∧ (∀ a ∈ v, 0 < a) ∧
        ((Erdos1002.cfTerminalDenominator (w ++ v) : ℝ) ≤ R w))
    (hc : ∀ w v, ‖c w v‖ ≤ 1) :
    ∑ w ∈ W, ‖∑ v ∈ S w, c w v *
        ∫ α in (Erdos1002.gaussInverseWord (w ++ v) 0)..
          (Erdos1002.gaussInverseWord (w ++ v) 1),
          Erdos1002.oscillatoryPhase ((n : ℝ) * (Q w : ℝ)) α‖
      ≤ 14 * ε := by
  have hm : 0 < k - d := by omega
  have hsum := sum_cylinder_length_le (d := d) W hW
  calc ∑ w ∈ W, ‖∑ v ∈ S w, c w v *
          ∫ α in (Erdos1002.gaussInverseWord (w ++ v) 0)..
            (Erdos1002.gaussInverseWord (w ++ v) 1),
            Erdos1002.oscillatoryPhase ((n : ℝ) * (Q w : ℝ)) α‖
      ≤ ∑ w ∈ W, 3 * ε * |Erdos1002.gaussInverseWord w 1
          - Erdos1002.gaussInverseWord w 0| :=
        Finset.sum_le_sum (fun w hw =>
          cylinder_block_bound (hW w hw).2 hm hε hn (hQ w hw) (hR w hw)
            (c w) (hc w) (hS w hw))
    _ = 3 * ε * ∑ w ∈ W, |Erdos1002.gaussInverseWord w 1
          - Erdos1002.gaussInverseWord w 0| := by rw [Finset.mul_sum]
    _ ≤ 3 * ε * (35 / 8) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 14 * ε := by linarith

/-! ### Auxiliary facts about the phase and about cylinder integrals -/

lemma norm_oscillatoryPhase (K x : ℝ) : ‖Erdos1002.oscillatoryPhase K x‖ = 1 := by
  rw [Erdos1002.oscillatoryPhase, Complex.norm_exp]
  simp

lemma continuous_oscillatoryPhase (K : ℝ) :
    Continuous (Erdos1002.oscillatoryPhase K) := by
  unfold Erdos1002.oscillatoryPhase
  fun_prop

/-- For an even-length word the Möbius branch is increasing. -/
lemma gaussInverseWord_zero_le_one_of_even {u : List ℕ} (hu : ∀ a ∈ u, 0 < a)
    (he : Even u.length) :
    Erdos1002.gaussInverseWord u 0 ≤ Erdos1002.gaussInverseWord u 1 := by
  obtain ⟨-, -, hC, hD, -⟩ := quad_bounds hu
  have hCR : (0 : ℝ) ≤ (qC u : ℝ) := by exact_mod_cast hC
  have hDR : (0 : ℝ) < (qD u : ℝ) := by exact_mod_cast hD
  have hd1 : (0 : ℝ) < (qC u : ℝ) * 1 + (qD u : ℝ) := by nlinarith
  have hd0 : (0 : ℝ) < (qC u : ℝ) * 0 + (qD u : ℝ) := by nlinarith
  have h := gaussInverseWord_sub_quad hu (zero_le_one) (le_refl (0 : ℝ))
  rw [he.neg_one_pow] at h
  have hnn : (0 : ℝ) ≤ Erdos1002.gaussInverseWord u 1
      - Erdos1002.gaussInverseWord u 0 := by
    rw [h]
    exact div_nonneg (by norm_num) (le_of_lt (mul_pos hd1 hd0))
  linarith

/-- For an odd-length word the Möbius branch is decreasing. -/
lemma gaussInverseWord_one_le_zero_of_odd {u : List ℕ} (hu : ∀ a ∈ u, 0 < a)
    (ho : Odd u.length) :
    Erdos1002.gaussInverseWord u 1 ≤ Erdos1002.gaussInverseWord u 0 := by
  obtain ⟨-, -, hC, hD, -⟩ := quad_bounds hu
  have hCR : (0 : ℝ) ≤ (qC u : ℝ) := by exact_mod_cast hC
  have hDR : (0 : ℝ) < (qD u : ℝ) := by exact_mod_cast hD
  have hd1 : (0 : ℝ) < (qC u : ℝ) * 1 + (qD u : ℝ) := by nlinarith
  have hd0 : (0 : ℝ) < (qC u : ℝ) * 0 + (qD u : ℝ) := by nlinarith
  have h := gaussInverseWord_sub_quad hu (le_refl (0 : ℝ)) (zero_le_one)
  rw [ho.neg_one_pow] at h
  have hnn : (0 : ℝ) ≤ Erdos1002.gaussInverseWord u 0
      - Erdos1002.gaussInverseWord u 1 := by
    rw [h]
    exact div_nonneg (by norm_num) (le_of_lt (mul_pos hd0 hd1))
  linarith

/-- The set integral over a cylinder is the oriented interval integral between
its endpoints, up to the orientation sign `(-1)^{|u|}`. -/
lemma setIntegral_closedCylinder_eq {u : List ℕ} (hu : ∀ a ∈ u, 0 < a)
    (g : ℝ → ℂ) :
    (∫ x in Erdos1002.closedGaussPrefixCylinder u, g x)
      = (-1 : ℂ) ^ u.length *
        ∫ x in (Erdos1002.gaussInverseWord u 0)..(Erdos1002.gaussInverseWord u 1),
          g x := by
  rw [closedCylinder_eq_uIcc hu]
  rcases Nat.even_or_odd u.length with he | ho
  · have hle := gaussInverseWord_zero_le_one_of_even hu he
    rw [Set.uIcc_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, he.neg_one_pow, one_mul]
  · have hle := gaussInverseWord_one_le_zero_of_odd hu ho
    rw [Set.uIcc_of_ge hle, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, ho.neg_one_pow,
      intervalIntegral.integral_symm]
    ring

/-- **The bridge from a genuine amplitude `A` to its descendant expansion.**

`A` is constant on every depth-`k` cylinder, bounded, measurable, and vanishes on
`I_w` off the retained depth-`k` descendants `S`.  Then the integral of
`e^{2πiKα} A(α)` over `I_w` is the finite sum over `S` of the constant values
times the complete-descendant integrals.  The factor `(-1)^k` is the (uniform)
orientation of a depth-`k` cylinder: `gaussInverseWord u` reverses order exactly
when `|u|` is odd.  It has modulus one, so it is invisible in display (22). -/
theorem cylinder_integral_decomposition
    {d k : ℕ} (hdk : d < k) {w : List ℕ} (hwlen : w.length = d)
    (hwpos : ∀ a ∈ w, 0 < a) (S : Finset (List ℕ))
    (hS : ∀ v ∈ S, v.length = k - d ∧ (∀ a ∈ v, 0 < a))
    (A : ℝ → ℂ) (hAmeas : Measurable A) (hAbd : ∀ α, ‖A α‖ ≤ 1)
    (hAconst : ∀ u : List ℕ, u.length = k → (∀ a ∈ u, 0 < a) →
      ∀ α ∈ Erdos1002.closedGaussPrefixCylinder u,
        ∀ β ∈ Erdos1002.closedGaussPrefixCylinder u, A α = A β)
    (hAsupp : ∀ α ∈ Erdos1002.closedGaussPrefixCylinder w, A α ≠ 0 →
      ∃ v ∈ S, α ∈ Erdos1002.closedGaussPrefixCylinder (w ++ v))
    (K : ℝ) :
    (∫ α in Erdos1002.closedGaussPrefixCylinder w,
        Erdos1002.oscillatoryPhase K α * A α)
      = ∑ v ∈ S, ((-1 : ℂ) ^ k * A (Erdos1002.gaussInverseWord (w ++ v) 0)) *
          ∫ α in (Erdos1002.gaussInverseWord (w ++ v) 0)..
            (Erdos1002.gaussInverseWord (w ++ v) 1),
            Erdos1002.oscillatoryPhase K α := by
  classical
  have hupos : ∀ v ∈ S, ∀ a ∈ w ++ v, 0 < a := by
    intro v hv a ha
    rcases List.mem_append.mp ha with h | h
    · exact hwpos a h
    · exact (hS v hv).2 a h
  have hulen : ∀ v ∈ S, (w ++ v).length = k := by
    intro v hv
    rw [List.length_append, hwlen, (hS v hv).1]
    omega
  -- measurability of the sets involved
  have hmw : MeasurableSet (Erdos1002.closedGaussPrefixCylinder w) := by
    rw [closedCylinder_eq_uIcc hwpos]; exact measurableSet_uIcc
  have hmC : ∀ v ∈ S, MeasurableSet (Erdos1002.closedGaussPrefixCylinder (w ++ v)) := by
    intro v hv; rw [closedCylinder_eq_uIcc (hupos v hv)]; exact measurableSet_uIcc
  have hmH : ∀ v : List ℕ,
      MeasurableSet (Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)) :=
    fun v => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder _
  have hmU : MeasurableSet (⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v)) :=
    S.measurableSet_biUnion hmC
  have hmUH : MeasurableSet (⋃ v ∈ S, Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)) :=
    S.measurableSet_biUnion (fun v _ => hmH v)
  -- closed and half-open descendants differ by a null set
  have hHsubC : ∀ v ∈ S, Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)
      ⊆ Erdos1002.closedGaussPrefixCylinder (w ++ v) :=
    fun v hv => Erdos1002.gaussHalfOpenPrefixCylinder_subset_closed (hupos v hv)
  have hnullCH : ∀ v ∈ S, volume (Erdos1002.closedGaussPrefixCylinder (w ++ v)
      \ Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)) = 0 := by
    intro v hv
    have hfin : volume (Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (by simp : volume (Icc (0 : ℝ) 1) ≠ ⊤) ?_
      exact measure_mono ((hHsubC v hv).trans
        (Erdos1002.closedGaussPrefixCylinder_subset_unit (hupos v hv)))
    rw [measure_diff (hHsubC v hv) (hmH v).nullMeasurableSet hfin,
      volume_closedCylinder_eq_halfOpen (hupos v hv), tsub_self]
  -- integrability of bounded measurable functions on subsets of `[0,1]`
  have hintOn : ∀ (g : ℝ → ℂ), Measurable g → (∀ x, ‖g x‖ ≤ 1) →
      ∀ s : Set ℝ, s ⊆ Icc (0 : ℝ) 1 → IntegrableOn g s volume := by
    intro g hg hgb s hs
    have hfin : volume s ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp : volume (Icc (0 : ℝ) 1) ≠ ⊤) (measure_mono hs)
    haveI : IsFiniteMeasure (volume.restrict s) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact hfin.lt_top
    exact ⟨hg.aestronglyMeasurable,
      MeasureTheory.HasFiniteIntegral.of_bounded (C := 1)
        (Filter.Eventually.of_forall (fun x => hgb x))⟩
  have hfmeas : Measurable (fun α => Erdos1002.oscillatoryPhase K α * A α) :=
    ((continuous_oscillatoryPhase K).measurable).mul hAmeas
  have hfbd : ∀ x, ‖Erdos1002.oscillatoryPhase K x * A x‖ ≤ 1 := by
    intro x
    rw [norm_mul, norm_oscillatoryPhase, one_mul]
    exact hAbd x
  -- Step 1: restrict to the union of retained descendants
  have hsubU : (⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v))
      ⊆ Erdos1002.closedGaussPrefixCylinder w := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    exact closedCylinder_append_subset (hS v hv).2 hxv
  have h1 : (∫ α in Erdos1002.closedGaussPrefixCylinder w,
        Erdos1002.oscillatoryPhase K α * A α)
      = ∫ α in (⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v)),
          Erdos1002.oscillatoryPhase K α * A α := by
    rw [← MeasureTheory.integral_indicator hmw,
      ← MeasureTheory.integral_indicator hmU]
    congr 1
    funext α
    simp only [Set.indicator_apply]
    by_cases hin : α ∈ ⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v)
    · simp [hin, hsubU hin]
    · by_cases hw : α ∈ Erdos1002.closedGaussPrefixCylinder w
      · have hA0 : A α = 0 := by
          by_contra hne
          obtain ⟨v, hv, hmem⟩ := hAsupp α hw hne
          exact hin (Set.mem_biUnion hv hmem)
        simp [hin, hw, hA0]
      · simp [hin, hw]
  -- Step 2: pass to the half-open descendants, which are genuinely disjoint
  have haeU : (⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v))
      =ᵐ[volume] (⋃ v ∈ S, Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)) := by
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · have hsub : (⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v))
          \ (⋃ v ∈ S, Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v))
          ⊆ ⋃ v ∈ S, (Erdos1002.closedGaussPrefixCylinder (w ++ v)
            \ Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)) := by
        rintro x ⟨hx1, hx2⟩
        simp only [Set.mem_iUnion, exists_prop] at hx1 ⊢
        obtain ⟨v, hv, hxv⟩ := hx1
        refine ⟨v, hv, hxv, fun hxH => hx2 ?_⟩
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨v, hv, hxH⟩
      refine measure_mono_null hsub ?_
      exact (measure_biUnion_null_iff S.countable_toSet).mpr hnullCH
    · have hemp : (⋃ v ∈ S, Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v))
          \ (⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v)) = ∅ := by
        rw [Set.diff_eq_empty]
        exact Set.iUnion₂_mono hHsubC
      rw [hemp]
      simp
  have h2 : (∫ α in (⋃ v ∈ S, Erdos1002.closedGaussPrefixCylinder (w ++ v)),
        Erdos1002.oscillatoryPhase K α * A α)
      = ∫ α in (⋃ v ∈ S, Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)),
          Erdos1002.oscillatoryPhase K α * A α :=
    MeasureTheory.setIntegral_congr_set haeU
  have hdisjH : (S : Set (List ℕ)).PairwiseDisjoint
      (fun v => Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)) := by
    intro x hx y hy hxy
    exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
      (by rw [hulen x hx, hulen y hy]) (hupos x hx) (hupos y hy)
      (fun h => hxy (List.append_cancel_left h))
  have h3 : (∫ α in (⋃ v ∈ S, Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)),
        Erdos1002.oscillatoryPhase K α * A α)
      = ∑ v ∈ S, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v),
          Erdos1002.oscillatoryPhase K α * A α := by
    refine MeasureTheory.integral_biUnion_finset S (fun v _ => hmH v) hdisjH ?_
    intro v hv
    exact hintOn _ hfmeas hfbd _ ((hHsubC v hv).trans
      (Erdos1002.closedGaussPrefixCylinder_subset_unit (hupos v hv)))
  -- Step 3: back to the closed descendants, then use constancy and orientation
  have h4 : ∀ v ∈ S, (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v),
        Erdos1002.oscillatoryPhase K α * A α)
      = ((-1 : ℂ) ^ k * A (Erdos1002.gaussInverseWord (w ++ v) 0)) *
          ∫ α in (Erdos1002.gaussInverseWord (w ++ v) 0)..
            (Erdos1002.gaussInverseWord (w ++ v) 1),
            Erdos1002.oscillatoryPhase K α := by
    intro v hv
    have hae : Erdos1002.gaussHalfOpenPrefixCylinder (w ++ v)
        =ᵐ[volume] Erdos1002.closedGaussPrefixCylinder (w ++ v) := by
      refine MeasureTheory.ae_eq_set.mpr ⟨?_, hnullCH v hv⟩
      rw [Set.diff_eq_empty.mpr (hHsubC v hv)]
      simp
    rw [MeasureTheory.setIntegral_congr_set hae]
    have hconst : (∫ α in Erdos1002.closedGaussPrefixCylinder (w ++ v),
        Erdos1002.oscillatoryPhase K α * A α)
        = A (Erdos1002.gaussInverseWord (w ++ v) 0)
          * ∫ α in Erdos1002.closedGaussPrefixCylinder (w ++ v),
              Erdos1002.oscillatoryPhase K α := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun (hmC v hv) ?_
      intro α hα
      show Erdos1002.oscillatoryPhase K α * A α
          = A (Erdos1002.gaussInverseWord (w ++ v) 0)
            * Erdos1002.oscillatoryPhase K α
      rw [hAconst (w ++ v) (hulen v hv) (hupos v hv) α hα
        (Erdos1002.gaussInverseWord (w ++ v) 0) ⟨0, by norm_num, rfl⟩]
      ring
    rw [hconst,
      setIntegral_closedCylinder_eq (hupos v hv) (Erdos1002.oscillatoryPhase K),
      hulen v hv]
    ring
  rw [h1, h2, h3]
  exact Finset.sum_congr rfl h4

/-- **Display (22), Lemma 3.4, substantive half, manuscript form.**

`{I_w}` cylinders of a fixed depth `d`; on `I_w`, `Q_w ∈ ℤ \ {0}`; `k > d`; `A`
constant on every depth-`k` cylinder with `|A| ≤ 1`; below `I_w` the support of
`A` is a union of depth-`k` descendants with `q_k ≤ R_w`, where
`R_w² ≤ ε n |Q_w|`.  Then `∑_w |∫_{I_w} e^{2πi n Q_w α} A(α) dα| ≤ C ε`. -/
theorem descendant_cylinder_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n d k : ℕ), 0 < n → d < k →
      ∀ (W : Finset (List ℕ)) (Q : List ℕ → ℤ) (R : List ℕ → ℝ)
        (S : List ℕ → Finset (List ℕ)) (A : ℝ → ℂ),
        -- `{I_w}` are cylinders of a fixed depth `d`
        (∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) →
        -- on `I_w`, `Q_w ∈ ℤ \ {0}` is fixed
        (∀ w ∈ W, Q w ≠ 0) →
        -- `R_w² ≤ ε n |Q_w|`
        (∀ w ∈ W, (R w) ^ 2 ≤ ε * (n : ℝ) * |(Q w : ℝ)|) →
        -- `|A| ≤ 1`
        (∀ α, ‖A α‖ ≤ 1) →
        -- `A` is constant on every depth-`k` cylinder
        (∀ u : List ℕ, u.length = k → (∀ a ∈ u, 0 < a) →
          ∀ α ∈ Erdos1002.closedGaussPrefixCylinder u,
            ∀ β ∈ Erdos1002.closedGaussPrefixCylinder u, A α = A β) →
        -- the measurability the manuscript makes explicit
        Measurable A →
        -- below `I_w` the support of `A` is a union of depth-`k` descendants
        (∀ w ∈ W, ∀ v ∈ S w, v.length = k - d ∧ (∀ a ∈ v, 0 < a)) →
        (∀ w ∈ W, ∀ α ∈ Erdos1002.closedGaussPrefixCylinder w, A α ≠ 0 →
          ∃ v ∈ S w, α ∈ Erdos1002.closedGaussPrefixCylinder (w ++ v)) →
        -- those descendants satisfy `q_k ≤ R_w`
        (∀ w ∈ W, ∀ v ∈ S w,
          (Erdos1002.cfTerminalDenominator (w ++ v) : ℝ) ≤ R w) →
        ∑ w ∈ W, ‖∫ α in Erdos1002.closedGaussPrefixCylinder w,
            Erdos1002.oscillatoryPhase ((n : ℝ) * (Q w : ℝ)) α * A α‖ ≤ C * ε := by
  refine ⟨14, by norm_num, ?_⟩
  intro ε hε n d k hn hdk W Q R S A hW hQ hR hAbd hAconst hAmeas hSlen hAsupp hSden
  have hrw : ∀ w ∈ W,
      (∫ α in Erdos1002.closedGaussPrefixCylinder w,
          Erdos1002.oscillatoryPhase ((n : ℝ) * (Q w : ℝ)) α * A α)
        = ∑ v ∈ S w, ((-1 : ℂ) ^ k * A (Erdos1002.gaussInverseWord (w ++ v) 0)) *
            ∫ α in (Erdos1002.gaussInverseWord (w ++ v) 0)..
              (Erdos1002.gaussInverseWord (w ++ v) 1),
              Erdos1002.oscillatoryPhase ((n : ℝ) * (Q w : ℝ)) α := by
    intro w hw
    exact cylinder_integral_decomposition hdk (hW w hw).1 (hW w hw).2 (S w)
      (hSlen w hw) A hAmeas hAbd hAconst (hAsupp w hw) _
  rw [Finset.sum_congr rfl (fun w hw => by rw [hrw w hw])]
  refine descendant_cylinder_estimate_core hε hn hdk W Q R S
    (fun w v => (-1 : ℂ) ^ k * A (Erdos1002.gaussInverseWord (w ++ v) 0)) hW hQ hR
    (fun w hw v hv => ⟨(hSlen w hw v hv).1, (hSlen w hw v hv).2, hSden w hw v hv⟩)
    (fun w v => ?_)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hAbd _

end

end Kwon1002

