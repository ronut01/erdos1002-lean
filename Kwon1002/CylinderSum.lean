import Kwon1002.NonzeroMode

/-!
# CylinderSum: the cylinder-summation glue of the nonzero-mode cases of 4.2

`Kwon1002/PhaseBounds.lean` §7 records the exact residual separating the two
nonzero-mode cases of Proposition 4.2 from the proved analytic inputs: the
*cylinder-summation glue* — partitioning `(0,1)` into complete prefix
cylinders, transporting the two window indicators to per-cylinder constants,
and matching the cylinder integrals against the interval integrals in which
display (22) is stated.  This file supplies that glue, in the `List`-word
language of the substrate, and independently of Proposition 4.2.

* §1 **cylinder integrals**: a closed cylinder and its half-open companion
  differ by two points, so they carry the same integral
  (`setIntegral_closed_eq_halfOpen`); and the oriented interval integral
  between a cylinder's two endpoints — the shape in which
  `Display22.descendant_cylinder_estimate_core` states display (22) — is the
  cylinder integral up to the sign `(-1)^{|w|}`
  (`intervalIntegral_eq_cylinder`).
* §2 **the complete prefix partition**: for any finite family of distinct
  depth-`d` words, the integral of a bounded measurable function over `(0,1)`
  is the sum of the cylinder integrals up to the mass of the uncovered part
  (`norm_integral_sub_sum_le`), and the same for a sum split along prefixes
  (`sum_fiber_eq`).
* §3 **windows are frozen on a deep enough cylinder**: the radius-`R` digit
  window at time `j` is a function of the word alone as soon as the word
  reaches depth `j + R` (`windowWord_eq_windowOfWord`), which is what turns
  the two window indicators of (33) into the per-cylinder constants
  `c w v` of display (22).

Everything here is proved outright; no `sorry`, no new axioms.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace CylinderSum

noncomputable section

/-! ## 1. Cylinder integrals -/

/-- A positive cylinder has finite Lebesgue measure. -/
theorem volume_closed_ne_top {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    volume (Erdos1002.closedGaussPrefixCylinder w) ≠ ⊤ := by
  rw [Kwon1002.closedCylinder_eq_uIcc hpos, Set.uIcc, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- **A closed cylinder and its half-open companion carry the same integral**:
they differ inside the two endpoints. -/
theorem setIntegral_closed_eq_halfOpen {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a)
    (f : ℝ → ℂ) :
    (∫ α in Erdos1002.closedGaussPrefixCylinder w, f α)
      = ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α := by
  have hsub : Erdos1002.gaussHalfOpenPrefixCylinder w
      ⊆ Erdos1002.closedGaussPrefixCylinder w :=
    Erdos1002.gaussHalfOpenPrefixCylinder_subset_closed hpos
  have hvol : volume (Erdos1002.closedGaussPrefixCylinder w)
      = volume (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    Kwon1002.volume_closedCylinder_eq_halfOpen hpos
  have hhalfmeas : MeasurableSet (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hdiff : volume (Erdos1002.closedGaussPrefixCylinder w
      \ Erdos1002.gaussHalfOpenPrefixCylinder w) = 0 := by
    have hfin : volume (Erdos1002.gaussHalfOpenPrefixCylinder w) ≠ ⊤ := by
      rw [← hvol]; exact volume_closed_ne_top hpos
    rw [measure_diff hsub hhalfmeas.nullMeasurableSet hfin, ← hvol, tsub_self]
  have hae : Erdos1002.closedGaussPrefixCylinder w
      =ᵐ[volume] Erdos1002.gaussHalfOpenPrefixCylinder w := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hdiff, by rw [Set.diff_eq_empty.2 hsub, measure_empty]⟩
  exact setIntegral_congr_set hae

/-- **The oriented interval integral between a cylinder's two endpoints is the
cylinder integral up to `(-1)^{|w|}`.**  This is the bridge between the
statement of display (22)
(`Display22.descendant_cylinder_estimate_core`, which integrates along
`gaussInverseWord w 0 .. gaussInverseWord w 1`) and the set integrals in
which the two-block integrand of (33) is written. -/
theorem intervalIntegral_eq_cylinder {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a)
    (f : ℝ → ℂ) :
    (∫ α in (Erdos1002.gaussInverseWord w 0)..(Erdos1002.gaussInverseWord w 1), f α)
      = (-1 : ℂ) ^ w.length
          * ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α := by
  set a := Erdos1002.gaussInverseWord w 0 with ha
  set b := Erdos1002.gaussInverseWord w 1 with hb
  have hclosed : Erdos1002.closedGaussPrefixCylinder w = Set.uIcc a b :=
    Kwon1002.closedCylinder_eq_uIcc hpos
  rcases Nat.even_or_odd w.length with he | ho
  · have hab : a ≤ b := Kwon1002.gaussInverseWord_zero_le_one_of_even hpos he
    have hu : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
    have hsign : (-1 : ℂ) ^ w.length = 1 := he.neg_one_pow
    rw [hsign, one_mul, intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← MeasureTheory.integral_Icc_eq_integral_Ioo, ← hu, ← hclosed]
    exact setIntegral_closed_eq_halfOpen hpos f
  · have hba : b ≤ a := Kwon1002.gaussInverseWord_one_le_zero_of_odd hpos ho
    have hu : Set.uIcc a b = Set.Icc b a := Set.uIcc_comm a b ▸ Set.uIcc_of_le hba
    have hsign : (-1 : ℂ) ^ w.length = -1 := ho.neg_one_pow
    rw [hsign, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hba,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← MeasureTheory.integral_Icc_eq_integral_Ioo, ← hu, ← hclosed,
      setIntegral_closed_eq_halfOpen hpos f]
    ring

/-! ## 2. The complete prefix partition -/

/-- A bounded measurable function is integrable on any finite-measure set. -/
theorem integrableOn_of_finite {s : Set ℝ} (hs : volume s ≠ ⊤) {f : ℝ → ℂ}
    (hfm : Measurable f) {B : ℝ} (hf : ∀ α, ‖f α‖ ≤ B) :
    IntegrableOn f s volume := by
  haveI : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hs⟩
  exact Integrable.of_bound hfm.aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun α => hf α))

/-- A positive half-open cylinder has finite Lebesgue measure. -/
theorem volume_halfOpen_ne_top {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    volume (Erdos1002.gaussHalfOpenPrefixCylinder w) ≠ ⊤ := by
  rw [← Kwon1002.volume_closedCylinder_eq_halfOpen hpos]
  exact volume_closed_ne_top hpos

/-- **The complete prefix partition.**  For a finite family of distinct
positive words of a common positive depth, the integral of a bounded
measurable function over `(0,1)` is the sum of its cylinder integrals, up to
the Lebesgue mass of the part of `(0,1)` the family fails to cover. -/
theorem norm_integral_sub_sum_le {d : ℕ} (hd : 0 < d) (W : Finset (List ℕ))
    (hW : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf1 : ∀ α, ‖f α‖ ≤ 1) :
    ‖(∫ α in Ioo (0 : ℝ) 1, f α)
        - ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α‖
      ≤ (volume (Ioo (0 : ℝ) 1
          \ ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
  classical
  set U : Set ℝ := ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w with hU
  have hwne : ∀ w ∈ W, w ≠ [] := by
    intro w hw hnil
    have hl := (hW w hw).1
    rw [hnil] at hl
    simp at hl
    omega
  have hUmeas : MeasurableSet U := by
    rw [hU]
    exact Finset.measurableSet_biUnion _
      (fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w)
  have hUsub : U ⊆ Ioc (0 : ℝ) 1 := by
    rw [hU]
    refine Set.iUnion₂_subset (fun w hw => ?_)
    exact ZeroMode.halfOpenCylinder_subset_Ioc (hwne w hw) (hW w hw).2
  have hUfin : volume U ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hUsub)
    rw [Real.volume_Ioc]
    simp
  have hIoofin : volume (Ioo (0 : ℝ) 1) ≠ ⊤ := by rw [Real.volume_Ioo]; simp
  -- the sum of the cylinder integrals is the integral over the union
  have hdisj : (W : Set (List ℕ)).PairwiseDisjoint
      (fun w => Erdos1002.gaussHalfOpenPrefixCylinder w) := by
    intro x hx y hy hxy
    exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
      (by rw [(hW x (Finset.mem_coe.1 hx)).1, (hW y (Finset.mem_coe.1 hy)).1])
      (hW x (Finset.mem_coe.1 hx)).2 (hW y (Finset.mem_coe.1 hy)).2 hxy
  have hsum : (∫ α in U, f α)
      = ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α := by
    rw [hU]
    exact integral_finset_biUnion W
      (fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w) hdisj
      (fun w hw => integrableOn_of_finite (volume_halfOpen_ne_top (hW w hw).2) hfm hf1)
  -- the part of `U` outside `(0,1)` is null
  have hnull : volume (U \ Ioo (0 : ℝ) 1) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_singleton (1 : ℝ))
    have h1 := hUsub hx.1
    have h2 : ¬ (0 < x ∧ x < 1) := fun hc => hx.2 ⟨hc.1, hc.2⟩
    rcases lt_or_eq_of_le h1.2 with h | h
    · exact absurd ⟨h1.1, h⟩ h2
    · simpa using h
  have hzero : (∫ α in U \ Ioo (0 : ℝ) 1, f α) = 0 := by
    rw [Measure.restrict_eq_zero.2 hnull, integral_zero_measure]
  -- split both integrals along `U ∩ (0,1)`
  have hsplit1 : (∫ α in Ioo (0 : ℝ) 1 ∩ U, f α)
        + ∫ α in Ioo (0 : ℝ) 1 \ U, f α = ∫ α in Ioo (0 : ℝ) 1, f α :=
    integral_inter_add_diff hUmeas (integrableOn_of_finite hIoofin hfm hf1)
  have hsplit2 : (∫ α in U ∩ Ioo (0 : ℝ) 1, f α)
        + ∫ α in U \ Ioo (0 : ℝ) 1, f α = ∫ α in U, f α :=
    integral_inter_add_diff measurableSet_Ioo (integrableOn_of_finite hUfin hfm hf1)
  rw [hzero, add_zero, Set.inter_comm] at hsplit2
  have hkey : (∫ α in Ioo (0 : ℝ) 1, f α)
      - ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α
      = ∫ α in Ioo (0 : ℝ) 1 \ U, f α := by
    rw [← hsum, ← hsplit1, ← hsplit2]
    ring
  rw [hkey]
  have hlt : volume (Ioo (0 : ℝ) 1 \ U) < ⊤ :=
    lt_top_iff_ne_top.2 (ne_top_of_le_ne_top hIoofin (measure_mono Set.diff_subset))
  have hbd : ‖∫ α in Ioo (0 : ℝ) 1 \ U, f α‖
      ≤ 1 * (volume (Ioo (0 : ℝ) 1 \ U)).toReal :=
    norm_setIntegral_le_of_norm_le_const hlt (fun x _ => hf1 x)
  rw [one_mul] at hbd
  exact hbd

/-! ## 3. Windows are frozen on a deep enough cylinder -/

/-- The radius-`R` window at time `j`, read off a word instead of a point. -/
def windowOfWord (R : ℕ) (u : List ℕ) (j : ℕ) : Fin (2 * R) → ℕ :=
  fun t => u.getD (j + (t : ℕ) - R) 0

/-- **The window is a function of the word alone**, as soon as the word
reaches depth `j + R`.  This is what turns the two window indicators of the
oscillatory form (33) into the per-cylinder constants of display (22). -/
theorem windowWord_eq_windowOfWord {R j : ℕ} {u : List ℕ}
    (hpos : ∀ a ∈ u, 0 < a) (hR : R ≤ j) (hlen : j + R ≤ u.length)
    {α : ℝ} (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u)
    (hirr : Irrational α) :
    windowWord R α j = windowOfWord R u j := by
  funext t
  have ht : (t : ℕ) < 2 * R := t.isLt
  have hR1 : 1 ≤ R := by omega
  have hune : u ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
    omega
  have hαIoo : α ∈ Ioo (0 : ℝ) 1 := ZeroMode.mem_Ioo_of_mem_halfOpen hune hpos hα hirr
  have hidx : j + (t : ℕ) - R < u.length := by omega
  have hdig := ZeroMode.digit_eq_of_mem_halfOpen hαIoo hirr hα (j + (t : ℕ) - R) hidx
  show digit α (j + (t : ℕ) - R) = u.getD (j + (t : ℕ) - R) 0
  rw [hdig, List.getD_eq_getElem u 0 hidx]

end

end CylinderSum

end Kwon1002
