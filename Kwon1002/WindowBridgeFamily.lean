import Kwon1002.TupleFinal

/-!
# The §7/§4 index-set bridge at a **per-level** family of targets

`Kwon1002.TupleFinal.bulk_window_bridge_tuple` compares the ordered-tuple sums
attached to the random bulk `Marks.bulkIndices c α n` and to the deterministic
bulk `Section4.bulkJ n` for **one** target set `B` used at every level.  A
multilinear expansion of a step symbol across `k` levels does not produce that
shape: it produces a *different* target at each level.  This module proves the
per-level form.

Two things change and one does not.

* The statement carries `E : ℕ → Set ℝ`, a target per level, and the tuple
  events are `⋂_i bulkMarkEvent c n (E (f i)) (f i)`.
* The conclusion is the **sum of absolute values**, not the absolute value of
  the sum.  That is what the original proof produces (it bounds `∑_f |a f − b f|`
  and only then applies `squeeze_zero_norm'`), and it is what a multilinear
  expansion needs, because the expansion's coefficients have signs.
* The majorant does **not** change, and in particular does not depend on the
  family: the two per-tuple measure bounds (`tuple_measure_le_family`,
  `det_tuple_measure_le_family` below) have constants depending only on the
  common inner radius `δ`, and the two combinatorial counts
  (`TupleFinal.card_lowEmb_le`, `TupleFinal.card_windowEmb_le`) and the
  stopping-time estimate `StopWin.stopBad_measure_le` know nothing about the
  targets at all.  So the bound is stated uniformly over every family with a
  common `δ`, which is the form the expansion consumes.

The proof is the three-way split of the single-set case: above the Lamé cap both
tuple events are null; on the `O(H)`-sized window the two are separately bounded
by the uniform `(C/L)^k`; off the window they differ only inside
`StopWin.stopBad n`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace WindowBridgeFamily

noncomputable section

open LevyExponent TupleMeasure TupleFinal

/-! ## The two per-tuple measure bounds, uniformly over families -/

/-- Display (15) at `k` random-bulk levels, uniformly over every per-level family
of targets with a common inner radius. -/
theorem tuple_measure_le_family (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ E : ℕ → Set ℝ,
      (∀ x : ℕ, ∀ y ∈ E x, δ ≤ |y|) →
      ∀ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f)
          ≤ (C / Lnorm n) ^ k := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have h : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_Lnorm_atTop
    exact h.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 E hE f
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin k, (fun _ : Fin k => 8 * δ * Lnorm n) i ≤ (digit α (embTuple f i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ k * ∏ _i : Fin k, (8 * δ * Lnorm n)⁻¹ :=
    hC k (embTuple f) (fun _ => 8 * δ * Lnorm n)
      ((injF_iff _).mp (embTuple_injF f)) (fun _ => hn1)
  have hsub : Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f
      ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    refine ⟨hαI, fun i => ?_⟩
    exact digit_ge_of_mem_bulkMarkEvent c (E (embTuple f i)) (hE _) hn2
      (Set.mem_iInter.mp hα i)
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f)
      ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound (le_of_eq ?_))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, div_div,
    ← div_eq_mul_inv]

/-- Display (15) at `k` deterministic-bulk levels, uniformly over every per-level
family of targets with a common inner radius. -/
theorem det_tuple_measure_le_family {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ E : ℕ → Set ℝ,
      (∀ x : ℕ, ∀ y ∈ E x, δ ≤ |y|) →
      ∀ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)
          ≤ (C / Lnorm n) ^ k := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have h : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_Lnorm_atTop
    exact h.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 E hE f
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin k, (fun _ : Fin k => 8 * δ * Lnorm n) i ≤ (digit α (embTuple f i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ k * ∏ _i : Fin k, (8 * δ * Lnorm n)⁻¹ :=
    hC k (embTuple f) (fun _ => 8 * δ * Lnorm n)
      ((injF_iff _).mp (embTuple_injF f)) (fun _ => hn1)
  have hsub : Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f
      ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    refine ⟨hαI, fun i => ?_⟩
    exact digit_ge_of_signedMark_mem (E (embTuple f i)) (hE _) hn2
      (Set.mem_iInter.mp hα i).2
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)
      ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound (le_of_eq ?_))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, div_div,
    ← div_eq_mul_inv]

/-! ## The bridge, per level and uniformly over families -/

/-- **The §7/§4 index-set bridge at a per-level family.**

For every common inner radius `δ > 0` and every tuple length `k` there is one
majorant, tending to `0` and independent of the family, which eventually bounds

  `∑_f |P(⋂_i X_{n,f i} ∈ E (f i), f i ∈ J_n) − P(⋂_i X_{n,f i} ∈ E (f i), f i ∈ J_n^det)|`

for **every** per-level family `E` whose targets all avoid `(−δ, δ)`.  The
single-set case is `TupleFinal.bulk_window_bridge_tuple`; nothing in its proof
used the targets beyond the two per-tuple measure bounds, which are uniform over
families by `tuple_measure_le_family` and `det_tuple_measure_le_family`. -/
theorem exists_window_bridge_family (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∃ maj : ℕ → ℝ, Tendsto maj atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ E : ℕ → Set ℝ, (∀ x : ℕ, ∀ y ∈ E x, δ ≤ |y|) →
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            |unifIoo.real (Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f)
              - unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)|)
          ≤ maj n := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
    filter_upwards with n E _
    have heq : ∀ f : Fin 0 ↪ (Finset.range (n + 1) : Finset ℕ),
        Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f
          = Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f := by
      intro f; simp [Erdos1002.tupleEvent]
    simp [heq]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  obtain ⟨C₁, hC₁, hC₁le⟩ := tuple_measure_le_family c hδ (m + 1)
  obtain ⟨C₂, hC₂, hC₂le⟩ := det_tuple_measure_le_family hδ (m + 1)
  obtain ⟨Cs, cs, hCs, hcs, hbad⟩ := StopWin.stopBad_measure_le
  set C : ℝ := max C₁ C₂ with hCdef
  have hC0 : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  set K1 : ℝ := 2 * ((m : ℝ) + 1) * 6 ^ m * C ^ (m + 1) with hK1
  set K2 : ℝ := 6 ^ (m + 1) * Cs with hK2
  refine ⟨fun n => K1 * ((2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1)
      / Lnorm n) + K2 * ((Lnorm n) ^ (m + 1) * Real.exp (-cs * Real.sqrt (Lnorm n))), ?_, ?_⟩
  · simpa using ((StopWin.tendsto_windowCard_div_Lnorm c).const_mul K1).add
      ((tendsto_pow_Lnorm_mul_exp_neg_sqrt hcs (m + 1)).const_mul K2)
  filter_upwards [hC₁le, hC₂le, hbad, StopWin.eventually_stop_room,
    tendsto_Lnorm_atTop.eventually_ge_atTop (1 : ℝ)] with n h1n h2n hbadn hroom hL1 E hE
  obtain ⟨hn, hL0, hH0, hAm, hone, hle2m⟩ := hroom
  set Tc : ℕ := StopWin.Tcap n with hTc
  set Dw : Finset ℕ := StopWin.diffWindow c n with hDw
  set a : (Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ)) → ℝ :=
    fun f => unifIoo.real (Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f)
    with hadef
  set b : (Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ)) → ℝ :=
    fun f => unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)
    with hbdef
  set P : ℝ := unifIoo.real (StopWin.stopBad n) with hPdef
  have hPnn : 0 ≤ P := measureReal_nonneg
  have hPle : P ≤ Cs * Real.exp (-cs * Real.sqrt (Lnorm n)) := by
    refine le_trans ?_ hbadn
    have hfin : volume (StopWin.stopBad n) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    rw [hPdef, Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono Set.inter_subset_left)
  -- above the Lamé cap both tuple events are null
  have hvan : ∀ f, f ∉ lowEmb n (m + 1) Tc → a f - b f = 0 := by
    intro f hf
    rw [mem_lowEmb] at hf
    push_neg at hf
    obtain ⟨i, hi⟩ := hf
    have hja : a f = 0 := by
      have hsub : Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f
          ⊆ bulkMarkEvent c n (E (embTuple f i)) (embTuple f i) := Set.iInter_subset _ i
      have h0 := StopWin.unifIoo_bulkMarkEvent_eq_zero c (E (embTuple f i)) hn hi
      have hle : a f ≤ unifIoo.real (bulkMarkEvent c n (E (embTuple f i)) (embTuple f i)) :=
        measureReal_mono hsub
      rw [h0] at hle
      exact le_antisymm hle measureReal_nonneg
    have hjb : b f = 0 := by
      have hnb : (embTuple f i) ∉ bulkJ n := StopWin.not_mem_bulkJ_of_Tcap_le hL0 hi
      have hsub : Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f ⊆ ∅ := by
        rw [← detMarkEvent_of_not_mem hnb (E (embTuple f i))]
        exact Set.iInter_subset _ i
      rw [hbdef]
      simp only
      rw [Set.subset_empty_iff.mp hsub]
      simp
    rw [hja, hjb]; ring
  have hstep : ∀ S U : Set ℝ,
      S ⊆ U ∪ StopWin.stopBad n ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1} →
      unifIoo.real S ≤ unifIoo.real U + P := by
    intro S U hSU
    calc unifIoo.real S
        ≤ unifIoo.real (U ∪ StopWin.stopBad n ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1}) :=
          measureReal_mono hSU
      _ ≤ unifIoo.real (U ∪ StopWin.stopBad n)
            + unifIoo.real {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := measureReal_union_le _ _
      _ ≤ (unifIoo.real U + unifIoo.real (StopWin.stopBad n))
            + unifIoo.real {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := by
          gcongr; exact measureReal_union_le _ _
      _ = unifIoo.real U + P := by rw [StopWin.unifIoo_real_not_mem_Ioo, hPdef]; ring
  have hoff : ∀ f ∈ lowEmb n (m + 1) Tc \ windowEmb Dw n (m + 1) Tc, |a f - b f| ≤ P := by
    intro f hf
    rw [Finset.mem_sdiff] at hf
    have hlow := (mem_lowEmb f).mp hf.1
    have hnw : ∀ i, embTuple f i ∉ Dw := fun i hi =>
      hf.2 ((mem_windowEmb f).mpr ⟨hlow, ⟨i, hi⟩⟩)
    have hAD : Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f
        ⊆ Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f ∪ StopWin.stopBad n
          ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := by
      intro α hα
      by_cases hαI : α ∈ Ioo (0 : ℝ) 1
      · by_cases hg : α ∈ StopWin.stopBad n
        · exact Or.inl (Or.inr hg)
        · refine Or.inl (Or.inl (Set.mem_iInter.mpr (fun i => ?_)))
          have hi := Set.mem_iInter.mp hα i
          exact ⟨(StopWin.mem_bulkIndices_iff c n hH0 hg hαI (hnw i)).mp hi.1, hi.2⟩
      · exact Or.inr hαI
    have hDA : Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f
        ⊆ Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f ∪ StopWin.stopBad n
          ∪ {x : ℝ | x ∉ Ioo (0 : ℝ) 1} := by
      intro α hα
      by_cases hαI : α ∈ Ioo (0 : ℝ) 1
      · by_cases hg : α ∈ StopWin.stopBad n
        · exact Or.inl (Or.inr hg)
        · refine Or.inl (Or.inl (Set.mem_iInter.mpr (fun i => ?_)))
          have hi := Set.mem_iInter.mp hα i
          exact ⟨(StopWin.mem_bulkIndices_iff c n hH0 hg hαI (hnw i)).mpr hi.1, hi.2⟩
      · exact Or.inr hαI
    have h1 := hstep _ _ hAD
    have h2 := hstep _ _ hDA
    rw [abs_le]
    constructor <;> [linarith; linarith]
  have hwin : ∀ f ∈ windowEmb Dw n (m + 1) Tc,
      |a f - b f| ≤ 2 * (C / Lnorm n) ^ (m + 1) := by
    intro f _
    have ha := h1n E hE f
    have hb := h2n E hE f
    have hann : 0 ≤ a f := measureReal_nonneg
    have hbnn : 0 ≤ b f := measureReal_nonneg
    have hm1 : (C₁ / Lnorm n) ^ (m + 1) ≤ (C / Lnorm n) ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) (by gcongr; exact le_max_left _ _) _
    have hm2 : (C₂ / Lnorm n) ^ (m + 1) ≤ (C / Lnorm n) ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) (by gcongr; exact le_max_right _ _) _
    rw [abs_le]
    constructor <;> linarith
  -- cardinalities and summation
  have hLne : Lnorm n ≠ 0 := ne_of_gt hL0
  set Wn : ℝ := 2 * (StopWin.bdryLen c n : ℝ) + 2 * (StopWin.trimAmt n : ℝ) + 1 with hWn
  have hWn0 : 0 ≤ Wn := by rw [hWn]; positivity
  have hTle : (Tc : ℝ) ≤ 6 * Lnorm n := by
    have h := StopWin.Tcap_le n hL0.le
    rw [hTc]; linarith
  have hT0 : (0 : ℝ) ≤ (Tc : ℝ) := Nat.cast_nonneg _
  have hDwle : ((Dw.card : ℕ) : ℝ) ≤ Wn := by
    have h := StopWin.card_diffWindow_le c n
    rw [← hDw] at h
    have h2 : ((Dw.card : ℕ) : ℝ)
        ≤ ((2 * StopWin.bdryLen c n + 2 * StopWin.trimAmt n + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hWn]; push_cast at h2 ⊢; linarith
  have hwc : ((windowEmb Dw n (m + 1) Tc).card : ℝ)
      ≤ ((m : ℝ) + 1) * (Wn * (6 * Lnorm n) ^ m) := by
    have h := card_windowEmb_le Dw n (m + 1) Tc
    simp only [Nat.add_sub_cancel] at h
    have hcast : (((windowEmb Dw n (m + 1) Tc).card : ℕ) : ℝ)
        ≤ ((m : ℝ) + 1) * ((Dw.card : ℝ) * (Tc : ℝ) ^ m) := by
      have h3 := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at h3
      linarith
    refine le_trans hcast ?_
    have hTm : (Tc : ℝ) ^ m ≤ (6 * Lnorm n) ^ m := pow_le_pow_left₀ hT0 hTle m
    have hd0 : (0 : ℝ) ≤ (Dw.card : ℝ) := Nat.cast_nonneg _
    have h6 : (0 : ℝ) ≤ (6 * Lnorm n) ^ m := by positivity
    have hin : (Dw.card : ℝ) * (Tc : ℝ) ^ m ≤ Wn * (6 * Lnorm n) ^ m := by
      calc (Dw.card : ℝ) * (Tc : ℝ) ^ m ≤ (Dw.card : ℝ) * (6 * Lnorm n) ^ m := by gcongr
        _ ≤ Wn * (6 * Lnorm n) ^ m := by gcongr
    have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    exact mul_le_mul_of_nonneg_left hin hm0
  have hlc : ((lowEmb n (m + 1) Tc).card : ℝ) ≤ (6 * Lnorm n) ^ (m + 1) := by
    have h := card_lowEmb_le n (m + 1) Tc
    have h2 : (((lowEmb n (m + 1) Tc).card : ℕ) : ℝ) ≤ ((Tc : ℝ)) ^ (m + 1) := by
      have h3 := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at h3
      linarith
    exact le_trans h2 (pow_le_pow_left₀ hT0 hTle _)
  have hsplit : ∑ f : (Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ)), |a f - b f|
      = ∑ f ∈ lowEmb n (m + 1) Tc, |a f - b f| :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun f _ hf => by rw [hvan f hf, abs_zero])).symm
  have hbound : ∑ f ∈ lowEmb n (m + 1) Tc, |a f - b f|
      ≤ ((windowEmb Dw n (m + 1) Tc).card : ℝ) * (2 * (C / Lnorm n) ^ (m + 1))
        + ((lowEmb n (m + 1) Tc).card : ℝ) * P := by
    rw [← Finset.sum_sdiff (windowEmb_subset_lowEmb Dw n (m + 1) Tc)]
    have h1 : ∑ f ∈ windowEmb Dw n (m + 1) Tc, |a f - b f|
        ≤ ((windowEmb Dw n (m + 1) Tc).card : ℝ) * (2 * (C / Lnorm n) ^ (m + 1)) := by
      calc ∑ f ∈ windowEmb Dw n (m + 1) Tc, |a f - b f|
          ≤ ∑ _f ∈ windowEmb Dw n (m + 1) Tc, (2 * (C / Lnorm n) ^ (m + 1)) :=
            Finset.sum_le_sum hwin
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ f ∈ lowEmb n (m + 1) Tc \ windowEmb Dw n (m + 1) Tc, |a f - b f|
        ≤ ((lowEmb n (m + 1) Tc).card : ℝ) * P := by
      calc ∑ f ∈ lowEmb n (m + 1) Tc \ windowEmb Dw n (m + 1) Tc, |a f - b f|
          ≤ ∑ _f ∈ lowEmb n (m + 1) Tc \ windowEmb Dw n (m + 1) Tc, P :=
            Finset.sum_le_sum hoff
        _ = ((lowEmb n (m + 1) Tc \ windowEmb Dw n (m + 1) Tc).card : ℝ) * P := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((lowEmb n (m + 1) Tc).card : ℝ) * P := by
            refine mul_le_mul_of_nonneg_right ?_ hPnn
            exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
    linarith
  rw [hsplit]
  refine le_trans hbound ?_
  have hfac1 : ((windowEmb Dw n (m + 1) Tc).card : ℝ) * (2 * (C / Lnorm n) ^ (m + 1))
      ≤ K1 * (Wn / Lnorm n) := by
    have hq : (0 : ℝ) ≤ 2 * (C / Lnorm n) ^ (m + 1) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_right hwc hq) (le_of_eq ?_)
    rw [hK1, div_pow, mul_pow, pow_succ (Lnorm n) m]
    field_simp
  have hfac2 : ((lowEmb n (m + 1) Tc).card : ℝ) * P
      ≤ K2 * ((Lnorm n) ^ (m + 1) * Real.exp (-cs * Real.sqrt (Lnorm n))) := by
    calc ((lowEmb n (m + 1) Tc).card : ℝ) * P
        ≤ (6 * Lnorm n) ^ (m + 1) * P := mul_le_mul_of_nonneg_right hlc hPnn
      _ ≤ (6 * Lnorm n) ^ (m + 1) * (Cs * Real.exp (-cs * Real.sqrt (Lnorm n))) := by
          refine mul_le_mul_of_nonneg_left hPle (by positivity)
      _ = K2 * ((Lnorm n) ^ (m + 1) * Real.exp (-cs * Real.sqrt (Lnorm n))) := by
          rw [hK2, mul_pow]; ring
  linarith

/-- The bridge at a fixed per-level family, in limit form. -/
theorem window_bridge_family (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (E : ℕ → Set ℝ)
    (hE : ∀ x : ℕ, ∀ y ∈ E x, δ ≤ |y|) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
          |unifIoo.real (Erdos1002.tupleEvent (fun j => bulkMarkEvent c n (E j) j) f)
            - unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)|)
      atTop (𝓝 0) := by
  obtain ⟨maj, hmaj, hev⟩ := exists_window_bridge_family c hδ k
  refine squeeze_zero' (Filter.Eventually.of_forall
    (fun n => Finset.sum_nonneg (fun f _ => abs_nonneg _))) ?_ hmaj
  filter_upwards [hev] with n hn using hn E hE

/-- **The single-set bridge is recovered.**  Instantiating the family at the
constant family gives back `TupleFinal.bulk_window_bridge_tuple` token for token,
so the generalisation is a genuine strengthening and not a different statement. -/
theorem bulk_window_bridge_tuple_of_family (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
      atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hB0⟩ := _hB0
  have h := window_bridge_family c hδ (fun _ => B) (fun _ y hy => hB0 y hy) k
  refine squeeze_zero_norm' ?_ h
  filter_upwards with n
  rw [Real.norm_eq_abs, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Statement guard: the theorem above is the canonical
`Kwon1002.TupleFinal.bulk_window_bridge_tuple`, token for token. -/
example : ∀ (c : ℝ) (B : Set ℝ), MeasurableSet B → (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) →
    (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → ∀ k : ℕ,
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
      atTop (𝓝 0) :=
  @TupleFinal.bulk_window_bridge_tuple

example : ∀ (c : ℝ) (B : Set ℝ), MeasurableSet B → (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) →
    (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → ∀ k : ℕ,
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
      atTop (𝓝 0) :=
  bulk_window_bridge_tuple_of_family

end

end WindowBridgeFamily

end Kwon1002
