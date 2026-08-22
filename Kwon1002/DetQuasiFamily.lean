import Kwon1002.TupleTransfer
import Kwon1002.WindowBridgeFamily

/-!
# Deterministic quasi-independence at a **per-level** family of targets

`Kwon1002.TupleFinal.det_quasi_independence_of_residual` proves displays
(39)-(40) on the deterministic bulk for one target `B` used at every level, and
in the form `|∑_f (…) − ∑_f (…)| → 0`.  A multilinear expansion of a step symbol
needs two changes, both of which the existing proof already supports:

* a **per-level** family `E : ℕ → Set ℝ`, because the expansion assigns a
  different cell to each level.  The residual it spends is
  `TupleTransfer.multiSet_mark_factorization`, which is *already* stated
  uniformly over per-level families with one constant, so nothing has to be
  re-proved on that side;
* the **sum of absolute values**, because the expansion's coefficients carry
  signs and a cancellation across `f` cannot be assumed.  The existing proof
  bounds `∑_f |D f|` and only afterwards collapses it, so this is the estimate it
  actually produces.

The majorant is uniform over the family: it is built from `badIn_emb_count`
(target-free), the multi-set residual's constant (one for all families of a
given interval count), and the two per-level measure bounds, whose constants
depend only on the common inner radius.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace DetQuasiFamily

noncomputable section

open LevyExponent TupleMeasure TupleFinal WindowBridgeFamily

/-- Display (15) at one deterministic level, uniformly over per-level families
with a common inner radius. -/
theorem det_singleLevel_measure_le_family {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ E : ℕ → Set ℝ,
      (∀ x : ℕ, ∀ y ∈ E x, δ ≤ |y|) →
      ∀ j : ℕ, unifIoo.real (detMarkEvent n (E j) j) ≤ C / Lnorm n := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have h : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_Lnorm_atTop
    exact h.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 E hE j
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin 1, (fun _ : Fin 1 => 8 * δ * Lnorm n) i ≤ (digit α ((fun _ : Fin 1 => j) i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ 1 * ∏ _i : Fin 1, (8 * δ * Lnorm n)⁻¹ :=
    hC 1 (fun _ => j) (fun _ => 8 * δ * Lnorm n)
      (fun a b _ => Subsingleton.elim a b) (fun _ => hn1)
  have hsub : detMarkEvent n (E j) j ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    exact ⟨hαI, fun _ => digit_ge_of_signedMark_mem (E j) (hE j) hn2 hα.2⟩
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (detMarkEvent n (E j) j) ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound ?_)
  rw [pow_one, Fin.prod_univ_one, div_div, ← div_eq_mul_inv]

/-- `TupleFinal.tupleEvent_eq_biInter` at a per-level family. -/
lemma tupleEvent_eq_biInter_family {k n : ℕ} (E : ℕ → Set ℝ)
    (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :
    Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f
      = ⋂ x ∈ ((Finset.univ.image (embTuple f) : Finset ℕ) : Set ℕ),
          detMarkEvent n (E x) x := by
  ext α
  rw [Set.mem_iInter₂]
  constructor
  · intro hα x hx
    have hα' : α ∈ ⋂ i : Fin k, detMarkEvent n (E (embTuple f i)) (embTuple f i) := hα
    have hex : ∃ i : Fin k, embTuple f i = x := by simpa using hx
    obtain ⟨i, hi⟩ := hex
    have h2 := Set.mem_iInter.mp hα' i
    rwa [hi] at h2
  · intro hα
    show α ∈ ⋂ i : Fin k, detMarkEvent n (E (embTuple f i)) (embTuple f i)
    exact Set.mem_iInter.mpr fun i => hα (embTuple f i) (by simp)

/-- `TupleFinal.prod_eq_prod_image` at a per-level family. -/
lemma prod_eq_prod_image_family {k n : ℕ} (E : ℕ → Set ℝ)
    (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :
    (∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ)))
      = ∏ x ∈ Finset.univ.image (embTuple f), unifIoo.real (detMarkEvent n (E x) x) :=
  prod_eq_prod_image (fun x => unifIoo.real (detMarkEvent n (E x) x)) f

/-- **Displays (39)-(40) on the deterministic bulk, at a per-level family.**

For every interval count `m`, tuple length `k` and common inner radius `δ` there
is one majorant tending to `0` which eventually bounds

  `∑_f |P(⋂_ℓ X_{n,f ℓ} ∈ E (f ℓ)) − ∏_ℓ P(X_{n,f ℓ} ∈ E (f ℓ))|`

for **every** per-level family `E` of targets that are unions of at most `m`
intervals and avoid `(−δ, δ)`.  The residual spent is
`TupleTransfer.multiSet_mark_factorization`, which is a theorem, so the
conclusion is unconditional. -/
theorem exists_det_quasi_independence_family (m k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ maj : ℕ → ℝ, Tendsto maj atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ E : ℕ → Set ℝ, (∀ x, MeasurableSet (E x)) →
        (∀ x, IntervalClass.IsUnionOfIntervals m (E x)) →
        (∀ x : ℕ, ∀ y ∈ E x, δ ≤ |y|) →
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            |unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)
              - ∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ))|)
          ≤ maj n := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
    filter_upwards with n E _ _ _
    have hz : ∀ f : Fin 0 ↪ (Finset.range (n + 1) : Finset ℕ),
        |unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)
          - ∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ))| = 0 := by
      intro f
      have he : Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f
          = (Set.univ : Set ℝ) := Set.iInter_of_empty _
      have hu : unifIoo.real (Set.univ : Set ℝ) = 1 := by
        rw [Measure.real, unifIoo, Measure.restrict_apply_univ, Real.volume_Ioo]
        simp
      simp [he, hu]
    exact le_of_eq (Finset.sum_eq_zero (fun f _ => hz f))
  obtain ⟨m', rfl⟩ : ∃ m', k = m' + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  obtain ⟨C₁, hC₁, hC₁le⟩ := det_singleLevel_measure_le_family hδ
  obtain ⟨C₂, hC₂, hC₂le⟩ := det_tuple_measure_le_family hδ (m' + 1)
  obtain ⟨C₃, hC₃, hC₃le⟩ := TupleTransfer.multiSet_mark_factorization m (m' + 1)
  obtain ⟨C₄, hC₄, hC₄le⟩ := badIn_emb_count (m' + 1)
  set C : ℝ := max C₁ C₂ with hCdef
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨fun n => 2 * C ^ (m' + 1) * C₄ * (Hscale n / Lnorm n)
    + 2 ^ (m' + 1) * C₃ * (1 / Lnorm n), ?_, ?_⟩
  · have hl1 : Tendsto (fun n : ℕ => 2 * C ^ (m' + 1) * C₄ * (Hscale n / Lnorm n))
        atTop (𝓝 0) := by
      simpa using tendsto_H_div_L.const_mul (2 * C ^ (m' + 1) * C₄)
    have hl2 : Tendsto (fun n : ℕ => 2 ^ (m' + 1) * C₃ * (1 / Lnorm n)) atTop (𝓝 0) := by
      simpa using tendsto_one_div_L.const_mul ((2 : ℝ) ^ (m' + 1) * C₃)
    simpa using hl1.add hl2
  filter_upwards [hC₁le, hC₂le, hC₃le, hC₄le,
    tendsto_Lnorm_atTop.eventually_ge_atTop 1] with n h1 h2 h3 h4 hL1 E hEm hEi hE0
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  simp only [Nat.add_sub_cancel] at h4
  set D : (Fin (m' + 1) ↪ (Finset.range (n + 1) : Finset ℕ)) → ℝ := fun f =>
    unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)
      - ∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ)) with hD
  have hprodle : ∀ f : Fin (m' + 1) ↪ (Finset.range (n + 1) : Finset ℕ),
      (∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ)))
        ≤ (C₁ / Lnorm n) ^ (m' + 1) := by
    intro f
    calc (∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ)))
        ≤ ∏ _ℓ : Fin (m' + 1), (C₁ / Lnorm n) :=
          Finset.prod_le_prod (fun ℓ _ => measureReal_nonneg)
            (fun ℓ _ => h1 E hE0 (embTuple f ℓ))
      _ = (C₁ / Lnorm n) ^ (m' + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprodnn : ∀ f : Fin (m' + 1) ↪ (Finset.range (n + 1) : Finset ℕ),
      (0 : ℝ) ≤ ∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ)) :=
    fun f => Finset.prod_nonneg fun ℓ _ => measureReal_nonneg
  have hdisj : Disjoint (goodEmb n (m' + 1)) (badEmb n (m' + 1)) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact ((mem_badEmb f).mp hf').2 ((mem_goodEmb f).mp hf).2
  have hzero : ∀ f ∈ (Finset.univ : Finset (Fin (m' + 1) ↪ (Finset.range (n + 1) : Finset ℕ))),
      f ∉ goodEmb n (m' + 1) ∪ badEmb n (m' + 1) → |D f| = 0 := by
    intro f _ hf
    have hnotin : ¬ (∀ i, ((f i : ℕ)) ∈ bulkJ n) := by
      intro hin
      rcases Classical.em (SepGood n (embTuple f)) with hg | hg
      · exact hf (Finset.mem_union_left _ ((mem_goodEmb f).mpr ⟨hin, hg⟩))
      · exact hf (Finset.mem_union_right _ ((mem_badEmb f).mpr ⟨hin, hg⟩))
    push_neg at hnotin
    obtain ⟨i₀, hi₀⟩ := hnotin
    have hi₀' : embTuple f i₀ ∉ bulkJ n := hi₀
    have he : Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro α hα
      have hα' : α ∈ ⋂ i : Fin (m' + 1),
          detMarkEvent n (E (embTuple f i)) (embTuple f i) := hα
      have hmem := Set.mem_iInter.mp hα' i₀
      rw [detMarkEvent_of_not_mem hi₀'] at hmem
      exact hmem
    have hp : (∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ))) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      rw [detMarkEvent_of_not_mem hi₀']
      simp
    simp [hD, he, hp]
  have hsum : (∑ f ∈ goodEmb n (m' + 1) ∪ badEmb n (m' + 1), |D f|)
      = ∑ f : Fin (m' + 1) ↪ (Finset.range (n + 1) : Finset ℕ), |D f| :=
    Finset.sum_subset (Finset.subset_univ _) hzero
  have hgoodterm : ∀ f ∈ goodEmb n (m' + 1), |D f| ≤ C₃ / (Lnorm n) ^ (m' + 1 + 1) := by
    intro f hf
    obtain ⟨hfin, hfsep⟩ := (mem_goodEmb f).mp hf
    have hres := h3 E hEm hEi (Finset.univ.image (embTuple f)) (card_image_embTuple f)
      (sepGoodSet_of_sepGood f hfin hfsep)
    rw [hD]
    simp only
    rw [tupleEvent_eq_biInter_family E f, prod_eq_prod_image_family E f]
    exact hres
  have hgoodcard : ((goodEmb n (m' + 1)).card : ℝ) ≤ (2 * Lnorm n) ^ (m' + 1) := by
    have hsub : ((goodEmb n (m' + 1)).card : ℕ) ≤ ((bulkJ n).card) ^ (m' + 1) := by
      have hh : (goodEmb n (m' + 1)).card
          ≤ (Fintype.piFinset (fun _ : Fin (m' + 1) => bulkJ n)).card := by
        refine Finset.card_le_card_of_injOn (fun f => embTuple f) ?_ ?_
        · intro f hf
          exact Fintype.mem_piFinset.2 ((mem_goodEmb f).mp hf).1
        · intro f _ g _ h
          exact embTuple_injective h
      rwa [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hh
    calc ((goodEmb n (m' + 1)).card : ℝ) ≤ (((bulkJ n).card : ℝ)) ^ (m' + 1) := by
          exact_mod_cast hsub
      _ ≤ (2 * Lnorm n) ^ (m' + 1) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (bulkJ_card_le hL1) _
  have hgood : (∑ f ∈ goodEmb n (m' + 1), |D f|)
      ≤ 2 ^ (m' + 1) * C₃ * (1 / Lnorm n) := by
    have hb := Finset.sum_le_card_nsmul (goodEmb n (m' + 1)) (fun f => |D f|)
      (C₃ / (Lnorm n) ^ (m' + 1 + 1)) hgoodterm
    rw [nsmul_eq_mul] at hb
    refine le_trans hb ?_
    have hq : (0 : ℝ) ≤ C₃ / (Lnorm n) ^ (m' + 1 + 1) := by positivity
    calc ((goodEmb n (m' + 1)).card : ℝ) * (C₃ / (Lnorm n) ^ (m' + 1 + 1))
        ≤ (2 * Lnorm n) ^ (m' + 1) * (C₃ / (Lnorm n) ^ (m' + 1 + 1)) :=
          mul_le_mul_of_nonneg_right hgoodcard hq
      _ = 2 ^ (m' + 1) * C₃ * (1 / Lnorm n) := by
          rw [mul_pow, pow_succ (Lnorm n) (m' + 1)]
          field_simp
  have hCC₂ : C₂ / Lnorm n ≤ C / Lnorm n := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (inv_nonneg.mpr hL0.le)
  have hCC₁ : C₁ / Lnorm n ≤ C / Lnorm n := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (inv_nonneg.mpr hL0.le)
  have hbadterm : ∀ f ∈ badEmb n (m' + 1), |D f| ≤ 2 * (C / Lnorm n) ^ (m' + 1) := by
    intro f _
    have hA : unifIoo.real (Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f)
        ≤ (C / Lnorm n) ^ (m' + 1) :=
      le_trans (h2 E hE0 f) (pow_le_pow_left₀ (by positivity) hCC₂ _)
    have hP : (∏ ℓ, unifIoo.real (detMarkEvent n (E (embTuple f ℓ)) (embTuple f ℓ)))
        ≤ (C / Lnorm n) ^ (m' + 1) :=
      le_trans (hprodle f) (pow_le_pow_left₀ (by positivity) hCC₁ _)
    rw [hD]
    simp only
    rw [abs_le]
    constructor <;> [linarith [measureReal_nonneg (μ := unifIoo)
      (s := Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f), hprodnn f, hP];
      linarith [measureReal_nonneg (μ := unifIoo)
      (s := Erdos1002.tupleEvent (fun j => detMarkEvent n (E j) j) f), hprodnn f, hA]]
  have hbad : (∑ f ∈ badEmb n (m' + 1), |D f|)
      ≤ 2 * C ^ (m' + 1) * C₄ * (Hscale n / Lnorm n) := by
    have hb := Finset.sum_le_card_nsmul (badEmb n (m' + 1)) (fun f => |D f|)
      (2 * (C / Lnorm n) ^ (m' + 1)) hbadterm
    rw [nsmul_eq_mul] at hb
    refine le_trans hb ?_
    have hq : (0 : ℝ) ≤ 2 * (C / Lnorm n) ^ (m' + 1) := by positivity
    calc ((badEmb n (m' + 1)).card : ℝ) * (2 * (C / Lnorm n) ^ (m' + 1))
        ≤ (C₄ * (Lnorm n) ^ m' * Hscale n) * (2 * (C / Lnorm n) ^ (m' + 1)) :=
          mul_le_mul_of_nonneg_right h4 hq
      _ = 2 * C ^ (m' + 1) * C₄ * (Hscale n / Lnorm n) := by
          rw [div_pow, pow_succ (Lnorm n) m']
          field_simp
  calc (∑ f : Fin (m' + 1) ↪ (Finset.range (n + 1) : Finset ℕ), |D f|)
      = (∑ f ∈ goodEmb n (m' + 1), |D f|) + ∑ f ∈ badEmb n (m' + 1), |D f| := by
        rw [← hsum, Finset.sum_union hdisj]
    _ ≤ 2 * C ^ (m' + 1) * C₄ * (Hscale n / Lnorm n)
          + 2 ^ (m' + 1) * C₃ * (1 / Lnorm n) := by linarith

end

end DetQuasiFamily

end Kwon1002
