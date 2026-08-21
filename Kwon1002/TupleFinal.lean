import Kwon1002.FiveFinal
import Kwon1002.TupleCount
import Kwon1002.IntervalClass

/-!
# Scratch (agent `tuples`), the two `TupleMeasure` inputs and (39)-(40)

Targets, all three reproduced **token for token** (diffed against the sources;
each carries no prime, they live in this file's own namespace, and each is
additionally checked inside Lean by an `example … := rfl` at the very bottom,
so the elaborated `Prop`s coincide and not merely the surface syntax):

* `oneLevel_intensity_limit`   = `Kwon1002.TupleMeasure.oneLevel_intensity_limit`
  (`Kwon1002/TupleMeasure.lean` line 544);
* `tuple_quasi_independence`   = `Kwon1002.TupleMeasure.tuple_quasi_independence`
  (line 570);
* `tuple_measure_convergence`  = `Kwon1002.LevyExponent.tuple_measure_convergence`
  (`Kwon1002/LevyExponent.lean` line 263), the only gap between the substrate
  and Proposition 5.1.

None of the three closes outright: all three sit below Proposition 4.1, which
is only *stated* in this development.  What this pass delivers is a strictly
tighter reduction than the previous best (`Kwon1002/FiveFinal.lean`), with the
bad-tuple removal, the step the manuscript disposes of in one sentence -
**machine-checked** rather than bundled into the residual.

## The recorded finding, addressed head on

§5 of the manuscript writes (38)-(40) over the index set of (38), which is the
**random** bulk `J_n` produced by the §7 stopping time, while Proposition 4.1
and displays (25)-(27) quantify over the **deterministic** bulk `J_n` of
display (19).  The switch is made without remark.  This file uses the
*deterministic* set of (19) everywhere the §4 machinery is invoked, and
isolates the comparison as a single named residual,
`bulk_window_bridge_tuple`, at the level of `k`-tuples, the level at which
(38)-(40) actually need it.  `Kwon1002.bulk_window_bridge_oneLevel`
(`FiveFinal`) is the `k = 1` case; it is **derived** here from
`bulk_window_bridge_tuple` (see `oneLevel_intensity_limit`), so this file
replaces two bridges by one.

Concretely, `detMarkEvent n B j = {α | j ∈ J_n^{(19)} ∧ X_{n,j}(α) ∈ B}` is
`bulkMarkEvent` with the random index set of `Marks.bulkIndices` replaced by
the deterministic `Section4.bulkJ`, and nothing else changed.

**A second finding, recorded here.**  The mismatch is not only
random-versus-deterministic: the two index sets have *different trimming
conventions*.

* `Section4.bulkJ n` (display (19)) trims at **both** ends and with the
  explicit constant `200`:  `200H ≤ j ≤ m_n − 200H`.
* `Marks.bulkIndices c α n` (§7) trims only at the **bottom**, and with a
  *free parameter* `c`:  `c·H ≤ j < τ_n(α)`.

So the bridge has three separate jobs, none of which the manuscript states:
replace `τ_n` by `m_n` (this is Lemma 7.1, `|τ_n − m_n| = O(H)`), add the
missing top trim of `200H` levels, and reconcile `c` with `200`.  Each of the
three discrepancy regions holds `O(H)` levels, and each level carries
probability `O(1/L)` by the *proved* `det_singleLevel_measure_le`, so each
contributes `O(H/L) = O(L^{−1/4}) = o(1)`: the bridge is believable for every
`c > 0`, and is shallow, but it is genuinely absent from §5, and it is
absent from `Kwon1002/` too.  It is residual 1 below.

## The residuals

Exactly **three**, all stated in this file:

1. `bulk_window_bridge_tuple`, the index-set bridge above (the finding).
2. `deterministic_oneLevel_intensity`, display (35) on the deterministic
   bulk, read against an indicator.  This one is *not* restated here: it is
   `Kwon1002.deterministic_oneLevel_intensity` of `Kwon1002/FiveFinal.lean`,
   consumed as a sorried input and named as such.
3. `goodSet_mark_factorization`, Proposition 4.1 for the mark event, with
   error `O(L^{-(k+1)})` per good tuple.

Everything else is proved here.

## What is proved outright here (and was not before)

* `det_singleLevel_measure_le`, `det_tuple_measure_le`, the deterministic
  analogues of `TupleMeasure.singleLevel_measure_le` / `tuple_measure_le`
  (display (15) at one and at `k` levels), out of the proved
  `Kwon1002.digit_tail_product` and `Kwon1002.W_le_eighth`.
* `badIn_emb_count`, **the bad-tuple count in the currency (39) needs it**:
  the number of *embeddings* `Fin k ↪ {0,…,n}` with all values in the bulk
  that fail the symmetrized (25)/(26) separation is `O_k(L^{k-1}H)`.  Proved
  from `Kwon1002.TupleCount.card_BadF_le` (proved), note that
  `Kwon1002.nonGood_tuple_count'` itself is *not* directly usable here,
  because it counts *increasing* tuples, whereas (39) sums over embeddings;
  the exceptional finsets `TupleCount.SgapF`/`SresF` are quantified over
  ordered pairs `p ≠ q` and so cover the symmetrized condition unchanged.
* `det_quasi_independence`, the whole of the manuscript's step 2+3 on the
  deterministic side: bad tuples removed against `badIn_emb_count` and
  `det_tuple_measure_le`, good tuples handed to residual 3, and the two error
  terms shown to be `O(H/L) + O(1/L) = o(1)`.
* The diagonal bookkeeping of (39) is *not* redone: it is
  `TupleMeasure.tendsto_emb_sum_of_inputs` (proved there), used as a black box.

## Deliberate strengthening of the *hypothesis* side, i.e. weakening of the ask

`SepGood` symmetrizes display (26): the manuscript asks `|j_ℓ - (m_n+j_i)/2| ≥
200H` only for `i < ℓ`, and here it is asked for all `i ≠ ℓ`.  That makes the
*good* set smaller, hence residual 3 a **weaker** assumption, and it makes the
*bad* set larger, which is paid for in `badIn_emb_count`, since
`TupleCount.card_BadF_le` already ranges over all ordered pairs.  No target is
weakened; the residual is.

## One bookkeeping step that is *not* machine-checked, stated plainly

`goodSet_mark_factorization` is phrased on the `k`-element **subset**
`S ⊆ J_n^{(19)}` rather than on an increasing tuple `j_1 < … < j_k`, because
both sides of (27) depend only on `S` (the event is an intersection, the
comparison term a product).  Proposition 4.1 is stated on the increasing
tuple.  The identification of the two is the sorting bijection, which is not
carried out in Lean here.  It is recorded as the single gap between residual 3
and Proposition 4.1 as stated in `Kwon1002/Section4.lean`.

## Sorried results consumed

* `Kwon1002.deterministic_oneLevel_intensity` (`Kwon1002/FiveFinal.lean`) -
  once, in `sum_det_tendsto`.
* the two residuals declared in this file.
* **Nothing else.**  In particular `Kwon1002.LevyExponent.tuple_measure_convergence`,
  `Kwon1002.TupleMeasure.oneLevel_intensity_limit`,
  `Kwon1002.TupleMeasure.tuple_quasi_independence`,
  `Kwon1002.bulk_window_bridge_oneLevel`, `Kwon1002.Section4.prop_4_1_marked_factorization`
  and `Kwon1002.Section4.nonGood_tuple_count` are **not** consumed.
  `TupleMeasure.tendsto_emb_sum_of_inputs`, `TupleMeasure.singleLevel_measure_le`,
  `Kwon1002.tendsto_emb_prod_sum`, `Kwon1002.TupleCount.card_BadF_le`,
  `Kwon1002.digit_tail_product` and `Kwon1002.W_le_eighth` are all **proved**
  where they live.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal Classical

namespace Kwon1002

namespace TupleFinal

open LevyExponent TupleMeasure

noncomputable section

/-! ## Part A, the deterministic one-level event -/

/-- **The deterministic mark event.**  `bulkMarkEvent` with the *random* bulk
`Marks.bulkIndices c α n` of §7 replaced by the *deterministic* bulk
`Section4.bulkJ n` of display (19).  Nothing else is changed. -/
def detMarkEvent (n : ℕ) (B : Set ℝ) (j : ℕ) : Set ℝ :=
  {α : ℝ | j ∈ bulkJ n ∧ signedMark α n j ∈ B}

lemma detMarkEvent_of_mem {n j : ℕ} (h : j ∈ bulkJ n) (B : Set ℝ) :
    detMarkEvent n B j = oneLevelEvent n B j := by
  ext α; simp [detMarkEvent, oneLevelEvent, h]

lemma detMarkEvent_of_not_mem {n j : ℕ} (h : j ∉ bulkJ n) (B : Set ℝ) :
    detMarkEvent n B j = ∅ := by
  ext α; simp [detMarkEvent, h]

lemma measurableSet_detMarkEvent (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) (j : ℕ) :
    MeasurableSet (detMarkEvent n B j) := by
  by_cases h : j ∈ bulkJ n
  · have : detMarkEvent n B j = (fun α : ℝ => signedMark α n j) ⁻¹' B := by
      ext α; simp [detMarkEvent, h]
    rw [this]
    exact (measurable_signedMark n j) hB
  · rw [detMarkEvent_of_not_mem h]
    exact MeasurableSet.empty

/-! ## Part B, display (15) on the deterministic side

Copies of `TupleMeasure.singleLevel_measure_le` and
`TupleMeasure.tuple_measure_le` with `bulkMarkEvent` replaced by
`detMarkEvent`; the digit constraint `W ≤ 1/8` never used the index set. -/

/-- The manuscript's "if `φ_ℓ((-1)^j a W(θ)/L) ≠ 0` then `a ≥ 8cL`", with no
reference to any index set: a level whose normalized signed mark is at
distance `≥ δ` from the origin has digit `≥ 8δL`. -/
lemma digit_ge_of_signedMark_mem (B : Set ℝ) {δ : ℝ} (hB0 : ∀ x ∈ B, δ ≤ |x|)
    {n : ℕ} (hn : 0 < Lnorm n) {j : ℕ} {α : ℝ} (hα : signedMark α n j ∈ B) :
    8 * δ * Lnorm n ≤ (digit α j : ℝ) := by
  have hδle : δ ≤ |signedMark α n j| := hB0 _ hα
  have hWnn : 0 ≤ W (theta α n j) := W_nonneg _
  have hprodnn : (0 : ℝ) ≤ (digit α j : ℝ) * W (theta α n j) :=
    mul_nonneg (Nat.cast_nonneg _) hWnn
  have habs : |signedMark α n j| = (digit α j : ℝ) * W (theta α n j) / Lnorm n := by
    rw [signedMark, mark, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hn.le, abs_of_nonneg hprodnn]
  rw [habs, le_div_iff₀ hn] at hδle
  have hW8 : W (theta α n j) ≤ 1 / 8 := W_le_eighth _
  have hbnd : (digit α j : ℝ) * W (theta α n j) ≤ (digit α j : ℝ) * (1 / 8) :=
    mul_le_mul_of_nonneg_left hW8 (Nat.cast_nonneg _)
  linarith

/-- **Display (15) at one deterministic level, proved unconditionally.**
Consumes `Kwon1002.digit_tail_product` (proved) and `Kwon1002.W_le_eighth`. -/
theorem det_singleLevel_measure_le (B : Set ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hB0 : ∀ x ∈ B, δ ≤ |x|) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      unifIoo.real (detMarkEvent n B j) ≤ C / Lnorm n := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_Lnorm_atTop
    exact this.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 j
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin 1, (fun _ : Fin 1 => 8 * δ * Lnorm n) i ≤ (digit α ((fun _ : Fin 1 => j) i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ 1 * ∏ _i : Fin 1, (8 * δ * Lnorm n)⁻¹ :=
    hC 1 (fun _ => j) (fun _ => 8 * δ * Lnorm n)
      (fun a b _ => Subsingleton.elim a b) (fun _ => hn1)
  have hsub : detMarkEvent n B j ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    exact ⟨hαI, fun _ => digit_ge_of_signedMark_mem B hB0 hn2 hα.2⟩
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (detMarkEvent n B j) ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound ?_)
  rw [pow_one, Fin.prod_univ_one, div_div, ← div_eq_mul_inv]

/-- **Display (15) at `k` deterministic levels, proved unconditionally.**
Consumes `Kwon1002.digit_tail_product` (proved) and `Kwon1002.W_le_eighth`. -/
theorem det_tuple_measure_le (B : Set ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hB0 : ∀ x ∈ B, δ ≤ |x|) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f) ≤ (C / Lnorm n) ^ k := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_Lnorm_atTop
    exact this.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 f
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin k, (fun _ : Fin k => 8 * δ * Lnorm n) i ≤ (digit α (embTuple f i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ k * ∏ _i : Fin k, (8 * δ * Lnorm n)⁻¹ :=
    hC k (embTuple f) (fun _ => 8 * δ * Lnorm n)
      ((injF_iff _).mp (embTuple_injF f)) (fun _ => hn1)
  have hsub : Erdos1002.tupleEvent (detMarkEvent n B) f ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    refine ⟨hαI, fun i => ?_⟩
    exact digit_ge_of_signedMark_mem B hB0 hn2 (Set.mem_iInter.mp hα i).2
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f)
      ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound (le_of_eq ?_))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, div_div,
    ← div_eq_mul_inv]

/-! ## Part C, the deterministic bulk sits inside `{0,…,n}` -/

/-- `λ = π²/(12 log 2) > 1`.  (`π² > 9 > 12 log 2`.) -/
lemma lyapunov_gt_one : 1 < lyapunov := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h12 : (0 : ℝ) < 12 * Real.log 2 := by linarith
  show 1 < Real.pi ^ 2 / (12 * Real.log 2)
  rw [lt_div_iff₀ h12]
  nlinarith

lemma Lnorm_le_self (n : ℕ) : Lnorm n ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Lnorm]
  · have h : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have := Real.log_le_sub_one_of_pos h
    have : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := this
    show Real.log (n : ℝ) ≤ (n : ℝ)
    linarith

lemma mIndex_le (n : ℕ) : mIndex n ≤ n := by
  have hlam := lyapunov_gt_one
  have hL0 : (0 : ℝ) ≤ Lnorm n := Lnorm_nonneg n
  have h1 : Lnorm n / lyapunov ≤ (n : ℝ) := by
    have hdiv : Lnorm n / lyapunov ≤ Lnorm n := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith [Lnorm_le_self n]
  calc mIndex n = ⌊Lnorm n / lyapunov⌋₊ := rfl
    _ ≤ ⌊(n : ℝ)⌋₊ := Nat.floor_mono h1
    _ = n := Nat.floor_natCast n

lemma bulkJ_subset_range (n : ℕ) : bulkJ n ⊆ Finset.range (n + 1) := by
  intro j hj
  have h1 : j ∈ Finset.range (mIndex n + 1) := Finset.mem_of_mem_filter j hj
  rw [Finset.mem_range] at h1 ⊢
  have := mIndex_le n
  omega

/-- `#J_n ≤ 2L` once `L ≥ 1`, from `#J_n ≤ m_n + 1` and `λ > 1`. -/
lemma bulkJ_card_le {n : ℕ} (hL1 : (1 : ℝ) ≤ Lnorm n) :
    ((bulkJ n).card : ℝ) ≤ 2 * Lnorm n := by
  have hlam := lyapunov_gt_one
  have hL0 : (0 : ℝ) ≤ Lnorm n := by linarith
  have hsub : bulkJ n ⊆ Finset.range (mIndex n + 1) := Finset.filter_subset _ _
  have h := Finset.card_le_card hsub
  rw [Finset.card_range] at h
  have h1 : ((bulkJ n).card : ℝ) ≤ (mIndex n : ℝ) + 1 := by exact_mod_cast h
  have h2 : (mIndex n : ℝ) ≤ Lnorm n / lyapunov :=
    Nat.floor_le (div_nonneg hL0 (by linarith))
  have h3 : Lnorm n / lyapunov ≤ Lnorm n := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The deterministic one-level sum over `{0,…,n}` *is* the sum over `J_n` of
display (19): `detMarkEvent` is empty off `J_n`. -/
lemma sum_det_eq_sum_bulkJ (n : ℕ) (B : Set ℝ) :
    (∑ j ∈ Finset.range (n + 1), unifIoo.real (detMarkEvent n B j))
      = ∑ j ∈ bulkJ n, unifIoo.real (oneLevelEvent n B j) := by
  have h1 : (∑ j ∈ bulkJ n, unifIoo.real (detMarkEvent n B j))
      = ∑ j ∈ Finset.range (n + 1), unifIoo.real (detMarkEvent n B j) :=
    Finset.sum_subset (bulkJ_subset_range n) (fun j _ hj => by
      rw [detMarkEvent_of_not_mem hj]; simp)
  rw [← h1]
  exact Finset.sum_congr rfl fun j hj => by rw [detMarkEvent_of_mem hj]

/-! ## Part D, `H/L → 0` -/

lemma tendsto_H_div_L : Tendsto (fun n : ℕ => Hscale n / Lnorm n) atTop (𝓝 0) := by
  have hLtop : Tendsto (fun n : ℕ => Lnorm n) atTop atTop := tendsto_Lnorm_atTop
  have h0 : Tendsto (fun n : ℕ => (Lnorm n) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hLtop
  refine h0.congr' ?_
  filter_upwards [hLtop.eventually_gt_atTop 0] with n hn
  have h : Hscale n / Lnorm n = (Lnorm n) ^ ((3 / 4 : ℝ) - 1) := by
    rw [Real.rpow_sub hn, Real.rpow_one, Hscale]
  rw [h]
  norm_num

lemma tendsto_one_div_L : Tendsto (fun n : ℕ => 1 / Lnorm n) atTop (𝓝 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_Lnorm_atTop

/-! ## Part E, separation (the symmetrized (25)/(26)) and the bad-tuple count -/

/-- **The symmetrized separation conditions (25)-(26)** on an unordered
`k`-tuple.  The manuscript asks (26) only for `i < ℓ`; asking it for all
`i ≠ ℓ` makes the good set smaller, i.e. the residual weaker, and costs
nothing in the count because `TupleCount.SresF` is already quantified over all
ordered pairs. -/
def SepGood {k : ℕ} (n : ℕ) (g : Fin k → ℕ) : Prop :=
  (∀ p q : Fin k, p ≠ q → 200 * Hscale n ≤ |(g q : ℝ) - (g p : ℝ)|) ∧
  (∀ p q : Fin k, p ≠ q → 200 * Hscale n ≤ |(g q : ℝ) - ((mIndex n : ℝ) + (g p : ℝ)) / 2|)

/-- The same conditions read on the `k`-element **subset** `S ⊆ J_n`.  Both
sides of Proposition 4.1 depend only on `S`, so this is the invariant form. -/
def SepGoodSet (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ bulkJ n ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 200 * Hscale n ≤ |(y : ℝ) - (x : ℝ)|) ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 200 * Hscale n ≤ |(y : ℝ) - ((mIndex n : ℝ) + (x : ℝ)) / 2|)

/-- A bulk tuple failing the symmetrized separation lands in Wang-style
exceptional finset `TupleCount.BadF`.  Mirrors `TupleCount.restr_mem_BadF`,
with the ordering hypotheses dropped. -/
lemma sepBad_mem_BadF {k : ℕ} (n K W : ℕ) (hK : 200 * Hscale n ≤ (K : ℝ))
    (hW : 2 * K + 1 ≤ W) (g : Fin k → ℕ) (hin : ∀ i, g i ∈ bulkJ n)
    (hbad : ¬ SepGood n g) : g ∈ TupleCount.BadF n k K W := by
  classical
  have hallJ : g ∈ TupleCount.AllJ n k := Fintype.mem_piFinset.2 hin
  have hKW : (K : ℝ) ≤ (W : ℝ) := by exact_mod_cast (by omega : K ≤ W)
  rcases not_and_or.mp hbad with h | h
  · -- the gap constraint (25) fails
    push_neg at h
    obtain ⟨p, q, hpq, hlt⟩ := h
    have hltK : |(g q : ℝ) - (g p : ℝ)| < (K : ℝ) := lt_of_lt_of_le hlt hK
    have habs := abs_lt.1 hltK
    by_cases hle : g p ≤ g q
    · refine Finset.mem_biUnion.2 ⟨(p, q), Finset.mem_filter.2 ⟨Finset.mem_univ _, hpq⟩, ?_⟩
      refine Finset.mem_union.2 (Or.inl ?_)
      have hub : g q < g p + W := by
        have : ((g q : ℕ) : ℝ) < ((g p + W : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      simp only [TupleCount.SgapF, Finset.mem_filter]
      exact ⟨hallJ, hle, hub⟩
    · push_neg at hle
      refine Finset.mem_biUnion.2 ⟨(q, p),
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hpq.symm⟩, ?_⟩
      refine Finset.mem_union.2 (Or.inl ?_)
      have hub : g p < g q + W := by
        have : ((g p : ℕ) : ℝ) < ((g q + W : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      simp only [TupleCount.SgapF, Finset.mem_filter]
      exact ⟨hallJ, hle.le, hub⟩
  · -- the resonance constraint (26) fails
    push_neg at h
    obtain ⟨p, q, hpq, hres⟩ := h
    have hresK : |(g q : ℝ) - ((mIndex n : ℝ) + (g p : ℝ)) / 2| < (K : ℝ) :=
      lt_of_lt_of_le hres hK
    have habs := abs_lt.1 hresK
    refine Finset.mem_biUnion.2 ⟨(p, q), Finset.mem_filter.2 ⟨Finset.mem_univ _, hpq⟩, ?_⟩
    refine Finset.mem_union.2 (Or.inr ?_)
    set M : ℕ := (mIndex n + g p) / 2 with hM
    have hMd : 2 * M ≤ mIndex n + g p ∧ mIndex n + g p < 2 * M + 2 := by omega
    have hMle : (M : ℝ) ≤ ((mIndex n : ℝ) + (g p : ℝ)) / 2 := by
      have : (2 * M : ℝ) ≤ ((mIndex n : ℝ) + (g p : ℝ)) := by exact_mod_cast hMd.1
      linarith
    have hMlt : ((mIndex n : ℝ) + (g p : ℝ)) / 2 < (M : ℝ) + 1 := by
      have : ((mIndex n : ℝ) + (g p : ℝ)) < (2 * M : ℝ) + 2 := by exact_mod_cast hMd.2
      linarith
    have hub : g q < M + 1 + K := by
      have : ((g q : ℕ) : ℝ) < ((M + 1 + K : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hlb : M ≤ g q + K := by
      have : ((M : ℕ) : ℝ) ≤ ((g q + K : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    simp only [TupleCount.SresF, Finset.mem_filter]
    exact ⟨hallJ, by simpa [hM] using (by omega : M - K ≤ g q),
      by simpa [hM] using (by omega : g q < (M - K) + W)⟩

/-- The set of embeddings whose values all lie in `J_n` but which fail the
symmetrized separation. -/
def badEmb (n k : ℕ) : Finset (Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :=
  Finset.univ.filter
    (fun f => (∀ i, ((f i : ℕ)) ∈ bulkJ n) ∧ ¬ SepGood n (embTuple f))

/-- The set of embeddings whose values all lie in `J_n` and which satisfy the
symmetrized separation. -/
def goodEmb (n k : ℕ) : Finset (Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :=
  Finset.univ.filter
    (fun f => (∀ i, ((f i : ℕ)) ∈ bulkJ n) ∧ SepGood n (embTuple f))

lemma mem_badEmb {n k : ℕ} (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :
    f ∈ badEmb n k ↔ ((∀ i, ((f i : ℕ)) ∈ bulkJ n) ∧ ¬ SepGood n (embTuple f)) :=
  ⟨fun h => (Finset.mem_filter.mp h).2,
   fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

lemma mem_goodEmb {n k : ℕ} (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :
    f ∈ goodEmb n k ↔ ((∀ i, ((f i : ℕ)) ∈ bulkJ n) ∧ SepGood n (embTuple f)) :=
  ⟨fun h => (Finset.mem_filter.mp h).2,
   fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

lemma badEmb_card_le (n k K W : ℕ) (hK : 200 * Hscale n ≤ (K : ℝ)) (hW : 2 * K + 1 ≤ W) :
    (badEmb n k).card ≤ (TupleCount.BadF n k K W).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun f => embTuple f) ?_ ?_
  · intro f hf
    obtain ⟨h1, h2⟩ := (mem_badEmb f).mp hf
    exact sepBad_mem_BadF n K W hK hW (embTuple f) h1 h2
  · intro f _ g _ h
    exact embTuple_injective h

/-- **The bad-tuple count in the currency display (39) needs.**  The number of
embeddings `Fin k ↪ {0,…,n}` with all values in the bulk that violate the
symmetrized (25)/(26) is `O_k(L^{k-1}H)`.

This is *not* `Kwon1002.nonGood_tuple_count'`: that statement counts increasing
tuples, whereas (39) sums over embeddings, and the two differ by the `k!`
relabelings.  The proof goes back to `TupleCount.card_BadF_le`, which is stated
on arbitrary tuples and quantified over all ordered pairs, so it covers the
symmetrized condition verbatim. -/
theorem badIn_emb_count (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((badEmb n k).card : ℝ) ≤ C * (Lnorm n) ^ (k - 1) * Hscale n := by
  refine ⟨806 * ((k : ℝ) ^ 2 + 1) * 2 ^ (k - 1), by positivity, ?_⟩
  filter_upwards [tendsto_Lnorm_atTop.eventually_ge_atTop 1] with n hL1
  have hL0 : (0 : ℝ) ≤ Lnorm n := by linarith
  have hH1 : (1 : ℝ) ≤ Hscale n := by
    show (1 : ℝ) ≤ (Lnorm n) ^ (3 / 4 : ℝ)
    calc (1 : ℝ) = (1 : ℝ) ^ (3 / 4 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (Lnorm n) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hL1 (by norm_num)
  obtain ⟨K, hKge, hKlt⟩ : ∃ K : ℕ, 200 * Hscale n ≤ (K : ℝ) ∧ (K : ℝ) < 200 * Hscale n + 1 :=
    ⟨⌈200 * Hscale n⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  have hcard1 : (badEmb n k).card ≤ k * k * (2 * ((bulkJ n).card ^ (k - 1) * (2 * K + 1))) :=
    le_trans (badEmb_card_le n k K (2 * K + 1) hKge le_rfl)
      (TupleCount.card_BadF_le n k K (2 * K + 1))
  have hJ : ((bulkJ n).card : ℝ) ≤ 2 * Lnorm n := bulkJ_card_le hL1
  have hJ0 : (0 : ℝ) ≤ ((bulkJ n).card : ℝ) := Nat.cast_nonneg _
  have hY : 2 * (K : ℝ) + 1 ≤ 403 * Hscale n := by linarith
  have hcast : ((k * k * (2 * ((bulkJ n).card ^ (k - 1) * (2 * K + 1))) : ℕ) : ℝ)
      = ((k : ℝ) * (k : ℝ) * 2) * (((bulkJ n).card : ℝ) ^ (k - 1) * (2 * (K : ℝ) + 1)) := by
    push_cast; ring
  have hXY : ((bulkJ n).card : ℝ) ^ (k - 1) * (2 * (K : ℝ) + 1)
      ≤ ((2 : ℝ) ^ (k - 1) * (Lnorm n) ^ (k - 1)) * (403 * Hscale n) := by
    refine mul_le_mul ?_ hY (by linarith) (by positivity)
    calc ((bulkJ n).card : ℝ) ^ (k - 1) ≤ (2 * Lnorm n) ^ (k - 1) :=
          pow_le_pow_left₀ hJ0 hJ _
      _ = (2 : ℝ) ^ (k - 1) * (Lnorm n) ^ (k - 1) := mul_pow _ _ _
  have hrr : (0 : ℝ) ≤ (k : ℝ) * (k : ℝ) * 2 := by positivity
  have key := mul_le_mul_of_nonneg_left hXY hrr
  set P : ℝ := 2 ^ (k - 1) * (Lnorm n) ^ (k - 1) * Hscale n with hPdef
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  have hfinal : ((k * k * (2 * ((bulkJ n).card ^ (k - 1) * (2 * K + 1))) : ℕ) : ℝ)
      ≤ (806 * ((k : ℝ) ^ 2 + 1) * 2 ^ (k - 1)) * (Lnorm n) ^ (k - 1) * Hscale n := by
    rw [hcast]
    refine le_trans key ?_
    calc ((k : ℝ) * (k : ℝ) * 2)
            * ((2 : ℝ) ^ (k - 1) * (Lnorm n) ^ (k - 1) * (403 * Hscale n))
        = 806 * (k : ℝ) ^ 2 * P := by rw [hPdef]; ring
      _ ≤ 806 * ((k : ℝ) ^ 2 + 1) * P := by nlinarith [hP0]
      _ = (806 * ((k : ℝ) ^ 2 + 1) * 2 ^ (k - 1)) * (Lnorm n) ^ (k - 1) * Hscale n := by
          rw [hPdef]; ring
  refine le_trans ?_ hfinal
  exact_mod_cast hcard1

/-! ## Part F, subsets, embeddings, and the two residuals -/

lemma tupleEvent_eq_biInter {k n : ℕ} (B : Set ℝ)
    (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :
    Erdos1002.tupleEvent (detMarkEvent n B) f
      = ⋂ x ∈ ((Finset.univ.image (embTuple f) : Finset ℕ) : Set ℕ), detMarkEvent n B x := by
  ext α
  rw [Set.mem_iInter₂]
  constructor
  · intro hα x hx
    have hα' : α ∈ ⋂ i : Fin k, detMarkEvent n B (embTuple f i) := hα
    have hex : ∃ i : Fin k, embTuple f i = x := by simpa using hx
    obtain ⟨i, hi⟩ := hex
    have h2 := Set.mem_iInter.mp hα' i
    rwa [hi] at h2
  · intro hα
    show α ∈ ⋂ i : Fin k, detMarkEvent n B (embTuple f i)
    exact Set.mem_iInter.mpr fun i => hα (embTuple f i) (by simp)

lemma prod_eq_prod_image {k n : ℕ} (w : ℕ → ℝ)
    (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :
    (∏ ℓ, w (embTuple f ℓ)) = ∏ x ∈ Finset.univ.image (embTuple f), w x :=
  (Finset.prod_image (fun a _ b _ h => (embTuple_injF f) a b h)).symm

lemma card_image_embTuple {k n : ℕ} (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) :
    (Finset.univ.image (embTuple f)).card = k := by
  rw [Finset.card_image_of_injective _ ((injF_iff _).mp (embTuple_injF f)),
    Finset.card_univ, Fintype.card_fin]

lemma sepGoodSet_of_sepGood {k n : ℕ} (f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ))
    (hin : ∀ i, ((f i : ℕ)) ∈ bulkJ n) (hsep : SepGood n (embTuple f)) :
    SepGoodSet n (Finset.univ.image (embTuple f)) := by
  have hmem : ∀ x ∈ Finset.univ.image (embTuple f), ∃ i, embTuple f i = x := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := hmem x hx
    exact hin i
  · intro x hx y hy hxy
    obtain ⟨p, rfl⟩ := hmem x hx
    obtain ⟨q, rfl⟩ := hmem y hy
    exact hsep.1 p q (fun hpq => hxy (by rw [hpq]))
  · intro x hx y hy hxy
    obtain ⟨p, rfl⟩ := hmem x hx
    obtain ⟨q, rfl⟩ := hmem y hy
    exact hsep.2 p q (fun hpq => hxy (by rw [hpq]))

/-- **Residual 1: the §7/§4 index-set bridge, at the level of `k`-tuples.**

The ordered-distinct-tuple sums attached to the *random* bulk
`Marks.bulkIndices c α n` (§7, the stopping time) and to the *deterministic*
bulk `Section4.bulkJ n` of display (19) differ by `o(1)`.

**This is the recorded finding.**  §5 of the manuscript passes between (19)
and (38) without comment; `Kwon1002.bulk_window_bridge_oneLevel` isolates the
`k = 1` case, and this statement is the one (38)-(40) actually needs.  The
`k = 1` case is *derived* from it below, so the two bridges collapse to one.

**Obstruction.**  Needs the §7 stopping-time analysis (Lem. 7.1 and the `O(H)`
trimming at both ends), of which only the Lamé bound
`Kwon1002.L2Estimate.stoppingTime_le_log` is currently proved in-tree. -/
theorem bulk_window_bridge_tuple (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
      atTop (𝓝 0) := by
  sorry

/-- **Residual 2a: Proposition 4.1 for the mark event, at the class the
Jackson step actually admits.**

On a `k`-element subset `S` of the deterministic bulk satisfying the
symmetrized (25)/(26), the joint probability that every level of `S` carries a
mark in `B` factorizes into the product of the one-level probabilities, with
error `O(L^{-(k+1)})`, *one power of `L` better than the `O(L^{-k})` needed to
survive the `O(L^k)` tuples*, which is exactly the `O_{r,D,A}(L^{-A})` of
display (27) taken at `A = k+1`.

**The boundary-regularity hypothesis, and why it is here.**  The residual used
to quantify over merely measurable `B`.  `Kwon1002/JacksonGate.lean` shows the
route the residual names cannot reach that class: membership of the symbol
class `P_D(L)` of display (24) forces continuity
(`JacksonGate.continuous_of_isInPD`), so a two-valued member is constant
(`JacksonGate.isInPD_const_of_two_valued`), and the passage is therefore an
*approximation* whose rate the error budget fixes at `η_L = O(L^{-2})`
uniformly in the digit.  For an indicator with `m` jumps Jackson gives
`O(m/deg) = O(m·L^{-D})` with `D > 2`; for a merely measurable `B` no rate
exists at all, and `volume (frontier B) = 0` does not repair it (it gives
qualitative approximability, not a rate).  `IsFiniteUnionOfIntervals` is the
hypothesis that supplies the jump count, and
`IntervalClass.markSection_isUnionOfIntervals` proves it supplies it
*uniformly in the digit and in the sign*: `W` is piecewise monotone with
exactly two branches on the fundamental cell, so the `θ`-section of the mark
event over a union of `m` intervals is a union of at most `2m` intervals
whatever the digit `a` and the sign `(-1)^j` are.  That uniformity is what the
tuple sum needs.

**Obstruction that remains.**  Proposition 4.1 itself is now unconditional
(`Kwon1002.prop_4_1_marked_factorization_unconditional`), and the sorting
bijection between its increasing tuple `j_1 < ⋯ < j_k` and this residual's
subset `S` is discharged (`JacksonGate.exists_goodTuple_of_sepGoodSet`).  What
is left is exactly the Jackson construction: from "the `θ`-section is a union
of at most `2m` intervals" to "there is a trigonometric polynomial of degree
`L^{D}` within `L¹`-distance `O(m·L^{-D})` of its indicator, with coefficient
`ℓ¹` norm inside the budget of display (24)".  Mathlib carries no Fejér or
Jackson kernel, so this is a from-scratch construction.  Note also the budget
finding recorded in `Kwon1002/OneLevelLaw.lean`: the digit cut already spends
`L^D` of display (24)'s `ℓ¹` allowance, so the Jackson factor must be placed in
`P_{D'}(L)` for some `D' > D`; the `D` of the class and the `D` of the digit cut
are different constants. -/
theorem goodSet_mark_factorization_intervals (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (_hint : IntervalClass.IsFiniteUnionOfIntervals B) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S.card = k → SepGoodSet n S →
      |unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n B x)
          - ∏ x ∈ S, unifIoo.real (detMarkEvent n B x)| ≤ C / (Lnorm n) ^ (k + 1) := by
  sorry

/-- **Residual 2b: the passage from finite unions of intervals back to
measurable sets.**

Residual 2a is stated at finite unions of intervals because that is the class
the Jackson step admits (see its docstring).  The consumers of residual 2 —
`det_quasi_independence` below, and through it
`det_tuple_measure_convergence`, `tuple_measure_convergence` and
`tuple_quasi_independence` — quantify over merely measurable `B`, and those
statements are *not* weakened here: their `B`-generality is expected to be
true, recoverable from the interval case by an approximation argument against
the absolutely continuous limit `Λ`.  That argument is a separate step, and
isolating it is the point of this residual.  Pushing the interval hypothesis
into the consumers instead would weaken statements that are true, which is why
it is not done.

The residual is stated as the implication rather than as a second copy of the
conclusion, so that it says exactly one thing: *the interval case implies the
measurable case*, uniformly in `k`.

**Obstruction.**  The approximation is not free: the error in residual 2a is
`C/L^{k+1}` with `C` depending on `B`, and an approximation argument has to
control how `C` degrades as an interval family approaches a general measurable
set.  The route is the outer regularity of Lebesgue measure together with the
proved one-level bound `det_singleLevel_measure_le`, which caps the mass of
the symmetric difference at each level by `O(1/L)`. -/
theorem goodSet_intervals_to_measurable
    (_h : ∀ B : Set ℝ, MeasurableSet B → (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) →
        (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → IntervalClass.IsFiniteUnionOfIntervals B →
        ∀ k : ℕ,
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S.card = k → SepGoodSet n S →
          |unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n B x)
              - ∏ x ∈ S, unifIoo.real (detMarkEvent n B x)| ≤ C / (Lnorm n) ^ (k + 1)) :
    ∀ B : Set ℝ, MeasurableSet B → (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) →
      (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → ∀ k : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S.card = k → SepGoodSet n S →
        |unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n B x)
            - ∏ x ∈ S, unifIoo.real (detMarkEvent n B x)| ≤ C / (Lnorm n) ^ (k + 1) := by
  sorry

/-- **Residual 2: Proposition 4.1 for the mark event.**

Statement unchanged — every consumer below and every token-identity check at
the foot of this file reads exactly the same `Prop` as before — but it is no
longer a bare `sorry`: it is now *derived* from residuals 2a and 2b, which
between them say what the manuscript's proof actually does.  The split is the
content of `Kwon1002/JacksonGate.lean`'s verdict, carried out.

The concrete `B` the §5 chain instantiates is the large-jump truncation
`{x : ε < |x|}` cut to the bounded window that `_hBbd` forces, and
`IntervalClass.isUnionOfIntervals_truncation` proves that set is a union of
**two** intervals — so residual 2a alone already covers every instantiation the
development makes, and residual 2b is only needed to keep the consumers stated
at their present generality. -/
theorem goodSet_mark_factorization (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S.card = k → SepGoodSet n S →
      |unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n B x)
          - ∏ x ∈ S, unifIoo.real (detMarkEvent n B x)| ≤ C / (Lnorm n) ^ (k + 1) :=
  goodSet_intervals_to_measurable
    (fun B' hB' hB0' hBbd' hint' k' =>
      goodSet_mark_factorization_intervals B' hB' hB0' hBbd' hint' k')
    B _hB _hB0 _hBbd k

/-- **Every instantiation the §5 chain makes supplies the hypothesis of
residual 2a.**  The truncation window `{x : ε < |x| ∧ |x| ≤ R}` — the only
shape `B` ever takes below Proposition 5.1, and the shape the residual's own
`_hB0`/`_hBbd` hypotheses force — is a union of two intervals, so residual 2a
applies to it directly, with jump count `m = 2` and hence with a `θ`-section of
at most four intervals uniformly in the digit
(`IntervalClass.markSection_isUnionOfIntervals`). -/
theorem goodSet_mark_factorization_truncation (ε R : ℝ)
    (hB : MeasurableSet {x : ℝ | ε < |x| ∧ |x| ≤ R})
    (hB0 : ∃ δ > 0, ∀ x ∈ {x : ℝ | ε < |x| ∧ |x| ≤ R}, δ ≤ |x|) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S.card = k → SepGoodSet n S →
      |unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n {x : ℝ | ε < |x| ∧ |x| ≤ R} x)
          - ∏ x ∈ S, unifIoo.real (detMarkEvent n {x : ℝ | ε < |x| ∧ |x| ≤ R} x)|
        ≤ C / (Lnorm n) ^ (k + 1) :=
  goodSet_mark_factorization_intervals _ hB hB0 ⟨R, fun x hx => hx.2⟩
    (IntervalClass.isUnionOfIntervals_truncation ε R).finite k

/-! ## Part G, the deterministic quasi-independence, proved from the residual -/

/-- **The manuscript's steps 2 and 3, on the deterministic side.**

`∑_f P(⋂_ℓ X_{n,f ℓ} ∈ B) - ∑_f ∏_ℓ P(X_{n,f ℓ} ∈ B) → 0`, the sums over
ordered distinct `k`-tuples of levels.

Proved from `goodSet_mark_factorization` (residual 2) **and nothing else
sorried**:

* tuples with a level outside the bulk contribute `0` exactly;
* tuples inside the bulk failing the separation are `O_k(L^{k-1}H)` in number
  (`badIn_emb_count`, proved) and each contributes `O(L^{-k})`
  (`det_tuple_measure_le` and `det_singleLevel_measure_le`, proved), for a
  total `O(H/L) = O(L^{-1/4}) → 0`;
* the remaining tuples are `O(L^k)` in number and each contributes
  `O(L^{-(k+1)})` by residual 2, for a total `O(L^{-1}) → 0`. -/
theorem det_quasi_independence (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ)))
      atTop (𝓝 0) := by
  classical
  obtain ⟨δ, hδ, hBδ⟩ := hB0
  match k with
  | 0 =>
    have hzero : ∀ n : ℕ,
        (∑ f : Fin 0 ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
          - ∑ f : Fin 0 ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ)) = 0 := by
      intro n
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun f _ => ?_
      have he : Erdos1002.tupleEvent (detMarkEvent n B) f = (Set.univ : Set ℝ) :=
        Set.iInter_of_empty _
      have hu : unifIoo.real (Set.univ : Set ℝ) = 1 := by
        rw [Measure.real, unifIoo, Measure.restrict_apply_univ, Real.volume_Ioo]
        simp
      simp [he, hu]
    exact Filter.Tendsto.congr (fun n => (hzero n).symm) tendsto_const_nhds
  | (m + 1) =>
    obtain ⟨C₁, hC₁, hC₁le⟩ := det_singleLevel_measure_le B hδ hBδ
    obtain ⟨C₂, hC₂, hC₂le⟩ := det_tuple_measure_le B hδ hBδ (m + 1)
    obtain ⟨C₃, hC₃, hC₃le⟩ := goodSet_mark_factorization B hB ⟨δ, hδ, hBδ⟩ hBbd (m + 1)
    obtain ⟨C₄, hC₄, hC₄le⟩ := badIn_emb_count (m + 1)
    set C : ℝ := max C₁ C₂ with hCdef
    have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
    refine squeeze_zero_norm'
      (a := fun n : ℕ => 2 * C ^ (m + 1) * C₄ * (Hscale n / Lnorm n)
        + 2 ^ (m + 1) * C₃ * (1 / Lnorm n)) ?_ ?_
    · filter_upwards [hC₁le, hC₂le, hC₃le, hC₄le,
        tendsto_Lnorm_atTop.eventually_ge_atTop 1] with n h1 h2 h3 h4 hL1
      have hL0 : (0 : ℝ) < Lnorm n := by linarith
      simp only [Nat.add_sub_cancel] at h4
      set D : (Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ)) → ℝ := fun f =>
        unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f)
          - ∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ)) with hD
      -- one-level and tuple bounds, uniform in the tuple
      have hprodle : ∀ f : Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ),
          (∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ))) ≤ (C₁ / Lnorm n) ^ (m + 1) := by
        intro f
        calc (∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ)))
            ≤ ∏ _ℓ : Fin (m + 1), (C₁ / Lnorm n) :=
              Finset.prod_le_prod (fun ℓ _ => measureReal_nonneg)
                (fun ℓ _ => h1 (embTuple f ℓ))
          _ = (C₁ / Lnorm n) ^ (m + 1) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hprodnn : ∀ f : Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ),
          (0 : ℝ) ≤ ∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ)) :=
        fun f => Finset.prod_nonneg fun ℓ _ => measureReal_nonneg
      -- the three-way split
      have hdisj : Disjoint (goodEmb n (m + 1)) (badEmb n (m + 1)) := by
        rw [Finset.disjoint_left]
        intro f hf hf'
        exact ((mem_badEmb f).mp hf').2 ((mem_goodEmb f).mp hf).2
      have hzero : ∀ f ∈ (Finset.univ : Finset (Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ))),
          f ∉ goodEmb n (m + 1) ∪ badEmb n (m + 1) → |D f| = 0 := by
        intro f _ hf
        have hnotin : ¬ (∀ i, ((f i : ℕ)) ∈ bulkJ n) := by
          intro hin
          rcases Classical.em (SepGood n (embTuple f)) with hg | hg
          · exact hf (Finset.mem_union_left _ ((mem_goodEmb f).mpr ⟨hin, hg⟩))
          · exact hf (Finset.mem_union_right _ ((mem_badEmb f).mpr ⟨hin, hg⟩))
        push_neg at hnotin
        obtain ⟨i₀, hi₀⟩ := hnotin
        have hi₀' : embTuple f i₀ ∉ bulkJ n := hi₀
        have he : Erdos1002.tupleEvent (detMarkEvent n B) f = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro α hα
          have hα' : α ∈ ⋂ i : Fin (m + 1), detMarkEvent n B (embTuple f i) := hα
          have hmem := Set.mem_iInter.mp hα' i₀
          rw [detMarkEvent_of_not_mem hi₀'] at hmem
          exact hmem
        have hp : (∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ))) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
          rw [detMarkEvent_of_not_mem hi₀']
          simp
        simp [hD, he, hp]
      have hsum : (∑ f ∈ goodEmb n (m + 1) ∪ badEmb n (m + 1), |D f|)
          = ∑ f : Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ), |D f| :=
        Finset.sum_subset (Finset.subset_univ _) hzero
      -- the good part
      have hgoodterm : ∀ f ∈ goodEmb n (m + 1), |D f| ≤ C₃ / (Lnorm n) ^ (m + 1 + 1) := by
        intro f hf
        obtain ⟨hfin, hfsep⟩ := (mem_goodEmb f).mp hf
        have := h3 (Finset.univ.image (embTuple f)) (card_image_embTuple f)
          (sepGoodSet_of_sepGood f hfin hfsep)
        rw [hD]
        simp only
        rw [tupleEvent_eq_biInter B f,
          prod_eq_prod_image (fun x => unifIoo.real (detMarkEvent n B x)) f]
        exact this
      have hgoodcard : ((goodEmb n (m + 1)).card : ℝ) ≤ (2 * Lnorm n) ^ (m + 1) := by
        have hsub : ((goodEmb n (m + 1)).card : ℕ) ≤ ((bulkJ n).card) ^ (m + 1) := by
          have hh : (goodEmb n (m + 1)).card
              ≤ (Fintype.piFinset (fun _ : Fin (m + 1) => bulkJ n)).card := by
            refine Finset.card_le_card_of_injOn (fun f => embTuple f) ?_ ?_
            · intro f hf
              exact Fintype.mem_piFinset.2 ((mem_goodEmb f).mp hf).1
            · intro f _ g _ h
              exact embTuple_injective h
          rwa [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin] at hh
        calc ((goodEmb n (m + 1)).card : ℝ) ≤ (((bulkJ n).card : ℝ)) ^ (m + 1) := by
              exact_mod_cast hsub
          _ ≤ (2 * Lnorm n) ^ (m + 1) :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (bulkJ_card_le hL1) _
      have hgood : (∑ f ∈ goodEmb n (m + 1), |D f|)
          ≤ 2 ^ (m + 1) * C₃ * (1 / Lnorm n) := by
        have hb := Finset.sum_le_card_nsmul (goodEmb n (m + 1)) (fun f => |D f|)
          (C₃ / (Lnorm n) ^ (m + 1 + 1)) hgoodterm
        rw [nsmul_eq_mul] at hb
        refine le_trans hb ?_
        have hq : (0 : ℝ) ≤ C₃ / (Lnorm n) ^ (m + 1 + 1) := by positivity
        calc ((goodEmb n (m + 1)).card : ℝ) * (C₃ / (Lnorm n) ^ (m + 1 + 1))
            ≤ (2 * Lnorm n) ^ (m + 1) * (C₃ / (Lnorm n) ^ (m + 1 + 1)) :=
              mul_le_mul_of_nonneg_right hgoodcard hq
          _ = 2 ^ (m + 1) * C₃ * (1 / Lnorm n) := by
              rw [mul_pow, pow_succ (Lnorm n) (m + 1)]
              field_simp
      -- the bad part
      have hCC₂ : C₂ / Lnorm n ≤ C / Lnorm n := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (inv_nonneg.mpr hL0.le)
      have hCC₁ : C₁ / Lnorm n ≤ C / Lnorm n := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (inv_nonneg.mpr hL0.le)
      have hbadterm : ∀ f ∈ badEmb n (m + 1), |D f| ≤ 2 * (C / Lnorm n) ^ (m + 1) := by
        intro f _
        have hA : unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f)
            ≤ (C / Lnorm n) ^ (m + 1) :=
          le_trans (h2 f) (pow_le_pow_left₀ (by positivity) hCC₂ _)
        have hP : (∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ)))
            ≤ (C / Lnorm n) ^ (m + 1) :=
          le_trans (hprodle f) (pow_le_pow_left₀ (by positivity) hCC₁ _)
        rw [hD]
        simp only
        rw [abs_le]
        constructor <;> [linarith [measureReal_nonneg (μ := unifIoo)
          (s := Erdos1002.tupleEvent (detMarkEvent n B) f), hprodnn f, hP];
          linarith [measureReal_nonneg (μ := unifIoo)
          (s := Erdos1002.tupleEvent (detMarkEvent n B) f), hprodnn f, hA]]
      have hbad : (∑ f ∈ badEmb n (m + 1), |D f|)
          ≤ 2 * C ^ (m + 1) * C₄ * (Hscale n / Lnorm n) := by
        have hb := Finset.sum_le_card_nsmul (badEmb n (m + 1)) (fun f => |D f|)
          (2 * (C / Lnorm n) ^ (m + 1)) hbadterm
        rw [nsmul_eq_mul] at hb
        refine le_trans hb ?_
        have hq : (0 : ℝ) ≤ 2 * (C / Lnorm n) ^ (m + 1) := by positivity
        calc ((badEmb n (m + 1)).card : ℝ) * (2 * (C / Lnorm n) ^ (m + 1))
            ≤ (C₄ * (Lnorm n) ^ m * Hscale n) * (2 * (C / Lnorm n) ^ (m + 1)) :=
              mul_le_mul_of_nonneg_right h4 hq
          _ = 2 * C ^ (m + 1) * C₄ * (Hscale n / Lnorm n) := by
              rw [div_pow, pow_succ (Lnorm n) m]
              field_simp
      -- assemble
      rw [Real.norm_eq_abs, ← Finset.sum_sub_distrib]
      calc |∑ f : Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ), D f|
          ≤ ∑ f : Fin (m + 1) ↪ (Finset.range (n + 1) : Finset ℕ), |D f| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = (∑ f ∈ goodEmb n (m + 1), |D f|) + ∑ f ∈ badEmb n (m + 1), |D f| := by
            rw [← hsum, Finset.sum_union hdisj]
        _ ≤ 2 * C ^ (m + 1) * C₄ * (Hscale n / Lnorm n)
              + 2 ^ (m + 1) * C₃ * (1 / Lnorm n) := by linarith
    · have hl1 : Tendsto (fun n : ℕ => 2 * C ^ (m + 1) * C₄ * (Hscale n / Lnorm n))
          atTop (𝓝 0) := by
        simpa using tendsto_H_div_L.const_mul (2 * C ^ (m + 1) * C₄)
      have hl2 : Tendsto (fun n : ℕ => 2 ^ (m + 1) * C₃ * (1 / Lnorm n)) atTop (𝓝 0) := by
        simpa using tendsto_one_div_L.const_mul ((2 : ℝ) ^ (m + 1) * C₃)
      simpa using hl1.add hl2

/-! ## Part H, the deterministic limit and the three targets -/

/-- The deterministic one-level sums converge to the Lévy intensity.
**Consumes the sorried `Kwon1002.deterministic_oneLevel_intensity`** of
`Kwon1002/FiveFinal.lean` (display (35) on the bulk of (19)). -/
theorem sum_det_tendsto (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), unifIoo.real (detMarkEvent n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) :=
  Filter.Tendsto.congr (fun n => (sum_det_eq_sum_bulkJ n B).symm)
    (deterministic_oneLevel_intensity B hB hB0 hBbd)

/-- The deterministic `k`-tuple sums converge to `Λ(B)^k`: the whole of
displays (39)-(40) on the deterministic bulk.  Combines
`TupleMeasure.tendsto_emb_sum_of_inputs` (proved), `det_singleLevel_measure_le`
(proved), `sum_det_tendsto` and `det_quasi_independence`. -/
theorem det_tuple_measure_convergence (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  obtain ⟨δ, hδ, hBδ⟩ := hB0
  obtain ⟨C, hC, hCle⟩ := det_singleLevel_measure_le B hδ hBδ
  refine tendsto_emb_sum_of_inputs k (fun n => Finset.range (n + 1))
    (fun n j => unifIoo.real (detMarkEvent n B j)) _
    ((levyIntensity B).toReal) (fun n => C / Lnorm n)
    (fun n j => measureReal_nonneg) (fun n => div_nonneg hC.le (Lnorm_nonneg n))
    ?_ ?_ ?_ ?_
  · filter_upwards [hCle] with n hn j _ using hn j
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_Lnorm_atTop
  · exact sum_det_tendsto B hB ⟨δ, hδ, hBδ⟩ hBbd
  · exact det_quasi_independence B hB ⟨δ, hδ, hBδ⟩ hBbd k

/-- **Target 3**, `Kwon1002.LevyExponent.tuple_measure_convergence`
(`Kwon1002/LevyExponent.lean` line 263), reproduced token for token and proved
from `bulk_window_bridge_tuple` (residual 1) plus
`det_tuple_measure_convergence`. -/
theorem tuple_measure_convergence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  have h := (bulk_window_bridge_tuple c B _hB _hB0 _hBbd k).add
    (det_tuple_measure_convergence B _hB _hB0 _hBbd k)
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-- The `k = 1` instance of the bridge, in the one-level currency of
`Kwon1002.bulk_window_bridge_oneLevel`: an embedding `Fin 1 ↪ s` is an element
of `s`, and the tuple event is the one-level event. -/
def embOneEquiv (s : Finset ℕ) : (Fin 1 ↪ (s : Finset ℕ)) ≃ (s : Finset ℕ) where
  toFun f := f 0
  invFun a := ⟨fun _ => a, fun x y _ => Subsingleton.elim x y⟩
  left_inv f := by
    apply Function.Embedding.ext
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  right_inv a := rfl

lemma sum_emb_one_eq (n : ℕ) (E : ℕ → Set ℝ) :
    (∑ f : Fin 1 ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent E f))
      = ∑ j ∈ Finset.range (n + 1), unifIoo.real (E j) := by
  have h1 : ∀ f : Fin 1 ↪ (Finset.range (n + 1) : Finset ℕ),
      Erdos1002.tupleEvent E f = E ((f 0 : ℕ)) := by
    intro f
    ext α
    simp [Erdos1002.tupleEvent, Set.mem_iInter, Fin.forall_fin_one]
  simp only [h1]
  rw [← Finset.sum_coe_sort (Finset.range (n + 1)) (fun j => unifIoo.real (E j))]
  exact Fintype.sum_equiv (embOneEquiv (Finset.range (n + 1))) _ _ (fun f => rfl)

/-- **Target 1**, `Kwon1002.TupleMeasure.oneLevel_intensity_limit`
(`Kwon1002/TupleMeasure.lean` line 544), reproduced token for token and proved
from `bulk_window_bridge_tuple` at `k = 1` together with `sum_det_tendsto`.

In particular `Kwon1002.bulk_window_bridge_oneLevel` is **not** used: the
one-level bridge is the `k = 1` case of the tuple bridge. -/
theorem oneLevel_intensity_limit (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        unifIoo.real (bulkMarkEvent c n B j)) atTop (𝓝 ((levyIntensity B).toReal)) := by
  have hbr := bulk_window_bridge_tuple c B _hB _hB0 _hBbd 1
  have hbr' : Tendsto (fun n : ℕ =>
      (∑ j ∈ Finset.range (n + 1), unifIoo.real (bulkMarkEvent c n B j))
        - ∑ j ∈ Finset.range (n + 1), unifIoo.real (detMarkEvent n B j)) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun n => ?_) hbr
    rw [sum_emb_one_eq n (bulkMarkEvent c n B), sum_emb_one_eq n (detMarkEvent n B)]
  have h := hbr'.add (sum_det_tendsto B _hB _hB0 _hBbd)
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-- **Target 2**, `Kwon1002.TupleMeasure.tuple_quasi_independence`
(`Kwon1002/TupleMeasure.lean` line 570), reproduced token for token and proved
from `tuple_measure_convergence` (above), `oneLevel_intensity_limit` (above),
the proved `TupleMeasure.singleLevel_measure_le` and the proved
`Kwon1002.tendsto_emb_prod_sum`.

Unlike `Kwon1002.tuple_quasi_independence'` of `Kwon1002/FiveFinal.lean`, this
does **not** consume the sorried `LevyExponent.tuple_measure_convergence`: the
version it feeds on is the one proved above from residuals 1-2. -/
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

/-! ## Part I, the token-identity checks, inside Lean

Each `example` states the source theorem's type and closes it with this file's
version.  If a single token of a statement had drifted, these would not
elaborate. -/

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

end TupleFinal

end Kwon1002
