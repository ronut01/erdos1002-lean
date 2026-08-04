import Kwon1002.SmallJumps
import Kwon1002.DigitTail

/-!
# L2input, the analytic core of Lemma 5.2

Target: `Kwon1002.truncatedBulkSum_centered_L2` of `Kwon1002/SmallJumps.lean`,
the single sorried input on which the already-proved Lemma 5.2
(`small_jumps_variance`) rests.  It is reproduced here **verbatim** (diffed
token for token against lines 504-509 of `SmallJumps.lean`) as
`L2Estimate.truncatedBulkSum_centered_L2`; the enclosing `L2Estimate` namespace only
avoids a clash with the sorried original.

## Proved outright

* `integral_sq_le_of_tail`, a general layer-cake second-moment bound: on a
  finite measure space, `0 ≤ f ≤ M` together with `ν{f > t} ≤ K/(1+t)` gives
  `∫ f² ≤ 2KM`.  This is the step of the proof of (42) that must not lose a
  logarithm: `∫₀^M 2t·K/(1+t) dt ≤ 2KM`, whereas the cruder `E f² ≤ M·E f`
  gives `KM log(1+M)` and, after division by `L²`, a spurious `ε log(εL)`.
* `max_le_digit_of_lt_mark`, `mark_tail_bound`, the manuscript's opening
  sentence, "Since `W ≤ 1/8`, Lemma 3.1(ii) gives, uniformly in `j, n`,
  `P(Z_{n,j} > t) ≤ C/(1+t)`", from `mark_le_digit_div_eight` (`W ≤ 1/8`)
  and `digit_tail_product` (Lem 3.1(ii), display (15), proved in
  `DigitTail.lean`).  Effective constant `2·24 = 48`.
* `mark_joint_tail_bound`, the two-level companion the manuscript states
  next: `P(Z_{n,j} > s, Z_{n,k} > t) ≤ C/((1+s)(1+t))` for `j ≠ k`.  This
  is display (15) with `s = 2`; effective constant `4·24² = 2304`.  It is
  the input to the second half of (42), `E|U_j U_k| ≤ C log²(2+L)`.
* `truncatedMark_second_moment`, **display (42), first half**:
  `E|Z^{(ε)}_{n,j}|² ≤ CεL`, uniformly in `n` and `j`.
* `gaussIter_mul_succ_le_half` … `stoppingTime_le_log`, a **Lamé bound**:
  `x_j x_{j+1} ≤ 1/2` gives `N_{j+2} ≤ N_j/2`, hence
  `τ_n ≤ 2 log n / log 2 + 2` for *every* irrational `α ∈ (0,1)`.  This is
  what makes "the diagonal contribution is `O(εL²)`" legitimate.
* `stoppingTime_tail_input`, `bulkTerm_sq_le_prob`, `bulk_window_input` -
  the diagonal is carried by `O(L)` levels, each contributing `≤ Cε/L`.
* `sum_split_diag`, `diagonal_le_second_moment`, `bulkTerm_sq_integral_le`,
  and `truncatedBulkSum_centered_L2` itself, the assembly, with effective
  constant `C = κ·C₂ + 2`.

## The one sorried input, and the precise obstruction

`bulk_offdiagonal_input`, **Proposition 4.1**.  The off-diagonal
covariances of (41) sum to `o(L²)`.  Overlapping, `H`-near and
resonance-near pairs number `O(LH)` and, by the second half of (42),
contribute `O(LH log²L) = o(L²)`; for the remaining pairs one cuts each
digit at `A_L = L^D` (`D > 2`), applies Jackson approximation to the
Lipschitz truncation, and then Proposition 4.1.  Prop 4.1 is only *stated*
in this development: `Kwon1002.prop_4_1_marked_factorization` of
`Kwon1002/Section4.lean` is `sorry`-proved, as is the pair count
`Kwon1002.nonGood_tuple_count`.

Sorried results relied on as inputs: only that one.  `digit_tail_product`
(Lem 3.1(ii)) is **proved** in `Kwon1002/DigitTail.lean` and is a genuine
input here; `shrinking_anti_concentration` (Lem 3.3) is not needed.

## Two notes on the manuscript

1. The proof of Lemma 5.2 passes from `E|U^{(ε)}_{n,j}|² ≤ CεL` (42) to
   "the diagonal contribution is `O(εL²)`", which needs `#J_n = O(L)`.
   In the manuscript that is Lemma 7.1 (60), `τ_n = L/λ + O_P(H)`, a §7
   result, so §5 has a forward reference to §7.  The dependency is benign
   and is removed here: `stoppingTime_le_log` gives the required `O(L)`
   *deterministically*, from `x_j x_{j+1} ≤ 1/2` alone.
2. `truncatedMark` (the shared file's `Z^{(ε)}`) is the **hard** truncation
   `Z·1{Z ≤ εL}`, whereas (40) uses the smooth
   `U^{(ε)}_{n,j} = (−1)^j Z χ(Z/(εL))`.  Everything proved here is
   insensitive to both differences, the sign squares away and `M = εL`
   replaces `M = 2εL`.  The smooth `χ` is needed only for the Jackson step
   inside the sorried input, as already recorded in `SmallJumps.lean`.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Kwon1002

namespace L2Estimate

noncomputable section

/-! ### A layer-cake second-moment bound -/

/-- If `0 ≤ f ≤ M` and the tail of `f` obeys `ν{f > t} ≤ K/(1+t)`, then
`∫ f² ≤ 2KM`.  This is the layer-cake step of display (42): the `1/(1+t)`
tail is exactly integrable against `2t dt` on `[0,M]`, with no logarithm. -/
theorem integral_sq_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {f : Ω → ℝ} (hmeas : Measurable f) (hnn : ∀ ω, 0 ≤ f ω)
    {M K : ℝ} (hM : 0 ≤ M) (hfM : ∀ ω, f ω ≤ M) (hK : 0 ≤ K)
    (htail : ∀ t : ℝ, 0 < t → (ν {ω | t < f ω}).toReal ≤ K / (1 + t)) :
    ∫ ω, (f ω) ^ 2 ∂ν ≤ 2 * K * M := by
  have hKM : (0 : ℝ) ≤ 2 * K * M := mul_nonneg (by linarith) hM
  have hg : ∀ x : ℝ, (∫ t in (0:ℝ)..x, 2 * t) = x ^ 2 := by
    intro x
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have key := lintegral_comp_eq_lintegral_meas_lt_mul (f := f) (g := fun t : ℝ => 2 * t) ν
      (Eventually.of_forall hnn) hmeas.aemeasurable
      (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : (0:ℝ) < t := ht
        linarith)
  have hbound : (∫⁻ t in Ioi (0:ℝ), ν {a | t < f a} * ENNReal.ofReal (2 * t))
      ≤ ENNReal.ofReal (2 * K * M) := by
    have hstep : (∫⁻ t in Ioi (0:ℝ), ν {a | t < f a} * ENNReal.ofReal (2 * t))
        ≤ ∫⁻ t in Ioi (0:ℝ),
            (Ioo (0:ℝ) M).indicator (fun _ => ENNReal.ofReal (2 * K)) t := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      by_cases htM : t < M
      · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht0, htM⟩)]
        have h1 : ν {a | t < f a} ≤ ENNReal.ofReal (K / (1 + t)) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top ν {a | t < f a})]
          exact ENNReal.ofReal_le_ofReal (htail t ht0)
        have h2 : ENNReal.ofReal (K / (1 + t)) * ENNReal.ofReal (2 * t)
            ≤ ENNReal.ofReal (2 * K) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
        exact le_trans (mul_le_mul_right' h1 _) h2
      · have hempty : {a | t < f a} = (∅ : Set Ω) := by
          ext a
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
          exact le_trans (hfM a) (not_lt.mp htM)
        rw [hempty]
        simp
    refine le_trans hstep ?_
    have hset : (volume.restrict (Ioi (0:ℝ))) (Ioo (0:ℝ) M) = ENNReal.ofReal M := by
      rw [Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self, Real.volume_Ioo, sub_zero]
    rw [lintegral_indicator measurableSet_Ioo, setLIntegral_const, hset,
      ← ENNReal.ofReal_mul (by linarith)]
  have hfin : (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂ν) ≤ ENNReal.ofReal (2 * K * M) := by
    have heq : (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂ν)
        = ∫⁻ t in Ioi (0:ℝ), ν {a | t < f a} * ENNReal.ofReal (2 * t) := by
      rw [← key]
      simp only [hg]
    rw [heq]
    exact hbound
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg (f ω))
      ((hmeas.pow_const 2).aestronglyMeasurable)]
  calc (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂ν).toReal
      ≤ (ENNReal.ofReal (2 * K * M)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = 2 * K * M := ENNReal.toReal_ofReal hKM

/-! ### The uniform digit tail of Lemma 5.2 -/

lemma inv_max_le (t : ℝ) (ht : 0 < t) : (max (8 * t) 1)⁻¹ ≤ 2 / (1 + t) := by
  rcases le_or_gt (8 * t) 1 with h | h
  · rw [max_eq_right h, inv_one, le_div_iff₀ (by linarith : (0:ℝ) < 1 + t)]
    linarith
  · rw [max_eq_left h.le, inv_eq_one_div,
      div_le_div_iff₀ (by linarith : (0:ℝ) < 8 * t) (by linarith : (0:ℝ) < 1 + t)]
    linarith

lemma truncatedMark_le_mark (ε α : ℝ) (n j : ℕ) : truncatedMark ε α n j ≤ mark α n j := by
  unfold truncatedMark
  split_ifs with h
  · exact le_rfl
  · exact mark_nonneg α n j

lemma volume_ne_top_of_subset_Ioo {S : Set ℝ} (hS : S ⊆ Ioo (0:ℝ) 1) : volume S ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono hS)
  rw [Real.volume_Ioo]
  simp

/-- `W ≤ 1/8` (`mark_le_digit_div_eight`) turns `Z_{n,j} > t` into
`a_{j+1} ≥ max(8t, 1)`; the second alternative is free because a positive
mark forces a positive digit. -/
lemma max_le_digit_of_lt_mark {α : ℝ} {n j : ℕ} {t : ℝ} (ht : 0 < t)
    (h : t < mark α n j) : max (8 * t) 1 ≤ ((digit α j : ℕ) : ℝ) := by
  have h8 : (8:ℝ) * t < (digit α j : ℝ) := by
    have := mark_le_digit_div_eight α n j
    linarith
  have hdpos : (0:ℝ) < (digit α j : ℝ) := lt_trans (by linarith : (0:ℝ) < 8 * t) h8
  have hd1 : (1:ℝ) ≤ ((digit α j : ℕ) : ℝ) := by
    have hne : digit α j ≠ 0 := by
      intro hz
      rw [hz] at hdpos
      simp at hdpos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  exact max_le h8.le hd1

/-- **The uniform tail of the level mark**, the input the manuscript proof of
Lemma 5.2 opens with.  `W ≤ 1/8` turns `Z_{n,j} > t` into `a_{j+1} > 8t`, and
Lemma 3.1(ii) (display (15), `digit_tail_product`) bounds the latter. -/
theorem mark_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n j : ℕ) (t : ℝ), 0 < t →
      (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ t < mark α n j}).toReal ≤ C / (1 + t) := by
  obtain ⟨C₀, hC₀, hprod⟩ := digit_tail_product
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro n j t ht
  have hinj : Function.Injective (fun _ : Fin 1 => j) := fun a b _ => Subsingleton.elim a b
  have hA : ∀ _i : Fin 1, (1:ℝ) ≤ max (8 * t) 1 := fun _ => le_max_right _ _
  have hspec := hprod 1 (fun _ : Fin 1 => j) (fun _ : Fin 1 => max (8 * t) 1) hinj hA
  have hmono : (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ t < mark α n j}).toReal
      ≤ (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧
          ∀ _i : Fin 1, max (8 * t) 1 ≤ ((digit α j : ℕ) : ℝ)}).toReal := by
    refine ENNReal.toReal_mono (volume_ne_top_of_subset_Ioo (fun α hα => hα.1))
      (measure_mono ?_)
    rintro α ⟨hα, hmk⟩
    exact ⟨hα, fun _ => max_le_digit_of_lt_mark ht hmk⟩
  refine le_trans hmono (le_trans hspec ?_)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  calc C₀ * (max (8 * t) 1)⁻¹ ≤ C₀ * (2 / (1 + t)) :=
        mul_le_mul_of_nonneg_left (inv_max_le t ht) hC₀.le
    _ = 2 * C₀ / (1 + t) := by ring

/-- **The joint tail at two distinct levels**, the second tail input of the
proof of Lemma 5.2: for `j ≠ k`,
`P(Z_{n,j} > s, Z_{n,k} > t) ≤ C/((1+s)(1+t))`.  This is display (15) with
`s = 2`; it is what feeds the second half of (42),
`E|U_j U_k| ≤ C log²(2+L)`. -/
theorem mark_joint_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n j k : ℕ), j ≠ k → ∀ (s t : ℝ), 0 < s → 0 < t →
      (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ s < mark α n j ∧ t < mark α n k}).toReal
        ≤ C / ((1 + s) * (1 + t)) := by
  obtain ⟨C₀, hC₀, hprod⟩ := digit_tail_product
  refine ⟨4 * C₀ ^ 2, by positivity, ?_⟩
  intro n j k hjk s t hs ht
  have hs1 : (0:ℝ) < 1 + s := by linarith
  have ht1 : (0:ℝ) < 1 + t := by linarith
  have hinj : Function.Injective (![j, k] : Fin 2 → ℕ) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hA : ∀ i : Fin 2, (1:ℝ) ≤ (![max (8 * s) 1, max (8 * t) 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> simp
  have hspec := hprod 2 ![j, k] ![max (8 * s) 1, max (8 * t) 1] hinj hA
  have hmono : (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ s < mark α n j ∧ t < mark α n k}).toReal
      ≤ (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧
          ∀ i : Fin 2, (![max (8 * s) 1, max (8 * t) 1] : Fin 2 → ℝ) i
            ≤ ((digit α ((![j, k] : Fin 2 → ℕ) i) : ℕ) : ℝ)}).toReal := by
    refine ENNReal.toReal_mono (volume_ne_top_of_subset_Ioo (fun α hα => hα.1))
      (measure_mono ?_)
    rintro α ⟨hα, hj, hk⟩
    refine ⟨hα, fun i => ?_⟩
    fin_cases i
    · simpa using max_le_digit_of_lt_mark hs hj
    · simpa using max_le_digit_of_lt_mark ht hk
  refine le_trans hmono (le_trans hspec ?_)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hbs := inv_max_le s hs
  have hbt := inv_max_le t ht
  have hmul : (max (8 * s) 1)⁻¹ * (max (8 * t) 1)⁻¹ ≤ (2 / (1 + s)) * (2 / (1 + t)) :=
    mul_le_mul hbs hbt (by positivity) (by positivity)
  calc C₀ ^ 2 * ((max (8 * s) 1)⁻¹ * (max (8 * t) 1)⁻¹)
      ≤ C₀ ^ 2 * ((2 / (1 + s)) * (2 / (1 + t))) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = 4 * C₀ ^ 2 / ((1 + s) * (1 + t)) := by field_simp; ring

/-- **Display (42), first half**: `E|Z^{(ε)}_{n,j}|² ≤ CεL`, uniformly in `n`
and `j`.  Layer-cake integration of the uniform tail. -/
theorem truncatedMark_second_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 ≤ ε → ∀ (n j : ℕ),
      (∫ α in Ioo (0:ℝ) 1, (truncatedMark ε α n j) ^ 2) ≤ C * ε * Lnorm n := by
  obtain ⟨K, hK, htail⟩ := mark_tail_bound
  refine ⟨2 * K, by linarith, ?_⟩
  intro ε hε n j
  haveI := isProbabilityMeasure_restrict_Ioo
  have hMnn : (0:ℝ) ≤ ε * Lnorm n := mul_nonneg hε (Lnorm_nonneg n)
  have hmain := integral_sq_le_of_tail (volume.restrict (Ioo (0:ℝ) 1))
      (measurable_truncatedMark ε n j) (fun α => truncatedMark_nonneg ε α n j)
      (M := ε * Lnorm n) (K := K) hMnn (fun α => truncatedMark_le ε hε α n j) hK.le ?_
  · calc (∫ α in Ioo (0:ℝ) 1, (truncatedMark ε α n j) ^ 2)
        ≤ 2 * K * (ε * Lnorm n) := hmain
      _ = 2 * K * ε * Lnorm n := by ring
  · intro t ht
    have hms : MeasurableSet {α : ℝ | t < truncatedMark ε α n j} :=
      measurableSet_lt measurable_const (measurable_truncatedMark ε n j)
    rw [Measure.restrict_apply hms]
    have hsub : {α : ℝ | t < truncatedMark ε α n j} ∩ Ioo (0:ℝ) 1
        ⊆ {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ t < mark α n j} := by
      rintro α ⟨h1, h2⟩
      exact ⟨h2, lt_of_lt_of_le h1 (truncatedMark_le_mark ε α n j)⟩
    exact le_trans (ENNReal.toReal_mono
      (volume_ne_top_of_subset_Ioo (fun α hα => hα.1)) (measure_mono hsub)) (htail n j t ht)

/-! ### A Lamé bound for the stopping time

`τ_n = O(log n)` *deterministically*, which is all the diagonal of (41)
needs, the manuscript gets the same information from Lem 7.1 (60), a §7
result, so this replaces a forward reference by an elementary argument. -/

/-- `x_j x_{j+1} ≤ 1/2`: the two-step contraction of the Gauss map.  If
`a_{j+1} ≥ 2` then `x_j < 1/2`; if `a_{j+1} = 1` then
`x_j x_{j+1} = 1 - x_j < 1/2`. -/
lemma gaussIter_mul_succ_le_half {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α)
    (j : ℕ) : gaussIter α j * gaussIter α (j + 1) ≤ 1 / 2 := by
  have hj := gaussIter_mem_Ioo hα hirr j
  have hj1 := gaussIter_mem_Ioo hα hirr (j + 1)
  have hsplit := inv_gaussIter_eq hα hirr j
  have hd1 : 1 ≤ digit α j := one_le_digit hα hirr j
  rcases le_or_gt 2 (digit α j) with h2 | h2
  · have hd2 : (2:ℝ) ≤ (digit α j : ℝ) := by exact_mod_cast h2
    have hinv : (2:ℝ) < (gaussIter α j)⁻¹ := by
      rw [hsplit]; linarith [hj1.1]
    have hxj : 2 * gaussIter α j < 1 := by
      have h := mul_lt_mul_of_pos_right hinv hj.1
      rwa [inv_mul_cancel₀ (ne_of_gt hj.1)] at h
    nlinarith [hj.1, hj1.1, hj1.2]
  · have hdeq : digit α j = 1 := by omega
    have hinv : (gaussIter α j)⁻¹ = 1 + gaussIter α (j + 1) := by
      rw [hsplit, hdeq]; norm_num
    have hkey : gaussIter α j * (1 + gaussIter α (j + 1)) = 1 := by
      rw [← hinv, mul_inv_cancel₀ (ne_of_gt hj.1)]
    nlinarith [hkey, hj.1, hj1.2, mul_lt_mul_of_pos_left hj1.2 hj.1]

lemma heightSeq_succ_le_mul (α : ℝ) (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α)
    (n j : ℕ) :
    ((heightSeq α n (j + 1) : ℕ) : ℝ) ≤ ((heightSeq α n j : ℕ) : ℝ) * gaussIter α j := by
  have hx := (gaussIter_mem_Ioo hα hirr j).1
  have hnn : (0:ℝ) ≤ ((heightSeq α n j : ℕ) : ℝ) * gaussIter α j :=
    mul_nonneg (Nat.cast_nonneg _) hx.le
  have hfl : (0:ℤ) ≤ ⌊((heightSeq α n j : ℕ) : ℝ) * gaussIter α j⌋ :=
    Int.floor_nonneg.mpr hnn
  have hcast : ((⌊((heightSeq α n j : ℕ) : ℝ) * gaussIter α j⌋.toNat : ℕ) : ℝ)
      = ((⌊((heightSeq α n j : ℕ) : ℝ) * gaussIter α j⌋ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) (Int.toNat_of_nonneg hfl)
  rw [heightSeq_succ_eq, hcast]
  exact Int.floor_le _

lemma heightSeq_two_step (α : ℝ) (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α)
    (n j : ℕ) :
    ((heightSeq α n (j + 2) : ℕ) : ℝ) ≤ ((heightSeq α n j : ℕ) : ℝ) / 2 := by
  have h1 := heightSeq_succ_le_mul α hα hirr n (j + 1)
  have h2 := heightSeq_succ_le_mul α hα hirr n j
  have hx1 := (gaussIter_mem_Ioo hα hirr (j + 1)).1
  have hcontr := gaussIter_mul_succ_le_half hα hirr j
  have hNnn : (0:ℝ) ≤ ((heightSeq α n j : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [h1, h2, hx1, hcontr, hNnn]

lemma heightSeq_pow_bound (α : ℝ) (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α)
    (n m : ℕ) : ((heightSeq α n (2 * m) : ℕ) : ℝ) ≤ (n : ℝ) / 2 ^ m := by
  induction m with
  | zero => simp [heightSeq_zero_eq]
  | succ m ih =>
      have hstep := heightSeq_two_step α hα hirr n (2 * m)
      have heq : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [heq]
      have hpow : (0:ℝ) < 2 ^ m := by positivity
      calc ((heightSeq α n (2 * m + 2) : ℕ) : ℝ)
          ≤ ((heightSeq α n (2 * m) : ℕ) : ℝ) / 2 := hstep
        _ ≤ ((n : ℝ) / 2 ^ m) / 2 := by linarith
        _ = (n : ℝ) / 2 ^ (m + 1) := by rw [pow_succ]; ring

lemma stoppingTime_le_two_mul (α : ℝ) (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α)
    (n m : ℕ) (h : (n : ℝ) < 2 ^ m) : stoppingTime α n ≤ 2 * m := by
  have hpow : (0:ℝ) < 2 ^ m := by positivity
  have hb := heightSeq_pow_bound α hα hirr n m
  have hlt : ((heightSeq α n (2 * m) : ℕ) : ℝ) < 1 := by
    have : (n : ℝ) / 2 ^ m < 1 := (div_lt_one hpow).mpr h
    linarith
  have hz : heightSeq α n (2 * m) = 0 := by
    have : heightSeq α n (2 * m) < 1 := by exact_mod_cast hlt
    omega
  exact Nat.sInf_le hz

/-- **Lamé bound**: `τ_n ≤ 2L/log 2 + 2` for every irrational `α ∈ (0,1)`.
Deterministic, so no §7 input is needed for the diagonal of (41). -/
theorem stoppingTime_le_log (α : ℝ) (hα : α ∈ Ioo (0:ℝ) 1) (hirr : Irrational α)
    (n : ℕ) (hn : 1 ≤ n) :
    ((stoppingTime α n : ℕ) : ℝ) ≤ 2 * Lnorm n / Real.log 2 + 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hLnn : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hq : (0:ℝ) ≤ Real.log (n:ℝ) / Real.log 2 := by positivity
  set m : ℕ := ⌊Real.log (n:ℝ) / Real.log 2⌋₊ + 1 with hm
  have hmlt : Real.log (n:ℝ) / Real.log 2 < (m:ℝ) := by
    have h := Nat.lt_floor_add_one (Real.log (n:ℝ) / Real.log 2)
    rw [hm]
    push_cast
    exact h
  have hmle : (m:ℝ) ≤ Real.log (n:ℝ) / Real.log 2 + 1 := by
    have h := Nat.floor_le hq
    rw [hm]
    push_cast
    linarith
  have hpow : (n:ℝ) < 2 ^ m := by
    have h1 : Real.log (n:ℝ) < (m:ℝ) * Real.log 2 := by
      rw [div_lt_iff₀ hlog2] at hmlt
      linarith
    have h2 : Real.log ((2:ℝ) ^ m) = (m:ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    have h3 : Real.exp (Real.log (n:ℝ)) < Real.exp ((m:ℝ) * Real.log 2) :=
      Real.exp_lt_exp.mpr h1
    rwa [Real.exp_log hnpos, ← h2, Real.exp_log (by positivity)] at h3
  have hst := stoppingTime_le_two_mul α hα hirr n m hpow
  have hstR : ((stoppingTime α n : ℕ) : ℝ) ≤ 2 * (m:ℝ) := by exact_mod_cast hst
  unfold Lnorm
  have : 2 * (Real.log (n:ℝ) / Real.log 2) = 2 * Real.log (n:ℝ) / Real.log 2 := by ring
  linarith

/-! ### The diagonal -/

/-- The first-moment tail of the stopping time, `∑_{j ≥ κL} P(τ_n > j) ≤ 1`
for `κ = 2/log 2 + 2`.  The manuscript would get this from Lemma 7.1 (60);
here the Lamé bound makes every summand *identically* zero (off the
rationals), so no §7 input is needed. -/
theorem stoppingTime_tail_input :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1),
          (if κ * Lnorm n ≤ (j : ℝ) then
            (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n}).toReal
          else 0) ≤ 1 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 / Real.log 2 + 2, by positivity, 3, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hL1 : (1:ℝ) ≤ Lnorm n := by
    unfold Lnorm
    have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hexp : Real.exp 1 < (n:ℝ) := by
      have h := Real.exp_one_lt_d9
      linarith
    exact le_of_lt ((Real.lt_log_iff_exp_lt (by linarith : (0:ℝ) < (n:ℝ))).mpr hexp)
  refine le_of_eq_of_le (Finset.sum_eq_zero fun j _ => ?_) zero_le_one
  split_ifs with hj
  · -- on this range the event is contained in the rationals
    have hnull : volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n} = 0 := by
      refine measure_mono_null (fun α hα => ?_)
        ((Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume)
      by_contra hcon
      have hirr : Irrational α := by
        simpa [Irrational] using hcon
      have hle := stoppingTime_le_log α hα.1 hirr n hn1
      have hjR : ((j:ℕ) : ℝ) < ((stoppingTime α n : ℕ) : ℝ) := by exact_mod_cast hα.2
      have hkey : 2 * Lnorm n / Real.log 2 + 2 ≤ (j : ℝ) := by
        have hexp : (2 / Real.log 2 + 2) * Lnorm n
            = 2 * Lnorm n / Real.log 2 + 2 * Lnorm n := by
          field_simp
        rw [hexp] at hj
        linarith
      linarith
    rw [hnull]
    simp
  · rfl

/-- A single bulk level contributes at most `ε²` times the probability that
the stopping time has not yet fired: `g_j` vanishes off `{j < τ_n}` and is
bounded by `ε`. -/
lemma bulkTerm_sq_le_prob (c ε : ℝ) (hε : 0 < ε) (n j : ℕ) :
    (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2)
      ≤ ε ^ 2 * (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n}).toReal := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hTm : MeasurableSet {α : ℝ | j < stoppingTime α n} :=
    measurable_stoppingTime n trivial
  have hε2 : (0:ℝ) ≤ ε ^ 2 := by positivity
  have hsrc : Integrable (fun α : ℝ => (bulkTerm c ε α n j) ^ 2)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    refine integrable_of_bound ((measurable_bulkTerm c ε n j).pow_const 2) (M := ε ^ 2) ?_
    intro α
    have h := abs_bulkTerm_le c ε hε.le α n j
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hind : Integrable
      (fun α : ℝ => {β : ℝ | j < stoppingTime β n}.indicator (fun _ => ε ^ 2) α)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    refine integrable_of_bound (measurable_const.indicator hTm) (M := ε ^ 2) ?_
    intro α
    by_cases h : α ∈ {β : ℝ | j < stoppingTime β n}
    · rw [Set.indicator_of_mem h, abs_of_nonneg hε2]
    · rw [Set.indicator_of_notMem h, abs_zero]
      exact hε2
  have hpt : ∀ α : ℝ, (bulkTerm c ε α n j) ^ 2
      ≤ {β : ℝ | j < stoppingTime β n}.indicator (fun _ => ε ^ 2) α := by
    intro α
    by_cases h : j ∈ bulkIndices c α n
    · have hmem : α ∈ {β : ℝ | j < stoppingTime β n} :=
        Finset.mem_range.mp (Finset.mem_of_mem_filter j h)
      rw [Set.indicator_of_mem hmem]
      have hb := pow_le_pow_left₀ (abs_nonneg (bulkTerm c ε α n j))
        (abs_bulkTerm_le c ε hε.le α n j) 2
      rwa [sq_abs] at hb
    · simp only [bulkTerm, if_neg h]
      have hnn : (0:ℝ) ≤ {β : ℝ | j < stoppingTime β n}.indicator (fun _ => ε ^ 2) α :=
        Set.indicator_nonneg (fun _ _ => hε2) α
      simpa using hnn
  calc (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2)
      ≤ ∫ α in Ioo (0:ℝ) 1,
          {β : ℝ | j < stoppingTime β n}.indicator (fun _ => ε ^ 2) α :=
        integral_mono hsrc hind hpt
    _ = ε ^ 2 * (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n}).toReal := by
        rw [integral_indicator hTm, setIntegral_const, smul_eq_mul, measureReal_def,
          Measure.restrict_apply hTm]
        have hset : {β : ℝ | j < stoppingTime β n} ∩ Ioo (0:ℝ) 1
            = {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n} := by
          ext α
          simp [and_comm]
        rw [hset]
        ring

/-- **The bulk window**, now *proved* from the stopping-time tail: all but
`O(L)` levels together contribute at most `ε` to the diagonal. -/
theorem bulk_window_input (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset ℕ, S ⊆ Finset.range (n + 1) ∧ (S.card : ℝ) ≤ κ * Lnorm n ∧
        ∑ j ∈ Finset.range (n + 1) \ S,
            (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2) ≤ ε := by
  classical
  obtain ⟨κ, hκ, N₀, hN₀⟩ := stoppingTime_tail_input
  refine ⟨κ + 2, by linarith, ?_⟩
  intro ε hε hε1
  refine ⟨max N₀ 3, fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL1 : (1:ℝ) ≤ Lnorm n := by
    unfold Lnorm
    have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    have hexp : Real.exp 1 < (n:ℝ) := by
      have h := Real.exp_one_lt_d9
      linarith
    exact le_of_lt ((Real.lt_log_iff_exp_lt (by linarith : (0:ℝ) < (n:ℝ))).mpr hexp)
  have hKLnn : (0:ℝ) ≤ κ * Lnorm n := mul_nonneg hκ.le (by linarith)
  set p : ℕ → Prop := fun j => κ * Lnorm n ≤ (j : ℝ) with hp
  refine ⟨(Finset.range (n + 1)).filter (fun j => ¬ p j), Finset.filter_subset _ _, ?_, ?_⟩
  · have hsub : (Finset.range (n + 1)).filter (fun j => ¬ p j)
        ⊆ Finset.range ⌈κ * Lnorm n⌉₊ := by
      intro j hj
      have hjp : ¬ p j := (Finset.mem_filter.mp hj).2
      have hlt : (j : ℝ) < κ * Lnorm n := lt_of_not_ge hjp
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr hlt)
    have hcard : (((Finset.range (n + 1)).filter (fun j => ¬ p j)).card : ℝ)
        ≤ (⌈κ * Lnorm n⌉₊ : ℝ) := by
      have h := Finset.card_le_card hsub
      rw [Finset.card_range] at h
      exact_mod_cast h
    have hceil : (⌈κ * Lnorm n⌉₊ : ℝ) < κ * Lnorm n + 1 := Nat.ceil_lt_add_one hKLnn
    linarith
  · have hsdiff : Finset.range (n + 1) \ (Finset.range (n + 1)).filter (fun j => ¬ p j)
        = (Finset.range (n + 1)).filter p := by
      rw [Finset.filter_not, Finset.sdiff_sdiff_eq_self (Finset.filter_subset _ _)]
    rw [hsdiff]
    have hstep : ∑ j ∈ (Finset.range (n + 1)).filter p,
        (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2)
        ≤ ∑ j ∈ (Finset.range (n + 1)).filter p,
            ε ^ 2 * (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n}).toReal :=
      Finset.sum_le_sum fun j _ => bulkTerm_sq_le_prob c ε hε n j
    have hsum : ∑ j ∈ (Finset.range (n + 1)).filter p,
        (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n}).toReal ≤ 1 := by
      rw [Finset.sum_filter]
      exact hN₀ n hn0
    have hε2 : (0:ℝ) ≤ ε ^ 2 := by positivity
    calc ∑ j ∈ (Finset.range (n + 1)).filter p,
          (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2)
        ≤ ∑ j ∈ (Finset.range (n + 1)).filter p,
            ε ^ 2 * (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n}).toReal :=
          hstep
      _ = ε ^ 2 * ∑ j ∈ (Finset.range (n + 1)).filter p,
            (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ j < stoppingTime α n}).toReal := by
          rw [Finset.mul_sum]
      _ ≤ ε ^ 2 * 1 := mul_le_mul_of_nonneg_left hsum hε2
      _ ≤ ε := by nlinarith

/-- **Remaining input (E)**, the off-diagonal covariances of (41).

Overlapping, `H`-near and resonance-near pairs number `O(LH)` and, by the
second half of (42) (`E|U_j U_k| ≤ C log²(2+L)`, which follows from the joint
tail `mark_joint_tail_bound` above), contribute `O(LH log²L) = o(L²)`; for the
remaining pairs one cuts each digit at `A_L = L^D` with `D > 2`, applies
Jackson approximation to the truncated summand, and then Proposition 4.1.

Not provable here: Proposition 4.1 is a §4 target that is only *stated*
(sorried) in `Kwon1002/Section4.lean`. -/
theorem bulk_offdiagonal_input (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            ∫ α in Ioo (0:ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k) ≤ ε := by
  sorry

/-! ### Assembly -/

lemma sum_split_diag (m : ℕ) (I : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, I j k)
      = (∑ j ∈ Finset.range m, I j j)
        + ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, (if j = k then 0 else I j k) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hpt : ∀ k ∈ Finset.range m,
      I j k = (if j = k then I j k else 0) + (if j = k then 0 else I j k) := by
    intro k _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp [hj]

/-- Variance is bounded by the second moment. -/
lemma diagonal_le_second_moment (c ε : ℝ) (hε : 0 < ε) (n j : ℕ) :
    (∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ ∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2 := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hmb : Measurable fun α : ℝ => bulkTerm c ε α n j := measurable_bulkTerm c ε n j
  have hIf : Integrable (fun α : ℝ => bulkTerm c ε α n j)
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    integrable_of_bound hmb (fun α => abs_bulkTerm_le c ε hε.le α n j)
  have hIsq : Integrable (fun α : ℝ => (bulkTerm c ε α n j - 0) ^ 2)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    refine integrable_of_bound ((hmb.sub measurable_const).pow_const 2) (M := ε ^ 2) ?_
    intro α
    have h := abs_bulkTerm_le c ε hε.le α n j
    rw [sub_zero, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h1 := integral_sub_mean_sq_le hIf 0 hIsq
  have hrw : (∫ α in Ioo (0:ℝ) 1,
      bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      = ∫ α in Ioo (0:ℝ) 1,
          (bulkTerm c ε α n j - ∫ β in Ioo (0:ℝ) 1, bulkTerm c ε β n j) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    simp only [bulkTermCentered]
    ring
  have hrw2 : (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j - 0) ^ 2)
      = ∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    simp only [sub_zero]
  rw [hrw, ← hrw2]
  exact h1

/-- Each diagonal second moment is `≤ Cε/L`: `(42)` divided by `L²`. -/
lemma bulkTerm_sq_integral_le (c ε : ℝ) (hε : 0 < ε) (n j : ℕ) (hL : 0 < Lnorm n)
    (C₂ : ℝ)
    (hC₂ : (∫ α in Ioo (0:ℝ) 1, (truncatedMark ε α n j) ^ 2) ≤ C₂ * ε * Lnorm n) :
    (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2) ≤ C₂ * ε / Lnorm n := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hmb : Measurable fun α : ℝ => bulkTerm c ε α n j := measurable_bulkTerm c ε n j
  have hsrc : Integrable (fun α : ℝ => (bulkTerm c ε α n j) ^ 2)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    refine integrable_of_bound (hmb.pow_const 2) (M := ε ^ 2) ?_
    intro α
    have h := abs_bulkTerm_le c ε hε.le α n j
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hdom : Integrable (fun α : ℝ => (truncatedMark ε α n j / Lnorm n) ^ 2)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    refine integrable_of_bound
      (((measurable_truncatedMark ε n j).div measurable_const).pow_const 2) (M := ε ^ 2) ?_
    intro α
    have h0 := truncatedMark_div_nonneg ε α n j
    have h1' := truncatedMark_div_le ε hε.le α n j
    rw [abs_pow, abs_of_nonneg h0]
    exact pow_le_pow_left₀ h0 h1' 2
  have hle : (∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2)
      ≤ ∫ α in Ioo (0:ℝ) 1, (truncatedMark ε α n j / Lnorm n) ^ 2 := by
    refine integral_mono hsrc hdom (fun α => ?_)
    simp only [bulkTerm]
    split_ifs with h
    · exact le_rfl
    · simpa using sq_nonneg (truncatedMark ε α n j / Lnorm n)
  refine le_trans hle ?_
  have hdiv : (∫ α in Ioo (0:ℝ) 1, (truncatedMark ε α n j / Lnorm n) ^ 2)
      = (∫ α in Ioo (0:ℝ) 1, (truncatedMark ε α n j) ^ 2) / (Lnorm n) ^ 2 := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    simp only [div_pow]
  rw [hdiv, div_le_div_iff₀ (by positivity : (0:ℝ) < (Lnorm n) ^ 2) hL]
  nlinarith [mul_le_mul_of_nonneg_right hC₂ hL.le]

/-- **The target**: `Kwon1002.truncatedBulkSum_centered_L2`, reproduced
verbatim.  The diagonal is proved; the off-diagonal is the one sorried
input `bulk_offdiagonal_input` (Proposition 4.1). -/
theorem truncatedBulkSum_centered_L2 (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ b : ℝ,
        (∫ α in Ioo (0 : ℝ) 1,
            (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
          ≤ C * ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C₂, hC₂, hsm⟩ := truncatedMark_second_moment
  obtain ⟨κ, hκ, hwin⟩ := bulk_window_input c
  refine ⟨κ * C₂ + 2, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hwin ε hε hε1
  obtain ⟨N₂, hN₂⟩ := bulk_offdiagonal_input c ε hε hε1
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨S, hSsub, hScard, hStail⟩ := hN₁ n hn1
  refine ⟨∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0:ℝ) 1, bulkTerm c ε β n j, ?_⟩
  rw [integral_centered_eq, centered_second_moment_expand c ε hε.le n]
  refine le_trans (le_of_eq (sum_split_diag (n + 1) (fun j k =>
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k))) ?_
  have hoff := hN₂ n hn2
  -- diagonal
  have hdiagterm : ∀ j : ℕ,
      (∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2 :=
    fun j => diagonal_le_second_moment c ε hε n j
  have hSbound : (∑ j ∈ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε := by
    calc (∑ j ∈ S,
        ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∑ _j ∈ S, (C₂ * ε / Lnorm n) := by
          refine Finset.sum_le_sum fun j _ => le_trans (hdiagterm j) ?_
          exact bulkTerm_sq_integral_le c ε hε n j hL C₂ (hsm ε hε.le n j)
      _ = (S.card : ℝ) * (C₂ * ε / Lnorm n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (κ * Lnorm n) * (C₂ * ε / Lnorm n) := by
          refine mul_le_mul_of_nonneg_right hScard ?_
          have : (0:ℝ) ≤ C₂ * ε := by positivity
          positivity
      _ = κ * C₂ * ε := by field_simp
  have hRestBound : (∑ j ∈ Finset.range (n + 1) \ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ ε :=
    le_trans (Finset.sum_le_sum fun j _ => hdiagterm j) hStail
  have hdiag : (∑ j ∈ Finset.range (n + 1),
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε + ε := by
    rw [← Finset.sum_sdiff hSsub]
    linarith [hSbound, hRestBound]
  have hfinal : κ * C₂ * ε + ε + ε ≤ (κ * C₂ + 2) * ε := le_of_eq (by ring)
  linarith [hdiag, hoff, hfinal]

end

end L2Estimate

end Kwon1002


