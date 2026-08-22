import Kwon1002.DetPairJoin
import Kwon1002.MultiLevel
import Kwon1002.MonomialCore

/-!
# The three joins: §5's last open input, closed

`Kwon1002/DetPairJoin.lean` reduced `Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp`
— §5's last open input — to a **joint-tail transfer at two levels**: outside
`O(L·H)` pairs, at every pair of levels `j, k ∈ J_n` and every pair of
thresholds `s, t`,

  `|P(Z^{(ε)}_{n,j} > s, Z^{(ε)}_{n,k} > t)
      − P(Z^{(ε)}_{n,j} > s)·P(Z^{(ε)}_{n,k} > t)| ≤ δ/L⁴`.

That hypothesis is discharged here, from three theorems already in the tree,
by the three joins the reduction named.  No new mathematics is introduced.

## Join 1 — the tail indicator is a section indicator

`tailInd_truncatedMark_eq_indFull`.  For a **nonnegative** threshold `s`,

  `1{Z^{(ε)}_{n,j} > s} = indFull (truncSection L (s/L) ε) (a_j, θ_j)`,

because `Z^{(ε)}_{n,j} = a_j·W(θ_j)·1{a_j·W(θ_j) ≤ εL}`, so `Z^{(ε)}_{n,j} > s`
is `a_j·W(θ_j) ∈ (s, εL]`, which is the `θ`-section
`Kwon1002.Section5Join.truncSection` at the window `(s/L, ε]` — and
`Kwon1002.Section5Join.isUnionOfIntervals_truncSection` puts it in the interval
class at `m = 2`, uniformly in the digit and in the threshold.

For a **negative** threshold the indicator is identically `1`
(`tailInd_truncatedMark_of_neg`, since the truncated mark is nonnegative), and
the covariance is then exactly `0`.  This is the only place where the "for all
`s, t : ℝ`" of the residual reaches outside the section family, and it is
degenerate; the layer-cake conversion of `Kwon1002/PairLayerCake.lean` in fact
only ever calls positive thresholds.

## Join 2 — from a far, non-resonant pair to a good `2`-tuple

`goodTuple_pair`.  `Kwon1002.GoodTuple n 2` at the pair `(j, k)` asks for
displays (25) and (26) at `r = 2`: `200H ≤ k − j` and
`200H ≤ |k − (m_n + j)/2|`.  The pairs of `J_n` failing either are counted at
`O(L·H)` by `Kwon1002.MonomialCore.card_nearDiag_le` and
`Kwon1002.MonomialCore.card_nearRes_le`, so they can be put into the bad set
`R` the residual allows.  `badPairs` is their union, **symmetrised** (the
residual quantifies over ordered pairs in both orders, and the covariance is
symmetric), and `card_badPairs_le` does the arithmetic: `|R| ≤ κ·L·H` with
`κ = 1210·(1/λ + 1)`, out of `MonomialCore.card_bulkJ_le`.

Good `2`-tuples are not vacuous: `MultiLevel.eventually_exists_goodTuple 2`.

## Join 3 — `multiLevel_transfer 2 2` at `A = 5`

`tail_transfer`.  `Kwon1002.MultiLevel.multiLevel_transfer 2 2` gives, at the
free rate `A = 5` and uniformly over good `2`-tuples and over per-level
interval-class families,

  `|∫ ∏_{ℓ<2} 1_{B_ℓ} − ∏_{ℓ<2} stationaryMeanR 1_{B_ℓ}| ≤ C₂·L^{-5}`,

and its `r = 1` case `multiLevel_transfer_one` gives
`|∫ 1_{B} − stationaryMeanR 1_{B}| ≤ C₁·L^{-5}` at each level separately.  The
covariance is the difference of the two, so the triangle inequality with
`|∫ 1_B| ≤ 1` and `|stationaryMeanR 1_B| ≤ 1` yields
`(C₂ + 2C₁)·L^{-5} ≤ δ/L⁴` as soon as `L ≥ (C₂ + 2C₁)/δ`, which is eventual
because `L = log n → ∞`.  The constants do not depend on `ε` or `δ`, which is
why `κ` can be produced before either is introduced.

## What this closes

`bulk_offdiagonal_abs_far_sharp_proved` is
`Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` token for token — the
anonymous `example` at the foot of this file closes the canonical *type* by the
theorem proved here — and `#print axioms` on it reports exactly
`[propext, Classical.choice, Quot.sound]`.

As with the six earlier instances of the import-direction pathology in this
tree, the canonical declaration in `Kwon1002/CorFinal.lean` is **not** edited:
`CorFinal` sits below every module that supplies §4, so its `sorry` can never be
discharged where it stands.  `Kwon1002/TailTransferCauchy.lean` carries this
theorem up to the master theorem in the established way.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace TailTransferJoin

noncomputable section

/-- **Join 1.**  The tail indicator of the `ε`-truncated mark at a nonnegative
threshold `s` is the section indicator of the truncation window `(s, εL]`. -/
lemma tailInd_truncatedMark_eq_indFull (ε s : ℝ) (hs : 0 ≤ s) (n j : ℕ)
    (hL : 0 < Lnorm n) (α : ℝ) :
    PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α
      = Section5Join.indFull (Section5Join.truncSection (Lnorm n) (s / Lnorm n) ε)
          (digit α j) (theta α n j) := by
  classical
  have hcancel : s / Lnorm n * Lnorm n = s := div_mul_cancel₀ s (ne_of_gt hL)
  have hmark : (digit α j : ℝ) * W (theta α n j) = mark α n j := rfl
  have hiff : theta α n j
      ∈ Selberg.perSet (Section5Join.truncSection (Lnorm n) (s / Lnorm n) ε (digit α j))
      ↔ s < truncatedMark ε α n j := by
    rw [Section5Join.mem_perSet_truncSection, hcancel, hmark]
    unfold truncatedMark
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_pos h2]; exact h1
    · intro h
      by_cases hle : mark α n j ≤ ε * Lnorm n
      · rw [if_pos hle] at h; exact ⟨h, hle⟩
      · rw [if_neg hle] at h; linarith
  unfold PairLayerCake.tailInd Section5Join.indFull Selberg.perInd
  by_cases h : s < truncatedMark ε α n j
  · rw [if_pos h, Set.indicator_of_mem (hiff.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun hc => h (hiff.mp hc))]

/-- At a negative threshold the tail indicator of a nonnegative observable is
identically `1`. -/
lemma tailInd_truncatedMark_of_neg (ε s : ℝ) (hs : s < 0) (n j : ℕ) (α : ℝ) :
    PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α = 1 := by
  unfold PairLayerCake.tailInd
  rw [if_pos (lt_of_lt_of_le hs (truncatedMark_nonneg ε α n j))]

/-! ## Join 2: from a far, non-resonant pair to a good `2`-tuple -/

/-- The `2`-tuple carried by an ordered pair. -/
def pairTuple (j k : ℕ) : ℕ → ℕ := fun ℓ => if ℓ = 0 then j else if ℓ = 1 then k else 0

/-- The `1`-tuple carried by a single level. -/
def singleTuple (j : ℕ) : ℕ → ℕ := fun ℓ => if ℓ = 0 then j else 0

lemma goodTuple_one (n j : ℕ) (hj : j ∈ bulkJ n) : GoodTuple n 1 (singleTuple j) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro ℓ hℓ
    unfold singleTuple
    rw [if_neg (by omega)]
  · intro ℓ ℓ' _ hℓ'
    omega
  · intro ℓ hℓ
    interval_cases ℓ
    · simpa [singleTuple] using hj
  · intro ℓ hℓ; omega
  · intro i ℓ _ hℓ; omega

/-- The **symmetrised** exceptional set: pairs that are `200H`-close, or whose
later member is `200H`-close to the resonance time of the earlier one, together
with their swaps. -/
def badPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((MonomialCore.nearDiag n (200 * Hscale n) ∪ MonomialCore.nearRes n (200 * Hscale n))
    ∪ (MonomialCore.nearDiag n (200 * Hscale n)
        ∪ MonomialCore.nearRes n (200 * Hscale n)).image Prod.swap)

lemma badPairs_symm {n j k : ℕ} (h : (j, k) ∉ badPairs n) : (k, j) ∉ badPairs n := by
  classical
  intro hmem
  refine h ?_
  unfold badPairs at hmem ⊢
  rw [Finset.mem_union] at hmem ⊢
  rcases hmem with hm | hm
  · exact Or.inr (Finset.mem_image.mpr ⟨(k, j), hm, rfl⟩)
  · rw [Finset.mem_image] at hm
    obtain ⟨p, hp, hpe⟩ := hm
    left
    have : p = (j, k) := by
      have h1 : p.2 = k := congrArg Prod.fst hpe
      have h2 : p.1 = j := congrArg Prod.snd hpe
      exact Prod.ext h2 h1
    rwa [this] at hp

/-- **Join 2.**  A pair of levels of the deterministic bulk that is ordered and
misses the exceptional set carries a good `2`-tuple. -/
lemma goodTuple_pair {n j k : ℕ} (hj : j ∈ bulkJ n) (hk : k ∈ bulkJ n) (hlt : j < k)
    (hbad : (j, k) ∉ badPairs n) : GoodTuple n 2 (pairTuple j k) := by
  classical
  have hp : (j, k) ∈ bulkPairs n := by
    rw [bulkPairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hj, hk⟩, hlt⟩
  have hnd : (j, k) ∉ MonomialCore.nearDiag n (200 * Hscale n) := by
    intro hc
    refine hbad ?_
    unfold badPairs
    rw [Finset.mem_union]
    exact Or.inl (Finset.mem_union_left _ hc)
  have hnr : (j, k) ∉ MonomialCore.nearRes n (200 * Hscale n) := by
    intro hc
    refine hbad ?_
    unfold badPairs
    rw [Finset.mem_union]
    exact Or.inl (Finset.mem_union_right _ hc)
  have hgap : 200 * Hscale n < (k : ℝ) - (j : ℝ) := by
    by_contra hc
    refine hnd ?_
    rw [MonomialCore.nearDiag, Finset.mem_filter]
    exact ⟨hp, by simpa using not_lt.mp hc⟩
  have hres : 200 * Hscale n < |(k : ℝ) - ((mIndex n : ℝ) + (j : ℝ)) / 2| := by
    by_contra hc
    refine hnr ?_
    rw [MonomialCore.nearRes, Finset.mem_filter]
    exact ⟨hp, by simpa using not_lt.mp hc⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro ℓ hℓ
    unfold pairTuple
    rw [if_neg (by omega), if_neg (by omega)]
  · intro ℓ ℓ' hℓ hℓ'
    have hℓ0 : ℓ = 0 := by omega
    have hℓ1 : ℓ' = 1 := by omega
    subst hℓ0; subst hℓ1
    simpa [pairTuple] using hlt
  · intro ℓ hℓ
    interval_cases ℓ
    · simpa [pairTuple] using hj
    · simpa [pairTuple] using hk
  · intro ℓ hℓ
    have : ℓ = 0 := by omega
    subst this
    simpa [pairTuple] using hgap.le
  · intro i ℓ hiℓ hℓ
    have hℓ1 : ℓ = 1 := by omega
    have hi0 : i = 0 := by omega
    subst hℓ1; subst hi0
    simpa [pairTuple] using hres.le

/-! ## The covariance estimate at an ordered good pair -/

/-- The `α`-average of a section indicator is at most `1` in absolute value. -/
lemma abs_integral_indFull_le (B : ℕ → Set ℝ) (n j : ℕ) :
    |∫ α in Ioo (0:ℝ) 1, Section5Join.indFull B (digit α j) (theta α n j)| ≤ 1 := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (C := 1)
    (f := fun α : ℝ => Section5Join.indFull B (digit α j) (theta α n j))
    (Filter.Eventually.of_forall (fun α => by
      rw [Real.norm_eq_abs]; exact Section5Join.abs_indFull_le B _ _))
  rw [Real.norm_eq_abs] at h
  have hmass : (volume.restrict (Ioo (0:ℝ) 1)).real Set.univ = 1 := by
    simp [Measure.real, measure_univ]
  rw [hmass, mul_one] at h
  exact h

/-- **The pair covariance estimate.**  Given the two transfer bounds at `n`
(`r = 2` and `r = 1`, at the rate `L^{-5}`), an ordered pair of bulk levels that
misses the exceptional set decorrelates at every pair of nonnegative
thresholds. -/
lemma abs_tail_cov_le_of_transfer
    {n : ℕ} {C₁ C₂ ε : ℝ} (hL : 0 < Lnorm n)
    (h2 : ∀ jj : ℕ → ℕ, GoodTuple n 2 jj →
      ∀ Bs : ℕ → ℕ → Set ℝ, (∀ ℓ a, MeasurableSet (Bs ℓ a)) →
        (∀ ℓ a, IntervalClass.IsUnionOfIntervals 2 (Bs ℓ a)) →
        |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range 2,
              Section5Join.indFull (Bs ℓ) (digit α (jj ℓ)) (theta α n (jj ℓ)))
            - ∏ ℓ ∈ Finset.range 2,
                Section5Join.stationaryMeanR (Section5Join.indFull (Bs ℓ))|
          ≤ C₂ * (Lnorm n) ^ (-(5:ℝ)))
    (h1 : ∀ jj : ℕ → ℕ, GoodTuple n 1 jj →
      ∀ B : ℕ → Set ℝ, (∀ a, MeasurableSet (B a)) →
        (∀ a, IntervalClass.IsUnionOfIntervals 2 (B a)) →
        |(∫ α in Ioo (0:ℝ) 1, Section5Join.indFull B (digit α (jj 0)) (theta α n (jj 0)))
            - Section5Join.stationaryMeanR (Section5Join.indFull B)|
          ≤ C₁ * (Lnorm n) ^ (-(5:ℝ)))
    {j k : ℕ} (hj : j ∈ bulkJ n) (hk : k ∈ bulkJ n) (hlt : j < k)
    (hbad : (j, k) ∉ badPairs n) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |(∫ α in Ioo (0:ℝ) 1,
        PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α
          * PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)
      - (∫ α in Ioo (0:ℝ) 1, PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α)
        * (∫ α in Ioo (0:ℝ) 1,
            PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)|
      ≤ (C₂ + 2 * C₁) * (Lnorm n) ^ (-(5:ℝ)) := by
  classical
  set Bj : ℕ → Set ℝ := Section5Join.truncSection (Lnorm n) (s / Lnorm n) ε with hBj
  set Bk : ℕ → Set ℝ := Section5Join.truncSection (Lnorm n) (t / Lnorm n) ε with hBk
  set Bs : ℕ → ℕ → Set ℝ := fun ℓ => if ℓ = 0 then Bj else Bk with hBs
  have hBs0 : Bs 0 = Bj := by simp [hBs]
  have hBs1 : Bs 1 = Bk := by simp [hBs]
  have hfj : ∀ α : ℝ, PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α
      = Section5Join.indFull Bj (digit α j) (theta α n j) :=
    fun α => tailInd_truncatedMark_eq_indFull ε s hs n j hL α
  have hfk : ∀ α : ℝ, PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α
      = Section5Join.indFull Bk (digit α k) (theta α n k) :=
    fun α => tailInd_truncatedMark_eq_indFull ε t ht n k hL α
  have hmeas : ∀ ℓ a, MeasurableSet (Bs ℓ a) := by
    intro ℓ a
    rcases eq_or_ne ℓ 0 with rfl | hne
    · rw [hBs0, hBj]; exact Section5Join.measurableSet_truncSection _ _ _ _
    · have : Bs ℓ = Bk := by simp [hBs, hne]
      rw [this, hBk]; exact Section5Join.measurableSet_truncSection _ _ _ _
  have hclass : ∀ ℓ a, IntervalClass.IsUnionOfIntervals 2 (Bs ℓ a) := by
    intro ℓ a
    rcases eq_or_ne ℓ 0 with rfl | hne
    · rw [hBs0, hBj]; exact Section5Join.isUnionOfIntervals_truncSection _ _ _ _
    · have : Bs ℓ = Bk := by simp [hBs, hne]
      rw [this, hBk]; exact Section5Join.isUnionOfIntervals_truncSection _ _ _ _
  -- the r = 2 bound, with the product expanded
  have hprod : ∀ α : ℝ, (∏ ℓ ∈ Finset.range 2,
      Section5Join.indFull (Bs ℓ) (digit α (pairTuple j k ℓ)) (theta α n (pairTuple j k ℓ)))
      = Section5Join.indFull Bj (digit α j) (theta α n j)
        * Section5Join.indFull Bk (digit α k) (theta α n k) := by
    intro α
    rw [Finset.prod_range_succ, Finset.prod_range_one, hBs0, hBs1]
    simp [pairTuple]
  have hSprod : (∏ ℓ ∈ Finset.range 2,
      Section5Join.stationaryMeanR (Section5Join.indFull (Bs ℓ)))
      = Section5Join.stationaryMeanR (Section5Join.indFull Bj)
        * Section5Join.stationaryMeanR (Section5Join.indFull Bk) := by
    rw [Finset.prod_range_succ, Finset.prod_range_one, hBs0, hBs1]
  have hA := h2 (pairTuple j k) (goodTuple_pair hj hk hlt hbad) Bs hmeas hclass
  rw [hSprod] at hA
  simp only [hprod] at hA
  have hPj := h1 (singleTuple j) (goodTuple_one n j hj) Bj
    (fun a => by rw [hBj]; exact Section5Join.measurableSet_truncSection _ _ _ _)
    (fun a => by rw [hBj]; exact Section5Join.isUnionOfIntervals_truncSection _ _ _ _)
  have hPk := h1 (singleTuple k) (goodTuple_one n k hk) Bk
    (fun a => by rw [hBk]; exact Section5Join.measurableSet_truncSection _ _ _ _)
    (fun a => by rw [hBk]; exact Section5Join.isUnionOfIntervals_truncSection _ _ _ _)
  simp only [singleTuple] at hPj hPk
  -- names
  set A : ℝ := ∫ α in Ioo (0:ℝ) 1, Section5Join.indFull Bj (digit α j) (theta α n j)
      * Section5Join.indFull Bk (digit α k) (theta α n k) with hAdef
  set P : ℝ := ∫ α in Ioo (0:ℝ) 1, Section5Join.indFull Bj (digit α j) (theta α n j) with hPdef
  set Q : ℝ := ∫ α in Ioo (0:ℝ) 1, Section5Join.indFull Bk (digit α k) (theta α n k) with hQdef
  set S0 : ℝ := Section5Join.stationaryMeanR (Section5Join.indFull Bj) with hS0
  set S1 : ℝ := Section5Join.stationaryMeanR (Section5Join.indFull Bk) with hS1
  have hQ1 : |Q| ≤ 1 := abs_integral_indFull_le Bk n k
  have hS01 : |S0| ≤ 1 :=
    MultiLevel.abs_stationaryMeanR_le (Section5Join.abs_indFull_le Bj)
  have hpow : (0:ℝ) ≤ (Lnorm n) ^ (-(5:ℝ)) := Real.rpow_nonneg hL.le _
  have hgoal : |A - P * Q| ≤ |A - S0 * S1| + (|S0| * |S1 - Q| + |Q| * |S0 - P|) := by
    have hsplit : A - P * Q = (A - S0 * S1) + (S0 * (S1 - Q) + Q * (S0 - P)) := by ring
    calc |A - P * Q| ≤ |A - S0 * S1| + |S0 * (S1 - Q) + Q * (S0 - P)| := by
          rw [hsplit]; exact abs_add_le _ _
      _ ≤ |A - S0 * S1| + (|S0 * (S1 - Q)| + |Q * (S0 - P)|) := by
          gcongr; exact abs_add_le _ _
      _ = |A - S0 * S1| + (|S0| * |S1 - Q| + |Q| * |S0 - P|) := by
          rw [abs_mul, abs_mul]
  have hPQ : |S1 - Q| ≤ C₁ * (Lnorm n) ^ (-(5:ℝ)) := by
    rw [abs_sub_comm]; exact hPk
  have hSP : |S0 - P| ≤ C₁ * (Lnorm n) ^ (-(5:ℝ)) := by
    rw [abs_sub_comm]; exact hPj
  have hC1nn : (0:ℝ) ≤ C₁ * (Lnorm n) ^ (-(5:ℝ)) :=
    le_trans (abs_nonneg _) hSP
  have hfin : |S0| * |S1 - Q| + |Q| * |S0 - P| ≤ 2 * (C₁ * (Lnorm n) ^ (-(5:ℝ))) := by
    have e1 : |S0| * |S1 - Q| ≤ 1 * (C₁ * (Lnorm n) ^ (-(5:ℝ))) := by
      refine mul_le_mul hS01 hPQ (abs_nonneg _) (by norm_num)
    have e2 : |Q| * |S0 - P| ≤ 1 * (C₁ * (Lnorm n) ^ (-(5:ℝ))) := by
      refine mul_le_mul hQ1 hSP (abs_nonneg _) (by norm_num)
    linarith
  simp only [hfj, hfk]
  calc |A - P * Q| ≤ |A - S0 * S1| + (|S0| * |S1 - Q| + |Q| * |S0 - P|) := hgoal
    _ ≤ C₂ * (Lnorm n) ^ (-(5:ℝ)) + 2 * (C₁ * (Lnorm n) ^ (-(5:ℝ))) := by
        exact add_le_add hA hfin
    _ = (C₂ + 2 * C₁) * (Lnorm n) ^ (-(5:ℝ)) := by ring

/-! ## The exceptional-pair count -/

lemma card_badPairs_le (n : ℕ) (hH : 1 ≤ Hscale n) (hL : 1 ≤ Lnorm n) :
    ((badPairs n).card : ℝ) ≤ (1210 * (1 / lyapunov + 1)) * Lnorm n * Hscale n := by
  classical
  set T : ℝ := 200 * Hscale n with hT
  set S : Finset (ℕ × ℕ) :=
    MonomialCore.nearDiag n T ∪ MonomialCore.nearRes n T with hS
  have hT0 : (0:ℝ) ≤ T := by rw [hT]; linarith
  have hnat : (badPairs n).card ≤ 2 * ((3 * ⌊T⌋₊ + 5) * (bulkJ n).card) := by
    have h1 : (badPairs n).card ≤ S.card + (S.image Prod.swap).card :=
      Finset.card_union_le _ _
    have h2 : (S.image Prod.swap).card ≤ S.card := Finset.card_image_le
    have h3 : S.card ≤ (MonomialCore.nearDiag n T).card + (MonomialCore.nearRes n T).card :=
      Finset.card_union_le _ _
    have h4 := MonomialCore.card_nearDiag_le n T
    have h5 := MonomialCore.card_nearRes_le n T
    have h6 : S.card ≤ (3 * ⌊T⌋₊ + 5) * (bulkJ n).card := by
      refine le_trans h3 ?_
      have : (⌊T⌋₊ + 1) * (bulkJ n).card + (2 * ⌊T⌋₊ + 4) * (bulkJ n).card
          = (3 * ⌊T⌋₊ + 5) * (bulkJ n).card := by ring
      omega
    omega
  have hcast : ((badPairs n).card : ℝ)
      ≤ 2 * ((3 * (⌊T⌋₊ : ℝ) + 5) * ((bulkJ n).card : ℝ)) := by
    exact_mod_cast hnat
  have hfl : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hT0
  have hb := MonomialCore.card_bulkJ_le n hL
  have hbnn : (0:ℝ) ≤ ((bulkJ n).card : ℝ) := Nat.cast_nonneg _
  have hlam : (0:ℝ) < lyapunov := Prop42.lyapunov_pos
  have hinv : (0:ℝ) < 1 / lyapunov := by positivity
  have hstep1 : 3 * (⌊T⌋₊ : ℝ) + 5 ≤ 605 * Hscale n := by
    rw [hT] at hfl
    linarith
  have hstep2 : ((bulkJ n).card : ℝ) ≤ (1 / lyapunov + 1) * Lnorm n := hb
  have hH0 : (0:ℝ) ≤ Hscale n := by linarith
  have hL0 : (0:ℝ) ≤ Lnorm n := by linarith
  calc ((badPairs n).card : ℝ)
      ≤ 2 * ((3 * (⌊T⌋₊ : ℝ) + 5) * ((bulkJ n).card : ℝ)) := hcast
    _ ≤ 2 * ((605 * Hscale n) * ((1 / lyapunov + 1) * Lnorm n)) := by
        have hnn : (0:ℝ) ≤ 3 * (⌊T⌋₊ : ℝ) + 5 := by positivity
        have := mul_le_mul hstep1 hstep2 hbnn (by linarith : (0:ℝ) ≤ 605 * Hscale n)
        linarith
    _ = (1210 * (1 / lyapunov + 1)) * Lnorm n * Hscale n := by ring

/-! ## Degenerate thresholds -/

lemma cov_eq_zero_of_left_const {f g : ℝ → ℝ} (hf : ∀ α, f α = 1) :
    (∫ α in Ioo (0:ℝ) 1, f α * g α)
      - (∫ α in Ioo (0:ℝ) 1, f α) * (∫ α in Ioo (0:ℝ) 1, g α) = 0 := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hone : (∫ _α in Ioo (0:ℝ) 1, (1:ℝ)) = 1 := by simp
  simp only [hf, one_mul, hone]
  ring

lemma cov_eq_zero_of_right_const {f g : ℝ → ℝ} (hg : ∀ α, g α = 1) :
    (∫ α in Ioo (0:ℝ) 1, f α * g α)
      - (∫ α in Ioo (0:ℝ) 1, f α) * (∫ α in Ioo (0:ℝ) 1, g α) = 0 := by
  haveI := isProbabilityMeasure_restrict_Ioo
  have hone : (∫ _α in Ioo (0:ℝ) 1, (1:ℝ)) = 1 := by simp
  simp only [hg, mul_one, hone]
  ring

lemma cov_swap (f g : ℝ → ℝ) :
    (∫ α in Ioo (0:ℝ) 1, f α * g α)
      - (∫ α in Ioo (0:ℝ) 1, f α) * (∫ α in Ioo (0:ℝ) 1, g α)
      = (∫ α in Ioo (0:ℝ) 1, g α * f α)
        - (∫ α in Ioo (0:ℝ) 1, g α) * (∫ α in Ioo (0:ℝ) 1, f α) := by
  have h : (∫ α in Ioo (0:ℝ) 1, f α * g α) = ∫ α in Ioo (0:ℝ) 1, g α * f α := by
    simp_rw [mul_comm]
  rw [h, mul_comm (∫ α in Ioo (0:ℝ) 1, f α)]

/-! ## Join 3: the tail transfer -/

/-- **The joint-tail transfer at `r = 2`.**  Exactly the hypothesis of
`DetPairJoin.bulk_offdiagonal_abs_far_sharp_of_tail_transfer`. -/
theorem tail_transfer :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ R : Finset (ℕ × ℕ),
          ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
          ∀ j k : ℕ, j ∈ bulkJ n → k ∈ bulkJ n →
            Hscale n < |(j : ℝ) - (k : ℝ)| → (j, k) ∉ R →
            ∀ s t : ℝ,
              |(∫ α in Ioo (0 : ℝ) 1,
                  PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α
                    * PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)
                - (∫ α in Ioo (0 : ℝ) 1,
                    PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α)
                  * (∫ α in Ioo (0 : ℝ) 1,
                      PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)|
                ≤ δ / (Lnorm n) ^ 4 := by
  classical
  obtain ⟨C₂, hC₂, hev2⟩ := MultiLevel.multiLevel_transfer 2 2 (A := 5) (by norm_num)
  obtain ⟨C₁, hC₁, hev1⟩ := MultiLevel.multiLevel_transfer_one 2 (A := 5) (by norm_num)
  have hlam : (0:ℝ) < lyapunov := Prop42.lyapunov_pos
  have hinv : (0:ℝ) < 1 / lyapunov := by positivity
  refine ⟨1210 * (1 / lyapunov + 1), by linarith, ?_⟩
  intro ε hε hε1 δ hδ
  have hev : ∀ᶠ n : ℕ in atTop,
      ((∀ jj : ℕ → ℕ, GoodTuple n 2 jj →
        ∀ Bs : ℕ → ℕ → Set ℝ, (∀ ℓ a, MeasurableSet (Bs ℓ a)) →
          (∀ ℓ a, IntervalClass.IsUnionOfIntervals 2 (Bs ℓ a)) →
          |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range 2,
                Section5Join.indFull (Bs ℓ) (digit α (jj ℓ)) (theta α n (jj ℓ)))
              - ∏ ℓ ∈ Finset.range 2,
                  Section5Join.stationaryMeanR (Section5Join.indFull (Bs ℓ))|
            ≤ C₂ * (Lnorm n) ^ (-(5:ℝ)))
      ∧ (∀ jj : ℕ → ℕ, GoodTuple n 1 jj →
        ∀ B : ℕ → Set ℝ, (∀ a, MeasurableSet (B a)) →
          (∀ a, IntervalClass.IsUnionOfIntervals 2 (B a)) →
          |(∫ α in Ioo (0:ℝ) 1, Section5Join.indFull B (digit α (jj 0)) (theta α n (jj 0)))
              - Section5Join.stationaryMeanR (Section5Join.indFull B)|
            ≤ C₁ * (Lnorm n) ^ (-(5:ℝ))))
      ∧ (1 ≤ Lnorm n ∧ 1 ≤ Hscale n ∧ C₂ + 2 * C₁ ≤ δ * Lnorm n) := by
    filter_upwards [hev2, hev1, MultiLevel.eventually_const_mul_Hscale_le 1,
      TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop ((C₂ + 2 * C₁) / δ)]
      with n h2 h1 hHL hbig
    obtain ⟨hL0, hH1, hsum⟩ := hHL
    refine ⟨⟨h2, h1⟩, ?_, hH1, ?_⟩
    · linarith
    · rw [div_le_iff₀ hδ] at hbig
      linarith [hbig, mul_comm (Lnorm n) δ]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨⟨h2, h1⟩, hL1, hH1, hbig⟩ := hN n hn
  have hL0 : (0:ℝ) < Lnorm n := by linarith
  refine ⟨badPairs n, card_badPairs_le n hH1 hL1, ?_⟩
  -- the rate conversion
  have hrate : (C₂ + 2 * C₁) * (Lnorm n) ^ (-(5:ℝ)) ≤ δ / (Lnorm n) ^ 4 := by
    have hpow : (Lnorm n) ^ (-(5:ℝ)) = 1 / (Lnorm n) ^ (5:ℕ) := by
      rw [Real.rpow_neg hL0.le, show ((5:ℝ)) = ((5:ℕ):ℝ) by norm_num,
        Real.rpow_natCast, one_div]
    have h4pos : (0:ℝ) < (Lnorm n) ^ (4:ℕ) := by positivity
    have h5pos : (0:ℝ) < (Lnorm n) ^ (5:ℕ) := by positivity
    rw [hpow, mul_one_div, div_le_div_iff₀ h5pos h4pos]
    have h5 : (Lnorm n) ^ (5:ℕ) = (Lnorm n) ^ (4:ℕ) * Lnorm n := by ring
    rw [h5]
    have hmul := mul_le_mul_of_nonneg_right hbig h4pos.le
    nlinarith [hmul]
  -- the main estimate at an ordered pair
  have hmain : ∀ j k : ℕ, j ∈ bulkJ n → k ∈ bulkJ n → j < k → (j, k) ∉ badPairs n →
      ∀ s t : ℝ,
        |(∫ α in Ioo (0 : ℝ) 1,
            PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α
              * PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)
          - (∫ α in Ioo (0 : ℝ) 1,
              PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α)
            * (∫ α in Ioo (0 : ℝ) 1,
                PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)|
          ≤ δ / (Lnorm n) ^ 4 := by
    intro j k hj hk hlt hbad s t
    rcases lt_or_ge s 0 with hs | hs
    · rw [cov_eq_zero_of_left_const
        (f := fun α => PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α)
        (g := fun α => PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)
        (fun α => tailInd_truncatedMark_of_neg ε s hs n j α)]
      simp only [abs_zero]
      positivity
    · rcases lt_or_ge t 0 with ht | ht
      · rw [cov_eq_zero_of_right_const
          (f := fun α => PairLayerCake.tailInd (fun β => truncatedMark ε β n j) s α)
          (g := fun α => PairLayerCake.tailInd (fun β => truncatedMark ε β n k) t α)
          (fun α => tailInd_truncatedMark_of_neg ε t ht n k α)]
        simp only [abs_zero]
        positivity
      · exact le_trans
          (abs_tail_cov_le_of_transfer (ε := ε) hL0 h2 h1 hj hk hlt hbad hs ht) hrate
  intro j k hj hk hfar hbad s t
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exact hmain j k hj hk hlt hbad s t
  · exfalso
    rw [heq] at hfar
    simp at hfar
    linarith
  · rw [cov_swap]
    exact hmain k j hk hj hgt (badPairs_symm hbad) t s

/-! ## The residual, closed -/

/-- **`Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp`, proved.** -/
theorem bulk_offdiagonal_abs_far_sharp_proved (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            CorFinal.offdiagAbsTerm c ε n p ≤ ε / 2 :=
  DetPairJoin.bulk_offdiagonal_abs_far_sharp_of_tail_transfer c tail_transfer

end

end TailTransferJoin

end Kwon1002

/-- **Machine check.**  The theorem proved above carries the statement of the
canonical residual `Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` token for
token. -/
example : @Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp
    = @Kwon1002.TailTransferJoin.bulk_offdiagonal_abs_far_sharp_proved := rfl
