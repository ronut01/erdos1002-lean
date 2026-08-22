import Kwon1002.PairLayerCake
import Kwon1002.WindowCovJoin

/-!
# The residual, reduced to a joint-tail transfer at `r = 2`

`WindowCovJoin.DetPairDecay` — everything §5's last open input still owes after
`Kwon1002/WindowCovariance.lean` — is a covariance statement.  This module spends
`PairLayerCake.abs_cov_le_of_indicator_cov` on it and leaves a statement about
**tail events** only:

  for every `δ > 0`, outside `O(L·H)` pairs, at every pair of levels `j,k ∈ J_n`
  more than `H` apart and at every pair of thresholds `s,t`,

  `|P(Z^{(ε)}_j > s, Z^{(ε)}_k > t) − P(Z^{(ε)}_j > s)·P(Z^{(ε)}_k > t)| ≤ δ/L⁴`.

That is exactly the currency `Kwon1002.MultiLevel.multiLevel_transfer` is stated
in — an `α`-average of a product of indicators against the product of the
stationary means — at `r = 2`, with rate `L^{-A}` and `A` free, so `A = 5`
suffices.  The threshold sets are the interval-class families
`Kwon1002.Section5Join.truncSection` already used by `Kwon1002/BandMass.lean`.
-/

open Filter MeasureTheory Set

namespace Kwon1002

namespace DetPairJoin

noncomputable section

/-- The covariance of the two centred deterministic-bulk summands is the
covariance of the two truncated marks, divided by `L²`. -/
lemma integral_detTermCentered_mul_eq (ε : ℝ) (n j k : ℕ) (hε : 0 ≤ ε)
    (hL : 0 < Lnorm n) (hj : j ∈ bulkJ n) (hk : k ∈ bulkJ n) :
    (∫ α in Ioo (0 : ℝ) 1,
        WindowCov.detTermCentered ε α n j * WindowCov.detTermCentered ε α n k)
      = ((∫ α in Ioo (0 : ℝ) 1, truncatedMark ε α n j * truncatedMark ε α n k)
          - (∫ α in Ioo (0 : ℝ) 1, truncatedMark ε α n j)
            * (∫ α in Ioo (0 : ℝ) 1, truncatedMark ε α n k)) / (Lnorm n) ^ 2 := by
  haveI := isProbabilityMeasure_restrict_Ioo
  set Zj : ℝ → ℝ := fun α => truncatedMark ε α n j with hZj
  set Zk : ℝ → ℝ := fun α => truncatedMark ε α n k with hZk
  have hbdj : ∀ α, |Zj α| ≤ ε * Lnorm n := by
    intro α
    rw [hZj, abs_of_nonneg (truncatedMark_nonneg ε α n j)]
    exact truncatedMark_le ε hε α n j
  have hbdk : ∀ α, |Zk α| ≤ ε * Lnorm n := by
    intro α
    rw [hZk, abs_of_nonneg (truncatedMark_nonneg ε α n k)]
    exact truncatedMark_le ε hε α n k
  have hjint : Integrable Zj (volume.restrict (Ioo (0 : ℝ) 1)) :=
    PairLayerCake.integrable_of_bdd (measurable_truncatedMark ε n j) hbdj
  have hkint : Integrable Zk (volume.restrict (Ioo (0 : ℝ) 1)) :=
    PairLayerCake.integrable_of_bdd (measurable_truncatedMark ε n k) hbdk
  set a : ℝ := ∫ α in Ioo (0 : ℝ) 1, Zj α with ha
  set b : ℝ := ∫ α in Ioo (0 : ℝ) 1, Zk α with hb
  have hdet : ∀ (i : ℕ) (α : ℝ), i ∈ bulkJ n →
      WindowCov.detTerm ε α n i = truncatedMark ε α n i / Lnorm n := by
    intro i α hi
    unfold WindowCov.detTerm
    rw [if_pos hi]
  have hintdetj : (∫ β in Ioo (0 : ℝ) 1, WindowCov.detTerm ε β n j) = a / Lnorm n := by
    simp only [hdet j _ hj, ha, hZj]
    exact integral_div _ _
  have hintdetk : (∫ β in Ioo (0 : ℝ) 1, WindowCov.detTerm ε β n k) = b / Lnorm n := by
    simp only [hdet k _ hk, hb, hZk]
    exact integral_div _ _
  have hptw : ∀ α : ℝ,
      WindowCov.detTermCentered ε α n j * WindowCov.detTermCentered ε α n k
        = (Zj α * Zk α - b * Zj α - a * Zk α + a * b) / (Lnorm n) ^ 2 := by
    intro α
    unfold WindowCov.detTermCentered
    rw [hdet j α hj, hdet k α hk, hintdetj, hintdetk]
    field_simp
    ring
  have hprodint : Integrable (fun α => Zj α * Zk α)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine PairLayerCake.integrable_of_bdd
      ((measurable_truncatedMark ε n j).mul (measurable_truncatedMark ε n k))
      (C := (ε * Lnorm n) ^ 2) (fun α => ?_)
    rw [abs_mul]
    nlinarith [hbdj α, hbdk α, abs_nonneg (Zj α), abs_nonneg (Zk α)]
  have hnumint : Integrable
      (fun α => Zj α * Zk α - b * Zj α - a * Zk α + a * b)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((hprodint.sub (hjint.const_mul b)).sub (hkint.const_mul a)).add
      (integrable_const _)
  have hnum : (∫ α in Ioo (0 : ℝ) 1,
      (Zj α * Zk α - b * Zj α - a * Zk α + a * b))
      = (∫ α in Ioo (0 : ℝ) 1, Zj α * Zk α) - a * b := by
    have e1 : (∫ α in Ioo (0 : ℝ) 1,
          ((Zj α * Zk α - b * Zj α - a * Zk α) + a * b))
        = (∫ α in Ioo (0 : ℝ) 1, (Zj α * Zk α - b * Zj α - a * Zk α))
          + ∫ _α in Ioo (0 : ℝ) 1, a * b :=
      integral_add ((hprodint.sub (hjint.const_mul b)).sub (hkint.const_mul a))
        (integrable_const _)
    have e2 : (∫ α in Ioo (0 : ℝ) 1, ((Zj α * Zk α - b * Zj α) - a * Zk α))
        = (∫ α in Ioo (0 : ℝ) 1, (Zj α * Zk α - b * Zj α))
          - ∫ α in Ioo (0 : ℝ) 1, a * Zk α :=
      integral_sub (hprodint.sub (hjint.const_mul b)) (hkint.const_mul a)
    have e3 : (∫ α in Ioo (0 : ℝ) 1, (Zj α * Zk α - b * Zj α))
        = (∫ α in Ioo (0 : ℝ) 1, Zj α * Zk α)
          - ∫ α in Ioo (0 : ℝ) 1, b * Zj α :=
      integral_sub hprodint (hjint.const_mul b)
    have e4 : (∫ α in Ioo (0 : ℝ) 1, b * Zj α) = b * a := by
      rw [integral_const_mul, ← ha]
    have e5 : (∫ α in Ioo (0 : ℝ) 1, a * Zk α) = a * b := by
      rw [integral_const_mul, ← hb]
    have e6 : (∫ _α in Ioo (0 : ℝ) 1, a * b) = a * b := by simp
    rw [e1, e2, e3, e4, e5, e6]
    ring
  simp only [hptw]
  rw [integral_div, hnum]

/-! ## The reduction -/

/-- **The residual, as a joint-tail statement.**  `WindowCovJoin.DetPairDecay`
— and hence, through
`WindowCovJoin.bulk_offdiagonal_abs_far_sharp_of_detPairDecay`, the statement of
`Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` — follows from
quasi-independence of the *tail events* of the two truncated marks, uniformly in
the two thresholds, at rate `δ/L⁴`.

The rate is not sharp and is not meant to be: `MultiLevel.multiLevel_transfer`
supplies `C·L^{-A}` with `A` free, so `A = 5` clears it. -/
theorem detPairDecay_of_tail_transfer (c : ℝ)
    (h : ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
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
                ≤ δ / (Lnorm n) ^ 4) :
    WindowCovJoin.DetPairDecay c := by
  classical
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨κ, hκ, htr⟩ := h
  refine ⟨κ, hκ, ?_⟩
  intro ε hε hε1 δ hδ
  obtain ⟨N, hN⟩ := htr ε hε hε1 δ hδ
  refine ⟨max N 3, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL1 : (1 : ℝ) ≤ Lnorm n := WindowCov.one_le_Lnorm_of_three_le n hn3
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  obtain ⟨R, hRcard, hRtr⟩ := hN n hnN
  refine ⟨R, hRcard, fun j k hj hk hfar hR => ?_⟩
  set M : ℝ := ε * Lnorm n with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hcov := PairLayerCake.abs_cov_le_of_indicator_cov
    (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun α => truncatedMark ε α n j) (g := fun α => truncatedMark ε α n k)
    (measurable_truncatedMark ε n j) (measurable_truncatedMark ε n k)
    (M := M) (K := δ / (Lnorm n) ^ 4) hM0 (by positivity)
    (fun α => truncatedMark_nonneg ε α n j)
    (fun α => truncatedMark_le ε hε.le α n j)
    (fun α => truncatedMark_nonneg ε α n k)
    (fun α => truncatedMark_le ε hε.le α n k)
    (hRtr j k hj hk hfar hR)
  rw [integral_detTermCentered_mul_eq ε n j k hε.le hL0 hj hk]
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Lnorm n) ^ 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hMK : M ^ 2 * (δ / (Lnorm n) ^ 4) = ε ^ 2 * δ / (Lnorm n) ^ 2 := by
    rw [hM]; field_simp
  rw [hMK] at hcov
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hL2 : (1 : ℝ) ≤ (Lnorm n) ^ 2 := by nlinarith
  have hstep : ε ^ 2 * δ / (Lnorm n) ^ 2 * (Lnorm n) ^ 2 ≤ δ * (Lnorm n) ^ 2 := by
    have hcancel : ε ^ 2 * δ / (Lnorm n) ^ 2 * (Lnorm n) ^ 2 = ε ^ 2 * δ := by
      field_simp
    rw [hcancel]
    nlinarith [hδ.le, hε2, hL2]
  nlinarith [hcov, hstep, sq_nonneg (Lnorm n)]


/-- **The whole reduction, in one statement.**  `Kwon1002.CorFinal`'s residual
follows from the joint-tail transfer at `r = 2`.

Chain: `detPairDecay_of_tail_transfer` (the layer-cake conversion of this
module) then `WindowCovJoin.bulk_offdiagonal_abs_far_sharp_of_detPairDecay`
(the covariance-currency window bridge of `Kwon1002/WindowCovariance.lean`).
Both are axiom-clean, so this is too.

**What is left, precisely.**  Exhibiting the hypothesis is the composition of
three proved theorems that have never been composed:

* `Kwon1002.MultiLevel.multiLevel_transfer 2 2` at `A = 5`, which bounds
  `|∫ ∏_{ℓ<2} 1_{Bs ℓ} − ∏_{ℓ<2} stationaryMeanR (1_{Bs ℓ})|` by `C·L^{-5}`
  uniformly over good `2`-tuples of `J_n` and over families of `θ`-sections
  that are unions of at most `2` intervals;
* `Kwon1002.Section5Join.isUnionOfIntervals_truncSection`, which puts the
  threshold family `{θ ∈ [0,1) : a·W(θ) ∈ (s, εL]}` — the `θ`-section of
  `{Z^{(ε)}_{n,j} > s}` — in that class, for every threshold `s`;
* `Kwon1002.MonomialCore.card_nearDiag_le` and
  `Kwon1002.MonomialCore.card_nearRes_le`, which count the pairs of `J_n` that
  fail displays (25)–(26) at `O(L·H)`, the bad set `R` the hypothesis allows.

The two joins still to be written are: the identification of
`PairLayerCake.tailInd (Z^{(ε)}_{n,j}) s` with
`Section5Join.indFull (truncSection …) (digit α j) (theta α n j)` (the
periodisation `Selberg.perInd` composed with `theta α n j ∈ [0,1)`), and the
passage from a far, non-resonant *pair* to a `Kwon1002.GoodTuple n 2`. -/
theorem bulk_offdiagonal_abs_far_sharp_of_tail_transfer (c : ℝ)
    (h : ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
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
                ≤ δ / (Lnorm n) ^ 4) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            CorFinal.offdiagAbsTerm c ε n p ≤ ε / 2 :=
  WindowCovJoin.bulk_offdiagonal_abs_far_sharp_of_detPairDecay c
    (detPairDecay_of_tail_transfer c h)

end

end DetPairJoin

end Kwon1002
