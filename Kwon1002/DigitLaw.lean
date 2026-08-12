import Kwon1002.WindowMarginal
import Kwon1002.DigitTail

/-!
# The stationary digit law: single-digit tails under the window law `μ_R`

`Kwon1002.digit_tail_product` (`Kwon1002/DigitTail.lean`) bounds multi-digit
tail events under Lebesgue measure on `(0,1)`.  What the union bound of
`Prop64.event_truncation` consumes is the same one-level bound under the
*stationary window law* `μ_R = windowLaw R`, at every offset `t`.  This file
supplies the transport.

## The route

`μ_R = (stationaryWindow R)_* μ̂₀`, and the digit of a stationary window at
offset `t` is the leading Gauss digit of `(S^t z).1.1`
(`wA_stationaryWindow`).  So the law of the digit at offset `t` is the law
of `digit · 0` under `(z ↦ (S^t z).1.1)_* μ̂₀`, and the chain is:

* `hatSinv_measurePreserving`: the inverse cocycle preserves `μ̂₀`, the
  mirror of `Lemma62.hatS_measurePreserving` built from
  `Lemma62.natExtInv_measurePreserving` and the inverse fibre rotation.
  With it, `hatSzpow_measurePreserving` handles every integer power, both
  time directions.
* `hatMu0_map_hatSzpow_future`: stationarity moves the offset-`t` law to
  the offset-`0` law, which is the first-coordinate marginal of `ν̂`, i.e.
  the Gauss measure `gaussMarginal` (`NatExtMeasure.hatNu_fst_marginal`).
* `gaussMarginal_digit_tail`: the one-level tail under `gaussMarginal` is
  at most `2/A`, because `{a₁ ≥ A} ∩ (0,1) ⊆ (0, 1/A]` and the Gauss
  density is bounded by `1/log 2 ≤ 2`.
* `windowLaw_digit_tail` / `windowLaw_digitCoord_tail`: the deliverable,
  `μ_R{a_{j+t+1} ≥ A} ≤ 2/A` for every offset (vacuously outside
  `[-R, R]`, where `wA` reads `0`).

The joint (multi-offset) form is deliberately **not** stated: the union
bound of `event_truncation` needs only one level at a time.

Everything is exact pushforward bookkeeping — no almost-everywhere identity
is invoked, because `wA_stationaryWindow` is a pointwise identity of the
window construction.  The a.e. caution around `hatSzpow` concerns the
*orbit recursion* (`natExtGood`), not the measure-preservation used here.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

noncomputable section

/-! ## The inverse cocycle preserves `μ̂₀` -/

/-- The inverse fibre map `(θ', θ) ↦ ({θ + a θ'}, θ')` of `hatSinv`
preserves Lebesgue on the torus square; the mirror of
`Lemma62.torusFibre_measurePreserving`, by the same skew-product-of-a-
rotation factorization. -/
theorem torusFibreInv_measurePreserving (a : ℕ) :
    MeasurePreserving (fun q : ℝ × ℝ => (Int.fract (q.2 + (a : ℝ) * q.1), q.1))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [NatExtMeasure.restrict_unitSq_eq_prod]
  set μ := (volume : Measure ℝ).restrict (Ioo (0:ℝ) 1) with hμ
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) (μ.prod μ) (μ.prod μ) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hskew : MeasurePreserving
      (fun p : ℝ × ℝ => (id p.1, Int.fract (p.2 + (a : ℝ) * p.1))) (μ.prod μ) (μ.prod μ) := by
    refine (MeasurePreserving.id μ).skew_product
      (g := fun s r : ℝ => Int.fract (r + (a : ℝ) * s)) ?_ ?_
    · exact (measurable_snd.add (measurable_fst.const_mul _)).fract
    · filter_upwards with s
      simpa only [sub_neg_eq_add] using NatExtMeasure.map_fract_sub_Ioo (-((a : ℝ) * s))
  simpa [Function.comp] using hswap.comp hskew

/-- **The inverse cocycle preserves `μ̂₀`.**  Mirror of
`Lemma62.hatS_measurePreserving`: `hatSinv` is the skew product of
`natExtInv` (which preserves `ν̂` by `Lemma62.natExtInv_measurePreserving`)
with the inverse fibre rotation at the digit `a_j = ⌊1/y⌋` read off the
past coordinate of the base point. -/
theorem hatSinv_measurePreserving : MeasurePreserving hatSinv hatMu0 hatMu0 := by
  rw [hatMu0_eq_prod]
  have hgm : Measurable (Function.uncurry
      (fun (p : ℝ × ℝ) (q : ℝ × ℝ) =>
        (Int.fract (q.2 + (digit p.2 0 : ℝ) * q.1), q.1))) := by
    refine Measurable.prodMk ?_ (measurable_fst.comp measurable_snd)
    exact ((measurable_snd.comp measurable_snd).add
      (((measurable_digitCast 0).comp (measurable_snd.comp measurable_fst)).mul
        (measurable_fst.comp measurable_snd))).fract
  have hg : ∀ᵐ p ∂hatNu, Measure.map
      (fun q : ℝ × ℝ => (Int.fract (q.2 + (digit p.2 0 : ℝ) * q.1), q.1))
      ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
      = (volume : Measure (ℝ × ℝ)).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    Filter.Eventually.of_forall
      (fun p => (torusFibreInv_measurePreserving (digit p.2 0)).map_eq)
  exact Lemma62.natExtInv_measurePreserving.skew_product hgm hg

/-- Every integer power of the cocycle preserves `μ̂₀`; the two branches of
`hatSzpow` are iterates of `hatS` and of `hatSinv`. -/
theorem hatSzpow_measurePreserving (t : ℤ) :
    MeasurePreserving (hatSzpow t) hatMu0 hatMu0 := by
  by_cases h : (0 : ℤ) ≤ t
  · have he : hatSzpow t = hatS^[t.toNat] := by
      funext z; simp [hatSzpow, h]
    rw [he]
    exact Lemma62.hatS_measurePreserving.iterate _
  · have he : hatSzpow t = hatSinv^[(-t).toNat] := by
      funext z; simp [hatSzpow, h]
    rw [he]
    exact hatSinv_measurePreserving.iterate _

/-! ## The digit law at every offset -/

/-- **The stationary law of the future coordinate at every offset.**
Under `μ̂₀` the future Gauss coordinate of `S^t z` has the Gauss law
`gaussMarginal`, for every `t : ℤ`: stationarity
(`hatSzpow_measurePreserving`) moves every offset to `t = 0`, and the
`t = 0` law is the first-coordinate marginal of `ν̂`
(`NatExtMeasure.hatNu_fst_marginal`). -/
theorem hatMu0_map_hatSzpow_future (t : ℤ) :
    hatMu0.map (fun z : NatExtTorus => (hatSzpow t z).1.1) = gaussMarginal := by
  have hcomp : (fun z : NatExtTorus => (hatSzpow t z).1.1)
      = ((Prod.fst : ℝ × ℝ → ℝ) ∘ (Prod.fst : NatExtTorus → ℝ × ℝ)) ∘ hatSzpow t := rfl
  rw [hcomp, ← Measure.map_map (measurable_fst.comp measurable_fst)
      (measurable_hatSzpow t),
    (hatSzpow_measurePreserving t).map_eq,
    ← Measure.map_map measurable_fst measurable_fst,
    hatMu0_eq_prod, Measure.map_fst_prod, measure_univ, one_smul,
    NatExtMeasure.hatNu_fst_marginal]

/-- **The one-level Gauss digit tail**: `γ{a₁ ≥ A} ≤ 2/A` for `A ≥ 1`.
The event sits inside `(0, 1/A]` and the Gauss density is bounded by
`1/log 2 ≤ 2`. -/
theorem gaussMarginal_digit_tail {A : ℝ} (hA : 1 ≤ A) :
    gaussMarginal {x : ℝ | A ≤ (digit x 0 : ℝ)} ≤ ENNReal.ofReal (2 / A) := by
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  have hS : MeasurableSet {x : ℝ | A ≤ (digit x 0 : ℝ)} :=
    measurableSet_le measurable_const (measurable_digit_real 0)
  set T : Set ℝ := {x : ℝ | A ≤ (digit x 0 : ℝ)} ∩ Ioo 0 1 with hTdef
  have hTm : MeasurableSet T := hS.inter measurableSet_Ioo
  -- the event is confined to `(0, 1/A]`
  have hsub : T ⊆ Ioc (0:ℝ) A⁻¹ := by
    rintro x ⟨hxd, hx0, hx1⟩
    have hinv1 : (1:ℝ) < x⁻¹ := by
      rw [lt_inv_comm₀ one_pos hx0]; simpa using hx1
    have hfl : (0:ℤ) ≤ ⌊x⁻¹⌋ := Int.floor_nonneg.mpr (by linarith)
    have hd : digit x 0 = ⌊x⁻¹⌋.toNat := by simp [digit, gaussIter]
    have hcast : ((digit x 0 : ℕ) : ℝ) = ((⌊x⁻¹⌋ : ℤ) : ℝ) := by
      rw [hd]; exact_mod_cast Int.toNat_of_nonneg hfl
    have hAx : A ≤ x⁻¹ := by
      have hxd' : A ≤ ((digit x 0 : ℕ) : ℝ) := hxd
      rw [hcast] at hxd'
      exact hxd'.trans (Int.floor_le _)
    exact ⟨hx0, (le_inv_comm₀ hA0 hx0).mp hAx⟩
  -- the density is bounded by `2` on `(0,1)`
  have hle : ∫⁻ x in T, ENNReal.ofReal (1 / (Real.log 2 * (1 + x))) ∂volume
      ≤ ∫⁻ _ in T, ENNReal.ofReal 2 ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hTm] with x hx
    have hx0 : (0:ℝ) < x := hx.2.1
    have hlog : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  calc gaussMarginal {x : ℝ | A ≤ (digit x 0 : ℝ)}
      = ∫⁻ x in T, ENNReal.ofReal (1 / (Real.log 2 * (1 + x))) ∂volume := by
        rw [gaussMarginal, withDensity_apply _ hS, Measure.restrict_restrict hS]
    _ ≤ ∫⁻ _ in T, ENNReal.ofReal 2 ∂volume := hle
    _ = ENNReal.ofReal 2 * volume T := setLIntegral_const T _
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal A⁻¹ := by
        gcongr
        refine le_trans (measure_mono hsub) ?_
        rw [Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (2 / A) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv]

/-- **The single-digit tail bound under the stationary window law**, the
form the union bound of `Prop64.event_truncation` consumes:
`μ_R{ w | a_{j+t+1}(w) ≥ A } ≤ 2/A` for every offset `t` and every
threshold `A ≥ 1`.  Outside `-R ≤ t ≤ R` the reader `wA` returns `0` and
the event is empty, so no range hypothesis is needed. -/
theorem windowLaw_digit_tail (R : ℕ) (t : ℤ) {A : ℝ} (hA : 1 ≤ A) :
    windowLaw R {w : WindowSpace R | A ≤ (wA w t : ℝ)} ≤ ENNReal.ofReal (2 / A) := by
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  have hSA : MeasurableSet {x : ℝ | A ≤ (digit x 0 : ℝ)} :=
    measurableSet_le measurable_const (measurable_digit_real 0)
  by_cases hrange : 0 ≤ t + (R:ℤ) ∧ t + (R:ℤ) < 2 * (R:ℤ) + 1
  · have h1 : -(R:ℤ) ≤ t := by omega
    have h2 : t ≤ (R:ℤ) := by omega
    have hS : MeasurableSet {w : WindowSpace R | A ≤ (wA w t : ℝ)} := by
      have hrw : {w : WindowSpace R | A ≤ (wA w t : ℝ)}
          = (fun w : WindowSpace R => wA w t) ⁻¹' {n : ℕ | A ≤ (n : ℝ)} := rfl
      rw [hrw]
      exact measurable_wA R t MeasurableSet.of_discrete
    have hmeas : Measurable (fun z : NatExtTorus => (hatSzpow t z).1.1) :=
      (measurable_fst.comp measurable_fst).comp (measurable_hatSzpow t)
    rw [windowLaw, Measure.map_apply (measurable_stationaryWindow R) hS]
    have hpre : stationaryWindow R ⁻¹' {w : WindowSpace R | A ≤ (wA w t : ℝ)}
        = (fun z : NatExtTorus => (hatSzpow t z).1.1) ⁻¹'
            {x : ℝ | A ≤ (digit x 0 : ℝ)} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [wA_stationaryWindow R z h1 h2]
    rw [hpre, ← Measure.map_apply hmeas hSA, hatMu0_map_hatSzpow_future t]
    exact gaussMarginal_digit_tail hA
  · have hempty : {w : WindowSpace R | A ≤ (wA w t : ℝ)} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, wA,
        dif_neg hrange, Nat.cast_zero]
      exact hA0
    rw [hempty]
    simp

/-- The tail bound read on the raw digit coordinate `w.1 i`, which is how
`digitCapEvent` speaks: `μ_R{ w | w.1 i ≥ K + 1 } ≤ 2/(K+1)`. -/
theorem windowLaw_digitCoord_tail (R : ℕ) (i : Fin (2 * R + 1)) (K : ℕ) :
    windowLaw R {w : WindowSpace R | K + 1 ≤ w.1 i}
      ≤ ENNReal.ofReal (2 / ((K : ℝ) + 1)) := by
  have hset : {w : WindowSpace R | K + 1 ≤ w.1 i}
      = {w : WindowSpace R | ((K + 1 : ℕ) : ℝ) ≤ (wA w ((i : ℤ) - (R : ℤ)) : ℝ)} := by
    ext w
    have hc : 0 ≤ ((i:ℤ) - (R:ℤ)) + (R:ℤ) ∧ ((i:ℤ) - (R:ℤ)) + (R:ℤ) < 2 * (R:ℤ) + 1 := by
      have := i.isLt; constructor <;> omega
    simp only [Set.mem_setOf_eq, wA, dif_pos hc]
    have hfin : (⟨(((i:ℤ) - (R:ℤ)) + (R:ℤ)).toNat, by omega⟩ : Fin (2 * R + 1)) = i := by
      apply Fin.ext
      simp only
      omega
    rw [hfin]
    exact Nat.cast_le.symm
  have h1 : (1:ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr K.succ_ne_zero
  have := windowLaw_digit_tail R ((i : ℤ) - (R : ℤ)) h1
  rw [hset]
  refine le_trans this (le_of_eq ?_)
  congr 1
  push_cast
  ring

end

end Kwon1002
