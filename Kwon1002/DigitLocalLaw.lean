import Kwon1002.DigitTail

/-!
# The local Gauss digit law

`DigitLaw.lean` and `DigitTail.lean` carry only *tails* of the first digit, of
shape `2/A` and `12/f j`.  Finding F7 established that tails cannot supply the
band-mass input that `truncatedMark_sub_lipTrunc_L1_of_band` needs for
`CovarianceChain.farWindow_sum_small`: a tail bound gives the band
`{A ≤ a < 2A}` a mass `O(1/(εL))`, while the interface needs `o(1/(εL))`.  The
local law is the only route, and it is what this module proves:

`γ{x : a₁(x) = k} = log(1 + 1/(k(k+2))) / log 2`,

the classical Gauss-Kuzmin one-step law.  It is self-contained: the event is
exactly the interval `(1/(k+1), 1/k]`, and the Gauss density integrates in
closed form, which the substrate already supplies as
`Erdos1002.gaussMeasure_real_Ioc`.

Nothing in `DigitLaw.lean` is touched.
-/

open MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace DigitLocalLaw

noncomputable section

/-- On `(0,1]` the first digit is `⌊1/x⌋`, and `⌊1/x⌋ = k` cuts out exactly the
interval `(1/(k+1), 1/k]`. -/
theorem inter_digit_eq_Ioc {k : ℕ} (hk : 1 ≤ k) :
    Ioc (0 : ℝ) 1 ∩ {x : ℝ | digit x 0 = k} = Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, hd⟩
    have hmul : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx0)
    have hinv : (1 : ℝ) ≤ x⁻¹ := by
      rw [le_inv_comm₀ one_pos hx0]; simpa using hx1
    have hfl : (1 : ℤ) ≤ ⌊x⁻¹⌋ := Int.le_floor.mpr (by exact_mod_cast hinv)
    have hdig : (⌊x⁻¹⌋).toNat = k := hd
    have hfk : ⌊x⁻¹⌋ = (k : ℤ) := by omega
    have hlow : (k : ℝ) ≤ x⁻¹ := by
      have h := Int.floor_le x⁻¹
      rw [hfk] at h; exact_mod_cast h
    have hhigh : x⁻¹ < (k : ℝ) + 1 := by
      have h := Int.lt_floor_add_one x⁻¹
      rw [hfk] at h
      push_cast at h ⊢; linarith
    constructor
    · rw [div_lt_iff₀ hk1]
      have h1 : x⁻¹ * x < ((k : ℝ) + 1) * x :=
        mul_lt_mul_of_pos_right hhigh hx0
      rw [hmul] at h1; linarith
    · rw [le_div_iff₀ hk0]
      have h1 : (k : ℝ) * x ≤ x⁻¹ * x := mul_le_mul_of_nonneg_right hlow hx0.le
      rw [hmul] at h1; linarith
  · rintro ⟨hlo, hhi⟩
    have hx0 : (0 : ℝ) < x := lt_trans (by positivity) hlo
    have hmul : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx0)
    have hx1 : x ≤ 1 := by
      refine hhi.trans ?_
      rw [div_le_one hk0]; exact_mod_cast hk
    rw [div_lt_iff₀ hk1] at hlo
    rw [le_div_iff₀ hk0] at hhi
    have hlow : (k : ℝ) ≤ x⁻¹ := by
      refine le_of_mul_le_mul_right ?_ hx0
      rw [hmul]; linarith
    have hhigh : x⁻¹ < (k : ℝ) + 1 := by
      refine lt_of_mul_lt_mul_right ?_ hx0.le
      rw [hmul]; linarith
    have hfk : ⌊x⁻¹⌋ = (k : ℤ) := by
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast; exact hlow
      · push_cast; exact hhigh
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    show (⌊x⁻¹⌋).toNat = k
    rw [hfk]; simp

lemma measurableSet_digit_zero (k : ℕ) : MeasurableSet {x : ℝ | digit x 0 = k} := by
  have h : {x : ℝ | digit x 0 = k} = (fun x : ℝ => (digit x 0 : ℝ)) ⁻¹' {(k : ℝ)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => by rw [h], fun h => by exact_mod_cast h⟩
  rw [h]
  exact (measurable_digit_real 0) (measurableSet_singleton _)

/-- The Gauss measure is carried by `(0,1]`, so the digit event may be
intersected with it for free. -/
lemma gaussMeasure_inter_unit (A : Set ℝ) :
    Erdos1002.gaussMeasure (A ∩ Ioc (0 : ℝ) 1) = Erdos1002.gaussMeasure A := by
  have hnull : Erdos1002.gaussMeasure (A \ Ioc (0 : ℝ) 1) = 0 :=
    measure_mono_null (fun x hx => hx.2) gaussMeasure_compl_unit
  have h := measure_inter_add_diff (μ := Erdos1002.gaussMeasure) A
    (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))
  rw [hnull, add_zero] at h
  exact h

/-- **The local Gauss digit law.**  For every `k ≥ 1`,
`γ{x : a₁(x) = k} = log(1 + 1/(k(k+2)))/log 2`. -/
theorem gaussMeasure_real_digit_zero {k : ℕ} (hk : 1 ≤ k) :
    (Erdos1002.gaussMeasure {x : ℝ | digit x 0 = k}).toReal
      = Real.log (1 + 1 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  have hswap : Erdos1002.gaussMeasure {x : ℝ | digit x 0 = k}
      = Erdos1002.gaussMeasure (Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))) := by
    rw [← gaussMeasure_inter_unit {x : ℝ | digit x 0 = k}, Set.inter_comm,
      inter_digit_eq_Ioc hk]
  rw [hswap]
  have hval : (Erdos1002.gaussMeasure (Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)))).toReal
      = (Real.log (1 + 1 / (k : ℝ)) - Real.log (1 + 1 / ((k : ℝ) + 1))) / Real.log 2 :=
    Erdos1002.gaussMeasure_real_Ioc (by positivity)
      (by rw [div_le_div_iff_of_pos_left one_pos hk1 hk0]; linarith)
      (by rw [div_le_one hk0]; exact_mod_cast hk)
  rw [hval]
  congr 1
  have hpos1 : (0 : ℝ) < 1 + 1 / (k : ℝ) := by positivity
  have hpos2 : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by positivity
  rw [← Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)]
  congr 1
  field_simp
  ring

/-- On `(0,1]` the event `a₁(x) ≥ K` is exactly `(0, 1/K]`. -/
theorem inter_digit_ge_eq_Ioc {K : ℕ} (hK : 1 ≤ K) :
    Ioc (0 : ℝ) 1 ∩ {x : ℝ | K ≤ digit x 0} = Ioc (0 : ℝ) (1 / (K : ℝ)) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, hd⟩
    have hmul : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx0)
    have hinv : (1 : ℝ) ≤ x⁻¹ := by
      rw [le_inv_comm₀ one_pos hx0]; simpa using hx1
    have hfl : (1 : ℤ) ≤ ⌊x⁻¹⌋ := Int.le_floor.mpr (by exact_mod_cast hinv)
    have hdg : K ≤ (⌊x⁻¹⌋).toNat := hd
    have hfk : (K : ℤ) ≤ ⌊x⁻¹⌋ := by omega
    have hlow : (K : ℝ) ≤ x⁻¹ := by
      have h := Int.floor_le x⁻¹
      have h2 : ((K : ℤ) : ℝ) ≤ ((⌊x⁻¹⌋ : ℤ) : ℝ) := by exact_mod_cast hfk
      push_cast at h2; linarith
    refine ⟨hx0, ?_⟩
    rw [le_div_iff₀ hK0]
    have h1 : (K : ℝ) * x ≤ x⁻¹ * x := mul_le_mul_of_nonneg_right hlow hx0.le
    rw [hmul] at h1; linarith
  · rintro ⟨hx0, hhi⟩
    have hmul : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx0)
    have hx1 : x ≤ 1 := by
      refine hhi.trans ?_
      rw [div_le_one hK0]; exact_mod_cast hK
    rw [le_div_iff₀ hK0] at hhi
    have hlow : (K : ℝ) ≤ x⁻¹ := by
      refine le_of_mul_le_mul_right ?_ hx0
      rw [hmul]; linarith
    have hfk : (K : ℤ) ≤ ⌊x⁻¹⌋ := Int.le_floor.mpr (by exact_mod_cast hlow)
    exact ⟨⟨hx0, hx1⟩, by show K ≤ (⌊x⁻¹⌋).toNat; omega⟩

/-- **The exact (asymptotic) Gauss digit tail.**  `γ{a₁ ≥ K} = log(1 + 1/K)/log 2`.

`DigitTail.gaussMeasure_firstDigit_ge_le` bounds the same quantity by `2/K`;
this is the exact value, which is what display (35) needs. -/
theorem gaussMeasure_real_digit_zero_ge {K : ℕ} (hK : 1 ≤ K) :
    (Erdos1002.gaussMeasure {x : ℝ | K ≤ digit x 0}).toReal
      = Real.log (1 + 1 / (K : ℝ)) / Real.log 2 := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hswap : Erdos1002.gaussMeasure {x : ℝ | K ≤ digit x 0}
      = Erdos1002.gaussMeasure (Ioc (0 : ℝ) (1 / (K : ℝ))) := by
    rw [← gaussMeasure_inter_unit {x : ℝ | K ≤ digit x 0}, Set.inter_comm,
      inter_digit_ge_eq_Ioc hK]
  have hval : (Erdos1002.gaussMeasure (Ioc (0 : ℝ) (1 / (K : ℝ)))).toReal
      = (Real.log (1 + 1 / (K : ℝ)) - Real.log (1 + 0)) / Real.log 2 :=
    Erdos1002.gaussMeasure_real_Ioc le_rfl (by positivity)
      (by rw [div_le_one hK0]; exact_mod_cast hK)
  rw [hswap, hval]
  simp

/-! ## What this does and does not supply

The band-mass input of
`Kwon1002.CovarianceChain.truncatedMark_sub_lipTrunc_L1_of_band` is a bound on

`vol{α ∈ (0,1) : (1−h)εL < a_{j+1}(α)·W(θ_j(α)) ≤ εL}`,

a statement about the **joint** law of `(a_{j+1}, θ_j)` under Lebesgue measure
on `(0,1)`, at a single level `j`.  The local law proved here is the marginal
digit law under the **stationary** Gauss measure.  It is the missing analytic
ingredient — with the stationary law the band mass splits as
`∑_a γ{a₁ = a} · |{θ : (1−h)εL < a·W(θ) ≤ εL}|`, and the `a^{-2}` decay that
`gaussMeasure_real_digit_zero` makes exact is what turns that sum into
`o(1/(εL))`, which the `2/A`-shaped tails of `DigitTail.lean` cannot do
(finding F7).  What is still missing is the bridge from the level-`j` Lebesgue
law to the stationary law, which is §4's business and is gated by
Proposition 4.1's equidistribution of `θ_j`.  Recorded, not hidden. -/

end

end DigitLocalLaw

end Kwon1002
