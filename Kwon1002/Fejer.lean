import Kwon1002.Prop4Final
import Kwon1002.IntervalClass

/-!
# The Fejér kernel, and the trigonometric approximation of interval indicators

Mathlib carries **no** summability kernel of positive type: `Mathlib/Analysis/
Fourier/` has `AddCircle`, `FourierTransform`, `RiemannLebesgueLemma`,
`Inversion` and `PoissonSummation`, and a search of the whole library for
`Fejer`/`Fejér` returns nothing.  Every §5 residual of this development that
still funnels through "put the indicator of `B` into the symbol class `P_D(L)`
of display (24)" needs such a kernel, so it is built here from scratch.

## What is proved

* `fejerKernel N θ = (1/(N+1))·|∑_{k=0}^{N} e(kθ)|²`, rendered as the
  normalized squared modulus so that **nonnegativity is definitional**;
* `fejerKernel_eq_sum`, the Fourier expansion
  `F_N(θ) = Σ_{|v| ≤ N} (1 − |v|/(N+1)) e(vθ)` of the manuscript, resting on
  the combinatorial identity `sum_sq_diff` (the number of ordered pairs in
  `[0,N]²` with difference `v` is `N+1−|v|`);
* `fejerKernel_closed_form`, `F_N(θ) = (1/(N+1))·(sin(π(N+1)θ)/sin(πθ))²`;
* `integral_fejerKernel`, total mass `1` on the fundamental cell;
* `fejerKernel_le_of_mem`, the concentration bound
  `F_N(θ) ≤ 1/(4(N+1)·d(θ)²)` with `d(θ) = min(θ, 1−θ)` the distance to `ℤ`.

## Where this sits

The module is placed just above `Prop4Final` and `IntervalClass` so that every
consumer of the Jackson step (`TupleFinal`, `JacksonGate`, `FiveFinal`,
`CovarianceChain`, `CorFinal`) can import it without a cycle.  `torusChar_add`,
`norm_torusChar` and `torusChar_zero` are *not* redeclared: they already live
in `MonomialCore`, `Prop42` and `Prop4Final` and are used from there.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002
namespace Fejer

noncomputable section

/-! ## Part 0, the character toolkit

`torusChar_add`, `norm_torusChar` and `torusChar_zero` already exist in the
tree (`MonomialCore`, `Prop42`, `Prop4Final`); only the conjugation law is new.
-/

open MonomialCore (torusChar_add)

lemma torusChar_neg (t : ℝ) : torusChar (-t) = (starRingEnd ℂ) (torusChar t) := by
  unfold torusChar
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ))
      = -(((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    show (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

/-! ## Part 1, the counting identity behind the Fejér weights -/

/-- The number of ordered pairs `(j,k) ∈ [0,N]²` with `j - k = v` is `N+1-|v|`. -/
lemma card_pairs_diff (N : ℕ) {v : ℤ} (hv : v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    ((Finset.Icc (0 : ℤ) (N : ℤ)).filter (fun k => -k ≤ v ∧ v ≤ (N : ℤ) - k)).card
      = N + 1 - v.natAbs := by
  simp only [Finset.mem_Icc] at hv
  have hset : ((Finset.Icc (0 : ℤ) (N : ℤ)).filter (fun k => -k ≤ v ∧ v ≤ (N : ℤ) - k))
      = Finset.Icc (max 0 (-v)) (min (N : ℤ) ((N : ℤ) - v)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, by linarith, by linarith⟩
  rw [hset, Int.card_Icc]
  rcases le_or_gt 0 v with h | h
  · rw [max_eq_left (by omega), min_eq_right (by omega)]
    have : v.natAbs = v.toNat := by omega
    omega
  · rw [max_eq_right (by omega), min_eq_left (by omega)]
    omega

/-- **The grouping identity.**  Summing `g (j - k)` over the square `[0,N]²`
groups into a sum over the differences `v`, each weighted by the number
`N + 1 - |v|` of pairs realizing it.  This is the combinatorial content of the
Fejér weights. -/
lemma sum_sq_diff {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℤ → M) :
    ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), g (j - k)
      = ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (N + 1 - v.natAbs) • g v := by
  classical
  rw [Finset.sum_comm]
  have hstep : ∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ),
      ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), g (j - k)
        = ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            if -k ≤ v ∧ v ≤ (N : ℤ) - k then g v else 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hmap : (Finset.Icc (-k) ((N : ℤ) - k)).map (addRightEmbedding k)
        = Finset.Icc (0 : ℤ) (N : ℤ) := by
      rw [Finset.map_add_right_Icc]; congr 1 <;> ring
    have h1 : ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), g (j - k)
        = ∑ v ∈ Finset.Icc (-k) ((N : ℤ) - k), g v := by
      rw [← hmap, Finset.sum_map]
      exact Finset.sum_congr rfl fun v _ => by simp [addRightEmbedding]
    have hfil : (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
        (fun v => -k ≤ v ∧ v ≤ (N : ℤ) - k) = Finset.Icc (-k) ((N : ℤ) - k) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [h1, ← hfil, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_pairs_diff N hv]

/-! ## Part 2, the kernel -/

/-- `∑_{k=0}^{N} e(kθ)`, the Dirichlet-type partial sum whose squared modulus
is the Fejér kernel. -/
def charSum (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), torusChar ((k : ℝ) * θ)

/-- **The Fejér kernel** `F_N(θ) = (1/(N+1))·|∑_{k=0}^{N} e(kθ)|²`.

Rendered as the normalized squared modulus rather than as its Fourier
expansion, so that nonnegativity is definitional; `fejerKernel_eq_sum` proves
the expansion `Σ_{|v| ≤ N} (1 − |v|/(N+1)) e(vθ)` of the manuscript, and
`fejerKernel_closed_form` the closed form. -/
def fejerKernel (N : ℕ) (θ : ℝ) : ℝ := ‖charSum N θ‖ ^ 2 / ((N : ℝ) + 1)

/-- The Fejér weight `1 − |v|/(N+1)` of frequency `v`. -/
def fejerWeight (N : ℕ) (v : ℤ) : ℝ := 1 - (v.natAbs : ℝ) / ((N : ℝ) + 1)

lemma fejerKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ fejerKernel N θ := by
  unfold fejerKernel
  positivity

lemma fejerWeight_nonneg {N : ℕ} {v : ℤ} (hv : v.natAbs ≤ N) : 0 ≤ fejerWeight N v := by
  unfold fejerWeight
  rw [sub_nonneg, div_le_one (by positivity)]
  exact_mod_cast Nat.cast_le.mpr hv |>.trans (by linarith)

lemma fejerWeight_le_one (N : ℕ) (v : ℤ) : fejerWeight N v ≤ 1 := by
  unfold fejerWeight
  have : (0 : ℝ) ≤ (v.natAbs : ℝ) / ((N : ℝ) + 1) := by positivity
  linarith

lemma fejerWeight_eq_natSub {N : ℕ} {v : ℤ} (hv : v.natAbs ≤ N) :
    fejerWeight N v = ((N + 1 - v.natAbs : ℕ) : ℝ) / ((N : ℝ) + 1) := by
  unfold fejerWeight
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hN]
  have hcast : ((N + 1 - v.natAbs : ℕ) : ℝ) = ((N : ℝ) + 1) - (v.natAbs : ℝ) := by
    have : v.natAbs ≤ N + 1 := hv.trans (Nat.le_succ N)
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast]
  field_simp

/-- **The Fourier expansion of the Fejér kernel**, display form
`F_N(θ) = Σ_{|v| ≤ N} (1 − |v|/(N+1)) e(vθ)`. -/
theorem fejerKernel_eq_sum (N : ℕ) (θ : ℝ) :
    ((fejerKernel N θ : ℝ) : ℂ)
      = ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ((fejerWeight N v : ℝ) : ℂ) * torusChar ((v : ℝ) * θ) := by
  have hN : ((N : ℂ) + 1) ≠ 0 := by
    have : ((N : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast fun h => this (by exact_mod_cast h)
  have hsq : ((‖charSum N θ‖ ^ 2 : ℝ) : ℂ) = charSum N θ * (starRingEnd ℂ) (charSum N θ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hexp : charSum N θ * (starRingEnd ℂ) (charSum N θ)
      = ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ),
          torusChar (((j - k : ℤ) : ℝ) * θ) := by
    unfold charSum
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← torusChar_neg, ← MonomialCore.torusChar_add]
    congr 1
    push_cast
    ring
  have hgroup := sum_sq_diff (M := ℂ) N (fun v => torusChar ((v : ℝ) * θ))
  unfold fejerKernel
  rw [Complex.ofReal_div, hsq, hexp, hgroup]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [Finset.mem_Icc] at hv
  have hvN : v.natAbs ≤ N := by omega
  rw [nsmul_eq_mul, fejerWeight_eq_natSub hvN]
  push_cast
  field_simp

/-! ## Part 3, the closed form, the total mass, and the concentration -/

lemma torusChar_pow (t : ℝ) (k : ℕ) : torusChar ((k : ℝ) * t) = torusChar t ^ k := by
  induction k with
  | zero => simp [Prop4Final.torusChar_zero]
  | succ k ih =>
      rw [pow_succ, ← ih, ← MonomialCore.torusChar_add]
      congr 1
      push_cast
      ring

lemma charSum_eq_range (N : ℕ) (θ : ℝ) :
    charSum N θ = ∑ k ∈ Finset.range (N + 1), torusChar ((k : ℝ) * θ) := by
  classical
  unfold charSum
  have hset : Finset.Icc (0 : ℤ) (N : ℤ) = (Finset.range (N + 1)).image (fun k : ℕ => (k : ℤ)) := by
    ext v
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨v.toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [hset, Finset.sum_image (by intro a _ b _ h; simpa using h)]
  exact Finset.sum_congr rfl fun k _ => by norm_num

lemma norm_torusChar_sub_one (t : ℝ) : ‖torusChar t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have h : torusChar t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold torusChar; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi * t) / 2 = Real.pi * t by ring, Real.norm_eq_abs, abs_mul]
  norm_num

lemma torusChar_ne_one_of_sin {θ : ℝ} (h : Real.sin (Real.pi * θ) ≠ 0) : torusChar θ ≠ 1 := by
  intro hc
  have := norm_torusChar_sub_one θ
  rw [hc, sub_self, norm_zero] at this
  exact h (by simpa using (abs_eq_zero.mp (by linarith)))

/-- **The closed form** `F_N(θ) = (1/(N+1))·(sin(π(N+1)θ)/sin(πθ))²`, valid off
the zeros of `sin(πθ)`. -/
theorem fejerKernel_closed_form (N : ℕ) {θ : ℝ} (h : Real.sin (Real.pi * θ) ≠ 0) :
    fejerKernel N θ
      = Real.sin (Real.pi * (((N : ℝ) + 1) * θ)) ^ 2
          / (((N : ℝ) + 1) * Real.sin (Real.pi * θ) ^ 2) := by
  have hne := torusChar_ne_one_of_sin h
  have hgeom : charSum N θ = (torusChar θ ^ (N + 1) - 1) / (torusChar θ - 1) := by
    rw [charSum_eq_range]
    simp_rw [torusChar_pow]
    exact geom_sum_eq hne (N + 1)
  have hpow : torusChar θ ^ (N + 1) = torusChar ((((N : ℝ) + 1)) * θ) := by
    rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, torusChar_pow]
  have hden : ‖torusChar θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := norm_torusChar_sub_one θ
  have hnum : ‖torusChar ((((N : ℝ) + 1)) * θ) - 1‖
      = 2 * |Real.sin (Real.pi * (((N : ℝ) + 1) * θ))| := norm_torusChar_sub_one _
  have hd0 : (0 : ℝ) < 2 * |Real.sin (Real.pi * θ)| := by
    have : 0 < |Real.sin (Real.pi * θ)| := abs_pos.mpr h
    linarith
  have hnorm : ‖charSum N θ‖
      = |Real.sin (Real.pi * (((N : ℝ) + 1) * θ))| / |Real.sin (Real.pi * θ)| := by
    rw [hgeom, norm_div, hpow, hnum, hden]
    rw [div_eq_div_iff (by linarith) (ne_of_gt (abs_pos.mpr h))]
    ring
  unfold fejerKernel
  rw [hnorm, div_pow, sq_abs, sq_abs]
  field_simp

/-! ### Total mass -/

lemma integrable_mode (v : ℤ) (w : ℂ) :
    IntegrableOn (fun θ : ℝ => w * torusChar ((v : ℝ) * θ)) (Ioo (0 : ℝ) 1) := by
  have hcont : Continuous fun θ : ℝ => w * torusChar ((v : ℝ) * θ) :=
    continuous_const.mul
      (Prop42.continuous_torusChar.comp (continuous_const.mul continuous_id))
  refine Measure.integrableOn_of_bounded (M := ‖w‖) (by simp [Real.volume_Ioo])
    hcont.measurable.aestronglyMeasurable ?_
  filter_upwards with θ
  rw [norm_mul, Prop42.norm_torusChar, mul_one]

/-- **The Fejér kernel has total mass one** on the fundamental cell. -/
theorem integral_fejerKernel (N : ℕ) : (∫ θ in Ioo (0 : ℝ) 1, fejerKernel N θ) = 1 := by
  classical
  have hC : ((∫ θ in Ioo (0 : ℝ) 1, fejerKernel N θ : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    have hpt : ∀ θ : ℝ, ((fejerKernel N θ : ℝ) : ℂ)
        = ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ((fejerWeight N v : ℝ) : ℂ) * torusChar ((v : ℝ) * θ) :=
      fun θ => fejerKernel_eq_sum N θ
    simp only [hpt]
    rw [integral_finset_sum _ (fun v _ => integrable_mode v _)]
    have hterm : ∀ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (∫ θ in Ioo (0 : ℝ) 1, ((fejerWeight N v : ℝ) : ℂ) * torusChar ((v : ℝ) * θ))
          = if v = 0 then ((fejerWeight N v : ℝ) : ℂ) else 0 := by
      intro v _
      rw [integral_const_mul, Prop4Final.integral_torusChar_mode]
      by_cases hv : v = 0 <;> simp [hv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.Icc (-(N : ℤ)) (N : ℤ)) (0 : ℤ)]
    have h0 : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp
    rw [if_pos h0]
    simp [fejerWeight]
  exact_mod_cast hC

/-! ### Concentration away from the origin -/

/-- `|sin(πθ)| ≥ 2·dist(θ, ℤ)` on the fundamental cell. -/
lemma two_mul_min_le_sin {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    2 * min θ (1 - θ) ≤ Real.sin (Real.pi * θ) := by
  have hpi := Real.pi_pos
  rcases le_or_gt θ (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]
    have hx : Real.pi * θ ≤ Real.pi / 2 := by nlinarith
    have := Real.mul_le_sin (x := Real.pi * θ) (by positivity) hx
    calc 2 * θ = 2 / Real.pi * (Real.pi * θ) := by field_simp
      _ ≤ _ := this
  · rw [min_eq_right (by linarith)]
    have hsym : Real.sin (Real.pi * θ) = Real.sin (Real.pi * (1 - θ)) := by
      rw [show Real.pi * (1 - θ) = Real.pi - Real.pi * θ by ring, Real.sin_pi_sub]
    rw [hsym]
    have hx : Real.pi * (1 - θ) ≤ Real.pi / 2 := by nlinarith
    have := Real.mul_le_sin (x := Real.pi * (1 - θ)) (by nlinarith) hx
    calc 2 * (1 - θ) = 2 / Real.pi * (Real.pi * (1 - θ)) := by field_simp
      _ ≤ _ := this

/-- **Concentration.**  Off a neighbourhood of the origin the Fejér kernel is
`O(1/(N·d²))`, where `d = dist(θ, ℤ)`. -/
theorem fejerKernel_le_of_mem (N : ℕ) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    fejerKernel N θ ≤ 1 / (4 * ((N : ℝ) + 1) * (min θ (1 - θ)) ^ 2) := by
  have hd0 : 0 < min θ (1 - θ) := lt_min h0 (by linarith)
  have hsin := two_mul_min_le_sin h0 h1
  have hspos : 0 < Real.sin (Real.pi * θ) := lt_of_lt_of_le (by linarith) hsin
  rw [fejerKernel_closed_form N (ne_of_gt hspos)]
  have hsq : (2 * min θ (1 - θ)) ^ 2 ≤ Real.sin (Real.pi * θ) ^ 2 := by
    have h2 : 0 ≤ 2 * min θ (1 - θ) := by linarith
    nlinarith
  have hnum : Real.sin (Real.pi * (((N : ℝ) + 1) * θ)) ^ 2 ≤ 1 := by
    have := Real.sin_sq_le_one (Real.pi * (((N : ℝ) + 1) * θ))
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  have h4 : 4 * (min θ (1 - θ)) ^ 2 ≤ Real.sin (Real.pi * θ) ^ 2 := by nlinarith [hsq]
  calc Real.sin (Real.pi * (((N : ℝ) + 1) * θ)) ^ 2
          * (4 * ((N : ℝ) + 1) * (min θ (1 - θ)) ^ 2)
      ≤ 1 * (4 * ((N : ℝ) + 1) * (min θ (1 - θ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = ((N : ℝ) + 1) * (4 * (min θ (1 - θ)) ^ 2) := by ring
    _ ≤ ((N : ℝ) + 1) * Real.sin (Real.pi * θ) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (le_of_lt hNpos)
    _ = 1 * (((N : ℝ) + 1) * Real.sin (Real.pi * θ) ^ 2) := by ring

end

end Fejer
end Kwon1002
