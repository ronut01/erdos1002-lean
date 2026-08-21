import Kwon1002.Prop4Final
import Kwon1002.CharacterReduction
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
  `F_N(θ) ≤ 1/(4(N+1)·d(θ)²)` with `d(θ) = min(θ, 1−θ)` the distance to `ℤ`;
* `fejerPoly`, the Fejér mean, *defined by its coefficient list* so that
  display (24)'s `ℓ¹` budget is read off the definition, with the convolution
  identity `fejerPoly_eq_conv` proved rather than assumed;
* `fejerCoeff_l1_le` and `tsum_norm_fejerCoeff`, the `ℓ¹` budget;
* `fejerPoly_L1_error_le`, the `L¹` approximation bound;
* `isInPD_fejerPoly`, membership of the resulting symbol in the class `P_D(L)`
  of display (24).

## The rate that is proved, and the rate that is classical

`fejerPoly_L1_error_le` bounds the `L¹` error by `M/(2(N+1)s²) + 2M·β(s)`,
where `β(s)` is the measure of the set of points at which `f` moves under some
translation of size `≤ s`.  For an indicator with `m` jumps `β(s) = O(m·s)`,
and optimizing gives `O(m^{2/3}·N^{-1/3})`.

That is **weaker than the classical rates** and deliberately so: the classical
`O(1/N)` is Jackson's, obtained from the *fourth* power of the Dirichlet
kernel, whose first moment `∫|t|J_N(t)dt` is `O(1/N)`; the Fejér kernel itself
only gives `O(log N/N)`, because `∫|t|F_N(t)dt ≍ log N/N` — its `1/(N t²)`
tail has a logarithmically divergent first moment.  Both of those rates need a
Fubini interchange against the modulus of continuity of `f` in `L¹`.  The
bound proved here avoids the interchange entirely (at a good point the
integrand *vanishes* on the peak of the kernel, so one constant bound
suffices), and the loss costs nothing downstream: the residual it feeds needs
`η_L = O(L^{-2})` from a symbol of degree `L^{D'}`, and `D'` — the class
constant of display (24) — is free and *separate* from the `D` of the digit
cut `A_L = L^D`.  A cube-root rate at degree `L^{D'}` is `L^{-D'/3}`, so any
`D' > 6` clears the budget.

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

/-! ## Part 4, the Fejér mean

The symbols the Jackson step has to produce are *trigonometric polynomials*,
and display (24) budgets them by the `ℓ¹` norm of their coefficients.  So the
Fejér mean is defined here by its coefficient list, and the convolution
identity `fejerPoly_eq_conv` is a theorem: that way the `ℓ¹` bound is read off
the definition and the approximation property off the kernel.
-/

/-- A measurable, `1`-periodic, `M`-bounded symbol on the line: the shape every
`θ`-section indicator of this development takes. -/
structure IsPerBdd (f : ℝ → ℂ) (M : ℝ) : Prop where
  meas : Measurable f
  per : Function.Periodic f 1
  bdd : ∀ x, ‖f x‖ ≤ M

lemma IsPerBdd.nonneg {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) : 0 ≤ M :=
  le_trans (norm_nonneg _) (hf.bdd 0)

/-- Translation invariance of the integral over the fundamental cell, for a
`1`-periodic integrand. -/
lemma integral_periodic_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Function.Periodic g 1) (θ : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, g (θ - t)) = ∫ t in Ioo (0 : ℝ) 1, g t := by
  have hIoo : ∀ h : ℝ → E, (∫ t in Ioo (0 : ℝ) 1, h t) = ∫ t in (0 : ℝ)..1, h t := by
    intro h
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hIoo, hIoo, intervalIntegral.integral_comp_sub_left g θ, sub_zero]
  have := hg.intervalIntegral_add_eq (θ - 1) 0
  rw [sub_add_cancel, zero_add] at this
  exact this

lemma integrableOn_perBdd_mul_char {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (θ c : ℝ) :
    IntegrableOn (fun t : ℝ => f (θ - t) * torusChar (c * t)) (Ioo (0 : ℝ) 1) := by
  have hcont : Measurable fun t : ℝ => f (θ - t) * torusChar (c * t) :=
    (hf.meas.comp (measurable_const.sub measurable_id)).mul
      (Prop42.continuous_torusChar.measurable.comp (measurable_const.mul measurable_id))
  refine Measure.integrableOn_of_bounded (M := M) (by simp [Real.volume_Ioo])
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  rw [norm_mul, Prop42.norm_torusChar, mul_one]
  exact hf.bdd _

/-- The `v`-th Fourier coefficient on the fundamental cell. -/
def fourierCoeff1 (f : ℝ → ℂ) (v : ℤ) : ℂ :=
  ∫ t in Ioo (0 : ℝ) 1, f t * torusChar (-((v : ℝ) * t))

/-- **The Fejér mean**, defined by its coefficient list: the trigonometric
polynomial `Σ_{|v| ≤ N} (1 − |v|/(N+1))·f̂(v)·e(vθ)` of degree at most `N`. -/
def fejerPoly (N : ℕ) (f : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((fejerWeight N v : ℝ) : ℂ) * fourierCoeff1 f v * torusChar ((v : ℝ) * θ)

lemma norm_fourierCoeff1_le {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (v : ℤ) :
    ‖fourierCoeff1 f v‖ ≤ M := by
  unfold fourierCoeff1
  have hb : ∀ t : ℝ, ‖f t * torusChar (-((v : ℝ) * t))‖ ≤ M := by
    intro t
    rw [norm_mul, Prop42.norm_torusChar, mul_one]
    exact hf.bdd _
  have hvol : (volume : Measure ℝ).real (Ioo (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioo]
  have h := norm_setIntegral_le_of_norm_le_const (C := M) (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := 0) (b := 1)) (fun t _ => hb t)
  rwa [hvol, mul_one] at h

/-- **The convolution identity.**  The Fejér mean is the average of `f` against
the Fejér kernel. -/
theorem fejerPoly_eq_conv {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (N : ℕ) (θ : ℝ) :
    fejerPoly N f θ = ∫ t in Ioo (0 : ℝ) 1, f (θ - t) * ((fejerKernel N t : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, f (θ - t) * ((fejerKernel N t : ℝ) : ℂ)
      = ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ((fejerWeight N v : ℝ) : ℂ) * torusChar ((v : ℝ) * θ)
            * (f (θ - t) * torusChar (-((v : ℝ) * (θ - t)))) := by
    intro t
    rw [fejerKernel_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hchar : torusChar ((v : ℝ) * t)
        = torusChar ((v : ℝ) * θ) * torusChar (-((v : ℝ) * (θ - t))) := by
      rw [← MonomialCore.torusChar_add]
      congr 1
      ring
    rw [hchar]
    ring
  simp only [hpt]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_const_mul]
    have hper : Function.Periodic (fun s : ℝ => f s * torusChar (-((v : ℝ) * s))) 1 := by
      intro s
      show f (s + 1) * torusChar (-((v : ℝ) * (s + 1)))
          = f s * torusChar (-((v : ℝ) * s))
      rw [hf.per s]
      congr 1
      rw [show -((v : ℝ) * (s + 1)) = -((v : ℝ) * s) + ((-v : ℤ) : ℝ) by push_cast; ring]
      exact torusChar_add_int _ _
    rw [integral_periodic_shift hper θ]
    unfold fourierCoeff1
    ring
  · intro v _
    have hshift : (fun t : ℝ => ((fejerWeight N v : ℝ) : ℂ) * torusChar ((v : ℝ) * θ)
        * (f (θ - t) * torusChar (-((v : ℝ) * (θ - t)))))
        = fun t : ℝ => (((fejerWeight N v : ℝ) : ℂ) * torusChar ((v : ℝ) * θ)
            * torusChar (-((v : ℝ) * θ))) * (f (θ - t) * torusChar ((v : ℝ) * t)) := by
      funext t
      rw [show -((v : ℝ) * (θ - t)) = -((v : ℝ) * θ) + (v : ℝ) * t by ring,
        MonomialCore.torusChar_add]
      ring
    rw [hshift]
    exact (integrableOn_perBdd_mul_char hf θ (v : ℝ)).const_mul _

lemma continuous_charSum (N : ℕ) : Continuous (charSum N) := by
  unfold charSum
  exact continuous_finset_sum _ fun k _ =>
    Prop42.continuous_torusChar.comp (continuous_const.mul continuous_id)

lemma continuous_fejerKernel (N : ℕ) : Continuous (fejerKernel N) := by
  unfold fejerKernel
  exact ((continuous_charSum N).norm.pow 2).div_const _

lemma integrableOn_fejerKernel (N : ℕ) :
    IntegrableOn (fejerKernel N) (Ioo (0 : ℝ) 1) :=
  ((continuous_fejerKernel N).integrableOn_Ioc (a := (0 : ℝ)) (b := 1)).mono_set
    Ioo_subset_Ioc_self

/-- The Fejér mean is bounded by the same constant as `f`. -/
theorem norm_fejerPoly_le {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (N : ℕ) (θ : ℝ) :
    ‖fejerPoly N f θ‖ ≤ M := by
  rw [fejerPoly_eq_conv hf N θ]
  set g : ℝ → ℂ := fun t => f (θ - t) * ((fejerKernel N t : ℝ) : ℂ) with hg
  have hmeasg : Measurable g :=
    (hf.meas.comp (measurable_const.sub measurable_id)).mul
      (Complex.continuous_ofReal.comp (continuous_fejerKernel N)).measurable
  have hbdd : ∀ t : ℝ, ‖g t‖ ≤ M * fejerKernel N t := by
    intro t
    rw [hg]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerKernel_nonneg N t)]
    exact mul_le_mul_of_nonneg_right (hf.bdd _) (fejerKernel_nonneg N t)
  have hintF : IntegrableOn (fun t : ℝ => M * fejerKernel N t) (Ioo (0 : ℝ) 1) :=
    (integrableOn_fejerKernel N).const_mul M
  have hintg : IntegrableOn g (Ioo (0 : ℝ) 1) :=
    Integrable.mono' hintF hmeasg.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  calc ‖∫ t in Ioo (0 : ℝ) 1, g t‖
      ≤ ∫ t in Ioo (0 : ℝ) 1, ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioo (0 : ℝ) 1, M * fejerKernel N t :=
        integral_mono hintg.norm hintF (fun t => hbdd t)
    _ = M * ∫ t in Ioo (0 : ℝ) 1, fejerKernel N t := integral_const_mul _ _
    _ = M := by rw [integral_fejerKernel]; ring

/-- **The `ℓ¹` budget of the Fejér mean.**  The coefficient list of
`fejerPoly N f` has `ℓ¹` norm at most `(2N+1)·M`.  This is the crude bound,
uniform over all `M`-bounded symbols; `fejerCoeff_l1_interval_le` sharpens it
to `O(M + log N)` for an interval indicator, which is what display (24)'s
budget actually needs. -/
theorem fejerCoeff_l1_le {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (N : ℕ) :
    ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖((fejerWeight N v : ℝ) : ℂ) * fourierCoeff1 f v‖ ≤ (2 * (N : ℝ) + 1) * M := by
  have hcard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]; omega
  have hterm : ∀ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ‖((fejerWeight N v : ℝ) : ℂ) * fourierCoeff1 f v‖ ≤ M := by
    intro v hv
    simp only [Finset.mem_Icc] at hv
    have hvN : v.natAbs ≤ N := by omega
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerWeight_nonneg hvN)]
    calc fejerWeight N v * ‖fourierCoeff1 f v‖
        ≤ 1 * ‖fourierCoeff1 f v‖ :=
          mul_le_mul_of_nonneg_right (fejerWeight_le_one N v) (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact norm_fourierCoeff1_le hf v
  calc ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ‖((fejerWeight N v : ℝ) : ℂ) * fourierCoeff1 f v‖
      ≤ ∑ _v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), M := Finset.sum_le_sum hterm
    _ = ((2 * N + 1 : ℕ) : ℝ) * M := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = (2 * (N : ℝ) + 1) * M := by push_cast; ring

/-! ## Part 5, the `L¹` error of the Fejér mean

The estimate is run against an explicit **good set** `G`: the points of the
fundamental cell at which `f` does not move under translations of size at most
`s`.  For an indicator this is the complement of the `s`-neighbourhood of the
jump set, so `volume (Ioo 0 1 \ G)` is `O(m·s)` for an indicator with `m`
jumps, and the bound below is then optimized in `s`.
-/

lemma integrableOn_const_of_ne_top {S : Set ℝ} (hS : volume S ≠ ⊤) (c : ℝ) :
    IntegrableOn (fun _ : ℝ => c) S :=
  Measure.integrableOn_of_bounded (M := ‖c‖) hS aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => le_rfl)

lemma continuous_fejerPoly (N : ℕ) (f : ℝ → ℂ) : Continuous (fejerPoly N f) := by
  unfold fejerPoly
  exact continuous_finset_sum _ fun v _ =>
    continuous_const.mul (Prop42.continuous_torusChar.comp (continuous_const.mul continuous_id))

/-- The Fejér mean minus the function, as one average against the kernel.
Uses only that the kernel has unit mass. -/
theorem fejerPoly_sub_eq {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (N : ℕ) (θ : ℝ) :
    fejerPoly N f θ - f θ
      = ∫ t in Ioo (0 : ℝ) 1, (f (θ - t) - f θ) * ((fejerKernel N t : ℝ) : ℂ) := by
  have hint1 : IntegrableOn (fun t : ℝ => f (θ - t) * ((fejerKernel N t : ℝ) : ℂ))
      (Ioo (0 : ℝ) 1) := by
    have hmeasg : Measurable fun t : ℝ => f (θ - t) * ((fejerKernel N t : ℝ) : ℂ) :=
      (hf.meas.comp (measurable_const.sub measurable_id)).mul
        (Complex.continuous_ofReal.comp (continuous_fejerKernel N)).measurable
    refine Integrable.mono' ((integrableOn_fejerKernel N).const_mul M)
      hmeasg.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerKernel_nonneg N t)]
    exact mul_le_mul_of_nonneg_right (hf.bdd _) (fejerKernel_nonneg N t)
  have hint2 : IntegrableOn (fun t : ℝ => f θ * ((fejerKernel N t : ℝ) : ℂ))
      (Ioo (0 : ℝ) 1) := by
    have : IntegrableOn (fun t : ℝ => ((fejerKernel N t : ℝ) : ℂ)) (Ioo (0 : ℝ) 1) :=
      (integrableOn_fejerKernel N).ofReal
    exact this.const_mul _
  have hsplit : (∫ t in Ioo (0 : ℝ) 1, (f (θ - t) - f θ) * ((fejerKernel N t : ℝ) : ℂ))
      = (∫ t in Ioo (0 : ℝ) 1, f (θ - t) * ((fejerKernel N t : ℝ) : ℂ))
        - ∫ t in Ioo (0 : ℝ) 1, f θ * ((fejerKernel N t : ℝ) : ℂ) := by
    rw [← integral_sub hint1 hint2]
    exact setIntegral_congr_fun measurableSet_Ioo fun t _ => by ring
  rw [hsplit, ← fejerPoly_eq_conv hf N θ, integral_const_mul,
    show (∫ a in Ioo (0 : ℝ) 1, ((fejerKernel N a : ℝ) : ℂ))
        = ((∫ a in Ioo (0 : ℝ) 1, fejerKernel N a : ℝ) : ℂ) from integral_complex_ofReal,
    integral_fejerKernel]
  simp

/-- **The pointwise Fejér estimate at a good point.**  If `f` is constant under
all translations of size at most `s` around `θ`, then the Fejér mean at `θ` is
within `M/(2(N+1)s²)` of `f θ`.

The proof needs no tail integral: at a good `θ` the integrand *vanishes* on the
peak of the kernel, and on the rest of the cell the concentration bound caps
the kernel by `1/(4(N+1)s²)` — so a single constant bound suffices. -/
theorem norm_fejerPoly_sub_le_of_good {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (N : ℕ)
    {s : ℝ} (hs0 : 0 < s) {θ : ℝ}
    (hθ : ∀ t ∈ Ioo (0 : ℝ) 1, min t (1 - t) ≤ s → f (θ - t) = f θ) :
    ‖fejerPoly N f θ - f θ‖ ≤ M / (2 * ((N : ℝ) + 1) * s ^ 2) := by
  rw [fejerPoly_sub_eq hf N θ]
  have hvol : (volume : Measure ℝ).real (Ioo (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioo]
  have hbd : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖(f (θ - t) - f θ) * ((fejerKernel N t : ℝ) : ℂ)‖ ≤ M / (2 * ((N : ℝ) + 1) * s ^ 2) := by
    intro t ht
    rcases le_or_gt (min t (1 - t)) s with hnear | hfar
    · rw [hθ t ht hnear, sub_self, zero_mul, norm_zero]
      have := hf.nonneg
      positivity
    · have hk := fejerKernel_le_of_mem N ht.1 ht.2
      have hmin0 : 0 < min t (1 - t) := lt_min ht.1 (by linarith [ht.2])
      have hks : fejerKernel N t ≤ 1 / (4 * ((N : ℝ) + 1) * s ^ 2) := by
        refine hk.trans ?_
        have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hgap : 0 < (min t (1 - t) - s) * (min t (1 - t) + s) :=
          mul_pos (by linarith) (by linarith)
        nlinarith [hgap]
      have hnum : ‖f (θ - t) - f θ‖ ≤ 2 * M := by
        refine (norm_sub_le _ _).trans ?_
        have := hf.bdd (θ - t); have := hf.bdd θ; linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fejerKernel_nonneg N t)]
      have hM := hf.nonneg
      calc ‖f (θ - t) - f θ‖ * fejerKernel N t
          ≤ (2 * M) * (1 / (4 * ((N : ℝ) + 1) * s ^ 2)) :=
            mul_le_mul hnum hks (fejerKernel_nonneg N t) (by linarith)
        _ = M / (2 * ((N : ℝ) + 1) * s ^ 2) := by
            have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
            field_simp
            ring
  have h := norm_setIntegral_le_of_norm_le_const
    (C := M / (2 * ((N : ℝ) + 1) * s ^ 2)) (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := 0) (b := 1)) hbd
  rwa [hvol, mul_one] at h

/-- **The `L¹` error bound.**  Away from a bad set of measure `β` the Fejér
mean of an `M`-bounded periodic symbol is within `M/(2(N+1)s²)` of it, so the
`L¹` error over the fundamental cell is at most `M/(2(N+1)s²) + 2Mβ`.

Optimizing in `s` at `β = K·s` gives an `L¹` error `O((M + MK)·N^{-1/3})`; that
rate, not the classical `O(1/N)`, is what is proved here.  See the module note
on the rate. -/
theorem fejerPoly_L1_error_le {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (N : ℕ)
    {s : ℝ} (hs0 : 0 < s) (G : Set ℝ) (hGmeas : MeasurableSet G) (_hGsub : G ⊆ Ioo (0 : ℝ) 1)
    (hG : ∀ θ ∈ G, ∀ t ∈ Ioo (0 : ℝ) 1, min t (1 - t) ≤ s → f (θ - t) = f θ) :
    (∫ θ in Ioo (0 : ℝ) 1, ‖fejerPoly N f θ - f θ‖)
      ≤ M / (2 * ((N : ℝ) + 1) * s ^ 2)
        + 2 * M * (volume (Ioo (0 : ℝ) 1 \ G)).toReal := by
  classical
  set A : ℝ := M / (2 * ((N : ℝ) + 1) * s ^ 2) with hA
  have hM := hf.nonneg
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set bad : Set ℝ := Ioo (0 : ℝ) 1 \ G with hbad
  have hbadmeas : MeasurableSet bad := measurableSet_Ioo.diff hGmeas
  set u : ℝ → ℝ := fun θ => A + 2 * M * bad.indicator (fun _ => (1 : ℝ)) θ with hu
  have hmeasF : Measurable fun θ : ℝ => ‖fejerPoly N f θ - f θ‖ :=
    (((continuous_fejerPoly N f).measurable).sub hf.meas).norm
  have hle : ∀ θ ∈ Ioo (0 : ℝ) 1, ‖fejerPoly N f θ - f θ‖ ≤ u θ := by
    intro θ hθ
    by_cases hmem : θ ∈ G
    · have := norm_fejerPoly_sub_le_of_good hf N hs0 (hG θ hmem)
      have hind : (0 : ℝ) ≤ 2 * M * bad.indicator (fun _ => (1 : ℝ)) θ := by
        refine mul_nonneg (by linarith) ?_
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) θ
      rw [hu]
      simp only
      linarith
    · have hb : θ ∈ bad := ⟨hθ, hmem⟩
      have hnum : ‖fejerPoly N f θ - f θ‖ ≤ 2 * M := by
        refine (norm_sub_le _ _).trans ?_
        have := norm_fejerPoly_le hf N θ; have := hf.bdd θ; linarith
      rw [hu]
      simp only [Set.indicator_of_mem hb]
      linarith
  have hIoo_ne : volume (Ioo (0 : ℝ) 1) ≠ ⊤ := measure_Ioo_lt_top.ne
  have hcap_ne : volume (Ioo (0 : ℝ) 1 ∩ bad) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_Ioo_lt_top).ne
  have hindInt : IntegrableOn (fun θ : ℝ => bad.indicator (fun _ => (1 : ℝ)) θ)
      (Ioo (0 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := 1) hIoo_ne
      (measurable_const.indicator hbadmeas).aestronglyMeasurable ?_
    filter_upwards with θ
    by_cases h : θ ∈ bad <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hintu : IntegrableOn u (Ioo (0 : ℝ) 1) :=
    Integrable.add (integrableOn_const_of_ne_top hIoo_ne A) (hindInt.const_mul _)
  have hintF : IntegrableOn (fun θ : ℝ => ‖fejerPoly N f θ - f θ‖) (Ioo (0 : ℝ) 1) := by
    refine Integrable.mono' hintu hmeasF.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hle θ hθ
  have hmono : (∫ θ in Ioo (0 : ℝ) 1, ‖fejerPoly N f θ - f θ‖) ≤ ∫ θ in Ioo (0 : ℝ) 1, u θ := by
    refine setIntegral_mono_on hintF hintu measurableSet_Ioo hle
  refine hmono.trans (le_of_eq ?_)
  have hvol : (volume : Measure ℝ).real (Ioo (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioo]
  have hsub : Ioo (0 : ℝ) 1 ∩ bad = bad := Set.inter_eq_right.2 fun x hx => hx.1
  have h1 : (∫ _θ in Ioo (0 : ℝ) 1, A) = A := by
    rw [setIntegral_const, hvol, smul_eq_mul, one_mul]
  have h2 : (∫ θ in Ioo (0 : ℝ) 1, bad.indicator (fun _ => (1 : ℝ)) θ)
      = (volume bad).toReal := by
    rw [setIntegral_indicator hbadmeas, hsub, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [hu, integral_add (integrableOn_const_of_ne_top hIoo_ne A) (hindInt.const_mul _),
    h1, integral_const_mul, h2]

/-! ## Part 6, membership in the symbol class of display (24)

`Kwon1002/JacksonGate.lean` proves that an *indicator* cannot lie in `P_D(L)`
(members are trigonometric polynomials, hence continuous, hence constant if
two-valued).  Its approximants can, and that is what this part supplies: a
digit-indexed family of Fejér means, cut off above the digit `A`, is a member
of `P_{D}(L)` as soon as the degree and the total coefficient mass fit the
budget.

The two constants really are different, as `Kwon1002/OneLevelLaw.lean` records:
the `ℓ¹` sum of display (24) runs over **both** the digit and the frequency, so
a digit cut at `A_L = L^D` already spends the whole `L^D` allowance and the
approximant has to be placed in `P_{D'}(L)` for a strictly larger `D'`.  The
hypothesis `hbudget` below is exactly that accounting, written out.
-/

/-- The coefficient family of the Fejér mean, extended by zero off its degree
window. -/
def fejerCoeff (N : ℕ) (f : ℝ → ℂ) (v : ℤ) : ℂ :=
  if v.natAbs ≤ N then ((fejerWeight N v : ℝ) : ℂ) * fourierCoeff1 f v else 0

lemma fejerCoeff_eq_zero {N : ℕ} {f : ℝ → ℂ} {v : ℤ} (h : N < v.natAbs) :
    fejerCoeff N f v = 0 := by
  simp [fejerCoeff, Nat.not_le.mpr h]

lemma mem_Icc_iff_natAbs_le {N : ℕ} {v : ℤ} :
    v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ↔ v.natAbs ≤ N := by
  simp only [Finset.mem_Icc]; omega

/-- The Fejér mean *is* the trigonometric series of its coefficient family. -/
theorem tsum_fejerCoeff (N : ℕ) (f : ℝ → ℂ) (θ : ℝ) :
    ∑' v : ℤ, fejerCoeff N f v * torusChar ((v : ℝ) * θ) = fejerPoly N f θ := by
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) ?_]
  · unfold fejerPoly
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [fejerCoeff, if_pos (mem_Icc_iff_natAbs_le.mp hv)]
  · intro v hv
    rw [fejerCoeff_eq_zero (Nat.not_le.mp fun h => hv (mem_Icc_iff_natAbs_le.mpr h)), zero_mul]

/-- The `ℓ¹` mass of the coefficient family, as a `tsum`. -/
theorem tsum_norm_fejerCoeff {f : ℝ → ℂ} {M : ℝ} (hf : IsPerBdd f M) (N : ℕ) :
    ∑' v : ℤ, ‖fejerCoeff N f v‖ ≤ (2 * (N : ℝ) + 1) * M := by
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) ?_]
  · refine le_trans (le_of_eq ?_) (fejerCoeff_l1_le hf N)
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [fejerCoeff, if_pos (mem_Icc_iff_natAbs_le.mp hv)]
  · intro v hv
    rw [fejerCoeff_eq_zero (Nat.not_le.mp fun h => hv (mem_Icc_iff_natAbs_le.mpr h)), norm_zero]

/-- **The Jackson symbol lies in the class of display (24).**

`fun a θ => if a ≤ A then fejerPoly N (g a) θ else 0` is a member of
`P_D(L)` whenever

* the digit cut fits, `A ≤ L^D` (`hAle`);
* the degree fits, `N ≤ L^D` (`hNle`);
* the *total* coefficient mass over digits **and** frequencies fits,
  `(A+1)·(2N+1)·M ≤ L^D` (`hbudget`).

The third is the binding one, and it is why the class constant `D` here must
exceed the `D` of the digit cut `A_L = L^D`: at `A = L^D` the left side is
already `L^D·(2N+1)·M`. -/
theorem isInPD_fejerPoly (D L : ℝ) (A N : ℕ) (M : ℝ) (g : ℕ → ℝ → ℂ)
    (hg : ∀ a, IsPerBdd (g a) M)
    (hAle : (A : ℝ) ≤ L ^ D) (hNle : (N : ℝ) ≤ L ^ D)
    (hbudget : ((A : ℝ) + 1) * ((2 * (N : ℝ) + 1) * M) ≤ L ^ D) :
    IsInPD D L (fun a θ => if a ≤ A then fejerPoly N (g a) θ else 0) := by
  classical
  refine ⟨fun a v => if a ≤ A then fejerCoeff N (g a) v else 0, ?_, ?_, ?_, ?_⟩
  · intro a v ha
    have : ¬ a ≤ A := by
      intro h
      exact absurd (le_trans (by exact_mod_cast Nat.cast_le.mpr h) hAle) (not_le.mpr ha)
    simp [this]
  · intro a v hv
    have hvN : N < v.natAbs := by
      by_contra hc
      push_neg at hc
      have h1 : -(N : ℤ) ≤ v := by omega
      have h2 : v ≤ (N : ℤ) := by omega
      have hb : |(v : ℝ)| ≤ (N : ℝ) := by
        rw [abs_le]
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      linarith
    by_cases ha : a ≤ A
    · simp [ha, fejerCoeff_eq_zero hvN]
    · simp [ha]
  · -- the `ℓ¹` budget
    have hsupp : ∀ p : ℕ × ℤ,
        p ∉ (Finset.range (A + 1)) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ)) →
          ‖if p.1 ≤ A then fejerCoeff N (g p.1) p.2 else 0‖ = 0 := by
      rintro ⟨a, v⟩ hp
      simp only [Finset.mem_product, Finset.mem_range, not_and_or] at hp
      rcases hp with h | h
      · have : ¬ a ≤ A := by omega
        simp [this]
      · have hvN : N < v.natAbs := Nat.not_le.mp fun hc => h (mem_Icc_iff_natAbs_le.mpr hc)
        by_cases ha : a ≤ A <;> simp [ha, fejerCoeff_eq_zero hvN]
    rw [tsum_eq_sum hsupp, Finset.sum_product]
    have hrow : ∀ a ∈ Finset.range (A + 1),
        ∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ‖if a ≤ A then fejerCoeff N (g a) v else 0‖ ≤ (2 * (N : ℝ) + 1) * M := by
      intro a ha
      simp only [Finset.mem_range] at ha
      have haA : a ≤ A := by omega
      simp only [haA, if_pos]
      refine le_trans (le_of_eq ?_) (fejerCoeff_l1_le (hg a) N)
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [fejerCoeff, if_pos (mem_Icc_iff_natAbs_le.mp hv)]
    refine le_trans (Finset.sum_le_sum hrow) (le_trans (le_of_eq ?_) hbudget)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  · intro a θ
    by_cases ha : a ≤ A
    · simp only [ha, if_pos]
      rw [← tsum_fejerCoeff N (g a) θ]
    · simp [ha]

end

end Fejer

/-! ## The good set of a finite union of intervals

`fejerPoly_L1_error_le` above runs against an explicit good set: the points of
the fundamental cell at which the symbol does not move under translations of
size at most `s`.  This section builds one from a jump count, which is the step
`TupleFinal.goodSet_mark_factorization_intervals` records as the first of the
two instantiations it still needs.  It is stated in `namespace IntervalClass`,
where the class it consumes lives, and kept here because
`Kwon1002/IntervalClass.lean` sits below this module. -/

namespace IntervalClass

open scoped ENNReal

noncomputable section

/-- The two `s`-collars of an interval: the points within `s` of its infimum or
of its supremum.  For an unbounded or empty `I` the junk values of `sInf`/`sSup`
make this a harmless overestimate, because the corresponding branch of
`mem_collar_of_unstable` cannot fire. -/
def collar (s : ℝ) (I : Set ℝ) : Set ℝ :=
  Icc (sInf I - s) (sInf I + s) ∪ Icc (sSup I - s) (sSup I + s)

lemma measurableSet_collar (s : ℝ) (I : Set ℝ) : MeasurableSet (collar s I) :=
  (measurableSet_Icc).union measurableSet_Icc

lemma volume_collar_le (s : ℝ) (hs : 0 ≤ s) (I : Set ℝ) :
    volume (collar s I) ≤ ENNReal.ofReal (4 * s) := by
  refine le_trans (measure_union_le _ _) ?_
  rw [Real.volume_Icc, Real.volume_Icc,
    show sInf I + s - (sInf I - s) = 2 * s by ring,
    show sSup I + s - (sSup I - s) = 2 * s by ring,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The endpoint arithmetic.**  If membership in an order-convex `I` changes
under a shift of size at most `s`, the base point lies in one of the two
`s`-collars of `I`. -/
lemma mem_collar_of_unstable {I : Set ℝ} (hI : I.OrdConnected) {s θ u : ℝ}
    (hs : 0 ≤ s) (hu : |u - θ| ≤ s) (hne : ¬ (u ∈ I ↔ θ ∈ I)) : θ ∈ collar s I := by
  -- name the member `p` and the non-member `q`
  have hkey : ∀ p q : ℝ, p ∈ I → q ∉ I → |p - q| ≤ s → (θ = p ∨ θ = q) →
      θ ∈ collar s I := by
    intro p q hp hq hpq hθ
    have hps : p - q ≤ s := (le_abs_self _).trans hpq
    have hqp : q - p ≤ s := by
      have := neg_le_abs (p - q)
      linarith
    have hsplit : (∀ x ∈ I, q ≤ x) ∨ (∀ x ∈ I, x ≤ q) := by
      by_contra hc
      push_neg at hc
      obtain ⟨⟨x₁, hx₁, hlt₁⟩, ⟨x₂, hx₂, hlt₂⟩⟩ := hc
      exact hq (hI.out hx₁ hx₂ ⟨hlt₁.le, hlt₂.le⟩)
    rcases hsplit with hlow | hupp
    · have hbdd : BddBelow I := ⟨q, hlow⟩
      have hIne : I.Nonempty := ⟨p, hp⟩
      have hqa : q ≤ sInf I := le_csInf hIne hlow
      have hap : sInf I ≤ p := csInf_le hbdd hp
      refine Or.inl ?_
      rcases hθ with rfl | rfl
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    · have hbdd : BddAbove I := ⟨q, hupp⟩
      have hIne : I.Nonempty := ⟨p, hp⟩
      have hbq : sSup I ≤ q := csSup_le hIne hupp
      have hpb : p ≤ sSup I := le_csSup hbdd hp
      refine Or.inr ?_
      rcases hθ with rfl | rfl
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
  by_cases hθI : θ ∈ I
  · have huI : u ∉ I := fun h => hne (iff_of_true h hθI)
    refine hkey θ u hθI huI ?_ (Or.inl rfl)
    rw [abs_sub_comm]
    exact hu
  · have huI : u ∈ I := by
      by_contra h
      exact hne (iff_of_false h hθI)
    exact hkey u θ huI hθI hu (Or.inr rfl)

/-- **The good set of a finite union of intervals, with the wrap-around.**

For `B` a union of at most `m` intervals inside `(0,1)` and a shift budget
`s ≥ 0`, there is a measurable `G ⊆ (0,1)` on which membership in `B` is
insensitive to every shift of size at most `s` — and every such shift stays
inside `(0,1)`, which is what makes the periodised symbol of display (24) see
no wrap at `0` or `1` — with

`volume ((0,1) \ G) ≤ (4m + 2)·s`.

This is the input `Fejer.fejerPoly_L1_error_le` asks for: it turns a jump count
into a good set of the right measure, and `+2` is the price of the two
endpoints of the fundamental cell. -/
theorem exists_goodSet {m : ℕ} {B : Set ℝ} (hB : IsUnionOfIntervals m B)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ioo (0 : ℝ) 1 ∧
      (∀ θ ∈ G, ∀ u : ℝ, |u - θ| ≤ s → u ∈ Ioo (0 : ℝ) 1 ∧ (u ∈ B ↔ θ ∈ B)) ∧
      volume (Ioo (0 : ℝ) 1 \ G) ≤ ENNReal.ofReal ((4 * m + 2) * s) := by
  classical
  obtain ⟨t, hcard, hoc, hBeq⟩ := hB
  set Bad : Set ℝ := ⋃ I ∈ t, collar s I with hBadDef
  refine ⟨Ioo s (1 - s) \ Bad, ?_, ?_, ?_, ?_⟩
  · exact measurableSet_Ioo.diff
      (t.measurableSet_biUnion fun I _ => measurableSet_collar s I)
  · rintro θ ⟨hθ, -⟩
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  · rintro θ ⟨hθ, hθbad⟩ u hu
    have habs := abs_le.mp hu
    refine ⟨⟨by linarith [hθ.1, habs.1], by linarith [hθ.2, habs.2]⟩, ?_⟩
    by_contra hne
    -- some interval of the family is unstable at `θ`
    have hmem : ∀ I ∈ t, (u ∈ I ↔ θ ∈ I) := by
      intro I hI
      by_contra hIne
      exact hθbad (Set.mem_biUnion hI (mem_collar_of_unstable (hoc I hI) hs hu hIne))
    apply hne
    rw [hBeq]
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨I, hI, hxI⟩
      exact ⟨I, hI, (hmem I hI).mp hxI⟩
    · rintro ⟨I, hI, hxI⟩
      exact ⟨I, hI, (hmem I hI).mpr hxI⟩
  · have hsplit : Ioo (0 : ℝ) 1 \ (Ioo s (1 - s) \ Bad)
        ⊆ (Ioo (0 : ℝ) 1 \ Ioo s (1 - s)) ∪ Bad := by
      rintro x ⟨hx, hx2⟩
      by_cases hb : x ∈ Bad
      · exact Or.inr hb
      · exact Or.inl ⟨hx, fun hc => hx2 ⟨hc, hb⟩⟩
    have hedge : volume (Ioo (0 : ℝ) 1 \ Ioo s (1 - s)) ≤ ENNReal.ofReal (2 * s) := by
      have hsub : Ioo (0 : ℝ) 1 \ Ioo s (1 - s) ⊆ Icc 0 s ∪ Icc (1 - s) 1 := by
        rintro x ⟨hx, hx2⟩
        by_cases h : x ≤ s
        · exact Or.inl ⟨hx.1.le, h⟩
        · push_neg at h
          refine Or.inr ⟨?_, hx.2.le⟩
          by_contra hc
          push_neg at hc
          exact hx2 ⟨h, hc⟩
      refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
      rw [Real.volume_Icc, Real.volume_Icc,
        show (1 : ℝ) - (1 - s) = s by ring, show s - (0 : ℝ) = s by ring,
        ← ENNReal.ofReal_add hs hs]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hbad : volume Bad ≤ ENNReal.ofReal (4 * m * s) := by
      refine le_trans (measure_biUnion_finset_le _ _) ?_
      calc ∑ I ∈ t, volume (collar s I)
          ≤ ∑ _I ∈ t, ENNReal.ofReal (4 * s) :=
            Finset.sum_le_sum fun I _ => volume_collar_le s hs I
        _ = (t.card : ℝ≥0∞) * ENNReal.ofReal (4 * s) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (m : ℝ≥0∞) * ENNReal.ofReal (4 * s) := by
            exact mul_le_mul_right' (by exact_mod_cast hcard) _
        _ = ENNReal.ofReal (4 * m * s) := by
            rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 1
            ring
    refine le_trans (measure_mono hsplit) (le_trans (measure_union_le _ _) ?_)
    refine le_trans (add_le_add hedge hbad) ?_
    rw [← ENNReal.ofReal_add (by linarith) (mul_nonneg (by positivity) hs)]
    exact le_of_eq (by rw [show (2 : ℝ) * s + 4 * (m : ℝ) * s = (4 * (m : ℝ) + 2) * s by ring])

end

end IntervalClass

end Kwon1002
