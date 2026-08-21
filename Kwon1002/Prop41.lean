import Kwon1002.Section4
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scratch: Proposition 4.1 (Marked factorization), display (27)

Target: `Kwon1002.prop_4_1_marked_factorization` of `Kwon1002/Section4.lean`
(manuscript §4, display (27), proof on manuscript lines ≈ 340-404).

## What is proved here, and what is assumed

The manuscript's proof of Proposition 4.1 has two clearly separated halves.

1. **Analytic bookkeeping.**  Expand in digits and Fourier modes; the zero
   mode is handled by Lemma 3.2 across the gaps that (25) guarantees, and
   every nonzero mode is killed by the resonance argument (28)-(29) plus
   Lemmas 3.3/3.4.  Summing the polynomially many Fourier terms produces
   the manuscript's display (30):

   `δ_n := L^{O_{r,D}(1)} (e^{-cL^{1/2}} + e^{-cH} + ρ^{cH})`.

2. **The `O_A(L^{-A})` reduction.**  Display (30) then asserts
   `δ_n = O_A(L^{-A})`, this is what makes the error term of (27) *any*
   negative power of `L`, and it is the step that fixes the shape of the
   whole §4/§5 bookkeeping.

   What the proof of half 2 actually consumes from (18) is `H ≥ L^{1/2}`:
   that is the only reason the `e^{-cH}` and `ρ^{cH}` terms of (30) are
   dominated by the `e^{-cL^{1/2}}` term (`deltaScaleR_le`), and it is the
   *lower* constraint on `H`.  The complementary upper constraint is
   `400H ≤ m_n ≍ L/λ`, needed for `J_n` of (19) to be nonempty.  Any `H`
   with `L^{1/2} ≤ H ≪ L` therefore serves; `H = L^{3/4}` is a valid choice
   inside that window rather than a forced one.  The manuscript does not
   state this window, so it is recorded here.

Half 2 is **proved in full** here (`deltaScaleR_le_rpow_neg`,
`eventually_rpow_mul_deltaScale_le`), and Proposition 4.1 is **derived**
from half 1 in the exact shape (30) states it (`prop_4_1_error_shape`,
the single sorried input).  Two further genuine ingredients of half 1 are
proved outright:

* `good_avoids_resonance_window`, the manuscript's sentence "each lies
  either at least `100H` before `k_-` or at least `100H` after `k_+`",
  derived from (26) and `k_± = ⌊R_s ± 40H⌋`.  Machine-checked, including
  the floor losses the manuscript leaves implicit.
* `goodTuple_sep`, the separation (25) in the integer form Lemma 3.2
  consumes (`t_{i+1} - t_i ≥ M` with `M = ⌊200H⌋`).

The mixing input itself, Lemma 3.2 of the manuscript, is stated
faithfully as `lem_3_2_conditional_multiblock_mixing` (sorried); no other
module in `Kwon1002/` states it yet.

Nothing below weakens the target: `prop_4_1_marked_factorization` is
reproduced token-identically from `Kwon1002/Section4.lean` (diffed).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace Prop41

noncomputable section

/-! ## A norm fact for the character of (24) -/

/-- `|e(t)| = 1`: the "amplitude has modulus at most one" bookkeeping of
the proof of 4.1 rests on this. -/
theorem norm_torusChar (t : ℝ) : ‖torusChar t‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [torusChar, Complex.norm_exp, h, Real.exp_zero]

/-! ## (25): the separation, in the integer form Lemma 3.2 consumes -/

/-- **(25)** For a good tuple the consecutive gaps exceed `⌊200H⌋`, which
is the hypothesis `t_{i+1} - t_i ≥ M` of Lemma 3.2 with `M = ⌊200H⌋`. -/
theorem goodTuple_sep (n r : ℕ) (j : ℕ → ℕ) (hj : GoodTuple n r j)
    (ℓ : ℕ) (hℓ : ℓ + 1 < r) :
    j ℓ + ⌊200 * Hscale n⌋₊ ≤ j (ℓ + 1) := by
  have h := hj.2.1 ℓ hℓ
  rcases le_total (200 * Hscale n) 0 with h0 | h0
  · have hz : ⌊200 * Hscale n⌋₊ = 0 :=
      Nat.floor_eq_zero.2 (lt_of_le_of_lt h0 one_pos)
    rw [hz, Nat.add_zero]
    exact le_of_lt (hj.1.2.1 ℓ (ℓ + 1) (Nat.lt_succ_self ℓ) hℓ)
  · have hfl : ((⌊200 * Hscale n⌋₊ : ℕ) : ℝ) ≤ 200 * Hscale n := Nat.floor_le h0
    have hcast : ((j ℓ + ⌊200 * Hscale n⌋₊ : ℕ) : ℝ) ≤ ((j (ℓ + 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast

/-! ## (26): the two-sided resonance window

`R_s = (m_n + j_s)/2` is the nominal resonance time and `k_± = ⌊R_s ± 40H⌋`
are the two cut depths of the proof of 4.1. -/

/-- The nominal resonance time `R_i = (m_n + j_i)/2` of the proof of 4.1. -/
def resonanceTime (n : ℕ) (ji : ℕ) : ℝ := ((mIndex n : ℝ) + (ji : ℝ)) / 2

/-- `k_- = ⌊R_i - 40H⌋`. -/
def kMinus (n ji : ℕ) : ℤ := ⌊resonanceTime n ji - 40 * Hscale n⌋

/-- `k_+ = ⌊R_i + 40H⌋`. -/
def kPlus (n ji : ℕ) : ℤ := ⌊resonanceTime n ji + 40 * Hscale n⌋

/-- **The sentence after (29)**: "The factors after `s` are zero torus modes
and hence digit functions.  By (26), each lies either at least `100H` before
`k_-` or at least `100H` after `k_+`."

Both disjuncts are reachable, which is the content of the *two-sided*
reading of (26): under the one-sided reading (`j_ℓ - R_i ≥ 200H`, what the
garbled text extraction suggests) no `j_ℓ` of a good tuple ever sits below
the resonance time, so the first disjunct is vacuous.  That one-sided
reading is not merely wasteful, it breaks the count stated between (26) and
Proposition 4.1: it would disqualify a positive proportion of all tuples,
leaving `≍ L^r` non-good tuples rather than `O_r(L^{r-1}H)`.  So the count
forces the bars, independently of the PDF.

The margin is comfortable: (26) gives `200H` and the cuts cost only
`40H + 1`, so the `100H` claimed is reached with `60H - 1` to spare, the
`hH : 1 ≤ Hscale n` below is the only largeness this needs. -/
theorem good_avoids_resonance_window (n r : ℕ) (j : ℕ → ℕ) (hj : GoodTuple n r j)
    (hH : 1 ≤ Hscale n) (i ℓ : ℕ) (hiℓ : i < ℓ) (hℓ : ℓ < r) :
    (j ℓ : ℝ) ≤ (kMinus n (j i) : ℝ) - 100 * Hscale n ∨
      (kPlus n (j i) : ℝ) + 100 * Hscale n ≤ (j ℓ : ℝ) := by
  have h := hj.2.2 i ℓ hiℓ hℓ
  set Hn : ℝ := Hscale n with hHn
  set R : ℝ := resonanceTime n (j i) with hR
  have hRdef : (j ℓ : ℝ) - ((mIndex n : ℝ) + (j i : ℝ)) / 2 = (j ℓ : ℝ) - R := by
    rw [hR, resonanceTime]
  rw [hRdef] at h
  rcases le_abs.1 h with hcase | hcase
  · -- `j ℓ` lies at least `200H` *after* the resonance time
    right
    have hfl : ((kPlus n (j i) : ℤ) : ℝ) ≤ R + 40 * Hn := Int.floor_le _
    linarith
  · -- `j ℓ` lies at least `200H` *before* the resonance time
    left
    have hfl : R - 40 * Hn - 1 < ((kMinus n (j i) : ℤ) : ℝ) := Int.sub_one_lt_floor _
    linarith

/-! ## Display (30): the error scale, and its `O_A(L^{-A})` reduction

`δ_n = L^{O(1)} (e^{-cL^{1/2}} + e^{-cH} + ρ^{cH})`; here the polynomial
factor is carried separately, so `deltaScale` is the bracket. -/

/-- The bracket of (30), as a function of the real variable `L`
(`H = L^{3/4}` by (18)). -/
def deltaScaleR (c ρ L : ℝ) : ℝ :=
  Real.exp (-c * Real.sqrt L) + Real.exp (-c * L ^ (3 / 4 : ℝ)) + ρ ^ (c * L ^ (3 / 4 : ℝ))

/-- The bracket of (30) at `L = log n`, `H = L^{3/4}`. -/
def deltaScale (c ρ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)

theorem deltaScale_eq (c ρ : ℝ) (n : ℕ) : deltaScale c ρ n = deltaScaleR c ρ (Lnorm n) := rfl

/-- All three terms of (30)'s bracket are dominated by a single stretched
exponential `e^{-c₁√L}`; `H = L^{3/4} ≥ L^{1/2}` for `L ≥ 1`. -/
theorem deltaScaleR_le (c ρ : ℝ) (hc : 0 < c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ L : ℝ in atTop,
      deltaScaleR c ρ L ≤ 3 * Real.exp (-min c (c * (-Real.log ρ)) * Real.sqrt L) := by
  have hlogρ : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  set c₁ : ℝ := min c (c * (-Real.log ρ)) with hc₁def
  have hc₁ : 0 < c₁ := lt_min hc (mul_pos hc (neg_pos.2 hlogρ))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  have hs0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hs : Real.sqrt L ≤ L ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hp : (0 : ℝ) ≤ L ^ (3 / 4 : ℝ) := le_trans hs0 hs
  have e1 : Real.exp (-c * Real.sqrt L) ≤ Real.exp (-c₁ * Real.sqrt L) := by
    apply Real.exp_le_exp.2
    have h1 : c₁ ≤ c := min_le_left _ _
    nlinarith
  have e2 : Real.exp (-c * L ^ (3 / 4 : ℝ)) ≤ Real.exp (-c₁ * Real.sqrt L) := by
    apply Real.exp_le_exp.2
    have h1 : c₁ ≤ c := min_le_left _ _
    have step : c₁ * Real.sqrt L ≤ c * L ^ (3 / 4 : ℝ) := by nlinarith
    linarith
  have e3 : ρ ^ (c * L ^ (3 / 4 : ℝ)) ≤ Real.exp (-c₁ * Real.sqrt L) := by
    rw [Real.rpow_def_of_pos hρ0]
    apply Real.exp_le_exp.2
    have h1 : c₁ ≤ c * (-Real.log ρ) := min_le_right _ _
    have step : c₁ * Real.sqrt L ≤ (c * (-Real.log ρ)) * L ^ (3 / 4 : ℝ) := by nlinarith
    nlinarith [step]
  simp only [deltaScaleR]
  linarith

/-- **Display (30), the `O_A(L^{-A})` half.**  For every polynomial weight
`L^B`, every mixing constant `c > 0` and every `ρ ∈ (0,1)`, the error scale
of (30) is eventually below `L^{-A}`, *any* fixed negative power. -/
theorem deltaScaleR_le_rpow_neg (A B c ρ : ℝ) (hc : 0 < c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ L : ℝ in atTop, L ^ B * deltaScaleR c ρ L ≤ L ^ (-A) := by
  have hlogρ : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  set c₁ : ℝ := min c (c * (-Real.log ρ)) with hc₁def
  have hc₁ : 0 < c₁ := lt_min hc (mul_pos hc (neg_pos.2 hlogρ))
  have key : ∀ᶠ L : ℝ in atTop,
      (3 : ℝ) * (L ^ (A + B) * Real.exp (-c₁ * Real.sqrt L)) ≤ 1 := by
    have h0 : Tendsto (fun x : ℝ => x ^ (2 * (A + B)) * Real.exp (-c₁ * x)) atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * (A + B)) c₁ hc₁
    have h1 : ∀ᶠ x : ℝ in atTop,
        x ^ (2 * (A + B)) * Real.exp (-c₁ * x) ≤ 1 / 3 :=
      Filter.Tendsto.eventually_le_const (by norm_num) h0
    have h2 := Real.tendsto_sqrt_atTop.eventually h1
    filter_upwards [h2, eventually_ge_atTop (0 : ℝ)] with L hL hL0
    have hsq : (Real.sqrt L) ^ (2 * (A + B)) = L ^ (A + B) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0]
      congr 1
      ring
    rw [hsq] at hL
    linarith
  filter_upwards [key, deltaScaleR_le c ρ hc hρ0 hρ1, eventually_gt_atTop (0 : ℝ)]
    with L hkey hδL hL0
  have hLB : L ^ B = L ^ (-A) * L ^ (A + B) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hpos : (0 : ℝ) < L ^ (-A) := Real.rpow_pos_of_pos hL0 _
  calc L ^ B * deltaScaleR c ρ L
      ≤ L ^ B * (3 * Real.exp (-c₁ * Real.sqrt L)) :=
        mul_le_mul_of_nonneg_left hδL (Real.rpow_nonneg hL0.le B)
    _ = L ^ (-A) * (3 * (L ^ (A + B) * Real.exp (-c₁ * Real.sqrt L))) := by
        rw [hLB]; ring
    _ ≤ L ^ (-A) * 1 := mul_le_mul_of_nonneg_left hkey hpos.le
    _ = L ^ (-A) := mul_one _

/-- The same statement along `n → ∞`, with `L = log n`, `H = L^{3/4}`. -/
theorem eventually_rpow_mul_deltaScale_le (A B c ρ : ℝ)
    (hc : 0 < c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, (Lnorm n) ^ B * deltaScale c ρ n ≤ (Lnorm n) ^ (-A) := by
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [deltaScale_eq] using
    hLtend.eventually (deltaScaleR_le_rpow_neg A B c ρ hc hρ0 hρ1)

/-! ## The mixing input: Lemma 3.2 of the manuscript, display (17) -/

/-- The depth-`d` cylinder of the digit word `w`, inside `(0,1)`. -/
def cylinder (d : ℕ) (w : ℕ → ℕ) : Set ℝ :=
  {α ∈ Ioo (0 : ℝ) 1 | ∀ i, i < d → digit α i = w i}

/-- `‖g‖_{BV(0,1)} ≤ K`: sup-norm and total variation on `(0,1)` both at
most `K`.  (The manuscript's `BV(0,1)` norm is `‖·‖_∞ + Var`; bounding both
by `K` is the same thing up to the constant `C_s` of (17), which is
existentially quantified.) -/
def BVBoundedBy (K : ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ K) ∧ eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K

/-- **Lemma 3.2** (Conditional multi-block mixing), display (17).

Let `I_w` be a cylinder of depth `d`, and let `d + M ≤ t_1 < ⋯ < t_s` with
`t_{i+1} - t_i ≥ M`.  If `g_1, …, g_s ∈ BV(0,1)` then

`|E(∏ᵢ gᵢ(T^{tᵢ}α) | I_w) - ∏ᵢ ∫ gᵢ dν| ≤ C_s ρ^M ∏ᵢ ‖gᵢ‖_BV`,

with constants uniform in the cylinder.

This is the mixing input the proof of Proposition 4.1 uses (through (25));
no module in `Kwon1002/` proves or states it yet, so it is recorded here as
the named hypothesis.  Its proof needs the substrate's transfer operator
(`Erdos1002.GaussTransferContraction`) together with Lemma 3.1(i). -/
theorem lem_3_2_conditional_multiblock_mixing (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : ℕ → ℕ) (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → BVBoundedBy K (g i)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        0 < (Erdos1002.gaussMeasure (cylinder d w)).toReal →
        |(∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
              ∂Erdos1002.gaussMeasure) / (Erdos1002.gaussMeasure (cylinder d w)).toReal
            - ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ M * K ^ s := by
  sorry

/-! ## The body of the §4 proof, in the shape (30) states it -/

/-! ## Display (30) and Proposition 4.1

`Kwon1002.Prop41.prop_4_1_error_shape` (display (30)) and
`Kwon1002.Prop41.prop_4_1_marked_factorization` are **declared in
`Kwon1002/Prop41Unconditional.lean`**, not here.  The `v_s ≠ 0` branch that
(30) rests on is discharged in `Kwon1002/NonzeroMode.lean`, above this file,
so declarations placed here could never lose their `sorry`.  Everything (30)
needs from this module — `deltaScale`, `eventually_rpow_mul_deltaScale_le`
and the `P_D(L)` apparatus — is proved above. -/

end

end Prop41

end Kwon1002
