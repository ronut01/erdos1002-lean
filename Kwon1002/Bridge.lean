/-
Scratch file (agent `bridge`).

ASSIGNED TARGET: discharge `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing`
from `Kwon1002.BVMixing.lemma_3_2_BV`, handling the four catalogued
mismatches (sign / constant shape / cylinder convention / measurability).

FINDING (scheduling, not mathematics).  That edge was already built, this
same day, by the sibling agent `mixbv`:
`Kwon1002.MixingBV.lem_3_2_conditional_multiblock_mixing'` is the target
reproduced token-identically and proved outright.  Section 1 below
*verifies* that claim independently rather than duplicating the work: the
mechanical diff of the two 10-line statement blocks is empty apart from the
prime, and the axioms are exactly `propext, Classical.choice, Quot.sound`.

WHAT THIS FILE ADDS.

* Section 2, the immediate downstream consequence, which nobody has taken.
  `Kwon1002.ErrorShape.good_tuple_multiblock_mixing` is the sole consumer of
  the target, and it is proved only *conditionally*: its proof calls the
  sorried `Prop41.lem_3_2_conditional_multiblock_mixing`, so its axiom list
  contains `sorryAx`.  Section 2 reproduces it token-identically as
  `good_tuple_multiblock_mixing'` (diffed against `Kwon1002/ErrorShape.lean`
  lines 497-505; only the name carries a prime) and reproves it against
  `MixingBV`'s unconditional version.  The result is axiom-clean, so the §4
  mixing input is now unconditional all the way from Wang's transfer-operator
  contraction to the good tuple's gap structure.

* Sections 4-5, the `BV` bound on the §4 zero-mode digit observable, which
  `Prop4Final.zero_mode_defect_eq` and `ErrorShape.zero_mode_factorization`
  both record as the one genuinely missing lemma ("the variation bound is
  the piece Mathlib's `eVariationOn` API does not yet support").

SORRIED RESULTS CONSUMED: none.
-/
import Kwon1002.ErrorShape
import Kwon1002.MixingBV
import Kwon1002.Prop4Final
import Kwon1002.BVLasotaYorke

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace Bridge

open Prop41 ErrorShape

noncomputable section

/-! ## 1. Verification of the sibling edge

The `example`s below are the machine-checked form of "the bridge really does
discharge the §4 mixing input": the primed theorem in `MixingBV` has
definitionally the same statement as the sorried `Prop41` target, and it is
available unconditionally.  The statement block is the `Prop41` target copied
verbatim, so this also certifies that the `BVBoundedBy`, `cylinder` and
`gaussIter` in scope here are the target's, not look-alikes. -/

/-- `MixingBV`'s theorem has exactly the type of the `Prop41` target. -/
example :
    (∀ s : ℕ, ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : ℕ → ℕ) (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → BVBoundedBy K (g i)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        0 < (Erdos1002.gaussMeasure (cylinder d w)).toReal →
        |(∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
              ∂Erdos1002.gaussMeasure) / (Erdos1002.gaussMeasure (cylinder d w)).toReal
            - ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ M * K ^ s) :=
  MixingBV.lem_3_2_conditional_multiblock_mixing'

example : @BVBoundedBy = @Kwon1002.Prop41.BVBoundedBy := rfl

example (d : ℕ) (w : ℕ → ℕ) : cylinder d w = Kwon1002.Prop41.cylinder d w := rfl

/-! ## 2. The downstream discharge

`ErrorShape.good_tuple_multiblock_mixing`, reproduced token-identically and
reproved from the *unconditional* mixing input.  Every side condition of
display (17) is discharged from `GoodTuple` exactly as in `ErrorShape`:

* depth `d = 0`, and `Prop41.cylinder 0 w = Ioo 0 1` (`ErrorShape.cylinder_zero`),
  so the conditioning is vacuous, and `ν(Ioo 0 1) > 0`
  (`ErrorShape.gaussMeasure_Ioo_pos`);
* the start condition `d + M ≤ t 0` is display (19): `j 0 ∈ J_n` gives
  `200 H ≤ j 0`, hence `⌊200 H⌋₊ ≤ j 0`;
* the gap condition is display (25), `Prop41.goodTuple_sep`.

The only change from `ErrorShape`'s proof is the first line: the mixing input
is now `MixingBV.lem_3_2_conditional_multiblock_mixing'` instead of the
sorried `Prop41.lem_3_2_conditional_multiblock_mixing`. -/
theorem good_tuple_multiblock_mixing' (r : ℕ) (hr : 0 < r) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (j : ℕ → ℕ), GoodTuple n r j →
      ∀ (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K → (∀ i, i < r → BVBoundedBy K (g i)) →
        |(∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i))
              ∂Erdos1002.gaussMeasure)
              / (Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1)).toReal
            - ∏ i ∈ Finset.range r, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ (⌊200 * Hscale n⌋₊) * K ^ r := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, h⟩ := MixingBV.lem_3_2_conditional_multiblock_mixing' r
  refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
  intro n j hj g K hK hg
  have hcyl : cylinder 0 (fun _ => 0) = Ioo (0 : ℝ) 1 := cylinder_zero _
  -- (19): `j 0 ∈ J_n` forces `200 H ≤ j 0`, hence `⌊200 H⌋₊ ≤ j 0`
  have hmemJ : j 0 ∈ bulkJ n := hj.1.2.2 0 hr
  have hge : 200 * Hscale n ≤ ((j 0 : ℕ) : ℝ) := ((Finset.mem_filter.1 hmemJ).2).1
  have hstart : 0 + ⌊200 * Hscale n⌋₊ ≤ j 0 := by
    have h1 : ⌊200 * Hscale n⌋₊ ≤ ⌊((j 0 : ℕ) : ℝ)⌋₊ := Nat.floor_mono hge
    rw [Nat.floor_natCast] at h1
    omega
  -- (25): the gaps
  have hgap : ∀ i, i + 1 < r → j i + ⌊200 * Hscale n⌋₊ ≤ j (i + 1) := fun i hi =>
    goodTuple_sep n r j hj i hi
  have hpos : 0 < (Erdos1002.gaussMeasure (cylinder 0 (fun _ => 0))).toReal := by
    rw [hcyl]; exact gaussMeasure_Ioo_pos
  have hmain := h 0 (⌊200 * Hscale n⌋₊) (fun _ => 0) j g K hK hg hstart hgap hpos
  rwa [hcyl] at hmain

/-! ## 3. Explicit constants at `K = 1`

`MixingBV.core_estimate` carries the explicit constant `2^r · bvBound 2 M r`
before the homogeneity rescaling; specialising the good-tuple application to
it records what the constant actually is,

  `C = 2^r · 478 · (r+1) · 16^r · 2`,   `ρ = √(527/540)`.

Both `Prop41.deltaScaleR_le_rpow_neg` and
`Prop41.eventually_rpow_mul_deltaScale_le` are quantified over every
`ρ ∈ (0,1)`, so the degraded rate costs nothing downstream. -/
theorem good_tuple_multiblock_mixing_explicit (r : ℕ) (hr : 0 < r)
    (n : ℕ) (j : ℕ → ℕ) (hj : GoodTuple n r j)
    (g : ℕ → ℝ → ℝ) (hg : ∀ i, i < r → BVBoundedBy 1 (g i)) :
    |(∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i))
          ∂Erdos1002.gaussMeasure)
          / (Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1)).toReal
        - ∏ i ∈ Finset.range r, ∫ x, g i x ∂Erdos1002.gaussMeasure|
      ≤ 2 ^ r * MixingBV.bvBound 2 (⌊200 * Hscale n⌋₊) r := by
  have hcyl : cylinder 0 (fun _ => 0) = Ioo (0 : ℝ) 1 := cylinder_zero _
  have hmemJ : j 0 ∈ bulkJ n := hj.1.2.2 0 hr
  have hge : 200 * Hscale n ≤ ((j 0 : ℕ) : ℝ) := ((Finset.mem_filter.1 hmemJ).2).1
  have hstart : 0 + ⌊200 * Hscale n⌋₊ ≤ j 0 := by
    have h1 : ⌊200 * Hscale n⌋₊ ≤ ⌊((j 0 : ℕ) : ℝ)⌋₊ := Nat.floor_mono hge
    rw [Nat.floor_natCast] at h1
    omega
  have hgap : ∀ i, i + 1 < r → j i + ⌊200 * Hscale n⌋₊ ≤ j (i + 1) := fun i hi =>
    goodTuple_sep n r j hj i hi
  have hpos : 0 < (Erdos1002.gaussMeasure (cylinder 0 (fun _ => 0))).toReal := by
    rw [hcyl]; exact gaussMeasure_Ioo_pos
  have hmain := MixingBV.core_estimate r 0 (⌊200 * Hscale n⌋₊) (fun _ => 0) j g hg
    hstart hgap hpos
  rwa [hcyl] at hmain

/-! ## 4. The `BV` bound on a step function of the first digit

`Prop4Final.zero_mode_defect_eq` reduces the zero-mode branch of §4 to the
mixing defect (17) for the digit observables `g_ℓ(x) = c_ℓ(a_1(x), 0)`, and
its docstring lists what is then still missing.  Two of the three items are
bookkeeping (`dα` versus `dν`; real versus complex).  The third is a genuine
lemma, which both `Prop4Final` and `ErrorShape.zero_mode_factorization`
record as absent:

> the `BV(0,1)` bound on `g_ℓ`, a step function with at most `L^D` jumps …
> the variation bound is the piece Mathlib's `eVariationOn` API does not yet
> support.

This section proves it.  The route is *not* a direct estimate on the
supremum defining `eVariationOn`: it writes the step function as a finite
combination of first-digit cylinder indicators and uses the additivity
lemmas that the `BVLasotaYorke`/`MixingBV` work already supplies. -/

/-- The indicator of a half-line takes only the values `0` and `1`. -/
theorem indicator_Ioi_eq (p x : ℝ) :
    (Ioi p).indicator (fun _ => (1 : ℝ)) x = 0 ∨
      (Ioi p).indicator (fun _ => (1 : ℝ)) x = 1 := by
  by_cases hx : x ∈ Ioi p
  · exact Or.inr (Set.indicator_of_mem hx _)
  · exact Or.inl (Set.indicator_of_notMem hx _)

/-- **Variation of a half-line indicator.**  It is monotone, so its variation
over `(0,1)` is at most the total jump `1`. -/
theorem eVariationOn_indicator_Ioi_le (p : ℝ) :
    eVariationOn ((Ioi p).indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1)
      ≤ ENNReal.ofReal 1 := by
  have hmono : MonotoneOn ((Ioi p).indicator (fun _ => (1 : ℝ))) (Icc (0 : ℝ) 1) := by
    intro x _ y _ hxy
    by_cases hx : x ∈ Ioi p
    · have hy : y ∈ Ioi p := lt_of_lt_of_le hx hxy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hx]
      rcases indicator_Ioi_eq p y with h | h
      · rw [h]
      · rw [h]; norm_num
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hle := hmono.eVariationOn_le h0 h1
  rw [Set.inter_self] at hle
  refine le_trans (le_trans (eVariationOn.mono _ Ioo_subset_Icc_self) hle)
    (ENNReal.ofReal_le_ofReal ?_)
  rcases indicator_Ioi_eq p 1 with ha | ha <;> rcases indicator_Ioi_eq p 0 with hb | hb <;>
    rw [ha, hb] <;> norm_num

/-- **Variation of an interval indicator.**  `1_{(p,q]} = 1_{(p,∞)} −
1_{(max p q,∞)}` pointwise, so the variation is at most `2`.  Mathlib has the
monotone case only, and `1_{(p,q]}` is not monotone. -/
theorem eVariationOn_indicator_Ioc_le (p q : ℝ) :
    eVariationOn ((Ioc p q).indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1)
      ≤ ENNReal.ofReal 2 := by
  have hpt : ∀ x : ℝ, (Ioc p q).indicator (fun _ => (1 : ℝ)) x
      = (Ioi p).indicator (fun _ => (1 : ℝ)) x
        + (-1) * (Ioi (max p q)).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hxp : p < x
    · by_cases hxq : x ≤ q
      · have hmax : x ∉ Ioi (max p q) :=
          fun h => absurd (le_trans hxq (le_max_right p q)) (not_le.2 h)
        rw [Set.indicator_of_mem (show x ∈ Ioc p q from ⟨hxp, hxq⟩),
          Set.indicator_of_mem (show x ∈ Ioi p from hxp),
          Set.indicator_of_notMem hmax]
        ring
      · have hq : q < x := lt_of_not_ge hxq
        have hmax : x ∈ Ioi (max p q) := max_lt hxp hq
        rw [Set.indicator_of_notMem (show x ∉ Ioc p q from fun h => hxq h.2),
          Set.indicator_of_mem (show x ∈ Ioi p from hxp),
          Set.indicator_of_mem hmax]
        ring
    · have hmax : x ∉ Ioi (max p q) :=
        fun h => hxp (lt_of_le_of_lt (le_max_left p q) h)
      rw [Set.indicator_of_notMem (show x ∉ Ioc p q from fun h => hxp h.1),
        Set.indicator_of_notMem (show x ∉ Ioi p from hxp),
        Set.indicator_of_notMem hmax]
      ring
  have heq : eVariationOn ((Ioc p q).indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1)
      = eVariationOn (fun x => (Ioi p).indicator (fun _ => (1 : ℝ)) x
          + (-1) * (Ioi (max p q)).indicator (fun _ => (1 : ℝ)) x) (Ioo (0 : ℝ) 1) :=
    eVariationOn.eq_of_eqOn (fun x _ => hpt x)
  rw [heq]
  refine le_trans (BVLasotaYorke.eVariationOn_add_le _ _ _) ?_
  have hA := eVariationOn_indicator_Ioi_le p
  have hB : eVariationOn (fun x => (-1 : ℝ) * (Ioi (max p q)).indicator (fun _ => (1 : ℝ)) x)
      (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
    refine le_trans (MixingBV.eVariationOn_const_mul_le (-1) _ _) ?_
    have habs : |(-1 : ℝ)| = 1 := by norm_num
    rw [habs, ENNReal.ofReal_one, one_mul]
    simpa using eVariationOn_indicator_Ioi_le (max p q)
  calc eVariationOn ((Ioi p).indicator (fun _ => (1 : ℝ))) (Ioo (0 : ℝ) 1)
        + eVariationOn (fun x => (-1 : ℝ) * (Ioi (max p q)).indicator (fun _ => (1 : ℝ)) x)
            (Ioo (0 : ℝ) 1)
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 := add_le_add hA hB
    _ = ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

/-- On `(0,1)` the first digit is positive, and membership in the `a`-th
first-digit cylinder is exactly "the first digit is `a`". -/
theorem mem_firstDigitCylinder_iff {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (a : ℕ) :
    x ∈ Erdos1002.firstDigitCylinder a ↔ a = digit x 0 := by
  have hxIoc : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hdig : digit x 0 = Erdos1002.gaussFirstDigitNat x := rfl
  have hcast : ((digit x 0 : ℕ) : ℤ) = Erdos1002.gaussFirstDigit x := by
    rw [hdig]; exact Erdos1002.gaussFirstDigitNat_cast hxIoc
  have hpos : 0 < digit x 0 := by
    rw [hdig]; exact Erdos1002.gaussFirstDigitNat_pos hxIoc
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    constructor
    · intro hmem
      exfalso
      rw [Erdos1002.firstDigitCylinder] at hmem
      have h1 : (1 : ℝ) < x := by
        have hm := hmem.1
        norm_num at hm
        exact hm
      linarith [hx.2]
    · intro h; omega
  · rw [← Erdos1002.gaussFirstDigit_eq_iff_mem_firstDigitCylinder hxIoc a ha, ← hcast]
    constructor
    · intro h
      have hnat : digit x 0 = a := by exact_mod_cast h
      exact hnat.symm
    · intro h
      have hnat : digit x 0 = a := h.symm
      exact_mod_cast hnat

/-- **The missing lemma.**  A step function of the first digit, supported on
digits `< S` and with `ℓ¹` mass at most `B`, lies in Kwon's class `BV(0,1)`
with norm at most `2B`.

Neither Mathlib, `wang_substrate/`, nor any other module in `Kwon1002/` has
this: `TransferIdentity.firstDigitIndicator_bv` covers only the single
indicator of `{a_1 = 1}`, which is monotone; a general step function of the
first digit is not. -/
theorem bv_of_firstDigit_step (φ : ℕ → ℝ) (S : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hsupp : ∀ a, S ≤ a → φ a = 0)
    (hsum : ∑ a ∈ Finset.range S, |φ a| ≤ B) :
    BVBoundedBy (2 * B) (fun x => φ (digit x 0)) := by
  classical
  have hnn : ∀ a, (0 : ℝ) ≤ |φ a| := fun a => abs_nonneg _
  -- the step-function representation, valid on `(0,1)`
  have hrep : EqOn
      (fun x => ∑ a ∈ Finset.range S,
        φ a * (Erdos1002.firstDigitCylinder a).indicator (fun _ => (1 : ℝ)) x)
      (fun x => φ (digit x 0)) (Ioo (0 : ℝ) 1) := by
    intro x hx
    have hterm : ∀ a ∈ Finset.range S,
        φ a * (Erdos1002.firstDigitCylinder a).indicator (fun _ => (1 : ℝ)) x
          = if a = digit x 0 then φ a else 0 := by
      intro a _
      by_cases ha : a = digit x 0
      · rw [Set.indicator_of_mem ((mem_firstDigitCylinder_iff hx a).2 ha), mul_one,
          if_pos ha]
      · rw [Set.indicator_of_notMem (fun hmem =>
          ha ((mem_firstDigitCylinder_iff hx a).1 hmem)), mul_zero, if_neg ha]
    simp only []
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range S) (digit x 0) φ]
    by_cases hd : digit x 0 ∈ Finset.range S
    · rw [if_pos hd]
    · rw [if_neg hd]
      exact (hsupp (digit x 0) (by simpa [Finset.mem_range, not_lt] using hd)).symm
  constructor
  · -- sup bound
    intro x _
    show |φ (digit x 0)| ≤ 2 * B
    by_cases hd : digit x 0 < S
    · have h1 : |φ (digit x 0)| ≤ ∑ a ∈ Finset.range S, |φ a| :=
        Finset.single_le_sum (f := fun a => |φ a|) (fun a _ => hnn a)
          (Finset.mem_range.2 hd)
      linarith
    · rw [hsupp (digit x 0) (by omega)]
      simp only [abs_zero]
      linarith
  · -- variation bound
    rw [← eVariationOn.eq_of_eqOn hrep]
    refine le_trans (BVLasotaYorke.eVariationOn_finsum_le
      (fun a x => φ a * (Erdos1002.firstDigitCylinder a).indicator (fun _ => (1 : ℝ)) x)
      (Ioo (0 : ℝ) 1) S) ?_
    have hstep : ∀ a ∈ Finset.range S,
        eVariationOn
            (fun x => φ a * (Erdos1002.firstDigitCylinder a).indicator (fun _ => (1 : ℝ)) x)
            (Ioo (0 : ℝ) 1)
          ≤ ENNReal.ofReal (2 * |φ a|) := by
      intro a _
      refine le_trans (MixingBV.eVariationOn_const_mul_le (φ a) _ _) ?_
      rw [Erdos1002.firstDigitCylinder]
      refine le_trans (mul_le_mul_left' (eVariationOn_indicator_Ioc_le _ _) _) ?_
      rw [← ENNReal.ofReal_mul (hnn a)]
      exact le_of_eq (by rw [mul_comm])
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.mul_sum]
    linarith

/-! ## 5. The bound applied to the §4 observable

`Prop4Final.digitObs c ℓ x = c_ℓ(a_1(x), 0)` is complex; Kwon's (17) is a
real statement, so the two real components are what must be `BV`.  Both are,
with the constant the manuscript claims. -/

/-- The `ℓ¹` mass of the zero-mode coefficients is at most `L^D`.  Same box
argument as `Prop4Final.coeff_norm_le`, but summed over the digit. -/
theorem sum_coeff_norm_le (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) :
    ∑ a ∈ Finset.range (⌊L ^ D⌋₊ + 1), ‖c ℓ a 0‖ ≤ L ^ D := by
  classical
  set box : Finset (ℕ × ℤ) := Finset.range (⌊L ^ D⌋₊ + 1) ×ˢ modeBox D L with hboxdef
  have hzero : ∀ p ∉ box, ‖c ℓ p.1 p.2‖ = 0 := by
    intro p hp
    by_cases hv : p.2 ∈ modeBox D L
    · have h1 : p.1 ∉ Finset.range (⌊L ^ D⌋₊ + 1) := by
        intro h
        exact hp (by rw [hboxdef]; exact Finset.mem_product.2 ⟨h, hv⟩)
      rw [Finset.mem_range, not_lt] at h1
      have hR : L ^ D < (p.1 : ℝ) := by
        have hfl : L ^ D < (⌊L ^ D⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one (L ^ D)
        have hcast : ((⌊L ^ D⌋₊ + 1 : ℕ) : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast h1
        push_cast at hcast
        linarith
      rw [(hc ℓ hℓ).1 p.1 p.2 hR, norm_zero]
    · rw [coeff_eq_zero_of_notMem_modeBox r D L F c hc ℓ hℓ p.1 p.2 hv, norm_zero]
  have htsum : (∑' p : ℕ × ℤ, ‖c ℓ p.1 p.2‖) = ∑ p ∈ box, ‖c ℓ p.1 p.2‖ :=
    tsum_eq_sum hzero
  have hle : ∑ p ∈ box, ‖c ℓ p.1 p.2‖ ≤ L ^ D := by
    rw [← htsum]; exact (hc ℓ hℓ).2.2.1
  have h0mem : (0 : ℤ) ∈ modeBox D L := by
    rw [modeBox, Finset.mem_Icc]
    exact ⟨neg_nonpos.2 (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hinj : ∀ a ∈ Finset.range (⌊L ^ D⌋₊ + 1), (a, (0 : ℤ)) ∈ box := by
    intro a ha
    rw [hboxdef]
    exact Finset.mem_product.2 ⟨ha, h0mem⟩
  have himg : ∑ a ∈ Finset.range (⌊L ^ D⌋₊ + 1), ‖c ℓ a 0‖
      = ∑ p ∈ (Finset.range (⌊L ^ D⌋₊ + 1)).image (fun a : ℕ => (a, (0 : ℤ))),
          ‖c ℓ p.1 p.2‖ := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).1
  rw [himg]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => norm_nonneg _)) hle
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  exact hinj a ha

/-- **The `BV` bound the manuscript asserts**, for the real part of the
zero-mode digit observable: `‖Re g_ℓ‖_BV ≤ 2 L^D`. -/
theorem digitObs_re_bv (r : ℕ) (D L : ℝ) (hL : 0 ≤ L ^ D) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) :
    BVBoundedBy (2 * L ^ D) (fun x => (Prop4Final.digitObs c ℓ x).re) := by
  refine bv_of_firstDigit_step (fun a => (c ℓ a 0).re) (⌊L ^ D⌋₊ + 1) (L ^ D) hL ?_ ?_
  · intro a ha
    show (c ℓ a 0).re = 0
    have hR : L ^ D < (a : ℝ) := by
      have hfl : L ^ D < (⌊L ^ D⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one (L ^ D)
      have hcast : ((⌊L ^ D⌋₊ + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      push_cast at hcast
      linarith
    rw [(hc ℓ hℓ).1 a 0 hR]
    simp
  · refine le_trans (Finset.sum_le_sum (fun a _ => Complex.abs_re_le_norm (c ℓ a 0))) ?_
    exact sum_coeff_norm_le r D L F c hc ℓ hℓ

/-- …and for the imaginary part. -/
theorem digitObs_im_bv (r : ℕ) (D L : ℝ) (hL : 0 ≤ L ^ D) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) :
    BVBoundedBy (2 * L ^ D) (fun x => (Prop4Final.digitObs c ℓ x).im) := by
  refine bv_of_firstDigit_step (fun a => (c ℓ a 0).im) (⌊L ^ D⌋₊ + 1) (L ^ D) hL ?_ ?_
  · intro a ha
    show (c ℓ a 0).im = 0
    have hR : L ^ D < (a : ℝ) := by
      have hfl : L ^ D < (⌊L ^ D⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one (L ^ D)
      have hcast : ((⌊L ^ D⌋₊ + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      push_cast at hcast
      linarith
    rw [(hc ℓ hℓ).1 a 0 hR]
    simp
  · refine le_trans (Finset.sum_le_sum (fun a _ => Complex.abs_im_le_norm (c ℓ a 0))) ?_
    exact sum_coeff_norm_le r D L F c hc ℓ hℓ

end

end Bridge

end Kwon1002

/-
## Summary

PROVED OUTRIGHT (no `sorry`).  Axioms were machine-checked on every theorem
below and are exactly `[propext, Classical.choice, Quot.sound]`; the
axiom-printing lines were then removed:

  `good_tuple_multiblock_mixing'`          (§2)
  `good_tuple_multiblock_mixing_explicit`  (§3)
  `indicator_Ioi_eq`, `eVariationOn_indicator_Ioi_le`,
  `eVariationOn_indicator_Ioc_le`, `mem_firstDigitCylinder_iff`,
  `bv_of_firstDigit_step`                  (§4)
  `sum_coeff_norm_le`, `digitObs_re_bv`, `digitObs_im_bv`  (§5)

For contrast, the axioms of `Kwon1002.ErrorShape.good_tuple_multiblock_mixing`
are `[propext, sorryAx, Classical.choice, Quot.sound]`, that is the debt §2
removes.

SORRIED RESULTS CONSUMED: none.

CONSUMED FROM OTHER FILES (all sorry-free):
  `Kwon1002.MixingBV`, `lem_3_2_conditional_multiblock_mixing'`,
    `core_estimate`, `bvBound`, `eVariationOn_const_mul_le`;
  `Kwon1002.BVLasotaYorke`, `eVariationOn_add_le`, `eVariationOn_finsum_le`;
  `Kwon1002.ErrorShape`, `cylinder_zero`, `gaussMeasure_Ioo_pos`,
    `RepresentsPD`, `modeBox`, `coeff_eq_zero_of_notMem_modeBox`;
  `Kwon1002.Prop41`, `BVBoundedBy`, `cylinder`, `goodTuple_sep`, `bulkJ`,
    `GoodTuple`, `Hscale`;
  `Kwon1002.Prop4Final`, `digitObs`;
  `Erdos1002`, `firstDigitCylinder`, `gaussFirstDigit`, `gaussFirstDigitNat`,
    `gaussFirstDigitNat_cast`, `gaussFirstDigitNat_pos`,
    `gaussFirstDigit_eq_iff_mem_firstDigitCylinder`, `gaussMeasure`.

## Findings

**F1 (the justification given for the `BV` constant is not the one that
works).**  `Prop4Final.zero_mode_defect_eq` and
`ErrorShape.zero_mode_factorization` both justify `‖g_ℓ‖_BV ≤ 2 L^D` by "a
step function with at most `L^D` jumps".  That reason does not give that
constant: the number of jumps is `≤ L^D + 1` and the sup norm is separately
`≤ L^D` (`Prop4Final.coeff_norm_le`), so counting jumps yields only
`‖g_ℓ‖_BV = O(L^{2D})`.  The constant `2 L^D` is correct, but it needs the
`ℓ¹` mass hypothesis of (24), `Σ_{a,v} |c(a,v)| ≤ L^D`, which is how
`bv_of_firstDigit_step` is stated (hypothesis `Σ_{a<S} |φ a| ≤ B`, conclusion
`2B`) and how `digitObs_re_bv` supplies it (`sum_coeff_norm_le`).  Benign for
the proof: the asserted bound does hold.  The docstrings should cite (24)'s
`ℓ¹` bound rather than the jump count.

**F2 (what still separates §4's zero mode from the mixing input).**  With §2
and §5 in hand the obstruction list of `zero_mode_factorization` is down to
two items, both bookkeeping rather than dynamics:
  * complex versus real observables, `∏_ℓ (u_ℓ + i v_ℓ)` expands by
    `Finset.prod_add` into `2^r` real multi-block products, and `∫ ∏` and
    `∏ ∫` expand identically, so the defect is a `2^r`-term signed
    combination of real defects; cost `2^r` in `C`;
  * `dα` versus `dν` on the outside of (27).
No further transfer-operator input is needed for the `v = 0` branch.
-/
