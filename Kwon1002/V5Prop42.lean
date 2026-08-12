import Kwon1002.P42Cases

/-!
# V5Prop42, Proposition 4.2 reconciled with manuscript version 5

This file brings the Proposition 4.2 layer of the development into exact
agreement with version 5 of the manuscript.  Nothing here is new
mathematics; every step is either a restatement of an existing proved
lemma at the version 5 constants, or the small piece of arithmetic that
version 5 added and the earlier draft did not have.

## What version 5 changed

**Statement, lines 640-650.**  The single generic exponent `c` of the
error bracket is split into three,

`C_{U,V}(e^{-c_ld L^{1/2}} + e^{-c_osc H} + rho^{c_mix H})`,

with `c_ld, c_osc, c_mix > 0` allowed to depend on `U, V`.

**Classification: unchanged in substance.**  The three-constant bracket
and the one-constant bracket of
`Kwon1002.prop_4_2_two_block_factorization` are equivalent, and both
directions are proved below (`prop_4_2_v5` and
`prop_4_2_uniform_of_v5`).  One direction is trivial (take all three
constants equal); the other takes `c = min(c_ld, c_osc, c_mix)`, under
which every summand of the bracket only grows.  Our statement is
therefore neither weakened nor strengthened, and no supporting lemma is
invalidated.

**Proof, lines 654-713 and 714-789.**  Version 5 now names the constants
that the earlier draft reused:

* `kappa` (anti-concentration only) and `delta` (denominator windows
  only) with `kappa + 3 delta < 80 lambda`, and `gamma := 80 lambda -
  kappa - 3 delta > 0` (lines 659-663);
* `c_anti = 2 log phi`, the decay constant version 5 attributes to the
  shrinking anti-concentration lemma (line 665, matching the lemma
  statement at line 405);
* `c_ac := min(kappa, 200 c_anti)` for the discarded anti-concentration
  mass (line 675);
* `c_ld` for the constant supplied by the local continuant estimate at
  this `delta` (lines 666-667);
* `gamma_+ := 80 lambda - 3 delta` for the post-resonance branch
  (line 754);
* `c_osc := min(c_ac, gamma/2, gamma_+/2)` (line 771).

## Effect on the constant ledger of `P42Cases`

`P42Cases.Compat c delta c0` recorded four constraints that the draft's
letter reuse forced.  Against version 5:

* `2c + 3 delta < 80 lambda` (`retainedMinus`): retired.  It existed only
  because the draft wrote the retained-descendant conclusion with the
  same letter `c` as the anti-concentration rate.  Version 5 writes that
  conclusion with `gamma/2`, and `gamma/2 <= gamma` needs nothing beyond
  `gamma > 0`.  See `retained_descendant_v5` together with
  `retained_descendant_absorb`, whose only compatibility hypothesis is
  `V5Admissible`, that is version 5's own line 661.
* `c + 3 delta < 80 lambda` (`retainedPlus`): kept, and now explicit in
  the manuscript (line 661).  This is `gammaOsc_pos_iff`, which is
  `Prop42.retained_rate_pos_iff` in version 5 notation.
* `c <= 200 c0` (`antiConc`): retired.  Version 5 takes
  `c_ac := min(kappa, 200 c_anti)` instead of demanding an inequality;
  `antiConc_v5` below proves the resulting mass bound with no hypothesis
  relating `kappa` to `c_anti`.
* `c <= 60` (`mixingGap`): retired as a coupling.  `c_mix` is now an
  independent existential, so the `60H` of room after `t_+` constrains
  only `c_mix`; `cmix_gap_eventually` fixes `c_mix = 59` once and for
  all, with no reference to `kappa` or `delta`.

Consequently `exists_v5Admissible` has no side hypotheses at all, whereas
`P42Cases.exists_compat` needed `delta <= 1` and `0 < c0`.

## One numerical discrepancy, recorded

Version 5 line 665 puts `c_anti = 2 log phi`, matching the Fibonacci form
`4 eta + 4 F_{j+1}^{-2}` of its line 404.  What
`AntiConcentration.shrinking_anti_concentration` proves in this
development is the same shape with the constant `log 2`, inherited from
`AntiConcentration.backward_ratio_anti_concentration`, which certifies
`64 (eta + 2^{-(k+1)})`.  Since `log 2 < 2 log phi`, our proved constant
is the weaker one.  This costs nothing in Proposition 4.2, because
`c_ac` is a `min` against `200 c_anti` and `200 log 2` already dwarfs any
admissible `kappa`; all statements below are therefore parameterised by a
general positive `c_anti` and apply to both values.

## What is new arithmetic

The post-resonance branch (lines 746-755) is a lower bound on
`q_{t_+}^2 / (n |Q_j|)`, using the upper frequency bound
`|Q_j| <= C_{r_1,s_1} q_j`.  The development had no counterpart: the
misleadingly named `P42Cases.retainedPlus_ground` is positivity of
`gamma`, not of `gamma_+`.  `retained_ascendant_exponent` and
`retained_ascendant_v5` supply it.  The upper frequency bound itself is
`Prop42.abs_Qfreq_le`, already proved, with `C_{r_1,s_1} = |r_1| + |s_1|`.

Lines 762-765 add a restoration step ("extend this replacement to the
discarded depth-`t_+` cylinders and restore them, at cost
`O(e^{-c_ld L^{1/2}})`; no future cutoff indicator then remains").
`restore_discarded` is that bookkeeping.

## What is still missing

Unchanged by version 5: the three case bounds
`MonomialCore.zeroMode_gauss_mixing`, `.laterMode_phase_bound` and
`.earlierMode_phase_bound` remain sorried, and the load-bearing absent
input is still the local continuant large-deviation estimate recorded as
`P42Cases.Display20`, which version 5 cites at lines 667, 693, 728, 737
and 747.  Version 5 names its constant `c_ld`; the predicate
`P42Cases.Display20 C delta c` already carries that constant in the right
slot, so no change is needed there either.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

namespace V5Prop42

noncomputable section

/-! ## 1. The version 5 constants (lines 659-667, 675, 754, 771) -/

/-- `gamma := 80 lambda - kappa - 3 delta`, version 5 line 662.  This is
the rate produced by `Prop42.retained_descendant_exponent` at the Levy
constant, with `kappa` in the anti-concentration slot. -/
def gammaOsc (κ δ : ℝ) : ℝ := 80 * lyapunov - κ - 3 * δ

/-- `gamma_+ := 80 lambda - 3 delta`, version 5 line 754.  The rate of
the post-resonance branch, which uses only the denominator windows and
the upper frequency bound, hence carries no `kappa`. -/
def gammaPlus (δ : ℝ) : ℝ := 80 * lyapunov - 3 * δ

/-- `c_anti = 2 log phi` with `phi = (1 + sqrt 5)/2`, version 5 lines
405-406 and 665.  See the module docstring: the value proved in this
development is `log 2`, which is smaller, and every statement below is
parameterised by a general positive `c_anti` so that both are covered. -/
def cAntiV5 : ℝ := 2 * Real.log ((1 + Real.sqrt 5) / 2)

/-- `c_ac := min(kappa, 200 c_anti)`, version 5 line 675. -/
def cAC (cAnti κ : ℝ) : ℝ := min κ (200 * cAnti)

/-- `c_osc := min(c_ac, gamma/2, gamma_+/2)`, version 5 line 771. -/
def cOsc (cAnti κ δ : ℝ) : ℝ :=
  min (cAC cAnti κ) (min (gammaOsc κ δ / 2) (gammaPlus δ / 2))

/-- The version 5 admissibility of the pair `(kappa, delta)`, lines
659-662: both positive, with `kappa + 3 delta < 80 lambda`. -/
def V5Admissible (κ δ : ℝ) : Prop := 0 < κ ∧ 0 < δ ∧ κ + 3 * δ < 80 * lyapunov

/-- Version 5's `kappa + 3 delta < 80 lambda` is our `ACCompatible`, the
constraint our referee report flagged as implicit in the draft. -/
lemma v5Admissible_acCompatible {κ δ : ℝ} (h : V5Admissible κ δ) :
    Prop42.ACCompatible κ δ := h.2.2

/-- `gamma > 0` is exactly `ACCompatible`, version 5 line 662.  This is
`Prop42.retained_rate_pos_iff` in the version 5 notation. -/
lemma gammaOsc_pos_iff {κ δ : ℝ} : 0 < gammaOsc κ δ ↔ Prop42.ACCompatible κ δ := by
  unfold gammaOsc
  rw [show 80 * lyapunov - κ - 3 * δ = 80 * lyapunov - 3 * δ - κ by ring]
  exact Prop42.retained_rate_pos_iff

lemma gammaOsc_pos {κ δ : ℝ} (h : V5Admissible κ δ) : 0 < gammaOsc κ δ :=
  gammaOsc_pos_iff.2 (v5Admissible_acCompatible h)

/-- `gamma_+ > 0`, version 5 line 754.  It needs only `3 delta < 80
lambda`, which admissibility gives with room to spare. -/
lemma gammaPlus_pos {κ δ : ℝ} (h : V5Admissible κ δ) : 0 < gammaPlus δ := by
  obtain ⟨hκ, _, hc⟩ := h
  unfold gammaPlus
  linarith

/-- `gamma <= gamma_+`: the pre-resonance rate is the smaller one, which
is why `c_osc` of line 771 is governed by `gamma/2` whenever `kappa` is
not tiny. -/
lemma gammaOsc_le_gammaPlus {κ δ : ℝ} (h : V5Admissible κ δ) :
    gammaOsc κ δ ≤ gammaPlus δ := by
  unfold gammaOsc gammaPlus
  linarith [h.1]

/-- `2 log phi > 0`, so version 5's stated anti-concentration constant is
admissible input to `cAC`. -/
lemma cAntiV5_pos : 0 < cAntiV5 := by
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hphi : (1 : ℝ) < (1 + Real.sqrt 5) / 2 := by linarith
  have h : 0 < Real.log ((1 + Real.sqrt 5) / 2) := Real.log_pos hphi
  unfold cAntiV5
  linarith

lemma cAC_le_kappa (cAnti κ : ℝ) : cAC cAnti κ ≤ κ := min_le_left _ _

lemma cAC_le_two_hundred_cAnti (cAnti κ : ℝ) : cAC cAnti κ ≤ 200 * cAnti := min_le_right _ _

lemma cAC_pos {cAnti κ : ℝ} (hκ : 0 < κ) (hc : 0 < cAnti) : 0 < cAC cAnti κ :=
  lt_min hκ (by linarith)

lemma cOsc_pos {cAnti κ δ : ℝ} (h : V5Admissible κ δ) (hc : 0 < cAnti) :
    0 < cOsc cAnti κ δ :=
  lt_min (cAC_pos h.1 hc)
    (lt_min (by linarith [gammaOsc_pos h]) (by linarith [gammaPlus_pos h]))

lemma cOsc_le_cAC (cAnti κ δ : ℝ) : cOsc cAnti κ δ ≤ cAC cAnti κ := min_le_left _ _

lemma cOsc_le_gammaOsc_half (cAnti κ δ : ℝ) : cOsc cAnti κ δ ≤ gammaOsc κ δ / 2 :=
  le_trans (min_le_right _ _) (min_le_left _ _)

lemma cOsc_le_gammaPlus_half (cAnti κ δ : ℝ) : cOsc cAnti κ δ ≤ gammaPlus δ / 2 :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-- **The version 5 ledger is unconditionally nonempty.**  Contrast
`P42Cases.exists_compat`, which needed `delta <= 1` and a positive decay
constant `c0` from the anti-concentration lemma; both of those entered
only through ledger entries that version 5 retires. -/
theorem exists_v5Admissible : ∃ κ δ : ℝ, V5Admissible κ δ := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  have := Prop42.eighty_lyapunov_bounds.1
  linarith

/-! ## 2. The error bracket of version 5, and its equivalence with ours

Version 5 lines 643-645 write the bracket with three exponents.  The
collapse below is the only thing needed to see that this is the same
statement as ours, and it is the reason no proved theorem has to be
touched. -/

/-- **The collapse.**  With `c = min(c_ld, c_osc, c_mix)` every summand
of the version 5 bracket only grows, so the version 5 bracket is
dominated by our uniform one.  Together with the trivial specialisation
`c_ld = c_osc = c_mix = c` this makes the two statements of Proposition
4.2 equivalent. -/
lemma bracket_collapse {C cld cosc cmix c ρ L H : ℝ}
    (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hH : 0 ≤ H)
    (hcld : c ≤ cld) (hcosc : c ≤ cosc) (hcmix : c ≤ cmix) :
    C * (Real.exp (-cld * Real.sqrt L) + Real.exp (-cosc * H) + ρ ^ (cmix * H))
      ≤ C * (Real.exp (-c * Real.sqrt L) + Real.exp (-c * H) + ρ ^ (c * H)) := by
  have hsq : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have e1 : Real.exp (-cld * Real.sqrt L) ≤ Real.exp (-c * Real.sqrt L) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-cosc * H) ≤ Real.exp (-c * H) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : ρ ^ (cmix * H) ≤ ρ ^ (c * H) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by nlinarith)
  exact mul_le_mul_of_nonneg_left (by linarith) hC

/-! ## 3. Proposition 4.2 in the version 5 constant structure -/

/-- **Proposition 4.2, version 5** (Two-block factorization), lines
636-650.  For fixed finite linear combinations `U, V` of cylinder-torus
monomials, all but `O_{U,V}(LH)` pairs `j < k` in `J_n` satisfy

`|∫ U_j V_k dα - ∫U dμ̂₀ ∫V dμ̂₀| ≤ C(e^{-c_ld √L} + e^{-c_osc H} + ρ^{c_mix H})`

with `c_ld, c_osc, c_mix > 0` depending on `U, V`.

Derived from `Kwon1002.prop_4_2_two_block_factorization'` by taking the
three exponents equal, so the version 5 separation costs nothing and the
whole supporting apparatus of `Prop42`, `MonomialCore` and `P42Cases`
carries over unchanged. -/
theorem prop_4_2_v5 {R K : ℕ} (U V : WindowSymbol R K) :
    ∃ C cld cosc cmix ρ : ℝ,
      0 < C ∧ 0 < cld ∧ 0 < cosc ∧ 0 < cmix ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-cld * Real.sqrt (Lnorm n))
                      + Real.exp (-cosc * Hscale n) + ρ ^ (cmix * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n := by
  obtain ⟨C, c, ρ, hC, hc, hρ0, hρ1, hmain⟩ := prop_4_2_two_block_factorization' U V
  exact ⟨C, c, c, c, ρ, hC, hc, hc, hc, hρ0, hρ1, hmain⟩

/-- **The converse.**  From the version 5 three-exponent statement one
recovers our one-exponent statement, by taking
`c = min(c_ld, c_osc, c_mix)`.  Hence the two are equivalent and the
version 5 statement is unchanged in substance: it is neither stronger nor
weaker than `Kwon1002.prop_4_2_two_block_factorization`. -/
theorem prop_4_2_uniform_of_v5 {R K : ℕ} (U V : WindowSymbol R K)
    (h : ∃ C cld cosc cmix ρ : ℝ,
      0 < C ∧ 0 < cld ∧ 0 < cosc ∧ 0 < cmix ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-cld * Real.sqrt (Lnorm n))
                      + Real.exp (-cosc * Hscale n) + ρ ^ (cmix * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                      + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n := by
  classical
  obtain ⟨C, cld, cosc, cmix, ρ, hC, hcld, hcosc, hcmix, hρ0, hρ1, hmain⟩ := h
  refine ⟨C, min cld (min cosc cmix), ρ, hC, lt_min hcld (lt_min hcosc hcmix), hρ0, hρ1, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop 1] with n hn hn1
  have hL : (0 : ℝ) ≤ Lnorm n := Real.log_nonneg (by exact_mod_cast hn1)
  have hH : (0 : ℝ) ≤ Hscale n := Real.rpow_nonneg hL _
  have hcollapse := bracket_collapse (C := C) (cld := cld) (cosc := cosc) (cmix := cmix)
    (c := min cld (min cosc cmix)) (ρ := ρ) (L := Lnorm n) (H := Hscale n)
    hC.le hρ0 hρ1.le hH (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))
    (le_trans (min_le_right _ _) (min_le_right _ _))
  refine le_trans ?_ hn
  refine Nat.cast_le.2 (Set.ncard_le_ncard ?_
    (Set.Finite.subset (bulkPairs n).finite_toSet (Set.sep_subset _ _)))
  rintro p ⟨hp1, hp2⟩
  exact ⟨hp1, fun hle => hp2 (le_trans hle hcollapse)⟩

/-! ## 4. The pre-resonance branch at the version 5 constants

Version 5 lines 690-708 (later mode nonzero) and 734-744 (earlier mode
nonzero, `k < t_0 - 100H`) both end in

`log (q_{t_-}^2 / (n |Q|)) <= -gamma H + O(1)`,   `q_{t_-}^2 <= e^{-gamma H/2} n |Q|`.

`Prop42.retained_descendant_exponent` already produces the rate
`80 lambda - 3 delta - kappa`, which is precisely `gamma`.  The only
thing version 5 changes is that the conclusion is written with `gamma/2`
rather than with the anti-concentration letter, which removes the
hypothesis `2 kappa + 3 delta < 80 lambda` that
`P42Cases.retained_descendant_at_compat` had to carry. -/

/-- `2 e^A <= e^{(gamma/2) H}` for all large `n`: the absorption of the
`O(1)` of version 5 line 700 into the halved exponent of line 703.  This
is where `gamma > 0`, hence `V5Admissible`, is actually used. -/
lemma exp_absorb_eventually {γ A : ℝ} (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.exp A ≤ Real.exp (γ / 2 * Hscale n) := by
  have h1 : Filter.Tendsto (fun n : ℕ => γ / 2 * Hscale n) atTop atTop :=
    P42Cases.tendsto_Hscale.const_mul_atTop (by linarith : (0 : ℝ) < γ / 2)
  have h2 : Filter.Tendsto (fun n : ℕ => Real.exp (γ / 2 * Hscale n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp h1
  exact h2.eventually_ge_atTop (2 * Real.exp A)

/-- **The retained-descendant line at the version 5 constants**, version
5 lines 695-703.

Compared with `P42Cases.retained_descendant_at_compat`, the hypothesis
`2 kappa + 3 delta < 80 lambda` is gone.  The residual side condition
`habs` is the `O(1)` absorption, which holds eventually for any
admissible pair by `retained_descendant_absorb`. -/
lemma retained_descendant_v5 {L H κ δ A t k qt qk Q nn : ℝ}
    (hqt0 : 0 ≤ qt)
    (hqt : qt ≤ Real.exp (lyapunov * t + δ * H))
    (hqk : Real.exp (lyapunov * k - δ * H) ≤ qk)
    (hQ : (1 / 2) * Real.exp (-κ * H) * qk ≤ Q)
    (hnn : Real.exp L ≤ nn)
    (ht : 2 * (lyapunov * t) = L + lyapunov * k - 80 * lyapunov * H + A)
    (habs : 2 * Real.exp A ≤ Real.exp (gammaOsc κ δ / 2 * H)) :
    qt ^ 2 ≤ Real.exp (-(gammaOsc κ δ) / 2 * H) * (nn * Q) := by
  have hbase := Prop42.retained_descendant_exponent hqt0 hqt hqk hQ hnn ht
  have hqk0 : 0 ≤ qk := le_trans (Real.exp_pos _).le hqk
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
  have hnn0 : 0 ≤ nn := le_trans (Real.exp_pos _).le hnn
  have hrate : -(80 * lyapunov - 3 * δ - κ) * H = -(gammaOsc κ δ) * H := by
    unfold gammaOsc; ring
  rw [hrate] at hbase
  refine le_trans hbase ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnn0 hQ0)
  have hstep : 2 * Real.exp A * Real.exp (-(gammaOsc κ δ) * H)
      ≤ Real.exp (gammaOsc κ δ / 2 * H) * Real.exp (-(gammaOsc κ δ) * H) :=
    mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
  refine le_trans hstep (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  ring

/-- The absorption hypothesis of `retained_descendant_v5` holds for all
large `n` under version 5 admissibility alone. -/
lemma retained_descendant_absorb {κ δ A : ℝ} (hadm : V5Admissible κ δ) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.exp A ≤ Real.exp (gammaOsc κ δ / 2 * Hscale n) :=
  exp_absorb_eventually (A := A) (gammaOsc_pos hadm)

/-! ## 5. The post-resonance branch, version 5 lines 746-755

This branch is new relative to the earlier draft.  It bounds
`q_{t_+}^2 / (n |Q_j|)` from below by `e^{gamma_+ H + O(1)}`, using the
denominator lower bound at `t_+`, the denominator upper bound at `j`, and
the trivial upper frequency bound `|Q_j| <= C_{r_1,s_1} q_j` (which is
`Prop42.abs_Qfreq_le`, with `C_{r_1,s_1} = |r_1| + |s_1|`).  No `kappa`
appears: the rate is `gamma_+ = 80 lambda - 3 delta`, strictly larger
than `gamma`. -/

/-- **The retained-ascendant exponent**, version 5 lines 748-753.  With
`2 lambda t_+ = L + lambda j + 80 lambda H + O(1)`,

`log (q_{t_+}^2 / (n |Q_j|)) >= (80 lambda - 3 delta) H + O(1)`. -/
lemma retained_ascendant_exponent {L H δ A t j qt qj Q nn Cq : ℝ}
    (hCq : 0 < Cq) (hQ0 : 0 ≤ Q) (_hnn0 : 0 ≤ nn)
    (hqt : Real.exp (lyapunov * t - δ * H) ≤ qt)
    (hqj : qj ≤ Real.exp (lyapunov * j + δ * H))
    (hQ : Q ≤ Cq * qj)
    (hnn : nn ≤ Real.exp L)
    (ht : 2 * (lyapunov * t) = L + lyapunov * j + 80 * lyapunov * H + A) :
    Real.exp A / Cq * Real.exp (gammaPlus δ * H) * (nn * Q) ≤ qt ^ 2 := by
  have hqt0 : (0 : ℝ) ≤ qt := le_trans (Real.exp_pos _).le hqt
  have h1 : Real.exp (L + lyapunov * j + 80 * lyapunov * H + A - 2 * (δ * H)) ≤ qt ^ 2 := by
    have hsq : (Real.exp (lyapunov * t - δ * H)) ^ 2 ≤ qt ^ 2 := by
      nlinarith [hqt0, hqt, (Real.exp_pos (lyapunov * t - δ * H)).le]
    refine le_trans (le_of_eq ?_) hsq
    rw [pow_two, ← Real.exp_add]
    congr 1
    linarith
  have hexpsum : Real.exp L * Real.exp (lyapunov * j + δ * H)
      = Real.exp (L + lyapunov * j + δ * H) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : nn * Q ≤ Cq * Real.exp (L + lyapunov * j + δ * H) := by
    have e1 : Q ≤ Cq * Real.exp (lyapunov * j + δ * H) :=
      le_trans hQ (mul_le_mul_of_nonneg_left hqj hCq.le)
    have e2 : nn * Q ≤ Real.exp L * (Cq * Real.exp (lyapunov * j + δ * H)) :=
      mul_le_mul hnn e1 hQ0 (Real.exp_pos _).le
    refine le_trans e2 (le_of_eq ?_)
    calc Real.exp L * (Cq * Real.exp (lyapunov * j + δ * H))
        = Cq * (Real.exp L * Real.exp (lyapunov * j + δ * H)) := by ring
      _ = Cq * Real.exp (L + lyapunov * j + δ * H) := by rw [hexpsum]
  have hfac : (0 : ℝ) ≤ Real.exp A / Cq * Real.exp (gammaPlus δ * H) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left h2 hfac) (le_trans (le_of_eq ?_) h1)
  have hcancel : Real.exp A / Cq * Real.exp (gammaPlus δ * H)
        * (Cq * Real.exp (L + lyapunov * j + δ * H))
      = (Cq / Cq) * (Real.exp A * Real.exp (gammaPlus δ * H)
        * Real.exp (L + lyapunov * j + δ * H)) := by
    ring
  rw [hcancel, div_self (ne_of_gt hCq), one_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold gammaPlus
  ring

/-- **The retained-ascendant line at the version 5 constants**, version 5
lines 754-755: `q_{t_+}^2 >= e^{gamma_+ H/2} n |Q_j|`, which is the
hypothesis of the phase-freezing display with
`epsilon = e^{-gamma_+ H/2}`. -/
lemma retained_ascendant_v5 {L H δ A t j qt qj Q nn Cq : ℝ}
    (hCq : 0 < Cq) (hQ0 : 0 ≤ Q) (hnn0 : 0 ≤ nn)
    (hqt : Real.exp (lyapunov * t - δ * H) ≤ qt)
    (hqj : qj ≤ Real.exp (lyapunov * j + δ * H))
    (hQ : Q ≤ Cq * qj)
    (hnn : nn ≤ Real.exp L)
    (ht : 2 * (lyapunov * t) = L + lyapunov * j + 80 * lyapunov * H + A)
    (habs : Cq ≤ Real.exp A * Real.exp (gammaPlus δ / 2 * H)) :
    Real.exp (gammaPlus δ / 2 * H) * (nn * Q) ≤ qt ^ 2 := by
  refine le_trans ?_ (retained_ascendant_exponent hCq hQ0 hnn0 hqt hqj hQ hnn ht)
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnn0 hQ0)
  have hrw : Real.exp A / Cq * Real.exp (gammaPlus δ * H)
      = (Real.exp A * Real.exp (gammaPlus δ * H)) / Cq := by ring
  rw [hrw, le_div_iff₀ hCq]
  have hstep := mul_le_mul_of_nonneg_left habs
    (Real.exp_pos (gammaPlus δ / 2 * H)).le
  have hhalf : Real.exp (gammaPlus δ / 2 * H) * Real.exp (gammaPlus δ / 2 * H)
      = Real.exp (gammaPlus δ * H) := by
    rw [← Real.exp_add]; congr 1; ring
  refine le_trans hstep (le_of_eq ?_)
  calc Real.exp (gammaPlus δ / 2 * H) * (Real.exp A * Real.exp (gammaPlus δ / 2 * H))
      = Real.exp A * (Real.exp (gammaPlus δ / 2 * H) * Real.exp (gammaPlus δ / 2 * H)) := by
        ring
    _ = Real.exp A * Real.exp (gammaPlus δ * H) := by rw [hhalf]

/-- The `O(1)` absorption for the post-resonance branch: for a fixed
frequency constant `C_{r_1,s_1}` the side condition of
`retained_ascendant_v5` holds for all large `n`, using only
`gamma_+ > 0`. -/
lemma retained_ascendant_absorb {κ δ A Cq : ℝ} (hadm : V5Admissible κ δ) :
    ∀ᶠ n : ℕ in atTop, Cq ≤ Real.exp A * Real.exp (gammaPlus δ / 2 * Hscale n) := by
  have hγ : 0 < gammaPlus δ := gammaPlus_pos hadm
  have h1 : Filter.Tendsto (fun n : ℕ => gammaPlus δ / 2 * Hscale n) atTop atTop :=
    P42Cases.tendsto_Hscale.const_mul_atTop (by linarith : (0 : ℝ) < gammaPlus δ / 2)
  have h2 : Filter.Tendsto (fun n : ℕ => Real.exp (gammaPlus δ / 2 * Hscale n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp h1
  filter_upwards [h2.eventually_ge_atTop (Cq / Real.exp A)] with n hn
  rw [div_le_iff₀ (Real.exp_pos A)] at hn
  calc Cq ≤ Real.exp (gammaPlus δ / 2 * Hscale n) * Real.exp A := hn
    _ = Real.exp A * Real.exp (gammaPlus δ / 2 * Hscale n) := by ring

/-! ## 6. The anti-concentration mass at the version 5 constants

Version 5 lines 673-675 replace the ledger entry `c <= 200 c_0` of
`P42Cases.Compat` by a `min`.  The result is unconditional. -/

/-- **Version 5 lines 670-675.**  At a bulk index `k >= 200 H` the
discarded anti-concentration mass `e^{-kappa H} + e^{-c_anti k}` is
`O(e^{-c_ac H})` with `c_ac = min(kappa, 200 c_anti)`, with no
compatibility hypothesis relating `kappa` to `c_anti`.  This retires the
ledger entry `P42Cases.antiConc_ground`, which required `c <= 200 c_0`. -/
lemma antiConc_v5 {cAnti κ H k : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ cAnti) (hbulk : 200 * H ≤ k) :
    Real.exp (-κ * H) + Real.exp (-cAnti * k) ≤ 2 * Real.exp (-(cAC cAnti κ) * H) := by
  have e1 : Real.exp (-κ * H) ≤ Real.exp (-(cAC cAnti κ) * H) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [cAC_le_kappa cAnti κ]
  have e2 : Real.exp (-cAnti * k) ≤ Real.exp (-(cAC cAnti κ) * H) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [cAC_le_two_hundred_cAnti cAnti κ]
  linarith

/-! ## 7. The mixing gap at the version 5 constant `c_mix`

Version 5 lines 758-760 say the later zero-mode block starts at least
`c_mix H` after `t_+` "for some `c_mix > 0` and all large `n`".  Since
`c_mix` is now an independent existential, the ledger entry `c <= 60` of
`P42Cases.Compat` no longer couples to `kappa`. -/

/-- **Version 5 lines 758-760.**  With `k > t_0 + 100H`,
`t_+ <= t_0 + 40H` and a fixed window radius `R`, the later block starts
more than `59 H` after `t_+`, for all large `n`.  The witness `59` is any
constant below `60`; the point is that it is independent of `kappa` and
`delta`. -/
lemma cmix_gap_eventually (Rr : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ t₀ tplus k : ℝ,
      tplus ≤ t₀ + 40 * Hscale n → t₀ + 100 * Hscale n < k →
      59 * Hscale n < (k - Rr) - tplus := by
  filter_upwards [P42Cases.mixingGap_eventually (c := 59) (Rr := Rr) (by norm_num),
    eventually_ge_atTop 1] with n hn hn1
  intro t₀ tplus k htp hk
  have hL : (0 : ℝ) ≤ Lnorm n := Real.log_nonneg (by exact_mod_cast hn1)
  have hH : (0 : ℝ) ≤ Hscale n := Real.rpow_nonneg hL _
  exact P42Cases.mixingGap_ground hH htp hk hn

/-! ## 8. Restoring the discarded cylinders, version 5 lines 762-765

"Extend this replacement to the discarded depth-`t_+` cylinders and
restore them, at cost `O(e^{-c_ld L^{1/2}})`; no future cutoff indicator
then remains in the earlier integral."  This step is new in version 5 and
is what makes the earlier phase integral free of a future-measurable
indicator.  The bookkeeping is the triangle estimate below: once the
stationary replacement has been extended to the discarded part, the
retained and discarded pieces recombine at twice the discarded mass. -/

/-- **Version 5 lines 762-765.**  If the two-block integral splits as
`I = I_ret + I_disc`, the stationary product splits as
`S = S_ret + S_disc`, the retained parts agree to `err`, and both
discarded parts are bounded by the discarded mass, then the whole
difference is bounded by `err + 2 * mass`.  With
`mass = O(e^{-c_ld L^{1/2}})` this is exactly the cost version 5
quotes. -/
lemma restore_discarded {I Ir Id S Sr Sd : ℂ} {err mass : ℝ}
    (hI : I = Ir + Id) (hS : S = Sr + Sd)
    (hmain : ‖Ir - Sr‖ ≤ err) (hId : ‖Id‖ ≤ mass) (hSd : ‖Sd‖ ≤ mass) :
    ‖I - S‖ ≤ err + 2 * mass := by
  subst hI
  subst hS
  have hsplit : Ir + Id - (Sr + Sd) = (Ir - Sr) + (Id - Sd) := by ring
  rw [hsplit]
  have h1 : ‖(Ir - Sr) + (Id - Sd)‖ ≤ ‖Ir - Sr‖ + ‖Id - Sd‖ := norm_add_le _ _
  have h2 : ‖Id - Sd‖ ≤ ‖Id‖ + ‖Sd‖ := norm_sub_le _ _
  linarith

/-! ## 9. Summary of the reconciliation

* `prop_4_2_v5` and `prop_4_2_uniform_of_v5` together show that version
  5's display (34) and `Kwon1002.prop_4_2_two_block_factorization` are
  the same statement.  No supporting lemma is invalidated.
* `Prop42.retained_rate_pos_iff` is now literally a manuscript line
  (`gammaOsc_pos_iff`, version 5 line 662).
* `P42Cases.retained_descendant_at_compat` is superseded by
  `retained_descendant_v5` plus `retained_descendant_absorb`, which drop
  the hypothesis `2 kappa + 3 delta < 80 lambda`.
* `P42Cases.antiConc_ground` is superseded by `antiConc_v5`, which drops
  the hypothesis `c <= 200 c_0`.
* `P42Cases.Compat` survives as a correct but now unnecessarily strong
  ledger; `V5Admissible` is the version 5 replacement, and
  `exists_v5Admissible` needs no side conditions.
* `retained_ascendant_exponent`, `retained_ascendant_v5` and
  `retained_ascendant_absorb` are new and cover version 5 lines 746-755,
  for which the development previously had nothing.
* `restore_discarded` covers version 5 lines 762-765.
* The three sorried case bounds of `MonomialCore` are untouched: version
  5 does not change what they assert, and their common missing input,
  `P42Cases.Display20`, is version 5's `c_ld` estimate. -/

end

end V5Prop42

end Kwon1002
