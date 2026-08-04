/-
Scratch file (BV-induced agent):

  **A BV LASOTA-YORKE INEQUALITY FOR THE GAUSS TRANSFER OPERATOR**

attacked via the *second* iterate, where the two-branch contraction is
unconditionally `≤ 1/4` (manuscript line ≈ 205: "On two-step inverse
branches the contraction is at most 1/2").

Kwon's §3 asserts, with no proof beyond one sentence,

    Var(L² f) ≤ ρ₀ Var(f) + C ‖f‖₁ ,   ρ₀ < 1,

and then invokes Helly compactness to get Lemma 3.1(i) at BV generality.
Nothing of this exists in mathlib, in Wang's substrate, or anywhere in
`Kwon1002/`.  It is the single ingredient gating §4 (whose observables are
digit indicators: `TransferIdentity.firstDigitIndicator_bv` /
`firstDigitIndicator_not_lipschitz`).

What is delivered here:

* §1  a general `eVariationOn` toolkit that mathlib does not have
      (increment-comparison, subadditivity, the Leibniz/product rule,
      Lipschitz ⇒ variation, countable subadditivity, and
      `sup ≤ Var + mean`);                                       [PROVED]
* §2  the abstract Lasota-Yorke bootstrap: one `L²` inequality with
      `ρ < 1` plus `L¹`-contractivity gives the bound for every `L^n`,
      even and odd;                                              [PROVED]
* §3  the two-step branch geometry of the Gauss map with *explicit*
      constants: `sup |W_{q,r}| ≤ 1/4`, `Var(W_{q,r}) ≤ 1/4`,
      `|Ψ_{q,r}(y) − Ψ_{q,r}(z)| ≤ ¼|y−z|`, and the exact rank-2
      cylinder length `1/((r(q+1)+1)(rq+1))`; and then **the heart of
      Lasota-Yorke one branch at a time**
      (`branch_term_lasotaYorke`), which is where `ρ = 1/2` is actually
      produced.                                                  [PROVED]
* §4  the `L²` Lasota-Yorke inequality itself, with `ρ = 1/2`,
      `C = 128`, **derived** (not assumed) from the branchwise heart via
      the summation step `lasotaYorke_of_branchwise`, modulo exactly six
      analytic inputs, each stated faithfully with its obstruction
      named.                                     [DERIVED from 6 SORRIES]

Everything marked [PROVED] is `#print axioms`-clean:
`[propext, Classical.choice, Quot.sound]` (checked, then removed).

The six remaining sorries are INPUTS 1, 1', 2, 3, 4, 5 in §4.  Note in
particular that the *rate* `ρ = 1/2` is nowhere assumed: it is computed
from `abs_weight2_le_quarter` + `eVariationOn_weight2_le_quarter`, both
proved.  The sorried inputs are (i) two `tsum`-rearrangement facts,
(ii) the `ω²`-order tiling of the rank-2 cylinders, (iii) the sharp
`Var(W_{q,r}) ≤ 90 |I_{q,r}|` envelope, (iv) `L¹`-contractivity of
`gaussTransfer`, (v) the Lebesgue↔Gauss density comparison.

Nothing in this file is imported by any shared module.
-/
import Kwon1002.TransferMixing
import Mathlib.Analysis.BoundedVariation

open MeasureTheory Set
open scoped ENNReal

namespace Kwon1002.BVIterate

open Erdos1002

noncomputable section

/-! ## 1.  A general toolkit for `eVariationOn`

Mathlib's `eVariationOn` API has `mono`, `union`, `add_le_union`, `sum`,
`comp_*` and the monotone bound, but **no** algebra: no subadditivity under
sums of functions, no product rule, no `Lipschitz ⇒ Var ≤ K·length`.  All of
these are needed for any Lasota-Yorke argument, so they are proved here from
the definition. -/

/-- Real `edist` in the form used repeatedly below. -/
theorem edist_real_le {x y c : ℝ} (h : |x - y| ≤ c) :
    edist x y ≤ ENNReal.ofReal c := by
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal h

/-- **Increment comparison (two terms).**  A pointwise bound on increments
by a linear combination of the increments of two other functions transfers
verbatim to the variations.  This is the engine of everything below. -/
theorem eVariationOn_le_two {s : Set ℝ} {h f g : ℝ → ℝ} {a b : ℝ≥0∞}
    (H : ∀ x ∈ s, ∀ y ∈ s,
      edist (h x) (h y) ≤ a * edist (f x) (f y) + b * edist (g x) (g y)) :
    eVariationOn h s ≤ a * eVariationOn f s + b * eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc (∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i)))
      ≤ ∑ i ∈ Finset.range n,
          (a * edist (f (u (i + 1))) (f (u i))
            + b * edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => H _ (us _) _ (us _)
    _ = a * (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + b * (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * eVariationOn f s + b * eVariationOn g s := by
        gcongr
        · exact eVariationOn.sum_le f n hu us
        · exact eVariationOn.sum_le g n hu us

/-- **Increment comparison (one term).** -/
theorem eVariationOn_le_one {s : Set ℝ} {h f : ℝ → ℝ} {a : ℝ≥0∞}
    (H : ∀ x ∈ s, ∀ y ∈ s, edist (h x) (h y) ≤ a * edist (f x) (f y)) :
    eVariationOn h s ≤ a * eVariationOn f s := by
  have := eVariationOn_le_two (s := s) (h := h) (f := f) (g := f) (a := a)
    (b := 0) (by intro x hx y hy; simpa using H x hx y hy)
  simpa using this

/-- Subadditivity of the variation under sums of functions. -/
theorem eVariationOn_add_le {s : Set ℝ} (f g : ℝ → ℝ) :
    eVariationOn (fun x => f x + g x) s
      ≤ eVariationOn f s + eVariationOn g s := by
  have := eVariationOn_le_two (s := s) (h := fun x => f x + g x) (f := f)
    (g := g) (a := 1) (b := 1) ?_
  · simpa using this
  · intro x _ y _
    simp only [one_mul]
    rw [edist_dist, Real.dist_eq, edist_dist, Real.dist_eq, edist_dist,
      Real.dist_eq, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by
          congr 1; ring
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _

/-- **Leibniz rule for the variation.**  If `|f| ≤ Mf` and `|g| ≤ Mg` on `s`
then `Var(fg) ≤ Mf · Var g + Mg · Var f`.  Not in mathlib. -/
theorem eVariationOn_mul_le {s : Set ℝ} {f g : ℝ → ℝ} {Mf Mg : ℝ}
    (hMf : ∀ x ∈ s, |f x| ≤ Mf) (hMg : ∀ x ∈ s, |g x| ≤ Mg) :
    eVariationOn (fun x => f x * g x) s
      ≤ ENNReal.ofReal Mf * eVariationOn g s
        + ENNReal.ofReal Mg * eVariationOn f s := by
  apply eVariationOn_le_two
  intro x hx y hy
  have hMf0 : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf x hx)
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hMg y hy)
  have key : |f x * g x - f y * g y| ≤ Mf * |g x - g y| + Mg * |f x - f y| := by
    have hrw : f x * g x - f y * g y
        = f x * (g x - g y) + g y * (f x - f y) := by ring
    rw [hrw]
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |f x * (g x - g y)| ≤ Mf * |g x - g y| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hMf x hx) (abs_nonneg _)
    have h2 : |g y * (f x - f y)| ≤ Mg * |f x - f y| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hMg y hy) (abs_nonneg _)
    linarith
  rw [edist_dist, Real.dist_eq, edist_dist, Real.dist_eq, edist_dist,
    Real.dist_eq, ← ENNReal.ofReal_mul hMf0, ← ENNReal.ofReal_mul hMg0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal key

/-- The variation of the identity on `[a,b]` is at most `b - a`. -/
theorem eVariationOn_id_Icc_le {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (fun x : ℝ => x) (Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hmono : MonotoneOn (fun x : ℝ => x) (Icc a b) := fun _ _ _ _ hxy => hxy
  have h := hmono.eVariationOn_le (Set.left_mem_Icc.2 hab)
    (Set.right_mem_Icc.2 hab)
  rwa [Set.inter_self] at h

/-- **Lipschitz ⇒ bounded variation, with the sharp constant.** -/
theorem eVariationOn_le_of_lipschitz_Icc {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    {f : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ K * |x - y|) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (K * (b - a)) := by
  have hstep : eVariationOn f (Icc a b)
      ≤ ENNReal.ofReal K * eVariationOn (fun x : ℝ => x) (Icc a b) := by
    apply eVariationOn_le_one
    intro x hx y hy
    rw [edist_dist, Real.dist_eq, edist_dist, Real.dist_eq,
      ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hf x hx y hy)
  refine le_trans hstep ?_
  rw [ENNReal.ofReal_mul hK]
  gcongr
  exact eVariationOn_id_Icc_le hab

/-- The `edist` of two real tsums is dominated by the tsum of the `edist`s. -/
theorem edist_tsum_le {ι : Type*} {g h : ι → ℝ} (hg : Summable g)
    (hh : Summable h) :
    edist (∑' j, g j) (∑' j, h j) ≤ ∑' j, edist (g j) (h j) := by
  have hsub : Summable fun j => g j - h j := hg.sub hh
  have habs : Summable fun j => |g j - h j| := hsub.abs
  have hnorm : Summable fun j => ‖g j - h j‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have h1 : |∑' j, (g j - h j)| ≤ ∑' j, |g j - h j| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  have h2 : ENNReal.ofReal (∑' j, |g j - h j|)
      = ∑' j, ENNReal.ofReal |g j - h j| :=
    ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) habs
  have h3 : ∀ j, ENNReal.ofReal |g j - h j| = edist (g j) (h j) := by
    intro j; rw [edist_dist, Real.dist_eq]
  rw [edist_dist, Real.dist_eq, ← hg.tsum_sub hh]
  refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
  rw [h2]
  exact le_of_eq (tsum_congr h3)

/-- **Countable subadditivity of the variation.**  Needed because the
transfer operator is an infinite sum over inverse branches. -/
theorem eVariationOn_tsum_le {ι : Type*} {s : Set ℝ} {F : ι → ℝ → ℝ}
    (hsum : ∀ x ∈ s, Summable fun i => F i x) :
    eVariationOn (fun y => ∑' i, F i y) s ≤ ∑' i, eVariationOn (F i) s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have step : ∀ i : ℕ,
      edist (∑' j, F j (u (i + 1))) (∑' j, F j (u i))
        ≤ ∑' j, edist (F j (u (i + 1))) (F j (u i)) :=
    fun i => edist_tsum_le (hsum _ (us (i + 1))) (hsum _ (us i))
  calc (∑ i ∈ Finset.range n,
        edist ((fun y => ∑' j, F j y) (u (i + 1)))
          ((fun y => ∑' j, F j y) (u i)))
      ≤ ∑ i ∈ Finset.range n, ∑' j, edist (F j (u (i + 1))) (F j (u i)) :=
        Finset.sum_le_sum fun i _ => step i
    _ = ∑' j, ∑ i ∈ Finset.range n, edist (F j (u (i + 1))) (F j (u i)) :=
        (Summable.tsum_finsetSum fun i _ => ENNReal.summable).symm
    _ ≤ ∑' j, eVariationOn (F j) s :=
        ENNReal.tsum_le_tsum fun j => eVariationOn.sum_le (F j) n hu us

/-- **`sup ≤ Var + mean`.**  The second half of every Lasota-Yorke
argument: on an interval, the sup-norm is controlled by the variation plus
the `L¹` average.  Proof: integrate `|f x| ≤ |f y| + Var` in `y`. -/
theorem abs_le_variation_add_average {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    {V : ℝ} (hV0 : 0 ≤ V)
    (hV : eVariationOn f (Icc a b) ≤ ENNReal.ofReal V)
    (hint : IntegrableOn (fun y => |f y|) (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    |f x| ≤ V + (∫ y in Icc a b, |f y|) / (b - a) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hptwise : ∀ y ∈ Icc a b, |f x| ≤ |f y| + V := by
    intro y hy
    have h1 : edist (f x) (f y) ≤ ENNReal.ofReal V :=
      le_trans (eVariationOn.edist_le f hx hy) hV
    rw [edist_dist, Real.dist_eq] at h1
    have h2 : |f x - f y| ≤ V := by
      by_contra hcon
      push_neg at hcon
      exact absurd h1 (not_le.2 (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hV0 |>.2 hcon))
    have hrw : f x = f y + (f x - f y) := by ring
    calc |f x| = |f y + (f x - f y)| := by rw [← hrw]
      _ ≤ |f y| + |f x - f y| := abs_add_le _ _
      _ ≤ |f y| + V := by linarith
  have hcst : IntegrableOn (fun _ : ℝ => V) (Icc a b) :=
    (continuous_const).integrableOn_Icc
  have hle : (∫ _y in Icc a b, |f x|) ≤ ∫ y in Icc a b, (|f y| + V) := by
    refine setIntegral_mono_on (continuous_const).integrableOn_Icc
      (hint.add hcst) measurableSet_Icc ?_
    intro y hy
    exact hptwise y hy
  rw [setIntegral_const, integral_add hint hcst, setIntegral_const,
    Real.volume_real_Icc_of_le hab.le, smul_eq_mul, smul_eq_mul] at hle
  have hdiv : |f x| - V ≤ (∫ y in Icc a b, |f y|) / (b - a) := by
    rw [le_div_iff₀ hba]
    nlinarith [hle]
  linarith

/-! ## 2.  The abstract Lasota-Yorke bootstrap

One inequality for `L²` with `ρ < 1`, plus `L¹`-contractivity, gives the
bound for **every** `L^n`.  Everything is in `ℝ≥0∞`, so there is no hidden
finiteness assumption and no `toReal` truncation: an infinite-variation `f`
gives `V f = ⊤` and the inequalities remain true rather than becoming
vacuous.  This is the "iteration lemma" of the task. -/

section Abstract

variable {L : (ℝ → ℝ) → (ℝ → ℝ)} {V N : (ℝ → ℝ) → ℝ≥0∞} {ρ c d : ℝ≥0∞}

/-- `L¹`-contractivity propagates along iterates. -/
theorem N_iterate_le (hN : ∀ g, N (L g) ≤ N g) (k : ℕ) (f : ℝ → ℝ) :
    N ((L^[k]) f) ≤ N f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (hN _) ih

private theorem iterate_two (f : ℝ → ℝ) : (L^[2]) f = L (L f) := by
  simp [Function.iterate_succ_apply]

/-- **Even iterates.**  `d` plays the role of `c / (1 - ρ)`: the hypothesis
`ρ * d + c ≤ d` is exactly `d ≥ c/(1-ρ)`. -/
theorem lasotaYorke_iterate_even
    (hLY : ∀ g, V (L (L g)) ≤ ρ * V g + c * N g)
    (hN : ∀ g, N (L g) ≤ N g)
    (hd : ρ * d + c ≤ d)
    (m : ℕ) (f : ℝ → ℝ) :
    V ((L^[2 * m]) f) ≤ ρ ^ m * V f + d * N f := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hidx : 2 * (m + 1) = 2 + 2 * m := by ring
      rw [hidx, Function.iterate_add_apply, iterate_two]
      calc V (L (L ((L^[2 * m]) f)))
          ≤ ρ * V ((L^[2 * m]) f) + c * N ((L^[2 * m]) f) := hLY _
        _ ≤ ρ * (ρ ^ m * V f + d * N f) + c * N f := by
            gcongr
            exact N_iterate_le hN _ f
        _ = ρ ^ (m + 1) * V f + (ρ * d + c) * N f := by ring
        _ ≤ ρ ^ (m + 1) * V f + d * N f := by gcongr

/-- **Odd iterates.**  `e`, `g` are the constants of the (crude) one-step
inequality; no smallness is required of `e`. -/
theorem lasotaYorke_iterate_odd {e g : ℝ≥0∞}
    (hLY : ∀ h, V (L (L h)) ≤ ρ * V h + c * N h)
    (hN : ∀ h, N (L h) ≤ N h)
    (hstep : ∀ h, V (L h) ≤ e * V h + g * N h)
    (hd : ρ * d + c ≤ d)
    (m : ℕ) (f : ℝ → ℝ) :
    V ((L^[2 * m + 1]) f) ≤ ρ ^ m * (e * V f + g * N f) + d * N f := by
  rw [Function.iterate_add_apply, Function.iterate_one]
  calc V ((L^[2 * m]) (L f))
      ≤ ρ ^ m * V (L f) + d * N (L f) :=
        lasotaYorke_iterate_even hLY hN hd m (L f)
    _ ≤ ρ ^ m * (e * V f + g * N f) + d * N f := by
        gcongr
        · exact hstep f
        · exact hN f

/-- **All iterates.**  A single clean statement: the variation of `L^n f`
decays like `ρ^{⌊n/2⌋}` down to a fixed `L¹` floor. -/
theorem lasotaYorke_iterate {e g : ℝ≥0∞}
    (hρ : ρ ≤ 1)
    (hLY : ∀ h, V (L (L h)) ≤ ρ * V h + c * N h)
    (hN : ∀ h, N (L h) ≤ N h)
    (hstep : ∀ h, V (L h) ≤ e * V h + g * N h)
    (hd : ρ * d + c ≤ d)
    (n : ℕ) (f : ℝ → ℝ) :
    V ((L^[n]) f) ≤ ρ ^ (n / 2) * ((e + 1) * V f) + (g + d) * N f := by
  have hone : (1 : ℝ≥0∞) ≤ e + 1 := le_add_self
  rcases Nat.even_or_odd n with ⟨m', hm⟩ | ⟨m', hm⟩
  · have hn : n = 2 * m' := by omega
    have hdiv : n / 2 = m' := by omega
    subst hn
    rw [hdiv]
    refine le_trans (lasotaYorke_iterate_even hLY hN hd m' f) ?_
    refine add_le_add ?_ ?_
    · exact mul_le_mul_left' (le_mul_of_one_le_left' hone) _
    · exact mul_le_mul_right' (le_add_self : d ≤ g + d) _
  · have hn : n = 2 * m' + 1 := by omega
    have hdiv : n / 2 = m' := by omega
    subst hn
    rw [hdiv]
    refine le_trans (lasotaYorke_iterate_odd hLY hN hstep hd m' f) ?_
    have hpow' : ρ ^ m' ≤ 1 := by
      calc ρ ^ m' ≤ (1 : ℝ≥0∞) ^ m' := by gcongr
        _ = 1 := one_pow m'
    calc ρ ^ m' * (e * V f + g * N f) + d * N f
        = ρ ^ m' * (e * V f) + ρ ^ m' * (g * N f) + d * N f := by
          rw [mul_add]
      _ ≤ ρ ^ m' * ((e + 1) * V f) + 1 * (g * N f) + d * N f := by
          refine add_le_add (add_le_add ?_ ?_) le_rfl
          · exact mul_le_mul_left'
              (mul_le_mul_right' (le_self_add : e ≤ e + 1) _) _
          · exact mul_le_mul_right' hpow' _
      _ = ρ ^ m' * ((e + 1) * V f) + (g + d) * N f := by ring

end Abstract

/-! ## 3.  The two-step branch geometry of the Gauss map

`gaussTransfer f y = ∑_{q≥1} w_q(y) · f(ψ_q y)` with
`w_q = gaussBranchRatio q` and `ψ_q = gaussInverseBranch q`.  Iterating once
gives weights `W_{q,r} = w_q · (w_r ∘ ψ_q)` and inverse branches
`Ψ_{q,r} = ψ_r ∘ ψ_q`.

Everything in this section is proved, and it is exactly what pins the
Lasota-Yorke rate at `ρ = 1/2`:  `sup |W| ≤ 1/4` and `Var(W) ≤ 1/4`. -/

/-- `ψ_q` maps `[0,1]` into `[0,1]` for every positive digit. -/
theorem gaussInverseBranch_mem_Icc {q : ℕ} (hq : 0 < q) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : gaussInverseBranch q y ∈ Icc (0 : ℝ) 1 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < (q : ℝ) + y := by linarith [hy.1]
  constructor
  · exact le_of_lt (one_div_pos.mpr hden)
  · rw [gaussInverseBranch, div_le_one hden]; linarith [hy.1]

/-- `ψ_q` is `1`-Lipschitz on `[0,1]` (in fact `1/q²`-Lipschitz). -/
theorem gaussInverseBranch_lipschitz {q : ℕ} (hq : 0 < q) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussInverseBranch q y - gaussInverseBranch q z| ≤ |y - z| := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (0 : ℝ) < (q : ℝ) + y := by linarith [hy.1]
  have h2 : (0 : ℝ) < (q : ℝ) + z := by linarith [hz.1]
  have hrw : gaussInverseBranch q y - gaussInverseBranch q z
      = (z - y) / (((q : ℝ) + y) * ((q : ℝ) + z)) := by
    unfold gaussInverseBranch
    field_simp
    ring
  have hge : (1 : ℝ) ≤ ((q : ℝ) + y) * ((q : ℝ) + z) := by
    nlinarith [hy.1, hz.1]
  rw [hrw, abs_div, abs_of_pos (mul_pos h1 h2), abs_sub_comm]
  rw [div_le_iff₀ (mul_pos h1 h2)]
  nlinarith [abs_nonneg (y - z), hge]

/-- Every branch weight is at most `1/2` on `[0,1]`. -/
theorem gaussBranchRatio_le_half {q : ℕ} (hq : 0 < q) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : gaussBranchRatio q y ≤ 1 / 2 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ y := hy.1
  have hden : (0 : ℝ) < ((q : ℝ) + y) * ((q : ℝ) + y + 1) := by nlinarith
  unfold gaussBranchRatio
  rw [div_le_iff₀ hden]
  nlinarith

/-- `|w_q| ≤ 1/2` on `[0,1]`. -/
theorem abs_gaussBranchRatio_le_half {q : ℕ} (hq : 0 < q) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : |gaussBranchRatio q y| ≤ 1 / 2 := by
  rw [abs_of_pos (gaussBranchRatio_pos hq hy)]
  exact gaussBranchRatio_le_half hq hy

/-- **Uniform Lipschitz bound `1/4` for every branch weight.**  Assembles
the substrate's three cases (`q = 1`, `q = 2`, `q ≥ 3`). -/
theorem gaussBranchRatio_lipschitz_quarter {q : ℕ} (hq : 0 < q) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussBranchRatio q y - gaussBranchRatio q z| ≤ (1 / 4 : ℝ) * |y - z| := by
  rcases lt_or_ge q 3 with hlt | hge
  · interval_cases q
    · exact abs_gaussBranchRatio_one_sub_le hy hz
    · refine le_trans (abs_gaussBranchRatio_two_sub_le hy hz) ?_
      exact mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
  · refine le_trans (abs_gaussBranchRatio_sub_le_of_three_le hge hy hz) ?_
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hge
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- The two-step inverse branch `Ψ_{q,r} = ψ_r ∘ ψ_q`. -/
def branch2 (q r : ℕ) (y : ℝ) : ℝ :=
  gaussInverseBranch r (gaussInverseBranch q y)

/-- The two-step branch weight `W_{q,r} = w_q · (w_r ∘ ψ_q)`. -/
def weight2 (q r : ℕ) (y : ℝ) : ℝ :=
  gaussBranchRatio q y * gaussBranchRatio r (gaussInverseBranch q y)

/-- Closed form of the two-step branch: `Ψ_{q,r}(y) = (q+y)/(r(q+y)+1)`. -/
theorem branch2_eq {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    branch2 q r y = ((q : ℝ) + y) / ((r : ℝ) * ((q : ℝ) + y) + 1) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : (0 : ℝ) < (q : ℝ) + y := by linarith [hy.1]
  have h2 : (0 : ℝ) < (r : ℝ) * ((q : ℝ) + y) + 1 := by nlinarith
  have key : (r : ℝ) + 1 / ((q : ℝ) + y)
      = ((r : ℝ) * ((q : ℝ) + y) + 1) / ((q : ℝ) + y) := by
    field_simp
  unfold branch2 gaussInverseBranch
  rw [key, one_div_div]

/-- **Exact increment of the two-step branch.**  The denominator is
`≥ 4`, which is the two-branch contraction. -/
theorem branch2_sub_eq {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    branch2 q r y - branch2 q r z
      = (y - z) / ((((r : ℝ) * ((q : ℝ) + y) + 1))
          * (((r : ℝ) * ((q : ℝ) + z) + 1))) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : (0 : ℝ) < (q : ℝ) + y := by linarith [hy.1]
  have h1' : (0 : ℝ) < (q : ℝ) + z := by linarith [hz.1]
  have h2 : (0 : ℝ) < (r : ℝ) * ((q : ℝ) + y) + 1 := by nlinarith
  have h2' : (0 : ℝ) < (r : ℝ) * ((q : ℝ) + z) + 1 := by nlinarith
  rw [branch2_eq hq hr hy, branch2_eq hq hr hz]
  field_simp
  ring

/-- **The two-step contraction: `|Ψ_{q,r}(y) − Ψ_{q,r}(z)| ≤ ¼ |y − z|`.**
This is Kwon's "on two-step inverse branches the contraction is at most
1/2", proved here with the sharper constant `1/4`. -/
theorem branch2_contraction {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |branch2 q r y - branch2 q r z| ≤ (1 / 4 : ℝ) * |y - z| := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : (2 : ℝ) ≤ (r : ℝ) * ((q : ℝ) + y) + 1 := by nlinarith [hy.1]
  have h2' : (2 : ℝ) ≤ (r : ℝ) * ((q : ℝ) + z) + 1 := by nlinarith [hz.1]
  have hprod : (4 : ℝ) ≤ ((r : ℝ) * ((q : ℝ) + y) + 1)
      * ((r : ℝ) * ((q : ℝ) + z) + 1) := by nlinarith
  rw [branch2_sub_eq hq hr hy hz, abs_div, abs_of_pos (by linarith : (0:ℝ) <
    ((r : ℝ) * ((q : ℝ) + y) + 1) * ((r : ℝ) * ((q : ℝ) + z) + 1)),
    div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg (y - z)]

/-- `Ψ_{q,r}` maps `[0,1]` into `[0,1]`. -/
theorem branch2_mem_Icc {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : branch2 q r y ∈ Icc (0 : ℝ) 1 :=
  gaussInverseBranch_mem_Icc hr (gaussInverseBranch_mem_Icc hq hy)

/-- **Exact rank-2 cylinder length.**  `|I_{q,r}| = 1/((r(q+1)+1)(rq+1))`.
This is what makes the `L¹` constant of the Lasota-Yorke inequality
finite. -/
theorem branch2_length {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    branch2 q r 1 - branch2 q r 0
      = 1 / (((r : ℝ) * ((q : ℝ) + 1) + 1) * ((r : ℝ) * (q : ℝ) + 1)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  rw [branch2_sub_eq hq hr h1 h0]
  norm_num

/-- `Ψ_{q,r}` is increasing, so the rank-2 cylinder it parametrizes is
`[Ψ_{q,r}(0), Ψ_{q,r}(1)]`. -/
theorem branch2_zero_lt_one {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    branch2 q r 0 < branch2 q r 1 := by
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpos : (0 : ℝ)
      < 1 / (((r : ℝ) * ((q : ℝ) + 1) + 1) * ((r : ℝ) * (q : ℝ) + 1)) := by
    positivity
  have h := branch2_length hq hr
  linarith [h ▸ hpos]

/-- **`sup |W_{q,r}| ≤ 1/4`.**  Half of the rate `ρ = 1/2`. -/
theorem abs_weight2_le_quarter {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : |weight2 q r y| ≤ 1 / 4 := by
  have hy' := gaussInverseBranch_mem_Icc hq hy
  have h1 := abs_gaussBranchRatio_le_half hq hy
  have h2 := abs_gaussBranchRatio_le_half hr hy'
  unfold weight2
  rw [abs_mul]
  nlinarith [abs_nonneg (gaussBranchRatio q y),
    abs_nonneg (gaussBranchRatio r (gaussInverseBranch q y))]

/-- `W_{q,r}` is `1/4`-Lipschitz on `[0,1]`:
`|W| ≤ ½·¼ + ½·¼ = ¼` by the Leibniz rule. -/
theorem weight2_lipschitz_quarter {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |weight2 q r y - weight2 q r z| ≤ (1 / 4 : ℝ) * |y - z| := by
  have hy' := gaussInverseBranch_mem_Icc hq hy
  have hz' := gaussInverseBranch_mem_Icc hq hz
  set A : ℝ := gaussBranchRatio q y
  set B : ℝ := gaussBranchRatio q z
  set C : ℝ := gaussBranchRatio r (gaussInverseBranch q y)
  set D : ℝ := gaussBranchRatio r (gaussInverseBranch q z)
  have hA : |A| ≤ 1 / 2 := abs_gaussBranchRatio_le_half hq hy
  have hD : |D| ≤ 1 / 2 := abs_gaussBranchRatio_le_half hr hz'
  have hAB : |A - B| ≤ (1 / 4 : ℝ) * |y - z| :=
    gaussBranchRatio_lipschitz_quarter hq hy hz
  have hCD : |C - D| ≤ (1 / 4 : ℝ) * |y - z| := by
    refine le_trans (gaussBranchRatio_lipschitz_quarter hr hy' hz') ?_
    have := gaussInverseBranch_lipschitz hq hy hz
    linarith
  have hrw : weight2 q r y - weight2 q r z = A * (C - D) + D * (A - B) := by
    unfold weight2; ring
  rw [hrw]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul]
  nlinarith [abs_nonneg A, abs_nonneg D, abs_nonneg (C - D), abs_nonneg (A - B),
    abs_nonneg (y - z)]

/-- **`Var_{[0,1]}(W_{q,r}) ≤ 1/4`.**  The other half of `ρ = 1/2`. -/
theorem eVariationOn_weight2_le_quarter {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    eVariationOn (weight2 q r) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (1 / 4) := by
  have h := eVariationOn_le_of_lipschitz_Icc (a := (0 : ℝ)) (b := 1)
    (K := 1 / 4) (by norm_num) (by norm_num)
    (f := weight2 q r) (fun x hx y hy => weight2_lipschitz_quarter hq hr hx hy)
  simpa using h

/-- `Ψ_{q,r}` is monotone on `[0,1]`. -/
theorem branch2_monotoneOn {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    MonotoneOn (branch2 q r) (Icc (0 : ℝ) 1) := by
  intro y hy z hz hyz
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (0 : ℝ) < (r : ℝ) * ((q : ℝ) + y) + 1 := by nlinarith [hy.1]
  have hd2 : (0 : ℝ) < (r : ℝ) * ((q : ℝ) + z) + 1 := by nlinarith [hz.1]
  have h := branch2_sub_eq hq hr hy hz
  have hle : branch2 q r y - branch2 q r z ≤ 0 := by
    rw [h]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- `Ψ_{q,r}` maps `[0,1]` onto the rank-2 cylinder it parametrizes. -/
theorem branch2_mapsTo {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    Set.MapsTo (branch2 q r) (Icc (0 : ℝ) 1)
      (Icc (branch2 q r 0) (branch2 q r 1)) := by
  intro y hy
  have hm := branch2_monotoneOn hq hr
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  exact ⟨hm h0 hy hy.1, hm hy h1 hy.2⟩

/-- **THE HEART OF LASOTA-YORKE, ONE BRANCH AT A TIME.**  Fully proved.

For the rank-2 branch `(q,r)` with cylinder `I = [Ψ_{q,r}(0), Ψ_{q,r}(1)]`,

  `Var_{[0,1]}(W_{q,r} · (f ∘ Ψ_{q,r})) ≤ (1/4 + W)·Var_I(f) + W·avg_I|f|`

for any bound `W` on `Var_{[0,1]}(W_{q,r})`.  The two coefficients are
exactly `sup|W_{q,r}|` and `Var(W_{q,r})`, and by
`abs_weight2_le_quarter` / `eVariationOn_weight2_le_quarter` both are
`≤ 1/4`, so the coefficient of `Var_I f` is `≤ 1/2` uniformly in `(q,r)`.
Summing over the rank-2 cylinders (INPUT 2) is what turns this into
`ρ = 1/2`; the `avg_I|f|` terms are what turn into `C‖f‖₁` (INPUT 3). -/
theorem branch_term_lasotaYorke {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {f : ℝ → ℝ} {Vloc W : ℝ} (hVloc0 : 0 ≤ Vloc) (hW0 : 0 ≤ W)
    (hVloc : eVariationOn f (Icc (branch2 q r 0) (branch2 q r 1))
      ≤ ENNReal.ofReal Vloc)
    (hint : IntegrableOn (fun y => |f y|)
      (Icc (branch2 q r 0) (branch2 q r 1)))
    (hW : eVariationOn (weight2 q r) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal W) :
    eVariationOn (fun y => weight2 q r y * f (branch2 q r y)) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal ((1 / 4 + W) * Vloc
          + W * ((∫ y in Icc (branch2 q r 0) (branch2 q r 1), |f y|)
              / (branch2 q r 1 - branch2 q r 0))) := by
  set a := branch2 q r 0 with ha
  set b := branch2 q r 1 with hb
  have hab : a < b := branch2_zero_lt_one hq hr
  set mean := (∫ y in Icc a b, |f y|) / (b - a) with hmeandef
  have hmean0 : 0 ≤ mean := by
    rw [hmeandef]
    exact div_nonneg
      (setIntegral_nonneg measurableSet_Icc fun y _ => abs_nonneg _)
      (by linarith)
  have hS0 : 0 ≤ Vloc + mean := by linarith
  have hsup : ∀ y ∈ Icc (0 : ℝ) 1, |f (branch2 q r y)| ≤ Vloc + mean := by
    intro y hy
    exact abs_le_variation_add_average hab hVloc0 hVloc hint
      (branch2_mapsTo hq hr hy)
  have hmulle := eVariationOn_mul_le (s := Icc (0 : ℝ) 1)
    (f := weight2 q r) (g := fun y => f (branch2 q r y))
    (Mf := 1 / 4) (Mg := Vloc + mean)
    (fun x hx => abs_weight2_le_quarter hq hr hx) hsup
  have hcomp : eVariationOn (fun y => f (branch2 q r y)) (Icc (0 : ℝ) 1)
      ≤ eVariationOn f (Icc a b) :=
    eVariationOn.comp_le_of_monotoneOn f (branch2 q r)
      (branch2_monotoneOn hq hr) (branch2_mapsTo hq hr)
  refine le_trans hmulle ?_
  have h1 : ENNReal.ofReal (1 / 4)
        * eVariationOn (fun y => f (branch2 q r y)) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (1 / 4) * ENNReal.ofReal Vloc := by
    gcongr
    exact le_trans hcomp hVloc
  have h2 : ENNReal.ofReal (Vloc + mean)
        * eVariationOn (weight2 q r) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (Vloc + mean) * ENNReal.ofReal W := by
    gcongr
  refine le_trans (add_le_add h1 h2) ?_
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hS0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact le_of_eq (by rw [ENNReal.ofReal_eq_ofReal_iff (by positivity)
    (by positivity)]; ring)

/-! ## 4.  The `L²` Lasota-Yorke inequality

The six analytic inputs that §3 does **not** supply are isolated below,
each stated faithfully with its obstruction named.  §3 already delivers the
whole of the rate: `ρ = sup|W| + Var(W) ≤ 1/4 + 1/4 = 1/2`, and the
branchwise mechanism (`branch_term_lasotaYorke`).  What is left is
bookkeeping over the branch index, `tsum` rearrangement, the tiling of
`[0,1]` by rank-2 cylinders, one sharp distortion envelope, and the two
`L¹` facts. -/

/-- Variation over `[0,1]`, as an `ℝ≥0∞`-valued seminorm. -/
def bvV (f : ℝ → ℝ) : ℝ≥0∞ := eVariationOn f (Icc (0 : ℝ) 1)

/-- `L¹(ν)` norm against the Gauss measure. -/
def bvN (f : ℝ → ℝ) : ℝ≥0∞ := ENNReal.ofReal (∫ x, |f x| ∂gaussMeasure)

/-- **INPUT 1 (branch expansion).**  Two applications of `gaussTransfer`
regroup as a single sum over the rank-2 branches.

Obstruction: the double `tsum` must be rearranged into a `tsum` over
`ℕ × ℕ`.  Wang's substrate proves single-branch summability
(`summable_gaussTransfer_branch_of_unit_bounds`) only under
`GaussUnitNonnegative`/`GaussUnitUpperBound`; the *product* family is
dominated by `W_{q,r}(y) · A` with `∑_{q,r} W_{q,r}(y) = 1`, but the
corresponding `Summable (fun p : ℕ × ℕ => …)` and `Summable.tsum_prod'`
step is not available in-tree. -/
theorem gaussTransfer_sq_eq_tsum_branch2 {f : ℝ → ℝ} {A : ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussTransfer (gaussTransfer f) y
      = ∑' p : ℕ × ℕ,
          weight2 (p.1 + 1) (p.2 + 1) y * f (branch2 (p.1 + 1) (p.2 + 1) y) := by
  sorry

/-- **INPUT 1' (summability of the rank-2 branch family).**  Companion to
INPUT 1: the family is dominated by `A · W_{q,r}(y)`, whose total mass is
`(gaussTransfer^[2]) 1 y = 1`.

Obstruction: same as INPUT 1, `Summable` over `ℕ × ℕ` for the product
family is not derivable from the substrate's one-branch statement without
the `Summable.prod` / dominated-convergence step. -/
theorem summable_branch2_family {f : ℝ → ℝ} {A : ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Summable fun p : ℕ × ℕ =>
      weight2 (p.1 + 1) (p.2 + 1) y * f (branch2 (p.1 + 1) (p.2 + 1) y) := by
  sorry

/-- **INPUT 2 (the rank-2 cylinders tile `[0,1]`).**  The intervals
`[Ψ_{q,r}(0), Ψ_{q,r}(1)]`, `q, r ≥ 1`, have pairwise disjoint interiors
and are contained in `[0,1]`, so the variations over them sum to at most
the total variation.

Obstruction: mathlib's additivity (`eVariationOn.sum`, `add_le_union`)
enumerates intervals by a *monotone* `ℕ → ℝ`.  The rank-2 cylinders have
order type `ω²` (they accumulate at both endpoints of each rank-1
cylinder), so no such enumeration exists; one has to go through finite
subfamilies and `ENNReal.tsum_le_of_sum_le`, which needs a
"finitely many pairwise non-overlapping intervals" additivity lemma that
mathlib does not have either. -/
theorem tsum_eVariationOn_branch2_le (f : ℝ → ℝ) :
    (∑' p : ℕ × ℕ, eVariationOn f
        (Icc (branch2 (p.1 + 1) (p.2 + 1) 0) (branch2 (p.1 + 1) (p.2 + 1) 1)))
      ≤ eVariationOn f (Icc (0 : ℝ) 1) := by
  sorry

/-- **INPUT 3 (the sharp weight/length comparison).**  The crude uniform
bound `Var(W_{q,r}) ≤ 1/4` of §3 is enough for the *rate* but not for the
`L¹` constant, because `1/|I_{q,r}| = (r(q+1)+1)(rq+1)` is unbounded.  The
sharp form is `Var(W_{q,r}) ≤ 90 · |I_{q,r}|`, which comes from
`sup w_q ≤ 2/(q(q+1))`, `Lip(w_q) ≤ 5/(q+1)²`, `Lip(ψ_q) ≤ 1/q²` together
with the exact length of `branch2_length`.

Obstruction: the substrate's per-branch Lipschitz bounds are stated with
the constants `1/4`, `1/18`, `(q-1)/(q(q+1)²)`, which are *not* of the
form `5/(q+1)²` for `q = 1, 2`; re-deriving the `q`-uniform envelope from
`hasDerivAt_gaussBranchRatio` is a separate calculus computation. -/
theorem eVariationOn_weight2_le_length {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    eVariationOn (weight2 q r) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (90 * (branch2 q r 1 - branch2 q r 0)) := by
  sorry

/-- **INPUT 4 (`L¹`-contractivity).**  `gaussTransfer` is the adjoint of the
Gauss map on `L¹(ν)`, hence a contraction there.

Obstruction: `Erdos1002.lintegral_gaussTransferENN` gives this for
`ℝ≥0∞`-valued inputs; transferring to `|f|` needs
`|gaussTransfer f| ≤ gaussTransfer |f|` (a `tsum` triangle inequality
requiring summability) plus an `ofReal`/`toReal` round trip. -/
theorem bvN_gaussTransfer_le (f : ℝ → ℝ) :
    bvN (gaussTransfer f) ≤ bvN f := by
  sorry

/-- **INPUT 5 (Lebesgue ↔ Gauss `L¹`, summed).**  On `[0,1]`,
`dx ≤ 2 log 2 · dν`; combined with the disjointness of the rank-2 cylinders
this gives `∑_{q,r} 90 ∫_{I_{q,r}} |f| dx ≤ 90 · 2 log 2 · ‖f‖_{L¹(ν)}`,
and `90 · 2 log 2 ≤ 124.8 ≤ 128`.

Obstruction: `Erdos1002.gaussMeasure_eq_volume_withDensity` plus the
two-sided density bounds `lebesgueOverGaussDensityReal_bounds` give the
pointwise density comparison, but the `withDensity` set-integral
comparison and the disjoint-cylinder additivity of the Lebesgue integral
are not in-tree. -/
theorem tsum_branch2_setIntegral_le {f : ℝ → ℝ} :
    (∑' p : ℕ × ℕ, ENNReal.ofReal
        (90 * ∫ y in Icc (branch2 (p.1 + 1) (p.2 + 1) 0)
                (branch2 (p.1 + 1) (p.2 + 1) 1), |f y|))
      ≤ 128 * bvN f := by
  sorry

/-- **Summation step.**  Fully proved: it turns a branchwise family of
Lasota-Yorke estimates into the operator-level inequality.  This is where
`eVariationOn_tsum_le` (§1) is used. -/
theorem lasotaYorke_of_branchwise {ι : Type*} {f Lf : ℝ → ℝ} {T : ι → ℝ → ℝ}
    {ρ C : ℝ≥0∞} {Vloc E : ι → ℝ≥0∞}
    (heq : ∀ y ∈ Icc (0 : ℝ) 1, Lf y = ∑' p, T p y)
    (hsum : ∀ y ∈ Icc (0 : ℝ) 1, Summable fun p => T p y)
    (hbranch : ∀ p, eVariationOn (T p) (Icc (0 : ℝ) 1) ≤ ρ * Vloc p + E p)
    (hVloc : (∑' p, Vloc p) ≤ bvV f)
    (hE : (∑' p, E p) ≤ C * bvN f) :
    bvV Lf ≤ ρ * bvV f + C * bvN f := by
  have hcongr : eVariationOn Lf (Icc (0 : ℝ) 1)
      = eVariationOn (fun y => ∑' p, T p y) (Icc (0 : ℝ) 1) :=
    eVariationOn.eq_of_eqOn (fun y hy => heq y hy)
  show eVariationOn Lf (Icc (0 : ℝ) 1) ≤ _
  rw [hcongr]
  calc eVariationOn (fun y => ∑' p, T p y) (Icc (0 : ℝ) 1)
      ≤ ∑' p, eVariationOn (T p) (Icc (0 : ℝ) 1) := eVariationOn_tsum_le hsum
    _ ≤ ∑' p, (ρ * Vloc p + E p) := ENNReal.tsum_le_tsum hbranch
    _ = ρ * (∑' p, Vloc p) + ∑' p, E p := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ ρ * bvV f + C * bvN f := by gcongr

/-- `ENNReal.ofReal (1/2) = 1/2`. -/
theorem ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat]

/-- The `ℝ≥0∞` form of `branch_term_lasotaYorke`, with the rate `1/2`
already inserted.  Fully proved (the `⊤` case is handled separately, so no
finiteness assumption on `f` is smuggled in). -/
theorem branch_term_enn {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {f : ℝ → ℝ}
    {W : ℝ} (hW0 : 0 ≤ W) (hWq : W ≤ 1 / 4)
    (hW : eVariationOn (weight2 q r) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal W)
    (hint : IntegrableOn (fun y => |f y|)
      (Icc (branch2 q r 0) (branch2 q r 1))) :
    eVariationOn (fun y => weight2 q r y * f (branch2 q r y)) (Icc (0 : ℝ) 1)
      ≤ (1 / 2 : ℝ≥0∞)
          * eVariationOn f (Icc (branch2 q r 0) (branch2 q r 1))
        + ENNReal.ofReal (W
            * ((∫ y in Icc (branch2 q r 0) (branch2 q r 1), |f y|)
                / (branch2 q r 1 - branch2 q r 0))) := by
  have hab : branch2 q r 0 < branch2 q r 1 := branch2_zero_lt_one hq hr
  have hmean0 : 0 ≤ (∫ y in Icc (branch2 q r 0) (branch2 q r 1), |f y|)
      / (branch2 q r 1 - branch2 q r 0) :=
    div_nonneg (setIntegral_nonneg measurableSet_Icc fun y _ => abs_nonneg _)
      (by linarith)
  rw [← ofReal_half]
  by_cases htop :
      eVariationOn f (Icc (branch2 q r 0) (branch2 q r 1)) = ⊤
  · rw [htop, ENNReal.mul_top (by simp)]
    exact le_top
  · obtain ⟨Vt, hVt0, hVeq⟩ :
        ∃ Vt : ℝ, 0 ≤ Vt ∧ ENNReal.ofReal Vt
          = eVariationOn f (Icc (branch2 q r 0) (branch2 q r 1)) :=
      ⟨_, ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop⟩
    have h := branch_term_lasotaYorke hq hr hVt0 hW0 (le_of_eq hVeq.symm) hint hW
    refine le_trans h ?_
    rw [← hVeq, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [hmean0, hVt0, hWq]

/-- **THE `L²` BV LASOTA-YORKE INEQUALITY FOR THE GAUSS TRANSFER OPERATOR.**

    Var_{[0,1]}(L² f)  ≤  (1/2) · Var_{[0,1]}(f)  +  128 · ‖f‖_{L¹(ν)} .

`ρ = 1/2` is `sup|W_{q,r}| + Var(W_{q,r}) ≤ 1/4 + 1/4`, both proved in §3
(`abs_weight2_le_quarter`, `eVariationOn_weight2_le_quarter`), and the
branchwise mechanism is `branch_term_lasotaYorke`, also proved.
`C = 128` is `90 · 2 log 2 ≤ 124.8`, unoptimised; any larger constant also
holds.

This is the statement Kwon asserts in one line in §3 and never proves, and
which appears nowhere in mathlib or in Wang's substrate.  It is **derived
here** from exactly INPUTS 1, 1', 2, 3, 5, the rate itself is not
assumed. -/
theorem gaussTransfer_sq_bv_lasotaYorke {f : ℝ → ℝ} {A : ℝ}
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hint : IntegrableOn (fun y => |f y|) (Icc (0 : ℝ) 1)) :
    bvV (gaussTransfer (gaussTransfer f))
      ≤ (1 / 2 : ℝ≥0∞) * bvV f + 128 * bvN f := by
  classical
  set T : ℕ × ℕ → ℝ → ℝ := fun p y =>
    weight2 (p.1 + 1) (p.2 + 1) y * f (branch2 (p.1 + 1) (p.2 + 1) y) with hT
  set Wf : ℕ × ℕ → ℝ := fun p =>
    min (1 / 4) (90 * (branch2 (p.1 + 1) (p.2 + 1) 1
      - branch2 (p.1 + 1) (p.2 + 1) 0)) with hWf
  refine lasotaYorke_of_branchwise (T := T)
    (Vloc := fun p => eVariationOn f
      (Icc (branch2 (p.1 + 1) (p.2 + 1) 0) (branch2 (p.1 + 1) (p.2 + 1) 1)))
    (E := fun p => ENNReal.ofReal
      (90 * ∫ y in Icc (branch2 (p.1 + 1) (p.2 + 1) 0)
              (branch2 (p.1 + 1) (p.2 + 1) 1), |f y|))
    (fun y hy => gaussTransfer_sq_eq_tsum_branch2 hf0 hfA hy)
    (fun y hy => summable_branch2_family hf0 hfA hy)
    ?_ (tsum_eVariationOn_branch2_le f) tsum_branch2_setIntegral_le
  intro p
  obtain ⟨i, j⟩ := p
  have hq : 0 < i + 1 := Nat.succ_pos i
  have hr : 0 < j + 1 := Nat.succ_pos j
  have hab : branch2 (i + 1) (j + 1) 0 < branch2 (i + 1) (j + 1) 1 :=
    branch2_zero_lt_one hq hr
  have hlen : (0 : ℝ)
      ≤ 90 * (branch2 (i + 1) (j + 1) 1 - branch2 (i + 1) (j + 1) 0) := by
    linarith
  have hW0 : 0 ≤ Wf (i, j) := le_min (by norm_num) hlen
  have hWq : Wf (i, j) ≤ 1 / 4 := min_le_left _ _
  have hWlen : Wf (i, j)
      ≤ 90 * (branch2 (i + 1) (j + 1) 1 - branch2 (i + 1) (j + 1) 0) :=
    min_le_right _ _
  have hWvar : eVariationOn (weight2 (i + 1) (j + 1)) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (Wf (i, j)) := by
    have hmin : ENNReal.ofReal (Wf (i, j))
        = min (ENNReal.ofReal (1 / 4))
            (ENNReal.ofReal
              (90 * (branch2 (i + 1) (j + 1) 1 - branch2 (i + 1) (j + 1) 0))) := by
      rcases le_total (1 / 4 : ℝ)
          (90 * (branch2 (i + 1) (j + 1) 1 - branch2 (i + 1) (j + 1) 0)) with h | h
      · rw [hWf]
        simp only
        rw [min_eq_left h, min_eq_left (ENNReal.ofReal_le_ofReal h)]
      · rw [hWf]
        simp only
        rw [min_eq_right h, min_eq_right (ENNReal.ofReal_le_ofReal h)]
    rw [hmin]
    exact le_min (eVariationOn_weight2_le_quarter hq hr)
      (eVariationOn_weight2_le_length hq hr)
  have hsub : Icc (branch2 (i + 1) (j + 1) 0) (branch2 (i + 1) (j + 1) 1)
      ⊆ Icc (0 : ℝ) 1 := by
    have h0 := branch2_mem_Icc hq hr (Set.left_mem_Icc.2 (by norm_num : (0:ℝ) ≤ 1))
    have h1 := branch2_mem_Icc hq hr (Set.right_mem_Icc.2 (by norm_num : (0:ℝ) ≤ 1))
    exact Set.Icc_subset_Icc h0.1 h1.2
  have hintp : IntegrableOn (fun y => |f y|)
      (Icc (branch2 (i + 1) (j + 1) 0) (branch2 (i + 1) (j + 1) 1)) :=
    hint.mono_set hsub
  refine le_trans (branch_term_enn hq hr hW0 hWq hWvar hintp) ?_
  gcongr
  apply ENNReal.ofReal_le_ofReal
  have hI : (0 : ℝ) ≤ ∫ y in Icc (branch2 (i + 1) (j + 1) 0)
      (branch2 (i + 1) (j + 1) 1), |f y| :=
    setIntegral_nonneg measurableSet_Icc fun y _ => abs_nonneg _
  have hd : (0 : ℝ) < branch2 (i + 1) (j + 1) 1 - branch2 (i + 1) (j + 1) 0 := by
    linarith
  rw [div_eq_inv_mul,
    show (90 : ℝ) * ∫ y in Icc (branch2 (i + 1) (j + 1) 0)
        (branch2 (i + 1) (j + 1) 1), |f y|
      = (90 * (branch2 (i + 1) (j + 1) 1 - branch2 (i + 1) (j + 1) 0))
        * ((branch2 (i + 1) (j + 1) 1 - branch2 (i + 1) (j + 1) 0)⁻¹
          * ∫ y in Icc (branch2 (i + 1) (j + 1) 0)
              (branch2 (i + 1) (j + 1) 1), |f y|) by
      field_simp]
  exact mul_le_mul_of_nonneg_right hWlen
    (mul_nonneg (le_of_lt (inv_pos.2 hd)) hI)

/-- **THE ITERATION LEMMA, specialised.**  Given the `L²` inequality
(`gaussTransfer_sq_bv_lasotaYorke`), `L¹`-contractivity
(`bvN_gaussTransfer_le`) and any crude one-step bound, the variation of
`L^n f` decays like `2^{-⌊n/2⌋}` down to a fixed `L¹` floor, for **every**
`n`, even and odd, with no large-`n` quantifier gymnastics.

`d = 256` satisfies `(1/2)·256 + 128 ≤ 256`, i.e. `d ≥ C/(1-ρ)`. -/
theorem gaussTransfer_bv_iterate
    (hLY : ∀ g : ℝ → ℝ,
      bvV (gaussTransfer (gaussTransfer g)) ≤ (1 / 2 : ℝ≥0∞) * bvV g + 128 * bvN g)
    (hstep : ∀ g : ℝ → ℝ, bvV (gaussTransfer g) ≤ 1 * bvV g + 128 * bvN g)
    (n : ℕ) (f : ℝ → ℝ) :
    bvV ((gaussTransfer^[n]) f)
      ≤ (1 / 2 : ℝ≥0∞) ^ (n / 2) * (2 * bvV f) + 384 * bvN f := by
  have h2 : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  have hd : (1 / 2 : ℝ≥0∞) * 256 + 128 ≤ 256 := by
    rw [show (256 : ℝ≥0∞) = 2 * 128 by norm_num, ← mul_assoc, h2, one_mul,
      two_mul]
  have h := lasotaYorke_iterate (L := gaussTransfer) (V := bvV) (N := bvN)
    (ρ := (1 / 2 : ℝ≥0∞)) (c := 128) (d := 256) (e := 1) (g := 128)
    (by norm_num) hLY bvN_gaussTransfer_le hstep hd n f
  have e1 : (1 : ℝ≥0∞) + 1 = 2 := by norm_num
  have e2 : (128 : ℝ≥0∞) + 256 = 384 := by norm_num
  rw [e1, e2] at h
  exact h

end

end Kwon1002.BVIterate
