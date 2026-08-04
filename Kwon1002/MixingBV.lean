/-
Scratch file (agent `mixbv`).

TARGET: `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing`.

STATUS: **PROVED OUTRIGHT**, no `sorry`; `lem_3_2_conditional_multiblock_mixing'`
below is the target reproduced token-identically (diffed against
`Kwon1002/Prop41.lean` lines 267-276) and its axioms are exactly
`[propext, Classical.choice, Quot.sound]`.

WAVE-1 INPUT CONSUMED.  `Kwon1002.BVMixing.lemma_3_2_BV` (sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`) already supplies BV
multi-block mixing in the substrate's block-list formalism, for
**nonnegative** observables, at rate `√(527/540)`.  It is obtained from
Wang's Lipschitz contraction by mollification, *not* from a BV Lasota-Yorke
inequality.  (A BV Lasota-Yorke inequality is separately proved sorry-free
in `Kwon1002.BVLasotaYorke.gaussTransfer_bv_lasotaYorke`,
`Var(Lf) ≤ (3/4)Var f + ‖f‖₁`; the present file does not use it, confirming
`BVScout`'s strategic finding that BV Lasota-Yorke is **not** on the
critical path for §4.)  No sorried result from any module is consumed.

So the remaining debt was exactly the four bookkeeping mismatches recorded
in `TransferIdentity` §13 / `BVMixing` §6.  All four are discharged:

  (1) SIGN.  `Prop41.BVBoundedBy K g` only asks `|g| ≤ K`; `lemma_3_2_BV`
      needs `0 ≤ g ≤ K`.  §5-§6 prove the multilinear splitting
      `mixDefect (as ++ (m,h-c)::rest) = mixDefect (as ++ (m,h)::rest)
        - mixDefect (as ++ (m,c)::rest)`
      for the mixing defect and run it as an induction over the block list.
      Cost: exactly `2 ^ s`, as predicted.

  (2) CONSTANT SHAPE.  `lemma_3_2_BV` produces `K ^ (s+1)`; Kwon's (17) has
      `K ^ s`.  §11 fixes this by homogeneity (`g ↦ g/K`), which needed a
      variation-scaling lemma (`eVariationOn_const_mul_le`, §3) that Mathlib
      does not have.  The degenerate case `K = 0` is handled separately: the
      observables then vanish `ν`-a.e. and both sides are `0`.

  (3) MISSING MEASURABILITY HYPOTHESIS.  **The hypothesis is not missing.**
      The target quantifies over `g` with no measurability assumption, and
      that is sound: §3 shows `BVBoundedBy K g` already forces `g` to agree
      on `Ioo 0 1` with an explicit globally measurable, globally bounded
      function (Jordan decomposition via `BVMixing.bvP`/`bvQ`, then a
      global monotone extension `monoExt`, then a clamp), and `ν` gives full
      mass to `Ioo 0 1`.  So the statement as written in `Prop41` is
      provable and should NOT be amended.

  (4) CYLINDER CONVENTION.  `Prop41.cylinder d w` is digit-defined inside
      `Ioo 0 1`; the substrate conditions on
      `Erdos1002.gaussHalfOpenPrefixCylinder`.  §9 proves they agree
      `ν`-a.e.  The missing ingredient was a digit characterisation of the
      substrate's cylinder recursion (`mem_halfOpen_iff`), which exists
      nowhere in `wang_substrate/`.
-/
import Kwon1002.Prop41
import Kwon1002.BVMixing

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002.MixingBV

open Prop41

noncomputable section

/-! ## 1. Orbit and block-list algebra

Not in the tree: `Kwon1002.Transfer` has `blockProduct_cons`/`blockMean_cons`
but no `append` lemmas, and the substrate has no `gaussOrbit_add`. -/

theorem gaussOrbit_add (m n : ℕ) (x : ℝ) :
    Erdos1002.gaussOrbit m (Erdos1002.gaussOrbit n x)
      = Erdos1002.gaussOrbit (m + n) x := by
  simp [Erdos1002.gaussOrbit, Function.iterate_add_apply]

/-- `gaussIter` of `Kwon1002.GaussBasics` *is* the substrate's `gaussOrbit`. -/
theorem gaussIter_eq_gaussOrbit (α : ℝ) (j : ℕ) :
    Kwon1002.gaussIter α j = Erdos1002.gaussOrbit j α := rfl

/-- Total gap of a block list. -/
def gapSum (bs : List (ℕ × (ℝ → ℝ))) : ℕ := (bs.map Prod.fst).sum

@[simp] theorem gapSum_nil : gapSum [] = 0 := rfl

@[simp] theorem gapSum_cons (p : ℕ × (ℝ → ℝ)) (bs : List (ℕ × (ℝ → ℝ))) :
    gapSum (p :: bs) = p.1 + gapSum bs := rfl

theorem blockProduct_append (as cs : List (ℕ × (ℝ → ℝ))) (x : ℝ) :
    Kwon1002.Transfer.blockProduct (as ++ cs) x
      = Kwon1002.Transfer.blockProduct as x
          * Kwon1002.Transfer.blockProduct cs (Erdos1002.gaussOrbit (gapSum as) x) := by
  induction as generalizing x with
  | nil => simp [Erdos1002.gaussOrbit_zero]
  | cons p as ih =>
      rw [List.cons_append, Kwon1002.Transfer.blockProduct_cons,
        Kwon1002.Transfer.blockProduct_cons, ih, gapSum_cons, gaussOrbit_add,
        Nat.add_comm p.1 (gapSum as)]
      ring

theorem blockMean_append (as cs : List (ℕ × (ℝ → ℝ))) :
    Kwon1002.Transfer.blockMean (as ++ cs)
      = Kwon1002.Transfer.blockMean as * Kwon1002.Transfer.blockMean cs := by
  simp [Kwon1002.Transfer.blockMean, List.map_append, List.prod_append]

/-! ## 2. Two global regularity classes -/

/-- Measurable and globally bounded in absolute value.  This is all that any
integrability side condition below needs. -/
structure GlobBdd (A : ℝ) (g : ℝ → ℝ) : Prop where
  meas : Measurable g
  bd : ∀ x, |g x| ≤ A

/-- A *global* strengthening of the substrate's unit-interval class:
measurable, `0 ≤ g ≤ A` **everywhere**, plus the `BV` bound on `Ioo 0 1`.
Everything fed into `BVMixing.lemma_3_2_BV` below is of this form. -/
structure GlobGood (A : ℝ) (g : ℝ → ℝ) : Prop where
  meas : Measurable g
  nonneg : ∀ x, 0 ≤ g x
  le : ∀ x, g x ≤ A
  var : eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal A

theorem GlobGood.gaussUnitNonnegative {A : ℝ} {g : ℝ → ℝ} (h : GlobGood A g) :
    Erdos1002.GaussUnitNonnegative g := fun _ _ => h.nonneg _

theorem GlobGood.gaussUnitUpperBound {A : ℝ} {g : ℝ → ℝ} (h : GlobGood A g) :
    Erdos1002.GaussUnitUpperBound A g := fun _ _ => h.le _

theorem GlobGood.globBdd {A : ℝ} {g : ℝ → ℝ} (h : GlobGood A g) : GlobBdd A g :=
  ⟨h.meas, fun x => abs_le.2 ⟨by linarith [h.nonneg x, h.le x], h.le x⟩⟩

/-! ## 3. `BV(0,1)` already forces a measurable representative

The target quantifies over `g` with **no** measurability hypothesis.  It is
not missing: `BVBoundedBy K g` forces `g` to agree on `Ioo 0 1` with an
explicit globally measurable, globally bounded function. -/

/-- Adding a constant cannot increase the variation.  (Mathlib has no
algebraic lemma about `eVariationOn` at all.) -/
theorem eVariationOn_add_const_le (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x + c) s ≤ eVariationOn f s := by
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have hstep : ∀ i : ℕ,
      edist (f (u (i + 1)) + c) (f (u i) + c) = edist (f (u (i + 1))) (f (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    congr 1
    ring_nf
  calc ∑ i ∈ Finset.range n,
        edist ((fun x => f x + c) (u (i + 1))) ((fun x => f x + c) (u i))
      = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) :=
        Finset.sum_congr rfl (fun i _ => hstep i)
    _ ≤ eVariationOn f s := eVariationOn.sum_le f n hu us

/-- Scaling of the variation.  Also absent from Mathlib. -/
theorem eVariationOn_const_mul_le (c : ℝ) (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => c * f x) s ≤ ENNReal.ofReal |c| * eVariationOn f s := by
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have hstep : ∀ i : ℕ, edist (c * f (u (i + 1))) (c * f (u i))
      = ENNReal.ofReal |c| * edist (f (u (i + 1))) (f (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← abs_mul]
    congr 2
    ring
  calc ∑ i ∈ Finset.range n,
        edist ((fun x => c * f x) (u (i + 1))) ((fun x => c * f x) (u i))
      = ENNReal.ofReal |c| * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => hstep i)
    _ ≤ ENNReal.ofReal |c| * eVariationOn f s := by
        gcongr
        exact eVariationOn.sum_le f n hu us

/-- Global monotone extension of a function monotone on `Ioo 0 1` and bounded
there by `B`: constant `-B` on `Iic 0`, constant `B` on `Ici 1`. -/
def monoExt (B : ℝ) (p : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if x ≤ 0 then -B else if 1 ≤ x then B else p x

theorem monoExt_eq_of_mem {B : ℝ} {p : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    monoExt B p x = p x := by
  rw [monoExt, if_neg (not_le.2 hx.1), if_neg (not_le.2 hx.2)]

theorem monotone_monoExt {B : ℝ} {p : ℝ → ℝ} (hp : MonotoneOn p (Ioo (0 : ℝ) 1))
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |p x| ≤ B) : Monotone (monoExt B p) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hb (1 / 2) (by norm_num))
  intro a b hab
  rw [monoExt, monoExt]
  by_cases ha0 : a ≤ 0
  · rw [if_pos ha0]
    by_cases hb0 : b ≤ 0
    · rw [if_pos hb0]
    · rw [if_neg hb0]
      by_cases hb1 : 1 ≤ b
      · rw [if_pos hb1]; linarith
      · rw [if_neg hb1]
        have hmem : b ∈ Ioo (0 : ℝ) 1 := ⟨not_le.1 hb0, not_le.1 hb1⟩
        have h2 := abs_le.1 (hb b hmem)
        linarith [h2.1]
  · rw [if_neg ha0]
    by_cases ha1 : 1 ≤ a
    · have hb1 : 1 ≤ b := le_trans ha1 hab
      have hb0 : ¬ b ≤ 0 := by intro h; linarith
      rw [if_pos ha1, if_neg hb0, if_pos hb1]
    · rw [if_neg ha1]
      have hamem : a ∈ Ioo (0 : ℝ) 1 := ⟨not_le.1 ha0, not_le.1 ha1⟩
      have hb0 : ¬ b ≤ 0 := by intro h; linarith [hamem.1]
      rw [if_neg hb0]
      by_cases hb1 : 1 ≤ b
      · rw [if_pos hb1]
        exact le_trans (le_abs_self _) (hb a hamem)
      · rw [if_neg hb1]
        exact hp hamem ⟨not_le.1 hb0, not_le.1 hb1⟩ hab

theorem measurable_monoExt {B : ℝ} {p : ℝ → ℝ} (hp : MonotoneOn p (Ioo (0 : ℝ) 1))
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |p x| ≤ B) : Measurable (monoExt B p) :=
  (monotone_monoExt hp hb).measurable

/-- The measurable representative of a `BV(0,1)` function: `P - Q`, with `P`,
`Q` the monotone extensions of the Jordan pieces
`BVMixing.bvP` / `BVMixing.bvQ`. -/
def bvRepr (K : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => monoExt K (Kwon1002.BVMixing.bvP g) x
    - monoExt (2 * K) (Kwon1002.BVMixing.bvQ g) x

theorem measurable_bvRepr {K : ℝ} (hK : 0 ≤ K) {g : ℝ → ℝ}
    (hbv : BVBoundedBy K g) : Measurable (bvRepr K g) :=
  Measurable.sub
    (measurable_monoExt (Kwon1002.BVMixing.bvP_monotoneOn hbv.2)
      (fun _ hx => Kwon1002.BVMixing.abs_bvP_le hK hbv.2 hx))
    (measurable_monoExt (Kwon1002.BVMixing.bvQ_monotoneOn hbv.2)
      (fun _ hx => Kwon1002.BVMixing.abs_bvQ_le hK hbv.2 hbv.1 hx))

theorem bvRepr_eq_of_mem {K : ℝ} {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    bvRepr K g x = g x := by
  rw [bvRepr, monoExt_eq_of_mem hx, monoExt_eq_of_mem hx]
  exact Kwon1002.BVMixing.bvP_sub_bvQ g x

/-- The clamped measurable representative: agrees with `g` on `Ioo 0 1`
(because `|g| ≤ K` there) and takes values in `[-K, K]` everywhere. -/
def bvClamp (K : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => max (-K) (min K (bvRepr K g x))

theorem measurable_bvClamp {K : ℝ} (hK : 0 ≤ K) {g : ℝ → ℝ}
    (hbv : BVBoundedBy K g) : Measurable (bvClamp K g) :=
  measurable_const.max (measurable_const.min (measurable_bvRepr hK hbv))

theorem bvClamp_eq_of_mem {K : ℝ} {g : ℝ → ℝ} (hbv : BVBoundedBy K g) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : bvClamp K g x = g x := by
  have h := abs_le.1 (hbv.1 x hx)
  rw [bvClamp, bvRepr_eq_of_mem hx, min_eq_right h.2, max_eq_right h.1]

theorem bvClamp_bounds {K : ℝ} (hK : 0 ≤ K) (g : ℝ → ℝ) (x : ℝ) :
    -K ≤ bvClamp K g x ∧ bvClamp K g x ≤ K :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The shifted observable `h = bvClamp + K`: nonnegative, `≤ 2K`, of
variation `≤ 2K`, measurable.  Crucially `bvClamp = h - K` **globally**,
which is what the multilinear splitting of §5 needs. -/
theorem globGood_bvShift {K : ℝ} (hK : 0 ≤ K) {g : ℝ → ℝ} (hbv : BVBoundedBy K g) :
    GlobGood (2 * K) (fun x => bvClamp K g x + K) := by
  refine ⟨(measurable_bvClamp hK hbv).add_const K, ?_, ?_, ?_⟩
  · intro x; linarith [(bvClamp_bounds hK g x).1]
  · intro x; linarith [(bvClamp_bounds hK g x).2]
  · have heq : EqOn (fun x => bvClamp K g x + K) (fun x => g x + K) (Ioo (0 : ℝ) 1) := by
      intro x hx
      show bvClamp K g x + K = g x + K
      rw [bvClamp_eq_of_mem hbv hx]
    rw [eVariationOn.eq_of_eqOn heq]
    exact le_trans (eVariationOn_add_const_le g K (Ioo (0 : ℝ) 1))
      (le_trans hbv.2 (ENNReal.ofReal_le_ofReal (by linarith)))

theorem globGood_const {K : ℝ} (hK : 0 ≤ K) :
    GlobGood (2 * K) (fun _ : ℝ => K) := by
  refine ⟨measurable_const, fun _ => hK, fun _ => by linarith, ?_⟩
  have hsub : (((fun _ : ℝ => K) '' (Ioo (0 : ℝ) 1))).Subsingleton := by
    rintro a ⟨x, -, rfl⟩ b ⟨y, -, rfl⟩
    rfl
  rw [eVariationOn.constant_on hsub]
  exact zero_le _

/-! ## 4. Global bounds and integrability of `blockProduct` -/

theorem blockProduct_globBdd {A : ℝ} (hA : 0 ≤ A) :
    ∀ (bs : List (ℕ × (ℝ → ℝ))), (∀ p ∈ bs, GlobBdd A p.2) → ∀ x : ℝ,
      |Kwon1002.Transfer.blockProduct bs x| ≤ A ^ bs.length := by
  intro bs
  induction bs with
  | nil => intro _ x; simp
  | cons p rest ih =>
      intro h x
      have hp : GlobBdd A p.2 := h p (by simp)
      have hr : ∀ q ∈ rest, GlobBdd A q.2 := fun q hq => h q (by simp [hq])
      have h1 := ih hr (Erdos1002.gaussOrbit p.1 x)
      rw [Kwon1002.Transfer.blockProduct_cons, abs_mul, List.length_cons]
      calc |p.2 (Erdos1002.gaussOrbit p.1 x)|
            * |Kwon1002.Transfer.blockProduct rest (Erdos1002.gaussOrbit p.1 x)|
          ≤ A * A ^ rest.length :=
            mul_le_mul (hp.bd _) h1 (abs_nonneg _) hA
        _ = A ^ (rest.length + 1) := by ring

theorem integrable_blockProduct_comp {A : ℝ} (hA : 0 ≤ A)
    (bs : List (ℕ × (ℝ → ℝ))) (h : ∀ p ∈ bs, GlobBdd A p.2) (d : ℕ) :
    Integrable (fun α => Kwon1002.Transfer.blockProduct bs (Erdos1002.gaussOrbit d α))
      Erdos1002.gaussMeasure := by
  have hm : Measurable
      (fun α => Kwon1002.Transfer.blockProduct bs (Erdos1002.gaussOrbit d α)) :=
    (Kwon1002.Transfer.measurable_blockProduct bs (fun p hp => (h p hp).meas)).comp
      (Erdos1002.measurable_gaussOrbit d)
  refine Integrable.of_bound hm.aestronglyMeasurable (A ^ bs.length) ?_
  refine Filter.Eventually.of_forall (fun α => ?_)
  rw [Real.norm_eq_abs]
  exact blockProduct_globBdd hA bs h _

theorem integrable_of_globBdd {A : ℝ} {g : ℝ → ℝ} (h : GlobBdd A g) :
    Integrable g Erdos1002.gaussMeasure := by
  refine Integrable.of_bound h.meas.aestronglyMeasurable A ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  exact h.bd x

/-! ## 5. The mixing defect and its multilinear splitting

This is the machinery that removes the sign restriction of
`BVMixing.lemma_3_2_BV`. -/

/-- The mixing defect of a block list, conditioned on `S` at depth `d`. -/
def mixDefect (S : Set ℝ) (d : ℕ) (bs : List (ℕ × (ℝ → ℝ))) : ℝ :=
  Kwon1002.Transfer.condMean S
      (fun α => Kwon1002.Transfer.blockProduct bs (Erdos1002.gaussOrbit d α))
    - Kwon1002.Transfer.blockMean bs

theorem condMean_sub (S : Set ℝ) {F G : ℝ → ℝ}
    (hF : IntegrableOn F S Erdos1002.gaussMeasure)
    (hG : IntegrableOn G S Erdos1002.gaussMeasure) :
    Kwon1002.Transfer.condMean S (fun x => F x - G x)
      = Kwon1002.Transfer.condMean S F - Kwon1002.Transfer.condMean S G := by
  rw [Kwon1002.Transfer.condMean, Kwon1002.Transfer.condMean,
    Kwon1002.Transfer.condMean, integral_sub hF hG, sub_div]

/-- **The splitting.**  If the observable in one slot is a difference of two
globally bounded measurable observables, the mixing defect splits. -/
theorem mixDefect_split (S : Set ℝ) (d : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (as rest : List (ℕ × (ℝ → ℝ))) (p : ℕ × (ℝ → ℝ)) {h c : ℝ → ℝ}
    (hgc : ∀ x, p.2 x = h x - c x)
    (has : ∀ q ∈ as, GlobBdd A q.2) (hrest : ∀ q ∈ rest, GlobBdd A q.2)
    (hh : GlobBdd A h) (hc : GlobBdd A c) :
    mixDefect S d (as ++ p :: rest)
      = mixDefect S d (as ++ (p.1, h) :: rest)
        - mixDefect S d (as ++ (p.1, c) :: rest) := by
  have hmem : ∀ (u : ℝ → ℝ), GlobBdd A u →
      ∀ q ∈ as ++ (p.1, u) :: rest, GlobBdd A q.2 := by
    intro u hu q hq
    rcases List.mem_append.1 hq with hq' | hq'
    · exact has q hq'
    · rcases List.mem_cons.1 hq' with rfl | hq''
      · exact hu
      · exact hrest q hq''
  have hpt : ∀ x, Kwon1002.Transfer.blockProduct (as ++ p :: rest) x
      = Kwon1002.Transfer.blockProduct (as ++ (p.1, h) :: rest) x
        - Kwon1002.Transfer.blockProduct (as ++ (p.1, c) :: rest) x := by
    intro x
    rw [blockProduct_append, blockProduct_append, blockProduct_append,
      Kwon1002.Transfer.blockProduct_cons, Kwon1002.Transfer.blockProduct_cons,
      Kwon1002.Transfer.blockProduct_cons]
    simp only [hgc]
    ring
  have hfun : (fun α => Kwon1002.Transfer.blockProduct (as ++ p :: rest)
        (Erdos1002.gaussOrbit d α))
      = fun α => Kwon1002.Transfer.blockProduct (as ++ (p.1, h) :: rest)
            (Erdos1002.gaussOrbit d α)
          - Kwon1002.Transfer.blockProduct (as ++ (p.1, c) :: rest)
            (Erdos1002.gaussOrbit d α) := funext (fun α => hpt _)
  have hbm : Kwon1002.Transfer.blockMean (as ++ p :: rest)
      = Kwon1002.Transfer.blockMean (as ++ (p.1, h) :: rest)
        - Kwon1002.Transfer.blockMean (as ++ (p.1, c) :: rest) := by
    have hint : (∫ x, p.2 x ∂Erdos1002.gaussMeasure)
        = (∫ x, h x ∂Erdos1002.gaussMeasure) - (∫ x, c x ∂Erdos1002.gaussMeasure) := by
      rw [← integral_sub (integrable_of_globBdd hh) (integrable_of_globBdd hc)]
      exact integral_congr_ae (Filter.Eventually.of_forall hgc)
    rw [blockMean_append, blockMean_append, blockMean_append,
      Kwon1002.Transfer.blockMean_cons, Kwon1002.Transfer.blockMean_cons,
      Kwon1002.Transfer.blockMean_cons, hint]
    ring
  rw [mixDefect, mixDefect, mixDefect, hfun, hbm,
    condMean_sub S (integrable_blockProduct_comp hA _ (hmem h hh) d).integrableOn
      (integrable_blockProduct_comp hA _ (hmem c hc) d).integrableOn]
  ring

/-! ## 6. Signed BV multi-block mixing

`BVMixing.lemma_3_2_BV` with `|g| ≤ A` in place of `0 ≤ g ≤ A`. -/

/-- The explicit bound of `BVMixing.lemma_3_2_BV` at length `n`. -/
def bvBound (A : ℝ) (M n : ℕ) : ℝ :=
  478 * ((n : ℝ) + 1) * (8 * A) ^ n * A * Real.sqrt (527 / 540) ^ M

/-- A block observable that is a difference of two `GlobGood` observables. -/
def Splittable (A : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ h c : ℝ → ℝ, (∀ x, g x = h x - c x) ∧ GlobGood A h ∧ GlobGood A c

theorem Splittable.globBdd {A : ℝ} {g : ℝ → ℝ} (hg : Splittable A g) : GlobBdd A g := by
  obtain ⟨h, c, hgc, hh, hc⟩ := hg
  refine ⟨?_, ?_⟩
  · have : g = fun x => h x - c x := funext hgc
    rw [this]; exact hh.meas.sub hc.meas
  · intro x
    rw [hgc x]
    exact abs_le.2 ⟨by linarith [hh.nonneg x, hc.le x], by linarith [hh.le x, hc.nonneg x]⟩

/-- **Signed BV multi-block mixing**, in the substrate's block-list
formalism.  Proved by induction over the signed part of the list, each step
using `mixDefect_split`; the base case is `BVMixing.lemma_3_2_BV`. -/
theorem mixDefect_signed_le (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (Erdos1002.gaussMeasure
      (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal)
    {A : ℝ} (hA : 1 ≤ A) (M : ℕ) :
    ∀ (bs as : List (ℕ × (ℝ → ℝ))),
      (∀ p ∈ as, GlobGood A p.2) → (∀ p ∈ as, M ≤ p.1) →
      (∀ p ∈ bs, Splittable A p.2) → (∀ p ∈ bs, M ≤ p.1) →
      |mixDefect (Erdos1002.gaussHalfOpenPrefixCylinder w) w.length (as ++ bs)|
        ≤ 2 ^ bs.length * bvBound A M (as.length + bs.length) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  intro bs
  induction bs with
  | nil =>
      intro as hasG hasM _ _
      have hbase := Kwon1002.BVMixing.lemma_3_2_BV w hw hpos A hA M as
        (fun p hp => (hasG p hp).meas)
        (fun p hp => (hasG p hp).gaussUnitNonnegative)
        (fun p hp => (hasG p hp).gaussUnitUpperBound)
        (fun p hp => (hasG p hp).var) hasM
      rw [List.append_nil]
      simp only [List.length_nil, Nat.add_zero, pow_zero, one_mul, bvBound, mixDefect]
      exact hbase
  | cons p rest ih =>
      intro as hasG hasM hsp hgap
      obtain ⟨h, c, hgc, hh, hc⟩ := hsp p (by simp)
      have hrestSp : ∀ q ∈ rest, Splittable A q.2 := fun q hq => hsp q (by simp [hq])
      have hrestM : ∀ q ∈ rest, M ≤ q.1 := fun q hq => hgap q (by simp [hq])
      have hpM : M ≤ p.1 := hgap p (by simp)
      have hasB : ∀ q ∈ as, GlobBdd A q.2 := fun q hq => (hasG q hq).globBdd
      have hrestB : ∀ q ∈ rest, GlobBdd A q.2 := fun q hq => (hrestSp q hq).globBdd
      have hsplit := mixDefect_split (Erdos1002.gaussHalfOpenPrefixCylinder w) w.length
        hA0 as rest p hgc hasB hrestB hh.globBdd hc.globBdd
      have hextG : ∀ (u : ℝ → ℝ), GlobGood A u →
          ∀ q ∈ as ++ [(p.1, u)], GlobGood A q.2 := by
        intro u hu q hq
        rcases List.mem_append.1 hq with hq' | hq'
        · exact hasG q hq'
        · rcases List.mem_cons.1 hq' with rfl | hq''
          · exact hu
          · simp at hq''
      have hextM : ∀ (u : ℝ → ℝ), ∀ q ∈ as ++ [(p.1, u)], M ≤ q.1 := by
        intro u q hq
        rcases List.mem_append.1 hq with hq' | hq'
        · exact hasM q hq'
        · rcases List.mem_cons.1 hq' with rfl | hq''
          · exact hpM
          · simp at hq''
      have key : ∀ u : ℝ → ℝ, GlobGood A u →
          |mixDefect (Erdos1002.gaussHalfOpenPrefixCylinder w) w.length
              (as ++ (p.1, u) :: rest)|
            ≤ 2 ^ rest.length * bvBound A M (as.length + (rest.length + 1)) := by
        intro u hu
        have hre : as ++ (p.1, u) :: rest = (as ++ [(p.1, u)]) ++ rest := by simp
        rw [hre]
        have hIH := ih (as ++ [(p.1, u)]) (hextG u hu) (hextM u) hrestSp hrestM
        have hlen : (as ++ [(p.1, u)]).length + rest.length
            = as.length + (rest.length + 1) := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rwa [hlen] at hIH
      rw [hsplit, List.length_cons]
      calc |mixDefect (Erdos1002.gaussHalfOpenPrefixCylinder w) w.length
              (as ++ (p.1, h) :: rest)
            - mixDefect (Erdos1002.gaussHalfOpenPrefixCylinder w) w.length
              (as ++ (p.1, c) :: rest)|
          ≤ |mixDefect (Erdos1002.gaussHalfOpenPrefixCylinder w) w.length
                (as ++ (p.1, h) :: rest)|
            + |mixDefect (Erdos1002.gaussHalfOpenPrefixCylinder w) w.length
                (as ++ (p.1, c) :: rest)| := abs_sub _ _
        _ ≤ 2 ^ rest.length * bvBound A M (as.length + (rest.length + 1))
            + 2 ^ rest.length * bvBound A M (as.length + (rest.length + 1)) :=
              add_le_add (key h hh) (key c hc)
        _ = 2 ^ (rest.length + 1) * bvBound A M (as.length + (rest.length + 1)) := by
              ring

/-! ## 7. From `(d, t, g, s)` to a block list

Kwon indexes by absolute times `t i`; the substrate indexes by gaps.  This
section is the dictionary. -/

/-- The block list of the times `t 0 < t 1 < ⋯`, started at depth `prev`. -/
def blocks : (ℕ → ℕ) → (ℕ → ℝ → ℝ) → ℕ → ℕ → List (ℕ × (ℝ → ℝ))
  | _, _, _, 0 => []
  | t, G, prev, (n + 1) =>
      (t 0 - prev, G 0) :: blocks (fun i => t (i + 1)) (fun i => G (i + 1)) (t 0) n

@[simp] theorem blocks_zero (t : ℕ → ℕ) (G : ℕ → ℝ → ℝ) (prev : ℕ) :
    blocks t G prev 0 = [] := rfl

@[simp] theorem blocks_succ (t : ℕ → ℕ) (G : ℕ → ℝ → ℝ) (prev n : ℕ) :
    blocks t G prev (n + 1)
      = (t 0 - prev, G 0) :: blocks (fun i => t (i + 1)) (fun i => G (i + 1)) (t 0) n := rfl

theorem blocks_length : ∀ (n : ℕ) (t : ℕ → ℕ) (G : ℕ → ℝ → ℝ) (prev : ℕ),
    (blocks t G prev n).length = n := by
  intro n
  induction n with
  | zero => intro _ _ _; simp
  | succ n ih => intro t G prev; simp [ih]

theorem blocks_obs : ∀ (n : ℕ) (t : ℕ → ℕ) (G : ℕ → ℝ → ℝ) (prev : ℕ),
    ∀ p ∈ blocks t G prev n, ∃ i, i < n ∧ p.2 = G i := by
  intro n
  induction n with
  | zero => intro _ _ _ p hp; simp at hp
  | succ n ih =>
      intro t G prev p hp
      rw [blocks_succ] at hp
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact ⟨0, by omega, rfl⟩
      · obtain ⟨i, hi, hgi⟩ := ih (fun i => t (i + 1)) (fun i => G (i + 1)) (t 0) p hp'
        exact ⟨i + 1, by omega, hgi⟩

theorem blocks_gap (M : ℕ) : ∀ (n : ℕ) (t : ℕ → ℕ) (G : ℕ → ℝ → ℝ) (prev : ℕ),
    prev + M ≤ t 0 → (∀ i, t i + M ≤ t (i + 1)) →
    ∀ p ∈ blocks t G prev n, M ≤ p.1 := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ p hp; simp at hp
  | succ n ih =>
      intro t G prev hprev ht p hp
      rw [blocks_succ] at hp
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact Nat.le_sub_of_add_le (by omega)
      · exact ih (fun i => t (i + 1)) (fun i => G (i + 1)) (t 0) (ht 0)
          (fun i => ht (i + 1)) p hp'

theorem blockProduct_blocks : ∀ (n : ℕ) (t : ℕ → ℕ) (G : ℕ → ℝ → ℝ) (prev : ℕ) (α : ℝ),
    prev ≤ t 0 → (∀ i, t i ≤ t (i + 1)) →
    Kwon1002.Transfer.blockProduct (blocks t G prev n) (Erdos1002.gaussOrbit prev α)
      = ∏ i ∈ Finset.range n, G i (Erdos1002.gaussOrbit (t i) α) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _; simp
  | succ n ih =>
      intro t G prev α hprev ht
      have hstep : Erdos1002.gaussOrbit (t 0 - prev) (Erdos1002.gaussOrbit prev α)
          = Erdos1002.gaussOrbit (t 0) α := by
        rw [gaussOrbit_add, Nat.sub_add_cancel hprev]
      rw [blocks_succ, Kwon1002.Transfer.blockProduct_cons, hstep,
        ih (fun i => t (i + 1)) (fun i => G (i + 1)) (t 0) α (ht 0) (fun i => ht (i + 1)),
        Finset.prod_range_succ']
      ring

theorem blockMean_blocks : ∀ (n : ℕ) (t : ℕ → ℕ) (G : ℕ → ℝ → ℝ) (prev : ℕ),
    Kwon1002.Transfer.blockMean (blocks t G prev n)
      = ∏ i ∈ Finset.range n, ∫ x, G i x ∂Erdos1002.gaussMeasure := by
  intro n
  induction n with
  | zero => intro _ _ _; simp
  | succ n ih =>
      intro t G prev
      rw [blocks_succ, Kwon1002.Transfer.blockMean_cons,
        ih (fun i => t (i + 1)) (fun i => G (i + 1)) (t 0), Finset.prod_range_succ']
      ring

/-- The `M`-separated extension of `t`: agrees with `t` below `s`, and
continues with steps of exactly `M` afterwards.  This removes the mismatch
between Kwon's separation hypothesis (`∀ i, i + 1 < s → …`) and the
`∀ i` shape the block recursion needs; the block list only ever looks at
indices `< s`. -/
def tSep (M s : ℕ) (t : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i < s then t i else t (s - 1) + M * (i + 1 - s)

theorem tSep_eq {M s : ℕ} {t : ℕ → ℕ} {i : ℕ} (h : i < s) : tSep M s t i = t i :=
  if_pos h

theorem tSep_zero {d M s : ℕ} {t : ℕ → ℕ} (h0 : d + M ≤ t 0) : d + M ≤ tSep M s t 0 := by
  rw [tSep]
  by_cases hs : 0 < s
  · rw [if_pos hs]; exact h0
  · rw [if_neg hs]
    have : s = 0 := by omega
    subst this
    simp
    omega

theorem tSep_step {M s : ℕ} {t : ℕ → ℕ}
    (hstep : ∀ i, i + 1 < s → t i + M ≤ t (i + 1)) (i : ℕ) :
    tSep M s t i + M ≤ tSep M s t (i + 1) := by
  rw [tSep, tSep]
  by_cases hi : i < s
  · by_cases hi1 : i + 1 < s
    · rw [if_pos hi, if_pos hi1]; exact hstep i hi1
    · rw [if_pos hi, if_neg hi1]
      have hsi : s = i + 1 := by omega
      subst hsi
      simp
  · have hs : s ≤ i := Nat.not_lt.1 hi
    have hi1 : ¬ (i + 1 < s) := by omega
    have hres : i + 1 + 1 - s = (i + 1 - s) + 1 := by omega
    rw [if_neg hi, if_neg hi1, hres, Nat.mul_succ]
    exact le_of_eq (by ring)

/-! ## 8. `ν`-a.e. the whole forward orbit stays in `Ioo 0 1` -/

theorem ae_orbit_mem_lt (N : ℕ) :
    ∀ᵐ α ∂Erdos1002.gaussMeasure,
      ∀ k, k < N → Erdos1002.gaussOrbit k α ∈ Ioo (0 : ℝ) 1 := by
  have hex : Erdos1002.gaussMeasure (Erdos1002.gaussPrefixExceptional N) = 0 :=
    Erdos1002.gaussMeasure_gaussPrefixExceptional N
  have hexae : ∀ᵐ α ∂Erdos1002.gaussMeasure,
      α ∉ Erdos1002.gaussPrefixExceptional N := by
    rw [ae_iff]; simpa using hex
  filter_upwards [Kwon1002.Transfer.gaussMeasure_ae_Ioo, hexae] with α hα hαex
  intro k hk
  have h1 : Erdos1002.gaussOrbit k α ∈ Ioc (0 : ℝ) 1 :=
    Erdos1002.gaussOrbit_mem_Ioc_of_not_mem_exceptional ⟨hα.1, hα.2.le⟩ hαex hk
  cases k with
  | zero => rw [Erdos1002.gaussOrbit_zero]; exact hα
  | succ j => exact ⟨h1.1, (Erdos1002.gaussOrbit_succ_mem_Ico j α).2⟩

theorem ae_orbit_mem :
    ∀ᵐ α ∂Erdos1002.gaussMeasure, ∀ k : ℕ, Erdos1002.gaussOrbit k α ∈ Ioo (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro k
  filter_upwards [ae_orbit_mem_lt (k + 1)] with α hα
  exact hα k (by omega)

/-! ## 9. The cylinder convention

`Prop41.cylinder d w = {α ∈ Ioo 0 1 | ∀ i < d, digit α i = w i}` is defined
by digits inside the *open* interval; the substrate conditions on
`Erdos1002.gaussHalfOpenPrefixCylinder`, built recursively from the
half-open first-digit cylinders `Ioc (1/(q+1)) (1/q)` starting from
`Ico 0 1`.

They agree off a `ν`-null set.  The content is: for `α ∈ Ioo 0 1` whose
forward orbit never hits `0` (i.e. `α ∉ Erdos1002.gaussPrefixExceptional d`,
`ν`-null by `Erdos1002.gaussMeasure_gaussPrefixExceptional`), one has
`Kwon1002.digit α i = Erdos1002.gaussDigitAt i α` (both are
`⌊(gaussMap^[i] α)⁻¹⌋.toNat`, definitionally) and
`x ∈ Erdos1002.firstDigitCylinder q ↔ Erdos1002.gaussFirstDigitNat x = q`
for `x ∈ Ioc 0 1`, so both sets cut out the same digit prefix.  The two
endpoint discrepancies (`0 ∈ Ico 0 1 ∖ Ioo 0 1` at `d = 0`, and `1`) are
`ν`-null because `ν ≪ Lebesgue`.

The missing ingredient was a membership characterisation of
`gaussHalfOpenPrefixCylinder` in terms of `gaussDigitAt`: the recursion is
never unfolded into digits anywhere in `wang_substrate/`, and Mathlib has no
continued-fraction cylinder API for the Gauss map.  `mem_halfOpen_iff` below
supplies it. -/

def digitWord (d : ℕ) (w : ℕ → ℕ) : List ℕ := (List.range d).map w

@[simp] theorem digitWord_length (d : ℕ) (w : ℕ → ℕ) : (digitWord d w).length = d := by
  simp [digitWord]

/-- A word containing the digit `0` cuts out the empty set.  (Proved: this is
what turns the measure-positivity hypothesis into `∀ q ∈ w, 0 < q`.) -/
theorem firstDigitCylinder_zero : Erdos1002.firstDigitCylinder 0 = (∅ : Set ℝ) := by
  rw [Erdos1002.firstDigitCylinder]
  rw [Set.Ioc_eq_empty]
  push_neg
  norm_num

theorem halfOpen_eq_empty_of_zero_mem :
    ∀ (v : List ℕ), 0 ∈ v → Erdos1002.gaussHalfOpenPrefixCylinder v = ∅ := by
  intro v
  induction v with
  | nil => intro h; simp at h
  | cons q qs ih =>
      intro h
      rcases List.mem_cons.1 h with hq | h'
      · show Erdos1002.firstDigitCylinder q ∩ _ = ∅
        rw [← hq, firstDigitCylinder_zero, Set.empty_inter]
      · show Erdos1002.firstDigitCylinder q ∩ _ = ∅
        rw [ih h', Set.preimage_empty, Set.inter_empty]

theorem word_pos_of_measure_pos {v : List ℕ}
    (hpos : 0 < (Erdos1002.gaussMeasure
      (Erdos1002.gaussHalfOpenPrefixCylinder v)).toReal) : ∀ q ∈ v, 0 < q := by
  intro q hq
  rcases Nat.eq_zero_or_pos q with rfl | h
  · exfalso
    rw [halfOpen_eq_empty_of_zero_mem v hq] at hpos
    simp at hpos
  · exact h

/-- Kwon's digit is the substrate's orbit digit, definitionally. -/
theorem digit_eq_gaussDigitAt (α : ℝ) (i : ℕ) :
    Kwon1002.digit α i = Erdos1002.gaussDigitAt i α := rfl

/-- **Membership in the substrate's half-open prefix cylinder, read off in
digits.**  Nothing of this kind exists in `wang_substrate/`: the recursion
defining `gaussHalfOpenPrefixCylinder` is never unfolded into digits there.
The hypothesis is exactly the `ν`-full-measure condition of §8. -/
theorem mem_halfOpen_iff : ∀ (v : List ℕ) (α : ℝ),
    (∀ k : ℕ, Erdos1002.gaussOrbit k α ∈ Ioo (0 : ℝ) 1) →
      (α ∈ Erdos1002.gaussHalfOpenPrefixCylinder v
        ↔ ∀ i, ∀ h : i < v.length, Erdos1002.gaussDigitAt i α = v[i]'h) := by
  intro v
  induction v with
  | nil =>
      intro α hα
      constructor
      · intro _ i hi; simp at hi
      · intro _
        show α ∈ Ico (0 : ℝ) 1
        have h0 := hα 0
        rw [Erdos1002.gaussOrbit_zero] at h0
        exact ⟨h0.1.le, h0.2⟩
  | cons q qs ih =>
      intro α hα
      have h0 := hα 0
      rw [Erdos1002.gaussOrbit_zero] at h0
      have hunit : α ∈ Ioc (0 : ℝ) 1 := ⟨h0.1, h0.2.le⟩
      have hshift : ∀ k : ℕ, Erdos1002.gaussOrbit k (Erdos1002.gaussMap α)
          = Erdos1002.gaussOrbit (k + 1) α := by
        intro k
        simp [Erdos1002.gaussOrbit, Function.iterate_succ_apply]
      have hβ : ∀ k : ℕ, Erdos1002.gaussOrbit k (Erdos1002.gaussMap α) ∈ Ioo (0 : ℝ) 1 := by
        intro k; rw [hshift k]; exact hα (k + 1)
      have hdig : ∀ i : ℕ, Erdos1002.gaussDigitAt i (Erdos1002.gaussMap α)
          = Erdos1002.gaussDigitAt (i + 1) α := by
        intro i
        rw [Erdos1002.gaussDigitAt, Erdos1002.gaussDigitAt, hshift i]
      have hd0 : Erdos1002.gaussDigitAt 0 α = Erdos1002.gaussFirstDigitNat α := by
        rw [Erdos1002.gaussDigitAt, Erdos1002.gaussOrbit_zero]
      have hcast := Erdos1002.gaussFirstDigitNat_cast hunit
      have hfd : α ∈ Erdos1002.firstDigitCylinder q ↔ Erdos1002.gaussDigitAt 0 α = q := by
        constructor
        · intro hm
          rcases Nat.eq_zero_or_pos q with rfl | hq
          · rw [firstDigitCylinder_zero] at hm
            exact absurd hm (Set.notMem_empty _)
          · have hfe :=
              (Erdos1002.gaussFirstDigit_eq_iff_mem_firstDigitCylinder hunit q hq).2 hm
            rw [hd0]
            exact_mod_cast hcast.trans hfe
        · intro hm
          rw [hd0] at hm
          have hq : 0 < q := by
            rw [← hm]; exact Erdos1002.gaussFirstDigitNat_pos hunit
          refine (Erdos1002.gaussFirstDigit_eq_iff_mem_firstDigitCylinder hunit q hq).1 ?_
          rw [← hcast, hm]
      have hunfold : Erdos1002.gaussHalfOpenPrefixCylinder (q :: qs)
          = Erdos1002.firstDigitCylinder q ∩
            Erdos1002.gaussMap ⁻¹' Erdos1002.gaussHalfOpenPrefixCylinder qs := rfl
      rw [hunfold]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        cases i with
        | zero => simpa using hfd.1 h1
        | succ j =>
            have hj : j < qs.length := by simpa using hi
            have hrec := (ih (Erdos1002.gaussMap α) hβ).1 h2 j hj
            rw [hdig j] at hrec
            simpa using hrec
      · intro h
        refine ⟨hfd.2 (by simpa using h 0 (by simp)), ?_⟩
        refine (ih (Erdos1002.gaussMap α) hβ).2 (fun j hj => ?_)
        rw [hdig j]
        have hj1 := h (j + 1) (by simpa using hj)
        simpa using hj1

theorem cylinder_ae_eq_halfOpen (d : ℕ) (w : ℕ → ℕ) :
    (cylinder d w : Set ℝ) =ᵐ[Erdos1002.gaussMeasure]
      Erdos1002.gaussHalfOpenPrefixCylinder (digitWord d w) := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [ae_orbit_mem] with α hα
  have hiff := mem_halfOpen_iff (digitWord d w) α hα
  have h0 := hα 0
  rw [Erdos1002.gaussOrbit_zero] at h0
  have hget : ∀ i (h : i < (digitWord d w).length), (digitWord d w)[i]'h = w i := by
    intro i h
    simp [digitWord]
  rw [hiff]
  constructor
  · intro hmem i hi
    rw [hget i hi, ← digit_eq_gaussDigitAt]
    exact hmem.2 i (by simpa [digitWord] using hi)
  · intro h
    refine ⟨h0, fun i hi => ?_⟩
    rw [digit_eq_gaussDigitAt]
    have hi' : i < (digitWord d w).length := by simpa [digitWord] using hi
    have := h i hi'
    rwa [hget i hi'] at this

/-! ## 10. The core estimate, at `K = 1` -/

theorem core_estimate (s d M : ℕ) (w : ℕ → ℕ) (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ)
    (hbv : ∀ i, i < s → BVBoundedBy 1 (g i))
    (h0 : d + M ≤ t 0) (hstep : ∀ i, i + 1 < s → t i + M ≤ t (i + 1))
    (hpos : 0 < (Erdos1002.gaussMeasure (cylinder d w)).toReal) :
    |(∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
          ∂Erdos1002.gaussMeasure) / (Erdos1002.gaussMeasure (cylinder d w)).toReal
        - ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
      ≤ 2 ^ s * bvBound 2 M s := by
  classical
  set W : List ℕ := digitWord d w with hW
  have haeq := cylinder_ae_eq_halfOpen d w
  have hmeas : Erdos1002.gaussMeasure (cylinder d w)
      = Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder W) :=
    measure_congr haeq
  have hrestr : Erdos1002.gaussMeasure.restrict (cylinder d w)
      = Erdos1002.gaussMeasure.restrict (Erdos1002.gaussHalfOpenPrefixCylinder W) :=
    Measure.restrict_congr_set haeq
  have hposW : 0 < (Erdos1002.gaussMeasure
      (Erdos1002.gaussHalfOpenPrefixCylinder W)).toReal := by rwa [hmeas] at hpos
  have hwpos : ∀ q ∈ W, 0 < q := word_pos_of_measure_pos hposW
  -- the measurable, globally bounded representatives
  set G : ℕ → ℝ → ℝ := fun i => bvClamp 1 (g i) with hG
  have hsplit : ∀ i, i < s → Splittable 2 (G i) := by
    intro i hi
    refine ⟨fun x => bvClamp 1 (g i) x + 1, fun _ => 1, fun x => by ring, ?_, ?_⟩
    · simpa using globGood_bvShift (K := 1) zero_le_one (hbv i hi)
    · simpa using globGood_const (K := 1) zero_le_one
  have hTzero0 : d ≤ tSep M s t 0 := by
    have := tSep_zero (d := d) (M := M) (s := s) (t := t) h0; omega
  have hTstep0 : ∀ i, tSep M s t i ≤ tSep M s t (i + 1) := fun i => by
    have := tSep_step (M := M) (s := s) (t := t) hstep i; omega
  set T : ℕ → ℕ := tSep M s t with hT
  set bs : List (ℕ × (ℝ → ℝ)) := blocks T G d s with hbs
  have hbsG : ∀ p ∈ bs, Splittable 2 p.2 := by
    intro p hp
    obtain ⟨i, hi, hgi⟩ := blocks_obs s T G d p hp
    rw [hgi]; exact hsplit i hi
  have hbsM : ∀ p ∈ bs, M ≤ p.1 :=
    blocks_gap M s T G d (tSep_zero h0) (tSep_step hstep)
  have hmix := mixDefect_signed_le W hwpos hposW (A := 2) (by norm_num) M bs []
    (by simp) (by simp) hbsG hbsM
  rw [List.nil_append, List.length_nil, Nat.zero_add, blocks_length] at hmix
  -- identify `mixDefect` with the target expression
  have hbp : ∀ α : ℝ, Kwon1002.Transfer.blockProduct bs (Erdos1002.gaussOrbit W.length α)
      = ∏ i ∈ Finset.range s, G i (Erdos1002.gaussOrbit (T i) α) := by
    intro α
    have hlen : W.length = d := by rw [hW]; simp
    rw [hlen]
    exact blockProduct_blocks s T G d α hTzero0 hTstep0
  have hbm : Kwon1002.Transfer.blockMean bs
      = ∏ i ∈ Finset.range s, ∫ x, G i x ∂Erdos1002.gaussMeasure :=
    blockMean_blocks s T G d
  -- replace `G` by `g` (they agree on `Ioo 0 1`, which has full `ν`-mass)
  have hGg : ∀ i, i < s → ∀ x ∈ Ioo (0 : ℝ) 1, G i x = g i x := by
    intro i hi x hx
    exact bvClamp_eq_of_mem (hbv i hi) hx
  have hmean : ∀ i, i < s →
      (∫ x, G i x ∂Erdos1002.gaussMeasure) = ∫ x, g i x ∂Erdos1002.gaussMeasure := by
    intro i hi
    refine integral_congr_ae ?_
    filter_upwards [Kwon1002.Transfer.gaussMeasure_ae_Ioo] with x hx
    exact hGg i hi x hx
  have hprodmean : (∏ i ∈ Finset.range s, ∫ x, G i x ∂Erdos1002.gaussMeasure)
      = ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure :=
    Finset.prod_congr rfl (fun i hi => hmean i (Finset.mem_range.1 hi))
  have hintegrand : ∀ᵐ α ∂Erdos1002.gaussMeasure,
      (∏ i ∈ Finset.range s, G i (Erdos1002.gaussOrbit (T i) α))
        = ∏ i ∈ Finset.range s, g i (gaussIter α (t i)) := by
    filter_upwards [ae_orbit_mem] with α hα
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' : i < s := Finset.mem_range.1 hi
    rw [gaussIter_eq_gaussOrbit, ← tSep_eq (M := M) (t := t) hi']
    exact hGg i hi' _ (hα (T i))
  -- assemble
  have hcond : Kwon1002.Transfer.condMean (Erdos1002.gaussHalfOpenPrefixCylinder W)
        (fun α => Kwon1002.Transfer.blockProduct bs (Erdos1002.gaussOrbit W.length α))
      = (∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
            ∂Erdos1002.gaussMeasure)
          / (Erdos1002.gaussMeasure (cylinder d w)).toReal := by
    rw [Kwon1002.Transfer.condMean, ← hmeas, ← hrestr]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hintegrand] with α hα
    rw [hbp α]; exact hα
  rw [mixDefect, hcond, hbm, hprodmean] at hmix
  exact hmix

/-! ## 11. The target

Reproduced **token-identically** from `Kwon1002/Prop41.lean`, lines 267-276
(diffed character-for-character against the extracted block); only the name
carries a prime. -/

/-- Machine check that the identifiers in the reproduction below are the
target's, not local look-alikes. -/
example : @BVBoundedBy = @Kwon1002.Prop41.BVBoundedBy := rfl

example (d : ℕ) (w : ℕ → ℕ) : cylinder d w = Kwon1002.Prop41.cylinder d w := rfl

example : @gaussIter = @Kwon1002.gaussIter := rfl

/-- Homogeneity of a finite product in a field. -/
theorem const_pow_mul_prod_div (n : ℕ) (f : ℕ → ℝ) {K : ℝ} (hK : K ≠ 0) :
    K ^ n * ∏ i ∈ Finset.range n, (f i / K) = ∏ i ∈ Finset.range n, f i := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  field_simp

theorem lem_3_2_conditional_multiblock_mixing' (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : ℕ → ℕ) (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → BVBoundedBy K (g i)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        0 < (Erdos1002.gaussMeasure (cylinder d w)).toReal →
        |(∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
              ∂Erdos1002.gaussMeasure) / (Erdos1002.gaussMeasure (cylinder d w)).toReal
            - ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ M * K ^ s := by
  refine ⟨2 ^ s * (478 * ((s : ℝ) + 1) * 16 ^ s * 2), Real.sqrt (527 / 540),
    by positivity, Real.sqrt_pos.2 (by norm_num), ?_, ?_⟩
  · have h : Real.sqrt (527 / 540) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at h
  · intro d M w t g K hK hbv h0 hstep hpos
    have hCeq : (2 : ℝ) ^ s * bvBound 2 M s
        = 2 ^ s * (478 * ((s : ℝ) + 1) * 16 ^ s * 2) * Real.sqrt (527 / 540) ^ M := by
      rw [bvBound, show (8 : ℝ) * 2 = 16 by norm_num]
      ring
    set X : ℝ :=
      (∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
          ∂Erdos1002.gaussMeasure) / (Erdos1002.gaussMeasure (cylinder d w)).toReal
        - ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure with hX
    have main : ∀ K' : ℝ, 0 < K' → (∀ i, i < s → BVBoundedBy K' (g i)) →
        |X| ≤ 2 ^ s * (478 * ((s : ℝ) + 1) * 16 ^ s * 2)
            * Real.sqrt (527 / 540) ^ M * K' ^ s := by
      intro K' hK' hbv'
      obtain ⟨g', hg'⟩ : ∃ g' : ℕ → ℝ → ℝ, ∀ i x, g' i x = g i x / K' :=
        ⟨fun i x => g i x / K', fun _ _ => rfl⟩
      have hbv1 : ∀ i, i < s → BVBoundedBy 1 (g' i) := by
        intro i hi
        obtain ⟨hsup, hvar⟩ := hbv' i hi
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [hg' i x, abs_div, abs_of_pos hK', div_le_one hK']
          exact hsup x hx
        · have heq : eVariationOn (g' i) (Ioo (0 : ℝ) 1)
              = eVariationOn (fun x => (1 / K') * g i x) (Ioo (0 : ℝ) 1) := by
            refine eVariationOn.eq_of_eqOn (fun x _ => ?_)
            rw [hg' i x]
            field_simp
          rw [heq]
          refine le_trans (eVariationOn_const_mul_le (1 / K') (g i) (Ioo (0 : ℝ) 1)) ?_
          rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / K')]
          calc ENNReal.ofReal (1 / K') * eVariationOn (g i) (Ioo (0 : ℝ) 1)
              ≤ ENNReal.ofReal (1 / K') * ENNReal.ofReal K' := by gcongr
            _ = ENNReal.ofReal 1 := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                field_simp
      have hcore := core_estimate s d M w t g' hbv1 h0 hstep hpos
      have hptA : ∀ α : ℝ, (∏ i ∈ Finset.range s, g i (gaussIter α (t i)))
          = K' ^ s * ∏ i ∈ Finset.range s, g' i (gaussIter α (t i)) := by
        intro α
        rw [← const_pow_mul_prod_div s (fun i => g i (gaussIter α (t i))) (ne_of_gt hK')]
        congr 1
        exact Finset.prod_congr rfl (fun i _ => (hg' i _).symm)
      have hA : (∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
            ∂Erdos1002.gaussMeasure)
          = K' ^ s * ∫ α in cylinder d w, ∏ i ∈ Finset.range s, g' i (gaussIter α (t i))
              ∂Erdos1002.gaussMeasure := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall hptA)
      have hB : (∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure)
          = K' ^ s * ∏ i ∈ Finset.range s, ∫ x, g' i x ∂Erdos1002.gaussMeasure := by
        rw [← const_pow_mul_prod_div s
          (fun i => ∫ x, g i x ∂Erdos1002.gaussMeasure) (ne_of_gt hK')]
        congr 1
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [← integral_div]
        exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (hg' i x).symm))
      rw [hX, hA, hB]
      have hrw : K' ^ s * (∫ α in cylinder d w,
              ∏ i ∈ Finset.range s, g' i (gaussIter α (t i)) ∂Erdos1002.gaussMeasure)
            / (Erdos1002.gaussMeasure (cylinder d w)).toReal
          - K' ^ s * ∏ i ∈ Finset.range s, ∫ x, g' i x ∂Erdos1002.gaussMeasure
          = K' ^ s * ((∫ α in cylinder d w,
              ∏ i ∈ Finset.range s, g' i (gaussIter α (t i)) ∂Erdos1002.gaussMeasure)
            / (Erdos1002.gaussMeasure (cylinder d w)).toReal
          - ∏ i ∈ Finset.range s, ∫ x, g' i x ∂Erdos1002.gaussMeasure) := by ring
      rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ K' ^ s)]
      calc K' ^ s * |(∫ α in cylinder d w,
              ∏ i ∈ Finset.range s, g' i (gaussIter α (t i)) ∂Erdos1002.gaussMeasure)
            / (Erdos1002.gaussMeasure (cylinder d w)).toReal
          - ∏ i ∈ Finset.range s, ∫ x, g' i x ∂Erdos1002.gaussMeasure|
          ≤ K' ^ s * (2 ^ s * bvBound 2 M s) :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
        _ = 2 ^ s * (478 * ((s : ℝ) + 1) * 16 ^ s * 2)
              * Real.sqrt (527 / 540) ^ M * K' ^ s := by rw [hCeq]; ring
    rcases eq_or_lt_of_le hK with hK0 | hKpos
    · -- `K = 0`: the observables vanish on `Ioo 0 1`, which carries all the mass.
      rcases Nat.eq_zero_or_pos s with hs0 | hs
      · subst hs0
        simpa using main 1 one_pos (by intro i hi; omega)
      · have hz : ∀ i, i < s → ∀ x ∈ Ioo (0 : ℝ) 1, g i x = 0 := by
          intro i hi x hx
          have hle := (hbv i hi).1 x hx
          rw [← hK0] at hle
          exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))
        have hmean0 : (∫ x, g 0 x ∂Erdos1002.gaussMeasure) = 0 := by
          rw [show (0 : ℝ) = ∫ _x, (0 : ℝ) ∂Erdos1002.gaussMeasure by simp]
          refine integral_congr_ae ?_
          filter_upwards [Kwon1002.Transfer.gaussMeasure_ae_Ioo] with x hx
          exact hz 0 hs x hx
        have hprod0 : (∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure) = 0 :=
          Finset.prod_eq_zero (Finset.mem_range.2 hs) hmean0
        have hint0 : (∫ α in cylinder d w, ∏ i ∈ Finset.range s, g i (gaussIter α (t i))
              ∂Erdos1002.gaussMeasure) = 0 := by
          rw [show (0 : ℝ) = ∫ _α in cylinder d w, (0 : ℝ) ∂Erdos1002.gaussMeasure by simp]
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae ae_orbit_mem] with α hα
          refine Finset.prod_eq_zero (Finset.mem_range.2 hs) ?_
          rw [gaussIter_eq_gaussOrbit]
          exact hz 0 hs _ (hα (t 0))
        rw [hX, hint0, hprod0, zero_div, sub_zero, abs_zero, ← hK0,
          zero_pow (by omega), mul_zero]
    · exact main K hKpos hbv

end

end Kwon1002.MixingBV


/-
## Summary

PROVED OUTRIGHT (no `sorry`; axioms of every theorem below are exactly
`[propext, Classical.choice, Quot.sound]`, machine-checked with
`#print axioms`, then removed):

  `lem_3_2_conditional_multiblock_mixing'`, the target,
  `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing`, reproduced
  token-identically (diff of the two 10-line statement blocks is empty;
  only the name carries a prime) and derived.  Explicit constants:

      C = 2^s · 478 · (s+1) · 16^s · 2 ,    ρ = √(527/540) .

  The `2^s` is the sign expansion, the `478·(s+1)·16^s·2` is
  `BVMixing.lemma_3_2_BV` at `A = 2K`, and `√(527/540)` is Wang's
  Lipschitz contraction rate after the mollification interpolation.

Auxiliary results proved here, none of which exists in Mathlib, in Wang's
substrate, or elsewhere in `Kwon1002/`:

  * `eVariationOn_add_const_le`, `eVariationOn_const_mul_le`, the two
    missing algebraic facts about `eVariationOn` used below;
  * `monoExt` + `monotone_monoExt` + `bvRepr` + `bvClamp`, the measurable
    representative of a `BV(0,1)` function;
  * `blockProduct_append`, `blockMean_append`, `gaussOrbit_add`, block-list
    algebra;
  * `mixDefect_split`, multilinearity of the mixing defect;
  * `mixDefect_signed_le`, signed BV multi-block mixing (the sign fix);
  * `blocks` + `blockProduct_blocks` + `blockMean_blocks` + `tSep`, the
    absolute-times ↔ gaps dictionary;
  * `ae_orbit_mem`, `ν`-a.e. the entire forward orbit stays in `Ioo 0 1`;
  * `mem_halfOpen_iff`, digit characterisation of the substrate's
    half-open prefix cylinder;
  * `cylinder_ae_eq_halfOpen`, `firstDigitCylinder_zero`,
    `halfOpen_eq_empty_of_zero_mem`, `word_pos_of_measure_pos`, the
    cylinder-convention reconciliation;
  * `core_estimate`, the whole thing at `K = 1`.

CONSUMED FROM OTHER FILES: `Kwon1002.BVMixing` (Wave 1), `lemma_3_2_BV`,
`bvP`, `bvQ`, `bvP_monotoneOn`, `bvQ_monotoneOn`, `abs_bvP_le`,
`abs_bvQ_le`, `bvP_sub_bvQ`; `Kwon1002.Transfer`, `blockProduct`,
`blockMean`, `condMean`, `measurable_blockProduct`, `gaussMeasure_ae_Ioo`;
`Erdos1002`, `gaussOrbit`, `gaussDigitAt`, `gaussHalfOpenPrefixCylinder`,
`firstDigitCylinder`, `gaussFirstDigit_eq_iff_mem_firstDigitCylinder`,
`gaussFirstDigitNat_cast`, `gaussFirstDigitNat_pos`,
`gaussOrbit_mem_Ioc_of_not_mem_exceptional`,
`gaussMeasure_gaussPrefixExceptional`, `gaussOrbit_succ_mem_Ico`.
**No sorried result is consumed.**  (In particular the sorried
`Kwon1002.Transfer.cylinder_transfer_eq_kwonDensity` is *not* on the
dependency path: `BVMixing.lemma_3_2_BV` goes through
`TransferIdentity.lemma_3_2'`, which uses the corrected, axiom-clean
`TransferIdentity.cylinder_transfer_eq_kwonDensity_Ioo`.)

WHAT THIS UNBLOCKS.  `Kwon1002.ErrorShape.good_tuple_multiblock_mixing` is
the sole consumer of the target; promoting this file (or transplanting
§1-§11 into `Kwon1002/Prop41.lean`) removes that sorry, and with it the
§4 mixing debt.  The degradation of the rate from `527/540` to
`√(527/540)` is harmless: `Prop41.deltaScaleR_le_rpow_neg` and
`Prop41.eventually_rpow_mul_deltaScale_le` are quantified over every
`ρ ∈ (0,1)`.

NOT CLOSED (and not needed here): Lemma 3.1(i) in `BV` with a sharp rate
(`BVScout.lemma_3_1_i_bv`), which requires quasi-compactness /
Ionescu-Tulcea-Marinescu on top of a BV Lasota-Yorke inequality; and the
six analytic inputs of `BVIterate`'s `L²` route.
-/
