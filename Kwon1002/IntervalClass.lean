import Kwon1002.Reciprocity

/-!
# Finite unions of intervals, and the uniform jump count of the mark section

`Kwon1002/JacksonGate.lean` establishes that the approximation
`TupleFinal.goodSet_mark_factorization` asks for cannot exist under the
hypotheses that residual carries: membership of the symbol class `P_D(L)` of
display (24) forces continuity (`JacksonGate.continuous_of_isInPD`), a
two-valued member is constant (`JacksonGate.isInPD_const_of_two_valued`), and
for a merely measurable `B` no *rate* of `L¹` approximation exists.  What the
residual needs, and does not state, is boundary regularity on `B`.

This module supplies the missing class and proves the two facts that make it
the right one.

## The class

`IsUnionOfIntervals m B` says `B` is a union of at most `m` order-convex sets.
Order-convexity (`Set.OrdConnected`) is exactly "interval" on `ℝ`, in the form
that is stable under the operations the argument performs, and it avoids
having to name endpoints or to decide open versus closed — the boundary cases
are where an endpoint-based rendering leaks.

## Fact 1, the class is closed under what the argument does

`IsUnionOfIntervals.inter_preimage`: if `f` is monotone **or** antitone on an
order-convex set `S`, then `S ∩ f⁻¹(B)` is a union of at most `m` intervals.
The count does not grow.  Specialized to `f = id` this is closure under
intersection with an interval (`IsUnionOfIntervals.inter`).

## Fact 2, the uniform jump count of the `θ`-section

`markSection_isUnionOfIntervals` is the estimate `JacksonGate` names but does
not prove: `W(θ) = {θ}(1-{θ})/2` is piecewise monotone on the fundamental cell
with exactly **two** branches (increasing on `[0,1/2]`, decreasing on
`[1/2,1)`), so for `B` a union of `m` intervals the `θ`-section

  `{θ ∈ [0,1) : κ·W(θ) ∈ B}`

is a union of at most `2m` intervals — **uniformly in `κ`**, and in
particular uniformly in the digit `a` and in the sign `(-1)^j` that enter
through `κ = ±a/L`.  That uniformity is the property the tuple sum needs and
the reason a Jackson bound of the shape `O(m/deg)` is available at this class
and at no larger one.

The sign is handled by the monotone-or-antitone disjunction rather than by a
case split on `a`, so `a = 0` and negative `κ` are covered with no side
condition.

## What this does **not** supply

The instantiation of the Jackson approximation at this class.  The kernel
itself is no longer missing: `Kwon1002/Fejer.lean` builds it from scratch
(Mathlib still carries none — `Mathlib/Analysis/Fourier/` has `AddCircle`,
`FourierTransform`, `RiemannLebesgueLemma`, `Inversion`, `PoissonSummation`,
and no summability kernel of positive type), together with the `L¹`
approximation bound `Fejer.fejerPoly_L1_error_le`, the `ℓ¹` coefficient budget
`Fejer.fejerCoeff_l1_le`, and membership of the approximant in the symbol
class of display (24), `Fejer.isInPD_fejerPoly`.

What is *not* done here is the instantiation: `Fejer.fejerPoly_L1_error_le`
runs against an explicit **good set** — the points of the fundamental cell at
which the symbol does not move under translations of size at most `s` — and
turning `IsUnionOfIntervals m B` into such a good set with
`volume (bad) = O(m·s)` is the step that remains, together with the passage
from the `θ`-section back to `TupleFinal.detMarkEvent`.  Both are recorded on
`TupleFinal.goodSet_mark_factorization_intervals`.
-/

open Set

namespace Kwon1002

namespace IntervalClass

/-! ## The class -/

/-- `B` is a union of at most `m` intervals.  "Interval" is rendered as
`Set.OrdConnected`, which on `ℝ` is exactly order-convexity and is stable
under the intersections and monotone preimages the argument takes. -/
def IsUnionOfIntervals (m : ℕ) (B : Set ℝ) : Prop :=
  ∃ s : Finset (Set ℝ), s.card ≤ m ∧ (∀ I ∈ s, I.OrdConnected) ∧ B = ⋃ I ∈ s, I

/-- `B` is a finite union of intervals: the hypothesis
`Kwon1002/JacksonGate.lean` shows `TupleFinal.goodSet_mark_factorization`
requires. -/
def IsFiniteUnionOfIntervals (B : Set ℝ) : Prop := ∃ m : ℕ, IsUnionOfIntervals m B

theorem IsUnionOfIntervals.finite {m : ℕ} {B : Set ℝ} (h : IsUnionOfIntervals m B) :
    IsFiniteUnionOfIntervals B := ⟨m, h⟩

theorem IsUnionOfIntervals.mono {m m' : ℕ} {B : Set ℝ} (h : IsUnionOfIntervals m B)
    (hm : m ≤ m') : IsUnionOfIntervals m' B := by
  obtain ⟨s, hcard, hoc, hB⟩ := h
  exact ⟨s, hcard.trans hm, hoc, hB⟩

/-- A single interval. -/
theorem isUnionOfIntervals_one {B : Set ℝ} (hB : B.OrdConnected) :
    IsUnionOfIntervals 1 B := by
  classical
  refine ⟨{B}, by simp, ?_, ?_⟩
  · intro I hI
    rw [Finset.mem_singleton] at hI
    exact hI ▸ hB
  · simp

theorem isUnionOfIntervals_empty (m : ℕ) : IsUnionOfIntervals m (∅ : Set ℝ) :=
  ⟨∅, by simp, by simp, by simp⟩

/-- The union of a union of `m` intervals and a union of `m'` intervals is a
union of at most `m + m'` intervals. -/
theorem IsUnionOfIntervals.union {m m' : ℕ} {B B' : Set ℝ}
    (h : IsUnionOfIntervals m B) (h' : IsUnionOfIntervals m' B') :
    IsUnionOfIntervals (m + m') (B ∪ B') := by
  classical
  obtain ⟨s, hcard, hoc, hB⟩ := h
  obtain ⟨t, hcard', hoc', hB'⟩ := h'
  refine ⟨s ∪ t, ?_, ?_, ?_⟩
  · exact (Finset.card_union_le s t).trans (Nat.add_le_add hcard hcard')
  · intro I hI
    rcases Finset.mem_union.mp hI with hI | hI
    · exact hoc I hI
    · exact hoc' I hI
  · rw [Finset.set_biUnion_union, ← hB, ← hB']

/-! ## Order-convexity is preserved by monotone and antitone preimages -/

/-- If `f` is monotone on an order-convex `S`, the trace of a monotone
preimage on `S` is order-convex. -/
theorem ordConnected_inter_preimage_of_monotoneOn {f : ℝ → ℝ} {S J : Set ℝ}
    (hS : S.OrdConnected) (hf : MonotoneOn f S) (hJ : J.OrdConnected) :
    (S ∩ f ⁻¹' J).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  have hzS : z ∈ S := hS.out hx.1 hy.1 hz
  exact ⟨hzS, hJ.out hx.2 hy.2 ⟨hf hx.1 hzS hz.1, hf hzS hy.1 hz.2⟩⟩

/-- The antitone half of the previous lemma. -/
theorem ordConnected_inter_preimage_of_antitoneOn {f : ℝ → ℝ} {S J : Set ℝ}
    (hS : S.OrdConnected) (hf : AntitoneOn f S) (hJ : J.OrdConnected) :
    (S ∩ f ⁻¹' J).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  have hzS : z ∈ S := hS.out hx.1 hy.1 hz
  exact ⟨hzS, hJ.out hy.2 hx.2 ⟨hf hzS hy.1 hz.2, hf hx.1 hzS hz.1⟩⟩

/-- **The class is closed under monotone (or antitone) traces, without growth
of the interval count.**  This is the step that makes the count `2m` of
`markSection_isUnionOfIntervals` uniform: each branch of `W` contributes one
interval per interval of `B`, whatever the digit is. -/
theorem IsUnionOfIntervals.inter_preimage {m : ℕ} {B : Set ℝ}
    (hB : IsUnionOfIntervals m B) {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hf : MonotoneOn f S ∨ AntitoneOn f S) :
    IsUnionOfIntervals m (S ∩ f ⁻¹' B) := by
  classical
  obtain ⟨s, hcard, hoc, hB⟩ := hB
  refine ⟨s.image (fun J => S ∩ f ⁻¹' J), (Finset.card_image_le).trans hcard, ?_, ?_⟩
  · intro I hI
    obtain ⟨J, hJs, rfl⟩ := Finset.mem_image.mp hI
    rcases hf with hf | hf
    · exact ordConnected_inter_preimage_of_monotoneOn hS hf (hoc J hJs)
    · exact ordConnected_inter_preimage_of_antitoneOn hS hf (hoc J hJs)
  · rw [hB]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iUnion,
      Finset.mem_image, exists_prop, exists_exists_and_eq_and]
    constructor
    · rintro ⟨hxS, J, hJs, hxJ⟩
      exact ⟨J, hJs, hxS, hxJ⟩
    · rintro ⟨J, hJs, hxS, hxJ⟩
      exact ⟨hxS, J, hJs, hxJ⟩

/-- Intersection with an interval, the `f = id` case. -/
theorem IsUnionOfIntervals.inter {m : ℕ} {B J : Set ℝ} (hB : IsUnionOfIntervals m B)
    (hJ : J.OrdConnected) : IsUnionOfIntervals m (J ∩ B) :=
  hB.inter_preimage hJ (Or.inl (monotoneOn_id))

/-! ## The truncation sets of §5 are unions of two intervals

Every concrete instantiation of `B` in the §5 chain is a truncation
`{x : ε < |x|}` cut to a bounded window.  These lemmas are what let a consumer
of the amended `TupleFinal.goodSet_mark_factorization` actually *supply* the
new hypothesis rather than merely believe it. -/

/-- `{x : ε < |x|}` is the union of the two intervals `(ε, ∞)` and `(-∞, -ε)`. -/
theorem isUnionOfIntervals_abs_gt (ε : ℝ) :
    IsUnionOfIntervals 2 {x : ℝ | ε < |x|} := by
  have hsplit : {x : ℝ | ε < |x|} = Ioi ε ∪ Iio (-ε) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ioi, mem_Iio, lt_abs, lt_neg]
  rw [hsplit]
  exact (isUnionOfIntervals_one ordConnected_Ioi).union
    (isUnionOfIntervals_one ordConnected_Iio)

/-- `{x : δ ≤ |x|}` is the union of the two intervals `[δ, ∞)` and `(-∞, -δ]`. -/
theorem isUnionOfIntervals_abs_ge (δ : ℝ) :
    IsUnionOfIntervals 2 {x : ℝ | δ ≤ |x|} := by
  have hsplit : {x : ℝ | δ ≤ |x|} = Ici δ ∪ Iic (-δ) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ici, mem_Iic, le_abs, le_neg]
  rw [hsplit]
  exact (isUnionOfIntervals_one ordConnected_Ici).union
    (isUnionOfIntervals_one ordConnected_Iic)

/-- **The truncation window of §5 is a union of two intervals.**  This is the
shape every consumer of `goodSet_mark_factorization` instantiates `B` at: the
large-jump truncation `ε < |x|`, cut to the bounded window `|x| ≤ R` that the
residual's own `_hBbd` hypothesis forces. -/
theorem isUnionOfIntervals_truncation (ε R : ℝ) :
    IsUnionOfIntervals 2 {x : ℝ | ε < |x| ∧ |x| ≤ R} := by
  have hrw : {x : ℝ | ε < |x| ∧ |x| ≤ R} = Icc (-R) R ∩ {x : ℝ | ε < |x|} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_Icc, abs_le]
    tauto
  rw [hrw]
  exact (isUnionOfIntervals_abs_gt ε).inter ordConnected_Icc

/-- The closed-inner-radius variant, matching the residual's own
`∃ δ > 0, ∀ x ∈ B, δ ≤ |x|`. -/
theorem isUnionOfIntervals_annulus (δ R : ℝ) :
    IsUnionOfIntervals 2 {x : ℝ | δ ≤ |x| ∧ |x| ≤ R} := by
  have hrw : {x : ℝ | δ ≤ |x| ∧ |x| ≤ R} = Icc (-R) R ∩ {x : ℝ | δ ≤ |x|} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_Icc, abs_le]
    tauto
  rw [hrw]
  exact (isUnionOfIntervals_abs_ge δ).inter ordConnected_Icc

/-! ## `W` has exactly two monotone branches on the fundamental cell -/

/-- `W` increases on `[0, 1/2]`. -/
theorem monotoneOn_W_left : MonotoneOn W (Icc (0 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  rw [W_eq_of_mem hx0 (by linarith), W_eq_of_mem hy0 (by linarith)]
  nlinarith

/-- `W` decreases on `[1/2, 1)`. -/
theorem antitoneOn_W_right : AntitoneOn W (Ico (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  rw [W_eq_of_mem (by linarith) hx1, W_eq_of_mem (by linarith) hy1]
  nlinarith

/-- The fundamental cell is the union of the two branches. -/
theorem Ico_eq_branches : Ico (0 : ℝ) 1 = Icc (0 : ℝ) (1 / 2) ∪ Ico (1 / 2 : ℝ) 1 := by
  ext x
  simp only [mem_Ico, mem_union, mem_Icc]
  constructor
  · rintro ⟨h0, h1⟩
    rcases le_or_gt x (1 / 2) with h | h
    · exact Or.inl ⟨h0, h⟩
    · exact Or.inr ⟨h.le, h1⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · exact ⟨h0, by linarith⟩
    · exact ⟨by linarith, h1⟩

/-! ## The uniform jump count -/

/-- **The `θ`-section of the mark event has at most `2m` jumps, uniformly in
the scaling.**

For `B` a union of at most `m` intervals and *any* real `κ`, the set

  `{θ ∈ [0,1) : κ·W(θ) ∈ B}`

is a union of at most `2m` intervals.  Since `κ` is arbitrary, the bound is
uniform in the digit `a` and in the sign `(-1)^j`, both of which enter only
through `κ = ±a/L`.

This is the statement `Kwon1002/JacksonGate.lean` identifies as the content of
the missing boundary-regularity hypothesis: it is what makes a Jackson `L¹`
error `O(m/deg)` available at this class, and it fails for a general
measurable `B` (a fat Cantor set inside `[1,2]` satisfies all three hypotheses
the residual currently carries and has a section with no finite jump count). -/
theorem markSection_isUnionOfIntervals {m : ℕ} {B : Set ℝ}
    (hB : IsUnionOfIntervals m B) (κ : ℝ) :
    IsUnionOfIntervals (2 * m) {θ : ℝ | θ ∈ Ico (0 : ℝ) 1 ∧ κ * W θ ∈ B} := by
  have hmono : MonotoneOn (fun θ => κ * W θ) (Icc (0 : ℝ) (1 / 2))
      ∨ AntitoneOn (fun θ => κ * W θ) (Icc (0 : ℝ) (1 / 2)) := by
    rcases le_or_gt 0 κ with hκ | hκ
    · exact Or.inl fun x hx y hy hxy =>
        mul_le_mul_of_nonneg_left (monotoneOn_W_left hx hy hxy) hκ
    · exact Or.inr fun x hx y hy hxy =>
        mul_le_mul_of_nonpos_left (monotoneOn_W_left hx hy hxy) hκ.le
  have hanti : MonotoneOn (fun θ => κ * W θ) (Ico (1 / 2 : ℝ) 1)
      ∨ AntitoneOn (fun θ => κ * W θ) (Ico (1 / 2 : ℝ) 1) := by
    rcases le_or_gt 0 κ with hκ | hκ
    · exact Or.inr fun x hx y hy hxy =>
        mul_le_mul_of_nonneg_left (antitoneOn_W_right hx hy hxy) hκ
    · exact Or.inl fun x hx y hy hxy =>
        mul_le_mul_of_nonpos_left (antitoneOn_W_right hx hy hxy) hκ.le
  have hsplit : {θ : ℝ | θ ∈ Ico (0 : ℝ) 1 ∧ κ * W θ ∈ B}
      = (Icc (0 : ℝ) (1 / 2) ∩ (fun θ => κ * W θ) ⁻¹' B)
        ∪ (Ico (1 / 2 : ℝ) 1 ∩ (fun θ => κ * W θ) ⁻¹' B) := by
    ext θ
    simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_preimage, mem_Ico, mem_Icc]
    constructor
    · rintro ⟨⟨h0, h1⟩, hBθ⟩
      rcases le_or_gt θ (1 / 2) with h | h
      · exact Or.inl ⟨⟨h0, h⟩, hBθ⟩
      · exact Or.inr ⟨⟨h.le, h1⟩, hBθ⟩
    · rintro (⟨⟨h0, h1⟩, hBθ⟩ | ⟨⟨h0, h1⟩, hBθ⟩)
      · exact ⟨⟨h0, by linarith⟩, hBθ⟩
      · exact ⟨⟨by linarith, h1⟩, hBθ⟩
  rw [hsplit, two_mul]
  exact (hB.inter_preimage ordConnected_Icc hmono).union
    (hB.inter_preimage ordConnected_Ico hanti)

/-- The form the mark event is actually written in: the section of
`{α : σ·a·W(θ)/L ∈ B}` at fixed digit `a`, sign `σ` and scale `L`. -/
theorem markSection_signed_isUnionOfIntervals {m : ℕ} {B : Set ℝ}
    (hB : IsUnionOfIntervals m B) (σ : ℝ) (a : ℕ) (L : ℝ) :
    IsUnionOfIntervals (2 * m)
      {θ : ℝ | θ ∈ Ico (0 : ℝ) 1 ∧ σ * (a : ℝ) * W θ / L ∈ B} := by
  have hval : ∀ θ : ℝ, σ * (a : ℝ) * W θ / L = (σ * (a : ℝ) / L) * W θ := fun θ => by ring
  simp only [hval]
  exact markSection_isUnionOfIntervals hB _

end IntervalClass

end Kwon1002
