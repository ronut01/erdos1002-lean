import Kwon1002.ZeroMode
import Kwon1002.P42Cases

/-!
# RetainedCut: display (20) ⇒ the retained-cylinder cut, machine-checked

Stage B of the §4 push built the nonzero-mode cylinder bookkeeping of
`Kwon1002/ZeroMode.lean` §9 and left step 1 of the three-step chain in
*conditional* form: `ZeroMode.nonzero_mode_cut_of_retained` takes an
arbitrary finite family `W` of positive depth-`d` words together with an
explicit bound `η` on the discarded mass, and its docstring records that
"display (20) is exactly what supplies a `W` … with `η = O(e^{-c√L})`".

This file closes that conversion.  `nonzero_mode_cut_of_display20` proves,
**conditionally on an instance of `P42Cases.Display20`** (the predicate
recording display (20), of which no proved instance exists anywhere in the
tree — see `Kwon1002/P42Cases.lean` §4), that at every depth
`d ≤ 2 m_n` there is a finite family `W` of positive depth-`d` words such
that

* every irrational point of every retained cylinder satisfies the two-sided
  Lévy window `e^{λd−δH} ≤ q_d ≤ e^{λd+δH}` (the frozen-continuant form in
  which (28)/(29) consume display (20)),
* the discarded mass is at most `C₀ e^{-c₀ √L}`, and
* consequently, for every symbol family of `(24)` and every nonzero mode,
  `modeTerm` differs from its retained-cylinder truncation by at most
  `(L^D)^r · C₀ e^{-c₀ √L}` — step 1 of `ZeroMode.nonzero_mode_three_step`,
  with the constant `C = 1` of the retained-cut lemma.

The construction: the retained words are the depth-`d` digit words with all
entries in `[1, ⌊e^{λd+δH}⌋]` whose *frozen* continuant `q_d` (the word
continuant `wordDenom`, proved equal to `denom · d` on the cylinder) lies in
the Lévy window.  A good irrational `α` lies in the cylinder of its own digit
word, and the window bound at `α` forces every digit below `q_d ≤ e^{λd+δH}`,
so the retained cylinders cover everything but the display-(20) bad set and a
Lebesgue-null set of rationals.

## What this does and does not close

It does **not** discharge `nonzero_mode_three_step`: step 2 (the
Lebesgue-conditional stationary-mean replacement) and the two inequalities
of (29) remain open even conditionally, as recorded in the obstruction note
there.  What it closes is the sole remaining gap of *step 1*: the passage
from the α-set form of display (20) to the word-family form the cylinder cut
consumes was previously prose, and is now a theorem.

## Sorried results consumed

**None.**  Everything in this file is proved outright; `Display20` enters
only as an explicit hypothesis (the established conditional pattern, compare
`Kwon1002.Lemma63.lemma_6_3_good_cylinder_selection_corrected`).
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace RetainedCut

open Prop41 ErrorShape ZeroMode

noncomputable section

/-! ## 1. The continuant of a digit word -/

/-- One step of the continuant recursion, on the state `(q_k, q_{k-1})`. -/
def denomStep (p : ℕ × ℕ) (a : ℕ) : ℕ × ℕ := (a * p.1 + p.2, p.1)

/-- The pair `(q_d, q_{d-1})` of a digit word, read left to right, from the
seed `(q_0, q_{-1}) = (1, 0)`. -/
def wordDenomPair (w : List ℕ) : ℕ × ℕ := w.foldl denomStep (1, 0)

/-- The terminal continuant denominator `q_{|w|}` of a digit word. -/
def wordDenom (w : List ℕ) : ℕ := (wordDenomPair w).1

/-- The word of the first `d` digits of `α`. -/
def digitWordOf (α : ℝ) (d : ℕ) : List ℕ := List.ofFn (fun i : Fin d => digit α i)

@[simp] lemma digitWordOf_length (α : ℝ) (d : ℕ) : (digitWordOf α d).length = d := by
  simp [digitWordOf]

lemma digitWordOf_getElem (α : ℝ) (d : ℕ) (i : ℕ) (h : i < (digitWordOf α d).length) :
    (digitWordOf α d)[i] = digit α i := by
  simp [digitWordOf]

/-- The word continuant along the digit word is the continuant: the fold
carries exactly the recursion `q_{k+1} = a_k q_k + q_{k-1}` of `denom`. -/
lemma wordDenomPair_digitWordOf (α : ℝ) :
    ∀ d : ℕ, wordDenomPair (digitWordOf α d) = (denom α d, cfDenPrev α d)
  | 0 => rfl
  | (d + 1) => by
      have hsplit : digitWordOf α (d + 1) = digitWordOf α d ++ [digit α d] := by
        rw [digitWordOf, List.ofFn_succ', List.concat_eq_append]
        simp [digitWordOf]
      rw [wordDenomPair, hsplit, List.foldl_append]
      have hIH : (digitWordOf α d).foldl denomStep (1, 0) = (denom α d, cfDenPrev α d) :=
        wordDenomPair_digitWordOf α d
      rw [hIH]
      simp only [List.foldl_cons, List.foldl_nil, denomStep]
      rw [cfDen_succ α d]
      rfl

lemma wordDenom_digitWordOf (α : ℝ) (d : ℕ) :
    wordDenom (digitWordOf α d) = denom α d := by
  rw [wordDenom, wordDenomPair_digitWordOf]

/-- A word read off digit by digit *is* the digit word, so its word
continuant is the continuant of the point. -/
lemma eq_digitWordOf_of_digits {α : ℝ} {w : List ℕ} {d : ℕ} (hlen : w.length = d)
    (hdig : ∀ i (h : i < w.length), digit α i = w[i]'h) :
    w = digitWordOf α d := by
  apply List.ext_getElem
  · rw [hlen, digitWordOf_length]
  · intro i h1 h2
    rw [digitWordOf_getElem]
    exact (hdig i h1).symm

/-- Every digit read below depth `d` is at most the depth-`d` continuant. -/
lemma digit_le_denom {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    {i d : ℕ} (h : i < d) : digit α i ≤ denom α d := by
  have h1 : digit α i ≤ digit α i * denom α i :=
    Nat.le_mul_of_pos_right _ (denom_pos hα hirr i)
  have h2 : digit α i * denom α i ≤ denom α (i + 1) := by
    rw [cfDen_succ]
    exact Nat.le_add_right _ _
  exact le_trans (le_trans h1 h2) (Prop42.denom_mono hα hirr h)

/-- An irrational point of `(0,1)` lies in the cylinder of its own digit
word. -/
lemma mem_cylinder_digitWordOf {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (d : ℕ) :
    α ∈ Erdos1002.gaussHalfOpenPrefixCylinder (digitWordOf α d) := by
  have horb : ∀ k : ℕ, Erdos1002.gaussOrbit k α ∈ Ioo (0 : ℝ) 1 := by
    intro k
    rw [← MixingBV.gaussIter_eq_gaussOrbit]
    exact gaussIter_mem_Ioo hα hirr k
  refine (MixingBV.mem_halfOpen_iff (digitWordOf α d) α horb).2 ?_
  intro i h
  rw [digitWordOf_getElem, ← MixingBV.digit_eq_gaussDigitAt]

/-! ## 2. Display (20) ⇒ the retained word family, and the cut -/

/-- **Display (20), converted into the currency the cylinder cut consumes,
and the cut itself.**  Conditionally on an instance of
`P42Cases.Display20 C₀ δ c₀` — of which the tree contains none — every depth
`d ≤ 2 m_n` carries a finite family `W` of positive depth-`d` words such
that: (i) on every retained cylinder the frozen continuant `q_d` obeys the
two-sided Lévy window of (20); (ii) the discarded mass is at most
`C₀ e^{-c₀ √L}`; and (iii) for every symbol family of `(24)` and every mode
with top nonzero index `s`, `modeTerm` differs from its retained-cylinder
truncation by at most `(L^D)^r · C₀ e^{-c₀ √L}` — step 1 of
`ZeroMode.nonzero_mode_three_step`, via
`ZeroMode.nonzero_mode_cut_of_retained`.

The retained words are the depth-`d` digit words with entries in
`[1, ⌊e^{λd+δH}⌋]` whose word continuant lies in the window; the cover
argument is that a good irrational point lies in the cylinder of its own
digit word, every digit of which is bounded by `q_d ≤ e^{λd+δH}`. -/
theorem nonzero_mode_cut_of_display20 (C₀ δ c₀ : ℝ)
    (h20 : P42Cases.Display20 C₀ δ c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ 2 * mIndex n →
      ∃ W : Finset (List ℕ),
        (∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) ∧
        (∀ w ∈ W, ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α →
          Real.exp (lyapunov * (d : ℝ) - δ * Hscale n) ≤ (denom α d : ℝ) ∧
            (denom α d : ℝ) ≤ Real.exp (lyapunov * (d : ℝ) + δ * Hscale n)) ∧
        (volume (Ioo (0 : ℝ) 1 \
            ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
          ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) ∧
        ∀ (r : ℕ) (D : ℝ) (j : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ),
          RepresentsPD r D (Lnorm n) F c →
          ∀ (v : Fin r → ℤ) (s : ℕ), s < r → (∀ ℓ : Fin r, s < (ℓ : ℕ) → v ℓ = 0) →
            ‖modeTerm n r j c v
                - ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
                    (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
                      torusChar ((n : ℝ) *
                        ((Prop41Canon.freqQ α j (modeExt r v) s : ℤ) : ℝ) * α)‖
              ≤ ((Lnorm n) ^ D) ^ r
                  * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
  classical
  filter_upwards [h20] with n h20n
  intro d hd0 hdm
  have hBadBound := h20n d hdm
  -- the digit cap and the retained word family
  set M : ℕ := ⌊Real.exp (lyapunov * (d : ℝ) + δ * Hscale n)⌋₊ with hM
  set W : Finset (List ℕ) :=
    ((Fintype.piFinset (fun _ : Fin d => Finset.Icc 1 M)).image
        (fun f => List.ofFn f)).filter
      (fun w => Real.exp (lyapunov * (d : ℝ) - δ * Hscale n) ≤ (wordDenom w : ℝ)
        ∧ (wordDenom w : ℝ) ≤ Real.exp (lyapunov * (d : ℝ) + δ * Hscale n)) with hWdef
  -- shape of the retained words
  have hWshape : ∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a := by
    intro w hw
    obtain ⟨hwi, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hwi
    rw [Fintype.mem_piFinset] at hf
    refine ⟨by simp, ?_⟩
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    have := (Finset.mem_Icc.mp (hf i)).1
    omega
  -- the frozen continuant of a retained cylinder obeys the window
  have hWwin : ∀ w ∈ W, ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α →
      Real.exp (lyapunov * (d : ℝ) - δ * Hscale n) ≤ (denom α d : ℝ) ∧
        (denom α d : ℝ) ≤ Real.exp (lyapunov * (d : ℝ) + δ * Hscale n) := by
    intro w hw α hα hirr
    obtain ⟨hlen, hpos⟩ := hWshape w hw
    have hwne : w ≠ [] := by
      intro hnil
      rw [hnil] at hlen
      simp at hlen
      omega
    have hαIoo : α ∈ Ioo (0 : ℝ) 1 := mem_Ioo_of_mem_halfOpen hwne hpos hα hirr
    have hdig := digit_eq_of_mem_halfOpen hαIoo hirr hα
    have hword : w = digitWordOf α d := eq_digitWordOf_of_digits hlen hdig
    have hden : denom α d = wordDenom w := by
      rw [hword, wordDenom_digitWordOf]
    rw [hden]
    exact (Finset.mem_filter.mp hw).2
  -- the cover: a good irrational point lies in a retained cylinder
  have hcover : ∀ α ∈ Ioo (0 : ℝ) 1, Irrational α →
      (Real.exp (lyapunov * (d : ℝ) - δ * Hscale n) ≤ (denom α d : ℝ) ∧
        (denom α d : ℝ) ≤ Real.exp (lyapunov * (d : ℝ) + δ * Hscale n)) →
      α ∈ ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w := by
    intro α hα hirr hwin
    have hdigM : ∀ i : Fin d, digit α i ∈ Finset.Icc 1 M := by
      intro i
      rw [Finset.mem_Icc]
      refine ⟨one_le_digit hα hirr i, ?_⟩
      have h1 : digit α i ≤ denom α d := digit_le_denom hα hirr i.isLt
      have h2 : denom α d ≤ M := Nat.le_floor hwin.2
      omega
    have hmem : digitWordOf α d ∈ W := by
      rw [hWdef, Finset.mem_filter]
      constructor
      · rw [Finset.mem_image]
        refine ⟨fun i => digit α i, ?_, rfl⟩
        rw [Fintype.mem_piFinset]
        exact hdigM
      · rw [wordDenom_digitWordOf]
        exact hwin
    exact Set.mem_biUnion hmem (mem_cylinder_digitWordOf hα hirr d)
  -- the discarded mass is the display-(20) bad mass, up to a null set
  have hnull : volume {α : ℝ | ¬ Irrational α} = 0 := by
    have hset : {α : ℝ | ¬ Irrational α} = Set.range ((↑) : ℚ → ℝ) := by
      ext x
      simp [Irrational]
    rw [hset]
    exact (Set.countable_range _).measure_zero volume
  have hmass : (volume (Ioo (0 : ℝ) 1 \
      ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
      ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := by
    set Bad : Set ℝ := {α ∈ Ioo (0 : ℝ) 1 |
        ¬ (Real.exp (lyapunov * (d : ℝ) - δ * Hscale n) ≤ (denom α d : ℝ)
            ∧ (denom α d : ℝ) ≤ Real.exp (lyapunov * (d : ℝ) + δ * Hscale n))}
      with hBadDef
    have hsub : Ioo (0 : ℝ) 1 \ (⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)
        ⊆ Bad ∪ {α : ℝ | ¬ Irrational α} := by
      rintro α ⟨hα, hnu⟩
      by_cases hirr : Irrational α
      · left
        refine ⟨hα, fun hwin => ?_⟩
        exact hnu (hcover α hα hirr hwin)
      · right
        exact hirr
    have hle : volume (Ioo (0 : ℝ) 1 \
        ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w) ≤ volume Bad := by
      calc volume (Ioo (0 : ℝ) 1 \ ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)
          ≤ volume (Bad ∪ {α : ℝ | ¬ Irrational α}) := measure_mono hsub
        _ ≤ volume Bad + volume {α : ℝ | ¬ Irrational α} := measure_union_le _ _
        _ = volume Bad := by rw [hnull, add_zero]
    have hfin : volume Bad ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
      rw [Real.volume_Ioo]
      simp
    refine le_trans (ENNReal.toReal_mono hfin hle) ?_
    simpa [Measure.real, hBadDef] using hBadBound
  -- assemble, and apply the retained cut
  refine ⟨W, hWshape, hWwin, hmass, ?_⟩
  intro r D j F c hc v s hs htop
  exact nonzero_mode_cut_of_retained n r D j F c hc v s hs htop W d hd0 hWshape
    (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) hmass

end

end RetainedCut

end Kwon1002
