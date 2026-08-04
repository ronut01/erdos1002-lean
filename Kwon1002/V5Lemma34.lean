import Kwon1002.Display22
import Kwon1002.CylinderPhase

/-!
# Reconciliation of Lemma 3.4 with manuscript version 5

Version 5, lines 447 to 484, states the descendant-cylinder estimate as

> **Lemma (Descendant-cylinder estimate).**  Let `{I_w}` be cylinders of a
> fixed depth `d`.  On `I_w` let `Q_w ∈ ℤ \ {0}` be fixed.  Let `k > d` and
> let `A` be constant on every depth-`k` cylinder, with `|A| ≤ 1`.  Suppose
> that, below `I_w`, the support of `A` is a union of depth-`k` descendants
> satisfying `q_k ≤ R_w`, where `R_w² ≤ ε n |Q_w|`.  Then
>
> `(22)   |∑_w ∫_{I_w} e^{2πi n Q_w α} A(α) dα| ≤ C ε.`
>
> Conversely, let `Q ∈ ℤ \ {0}`.  If a depth-`k` cylinder `J` satisfies
> `q_k² ≥ ε⁻¹ n |Q|`, then
>
> `(23)   sup_{α, α' ∈ J} |n Q (α - α')| ≤ C ε.`

Three things changed relative to the draft, and none of them requires new
mathematics here.

## (a) Display (22): the version 5 statement is weaker than ours

Version 5 line 456 to 460 puts the absolute value **outside** the sum over
`w`.  Our `Kwon1002.descendant_cylinder_estimate` (Display22.lean) bounds
`∑_w ‖∫_{I_w} …‖`, the absolute value **inside**, with the explicit constant
`C = 14`.  By the triangle inequality ours implies the version 5 form, and
not conversely, so ours is strictly stronger and is kept unchanged.  The
version 5 display is recorded below as `lem_3_4_descendant_v5`, deduced from
ours in one line, so that a reader matching the paper against the Lean finds
the paper's own statement present verbatim.

The docstring of `Display22.lean` quotes the lemma in the sum-of-absolute-
values form; that quotation is the one place where the file no longer matches
the printed text.  The Lean statement itself needs no change, only that
docstring quotation, which lives in a shared module and is left alone here.

## (b) Display (23): the new hypothesis `Q ≠ 0` is not needed

Version 5 line 461 adds `Q ∈ ℤ \ {0}` to the converse clause.  Our
`Kwon1002.descendant_phase_small` (CylinderPhase.lean) proves the bound for
**every** integer `Q`, with no nonvanishing hypothesis, and the proof never
uses one: for `Q = 0` the left side is `0`.  Ours is therefore again stronger
and is kept unchanged.  The version 5 clause, with `Q ≠ 0` present as a
hypothesis, is recorded as `lem_3_4_phase_freeze_v5` and
`lem_3_4_phase_freeze_v5_sSup`; the hypothesis is discharged by being
ignored.

The version 5 phrasing also states the conclusion as a supremum over a
depth-`k` cylinder `J`, where the draft compared two points.  These are the
same statement: `cylinderV5 k a` below is the depth-`k` cylinder with digits
`a 0, …, a (k-1)`, membership in it is exactly the digit agreement hypothesis
of `descendant_phase_small`, and `denom_eq_of_mem_cylinderV5` shows that the
`q_k` appearing in the hypothesis is an attribute of `J` and not of a chosen
point of it.  Both the pointwise and the literal `sSup` form are given.

## (c) The renaming `(ℓ, ℓ')` and `(q, q_-)` is notational only

Version 5 line 470 to 473 renames the continuation denominators to `(ℓ, ℓ')`
and the prefix denominators to `(q, q_-)`, and writes the descendant
denominator identity as `q_k = q(w) ℓ + q_-(w) ℓ'`.  That identity is already
what `Kwon1002.quad_append` plus `Kwon1002.cfTerminal_eq_quad` prove; it is
restated in the version 5 letters as `cfTerminalDenominator_append_v5` below.
The consequence actually used, `q_k ≥ q(w) ℓ`, is
`Kwon1002.tden_mul_le_tden_append`, unchanged.  One caveat on the paper's
wording: `ℓ'` is the continuation's numerator continuant `p(v)`, not a
denominator; it is the denominator of the reversed continuation, by the
continuant symmetry used in Lemma 3.3.  No hypothesis changes.

## Summary

Nothing in Lemma 3.4 needs reproving.  Both halves as formalised are at least
as strong as version 5, and the version 5 statements are derived here from
them.
-/

open Set MeasureTheory

namespace Kwon1002

namespace V5Lem34

noncomputable section

/-! ## (c) The continuation denominator identity in the version 5 letters -/

/-- **Version 5, line 470 to 473.**  With `q = q(w)` and `q_- = q_-(w)` the
last two denominators of the prefix `w`, and `(ℓ, ℓ')` the continuant pair of
the continuation `v`, the final denominator is `q_k = q ℓ + q_- ℓ'`.

Here `qD w = q(w)`, `qC w = q_-(w)`, `ℓ = cfTerminalDenominator v` and
`ℓ' = cfTerminalNumerator v`.  This is `quad_append` read through
`cfTerminal_eq_quad`; the inequality `q_k ≥ q ℓ` extracted from it is
`tden_mul_le_tden_append`. -/
theorem cfTerminalDenominator_append_v5 (w v : List ℕ) :
    (Erdos1002.cfTerminalDenominator (w ++ v) : ℤ)
      = qD w * (Erdos1002.cfTerminalDenominator v : ℤ)
        + qC w * (Erdos1002.cfTerminalNumerator v : ℤ) := by
  rw [(cfTerminal_eq_quad (w ++ v)).2, (quad_append w v).2.2.2,
    (cfTerminal_eq_quad v).1, (cfTerminal_eq_quad v).2]
  ring

/-! ## (a) Display (22) in the version 5 form -/

/-- **Version 5 display (22), lines 456 to 460.**

The absolute value is outside the sum over `w`.  This follows from
`Kwon1002.descendant_cylinder_estimate`, which bounds the sum of the absolute
values, by the triangle inequality, with the same constant `C = 14`.  The
project keeps the stronger form. -/
theorem lem_3_4_descendant_v5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n d k : ℕ), 0 < n → d < k →
      ∀ (W : Finset (List ℕ)) (Q : List ℕ → ℤ) (R : List ℕ → ℝ)
        (S : List ℕ → Finset (List ℕ)) (A : ℝ → ℂ),
        -- `{I_w}` are cylinders of a fixed depth `d`
        (∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) →
        -- on `I_w`, `Q_w ∈ ℤ \ {0}` is fixed
        (∀ w ∈ W, Q w ≠ 0) →
        -- `R_w² ≤ ε n |Q_w|`
        (∀ w ∈ W, (R w) ^ 2 ≤ ε * (n : ℝ) * |(Q w : ℝ)|) →
        -- `|A| ≤ 1`
        (∀ α, ‖A α‖ ≤ 1) →
        -- `A` is constant on every depth-`k` cylinder
        (∀ u : List ℕ, u.length = k → (∀ a ∈ u, 0 < a) →
          ∀ α ∈ Erdos1002.closedGaussPrefixCylinder u,
            ∀ β ∈ Erdos1002.closedGaussPrefixCylinder u, A α = A β) →
        -- the measurability the manuscript makes explicit
        Measurable A →
        -- below `I_w` the support of `A` is a union of depth-`k` descendants
        (∀ w ∈ W, ∀ v ∈ S w, v.length = k - d ∧ (∀ a ∈ v, 0 < a)) →
        (∀ w ∈ W, ∀ α ∈ Erdos1002.closedGaussPrefixCylinder w, A α ≠ 0 →
          ∃ v ∈ S w, α ∈ Erdos1002.closedGaussPrefixCylinder (w ++ v)) →
        -- those descendants satisfy `q_k ≤ R_w`
        (∀ w ∈ W, ∀ v ∈ S w,
          (Erdos1002.cfTerminalDenominator (w ++ v) : ℝ) ≤ R w) →
        ‖∑ w ∈ W, ∫ α in Erdos1002.closedGaussPrefixCylinder w,
            Erdos1002.oscillatoryPhase ((n : ℝ) * (Q w : ℝ)) α * A α‖ ≤ C * ε := by
  obtain ⟨C, hC, hstrong⟩ := descendant_cylinder_estimate
  refine ⟨C, hC, ?_⟩
  intro ε hε n d k hn hdk W Q R S A hW hQ hR hAbd hAconst hAmeas hSlen hAsupp hSden
  exact (norm_sum_le _ _).trans
    (hstrong ε hε n d k hn hdk W Q R S A hW hQ hR hAbd hAconst hAmeas hSlen hAsupp hSden)

/-! ## (b) Display (23) in the version 5 form -/

/-- The depth-`k` cylinder `J` of irrationals of `(0,1)` whose first `k`
continued-fraction digits are `a 0, …, a (k-1)`. -/
def cylinderV5 (k : ℕ) (a : ℕ → ℕ) : Set ℝ :=
  {α | α ∈ Ioo (0 : ℝ) 1 ∧ Irrational α ∧ ∀ i < k, digit α i = a i}

/-- `q_k` is an attribute of the cylinder: it takes the same value at every
point of `cylinderV5 k a`. -/
theorem denom_eq_of_mem_cylinderV5 {k : ℕ} {a : ℕ → ℕ} {α α' : ℝ}
    (hα : α ∈ cylinderV5 k a) (hα' : α' ∈ cylinderV5 k a) :
    denom α k = denom α' k :=
  (cf_congr α α' k fun i hi => (hα.2.2 i hi).trans (hα'.2.2 i hi).symm).1

/-- **Version 5 display (23), lines 461 to 466, pointwise form.**

`Q ∈ ℤ \ {0}` is carried as a hypothesis to match the printed statement.  It
is not used: `Kwon1002.descendant_phase_small` proves the bound for every
integer `Q`, so the project keeps that stronger form.  The hypothesis
`hq` says that the cylinder `J = cylinderV5 k a` has denominator `q`, and
`hqbd` is `q_k² ≥ ε⁻¹ n |Q|`. -/
theorem lem_3_4_phase_freeze_v5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (Q : ℤ), Q ≠ 0 →
      ∀ (k q : ℕ) (a : ℕ → ℕ),
        (∀ α ∈ cylinderV5 k a, denom α k = q) →
        ε⁻¹ * (n : ℝ) * |(Q : ℝ)| ≤ (q : ℝ) ^ 2 →
        ∀ α ∈ cylinderV5 k a, ∀ α' ∈ cylinderV5 k a,
          |(n : ℝ) * (Q : ℝ) * (α - α')| ≤ C * ε := by
  obtain ⟨C, hC, hstrong⟩ := descendant_phase_small
  refine ⟨C, hC, ?_⟩
  intro ε hε n Q _ k q a hq hqbd α hα α' hα'
  refine hstrong ε hε n Q k α α' hα.1 hα'.1 hα.2.1 hα'.2.1
    (fun i hi => (hα.2.2 i hi).trans (hα'.2.2 i hi).symm) ?_
  rw [hq α hα]
  exact hqbd

/-- **Version 5 display (23), lines 461 to 466, literal supremum form.**

The supremum is over the set of values `|n Q (α - α')|` with `α, α'` in the
depth-`k` cylinder `J`.  If that set happens to be empty the real supremum is
`0`, which also satisfies the bound, so no nonemptiness hypothesis is
needed. -/
theorem lem_3_4_phase_freeze_v5_sSup :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (Q : ℤ), Q ≠ 0 →
      ∀ (k q : ℕ) (a : ℕ → ℕ),
        (∀ α ∈ cylinderV5 k a, denom α k = q) →
        ε⁻¹ * (n : ℝ) * |(Q : ℝ)| ≤ (q : ℝ) ^ 2 →
        sSup {t : ℝ | ∃ α ∈ cylinderV5 k a, ∃ α' ∈ cylinderV5 k a,
                t = |(n : ℝ) * (Q : ℝ) * (α - α')|} ≤ C * ε := by
  obtain ⟨C, hC, hpt⟩ := lem_3_4_phase_freeze_v5
  refine ⟨C, hC, ?_⟩
  intro ε hε n Q hQ k q a hq hqbd
  refine Real.sSup_le ?_ (by positivity)
  rintro t ⟨α, hα, α', hα', rfl⟩
  exact hpt ε hε n Q hQ k q a hq hqbd α hα α' hα'

end

end V5Lem34

end Kwon1002
