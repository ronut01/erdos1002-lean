import Kwon1002.CorFinal
import Kwon1002.CovarianceChain
import Kwon1002.Master
import Kwon1002.Section7Bridge
import Kwon1002.OneLevelLaw
import Kwon1002.Prop42Unconditional
import Kwon1002.LDMain
import Kwon1002.Fejer
import Kwon1002.JacksonGate

/-!
# The §4/§5 join

This module exists to put the modules that *declare* the §5 residuals and the
modules that *prove* §4 under one roof.  It compiles, so the join is
cycle-free; the `example`s in Part A witness that both families are visible
here at once.

## The structural record, corrected

`Kwon1002/CorFinal.lean`'s header states that the two module families are
"incomparable, not ordered", on the strength of an import table.  **Half of
that is false, and the false half is the load-bearing half.**  What is true is
the first row of the table: the import closure of every module declaring a §5
residual (`CorFinal`, `FiveFinal`, `TupleFinal`, `CovarianceChain`,
`Assembly5`, `Finale`, `OffDiagonal`, `OffDiagFinal`, `L2Estimate`,
`TupleMeasure`, `LevyExponent`, `SmallJumps`) misses `Prop41Unconditional`,
`Prop42Unconditional`, `LDMain`, `Fejer`, `OneLevelLaw` and `DigitLocalLaw`.
What is false is the converse: `Prop41Unconditional`, `Prop42Unconditional`,
`LDMain`, `OneLevelLaw` and `NonzeroMode` **do** import `FiveFinal` and
`TupleFinal`, and through them `Assembly5`, `OffDiagonal`, `L2Estimate`,
`TupleMeasure`, `LevyExponent` and `SmallJumps`.

So the families are *ordered*, with §4 sitting strictly above most of §5, not
incomparable.  The practical consequence is the one the header drew — the
residuals cannot shed `sorryAx` where they are declared, and a join module is
the vehicle — but the reason is one-directional, and the join is cheaper than
the header supposed: only `CorFinal`, `CovarianceChain` and `JacksonGate` are
not already below `OneLevelLaw`.  `CorFinal` is imported by `Master` and
`Section7Bridge` and by nothing else; `CovarianceChain` and `JacksonGate` are
imported by nothing at all.

**Residual 1 is gone, and it never needed the join.**
`Kwon1002.TupleFinal.bulk_window_bridge_tuple` is now proved outright, in
`Kwon1002/TupleFinal.lean`, from `StoppingWindow` plus two embedding counts.
Its docstring records the proof.  That removes one of the four items the
endgame carried and confirms that "the module direction blocks it" was not the
right diagnosis for that residual.

## What actually remains: one gate, not three

The three §5 residuals still open —

* `Kwon1002.TupleFinal.goodSet_mark_factorization_intervals` (residual 2a,
  Proposition 4.1 for the mark event at the interval class),
* `Kwon1002.TupleInputs.oneLevel_gaussKuzmin_intensity` (display (35) per
  level; note `Kwon1002.deterministic_oneLevel_intensity` is *already proved*
  from it in `Kwon1002/TupleInputs.lean`, so (35) is not a separate item), and
* the band-mass hypothesis of
  `Kwon1002.CovarianceChain.truncatedMark_sub_lipTrunc_L1_of_band`, finding
  (F7), which gates DEBT 2 —

are **the same gate read three times**: the level-`j` joint law of
`(a_{j+1}, θ_j)` under Lebesgue measure on `(0,1)`, evaluated at an
*indicator* whose `θ`-sections are finite unions of intervals.

`Kwon1002.OneLevelLaw.oneLevel_joint_law` proves exactly that law for symbols
in the class `IsInPD D L` of display (24), unconditionally.  What it does not
cover is indicators: membership of `IsInPD` forces continuity
(`JacksonGate.continuous_of_isInPD`), so a two-valued member is constant
(`JacksonGate.isInPD_const_of_two_valued`).  Part B below shows the two halves
compose — `Fejer.isInPD_fejerPoly` lands inside the class and
`oneLevel_joint_law` then applies to it — so the gate is precisely the passage
from the Fejér approximant back to the indicator.

**That passage is not bookkeeping, and the record should not say it is.**
`CorFinal`'s header lists the Jackson instantiation as needing only "the
`k`-level bookkeeping".  The missing step is one-sidedness.
`Fejer.fejerPoly_L1_error_le` measures `‖σ_N f − f‖` in `L¹` *of the
`θ`-variable under Lebesgue on the cell*, whereas what the argument has to
control is the error under the law of `(a_{j+1}(α), θ_j(α))` induced by
Lebesgue in `α` — which is the very object being computed.  Closing that loop
needs approximants that bracket the indicator from **both sides**, so that the
error never has to be measured against the unknown law: a trapezoidal
majorant/minorant pair, or Beurling–Selberg polynomials.  Fejér means are not
one-sided and the tree contains no such pair.  That, and not the `k`-level
bookkeeping, is the one genuinely open analytic step of §5.

## Finding (F7) is refuted, conditionally on that gate

`Kwon1002/CovarianceChain.lean` records finding (F7): the band-mass estimate
is "not derivable from the display-(15) tails", on the grounds that a law
satisfying every tail bound of display (15) could park its whole allowed mass
`≍ C/(1+εL)` immediately below the cutoff, leaving the band `L¹` cost at a
constant.  `Kwon1002/CorFinal.lean` promotes this to "the one input the tree
does not contain in any form".

The reasoning about *tails* is correct; the conclusion is not.  (F7)'s
adversarial law does not exist, because the mark is not an abstract random
variable: it is `a_{j+1}·W(θ_j)` with `W` a fixed sawtooth average.  Two
machine-checked facts now bound how much mass a thin band can carry, and
neither was used when (F7) was written:

* `Kwon1002.IntervalClass.volume_markBand_le` (proved, this pass): for **every**
  digit `a` and every cutoff `M > 0`, the `θ`-section of the relative band
  `((1−h)M, M]` of `a·W(θ)` has Lebesgue measure at most `√(h/(1−h))` — with
  no dependence on `a` or `M`.  It comes from
  `IntervalClass.volume_W_gt`, which computes the super-level set of `W` on the
  cell exactly: `vol{θ : u < W θ} = √(1−8u)`.
* `markBand_digit_gt` (Part C below): only digits `a > 8(1−h)εL` can be in the
  band at all, so `Kwon1002.digit_tail_product` caps the digit mass at
  `O(1/((1−h)εL))`.

Against the joint law those multiply to a band mass `O(√h/((1−h)εL))`, so
`εL·m = O(√h) → 0` as `h ↓ 0`, which is exactly the `o(1/(εL))` the interface
`truncatedMark_sub_lipTrunc_L1_of_band` asks for.  Note also that the exact
`a^{-2}` digit law is **not** needed: the display-(15) tail suffices once the
`θ`-geometry is used.  The `DigitLocalLaw` closing note, which attributes the
gain to the exact `a^{-2}` decay, is over-attributing.

So (F7)'s band-mass input is not an independent missing ingredient.  It is the
same gate as residuals 2a and (35), plus two now-proved elementary bounds.
The endgame is one statement, not four.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal Real

namespace Kwon1002

namespace Section5Join

noncomputable section

/-! ## Part A, the join is real

Each of these elaborates only because this module sees both families at once.
`Kwon1002/CorFinal.lean` cannot state the second, and `Kwon1002/OneLevelLaw.lean`
cannot state the first. -/

/-- The §5 endpoint, visible here. -/
example : ∀ (c : ℝ), Master.PrincipalCauchyLaw c := @Kwon1002.CorFinal.principal_cauchy_law_F

/-- The §4 one-level joint law, visible here. -/
example : ∀ D A : ℝ, 0 < D → 0 < A →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ bulkJ n, ∀ G : ℕ → ℝ → ℂ, IsInPD D (Lnorm n) G →
        ‖(∫ α in Ioo (0 : ℝ) 1, G (digit α j) (theta α n j)) - stationaryMean G‖
          ≤ C * (Lnorm n) ^ (-A) := @Kwon1002.OneLevelLaw.oneLevel_joint_law

/-- The §3 band interface, visible here. -/
example : ∀ (ε h m : ℝ), 0 < ε → 0 < h → h < 1 → ∀ n j : ℕ, 0 < Lnorm n →
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        (1 - h) * (ε * Lnorm n) < mark α n j ∧ mark α n j ≤ ε * Lnorm n}).toReal ≤ m →
    (∫ α in Ioo (0 : ℝ) 1,
        |truncatedMark ε α n j
          - CovarianceChain.lipTrunc (ε * Lnorm n) (h * (ε * Lnorm n)) (mark α n j)|)
      ≤ ε * Lnorm n * m :=
  @Kwon1002.CovarianceChain.truncatedMark_sub_lipTrunc_L1_of_band

/-- Residual 1, now proved, visible here. -/
example : ∀ (c : ℝ) (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) → ∀ k : ℕ,
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (LevyExponent.bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              unifIoo.real (Erdos1002.tupleEvent (TupleFinal.detMarkEvent n B) f))
      atTop (𝓝 0) := @Kwon1002.TupleFinal.bulk_window_bridge_tuple

/-! ## Part B, the two halves of the gate compose

`Fejer.isInPD_fejerPoly` produces members of display (24)'s class; §4's
one-level law applies to members of that class.  Neither module can see the
other, so this composition can only be written here.  It is the reason the
join module is the right vehicle: what is left after it is *not* a module
question. -/

/-- **§4's one-level law, read on a Fejér approximant.**  For every level of
the deterministic bulk, the `α`-average of a digit-cut Fejér polynomial in the
phase equals its stationary mean to `O_{D,A}(L^{-A})`, uniformly in the level,
in the digit cut, in the degree and in the symbol.

Proved by composing `Fejer.isInPD_fejerPoly` with
`OneLevelLaw.oneLevel_joint_law`; the three side conditions are exactly the
ones `isInPD_fejerPoly` keeps apart, and the binding one is the budget
`(A+1)(2N+1)M ≤ L^D`, since display (24)'s `ℓ¹` sum runs over the digit as
well as the frequency. -/
theorem oneLevel_fejer_law (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ∀ (Acut N : ℕ) (M : ℝ) (g : ℕ → ℝ → ℂ), (∀ a, Fejer.IsPerBdd (g a) M) →
        (Acut : ℝ) ≤ (Lnorm n) ^ D → (N : ℝ) ≤ (Lnorm n) ^ D →
        ((Acut : ℝ) + 1) * ((2 * (N : ℝ) + 1) * M) ≤ (Lnorm n) ^ D →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              (if digit α j ≤ Acut then Fejer.fejerPoly N (g (digit α j)) (theta α n j) else 0))
            - stationaryMean
                (fun a θ => if a ≤ Acut then Fejer.fejerPoly N (g a) θ else 0)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨C, hC, hev⟩ := OneLevelLaw.oneLevel_joint_law D A hD hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn j hj Acut N M g hg hAle hNle hbudget
  exact hn j hj _ (Fejer.isInPD_fejerPoly D (Lnorm n) Acut N M g hg hAle hNle hbudget)

/-! ## Part C, the two quantitative inputs of the (F7) refutation

The `θ`-half is `IntervalClass.volume_markBand_le`, proved in
`Kwon1002/IntervalClass.lean`.  The digit half is here. -/

/-- **Only large digits reach the band.**  If the mark exceeds `(1−h)εL` then
the digit exceeds `8(1−h)εL`, because `W ≤ 1/8`.  Together with
`Kwon1002.digit_tail_product` this caps the digit mass carried by the band at
`O(1/((1−h)εL))`; together with `IntervalClass.volume_markBand_le`, which caps
the `θ`-section at `√(h/(1−h))` uniformly in the digit, it gives the
`o(1/(εL))` band mass that finding (F7) asserts is unobtainable. -/
theorem markBand_digit_gt {t : ℝ} {α : ℝ} {n j : ℕ} (hmark : t < mark α n j) :
    8 * t < (digit α j : ℝ) := by
  have hW : W (theta α n j) ≤ 1 / 8 := W_le_eighth _
  have hWnn : 0 ≤ W (theta α n j) := W_nonneg _
  have hd : (0 : ℝ) ≤ (digit α j : ℝ) := Nat.cast_nonneg _
  have hbnd : (digit α j : ℝ) * W (theta α n j) ≤ (digit α j : ℝ) * (1 / 8) :=
    mul_le_mul_of_nonneg_left hW hd
  rw [mark] at hmark
  linarith

/-- The `θ`-section bound, restated at the mark's own band so that the two
halves of the (F7) refutation sit side by side.  `√(h/(1−h)) → 0` as `h ↓ 0`,
uniformly in the digit `a` and in the cutoff `M`; that uniformity is the whole
point, and it is what (F7)'s adversarial law would have had to violate. -/
theorem markBand_theta_section_le (a : ℕ) {M h : ℝ} (hM : 0 < M) (hh0 : 0 < h) (hh1 : h < 1) :
    (volume {θ : ℝ | θ ∈ Ico (0 : ℝ) 1 ∧
        (1 - h) * M < (a : ℝ) * W θ ∧ (a : ℝ) * W θ ≤ M}).toReal
      ≤ Real.sqrt (h / (1 - h)) :=
  IntervalClass.volume_markBand_le a hM hh0 hh1

/-- The band bound vanishes as the band narrows: `√(h/(1−h)) → 0` as `h ↓ 0`.
This is the `o(1)` that `truncatedMark_sub_lipTrunc_L1_of_band` converts into
`o(1/(εL))`, and it is uniform in the level, the digit and the cutoff. -/
theorem tendsto_bandBound_zero :
    Tendsto (fun h : ℝ => Real.sqrt (h / (1 - h))) (nhdsWithin 0 (Ioo (0 : ℝ) 1)) (𝓝 0) := by
  have hc : ContinuousAt (fun h : ℝ => Real.sqrt (h / (1 - h))) 0 := by
    refine Real.continuous_sqrt.continuousAt.comp ?_
    exact ContinuousAt.div continuousAt_id (by fun_prop) (by norm_num)
  have h0 : Real.sqrt ((0 : ℝ) / (1 - 0)) = 0 := by norm_num
  have := hc.continuousWithinAt (s := Ioo (0 : ℝ) 1)
  rw [ContinuousWithinAt, h0] at this
  exact this

end

end Section5Join

end Kwon1002
