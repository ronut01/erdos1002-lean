import Kwon1002.CorFinal
import Kwon1002.CovarianceChain
import Kwon1002.Master
import Kwon1002.Section7Bridge
import Kwon1002.OneLevelLaw
import Kwon1002.Prop42Unconditional
import Kwon1002.LDMain
import Kwon1002.Fejer
import Kwon1002.JacksonGate
import Kwon1002.Selberg
import Kwon1002.GaussKuzmin

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
`k`-level bookkeeping".  The missing step was one-sidedness.
`Fejer.fejerPoly_L1_error_le` measures `‖σ_N f − f‖` in `L¹` *of the
`θ`-variable under Lebesgue on the cell*, whereas what the argument has to
control is the error under the law of `(a_{j+1}(α), θ_j(α))` induced by
Lebesgue in `α` — which is the very object being computed.  Closing that loop
needs approximants that bracket the indicator from **both sides**, so that the
error never has to be measured against the unknown law.

**That step is now done, and the record is updated accordingly.**
`Kwon1002/Selberg.lean` builds the trapezoidal (Vaaler-style)
majorant/minorant pair: trigonometric polynomials `S⁻ ≤ 1_B ≤ S⁺` of degree
`N`, one-sided **pointwise on all of `ℝ`**, with `ℓ¹` coefficient mass
`(2N+1)(1+η)` and `L¹` gap `(4m+2)·2δ + 2η(N,δ)` for a union of `m` intervals,
`η(N,δ) = 1/(4(N+1)δ²)`.  Part D below composes it with
`OneLevelLaw.oneLevel_joint_law`: `oneLevel_indicator_sandwich` is §4's
one-level law read **at the indicator itself**, two-sided, and
`stationaryMeanR_gap_le` bounds what the sandwich costs by the jump count
alone.  Both are `#print axioms` clean.

So the sentence "the tree contains no such pair", written before this pass,
is no longer true, and neither is "one genuinely open analytic step".

**The Gauss-Kuzmin normalisation named here is now closed too, and this
paragraph is corrected accordingly.**  It used to read that what remains of
(35) is "the Gauss-Kuzmin *normalisation* — the identification of
`stationaryMeanR` of the mark indicator with `2λ·Λ`".
`Kwon1002/GaussKuzmin.lean` proves that identification outright:
`M·stationaryMeanR(1[M < a·W θ])` is trapped between
`(1/12 − 1/(32M))/log 2` and `(1/12)/log 2` for every `M > 0`, hence
`L·stationaryMeanR → 2λ·Λ((u,∞))` at `M = uL`, with
`Λ((u,∞)) = 1/(2π²u)` machine-checked (`GaussKuzmin.levyIntensity_Ioi`) and
not substituted.  Part E below carries the `rfl` guards.  The route is not the
one this paragraph anticipated: swapping the digit and phase integrals
replaces the infinite digit sum by the *exact* Gauss-Kuzmin tail
`γ{a₁ ≥ K} = log(1+1/K)/log 2` at `K = ⌊M/W θ⌋+1`, and
`x/(1+x) ≤ log(1+x) ≤ x` then pins the answer uniformly in the phase, with
`∫₀¹ W = 1/12` supplying the `1/12`.  No Riemann sum is needed, and
`IntervalClass.volume_W_gt` is not used.

What remained of (35) after Parts D and E was neither the one-sidedness nor the
constant, but (i) the *choice of bracket parameters* `(Acut, N, δ)` against `L`,
together with the two digit tails, and (ii) the passage from the interval class
— where both the bracket and the normalisation live — to the arbitrary
measurable `B` the residual is stated for.

**Part F closes item (i) and settles how much of item (ii) is real.**
`oneLevel_transfer` makes the choice explicit — `δ = L^{-2}`, `N = ⌈L^6⌉`,
`Acut = ⌈L^2⌉`, against display (24)'s `D = 11` and the one-level rate `A = 2`,
with `sched_admissible` discharging the budget — and proves the resulting error
is `o(1/L)` uniformly over the bulk and over the section family.  Item (ii) is
then split off as `TupleInputs.oneLevel_gaussKuzmin_intensity_to_measurable`,
and `oneLevel_gaussKuzmin_intensity_truncation` proves the residual's conclusion
**outright** at `B = {x : ε < |x| ≤ R}`, the only shape `B` takes below
Proposition 5.1.  What is left between that window and the general interval
class is a decomposition of an arbitrary `IsUnionOfIntervals` family into
disjoint bands, and what is left above the interval class is the density bound
`≍ x^{-2}`; see the corrected obstruction records on
`TupleInputs.oneLevel_gaussKuzmin_intensity_intervals` and
`TupleInputs.oneLevel_gaussKuzmin_intensity_to_measurable`.  For residual 2a and
(F7) the `k`-level and pair-level bookkeeping sits on top of the same items.

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

/-! ## Part D, the gate, closed at the indicator

Part B reads §4's one-level law on a Fejér approximant.  That is not enough,
for the reason this file's header records: the Fejér mean approximates in `L¹`
of the phase under **Lebesgue on the cell**, while the residual needs the error
under the law of `(a_{j+1}(α), θ_j(α))`, which is the object being computed.

`Kwon1002/Selberg.lean` removes the circularity by bracketing: it builds
trigonometric polynomials `S⁻ ≤ 1_B ≤ S⁺` of degree `N`, pointwise on all of
`ℝ`, with an `L¹` gap measured against Lebesgue alone.  Composed with
`OneLevelLaw.oneLevel_joint_law`, which applies to each of `S⁺` and `S⁻`
because `Selberg.isInPD_majSymbol` and `Selberg.isInPD_minSymbol` place them in
display (24)'s class, this gives a **two-sided** estimate for the α-average of
the *indicator itself* — the statement the three §5 residuals were reduced to.

The pointwise bracket needs no hypothesis on `B` beyond measurability; the
hypotheses of display (24) are the three budget conditions, exactly the ones
`Fejer.isInPD_fejerPoly` keeps apart.  The size of the gap is what carries the
interval structure, and that is `Selberg.integral_upInd_sub_downInd_le`. -/

/-- The stationary mean of a **real** symbol.  `stationaryMean` of display (27)
is complex, because display (24)'s class is; the bracket is an inequality
between real numbers, so this is the form the sandwich is stated in. -/
def stationaryMeanR (f : ℕ → ℝ → ℝ) : ℝ :=
  ∫ x, (∫ θ in Ioo (0 : ℝ) 1, f (digit x 0) θ) ∂Erdos1002.gaussMeasure

/-- The two agree on a real symbol.  Both steps are `integral_complex_ofReal`,
which needs no integrability hypothesis. -/
theorem stationaryMean_ofReal (f : ℕ → ℝ → ℝ) :
    stationaryMean (fun a θ => ((f a θ : ℝ) : ℂ)) = ((stationaryMeanR f : ℝ) : ℂ) := by
  unfold stationaryMean stationaryMeanR
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [integral_complex_ofReal]

/-- The digit-cut majorant family. -/
def majCut (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) : ℕ → ℝ → ℝ :=
  fun a θ => if a ≤ Acut then
    Selberg.realConv N (Selberg.majSymbol N δ (Selberg.upInd δ (Bs a))) θ else 0

/-- The digit-cut minorant family. -/
def minCut (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) : ℕ → ℝ → ℝ :=
  fun a θ => if a ≤ Acut then
    Selberg.realConv N (Selberg.minSymbol N δ (Selberg.downInd δ (Bs a))) θ else 0

/-- The digit-cut indicator family: the object the residuals need, and the
object display (24)'s class provably excludes. -/
def indCut (Acut : ℕ) (Bs : ℕ → Set ℝ) : ℕ → ℝ → ℝ :=
  fun a θ => if a ≤ Acut then Selberg.perInd (Bs a) θ else 0

theorem minCut_le_indCut {N Acut : ℕ} {δ : ℝ} (hδ : 0 < δ) (Bs : ℕ → Set ℝ) (a : ℕ) (θ : ℝ) :
    minCut N Acut δ Bs a θ ≤ indCut Acut Bs a θ := by
  unfold minCut indCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]
    exact Selberg.realConv_minSymbol_le N hδ (Selberg.isPerBddR_downInd δ (Bs a))
      (Selberg.downInd_le_one δ (Bs a)) (Selberg.perInd_nonneg (Bs a)) θ
      (fun t ht => Selberg.downInd_shift_le_perInd (Bs a) θ ht)
  · simp [hc]

theorem indCut_le_majCut {N Acut : ℕ} {δ : ℝ} (hδ : 0 < δ) (Bs : ℕ → Set ℝ) (a : ℕ) (θ : ℝ) :
    indCut Acut Bs a θ ≤ majCut N Acut δ Bs a θ := by
  unfold indCut majCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]
    exact Selberg.le_realConv_majSymbol N hδ (Selberg.isPerBddR_upInd δ (Bs a))
      (Selberg.upInd_nonneg δ (Bs a)) (Selberg.perInd_nonneg (Bs a))
      (Selberg.perInd_le_one (Bs a)) θ
      (fun t ht => Selberg.perInd_le_upInd_shift (Bs a) θ ht)
  · simp [hc]

/-- The majorant family lies in display (24)'s class. -/
theorem isInPD_majCut (D L : ℝ) (Acut N : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ)
    (hAle : (Acut : ℝ) ≤ L ^ D) (hNle : (N : ℝ) ≤ L ^ D)
    (hbudget : ((Acut : ℝ) + 1) * ((2 * (N : ℝ) + 1) * (1 + Selberg.farTail N δ)) ≤ L ^ D) :
    IsInPD D L (fun a θ => ((majCut N Acut δ Bs a θ : ℝ) : ℂ)) := by
  have hfun : (fun a θ => ((majCut N Acut δ Bs a θ : ℝ) : ℂ))
      = fun a θ => if a ≤ Acut then
          Fejer.fejerPoly N
            (fun x => ((Selberg.majSymbol N δ (Selberg.upInd δ (Bs a)) x : ℝ) : ℂ)) θ else 0 := by
    funext a θ
    unfold majCut
    by_cases hc : a ≤ Acut
    · simp only [if_pos hc]
      rw [Selberg.majSymbol_eq_fejerPoly]
    · simp [hc]
  rw [hfun]
  exact Selberg.isInPD_majSymbol D L Acut N δ 1 (fun a => Selberg.upInd δ (Bs a))
    (fun a => Selberg.isPerBddR_upInd δ (Bs a)) hAle hNle hbudget

/-- The minorant family lies in display (24)'s class. -/
theorem isInPD_minCut (D L : ℝ) (Acut N : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ)
    (hAle : (Acut : ℝ) ≤ L ^ D) (hNle : (N : ℝ) ≤ L ^ D)
    (hbudget : ((Acut : ℝ) + 1) * ((2 * (N : ℝ) + 1) * (1 + Selberg.farTail N δ)) ≤ L ^ D) :
    IsInPD D L (fun a θ => ((minCut N Acut δ Bs a θ : ℝ) : ℂ)) := by
  have hfun : (fun a θ => ((minCut N Acut δ Bs a θ : ℝ) : ℂ))
      = fun a θ => if a ≤ Acut then
          Fejer.fejerPoly N
            (fun x => ((Selberg.minSymbol N δ (Selberg.downInd δ (Bs a)) x : ℝ) : ℂ)) θ else 0 := by
    funext a θ
    unfold minCut
    by_cases hc : a ≤ Acut
    · simp only [if_pos hc]
      rw [Selberg.minSymbol_eq_fejerPoly]
    · simp [hc]
  rw [hfun]
  exact Selberg.isInPD_minSymbol D L Acut N δ 1 (fun a => Selberg.downInd δ (Bs a))
    (fun a => Selberg.isPerBddR_downInd δ (Bs a)) hAle hNle hbudget

/-! ### Measurability and integrability of the three families -/

lemma measurable_majCut (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) (a : ℕ) :
    Measurable (majCut N Acut δ Bs a) := by
  unfold majCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]
    exact (Selberg.continuous_realConv
      (Selberg.isPerBddR_majSymbol (Selberg.isPerBddR_upInd δ (Bs a)) N δ) N).measurable
  · simp only [if_neg hc]
    exact measurable_const

lemma measurable_minCut (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) (a : ℕ) :
    Measurable (minCut N Acut δ Bs a) := by
  unfold minCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]
    exact (Selberg.continuous_realConv
      (Selberg.isPerBddR_minSymbol (Selberg.isPerBddR_downInd δ (Bs a)) N δ) N).measurable
  · simp only [if_neg hc]
    exact measurable_const

lemma measurable_indCut (Acut : ℕ) {Bs : ℕ → Set ℝ} (hBs : ∀ a, MeasurableSet (Bs a)) (a : ℕ) :
    Measurable (indCut Acut Bs a) := by
  unfold indCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]; exact Selberg.measurable_perInd (hBs a)
  · simp only [if_neg hc]; exact measurable_const

lemma abs_majCut_le (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) (a : ℕ) (θ : ℝ) :
    |majCut N Acut δ Bs a θ| ≤ 1 + Selberg.farTail N δ := by
  unfold majCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]
    exact Selberg.abs_realConv_le
      (Selberg.isPerBddR_majSymbol (Selberg.isPerBddR_upInd δ (Bs a)) N δ) N θ
  · simp only [if_neg hc, abs_zero]
    have := Selberg.farTail_nonneg N δ
    linarith

lemma abs_minCut_le (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) (a : ℕ) (θ : ℝ) :
    |minCut N Acut δ Bs a θ| ≤ 1 + Selberg.farTail N δ := by
  unfold minCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]
    exact Selberg.abs_realConv_le
      (Selberg.isPerBddR_minSymbol (Selberg.isPerBddR_downInd δ (Bs a)) N δ) N θ
  · simp only [if_neg hc, abs_zero]
    have := Selberg.farTail_nonneg N δ
    linarith

lemma abs_indCut_le (Acut : ℕ) (Bs : ℕ → Set ℝ) (a : ℕ) (θ : ℝ) :
    |indCut Acut Bs a θ| ≤ 1 := by
  unfold indCut
  by_cases hc : a ≤ Acut
  · simp only [if_pos hc]
    rw [abs_of_nonneg (Selberg.perInd_nonneg (Bs a) θ)]
    exact Selberg.perInd_le_one (Bs a) θ
  · simp [hc]

/-- Composing a digit-indexed symbol with `(a_{j+1}, θ_j)` is measurable: the
digit takes countably many values, so `measurable_from_prod_countable_right`
applies to the pair `(digit ·, theta ·)`, which is measurable by
`Kwon1002.measurable_digit` and `Kwon1002.measurable_theta`. -/
lemma measurable_symbol_comp {f : ℕ → ℝ → ℝ} (hf : ∀ a, Measurable (f a)) (n j : ℕ) :
    Measurable fun α : ℝ => f (digit α j) (theta α n j) := by
  have hpair : Measurable fun α : ℝ => (digit α j, theta α n j) :=
    (measurable_digit j).prodMk (measurable_theta n j)
  exact (measurable_from_prod_countable_right (f := fun p : ℕ × ℝ => f p.1 p.2)
    (fun a => hf a)).comp hpair

lemma integrableOn_symbol_comp {f : ℕ → ℝ → ℝ} (hf : ∀ a, Measurable (f a)) {M : ℝ}
    (hb : ∀ a θ, |f a θ| ≤ M) (n j : ℕ) :
    IntegrableOn (fun α : ℝ => f (digit α j) (theta α n j)) (Ioo (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := M) (by simp [Real.volume_Ioo])
    (measurable_symbol_comp hf n j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun α => ?_)
  rw [Real.norm_eq_abs]
  exact hb _ _

/-- **The gate, closed: §4's one-level law read at an indicator.**

For every level of the deterministic bulk, the `α`-average of the digit-cut
*indicator* of an arbitrary measurable `θ`-section family is trapped between
the stationary means of the two members of the Selberg pair, up to the
one-level error `O_{D,A}(L^{-A})` on each side — uniformly in the level, in the
digit cut, in the degree, in the bracketing scale and in the family.

This is what Part B could not give.  The Fejér mean of Part B approximates in
`L¹` under Lebesgue on the cell and therefore leaves an error that has to be
weighed against the law being computed; the pair here is *pointwise* one-sided,
so no such weighing occurs, and the whole cost of the passage from the
indicator to the class is the single number
`stationaryMeanR (majCut) − stationaryMeanR (minCut)`, which
`Selberg.integral_upInd_sub_downInd_le` bounds by the jump count of the
sections.

Proved by applying `OneLevelLaw.oneLevel_joint_law` twice — once to the
majorant family and once to the minorant family, both placed in display (24)'s
class by `isInPD_majCut`/`isInPD_minCut` — and inserting the pointwise
inequalities `minCut ≤ indCut ≤ majCut` of `minCut_le_indCut` and
`indCut_le_majCut`. -/
theorem oneLevel_indicator_sandwich (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ∀ (Acut N : ℕ) (δ : ℝ), 0 < δ → ∀ Bs : ℕ → Set ℝ, (∀ a, MeasurableSet (Bs a)) →
        (Acut : ℝ) ≤ (Lnorm n) ^ D → (N : ℝ) ≤ (Lnorm n) ^ D →
        ((Acut : ℝ) + 1) * ((2 * (N : ℝ) + 1) * (1 + Selberg.farTail N δ)) ≤ (Lnorm n) ^ D →
        stationaryMeanR (minCut N Acut δ Bs) - C * (Lnorm n) ^ (-A)
              ≤ (∫ α in Ioo (0 : ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
          ∧ (∫ α in Ioo (0 : ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
              ≤ stationaryMeanR (majCut N Acut δ Bs) + C * (Lnorm n) ^ (-A) := by
  obtain ⟨C, hC, hev⟩ := OneLevelLaw.oneLevel_joint_law D A hD hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn j hj Acut N δ hδ Bs hBs hAle hNle hbud
  -- the three integrands
  have hindI : IntegrableOn
      (fun α : ℝ => indCut Acut Bs (digit α j) (theta α n j)) (Ioo (0 : ℝ) 1) :=
    integrableOn_symbol_comp (measurable_indCut Acut hBs) (abs_indCut_le Acut Bs) n j
  have hmajI : IntegrableOn
      (fun α : ℝ => majCut N Acut δ Bs (digit α j) (theta α n j)) (Ioo (0 : ℝ) 1) :=
    integrableOn_symbol_comp (measurable_majCut N Acut δ Bs) (abs_majCut_le N Acut δ Bs) n j
  have hminI : IntegrableOn
      (fun α : ℝ => minCut N Acut δ Bs (digit α j) (theta α n j)) (Ioo (0 : ℝ) 1) :=
    integrableOn_symbol_comp (measurable_minCut N Acut δ Bs) (abs_minCut_le N Acut δ Bs) n j
  -- the one-level law on each member of the pair, in real form
  have hreal : ∀ f : ℕ → ℝ → ℝ, IsInPD D (Lnorm n) (fun a θ => ((f a θ : ℝ) : ℂ)) →
      |(∫ α in Ioo (0 : ℝ) 1, f (digit α j) (theta α n j)) - stationaryMeanR f|
        ≤ C * (Lnorm n) ^ (-A) := by
    intro f hf
    have h := hn j hj _ hf
    rw [stationaryMean_ofReal] at h
    have hint : (∫ α in Ioo (0 : ℝ) 1, ((f (digit α j) (theta α n j) : ℝ) : ℂ))
        = ((∫ α in Ioo (0 : ℝ) 1, f (digit α j) (theta α n j) : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [hint, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hmaj := hreal _ (isInPD_majCut D (Lnorm n) Acut N δ Bs hAle hNle hbud)
  have hmin := hreal _ (isInPD_minCut D (Lnorm n) Acut N δ Bs hAle hNle hbud)
  have hle1 : (∫ α in Ioo (0 : ℝ) 1, minCut N Acut δ Bs (digit α j) (theta α n j))
      ≤ ∫ α in Ioo (0 : ℝ) 1, indCut Acut Bs (digit α j) (theta α n j) :=
    setIntegral_mono_on hminI hindI measurableSet_Ioo
      (fun α _ => minCut_le_indCut hδ Bs _ _)
  have hle2 : (∫ α in Ioo (0 : ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
      ≤ ∫ α in Ioo (0 : ℝ) 1, majCut N Acut δ Bs (digit α j) (theta α n j) :=
    setIntegral_mono_on hindI hmajI measurableSet_Ioo
      (fun α _ => indCut_le_majCut hδ Bs _ _)
  have habs1 := abs_le.mp hmaj
  have habs2 := abs_le.mp hmin
  exact ⟨by linarith [habs2.2], by linarith [habs1.1]⟩

/-! ### The size of the gate, from the jump count

The sandwich costs `stationaryMeanR (majCut) − stationaryMeanR (minCut)`.  That
number is bounded *uniformly in the digit* by the `L¹` gap of the pair, because
the stationary mean averages the digit against a probability measure; and the
`L¹` gap is the jump count, `Selberg.integral_upInd_sub_downInd_le`. -/

/-- The per-digit mean of a symbol over the fundamental cell. -/
def innerMean (f : ℕ → ℝ → ℝ) (a : ℕ) : ℝ := ∫ θ in Ioo (0 : ℝ) 1, f a θ

lemma stationaryMeanR_eq (f : ℕ → ℝ → ℝ) :
    stationaryMeanR f = ∫ x, innerMean f (digit x 0) ∂Erdos1002.gaussMeasure := rfl

lemma integrable_innerMean_comp (f : ℕ → ℝ → ℝ) {K : ℝ} (hK : ∀ a, |innerMean f a| ≤ K) :
    Integrable (fun x : ℝ => innerMean f (digit x 0)) Erdos1002.gaussMeasure := by
  have hm : Measurable fun x : ℝ => innerMean f (digit x 0) :=
    (measurable_of_countable (innerMean f)).comp (measurable_digit 0)
  refine Integrable.mono' (integrable_const K) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]; exact hK _

lemma abs_innerMean_majCut_le (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) (a : ℕ) :
    |innerMean (majCut N Acut δ Bs) a| ≤ 1 + Selberg.farTail N δ := by
  unfold innerMean
  have hI : (volume : Measure ℝ).real (Ioo (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioo]
  have h := norm_setIntegral_le_of_norm_le_const
    (C := 1 + Selberg.farTail N δ) (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := 0) (b := 1))
    (fun θ _ => by rw [Real.norm_eq_abs]; exact abs_majCut_le N Acut δ Bs a θ)
  rw [hI, mul_one, Real.norm_eq_abs] at h
  exact h

lemma abs_innerMean_minCut_le (N Acut : ℕ) (δ : ℝ) (Bs : ℕ → Set ℝ) (a : ℕ) :
    |innerMean (minCut N Acut δ Bs) a| ≤ 1 + Selberg.farTail N δ := by
  unfold innerMean
  have hI : (volume : Measure ℝ).real (Ioo (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioo]
  have h := norm_setIntegral_le_of_norm_le_const
    (C := 1 + Selberg.farTail N δ) (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := 0) (b := 1))
    (fun θ _ => by rw [Real.norm_eq_abs]; exact abs_minCut_le N Acut δ Bs a θ)
  rw [hI, mul_one, Real.norm_eq_abs] at h
  exact h

/-- **The gap of the gate, uniformly in the digit.**  When every `θ`-section is
a union of at most `m` intervals, the sandwich costs at most
`(4m+2)·2δ + 2η(N,δ)` — the pair's `L¹` gap, and nothing that depends on the
law of `(a_{j+1}, θ_j)`. -/
theorem stationaryMeanR_gap_le {m : ℕ} (N Acut : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (Bs : ℕ → Set ℝ) (hBs : ∀ a, IntervalClass.IsUnionOfIntervals m (Bs a)) :
    stationaryMeanR (majCut N Acut δ Bs) - stationaryMeanR (minCut N Acut δ Bs)
      ≤ (4 * (m : ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ := by
  set Γ : ℝ := (4 * (m : ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ with hΓ
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓ]
    have := Selberg.farTail_nonneg N δ
    positivity
  have hpt : ∀ a : ℕ,
      innerMean (majCut N Acut δ Bs) a - innerMean (minCut N Acut δ Bs) a ≤ Γ := by
    intro a
    by_cases hc : a ≤ Acut
    · have h := (Selberg.bracket_intervals (hBs a) hδ N).2.2
      have he1 : innerMean (majCut N Acut δ Bs) a
          = ∫ θ in Ioo (0 : ℝ) 1,
              Selberg.realConv N (Selberg.majSymbol N δ (Selberg.upInd δ (Bs a))) θ := by
        unfold innerMean majCut; simp only [if_pos hc]
      have he2 : innerMean (minCut N Acut δ Bs) a
          = ∫ θ in Ioo (0 : ℝ) 1,
              Selberg.realConv N (Selberg.minSymbol N δ (Selberg.downInd δ (Bs a))) θ := by
        unfold innerMean minCut; simp only [if_pos hc]
      rw [he1, he2, hΓ]
      exact h
    · have he1 : innerMean (majCut N Acut δ Bs) a = 0 := by
        unfold innerMean majCut; simp only [if_neg hc]; simp
      have he2 : innerMean (minCut N Acut δ Bs) a = 0 := by
        unfold innerMean minCut; simp only [if_neg hc]; simp
      rw [he1, he2, sub_zero]
      exact hΓ0
  have hIm := integrable_innerMean_comp (majCut N Acut δ Bs) (abs_innerMean_majCut_le N Acut δ Bs)
  have hIn := integrable_innerMean_comp (minCut N Acut δ Bs) (abs_innerMean_minCut_le N Acut δ Bs)
  rw [stationaryMeanR_eq, stationaryMeanR_eq, ← integral_sub hIm hIn]
  calc (∫ x, (innerMean (majCut N Acut δ Bs) (digit x 0)
          - innerMean (minCut N Acut δ Bs) (digit x 0)) ∂Erdos1002.gaussMeasure)
      ≤ ∫ _x, Γ ∂Erdos1002.gaussMeasure :=
        integral_mono (hIm.sub hIn) (integrable_const _) (fun x => hpt _)
    _ = Γ := by
        rw [integral_const]
        simp

/-! ## Part E, the Gauss-Kuzmin normalisation, closed at the interval class

Part D removed the one-sidedness: `oneLevel_indicator_sandwich` reads §4's
one-level law at the indicator itself, and `stationaryMeanR_gap_le` prices the
sandwich by the jump count alone.  What the header then named as the remaining
content of (35) — "the Gauss-Kuzmin *normalisation*, the identification of
`stationaryMeanR` of the mark indicator with `2λ·Λ`" — is proved in
`Kwon1002/GaussKuzmin.lean`, unconditionally and with the constant pinned.

The two `example`s below are the `rfl` guards: the object `GaussKuzmin`
computes with **is** `stationaryMeanR` of the mark-tail symbol, not a variant
of it. -/

/-- **`GaussKuzmin.markTailMean` is `stationaryMeanR` of the mark-tail
indicator**, definitionally.  This is the guard that the normalisation proved
in `Kwon1002/GaussKuzmin.lean` is about this file's object. -/
example : ∀ M : ℝ, GaussKuzmin.markTailMean M
    = stationaryMeanR (fun a θ => if M < (a : ℝ) * W θ then (1:ℝ) else 0) :=
  fun _ => rfl

/-- The same guard read through `indCut` at a full digit range: the mark-tail
symbol is the `indCut` family of Part D at the sections
`Bs a = {θ : M < a·W θ}`, once the digit cut is inactive.  (`Selberg.perInd` of
a `1`-periodic section is that section's indicator.) -/
theorem markTail_stationaryMeanR (M : ℝ) :
    stationaryMeanR (fun a θ => if M < (a : ℝ) * W θ then (1:ℝ) else 0)
      = GaussKuzmin.markTailMean M := rfl

/-- **The stationary side of display (35), at a half-line.**  Uniformly in
nothing — this is the exact stationary statement, and it is where the constant
`2λ·Λ` of the manuscript is pinned. -/
theorem stationaryMeanR_markTail_limit {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => Lnorm n *
        stationaryMeanR (fun a θ => if u * Lnorm n < (a : ℝ) * W θ then (1:ℝ) else 0))
      atTop (𝓝 (2 * lyapunov * (levyIntensity (Ioi u)).toReal)) :=
  GaussKuzmin.tendsto_scaled_markTailMean_nat hu

/-! ### The two digit tails item (i) needs

Cutting the digit at `Acut` is the one step of item (i) that is not pure
parameter juggling, because it is measured against two different laws: the
stationary one, where the exact Gauss-Kuzmin tail applies, and Lebesgue at
level `j`, where display (15) applies.  Both are bounded here, so that item (i)
is a finite and fully named list. -/

/-- The uncut indicator family: `indCut` with the digit cut removed. -/
def indFull (Bs : ℕ → Set ℝ) : ℕ → ℝ → ℝ := fun a θ => Selberg.perInd (Bs a) θ

lemma abs_indFull_le (Bs : ℕ → Set ℝ) (a : ℕ) (θ : ℝ) : |indFull Bs a θ| ≤ 1 := by
  unfold indFull
  rw [abs_of_nonneg (Selberg.perInd_nonneg (Bs a) θ)]
  exact Selberg.perInd_le_one (Bs a) θ

lemma abs_innerMean_le_of_bound {f : ℕ → ℝ → ℝ} {K : ℝ} (hK : ∀ a θ, |f a θ| ≤ K) (a : ℕ) :
    |innerMean f a| ≤ K := by
  unfold innerMean
  have hI : (volume : Measure ℝ).real (Ioo (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioo]
  have h := norm_setIntegral_le_of_norm_le_const (C := K) (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := 0) (b := 1))
    (fun θ _ => by rw [Real.norm_eq_abs]; exact hK a θ)
  rw [hI, mul_one, Real.norm_eq_abs] at h
  exact h

/-- **The stationary digit-cut tail.**  Cutting the digit at `Acut` moves
`stationaryMeanR` by at most the *exact* Gauss-Kuzmin tail
`γ{a₁ ≥ Acut+1} = log(1 + 1/(Acut+1))/log 2`, uniformly in the section family.
With `Acut ≈ L^D` this is `O(L^{-D})`, so it survives multiplication by `L` for
any `D > 1`. -/
theorem stationaryMeanR_digitCut_gap (Acut : ℕ) (Bs : ℕ → Set ℝ) :
    |stationaryMeanR (indCut Acut Bs) - stationaryMeanR (indFull Bs)|
      ≤ Real.log (1 + 1 / ((Acut : ℝ) + 1)) / Real.log 2 := by
  have habsCut : ∀ a θ, |indCut Acut Bs a θ| ≤ 1 := abs_indCut_le Acut Bs
  have hIc := integrable_innerMean_comp (indCut Acut Bs)
    (abs_innerMean_le_of_bound habsCut)
  have hIf := integrable_innerMean_comp (indFull Bs)
    (abs_innerMean_le_of_bound (abs_indFull_le Bs))
  set T : Set ℝ := {x : ℝ | Acut + 1 ≤ digit x 0} with hT
  have hTmeas : MeasurableSet T := (measurable_digit 0) (measurableSet_le measurable_const
    measurable_id)
  have hind : (fun x : ℝ => (if Acut + 1 ≤ digit x 0 then (1:ℝ) else 0))
      = Set.indicator T (fun _ => (1:ℝ)) := by
    funext x
    by_cases hx : Acut + 1 ≤ digit x 0
    · rw [if_pos hx, Set.indicator_of_mem (show x ∈ T from hx)]
    · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ T from hx)]
  have hIT : Integrable (fun x : ℝ => (if Acut + 1 ≤ digit x 0 then (1:ℝ) else 0))
      Erdos1002.gaussMeasure := by
    rw [hind]
    exact (integrable_const (1:ℝ)).indicator hTmeas
  have hpt : ∀ x : ℝ,
      ‖innerMean (indCut Acut Bs) (digit x 0) - innerMean (indFull Bs) (digit x 0)‖
        ≤ (if Acut + 1 ≤ digit x 0 then (1:ℝ) else 0) := by
    intro x
    rw [Real.norm_eq_abs]
    by_cases hc : digit x 0 ≤ Acut
    · have he : innerMean (indCut Acut Bs) (digit x 0) = innerMean (indFull Bs) (digit x 0) := by
        unfold innerMean indCut indFull
        simp only [if_pos hc]
      rw [he, sub_self, abs_zero]
      positivity
    · have he : innerMean (indCut Acut Bs) (digit x 0) = 0 := by
        unfold innerMean indCut
        simp only [if_neg hc]
        simp
      rw [he, zero_sub, abs_neg, if_pos (Nat.succ_le_of_lt (not_le.mp hc))]
      exact abs_innerMean_le_of_bound (abs_indFull_le Bs) _
  rw [stationaryMeanR_eq, stationaryMeanR_eq, ← integral_sub hIc hIf]
  have hbound := norm_integral_le_of_norm_le hIT (Filter.Eventually.of_forall hpt)
  refine le_trans hbound (le_of_eq ?_)
  rw [hind, integral_indicator_const (1:ℝ) hTmeas]
  simp only [smul_eq_mul, mul_one, Measure.real]
  have hK := DigitLocalLaw.gaussMeasure_real_digit_zero_ge (K := Acut + 1)
    (Nat.le_add_left 1 Acut)
  push_cast at hK
  exact hK

/-- **The Lebesgue digit-cut tail.**  `vol{α ∈ (0,1) : a_{j+1}(α) > Acut} ≤
C/(Acut+1)` with `C` absolute, uniformly in the level.  This is display (15) at
`r = 1`, i.e. `Kwon1002.digit_tail_product`; it is what bounds the part of the
level-`j` event that the digit cut discards. -/
theorem lebesgue_digitCut_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ j Acut : ℕ,
      (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Acut < digit α j}).toReal
        ≤ C / ((Acut : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := digit_tail_product
  refine ⟨C, hC, fun j Acut => ?_⟩
  have hset : {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Acut < digit α j}
      = {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧
          ∀ i : Fin 1, (fun _ : Fin 1 => (Acut : ℝ) + 1) i
            ≤ (digit α ((fun _ : Fin 1 => j) i) : ℝ)} := by
    ext α
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    constructor
    · intro h _
      have : (Acut : ℝ) + 1 ≤ ((digit α j : ℕ) : ℝ) := by exact_mod_cast h
      simpa using this
    · intro h
      have := h 0
      simp only at this
      have h2 : (Acut : ℝ) + 1 ≤ ((digit α j : ℕ) : ℝ) := this
      exact_mod_cast h2
  rw [hset]
  have h := hbound 1 (fun _ => j) (fun _ => (Acut : ℝ) + 1)
    (fun a b _ => Subsingleton.elim a b)
    (fun _ => by have h0 : (0:ℝ) ≤ (Acut : ℝ) := Nat.cast_nonneg _; linarith)
  refine le_trans h (le_of_eq ?_)
  simp [div_eq_mul_inv]


/-! ## Part F, item (i): the parameter choice, and display (35) at the
truncation window

Part D reduced display (35) to two items.  This part closes the first outright
and the second at the shape the tree actually names.

* **Item (i), the parameter choice** (`oneLevel_transfer`).  The bracket scale
  `δ`, the Fejér degree `N` and the digit cut `Acut` are tied to `L` by the
  schedule `δ = L^{-2}`, `N = ⌈L^6⌉`, `Acut = ⌈L^2⌉`, read against display
  (24)'s exponent `D = 11` and the one-level rate `A = 2`.  `sched_admissible`
  checks the three side conditions of `oneLevel_indicator_sandwich`, including
  the binding budget `(Acut+1)(2N+1)(1+η) ≤ L^{11}`; `oneLevel_transfer` then
  prices the five error terms and shows their sum is `o(1/L)`, uniformly in the
  level and in the section family.

* **Item (ii), the class.**  `oneLevel_gaussKuzmin_intensity_truncation` proves
  the residual outright at `B = {x : ε < |x| ≤ R}`, the shape
  `IntervalClass.isUnionOfIntervals_truncation` identifies as the only shape the
  §5 chain gives `B`.  The section family is
  `truncSection`, a union of two intervals uniformly in the digit; the
  stationary side is the band normalisation of Part E; and the level-`j` event
  is the section indicator (`oneLevelEvent_truncWindow`).  What is *not* closed
  here is the passage from this window to a general finite union of intervals,
  which needs a decomposition of an arbitrary `IsUnionOfIntervals` family into
  disjoint bands; that is recorded on
  `TupleInputs.oneLevel_gaussKuzmin_intensity_intervals`. -/


/-- Bounded measurable functions are integrable on the fundamental cell. -/
lemma integrableOn_cell {h : ℝ → ℝ} {K : ℝ} (hm : Measurable h) (hb : ∀ θ, |h θ| ≤ K) :
    IntegrableOn h (Ioo (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := K) (by simp [Real.volume_Ioo])
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs]; exact hb θ

lemma innerMean_mono {f g : ℕ → ℝ → ℝ} {K : ℝ}
    (hf : ∀ a, Measurable (f a)) (hg : ∀ a, Measurable (g a))
    (hfb : ∀ a θ, |f a θ| ≤ K) (hgb : ∀ a θ, |g a θ| ≤ K)
    (hle : ∀ a θ, f a θ ≤ g a θ) (a : ℕ) : innerMean f a ≤ innerMean g a := by
  unfold innerMean
  exact setIntegral_mono_on (integrableOn_cell (hf a) (hfb a))
    (integrableOn_cell (hg a) (hgb a)) measurableSet_Ioo (fun θ _ => hle a θ)

lemma stationaryMeanR_mono {f g : ℕ → ℝ → ℝ} {K : ℝ}
    (hf : ∀ a, Measurable (f a)) (hg : ∀ a, Measurable (g a))
    (hfb : ∀ a θ, |f a θ| ≤ K) (hgb : ∀ a θ, |g a θ| ≤ K)
    (hle : ∀ a θ, f a θ ≤ g a θ) : stationaryMeanR f ≤ stationaryMeanR g := by
  rw [stationaryMeanR_eq, stationaryMeanR_eq]
  exact integral_mono
    (integrable_innerMean_comp f (abs_innerMean_le_of_bound hfb))
    (integrable_innerMean_comp g (abs_innerMean_le_of_bound hgb))
    (fun x => innerMean_mono hf hg hfb hgb hle _)

lemma measurable_indFull {Bs : ℕ → Set ℝ} (hBs : ∀ a, MeasurableSet (Bs a)) (a : ℕ) :
    Measurable (indFull Bs a) := Selberg.measurable_perInd (hBs a)

/-- **The Lebesgue digit-cut gap at level `j`.**  Cutting the digit at `Acut`
moves the level-`j` `α`-average by at most the Lebesgue mass of
`{α : a_{j+1}(α) > Acut}`. -/
lemma abs_integral_indCut_sub_indFull_le (Acut : ℕ) {Bs : ℕ → Set ℝ}
    (hBs : ∀ a, MeasurableSet (Bs a)) (n j : ℕ) :
    |(∫ α in Ioo (0:ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
        - ∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j)|
      ≤ (volume {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Acut < digit α j}).toReal := by
  classical
  have hIc : IntegrableOn (fun α : ℝ => indCut Acut Bs (digit α j) (theta α n j))
      (Ioo (0:ℝ) 1) :=
    integrableOn_symbol_comp (measurable_indCut Acut hBs) (abs_indCut_le Acut Bs) n j
  have hIf : IntegrableOn (fun α : ℝ => indFull Bs (digit α j) (theta α n j))
      (Ioo (0:ℝ) 1) :=
    integrableOn_symbol_comp (measurable_indFull hBs) (abs_indFull_le Bs) n j
  set S : Set ℝ := {α : ℝ | Acut < digit α j} with hS
  have hSmeas : MeasurableSet S :=
    (measurable_digit j) (measurableSet_lt measurable_const measurable_id)
  have hGmeas : Measurable fun α : ℝ => S.indicator (fun _ => (1:ℝ)) α :=
    (measurable_const.indicator hSmeas)
  have hIG : IntegrableOn (fun α : ℝ => S.indicator (fun _ => (1:ℝ)) α) (Ioo (0:ℝ) 1) :=
    integrableOn_cell (K := 1) hGmeas (fun θ => by
      rw [Set.indicator_apply]; split_ifs <;> simp)
  have hpt : ∀ α : ℝ,
      ‖indCut Acut Bs (digit α j) (theta α n j) - indFull Bs (digit α j) (theta α n j)‖
        ≤ S.indicator (fun _ => (1:ℝ)) α := by
    intro α
    rw [Real.norm_eq_abs]
    by_cases hc : digit α j ≤ Acut
    · have he : indCut Acut Bs (digit α j) (theta α n j)
          = indFull Bs (digit α j) (theta α n j) := by
        unfold indCut indFull; simp only [if_pos hc]
      rw [he, sub_self, abs_zero]
      rw [Set.indicator_apply]; split_ifs <;> simp
    · have hmem : α ∈ S := not_le.mp hc
      have he : indCut Acut Bs (digit α j) (theta α n j) = 0 := by
        unfold indCut; simp only [if_neg hc]
      rw [he, zero_sub, abs_neg, Set.indicator_of_mem hmem]
      exact abs_indFull_le Bs _ _
  have hstep : |(∫ α in Ioo (0:ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
        - ∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j)|
      ≤ ∫ α in Ioo (0:ℝ) 1, S.indicator (fun _ => (1:ℝ)) α := by
    rw [← integral_sub hIc hIf, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact setIntegral_mono_on ((hIc.sub hIf).norm) hIG measurableSet_Ioo
      (fun α _ => hpt α)
  refine hstep.trans (le_of_eq ?_)
  rw [setIntegral_indicator hSmeas, setIntegral_const, smul_eq_mul, mul_one]
  have hset : Ioo (0:ℝ) 1 ∩ S = {α : ℝ | α ∈ Ioo (0:ℝ) 1 ∧ Acut < digit α j} := by
    ext α; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hS]
  rw [hset]
  rfl

/-! ### The parameter schedule -/

/-- The bracketing scale of the parameter schedule: `δ = L^{-2}`. -/
def schedDelta (L : ℝ) : ℝ := 1 / L ^ 2

/-- The Fejér degree of the parameter schedule: `N = ⌈L^6⌉`. -/
def schedDeg (L : ℝ) : ℕ := ⌈L ^ 6⌉₊

/-- The digit cut of the parameter schedule: `Acut = ⌈L^2⌉`. -/
def schedCut (L : ℝ) : ℕ := ⌈L ^ 2⌉₊

/-- **The parameter schedule is admissible for display (24).**

At `D = 11` the schedule `δ = L^{-2}`, `N = ⌈L^6⌉`, `Acut = ⌈L^2⌉` satisfies
every side condition `oneLevel_indicator_sandwich` imposes, and its Selberg far
tail is `O(L^{-2})`.  The budget is the binding one:
`(Acut+1)(2N+1)(1+η) ≤ L^3 · L^7 · L = L^{11}`. -/
theorem sched_admissible {L : ℝ} (h4L : (4:ℝ) ≤ L) :
    0 < schedDelta L ∧
    L ^ 2 ≤ (schedCut L : ℝ) ∧
    Selberg.farTail (schedDeg L) (schedDelta L) ≤ 1 / (4 * L ^ 2) ∧
    (schedCut L : ℝ) ≤ L ^ (11:ℝ) ∧
    (schedDeg L : ℝ) ≤ L ^ (11:ℝ) ∧
    ((schedCut L : ℝ) + 1) * ((2 * (schedDeg L : ℝ) + 1)
        * (1 + Selberg.farTail (schedDeg L) (schedDelta L))) ≤ L ^ (11:ℝ) := by
  have hLpos : (0:ℝ) < L := by linarith
  have h1L : (1:ℝ) ≤ L := by linarith
  have hL2pos : (0:ℝ) < L ^ 2 := by positivity
  have hL4pos : (0:ℝ) < L ^ 4 := by positivity
  have hL6pos : (0:ℝ) < L ^ 6 := by positivity
  set δ : ℝ := schedDelta L with hδdef
  set N : ℕ := schedDeg L with hNdef
  set Acut : ℕ := schedCut L with hAdef
  have hδpos : 0 < δ := by rw [hδdef, schedDelta]; positivity
  have hδsq : δ ^ 2 = 1 / L ^ 4 := by rw [hδdef, schedDelta]; field_simp
  have hNge : L ^ 6 ≤ (N:ℝ) := by rw [hNdef, schedDeg]; exact Nat.le_ceil _
  have hNlt : (N:ℝ) < L ^ 6 + 1 := by rw [hNdef, schedDeg]; exact Nat.ceil_lt_add_one hL6pos.le
  have hAge : L ^ 2 ≤ (Acut:ℝ) := by rw [hAdef, schedCut]; exact Nat.le_ceil _
  have hAlt : (Acut:ℝ) < L ^ 2 + 1 := by
    rw [hAdef, schedCut]; exact Nat.ceil_lt_add_one hL2pos.le
  have hfarnn : 0 ≤ Selberg.farTail N δ := Selberg.farTail_nonneg N δ
  have hfar : Selberg.farTail N δ ≤ 1 / (4 * L ^ 2) := by
    unfold Selberg.farTail
    rw [hδsq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hrw : 4 * ((N:ℝ) + 1) * (1 / L ^ 4) = 4 * ((N:ℝ) + 1) / L ^ 4 := by ring
    rw [hrw, le_div_iff₀ hL4pos]
    nlinarith [hNge]
  have hfar1 : Selberg.farTail N δ ≤ 1 := by
    refine hfar.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have hrpow : L ^ (11:ℝ) = L ^ (11:ℕ) := by
    rw [show (11:ℝ) = ((11:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hA3 : (Acut:ℝ) + 1 ≤ L ^ 3 := by nlinarith [hAlt, h4L]
  have hN7 : (2 * (N:ℝ) + 1) ≤ L ^ 7 := by nlinarith [hNlt, h4L, hL6pos]
  refine ⟨hδpos, hAge, hfar, ?_, ?_, ?_⟩
  · rw [hrpow]
    exact (by linarith [hA3] : (Acut:ℝ) ≤ L ^ 3).trans
      (pow_le_pow_right₀ h1L (by norm_num))
  · rw [hrpow]
    exact (by linarith [hN7] : (N:ℝ) ≤ L ^ 7).trans
      (pow_le_pow_right₀ h1L (by norm_num))
  · rw [hrpow]
    have hstep1 : (1 + Selberg.farTail N δ) ≤ L := by linarith
    have hstep2 : (2 * (N:ℝ) + 1) * (1 + Selberg.farTail N δ) ≤ L ^ 7 * L :=
      mul_le_mul hN7 hstep1 (by linarith) (by positivity)
    have hprod : ((Acut:ℝ) + 1) * ((2 * (N:ℝ) + 1) * (1 + Selberg.farTail N δ))
        ≤ L ^ 3 * (L ^ 7 * L) :=
      mul_le_mul hA3 hstep2 (by positivity) (by positivity)
    refine hprod.trans (le_of_eq ?_)
    ring

set_option maxHeartbeats 1000000 in
/-- **Item (i), the parameter choice, closed.**

At every level of the deterministic bulk the level-`j` `α`-average of an
indicator whose `θ`-sections are unions of at most `m` intervals agrees with its
stationary mean to `o(1/L)`: for every `ε > 0`, eventually in `n`,

  `L · |∫ 1_{Bs} (a_{j+1}(α), θ_j(α)) dα − stationaryMeanR (indFull Bs)| ≤ ε`

uniformly over `j ∈ J_n` and over the section family.

**The parameter choice, explicitly.**  Against display (24)'s exponent `D = 11`
and the one-level rate `A = 2`, the schedule is

  `δ = L^{-2}`,  `N = ⌈L^6⌉`,  `Acut = ⌈L^2⌉`,

and the four costs are priced as follows.

* Selberg gap `(4m+2)·2δ = (8m+4)L^{-2}`.
* Selberg far tail `η(N,δ) = 1/(4(N+1)δ²) ≤ L^4/(4L^6) = L^{-2}/4`, so
  `2η ≤ L^{-2}/2`.
* one-level rate `C·L^{-A} = C·L^{-2}`.
* stationary digit tail `log(1 + 1/(Acut+1))/log 2 ≤ L^{-2}/log 2 ≤ 2L^{-2}`
  (`stationaryMeanR_digitCut_gap` plus `log(1+x) ≤ x`).
* Lebesgue digit tail `C₂/(Acut+1) ≤ C₂L^{-2}` (`lebesgue_digitCut_tail`,
  i.e. display (15) at `r = 1`).

Their sum is `(8m + 7 + C + C₂)·L^{-2}`, which survives multiplication by `L`.
Display (24)'s budget is met with room to spare: `Acut + 1 ≤ L^3`,
`2N + 1 ≤ L^7`, `1 + η ≤ L`, so `(Acut+1)(2N+1)(1+η) ≤ L^{11}`
(`sched_admissible`).  Every one of `D`, `A`, and the three schedule exponents
is forced only by these five inequalities; nothing here is tuned to a
particular `B`. -/
theorem oneLevel_transfer (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ∀ Bs : ℕ → Set ℝ, (∀ a, MeasurableSet (Bs a)) →
        (∀ a, IntervalClass.IsUnionOfIntervals m (Bs a)) →
        |Lnorm n * (∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j))
            - Lnorm n * stationaryMeanR (indFull Bs)| ≤ ε := by
  obtain ⟨C, hC, hev⟩ := oneLevel_indicator_sandwich 11 2 (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, htail⟩ := lebesgue_digitCut_tail
  have hL0 : ∀ᶠ n : ℕ in atTop,
      max 4 ((8 * (m:ℝ) + 7 + C + C₂) / ε) ≤ Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop _
  filter_upwards [hev, hL0] with n hn hLbig j hj Bs hBsm hBsi
  have h4L : (4:ℝ) ≤ Lnorm n := le_trans (le_max_left _ _) hLbig
  have hbigε : (8 * (m:ℝ) + 7 + C + C₂) / ε ≤ Lnorm n := le_trans (le_max_right _ _) hLbig
  set L : ℝ := Lnorm n with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  have hL2pos : (0:ℝ) < L ^ 2 := by positivity
  have hu : (0:ℝ) < 1 / L ^ 2 := by positivity
  have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  obtain ⟨hδpos, hAge, hfar, hAle, hNle, hbud⟩ := sched_admissible h4L
  set δ : ℝ := schedDelta L with hδdef
  set N : ℕ := schedDeg L with hNdef
  set Acut : ℕ := schedCut L with hAdef
  have hδval : δ = 1 / L ^ 2 := by rw [hδdef, schedDelta]
  have hfarnn : 0 ≤ Selberg.farTail N δ := Selberg.farTail_nonneg N δ
  have hΓle : (4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ
      ≤ (8 * (m:ℝ) + 5) * (1 / L ^ 2) := by
    have hfaru : Selberg.farTail N δ ≤ (1 / L ^ 2) / 4 := by
      have he : (1:ℝ) / (4 * L ^ 2) = (1 / L ^ 2) / 4 := by ring
      linarith [hfar]
    have hstep : (4 * (m:ℝ) + 2) * (2 * δ) = (8 * (m:ℝ) + 4) * (1 / L ^ 2) := by
      rw [hδval]; ring
    linarith [hstep, hfaru, hu]
  have hrpowneg : L ^ (-(2:ℝ)) = 1 / L ^ 2 := by
    have h2 : (2:ℝ) = ((2:ℕ):ℝ) := by norm_num
    rw [Real.rpow_neg hLpos.le, h2, Real.rpow_natCast, one_div]
  -- the sandwich at the scheduled parameters
  obtain ⟨hlow, hhigh⟩ := hn j hj Acut N δ hδpos Bs hBsm hAle hNle hbud
  have hKind : ∀ a θ, |indCut Acut Bs a θ| ≤ 1 + Selberg.farTail N δ :=
    fun a θ => (abs_indCut_le Acut Bs a θ).trans (by linarith)
  have hminSc : stationaryMeanR (minCut N Acut δ Bs) ≤ stationaryMeanR (indCut Acut Bs) :=
    stationaryMeanR_mono (measurable_minCut N Acut δ Bs) (measurable_indCut Acut hBsm)
      (abs_minCut_le N Acut δ Bs) hKind (fun a θ => minCut_le_indCut hδpos Bs a θ)
  have hScmaj : stationaryMeanR (indCut Acut Bs) ≤ stationaryMeanR (majCut N Acut δ Bs) :=
    stationaryMeanR_mono (measurable_indCut Acut hBsm) (measurable_majCut N Acut δ Bs)
      hKind (abs_majCut_le N Acut δ Bs) (fun a θ => indCut_le_majCut hδpos Bs a θ)
  have hgap := stationaryMeanR_gap_le (m := m) N Acut hδpos Bs hBsi
  have hlebtail := (abs_integral_indCut_sub_indFull_le Acut hBsm n j).trans (htail j Acut)
  have hstattail := stationaryMeanR_digitCut_gap Acut Bs
  have hrpowneg : L ^ (-(2:ℝ)) = 1 / L ^ 2 := by
    have h2 : (2:ℝ) = ((2:ℕ):ℝ) := by norm_num
    rw [Real.rpow_neg hLpos.le, h2, Real.rpow_natCast, one_div]
  -- the three error terms, each priced against `L^{-2}`
  have hδval : δ = 1 / L ^ 2 := by rw [hδdef, schedDelta]
  have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hu : (0:ℝ) < 1 / L ^ 2 := by positivity
  have hΓle : (4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ
      ≤ (8 * (m:ℝ) + 5) * (1 / L ^ 2) := by
    have hfaru : Selberg.farTail N δ ≤ (1 / L ^ 2) / 4 := by
      have he : (1:ℝ) / (4 * L ^ 2) = (1 / L ^ 2) / 4 := by ring
      linarith [hfar]
    have hstep : (4 * (m:ℝ) + 2) * (2 * δ) = (8 * (m:ℝ) + 4) * (1 / L ^ 2) := by
      rw [hδval]; ring
    linarith [hstep, hfaru, hu]
  -- the two digit tails, priced against `L^{-2}`
  have hA1pos : (0:ℝ) < (Acut:ℝ) + 1 := by positivity
  have hAcut1 : L ^ 2 ≤ (Acut:ℝ) + 1 := by linarith
  have hlebu : C₂ / ((Acut:ℝ) + 1) ≤ C₂ * (1 / L ^ 2) := by
    rw [div_le_iff₀ hA1pos]
    have hrw : C₂ * (1 / L ^ 2) * ((Acut:ℝ) + 1) = C₂ * (((Acut:ℝ) + 1) / L ^ 2) := by ring
    rw [hrw]
    have h1 : (1:ℝ) ≤ ((Acut:ℝ) + 1) / L ^ 2 := by rw [le_div_iff₀ hL2pos]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC₂.le
    rw [mul_one] at h2
    exact h2
  have hlogu : Real.log (1 + 1 / ((Acut:ℝ) + 1)) / Real.log 2 ≤ 2 * (1 / L ^ 2) := by
    have hx : (0:ℝ) < 1 / ((Acut:ℝ) + 1) := by positivity
    have hxu : 1 / ((Acut:ℝ) + 1) ≤ 1 / L ^ 2 := by
      rw [div_le_div_iff₀ hA1pos hL2pos]; linarith
    have hnum : Real.log (1 + 1 / ((Acut:ℝ) + 1)) ≤ 1 / L ^ 2 :=
      le_trans (GaussKuzmin.log_one_add_le hx) hxu
    have hlog2 : (1:ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
    have h3 : (0:ℝ) ≤ (1 / L ^ 2) * (2 * Real.log 2 - 1) :=
      mul_nonneg hu.le (by linarith)
    linarith [hnum, h3]
  -- the sandwich, read as a two-sided bound on the digit-cut average
  have hIcSc : |(∫ α in Ioo (0:ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
      - stationaryMeanR (indCut Acut Bs)|
      ≤ ((4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ) + C * L ^ (-(2:ℝ)) := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have htri : |(∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j))
      - stationaryMeanR (indFull Bs)|
      ≤ C₂ / ((Acut:ℝ) + 1)
        + (((4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ) + C * L ^ (-(2:ℝ)))
        + Real.log (1 + 1 / ((Acut:ℝ) + 1)) / Real.log 2 := by
    have h1 : |(∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j))
        - (∫ α in Ioo (0:ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))|
        ≤ C₂ / ((Acut:ℝ) + 1) := by rw [abs_sub_comm]; exact hlebtail
    have hstep := abs_sub_le
      (∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j))
      (∫ α in Ioo (0:ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
      (stationaryMeanR (indFull Bs))
    have hstep2 := abs_sub_le
      (∫ α in Ioo (0:ℝ) 1, indCut Acut Bs (digit α j) (theta α n j))
      (stationaryMeanR (indCut Acut Bs))
      (stationaryMeanR (indFull Bs))
    linarith [h1, hIcSc, hstattail, hstep, hstep2]
  have hCterm : C * L ^ (-(2:ℝ)) = C * (1 / L ^ 2) := by rw [hrpowneg]
  have htot : |(∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j))
      - stationaryMeanR (indFull Bs)|
      ≤ (8 * (m:ℝ) + 7 + C + C₂) * (1 / L ^ 2) := by
    have hexp : (8 * (m:ℝ) + 7 + C + C₂) * (1 / L ^ 2)
        = (8 * (m:ℝ) + 5) * (1 / L ^ 2) + C * (1 / L ^ 2) + C₂ * (1 / L ^ 2)
          + 2 * (1 / L ^ 2) := by ring
    rw [hexp]
    linarith [htri, hΓle, hlebu, hlogu, hCterm]
  have habs : |L * (∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j))
      - L * stationaryMeanR (indFull Bs)|
      = L * |(∫ α in Ioo (0:ℝ) 1, indFull Bs (digit α j) (theta α n j))
          - stationaryMeanR (indFull Bs)| := by
    rw [← mul_sub, abs_mul, abs_of_pos hLpos]
  rw [habs]
  have hstep := mul_le_mul_of_nonneg_left htot hLpos.le
  have hfin : L * ((8 * (m:ℝ) + 7 + C + C₂) * (1 / L ^ 2))
      = (8 * (m:ℝ) + 7 + C + C₂) / L := by field_simp
  rw [hfin] at hstep
  refine hstep.trans ?_
  rw [div_le_iff₀ hLpos]
  rw [div_le_iff₀ hε] at hbigε
  linarith

/-! ### Part B: the stationary normalisation at the truncation window -/

/-- `Λ` is reflection invariant: its density `1/(2π²x²)` is even and Lebesgue
measure is `neg`-invariant. -/
theorem levyIntensity_neg {S : Set ℝ} (hS : MeasurableSet S) :
    levyIntensity ((fun x : ℝ => -x) ⁻¹' S) = levyIntensity S := by
  have heven : ∀ x : ℝ, levyIntensityDensity (-x) = levyIntensityDensity x := by
    intro x; unfold levyIntensityDensity; ring_nf
  unfold levyIntensity
  rw [withDensity_apply _ (hS.preimage measurable_neg), withDensity_apply _ hS,
    ← lintegral_indicator (hS.preimage measurable_neg), ← lintegral_indicator hS]
  rw [← lintegral_neg_eq_self (μ := (volume : Measure ℝ))]
  congr 1
  funext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem (show -x ∈ (fun y : ℝ => -y) ⁻¹' S by simpa using hx),
      Set.indicator_of_mem hx, heven]
  · rw [Set.indicator_of_notMem (show -x ∉ (fun y : ℝ => -y) ⁻¹' S by simpa using hx),
      Set.indicator_of_notMem hx]

/-- **The truncation window carries exactly twice the mass of its positive
half.**  `Λ{ε < |x| ≤ R} = 2·Λ((ε,R])`. -/
theorem levyIntensity_truncWindow {ε R : ℝ} (hε : 0 < ε) :
    (levyIntensity {x : ℝ | ε < |x| ∧ |x| ≤ R}).toReal
      = 2 * (levyIntensity (Ioc ε R)).toReal := by
  have hneg : Ico (-R) (-ε) = (fun x : ℝ => -x) ⁻¹' (Ioc ε R) := by
    ext x
    simp only [Set.mem_Ico, Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hsplit : {x : ℝ | ε < |x| ∧ |x| ≤ R} = Ioc ε R ∪ Ico (-R) (-ε) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioc, Set.mem_Ico]
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2⟩
        · exact absurd hx (by linarith)
    · rw [abs_of_neg hx]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact absurd h1 (by linarith)
        · exact ⟨by linarith, by linarith⟩
  have hdisj : Disjoint (Ioc ε R) (Ico (-R) (-ε)) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx1, -⟩ ⟨-, hx2⟩
    linarith
  have hfin : levyIntensity (Ioc ε R) ≠ ⊤ :=
    ne_top_of_le_ne_top (GaussKuzmin.levyIntensity_Ioi_lt_top hε)
      (measure_mono (fun x hx => hx.1))
  have hmeasure : levyIntensity {x : ℝ | ε < |x| ∧ |x| ≤ R}
      = levyIntensity (Ioc ε R) + levyIntensity (Ioc ε R) := by
    rw [hsplit, measure_union hdisj measurableSet_Ico, hneg,
      levyIntensity_neg measurableSet_Ioc]
  rw [hmeasure, ENNReal.toReal_add hfin hfin]
  ring

/-! ### The `θ`-sections of the truncation window -/

/-- The `θ`-section of the mark event at the truncation window `(ε, R]`, scale
`L`, digit `a`. -/
def truncSection (L ε R : ℝ) (a : ℕ) : Set ℝ :=
  {θ : ℝ | θ ∈ Ico (0:ℝ) 1 ∧ (a:ℝ) * W θ ∈ Ioc (ε * L) (R * L)}

lemma truncSection_eq (L ε R : ℝ) (a : ℕ) :
    truncSection L ε R a
      = Ico (0:ℝ) 1 ∩ (fun θ : ℝ => (a:ℝ) * W θ) ⁻¹' (Ioc (ε * L) (R * L)) := rfl

lemma measurableSet_truncSection (L ε R : ℝ) (a : ℕ) :
    MeasurableSet (truncSection L ε R a) := by
  rw [truncSection_eq]
  exact measurableSet_Ico.inter
    ((measurable_const.mul measurable_W) measurableSet_Ioc)

/-- **The sections are unions of two intervals, uniformly in the digit.**  `W`
has two monotone branches on the cell and `(ε L, R L]` is one interval. -/
lemma isUnionOfIntervals_truncSection (L ε R : ℝ) (a : ℕ) :
    IntervalClass.IsUnionOfIntervals 2 (truncSection L ε R a) := by
  have h := IntervalClass.markSection_isUnionOfIntervals
    (IntervalClass.isUnionOfIntervals_one (ordConnected_Ioc (a := ε * L) (b := R * L)))
    ((a:ℝ))
  rw [show 2 * 1 = 2 from rfl] at h
  exact h

/-- `W` sees only the fractional part.  (`Kwon1002.W_fract` of
`Kwon1002/Prop64.lean` is the same fact, but §6 is not in this module's import
closure, so it is reproved here rather than imported.) -/
lemma W_of_fract (θ : ℝ) : W (Int.fract θ) = W θ := by
  unfold W; rw [Int.fract_fract]

/-- Membership in the periodised section, unwound. -/
lemma mem_perSet_truncSection (L ε R : ℝ) (a : ℕ) (θ : ℝ) :
    θ ∈ Selberg.perSet (truncSection L ε R a)
      ↔ (ε * L < (a:ℝ) * W θ ∧ (a:ℝ) * W θ ≤ R * L) := by
  unfold Selberg.perSet truncSection
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioc, W_of_fract]
  exact ⟨fun h => h.2, fun h => ⟨⟨Int.fract_nonneg θ, Int.fract_lt_one θ⟩, h⟩⟩

/-- **The section indicator is a difference of two mark-tail indicators.** -/
lemma indFull_truncSection {L ε R : ℝ} (hεR : ε * L ≤ R * L) (a : ℕ) (θ : ℝ) :
    indFull (truncSection L ε R) a θ
      = (if ε * L < (a:ℝ) * W θ then (1:ℝ) else 0)
        - (if R * L < (a:ℝ) * W θ then (1:ℝ) else 0) := by
  classical
  have hmem := mem_perSet_truncSection L ε R a θ
  unfold indFull Selberg.perInd
  rw [Set.indicator_apply]
  by_cases h : θ ∈ Selberg.perSet (truncSection L ε R a)
  · obtain ⟨h1, h2⟩ := hmem.mp h
    rw [if_pos h, if_pos h1, if_neg (not_lt.mpr h2)]
    ring
  · rw [if_neg h]
    have hnot := (not_iff_not.mpr hmem).mp h
    rw [not_and_or, not_lt, not_le] at hnot
    rcases hnot with h1 | h2
    · rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr (le_trans h1 hεR))]
      ring
    · rw [if_pos (lt_of_le_of_lt hεR h2), if_pos h2]
      ring

/-- `stationaryMeanR` is additive on bounded measurable symbols. -/
lemma stationaryMeanR_sub {f g : ℕ → ℝ → ℝ} {K : ℝ}
    (hf : ∀ a, Measurable (f a)) (hg : ∀ a, Measurable (g a))
    (hfb : ∀ a θ, |f a θ| ≤ K) (hgb : ∀ a θ, |g a θ| ≤ K) :
    stationaryMeanR (fun a θ => f a θ - g a θ) = stationaryMeanR f - stationaryMeanR g := by
  have hinner : ∀ x : ℝ, (∫ θ in Ioo (0:ℝ) 1, (f (digit x 0) θ - g (digit x 0) θ))
      = innerMean f (digit x 0) - innerMean g (digit x 0) := by
    intro x
    exact integral_sub (integrableOn_cell (hf _) (hfb _)) (integrableOn_cell (hg _) (hgb _))
  show (∫ x, (∫ θ in Ioo (0:ℝ) 1, (f (digit x 0) θ - g (digit x 0) θ))
      ∂Erdos1002.gaussMeasure) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), stationaryMeanR_eq,
    stationaryMeanR_eq]
  exact integral_sub (integrable_innerMean_comp f (abs_innerMean_le_of_bound hfb))
    (integrable_innerMean_comp g (abs_innerMean_le_of_bound hgb))

lemma measurable_markTailSymbol (M : ℝ) (a : ℕ) :
    Measurable (fun θ : ℝ => if M < (a:ℝ) * W θ then (1:ℝ) else 0) :=
  measurable_const.ite (measurableSet_lt measurable_const (measurable_const.mul measurable_W))
    measurable_const

lemma abs_markTailSymbol_le (M : ℝ) (a : ℕ) (θ : ℝ) :
    |(if M < (a:ℝ) * W θ then (1:ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

/-- **The stationary side of display (35) at the truncation window.**  The
stationary mean of the section indicator is the mark-tail band mass. -/
theorem stationaryMeanR_truncSection {L ε R : ℝ} (hεR : ε * L ≤ R * L) :
    stationaryMeanR (indFull (truncSection L ε R))
      = GaussKuzmin.markTailMean (ε * L) - GaussKuzmin.markTailMean (R * L) := by
  have hfun : indFull (truncSection L ε R)
      = fun (a : ℕ) (θ : ℝ) => (if ε * L < (a:ℝ) * W θ then (1:ℝ) else 0)
        - (if R * L < (a:ℝ) * W θ then (1:ℝ) else 0) := by
    funext a θ; exact indFull_truncSection hεR a θ
  rw [hfun, stationaryMeanR_sub (K := 1) (measurable_markTailSymbol (ε * L))
    (measurable_markTailSymbol (R * L)) (abs_markTailSymbol_le (ε * L))
    (abs_markTailSymbol_le (R * L)), markTail_stationaryMeanR, markTail_stationaryMeanR]

/-! ### The level-`j` event *is* the section indicator -/

lemma measurableSet_truncWindow (ε R : ℝ) : MeasurableSet {x : ℝ | ε < |x| ∧ |x| ≤ R} :=
  (measurableSet_lt measurable_const measurable_abs).inter
    (measurableSet_le measurable_abs measurable_const)

/-- **The `α`-average of the section indicator is the level-`j` event mass.**
The sign `(-1)^j` cancels because the truncation window is symmetric and the
mark is nonnegative, so the identity holds at every parity. -/
theorem oneLevelEvent_truncWindow {ε R : ℝ} {n j : ℕ} (hL : 0 < Lnorm n) :
    unifIoo.real (oneLevelEvent n {x : ℝ | ε < |x| ∧ |x| ≤ R} j)
      = ∫ α in Ioo (0:ℝ) 1,
          indFull (truncSection (Lnorm n) ε R) (digit α j) (theta α n j) := by
  classical
  set B : Set ℝ := {x : ℝ | ε < |x| ∧ |x| ≤ R} with hBdef
  have hE : MeasurableSet (oneLevelEvent n B j) :=
    (measurable_signedMark n j) (measurableSet_truncWindow ε R)
  have hiff : ∀ α : ℝ,
      theta α n j ∈ Selberg.perSet (truncSection (Lnorm n) ε R (digit α j))
        ↔ α ∈ oneLevelEvent n B j := by
    intro α
    rw [mem_perSet_truncSection]
    have hmarknn : (0:ℝ) ≤ mark α n j :=
      mul_nonneg (Nat.cast_nonneg _) (W_nonneg _)
    have habs : |signedMark α n j| = mark α n j / Lnorm n := by
      rw [signedMark, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg hL.le, abs_of_nonneg hmarknn]
    have hmk : (digit α j : ℝ) * W (theta α n j) = mark α n j := rfl
    rw [hmk]
    show _ ↔ signedMark α n j ∈ B
    rw [hBdef]
    simp only [Set.mem_setOf_eq, habs]
    rw [lt_div_iff₀ hL, div_le_iff₀ hL]
  have hind : ∀ α : ℝ, indFull (truncSection (Lnorm n) ε R) (digit α j) (theta α n j)
      = Set.indicator (oneLevelEvent n B j) (fun _ => (1:ℝ)) α := by
    intro α
    unfold indFull Selberg.perInd
    by_cases hc : theta α n j ∈ Selberg.perSet (truncSection (Lnorm n) ε R (digit α j))
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((hiff α).mp hc)]
    · rw [Set.indicator_of_notMem hc,
        Set.indicator_of_notMem (fun h => hc ((hiff α).mpr h))]
  rw [integral_congr_ae (Filter.Eventually.of_forall hind),
    setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
  show (unifIoo (oneLevelEvent n B j)).toReal = _
  rw [unifIoo, Measure.restrict_apply hE]
  congr 2
  exact Set.inter_comm _ _

/-! ### Display (35) at the truncation window, unconditionally -/

/-- **`TupleInputs.oneLevel_gaussKuzmin_intensity` at the truncation window,
proved.**

For `B = {x : ε < |x| ≤ R}` — the shape `IntervalClass.isUnionOfIntervals_truncation`
identifies as the only shape the §5 chain gives `B` — display (35) holds
unconditionally, with `Λe = Λo = Λ((ε,R])` and `Λe + Λo = Λ(B)`
(`levyIntensity_truncWindow`).

The three ingredients are Part D's sandwich read through `oneLevel_transfer`
(item (i), the parameter choice), the Gauss-Kuzmin band normalisation
`GaussKuzmin.tendsto_scaled_markBandMean` (Part E), and the identification of
the level-`j` event with the section indicator (`oneLevelEvent_truncWindow`).
The sign `(-1)^j` does not enter: the window is symmetric and the mark is
nonnegative, so the section is the same at both parities, and the two halves of
`Λ` are equal by `levyIntensity_neg`. -/
theorem oneLevel_gaussKuzmin_intensity_truncation {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity {x : ℝ | ε < |x| ∧ |x| ≤ R}).toReal ∧
      ∀ ε' > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        |Lnorm n * unifIoo.real (oneLevelEvent n {x : ℝ | ε < |x| ∧ |x| ≤ R} j)
            - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε' := by
  refine ⟨(levyIntensity (Ioc ε R)).toReal, (levyIntensity (Ioc ε R)).toReal, ?_, ?_⟩
  · rw [levyIntensity_truncWindow hε]; ring
  intro ε' hε'
  set Λ : ℝ := (levyIntensity (Ioc ε R)).toReal with hΛdef
  have hband : Tendsto (fun n : ℕ => Lnorm n *
      (GaussKuzmin.markTailMean (ε * Lnorm n) - GaussKuzmin.markTailMean (R * Lnorm n)))
      atTop (𝓝 (2 * lyapunov * Λ)) :=
    (GaussKuzmin.tendsto_scaled_markBandMean hε hεR).comp TupleMeasure.tendsto_Lnorm_atTop
  have hb0 : Tendsto (fun n : ℕ => |Lnorm n *
      (GaussKuzmin.markTailMean (ε * Lnorm n) - GaussKuzmin.markTailMean (R * Lnorm n))
        - 2 * lyapunov * Λ|) atTop (𝓝 0) := by
    have h := (hband.sub (tendsto_const_nhds (x := 2 * lyapunov * Λ) (f := atTop))).abs
    simpa using h
  have hbd : ∀ᶠ n : ℕ in atTop, |Lnorm n *
      (GaussKuzmin.markTailMean (ε * Lnorm n) - GaussKuzmin.markTailMean (R * Lnorm n))
        - 2 * lyapunov * Λ| ≤ ε' / 2 :=
    hb0.eventually_le_const (by linarith)
  filter_upwards [oneLevel_transfer 2 (half_pos hε'), hbd,
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0] with n htr hbdn hL j hj
  have hεRL : ε * Lnorm n ≤ R * Lnorm n := mul_le_mul_of_nonneg_right hεR hL.le
  have hev := htr j hj (truncSection (Lnorm n) ε R)
    (measurableSet_truncSection (Lnorm n) ε R) (isUnionOfIntervals_truncSection (Lnorm n) ε R)
  rw [stationaryMeanR_truncSection hεRL] at hev
  rw [oneLevelEvent_truncWindow hL, ite_self]
  refine le_trans (abs_sub_le _ (Lnorm n *
      (GaussKuzmin.markTailMean (ε * Lnorm n) - GaussKuzmin.markTailMean (R * Lnorm n))) _) ?_
  linarith [hev, hbdn]

/-- **Token-identity check.**  The statement proved above is the canonical
residual `Kwon1002.TupleInputs.oneLevel_gaussKuzmin_intensity`, read at
`B = {x : ε < |x| ≤ R}`; this `example` reproduces that residual token for
token, so the instance above is an instance of *it* and not of a variant. -/
example : ∀ (B : Set ℝ), MeasurableSet B →
    (∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) → (∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) →
    ∃ Λe Λo : ℝ, Λe + Λo = (levyIntensity B).toReal ∧
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        |Lnorm n * unifIoo.real (oneLevelEvent n B j)
            - 2 * lyapunov * (if Even j then Λe else Λo)| ≤ ε :=
  TupleInputs.oneLevel_gaussKuzmin_intensity

end

end Section5Join

end Kwon1002
