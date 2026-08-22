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

What remains of (35) after Parts D and E is therefore neither the
one-sidedness nor the constant.  It is (i) the *choice of bracket parameters*
`(Acut, N, δ)` against `L`, together with the two digit tails, and (ii) the
passage from the interval class — where both the bracket and the normalisation
live — to the arbitrary measurable `B` the residual is stated for.  Item (ii)
needs a uniform-in-`L` density bound on the level-`j` law and is the one
genuinely open item; see the corrected obstruction record on
`TupleInputs.oneLevel_gaussKuzmin_intensity`.  For residual 2a and (F7) the
`k`-level and pair-level bookkeeping sits on top of the same two items.

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

end

end Section5Join

end Kwon1002
