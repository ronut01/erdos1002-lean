import Kwon1002.FourierPairs
import Kwon1002.LevyExponent
import Kwon1002.TupleCount
import Kwon1002.CharacterReduction
import Kwon1002.TransferIdentity

/-!
# Discharge: canonical statements, now unconditional

Several canonical goals are declared with `sorry` in the module that
introduces them, because that module sits BELOW the modules that prove
them in the import order (`CauchyLaw` supplies `cauchyMeasure`, which the
analytic proofs consume; `Section4` states the §4 goals that later modules
discharge). The dependency cannot be reversed without splitting files.

This capstone closes the loop: each theorem restates a canonical goal
VERBATIM and proves it outright. **Cite these versions**, each is
`#print axioms`-clean, whereas the same-named declaration in the
introducing module still carries `sorryAx`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Kwon1002

/-- `∫_ℝ (1 - cos u)/u² du = π`, the classical integral behind the Cauchy
characteristic exponent. Unconditional. -/
theorem integral_one_sub_cos_div_sq' :
    (∫ u : ℝ, (1 - Real.cos u) / u ^ 2) = Real.pi :=
  Kwon1002.FourierPairs.integral_one_sub_cos_div_sq

/-- Characteristic function of Cauchy(0, 1/(2π)): `E[e^{itX}] = e^{-|t|/(2π)}`.
Unconditional, and, with `cauchyMeasure_Iic_toReal`, an independent
second confirmation of the constant 1/(2π). -/
theorem charFun_cauchyProb' (t : ℝ) :
    charFun (cauchyProb : Measure ℝ) t
      = (Real.exp (-(|t| / (2 * Real.pi))) : ℂ) :=
  Kwon1002.FourierPairs.charFun_cauchyProb t

/-- **Kwon, §4: the count of non-good r-tuples is O_r(L^{r-1} H) (between (26) and Prop 4.1)**. Unconditional. -/
theorem nonGood_tuple_count' (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j}).ncard : ℝ)
        ≤ C * (Lnorm n) ^ (r - 1) * Hscale n :=
  Kwon1002.TupleCount.nonGood_tuple_count r

/-- **Kwon, display (31): window characters reduce to the central pair**. Unconditional. -/
theorem window_character_reduction' (R : ℕ) (c : Fin (2 * R + 1) → ℤ) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R ≤ j →
        ∃ m : ℤ,
          (∑ i : Fin (2 * R + 1), (c i : ℝ) * theta α n (j + (i : ℕ) - R))
            = (A (windowWord R α j) : ℝ) * theta α n j
              + (B (windowWord R α j) : ℝ) * thetaPred α n j + (m : ℝ) :=
  Kwon1002.S4chars.window_character_reduction R c

/-! ### Not restated here

`Kwon1002.TransferIdentity.cylinder_transfer_eq_kwonDensity_Ioo` (Kwon's
display (14), corrected domain) and `TransferIdentity.lemma_3_2'`
(Lemma 3.2, display (17)) are both proved and axiom-clean, but their
statements mention names that only resolve inside that module's namespace,
so they are cited there rather than restated here. -/

end Kwon1002
