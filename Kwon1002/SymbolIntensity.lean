import Kwon1002.TupleTransfer
import Kwon1002.LayerAssembly

/-!
# The one-level intensity at a symbol

`Kwon1002/LayerAssembly.lean` reduces `CorFinal.largeSum_charFun_limit` to two
analytic inputs, of which the first is

  `hp1 : ∑_{j ≤ n} ∫₀¹ h_j → Λ̂`,   `h_j(α) = (e^{itX_{n,j}} − 1)·1{j ∈ J_n, |X_{n,j}| > ε}`,

and `Kwon1002/FactorialSeries.lean`, `Kwon1002/MultiLevel.lean` and
`Kwon1002/CorFinal.lean` all record the obstruction to it in the same words: the
per-level intensity is available at an *indicator*, and what `hp1` needs is a
**complex symbol**, reached by "a simple-function approximation inside the
truncation window, plus its tail".

This module carries out the first half of that sentence, unconditionally: the
one-level sums converge for **every step symbol** built from the interval class.

* `levelSymbol` — the currency: `∫₀¹ 1{j ∈ J_n}·ψ(X_{n,j})`, of which
  `LayerAssembly.mu` is the case `ψ(x) = (e^{itx}−1)1{|x|>ε}`
  (`mu_eq_levelSymbol`, proved).
* `sum_levelSymbol_step_tendsto` — for `ψ = ∑_i w_i 1_{E_i}` with each `E_i` in
  the interval class, bounded away from `0` and bounded,
  `∑_{j ≤ n} levelSymbol ψ c n j → ∑_i w_i Λ(E_i)`.

The proof is linearity over `LayerAssembly`-free ground: the level integral of an
indicator symbol is exactly the mass of `LevyExponent.bulkMarkEvent`, and the
limit of that is `TupleTransfer.oneLevel_intensity_limit_intervals`, which is now
unconditional.  No disjointness of the `E_i` is needed; the sets may overlap.

**What this does not do.**  It does not prove `hp1`.  Two steps separate the two,
and both are metric rather than structural:

1. *the window approximation.*  `x ↦ (e^{itx}−1)` is uniformly continuous on
   `{ε < |x| ≤ R}`, so it is within `η` of a step symbol on `O(R/η)` pieces; what
   this costs is `η` times the total window mass
   `∑_{j≤n} P(ε < |X_{n,j}| ≤ R)`, which is bounded uniformly in `n` by
   `FactorialRoute.exists_tupleBigEvent_bound` at `|S| = 1`;
2. *the tail.*  `∑_{j≤n} P(|X_{n,j}| > R) = O(1/R)` uniformly in `n`, by the same
   bound with its constant `C₀/(8R)`, against `Λ{|x| > R} = 1/(π²R)`.

Neither is written here.  What is written is the step that needed §4, and the
two that remain need no further input from §4.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace SymbolIntensity

noncomputable section

open LevyExponent TupleMeasure

/-- **The level-`j` integral of a symbol on the random bulk.**
`∫₀¹ 1{j ∈ J_n(α)}·ψ(X_{n,j}(α)) dα`. -/
def levelSymbol (ψ : ℝ → ℂ) (c : ℝ) (n j : ℕ) : ℂ :=
  ∫ α in Ioo (0:ℝ) 1,
    Set.indicator {β : ℝ | j ∈ bulkIndices c β n} (fun β => ψ (signedMark β n j)) α

/-- `LayerAssembly.mu` is `levelSymbol` at the symbol
`x ↦ (e^{itx} − 1)·1{|x| > ε}`.  The two indicators agree because the symbol
already vanishes off the truncation set. -/
theorem mu_eq_levelSymbol (t c ε : ℝ) (n j : ℕ) :
    LayerAssembly.mu t c ε n j
      = levelSymbol (fun x : ℝ => Set.indicator (PoissonRoute.truncSet ε)
          (fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) - 1) x) c n j := by
  unfold LayerAssembly.mu levelSymbol
  refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
  by_cases hb : j ∈ bulkIndices c α n <;>
    by_cases hs : signedMark α n j ∈ PoissonRoute.truncSet ε <;>
    simp [FactorialRoute.jumpFactor, FactorialRoute.bigEvent, bulkMarkEvent, hb, hs]

/-- The level integral of an **indicator** symbol is the mass of the marked bulk
event: the currency of `Kwon1002/TupleMeasure.lean` sits inside the currency of
`levelSymbol`. -/
theorem levelSymbol_indicator (c : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (n j : ℕ) :
    levelSymbol (fun x => Set.indicator B (fun _ => (1:ℂ)) x) c n j
      = ((unifIoo.real (bulkMarkEvent c n B j) : ℝ) : ℂ) := by
  have hE : MeasurableSet (bulkMarkEvent c n B j) := measurableSet_bulkMarkEvent c n hB j
  have hpt : ∀ α : ℝ, Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
      (fun β => Set.indicator B (fun _ => (1:ℂ)) (signedMark β n j)) α
      = Set.indicator (bulkMarkEvent c n B j) (fun _ => (1:ℂ)) α := by
    intro α
    by_cases hb : j ∈ bulkIndices c α n <;> by_cases hs : signedMark α n j ∈ B <;>
      simp [bulkMarkEvent, hb, hs]
  unfold levelSymbol
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), setIntegral_indicator hE,
    setIntegral_const, Complex.real_smul, mul_one]
  congr 1
  simp [Measure.real, unifIoo, Measure.restrict_apply hE, Set.inter_comm]

/-- `levelSymbol` is linear in the symbol along a finite sum of indicators. -/
theorem levelSymbol_step (c : ℝ) {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (n j : ℕ) :
    levelSymbol (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x) c n j
      = ∑ i, w i * ((unifIoo.real (bulkMarkEvent c n (E i) j) : ℝ) : ℂ) := by
  classical
  have hpt : ∀ α : ℝ, Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
        (fun β => ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) (signedMark β n j)) α
      = ∑ i, w i * Set.indicator (bulkMarkEvent c n (E i) j) (fun _ => (1:ℂ)) α := by
    intro α
    by_cases hb : j ∈ bulkIndices c α n
    · rw [Set.indicator_of_mem (show α ∈ {β : ℝ | j ∈ bulkIndices c β n} from hb)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hs : signedMark α n j ∈ E i <;>
        simp [bulkMarkEvent, hb, hs]
    · rw [Set.indicator_of_notMem (show α ∉ {β : ℝ | j ∈ bulkIndices c β n} from hb)]
      refine (Finset.sum_eq_zero (fun i _ => ?_)).symm
      rw [Set.indicator_of_notMem (show α ∉ bulkMarkEvent c n (E i) j from fun h => hb h.1),
        mul_zero]
  have hint : ∀ i : Fin M, IntegrableOn
      (fun α : ℝ => w i * Set.indicator (bulkMarkEvent c n (E i) j) (fun _ => (1:ℂ)) α)
      (Ioo (0:ℝ) 1) := by
    intro i
    refine Integrable.const_mul ?_ _
    exact (integrable_const (1:ℂ)).indicator
      (measurableSet_bulkMarkEvent c n (hE i) j)
  unfold levelSymbol
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finset_sum _ (fun i _ => hint i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul]
  congr 1
  have hli := levelSymbol_indicator c (hE i) n j
  unfold levelSymbol at hli
  rw [← hli]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
  by_cases hb : j ∈ bulkIndices c α n <;> by_cases hs : signedMark α n j ∈ E i <;>
    simp [bulkMarkEvent, hb, hs]

/-- **`hp1` at a step symbol, unconditionally.**  For every finite family of
target sets in the interval class, bounded away from the origin and bounded, and
every complex weights,

  `∑_{j ≤ n} ∫₀¹ 1{j ∈ J_n}·(∑_i w_i 1_{E_i})(X_{n,j}) → ∑_i w_i Λ(E_i)`.

The sets need not be disjoint; only linearity and
`TupleTransfer.oneLevel_intensity_limit_intervals` are used, and the latter is
axiom-clean. -/
theorem sum_levelSymbol_step_tendsto (c : ℝ) {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hE0 : ∀ i, ∃ δ > 0, ∀ x ∈ E i, δ ≤ |x|)
    (hEb : ∀ i, ∃ R : ℝ, ∀ x ∈ E i, |x| ≤ R)
    (hEi : ∀ i, IntervalClass.IsFiniteUnionOfIntervals (E i)) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        levelSymbol (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x) c n j)
      atTop (𝓝 (∑ i, w i * (((levyIntensity (E i)).toReal : ℝ) : ℂ))) := by
  classical
  have hswap : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1),
        levelSymbol (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x) c n j)
      = ∑ i, w i * ((∑ j ∈ Finset.range (n + 1),
          unifIoo.real (bulkMarkEvent c n (E i) j) : ℝ) : ℂ) := by
    intro n
    rw [Finset.sum_congr rfl (fun j _ => levelSymbol_step c w E hE n j),
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
    push_cast
    rfl
  refine Filter.Tendsto.congr (fun n => (hswap n).symm) ?_
  refine tendsto_finset_sum _ (fun i _ => ?_)
  refine Filter.Tendsto.const_mul _ ?_
  exact (Complex.continuous_ofReal.tendsto _).comp
    (TupleTransfer.oneLevel_intensity_limit_intervals c (E i) (hE i) (hE0 i) (hEb i) (hEi i))

end

end SymbolIntensity

end Kwon1002
