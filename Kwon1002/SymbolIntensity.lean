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

**Record correction (both steps are now written).**  Both are carried out in
`Kwon1002/SymbolLimit.lean`: the window approximation is
`SymbolLimit.exists_step_approx` together with `SymbolLimit.norm_levelSymbol_sub_le`,
and the two tails are `SymbolLimit.eventually_sum_bigEvent_mass` (with the
constant of `SymbolLimit.exists_tupleBigEvent_bound_uniform`, which exhibits the
`ε`-dependence `C₀/(8ε)` that `FactorialRoute.exists_tupleBigEvent_bound` hides
inside an existential) and `SymbolLimit.tendsto_integral_far_density`.
`SymbolLimit.sum_mu_tendsto` **is** `hp1`, axiom-clean, and
`SymbolLimit.largeSum_charFun_limit_of_hqi` records inside Lean that `hqi` is
then the only remaining input to `CorFinal.largeSum_charFun_limit`.
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


/-! ## The window mass, uniformly in `n`

The second half of `hp1` — the approximation and the tail — is priced against the
total mass the levels put on the truncation window.  That mass is bounded
uniformly in `n`, with a constant that decays in the truncation level, and the
bound is the mass analogue of `LayerAssembly.sum_norm_mu_le`: only `O(L)` levels
can contribute (the Lamé cap) and each contributes `O(1/L)` (display (15)). -/

/-- **The total large-jump mass is `O(1)` uniformly in `n`, with the constant of
`FactorialRoute.exists_tupleBigEvent_bound`.**  Since that constant is
`C₀/(8ε)`, the same statement read at truncation level `R` in place of `ε` gives
`∑_{j ≤ n} P(|X_{n,j}| > R, j ∈ J_n) ≤ C₀/(2R)`, which is the tail estimate
`hp1` needs; and read at `ε` it is the window mass the approximation error is
multiplied by. -/
theorem sum_bigEvent_mass_le (c ε : ℝ) {C : ℝ} (_hC : 0 < C) {n : ℕ} (hn : 1 ≤ n)
    (hL : 3 ≤ Lnorm n)
    (hbnd : ∀ S : Finset ℕ,
      unifIoo.real (FactorialRoute.tupleBigEvent c ε n S) ≤ (C / Lnorm n) ^ S.card) :
    (∑ j ∈ Finset.range (n + 1), unifIoo.real (FactorialRoute.bigEvent c ε n j))
      ≤ 4 * C := by
  classical
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  have hsingle : ∀ j : ℕ, FactorialRoute.tupleBigEvent c ε n ({j} : Finset ℕ)
      = FactorialRoute.bigEvent c ε n j := by
    intro j
    simp [FactorialRoute.tupleBigEvent]
  set M : ℕ := min (n + 1) (FactorialRoute.lameCap n) with hM
  have hcap : (∑ j ∈ Finset.range (n + 1), unifIoo.real (FactorialRoute.bigEvent c ε n j))
      = ∑ j ∈ Finset.range M, unifIoo.real (FactorialRoute.bigEvent c ε n j) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro j hj
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _))
    · intro j hjmem hjnot
      have hjn : j < n + 1 := Finset.mem_range.mp hjmem
      have hjc : FactorialRoute.lameCap n ≤ j := by
        simp only [hM, Finset.mem_range, not_lt] at hjnot
        omega
      rw [Measure.real,
        FactorialRoute.bigEvent_null_of_large c ε n j hn (FactorialRoute.lameCap_lt hjc),
        ENNReal.toReal_zero]
  rw [hcap]
  have hterm : ∀ j ∈ Finset.range M,
      unifIoo.real (FactorialRoute.bigEvent c ε n j) ≤ C / Lnorm n := by
    intro j _
    have h := hbnd ({j} : Finset ℕ)
    rw [hsingle j, Finset.card_singleton, pow_one] at h
    exact h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hMle : (M : ℝ) ≤ 4 * Lnorm n :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (min_le_right (n + 1) (FactorialRoute.lameCap n)))
      (FactorialRoute.lameCap_le hL)
  have hCnn : (0:ℝ) ≤ C / Lnorm n := by positivity
  refine le_trans (mul_le_mul_of_nonneg_right hMle hCnn) (le_of_eq ?_)
  field_simp

end

end SymbolIntensity

end Kwon1002
