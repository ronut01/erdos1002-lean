import Kwon1002.PatternSum
import Kwon1002.SymbolLimit

/-!
# Quasi-independence on the **random** bulk at a cell pattern

`Kwon1002.PatternSum` reads the two family theorems at a fixed cell pattern.
Composing them gives the estimate a multilinear expansion actually consumes:
on the *random* bulk of §7, the joint mass of a `k`-tuple of marked cells is
the product of the one-level masses, uniformly over patterns, after summing
over the embeddings.

The composition is the three-term split

  `|P(⋂ bulk) − ∏ P(bulk)| ≤ |P(⋂ bulk) − P(⋂ det)|`
      `+ |P(⋂ det) − ∏ P(det)| + |∏ P(det) − ∏ P(bulk)|`,

whose first two terms are the two pattern theorems.  The third is the one the
plan lists as missing: it is telescoped by `PatternSum.norm_prod_sub_prod_le`
against `PatternSum.sum_emb_prod_le_prod_sum`, so that the one-level bridge
`PatternSum.exists_oneLevel_bridge` is spent once per position and the other
positions contribute their *level sums*, which are `O(1)` by the total
large-jump mass bound.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace StepQuasi

noncomputable section

open LevyExponent TupleMeasure TupleFinal FactorialRoute PatternSum

/-! ## The total mass of a marked bulk level, uniformly over targets -/

/-- The total mass of the marked bulk over all levels is `O(1)`, uniformly over
every target avoiding `(−δ, δ)`. -/
theorem exists_mass_bound (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ B : Set ℝ, (∀ y ∈ B, δ ≤ |y|) →
      (∑ j ∈ Finset.range (n + 1), unifIoo.real (bulkMarkEvent c n B j)) ≤ K := by
  classical
  obtain ⟨C₀, hC₀, hbnd⟩ := SymbolLimit.exists_tupleBigEvent_bound_uniform c
  refine ⟨C₀ / (2 * (δ / 2)), by positivity, ?_⟩
  filter_upwards [SymbolLimit.eventually_sum_bigEvent_mass c hbnd hC₀ (half_pos hδ)]
    with n hn B hB
  refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) hn
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro α hα
  refine ⟨hα.1, ?_⟩
  have h := hB _ hα.2
  have : δ / 2 < |signedMark α n j| := by linarith
  exact this

/-! ## Random-bulk quasi-independence at a pattern -/

/-- **Quasi-independence on the random bulk, at a fixed cell pattern.**

For every interval count `m`, tuple length `k`, cell count `M` and inner radius
`δ` there is one majorant tending to `0` which eventually bounds

  `∑_f |P(⋂_ℓ X_{n,f ℓ} ∈ C (u ℓ)) − ∏_ℓ P(X_{n,f ℓ} ∈ C (u ℓ))|`

for **every** cell family `C` admissible for `(m, δ)` and **every** pattern
`u`.  This is the form a multilinear expansion of a step symbol consumes. -/
theorem exists_bulk_quasi_pattern (c : ℝ) (m k M : ℕ) {δ : ℝ} (hδ : 0 < δ) (hM : 0 < M) :
    ∃ maj : ℕ → ℝ, Tendsto maj atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ C : Fin M → Set ℝ, (∀ i, MeasurableSet (C i)) →
        (∀ i, IntervalClass.IsUnionOfIntervals m (C i)) →
        (∀ i, ∀ y ∈ C i, δ ≤ |y|) → ∀ u : Fin k → Fin M,
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ))
              - ∏ ℓ, unifIoo.real (bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ))|)
          ≤ maj n := by
  classical
  obtain ⟨maj₁, h1lim, h1⟩ := PatternSum.exists_window_bridge_pattern c hδ k M hM
  obtain ⟨maj₂, h2lim, h2⟩ := PatternSum.exists_det_quasi_pattern m k M hδ hM
  obtain ⟨maj₃, h3lim, h3⟩ := PatternSum.exists_oneLevel_bridge c hδ
  obtain ⟨K, hK0, hK⟩ := exists_mass_bound c hδ
  refine ⟨fun n => maj₁ n + maj₂ n + (k : ℝ) * ((K + maj₃ n) ^ (k - 1) * maj₃ n), ?_, ?_⟩
  · have hlim : Tendsto (fun n : ℕ => (k : ℝ) * ((K + maj₃ n) ^ (k - 1) * maj₃ n)) atTop
        (𝓝 ((k : ℝ) * ((K + 0) ^ (k - 1) * 0))) := by
      exact ((((tendsto_const_nhds.add h3lim).pow (k - 1)).mul h3lim).const_mul (k : ℝ))
    simpa using ((h1lim.add h2lim).add (by simpa using hlim))
  filter_upwards [h1, h2, h3, hK] with n hn1 hn2 hn3 hnK C hCm hCi hC u
  set p : Fin k → (Finset.range (n + 1) : Finset ℕ) → ℝ :=
    fun ℓ x => unifIoo.real (bulkMarkEvent c n (C (u ℓ)) (x : ℕ)) with hp
  set q : Fin k → (Finset.range (n + 1) : Finset ℕ) → ℝ :=
    fun ℓ x => unifIoo.real (detMarkEvent n (C (u ℓ)) (x : ℕ)) with hq
  set r : Fin k → (Finset.range (n + 1) : Finset ℕ) → ℝ :=
    fun ℓ x => p ℓ x + |p ℓ x - q ℓ x| with hr
  have hp0 : ∀ ℓ x, 0 ≤ p ℓ x := fun ℓ x => measureReal_nonneg
  have hq0 : ∀ ℓ x, 0 ≤ q ℓ x := fun ℓ x => measureReal_nonneg
  have hr0 : ∀ ℓ x, 0 ≤ r ℓ x := fun ℓ x => by
    have := hp0 ℓ x; have := abs_nonneg (p ℓ x - q ℓ x); simp only [hr]; linarith
  -- the one-level bridge and the mass bound, in the coerced level currency
  have hbridge : ∀ ℓ : Fin k, (∑ x : (Finset.range (n + 1) : Finset ℕ), |p ℓ x - q ℓ x|)
      ≤ maj₃ n := by
    intro ℓ
    rw [Finset.sum_coe_sort (Finset.range (n + 1))
      (fun j => |unifIoo.real (bulkMarkEvent c n (C (u ℓ)) j)
        - unifIoo.real (detMarkEvent n (C (u ℓ)) j)|)]
    exact hn3 (C (u ℓ)) (fun y hy => hC (u ℓ) y hy)
  have hmass : ∀ ℓ : Fin k, (∑ x : (Finset.range (n + 1) : Finset ℕ), p ℓ x) ≤ K := by
    intro ℓ
    rw [Finset.sum_coe_sort (Finset.range (n + 1))
      (fun j => unifIoo.real (bulkMarkEvent c n (C (u ℓ)) j))]
    exact hnK (C (u ℓ)) (fun y hy => hC (u ℓ) y hy)
  have hrsum : ∀ ℓ : Fin k, (∑ x : (Finset.range (n + 1) : Finset ℕ), r ℓ x) ≤ K + maj₃ n := by
    intro ℓ
    have h := hbridge ℓ
    have h' := hmass ℓ
    simp only [hr, Finset.sum_add_distrib]
    linarith
  -- the third term, telescoped
  have hthird : (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
      |(∏ ℓ, q ℓ (f ℓ)) - ∏ ℓ, p ℓ (f ℓ)|)
      ≤ (k : ℝ) * ((K + maj₃ n) ^ (k - 1) * maj₃ n) := by
    have hstep : ∀ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        |(∏ ℓ, q ℓ (f ℓ)) - ∏ ℓ, p ℓ (f ℓ)|
          ≤ ∑ ℓ : Fin k, (∏ ℓ' ∈ Finset.univ.erase ℓ, r ℓ' (f ℓ')) * |q ℓ (f ℓ) - p ℓ (f ℓ)| := by
      intro f
      have h := PatternSum.norm_prod_sub_prod_le (K := ℝ) (Finset.univ : Finset (Fin k))
        (fun ℓ => q ℓ (f ℓ)) (fun ℓ => p ℓ (f ℓ)) (fun ℓ => r ℓ (f ℓ))
        (fun ℓ _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hq0 ℓ (f ℓ))]
          have h1 := abs_nonneg (p ℓ (f ℓ) - q ℓ (f ℓ))
          have h2 : q ℓ (f ℓ) - p ℓ (f ℓ) ≤ |p ℓ (f ℓ) - q ℓ (f ℓ)| := by
            rw [abs_sub_comm]; exact le_abs_self _
          simp only [hr]; linarith)
        (fun ℓ _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hp0 ℓ (f ℓ))]
          have h1 := abs_nonneg (p ℓ (f ℓ) - q ℓ (f ℓ))
          simp only [hr]; linarith)
      simpa only [Real.norm_eq_abs] using h
    refine le_trans (Finset.sum_le_sum (fun f _ => hstep f)) ?_
    rw [Finset.sum_comm]
    have hterm : ∀ ℓ : Fin k,
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
          (∏ ℓ' ∈ Finset.univ.erase ℓ, r ℓ' (f ℓ')) * |q ℓ (f ℓ) - p ℓ (f ℓ)|)
          ≤ (K + maj₃ n) ^ (k - 1) * maj₃ n := by
      intro ℓ
      set aa : Fin k → (Finset.range (n + 1) : Finset ℕ) → ℝ :=
        fun ℓ' x => if ℓ' = ℓ then |q ℓ x - p ℓ x| else r ℓ' x with haa
      have haa0 : ∀ ℓ' x, 0 ≤ aa ℓ' x := by
        intro ℓ' x
        simp only [haa]
        split
        · exact abs_nonneg _
        · exact hr0 ℓ' x
      have hprodeq : ∀ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
          (∏ ℓ' , aa ℓ' (f ℓ'))
            = (∏ ℓ' ∈ Finset.univ.erase ℓ, r ℓ' (f ℓ')) * |q ℓ (f ℓ) - p ℓ (f ℓ)| := by
        intro f
        rw [← Finset.mul_prod_erase (Finset.univ) (fun ℓ' => aa ℓ' (f ℓ')) (Finset.mem_univ ℓ)]
        have h1 : aa ℓ (f ℓ) = |q ℓ (f ℓ) - p ℓ (f ℓ)| := by simp [haa]
        have h2 : (∏ ℓ' ∈ Finset.univ.erase ℓ, aa ℓ' (f ℓ'))
            = ∏ ℓ' ∈ Finset.univ.erase ℓ, r ℓ' (f ℓ') := by
          refine Finset.prod_congr rfl (fun ℓ' hℓ' => ?_)
          have : ℓ' ≠ ℓ := Finset.ne_of_mem_erase hℓ'
          simp [haa, this]
        rw [h1, h2]
        ring
      have hQ := PatternSum.sum_emb_prod_le_prod_sum
        (ι := (Finset.range (n + 1) : Finset ℕ)) aa haa0
      simp only [hprodeq] at hQ
      refine le_trans hQ ?_
      rw [← Finset.mul_prod_erase (Finset.univ) (fun ℓ' => ∑ x, aa ℓ' x) (Finset.mem_univ ℓ)]
      have hℓ : (∑ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ x) ≤ maj₃ n := by
        have : ∀ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ x = |p ℓ x - q ℓ x| := by
          intro x; simp [haa, abs_sub_comm]
        simp only [this]
        exact hbridge ℓ
      have hrest : (∏ ℓ' ∈ Finset.univ.erase ℓ, ∑ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ' x)
          ≤ (K + maj₃ n) ^ (k - 1) := by
        have hcard : (Finset.univ.erase ℓ : Finset (Fin k)).card = k - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ ℓ), Finset.card_univ, Fintype.card_fin]
        calc (∏ ℓ' ∈ Finset.univ.erase ℓ, ∑ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ' x)
            ≤ ∏ _ℓ' ∈ Finset.univ.erase ℓ, (K + maj₃ n) := by
              refine Finset.prod_le_prod (fun ℓ' _ => Finset.sum_nonneg (fun x _ => haa0 ℓ' x))
                (fun ℓ' hℓ' => ?_)
              have hne : ℓ' ≠ ℓ := Finset.ne_of_mem_erase hℓ'
              have : ∀ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ' x = r ℓ' x := by
                intro x; simp [haa, hne]
              simp only [this]
              exact hrsum ℓ'
          _ = (K + maj₃ n) ^ (k - 1) := by rw [Finset.prod_const, hcard]
      have hmaj0 : 0 ≤ maj₃ n :=
        le_trans (Finset.sum_nonneg (fun x _ => abs_nonneg _)) (hbridge ℓ)
      have hprod0 : (0:ℝ) ≤ ∏ ℓ' ∈ Finset.univ.erase ℓ,
          ∑ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ' x :=
        Finset.prod_nonneg (fun ℓ' _ => Finset.sum_nonneg (fun x _ => haa0 ℓ' x))
      calc (∑ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ x)
            * ∏ ℓ' ∈ Finset.univ.erase ℓ, ∑ x : (Finset.range (n + 1) : Finset ℕ), aa ℓ' x
          ≤ maj₃ n * (K + maj₃ n) ^ (k - 1) := mul_le_mul hℓ hrest hprod0 hmaj0
        _ = (K + maj₃ n) ^ (k - 1) * maj₃ n := mul_comm _ _
    refine le_trans (Finset.sum_le_sum (fun ℓ _ => hterm ℓ)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- assembling the three terms
  have htri : ∀ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
      |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ))
        - ∏ ℓ, p ℓ (f ℓ)|
        ≤ |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ))
            - unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))|
          + |unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))
              - ∏ ℓ, q ℓ (f ℓ)|
          + |(∏ ℓ, q ℓ (f ℓ)) - ∏ ℓ, p ℓ (f ℓ)| := by
    intro f
    calc |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ)) - ∏ ℓ, p ℓ (f ℓ)|
        ≤ |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ))
            - unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))|
          + |unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ)) - ∏ ℓ, p ℓ (f ℓ)| := by
          have := abs_sub_le (unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ)))
            (unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))) (∏ ℓ, p ℓ (f ℓ))
          exact this
      _ ≤ _ := by
          have := abs_sub_le (unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ)))
            (∏ ℓ, q ℓ (f ℓ)) (∏ ℓ, p ℓ (f ℓ))
          linarith
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (Fin k ↪ (Finset.range (n + 1) : Finset ℕ))))
    (fun f _ => htri f)
  simp only [Finset.sum_add_distrib] at hsum
  have h2' := hn2 C hCm hCi hC u
  have h1' := hn1 C hC u
  refine le_trans hsum ?_
  have hq' : (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
      |unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ)) - ∏ ℓ, q ℓ (f ℓ)|)
      ≤ maj₂ n := h2'
  linarith [hthird]

end

end StepQuasi

end Kwon1002
