import Kwon1002.Section5Join

/-!
# The multi-set (per-level) tuple factorization

`Kwon1002/FactorialSeries.lean` records that the layer limit of the factorial
route needs the *multi-set* tuple statement — the tuple event carrying a
**different** set at each level — and that
`LevyExponent.tuple_measure_convergence`, which fixes one `B` at every level,
does not supply it.  That reading of `tuple_measure_convergence` is right.  The
inference drawn from it, that the tree contains no per-level statement "in any
form", is **wrong at Proposition 4.1**, and this module records the correction.

## Proposition 4.1 is already per-level

`Kwon1002.prop_4_1_marked_factorization` quantifies over
`F : ℕ → ℕ → ℝ → ℂ` with `∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)` and bounds

  `‖∫₀¹ ∏_{ℓ<r} F ℓ (a_{j_ℓ+1}(α), θ_{j_ℓ}(α)) dα − ∏_{ℓ<r} stationaryMean (F ℓ)‖`.

The symbol family is indexed by the level slot `ℓ`, so a *different* symbol at
each level is already what the statement says; the diagonal `F ℓ = G` is a
special case, not the general one.  `example`s at the head of the file below
check this against the canonical name rather than asserting it.

## What was actually missing, and is supplied here

Proposition 4.1 is stated for symbols in display (24)'s class `P_D(L)`.  An
indicator is provably not in that class, and `Kwon1002/Section5Join.lean` closes
that gap **at one level only** (`oneLevel_indicator_sandwich`,
`oneLevel_transfer`).  The multi-level passage from the class to indicators is
what this module adds:

* `abs_prod_range_sub_prod_range_le` — the telescoping bound
  `|∏ a − ∏ b| ≤ K^r ∑ |aᵢ − bᵢ|` for factors bounded by `K ≥ 1`.
* `abs_stationaryMeanR_le` — `|stationaryMeanR f| ≤ K` from `|f| ≤ K`.
* `multiLevel_indCut_factorization` — Proposition 4.1 read at the **digit-cut
  indicator** of a per-level section family, on good tuples, with the sandwich
  cost `Γ = (4m+2)·2δ + 2η(N,δ)` paid once per level.
* `multiLevel_indFull_factorization` — the same with the digit cut removed,
  paying the two digit tails of `Section5Join` once per level.
* `schedDelta'`, `schedDeg'`, `schedCut'`, `sched_admissible'` — the
  `Section5Join` schedule at a free exponent `s` (the fixed exponent `2` there
  is tuned to the single-level budget `o(1/L)`; `r` levels need `o(L^{-r})`,
  so the exponent has to move and `D` with it).
* `eventually_exists_goodTuple` — **non-vacuity**: `J_n` eventually carries a
  good `r`-tuple.  `Kwon1002/OneLevelLaw.lean` establishes this only at `r = 1`,
  where (25) and (26) are vacuous; for `r ≥ 2` nothing in the tree checked that
  the gap and resonance conditions can be met at once.  Without it every
  `GoodTuple n r`-quantified statement of §4 is empty for `r ≥ 2`.
* `multiLevel_transfer` — the **multi-set tuple factorization**: for every
  `r`, every interval count `m` and every rate `A`, uniformly over good tuples
  in `J_n` and over per-level section families,

    `|∫₀¹ ∏_{ℓ<r} 1_{B_ℓ}(a_{j_ℓ+1}, θ_{j_ℓ}) − ∏_{ℓ<r} stationaryMeanR 1_{B_ℓ}|
        ≤ C·L^{−A}`.

  This is the `r`-level analogue of `Section5Join.oneLevel_transfer`, which is
  its `r = 1` case up to the `L·` normalisation.

Nothing here is sorried and nothing here consumes a `sorry`.

## What this does *not* close

`multiLevel_transfer` is the *factorization* half of the multi-set tuple limit.
The limit itself additionally needs, and this module does not supply:

1. the per-level intensity for the **complex** symbol
   `x ↦ (e^{itx} − 1)1{|x| > ε}` rather than an indicator (a simple-function
   approximation inside the truncation window, plus its tail);
2. the count of **non-good** tuples, `Kwon1002.nonGood_tuple_count`, still
   sorried in `Kwon1002/Section4.lean`;
3. the `r`-level index-set bridge between the random bulk
   `Marks.bulkIndices c α n` and the deterministic `bulkJ n`
   (`bulk_window_bridge_oneLevel` is proved at one level;
   `TupleFinal.bulk_window_bridge_tuple` is not);
4. the passage from the per-level products to `Λ̂^k/k!`, i.e. the elementary
   symmetric / power sum comparison.

These four are named, not hidden, and none of them is closed below.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology

namespace Kwon1002

namespace MultiLevel

open Section5Join

noncomputable section

/-! ## Proposition 4.1 is per-level: the machine check

The two `example`s below are the correction of the record.  The first exhibits
the canonical Proposition 4.1 as a statement about a symbol family indexed by
the level slot; the second instantiates it at a genuinely per-level family
built from an arbitrary sequence of sets, which is the shape a multi-set tuple
statement needs. -/

/-- **Proposition 4.1 already quantifies over a per-level symbol family.**
The `F` of `Kwon1002.prop_4_1_marked_factorization` has type `ℕ → ℕ → ℝ → ℂ`
and its hypothesis is `∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)` — one membership
per level slot, not one symbol for all slots. -/
example (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) :=
  prop_4_1_marked_factorization r D A hD hA

/-- **Proposition 4.1 at a per-level family, spelled out.**  Given one symbol
`G ℓ` per level, each in the class, the factorization holds with the product of
the *individual* stationary means on the right.  Nothing in the statement ties
the levels together. -/
theorem prop_4_1_perLevel (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ G : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (G ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, G ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (G ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) :=
  prop_4_1_marked_factorization r D A hD hA

/-! ## A telescoping bound for finite products -/

/-- `|∏_{i<r} aᵢ − ∏_{i<r} bᵢ| ≤ K^r ∑_{i<r} |aᵢ − bᵢ|` when every factor is
bounded by `K ≥ 1`.  The `r`-level analogue of the pointwise sandwich: at one
level the majorant/minorant pair is one-sided, at `r` levels the product of
signed factors is not, so the comparison has to be made term by term. -/
lemma abs_prod_range_sub_prod_range_le (a b : ℕ → ℝ) {K : ℝ} (hK : 1 ≤ K)
    (ha : ∀ i, |a i| ≤ K) (hb : ∀ i, |b i| ≤ K) (r : ℕ) :
    |∏ i ∈ Finset.range r, a i - ∏ i ∈ Finset.range r, b i|
      ≤ K ^ r * ∑ i ∈ Finset.range r, |a i - b i| := by
  have hK0 : (0:ℝ) ≤ K := le_trans zero_le_one hK
  have hpa : ∀ s : Finset ℕ, |∏ i ∈ s, a i| ≤ K ^ s.card := by
    intro s
    rw [Finset.abs_prod]
    calc ∏ i ∈ s, |a i| ≤ ∏ _i ∈ s, K :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ha i)
      _ = K ^ s.card := by rw [Finset.prod_const]
  have hpb : ∀ s : Finset ℕ, |∏ i ∈ s, b i| ≤ K ^ s.card := by
    intro s
    rw [Finset.abs_prod]
    calc ∏ i ∈ s, |b i| ≤ ∏ _i ∈ s, K :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hb i)
      _ = K ^ s.card := by rw [Finset.prod_const]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    have hid : (∏ i ∈ Finset.range r, a i) * a r - (∏ i ∈ Finset.range r, b i) * b r
        = (∏ i ∈ Finset.range r, a i) * (a r - b r)
          + ((∏ i ∈ Finset.range r, a i) - ∏ i ∈ Finset.range r, b i) * b r := by ring
    rw [hid]
    have h1 : |(∏ i ∈ Finset.range r, a i) * (a r - b r)| ≤ K ^ r * |a r - b r| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa [Finset.card_range] using hpa (Finset.range r)) (abs_nonneg _)
    have h2 : |((∏ i ∈ Finset.range r, a i) - ∏ i ∈ Finset.range r, b i) * b r|
        ≤ (K ^ r * ∑ i ∈ Finset.range r, |a i - b i|) * K := by
      rw [abs_mul]
      exact mul_le_mul ih (hb r) (abs_nonneg _) (by positivity)
    have hsum0 : (0:ℝ) ≤ ∑ i ∈ Finset.range r, |a i - b i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have hKr : K ^ r ≤ K ^ (r + 1) := by
      calc K ^ r = K ^ r * 1 := by ring
        _ ≤ K ^ r * K := by exact mul_le_mul_of_nonneg_left hK (by positivity)
        _ = K ^ (r + 1) := by ring
    calc |(∏ i ∈ Finset.range r, a i) * (a r - b r)
            + ((∏ i ∈ Finset.range r, a i) - ∏ i ∈ Finset.range r, b i) * b r|
        ≤ |(∏ i ∈ Finset.range r, a i) * (a r - b r)|
            + |((∏ i ∈ Finset.range r, a i) - ∏ i ∈ Finset.range r, b i) * b r| :=
          abs_add_le _ _
      _ ≤ K ^ r * |a r - b r| + (K ^ r * ∑ i ∈ Finset.range r, |a i - b i|) * K := by
          linarith
      _ ≤ K ^ (r+1) * |a r - b r| + K ^ (r+1) * ∑ i ∈ Finset.range r, |a i - b i| := by
          have e1 : K ^ r * |a r - b r| ≤ K ^ (r+1) * |a r - b r| :=
            mul_le_mul_of_nonneg_right hKr (abs_nonneg _)
          have e2 : (K ^ r * ∑ i ∈ Finset.range r, |a i - b i|) * K
              = K ^ (r+1) * ∑ i ∈ Finset.range r, |a i - b i| := by ring
          linarith [e2]
      _ = K ^ (r+1) * ((∑ i ∈ Finset.range r, |a i - b i|) + |a r - b r|) := by ring

/-! ## Integrability of a per-level product, and the integrated telescoping -/

/-- A per-level product of bounded measurable symbols, read at a tuple, is
integrable on the fundamental interval. -/
lemma integrableOn_prod_symbol_comp {f : ℕ → ℕ → ℝ → ℝ} {K : ℝ} (_hK : 0 ≤ K)
    (hfm : ∀ ℓ a, Measurable (f ℓ a)) (hfb : ∀ ℓ a θ, |f ℓ a θ| ≤ K)
    (n r : ℕ) (j : ℕ → ℕ) :
    IntegrableOn (fun α : ℝ => ∏ ℓ ∈ Finset.range r,
        f ℓ (digit α (j ℓ)) (theta α n (j ℓ))) (Ioo (0:ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := K ^ r) (by simp [Real.volume_Ioo])
    ((Finset.measurable_prod _ fun ℓ _ =>
      measurable_symbol_comp (hfm ℓ) n (j ℓ)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun α => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ ℓ ∈ Finset.range r, |f ℓ (digit α (j ℓ)) (theta α n (j ℓ))|
      ≤ ∏ _ℓ ∈ Finset.range r, K :=
        Finset.prod_le_prod (fun ℓ _ => abs_nonneg _) (fun ℓ _ => hfb _ _ _)
    _ = K ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- **The integrated telescoping bound.**  Replacing a per-level symbol family
by another, level by level, costs the sum of the level-`ℓ` `L¹` gaps, weighted
by `K^r`. -/
lemma abs_integral_prod_sub_prod_le {f g : ℕ → ℕ → ℝ → ℝ} {K : ℝ} (hK : 1 ≤ K)
    (hfm : ∀ ℓ a, Measurable (f ℓ a)) (hgm : ∀ ℓ a, Measurable (g ℓ a))
    (hfb : ∀ ℓ a θ, |f ℓ a θ| ≤ K) (hgb : ∀ ℓ a θ, |g ℓ a θ| ≤ K)
    (n r : ℕ) (j : ℕ → ℕ) :
    |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
          f ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        - ∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
            g ℓ (digit α (j ℓ)) (theta α n (j ℓ))|
      ≤ K ^ r * ∑ ℓ ∈ Finset.range r,
          ∫ α in Ioo (0:ℝ) 1, |f ℓ (digit α (j ℓ)) (theta α n (j ℓ))
              - g ℓ (digit α (j ℓ)) (theta α n (j ℓ))| := by
  have hK0 : (0:ℝ) ≤ K := le_trans zero_le_one hK
  have hIf := integrableOn_prod_symbol_comp hK0 hfm hfb n r j
  have hIg := integrableOn_prod_symbol_comp hK0 hgm hgb n r j
  -- each level's `L¹` gap is integrable
  have hIgap : ∀ ℓ : ℕ, IntegrableOn
      (fun α : ℝ => |f ℓ (digit α (j ℓ)) (theta α n (j ℓ))
          - g ℓ (digit α (j ℓ)) (theta α n (j ℓ))|) (Ioo (0:ℝ) 1) := by
    intro ℓ
    have h1 : IntegrableOn (fun α : ℝ => f ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        (Ioo (0:ℝ) 1) := integrableOn_symbol_comp (hfm ℓ) (hfb ℓ) n (j ℓ)
    have h2 : IntegrableOn (fun α : ℝ => g ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        (Ioo (0:ℝ) 1) := integrableOn_symbol_comp (hgm ℓ) (hgb ℓ) n (j ℓ)
    exact (h1.sub h2).abs
  have hsum : IntegrableOn (fun α : ℝ => K ^ r * ∑ ℓ ∈ Finset.range r,
      |f ℓ (digit α (j ℓ)) (theta α n (j ℓ))
        - g ℓ (digit α (j ℓ)) (theta α n (j ℓ))|) (Ioo (0:ℝ) 1) :=
    (integrable_finset_sum _ (fun ℓ _ => hIgap ℓ)).const_mul _
  have hpt : ∀ α : ℝ, |(∏ ℓ ∈ Finset.range r, f ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        - ∏ ℓ ∈ Finset.range r, g ℓ (digit α (j ℓ)) (theta α n (j ℓ))|
      ≤ K ^ r * ∑ ℓ ∈ Finset.range r, |f ℓ (digit α (j ℓ)) (theta α n (j ℓ))
          - g ℓ (digit α (j ℓ)) (theta α n (j ℓ))| := fun α =>
    abs_prod_range_sub_prod_range_le
      (fun i => f i (digit α (j i)) (theta α n (j i)))
      (fun i => g i (digit α (j i)) (theta α n (j i))) hK
      (fun i => hfb _ _ _) (fun i => hgb _ _ _) r
  rw [← integral_sub hIf hIg]
  refine le_trans (abs_integral_le_integral_abs) ?_
  refine le_trans (integral_mono ((hIf.sub hIg).abs) hsum hpt) (le_of_eq ?_)
  rw [integral_const_mul, integral_finset_sum _ (fun ℓ _ => hIgap ℓ)]

/-! ## The stationary mean of a bounded symbol is bounded -/

/-- `|stationaryMeanR f| ≤ K` whenever `|f| ≤ K`: the stationary mean averages
against a probability measure in the digit and against Lebesgue on the cell. -/
lemma abs_stationaryMeanR_le {f : ℕ → ℝ → ℝ} {K : ℝ} (hK : ∀ a θ, |f a θ| ≤ K) :
    |stationaryMeanR f| ≤ K := by
  have hK0 : (0:ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0 0)
  rw [stationaryMeanR_eq]
  have hbd : ∀ x : ℝ, ‖innerMean f (digit x 0)‖ ≤ K := fun x => by
    rw [Real.norm_eq_abs]; exact abs_innerMean_le_of_bound hK _
  have h := norm_integral_le_of_norm_le_const (μ := Erdos1002.gaussMeasure)
    (C := K) (f := fun x : ℝ => innerMean f (digit x 0))
    (Filter.Eventually.of_forall hbd)
  rw [Real.norm_eq_abs] at h
  have hmass : (Erdos1002.gaussMeasure : Measure ℝ).real Set.univ = 1 := by
    simp [Measure.real, measure_univ]
  calc |∫ x, innerMean f (digit x 0) ∂Erdos1002.gaussMeasure|
      ≤ K * (Erdos1002.gaussMeasure : Measure ℝ).real Set.univ := h
    _ = K := by rw [hmass, mul_one]


/-! ## The multi-set factorization at the digit-cut indicator

Proposition 4.1 is applied *once*, at `r` levels, to the per-level **majorant**
family; the passage from the majorant to the indicator is then made level by
level through the integrated telescoping bound, paying the one-level cost
`Γ = (4m+2)·2δ + 2η(N,δ)` of `Section5Join.stationaryMeanR_gap_le` once per
level.  Nothing in the argument couples the levels, which is exactly the
content of Proposition 4.1 being per-level. -/

set_option maxHeartbeats 1000000 in
/-- **The multi-set tuple factorization at the digit-cut indicator.**

For a good tuple `j` in the deterministic bulk and a **per-level** family of
`θ`-section families `Bs ℓ`, each of whose sections is a union of at most `m`
intervals, the `α`-average of the product of the level indicators factorizes
into the product of their stationary means, up to `C·(L^{-A} + Γ)`.

`Γ = (4m+2)·2δ + 2η(N,δ)` is the Selberg bracket gap; it is paid once per
level, and the `A` is Proposition 4.1's, so it may be taken as large as
wanted. -/
theorem multiLevel_indCut_factorization (r m : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ (Acut N : ℕ) (δ : ℝ), 0 < δ → Selberg.farTail N δ ≤ 1 →
      ∀ Bs : ℕ → ℕ → Set ℝ, (∀ ℓ a, MeasurableSet (Bs ℓ a)) →
        (∀ ℓ a, IntervalClass.IsUnionOfIntervals m (Bs ℓ a)) →
        (Acut : ℝ) ≤ (Lnorm n) ^ D → (N : ℝ) ≤ (Lnorm n) ^ D →
        ((Acut : ℝ) + 1) * ((2 * (N : ℝ) + 1) * (1 + Selberg.farTail N δ))
            ≤ (Lnorm n) ^ D →
        |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
              indCut Acut (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMeanR (indCut Acut (Bs ℓ))|
          ≤ C * ((Lnorm n) ^ (-A)
              + ((4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ)) := by
  classical
  obtain ⟨C₁, hC₁, hev₁⟩ := prop_4_1_marked_factorization r D A hD hA
  obtain ⟨C₂, hC₂, hev₂⟩ := oneLevel_indicator_sandwich D A hD hA
  obtain ⟨C₃, hC₃, hev₃⟩ := OneLevelLaw.oneLevel_joint_law D A hD hA
  refine ⟨C₁ + (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2), by positivity, ?_⟩
  filter_upwards [hev₁, hev₂, hev₃] with n hn₁ hn₂ hn₃
  intro j hj Acut N δ hδ hfar1 Bs hBsm hBsi hAle hNle hbud
  set L : ℝ := Lnorm n with hL
  set Γ : ℝ := (4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ with hΓ
  have hfar0 : 0 ≤ Selberg.farTail N δ := Selberg.farTail_nonneg N δ
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hRA : (0:ℝ) ≤ L ^ (-A) := Real.rpow_nonneg (Lnorm_nonneg n) _
  have hjJ : ∀ ℓ, ℓ < r → j ℓ ∈ bulkJ n := hj.1.2.2
  -- the three per-level families
  set M : ℕ → ℕ → ℝ → ℝ := fun ℓ => majCut N Acut δ (Bs ℓ) with hM
  set I : ℕ → ℕ → ℝ → ℝ := fun ℓ => indCut Acut (Bs ℓ) with hI
  set mn : ℕ → ℕ → ℝ → ℝ := fun ℓ => minCut N Acut δ (Bs ℓ) with hmn
  have hMb : ∀ ℓ a θ, |M ℓ a θ| ≤ 2 := fun ℓ a θ =>
    (abs_majCut_le N Acut δ (Bs ℓ) a θ).trans (by linarith)
  have hIb : ∀ ℓ a θ, |I ℓ a θ| ≤ 2 := fun ℓ a θ =>
    (abs_indCut_le Acut (Bs ℓ) a θ).trans (by norm_num)
  have hMm : ∀ ℓ a, Measurable (M ℓ a) := fun ℓ a => measurable_majCut N Acut δ (Bs ℓ) a
  have hIm : ∀ ℓ a, Measurable (I ℓ a) := fun ℓ a => measurable_indCut Acut (hBsm ℓ) a
  -- Step 1: Proposition 4.1 at `r` levels, on the majorant family
  have hstep1 : |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
        M ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      - ∏ ℓ ∈ Finset.range r, stationaryMeanR (M ℓ)| ≤ C₁ * L ^ (-A) := by
    have hF : ∀ ℓ, ℓ < r → IsInPD D L (fun a θ => ((M ℓ a θ : ℝ) : ℂ)) := fun ℓ _ =>
      isInPD_majCut D L Acut N δ (Bs ℓ) hAle hNle hbud
    have h := hn₁ j hj (fun ℓ a θ => ((M ℓ a θ : ℝ) : ℂ)) hF
    have e1 : (fun α : ℝ => ∏ ℓ ∈ Finset.range r,
          ((M ℓ (digit α (j ℓ)) (theta α n (j ℓ)) : ℝ) : ℂ))
        = fun α : ℝ => ((∏ ℓ ∈ Finset.range r,
            M ℓ (digit α (j ℓ)) (theta α n (j ℓ)) : ℝ) : ℂ) := by
      funext α; push_cast; ring
    have e2 : ∀ ℓ, stationaryMean (fun a θ => ((M ℓ a θ : ℝ) : ℂ))
        = ((stationaryMeanR (M ℓ) : ℝ) : ℂ) := fun ℓ => stationaryMean_ofReal (M ℓ)
    rw [e1] at h
    simp only [e2] at h
    rw [integral_complex_ofReal, ← Complex.ofReal_prod, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  -- Step 2: the level-`ℓ` `L¹` gap between the indicator and the majorant
  have hgapL : ∀ ℓ, ℓ < r →
      (∫ α in Ioo (0:ℝ) 1, |I ℓ (digit α (j ℓ)) (theta α n (j ℓ))
          - M ℓ (digit α (j ℓ)) (theta α n (j ℓ))|)
        ≤ Γ + (C₂ + C₃) * L ^ (-A) := by
    intro ℓ hℓ
    have hIle : ∀ a θ, I ℓ a θ ≤ M ℓ a θ := fun a θ => indCut_le_majCut hδ (Bs ℓ) a θ
    have hII : IntegrableOn (fun α : ℝ => I ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        (Ioo (0:ℝ) 1) := integrableOn_symbol_comp (hIm ℓ) (hIb ℓ) n (j ℓ)
    have hMI : IntegrableOn (fun α : ℝ => M ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        (Ioo (0:ℝ) 1) := integrableOn_symbol_comp (hMm ℓ) (hMb ℓ) n (j ℓ)
    have habs : (∫ α in Ioo (0:ℝ) 1, |I ℓ (digit α (j ℓ)) (theta α n (j ℓ))
          - M ℓ (digit α (j ℓ)) (theta α n (j ℓ))|)
        = (∫ α in Ioo (0:ℝ) 1, M ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∫ α in Ioo (0:ℝ) 1, I ℓ (digit α (j ℓ)) (theta α n (j ℓ)) := by
      rw [← integral_sub hMI hII]
      refine integral_congr_ae ?_
      filter_upwards with α
      rw [abs_of_nonpos (by linarith [hIle (digit α (j ℓ)) (theta α n (j ℓ))])]
      ring
    rw [habs]
    -- upper bound on the majorant average, from the one-level law
    have hup : (∫ α in Ioo (0:ℝ) 1, M ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        ≤ stationaryMeanR (M ℓ) + C₃ * L ^ (-A) := by
      have h := hn₃ (j ℓ) (hjJ ℓ hℓ) (fun a θ => ((M ℓ a θ : ℝ) : ℂ))
        (isInPD_majCut D L Acut N δ (Bs ℓ) hAle hNle hbud)
      rw [stationaryMean_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] at h
      have := (abs_le.mp h).2
      linarith
    -- lower bound on the indicator average, from the sandwich
    have hlow : stationaryMeanR (mn ℓ) - C₂ * L ^ (-A)
        ≤ ∫ α in Ioo (0:ℝ) 1, I ℓ (digit α (j ℓ)) (theta α n (j ℓ)) :=
      (hn₂ (j ℓ) (hjJ ℓ hℓ) Acut N δ hδ (Bs ℓ) (hBsm ℓ) hAle hNle hbud).1
    have hgap : stationaryMeanR (M ℓ) - stationaryMeanR (mn ℓ) ≤ Γ :=
      stationaryMeanR_gap_le (m := m) N Acut hδ (Bs ℓ) (hBsi ℓ)
    linarith
  -- Step 3: the integrated telescoping, indicator against majorant
  have hstep3 : |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
        I ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      - ∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
          M ℓ (digit α (j ℓ)) (theta α n (j ℓ))|
      ≤ (2:ℝ) ^ r * (r * (Γ + (C₂ + C₃) * L ^ (-A))) := by
    refine le_trans (abs_integral_prod_sub_prod_le (K := 2) (by norm_num)
      hIm hMm hIb hMb n r j) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ ℓ ∈ Finset.range r, ∫ α in Ioo (0:ℝ) 1,
            |I ℓ (digit α (j ℓ)) (theta α n (j ℓ))
              - M ℓ (digit α (j ℓ)) (theta α n (j ℓ))|
        ≤ ∑ _ℓ ∈ Finset.range r, (Γ + (C₂ + C₃) * L ^ (-A)) :=
          Finset.sum_le_sum fun ℓ hℓ => hgapL ℓ (Finset.mem_range.mp hℓ)
      _ = r * (Γ + (C₂ + C₃) * L ^ (-A)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Step 4: the stationary side, indicator against majorant
  have hstep4 : |(∏ ℓ ∈ Finset.range r, stationaryMeanR (I ℓ))
      - ∏ ℓ ∈ Finset.range r, stationaryMeanR (M ℓ)| ≤ (2:ℝ) ^ r * (r * Γ) := by
    have hSI : ∀ ℓ, |stationaryMeanR (I ℓ)| ≤ 2 := fun ℓ =>
      abs_stationaryMeanR_le (hIb ℓ)
    have hSM : ∀ ℓ, |stationaryMeanR (M ℓ)| ≤ 2 := fun ℓ =>
      abs_stationaryMeanR_le (hMb ℓ)
    refine le_trans (abs_prod_range_sub_prod_range_le
      (fun ℓ => stationaryMeanR (I ℓ)) (fun ℓ => stationaryMeanR (M ℓ))
      (by norm_num : (1:ℝ) ≤ 2) hSI hSM r) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hterm : ∀ ℓ, |stationaryMeanR (I ℓ) - stationaryMeanR (M ℓ)| ≤ Γ := by
      intro ℓ
      have hmI : stationaryMeanR (mn ℓ) ≤ stationaryMeanR (I ℓ) :=
        stationaryMeanR_mono (K := 1 + Selberg.farTail N δ)
          (measurable_minCut N Acut δ (Bs ℓ)) (hIm ℓ)
          (abs_minCut_le N Acut δ (Bs ℓ))
          (fun a θ => (abs_indCut_le Acut (Bs ℓ) a θ).trans (by linarith))
          (fun a θ => minCut_le_indCut hδ (Bs ℓ) a θ)
      have hIM : stationaryMeanR (I ℓ) ≤ stationaryMeanR (M ℓ) :=
        stationaryMeanR_mono (K := 1 + Selberg.farTail N δ) (hIm ℓ)
          (measurable_majCut N Acut δ (Bs ℓ))
          (fun a θ => (abs_indCut_le Acut (Bs ℓ) a θ).trans (by linarith))
          (abs_majCut_le N Acut δ (Bs ℓ))
          (fun a θ => indCut_le_majCut hδ (Bs ℓ) a θ)
      have hgap : stationaryMeanR (M ℓ) - stationaryMeanR (mn ℓ) ≤ Γ :=
        stationaryMeanR_gap_le (m := m) N Acut hδ (Bs ℓ) (hBsi ℓ)
      rw [abs_le]
      constructor <;> linarith
    calc ∑ ℓ ∈ Finset.range r, |stationaryMeanR (I ℓ) - stationaryMeanR (M ℓ)|
        ≤ ∑ _ℓ ∈ Finset.range r, Γ := Finset.sum_le_sum fun ℓ _ => hterm ℓ
      _ = r * Γ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- assembly
  have htri : |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
        I ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      - ∏ ℓ ∈ Finset.range r, stationaryMeanR (I ℓ)|
      ≤ (2:ℝ) ^ r * (r * (Γ + (C₂ + C₃) * L ^ (-A))) + C₁ * L ^ (-A)
        + (2:ℝ) ^ r * (r * Γ) := by
    have h1 := abs_sub_le
      (∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r, I ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      (∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r, M ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      (∏ ℓ ∈ Finset.range r, stationaryMeanR (I ℓ))
    have h2 := abs_sub_le
      (∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r, M ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      (∏ ℓ ∈ Finset.range r, stationaryMeanR (M ℓ))
      (∏ ℓ ∈ Finset.range r, stationaryMeanR (I ℓ))
    have h3 : |(∏ ℓ ∈ Finset.range r, stationaryMeanR (M ℓ))
        - ∏ ℓ ∈ Finset.range r, stationaryMeanR (I ℓ)| ≤ (2:ℝ) ^ r * (r * Γ) := by
      rw [abs_sub_comm]; exact hstep4
    linarith
  refine le_trans htri ?_
  have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
  have h2r : (0:ℝ) < (2:ℝ) ^ r := by positivity
  have hexp : (C₁ + (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2)) * (L ^ (-A) + Γ)
      = C₁ * L ^ (-A) + C₁ * Γ
        + (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2) * L ^ (-A)
        + (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2) * Γ := by ring
  rw [hexp]
  have e1 : (2:ℝ) ^ r * (r * ((C₂ + C₃) * L ^ (-A)))
      ≤ (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2) * L ^ (-A) := by
    have key : (r:ℝ) * (C₂ + C₃) ≤ ((r:ℝ) + 1) * (C₂ + C₃ + 2) := by nlinarith
    have hl : (2:ℝ) ^ r * (r * ((C₂ + C₃) * L ^ (-A)))
        = ((2:ℝ) ^ r * L ^ (-A)) * ((r:ℝ) * (C₂ + C₃)) := by ring
    have hrr : (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2) * L ^ (-A)
        = ((2:ℝ) ^ r * L ^ (-A)) * (((r:ℝ) + 1) * (C₂ + C₃ + 2)) := by ring
    rw [hl, hrr]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  have e2 : (2:ℝ) ^ r * (r * Γ) + (2:ℝ) ^ r * (r * Γ)
      ≤ (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2) * Γ := by
    have key : 2 * (r:ℝ) ≤ ((r:ℝ) + 1) * (C₂ + C₃ + 2) := by nlinarith
    have hl : (2:ℝ) ^ r * (r * Γ) + (2:ℝ) ^ r * (r * Γ)
        = ((2:ℝ) ^ r * Γ) * (2 * (r:ℝ)) := by ring
    have hrr : (2:ℝ) ^ r * (r + 1) * (C₂ + C₃ + 2) * Γ
        = ((2:ℝ) ^ r * Γ) * (((r:ℝ) + 1) * (C₂ + C₃ + 2)) := by ring
    rw [hl, hrr]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  have e3 : (0:ℝ) ≤ C₁ * Γ := by positivity
  have e4 : (2:ℝ) ^ r * ((r:ℝ) * (Γ + (C₂ + C₃) * L ^ (-A)))
      = (2:ℝ) ^ r * (r * Γ) + (2:ℝ) ^ r * (r * ((C₂ + C₃) * L ^ (-A))) := by ring
  linarith [e1, e2, e3, e4]



/-! ## Removing the digit cut

The digit cut is paid once per level against two different laws: Lebesgue at
level `j ℓ` (`Section5Join.lebesgue_digitCut_tail`, display (15) at `r = 1`) and
the stationary law (`Section5Join.stationaryMeanR_digitCut_gap`, the exact
Gauss-Kuzmin tail).  Both are uniform in the level and in the section family, so
the telescoping bound carries them across the `r` levels unchanged. -/

set_option maxHeartbeats 1000000 in
/-- **The multi-set tuple factorization at the indicator itself.**  The
digit-cut version with the cut removed, at the cost of the two digit tails,
each paid once per level. -/
theorem multiLevel_indFull_factorization (r m : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ (Acut N : ℕ) (δ : ℝ), 0 < δ → Selberg.farTail N δ ≤ 1 →
      ∀ Bs : ℕ → ℕ → Set ℝ, (∀ ℓ a, MeasurableSet (Bs ℓ a)) →
        (∀ ℓ a, IntervalClass.IsUnionOfIntervals m (Bs ℓ a)) →
        (Acut : ℝ) ≤ (Lnorm n) ^ D → (N : ℝ) ≤ (Lnorm n) ^ D →
        ((Acut : ℝ) + 1) * ((2 * (N : ℝ) + 1) * (1 + Selberg.farTail N δ))
            ≤ (Lnorm n) ^ D →
        |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
              indFull (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMeanR (indFull (Bs ℓ))|
          ≤ C * ((Lnorm n) ^ (-A)
              + ((4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ)
              + 1 / ((Acut : ℝ) + 1)
              + Real.log (1 + 1 / ((Acut : ℝ) + 1)) / Real.log 2) := by
  classical
  obtain ⟨C₅, hC₅, hev₅⟩ := multiLevel_indCut_factorization r m D A hD hA
  obtain ⟨C₄, hC₄, htail⟩ := lebesgue_digitCut_tail
  refine ⟨C₅ + (2:ℝ) ^ r * (r + 1) * (C₄ + 1), by positivity, ?_⟩
  filter_upwards [hev₅] with n hn
  intro j hj Acut N δ hδ hfar1 Bs hBsm hBsi hAle hNle hbud
  set L : ℝ := Lnorm n with hL
  set Γ : ℝ := (4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ with hΓ
  set T : ℝ := 1 / ((Acut : ℝ) + 1) with hT
  set S : ℝ := Real.log (1 + 1 / ((Acut : ℝ) + 1)) / Real.log 2 with hS
  have hfar0 : 0 ≤ Selberg.farTail N δ := Selberg.farTail_nonneg N δ
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hS0 : 0 ≤ S := by
    rw [hS]
    have h1 : (0:ℝ) ≤ Real.log (1 + 1 / ((Acut : ℝ) + 1)) :=
      Real.log_nonneg (by
        have hx : (0:ℝ) < 1 / ((Acut : ℝ) + 1) := by positivity
        linarith)
    have h2 : (0:ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    exact div_nonneg h1 h2.le
  have hRA : (0:ℝ) ≤ L ^ (-A) := Real.rpow_nonneg (Lnorm_nonneg n) _
  set I : ℕ → ℕ → ℝ → ℝ := fun ℓ => indCut Acut (Bs ℓ) with hI
  set J : ℕ → ℕ → ℝ → ℝ := fun ℓ => indFull (Bs ℓ) with hJ
  have hIb : ∀ ℓ a θ, |I ℓ a θ| ≤ 2 := fun ℓ a θ =>
    (abs_indCut_le Acut (Bs ℓ) a θ).trans (by norm_num)
  have hJb : ∀ ℓ a θ, |J ℓ a θ| ≤ 2 := fun ℓ a θ =>
    (abs_indFull_le (Bs ℓ) a θ).trans (by norm_num)
  have hIm : ∀ ℓ a, Measurable (I ℓ a) := fun ℓ a => measurable_indCut Acut (hBsm ℓ) a
  have hJm : ∀ ℓ a, Measurable (J ℓ a) := fun ℓ a => measurable_indFull (hBsm ℓ) a
  have hle : ∀ ℓ a θ, I ℓ a θ ≤ J ℓ a θ := by
    intro ℓ a θ
    simp only [hI, hJ, indCut, indFull]
    by_cases hc : a ≤ Acut
    · simp [hc]
    · simp [hc]; exact Selberg.perInd_nonneg (Bs ℓ a) θ
  -- the level-`ℓ` Lebesgue digit tail
  have hgapL : ∀ ℓ : ℕ,
      (∫ α in Ioo (0:ℝ) 1, |J ℓ (digit α (j ℓ)) (theta α n (j ℓ))
          - I ℓ (digit α (j ℓ)) (theta α n (j ℓ))|) ≤ C₄ * T := by
    intro ℓ
    have hII : IntegrableOn (fun α : ℝ => I ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        (Ioo (0:ℝ) 1) := integrableOn_symbol_comp (hIm ℓ) (hIb ℓ) n (j ℓ)
    have hJI : IntegrableOn (fun α : ℝ => J ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
        (Ioo (0:ℝ) 1) := integrableOn_symbol_comp (hJm ℓ) (hJb ℓ) n (j ℓ)
    have habs : (∫ α in Ioo (0:ℝ) 1, |J ℓ (digit α (j ℓ)) (theta α n (j ℓ))
          - I ℓ (digit α (j ℓ)) (theta α n (j ℓ))|)
        = (∫ α in Ioo (0:ℝ) 1, J ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∫ α in Ioo (0:ℝ) 1, I ℓ (digit α (j ℓ)) (theta α n (j ℓ)) := by
      rw [← integral_sub hJI hII]
      refine integral_congr_ae ?_
      filter_upwards with α
      exact abs_of_nonneg (by linarith [hle ℓ (digit α (j ℓ)) (theta α n (j ℓ))])
    rw [habs]
    have h1 := abs_integral_indCut_sub_indFull_le Acut (hBsm ℓ) n (j ℓ)
    have h2 := htail (j ℓ) Acut
    have h3 : C₄ / ((Acut : ℝ) + 1) = C₄ * T := by rw [hT]; ring
    have h4 := (abs_le.mp h1).1
    linarith [h2, h3, h4]
  -- Step A: the two `α`-averages
  have hstepA : |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
        J ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      - ∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
          I ℓ (digit α (j ℓ)) (theta α n (j ℓ))|
      ≤ (2:ℝ) ^ r * (r * (C₄ * T)) := by
    refine le_trans (abs_integral_prod_sub_prod_le (K := 2) (by norm_num)
      hJm hIm hJb hIb n r j) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ ℓ ∈ Finset.range r, ∫ α in Ioo (0:ℝ) 1,
            |J ℓ (digit α (j ℓ)) (theta α n (j ℓ))
              - I ℓ (digit α (j ℓ)) (theta α n (j ℓ))|
        ≤ ∑ _ℓ ∈ Finset.range r, (C₄ * T) :=
          Finset.sum_le_sum fun ℓ _ => hgapL ℓ
      _ = r * (C₄ * T) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Step B: the two stationary sides
  have hstepB : |(∏ ℓ ∈ Finset.range r, stationaryMeanR (I ℓ))
      - ∏ ℓ ∈ Finset.range r, stationaryMeanR (J ℓ)| ≤ (2:ℝ) ^ r * (r * S) := by
    refine le_trans (abs_prod_range_sub_prod_range_le
      (fun ℓ => stationaryMeanR (I ℓ)) (fun ℓ => stationaryMeanR (J ℓ))
      (by norm_num : (1:ℝ) ≤ 2) (fun ℓ => abs_stationaryMeanR_le (hIb ℓ))
      (fun ℓ => abs_stationaryMeanR_le (hJb ℓ)) r) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ ℓ ∈ Finset.range r, |stationaryMeanR (I ℓ) - stationaryMeanR (J ℓ)|
        ≤ ∑ _ℓ ∈ Finset.range r, S :=
          Finset.sum_le_sum fun ℓ _ => stationaryMeanR_digitCut_gap Acut (Bs ℓ)
      _ = r * S := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hstepC := hn j hj Acut N δ hδ hfar1 Bs hBsm hBsi hAle hNle hbud
  have htri : |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
        J ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      - ∏ ℓ ∈ Finset.range r, stationaryMeanR (J ℓ)|
      ≤ (2:ℝ) ^ r * (r * (C₄ * T)) + C₅ * (L ^ (-A) + Γ) + (2:ℝ) ^ r * (r * S) := by
    have h1 := abs_sub_le
      (∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r, J ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      (∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r, I ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      (∏ ℓ ∈ Finset.range r, stationaryMeanR (J ℓ))
    have h2 := abs_sub_le
      (∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r, I ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      (∏ ℓ ∈ Finset.range r, stationaryMeanR (I ℓ))
      (∏ ℓ ∈ Finset.range r, stationaryMeanR (J ℓ))
    linarith [hstepA, hstepB, hstepC]
  refine le_trans htri ?_
  have h2r : (0:ℝ) < (2:ℝ) ^ r := by positivity
  have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
  have eT : (2:ℝ) ^ r * ((r:ℝ) * (C₄ * T))
      ≤ (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * T := by
    have key : (r:ℝ) * C₄ ≤ ((r:ℝ) + 1) * (C₄ + 1) := by nlinarith
    have hl : (2:ℝ) ^ r * ((r:ℝ) * (C₄ * T)) = ((2:ℝ) ^ r * T) * ((r:ℝ) * C₄) := by ring
    have hrr : (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * T
        = ((2:ℝ) ^ r * T) * (((r:ℝ) + 1) * (C₄ + 1)) := by ring
    rw [hl, hrr]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  have eS : (2:ℝ) ^ r * ((r:ℝ) * S) ≤ (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * S := by
    have key : (r:ℝ) ≤ ((r:ℝ) + 1) * (C₄ + 1) := by nlinarith
    have hl : (2:ℝ) ^ r * ((r:ℝ) * S) = ((2:ℝ) ^ r * S) * (r:ℝ) := by ring
    have hrr : (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * S
        = ((2:ℝ) ^ r * S) * (((r:ℝ) + 1) * (C₄ + 1)) := by ring
    rw [hl, hrr]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  have hexp : (C₅ + (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1)) * (L ^ (-A) + Γ + T + S)
      = C₅ * (L ^ (-A) + Γ) + C₅ * T + C₅ * S
        + (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * (L ^ (-A) + Γ)
        + (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * T
        + (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * S := by ring
  rw [hexp]
  have p1 : (0:ℝ) ≤ C₅ * T := by positivity
  have p2 : (0:ℝ) ≤ C₅ * S := by positivity
  have p3 : (0:ℝ) ≤ (2:ℝ) ^ r * ((r:ℝ) + 1) * (C₄ + 1) * (L ^ (-A) + Γ) := by positivity
  linarith [eT, eS, p1, p2, p3]



/-! ## The schedule at a free exponent

`Section5Join.schedDelta`/`schedDeg`/`schedCut` fix the exponent at `2`, which
is what a *single* level needs: the one-level budget is `o(1/L)`, so an error
`O(L^{-2})` survives multiplication by `L`.  A tuple of `r` levels is summed
against `O(L^r)` tuples, so the exponent has to move with `r`, and display
(24)'s `D` with it.  The schedule below is the same one at a free exponent `s`,
admissible at `D = 4s + 3`. -/

/-- The bracketing scale at exponent `s`: `δ = L^{-s}`. -/
def schedDelta' (s : ℕ) (L : ℝ) : ℝ := 1 / L ^ s

/-- The Fejér degree at exponent `s`: `N = ⌈L^{3s}⌉`. -/
def schedDeg' (s : ℕ) (L : ℝ) : ℕ := ⌈L ^ (3 * s)⌉₊

/-- The digit cut at exponent `s`: `Acut = ⌈L^s⌉`. -/
def schedCut' (s : ℕ) (L : ℝ) : ℕ := ⌈L ^ s⌉₊

/-- **The schedule at exponent `s` is admissible for display (24) at
`D = 4s + 3`.**  At `s = 2` this is `Section5Join.sched_admissible` with
`D = 11`; the point of the generalisation is that `r` levels need the four
costs to be `O(L^{-s})` with `s` as large as `r`, not `2`. -/
theorem sched_admissible' (s : ℕ) (hs : 1 ≤ s) {L : ℝ} (h4L : (4:ℝ) ≤ L) :
    0 < schedDelta' s L ∧
    L ^ s ≤ (schedCut' s L : ℝ) ∧
    Selberg.farTail (schedDeg' s L) (schedDelta' s L) ≤ 1 / (4 * L ^ s) ∧
    (schedCut' s L : ℝ) ≤ L ^ (((4 * s + 3 : ℕ) : ℝ)) ∧
    (schedDeg' s L : ℝ) ≤ L ^ (((4 * s + 3 : ℕ) : ℝ)) ∧
    ((schedCut' s L : ℝ) + 1) * ((2 * (schedDeg' s L : ℝ) + 1)
        * (1 + Selberg.farTail (schedDeg' s L) (schedDelta' s L)))
      ≤ L ^ (((4 * s + 3 : ℕ) : ℝ)) := by
  have hLpos : (0:ℝ) < L := by linarith
  have h1L : (1:ℝ) ≤ L := by linarith
  have hLs : (1:ℝ) ≤ L ^ s := one_le_pow₀ h1L
  have hLspos : (0:ℝ) < L ^ s := by positivity
  have hL3s : (1:ℝ) ≤ L ^ (3 * s) := one_le_pow₀ h1L
  have hL3spos : (0:ℝ) < L ^ (3 * s) := by positivity
  have hd : schedDelta' s L = 1 / L ^ s := rfl
  have hδpos : (0:ℝ) < schedDelta' s L := by rw [hd]; positivity
  have hδsq : (schedDelta' s L) ^ 2 = 1 / L ^ (2 * s) := by
    rw [hd, div_pow, one_pow, ← pow_mul, mul_comm s 2]
  have hNge : L ^ (3 * s) ≤ (schedDeg' s L : ℝ) := Nat.le_ceil _
  have hNlt : (schedDeg' s L : ℝ) < L ^ (3 * s) + 1 :=
    Nat.ceil_lt_add_one hL3spos.le
  have hAge : L ^ s ≤ (schedCut' s L : ℝ) := Nat.le_ceil _
  have hAlt : (schedCut' s L : ℝ) < L ^ s + 1 := Nat.ceil_lt_add_one hLspos.le
  have hfar : Selberg.farTail (schedDeg' s L) (schedDelta' s L) ≤ 1 / (4 * L ^ s) := by
    unfold Selberg.farTail
    rw [hδsq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hrw : 4 * ((schedDeg' s L : ℝ) + 1) * (1 / L ^ (2 * s))
        = 4 * ((schedDeg' s L : ℝ) + 1) / L ^ (2 * s) := by ring
    rw [hrw, le_div_iff₀ (by positivity)]
    have hsplit : L ^ (3 * s) = L ^ s * L ^ (2 * s) := by
      rw [← pow_add]; ring_nf
    nlinarith [hNge, hsplit, hLspos, hL3spos]
  have hfarnn : (0:ℝ) ≤ Selberg.farTail (schedDeg' s L) (schedDelta' s L) :=
    Selberg.farTail_nonneg _ _
  have hfar1 : Selberg.farTail (schedDeg' s L) (schedDelta' s L) ≤ 1 := by
    refine hfar.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have hrpow : L ^ (((4 * s + 3 : ℕ) : ℝ)) = L ^ (4 * s + 3) := Real.rpow_natCast L _
  have hA1 : (schedCut' s L : ℝ) + 1 ≤ L ^ (s + 1) := by
    have hstep : L ^ (s + 1) = L ^ s * L := pow_succ L s
    nlinarith [hAlt, hLs, hstep]
  have hN1 : 2 * (schedDeg' s L : ℝ) + 1 ≤ L ^ (3 * s + 1) := by
    have hstep : L ^ (3 * s + 1) = L ^ (3 * s) * L := pow_succ L (3 * s)
    have h64 : (4:ℝ) ^ (3 * s) ≤ L ^ (3 * s) := pow_le_pow_left₀ (by norm_num) h4L _
    have h4s : (4:ℝ) ≤ (4:ℝ) ^ (3 * s) := by
      calc (4:ℝ) = (4:ℝ) ^ (1:ℕ) := by norm_num
        _ ≤ (4:ℝ) ^ (3 * s) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [hNlt, hstep, h64, h4s]
  refine ⟨hδpos, hAge, hfar, ?_, ?_, ?_⟩
  · rw [hrpow]
    refine le_trans (by linarith [hA1] : (schedCut' s L : ℝ) ≤ L ^ (s + 1)) ?_
    exact pow_le_pow_right₀ h1L (by omega)
  · rw [hrpow]
    refine le_trans (by linarith [hN1] : (schedDeg' s L : ℝ) ≤ L ^ (3 * s + 1)) ?_
    exact pow_le_pow_right₀ h1L (by omega)
  · rw [hrpow]
    have hone : 1 + Selberg.farTail (schedDeg' s L) (schedDelta' s L) ≤ L := by linarith
    have hstep2 : (2 * (schedDeg' s L : ℝ) + 1)
        * (1 + Selberg.farTail (schedDeg' s L) (schedDelta' s L))
        ≤ L ^ (3 * s + 1) * L :=
      mul_le_mul hN1 hone (by linarith) (by positivity)
    have hprod : ((schedCut' s L : ℝ) + 1) * ((2 * (schedDeg' s L : ℝ) + 1)
        * (1 + Selberg.farTail (schedDeg' s L) (schedDelta' s L)))
        ≤ L ^ (s + 1) * (L ^ (3 * s + 1) * L) :=
      mul_le_mul hA1 hstep2 (by positivity) (by positivity)
    refine hprod.trans (le_of_eq ?_)
    rw [← pow_succ, ← pow_add]
    congr 1
    omega

/-! ## The multi-set tuple factorization

The headline of the module.  It is the `r`-level analogue of
`Section5Join.oneLevel_transfer`: the same four costs, the same schedule shape,
the same uniformity in the level and in the section family — but a **different
section family at each level**, and a rate `L^{-A}` with `A` free rather than
the single `o(1/L)` a one-level statement needs. -/

set_option maxHeartbeats 1000000 in
/-- **The multi-set tuple factorization.**  For every tuple length `r`, every
interval count `m` and every rate `A > 0` there is a constant `C` such that,
eventually in `n`, uniformly over good tuples `j` of `J_n` and over **per-level**
families of `θ`-sections `Bs ℓ` whose sections are unions of at most `m`
intervals,

  `|∫₀¹ ∏_{ℓ<r} 1_{Bs ℓ}(a_{j_ℓ+1}(α), θ_{j_ℓ}(α)) dα
      − ∏_{ℓ<r} stationaryMeanR (1_{Bs ℓ})| ≤ C·L^{−A}`.

This is the statement `Kwon1002/FactorialSeries.lean` records as "the multi-set
tuple limit, which is a statement the tree does not contain in any form" — its
*factorization* half.  It is proved here from Proposition 4.1 alone, together
with the Selberg bracket and the two digit tails of `Section5Join`; the record
in `FactorialSeries` is corrected in this module's header. -/
theorem multiLevel_transfer (r m : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ Bs : ℕ → ℕ → Set ℝ, (∀ ℓ a, MeasurableSet (Bs ℓ a)) →
        (∀ ℓ a, IntervalClass.IsUnionOfIntervals m (Bs ℓ a)) →
        |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
              indFull (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMeanR (indFull (Bs ℓ))|
          ≤ C * (Lnorm n) ^ (-A) := by
  classical
  set s : ℕ := max 1 ⌈A⌉₊ with hsdef
  have hs1 : 1 ≤ s := le_max_left _ _
  have hsA : A ≤ (s:ℝ) := by
    refine le_trans (Nat.le_ceil A) ?_
    exact_mod_cast le_max_right 1 ⌈A⌉₊
  obtain ⟨C, hC, hev⟩ := multiLevel_indFull_factorization r m
    (((4 * s + 3 : ℕ) : ℝ)) A (by positivity) hA
  refine ⟨C * (8 * m + 9), by positivity, ?_⟩
  have hL4 : ∀ᶠ n : ℕ in atTop, (4:ℝ) ≤ Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop 4
  filter_upwards [hev, hL4] with n hn h4L
  intro j hj Bs hBsm hBsi
  set L : ℝ := Lnorm n with hL
  have hLpos : (0:ℝ) < L := by linarith
  have h1L : (1:ℝ) ≤ L := by linarith
  have hLs : (1:ℝ) ≤ L ^ s := one_le_pow₀ h1L
  have hLspos : (0:ℝ) < L ^ s := by positivity
  obtain ⟨hδpos, hAge, hfar, hAle, hNle, hbud⟩ := sched_admissible' s hs1 h4L
  set δ : ℝ := schedDelta' s L with hδdef
  set N : ℕ := schedDeg' s L with hNdef
  set Acut : ℕ := schedCut' s L with hAdef
  have hfarnn : (0:ℝ) ≤ Selberg.farTail N δ := Selberg.farTail_nonneg N δ
  have hfar1 : Selberg.farTail N δ ≤ 1 := by
    refine hfar.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have hbase := hn j hj Acut N δ hδpos hfar1 Bs hBsm hBsi hAle hNle hbud
  refine le_trans hbase ?_
  -- the four costs, each priced against `L^{-s} ≤ L^{-A}`
  have hinv : 1 / L ^ s ≤ L ^ (-A) := by
    have h1 : (1:ℝ) / L ^ s = L ^ (-(s:ℝ)) := by
      rw [Real.rpow_neg hLpos.le, Real.rpow_natCast, one_div]
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_le h1L (by linarith)
  have hδval : δ = 1 / L ^ s := rfl
  have hΓ : (4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ
      ≤ (8 * (m:ℝ) + 5) * (1 / L ^ s) := by
    have hf2 : 2 * Selberg.farTail N δ ≤ 1 / L ^ s := by
      have : Selberg.farTail N δ ≤ 1 / (4 * L ^ s) := hfar
      have hrw : (1:ℝ) / (4 * L ^ s) = (1 / L ^ s) / 4 := by ring
      rw [hrw] at this
      linarith
    have hd2 : (4 * (m:ℝ) + 2) * (2 * δ) = (8 * (m:ℝ) + 4) * (1 / L ^ s) := by
      rw [hδval]; ring
    linarith
  have hA1pos : (0:ℝ) < (Acut:ℝ) + 1 := by positivity
  have hT : 1 / ((Acut:ℝ) + 1) ≤ 1 / L ^ s := by
    rw [div_le_div_iff₀ hA1pos hLspos]
    linarith [hAge]
  have hS : Real.log (1 + 1 / ((Acut:ℝ) + 1)) / Real.log 2 ≤ 2 * (1 / L ^ s) := by
    have hx : (0:ℝ) < 1 / ((Acut:ℝ) + 1) := by positivity
    have hnum : Real.log (1 + 1 / ((Acut:ℝ) + 1)) ≤ 1 / L ^ s :=
      le_trans (GaussKuzmin.log_one_add_le hx) hT
    have hlog2 : (1:ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hu : (0:ℝ) < 1 / L ^ s := by positivity
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
    nlinarith
  have hRA : (0:ℝ) ≤ L ^ (-A) := Real.rpow_nonneg hLpos.le _
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have htot : L ^ (-A)
      + ((4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ)
      + 1 / ((Acut:ℝ) + 1)
      + Real.log (1 + 1 / ((Acut:ℝ) + 1)) / Real.log 2
      ≤ (8 * (m:ℝ) + 9) * L ^ (-A) := by
    have hstep : (8 * (m:ℝ) + 5) * (1 / L ^ s) ≤ (8 * (m:ℝ) + 5) * L ^ (-A) :=
      mul_le_mul_of_nonneg_left hinv (by linarith)
    have hstep2 : 2 * (1 / L ^ s) ≤ 2 * L ^ (-A) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    linarith [hΓ, hT, hS, hinv, hstep, hstep2]
  calc C * (L ^ (-A)
        + ((4 * (m:ℝ) + 2) * (2 * δ) + 2 * Selberg.farTail N δ)
        + 1 / ((Acut:ℝ) + 1)
        + Real.log (1 + 1 / ((Acut:ℝ) + 1)) / Real.log 2)
      ≤ C * ((8 * (m:ℝ) + 9) * L ^ (-A)) :=
        mul_le_mul_of_nonneg_left htot hC.le
    _ = C * (8 * (m:ℝ) + 9) * L ^ (-A) := by ring

/-- **`Section5Join.oneLevel_transfer` is the `r = 1` case.**  A guard that the
multi-level statement really is the one-level one generalised: at `r = 1` the
product collapses and the bound is the same `o(1/L)` once `A > 1`, since
`L·C·L^{-A} → 0`. -/
theorem multiLevel_transfer_one (m : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n 1 j →
      ∀ B : ℕ → Set ℝ, (∀ a, MeasurableSet (B a)) →
        (∀ a, IntervalClass.IsUnionOfIntervals m (B a)) →
        |(∫ α in Ioo (0:ℝ) 1, indFull B (digit α (j 0)) (theta α n (j 0)))
            - stationaryMeanR (indFull B)| ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨C, hC, hev⟩ := multiLevel_transfer 1 m hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn j hj B hBm hBi
  have h := hn j hj (fun _ => B) (fun _ => hBm) (fun _ => hBi)
  simpa using h



/-! ## Non-vacuity: good `r`-tuples exist

Every statement of the form `∀ j, GoodTuple n r j → …` is vacuous if `J_n`
carries no good `r`-tuple, and `Kwon1002/OneLevelLaw.lean` establishes existence
only at `r = 1` (`eventually_bulkJ_nonempty`, where (25) and (26) are vacuous).
For `r ≥ 2` both conditions have content, and nothing in the tree checked that
they can be met simultaneously.  They can: an arithmetic progression of step
`300H` started just above the lower trim stays in the lower `O(rH)` of `J_n`,
which is `Ω(L)` away from every resonance time `(m_n + j_i)/2 ≥ m_n/2`. -/

/-- `L` eventually dominates any fixed multiple of `H`, because
`L = H·L^{1/4}`. -/
theorem eventually_const_mul_Hscale_le (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < Lnorm n ∧ 1 ≤ Hscale n ∧ c * Hscale n + c ≤ Lnorm n := by
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQ : Tendsto (fun n : ℕ => (Lnorm n) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 4)).comp hLtend
  have hH : Tendsto (fun n : ℕ => Hscale n) atTop atTop := P42Cases.tendsto_Hscale
  filter_upwards [hLtend.eventually_gt_atTop 0, hH.eventually_ge_atTop 1,
    hQ.eventually_ge_atTop (2 * |c| + 2)] with n hL0 hH1 hQbig
  refine ⟨hL0, hH1, ?_⟩
  have hsplit : Lnorm n = Hscale n * (Lnorm n) ^ (1 / 4 : ℝ) :=
    OneLevelLaw.Lnorm_eq_Hscale_mul hL0
  have hc : c ≤ |c| := le_abs_self c
  have hstep : Hscale n * (2 * |c| + 2) ≤ Hscale n * (Lnorm n) ^ (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left hQbig (by linarith)
  nlinarith [hH1, hc, abs_nonneg c]

/-- **Good `r`-tuples exist.**  Eventually in `n`, the deterministic bulk `J_n`
carries a good `r`-tuple, so `multiLevel_transfer` and every other
`GoodTuple n r`-quantified statement in §4 has content.  The witness is the
arithmetic progression `j_ℓ = ⌊200H⌋ + 1 + ℓ·(⌊300H⌋ + 1)`. -/
theorem eventually_exists_goodTuple (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ j : ℕ → ℕ, GoodTuple n r j := by
  filter_upwards [eventually_const_mul_Hscale_le (3000 * ((r:ℝ) + 1))] with n hn
  obtain ⟨hL0, hH1, hbig⟩ := hn
  set H : ℝ := Hscale n with hHdef
  set L : ℝ := Lnorm n with hLdef
  have hH0 : (0:ℝ) ≤ H := by linarith
  have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
  have hlamp : (0:ℝ) < lyapunov := OneLevelLaw.lyapunov_pos
  have hlam2 : lyapunov < 2 := OneLevelLaw.lyapunov_lt_two
  -- the progression
  set base : ℕ := ⌊200 * H⌋₊ + 1 with hbdef
  set K : ℕ := ⌊300 * H⌋₊ + 1 with hKdef
  have hbaselow : 200 * H ≤ (base : ℝ) := by
    have := Nat.lt_floor_add_one (200 * H)
    rw [hbdef]; push_cast; linarith
  have hbasehigh : (base : ℝ) ≤ 200 * H + 1 := by
    have := Nat.floor_le (by positivity : (0:ℝ) ≤ 200 * H)
    rw [hbdef]; push_cast; linarith
  have hKlow : 300 * H ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one (300 * H)
    rw [hKdef]; push_cast; linarith
  have hKhigh : (K : ℝ) ≤ 300 * H + 1 := by
    have := Nat.floor_le (by positivity : (0:ℝ) ≤ 300 * H)
    rw [hKdef]; push_cast; linarith
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hK1 : 1 ≤ K := by rw [hKdef]; omega
  refine ⟨fun ℓ => if ℓ < r then base + ℓ * K else 0, ?_⟩
  set j : ℕ → ℕ := fun ℓ => if ℓ < r then base + ℓ * K else 0 with hjdef
  have hjval : ∀ ℓ, ℓ < r → j ℓ = base + ℓ * K := by
    intro ℓ hℓ; rw [hjdef]; simp [hℓ]
  have hjR : ∀ ℓ, ℓ < r → (j ℓ : ℝ) = (base : ℝ) + (ℓ : ℝ) * (K : ℝ) := by
    intro ℓ hℓ; rw [hjval ℓ hℓ]; push_cast; ring
  -- the top of the progression
  have hjub : ∀ ℓ, ℓ < r → (j ℓ : ℝ) ≤ 300 * (r:ℝ) * H + (r:ℝ) := by
    intro ℓ hℓ
    have hℓr : (ℓ:ℝ) ≤ (r:ℝ) - 1 := by
      have : (ℓ:ℝ) + 1 ≤ (r:ℝ) := by exact_mod_cast hℓ
      linarith
    have hℓ0 : (0:ℝ) ≤ (ℓ:ℝ) := Nat.cast_nonneg ℓ
    have hmul : (ℓ:ℝ) * (K:ℝ) ≤ ((r:ℝ) - 1) * (300 * H + 1) := by
      calc (ℓ:ℝ) * (K:ℝ) ≤ ((r:ℝ) - 1) * (K:ℝ) :=
            mul_le_mul_of_nonneg_right hℓr hK0
        _ ≤ ((r:ℝ) - 1) * (300 * H + 1) := by
            refine mul_le_mul_of_nonneg_left hKhigh (by linarith)
    rw [hjR ℓ hℓ]
    nlinarith [hbasehigh, hmul, hH0]
  have hjlb : ∀ ℓ, ℓ < r → 200 * H ≤ (j ℓ : ℝ) := by
    intro ℓ hℓ
    rw [hjR ℓ hℓ]
    have : (0:ℝ) ≤ (ℓ:ℝ) * (K:ℝ) := by positivity
    linarith
  -- the bulk index bound
  have hmR : L / lyapunov - 1 < (mIndex n : ℝ) := by
    have h := Nat.lt_floor_add_one (L / lyapunov)
    rw [mIndex, ← hLdef]
    linarith
  have hLlam : L / 2 ≤ L / lyapunov := by
    rw [div_le_div_iff₀ (by norm_num) hlamp]
    nlinarith
  have hmlow : L / 2 - 1 ≤ (mIndex n : ℝ) := by linarith
  have hroom : ∀ ℓ, ℓ < r → (j ℓ : ℝ) ≤ (mIndex n : ℝ) - 200 * H := by
    intro ℓ hℓ
    have h1 := hjub ℓ hℓ
    nlinarith [hbig, hmlow, hH1, hr0, hH0]
  have hmemJ : ∀ ℓ, ℓ < r → j ℓ ∈ bulkJ n := by
    intro ℓ hℓ
    have hle : (j ℓ : ℝ) ≤ (mIndex n : ℝ) := by
      have := hroom ℓ hℓ
      linarith [hH0]
    have hnat : j ℓ ≤ mIndex n := by exact_mod_cast hle
    rw [bulkJ, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hjlb ℓ hℓ, hroom ℓ hℓ⟩
  refine ⟨⟨?_, ?_, hmemJ⟩, ?_, ?_⟩
  · intro ℓ hℓ
    rw [hjdef]; simp [Nat.not_lt.mpr hℓ]
  · intro ℓ ℓ' hlt hℓ'
    have hℓ : ℓ < r := lt_trans hlt hℓ'
    rw [hjval ℓ hℓ, hjval ℓ' hℓ']
    have : ℓ * K < ℓ' * K := Nat.mul_lt_mul_of_lt_of_le hlt le_rfl (by omega)
    omega
  · intro ℓ hℓ
    have hℓr : ℓ < r := by omega
    have hℓ1r : ℓ + 1 < r := hℓ
    rw [hjR (ℓ + 1) hℓ1r, hjR ℓ hℓr]
    push_cast
    nlinarith [hKlow, hH0]
  · intro i ℓ hiℓ hℓr
    have hir : i < r := lt_trans hiℓ hℓr
    have hi0 : (0:ℝ) ≤ (j i : ℝ) := Nat.cast_nonneg _
    have hub := hjub ℓ hℓr
    have hkey : 200 * H ≤ ((mIndex n : ℝ) + (j i : ℝ)) / 2 - (j ℓ : ℝ) := by
      nlinarith [hbig, hmlow, hH1, hr0, hH0, hi0, hub]
    have : 200 * H ≤ |(j ℓ : ℝ) - ((mIndex n : ℝ) + (j i : ℝ)) / 2| := by
      rw [abs_sub_comm]
      exact le_trans hkey (le_abs_self _)
    exact this



/-- **The multi-set factorization is non-vacuous.**  Combining
`multiLevel_transfer` with `eventually_exists_goodTuple`: eventually there
really is a good `r`-tuple for it to speak about. -/
theorem multiLevel_transfer_nonvacuous (r m : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ j : ℕ → ℕ, GoodTuple n r j ∧
      ∀ Bs : ℕ → ℕ → Set ℝ, (∀ ℓ a, MeasurableSet (Bs ℓ a)) →
        (∀ ℓ a, IntervalClass.IsUnionOfIntervals m (Bs ℓ a)) →
        |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range r,
              indFull (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMeanR (indFull (Bs ℓ))|
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨C, hC, hev⟩ := multiLevel_transfer r m hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_exists_goodTuple r] with n hn hex
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, hj, hn j hj⟩


end

end MultiLevel

end Kwon1002
