import Kwon1002.MultiLevel
import Kwon1002.Section5Intervals

/-!
# Residual 2a, from the multi-set transfer

`Kwon1002.TupleFinal.goodSet_mark_factorization_intervals` — residual 2a, the
Jackson step of Proposition 4.1 at the deterministic mark event — is proved
here, at a new name, from `Kwon1002.MultiLevel.multiLevel_transfer` alone.

The three interfaces the reduction needs, and where each comes from.

* **`SepGoodSet` ↔ `GoodTuple`, the sorting bijection.**  Already discharged:
  `Kwon1002.JacksonGate.exists_goodTuple_of_sepGoodSet` turns a separated
  `k`-element subset of the deterministic bulk into an increasing
  `Section4.GoodTuple`, and transfers both the `Finset` product and the indexed
  intersection to the tuple indexing.
* **`detMarkEvent` ↔ the `indFull` sections of `MultiLevel`.**  The one-level
  half is `Section5Intervals.oneLevelEvent_section`, whose section family is
  `Section5Intervals.signedSection ((-1)^j) L B`; `prod_indFull_signedSection`
  below is its `k`-level form, and it is a pointwise identity of indicators, so
  it costs nothing beyond bookkeeping.
* **`∏ unifIoo.real` ↔ `∏ stationaryMeanR`.**  Not an identity: the two differ,
  and the gap is bounded by applying the transfer once per level at `r = 1`
  (`MultiLevel.multiLevel_transfer_one`) and telescoping with
  `MultiLevel.abs_prod_range_sub_prod_range_le`.  Both sides are bounded by `1`,
  so the telescoping constant is `1^k = 1`.

The rate is free.  `multiLevel_transfer` holds at **every** `A > 0`, so taking
`A = k + 1` delivers residual 2a's `C·L^{-(k+1)}` directly; no sharpening of the
transfer is needed, and the two applications may use the same `A`.

The interval hypothesis is used exactly once, through
`IntervalClass.markSection_signed_isUnionOfIntervals`: a `B` that is a union of
`m` intervals has `θ`-sections that are unions of at most `2m` intervals,
uniformly in the digit and in the sign, which is the `m` that
`multiLevel_transfer` is instantiated at.  The residual's other two hypotheses
(`_hB0`, `_hBbd`) are not needed for this direction and are carried only to keep
the statement byte-identical to the canonical one.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace TupleTransfer

noncomputable section

open Section5Join Section5Intervals TupleFinal LevyExponent TupleMeasure

/-! ## Interface 2: the `k`-level section identity -/

/-- The one-level pointwise identity behind `Section5Intervals.oneLevelEvent_section`,
isolated: the section indicator read at `(a_{j+1}(α), θ_j(α))` *is* the indicator
of the level-`j` mark event. -/
lemma indFull_signedSection_eq_indicator (B : Set ℝ) (n j : ℕ) (α : ℝ) :
    indFull (signedSection ((-1:ℝ) ^ j) (Lnorm n) B) (digit α j) (theta α n j)
      = Set.indicator (oneLevelEvent n B j) (fun _ => (1:ℝ)) α := by
  have hiff : theta α n j ∈ Selberg.perSet (signedSection ((-1:ℝ) ^ j) (Lnorm n) B (digit α j))
      ↔ α ∈ oneLevelEvent n B j := by
    rw [mem_perSet_signedSection]
    have hval : (-1:ℝ) ^ j * (digit α j : ℝ) * W (theta α n j) / Lnorm n
        = signedMark α n j := by
      rw [signedMark, mark]; ring
    rw [hval]
    exact Iff.rfl
  unfold indFull Selberg.perInd
  by_cases hc : theta α n j
      ∈ Selberg.perSet (signedSection ((-1:ℝ) ^ j) (Lnorm n) B (digit α j))
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (hiff.mp hc)]
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun h => hc (hiff.mpr h))]

/-- A finite product of indicators is the indicator of the intersection. -/
lemma prod_indicator_range (k : ℕ) (E : ℕ → Set ℝ) (α : ℝ) :
    (∏ ℓ ∈ Finset.range k, Set.indicator (E ℓ) (fun _ => (1:ℝ)) α)
      = Set.indicator (⋂ ℓ ∈ (Finset.range k : Set ℕ), E ℓ) (fun _ => (1:ℝ)) α := by
  classical
  by_cases h : ∀ ℓ ∈ Finset.range k, α ∈ E ℓ
  · have hmem : α ∈ ⋂ ℓ ∈ (Finset.range k : Set ℕ), E ℓ := by
      simp only [Set.mem_iInter, Finset.mem_coe]
      exact fun ℓ hℓ => h ℓ hℓ
    rw [Set.indicator_of_mem hmem,
      Finset.prod_congr rfl (fun ℓ hℓ => Set.indicator_of_mem (h ℓ hℓ) _)]
    simp
  · push_neg at h
    obtain ⟨ℓ, hℓ, hnot⟩ := h
    have hnotmem : α ∉ ⋂ ℓ ∈ (Finset.range k : Set ℕ), E ℓ := by
      simp only [Set.mem_iInter, Finset.mem_coe, not_forall]
      exact ⟨ℓ, hℓ, hnot⟩
    rw [Set.indicator_of_notMem hnotmem,
      Finset.prod_eq_zero hℓ (Set.indicator_of_notMem hnot _)]

/-- **The `k`-level section identity**, at a **per-level** family of target
sets.  The mass of a `k`-fold intersection of level events is the `α`-average of
the product of the section indicators — the exact left-hand side of
`MultiLevel.multiLevel_transfer`.  Nothing forces the same set at every level,
which is the point: the multi-set form is what a simple-function expansion of a
symbol needs. -/
theorem prod_indFull_signedSection {E : ℕ → Set ℝ} (hE : ∀ x, MeasurableSet (E x))
    (n k : ℕ) (j : ℕ → ℕ) :
    unifIoo.real (⋂ ℓ ∈ (Finset.range k : Set ℕ), oneLevelEvent n (E (j ℓ)) (j ℓ))
      = ∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range k,
          indFull (signedSection ((-1:ℝ) ^ (j ℓ)) (Lnorm n) (E (j ℓ)))
            (digit α (j ℓ)) (theta α n (j ℓ)) := by
  classical
  have hmeas : MeasurableSet
      (⋂ ℓ ∈ (Finset.range k : Set ℕ), oneLevelEvent n (E (j ℓ)) (j ℓ)) := by
    refine MeasurableSet.biInter (Set.Finite.countable (Finset.range k).finite_toSet) ?_
    intro ℓ _
    exact (measurable_signedMark n (j ℓ)) (hE (j ℓ))
  have hpt : ∀ α : ℝ, (∏ ℓ ∈ Finset.range k,
        indFull (signedSection ((-1:ℝ) ^ (j ℓ)) (Lnorm n) (E (j ℓ)))
          (digit α (j ℓ)) (theta α n (j ℓ)))
      = Set.indicator (⋂ ℓ ∈ (Finset.range k : Set ℕ), oneLevelEvent n (E (j ℓ)) (j ℓ))
          (fun _ => (1:ℝ)) α := by
    intro α
    rw [Finset.prod_congr rfl
      (fun ℓ _ => indFull_signedSection_eq_indicator (E (j ℓ)) n (j ℓ) α)]
    exact prod_indicator_range k (fun ℓ => oneLevelEvent n (E (j ℓ)) (j ℓ)) α
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), setIntegral_indicator hmeas,
    setIntegral_const, smul_eq_mul, mul_one]
  show (unifIoo _).toReal = _
  rw [unifIoo, Measure.restrict_apply hmeas]
  congr 2
  exact Set.inter_comm _ _

/-! ## Interface 3: the product of one-level masses against the stationary product -/

/-- Every level mass is at most `1`: it is the mass of a subset of the unit
interval under a probability measure. -/
lemma abs_measureReal_le_one (E : Set ℝ) : |unifIoo.real E| ≤ 1 := by
  rw [abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- The one-level tuple carrying a single bulk level.  `GoodTuple n 1` asks
nothing beyond membership in the bulk: both separation conditions quantify over
pairs, and there are none. -/
def solo (x : ℕ) : ℕ → ℕ := fun i => if i = 0 then x else 0

lemma solo_zero (x : ℕ) : solo x 0 = x := by simp [solo]

lemma goodTuple_solo {n x : ℕ} (hx : x ∈ bulkJ n) : GoodTuple n 1 (solo x) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    have : i ≠ 0 := by omega
    simp [solo, this]
  · intro i i' _ hi'
    omega
  · intro i hi
    have : i = 0 := by omega
    subst this
    simpa [solo_zero] using hx
  · intro i hi
    omega
  · intro i i' hii' hi'
    omega

/-! ## The multi-set factorization at the mark event, and residual 2a -/

/-- **The multi-set factorization at the deterministic mark event.**

For every interval count `m` and every tuple length `k` there is one constant
`C`, eventually in `n`, valid **uniformly over every per-level family** `E` of
target sets each of which is a union of at most `m` intervals, and over every
separated `k`-element subset `S` of the deterministic bulk:

  `|P(⋂_{x∈S} X_{n,x} ∈ E x) − ∏_{x∈S} P(X_{n,x} ∈ E x)| ≤ C·L^{−(k+1)}`.

This is the shape a simple-function expansion of a symbol produces — a
*different* set at each level — and it is the statement
`Kwon1002/FactorialSeries.lean` records as the multi-set half that
`LevyExponent.tuple_measure_convergence` does not supply.  It is proved from
`MultiLevel.multiLevel_transfer` alone; that theorem is already per-level, so no
widening of Proposition 4.1 is involved.

Uniformity in `E` is not an accident of the statement: the constant produced
below is `C₁ + k·C₂` with `C₁, C₂` the constants of `multiLevel_transfer` at
`(k, 2m)` and `(1, 2m)`, and neither depends on the section family. -/
theorem multiSet_mark_factorization (m k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ E : ℕ → Set ℝ,
      (∀ x, MeasurableSet (E x)) → (∀ x, IntervalClass.IsUnionOfIntervals m (E x)) →
      ∀ S : Finset ℕ, S.card = k → SepGoodSet n S →
      |unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n (E x) x)
          - ∏ x ∈ S, unifIoo.real (detMarkEvent n (E x) x)| ≤ C / (Lnorm n) ^ (k + 1) := by
  classical
  have hA : (0:ℝ) < (k:ℝ) + 1 := by positivity
  obtain ⟨C₁, hC₁, hev₁⟩ := MultiLevel.multiLevel_transfer k (2 * m) hA
  obtain ⟨C₂, hC₂, hev₂⟩ := MultiLevel.multiLevel_transfer_one (2 * m) hA
  refine ⟨C₁ + k * C₂, by positivity, ?_⟩
  have hLpos : ∀ᶠ n : ℕ in atTop, (0:ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [hev₁, hev₂, hLpos] with n h1 h2 hL E hEm hEi S hcard hS
  obtain ⟨j, hj, hprod, hinter⟩ := JacksonGate.exists_goodTuple_of_sepGoodSet hcard hS
  -- the per-level section family
  set Bs : ℕ → ℕ → Set ℝ :=
    fun ℓ => signedSection ((-1:ℝ) ^ (j ℓ)) (Lnorm n) (E (j ℓ)) with hBs
  have hBsm : ∀ ℓ a, MeasurableSet (Bs ℓ a) := fun ℓ a =>
    measurableSet_signedSection (hEm (j ℓ)) _ _ a
  have hBsi : ∀ ℓ a, IntervalClass.IsUnionOfIntervals (2 * m) (Bs ℓ a) := fun ℓ a =>
    IntervalClass.markSection_signed_isUnionOfIntervals (hEi (j ℓ)) _ a _
  -- on the bulk the deterministic event is the level event
  have hEq : ∀ ℓ, ℓ ∈ Finset.range k →
      detMarkEvent n (E (j ℓ)) (j ℓ) = oneLevelEvent n (E (j ℓ)) (j ℓ) :=
    fun ℓ hℓ => detMarkEvent_of_mem (hj.1.2.2 ℓ (Finset.mem_range.mp hℓ)) _
  -- rewrite both sides at the tuple indexing
  have hLHS : unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n (E x) x)
      = ∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range k,
          indFull (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)) := by
    rw [hinter (fun x => detMarkEvent n (E x) x)]
    have hcong : (⋂ ℓ ∈ (Finset.range k : Set ℕ), detMarkEvent n (E (j ℓ)) (j ℓ))
        = ⋂ ℓ ∈ (Finset.range k : Set ℕ), oneLevelEvent n (E (j ℓ)) (j ℓ) :=
      Set.iInter₂_congr (fun ℓ hℓ => hEq ℓ (Finset.mem_coe.mp hℓ))
    rw [hcong, prod_indFull_signedSection hEm n k j]
  have hRHS : ∏ x ∈ S, unifIoo.real (detMarkEvent n (E x) x)
      = ∏ ℓ ∈ Finset.range k, unifIoo.real (oneLevelEvent n (E (j ℓ)) (j ℓ)) := by
    rw [hprod (fun x => unifIoo.real (detMarkEvent n (E x) x))]
    exact Finset.prod_congr rfl (fun ℓ hℓ => by rw [hEq ℓ hℓ])
  rw [hLHS, hRHS]
  -- the two transfer applications
  have hmain := h1 j hj Bs hBsm hBsi
  have hone : ∀ ℓ ∈ Finset.range k,
      |unifIoo.real (oneLevelEvent n (E (j ℓ)) (j ℓ)) - stationaryMeanR (indFull (Bs ℓ))|
        ≤ C₂ * (Lnorm n) ^ (-((k:ℝ) + 1)) := by
    intro ℓ hℓ
    have hgood : GoodTuple n 1 (solo (j ℓ)) :=
      goodTuple_solo (hj.1.2.2 ℓ (Finset.mem_range.mp hℓ))
    have h := h2 (solo (j ℓ)) hgood (Bs ℓ) (hBsm ℓ) (hBsi ℓ)
    rw [solo_zero] at h
    rwa [oneLevelEvent_section (hEm (j ℓ)) n (j ℓ)]
  have hprodgap :
      |(∏ ℓ ∈ Finset.range k, unifIoo.real (oneLevelEvent n (E (j ℓ)) (j ℓ)))
          - ∏ ℓ ∈ Finset.range k, stationaryMeanR (indFull (Bs ℓ))|
        ≤ (k : ℝ) * (C₂ * (Lnorm n) ^ (-((k:ℝ) + 1))) := by
    have hbase := MultiLevel.abs_prod_range_sub_prod_range_le
      (fun ℓ => unifIoo.real (oneLevelEvent n (E (j ℓ)) (j ℓ)))
      (fun ℓ => stationaryMeanR (indFull (Bs ℓ))) (le_refl (1:ℝ))
      (fun ℓ => abs_measureReal_le_one _)
      (fun ℓ => MultiLevel.abs_stationaryMeanR_le (abs_indFull_le (Bs ℓ))) k
    refine le_trans hbase ?_
    rw [one_pow, one_mul]
    refine le_trans (Finset.sum_le_sum hone) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- assemble
  have hsplit : |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range k,
          indFull (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)))
        - ∏ ℓ ∈ Finset.range k, unifIoo.real (oneLevelEvent n (E (j ℓ)) (j ℓ))|
      ≤ (C₁ + (k:ℝ) * C₂) * (Lnorm n) ^ (-((k:ℝ) + 1)) := by
    calc |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range k,
              indFull (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range k, unifIoo.real (oneLevelEvent n (E (j ℓ)) (j ℓ))|
        ≤ |(∫ α in Ioo (0:ℝ) 1, ∏ ℓ ∈ Finset.range k,
              indFull (Bs ℓ) (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range k, stationaryMeanR (indFull (Bs ℓ))|
          + |(∏ ℓ ∈ Finset.range k, stationaryMeanR (indFull (Bs ℓ)))
            - ∏ ℓ ∈ Finset.range k, unifIoo.real (oneLevelEvent n (E (j ℓ)) (j ℓ))| :=
          abs_sub_le _ _ _
      _ ≤ C₁ * (Lnorm n) ^ (-((k:ℝ) + 1))
            + (k : ℝ) * (C₂ * (Lnorm n) ^ (-((k:ℝ) + 1))) := by
          refine add_le_add hmain ?_
          rw [abs_sub_comm]
          exact hprodgap
      _ = (C₁ + (k:ℝ) * C₂) * (Lnorm n) ^ (-((k:ℝ) + 1)) := by ring
  refine le_trans hsplit (le_of_eq ?_)
  have hpow : (Lnorm n) ^ (-((k:ℝ) + 1)) = ((Lnorm n) ^ (k + 1))⁻¹ := by
    rw [Real.rpow_neg hL.le]
    congr 1
    rw [show ((k:ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hpow, div_eq_mul_inv]

/-- **Residual 2a, proved.**  The statement of
`Kwon1002.TupleFinal.goodSet_mark_factorization_intervals`, reproduced token for
token (the guard at the foot of this file checks that inside Lean), as the
diagonal `E ≡ B` of `multiSet_mark_factorization`.

The residual's hypotheses `_hB0` and `_hBbd` are not used in this direction and
are carried only to keep the statement byte-identical to the canonical one; what
is used is measurability and the interval count. -/
theorem goodSet_mark_factorization_intervals (B : Set ℝ) (hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (hint : IntervalClass.IsFiniteUnionOfIntervals B) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S.card = k → SepGoodSet n S →
      |unifIoo.real (⋂ x ∈ (S : Set ℕ), detMarkEvent n B x)
          - ∏ x ∈ S, unifIoo.real (detMarkEvent n B x)| ≤ C / (Lnorm n) ^ (k + 1) := by
  obtain ⟨m, hm⟩ := hint
  obtain ⟨C, hC, hev⟩ := multiSet_mark_factorization m k
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn
  exact hn (fun _ => B) (fun _ => hB) (fun _ => hm)


/-! ## The §5 chain at the interval class, unconditional

With residual 2a a theorem, the deterministic side of displays (39)-(40) closes
at every `B` in the interval class — the class that carries every instantiation
the §5 chain makes, by
`IntervalClass.isUnionOfIntervals_truncation`.  The proofs are the ones already
in `Kwon1002/TupleFinal.lean` and `Kwon1002/TupleInputs.lean`; what is new is
only that the two inputs they were waiting on are now available *here*:
residual 2a above, and residual (35a)
`Section5Intervals.deterministic_oneLevel_intensity_intervals`.

Residual 2b (`TupleFinal.goodSet_intervals_to_measurable`) and residual 35b
(`TupleInputs.oneLevel_gaussKuzmin_intensity_to_measurable`) are **not** used:
they are the passage from the interval class to general measurable sets, which
the §5 chain does not need. -/

/-- The deterministic one-level sums converge to `Λ(B)`, unconditionally on the
interval class. -/
theorem sum_det_tendsto_intervals (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (hint : IntervalClass.IsFiniteUnionOfIntervals B) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), unifIoo.real (detMarkEvent n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) :=
  Filter.Tendsto.congr (fun n => (sum_det_eq_sum_bulkJ n B).symm)
    (deterministic_oneLevel_intensity_intervals B hB hB0 hBbd hint)

/-- **The manuscript's steps 2 and 3 on the deterministic side**, unconditionally
on the interval class: `TupleFinal.det_quasi_independence` with residual 2
supplied by `goodSet_mark_factorization_intervals`. -/
theorem det_quasi_independence_intervals (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (hint : IntervalClass.IsFiniteUnionOfIntervals B) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (detMarkEvent n B (embTuple f ℓ)))
      atTop (𝓝 0) :=
  det_quasi_independence_of_residual B hB hB0 hBbd k
    (goodSet_mark_factorization_intervals B hB hB0 hBbd hint k)

/-- **Displays (39)-(40) on the deterministic bulk**, unconditionally on the
interval class. -/
theorem det_tuple_measure_convergence_intervals (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (hint : IntervalClass.IsFiniteUnionOfIntervals B) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (detMarkEvent n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  obtain ⟨δ, hδ, hBδ⟩ := hB0
  obtain ⟨C, hC, hCle⟩ := det_singleLevel_measure_le B hδ hBδ
  refine tendsto_emb_sum_of_inputs k (fun n => Finset.range (n + 1))
    (fun n j => unifIoo.real (detMarkEvent n B j)) _
    ((levyIntensity B).toReal) (fun n => C / Lnorm n)
    (fun n j => measureReal_nonneg) (fun n => div_nonneg hC.le (Lnorm_nonneg n))
    ?_ ?_ ?_ ?_
  · filter_upwards [hCle] with n hn j _ using hn j
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_Lnorm_atTop
  · exact sum_det_tendsto_intervals B hB ⟨δ, hδ, hBδ⟩ hBbd hint
  · exact det_quasi_independence_intervals B hB ⟨δ, hδ, hBδ⟩ hBbd hint k

/-- **`LevyExponent.tuple_measure_convergence` on the interval class**,
unconditionally: displays (39)-(40) on the random bulk, from the proved index-set
bridge `TupleFinal.bulk_window_bridge_tuple` and the deterministic form above. -/
theorem tuple_measure_convergence_intervals (c : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (hint : IntervalClass.IsFiniteUnionOfIntervals B) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  have h := (bulk_window_bridge_tuple c B hB hB0 hBbd k).add
    (det_tuple_measure_convergence_intervals B hB hB0 hBbd hint k)
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-- **The one-level intensity limit on the interval class**, unconditionally:
`TupleMeasure.oneLevel_intensity_limit` with no residual left. -/
theorem oneLevel_intensity_limit_intervals (c : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (hint : IntervalClass.IsFiniteUnionOfIntervals B) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        unifIoo.real (bulkMarkEvent c n B j))
      atTop (𝓝 ((levyIntensity B).toReal)) := by
  have hbr : Tendsto (fun n : ℕ =>
      (∑ j ∈ Finset.range (n + 1), unifIoo.real (bulkMarkEvent c n B j))
        - ∑ j ∈ Finset.range (n + 1), unifIoo.real (detMarkEvent n B j))
      atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun n => ?_)
      (bulk_window_bridge_tuple c B hB hB0 hBbd 1)
    rw [sum_emb_one_eq n (bulkMarkEvent c n B),
      sum_emb_one_eq n (detMarkEvent n B)]
  have h := hbr.add (sum_det_tendsto_intervals B hB hB0 hBbd hint)
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-- **`TupleMeasure.tuple_quasi_independence` on the interval class**,
unconditionally. -/
theorem tuple_quasi_independence_intervals (c : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R)
    (hint : IntervalClass.IsFiniteUnionOfIntervals B) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (bulkMarkEvent c n B (embTuple f ℓ)))
      atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hBδ⟩ := hB0
  obtain ⟨C, hC, hCle⟩ := singleLevel_measure_le c B hδ hBδ
  have hT := tuple_measure_convergence_intervals c B hB ⟨δ, hδ, hBδ⟩ hBbd hint k
  have hP := tendsto_emb_prod_sum k (fun n => Finset.range (n + 1))
      (fun n j => unifIoo.real (bulkMarkEvent c n B j))
      ((levyIntensity B).toReal) (fun n => C / Lnorm n)
      (fun n j => measureReal_nonneg) (fun n => div_nonneg hC.le (Lnorm_nonneg n))
      (by filter_upwards [hCle] with n hn j _ using hn j)
      (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_Lnorm_atTop)
      (oneLevel_intensity_limit_intervals c B hB ⟨δ, hδ, hBδ⟩ hBbd hint)
  have hsub := hT.sub hP
  rw [sub_self] at hsub
  exact hsub

end

end TupleTransfer

end Kwon1002
