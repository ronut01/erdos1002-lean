import Kwon1002.TupleFinal

/-!
# The Jackson gate of `goodSet_mark_factorization`, and the sorting bijection

Two things about `Kwon1002.TupleFinal.goodSet_mark_factorization`, the residual
that Proposition 4.1 was expected to unlock.

## 1. The bookkeeping step, carried out

The docstring of `goodSet_mark_factorization` records, without proving it, that
Proposition 4.1 is stated on an increasing tuple `j_1 < ⋯ < j_k` while the
residual is stated on a `Finset S`, and that the two agree through the sorting
bijection.  `exists_goodTuple_of_sepGoodSet` below carries that out: from
`SepGoodSet n S` with `S.card = k` it produces an increasing `j` with
`Section4.GoodTuple n k j`, together with the transfer of *both* sides — the
`Finset` product and the indexed intersection — to the tuple indexing.  The
debt is discharged.

## 2. The Jackson step is a statement-level gap

The same docstring names the route: apply Proposition 4.1 to
`F_ℓ = 1_B ∘ ((-1)^j a W(θ)/L)` after the digit cut at `A_L = L^D` and "a
Jackson approximation putting the indicator of `B` into the symbol class
`P_D(L)` of display (24)".

`1_B` cannot be *put into* `P_D(L)`.  Membership of that class is an exact
finite Fourier expansion — the coefficients `c(a,v)` vanish for `|v| > L^D`, so
the `tsum` of display (24) is a trigonometric polynomial — and a trigonometric
polynomial is continuous.  `continuous_of_isInPD` below proves that, and
`isInPD_const_of_two_valued` draws the consequence: a symbol of the class that
takes only the values `0` and `1` is *constant* in `θ`.  So the composite
`θ ↦ 1_B(±aW(θ)/L)` belongs to `P_D(L)` only when `B` misses or swallows the
whole range of the mark at that digit.

The passage is therefore an **approximation**, and the residual's own error
budget fixes the rate it must achieve.  `goodSet_mark_factorization` asks for
absolute error `C·L^{-(k+1)}` while a single level already carries mass
`Θ(L^{-1})` (`TupleFinal.det_singleLevel_measure_le`), so replacing `1_B` by a
symbol `P` at each of the `k` levels costs about `k·η_L·L^{-(k-1)}`, where
`η_L` is the `L¹` error of the replacement against the law of `θ_j`.  Surviving
the budget needs

  `η_L = O(L^{-2})` uniformly in the digit `a`,

with a symbol of degree at most `L^D`.  For an indicator with finitely many
jumps Jackson gives `η_L = O(m/deg) = O(m·L^{-D})`, and `D > 2` — the constant
the docstring itself carries — is exactly what makes `L^{-D}` beat `L^{-2}`.
That is strong evidence the intended `B` is a finite union of intervals: `W` is
piecewise monotone with two branches, so the `θ`-section of a union of `m`
intervals is an indicator of at most `2m` intervals, *uniformly in `a`*, which
is the uniformity the tuple sum needs.

Under the hypotheses the residual actually carries — `MeasurableSet B`,
`∃ δ > 0, ∀ x ∈ B, δ ≤ |x|`, `∃ R, ∀ x ∈ B, |x| ≤ R` — no rate exists.  Best
`L¹` approximation by degree-`d` trigonometric polynomials converges for every
integrable function but at no uniform rate, and for an indicator whose boundary
carries positive measure the rate can be made slower than any prescribed
sequence.  Note also that `volume (frontier B) = 0` would *not* repair this: it
gives qualitative approximability, not a rate.

**Verdict as of this file, and how it was settled.**  The verdict below stands:
the residual is not provable by the route its own docstring names under the
hypotheses it carried, and the split into an interval case and an approximation
case is the right repair.  The interval case is now a **theorem**:
`Kwon1002/TupleTransfer.lean` proves
`TupleFinal.goodSet_mark_factorization_intervals` token for token and
axiom-clean.  The route it takes is not Jackson approximation of `1_B` at all —
that is what Part 2 below shows is impossible inside `P_D(L)` — but the Selberg
bracket of `Kwon1002/Selberg.lean`, carried to `r` levels by
`MultiLevel.multiLevel_transfer` and read at the mark event through
`Section5Intervals.signedSection`.  The budget arithmetic below (`η_L =
O(L^{-2})`, `D > 2`) is therefore superseded rather than met: the transfer holds
at every rate `A > 0`, so the residual's `C·L^{-(k+1)}` is arranged by choosing
`A = k + 1` and costs nothing.  What the interval hypothesis is really needed
for is exactly what Part 3 below says — the uniform jump count of the
`θ`-section — and that is where it is spent, once.

**Verdict, and what was done about it.**  `goodSet_mark_factorization` is not
provable by the route its own docstring names under the hypotheses it carried.
It needs a boundary-regularity hypothesis on `B` — a finite union of intervals,
or an indicator of bounded variation.

The residual is now **split** in `Kwon1002/TupleFinal.lean`, and no consumer
signature changed:

* `TupleFinal.goodSet_mark_factorization_intervals` carries the added
  hypothesis `IntervalClass.IsFiniteUnionOfIntervals B` and is the Jackson step
  at the class it admits;
* `TupleFinal.goodSet_intervals_to_measurable` is the separate approximation
  step, *interval case implies measurable case*;
* `TupleFinal.goodSet_mark_factorization` keeps its exact statement — every
  consumer and every token-identity check reads the same `Prop` as before — and
  is derived from the two.

The hypothesis was deliberately **not** propagated into
`TupleFinal.det_quasi_independence`, `LevyExponent.tuple_measure_convergence`,
`PoissonRoute.factorialMoment_convergence` or
`PoissonRoute.xi_count_poisson_limit`.  Those statements quantify over
measurable `B` and are expected to be true at that generality, recoverable from
the interval case by approximation against the absolutely continuous limit `Λ`;
adding the hypothesis to them would weaken true statements rather than repair a
false one.  The approximation is what the second residual isolates.

**Why finite unions of intervals are the right class, machine-checked.**
`Kwon1002/IntervalClass.lean` proves that `W` is piecewise monotone with exactly
two branches on the fundamental cell, so the `θ`-section of the mark event over
a union of `m` intervals is a union of at most `2m` intervals *uniformly in the
scaling* — hence uniformly in the digit and in the sign
(`IntervalClass.markSection_isUnionOfIntervals`).  That is the uniformity the
tuple sum needs.  It also proves that every concrete instantiation in the tree,
the truncation `{x | ε < |x|}` cut to a bounded window, is a union of **two**
intervals (`IntervalClass.isUnionOfIntervals_truncation`), so the interval case
already covers every use the development makes.

**The kernel now exists.**  `Kwon1002/Fejer.lean` builds the Fejér kernel from
scratch — expansion, closed form, unit mass, concentration — together with the
Fejér mean, its `L¹` approximation bound, its `ℓ¹` coefficient budget, and
`Fejer.isInPD_fejerPoly`, which places the approximant inside the class
`P_D(L)` this file proves the indicator itself cannot inhabit.  The two facts
are consistent and complementary: `continuous_of_isInPD` rules out the
*indicator*, `Fejer.isInPD_fejerPoly` admits its *approximants*, and the
residual is the passage between them.  What is left of that passage is
recorded on `TupleFinal.goodSet_mark_factorization_intervals`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace JacksonGate

noncomputable section

/-! ## Part 1, the sorting bijection -/

/-- The increasing enumeration of a `k`-element set of levels, extended by `0`
above `k` (the normalization `Section4.IsAdmissibleTuple` uses). -/
def sortTuple {k : ℕ} (S : Finset ℕ) (hcard : S.card = k) : ℕ → ℕ :=
  fun ℓ => if h : ℓ < k then ((S.orderIsoOfFin hcard ⟨ℓ, h⟩ : ℕ)) else 0

lemma sortTuple_mem {k : ℕ} {S : Finset ℕ} (hcard : S.card = k) {ℓ : ℕ} (h : ℓ < k) :
    sortTuple S hcard ℓ ∈ S := by
  simp only [sortTuple, dif_pos h]
  exact (S.orderIsoOfFin hcard ⟨ℓ, h⟩).2

lemma sortTuple_strictMono {k : ℕ} {S : Finset ℕ} (hcard : S.card = k) {ℓ ℓ' : ℕ}
    (hlt : ℓ < ℓ') (h' : ℓ' < k) : sortTuple S hcard ℓ < sortTuple S hcard ℓ' := by
  have h : ℓ < k := lt_trans hlt h'
  simp only [sortTuple, dif_pos h, dif_pos h']
  have : (⟨ℓ, h⟩ : Fin k) < ⟨ℓ', h'⟩ := hlt
  exact (S.orderIsoOfFin hcard).strictMono this

lemma sortTuple_injOn {k : ℕ} {S : Finset ℕ} (hcard : S.card = k) :
    ∀ x ∈ Finset.range k, ∀ y ∈ Finset.range k,
      sortTuple S hcard x = sortTuple S hcard y → x = y := by
  intro x hx y hy hxy
  simp only [Finset.mem_range] at hx hy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (ne_of_lt (sortTuple_strictMono hcard h hy))
  · exact h
  · exact absurd hxy.symm (ne_of_lt (sortTuple_strictMono hcard h hx))

lemma sortTuple_image {k : ℕ} {S : Finset ℕ} (hcard : S.card = k) :
    (Finset.range k).image (sortTuple S hcard) = S := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hx
    exact sortTuple_mem hcard (Finset.mem_range.mp hℓ)
  · rw [Finset.card_image_of_injOn (fun x hx y hy h => sortTuple_injOn hcard x hx y hy h),
      Finset.card_range, hcard]

lemma sortTuple_surj {k : ℕ} {S : Finset ℕ} (hcard : S.card = k) {x : ℕ} (hx : x ∈ S) :
    ∃ ℓ, ℓ < k ∧ sortTuple S hcard ℓ = x := by
  rw [← sortTuple_image hcard] at hx
  obtain ⟨ℓ, hℓ, hle⟩ := Finset.mem_image.mp hx
  exact ⟨ℓ, Finset.mem_range.mp hℓ, hle⟩

/-- **The `Finset` side and the tuple side agree, for products.** -/
theorem prod_eq_sortTuple {k : ℕ} {S : Finset ℕ} (hcard : S.card = k) (f : ℕ → ℝ) :
    ∏ x ∈ S, f x = ∏ ℓ ∈ Finset.range k, f (sortTuple S hcard ℓ) := by
  classical
  have h : ∏ x ∈ (Finset.range k).image (sortTuple S hcard), f x
      = ∏ ℓ ∈ Finset.range k, f (sortTuple S hcard ℓ) :=
    Finset.prod_image (fun x hx y hy hxy => sortTuple_injOn hcard x hx y hy hxy)
  rw [sortTuple_image hcard] at h
  exact h

/-- **The `Finset` side and the tuple side agree, for intersections.** -/
theorem iInter_eq_sortTuple {k : ℕ} {S : Finset ℕ} (hcard : S.card = k) (E : ℕ → Set ℝ) :
    (⋂ x ∈ (S : Set ℕ), E x) = ⋂ ℓ ∈ (Finset.range k : Set ℕ), E (sortTuple S hcard ℓ) := by
  ext α
  simp only [Set.mem_iInter, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro h ℓ hℓ
    exact h _ (sortTuple_mem hcard hℓ)
  · intro h x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := sortTuple_surj hcard hx
    exact h ℓ hℓ

/-- **The recorded bookkeeping step, discharged.**  A separated `k`-element
subset of the deterministic bulk is the image of a `Section4.GoodTuple`, and
both sides of Proposition 4.1 transfer along the sorting bijection. -/
theorem exists_goodTuple_of_sepGoodSet {n k : ℕ} {S : Finset ℕ} (hcard : S.card = k)
    (hS : TupleFinal.SepGoodSet n S) :
    ∃ j : ℕ → ℕ, GoodTuple n k j ∧
      (∀ f : ℕ → ℝ, ∏ x ∈ S, f x = ∏ ℓ ∈ Finset.range k, f (j ℓ)) ∧
      (∀ E : ℕ → Set ℝ,
        (⋂ x ∈ (S : Set ℕ), E x) = ⋂ ℓ ∈ (Finset.range k : Set ℕ), E (j ℓ)) := by
  classical
  obtain ⟨hsub, hsep, hres⟩ := hS
  refine ⟨sortTuple S hcard, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩,
    prod_eq_sortTuple hcard, iInter_eq_sortTuple hcard⟩
  · intro ℓ hℓ
    simp only [sortTuple, dif_neg (not_lt.mpr hℓ)]
  · intro ℓ ℓ' hlt hℓ'
    exact sortTuple_strictMono hcard hlt hℓ'
  · intro ℓ hℓ
    exact hsub (sortTuple_mem hcard hℓ)
  · intro ℓ hℓ
    have hℓk : ℓ < k := by omega
    have hne : sortTuple S hcard ℓ ≠ sortTuple S hcard (ℓ + 1) :=
      ne_of_lt (sortTuple_strictMono hcard (Nat.lt_succ_self ℓ) hℓ)
    have h := hsep _ (sortTuple_mem hcard hℓk) _ (sortTuple_mem hcard hℓ) hne
    have hlt := sortTuple_strictMono hcard (Nat.lt_succ_self ℓ) hℓ
    have hcast : (0 : ℝ) ≤ (sortTuple S hcard (ℓ + 1) : ℝ) - (sortTuple S hcard ℓ : ℝ) := by
      have : (sortTuple S hcard ℓ : ℝ) ≤ (sortTuple S hcard (ℓ + 1) : ℝ) := by
        exact_mod_cast hlt.le
      linarith
    rwa [abs_of_nonneg hcast] at h
  · intro i ℓ hiℓ hℓ
    have hik : i < k := lt_trans hiℓ hℓ
    have hne : sortTuple S hcard i ≠ sortTuple S hcard ℓ :=
      ne_of_lt (sortTuple_strictMono hcard hiℓ hℓ)
    exact hres _ (sortTuple_mem hcard hik) _ (sortTuple_mem hcard hℓ) hne

/-! ## Part 2, the symbol class is continuous, so `1_B` is not in it -/

lemma continuous_torusChar : Continuous torusChar := by
  unfold torusChar
  fun_prop

/-- **Every symbol of `P_D(L)` is continuous in `θ`.**  Display (24) makes the
coefficient family vanish outside `|v| ≤ L^D`, so the `tsum` is a finite
trigonometric sum. -/
theorem continuous_of_isInPD {D L : ℝ} {F : ℕ → ℝ → ℂ} (h : IsInPD D L F) (a : ℕ) :
    Continuous (F a) := by
  classical
  obtain ⟨c, _hca, hcv, _hsum, hrep⟩ := h
  set N : ℤ := ⌈L ^ D⌉ with hN
  set s : Finset ℤ := Finset.Icc (-N) N with hs
  have hkey : ∀ v : ℤ, v ∉ s → L ^ D < |(v : ℝ)| := by
    intro v hv
    have hle : (L ^ D) ≤ (N : ℝ) := by
      rw [hN]; exact_mod_cast Int.le_ceil (L ^ D)
    simp only [hs, Finset.mem_Icc, not_and_or, not_le] at hv
    rcases hv with hv | hv
    · have h2 : (v : ℝ) < ((-N : ℤ) : ℝ) := by exact_mod_cast hv
      push_cast at h2
      have h3 : L ^ D < -(v : ℝ) := by linarith
      exact lt_of_lt_of_le h3 (neg_le_abs _)
    · have h2 : ((N : ℤ) : ℝ) < (v : ℝ) := by exact_mod_cast hv
      have h3 : L ^ D < (v : ℝ) := by linarith
      exact lt_of_lt_of_le h3 (le_abs_self _)
  have hfin : ∀ θ : ℝ, F a θ = ∑ v ∈ s, c a v * torusChar ((v : ℝ) * θ) := by
    intro θ
    rw [hrep a θ]
    refine tsum_eq_sum ?_
    intro v hv
    rw [hcv a v (hkey v hv), zero_mul]
  rw [show F a = fun θ => ∑ v ∈ s, c a v * torusChar ((v : ℝ) * θ) from funext hfin]
  exact continuous_finset_sum _ fun v _ =>
    continuous_const.mul (continuous_torusChar.comp (continuous_const.mul continuous_id))

/-- **The gate.**  A symbol of `P_D(L)` that takes only the values `0` and `1`
is constant in `θ`.  Hence the indicator `θ ↦ 1_B(mark)` of
`TupleFinal.goodSet_mark_factorization` is a member of the class only in the
degenerate cases; the Jackson step is an approximation, not a membership. -/
theorem isInPD_const_of_two_valued {D L : ℝ} {F : ℕ → ℝ → ℂ} (h : IsInPD D L F)
    (a : ℕ) (h01 : ∀ θ : ℝ, F a θ = 0 ∨ F a θ = 1) (θ₁ θ₂ : ℝ) :
    F a θ₁ = F a θ₂ := by
  have hcont := continuous_of_isInPD h a
  set s : Set ℝ := (F a) ⁻¹' {0} with hsdef
  have hsclosed : IsClosed s := isClosed_singleton.preimage hcont
  have htclosed : IsClosed ((F a) ⁻¹' {1}) := isClosed_singleton.preimage hcont
  have hcompl : sᶜ = (F a) ⁻¹' {1} := by
    ext θ
    simp only [hsdef, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hne
      rcases h01 θ with h0 | h1
      · exact absurd h0 hne
      · exact h1
    · intro h1 h0
      rw [h0] at h1
      exact zero_ne_one h1
  have hsopen : IsOpen s := by
    rw [← isClosed_compl_iff, hcompl]; exact htclosed
  have hclopen : IsClopen s := ⟨hsclosed, hsopen⟩
  rcases isClopen_iff.mp hclopen with hemp | huniv
  · have h1 : ∀ θ : ℝ, F a θ = 1 := by
      intro θ
      rcases h01 θ with h0 | h1
      · exact absurd (show θ ∈ s from h0) (by rw [hemp]; exact Set.notMem_empty θ)
      · exact h1
    rw [h1 θ₁, h1 θ₂]
  · have h0 : ∀ θ : ℝ, F a θ = 0 := by
      intro θ
      have : θ ∈ s := by rw [huniv]; trivial
      exact this
    rw [h0 θ₁, h0 θ₂]

end

end JacksonGate

end Kwon1002
