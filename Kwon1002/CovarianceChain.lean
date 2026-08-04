import Kwon1002.OffDiagFinal

/-!
# CovarianceChain, the off-diagonal covariance chain of Lemma 5.2

Targets, each reproduced **token for token** (mechanically diffed against the
source; only the theorem name carries the `_od` suffix):

1. `Kwon1002.OffDiag.bulk_offdiagonal_far`    (`Kwon1002/OffDiagonal.lean` 870-875)
  , which is also `Kwon1002.bulk_offdiagonal_far'` (`Kwon1002/FiveFinal.lean`
   370-375), the two being the same statement;
2. `Kwon1002.L2Estimate.bulk_offdiagonal_input` (`Kwon1002/L2Estimate.lean` 570-575);
3. `Kwon1002.truncatedBulkSum_centered_L2`     (`Kwon1002/SmallJumps.lean` 504-509);
4. `Kwon1002.bulk_offdiagonal_far_sharp`       (`Kwon1002/FiveFinal.lean` 388-393).

All four are proved here from **one** residual, `farWindow_sum_small` of §3,
which is *strictly weaker* than every residual previously used for this chain.
Each statement block was diffed mechanically against its source; the diffs are
empty apart from the theorem name and the source's own `sorry`/docstring lines.

**Axiom audit** (`#print axioms` run on every declaration, then removed):
everything proved outright, `markSymbol`, `truncatedMark_eq_symbol`,
`bulkTerm_eq_indicator_symbol`, `farWindowPairs_subset`,
`card_farWindowPairs_le`, `sdiff_union_nearPairs_eq`,
`farWindow_sum_small_of_covariance_decay`, `logFactor_le_rpow`,
`card_le_sharp`, reports exactly `[propext, Classical.choice, Quot.sound]`.
The four targets report those three plus `sorryAx`, coming from
`farWindow_sum_small` and from nothing else.

## What is new here

* **§1, the §5 summand is a §4 symbol times the stopping-time indicator,
  and nothing else** (`bulkTerm_eq_indicator_symbol`, proved).  Writing
  `G_{ε,L}(a,θ) = a·W(θ)·1{a·W(θ) ≤ εL}`, one has *definitionally*
  `Z^{(ε)}_{n,j} = G_{ε,L}(a_{j+1}, θ_j)`, hence

    `bulkTerm c ε α n j = 1{j ∈ J_n(α)} · G_{ε,L}(a_{j+1}(α), θ_j(α)) / L`.

  This is the machine-checked form of the (F2) obstruction recorded in
  `Kwon1002/OffDiagFinal.lean`: the summand is *exactly* of the two-argument
  shape `F(a_{j+1}, θ_j)` that Proposition 4.1's display (27) integrates -
  the **only** thing standing between §5 and §4 is the factor
  `1{j ∈ bulkIndices c α n} = 1{cH ≤ j}·1{j < τ_n(α)}`.  Since
  `τ_n(α) = min{j : N_j = 0}` and `N_j = nβ_{j-1} − E_j` with `E_j` bounded
  (`Kwon1002.heightError_mem_Icc`), that factor is a condition on the
  *integer part* of `nβ_{j-1}`, whereas `θ_j = {nβ_j}` is its fractional
  part: no symbol `F(a,θ) ∈ P_D(L)` can carry it.  Removing it is §7's
  Lemma 7.1 (`τ_n = m_n + O_P(H)`), which is where the manuscript puts it -
  Kwon's (41) is stated over the *deterministic* `J_n` of (19), so the
  manuscript never meets this factor at all.

* **§3-§4, a strictly weaker residual, with the weakening machine-checked.**
  `farWindow_sum_small` asks only for a bound on the *sum* of the covariances
  over the far pairs of the Lamé window; the previous residual for this chain,
  `Kwon1002.OffDiagFinal.farPair_covariance_decay`, asks for a bound on each
  such covariance *individually*.  §4 proves the implication
  `farPair_covariance_decay ⟹ farWindow_sum_small` as a theorem taking the
  former as an explicit hypothesis (so the implication itself is axiom-clean),
  and an `example` checks that the hypothesis is the `OffDiagFinal` statement
  on the nose.  A summed bound is the currency Proposition 4.1 produces after
  the pair count, so this is the shape a discharge would actually arrive in.

## Findings

**(F4)  `digit_tail_product` (Lemma 3.1(ii)) cannot produce the off-diagonal
bound, however it is used.**  The task brief for this pass records
`digit_tail_product` as "the product bound over distinct levels, this IS the
decorrelation".  It is not, and the gap is structural rather than technical.
The proved statement carries a constant *per level*,

  `P(a_{j+1} ≥ A₁, a_{k+1} ≥ A₂) ≤ C² /(A₁A₂)`   with `C = 24`,

so what it yields is `E[Z_j Z_k] ≤ C·(1+log(2+L))²`, display (42)'s second
half, which is exactly how the tree already uses it
(`OffDiag.truncatedMark_joint_moment`, proved).  The off-diagonal needs
`|E[Z_j Z_k] − E Z_j · E Z_k| ≤ δ` with `δ` an *absolute constant*, while
`E Z_j ≍ log L`; i.e. it needs the product structure to hold to *relative*
precision `1/log²L`.  A joint-tail bound that loses a multiplicative
constant is compatible with `E[Z_jZ_k] = C·E Z_j·E Z_k`, `C ≠ 1`, and hence
cannot bound a covariance at all.  This is why the manuscript, at exactly
this point, stops using §3 and invokes Proposition 4.1 (whose error is
`O_A(L^{-A})`, i.e. *additive* and arbitrarily small).  The same remark
disposes of the neighbouring suggestion that the substrate's
quasi-Bernoulli/bounded-distortion inequality (`ν(E ∩ T⁻ᵐB) ≤ 6 ν(E)ν(B)`)
could serve: it too is a constant-factor bound.

**(F5)  `Bridge.good_tuple_multiblock_mixing'` does not reach this chain,
and §1 says exactly why.**  It bounds
`|∫ ∏ᵢ gᵢ(T^{jᵢ}α) − ∏ᵢ ∫ gᵢ|` for `BV` observables of the *orbit point*.
By §1 the summand here is `1{j < τ_n}·G(a_{j+1}, θ_j)/L`: the first factor is
not a function of `T^{j}α` at all (it depends on `n` and on the whole past),
and the second is a function of `T^{j}α` only through `a_{j+1}`, the argument
`θ_j = {nβ_j}` being a function of the whole past as well.  This confirms,
from the definitions rather than from a docstring, the (F3) finding of
`Kwon1002/OffDiagFinal.lean`.  Two-block mixing enters §4 only as the
`v = 0` branch of Proposition 4.1 (`ErrorShape.zero_mode_factorization`,
proved), and the branch that is still open is `v ≠ 0`
(`ErrorShape.nonzero_mode_small`).

**(F6)  The residual really is the last §5 step, and it is a §4 statement.**
With §1 in hand, `farWindow_sum_small` for a pair `(j,k)` is display (27) of
Proposition 4.1 at `r = 2` for the symbol `G_{ε,L}`, *plus* the digit cut at
`A_L = L^D` and the `L¹` (rather than Jackson) approximation forced by the
hard truncation, *plus* the stopping-time factor of (F2).  Only the last of
these is absent from the manuscript.

## Sorried results consumed

**Exactly one**, and it is stated in this file: `farWindow_sum_small`.
Nothing else here rests on a `sorry`.  In particular
`OffDiag.bulkTermCentered_offdiag_bound`, `OffDiag.near_pair_decay`,
`OffDiag.sum_offdiag_eq`, `OffDiagFinal.offdiagTerm_eq_zero_of_lame`,
`OffDiagFinal.card_nearPairs_le`, `OffDiagFinal.lameIdx_le`,
`L2Estimate.bulk_window_input`, `L2Estimate.truncatedMark_second_moment`,
`L2Estimate.diagonal_le_second_moment`, `L2Estimate.bulkTerm_sq_integral_le`,
`L2Estimate.sum_split_diag`, `Kwon1002.integral_centered_eq` and
`Kwon1002.centered_second_moment_expand` are all proved where they live.
Neither `OffDiag.bulk_offdiagonal_far` nor
`OffDiagFinal.farPair_covariance_decay` is used: the latter appears only as
an explicit *hypothesis* in §4 and in one `example`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace CovarianceChain

open OffDiag OffDiagFinal

noncomputable section

/-! ## 1. The §5 summand is a §4 symbol times the stopping-time indicator

`G_{ε,L}(a,θ) = a·W(θ)·1{a·W(θ) ≤ εL}` is a function of the two arguments
`(a_{j+1}, θ_j)` that display (27) integrates.  `truncatedMark` *is* that
function evaluated at `(a_{j+1}(α), θ_j(α))`, the proof is `rfl`, and
`bulkTerm` is it times the indicator of the random index set. -/

/-- The §5 mark read as a two-argument §4 symbol: the hard truncation at
`εL` of `a·W(θ)`. -/
def markSymbol (ε L : ℝ) (a : ℕ) (θ : ℝ) : ℝ :=
  if (a : ℝ) * W θ ≤ ε * L then (a : ℝ) * W θ else 0

/-- `Z^{(ε)}_{n,j} = G_{ε,L}(a_{j+1}, θ_j)`, definitionally. -/
lemma truncatedMark_eq_symbol (ε α : ℝ) (n j : ℕ) :
    truncatedMark ε α n j = markSymbol ε (Lnorm n) (digit α j) (theta α n j) := rfl

/-- **The whole distance between §5 and §4, made explicit.**  The `j`-th
summand of (41) is the §4 symbol `G_{ε,L}` evaluated at `(a_{j+1}, θ_j)`,
normalized by `L`, times the indicator of the random bulk index set.  Every
other feature of the summand is already of display (27)'s shape. -/
lemma bulkTerm_eq_indicator_symbol (c ε α : ℝ) (n j : ℕ) :
    bulkTerm c ε α n j
      = (if j ∈ bulkIndices c α n then (1 : ℝ) else 0)
          * (markSymbol ε (Lnorm n) (digit α j) (theta α n j) / Lnorm n) := by
  unfold bulkTerm
  split_ifs with h
  · rw [one_mul, truncatedMark_eq_symbol]
  · rw [zero_mul]

/-! ## 2. The far pairs of the Lamé window

`offdiagTerm` vanishes identically off the Lamé window
(`OffDiagFinal.offdiagTerm_eq_zero_of_lame`, proved), and the pairs of the
window at distance `≤ H` are the manuscript's overlapping and `H`-near pairs
(`OffDiagFinal.nearPairs`, counted there).  What is left is: -/

/-- The pairs of `{0,…,n}²` that lie in the Lamé window and are at distance
more than `H`. -/
def farWindowPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => p.1 < lameIdx n ∧ p.2 < lameIdx n ∧ Hscale n < |(p.1 : ℝ) - (p.2 : ℝ)|)

lemma farWindowPairs_subset (n : ℕ) :
    farWindowPairs n ⊆ Finset.range (n + 1) ×ˢ Finset.range (n + 1) :=
  Finset.filter_subset _ _

lemma card_farWindowPairs_le (n : ℕ) :
    (((farWindowPairs n).card : ℕ) : ℝ) ≤ (lameIdx n : ℝ) * (lameIdx n : ℝ) := by
  classical
  have hsub : farWindowPairs n ⊆ Finset.range (lameIdx n) ×ˢ Finset.range (lameIdx n) := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr h.1, Finset.mem_range.mpr h.2.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range] at hcard
  have : (((farWindowPairs n).card : ℕ) : ℝ) ≤ ((lameIdx n * lameIdx n : ℕ) : ℝ) := by
    exact_mod_cast hcard
  simpa using this

/-- The window splits into the near pairs and the far pairs: on `{0,…,n}²`
intersected with the window, "not near" is "far". -/
lemma sdiff_union_nearPairs_eq (n : ℕ) (R : Finset (ℕ × ℕ)) :
    (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ (nearPairs n ∪ R)).filter
        (fun p => p.1 < lameIdx n ∧ p.2 < lameIdx n))
      = farWindowPairs n \ R := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpPB, hcond⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, hpB⟩ := Finset.mem_sdiff.mp hpPB
    rw [Finset.mem_union, not_or] at hpB
    refine Finset.mem_sdiff.mpr ⟨?_, hpB.2⟩
    refine Finset.mem_filter.mpr ⟨hpP, hcond.1, hcond.2, ?_⟩
    by_contra hcon
    push_neg at hcon
    exact hpB.1 (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hcond.1,
        Finset.mem_range.mpr hcond.2⟩, hcon⟩)
  · intro hp
    obtain ⟨hpF, hpR⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpP, hcond⟩ := Finset.mem_filter.mp hpF
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hpP, ?_⟩, hcond.1, hcond.2.1⟩
    rw [Finset.mem_union, not_or]
    refine ⟨fun hn => ?_, hpR⟩
    have hnear := (Finset.mem_filter.mp hn).2
    linarith [hcond.2.2]

/-! ## 3. The residual

**Proposition 4.1 for pairs, in summed form.**  There is a set `R` of pairs
with `#R = O(L·H)`, the manuscript's resonance-near pairs, the ones
`Kwon1002.nonGood_tuple_count` counts at `r = 2`, outside of which the
covariances of the far pairs of the Lamé window sum to at most `δ`, for every
`δ > 0` and all large `n`.

Compared with `Kwon1002.OffDiag.bulk_offdiagonal_far` this is weaker on two
counts and stronger on none:

* the sum runs only over the far pairs of the Lamé window, the remaining
  pairs of `{0,…,n}²` being handled here, the ones outside the window
  contribute *exactly* `0`
  (`OffDiagFinal.offdiagTerm_eq_zero_of_lame`, proved) and the `H`-near ones
  are paid for by display (42)'s second half
  (`OffDiag.bulkTermCentered_offdiag_bound` and `OffDiag.near_pair_decay`,
  both proved);
* the bound is `δ` for an arbitrary `δ > 0` rather than `ε/2`; this is a
  *strengthening* of the hypothesis in isolation, but it is the form
  Proposition 4.1 supplies (its error is `O_A(L^{-A})` with `A` free), and it
  is what lets the near-pair budget be paid out of the same `ε`.

Compared with `Kwon1002.OffDiagFinal.farPair_covariance_decay` it is weaker:
that statement bounds each far-pair covariance individually by `δ/L²`, and
§4 below derives this one from it.

**What a discharge must supply**, beyond what is proved in this file:

* `Kwon1002.Prop41.prop_4_1_error_shape` at `r = 2`, and inside it the
  `vₛ ≠ 0` branch `Kwon1002.ErrorShape.nonzero_mode_small`, still the one
  open statement of §4 (`Kwon1002/Prop41Final.lean` reduces (30) to exactly
  it);
* the digit cut at `A_L = L^D` (`D > 2`) and, since
  `Kwon1002.truncatedMark` is the *hard* truncation, an `L¹` approximation of
  `z ↦ z·1{z ≤ εL}` in place of the manuscript's Jackson step, the symbol
  `markSymbol` of §1 is bounded and monotone but not Lipschitz;
* the removal of the stopping-time factor isolated in §1, which display (27)
  knows nothing about and which the manuscript never meets, its (41) being
  stated over the deterministic `J_n` of (19). -/
theorem farWindow_sum_small (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ R : Finset (ℕ × ℕ),
          ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
          ∑ p ∈ farWindowPairs n \ R, offdiagTerm c ε n p ≤ δ := by
  sorry

/-! ## 4. The residual is weaker than the previous one

`farPair_covariance_decay` of `Kwon1002/OffDiagFinal.lean` is reproduced here
as an explicit hypothesis (token for token; the `example` after the theorem
checks that it is that statement and not a look-alike), and
`farWindow_sum_small` is derived from it.  The derivation is axiom-clean, so
the weakening is machine-checked rather than asserted. -/
theorem farWindow_sum_small_of_covariance_decay (c : ℝ)
    (hcov : ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ R : Finset (ℕ × ℕ),
          ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
          ∀ j k : ℕ, j < lameIdx n → k < lameIdx n →
            Hscale n < |(j : ℝ) - (k : ℝ)| → (j, k) ∉ R →
            (∫ α in Ioo (0:ℝ) 1,
                bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
              ≤ δ / (Lnorm n) ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ R : Finset (ℕ × ℕ),
          ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
          ∑ p ∈ farWindowPairs n \ R, offdiagTerm c ε n p ≤ δ := by
  classical
  obtain ⟨κR, hκR, hres⟩ := hcov
  set κ₀ : ℝ := 2 / Real.log 2 + 3 with hκ₀def
  have hκ₀0 : 0 < κ₀ := by
    have : (0:ℝ) < 2 / Real.log 2 := div_pos (by norm_num) log_two_pos
    rw [hκ₀def]; linarith
  refine ⟨κR, hκR, ?_⟩
  intro ε hε hε1 δ hδ
  obtain ⟨N₁, hN₁⟩ := hres ε hε hε1 (δ / κ₀ ^ 2) (by positivity)
  refine ⟨max N₁ 3, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL1 : (1:ℝ) ≤ Lnorm n := one_le_Lnorm n hn3
  have hH1 : (1:ℝ) ≤ Hscale n := one_le_Hscale n hL1
  obtain ⟨R, hRcard, hRfar⟩ := hN₁ n hn1
  refine ⟨R, hRcard, ?_⟩
  set T : ℕ := lameIdx n with hTdef
  have hT : (T : ℝ) ≤ κ₀ * Lnorm n := by
    have h := lameIdx_le n (by linarith)
    have h2 : 2 * Lnorm n / Real.log 2 = (2 / Real.log 2) * Lnorm n := by field_simp
    rw [hTdef, hκ₀def]
    rw [h2] at h
    nlinarith [h, hL1]
  have hLpos : (0:ℝ) < (Lnorm n) ^ 2 := by nlinarith
  have hq0 : (0:ℝ) ≤ δ / κ₀ ^ 2 / (Lnorm n) ^ 2 := by positivity
  have hbd : ∀ p ∈ farWindowPairs n \ R,
      offdiagTerm c ε n p ≤ δ / κ₀ ^ 2 / (Lnorm n) ^ 2 := by
    intro p hp
    obtain ⟨hpF, hpR⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨-, hcond⟩ := Finset.mem_filter.mp hpF
    have hfar : Hscale n < |(p.1 : ℝ) - (p.2 : ℝ)| := hcond.2.2
    have hne : p.1 ≠ p.2 := by
      intro heq
      rw [heq] at hfar
      simp at hfar
      linarith
    unfold offdiagTerm
    rw [if_neg hne]
    exact hRfar p.1 p.2 hcond.1 hcond.2.1 hfar (by simpa using hpR)
  have hsum := Finset.sum_le_card_nsmul (farWindowPairs n \ R) (offdiagTerm c ε n)
    (δ / κ₀ ^ 2 / (Lnorm n) ^ 2) hbd
  rw [nsmul_eq_mul] at hsum
  refine le_trans hsum ?_
  have hcard : (((farWindowPairs n \ R).card : ℕ) : ℝ) ≤ (T : ℝ) * (T : ℝ) := by
    refine le_trans ?_ (card_farWindowPairs_le n)
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
  have hT0 : (0:ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
  have hstep : (((farWindowPairs n \ R).card : ℕ) : ℝ) * (δ / κ₀ ^ 2 / (Lnorm n) ^ 2)
      ≤ ((T : ℝ) * (T : ℝ)) * (δ / κ₀ ^ 2 / (Lnorm n) ^ 2) :=
    mul_le_mul_of_nonneg_right hcard hq0
  refine le_trans hstep ?_
  have hTT : (T : ℝ) * (T : ℝ) ≤ (κ₀ * Lnorm n) * (κ₀ * Lnorm n) := by
    nlinarith [hT, hT0, hκ₀0, hL1]
  have hfin : ((κ₀ * Lnorm n) * (κ₀ * Lnorm n)) * (δ / κ₀ ^ 2 / (Lnorm n) ^ 2) = δ := by
    field_simp
  calc ((T : ℝ) * (T : ℝ)) * (δ / κ₀ ^ 2 / (Lnorm n) ^ 2)
      ≤ ((κ₀ * Lnorm n) * (κ₀ * Lnorm n)) * (δ / κ₀ ^ 2 / (Lnorm n) ^ 2) :=
        mul_le_mul_of_nonneg_right hTT hq0
    _ = δ := hfin

/-- The hypothesis of `farWindow_sum_small_of_covariance_decay` is exactly
`Kwon1002.OffDiagFinal.farPair_covariance_decay`. -/
example (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ R : Finset (ℕ × ℕ),
          ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
          ∀ j k : ℕ, j < lameIdx n → k < lameIdx n →
            Hscale n < |(j : ℝ) - (k : ℝ)| → (j, k) ∉ R →
            (∫ α in Ioo (0:ℝ) 1,
                bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
              ≤ δ / (Lnorm n) ^ 2 :=
  OffDiagFinal.farPair_covariance_decay c

/-! ## 5. Target 1, `OffDiag.bulk_offdiagonal_far`

Reproduced token for token from `Kwon1002/OffDiagonal.lean` (lines 870-875);
this is also `Kwon1002.bulk_offdiagonal_far'` of `Kwon1002/FiveFinal.lean`
(lines 370-375), the two statements being identical. -/
theorem bulk_offdiagonal_far_od (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagTerm c ε n p ≤ ε / 2 := by
  classical
  obtain ⟨κR, hκR, hres⟩ := farWindow_sum_small c
  set κ₀ : ℝ := 2 / Real.log 2 + 3 with hκ₀def
  have hκ₀0 : 0 < κ₀ := by
    have : (0:ℝ) < 2 / Real.log 2 := div_pos (by norm_num) log_two_pos
    rw [hκ₀def]; linarith
  refine ⟨3 * κ₀ + κR, by linarith, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hres ε hε hε1 (ε / 2) (by positivity)
  refine ⟨max N₁ 3, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 1 ≤ n := by omega
  have hL1 : (1:ℝ) ≤ Lnorm n := one_le_Lnorm n hn3
  have hH1 : (1:ℝ) ≤ Hscale n := one_le_Hscale n hL1
  obtain ⟨R, hRcard, hRsum⟩ := hN₁ n hn1
  have hT : ((lameIdx n : ℕ) : ℝ) ≤ κ₀ * Lnorm n := by
    have h := lameIdx_le n (by linarith)
    have h2 : 2 * Lnorm n / Real.log 2 = (2 / Real.log 2) * Lnorm n := by field_simp
    rw [hκ₀def]
    rw [h2] at h
    nlinarith [h, hL1]
  refine ⟨nearPairs n ∪ R, ?_, ?_⟩
  · -- the count: `#nearPairs ≤ T(2H+1) ≤ 3κ₀ L H`, and `#R ≤ κR L H`
    have hcu : ((nearPairs n ∪ R).card : ℝ) ≤ ((nearPairs n).card : ℝ) + (R.card : ℝ) := by
      have := Finset.card_union_le (nearPairs n) R
      exact_mod_cast this
    have hnear := card_nearPairs_le n (by linarith)
    have hstep : ((lameIdx n : ℕ) : ℝ) * (2 * Hscale n + 1)
        ≤ (3 * κ₀) * Lnorm n * Hscale n := by
      have h1 : 2 * Hscale n + 1 ≤ 3 * Hscale n := by linarith
      have h2 : (0:ℝ) ≤ ((lameIdx n : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hT, h1, h2, hH1, hL1]
    linarith [hcu, hnear, hRcard, hstep]
  · -- the sum: off the window every term is `0`, and on it the near pairs
    -- have been removed, so what is left is the residual's own sum
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ (nearPairs n ∪ R))
      (fun p : ℕ × ℕ => p.1 < lameIdx n ∧ p.2 < lameIdx n) (offdiagTerm c ε n)
    have houter : (∑ p ∈ (((Finset.range (n + 1) ×ˢ Finset.range (n + 1))
          \ (nearPairs n ∪ R)).filter
          (fun p : ℕ × ℕ => ¬ (p.1 < lameIdx n ∧ p.2 < lameIdx n))),
        offdiagTerm c ε n p) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have h := (Finset.mem_filter.mp hp).2
      simp only [not_and_or, not_lt] at h
      exact offdiagTerm_eq_zero_of_lame c ε n p hnpos h
    have hinner : (∑ p ∈ (((Finset.range (n + 1) ×ˢ Finset.range (n + 1))
          \ (nearPairs n ∪ R)).filter
          (fun p : ℕ × ℕ => p.1 < lameIdx n ∧ p.2 < lameIdx n)),
        offdiagTerm c ε n p) ≤ ε / 2 := by
      rw [sdiff_union_nearPairs_eq n R]
      exact hRsum
    linarith [hsplit, houter, hinner]

/-! ## 6. Target 2, `L2Estimate.bulk_offdiagonal_input`

Reproduced token for token from `Kwon1002/L2Estimate.lean` (lines 570-575).
The proof body is `OffDiag.bulk_offdiagonal_input'` verbatim, with the
sorried `OffDiag.bulk_offdiagonal_far` replaced by `bulk_offdiagonal_far_od`. -/
theorem bulk_offdiagonal_input_od (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            ∫ α in Ioo (0:ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k) ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hpair⟩ := bulkTermCentered_offdiag_bound c
  obtain ⟨κ, hκ, hfar⟩ := bulk_offdiagonal_far_od c
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hfar ε hε hε1
  obtain ⟨N₂, hN₂⟩ := near_pair_decay κ Cp (ε / 2) hκ hCp (by positivity)
  refine ⟨max (max N₁ N₂) 3, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨B, hBcard, hBfar⟩ := hN₁ n hn1
  rw [sum_offdiag_eq c ε n]
  set P : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hP
  have hsplit : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagTerm c ε n p)
      + ∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagTerm c ε n p
      = ∑ p ∈ P, offdiagTerm c ε n p :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ∈ B) _
  have hnotB : P.filter (fun p => ¬ p ∈ B) = P \ B := (Finset.sdiff_eq_filter P B).symm
  have hQ0 : (0:ℝ) ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by positivity
  have hbound : ∀ p ∈ P.filter (fun p => p ∈ B),
      offdiagTerm c ε n p ≤ Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2 := by
    intro p _
    simp only [offdiagTerm]
    by_cases hpq : p.1 = p.2
    · rw [if_pos hpq]
      exact hQ0
    · rw [if_neg hpq]
      exact le_trans (le_abs_self _) (hpair ε hε hε1 n p.1 p.2 hpq hL)
  have hnear : (∑ p ∈ P.filter (fun p => p ∈ B), offdiagTerm c ε n p) ≤ ε / 2 := by
    have hb := Finset.sum_le_card_nsmul (P.filter (fun p => p ∈ B)) (offdiagTerm c ε n)
      (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) hbound
    rw [nsmul_eq_mul] at hb
    refine le_trans hb ?_
    have hcard : (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ) ≤ κ * Lnorm n * Hscale n := by
      refine le_trans ?_ hBcard
      exact_mod_cast Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).2)
    calc (((P.filter (fun p => p ∈ B)).card : ℕ) : ℝ)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2)
        ≤ (κ * Lnorm n * Hscale n)
            * (Cp * (1 + Real.log (2 + Lnorm n)) ^ 2 / (Lnorm n) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard hQ0
      _ ≤ ε / 2 := hN₂ n hn2
  have hfarsum : (∑ p ∈ P.filter (fun p => ¬ p ∈ B), offdiagTerm c ε n p) ≤ ε / 2 := by
    rw [hnotB]
    exact hBfar
  linarith [hsplit, hnear, hfarsum]

/-! ## 7. Target 3, `Kwon1002.truncatedBulkSum_centered_L2`

Reproduced token for token from `Kwon1002/SmallJumps.lean` (lines 504-509).
The proof body is `OffDiag.truncatedBulkSum_centered_L2'` verbatim, with
`bulk_offdiagonal_input'` replaced by `bulk_offdiagonal_input_od`.  This is
the statement whose discharge makes the already-proved
`Kwon1002.SmallJumps.small_jumps_variance` (Lemma 5.2) unconditional. -/
theorem truncatedBulkSum_centered_L2_od (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ b : ℝ,
        (∫ α in Ioo (0 : ℝ) 1,
            (∑ j ∈ bulkIndices c α n, truncatedMark ε α n j / Lnorm n - b) ^ 2)
          ≤ C * ε := by
  haveI := isProbabilityMeasure_restrict_Ioo
  obtain ⟨C₂, hC₂, hsm⟩ := L2Estimate.truncatedMark_second_moment
  obtain ⟨κ, hκ, hwin⟩ := L2Estimate.bulk_window_input c
  refine ⟨κ * C₂ + 2, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hwin ε hε hε1
  obtain ⟨N₂, hN₂⟩ := bulk_offdiagonal_input_od c ε hε hε1
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 0 < Lnorm n := by
    unfold Lnorm
    refine Real.log_pos ?_
    have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
    linarith
  obtain ⟨S, hSsub, hScard, hStail⟩ := hN₁ n hn1
  refine ⟨∑ j ∈ Finset.range (n + 1), ∫ β in Ioo (0:ℝ) 1, bulkTerm c ε β n j, ?_⟩
  rw [integral_centered_eq, centered_second_moment_expand c ε hε.le n]
  refine le_trans (le_of_eq (L2Estimate.sum_split_diag (n + 1) (fun j k =>
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n k))) ?_
  have hoff := hN₂ n hn2
  have hdiagterm : ∀ j : ℕ,
      (∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∫ α in Ioo (0:ℝ) 1, (bulkTerm c ε α n j) ^ 2 :=
    fun j => L2Estimate.diagonal_le_second_moment c ε hε n j
  have hSbound : (∑ j ∈ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε := by
    calc (∑ j ∈ S,
        ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
        ≤ ∑ _j ∈ S, (C₂ * ε / Lnorm n) := by
          refine Finset.sum_le_sum fun j _ => le_trans (hdiagterm j) ?_
          exact L2Estimate.bulkTerm_sq_integral_le c ε hε n j hL C₂ (hsm ε hε.le n j)
      _ = (S.card : ℝ) * (C₂ * ε / Lnorm n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (κ * Lnorm n) * (C₂ * ε / Lnorm n) := by
          refine mul_le_mul_of_nonneg_right hScard ?_
          have : (0:ℝ) ≤ C₂ * ε := by positivity
          positivity
      _ = κ * C₂ * ε := by field_simp
  have hRestBound : (∑ j ∈ Finset.range (n + 1) \ S,
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ ε :=
    le_trans (Finset.sum_le_sum fun j _ => hdiagterm j) hStail
  have hdiag : (∑ j ∈ Finset.range (n + 1),
      ∫ α in Ioo (0:ℝ) 1, bulkTermCentered c ε α n j * bulkTermCentered c ε α n j)
      ≤ κ * C₂ * ε + ε := by
    rw [← Finset.sum_sdiff hSsub]
    linarith [hSbound, hRestBound]
  have hfinal : κ * C₂ * ε + ε + ε ≤ (κ * C₂ + 2) * ε := le_of_eq (by ring)
  linarith [hdiag, hoff, hfinal]

/-! ## 8. The `FiveFinal` variants

`Kwon1002.bulk_offdiagonal_far'` (`Kwon1002/FiveFinal.lean` 370-375) is the
*same statement* as Target 1, so it is discharged by
`bulk_offdiagonal_far_od` verbatim (the `example` below is the check).
`Kwon1002.bulk_offdiagonal_far_sharp` (lines 388-394) is its weakening to a
bad set of size `κ L²/(1+log(2+L))³`, and follows from Target 1 by the
arithmetic `L·H·(1+log(2+L))³ ≤ κ L²`, proved below out of
`log x ≤ 16 x^{1/16}`, no limit argument is needed, the constant `33³` and
`H = L^{3/4}` do it for every `L ≥ 1`. -/

/-- `log x ≤ 16 x^{1/16}` in the form the counting needs. -/
lemma logFactor_le_rpow (n : ℕ) (hL1 : (1:ℝ) ≤ Lnorm n) :
    1 + Real.log (2 + Lnorm n) ≤ 33 * (Lnorm n) ^ (1/16 : ℝ) := by
  have hL0 : (0:ℝ) < Lnorm n := by linarith
  have hv1 : (1:ℝ) ≤ (Lnorm n) ^ (1/16 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL1
      (by norm_num : (0:ℝ) ≤ 1/16)
    simpa using h
  have hv0 : (0:ℝ) < (Lnorm n) ^ (1/16 : ℝ) := lt_of_lt_of_le zero_lt_one hv1
  have hlog := Real.log_le_rpow_div (x := 2 + Lnorm n) (by linarith)
    (show (0:ℝ) < 1/16 by norm_num)
  have hdiv : (2 + Lnorm n) ^ (1/16:ℝ) / (1/16:ℝ) = 16 * (2 + Lnorm n) ^ (1/16:ℝ) := by
    ring
  rw [hdiv] at hlog
  have h3L : (2:ℝ) + Lnorm n ≤ 3 * Lnorm n := by linarith
  have hmono : (2 + Lnorm n) ^ (1/16:ℝ) ≤ (3 * Lnorm n) ^ (1/16:ℝ) :=
    Real.rpow_le_rpow (by linarith) h3L (by norm_num)
  have hsplit : (3 * Lnorm n) ^ (1/16:ℝ)
      = (3:ℝ) ^ (1/16:ℝ) * (Lnorm n) ^ (1/16:ℝ) :=
    Real.mul_rpow (by norm_num) hL0.le
  have h3 : (3:ℝ) ^ (1/16:ℝ) ≤ 2 := by
    have h65 : (3:ℝ) ≤ 65536 := by norm_num
    have hle := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 3) h65
      (by norm_num : (0:ℝ) ≤ 1/16)
    have he : (65536:ℝ) ^ (1/16:ℝ) = 2 := by
      rw [show (65536:ℝ) = (2:ℝ) ^ (16:ℕ) by norm_num,
        ← Real.rpow_natCast (2:ℝ) 16, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [he] at hle
    exact hle
  have step2 : 16 * (2 + Lnorm n) ^ (1/16:ℝ)
      ≤ 16 * ((3:ℝ) ^ (1/16:ℝ) * (Lnorm n) ^ (1/16:ℝ)) := by
    rw [← hsplit]; linarith
  have step3 : 16 * ((3:ℝ) ^ (1/16:ℝ) * (Lnorm n) ^ (1/16:ℝ))
      ≤ 32 * (Lnorm n) ^ (1/16:ℝ) := by nlinarith [hv0.le]
  linarith

/-- `O(L·H)` fits inside `κ L²/(1+log(2+L))³` for every `L ≥ 1`, with
`κ = 33³ κ₁`. -/
lemma card_le_sharp (n : ℕ) (κ₁ x : ℝ) (hκ₁ : 0 < κ₁) (hL1 : (1:ℝ) ≤ Lnorm n)
    (_hx0 : 0 ≤ x) (hxc : x ≤ κ₁ * Lnorm n * Hscale n) :
    x ≤ 35937 * κ₁ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3 := by
  have hL0 : (0:ℝ) < Lnorm n := by linarith
  have hu1 : (1:ℝ) ≤ 1 + Real.log (2 + Lnorm n) := one_le_logFactor n
  have hlog := logFactor_le_rpow n hL1
  have hv1 : (1:ℝ) ≤ (Lnorm n) ^ (1/16 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL1
      (by norm_num : (0:ℝ) ≤ 1/16)
    simpa using h
  have hLv : Lnorm n = ((Lnorm n) ^ (1/16 : ℝ)) ^ (16:ℕ) := by
    rw [← Real.rpow_natCast ((Lnorm n) ^ (1/16:ℝ)) 16, ← Real.rpow_mul hL0.le]
    norm_num
  have hHv : Hscale n = ((Lnorm n) ^ (1/16 : ℝ)) ^ (12:ℕ) := by
    rw [Hscale, ← Real.rpow_natCast ((Lnorm n) ^ (1/16:ℝ)) 12, ← Real.rpow_mul hL0.le]
    norm_num
  set v : ℝ := (Lnorm n) ^ (1/16 : ℝ) with hvdef
  set u : ℝ := 1 + Real.log (2 + Lnorm n) with hudef
  have hu0 : (0:ℝ) ≤ u := by linarith
  have hv0 : (0:ℝ) < v := lt_of_lt_of_le zero_lt_one hv1
  rw [hLv] at hxc ⊢
  rw [hHv] at hxc
  rw [le_div_iff₀ (by positivity : (0:ℝ) < u ^ 3)]
  have hcube : u ^ 3 ≤ 35937 * v ^ 3 := by
    have hp := pow_le_pow_left₀ hu0 hlog 3
    have he : (33 * v) ^ 3 = 35937 * v ^ 3 := by ring
    linarith [hp, he.le, he.ge]
  have h1 : x * u ^ 3 ≤ (κ₁ * v ^ (16:ℕ) * v ^ (12:ℕ)) * (35937 * v ^ 3) :=
    mul_le_mul hxc hcube (by positivity) (by positivity)
  have h2 : (κ₁ * v ^ (16:ℕ) * v ^ (12:ℕ)) * (35937 * v ^ 3)
      = 35937 * κ₁ * v ^ (31:ℕ) := by ring
  have h3 : v ^ (31:ℕ) ≤ v ^ (32:ℕ) := pow_le_pow_right₀ hv1 (by norm_num)
  have h4 : 35937 * κ₁ * (v ^ (16:ℕ)) ^ 2 = 35937 * κ₁ * v ^ (32:ℕ) := by ring
  have h5 : 35937 * κ₁ * v ^ (31:ℕ) ≤ 35937 * κ₁ * v ^ (32:ℕ) := by
    nlinarith [h3, hκ₁.le]
  linarith [h1, h2.le, h2.ge, h4.le, h4.ge, h5]

/-- **`Kwon1002.bulk_offdiagonal_far_sharp`** (`Kwon1002/FiveFinal.lean`
388-394), reproduced token for token and proved from Target 1. -/
theorem bulk_offdiagonal_far_sharp_od (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagTerm c ε n p ≤ ε / 2 := by
  obtain ⟨κ₁, hκ₁, hfar⟩ := bulk_offdiagonal_far_od c
  refine ⟨35937 * κ₁, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨N, hN⟩ := hfar ε hε hε1
  refine ⟨max N 3, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hL1 : (1:ℝ) ≤ Lnorm n := one_le_Lnorm n hn3
  obtain ⟨B, hBcard, hBsum⟩ := hN n hnN
  exact ⟨B, card_le_sharp n κ₁ _ hκ₁ hL1 (Nat.cast_nonneg _) hBcard, hBsum⟩

/-- `Kwon1002.bulk_offdiagonal_far'` of `Kwon1002/FiveFinal.lean` is Target 1
on the nose. -/
example (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagTerm c ε n p ≤ ε / 2 :=
  bulk_offdiagonal_far_od c

end

end CovarianceChain

end Kwon1002
