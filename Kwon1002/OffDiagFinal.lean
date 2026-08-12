import Kwon1002.OffDiagonal

/-!
# OffDiagFinal, the off-diagonal chain of Lemma 5.2, cut down to a far-pair residual

Targets, in the order requested, each reproduced **token for token** (diffed
mechanically against the source; only the name carries a `_scr` suffix):

1. `Kwon1002.OffDiag.bulk_offdiagonal_far`   (`Kwon1002/OffDiagonal.lean` 870-875);
2. `Kwon1002.L2Estimate.bulk_offdiagonal_input` (`Kwon1002/L2Estimate.lean` 571-576);
3. `Kwon1002.truncatedBulkSum_centered_L2`   (`Kwon1002/SmallJumps.lean` 504-509).

2 and 3 are proved from 1; 1 is proved from a single residual,
`farPair_covariance_decay`, stated in §3 below.

## Proved outright (axiom-clean: exactly `propext, Classical.choice, Quot.sound`)

* `lameIdx`, `lame_le_lameIdx`, `lameIdx_le`, the Lamé window
  `T_n = ⌈2L/log 2 + 2⌉`, with `T_n ≤ (2/log 2 + 3)·L` once `L ≥ 1`.
* `bulkTerm_eq_zero_of_lame`, `integral_bulkTerm_eq_zero_of_lame`,
  `bulkTermCentered_eq_zero_of_lame`, `offdiagTerm_eq_zero_of_lame`, **the
  off-diagonal window tail is empty**: every `(j,k)` with `max(j,k) ≥ T_n`
  contributes *exactly* `0` to (41).  This discharges, unconditionally, the
  caveat that `Kwon1002/OffDiagonal.lean` records as "folded into
  `bulk_offdiagonal_far`"; the residual below no longer carries it.
* `sum_offdiag_eq_lame_window`, `card_lame_window_le`, the deterministic
  double sum of (41) is supported on the Lamé window, and that window has at
  most `(2/log 2 + 3)² L²` pairs.  This is the machine-checked form of the
  manuscript's `#J_n = O(L)`, obtained *deterministically* from the Lamé
  bound rather than from §7's Lemma 7.1.
* `nearPairs`, `card_nearPairs_le`, the overlapping and `H`-near pairs of the
  window number at most `T_n·(2H+1) = O(LH)`, the manuscript's own count,
  proved rather than assumed.
* `one_le_Lnorm`, `one_le_Hscale`.

## The scope mismatch, resolved, and a correction to how it was recorded

The mismatch is a **three**-way one, and the direction in which it has been
recorded so far (both in the task brief and in the module docstring of
`Kwon1002/OffDiagonal.lean`) is the wrong way round.

* Kwon's `J_n` of **(19)** is `{j : 200H ≤ j ≤ m_n − 200H}`, `m_n = ⌊L/λ⌋`.
  It is **deterministic**, and it is trimmed at *both* ends.  Display (41)
  sums over exactly that set.  (`Kwon1002.bulkJ` of `Kwon1002/Section4.lean`
  is this set; its docstring says so.)
* The Lean chain's `Kwon1002.bulkIndices c α n` is
  `{j : c·H ≤ j < τ_n(α)}`.  It is **random** (it depends on `α` through the
  stopping time) and it is trimmed only at the bottom.
* `Finset.range (n+1)`, over which `bulk_offdiagonal_input` sums, is a purely
  deterministic *device* introduced in `Kwon1002/SmallJumps.lean`
  (`truncatedBulkSum_eq_range`), legitimate because `bulkTerm` vanishes off
  `bulkIndices` and `bulkIndices ⊆ range (n+1)` a.e.

So the manuscript is the deterministic one and the Lean target is the random
one, not the other way about.  What is *proved* here settles the third leg
completely: `sum_offdiag_eq_lame_window` collapses `range (n+1)` onto a window
of `O(L)` levels with **no** residual tail, so the `range (n+1)` device costs
nothing and is not an extra assumption hidden in the residual.

The first leg, Kwon's deterministic `J_n` versus the Lean `bulkIndices`, is
**not** settled here, and is not settled anywhere in the tree.  It is a real
difference of statement, recorded as finding (F1) below; it is *not* a
weakening, because everything below is proved for the Lean (random) index set
as it stands.

## Findings

**(F1)  `truncatedBulkSum_centered_L2` is not display (41).**  Kwon's (41)
bounds `Var(Σ_{j ∈ J_n} U^{(ε)}_{n,j})` over the deterministic (19)-bulk,
trimmed by `200H` at *both* ends.  The Lean statement bounds the same object
over `bulkIndices c α n = {c·H ≤ j < τ_n(α)}`: random, and with no upper trim.
The two differ by the `|τ_n − m_n| = O_P(H)` levels at the top (Lemma 7.1
(60)).  Morally negligible, `O(H)` levels each contributing `O(1/L)`, but it
is an argument the manuscript does not make, because the manuscript never has
those levels in the sum.  Whoever finally links §5 to §7 must supply it.

**(F2)  The manuscript's proof of Lemma 5.2 never mentions the index set.**
Lines 606-630 of the manuscript treat `Σ_{j ∈ J_n}` as a sum over a fixed
finite index set throughout: the layer-cake bounds (42), the pair count, the
digit cut at `A_L` and the appeal to Proposition 4.1 are all stated for the
marks `U^{(ε)}_{n,j}` themselves.  That is sound for (19)'s deterministic
`J_n`, and it is exactly why (F1) matters: with the random `bulkIndices`,
every summand carries an extra factor `1{j < τ_n(α)}`, and Proposition 4.1
(27), a statement about `∫ ∏ F_ℓ(a_{j_ℓ+1}, θ_{j_ℓ})`, says nothing about
such a factor.  Removing it is a step neither the manuscript nor this
development performs.

**(F3)  The BV multi-block mixing of `Kwon1002/BVMixing.lean` does not reach
this residual.**  `BVMixing.lemma_3_2_BV` bounds
`|E(∏ᵢ gᵢ(T^{tᵢ}α) | I_w) − ∏ᵢ ∫ gᵢ|`: its observables are functions of the
**forward orbit point**.  The mark is `Z_{n,j} = a_{j+1}·W(θ_j)` with
`θ_j = {n·β_j}` and `β_j = x_0x_1⋯x_j` (`Kwon1002/Reciprocity.lean`), i.e. the
second argument is a function of the *whole past* `a_1,…,a_{j+1}` and of `n`.
So `bulkTerm c ε α n j` is not of the form `g(T^{t}α)` and `lemma_3_2_BV` does
not apply to it directly.  Kwon's two-argument window symbols `F(a_{j+1},θ_j)`
and the resonance analysis of Prop 4.2 exist precisely to handle that second
argument; the BV mixing lemma is the `v = 0` (zero-mode) branch of Prop 4.1's
proof only.  The premise that this pass could be closed from "the two-tuple
case of §4 factorization plus the digit-tail bound" therefore does not hold as
stated: the digit-tail half is indeed in place
(`OffDiag.bulkTermCentered_offdiag_bound`, proved, and used), but the §4 half
still needs the `vₛ ≠ 0` branch, i.e. `Prop41.prop_4_1_error_shape`.

## Sorried results consumed

**Exactly one**, and it is stated in this file: `farPair_covariance_decay`.
Nothing else here rests on a `sorry`.  In particular
`OffDiag.bulkTermCentered_offdiag_bound`, `OffDiag.near_pair_decay`,
`OffDiag.sum_offdiag_eq`, `L2Estimate.stoppingTime_le_log`,
`L2Estimate.bulk_window_input`, `L2Estimate.truncatedMark_second_moment`,
`L2Estimate.diagonal_le_second_moment`, `L2Estimate.bulkTerm_sq_integral_le`,
`L2Estimate.sum_split_diag`, `Kwon1002.integral_centered_eq`,
`Kwon1002.centered_second_moment_expand` and `Kwon1002.ae_irrational_restrict`
are all proved where they live.  `OffDiag.bulk_offdiagonal_far`, the sorried
original, is **not** used.

## Axiom audit

`#print axioms` was run on every result proved outright above; each depends on
exactly `[propext, Classical.choice, Quot.sound]`.  The three targets depend
additionally on `sorryAx`, from `farPair_covariance_decay` and from nothing
else.  The audit block has been removed.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace OffDiagFinal

open OffDiag

noncomputable section

/-! ## 1. The Lamé window

`τ_n ≤ 2L/log 2 + 2` deterministically off the rationals
(`L2Estimate.stoppingTime_le_log`), so `bulkTerm`, and hence
`bulkTermCentered`, and hence `offdiagTerm`, vanishes identically at every
level beyond that.  `lameIdx n` is the first such level. -/

/-- The first level at which the Lamé bound has certainly fired. -/
def lameIdx (n : ℕ) : ℕ := ⌈2 * Lnorm n / Real.log 2 + 2⌉₊

lemma log_two_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

lemma lame_le_lameIdx (n : ℕ) :
    2 * Lnorm n / Real.log 2 + 2 ≤ (lameIdx n : ℝ) := Nat.le_ceil _

lemma lameIdx_le (n : ℕ) (hL : 0 ≤ Lnorm n) :
    (lameIdx n : ℝ) ≤ 2 * Lnorm n / Real.log 2 + 3 := by
  have h0 : (0:ℝ) ≤ 2 * Lnorm n / Real.log 2 + 2 := by
    have : (0:ℝ) ≤ 2 * Lnorm n / Real.log 2 :=
      div_nonneg (by linarith) log_two_pos.le
    linarith
  have h := Nat.ceil_lt_add_one h0
  unfold lameIdx
  linarith

/-- Off the rationals the `j`-th bulk summand is identically zero beyond the
Lamé window. -/
lemma bulkTerm_eq_zero_of_lame (c ε α : ℝ) (hα : α ∈ Ioo (0:ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hn : 1 ≤ n) (hj : lameIdx n ≤ j) :
    bulkTerm c ε α n j = 0 := by
  unfold bulkTerm
  rw [if_neg]
  intro hmem
  have hlt : j < stoppingTime α n :=
    Finset.mem_range.mp (Finset.mem_of_mem_filter j hmem)
  have h1 := L2Estimate.stoppingTime_le_log α hα hirr n hn
  have h2 : (lameIdx n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h3 := lame_le_lameIdx n
  have h4 : ((j : ℕ) : ℝ) < ((stoppingTime α n : ℕ) : ℝ) := by exact_mod_cast hlt
  linarith

lemma integral_bulkTerm_eq_zero_of_lame (c ε : ℝ) (n j : ℕ) (hn : 1 ≤ n)
    (hj : lameIdx n ≤ j) :
    (∫ β in Ioo (0:ℝ) 1, bulkTerm c ε β n j) = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
    with α hα hirr
  exact bulkTerm_eq_zero_of_lame c ε α hα hirr n j hn hj

lemma bulkTermCentered_eq_zero_of_lame (c ε α : ℝ) (hα : α ∈ Ioo (0:ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hn : 1 ≤ n) (hj : lameIdx n ≤ j) :
    bulkTermCentered c ε α n j = 0 := by
  unfold bulkTermCentered
  rw [bulkTerm_eq_zero_of_lame c ε α hα hirr n j hn hj,
    integral_bulkTerm_eq_zero_of_lame c ε n j hn hj, sub_zero]

/-- **The off-diagonal window tail is empty.**  Every pair with an index
beyond the Lamé window contributes exactly `0` to (41). -/
lemma offdiagTerm_eq_zero_of_lame (c ε : ℝ) (n : ℕ) (p : ℕ × ℕ) (hn : 1 ≤ n)
    (hp : lameIdx n ≤ p.1 ∨ lameIdx n ≤ p.2) :
    offdiagTerm c ε n p = 0 := by
  unfold offdiagTerm
  split_ifs with h
  · rfl
  · refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
      with α hα hirr
    have hz : bulkTermCentered c ε α n p.1 * bulkTermCentered c ε α n p.2 = 0 := by
      rcases hp with h1 | h1
      · rw [bulkTermCentered_eq_zero_of_lame c ε α hα hirr n p.1 hn h1, zero_mul]
      · rw [bulkTermCentered_eq_zero_of_lame c ε α hα hirr n p.2 hn h1, mul_zero]
    exact hz

/-! ### The recorded scope mismatch, resolved

The manuscript's (41) sums over the **random** bulk index set `J_n`; the Lean
targets (`L2Estimate.bulk_offdiagonal_input`, and hence `bulk_offdiagonal_far`)
sum over the **deterministic** range `{0,…,n}` with `bulkTerm` extended by `0`
off the bulk.  The two agree, and the reconciliation is *not* an extra
hypothesis: `bulkTerm` is by definition supported on `bulkIndices c α n`, and
by the Lamé bound `bulkIndices c α n ⊆ {0,…,lameIdx n}` for every irrational
`α ∈ (0,1)`.  So the deterministic double sum collapses onto a window of
`O(L)` levels, exactly the manuscript's `#J_n = O(L)`, with **no** leftover
"off-diagonal window tail". -/

/-- The deterministic double sum of (41) is supported on the Lamé window. -/
lemma sum_offdiag_eq_lame_window (c ε : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), offdiagTerm c ε n p
      = ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 < lameIdx n ∧ p.2 < lameIdx n), offdiagTerm c ε n p := by
  classical
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro p hp hnot
  rw [Finset.mem_filter, not_and] at hnot
  have h := hnot hp
  simp only [not_and_or, not_lt] at h
  exact offdiagTerm_eq_zero_of_lame c ε n p hn h

/-- …and that window carries only `O(L²)` pairs. -/
lemma card_lame_window_le (n : ℕ) (hn : 3 ≤ n) :
    ((((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 < lameIdx n ∧ p.2 < lameIdx n)).card : ℕ) : ℝ)
      ≤ (2 / Real.log 2 + 3) ^ 2 * (Lnorm n) ^ 2 := by
  classical
  have hL1 : (1:ℝ) ≤ Lnorm n := by
    unfold Lnorm
    have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hexp : Real.exp 1 < (n:ℝ) := by
      have h := Real.exp_one_lt_d9
      linarith
    exact le_of_lt ((Real.lt_log_iff_exp_lt (by linarith : (0:ℝ) < (n:ℝ))).mpr hexp)
  have hsub : ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 < lameIdx n ∧ p.2 < lameIdx n))
      ⊆ Finset.range (lameIdx n) ×ˢ Finset.range (lameIdx n) := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr h.1, Finset.mem_range.mpr h.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range] at hcard
  have hcast : ((((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 < lameIdx n ∧ p.2 < lameIdx n)).card : ℕ) : ℝ)
      ≤ (lameIdx n : ℝ) * (lameIdx n : ℝ) := by
    have : ((((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 < lameIdx n ∧ p.2 < lameIdx n)).card : ℕ) : ℝ)
        ≤ ((lameIdx n * lameIdx n : ℕ) : ℝ) := by exact_mod_cast hcard
    simpa using this
  have hT : (lameIdx n : ℝ) ≤ (2 / Real.log 2 + 3) * Lnorm n := by
    have h := lameIdx_le n (by linarith)
    have h2 : 2 * Lnorm n / Real.log 2 = (2 / Real.log 2) * Lnorm n := by field_simp
    rw [h2] at h
    nlinarith [h, hL1]
  have hT0 : (0:ℝ) ≤ (lameIdx n : ℝ) := Nat.cast_nonneg _
  nlinarith [hcast, hT, hT0, hL1]

/-! ## 2. The near-diagonal pairs inside the window -/

/-- The `H`-near pairs of the Lamé window: the manuscript's overlapping and
`H`-near pairs of the sentences after (42). -/
def nearPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (lameIdx n) ×ˢ Finset.range (lameIdx n)).filter
    (fun p => |(p.1 : ℝ) - (p.2 : ℝ)| ≤ Hscale n)

lemma card_nearPairs_le (n : ℕ) (hH : 0 ≤ Hscale n) :
    ((nearPairs n).card : ℝ) ≤ (lameIdx n : ℝ) * (2 * Hscale n + 1) := by
  classical
  set m : ℕ := ⌊Hscale n⌋₊ with hm
  set T : ℕ := lameIdx n with hT
  have hsub : nearPairs n ⊆ (Finset.range T).biUnion
      (fun j => (Finset.Icc (j - m) (j + m)).image (fun k => (j, k))) := by
    intro p hp
    simp only [nearPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_range.mpr h1, ?_⟩
    refine Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩
    have habs := abs_le.mp h3
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rcases le_total p.1 p.2 with hle | hle
      · omega
      · have hd : ((p.1 - p.2 : ℕ) : ℝ) ≤ Hscale n := by
          rw [Nat.cast_sub hle]; linarith [habs.2]
        have : p.1 - p.2 ≤ m := Nat.le_floor hd
        omega
    · rcases le_total p.1 p.2 with hle | hle
      · have hd : ((p.2 - p.1 : ℕ) : ℝ) ≤ Hscale n := by
          rw [Nat.cast_sub hle]; linarith [habs.1]
        have : p.2 - p.1 ≤ m := Nat.le_floor hd
        omega
      · omega
  have hcard1 : (nearPairs n).card ≤ ∑ j ∈ Finset.range T,
      ((Finset.Icc (j - m) (j + m)).image (fun k => (j, k))).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  have hcard2 : ∀ j ∈ Finset.range T,
      ((Finset.Icc (j - m) (j + m)).image (fun k => (j, k))).card ≤ 2 * m + 1 := by
    intro j _
    refine le_trans (Finset.card_image_le) ?_
    rw [Nat.card_Icc]
    omega
  have hcard3 : (nearPairs n).card ≤ T * (2 * m + 1) := by
    refine le_trans hcard1 ?_
    calc ∑ j ∈ Finset.range T,
          ((Finset.Icc (j - m) (j + m)).image (fun k => (j, k))).card
        ≤ ∑ _j ∈ Finset.range T, (2 * m + 1) := Finset.sum_le_sum hcard2
      _ = T * (2 * m + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hcast : ((nearPairs n).card : ℝ) ≤ (T : ℝ) * (2 * (m : ℝ) + 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard3
    push_cast at this
    linarith
  have hmH : (m : ℝ) ≤ Hscale n := Nat.floor_le hH
  have hT0 : (0:ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
  nlinarith [hcast, hmH, hT0]

/-! ## 3. The residual input: far-pair covariance decay

This is Proposition 4.1 for pairs, *localized*.  Compared with
`OffDiag.bulk_offdiagonal_far` it is weaker in three independent ways:

* it speaks only about pairs **inside the Lamé window** `j, k < lameIdx n`
  (`offdiagTerm` is identically zero outside it, by
  `offdiagTerm_eq_zero_of_lame`);
* it speaks only about pairs at distance `> H`, the overlapping and `H`-near
  pairs are discarded here, unconditionally, and their count is *proved*
  (`card_nearPairs_le`);
* it asks for a **per-pair** bound `Cov ≤ δ/L²` rather than for a bound on a
  sum, which is the currency Proposition 4.1 actually produces.

It still carries a bad set `R` of size `O(LH)`, for the manuscript's
*resonance-near* pairs; those are the ones Prop 4.2 (`nonGood_tuple_count`)
counts.

What it does **not** shed, and what a discharge must therefore supply, is:

* the digit cut at `A_L = L^D` (`D > 2`) and the Jackson approximation of
  `z ↦ z·1{z ≤ εL}`, with the hard truncation of `Kwon1002.truncatedMark` in
  place of Kwon's smooth `zχ(z/(εL))` this is the extra `L¹` step already
  recorded in `Kwon1002/SmallJumps.lean`;
* `Kwon1002.Prop41.prop_4_1_error_shape`, in particular its `vₛ ≠ 0` branch,
  which is what `Kwon1002/BVMixing.lean` does *not* supply (finding (F3));
* the removal of the stopping-time factor `1{j < τ_n(α)}` carried by
  `bulkTerm`, which display (27) knows nothing about (finding (F2)). -/
theorem farPair_covariance_decay (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ R : Finset (ℕ × ℕ),
          ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
          ∀ j k : ℕ, j < lameIdx n → k < lameIdx n →
            Hscale n < |(j : ℝ) - (k : ℝ)| → (j, k) ∉ R →
            (∫ α in Ioo (0:ℝ) 1,
                bulkTermCentered c ε α n j * bulkTermCentered c ε α n k)
              ≤ δ / (Lnorm n) ^ 2 := by
  sorry

/-! ## 4. Target 1, `OffDiag.bulk_offdiagonal_far`

Reproduced token for token from `Kwon1002/OffDiagonal.lean` (lines 870-875),
and proved from `farPair_covariance_decay`. -/

lemma one_le_Lnorm (n : ℕ) (hn : 3 ≤ n) : (1:ℝ) ≤ Lnorm n := by
  unfold Lnorm
  have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hexp : Real.exp 1 < (n:ℝ) := by
    have h := Real.exp_one_lt_d9
    linarith
  exact le_of_lt ((Real.lt_log_iff_exp_lt (by linarith : (0:ℝ) < (n:ℝ))).mpr hexp)

lemma one_le_Hscale (n : ℕ) (hL : (1:ℝ) ≤ Lnorm n) : (1:ℝ) ≤ Hscale n := by
  unfold Hscale
  have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hL
    (by norm_num : (0:ℝ) ≤ (3/4:ℝ))
  simpa using h

theorem bulk_offdiagonal_far_scr (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            offdiagTerm c ε n p ≤ ε / 2 := by
  classical
  obtain ⟨κR, hκR, hres⟩ := farPair_covariance_decay c
  set κ₀ : ℝ := 2 / Real.log 2 + 3 with hκ₀def
  have hκ₀0 : 0 < κ₀ := by
    have : (0:ℝ) < 2 / Real.log 2 := div_pos (by norm_num) log_two_pos
    rw [hκ₀def]; linarith
  refine ⟨3 * κ₀ + κR, by linarith, ?_⟩
  intro ε hε hε1
  obtain ⟨N₁, hN₁⟩ := hres ε hε hε1 (ε / (2 * κ₀ ^ 2)) (by positivity)
  refine ⟨max N₁ 3, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 1 ≤ n := by omega
  have hL1 : (1:ℝ) ≤ Lnorm n := one_le_Lnorm n hn3
  have hH1 : (1:ℝ) ≤ Hscale n := one_le_Hscale n hL1
  obtain ⟨R, hRcard, hRfar⟩ := hN₁ n hn1
  set T : ℕ := lameIdx n with hTdef
  set δ : ℝ := ε / (2 * κ₀ ^ 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hT : (T : ℝ) ≤ κ₀ * Lnorm n := by
    have h := lameIdx_le n (by linarith)
    have h2 : 2 * Lnorm n / Real.log 2 = (2 / Real.log 2) * Lnorm n := by
      field_simp
    rw [hTdef, hκ₀def]
    rw [h2] at h
    nlinarith [h, hL1]
  refine ⟨nearPairs n ∪ R, ?_, ?_⟩
  · -- the count
    have hcu : ((nearPairs n ∪ R).card : ℝ) ≤ ((nearPairs n).card : ℝ) + (R.card : ℝ) := by
      have := Finset.card_union_le (nearPairs n) R
      exact_mod_cast this
    have hnear := card_nearPairs_le n (by linarith)
    have hstep : (T : ℝ) * (2 * Hscale n + 1) ≤ (3 * κ₀) * Lnorm n * Hscale n := by
      have h1 : 2 * Hscale n + 1 ≤ 3 * Hscale n := by linarith
      have h2 : (0:ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
      nlinarith [hT, h1, h2, hH1, hL1]
    linarith [hcu, hnear, hRcard, hstep]
  · -- the sum
    set P : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hP
    set B : Finset (ℕ × ℕ) := nearPairs n ∪ R with hB
    set cond : ℕ × ℕ → Prop := fun p => p.1 < T ∧ p.2 < T with hcond
    have hsplit : (∑ p ∈ (P \ B).filter cond, offdiagTerm c ε n p)
        + ∑ p ∈ (P \ B).filter (fun p => ¬ cond p), offdiagTerm c ε n p
        = ∑ p ∈ P \ B, offdiagTerm c ε n p :=
      Finset.sum_filter_add_sum_filter_not (P \ B) cond _
    have houter : (∑ p ∈ (P \ B).filter (fun p => ¬ cond p), offdiagTerm c ε n p) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have h := (Finset.mem_filter.mp hp).2
      rw [hcond] at h
      simp only [not_and_or, not_lt] at h
      exact offdiagTerm_eq_zero_of_lame c ε n p hnpos h
    have hinner : (∑ p ∈ (P \ B).filter cond, offdiagTerm c ε n p) ≤ ε / 2 := by
      have hbd : ∀ p ∈ (P \ B).filter cond,
          offdiagTerm c ε n p ≤ δ / (Lnorm n) ^ 2 := by
        intro p hp
        obtain ⟨hpPB, hpc⟩ := Finset.mem_filter.mp hp
        have hpB : p ∉ B := (Finset.mem_sdiff.mp hpPB).2
        rw [hB, Finset.mem_union, not_or] at hpB
        obtain ⟨hpnear, hpR⟩ := hpB
        rw [hcond] at hpc
        have hfar : Hscale n < |(p.1 : ℝ) - (p.2 : ℝ)| := by
          by_contra hcon
          push_neg at hcon
          exact hpnear (Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hpc.1,
              Finset.mem_range.mpr hpc.2⟩, hcon⟩)
        have hne : p.1 ≠ p.2 := by
          intro heq
          rw [heq] at hfar
          simp at hfar
          linarith
        unfold offdiagTerm
        rw [if_neg hne]
        have := hRfar p.1 p.2 hpc.1 hpc.2 hfar (by simpa using hpR)
        exact this
      have hsum := Finset.sum_le_card_nsmul ((P \ B).filter cond)
        (offdiagTerm c ε n) (δ / (Lnorm n) ^ 2) hbd
      rw [nsmul_eq_mul] at hsum
      refine le_trans hsum ?_
      have hsub : ((P \ B).filter cond) ⊆ Finset.range T ×ˢ Finset.range T := by
        intro p hp
        have hpc := (Finset.mem_filter.mp hp).2
        rw [hcond] at hpc
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hpc.1, Finset.mem_range.mpr hpc.2⟩
      have hcard : ((((P \ B).filter cond).card : ℕ) : ℝ) ≤ (T : ℝ) * (T : ℝ) := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_product, Finset.card_range] at h1
        have : ((((P \ B).filter cond).card : ℕ) : ℝ) ≤ ((T * T : ℕ) : ℝ) := by
          exact_mod_cast h1
        simpa using this
      have hLpos : (0:ℝ) < (Lnorm n) ^ 2 := by nlinarith
      have hq0 : (0:ℝ) ≤ δ / (Lnorm n) ^ 2 := by positivity
      have hT0 : (0:ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
      have hstep : ((((P \ B).filter cond).card : ℕ) : ℝ) * (δ / (Lnorm n) ^ 2)
          ≤ ((T : ℝ) * (T : ℝ)) * (δ / (Lnorm n) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard hq0
      refine le_trans hstep ?_
      have hTT : (T : ℝ) * (T : ℝ) ≤ (κ₀ * Lnorm n) * (κ₀ * Lnorm n) := by
        nlinarith [hT, hT0, hκ₀0, hL1]
      have hfin : ((κ₀ * Lnorm n) * (κ₀ * Lnorm n)) * (δ / (Lnorm n) ^ 2) = ε / 2 := by
        rw [hδdef]
        field_simp
      calc ((T : ℝ) * (T : ℝ)) * (δ / (Lnorm n) ^ 2)
          ≤ ((κ₀ * Lnorm n) * (κ₀ * Lnorm n)) * (δ / (Lnorm n) ^ 2) :=
            mul_le_mul_of_nonneg_right hTT hq0
        _ = ε / 2 := hfin
    linarith [hsplit, houter, hinner]


/-! ## 5. Target 2, `L2Estimate.bulk_offdiagonal_input`

Reproduced token for token from `Kwon1002/L2Estimate.lean` (lines 571-576).
The proof body is `OffDiag.bulk_offdiagonal_input'` verbatim, with the sorried
`OffDiag.bulk_offdiagonal_far` replaced by the proved
`bulk_offdiagonal_far_scr`. -/

theorem bulk_offdiagonal_input_scr (c : ℝ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if j = k then 0 else
            ∫ α in Ioo (0:ℝ) 1,
              bulkTermCentered c ε α n j * bulkTermCentered c ε α n k) ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hpair⟩ := bulkTermCentered_offdiag_bound c
  obtain ⟨κ, hκ, hfar⟩ := bulk_offdiagonal_far_scr c
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

/-! ## 6. Target 3, `Kwon1002.truncatedBulkSum_centered_L2`

Reproduced token for token from `Kwon1002/SmallJumps.lean` (lines 504-509).
The proof body is `OffDiag.truncatedBulkSum_centered_L2'` verbatim, with
`bulk_offdiagonal_input'` replaced by `bulk_offdiagonal_input_scr`. -/

theorem truncatedBulkSum_centered_L2_scr (c : ℝ) :
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
  obtain ⟨N₂, hN₂⟩ := bulk_offdiagonal_input_scr c ε hε hε1
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
end

end OffDiagFinal

end Kwon1002
