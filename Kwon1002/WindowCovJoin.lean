import Kwon1002.CorFinal
import Kwon1002.WindowCovariance

/-!
# The join: the covariance-currency bridge, read at the canonical residual

`Kwon1002/WindowCovariance.lean` proves the bridge and the reduction below
`Kwon1002.CorFinal`, so it cannot mention `CorFinal.offdiagAbsTerm`.  This
module, which imports both sides, reads the reduction in exactly the currency
`Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` is stated in, and guards the
match inside Lean: the `example` at the foot of the file closes the *canonical*
statement text by the canonical (sorried) declaration, so the two are the same
statement and not a look-alike.

**What this establishes.**  §5's last open input,
`CorFinal.bulk_offdiagonal_abs_far_sharp`, is implied — axiom-cleanly — by a
far-pair covariance decay in which **no random index set and no stopping time
appear**: the hypothesis quantifies over `j, k ∈ bulkJ n`, the deterministic
bulk of display (19), and speaks only about `Kwon1002.truncatedMark` at those
two levels (through `WindowCov.detTermCentered`, which is `truncatedMark/L`
centred, restricted to `bulkJ n`).

Everything §5-specific is discharged in `WindowCovariance`:

* the random bulk `bulkIndices c α n` versus the deterministic `bulkJ n`
  (`WindowCov.window_covariance_bridge`, out of `StopWin.mem_bulkIndices_iff`
  and `StopWin.stopBad_measure_le`);
* the Lamé cap, which kills every pair outside an `O(L²)` window
  (`WindowCov.offdiagAbs_eq_zero_of_Tcap`);
* the three `O(L·H)` bad-set families and their arithmetic
  (`WindowCov.card_excPairs_le`, `WindowCov.card_sharpen`).

So what remains of the residual is a §4 statement about a pair of `ε`-truncated
marks at two far-separated levels of `J_n`.
-/

open Filter MeasureTheory Set

namespace Kwon1002

namespace WindowCovJoin

noncomputable section

/-- **The residual, in the deterministic bulk.**  The statement
`WindowCov.abs_far_sharp_of_det_pair_decay` consumes, spelled out here so that
it can be quoted without unfolding: outside a bad set of `O(L·H)` pairs, the
covariance of the `ε`-truncated marks at two levels of `J_n` more than `H`
apart is `≤ δ/L²`, for every `δ > 0` and all large `n`. -/
def DetPairDecay (c : ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ R : Finset (ℕ × ℕ),
        ((R.card : ℝ) ≤ κ * Lnorm n * Hscale n) ∧
        ∀ j k : ℕ, j ∈ bulkJ n → k ∈ bulkJ n →
          Hscale n < |(j : ℝ) - (k : ℝ)| → (j, k) ∉ R →
          |∫ α in Ioo (0 : ℝ) 1,
              WindowCov.detTermCentered ε α n j * WindowCov.detTermCentered ε α n k|
            ≤ δ / (Lnorm n) ^ 2

/-- `c` does not occur in `DetPairDecay`; it is carried only so that the
implication below reads at the same `c` as the residual. -/
lemma detPairDecay_const {c c' : ℝ} (h : DetPairDecay c) : DetPairDecay c' := h

/-- **The residual is implied by a purely deterministic §4 statement.**  The
conclusion is `Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp` token for
token; the `example` below checks that inside Lean. -/
theorem bulk_offdiagonal_abs_far_sharp_of_detPairDecay (c : ℝ) (h : DetPairDecay c) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            CorFinal.offdiagAbsTerm c ε n p ≤ ε / 2 :=
  WindowCov.abs_far_sharp_of_det_pair_decay c h

/-- **Machine check.**  The conclusion just proved is the statement of the
canonical residual `Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp`: the
statement text below is closed by the canonical declaration itself. -/
example (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ B : Finset (ℕ × ℕ),
        ((B.card : ℝ) ≤ κ * (Lnorm n) ^ 2 / (1 + Real.log (2 + Lnorm n)) ^ 3) ∧
        ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) \ B,
            CorFinal.offdiagAbsTerm c ε n p ≤ ε / 2 :=
  CorFinal.bulk_offdiagonal_abs_far_sharp c

end

end WindowCovJoin

end Kwon1002
