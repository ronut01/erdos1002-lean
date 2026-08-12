import Kwon1002.CharacterReduction

/-!
# Reconciliation of identity (31) with manuscript version 5

Version 5 states the block character reduction
(`eq:block-character-reduction`) over the index range `t = -R-1, …, R`:
for `R ≥ 0` and integers `c_{-R-1}, …, c_R`, with the word
`w_{j,R} = (a_{j-R+1}, …, a_{j+R})`, there are integers `A_w`, `B_w`
depending only on that word with

`∑_{t=-R-1}^{R} c_t θ_{j+t} ≡ A_w θ_j + B_w θ_{j-1} (mod 1)`,

and the resulting phase is `n (-1)^j (A_w q_j - B_w q_{j-1}) α`.

The formalisation in `Kwon1002.Section4` (and its proved twin
`Kwon1002.S4chars.window_character_reduction`) sums over
`i : Fin (2R+1)` at times `j + i - R`, that is over `t = -R, …, R`.
That is the narrower range of the earlier draft: it omits the term
`t = -R-1`.  Version 5 is therefore strictly stronger, by exactly one
extra term at the bottom of the window.

The word itself needs no change.  With the manuscript indexing
`a_k = digit α (k-1)`, forced by `θ_{j+1} = {θ_{j-1} - a_{j+1} θ_j}`
versus the Lean recursion `θ_{k+1} ≡ θ_{k-1} - digit α k · θ_k`, the
manuscript word `(a_{j-R+1}, …, a_{j+R})` is
`(digit α (j-R), …, digit α (j+R-1))`, which is `windowWord R α j`
verbatim.  The backward substitutions down to `θ_{j-R-1}` consume
`a_j, …, a_{j-R+1}`, the last of which is `digit α (j-R) = w 0`, still
inside the window.  So the same `2R` letters carry the one extra term,
and the only work is to run the downward recursion one step further,
from depth `R` to depth `R+1`.  This also forces the standing hypothesis
`R ≤ j` to become `R + 1 ≤ j`, since `θ_{j-R-1}` must exist.

Everything below reuses the existing machinery of
`Kwon1002.CharacterReduction`: the coefficient recursions `upC`, `downC`,
the upward half `up_theta` unchanged, and the downward half re-run with
the depth bound relaxed by one.

The phase formula is checked against `torusChar_monomial_frequency'`:
the reduced character is `B_w θ_{j-1} + A_w θ_j`, whose frequency is
`Qfreq α j B_w A_w = A_w q_j - B_w q_{j-1}`, so the phase is
`(-1)^j (A_w q_j - B_w q_{j-1}) n α`, exactly the version 5 formula.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

namespace V5Identity31

noncomputable section

/-! ## The downward recursion, run one step deeper

`Kwon1002.down_theta` expands `θ_{j-d}` for `d ≤ R`.  Version 5 needs
`d ≤ R + 1`.  The recursion `downC` already has the right shape: the step
producing depth `d+2` reads the letter `v (R - d - 1)`, so depth `R+1`
reads `v 0`, the first letter of the window.  Only the depth bound and
the range hypothesis on `j` change.
-/

/-- Downward half of (31), version 5 range: `θ_{j-d}` for `d ≤ R + 1`. -/
lemma down_theta_ext {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j R : ℕ) (hRj : R + 1 ≤ j) (v : ℕ → ℕ)
    (hv : ∀ t, t < 2 * R → v t = digit α (j + t - R)) :
    ∀ d, d ≤ R + 1 → ∃ m : ℤ, theta α n (j - d)
      = ((downC R v d).1 : ℝ) * theta α n j
        + ((downC R v d).2 : ℝ) * thetaPred α n j + (m : ℝ) := by
  have key : ∀ d : ℕ,
      (d ≤ R + 1 → ∃ m : ℤ, theta α n (j - d)
        = ((downC R v d).1 : ℝ) * theta α n j
          + ((downC R v d).2 : ℝ) * thetaPred α n j + (m : ℝ))
      ∧ (d + 1 ≤ R + 1 → ∃ m : ℤ, theta α n (j - (d + 1))
        = ((downC R v (d + 1)).1 : ℝ) * theta α n j
          + ((downC R v (d + 1)).2 : ℝ) * thetaPred α n j + (m : ℝ)) := by
    intro d
    induction d with
    | zero =>
      constructor
      · intro _
        refine ⟨0, ?_⟩
        have hc : downC R v 0 = ((1 : ℤ), (0 : ℤ)) := rfl
        rw [show j - 0 = j from rfl, hc]
        push_cast
        ring
      · intro _
        refine ⟨0, ?_⟩
        have hc : downC R v (0 + 1) = ((0 : ℤ), (1 : ℤ)) := rfl
        rw [hc, thetaPred_eq_theta_sub α n j (by omega), show j - (0 + 1) = j - 1 from rfl]
        push_cast
        ring
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      intro hR
      obtain ⟨m1, hm1⟩ := ih.1 (by omega)
      obtain ⟨m2, hm2⟩ := ih.2 (by omega)
      obtain ⟨k, hk⟩ : ∃ k, j - d - 2 = k := ⟨_, rfl⟩
      have ek0 : j - (d + 1 + 1) = k := by omega
      have ek1 : j - (d + 1) = k + 1 := by omega
      have ek2 : j - d = k + 2 := by omega
      obtain ⟨m0, hm0⟩ := theta_succ_mod hα hirr n (k + 1)
      have hvidx : v (R - d - 1) = digit α (k + 1) := by
        rw [hv (R - d - 1) (by omega)]
        congr 1
        omega
      have hpred : thetaPred α n (k + 1) = theta α n k := rfl
      have hm0' : theta α n (k + 2)
          = theta α n k - (v (R - d - 1) : ℝ) * theta α n (k + 1) + (m0 : ℝ) := by
        rw [hvidx, show k + 2 = k + 1 + 1 from rfl, hm0, hpred]
      rw [ek2] at hm1
      rw [ek1] at hm2
      have hc : downC R v (d + 1 + 1)
          = ((downC R v d).1 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).1,
             (downC R v d).2 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).2) := rfl
      refine ⟨m1 + (v (R - d - 1) : ℤ) * m2 - m0, ?_⟩
      have hstep : theta α n k
          = theta α n (k + 2) + (v (R - d - 1) : ℝ) * theta α n (k + 1) - (m0 : ℝ) := by
        rw [hm0']; ring
      rw [ek0, hstep, hm1, hm2, hc]
      push_cast
      ring
  exact fun d hd => (key d).1 hd

/-! ## The version 5 coefficient bookkeeping

Window positions are now `i ∈ {0, …, 2R+1}`, attached to the times
`j + i - (R+1)`, so that `i = 0` is `t = -R-1` and `i = 2R+1` is `t = R`.
The central pair sits at `i = R+1` (giving `θ_j`) and `i = R` (giving
`θ_{j-1}`).
-/

/-- The coefficient pair attached to the version 5 window position
`i ∈ {0, …, 2R+1}`, that is to the time `j + i - (R+1)`. -/
def winC1 (R : ℕ) (v : ℕ → ℕ) (i : ℕ) : ℤ × ℤ :=
  if R + 1 ≤ i then upC R v (i - (R + 1)) else downC R v (R + 1 - i)

/-- `A_w` of (31), version 5 range. -/
def winA1 (R : ℕ) (c : Fin (2 * R + 2) → ℤ) (w : Fin (2 * R) → ℕ) : ℤ :=
  ∑ i : Fin (2 * R + 2), c i * (winC1 R (wordFn R w) (i : ℕ)).1

/-- `B_w` of (31), version 5 range. -/
def winB1 (R : ℕ) (c : Fin (2 * R + 2) → ℤ) (w : Fin (2 * R) → ℕ) : ℤ :=
  ∑ i : Fin (2 * R + 2), c i * (winC1 R (wordFn R w) (i : ℕ)).2

/-! ## (31) at the version 5 range -/

/-- **(31), manuscript version 5** (`eq:block-character-reduction`, lines
603-623).  For `R ≥ 0` and integers `c_{-R-1}, …, c_R`, indexed here by
`i : Fin (2R+2)` through `t = i - (R+1)`, there are integers `A_w`, `B_w`
depending only on the word `w = w_{j,R} = (a_{j-R+1}, …, a_{j+R})` such
that

`∑_{t=-R-1}^{R} c_t θ_{j+t} ≡ A_w θ_j + B_w θ_{j-1} (mod 1)`.

**Reading.**  "Depending only on `w`" is rendered by quantifying `A`, `B`
as functions of the word before `α`, `n`, `j` are introduced; the
`(mod 1)` is the existential integer `m`; `θ_{j-1}` is `thetaPred α n j`.
The hypothesis `R + 1 ≤ j` is what makes `θ_{j-R-1}` a coordinate of the
orbit at all, and it is the version 5 range that forces it: the earlier
draft, summing only over `t = -R, …, R`, needed just `R ≤ j`. -/
theorem window_character_reduction_v5 (R : ℕ) (c : Fin (2 * R + 2) → ℤ) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R + 1 ≤ j →
        ∃ m : ℤ,
          (∑ i : Fin (2 * R + 2), (c i : ℝ) * theta α n (j + (i : ℕ) - (R + 1)))
            = (A (windowWord R α j) : ℝ) * theta α n j
              + (B (windowWord R α j) : ℝ) * thetaPred α n j + (m : ℝ) := by
  refine ⟨winA1 R c, winB1 R c, ?_⟩
  intro α hirr hα n j hRj
  have hv : ∀ t, t < 2 * R → wordFn R (windowWord R α j) t = digit α (j + t - R) :=
    fun t ht => wordFn_windowWord R α j t ht
  have key : ∀ i : Fin (2 * R + 2), ∃ m : ℤ, theta α n (j + (i : ℕ) - (R + 1))
      = ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).1 : ℝ) * theta α n j
        + ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).2 : ℝ) * thetaPred α n j
        + (m : ℝ) := by
    intro i
    have hi := i.isLt
    by_cases h : R + 1 ≤ (i : ℕ)
    · obtain ⟨m, hm⟩ := up_theta hα hirr n j R (wordFn R (windowWord R α j)) hv
        ((i : ℕ) - (R + 1)) (by omega)
      refine ⟨m, ?_⟩
      rw [show j + (i : ℕ) - (R + 1) = j + ((i : ℕ) - (R + 1)) from by omega, hm,
        winC1, if_pos h]
    · obtain ⟨m, hm⟩ := down_theta_ext hα hirr n j R hRj (wordFn R (windowWord R α j)) hv
        (R + 1 - (i : ℕ)) (by omega)
      refine ⟨m, ?_⟩
      rw [show j + (i : ℕ) - (R + 1) = j - (R + 1 - (i : ℕ)) from by omega, hm,
        winC1, if_neg h]
  choose m hm using key
  refine ⟨∑ i : Fin (2 * R + 2), c i * m i, ?_⟩
  calc (∑ i : Fin (2 * R + 2), (c i : ℝ) * theta α n (j + (i : ℕ) - (R + 1)))
      = ∑ i : Fin (2 * R + 2),
          ((c i : ℝ) * ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).1 : ℝ) * theta α n j
            + (c i : ℝ) * ((winC1 R (wordFn R (windowWord R α j)) (i : ℕ)).2 : ℝ)
                * thetaPred α n j
            + (c i : ℝ) * (m i : ℝ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hm i]; ring
    _ = (winA1 R c (windowWord R α j) : ℝ) * theta α n j
          + (winB1 R c (windowWord R α j) : ℝ) * thetaPred α n j
          + ((∑ i : Fin (2 * R + 2), c i * m i : ℤ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        simp only [winA1, winB1]
        push_cast
        ring

/-! ## The draft range is the case `c_{-R-1} = 0` -/

/-- The earlier draft range `t = -R, …, R` is recovered from the version 5
range by setting the bottom coefficient to zero.  This is the machine check
that the reindexing `t = i - (R+1)` used above describes the same window as
the draft's `t = i - R`, shifted down by one and extended at the bottom, so
that the change really is an extension and not a relabelling. -/
theorem draft_range_of_v5 (R : ℕ) (c : Fin (2 * R + 1) → ℤ) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R + 1 ≤ j →
        ∃ m : ℤ,
          (∑ i : Fin (2 * R + 1), (c i : ℝ) * theta α n (j + (i : ℕ) - R))
            = (A (windowWord R α j) : ℝ) * theta α n j
              + (B (windowWord R α j) : ℝ) * thetaPred α n j + (m : ℝ) := by
  obtain ⟨A, B, hAB⟩ := window_character_reduction_v5 R (Fin.cases (0 : ℤ) c)
  refine ⟨A, B, ?_⟩
  intro α hirr hα n j hRj
  obtain ⟨m, hm⟩ := hAB α hirr hα n j hRj
  refine ⟨m, ?_⟩
  rw [← hm]
  conv_rhs => rw [Fin.sum_univ_succ]
  rw [Fin.cases_zero]
  push_cast
  rw [zero_mul, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.cases_succ, Fin.val_succ,
    show j + ((i : ℕ) + 1) - (R + 1) = j + (i : ℕ) - R from by omega]

/-! ## The version 5 phase formula

Version 5 line 623: "the resulting phase is `n(-1)^j(A_w q_j - B_w q_{j-1}) α`".
Against `Qfreq α j r s = s q_j - r q_{j-1}` and
`torusChar_monomial_frequency'`, the reduced character
`A_w θ_j + B_w θ_{j-1}` is the monomial with `(r, s) = (B_w, A_w)`, whose
frequency is `Qfreq α j B_w A_w = A_w q_j - B_w q_{j-1}`.  So the two
agree, and the same pairing `(r,s) = (B, A)` is what the manuscript uses
downstream at line 1383.
-/

/-- `Qfreq` at the reduced modes is exactly the version 5 integer
`A_w q_j - B_w q_{j-1}`. -/
lemma qfreq_reduced (α : ℝ) (j : ℕ) (A B : ℤ) :
    Qfreq α j B A = A * (denom α j : ℤ) - B * (denom α (j - 1) : ℤ) := rfl

/-- **(31) together with the version 5 phase formula.**  The window
character of the full range `t = -R-1, …, R` is the pure phase
`e(n (-1)^j (A_w q_j - B_w q_{j-1}) α)`. -/
theorem window_character_phase_v5 (R : ℕ) (c : Fin (2 * R + 2) → ℤ) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R + 1 ≤ j →
        (torusChar (∑ i : Fin (2 * R + 2), (c i : ℝ) * theta α n (j + (i : ℕ) - (R + 1)))
          = torusChar ((n : ℝ) * (-1 : ℝ) ^ j
              * ((A (windowWord R α j) * (denom α j : ℤ)
                   - B (windowWord R α j) * (denom α (j - 1) : ℤ) : ℤ) : ℝ) * α)) := by
  obtain ⟨A, B, hAB⟩ := window_character_reduction_v5 R c
  refine ⟨A, B, ?_⟩
  intro α hirr hα n j hRj
  obtain ⟨m, hm⟩ := hAB α hirr hα n j hRj
  set w := windowWord R α j with hw
  have h1 : (∑ i : Fin (2 * R + 2), (c i : ℝ) * theta α n (j + (i : ℕ) - (R + 1)))
      = ((B w : ℤ) : ℝ) * thetaPred α n j + ((A w : ℤ) : ℝ) * theta α n j + (m : ℝ) := by
    rw [hm]; ring
  rw [h1, torusChar_add_int,
    torusChar_monomial_frequency' hα hirr n j (by omega) (B w) (A w),
    qfreq_reduced α j (A w) (B w)]
  congr 1
  ring

end

end V5Identity31

end Kwon1002
