import Kwon1002.NonzeroMode

/-!
# Proposition 4.1, unconditional

`Kwon1002/NonzeroMode.lean` closes the `v_s ≠ 0` branch of §4 outright
(`NonzeroMode.nonzero_mode_three_step_unconditional`, the manuscript's own
three-step chain).  This file spends it:

* `nonzero_mode_small_unconditional` — the `v_s ≠ 0` branch in the shape §4
  consumes, i.e. the statement of the sorried
  `Kwon1002.ErrorShape.nonzero_mode_small`;
* `prop_4_1_error_shape_unconditional` — display (30), the statement of the
  sorried `Kwon1002.Prop41.prop_4_1_error_shape`;
* `prop_4_1_marked_factorization_unconditional` — **display (27),
  Proposition 4.1**.  The canonical name `Kwon1002.prop_4_1_marked_factorization`
  is declared here too, and proved: `Kwon1002/Section4.lean` sits below every
  module able to discharge the `v_s ≠ 0` branch, so a declaration there could
  never shed its `sorry`.

Each of the three carries an `example` guard immediately after it asserting
that its type is *literally* the type of the canonical declaration it
reproduces (`@ours = @canonical := rfl`, which typechecks only when the two
statements are the same up to definitional unfolding, proof irrelevance
supplying the value).  So the reproductions are machine-checked, not
eyeballed.

Nothing here is sorried, and the two inputs it consumes —
`Prop41Final.prop_4_1_error_shape_of_nonzero` (the axiom-clean assembly of
the three §4-body steps) and `Prop41.eventually_rpow_mul_deltaScale_le` (the
`O_A(L^{-A})` reduction) — are sorry-free.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology

namespace Kwon1002

namespace NonzeroMode

open Prop41 ErrorShape

noncomputable section

/-- **The `v_s ≠ 0` branch of §4, unconditional.**  Statement reproduced
token-identically from `Kwon1002.ErrorShape.nonzero_mode_small` (sorried in
place); derived from the three-step chain by the triangle inequality,
exactly as `ZeroMode.nonzero_mode_small` derives it from the sorried
`ZeroMode.nonzero_mode_three_step`. -/
theorem nonzero_mode_small_unconditional (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C c₀ ρ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
      ∀ v ∈ modeTuples r D (Lnorm n), v ≠ 0 →
        ‖modeTerm n r j c v‖
          ≤ C * (Lnorm n) ^ (D * r) *
              (Real.exp (-c₀ * Real.sqrt (Lnorm n)) + Real.exp (-c₀ * Hscale n)
                + ρ ^ (c₀ * Hscale n)) := by
  obtain ⟨C, c₀, ρ, hC, hc₀, hρ0, hρ1, hbd⟩ :=
    nonzero_mode_three_step_unconditional r D hD
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨3 * C, c₀, ρ, by linarith, hc₀, hρ0, hρ1, ?_⟩
  filter_upwards [hbd, hLtend.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hL1 j hj F c hc v hv hv0
  obtain ⟨T₁, T₂, h1, h2, h3⟩ := hn j hj F c hc v hv hv0
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hX : (0 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) := Real.rpow_nonneg hL0.le _
  have e1 : (0 : ℝ) < Real.exp (-c₀ * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have e2 : (0 : ℝ) < Real.exp (-c₀ * Hscale n) := Real.exp_pos _
  have e3 : (0 : ℝ) < ρ ^ (c₀ * Hscale n) := Real.rpow_pos_of_pos hρ0 _
  have htri : ‖modeTerm n r j c v‖
      ≤ ‖modeTerm n r j c v - T₁‖ + ‖T₁ - T₂‖ + ‖T₂‖ := by
    calc ‖modeTerm n r j c v‖
        = ‖(modeTerm n r j c v - T₁) + ((T₁ - T₂) + T₂)‖ := by ring_nf
      _ ≤ ‖modeTerm n r j c v - T₁‖ + ‖(T₁ - T₂) + T₂‖ := norm_add_le _ _
      _ ≤ ‖modeTerm n r j c v - T₁‖ + (‖T₁ - T₂‖ + ‖T₂‖) :=
          add_le_add le_rfl (norm_add_le _ _)
      _ = ‖modeTerm n r j c v - T₁‖ + ‖T₁ - T₂‖ + ‖T₂‖ := by ring
  refine le_trans htri ?_
  have hsum := add_le_add (add_le_add h1 h2) h3
  refine le_trans hsum ?_
  nlinarith [hX, e1.le, e2.le, e3.le, hC.le,
    mul_nonneg hX e1.le, mul_nonneg hX e2.le, mul_nonneg hX e3.le]

/-- Machine check: the statement above **is** the canonical one. -/
example : @nonzero_mode_small_unconditional
    = @Kwon1002.ErrorShape.nonzero_mode_small := rfl

/-- **Display (30), unconditional.**  The axiom-clean assembly
`Prop41Final.prop_4_1_error_shape_of_nonzero` fed with the now-proved
`v_s ≠ 0` branch.  Statement token-identical to
`Kwon1002.Prop41.prop_4_1_error_shape` (sorried in place). -/
theorem prop_4_1_error_shape_unconditional (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ B C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ B * deltaScale c ρ n :=
  Prop41Final.prop_4_1_error_shape_of_nonzero r D hD
    (nonzero_mode_small_unconditional r D hD)

end

end NonzeroMode


/-! ## Display (30) and Proposition 4.1 in `namespace Prop41`

`Kwon1002/Prop41.lean` states display (30) and derives Proposition 4.1 from
it, but sits below the module that discharges the `v_s ≠ 0` branch.  The two
declarations therefore live here, in the same namespace and with the same
statements. -/

namespace Prop41

noncomputable section

/-- **Display (30)**, the body of the manuscript's proof of Proposition 4.1.

Declared here rather than in `Kwon1002/Prop41.lean` (where `deltaScale` and
the rest of its apparatus live) because the `v_s ≠ 0` branch it rests on is
discharged in `Kwon1002/NonzeroMode.lean`, above that module.

Reading: there are a polynomial weight `L^B` (the `L^{O_{r,D}(1)}` of (30),
coming from the `ℓ¹` mass `L^{Dr}` of the extracted Fourier-digit
coefficients times the number of Fourier terms) and mixing/deviation
constants `c > 0`, `ρ ∈ (0,1)` such that, uniformly over good tuples and
over symbol families in `P_D(L)`, the factorization error of (27) is at
most `C L^B δ_n`.

What this packages (manuscript lines ≈ 340-404):
* the digit/Fourier expansion and the `ℓ¹` bound `L^{Dr}` on the extracted
  coefficients;
* the `v = 0` branch: `lem_3_2_conditional_multiblock_mixing` applied across
  the gaps `goodTuple_sep` supplies, error `L^{O(1)} ρ^{200H}`;
* the `v_s ≠ 0` branch: the deterministic frequency bound (28), the three
  local complete-cylinder cuts at depths `j_s`, `k_-`, `k_+` with discarded
  mass `O(e^{-cL^{1/2}})` by (20), the consequence (29), the replacement of
  the post-resonance digit factors by their stationary means (which uses
  `good_avoids_resonance_window` to place them `100H` clear of the window),
  and Lemma 3.4 (`Kwon1002.descendant_phase_small`) on each depth-`(j_s+1)`
  prefix. -/
theorem prop_4_1_error_shape (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ B C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ B * deltaScale c ρ n :=
  NonzeroMode.prop_4_1_error_shape_unconditional r D hD

/-- Machine check: the statement just proved **is** display (30) verbatim as
`Kwon1002/Prop41.lean` used to state it. -/
example : @NonzeroMode.prop_4_1_error_shape_unconditional
    = @prop_4_1_error_shape := rfl

/-! ## Proposition 4.1 -/

/-- **Proposition 4.1** (Marked factorization), display (27).

The `namespace Prop41` reading, proved from `prop_4_1_error_shape` and the
fully proved `O_A(L^{-A})` reduction `eventually_rpow_mul_deltaScale_le`. -/
theorem prop_4_1_marked_factorization (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨B, C, c, ρ, hC, hc, hρ0, hρ1, hbd⟩ := prop_4_1_error_shape r D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbd, eventually_rpow_mul_deltaScale_le A B c ρ hc hρ0 hρ1]
    with n hn harith j hj F hF
  calc ‖(∫ α in Ioo (0 : ℝ) 1,
            ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C * (Lnorm n) ^ B * deltaScale c ρ n := hn j hj F hF
    _ = C * ((Lnorm n) ^ B * deltaScale c ρ n) := by ring
    _ ≤ C * (Lnorm n) ^ (-A) := mul_le_mul_of_nonneg_left harith hC.le


end

end Prop41

/-! ## Proposition 4.1 in `Kwon1002`'s own namespace

Stated in `namespace Kwon1002`, so `GoodTuple`, `IsInPD`, `Lnorm`, `digit`,
`theta` and `stationaryMean` resolve exactly as they do in
`Kwon1002/Section4.lean`, where the rest of §4's statements are declared. -/

noncomputable section

/-- **Proposition 4.1 (Marked factorization), display (27), unconditional.**

Statement token-identical to the canonical
`Kwon1002.prop_4_1_marked_factorization`, which is declared just below (this
module, not `Kwon1002/Section4.lean`, is the lowest one that can prove it).
All three steps of the §4 body are now proved: step 1
(`Prop4Final.integral_eq_sum_modeTerm'`), step 2
(`Prop41Final.zero_mode_factorization_f`) and step 3
(`NonzeroMode.nonzero_mode_small_unconditional`, this pass). -/
theorem prop_4_1_marked_factorization_unconditional (r : ℕ) (D A : ℝ)
    (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨B, C, c, ρ, hC, hc, hρ0, hρ1, hbd⟩ :=
    NonzeroMode.prop_4_1_error_shape_unconditional r D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbd, Prop41.eventually_rpow_mul_deltaScale_le A B c ρ hc hρ0 hρ1]
    with n hn harith j hj F hF
  calc ‖(∫ α in Ioo (0 : ℝ) 1,
            ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C * (Lnorm n) ^ B * Prop41.deltaScale c ρ n := hn j hj F hF
    _ = C * ((Lnorm n) ^ B * Prop41.deltaScale c ρ n) := by ring
    _ ≤ C * (Lnorm n) ^ (-A) := mul_le_mul_of_nonneg_left harith hC.le

/-- **Proposition 4.1** (Marked factorization), display (27).

For fixed `r, D, A`: uniformly over good tuples `(j_1,…,j_r)` in `J_n`
and over `F_1,…,F_r ∈ P_D(L)`,

`∫₀¹ ∏_ℓ F_ℓ(a_{j_ℓ+1}, θ_{j_ℓ}) dα
   = ∏_ℓ ∫₀¹∫₀¹ F_ℓ(a₁(x), θ) dθ dν(x) + O_{r,D,A}(L^{-A})`.

**Reading (uniformity).**  `O_{r,D,A}` means: one constant `C`,
depending on `r, D, A` only, valid for all large `n`, all good tuples and
all admissible symbol families.  That is the reading the downstream use
in §§5-6 needs, and it is the strongest one; the constant is therefore
quantified outside `n`, `j` and `F`.

This is the canonical name.  It is declared here rather than in
`Kwon1002/Section4.lean`, where the rest of §4's statements live, because the
`v_s ≠ 0` branch it consumes is discharged in `Kwon1002/NonzeroMode.lean`;
a declaration in `Section4` would sit below every module able to prove it and
so could never lose its `sorry`. -/
theorem prop_4_1_marked_factorization (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) :=
  prop_4_1_marked_factorization_unconditional r D A hD hA

/-- Machine check: the statement proved above **is** the canonical
Proposition 4.1, verbatim as `Kwon1002/Section4.lean` used to state it. -/
example : @prop_4_1_marked_factorization_unconditional
    = @Kwon1002.prop_4_1_marked_factorization := rfl

end

end Kwon1002
