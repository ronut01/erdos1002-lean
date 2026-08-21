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
  Proposition 4.1**, the statement of the sorried canonical
  `Kwon1002.prop_4_1_marked_factorization` of `Kwon1002/Section4.lean`.

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

/-- Machine check: the statement above **is** the canonical one. -/
example : @prop_4_1_error_shape_unconditional
    = @Kwon1002.Prop41.prop_4_1_error_shape := rfl

end

end NonzeroMode

/-! ## Proposition 4.1 in `Kwon1002`'s own namespace

Reproduced from `Kwon1002/Section4.lean` lines 137-144; placing it in
`namespace Kwon1002` makes `GoodTuple`, `IsInPD`, `Lnorm`, `digit`, `theta`
and `stationaryMean` resolve exactly as they do there. -/

noncomputable section

/-- **Proposition 4.1 (Marked factorization), display (27), unconditional.**

Statement token-identical to the canonical
`Kwon1002.prop_4_1_marked_factorization` (sorried in `Kwon1002/Section4.lean`
because that module sits below the modules that discharge it).  All three
steps of the §4 body are now proved: step 1
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

/-- Machine check: the statement above **is** the canonical Proposition 4.1
of `Kwon1002/Section4.lean`. -/
example : @prop_4_1_marked_factorization_unconditional
    = @Kwon1002.prop_4_1_marked_factorization := rfl

end

end Kwon1002
