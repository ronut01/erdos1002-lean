import Kwon1002.P42Later

/-!
# Proposition 4.2, assembled above the modules that discharge its cases

`Kwon1002/MonomialCore.lean` decomposes the proof of Proposition 4.2 into the
manuscript's three cases and assembles them; but it sits *below*
`Kwon1002/PhaseBounds.lean`, so the case-1 proof living there cannot be used
by it.  This file sits above every module that proves a case, and redoes the
assembly with the proved inputs.

## What is achieved here

* **Cases 1 and 2 are consumed, proved.**  `P42Later.laterMode_phase_bound''`
  is case 2, proved outright.
* **Case 1.**  `PhaseBounds.zeroMode_gauss_mixing'` is
  the token-identical, sorry-free form of `MonomialCore.zeroMode_gauss_mixing`;
  the assembly below uses it directly, so the zero-mode branch of
  Proposition 4.2 carries no residual.
* **The bilinear bookkeeping is redone** on top of that assembly, giving
  `prop_4_2_two_block_factorization''`, machine-checked (`rfl`) to be the
  canonical `Kwon1002.prop_4_2_two_block_factorization` of
  `Kwon1002/Section4.lean`.

## Residuals

Exactly one: `earlierMode_phase_bound'`, case 3 of the manuscript's proof
("the earlier mode is nonzero and the later mode is zero"), restated here
token-identically from `Kwon1002/MonomialCore.lean`.  Case 2 is proved in
`Kwon1002/P42Later.lean` and case 1 in `Kwon1002/PhaseBounds.lean`;
everything else on the route from the cases to display (34) is proved
outright.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace P42Unc

noncomputable section

/-! ## 1. The two nonzero-mode cases -/

/-- **Case 2 of the proof of 4.2**, "Assume the later mode `(r₂,s₂)` is
nonzero", token-identical to `Kwon1002.MonomialCore.laterMode_phase_bound`,
**proved** in `Kwon1002/P42Later.lean`. -/
theorem laterMode_phase_bound' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ Prop42.modeBox K, m' ≠ (0, 0) →
      ∀ p ∈ bulkPairs n, C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) :=
  P42Later.laterMode_phase_bound'' R K Wu Wv

/-- **Case 3 of the proof of 4.2**, "the earlier mode is nonzero and the later
mode is zero", token-identical to
`Kwon1002.MonomialCore.earlierMode_phase_bound`. -/
theorem earlierMode_phase_bound' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, m ≠ (0, 0) → ∀ w' ∈ Wv,
      ∀ p ∈ bulkPairs n,
        100 * Hscale n < |(p.2 : ℝ) - ((mIndex n : ℝ) + (p.1 : ℝ)) / 2| →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  sorry

/-! ## 2. The monomial core, with case 1 discharged

The proof is the three-case merge of `MonomialCore.two_block_monomial_core'`,
with `PhaseBounds.zeroMode_gauss_mixing'` — proved — in place of the sorried
`MonomialCore.zeroMode_gauss_mixing`. -/

/-- **Monomial core of Proposition 4.2**, token-identical to
`Kwon1002.Prop42.two_block_monomial_core`. -/
theorem two_block_monomial_core''' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ Prop42.modeBox K,
        (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
            ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
                    Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)
                  - Prop42.monoStationary R w m.1 m.2 * Prop42.monoStationary R w' m'.1 m'.2‖
                ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                        + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
          ≤ C * Lnorm n * Hscale n := by
  classical
  obtain ⟨CA, cA, ρA, hCA0, hcA0, hρA0, hρA1, hA⟩ :=
    PhaseBounds.zeroMode_gauss_mixing' R Wu Wv
  obtain ⟨CB, cB, ρB, hCB0, hcB0, hρB0, hρB1, hB⟩ := laterMode_phase_bound' R K Wu Wv
  obtain ⟨CD, cD, ρD, hCD0, hcD0, hρD0, hρD1, hD⟩ := earlierMode_phase_bound' R K Wu Wv
  set C₁ : ℝ := max CA (max CB CD) with hC₁def
  set c₁ : ℝ := min cA (min cB cD) with hc₁def
  set ρ₁ : ℝ := max ρA (max ρB ρD) with hρ₁def
  set A : ℝ := 1 / lyapunov + 1 with hAdef
  have hA0 : 0 < A := by
    have h := one_div_pos.2 Prop42.lyapunov_pos
    rw [hAdef]; linarith
  set C : ℝ := max C₁ (A * (C₁ + 205)) with hCdef
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le hCA0 (le_max_left _ _)
  have hc₁0 : 0 < c₁ := lt_min hcA0 (lt_min hcB0 hcD0)
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le hρA0 (le_max_left _ _)
  have hρ₁1 : ρ₁ < 1 := max_lt hρA1 (max_lt hρB1 hρD1)
  have hC0 : 0 < C := lt_of_lt_of_le hC₁0 (le_max_left _ _)
  have hC₁C : C₁ ≤ C := le_max_left _ _
  refine ⟨C, c₁, ρ₁, hC0, hc₁0, hρ₁0, hρ₁1, ?_⟩
  have htend : Filter.Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hA, hB, hD, htend.eventually_ge_atTop 1] with n hAn hBn hDn hL1
  intro w hw m hm w' hw' m' hm'
  have hL0 : (0 : ℝ) ≤ Lnorm n := by linarith
  have hH1 : (1 : ℝ) ≤ Hscale n := MonomialCore.one_le_Hscale hL1
  have hH0 : (0 : ℝ) ≤ Hscale n := by linarith
  set Exc : Finset (ℕ × ℕ) :=
    MonomialCore.nearDiag n (C₁ * Hscale n) ∪ MonomialCore.nearRes n (100 * Hscale n)
    with hExcdef
  have hsub : {p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)
            - Prop42.monoStationary R w m.1 m.2 * Prop42.monoStationary R w' m'.1 m'.2‖
          ≤ C * (Real.exp (-c₁ * Real.sqrt (Lnorm n))
                  + Real.exp (-c₁ * Hscale n) + ρ₁ ^ (c₁ * Hscale n))} ⊆ ↑Exc := by
    rintro p ⟨hp1, hp2⟩
    by_contra hcon
    apply hp2
    have hpb : p ∈ bulkPairs n := Finset.mem_coe.mp hp1
    have hnd : p ∉ MonomialCore.nearDiag n (C₁ * Hscale n) := fun h =>
      hcon (Finset.mem_coe.2 (Finset.mem_union_left _ h))
    have hnr : p ∉ MonomialCore.nearRes n (100 * Hscale n) := fun h =>
      hcon (Finset.mem_coe.2 (Finset.mem_union_right _ h))
    have hgap : C₁ * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) := by
      by_contra hg
      push_neg at hg
      exact hnd (Finset.mem_filter.2 ⟨hpb, hg⟩)
    have hres : 100 * Hscale n < |(p.2 : ℝ) - ((mIndex n : ℝ) + (p.1 : ℝ)) / 2| := by
      by_contra hg
      push_neg at hg
      exact hnr (Finset.mem_filter.2 ⟨hpb, hg⟩)
    by_cases hm'0 : m' = (0, 0)
    · have hm'1 : m'.1 = 0 := by rw [hm'0]
      have hm'2 : m'.2 = 0 := by rw [hm'0]
      by_cases hm0 : m = (0, 0)
      · have hm1 : m.1 = 0 := by rw [hm0]
        have hm2 : m.2 = 0 := by rw [hm0]
        rw [hm1, hm2, hm'1, hm'2]
        refine le_trans (hAn w hw w' hw' p hpb ?_) ?_
        · calc CA * Hscale n ≤ C₁ * Hscale n :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hH0
            _ < _ := hgap
        · exact MonomialCore.err_le hCA0 (le_trans (le_max_left _ _) hC₁C) hc₁0
            (min_le_left _ _) hρA0 (le_max_left _ _) hρ₁1 hL0 hH0
      · have hstat : Prop42.monoStationary R w m.1 m.2 = 0 :=
          MonomialCore.monoStationary_eq_zero R w (by rw [Prod.mk.eta]; exact hm0)
        rw [hm'1, hm'2, hstat, zero_mul, sub_zero]
        refine le_trans (hDn w hw m hm hm0 w' hw' p hpb hres) ?_
        exact MonomialCore.err_le hCD0
          (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC₁C)
          hc₁0 (le_trans (min_le_right _ _) (min_le_right _ _))
          hρD0 (le_trans (le_max_right _ _) (le_max_right _ _)) hρ₁1 hL0 hH0
    · have hstat : Prop42.monoStationary R w' m'.1 m'.2 = 0 :=
        MonomialCore.monoStationary_eq_zero R w' (by rw [Prod.mk.eta]; exact hm'0)
      rw [hstat, mul_zero, sub_zero]
      refine le_trans (hBn w hw m hm w' hw' m' hm' hm'0 p hpb ?_) ?_
      · calc CB * Hscale n ≤ C₁ * Hscale n :=
              mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hH0
          _ < _ := hgap
      · exact MonomialCore.err_le hCB0
          (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC₁C)
          hc₁0 (le_trans (min_le_right _ _) (min_le_left _ _))
          hρB0 (le_trans (le_max_left _ _) (le_max_right _ _)) hρ₁1 hL0 hH0
  have hfin := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hfin
  have hcount : ((Exc.card : ℕ) : ℝ) ≤ C * Lnorm n * Hscale n := by
    have h1 : ((Exc.card : ℕ) : ℝ) ≤ (A * (C₁ + 205)) * Lnorm n * Hscale n := by
      rw [hExcdef, hAdef]
      exact MonomialCore.exc_card_bound n C₁ hC₁0.le hL1
    have h2 : A * (C₁ + 205) ≤ C := le_max_right _ _
    calc ((Exc.card : ℕ) : ℝ) ≤ (A * (C₁ + 205)) * Lnorm n * Hscale n := h1
      _ = (A * (C₁ + 205)) * (Lnorm n * Hscale n) := by ring
      _ ≤ C * (Lnorm n * Hscale n) := mul_le_mul_of_nonneg_right h2 (mul_nonneg hL0 hH0)
      _ = C * Lnorm n * Hscale n := by ring
  refine le_trans ?_ hcount
  exact_mod_cast hfin

end

end P42Unc

/-! ## 3. Token-identical restatements and the canonical Proposition 4.2 -/

namespace Prop42

noncomputable section

/-- Token-identical restatement of `Kwon1002.Prop42.two_block_monomial_core`
(triple-primed: `MonomialCore` claims the single prime and `P42Cases` the
double). -/
theorem two_block_monomial_core''' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ modeBox K,
        (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
            ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
                    monoAt R w m.1 m.2 α n p.1 * monoAt R w' m'.1 m'.2 α n p.2)
                  - monoStationary R w m.1 m.2 * monoStationary R w' m'.1 m'.2‖
                ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                        + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
          ≤ C * Lnorm n * Hscale n :=
  P42Unc.two_block_monomial_core''' R K Wu Wv

/-- Machine check: the statement above **is** the canonical monomial core. -/
example : @two_block_monomial_core''' = @Kwon1002.Prop42.two_block_monomial_core := rfl

end

end Prop42

noncomputable section

/-- **Proposition 4.2** (Two-block factorization), display (34), assembled
from the monomial core of §2 by the bilinear bookkeeping of `Prop42`. -/
theorem prop_4_2_two_block_factorization'' {R K : ℕ} (U V : WindowSymbol R K) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                      + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n := by
  classical
  obtain ⟨C₀, c, ρ, hC₀, hc, hρ0, hρ1, hcore⟩ :=
    Prop42.two_block_monomial_core''' R K U.words V.words
  set C : ℝ := max 1 (max
      ((∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
        * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀)
      ((((Prop42.symIdx U).card * (Prop42.symIdx V).card : ℕ) : ℝ) * C₀)) with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCA : (∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
      * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀ ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCN : (((Prop42.symIdx U).card * (Prop42.symIdx V).card : ℕ) : ℝ) * C₀ ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, c, ρ, by linarith, hc, hρ0, hρ1, ?_⟩
  filter_upwards [hcore, eventually_ge_atTop 1] with n hn hn1
  have hL : (0 : ℝ) ≤ Lnorm n := Real.log_nonneg (by exact_mod_cast hn1)
  have hH : (0 : ℝ) ≤ Hscale n := Real.rpow_nonneg hL _
  set E : ℝ := Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n)
      + ρ ^ (c * Hscale n) with hEdef
  have hEpos : 0 < E := by
    have h1 := Real.exp_pos (-c * Real.sqrt (Lnorm n))
    have h2 := Real.exp_pos (-c * Hscale n)
    have h3 := Real.rpow_pos_of_pos hρ0 (c * Hscale n)
    rw [hEdef]; linarith
  set Bad : (((Fin (2 * R) → ℕ) × ℤ × ℤ) × ((Fin (2 * R) → ℕ) × ℤ × ℤ)) → Finset (ℕ × ℕ) :=
    fun q => (bulkPairs n).filter (fun p =>
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
            Prop42.monoAt R q.1.1 q.1.2.1 q.1.2.2 α n p.1
              * Prop42.monoAt R q.2.1 q.2.2.1 q.2.2.2 α n p.2)
          - Prop42.monoStationary R q.1.1 q.1.2.1 q.1.2.2
            * Prop42.monoStationary R q.2.1 q.2.2.1 q.2.2.2‖
        ≤ C₀ * E) with hBad
  have hIdx : ∀ q ∈ Prop42.symIdx U ×ˢ Prop42.symIdx V,
      ((Bad q).card : ℝ) ≤ C₀ * Lnorm n * Hscale n := by
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Prop42.symIdx, Finset.mem_product] at hq1 hq2
    have hcore' := hn q.1.1 hq1.1 q.1.2 hq1.2 q.2.1 hq2.1 q.2.2 hq2.2
    rw [hBad]
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    exact hcore'
  have hsub : {p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}
      ⊆ ↑((Prop42.symIdx U ×ˢ Prop42.symIdx V).biUnion Bad) := by
    rintro p ⟨hp1, hp2⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    by_contra hcon
    push_neg at hcon
    apply hp2
    have hmono : ∀ t ∈ Prop42.symIdx U, ∀ t' ∈ Prop42.symIdx V,
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R t.1 t.2.1 t.2.2 α n p.1
                * Prop42.monoAt R t'.1 t'.2.1 t'.2.2 α n p.2)
            - Prop42.monoStationary R t.1 t.2.1 t.2.2
              * Prop42.monoStationary R t'.1 t'.2.1 t'.2.2‖
          ≤ C₀ * E := by
      intro t ht t' ht'
      have hq := hcon (t, t') (Finset.mem_product.mpr ⟨ht, ht'⟩)
      simp only [hBad, Finset.mem_filter, not_and, not_not] at hq
      exact hq (Finset.mem_coe.mp hp1)
    calc ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖
        ≤ (∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * (C₀ * E) :=
          Prop42.two_block_bound_of_mono U V n p.1 p.2 (C₀ * E) hmono
      _ = ((∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀) * E := by ring
      _ ≤ C * E := mul_le_mul_of_nonneg_right hCA hEpos.le
  calc (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}).ncard : ℝ)
      ≤ ((((Prop42.symIdx U ×ˢ Prop42.symIdx V).biUnion Bad).card : ℕ) : ℝ) := by
        have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        rw [Set.ncard_coe_finset] at h
        exact_mod_cast h
    _ ≤ ∑ q ∈ Prop42.symIdx U ×ˢ Prop42.symIdx V, ((Bad q).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Prop42.symIdx U ×ˢ Prop42.symIdx V, C₀ * Lnorm n * Hscale n :=
        Finset.sum_le_sum hIdx
    _ = (((Prop42.symIdx U).card * (Prop42.symIdx V).card : ℕ) : ℝ) * C₀
          * (Lnorm n * Hscale n) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ C * (Lnorm n * Hscale n) :=
        mul_le_mul_of_nonneg_right hCN (mul_nonneg hL hH)
    _ = C * Lnorm n * Hscale n := by ring

/-- Machine check: the statement above **is** the canonical Proposition 4.2
of `Kwon1002/Section4.lean`. -/
example : @prop_4_2_two_block_factorization''
    = @Kwon1002.prop_4_2_two_block_factorization := rfl

end

end Kwon1002
