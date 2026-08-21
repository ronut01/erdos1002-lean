import Kwon1002.P42Super

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
  canonical `Kwon1002.prop_4_2_two_block_factorization` — which is itself
  declared here, since `Kwon1002/Section4.lean` sits below every module that
  discharges a case and so could never prove it.

* **Case 3 is consumed, proved.**  Its `k < t₀ − 100H` branch is
  `P42Later.earlierMode_subResonance_bound` and its `k > t₀ + 100H` branch is
  `P42Super.earlierMode_superResonance_bound'`; `earlierMode_phase_bound'`
  merges them.

## Residuals

**None.**  `prop_4_2_two_block_factorization''` is proved outright, and is
`rfl`-checked below to be the canonical
`Kwon1002.prop_4_2_two_block_factorization`, declared here.
Case 1 is proved in `Kwon1002/PhaseBounds.lean`, case 2 and the
`k < t₀ − 100H` branch of case 3 in `Kwon1002/P42Later.lean`, the
`k > t₀ + 100H` branch of case 3 in `Kwon1002/P42Super.lean`, and everything
else on the route from the cases to display (34) is proved outright.  With
Proposition 4.1 (`Kwon1002/Prop41Final.lean`) already closed, this completes
section 4.
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

/-- **The super-resonance branch of case 3**, "If `k > t₀ + 100H`",
**proved** in `Kwon1002/P42Super.lean`.

The sub-resonance branch `k < t₀ − 100H` is `P42Later.earlierMode_subResonance_bound`,
and case 3 is assembled from the two branches below.  This branch carries out
the manuscript's extra step: on each retained depth-`t₊` cylinder the earlier
phase is frozen (`NonzeroMode.phase_freeze_on_cylinder`, at the margin
supplied by `PhaseBounds.ascended_descendant_bound_at_cut`), the later
zero-mode block is replaced by its stationary Gauss mean
(`StationaryReplace.leb_halfOpen_multiblock_mixing`, at a gap of `H` past
`t₊`, which `P42Cases.mixingGap_ground` provides), the discarded depth-`t₊`
cylinders are restored, and what is left — the earlier monomial alone — is
killed by display (22) at prefix depth `j + R` with descendant depth `t₋`
(`P42Super.oscillatory_single_bound`, the `P42Later` engine at the degenerate
pair `(j, j)`). -/
theorem earlierMode_superResonance_bound (R K : ℕ)
    (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, m ≠ (0, 0) → ∀ w' ∈ Wv,
      ∀ p ∈ bulkPairs n,
        Prop41.resonanceTime n p.1 + 100 * Hscale n < (p.2 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) :=
  P42Super.earlierMode_superResonance_bound' R K Wu Wv

/-- **Case 3 of the proof of 4.2**, "the earlier mode is nonzero and the later
mode is zero", token-identical to
`Kwon1002.MonomialCore.earlierMode_phase_bound`, assembled from its two
branches, both proved: the sub-resonance branch in `Kwon1002/P42Later.lean`,
the super-resonance branch in `Kwon1002/P42Super.lean`. -/
theorem earlierMode_phase_bound' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, m ≠ (0, 0) → ∀ w' ∈ Wv,
      ∀ p ∈ bulkPairs n,
        100 * Hscale n < |(p.2 : ℝ) - ((mIndex n : ℝ) + (p.1 : ℝ)) / 2| →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  obtain ⟨C₁, c₁, ρ₁, hC₁, hc₁, hρ₁0, hρ₁1, hsub⟩ :=
    P42Later.earlierMode_subResonance_bound R K Wu Wv
  obtain ⟨C₂, c₂, ρ₂, hC₂, hc₂, hρ₂0, hρ₂1, hsup⟩ :=
    earlierMode_superResonance_bound R K Wu Wv
  refine ⟨max C₁ C₂, min c₁ c₂, max ρ₁ ρ₂, lt_of_lt_of_le hC₁ (le_max_left _ _),
    lt_min hc₁ hc₂, lt_of_lt_of_le hρ₁0 (le_max_left _ _), max_lt hρ₁1 hρ₂1, ?_⟩
  have htend : Filter.Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsub, hsup, htend.eventually_ge_atTop 1] with n hsubn hsupn hL1
  intro w hw m hm hm0 w' hw' p hp habs
  have hL0 : (0 : ℝ) ≤ Lnorm n := by linarith
  have hH0 : (0 : ℝ) ≤ Hscale n := by
    have := MonomialCore.one_le_Hscale hL1
    linarith
  have hres : Prop41.resonanceTime n p.1 = ((mIndex n : ℝ) + (p.1 : ℝ)) / 2 := rfl
  rcases lt_abs.1 habs with hcase | hcase
  · -- `k > t₀ + 100H`
    refine le_trans (hsupn w hw m hm hm0 w' hw' p hp (by rw [hres]; linarith)) ?_
    exact MonomialCore.err_le hC₂ (le_max_right _ _) (lt_min hc₁ hc₂)
      (min_le_right _ _) hρ₂0 (le_max_right _ _) (max_lt hρ₁1 hρ₂1) hL0 hH0
  · -- `k < t₀ − 100H`
    refine le_trans (hsubn w hw m hm hm0 w' hw' p hp (by rw [hres]; linarith)) ?_
    exact MonomialCore.err_le hC₁ (le_max_left _ _) (lt_min hc₁ hc₂)
      (min_le_left _ _) hρ₁0 (le_max_left _ _) (max_lt hρ₁1 hρ₂1) hL0 hH0

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

/-- **Monomial core of Proposition 4.2.**  This is the content of Kwon's
proof of 4.2 ("It suffices to treat monomials"): the three-case analysis
that uses Lemma 3.3 (`shrinking_anti_concentration`, proved), Lemma 3.4
(`descendant_phase_small`, proved), the denominator deviation (20), and -
the input not yet available in this development, Lemma 3.2's conditional
two-sided Gauss mixing across the block gap — an input now supplied by
`Kwon1002/PhaseBounds.lean`, which is why this statement is declared here and
not in `Kwon1002/Prop42.lean`.  The constants are allowed to
depend on the radius `R`, the mode cap `K` and the two finite word sets,
exactly as in the manuscript, where `U` and `V` are fixed.

The anti-concentration constant `c` here is the `c` of `η = e^{-cH}`; by
`acCompatible_of_le_one` every `c ≤ 1` meets the compatibility constraint
`c + 3δ < 80λ` of referee note 5, so the existential quantifier over `c`
absorbs it and it constrains nothing downstream. -/
theorem two_block_monomial_core (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
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

/-- **Proposition 4.2** (Two-block factorization), display (34).

For window symbols `U, V` of radius `R` and mode budget `K`, all but
`O_{U,V}(LH)` pairs `j < k` in `J_n` satisfy

`|∫₀¹ U_j V_k dα - ∫U dμ̂₀ ∫V dμ̂₀| ≤ C_{U,V}(e^{-cL^{1/2}} + e^{-cH} + ρ^{cH})`.

**Reading (exceptional set).**  "All but `O(LH)` pairs" is rendered as a
cardinality bound on the set of pairs in `J_n` *failing* the estimate,
with the implied constant depending only on `U` and `V`, not on `n`.

**Reading (constants).**  `c` and `ρ ∈ (0,1)` are the mixing/deviation
constants of §3, existentially quantified together with `C`; note cosmetic
item 5 of our referee report: the proof needs the anti-concentration
constant `c` (in `η = e^{-cH}`), together with `3δ`, to sit below
`80λ ≈ 94.9`.  That compatibility is a constraint on the *choice* of `c`
and so is absorbed by the existential here.

This is the canonical name.  It is declared here rather than in
`Kwon1002/Section4.lean`, where the rest of §4's statements live, because the
three cases of its monomial core are discharged in `Kwon1002/PhaseBounds.lean`,
`Kwon1002/P42Later.lean` and `Kwon1002/P42Super.lean`; a declaration in
`Section4` would sit below all of them and so could never lose its `sorry`. -/
theorem prop_4_2_two_block_factorization {R K : ℕ} (U V : WindowSymbol R K) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                      + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n :=
  prop_4_2_two_block_factorization'' U V

/-- Machine check: the statement proved above **is** the canonical
Proposition 4.2, verbatim as `Kwon1002/Section4.lean` used to state it. -/
example : @prop_4_2_two_block_factorization''
    = @Kwon1002.prop_4_2_two_block_factorization := rfl

end


/-! ## Proposition 4.2 in `namespace Prop42`

`Kwon1002/Prop42.lean` carries the bilinear bookkeeping that turns the
monomial core into display (34); the derivation is reproduced here, above the
modules that discharge the core's three cases. -/

namespace Prop42

noncomputable section

/-- **Proposition 4.2** (Two-block factorization), display (34), the
`namespace Prop42` reading: the bilinear bookkeeping of this namespace run on
`two_block_monomial_core`.  Declared here rather than in
`Kwon1002/Prop42.lean` because the core is. -/
theorem prop_4_2_two_block_factorization {R K : ℕ} (U V : WindowSymbol R K) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                      + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n := by
  classical
  obtain ⟨C₀, c, ρ, hC₀, hc, hρ0, hρ1, hcore⟩ := two_block_monomial_core R K U.words V.words
  set C : ℝ := max 1 (max
      ((∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
        * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀)
      ((((symIdx U).card * (symIdx V).card : ℕ) : ℝ) * C₀)) with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCA : (∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
      * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀ ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCN : (((symIdx U).card * (symIdx V).card : ℕ) : ℝ) * C₀ ≤ C :=
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
            monoAt R q.1.1 q.1.2.1 q.1.2.2 α n p.1 * monoAt R q.2.1 q.2.2.1 q.2.2.2 α n p.2)
          - monoStationary R q.1.1 q.1.2.1 q.1.2.2 * monoStationary R q.2.1 q.2.2.1 q.2.2.2‖
        ≤ C₀ * E) with hBad
  -- (a) each monomial pair contributes at most `C₀ L H` exceptional pairs
  have hIdx : ∀ q ∈ symIdx U ×ˢ symIdx V,
      ((Bad q).card : ℝ) ≤ C₀ * Lnorm n * Hscale n := by
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [symIdx, Finset.mem_product] at hq1 hq2
    have hcore' := hn q.1.1 hq1.1 q.1.2 hq1.2 q.2.1 hq2.1 q.2.2 hq2.2
    rw [hBad]
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    exact hcore'
  -- (b) the exceptional set of the pair `(U,V)` is covered by those of the monomials
  have hsub : {p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}
      ⊆ ↑((symIdx U ×ˢ symIdx V).biUnion Bad) := by
    rintro p ⟨hp1, hp2⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    by_contra hcon
    push_neg at hcon
    apply hp2
    have hmono : ∀ t ∈ symIdx U, ∀ t' ∈ symIdx V,
        ‖(∫ α in Ioo (0 : ℝ) 1,
              monoAt R t.1 t.2.1 t.2.2 α n p.1 * monoAt R t'.1 t'.2.1 t'.2.2 α n p.2)
            - monoStationary R t.1 t.2.1 t.2.2 * monoStationary R t'.1 t'.2.1 t'.2.2‖
          ≤ C₀ * E := by
      intro t ht t' ht'
      have hq := hcon (t, t') (Finset.mem_product.mpr ⟨ht, ht'⟩)
      simp only [hBad, Finset.mem_filter, not_and, not_not] at hq
      exact hq (Finset.mem_coe.mp hp1)
    calc ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖
        ≤ (∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * (C₀ * E) :=
          two_block_bound_of_mono U V n p.1 p.2 (C₀ * E) hmono
      _ = ((∑ t ∈ symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀) * E := by ring
      _ ≤ C * E := mul_le_mul_of_nonneg_right hCA hEpos.le
  -- (c) count
  calc (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}).ncard : ℝ)
      ≤ ((((symIdx U ×ˢ symIdx V).biUnion Bad).card : ℕ) : ℝ) := by
        have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        rw [Set.ncard_coe_finset] at h
        exact_mod_cast h
    _ ≤ ∑ q ∈ symIdx U ×ˢ symIdx V, ((Bad q).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ symIdx U ×ˢ symIdx V, C₀ * Lnorm n * Hscale n := Finset.sum_le_sum hIdx
    _ = (((symIdx U).card * (symIdx V).card : ℕ) : ℝ) * C₀ * (Lnorm n * Hscale n) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ C * (Lnorm n * Hscale n) :=
        mul_le_mul_of_nonneg_right hCN (mul_nonneg hL hH)
    _ = C * Lnorm n * Hscale n := by ring

/-- Machine check: the `namespace Prop42` reading **is** the canonical
Proposition 4.2. -/
example : @prop_4_2_two_block_factorization
    = @Kwon1002.prop_4_2_two_block_factorization := rfl

end

end Prop42

end Kwon1002
