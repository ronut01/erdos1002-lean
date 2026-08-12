import Kwon1002.ErrorShape
import Kwon1002.MonomialCore

/-!
# Scratch (`prop4`): closing step 1 of §4, and the two §4 targets

Targets:

* `Kwon1002.Prop41.prop_4_1_error_shape` (display (30)), and
* `Kwon1002.prop_4_1_marked_factorization` (display (27), the canonical
  §4 statement of `Kwon1002/Section4.lean`),

both reproduced **token-identically** below (`prop_4_1_error_shape''`,
`prop_4_1_marked_factorization''`; diffed against `Kwon1002/Prop41.lean`
lines 303-310 and `Kwon1002/Section4.lean` lines 137-144, only the name
carries the primes).  Nothing is weakened.

## What is new here

`Kwon1002/ErrorShape.lean` already derives display (30) from a three-step
decomposition of the manuscript's proof (lines ≈ 331-404),

1. `integral_eq_sum_modeTerm`, the digit-Fourier expansion,
2. `zero_mode_factorization`, the `v = 0` branch,
3. `nonzero_mode_small`, the `v_s ≠ 0` branch,

all three sorried.  **This file proves step 1 outright** and reassembles
display (30) from it, so that the §4 body now rests on two inputs rather
than three.

Step 1 is the manuscript's sentence "Expand both in the digit values and in
the Fourier modes `v_1,…,v_r`, and pull out the scalar coefficient of each
digit-Fourier term."  What it actually needs, and what is supplied here:

* `coeff_norm_le`, a single coefficient of a `P_D(L)` symbol is bounded by
  the `ℓ¹` mass, `‖c(a,v)‖ ≤ L^D`.  This is where `(24)`'s *two* vanishing
  hypotheses are used: they make the coefficient family supported on the
  finite box `{a ≤ L^D} × {|v| ≤ L^D}`, so the `tsum` of `(24)` is a finite
  sum and no summability side condition is needed anywhere.
* `torusChar_sum`, `e(∑ t_ℓ) = ∏ e(t_ℓ)`, the reason the `r`-fold Fourier
  expansion recombines into the single phase of `modeTerm`.
* `prod_eq_sum_mode`, the pointwise expansion, valid for **every** `α`
  (not just a.e.): each factor is a finite sum over `modeBox`, and
  `Finset.prod_univ_sum` turns the `r`-fold product of finite sums into the
  sum over `modeTuples`, which is *literally* `Fintype.piFinset (fun _ =>
  modeBox D L)`, so the mode box of `ErrorShape` is exactly what the
  expansion produces.
* `integrableOn_modeFun`, each mode function is integrable on `(0,1)`:
  measurable (through `Prop42.measurable_digitNat` and
  `Kwon1002.measurable_theta`) and bounded by `(L^D)^r` (through
  `coeff_norm_le` and `Prop42.norm_torusChar`), on a finite-measure set.
  This is what licenses the interchange `∫ ∑ = ∑ ∫`.

The manuscript's "interchange" is therefore *not* dominated convergence for
a genuine series: `(24)` is a finitely supported family, so the expansion is
a finite sum throughout and the interchange is `integral_finset_sum`.  That
is a small simplification of the obstruction as recorded in
`ErrorShape.integral_eq_sum_modeTerm`'s docstring, and it is why step 1 can
be closed here at all.

## Sorried results consumed

* `Kwon1002.ErrorShape.zero_mode_factorization` (the `v = 0` branch), and
* `Kwon1002.ErrorShape.nonzero_mode_small` (the `v_s ≠ 0` branch).

Nothing else.  In particular `ErrorShape.integral_eq_sum_modeTerm` is *not*
consumed, `integral_eq_sum_modeTerm'` below replaces it, and is proved.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace Prop4Final

open Prop41 ErrorShape

noncomputable section

/-! ## 1. `e(∑ t_ℓ) = ∏ e(t_ℓ)` -/

/-- The additive character of §4 is multiplicative over a finite family. -/
theorem torusChar_sum {r : ℕ} (t : Fin r → ℝ) :
    torusChar (∑ i, t i) = ∏ i, torusChar (t i) := by
  unfold torusChar
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-! ## 2. A single coefficient is bounded by the `ℓ¹` mass of (24)

`(24)` bounds `∑_{a,v} |c(a,v)|` by `L^D` and kills every coefficient
outside the box `{a ≤ L^D} × {|v| ≤ L^D}`.  The box being finite is what
turns the `tsum` into a finite sum, and hence gives the per-coefficient
bound with no summability hypothesis. -/

theorem coeff_norm_le (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) (a : ℕ) (v : ℤ) :
    ‖c ℓ a v‖ ≤ L ^ D := by
  classical
  set box : Finset (ℕ × ℤ) := Finset.range (⌊L ^ D⌋₊ + 1) ×ˢ modeBox D L with hboxdef
  have hzero : ∀ p ∉ box, ‖c ℓ p.1 p.2‖ = 0 := by
    intro p hp
    by_cases hv : p.2 ∈ modeBox D L
    · have h1 : p.1 ∉ Finset.range (⌊L ^ D⌋₊ + 1) := by
        intro h
        exact hp (by rw [hboxdef]; exact Finset.mem_product.2 ⟨h, hv⟩)
      rw [Finset.mem_range, not_lt] at h1
      have hR : L ^ D < (p.1 : ℝ) := by
        have hfl : L ^ D < (⌊L ^ D⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one (L ^ D)
        have hcast : ((⌊L ^ D⌋₊ + 1 : ℕ) : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast h1
        push_cast at hcast
        linarith
      rw [(hc ℓ hℓ).1 p.1 p.2 hR, norm_zero]
    · rw [coeff_eq_zero_of_notMem_modeBox r D L F c hc ℓ hℓ p.1 p.2 hv, norm_zero]
  have htsum : (∑' p : ℕ × ℤ, ‖c ℓ p.1 p.2‖) = ∑ p ∈ box, ‖c ℓ p.1 p.2‖ :=
    tsum_eq_sum hzero
  have hle : ∑ p ∈ box, ‖c ℓ p.1 p.2‖ ≤ L ^ D := by
    rw [← htsum]; exact (hc ℓ hℓ).2.2.1
  by_cases hmem : (a, v) ∈ box
  · refine le_trans ?_ hle
    exact Finset.single_le_sum (f := fun p : ℕ × ℤ => ‖c ℓ p.1 p.2‖)
      (fun p _ => norm_nonneg _) hmem
  · have h0 : ‖c ℓ a v‖ = 0 := hzero (a, v) hmem
    have hnn : (0 : ℝ) ≤ ∑ p ∈ box, ‖c ℓ p.1 p.2‖ :=
      Finset.sum_nonneg (fun p _ => norm_nonneg _)
    rw [h0]; linarith

/-! ## 3. The pointwise digit-Fourier expansion

Manuscript: "Expand both in the digit values and in the Fourier modes
`v_1,…,v_r`, and pull out the scalar coefficient of each digit-Fourier
term."  Valid for every `α`, with no exceptional set. -/

theorem prod_eq_sum_mode (n r : ℕ) (D : ℝ) (j : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D (Lnorm n) F c) (α : ℝ) :
    (∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      = ∑ v ∈ modeTuples r D (Lnorm n),
          (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
            torusChar (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ)) := by
  classical
  rw [← Fin.prod_univ_eq_prod_range
    (fun ℓ => F ℓ (digit α (j ℓ)) (theta α n (j ℓ))) r]
  have hstep : ∀ ℓ : Fin r,
      F (ℓ : ℕ) (digit α (j ℓ)) (theta α n (j ℓ))
        = ∑ v ∈ modeBox D (Lnorm n),
            c (ℓ : ℕ) (digit α (j ℓ)) v * torusChar ((v : ℝ) * theta α n (j ℓ)) := by
    intro ℓ
    rw [(hc (ℓ : ℕ) ℓ.isLt).2.2.2 (digit α (j ℓ)) (theta α n (j ℓ))]
    refine tsum_eq_sum ?_
    intro v hv
    rw [coeff_eq_zero_of_notMem_modeBox r D (Lnorm n) F c hc (ℓ : ℕ) ℓ.isLt _ v hv,
      zero_mul]
  simp only [hstep]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro v _
  rw [Finset.prod_mul_distrib, torusChar_sum]

/-! ## 4. Each mode function is integrable on `(0,1)` -/

theorem integrableOn_modeFun (n r : ℕ) (D : ℝ) (j : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D (Lnorm n) F c) (v : Fin r → ℤ) :
    IntegrableOn (fun α : ℝ =>
        (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
          torusChar (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ)))
      (Ioo (0 : ℝ) 1) volume := by
  classical
  have hm1 : Measurable fun α : ℝ => ∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ) := by
    refine Finset.measurable_prod _ ?_
    intro ℓ _
    exact (measurable_from_top (f := fun a : ℕ => c (ℓ : ℕ) a (v ℓ))).comp
      (Prop42.measurable_digitNat (j ℓ))
  have hm2 : Measurable fun α : ℝ =>
      torusChar (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ)) := by
    refine Prop42.continuous_torusChar.measurable.comp ?_
    refine Finset.measurable_sum _ ?_
    intro ℓ _
    exact (measurable_theta n (j ℓ)).const_mul _
  have hbd : ∀ α : ℝ,
      ‖(∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
          torusChar (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ))‖
        ≤ ((Lnorm n) ^ D) ^ r := by
    intro α
    rw [norm_mul, Prop42.norm_torusChar, mul_one, Complex.norm_prod]
    calc ∏ ℓ : Fin r, ‖c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)‖
        ≤ ∏ _ℓ : Fin r, (Lnorm n) ^ D :=
          Finset.prod_le_prod (fun ℓ _ => norm_nonneg _)
            (fun ℓ _ => coeff_norm_le r D (Lnorm n) F c hc (ℓ : ℕ) ℓ.isLt _ _)
      _ = ((Lnorm n) ^ D) ^ r := by simp
  refine Measure.integrableOn_of_bounded (M := ((Lnorm n) ^ D) ^ r) ?_
    (hm1.mul hm2).aestronglyMeasurable ?_
  · simp [Real.volume_Ioo]
  · filter_upwards with α using hbd α

/-! ## 5. Step 1 of the §4 body, proved

Statement reproduced token-identically from
`Kwon1002.ErrorShape.integral_eq_sum_modeTerm` (only the name is primed). -/

theorem integral_eq_sum_modeTerm' (n r : ℕ) (D : ℝ) (j : ℕ → ℕ)
    (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D (Lnorm n) F c) :
    (∫ α in Ioo (0 : ℝ) 1,
        ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      = ∑ v ∈ modeTuples r D (Lnorm n), modeTerm n r j c v := by
  classical
  have hpt := prod_eq_sum_mode n r D j F c hc
  simp only [hpt]
  rw [integral_finset_sum _ (fun v _ => integrableOn_modeFun n r D j F c hc v)]
  rfl

/-! ## 6. Display (30), reassembled from two inputs instead of three

The proof is `ErrorShape.prop_4_1_error_shape'` with its first input, the
sorried `integral_eq_sum_modeTerm`, replaced by the proved
`integral_eq_sum_modeTerm'` above.  The exponent produced is `B = 2Dr`; see
the discussion in `ErrorShape`. -/

theorem prop_4_1_error_shape'' (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ B C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ B * deltaScale c ρ n := by
  classical
  obtain ⟨C₂, ρ₂, hC₂, hρ₂0, hρ₂1, h2⟩ := zero_mode_factorization r D hD
  obtain ⟨C₃, c₃, ρ₃, hC₃, hc₃, hρ₃0, hρ₃1, h3⟩ := nonzero_mode_small r D hD
  have hc0 : (0 : ℝ) < min c₃ 200 := lt_min hc₃ (by norm_num)
  have hr0 : (0 : ℝ) < max ρ₂ ρ₃ := lt_of_lt_of_le hρ₂0 (le_max_left _ _)
  have hr1 : max ρ₂ ρ₃ < 1 := max_lt hρ₂1 hρ₃1
  refine ⟨2 * D * r, C₂ + 3 ^ r * C₃, min c₃ 200, max ρ₂ ρ₃,
    add_pos hC₂ (mul_pos (by positivity) hC₃), hc0, hr0, hr1, ?_⟩
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h2, h3, hLtend.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn2 hn3 hL1
  intro j hj F hF
  obtain ⟨cc, hcc⟩ := exists_representsPD r D (Lnorm n) F hF
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hH1 : (1 : ℝ) ≤ Hscale n := by
    rw [Hscale]; exact Real.one_le_rpow hL1 (by norm_num)
  have hH0 : (0 : ℝ) ≤ Hscale n := le_trans zero_le_one hH1
  have hX1 : (1 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) :=
    Real.one_le_rpow hL1 (by positivity)
  have hX0 : (0 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) := le_trans zero_le_one hX1
  have hY : (Lnorm n) ^ (2 * D * (r : ℝ))
      = (Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  have hδ0 : (0 : ℝ) ≤ deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := deltaScale_nonneg hr0 n
  have hA : ‖modeTerm n r j cc 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C₂ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    refine le_trans (hn2 j hj F cc hcc) ?_
    have hbr := zero_branch_le_deltaScale (c := min c₃ 200) (ρ := max ρ₂ ρ₃) (ρ₂ := ρ₂)
      n hρ₂0 hρ₂1 (le_max_left _ _) hc0 (min_le_right _ _) hH0
    have hpos : (0 : ℝ) ≤ C₂ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hbr hpos
  have hBnd : ∀ v ∈ (modeTuples r D (Lnorm n)).erase 0,
      ‖modeTerm n r j cc v‖
        ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    intro v hv
    rcases Finset.mem_erase.1 hv with ⟨hv0, hvmem⟩
    refine le_trans (hn3 j hj F cc hcc v hvmem hv0) ?_
    have hbr := nonzero_branch_le_deltaScale (c := min c₃ 200) (ρ := max ρ₂ ρ₃)
      (c₃ := c₃) (ρ₃ := ρ₃) n hr0 hr1 hρ₃0 (le_max_right _ _) hc0 (min_le_left _ _) hH0
    have hpos : (0 : ℝ) ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hbr hpos
  have hcardS : (((modeTuples r D (Lnorm n)).erase 0).card : ℝ)
      ≤ 3 ^ r * (Lnorm n) ^ (D * (r : ℝ)) := by
    refine le_trans ?_ (card_modeTuples_le r D (Lnorm n) hL1 hD.le)
    exact_mod_cast Finset.card_erase_le
  have hsum : ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, ‖modeTerm n r j cc v‖
      ≤ (3 ^ r * (Lnorm n) ^ (D * (r : ℝ))) *
          (C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hBnd) ?_
    rw [nsmul_eq_mul]
    have hb0 : (0 : ℝ)
        ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
      have : (0 : ℝ) ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
      exact mul_nonneg this hδ0
    exact mul_le_mul_of_nonneg_right hcardS hb0
  have h0mem : (0 : Fin r → ℤ) ∈ modeTuples r D (Lnorm n) := by
    rw [modeTuples, Fintype.mem_piFinset]
    intro i
    have hzero : (0 : Fin r → ℤ) i = 0 := rfl
    rw [hzero, modeBox, Finset.mem_Icc]
    exact ⟨neg_nonpos.2 (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  rw [integral_eq_sum_modeTerm' n r D j F cc hcc,
    ← Finset.add_sum_erase _ (modeTerm n r j cc) h0mem]
  have hrw : (modeTerm n r j cc 0
        + ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, modeTerm n r j cc v)
      - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)
      = (modeTerm n r j cc 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ))
        + ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, modeTerm n r j cc v := by
    ring
  rw [hrw]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add le_rfl (norm_sum_le _ _)) ?_
  refine le_trans (add_le_add hA hsum) ?_
  rw [hY]
  have hXX : (Lnorm n) ^ (D * (r : ℝ))
      ≤ (Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)) := by
    nlinarith
  have hstep : C₂ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n
      ≤ C₂ * ((Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)))
          * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    have h1 : C₂ * (Lnorm n) ^ (D * (r : ℝ))
        ≤ C₂ * ((Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ))) :=
      mul_le_mul_of_nonneg_left hXX hC₂.le
    exact mul_le_mul_of_nonneg_right h1 hδ0
  nlinarith [hδ0, hX0, hC₃.le]

/-! ## 7. The zero mode, reduced to Kwon's (17)

`ErrorShape.zero_mode_factorization` is stated with the *Fourier-side* data
still visible (`modeTerm … 0` and `∏ stationaryMean (F ℓ)`), and its
docstring names three gaps between it and the mixing input.  This section
removes the Fourier bookkeeping from that list: it shows that the zero-mode
defect **is literally** the multi-block mixing defect of Kwon's (17) for the
digit observables `g_ℓ(x) = c_ℓ(a_1(x), 0)`, so that only the genuinely
analytic gaps (Lebesgue `dα` versus Gauss `dν` on the outside; a `BV` bound
on `g_ℓ`) survive.

Two things get proved on the way, both of which the manuscript uses
silently:

* `integral_F_eq_coeff`, integrating a `P_D(L)` symbol over the torus
  variable kills every nonzero Fourier mode and returns the zero
  coefficient, `∫₀¹ F(a,θ) dθ = c(a,0)`.  (Uses the proved
  `MonomialCore.integral_torusChar_eq_zero`.)
* `stationaryMean_eq`, hence the right-hand side of (27) *is* the Gauss
  mean of the digit observable, `∫ F dθ dν = ∫ g dν`. -/

/-- The digit observable of the zero mode: `g_ℓ(x) = c_ℓ(a_1(x), 0)`. -/
def digitObs (c : ℕ → ℕ → ℤ → ℂ) (ℓ : ℕ) (x : ℝ) : ℂ := c ℓ (digit x 0) 0

theorem torusChar_zero : torusChar 0 = 1 := by
  simp [torusChar]

/-- `a_{k+1}(α) = a_1(T^k α)`: the digit at time `k` is the first digit of
the `k`-th iterate.  This is what makes the zero-mode integrand a genuine
multi-block product in the sense of (17). -/
theorem digit_gaussIter (α : ℝ) (k : ℕ) : digit (gaussIter α k) 0 = digit α k := by
  simp [digit]

/-- `∫₀¹ e(vθ) dθ = 1` if `v = 0` and `0` otherwise. -/
theorem integral_torusChar_mode (v : ℤ) :
    (∫ θ in Ioo (0 : ℝ) 1, torusChar ((v : ℝ) * θ)) = if v = 0 then 1 else 0 := by
  by_cases hv : v = 0
  · subst hv
    have hpt : ∀ θ : ℝ, torusChar (((0 : ℤ) : ℝ) * θ) = 1 := by
      intro θ
      rw [Int.cast_zero, zero_mul, torusChar_zero]
    simp only [hpt]
    rw [setIntegral_const]
    simp
  · rw [if_neg hv]
    exact MonomialCore.integral_torusChar_eq_zero hv

/-- **The torus integral of a `P_D(L)` symbol is its zero coefficient.** -/
theorem integral_F_eq_coeff (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) (a : ℕ) :
    (∫ θ in Ioo (0 : ℝ) 1, F ℓ a θ) = c ℓ a 0 := by
  classical
  have hexp : ∀ θ : ℝ,
      F ℓ a θ = ∑ v ∈ modeBox D L, c ℓ a v * torusChar ((v : ℝ) * θ) := by
    intro θ
    rw [(hc ℓ hℓ).2.2.2 a θ]
    refine tsum_eq_sum ?_
    intro v hv
    rw [coeff_eq_zero_of_notMem_modeBox r D L F c hc ℓ hℓ a v hv, zero_mul]
  have hint : ∀ v ∈ modeBox D L,
      IntegrableOn (fun θ : ℝ => c ℓ a v * torusChar ((v : ℝ) * θ))
        (Ioo (0 : ℝ) 1) volume := by
    intro v _
    have hcont : Continuous fun θ : ℝ => c ℓ a v * torusChar ((v : ℝ) * θ) :=
      continuous_const.mul
        (Prop42.continuous_torusChar.comp (continuous_const.mul continuous_id))
    refine Measure.integrableOn_of_bounded (M := ‖c ℓ a v‖) (by simp [Real.volume_Ioo])
      hcont.measurable.aestronglyMeasurable ?_
    filter_upwards with θ
    rw [norm_mul, Prop42.norm_torusChar, mul_one]
  simp only [hexp]
  rw [integral_finset_sum _ hint]
  have h0mem : (0 : ℤ) ∈ modeBox D L := by
    rw [modeBox, Finset.mem_Icc]
    exact ⟨neg_nonpos.2 (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  refine (Finset.sum_eq_single (0 : ℤ) ?_ ?_).trans ?_
  · intro v _ hv
    rw [integral_const_mul, integral_torusChar_mode, if_neg hv, mul_zero]
  · intro h
    exact absurd h0mem h
  · rw [integral_const_mul, integral_torusChar_mode, if_pos rfl, mul_one]

/-- **The right-hand side of (27) is the Gauss mean of the digit
observable.** -/
theorem stationaryMean_eq (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) :
    stationaryMean (F ℓ) = ∫ x, digitObs c ℓ x ∂Erdos1002.gaussMeasure := by
  unfold stationaryMean digitObs
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact integral_F_eq_coeff r D L F c hc ℓ hℓ (digit x 0)

/-- **The zero mode is a multi-block product of digit observables.** -/
theorem modeTerm_zero_eq (n r : ℕ) (j : ℕ → ℕ) (c : ℕ → ℕ → ℤ → ℂ) :
    modeTerm n r j c 0
      = ∫ α in Ioo (0 : ℝ) 1, ∏ ℓ : Fin r, digitObs c ℓ (gaussIter α (j ℓ)) := by
  unfold modeTerm digitObs
  refine setIntegral_congr_fun measurableSet_Ioo (fun α _ => ?_)
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
    torusChar_zero, mul_one]
  exact Finset.prod_congr rfl (fun ℓ _ => by rw [digit_gaussIter])

/-- **The zero-mode defect of (30) is exactly the mixing defect of (17)**
for the digit observables `g_ℓ(x) = c_ℓ(a_1(x), 0)`, at the times `j_ℓ`.

This is the reduction that removes the Fourier bookkeeping from the
obstruction list of `ErrorShape.zero_mode_factorization`: what remains
between this and `ErrorShape.good_tuple_multiblock_mixing` (which *does*
apply Lemma 3.2 at the good tuple's gap structure) is only

* the outer measure: `dα` on the left of (27) versus `dν` in (17), a
  `ρ^{200H}` change by Gauss-Kuzmin, since `j_1 ≥ 200H`;
* real versus complex observables (a factor `2^r` in the constant);
* the `BV(0,1)` bound on `g_ℓ`, a step function with at most `L^D` jumps.

The sup bound `‖g_ℓ‖_∞ ≤ L^D` is `norm_digitObs_le` below; the variation
bound is the piece Mathlib's `eVariationOn` API does not yet support. -/
theorem zero_mode_defect_eq (n r : ℕ) (D : ℝ) (j : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D (Lnorm n) F c) :
    modeTerm n r j c 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)
      = (∫ α in Ioo (0 : ℝ) 1, ∏ ℓ : Fin r, digitObs c ℓ (gaussIter α (j ℓ)))
        - ∏ ℓ : Fin r, ∫ x, digitObs c ℓ x ∂Erdos1002.gaussMeasure := by
  rw [modeTerm_zero_eq, ← Fin.prod_univ_eq_prod_range (fun ℓ => stationaryMean (F ℓ)) r]
  congr 1
  exact Finset.prod_congr rfl
    (fun ℓ _ => stationaryMean_eq r D (Lnorm n) F c hc (ℓ : ℕ) ℓ.isLt)

/-- The sup bound on the zero-mode digit observable: `‖g_ℓ‖_∞ ≤ L^D`, the
`K` that Kwon's (17) charges `K^s` for. -/
theorem norm_digitObs_le (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r) (x : ℝ) :
    ‖digitObs c ℓ x‖ ≤ L ^ D :=
  coeff_norm_le r D L F c hc ℓ hℓ (digit x 0) 0

end

end Prop4Final

/-! ## 7. Proposition 4.1, in `Kwon1002`'s own namespace

The statement below is reproduced token-identically from the canonical
target `Kwon1002.prop_4_1_marked_factorization` (`Kwon1002/Section4.lean`
lines 137-144), with only the theorem *name* primed; placing it in
`namespace Kwon1002` makes `GoodTuple`, `IsInPD`, `digit`, `theta`,
`stationaryMean` and `Lnorm` resolve exactly as they do there, so the
reproduction is literal rather than up to qualification.

Proved from `Prop4Final.prop_4_1_error_shape''` and the fully proved
`O_A(L^{-A})` reduction `Prop41.eventually_rpow_mul_deltaScale_le`. -/

theorem prop_4_1_marked_factorization'' (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨B, C, c, ρ, hC, hc, hρ0, hρ1, hbd⟩ := Prop4Final.prop_4_1_error_shape'' r D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbd, Prop41.eventually_rpow_mul_deltaScale_le A B c ρ hc hρ0 hρ1]
    with n hn harith j hj F hF
  calc ‖(∫ α in Ioo (0 : ℝ) 1,
            ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C * (Lnorm n) ^ B * Prop41.deltaScale c ρ n := hn j hj F hF
    _ = C * ((Lnorm n) ^ B * Prop41.deltaScale c ρ n) := by ring
    _ ≤ C * (Lnorm n) ^ (-A) := mul_le_mul_of_nonneg_left harith hC.le

end Kwon1002
