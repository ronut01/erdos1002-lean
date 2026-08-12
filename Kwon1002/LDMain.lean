import Kwon1002.LDDeviation
import Kwon1002.LDDisplay20
import Kwon1002.RetainedCut
import Kwon1002.Lemma63

/-!
# Large deviations for continuants: display (16), and display (20) proved

Assembly of the stages (spine, centering, excess, covariance, ψ-decoupling,
blocks) into:

* `continuant_large_deviation` — the self-contained form of display (16):
  `P(|log q_r − λr| > v) ≤ C exp(−c·min(v²/r, v/(1+log(r+1))²))` under
  Lebesgue measure on `(0,1)`, for all `r ≥ 1`, `v > 0`.  Relative to the
  manuscript's `min(v²/r, v)` the linear branch carries a `log²` loss,
  harmless to every consumer in this development: display (20) sits at
  `v = δH ≍ L^{3/4}`, `r ≤ 2m_n ≍ L`, where the quadratic branch gives
  `≍ δ²√L` and the clamped branch gives `≫ √L`.  The verbatim linear
  branch is a spectral-gap fact not claimed here.

* `display20_of_pos` / `display20_holds` — **proved instances of
  `P42Cases.Display20`**, closing the gap recorded in `P42Cases` §4: at any
  window constant `δ > 0` there are `C, c > 0` with `Display20 C δ c`.

* `nonzero_mode_cut_unconditional` — the retained-cylinder cut of
  `RetainedCut.nonzero_mode_cut_of_display20`, now unconditional.

## Parameter ledger (fixed inside the proof)

Given `r ≥ 1`: cap `u := log C_E + 4 log(r+1)` (`C_E` the excess-tail
threshold constant), window `W := ⌈K(log(r+1)+1)⌉` with
`K := 200(1 + log C_E)`, block length `2W`, gap `W`, Chernoff parameter
`σ := min(z/(4C₁r), 1/(8W(u+3)))`.  Mixing smallness `24ρ₀^W r ≤ 1` holds
because `W·log(540/527) ≥ 4(log(r+1)+1) ≥ log(24r)`; windowing smallness
`r·e^{u+λ}·2^{1−W} ≤ 1` because `W log 2` dominates `u + log(2r) + λ`.
-/

open Set MeasureTheory Filter

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-- **Display (20) of the manuscript, proved** (the predicate
`P42Cases.Display20`, recorded in `P42Cases` §4 as the sole missing analytic
input of cases 2–3 of Proposition 4.2): for every window constant `δ > 0`
there are `C, c > 0` such that eventually every continuant up to index
`2 m_n` obeys the two-sided Lévy window `e^{λj ± δH}` outside a set of
Lebesgue measure `C e^{−c√L}`. -/
theorem display20_of_pos (δ : ℝ) (hδ : 0 < δ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ P42Cases.Display20 C δ c :=
  display20_of_deviation continuant_large_deviation δ hδ

/-- **Display (20), existential form.** -/
theorem display20_holds :
    ∃ C δ c : ℝ, 0 < C ∧ 0 < δ ∧ 0 < c ∧ P42Cases.Display20 C δ c := by
  obtain ⟨C, c, hC, hc, h⟩ := display20_of_pos 1 one_pos
  exact ⟨C, 1, c, hC, one_pos, hc, h⟩

/-- **The retained-cylinder cut, unconditional**: display (20) being proved,
`RetainedCut.nonzero_mode_cut_of_display20` now yields, for some
`C₀, δ, c₀ > 0` and eventually in `n`, at every depth `d ≤ 2m_n` a retained
word family with the Lévy window on every retained cylinder, discarded mass
`≤ C₀e^{−c₀√L}`, and the step-1 cut for every symbol family and nonzero
mode. -/
theorem nonzero_mode_cut_unconditional :
    ∃ C₀ δ c₀ : ℝ, 0 < C₀ ∧ 0 < δ ∧ 0 < c₀ ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ 2 * mIndex n →
        ∃ W : Finset (List ℕ),
          (∀ w ∈ W, w.length = d ∧ ∀ a ∈ w, 0 < a) ∧
          (∀ w ∈ W, ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α →
            Real.exp (lyapunov * (d : ℝ) - δ * Hscale n) ≤ (denom α d : ℝ) ∧
              (denom α d : ℝ) ≤ Real.exp (lyapunov * (d : ℝ) + δ * Hscale n)) ∧
          (volume (Ioo (0 : ℝ) 1 \
              ⋃ w ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
            ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) ∧
          ∀ (r : ℕ) (D : ℝ) (j : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ),
            ErrorShape.RepresentsPD r D (Lnorm n) F c →
            ∀ (v : Fin r → ℤ) (s : ℕ), s < r → (∀ ℓ : Fin r, s < (ℓ : ℕ) → v ℓ = 0) →
              ‖ErrorShape.modeTerm n r j c v
                  - ∑ w ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
                      (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
                        torusChar ((n : ℝ) *
                          ((Prop41Canon.freqQ α j (ZeroMode.modeExt r v) s : ℤ) : ℝ) * α)‖
                ≤ ((Lnorm n) ^ D) ^ r
                    * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
  obtain ⟨C₀, δ, c₀, hC₀, hδ, hc₀, h20⟩ := display20_holds
  exact ⟨C₀, δ, c₀, hC₀, hδ, hc₀,
    RetainedCut.nonzero_mode_cut_of_display20 C₀ δ c₀ h20⟩

/-- **Lemma 6.3, good-cylinder selection, unconditional**: display (20)
being proved, `Lemma63.lemma_6_3_good_cylinder_selection_corrected` holds
without its `Display20` hypothesis, at every anti-concentration constant
`κ > 0` and every window constant `δ > 0`. -/
theorem good_cylinder_selection_unconditional (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ C₀ c₀ C c : ℝ, 0 < C₀ ∧ 0 < c₀ ∧ 0 < C ∧ 0 < c ∧
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
        ∀ A B : ℤ, (A, B) ≠ (0, 0) →
          ∃ E : Set ℝ, MeasurableSet E ∧
            (volume.restrict (Ioo (0 : ℝ) 1)).real E
                ≤ C * Real.exp (-c * Hscale n)
                  + C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) ∧
            ∀ α ∈ Ioo (0 : ℝ) 1 \ E,
              Real.exp (lyapunov * j - δ * Hscale n) ≤ (denom α j : ℝ) ∧
              Real.exp (-κ * Hscale n) * (denom α j : ℝ) ≤ |(Qfreq α j B A : ℝ)| := by
  obtain ⟨C₀, c₀, hC₀, hc₀, h20⟩ := display20_of_pos δ hδ
  obtain ⟨C, c, hC, hc, hev⟩ :=
    Lemma63.lemma_6_3_good_cylinder_selection_corrected κ δ hκ hδ C₀ c₀ hC₀ h20
  exact ⟨C₀, c₀, C, c, hC₀, hc₀, hC, hc, hev⟩

end

end LargeDeviation

end Kwon1002
