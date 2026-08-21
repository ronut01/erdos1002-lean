import Kwon1002.Prop41Unconditional
import Kwon1002.Prop4Final

/-!
# The one-level joint law of digit and phase

Three residuals of §5 name "equidistribution of `θ_j`" as their missing
ingredient: display (35) (`Kwon1002.deterministic_oneLevel_intensity`), the
band-mass input of `Kwon1002.CovarianceChain.farWindow_sum_small`, and the
level-`j` Lebesgue-to-stationary bridge that the closing note of
`Kwon1002/DigitLocalLaw.lean` records as missing.  All three want the same
thing: the joint law of `(a_{j+1}, θ_j)` under Lebesgue measure on `(0,1)`, at
a **single** level `j` of the deterministic bulk.

That is Proposition 4.1 read at `r = 1`, and Proposition 4.1 is now
unconditional (`Kwon1002.prop_4_1_marked_factorization_unconditional`).  This
module extracts the `r = 1` case once, in the three shapes the consumers want,
so that none of them has to re-derive it.

## What is here

* `oneLevel_joint_law` — Proposition 4.1 at `r = 1`: for every level `j` of the
  deterministic bulk `J_n` of display (19) and every symbol `G ∈ P_D(L)`,

    `∫₀¹ G(a_{j+1}(α), θ_j(α)) dα = ∫∫ G(a₁(x), θ) dθ dν(x) + O_{D,A}(L^{-A})`,

  with one constant, uniform in `j` and in `G`.

* `isInPD_separable` — **the first exhibited member of the symbol class
  `P_D(L)` of display (24) anywhere in this development.**  A separable symbol
  `G(a,θ) = g(a) e(v₀θ)` with `g` supported on the digit cut `a ≤ L^D`, with
  `|v₀| ≤ L^D` and with `∑_a |g(a)| ≤ L^D` lies in the class.  Before this
  lemma the class was only ever consumed, never populated, so nothing in the
  tree checked that display (24) admits the symbols §5 needs.

* `stationaryMean_separable` — the stationary mean of a separable symbol
  factorizes as `(∫ g(a₁) dν) · 1{v₀ = 0}`, because Haar kills every nonzero
  mode.

* `oneLevel_phase_equidistribution` — the `v₀ ≠ 0` case, which is
  *equidistribution of `θ_j`* in quantitative form: the level-`j` phase is
  equidistributed on the torus at rate `O_{D,A}(L^{-A})`, **uniformly over the
  digit weight `g`** and over the level `j ∈ J_n`.  The uniformity in `g` is
  the point: it is what lets a consumer integrate the phase against a digit
  observable rather than only against `1`.

* `oneLevel_digit_law` — the `v₀ = 0` case: the level-`j` digit law under
  Lebesgue agrees with the **stationary Gauss** digit law up to
  `O_{D,A}(L^{-A})`.  This is exactly the bridge that the closing note of
  `Kwon1002/DigitLocalLaw.lean` records as missing ("the bridge from the
  level-`j` Lebesgue law to the stationary law, which is §4's business and is
  gated by Proposition 4.1's equidistribution of `θ_j`").  With it, the exact
  Gauss digit law `DigitLocalLaw.gaussMeasure_real_digit_zero` transfers to the
  level-`j` Lebesgue law.

## The digit cut is not free, and neither is the coefficient budget

`isInPD_separable` needs three things, and each is a real constraint that a
consumer must meet, not bookkeeping:

1. `g` vanishes off a finite set `s` (the digit cut `A_L = L^D`);
2. every `a ∈ s` satisfies `a ≤ L^D` (the same cut, in the form display (24)
   imposes on the coefficients);
3. `∑_{a ∈ s} |g(a)| ≤ L^D` (display (24)'s `ℓ¹` budget).

Constraint 3 is the binding one and is worth recording, because it is easy to
read display (24) as if it were free.  A digit weight that is `O(1)` on a cut
of size `L^D` has `ℓ¹` norm of order `L^D` already, so a consumer that also
wants a nonconstant *phase* factor — a Jackson polynomial of degree `L^{D}`,
whose coefficients carry a further `log`-sized `ℓ¹` norm — **overshoots the
budget of `P_D(L)` and must be placed in `P_{D'}(L)` for some `D' > D`**.
Proposition 4.1 holds for every `D > 0`, so this costs nothing; but the `D` of
the symbol class and the `D` of the digit cut are then *different constants*,
and a statement that ties them together is mis-stated.  Recorded here rather
than discovered downstream.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

namespace OneLevelLaw

noncomputable section

/-! ## Part 1, Proposition 4.1 at `r = 1` -/

/-- The one-level tuple: the level `j` at position `0`, normalized to `0`
above, which is the convention `Kwon1002.IsAdmissibleTuple` fixes. -/
def oneTuple (j : ℕ) : ℕ → ℕ := fun ℓ => if ℓ = 0 then j else 0

@[simp] lemma oneTuple_zero (j : ℕ) : oneTuple j 0 = j := by simp [oneTuple]

/-- At `r = 1` every level of the deterministic bulk is a good tuple: the gap
condition (25) and the resonance condition (26) are both vacuous, since they
constrain pairs of entries and there is only one entry. -/
lemma goodTuple_oneTuple {n j : ℕ} (hj : j ∈ bulkJ n) : GoodTuple n 1 (oneTuple j) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro ℓ hℓ
    have hne : ℓ ≠ 0 := by omega
    simp [oneTuple, hne]
  · intro ℓ ℓ' hlt hℓ'
    exact absurd hℓ' (by omega)
  · intro ℓ hℓ
    have h0 : ℓ = 0 := by omega
    subst h0
    simpa using hj
  · intro ℓ hℓ
    exact absurd hℓ (by omega)
  · intro i ℓ hi hℓ
    exact absurd hℓ (by omega)

/-- **The one-level joint law of digit and phase**, Proposition 4.1 at `r = 1`.

For every level `j` of the deterministic bulk `J_n` of display (19) and every
symbol `G` of the class `P_D(L)` of display (24),

`∫₀¹ G(a_{j+1}(α), θ_j(α)) dα = ∫∫ G(a₁(x), θ) dθ dν(x) + O_{D,A}(L^{-A})`,

with a single constant, uniform in `j` and in `G`.  Unconditional: the only
input is `Kwon1002.prop_4_1_marked_factorization_unconditional`. -/
theorem oneLevel_joint_law (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ bulkJ n, ∀ G : ℕ → ℝ → ℂ, IsInPD D (Lnorm n) G →
        ‖(∫ α in Ioo (0 : ℝ) 1, G (digit α j) (theta α n j)) - stationaryMean G‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨C, hC, hev⟩ := prop_4_1_marked_factorization_unconditional 1 D A hD hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn j hj G hG
  have h := hn (oneTuple j) (goodTuple_oneTuple hj) (fun _ => G) (fun _ _ => hG)
  simpa using h

/-! ## Part 2, the symbol class of display (24) is inhabited

Nothing in `Kwon1002/` had ever exhibited a member of `IsInPD`.  The class is
consumed by Proposition 4.1 and by every §5 residual below it, so a mis-stated
class would have gone unnoticed; this part checks it by construction. -/

/-- The coefficient family of the separable symbol `g(a) e(v₀θ)`: a single
nonzero mode, with the digit profile `g` as its amplitude. -/
def sepCoeff (g : ℕ → ℂ) (v₀ : ℤ) : ℕ → ℤ → ℂ :=
  fun a v => if v = v₀ then g a else 0

/-- **The symbol class of display (24) is inhabited.**  A separable symbol
`G(a,θ) = g(a) e(v₀θ)` lies in `P_D(L)` as soon as `g` is supported on a finite
digit set `s` lying below the cut `L^D`, the mode `v₀` lies below the same cut,
and the `ℓ¹` budget `∑_{a ∈ s} |g(a)| ≤ L^D` of display (24) is met. -/
theorem isInPD_separable {D L : ℝ} {g : ℕ → ℂ} {v₀ : ℤ} {s : Finset ℕ}
    (hsupp : ∀ a ∉ s, g a = 0)
    (hcut : ∀ a ∈ s, (a : ℝ) ≤ L ^ D)
    (hv : |(v₀ : ℝ)| ≤ L ^ D)
    (hsum : (∑ a ∈ s, ‖g a‖) ≤ L ^ D) :
    IsInPD D L (fun a θ => g a * torusChar ((v₀ : ℝ) * θ)) := by
  classical
  refine ⟨sepCoeff g v₀, ?_, ?_, ?_, ?_⟩
  · intro a v ha
    have hns : a ∉ s := fun h => absurd (hcut a h) (not_le.mpr ha)
    simp [sepCoeff, hsupp a hns]
  · intro a v hv'
    have hne : v ≠ v₀ := by
      rintro rfl
      exact absurd hv (not_le.mpr hv')
    simp [sepCoeff, hne]
  · have hzero : ∀ p : ℕ × ℤ, p ∉ s ×ˢ ({v₀} : Finset ℤ) →
        ‖sepCoeff g v₀ p.1 p.2‖ = 0 := by
      rintro ⟨a, v⟩ hp
      simp only [Finset.mem_product, Finset.mem_singleton, not_and_or] at hp
      rcases hp with hp | hp
      · simp [sepCoeff, hsupp a hp]
      · simp [sepCoeff, hp]
    rw [tsum_eq_sum hzero, Finset.sum_product]
    simpa [sepCoeff] using hsum
  · intro a θ
    rw [tsum_eq_single v₀ (fun v hv' => by simp [sepCoeff, hv'])]
    simp [sepCoeff]

/-! ## Part 3, the stationary mean of a separable symbol -/

/-- The stationary mean of `g(a) e(v₀θ)` factorizes: Haar measure kills every
nonzero mode, so the mean is `(∫ g(a₁) dν)` when `v₀ = 0` and `0` otherwise. -/
theorem stationaryMean_separable (g : ℕ → ℂ) (v₀ : ℤ) :
    stationaryMean (fun a θ => g a * torusChar ((v₀ : ℝ) * θ))
      = (∫ x, g (digit x 0) ∂Erdos1002.gaussMeasure) * (if v₀ = 0 then 1 else 0) := by
  have hinner : ∀ x : ℝ,
      (∫ θ in Ioo (0 : ℝ) 1, g (digit x 0) * torusChar ((v₀ : ℝ) * θ))
        = g (digit x 0) * (if v₀ = 0 then 1 else 0) := by
    intro x
    rw [integral_const_mul, Prop4Final.integral_torusChar_mode]
  simp only [stationaryMean, hinner]
  exact integral_mul_const _ _

/-! ## Part 4, the two shapes the §5 residuals ask for -/

/-- **Equidistribution of the phase `θ_j`, quantitative and uniform in the
digit weight.**

For every level `j` of the deterministic bulk and every nonzero mode `v₀` below
the cut `L^D`,

`|∫₀¹ g(a_{j+1}(α)) e(v₀ θ_j(α)) dα| ≤ C L^{-A}`,

uniformly over all digit weights `g` supported below the cut with `ℓ¹` norm at
most `L^D`.  This is the ingredient named — and left unproved — by display
(35), by the band-mass input of `CovarianceChain.farWindow_sum_small`, and by
the closing note of `Kwon1002/DigitLocalLaw.lean`. -/
theorem oneLevel_phase_equidistribution (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ bulkJ n, ∀ v₀ : ℤ, v₀ ≠ 0 → |(v₀ : ℝ)| ≤ (Lnorm n) ^ D →
      ∀ (g : ℕ → ℂ) (s : Finset ℕ), (∀ a ∉ s, g a = 0) →
        (∀ a ∈ s, (a : ℝ) ≤ (Lnorm n) ^ D) → (∑ a ∈ s, ‖g a‖) ≤ (Lnorm n) ^ D →
        ‖∫ α in Ioo (0 : ℝ) 1,
            g (digit α j) * torusChar ((v₀ : ℝ) * theta α n j)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨C, hC, hev⟩ := oneLevel_joint_law D A hD hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn j hj v₀ hv₀ hvle g s hsupp hcut hsum
  have hmem := isInPD_separable (D := D) (L := Lnorm n) hsupp hcut hvle hsum
  have h := hn j hj _ hmem
  rwa [stationaryMean_separable g v₀, if_neg hv₀, mul_zero, sub_zero] at h

/-- **The level-`j` digit law is the stationary Gauss digit law**, to
`O_{D,A}(L^{-A})`, uniformly over digit observables supported below the cut.

This is the bridge the closing note of `Kwon1002/DigitLocalLaw.lean` records as
missing.  Combined with `DigitLocalLaw.gaussMeasure_real_digit_zero` (the exact
value `γ{a₁ = k} = log(1 + 1/(k(k+2)))/log 2`) it gives the level-`j` Lebesgue
digit law with the exact `a^{-2}` decay that finding F7 shows the `O(1/A)`-shaped
tails of `Kwon1002/DigitTail.lean` cannot supply. -/
theorem oneLevel_digit_law (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ bulkJ n, ∀ (g : ℕ → ℂ) (s : Finset ℕ), (∀ a ∉ s, g a = 0) →
        (∀ a ∈ s, (a : ℝ) ≤ (Lnorm n) ^ D) → (∑ a ∈ s, ‖g a‖) ≤ (Lnorm n) ^ D →
        ‖(∫ α in Ioo (0 : ℝ) 1, g (digit α j))
            - ∫ x, g (digit x 0) ∂Erdos1002.gaussMeasure‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨C, hC, hev⟩ := oneLevel_joint_law D A hD hA
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, hLtend.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hL1 j hj g s hsupp hcut hsum
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hv0 : |((0 : ℤ) : ℝ)| ≤ (Lnorm n) ^ D := by
    simpa using (Real.rpow_pos_of_pos hL0 D).le
  have hmem := isInPD_separable (D := D) (L := Lnorm n) (v₀ := 0) hsupp hcut hv0 hsum
  have h := hn j hj _ hmem
  rw [stationaryMean_separable g 0, if_pos rfl, mul_one] at h
  have hint : ∀ α : ℝ, g (digit α j) * torusChar (((0 : ℤ) : ℝ) * theta α n j)
      = g (digit α j) := by
    intro α
    have hz : ((0 : ℤ) : ℝ) * theta α n j = 0 := by simp
    rw [hz, Prop4Final.torusChar_zero, mul_one]
  simpa only [hint] using h

end

end OneLevelLaw

end Kwon1002
