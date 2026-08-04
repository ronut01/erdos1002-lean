import Kwon1002.Prop42

/-!
# MonomialCore, the monomial core of Proposition 4.2

Target: `Kwon1002.Prop42.two_block_monomial_core`, reproduced here
token-identically as `two_block_monomial_core'` and proved from an honest
three-case decomposition following the manuscript's proof of Proposition 4.2
(lines ≈ 405-470 of the full text).

## Proved outright here

* `monoStationary_eq_zero`, **"the stationary product is zero because the
  (later / earlier) Haar character is nontrivial"**, the step the manuscript
  invokes at the end of both nonzero-mode cases.  `μ̂₀` is a product of a
  density measure in the natural-extension coordinates `(x,y)` and Haar
  measure on `T²`; a monomial factors accordingly, and the `T²` factor is
  `∫₀¹∫₀¹ e(rθ' + sθ) = 0` whenever `(r,s) ≠ (0,0)`.
* `card_nearDiag_le`, `card_nearRes_le`, the two exceptional-pair counts
  ("there are `O(LH)` overlapping or `H`-near pairs"; "declare `|k − t₀| ≤
  100H` exceptional; this gives `O(H)` values of `k` per `j`, hence `O(LH)`
  pairs in total").  Both are `≤ C · L · H` with an explicit constant.
* `err_le`, monotonicity of the right-hand side of (34) in `(C, c, ρ)`,
  which is what lets three separately-quantified case constants be merged.
* `two_block_monomial_core'`, the assembly.

## Assumed (three named sorried lemmas, one per case of Kwon's proof)

* `zeroMode_gauss_mixing` (both torus modes vanish), needs Lemma 3.2
  (two-sided Gauss mixing) *for digit-cylinder indicators*.  Obstruction:
  `Kwon1002.Transfer.lemma_3_2` is proved only for **Lipschitz** observables
  (Wang's Lasota-Yorke contraction is on the Lipschitz seminorm), and the
  finding recorded at `TransferMixing.lean:644-663` states explicitly that
  this does *not* cover §4's use on digit indicators, which are BV but not
  Lipschitz.  `lemma_3_2` also still rests on the sorried
  `cylinder_transfer_eq_kwonDensity`.
* `laterMode_phase_bound` (later torus mode nonzero) and
  `earlierMode_phase_bound` (later mode zero, earlier mode nonzero), both
  are the oscillatory bound of **Lemma 3.4, display (22)**, applied on the
  retained deep descendants.  Obstruction: display (22) is *not present in
  this development at all* (only its converse `descendant_phase_small`
  is proved, in `CylinderPhase.lean`); the anti-concentration input
  `shrinking_anti_concentration` and the frequency-domination step
  `Prop42.later_frequency_dominates` / `Prop42.retained_descendant_exponent`
  *are* proved and feed exactly into these two statements.

No other sorried result is consumed.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace MonomialCore

noncomputable section

/-! ## 1. A nontrivial Haar character has stationary mean zero -/

lemma torusChar_add (a b : ℝ) : torusChar (a + b) = torusChar a * torusChar b := by
  unfold torusChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `∫₀¹ e(rθ) dθ = 0` for a nonzero integer mode `r`. -/
lemma integral_torusChar_eq_zero {r : ℤ} (hr : r ≠ 0) :
    (∫ θ in Ioo (0 : ℝ) 1, torusChar ((r : ℝ) * θ)) = 0 := by
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    have h1 : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h2 : (r : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hr
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) Complex.I_ne_zero) h2
  have hpt : ∀ θ : ℝ, torusChar ((r : ℝ) * θ) = Complex.exp (c * θ) := by
    intro θ
    unfold torusChar
    congr 1
    rw [hc]
    push_cast
    ring
  have hstep : (∫ θ in Ioo (0 : ℝ) 1, torusChar ((r : ℝ) * θ))
      = ∫ θ in (0 : ℝ)..1, Complex.exp (c * θ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hpt θ)
  rw [hstep, integral_exp_mul_complex hcne]
  have h1 : c * (1 : ℝ) = (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hc]; push_cast; ring
  have h0 : c * (0 : ℝ) = 0 := by simp
  rw [h1, h0, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero, sub_self, zero_div]

/-- The Haar factor of a monomial has mean zero when its mode is nontrivial. -/
lemma integral_torusChar_pair_eq_zero {r s : ℤ} (h : (r, s) ≠ (0, 0)) :
    (∫ q in (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
        torusChar ((r : ℝ) * q.1 + (s : ℝ) * q.2)) = 0 := by
  have hbox : (volume : Measure (ℝ × ℝ)).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
      = ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
          ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hsplit : ∀ q : ℝ × ℝ, torusChar ((r : ℝ) * q.1 + (s : ℝ) * q.2)
      = torusChar ((r : ℝ) * q.1) * torusChar ((s : ℝ) * q.2) := fun q => torusChar_add _ _
  rw [hbox]
  simp only [hsplit]
  rw [MeasureTheory.integral_prod_mul
    (f := fun x : ℝ => torusChar ((r : ℝ) * x))
    (g := fun y : ℝ => torusChar ((s : ℝ) * y))]
  rcases (by
    by_contra hcon
    push_neg at hcon
    exact h (by rw [hcon.1, hcon.2]) : r ≠ 0 ∨ s ≠ 0) with hr | hs
  · rw [integral_torusChar_eq_zero hr, zero_mul]
  · rw [integral_torusChar_eq_zero hs, mul_zero]

/-- The natural-extension density, as a function of the `(x,y)` coordinates. -/
def gdens (p : ℝ × ℝ) : ℝ := 1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2)

lemma gdens_nonneg (p : ℝ × ℝ) : 0 ≤ gdens p := by
  have hl : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact div_nonneg zero_le_one (mul_nonneg hl (sq_nonneg _))

lemma measurable_gdens_toNNReal :
    Measurable fun z : (ℝ × ℝ) × ℝ × ℝ => (gdens z.1).toNNReal := by
  refine Measurable.real_toNNReal ?_
  unfold gdens
  exact measurable_const.div
    ((measurable_const.mul (((measurable_fst.fst.mul measurable_fst.snd).const_add 1).pow_const 2)))

/-- **"The stationary product is zero because the Haar character is
nontrivial."**  The step Kwon uses to close both nonzero-mode cases of the
proof of Proposition 4.2. -/
theorem monoStationary_eq_zero (R : ℕ) (w : Fin (2 * R) → ℕ) {r s : ℤ}
    (h : (r, s) ≠ (0, 0)) : Prop42.monoStationary R w r s = 0 := by
  classical
  set Bx : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 with hBx
  have hden : hatMu0 = (volume.restrict (Bx ×ˢ Bx)).withDensity
      (fun z => ((gdens z.1).toNNReal : ℝ≥0∞)) := rfl
  have hstep1 : Prop42.monoStationary R w r s
      = ∫ z in (Bx ×ˢ Bx), ((gdens z.1).toNNReal : ℝ≥0) • Prop42.monoEval R w r s z := by
    rw [Prop42.monoStationary, hden,
      integral_withDensity_eq_integral_smul measurable_gdens_toNNReal]
  have hsmul : ∀ z : (ℝ × ℝ) × ℝ × ℝ,
      ((gdens z.1).toNNReal : ℝ≥0) • Prop42.monoEval R w r s z
        = ((gdens z.1 * (if natExtWord R z.1 = w then (1 : ℝ) else 0) : ℝ) : ℂ)
            * torusChar ((r : ℝ) * z.2.1 + (s : ℝ) * z.2.2) := by
    intro z
    rw [NNReal.smul_def, Real.coe_toNNReal _ (gdens_nonneg z.1), Complex.real_smul,
      Prop42.monoEval]
    push_cast
    by_cases hw : natExtWord R z.1 = w <;> simp [hw]
  rw [hstep1]
  simp only [hsmul]
  have hbox : (volume : Measure ((ℝ × ℝ) × ℝ × ℝ)).restrict (Bx ×ˢ Bx)
      = ((volume : Measure (ℝ × ℝ)).restrict Bx).prod
          ((volume : Measure (ℝ × ℝ)).restrict Bx) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [hbox, MeasureTheory.integral_prod_mul
    (f := fun p : ℝ × ℝ => ((gdens p * (if natExtWord R p = w then (1 : ℝ) else 0) : ℝ) : ℂ))
    (g := fun q : ℝ × ℝ => torusChar ((r : ℝ) * q.1 + (s : ℝ) * q.2)),
    hBx, integral_torusChar_pair_eq_zero h, mul_zero]

/-! ## 2. The two exceptional-pair counts -/

/-- Pairs whose blocks are within `T` of each other ("overlapping or
`H`-near pairs"). -/
def nearDiag (n : ℕ) (T : ℝ) : Finset (ℕ × ℕ) :=
  (bulkPairs n).filter (fun p => (p.2 : ℝ) - (p.1 : ℝ) ≤ T)

/-- Pairs whose later block is within `T` of the resonance time
`t₀ = (m_n + j)/2` of the earlier one. -/
def nearRes (n : ℕ) (T : ℝ) : Finset (ℕ × ℕ) :=
  (bulkPairs n).filter (fun p => |(p.2 : ℝ) - ((mIndex n : ℝ) + (p.1 : ℝ)) / 2| ≤ T)

lemma card_bulkJ_le (n : ℕ) (hL1 : 1 ≤ Lnorm n) :
    ((bulkJ n).card : ℝ) ≤ (1 / lyapunov + 1) * Lnorm n := by
  have hlam : (0 : ℝ) < lyapunov := Prop42.lyapunov_pos
  have hsub2 : bulkJ n ⊆ Finset.range (mIndex n + 1) := Finset.filter_subset _ _
  have h1 : ((bulkJ n).card : ℝ) ≤ (mIndex n : ℝ) + 1 := by
    have h := Finset.card_le_card hsub2
    rw [Finset.card_range] at h
    have h' : ((bulkJ n).card : ℝ) ≤ ((mIndex n + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have h2 : (mIndex n : ℝ) ≤ Lnorm n / lyapunov :=
    Nat.floor_le (div_nonneg (by linarith) hlam.le)
  have h3 : Lnorm n / lyapunov = (1 / lyapunov) * Lnorm n := by ring
  rw [h3] at h2
  nlinarith

lemma mem_bulkPairs_fst {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ bulkPairs n) : p.1 ∈ bulkJ n := by
  rw [bulkPairs, Finset.mem_filter, Finset.mem_product] at hp
  exact hp.1.1

lemma mem_bulkPairs_lt {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ bulkPairs n) : p.1 < p.2 := by
  rw [bulkPairs, Finset.mem_filter] at hp
  exact hp.2

/-- **"There are `O(LH)` overlapping or `H`-near pairs."** -/
lemma card_nearDiag_le (n : ℕ) (T : ℝ) :
    (nearDiag n T).card ≤ (⌊T⌋₊ + 1) * (bulkJ n).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst) ?_ _ ?_
  · intro p hp
    rw [nearDiag, Finset.mem_filter] at hp
    exact mem_bulkPairs_fst hp.1
  · intro a _
    have hmaps : ∀ p ∈ (nearDiag n T).filter (fun p => Prod.fst p = a),
        p.2 ∈ Finset.Icc (a + 1) (a + ⌊T⌋₊ + 1) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [nearDiag, Finset.mem_filter] at hp1
      obtain ⟨hbp, hT⟩ := hp1
      have hlt : p.1 < p.2 := mem_bulkPairs_lt hbp
      have hp2' : p.1 = a := hp2
      refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
      have hTf : T ≤ (⌊T⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one T).le
      have ha : ((p.1 : ℕ) : ℝ) = ((a : ℕ) : ℝ) := by exact_mod_cast hp2'
      have hcast : ((p.2 : ℕ) : ℝ) ≤ ((a + ⌊T⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    have hinj : Set.InjOn Prod.snd
        (((nearDiag n T).filter (fun p => Prod.fst p = a) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro p hp q hq hpq
      rw [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by rw [hp.2, hq.2]
      exact Prod.ext h1 hpq
    calc ((nearDiag n T).filter (fun p => Prod.fst p = a)).card
        ≤ (Finset.Icc (a + 1) (a + ⌊T⌋₊ + 1)).card :=
          Finset.card_le_card_of_injOn Prod.snd hmaps hinj
      _ = ⌊T⌋₊ + 1 := by rw [Nat.card_Icc]; omega

/-- **"`|k − t₀| ≤ 100H` is exceptional; this gives `O(H)` values of `k` per
`j`, hence `O(LH)` pairs in total."** -/
lemma card_nearRes_le (n : ℕ) (T : ℝ) :
    (nearRes n T).card ≤ (2 * ⌊T⌋₊ + 4) * (bulkJ n).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst) ?_ _ ?_
  · intro p hp
    rw [nearRes, Finset.mem_filter] at hp
    exact mem_bulkPairs_fst hp.1
  · intro a _
    set c : ℝ := ((mIndex n : ℝ) + (a : ℝ)) / 2 with hcdef
    have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
    have hmaps : ∀ p ∈ (nearRes n T).filter (fun p => Prod.fst p = a),
        p.2 + ⌊T⌋₊ + 1 ∈ Finset.Icc ⌊c⌋₊ (⌊c⌋₊ + 2 * ⌊T⌋₊ + 3) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [nearRes, Finset.mem_filter] at hp1
      obtain ⟨-, hT⟩ := hp1
      have hp2' : p.1 = a := hp2
      have ha : ((p.1 : ℕ) : ℝ) = ((a : ℕ) : ℝ) := by exact_mod_cast hp2'
      have hTeq : |(p.2 : ℝ) - c| ≤ T := by
        rw [hcdef, ← ha]
        exact hT
      have habs := abs_le.mp hTeq
      have hfc : ((⌊c⌋₊ : ℕ) : ℝ) ≤ c := Nat.floor_le hc0
      have hfc' : c < ((⌊c⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one c
      have hTf : T ≤ (⌊T⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one T).le
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · have hcast : ((⌊c⌋₊ : ℕ) : ℝ) ≤ ((p.2 + ⌊T⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast hcast
      · have hcast : ((p.2 + ⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ ((⌊c⌋₊ + 2 * ⌊T⌋₊ + 3 : ℕ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast hcast
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 + ⌊T⌋₊ + 1)
        (((nearRes n T).filter (fun p => Prod.fst p = a) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro p hp q hq hpq
      rw [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      simp only at hpq
      have h1 : p.1 = q.1 := by rw [hp.2, hq.2]
      have h2 : p.2 = q.2 := by omega
      exact Prod.ext h1 h2
    calc ((nearRes n T).filter (fun p => Prod.fst p = a)).card
        ≤ (Finset.Icc ⌊c⌋₊ (⌊c⌋₊ + 2 * ⌊T⌋₊ + 3)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = 2 * ⌊T⌋₊ + 4 := by rw [Nat.card_Icc]; omega

lemma one_le_Hscale {n : ℕ} (hL1 : 1 ≤ Lnorm n) : (1 : ℝ) ≤ Hscale n := by
  show (1 : ℝ) ≤ (Lnorm n) ^ (3 / 4 : ℝ)
  calc (1 : ℝ) = (1 : ℝ) ^ (3 / 4 : ℝ) := (Real.one_rpow _).symm
    _ ≤ (Lnorm n) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hL1 (by norm_num)

/-- The combined exceptional-pair count of the proof of 4.2 is `O(LH)`. -/
lemma exc_card_bound (n : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hL1 : 1 ≤ Lnorm n) :
    (((nearDiag n (b * Hscale n) ∪ nearRes n (100 * Hscale n)).card : ℕ) : ℝ)
      ≤ ((1 / lyapunov + 1) * (b + 205)) * Lnorm n * Hscale n := by
  have hH1 : (1 : ℝ) ≤ Hscale n := one_le_Hscale hL1
  have hH0 : (0 : ℝ) ≤ Hscale n := by linarith
  have hL0 : (0 : ℝ) ≤ Lnorm n := by linarith
  set A : ℝ := 1 / lyapunov + 1 with hAdef
  have hA0 : 0 < A := by
    have h := one_div_pos.2 Prop42.lyapunov_pos
    rw [hAdef]; linarith
  have hJ : ((bulkJ n).card : ℝ) ≤ A * Lnorm n := card_bulkJ_le n hL1
  have hJ0 : (0 : ℝ) ≤ ((bulkJ n).card : ℝ) := Nat.cast_nonneg _
  have hunion : (((nearDiag n (b * Hscale n) ∪ nearRes n (100 * Hscale n)).card : ℕ) : ℝ)
      ≤ ((nearDiag n (b * Hscale n)).card : ℝ) + ((nearRes n (100 * Hscale n)).card : ℝ) := by
    have h := Finset.card_union_le (nearDiag n (b * Hscale n)) (nearRes n (100 * Hscale n))
    exact_mod_cast h
  have hf1 : ((⌊b * Hscale n⌋₊ : ℕ) : ℝ) ≤ b * Hscale n := Nat.floor_le (by positivity)
  have hf2 : ((⌊100 * Hscale n⌋₊ : ℕ) : ℝ) ≤ 100 * Hscale n := Nat.floor_le (by positivity)
  have h1 : ((nearDiag n (b * Hscale n)).card : ℝ) ≤ ((b + 1) * Hscale n) * (A * Lnorm n) := by
    have hle := card_nearDiag_le n (b * Hscale n)
    have hcast : ((nearDiag n (b * Hscale n)).card : ℝ)
        ≤ (((⌊b * Hscale n⌋₊ : ℕ) : ℝ) + 1) * ((bulkJ n).card : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this
      linarith
    refine le_trans hcast (mul_le_mul ?_ hJ hJ0 (by nlinarith))
    nlinarith
  have h2 : ((nearRes n (100 * Hscale n)).card : ℝ) ≤ (204 * Hscale n) * (A * Lnorm n) := by
    have hle := card_nearRes_le n (100 * Hscale n)
    have hcast : ((nearRes n (100 * Hscale n)).card : ℝ)
        ≤ (2 * ((⌊100 * Hscale n⌋₊ : ℕ) : ℝ) + 4) * ((bulkJ n).card : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this
      linarith
    refine le_trans hcast (mul_le_mul ?_ hJ hJ0 (by nlinarith))
    nlinarith
  have hfin : ((b + 1) * Hscale n) * (A * Lnorm n) + (204 * Hscale n) * (A * Lnorm n)
      = (A * (b + 205)) * Lnorm n * Hscale n := by ring
  linarith

/-! ## 3. Monotonicity of the right-hand side of (34) in `(C, c, ρ)` -/

lemma err_le {C C' c c' ρ ρ' L H : ℝ}
    (hC0 : 0 < C) (hCC : C ≤ C') (hc' : 0 < c') (hcc : c' ≤ c)
    (hρ0 : 0 < ρ) (hρρ : ρ ≤ ρ') (hρ'1 : ρ' < 1) (_hL : 0 ≤ L) (hH : 0 ≤ H) :
    C * (Real.exp (-c * Real.sqrt L) + Real.exp (-c * H) + ρ ^ (c * H))
      ≤ C' * (Real.exp (-c' * Real.sqrt L) + Real.exp (-c' * H) + ρ' ^ (c' * H)) := by
  have hρ1 : ρ ≤ 1 := le_of_lt (lt_of_le_of_lt hρρ hρ'1)
  have hsq : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have e1 : Real.exp (-c * Real.sqrt L) ≤ Real.exp (-c' * Real.sqrt L) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-c * H) ≤ Real.exp (-c' * H) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : ρ ^ (c * H) ≤ ρ' ^ (c' * H) := by
    have h1 : ρ ^ (c * H) ≤ ρ ^ (c' * H) :=
      Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by nlinarith)
    have h2 : ρ ^ (c' * H) ≤ ρ' ^ (c' * H) :=
      Real.rpow_le_rpow hρ0.le hρρ (mul_nonneg hc'.le hH)
    linarith
  have hsum0 : (0 : ℝ) ≤ Real.exp (-c * Real.sqrt L) + Real.exp (-c * H) + ρ ^ (c * H) := by
    have := Real.exp_pos (-c * Real.sqrt L)
    have := Real.exp_pos (-c * H)
    have := Real.rpow_pos_of_pos hρ0 (c * H)
    linarith
  exact mul_le_mul hCC (by linarith) hsum0 (by linarith)

/-! ## 4. The three cases of Kwon's proof of Proposition 4.2

Each is stated exactly as the manuscript's corresponding case, for a single
pair of monomials, uniformly over the two fixed finite word sets and the mode
box.  See the module docstring for the obstruction attached to each.
-/

/-- **Case 1 of the proof of 4.2.** "If both torus modes vanish, ordinary
two-sided Gauss mixing proves (34) unless the blocks overlap."

OBSTRUCTION: this is Lemma 3.2 applied to *digit-cylinder indicators*.
`Kwon1002.Transfer.lemma_3_2` is available only for Lipschitz observables
(Wang's Lasota-Yorke contraction is on the Lipschitz seminorm), see the
finding recorded in `TransferMixing.lean`, which states explicitly that the
proved form does not cover §4's use, and it still rests on the sorried
`cylinder_transfer_eq_kwonDensity`. -/
theorem zeroMode_gauss_mixing (R : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ w' ∈ Wv, ∀ p ∈ bulkPairs n,
        C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w 0 0 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)
            - Prop42.monoStationary R w 0 0 * Prop42.monoStationary R w' 0 0‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  sorry

/-- **Case 2 of the proof of 4.2**, "Assume the later mode `(r₂,s₂)` is
nonzero": after Lemma 3.3 (`shrinking_anti_concentration`, proved) and the
Fibonacci domination `|Q| ≥ ½ e^{−cH} q_k` (`Prop42.later_frequency_dominates`,
proved) and the retained-descendant exponent
(`Prop42.retained_descendant_exponent`, proved), the whole two-block integral
is `O(e^{−cH} + e^{−cL^{1/2}})`.

OBSTRUCTION: the last step is **Lemma 3.4, display (22)**, the oscillatory
bound `|Σ_w ∫_{I_w} e(nQ_w α) A(α) dα| ≤ Cε` on the retained depth-`t₋`
descendants.  Display (22) is not present anywhere in this development; only
its converse (`CylinderPhase.descendant_phase_small`, "the phase is nearly
constant on a deep cylinder") is proved. -/
theorem laterMode_phase_bound (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ Prop42.modeBox K, m' ≠ (0, 0) →
      ∀ p ∈ bulkPairs n, C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  sorry

/-- **Case 3 of the proof of 4.2**, "It remains to suppose that the earlier
mode is nonzero and the later mode is zero."  With `t₀ = (m_n + j)/2`, the
pairs with `|k − t₀| ≤ 100H` are declared exceptional (they are counted by
`card_nearRes_le`); off that window the two sub-cases `k < t₀ − 100H` and
`k > t₀ + 100H` are handled by Lemma 3.4 and by (23) plus conditional Gauss
mixing respectively.

OBSTRUCTION: as in `laterMode_phase_bound`, the substantive half of Lemma 3.4
(display (22)) is missing; the `k > t₀ + 100H` branch additionally needs the
conditional Gauss mixing of Lemma 3.2 for digit indicators. -/
theorem earlierMode_phase_bound (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, m ≠ (0, 0) → ∀ w' ∈ Wv,
      ∀ p ∈ bulkPairs n,
        100 * Hscale n < |(p.2 : ℝ) - ((mIndex n : ℝ) + (p.1 : ℝ)) / 2| →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  sorry

/-! ## 5. The monomial core -/

/-- **Monomial core of Proposition 4.2**, reproduced token-identically from
`Kwon1002/Prop42.lean` (`two_block_monomial_core`) and proved from the
three-case decomposition above. -/
theorem two_block_monomial_core' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
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
  obtain ⟨CA, cA, ρA, hCA0, hcA0, hρA0, hρA1, hA⟩ := zeroMode_gauss_mixing R Wu Wv
  obtain ⟨CB, cB, ρB, hCB0, hcB0, hρB0, hρB1, hB⟩ := laterMode_phase_bound R K Wu Wv
  obtain ⟨CD, cD, ρD, hCD0, hcD0, hρD0, hρD1, hD⟩ := earlierMode_phase_bound R K Wu Wv
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
  have hH1 : (1 : ℝ) ≤ Hscale n := one_le_Hscale hL1
  have hH0 : (0 : ℝ) ≤ Hscale n := by linarith
  set Exc : Finset (ℕ × ℕ) :=
    nearDiag n (C₁ * Hscale n) ∪ nearRes n (100 * Hscale n) with hExcdef
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
    have hnd : p ∉ nearDiag n (C₁ * Hscale n) := fun h =>
      hcon (Finset.mem_coe.2 (Finset.mem_union_left _ h))
    have hnr : p ∉ nearRes n (100 * Hscale n) := fun h =>
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
      · -- both modes vanish: ordinary two-sided Gauss mixing
        have hm1 : m.1 = 0 := by rw [hm0]
        have hm2 : m.2 = 0 := by rw [hm0]
        rw [hm1, hm2, hm'1, hm'2]
        refine le_trans (hAn w hw w' hw' p hpb ?_) ?_
        · calc CA * Hscale n ≤ C₁ * Hscale n :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hH0
            _ < _ := hgap
        · exact err_le hCA0 (le_trans (le_max_left _ _) hC₁C) hc₁0 (min_le_left _ _)
            hρA0 (le_max_left _ _) hρ₁1 hL0 hH0
      · -- earlier mode nonzero, later mode zero
        have hstat : Prop42.monoStationary R w m.1 m.2 = 0 :=
          monoStationary_eq_zero R w (by rw [Prod.mk.eta]; exact hm0)
        rw [hm'1, hm'2, hstat, zero_mul, sub_zero]
        refine le_trans (hDn w hw m hm hm0 w' hw' p hpb hres) ?_
        exact err_le hCD0 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC₁C)
          hc₁0 (le_trans (min_le_right _ _) (min_le_right _ _))
          hρD0 (le_trans (le_max_right _ _) (le_max_right _ _)) hρ₁1 hL0 hH0
    · -- later mode nonzero
      have hstat : Prop42.monoStationary R w' m'.1 m'.2 = 0 :=
        monoStationary_eq_zero R w' (by rw [Prod.mk.eta]; exact hm'0)
      rw [hstat, mul_zero, sub_zero]
      refine le_trans (hBn w hw m hm w' hw' m' hm' hm'0 p hpb ?_) ?_
      · calc CB * Hscale n ≤ C₁ * Hscale n :=
              mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hH0
          _ < _ := hgap
      · exact err_le hCB0 (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC₁C)
          hc₁0 (le_trans (min_le_right _ _) (min_le_left _ _))
          hρB0 (le_trans (le_max_left _ _) (le_max_right _ _)) hρ₁1 hL0 hH0
  have hfin := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hfin
  have hcount : ((Exc.card : ℕ) : ℝ) ≤ C * Lnorm n * Hscale n := by
    have h1 : ((Exc.card : ℕ) : ℝ) ≤ (A * (C₁ + 205)) * Lnorm n * Hscale n := by
      rw [hExcdef, hAdef]
      exact exc_card_bound n C₁ hC₁0.le hL1
    have h2 : A * (C₁ + 205) ≤ C := le_max_right _ _
    calc ((Exc.card : ℕ) : ℝ) ≤ (A * (C₁ + 205)) * Lnorm n * Hscale n := h1
      _ = (A * (C₁ + 205)) * (Lnorm n * Hscale n) := by ring
      _ ≤ C * (Lnorm n * Hscale n) := mul_le_mul_of_nonneg_right h2 (mul_nonneg hL0 hH0)
      _ = C * Lnorm n * Hscale n := by ring
  refine le_trans ?_ hcount
  exact_mod_cast hfin

end

end MonomialCore

/-! ## 6. Token-identical restatement in `Prop42`'s own namespace

The statement below is a byte-for-byte copy of the target
`Kwon1002.Prop42.two_block_monomial_core` (Prop42.lean lines 582-591), with
only the theorem *name* primed; placing it inside `namespace Prop42` makes
`modeBox`, `monoAt`, `monoStationary` resolve exactly as they do there, so the
reproduction is literal rather than up to qualification.
-/

namespace Prop42

theorem two_block_monomial_core' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ modeBox K,
        (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
            ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
                    monoAt R w m.1 m.2 α n p.1 * monoAt R w' m'.1 m'.2 α n p.2)
                  - monoStationary R w m.1 m.2 * monoStationary R w' m'.1 m'.2‖
                ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                        + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
          ≤ C * Lnorm n * Hscale n :=
  MonomialCore.two_block_monomial_core' R K Wu Wv

end Prop42

end Kwon1002
