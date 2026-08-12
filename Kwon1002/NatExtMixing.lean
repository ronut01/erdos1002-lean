import Kwon1002.NatExtInvariance
import Erdos1002.GaussTransferCorrelation

/-!
# The two-sided mixing reduction: `natExt_zero_mode_mixing`

Target: the natural extension `σ = natExtMap` of the Gauss map is mixing
for `ν̂ = hatNu` — for all measurable `A, B ⊆ ℝ²`,

`ν̂(A ∩ σ⁻ᵐ B) → ν̂(A) ν̂(B)`.

The manuscript disposes of this in one line ("the natural extension of a
mixing endomorphism is mixing"); Mathlib has neither a notion of mixing
nor a natural-extension construction, so the reduction to the one-sided
transfer-operator contraction is built here by hand against the concrete
model.

## The route

The structural fact the whole file leans on: the future coordinate of
`σ^m(x,y)` is `T^m x` — it does not depend on `y` at all — while the past
coordinate is an `m`-fold composition of the contractions `y ↦ 1/(a+y)`.

1. **Past contraction** (`iterate_snd_dist_le`): for a fixed future
   coordinate `x` with all digits ≥ 1, two starting pasts `u, v ∈ [0,1]`
   satisfy `|σ^m(x,u)₂ - σ^m(x,v)₂| ≤ 2 (1/2)^m |u - v|`.  One step never
   expands, and two consecutive steps contract by `1/4`, because
   `(a₂ + 1/(a₁+u))(a₁+u) = a₁ + u + 1 ≥ 2`.
2. **Conditional-expectation collapse** (`integral_fst_mul_hatNu`): for an
   observable `F` of the future coordinate alone,
   `∫ F(x) f(x,y) dν̂ = ∫ F · (wProj f) dγ`, where
   `wProj f x = ∫₀¹ f(x,y) (1+x)/(1+xy)² dy` and `γ = gaussMarginal` is
   the Gauss measure.  If `f` is `L`-Lipschitz in `x`, then `wProj f` is
   `(2L+4)`-Lipschitz (`wProj` kernel algebra: `Rker_diff_bound`).
3. **The marginal is the substrate's Gauss measure**
   (`gaussMarginal_eq_gaussMeasure`), so Wang's transfer-operator
   contraction applies to the collapsed side.
4. **One-sided correlation decay** (`gauss_correlation_le`): from the
   Perron–Frobenius adjoint identity and the sup-norm contraction
   `|L^q F - ∫F| ≤ (527/540)^q K`, a two-block correlation
   `∫ F · (G ∘ T^q) dγ` is within `(527/540)^q K M` of `∫F ∫G`, with `G`
   only bounded measurable.
5. **Mixing for Lipschitz observables** (`lipschitz_mixing_le`,
   `lipschitz_mixing`): split `m = q + K` with `K = m/2`.  Freezing the
   past at `1/2` costs `2 Lg (1/2)^m` (step 1); the collapse turns the
   correlation into a one-sided one against
   `h(x') = g(σ^K(x', 1/2))` at gap `q`; truncating the past dependence
   to the top `K` digits costs `2 Lg (1/2)^K`; the mean of `h` is within
   `2 Lg (1/2)^K` of `∫ g dν̂` by `σ^K`-invariance of `ν̂`.  Total:
   `(2 Lf + 4 + 6 Lg) (527/540)^(m/2)`.
6. **Indicators** (`exists_lipschitz_approx`, `natExt_zero_mode_mixing`):
   `ν̂` is a finite Borel measure on `ℝ²`, hence inner regular by closed
   sets; a closed set is approximated from outside by its `δ`-thickening,
   and `p ↦ max 0 (1 - infDist(p,F)/δ)` is a `[0,1]`-valued Lipschitz
   function wedged between them.  A `3ε`-argument (using
   `σ`-invariance of `ν̂` on the `B`-side error) transfers the Lipschitz
   mixing statement to indicators of arbitrary measurable sets.

`Kwon1002.Lemma62.natExt_zero_mode_mixing` delegates here.

## Refute-first notes

* `m = 0`: every estimate above is stated and proved for all `m`; the
  contraction bound at `m = 0` reads `|u - v| ≤ 2|u - v|`.
* `0⁻¹ = 0`: the digit recursion is only used on irrational futures in
  `(0,1)`, which is a `ν̂`- and `γ`-full set (`hatNu_ae_good`,
  `gaussMarginal_ae_mem`); no statement below evaluates `σ` outside it
  except through measurable-function bookkeeping.
* The frozen past `1/2` is arbitrary; any point of `[0,1]` works, and the
  proof only uses `|y - 1/2| ≤ 1` for `y ∈ [0,1]`.
-/

open MeasureTheory Set Filter Metric
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace NatExtMixing

noncomputable section

/-! ## 1. Orbit bookkeeping and full-measure sets -/

/-- The future coordinate of the natural extension advances by the Gauss
map alone (same statement as `Lemma62.natExtMap_iterate_fst`, reproved
here because this module sits upstream of `Lemma62`). -/
theorem natExtMap_iterate_fst (m : ℕ) (p : ℝ × ℝ) :
    (natExtMap^[m] p).1 = gaussIter p.1 m := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, natExtMap]
      simp [gaussIter, Function.iterate_succ_apply]

/-- `Kwon1002.gaussIter` is the substrate's `gaussOrbit` (same statement
as `MixingBV.gaussIter_eq_gaussOrbit`, reproved as a `rfl` because this
module sits upstream). -/
theorem gaussIter_eq_gaussOrbit (α : ℝ) (j : ℕ) :
    gaussIter α j = Erdos1002.gaussOrbit j α := rfl

/-- The `ν̂`-generic point: both coordinates in `(0,1)`, future irrational. -/
def Good : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 ∧ Irrational p.1}

theorem hatNu_ac : hatNu ≪ (volume : Measure (ℝ × ℝ)) :=
  (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous

/-- The irrational-future unit square carries full `ν̂`-measure. -/
theorem hatNu_ae_good : ∀ᵐ p ∂hatNu, p ∈ Good := by
  have h1 : ∀ᵐ p ∂hatNu, p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    rw [hatNu]
    exact (ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  have h2 : ∀ᵐ p ∂hatNu, Irrational p.1 := by
    refine hatNu_ac ?_
    have hcov : {p : ℝ × ℝ | ¬Irrational p.1}
        ⊆ Prod.fst ⁻¹' (Set.range ((↑) : ℚ → ℝ)) := by
      intro p hp
      simpa [Irrational] using hp
    refine measure_mono_null hcov ?_
    have hpre : (Prod.fst ⁻¹' (Set.range ((↑) : ℚ → ℝ)) : Set (ℝ × ℝ))
        = (Set.range ((↑) : ℚ → ℝ)) ×ˢ (univ : Set ℝ) := by
      ext p; simp
    rw [hpre, Measure.volume_eq_prod, Measure.prod_prod,
      (Set.countable_range _).measure_zero, zero_mul]
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1.1, hp1.2, hp2⟩

/-- The Gauss marginal lives on `(0,1)`. -/
theorem gaussMarginal_ae_mem : ∀ᵐ x ∂gaussMarginal, x ∈ Ioo (0 : ℝ) 1 := by
  rw [gaussMarginal]
  exact (ae_restrict_mem measurableSet_Ioo).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

theorem gaussMarginal_ac : gaussMarginal ≪ (volume : Measure ℝ) :=
  (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous

/-- Irrationality is `γ`-generic. -/
theorem gaussMarginal_ae_irrational : ∀ᵐ x ∂gaussMarginal, Irrational x := by
  refine gaussMarginal_ac ?_
  have hcov : {x : ℝ | ¬Irrational x} ⊆ Set.range ((↑) : ℚ → ℝ) := by
    intro x hx
    simpa [Irrational] using hx
  exact measure_mono_null hcov ((Set.countable_range _).measure_zero _)

/-! ## 2. The past-coordinate contraction

One application of `y ↦ 1/(a+y)`, `a ≥ 1`, never expands distances on
`[0,1]`; two consecutive applications contract by `1/4`, because
`(a₂ + 1/(a₁+u)) (a₁+u) = a₁ + u + 1 ≥ 2` for each of the two points.
The `m`-fold composition therefore contracts at rate `2 (1/2)^m`. -/

theorem inv_add_mem_Icc {a u : ℝ} (ha : 1 ≤ a) (hu : u ∈ Icc (0 : ℝ) 1) :
    (a + u)⁻¹ ∈ Icc (0 : ℝ) 1 := by
  have h1 : (1 : ℝ) ≤ a + u := by linarith [hu.1]
  have h0 : (0 : ℝ) < a + u := by linarith
  exact ⟨(inv_pos.mpr h0).le, inv_le_one_of_one_le₀ h1⟩

/-- One past step never expands. -/
theorem inv_add_dist_le {a u v : ℝ} (ha : 1 ≤ a) (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    |(a + u)⁻¹ - (a + v)⁻¹| ≤ |u - v| := by
  have hu0 : (0 : ℝ) < a + u := by linarith [hu.1]
  have hv0 : (0 : ℝ) < a + v := by linarith [hv.1]
  have hkey : (a + u)⁻¹ - (a + v)⁻¹ = (v - u) / ((a + u) * (a + v)) := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos (by positivity : (0:ℝ) < (a + u) * (a + v))]
  have h1 : (1 : ℝ) ≤ (a + u) * (a + v) := by nlinarith [hu.1, hv.1]
  calc |v - u| / ((a + u) * (a + v)) ≤ |v - u| / 1 :=
        div_le_div_of_nonneg_left (abs_nonneg _) one_pos h1 |>.trans_eq (by ring_nf)
    _ = |u - v| := by rw [div_one, abs_sub_comm]

/-- Two past steps contract by `1/4`. -/
theorem inv_add_two_dist_le {a₁ a₂ u v : ℝ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    |(a₂ + (a₁ + u)⁻¹)⁻¹ - (a₂ + (a₁ + v)⁻¹)⁻¹| ≤ |u - v| / 4 := by
  have hu0 : (0 : ℝ) < a₁ + u := by linarith [hu.1]
  have hv0 : (0 : ℝ) < a₁ + v := by linarith [hv.1]
  have hcu := inv_add_mem_Icc ha₁ hu
  have hcv := inv_add_mem_Icc ha₁ hv
  have hu2 : (0 : ℝ) < a₂ + (a₁ + u)⁻¹ := by linarith [hcu.1]
  have hv2 : (0 : ℝ) < a₂ + (a₁ + v)⁻¹ := by linarith [hcv.1]
  have hkey : (a₂ + (a₁ + u)⁻¹)⁻¹ - (a₂ + (a₁ + v)⁻¹)⁻¹
      = ((a₁ + v)⁻¹ - (a₁ + u)⁻¹) / ((a₂ + (a₁ + u)⁻¹) * (a₂ + (a₁ + v)⁻¹)) := by
    field_simp
    ring
  have hkey2 : (a₁ + v)⁻¹ - (a₁ + u)⁻¹ = (u - v) / ((a₁ + u) * (a₁ + v)) := by
    field_simp
    ring
  -- the two-step denominator: `(a₂ + 1/(a₁+u))(a₁+u) = a₂(a₁+u) + 1 ≥ 2`
  have hd1 : (2 : ℝ) ≤ (a₂ + (a₁ + u)⁻¹) * (a₁ + u) := by
    have : (a₂ + (a₁ + u)⁻¹) * (a₁ + u) = a₂ * (a₁ + u) + 1 := by
      field_simp
    rw [this]
    nlinarith [hu.1]
  have hd2 : (2 : ℝ) ≤ (a₂ + (a₁ + v)⁻¹) * (a₁ + v) := by
    have : (a₂ + (a₁ + v)⁻¹) * (a₁ + v) = a₂ * (a₁ + v) + 1 := by
      field_simp
    rw [this]
    nlinarith [hv.1]
  have hprod : (4 : ℝ) ≤ ((a₂ + (a₁ + u)⁻¹) * (a₁ + u)) * ((a₂ + (a₁ + v)⁻¹) * (a₁ + v)) := by
    nlinarith [hd1, hd2]
  rw [hkey, hkey2, div_div, abs_div]
  rw [abs_of_pos (by positivity : (0:ℝ) <
    (a₁ + u) * (a₁ + v) * ((a₂ + (a₁ + u)⁻¹) * (a₂ + (a₁ + v)⁻¹)))]
  have hre : (a₁ + u) * (a₁ + v) * ((a₂ + (a₁ + u)⁻¹) * (a₂ + (a₁ + v)⁻¹))
      = ((a₂ + (a₁ + u)⁻¹) * (a₁ + u)) * ((a₂ + (a₁ + v)⁻¹) * (a₁ + v)) := by ring
  rw [hre]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hprod

/-- The second coordinate of the orbit stays in `[0,1]`. -/
theorem iterate_snd_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hirr : Irrational x)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    (natExtMap^[m] (x, u)).2 ∈ Icc (0 : ℝ) 1 := by
  induction m generalizing x u with
  | zero => simpa using hu
  | succ m ih =>
      rw [Function.iterate_succ_apply, natExtMap]
      exact ih (gaussMap_mem_Ioo hirr) (gaussMap_irrational hirr)
        (inv_add_mem_Icc (by exact_mod_cast one_le_digit hx hirr 0) hu)

/-- **The past contraction.**  With the future coordinate fixed at an
irrational `x ∈ (0,1)`, the `m`-th past coordinates started from
`u, v ∈ [0,1]` are within `2 (1/2)^m |u - v|` of each other. -/
theorem iterate_snd_dist_le (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational x) {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    |(natExtMap^[m] (x, u)).2 - (natExtMap^[m] (x, v)).2|
      ≤ 2 * (1 / 2 : ℝ) ^ m * |u - v| := by
  induction m using Nat.strong_induction_on generalizing x u v with
  | _ m ih =>
    match m with
    | 0 => simpa using by linarith [abs_nonneg (u - v)]
    | 1 =>
        simp only [Function.iterate_one, natExtMap]
        have h := inv_add_dist_le
          (by exact_mod_cast one_le_digit hx hirr 0 : (1:ℝ) ≤ (digit x 0 : ℝ)) hu hv
        calc |((digit x 0 : ℝ) + u)⁻¹ - ((digit x 0 : ℝ) + v)⁻¹| ≤ |u - v| := h
          _ ≤ 2 * (1 / 2 : ℝ) ^ 1 * |u - v| := by
              rw [pow_one]; nlinarith [abs_nonneg (u - v)]
    | m + 2 =>
        have ha₁ : (1 : ℝ) ≤ (digit x 0 : ℝ) := by
          exact_mod_cast one_le_digit hx hirr 0
        have hx1 : gaussMap x ∈ Ioo (0 : ℝ) 1 := gaussMap_mem_Ioo hirr
        have hirr1 : Irrational (gaussMap x) := gaussMap_irrational hirr
        have ha₂ : (1 : ℝ) ≤ (digit (gaussMap x) 0 : ℝ) := by
          exact_mod_cast one_le_digit hx1 hirr1 0
        have hx2 : gaussMap (gaussMap x) ∈ Ioo (0 : ℝ) 1 := gaussMap_mem_Ioo hirr1
        have hirr2 : Irrational (gaussMap (gaussMap x)) := gaussMap_irrational hirr1
        -- two explicit steps
        have hstep : ∀ w : ℝ, natExtMap^[m + 2] (x, w)
            = natExtMap^[m] (gaussMap (gaussMap x),
                ((digit (gaussMap x) 0 : ℝ) + ((digit x 0 : ℝ) + w)⁻¹)⁻¹) := by
          intro w
          rw [show m + 2 = m + (1 + 1) by ring, Function.iterate_add_apply]
          congr 1
        rw [hstep u, hstep v]
        have hmem_u : ((digit (gaussMap x) 0 : ℝ) + ((digit x 0 : ℝ) + u)⁻¹)⁻¹
            ∈ Icc (0 : ℝ) 1 := inv_add_mem_Icc ha₂ (inv_add_mem_Icc ha₁ hu)
        have hmem_v : ((digit (gaussMap x) 0 : ℝ) + ((digit x 0 : ℝ) + v)⁻¹)⁻¹
            ∈ Icc (0 : ℝ) 1 := inv_add_mem_Icc ha₂ (inv_add_mem_Icc ha₁ hv)
        have hIH := ih m (by omega) hx2 hirr2 hmem_u hmem_v
        have h2 := inv_add_two_dist_le ha₁ ha₂ hu hv
        calc |(natExtMap^[m] (gaussMap (gaussMap x),
                ((digit (gaussMap x) 0 : ℝ) + ((digit x 0 : ℝ) + u)⁻¹)⁻¹)).2
              - (natExtMap^[m] (gaussMap (gaussMap x),
                ((digit (gaussMap x) 0 : ℝ) + ((digit x 0 : ℝ) + v)⁻¹)⁻¹)).2|
            ≤ 2 * (1 / 2 : ℝ) ^ m
              * |((digit (gaussMap x) 0 : ℝ) + ((digit x 0 : ℝ) + u)⁻¹)⁻¹
                  - ((digit (gaussMap x) 0 : ℝ) + ((digit x 0 : ℝ) + v)⁻¹)⁻¹| := hIH
          _ ≤ 2 * (1 / 2 : ℝ) ^ m * (|u - v| / 4) := by
              refine mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 2 * (1 / 2 : ℝ) ^ (m + 2) * |u - v| := by ring

/-! ## 3. The conditional-expectation collapse

For an observable `F` of the future coordinate alone,
`∫ F(x) f(x,y) dν̂(x,y) = ∫ F(x) (wProj f)(x) dγ(x)`, where
`wProj f x = ∫₀¹ f(x,y) Rker x y dy` and `Rker x y = (1+x)/(1+xy)²` is
exactly the fibre density of `ν̂` over its Gauss marginal `γ`.  The kernel
integrates to `1` in `y`, is bounded by `2`, and is `4`-Lipschitz in `x`,
so `wProj` maps the `[0,1]`-valued `L`-in-`x`-Lipschitz class into the
`[0,1]`-valued `(2L+4)`-Lipschitz class on the unit interval. -/

instance : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  simp [Real.volume_Ioo]

instance : IsProbabilityMeasure gaussMarginal := by
  rw [← NatExtMeasure.hatNu_fst_marginal]
  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- The real-valued density of `ν̂` against Lebesgue on the square. -/
def densReal (p : ℝ × ℝ) : ℝ := 1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2)

/-- The real-valued density of `γ` against Lebesgue on `(0,1)`. -/
def gaussDensReal (x : ℝ) : ℝ := 1 / (Real.log 2 * (1 + x))

/-- The fibre kernel `Rker x y = (1+x)/(1+xy)²`, the conditional density
of the past coordinate given the future one. -/
def Rker (x y : ℝ) : ℝ := (1 + x) / (1 + x * y) ^ 2

theorem measurable_densReal : Measurable densReal := by
  unfold densReal; fun_prop

theorem measurable_gaussDensReal : Measurable gaussDensReal := by
  unfold gaussDensReal; fun_prop

theorem measurable_Rker : Measurable (fun p : ℝ × ℝ => Rker p.1 p.2) := by
  unfold Rker; fun_prop

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

theorem one_le_one_add_mul_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1:ℝ) ≤ (1 + x * y) ^ 2 := by
  nlinarith [mul_nonneg hx hy]

theorem pos_one_add_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (0:ℝ) < 1 + x * y := by
  nlinarith [mul_nonneg hx hy]

/-- The density factorization `densReal (x,y) = gaussDensReal x · Rker x y`,
valid whenever `1 + x ≠ 0` (in particular on the closed square). -/
theorem densReal_eq {x y : ℝ} (hx : (0:ℝ) ≤ x) :
    densReal (x, y) = gaussDensReal x * Rker x y := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  simp only [densReal, gaussDensReal, Rker]
  field_simp

theorem Rker_nonneg {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    0 ≤ Rker x y := by
  have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1 + x * y := pos_one_add_mul hx.1 hy.1
  unfold Rker
  positivity

theorem Rker_le_two {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    Rker x y ≤ 2 := by
  have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (1:ℝ) ≤ (1 + x * y) ^ 2 := one_le_one_add_mul_sq hx.1 hy.1
  unfold Rker
  calc (1 + x) / (1 + x * y) ^ 2 ≤ (1 + x) / 1 :=
        div_le_div_of_nonneg_left h1.le one_pos h2
    _ = 1 + x := div_one _
    _ ≤ 2 := by linarith [hx.2]

/-- The kernel is `4`-Lipschitz in the future coordinate, uniformly over
the past: the difference factors as
`(x - x') (1 - 2y - (x+x')y² - x x' y²) / ((1+xy)²(1+x'y)²)` with the
bracket in `[-4, 1]` and the denominator at least `1`. -/
theorem Rker_diff_bound {x x' y : ℝ} (hx : x ∈ Icc (0:ℝ) 1)
    (hx' : x' ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    |Rker x y - Rker x' y| ≤ 4 * |x - x'| := by
  have hDx : (1:ℝ) ≤ (1 + x * y) ^ 2 := one_le_one_add_mul_sq hx.1 hy.1
  have hDx' : (1:ℝ) ≤ (1 + x' * y) ^ 2 := one_le_one_add_mul_sq hx'.1 hy.1
  have hDx0 : (0:ℝ) < (1 + x * y) ^ 2 := lt_of_lt_of_le one_pos hDx
  have hDx'0 : (0:ℝ) < (1 + x' * y) ^ 2 := lt_of_lt_of_le one_pos hDx'
  have hkey : Rker x y - Rker x' y
      = ((1 + x) * (1 + x' * y) ^ 2 - (1 + x * y) ^ 2 * (1 + x'))
        / ((1 + x * y) ^ 2 * (1 + x' * y) ^ 2) := by
    unfold Rker
    exact div_sub_div _ _ (ne_of_gt hDx0) (ne_of_gt hDx'0)
  have hnum : (1 + x) * (1 + x' * y) ^ 2 - (1 + x * y) ^ 2 * (1 + x')
      = (x - x') * (1 - 2 * y - (x + x') * y ^ 2 - x * x' * y ^ 2) := by
    ring
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have hy2' : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
  have hs1 : (x + x') * y ^ 2 ≤ 2 := by
    nlinarith [mul_nonneg (add_nonneg hx.1 hx'.1) (by linarith : (0:ℝ) ≤ 1 - y ^ 2),
      hx.2, hx'.2]
  have hs1' : (0:ℝ) ≤ (x + x') * y ^ 2 := mul_nonneg (add_nonneg hx.1 hx'.1) hy2'
  have hs2 : x * x' * y ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (mul_nonneg hx.1 hx'.1) (by linarith : (0:ℝ) ≤ 1 - y ^ 2),
      mul_nonneg hx.1 (by linarith [hx'.2] : (0:ℝ) ≤ 1 - x'), hx.2]
  have hs2' : (0:ℝ) ≤ x * x' * y ^ 2 := mul_nonneg (mul_nonneg hx.1 hx'.1) hy2'
  have hbr : |1 - 2 * y - (x + x') * y ^ 2 - x * x' * y ^ 2| ≤ 4 := by
    rw [abs_le]
    constructor
    · linarith [hy.2]
    · linarith [hy.1]
  have hden : (1:ℝ) ≤ (1 + x * y) ^ 2 * (1 + x' * y) ^ 2 := by nlinarith
  rw [hkey, hnum, abs_div, abs_mul]
  calc |x - x'| * |1 - 2 * y - (x + x') * y ^ 2 - x * x' * y ^ 2|
        / |(1 + x * y) ^ 2 * (1 + x' * y) ^ 2|
      ≤ |x - x'| * |1 - 2 * y - (x + x') * y ^ 2 - x * x' * y ^ 2| := by
        refine div_le_self (by positivity) ?_
        rw [abs_of_pos (by positivity)]
        exact hden
    _ ≤ |x - x'| * 4 := mul_le_mul_of_nonneg_left hbr (abs_nonneg _)
    _ = 4 * |x - x'| := by ring

/-- The kernel integrates to `1` over the past fibre. -/
theorem integral_Rker {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    ∫ y in Ioo (0:ℝ) 1, Rker x y = 1 := by
  have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
  have hIoo : ∫ y in Ioo (0:ℝ) 1, Rker x y = ∫ y in (0:ℝ)..1, Rker x y := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hIoo]
  have hsplit : (fun y : ℝ => Rker x y)
      = fun y : ℝ => (1 + x) * (1 / (1 + x * y) ^ 2) := by
    funext y
    unfold Rker
    ring
  rw [hsplit, intervalIntegral.integral_const_mul,
    NatExtMeasure.integral_inv_one_add_mul_sq x hx.1]
  field_simp

/-- The fibre projection: the conditional expectation of `f` given the
future coordinate, written against the explicit kernel. -/
def wProj (f : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioo (0:ℝ) 1, f (x, y) * Rker x y

theorem integrableOn_unit_of_bound {h : ℝ → ℝ} (C : ℝ) (hm : Measurable h)
    (hb : ∀ y ∈ Ioo (0:ℝ) 1, |h y| ≤ C) :
    IntegrableOn h (Ioo (0:ℝ) 1) volume := by
  refine Integrable.of_bound hm.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  rw [Real.norm_eq_abs]
  exact hb y hy

theorem measurable_slice {f : ℝ × ℝ → ℝ} (hf : Measurable f) (x : ℝ) :
    Measurable (fun y => f (x, y)) :=
  hf.comp (measurable_const.prodMk measurable_id)

theorem wProj_integrand_integrable {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf01 : ∀ p, f p ∈ Icc (0:ℝ) 1) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    IntegrableOn (fun y => f (x, y) * Rker x y) (Ioo (0:ℝ) 1) volume := by
  refine integrableOn_unit_of_bound 2 ((measurable_slice hf x).mul (by unfold Rker; fun_prop)) ?_
  intro y hy
  have hy' : y ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hy
  rw [abs_mul, abs_of_nonneg (hf01 (x, y)).1, abs_of_nonneg (Rker_nonneg hx hy')]
  calc f (x, y) * Rker x y ≤ 1 * 2 :=
        mul_le_mul (hf01 (x, y)).2 (Rker_le_two hx hy') (Rker_nonneg hx hy') one_pos.le
    _ = 2 := one_mul 2

theorem wProj_nonneg {f : ℝ × ℝ → ℝ} (hf01 : ∀ p, f p ∈ Icc (0:ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ wProj f x := by
  refine setIntegral_nonneg measurableSet_Ioo (fun y hy => ?_)
  exact mul_nonneg (hf01 (x, y)).1 (Rker_nonneg hx (Ioo_subset_Icc_self hy))

theorem wProj_le_one {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf01 : ∀ p, f p ∈ Icc (0:ℝ) 1) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    wProj f x ≤ 1 := by
  have hint := wProj_integrand_integrable hf hf01 hx
  have hintR : IntegrableOn (fun y => Rker x y) (Ioo (0:ℝ) 1) volume := by
    refine integrableOn_unit_of_bound 2 (by unfold Rker; fun_prop) (fun y hy => ?_)
    have hy' : y ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hy
    rw [abs_of_nonneg (Rker_nonneg hx hy')]
    exact Rker_le_two hx hy'
  calc wProj f x ≤ ∫ y in Ioo (0:ℝ) 1, Rker x y := by
        refine setIntegral_mono_on hint hintR measurableSet_Ioo (fun y hy => ?_)
        have hy' : y ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hy
        calc f (x, y) * Rker x y ≤ 1 * Rker x y :=
              mul_le_mul_of_nonneg_right (hf01 (x, y)).2 (Rker_nonneg hx hy')
          _ = Rker x y := one_mul _
    _ = 1 := integral_Rker hx

theorem measurable_wProj {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (wProj f) := by
  have h : StronglyMeasurable (fun p : ℝ × ℝ => f p * Rker p.1 p.2) :=
    (hf.mul measurable_Rker).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- `wProj` carries the `[0,1]`-valued `L`-Lipschitz-in-`x` class into the
`(2L+4)`-Lipschitz class on the unit interval. -/
theorem wProj_lipschitz {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf01 : ∀ p, f p ∈ Icc (0:ℝ) 1) {L : ℝ} (hL : 0 ≤ L)
    (hfLx : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃x'⦄, x' ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 → |f (x, y) - f (x', y)| ≤ L * |x - x'|) :
    Erdos1002.GaussUnitLipschitzBound (2 * L + 4) (wProj f) := by
  intro x hx x' hx'
  have hint := wProj_integrand_integrable hf hf01 hx
  have hint' := wProj_integrand_integrable hf hf01 hx'
  have hsub : wProj f x - wProj f x'
      = ∫ y in Ioo (0:ℝ) 1, (f (x, y) * Rker x y - f (x', y) * Rker x' y) :=
    (integral_sub hint hint').symm
  rw [hsub]
  have hbd : ∀ᵐ y ∂(volume.restrict (Ioo (0:ℝ) 1)),
      ‖f (x, y) * Rker x y - f (x', y) * Rker x' y‖ ≤ (2 * L + 4) * |x - x'| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hy' : y ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hy
    have hsplit : f (x, y) * Rker x y - f (x', y) * Rker x' y
        = (f (x, y) - f (x', y)) * Rker x y + f (x', y) * (Rker x y - Rker x' y) := by
      ring
    rw [Real.norm_eq_abs, hsplit]
    calc |(f (x, y) - f (x', y)) * Rker x y + f (x', y) * (Rker x y - Rker x' y)|
        ≤ |(f (x, y) - f (x', y)) * Rker x y| + |f (x', y) * (Rker x y - Rker x' y)| :=
          abs_add_le _ _
      _ = |f (x, y) - f (x', y)| * |Rker x y| + |f (x', y)| * |Rker x y - Rker x' y| := by
          rw [abs_mul, abs_mul]
      _ ≤ (L * |x - x'|) * 2 + 1 * (4 * |x - x'|) := by
          refine add_le_add (mul_le_mul (hfLx hx hx' hy') ?_ (abs_nonneg _)
            (by positivity)) (mul_le_mul ?_ (Rker_diff_bound hx hx' hy')
            (abs_nonneg _) one_pos.le)
          · rw [abs_of_nonneg (Rker_nonneg hx hy')]
            exact Rker_le_two hx hy'
          · rw [abs_of_nonneg (hf01 (x', y)).1]
            exact (hf01 (x', y)).2
      _ = (2 * L + 4) * |x - x'| := by ring
  calc |∫ y in Ioo (0:ℝ) 1, (f (x, y) * Rker x y - f (x', y) * Rker x' y)|
      ≤ (2 * L + 4) * |x - x'| * ((volume.restrict (Ioo (0:ℝ) 1)) univ).toReal := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const hbd
    _ = (2 * L + 4) * |x - x'| := by
        rw [measure_univ]
        simp

/-- **The conditional-expectation collapse.**  An integral of
`F(future) · f` against `ν̂` is the integral of `F · wProj f` against the
Gauss marginal `γ`. -/
theorem integral_fst_mul_hatNu {F : ℝ → ℝ} (hFm : Measurable F) {CF : ℝ}
    (hFb : ∀ x, |F x| ≤ CF) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf01 : ∀ p, f p ∈ Icc (0:ℝ) 1) :
    ∫ p, F p.1 * f p ∂hatNu = ∫ x, F x * wProj f x ∂gaussMarginal := by
  have hCF : 0 ≤ CF := le_trans (abs_nonneg _) (hFb 0)
  have hrfl : hatNu = (volume.restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)).withDensity
      NatExtInvariance.dens := rfl
  have hgrfl : gaussMarginal = (volume.restrict (Ioo (0:ℝ) 1)).withDensity
      (fun x => ENNReal.ofReal (gaussDensReal x)) := rfl
  -- move both sides to weighted Lebesgue integrals
  rw [hrfl, integral_withDensity_eq_integral_toReal_smul NatExtInvariance.measurable_dens
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _,
    hgrfl, integral_withDensity_eq_integral_toReal_smul
      (by unfold gaussDensReal; fun_prop : Measurable fun x => ENNReal.ofReal (gaussDensReal x))
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _]
  -- identify the `toReal ∘ ofReal` weights on the two domains
  have hLcongr : ∫ p, (NatExtInvariance.dens p).toReal • (F p.1 * f p)
        ∂(volume.restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1))
      = ∫ p in Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, densReal p * (F p.1 * f p) := by
    refine setIntegral_congr_ae (measurableSet_Ioo.prod measurableSet_Ioo)
      (Eventually.of_forall (fun p hp => ?_))
    have hpos : 0 ≤ densReal p := by
      have h2 : (0:ℝ) < 1 + p.1 * p.2 := pos_one_add_mul hp.1.1.le hp.2.1.le
      unfold densReal
      positivity
    simp only [NatExtInvariance.dens, smul_eq_mul]
    rw [show (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2)) = densReal p from rfl,
      ENNReal.toReal_ofReal hpos]
  have hRcongr : ∫ x, (ENNReal.ofReal (gaussDensReal x)).toReal • (F x * wProj f x)
        ∂(volume.restrict (Ioo (0:ℝ) 1))
      = ∫ x in Ioo (0:ℝ) 1, gaussDensReal x * (F x * wProj f x) := by
    refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall (fun x hx => ?_))
    have hpos : 0 ≤ gaussDensReal x := by
      have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
      unfold gaussDensReal
      positivity
    rw [smul_eq_mul, ENNReal.toReal_ofReal hpos]
  rw [hLcongr, hRcongr]
  -- Fubini on the square
  have hdens2 : ∀ p : ℝ × ℝ, p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 → |densReal p| ≤ 2 := by
    intro p hp
    have hsq : (1:ℝ) ≤ (1 + p.1 * p.2) ^ 2 := one_le_one_add_mul_sq hp.1.1.le hp.2.1.le
    have hden : (1/2 : ℝ) ≤ Real.log 2 * (1 + p.1 * p.2) ^ 2 := by
      nlinarith [half_le_log_two, log_two_pos, mul_nonneg log_two_pos.le
        (by linarith : (0:ℝ) ≤ (1 + p.1 * p.2) ^ 2 - 1)]
    unfold densReal
    rw [abs_of_nonneg (by positivity)]
    calc 1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2) ≤ 1 / (1/2 : ℝ) :=
          div_le_div_of_nonneg_left one_pos.le (by norm_num) hden
      _ = 2 := by norm_num
  have hIntProd : Integrable (fun p : ℝ × ℝ => densReal p * (F p.1 * f p))
      (((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1))) := by
    have hae : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Ioo (0:ℝ) 1))),
        p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 := by
      rw [← NatExtMeasure.restrict_unitSq_eq_prod]
      exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    refine Integrable.of_bound
      ((measurable_densReal.mul ((hFm.comp measurable_fst).mul hf)).aestronglyMeasurable)
      (2 * (CF * 1)) ?_
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    refine mul_le_mul (hdens2 p hp) (mul_le_mul (hFb p.1) ?_ (abs_nonneg _) hCF)
      (by positivity) (by norm_num)
    rw [abs_of_nonneg (hf01 p).1]
    exact (hf01 p).2
  rw [NatExtMeasure.restrict_unitSq_eq_prod, integral_prod _ hIntProd]
  refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall (fun x hx => ?_))
  have hx' : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
  calc ∫ y in Ioo (0:ℝ) 1, densReal (x, y) * (F x * f (x, y))
      = ∫ y in Ioo (0:ℝ) 1, gaussDensReal x * (F x * (f (x, y) * Rker x y)) := by
        refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall (fun y _ => ?_))
        rw [densReal_eq hx'.1]
        ring
    _ = gaussDensReal x * ∫ y in Ioo (0:ℝ) 1, F x * (f (x, y) * Rker x y) :=
        integral_const_mul _ _
    _ = gaussDensReal x * (F x * ∫ y in Ioo (0:ℝ) 1, f (x, y) * Rker x y) := by
        rw [integral_const_mul]
    _ = gaussDensReal x * (F x * wProj f x) := rfl

/-! ## 4. The marginal is the substrate's Gauss measure

`gaussMarginal` (Lebesgue-with-density on `(0,1)`) and the substrate's
Stieltjes `Erdos1002.gaussMeasure` (CDF `log(1+x)/log 2` clamped to the
unit interval) are the same Borel measure on `ℝ`: both are finite, and
they agree on every `Iic a`. -/

/-- The distribution function of `γ` up to `a ∈ [0,1]`. -/
theorem lintegral_gaussDens_Ioc {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    ∫⁻ x in Ioc (0:ℝ) a, ENNReal.ofReal (gaussDensReal x)
      = ENNReal.ofReal (Real.log (1 + a) / Real.log 2) := by
  have hcont : ContinuousOn gaussDensReal (Icc (0:ℝ) a) := by
    unfold gaussDensReal
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro x hx
    have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
    exact mul_ne_zero log_two_pos.ne' h1.ne'
  have hInt : IntegrableOn gaussDensReal (Ioc (0:ℝ) a) volume :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) a)] gaussDensReal := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
    unfold gaussDensReal
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le ha.1]
  have hderiv : ∀ y ∈ uIcc (0:ℝ) a,
      HasDerivAt (fun t : ℝ => Real.log (1 + t) / Real.log 2) (gaussDensReal y) y := by
    intro y hy
    rw [uIcc_of_le ha.1] at hy
    have h1 : (0:ℝ) < 1 + y := by linarith [hy.1]
    have h2 : HasDerivAt (fun t : ℝ => 1 + t) 1 y := by
      simpa using (hasDerivAt_id y).const_add (1:ℝ)
    have h3 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + y)) y := h2.log h1.ne'
    have h4 := h3.div_const (Real.log 2)
    convert h4 using 1
    unfold gaussDensReal
    field_simp
  have hint : IntervalIntegrable gaussDensReal volume 0 a := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [uIcc_of_le ha.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **The Gauss marginal of `ν̂` is the substrate's Gauss measure.** -/
theorem gaussMarginal_eq_gaussMeasure : gaussMarginal = Erdos1002.gaussMeasure := by
  refine Measure.ext_of_Iic gaussMarginal Erdos1002.gaussMeasure (fun a => ?_)
  have hR : Erdos1002.gaussMeasure (Iic a) = ENNReal.ofReal (Erdos1002.gaussCDF a) := by
    have h := (Erdos1002.gaussStieltjes).measure_Iic Erdos1002.tendsto_gaussCDF_atBot a
    rw [show Erdos1002.gaussMeasure = Erdos1002.gaussStieltjes.measure from rfl, h]
    norm_num
    rfl
  have hL : gaussMarginal (Iic a)
      = ∫⁻ x in Iic a ∩ Ioo (0:ℝ) 1, ENNReal.ofReal (gaussDensReal x) := by
    rw [show gaussMarginal = (volume.restrict (Ioo (0:ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (gaussDensReal x)) from rfl,
      withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  rw [hL, hR]
  rcases le_or_gt a 0 with ha0 | ha0
  · have he : Iic a ∩ Ioo (0:ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
      intro hxa hx0
      linarith [hx0]
    rw [he, Erdos1002.gaussCDF_eq_zero_of_le ha0]
    simp
  · rcases lt_or_ge a 1 with ha1 | ha1
    · have he : Iic a ∩ Ioo (0:ℝ) 1 = Ioc 0 a := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
        constructor
        · rintro ⟨hxa, hx0, _⟩
          exact ⟨hx0, hxa⟩
        · rintro ⟨hx0, hxa⟩
          exact ⟨hxa, hx0, lt_of_le_of_lt hxa ha1⟩
      rw [he, lintegral_gaussDens_Ioc ⟨ha0.le, ha1.le⟩]
      congr 1
      rw [Erdos1002.gaussCDF, Erdos1002.unitClamp_eq_of_mem_Icc ⟨ha0.le, ha1.le⟩]
    · have he : Iic a ∩ Ioo (0:ℝ) 1 = Ioo 0 1 := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Ioo, and_iff_right_iff_imp]
        rintro ⟨_, hx1⟩
        linarith
      rw [he, setLIntegral_congr Ioo_ae_eq_Ioc,
        lintegral_gaussDens_Ioc (⟨zero_le_one, le_refl (1:ℝ)⟩ : (1:ℝ) ∈ Icc (0:ℝ) 1),
        Erdos1002.gaussCDF_eq_one_of_le ha1]
      congr 1
      rw [show (1:ℝ) + 1 = 2 by norm_num]
      exact div_self log_two_pos.ne'

/-- Integrals against `γ` are `ν̂`-integrals of future-coordinate
observables. -/
theorem integral_gaussMarginal_eq_hatNu {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫ x, φ x ∂gaussMarginal = ∫ p, φ p.1 ∂hatNu := by
  rw [← NatExtMeasure.hatNu_fst_marginal]
  exact integral_map measurable_fst.aemeasurable hφ.aestronglyMeasurable

/-! ## 5. One-sided correlation decay from the transfer contraction

`∫ F (G ∘ T^q) dγ = ∫ (L^q F) G dγ` and `|L^q F - ∫F| ≤ (527/540)^q K`
uniformly, so the correlation decays at that rate against any bounded
measurable `G` — no regularity on `G` at all.  This is the decisive
simplification of the whole reduction: the collapsed past observable
needs to be Lipschitz, but the future one is arbitrary. -/

theorem gauss_correlation_le {A K : ℝ} {F : ℝ → ℝ} (hK : 0 ≤ K)
    (hFm : Measurable F) (hF0 : Erdos1002.GaussUnitNonnegative F)
    (hFA : Erdos1002.GaussUnitUpperBound A F)
    (hFL : Erdos1002.GaussUnitLipschitzBound K F)
    {G : ℝ → ℝ} (hGm : Measurable G) {M : ℝ} (hGb : ∀ x, |G x| ≤ M) (q : ℕ) :
    |(∫ x, F x * G (Erdos1002.gaussOrbit q x) ∂Erdos1002.gaussMeasure)
        - (∫ x, F x ∂Erdos1002.gaussMeasure) * ∫ x, G x ∂Erdos1002.gaussMeasure|
      ≤ (527 / 540 : ℝ) ^ q * K * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hGb 0)
  have hA0 : (0:ℝ) ≤ A := le_trans (hF0 (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Icc (0:ℝ) 1))
    (hFA (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Icc (0:ℝ) 1))
  have hadj := Erdos1002.integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate
    hFm hGm hF0 hFA q
  have hb := Erdos1002.gaussTransfer_iterate_unit_bounds hF0 hFA q
  have hIntT : Integrable ((Erdos1002.gaussTransfer^[q]) F) Erdos1002.gaussMeasure :=
    Erdos1002.integrable_gaussTransfer_iterate_of_unit_bounds hFm hF0 hFA q
  have hGint : Integrable G Erdos1002.gaussMeasure :=
    Integrable.of_bound hGm.aestronglyMeasurable M
      (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hGb x))
  have hprodint : Integrable
      (fun y => (Erdos1002.gaussTransfer^[q]) F y * G y) Erdos1002.gaussMeasure := by
    refine Integrable.of_bound (hIntT.aestronglyMeasurable.mul hGm.aestronglyMeasurable)
      (A * M) ?_
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0:ℝ) 1 := ⟨hy.1.le, hy.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (hGb y) (abs_nonneg _) hA0
    rw [abs_of_nonneg (hb.1 hycc)]
    exact hb.2 hycc
  have hkey : ∀ y ∈ Icc (0:ℝ) 1,
      |(Erdos1002.gaussTransfer^[q]) F y - ∫ x, F x ∂Erdos1002.gaussMeasure|
        ≤ (527 / 540 : ℝ) ^ q * K :=
    fun y hy => Erdos1002.abs_gaussTransfer_iterate_sub_integral_le hK hFm hF0 hFA hFL q hy
  rw [hadj]
  have hdiff : (∫ y, (Erdos1002.gaussTransfer^[q]) F y * G y ∂Erdos1002.gaussMeasure)
        - (∫ x, F x ∂Erdos1002.gaussMeasure) * ∫ x, G x ∂Erdos1002.gaussMeasure
      = ∫ y, ((Erdos1002.gaussTransfer^[q]) F y - ∫ x, F x ∂Erdos1002.gaussMeasure)
          * G y ∂Erdos1002.gaussMeasure := by
    rw [← integral_const_mul, ← integral_sub hprodint (hGint.const_mul _)]
    exact integral_congr_ae (Eventually.of_forall (fun y => by ring))
  rw [hdiff, ← Real.norm_eq_abs]
  have hcst : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      ‖((Erdos1002.gaussTransfer^[q]) F y - ∫ x, F x ∂Erdos1002.gaussMeasure) * G y‖
        ≤ (527 / 540 : ℝ) ^ q * K * M := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0:ℝ) 1 := ⟨hy.1.le, hy.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hkey y hycc) (hGb y) (abs_nonneg _) (by positivity)
  calc ‖∫ y, ((Erdos1002.gaussTransfer^[q]) F y - ∫ x, F x ∂Erdos1002.gaussMeasure)
          * G y ∂Erdos1002.gaussMeasure‖
      ≤ (527 / 540 : ℝ) ^ q * K * M
          * (Erdos1002.gaussMeasure univ).toReal := norm_integral_le_of_norm_le_const hcst
    _ = (527 / 540 : ℝ) ^ q * K * M := by
        rw [measure_univ]
        simp

/-! ## 6. Mixing for coordinate-Lipschitz observables

The reduction proper.  Only the minimal regularity enters: `f` is
Lipschitz in the **future** coordinate (its past dependence is integrated
out exactly by `wProj`), and `g` is Lipschitz in the **past** coordinate
(its future argument `T^m x` is exact). -/

theorem integrable_of_ae_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {h : α → ℝ} (hm : Measurable h) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, |h x| ≤ C) : Integrable h μ :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (hb.mono (fun x hx => by rwa [Real.norm_eq_abs]))

/-- On a probability space, an a.e. bound on the pointwise difference
bounds the difference of the integrals. -/
theorem abs_integral_diff_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h₁ h₂ : α → ℝ} (hi1 : Integrable h₁ μ)
    (hi2 : Integrable h₂ μ) {C : ℝ} (hb : ∀ᵐ x ∂μ, |h₁ x - h₂ x| ≤ C) :
    |(∫ x, h₁ x ∂μ) - ∫ x, h₂ x ∂μ| ≤ C := by
  rw [← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  calc ‖∫ x, (h₁ x - h₂ x) ∂μ‖ ≤ C * (μ univ).toReal :=
        norm_integral_le_of_norm_le_const
          (hb.mono (fun x hx => by rwa [Real.norm_eq_abs]))
    _ = C := by rw [measure_univ]; simp

/-- The frozen-past comparison: changing the initial past coordinate from
`u` to `v` moves `g` of the `j`-step orbit by at most
`Lg · 2 (1/2)^j |u - v|`. -/
theorem frozen_past_diff_le {g : ℝ × ℝ → ℝ} {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hgLy : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y'⦄, y' ∈ Icc (0:ℝ) 1 → |g (x, y) - g (x, y')| ≤ Lg * |y - y'|)
    (j : ℕ) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) (hirr : Irrational x)
    {u v : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) :
    |g (natExtMap^[j] (x, u)) - g (natExtMap^[j] (x, v))|
      ≤ Lg * (2 * (1/2:ℝ) ^ j * |u - v|) := by
  have hfst : (natExtMap^[j] (x, v)).1 = (natExtMap^[j] (x, u)).1 := by
    rw [natExtMap_iterate_fst, natExtMap_iterate_fst]
  have hxj : (natExtMap^[j] (x, u)).1 ∈ Icc (0:ℝ) 1 := by
    rw [natExtMap_iterate_fst]
    exact Ioo_subset_Icc_self (gaussIter_mem_Ioo hx hirr j)
  have h1 : (natExtMap^[j] (x, u)).2 ∈ Icc (0:ℝ) 1 := iterate_snd_mem hx hirr hu j
  have h2 : (natExtMap^[j] (x, v)).2 ∈ Icc (0:ℝ) 1 := iterate_snd_mem hx hirr hv j
  have hsnd := iterate_snd_dist_le j hx hirr hu hv
  have hv_pair : natExtMap^[j] (x, v)
      = ((natExtMap^[j] (x, u)).1, (natExtMap^[j] (x, v)).2) := Prod.ext hfst rfl
  have hu_pair : natExtMap^[j] (x, u)
      = ((natExtMap^[j] (x, u)).1, (natExtMap^[j] (x, u)).2) := rfl
  calc |g (natExtMap^[j] (x, u)) - g (natExtMap^[j] (x, v))|
      = |g ((natExtMap^[j] (x, u)).1, (natExtMap^[j] (x, u)).2)
          - g ((natExtMap^[j] (x, u)).1, (natExtMap^[j] (x, v)).2)| := by
        rw [← hu_pair, ← hv_pair]
    _ ≤ Lg * |(natExtMap^[j] (x, u)).2 - (natExtMap^[j] (x, v)).2| := hgLy hxj h1 h2
    _ ≤ Lg * (2 * (1/2:ℝ) ^ j * |u - v|) := mul_le_mul_of_nonneg_left hsnd hLg

theorem abs_sub_le₄' (a b c d e : ℝ) :
    |a - e| ≤ |a - b| + |b - c| + |c - d| + |d - e| := by
  calc |a - e| ≤ |a - d| + |d - e| := abs_sub_le a d e
    _ ≤ (|a - c| + |c - d|) + |d - e| := by linarith [abs_sub_le a c d]
    _ ≤ ((|a - b| + |b - c|) + |c - d|) + |d - e| := by linarith [abs_sub_le a b c]
    _ = |a - b| + |b - c| + |c - d| + |d - e| := by ring

/-- **Quantitative mixing for coordinate-Lipschitz observables**: the
`ν̂`-correlation of `f` and `g ∘ σ^m` is within
`(2 Lf + 4 + 6 Lg) (527/540)^(m/2)` of the product of the means. -/
theorem lipschitz_mixing_le
    {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf01 : ∀ p, f p ∈ Icc (0:ℝ) 1) (hg01 : ∀ p, g p ∈ Icc (0:ℝ) 1)
    {Lf : ℝ} (hLf : 0 ≤ Lf)
    (hfLx : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃x'⦄, x' ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 → |f (x, y) - f (x', y)| ≤ Lf * |x - x'|)
    {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hgLy : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y'⦄, y' ∈ Icc (0:ℝ) 1 → |g (x, y) - g (x, y')| ≤ Lg * |y - y'|)
    (m : ℕ) :
    |(∫ p, f p * g (natExtMap^[m] p) ∂hatNu)
        - (∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu|
      ≤ (2 * Lf + 4 + 6 * Lg) * (527/540 : ℝ) ^ (m / 2) := by
  have hf1 : ∀ p, |f p| ≤ 1 := fun p =>
    abs_le.mpr ⟨by linarith [(hf01 p).1], (hf01 p).2⟩
  have hg1 : ∀ p, |g p| ≤ 1 := fun p =>
    abs_le.mpr ⟨by linarith [(hg01 p).1], (hg01 p).2⟩
  have hhalf : (1/2 : ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  set K := m / 2 with hKdef
  set q := m - m / 2 with hqdef
  have hKq : K + q = m := by omega
  have hKleq : K ≤ q := by omega
  have hKlem : K ≤ m := by omega
  have hσm : Measurable (natExtMap^[m]) := measurable_natExtMap.iterate m
  have hσK : Measurable (natExtMap^[K]) := measurable_natExtMap.iterate K
  -- the frozen-past observables
  set Gm : ℝ → ℝ := fun x => g (natExtMap^[m] (x, 1/2)) with hGmdef
  set hFn : ℝ → ℝ := fun x' => g (natExtMap^[K] (x', 1/2)) with hhFndef
  have hGmM : Measurable Gm :=
    hg.comp (hσm.comp (measurable_id.prodMk measurable_const))
  have hhFnM : Measurable hFn :=
    hg.comp (hσK.comp (measurable_id.prodMk measurable_const))
  have hGm1 : ∀ x, |Gm x| ≤ 1 := fun x => hg1 _
  have hhFn1 : ∀ x, |hFn x| ≤ 1 := fun x => hg1 _
  -- integrability workhorses
  have hint_fg : Integrable (fun p => f p * g (natExtMap^[m] p)) hatNu := by
    refine integrable_of_ae_abs_le (hf.mul (hg.comp hσm)) (C := 1)
      (Eventually.of_forall (fun p => ?_))
    rw [abs_mul]
    exact mul_le_one₀ (hf1 p) (abs_nonneg _) (hg1 _)
  have hint_fGm : Integrable (fun p => Gm p.1 * f p) hatNu := by
    refine integrable_of_ae_abs_le ((hGmM.comp measurable_fst).mul hf) (C := 1)
      (Eventually.of_forall (fun p => ?_))
    rw [abs_mul]
    exact mul_le_one₀ (hGm1 _) (abs_nonneg _) (hf1 p)
  have hwf01 : ∀ᵐ x ∂gaussMarginal, 0 ≤ wProj f x ∧ wProj f x ≤ 1 := by
    filter_upwards [gaussMarginal_ae_mem] with x hx
    exact ⟨wProj_nonneg hf01 (Ioo_subset_Icc_self hx),
      wProj_le_one hf hf01 (Ioo_subset_Icc_self hx)⟩
  have hint_wGm : Integrable (fun x => Gm x * wProj f x) gaussMarginal := by
    refine integrable_of_ae_abs_le (hGmM.mul (measurable_wProj hf)) (C := 1) ?_
    filter_upwards [hwf01] with x hx
    rw [abs_mul]
    exact mul_le_one₀ (hGm1 x) (abs_nonneg _) (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
  have hint_wh : Integrable
      (fun x => wProj f x * hFn (Erdos1002.gaussOrbit q x)) gaussMarginal := by
    refine integrable_of_ae_abs_le ((measurable_wProj hf).mul
      (hhFnM.comp (Erdos1002.measurable_gaussOrbit q))) (C := 1) ?_
    filter_upwards [hwf01] with x hx
    rw [abs_mul]
    exact mul_le_one₀ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩) (abs_nonneg _) (hhFn1 _)
  -- E1: freeze the past of `g` at `1/2`
  have hE1 : |(∫ p, f p * g (natExtMap^[m] p) ∂hatNu)
        - ∫ p, Gm p.1 * f p ∂hatNu|
      ≤ 2 * Lg * (1/2:ℝ) ^ m := by
    refine abs_integral_diff_le hint_fg hint_fGm ?_
    filter_upwards [hatNu_ae_good] with p hp
    obtain ⟨hx, hy, hirr⟩ := hp
    have hy' : p.2 ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hy
    have hgd := frozen_past_diff_le hLg hgLy m hx hirr hy' hhalf
    have hd2 : |p.2 - 1/2| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [hy.1]; linarith [hy.2]]
    have hfactor : f p * g (natExtMap^[m] p) - Gm p.1 * f p
        = f p * (g (natExtMap^[m] (p.1, p.2)) - g (natExtMap^[m] (p.1, 1/2))) := by
      rw [hGmdef]
      ring_nf
    rw [hfactor, abs_mul]
    calc |f p| * |g (natExtMap^[m] (p.1, p.2)) - g (natExtMap^[m] (p.1, 1/2))|
        ≤ 1 * (Lg * (2 * (1/2:ℝ) ^ m * |p.2 - 1/2|)) :=
          mul_le_mul (hf1 p) hgd (abs_nonneg _) one_pos.le
      _ ≤ 2 * Lg * (1/2:ℝ) ^ m := by
          rw [one_mul]
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) m, hd2,
            mul_nonneg hLg (pow_pos (by norm_num : (0:ℝ) < 1/2) m).le]
  -- E2: collapse the past of `f`
  have hE2 : ∫ p, Gm p.1 * f p ∂hatNu = ∫ x, Gm x * wProj f x ∂gaussMarginal :=
    integral_fst_mul_hatNu hGmM hGm1 hf hf01
  -- E3: truncate the past dependence of `Gm` to the top `K` digits
  have hE3 : |(∫ x, Gm x * wProj f x ∂gaussMarginal)
        - ∫ x, wProj f x * hFn (Erdos1002.gaussOrbit q x) ∂gaussMarginal|
      ≤ 2 * Lg * (1/2:ℝ) ^ K := by
    refine abs_integral_diff_le hint_wGm hint_wh ?_
    filter_upwards [gaussMarginal_ae_mem, gaussMarginal_ae_irrational, hwf01]
      with x hx hirr hwf
    have hsplit : natExtMap^[m] (x, (1:ℝ)/2)
        = natExtMap^[K] (natExtMap^[q] (x, (1:ℝ)/2)) := by
      rw [← hKq, Function.iterate_add_apply]
    have hXq : gaussIter x q ∈ Ioo (0:ℝ) 1 := gaussIter_mem_Ioo hx hirr q
    have hXirr : Irrational (gaussIter x q) := gaussIter_irrational hirr q
    have hYq : (natExtMap^[q] (x, (1:ℝ)/2)).2 ∈ Icc (0:ℝ) 1 :=
      iterate_snd_mem hx hirr hhalf q
    have hpair : natExtMap^[q] (x, (1:ℝ)/2)
        = (gaussIter x q, (natExtMap^[q] (x, (1:ℝ)/2)).2) :=
      Prod.ext (natExtMap_iterate_fst q (x, 1/2)) rfl
    have hgd : |Gm x - hFn (Erdos1002.gaussOrbit q x)| ≤ Lg * (2 * (1/2:ℝ) ^ K * 1) := by
      have horb : Erdos1002.gaussOrbit q x = gaussIter x q :=
        (gaussIter_eq_gaussOrbit x q).symm
      have h1 : Gm x = g (natExtMap^[K] (gaussIter x q, (natExtMap^[q] (x, (1:ℝ)/2)).2)) := by
        rw [hGmdef]
        simp only
        rw [hsplit, hpair]
      have h2 : hFn (Erdos1002.gaussOrbit q x)
          = g (natExtMap^[K] (gaussIter x q, (1:ℝ)/2)) := by
        rw [hhFndef, horb]
      rw [h1, h2]
      have := frozen_past_diff_le hLg hgLy K hXq hXirr hYq hhalf
      refine this.trans ?_
      have hd2 : |(natExtMap^[q] (x, (1:ℝ)/2)).2 - 1/2| ≤ 1 := by
        rw [abs_le]
        constructor <;> [linarith [hYq.1]; linarith [hYq.2]]
      have hnn : (0:ℝ) ≤ 2 * (1/2:ℝ) ^ K := by positivity
      refine mul_le_mul_of_nonneg_left ?_ hLg
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) K]
    have hfactor : Gm x * wProj f x - wProj f x * hFn (Erdos1002.gaussOrbit q x)
        = wProj f x * (Gm x - hFn (Erdos1002.gaussOrbit q x)) := by ring
    rw [hfactor, abs_mul]
    calc |wProj f x| * |Gm x - hFn (Erdos1002.gaussOrbit q x)|
        ≤ 1 * (Lg * (2 * (1/2:ℝ) ^ K * 1)) :=
          mul_le_mul (abs_le.mpr ⟨by linarith [hwf.1], hwf.2⟩) hgd (abs_nonneg _)
            one_pos.le
      _ = 2 * Lg * (1/2:ℝ) ^ K := by ring
  -- E4: the one-sided correlation decay at gap `q`
  have hE4 : |(∫ x, wProj f x * hFn (Erdos1002.gaussOrbit q x) ∂gaussMarginal)
        - (∫ x, wProj f x ∂gaussMarginal) * ∫ x, hFn x ∂gaussMarginal|
      ≤ (527/540 : ℝ) ^ q * (2 * Lf + 4) * 1 := by
    have h := gauss_correlation_le (A := 1) (K := 2 * Lf + 4) (by positivity)
      (measurable_wProj hf)
      (fun x hx => wProj_nonneg hf01 hx)
      (fun x hx => wProj_le_one hf hf01 hx)
      (wProj_lipschitz hf hf01 hLf hfLx)
      hhFnM (M := 1) hhFn1 q
    rwa [← gaussMarginal_eq_gaussMeasure] at h
  -- E5a: the mean of `wProj f` is the mean of `f`
  have hE5a : ∫ x, wProj f x ∂gaussMarginal = ∫ p, f p ∂hatNu := by
    have h := integral_fst_mul_hatNu (F := fun _ => (1:ℝ)) measurable_const
      (CF := 1) (fun x => by norm_num) hf hf01
    simpa using h.symm
  -- E5b: the mean of `hFn` is within `2 Lg (1/2)^K` of the mean of `g`
  have hE5b : |(∫ x, hFn x ∂gaussMarginal) - ∫ p, g p ∂hatNu|
      ≤ 2 * Lg * (1/2:ℝ) ^ K := by
    have htrans : ∫ x, hFn x ∂gaussMarginal = ∫ p, hFn p.1 ∂hatNu :=
      integral_gaussMarginal_eq_hatNu hhFnM
    have hmp : MeasurePreserving (natExtMap^[K]) hatNu hatNu :=
      NatExtInvariance.natExtMap_measurePreserving.iterate K
    have hinv : ∫ p, g (natExtMap^[K] p) ∂hatNu = ∫ p, g p ∂hatNu := by
      calc ∫ p, g (natExtMap^[K] p) ∂hatNu
          = ∫ y, g y ∂(hatNu.map (natExtMap^[K])) :=
            (integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable).symm
        _ = ∫ p, g p ∂hatNu := by rw [hmp.map_eq]
    rw [htrans, ← hinv]
    have hint1 : Integrable (fun p : ℝ × ℝ => hFn p.1) hatNu :=
      integrable_of_ae_abs_le (hhFnM.comp measurable_fst)
        (Eventually.of_forall (fun p => hhFn1 _))
    have hint2 : Integrable (fun p => g (natExtMap^[K] p)) hatNu :=
      integrable_of_ae_abs_le (hg.comp hσK) (Eventually.of_forall (fun p => hg1 _))
    refine abs_integral_diff_le hint1 hint2 ?_
    filter_upwards [hatNu_ae_good] with p hp
    obtain ⟨hx, hy, hirr⟩ := hp
    have hy' : p.2 ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hy
    have hgd := frozen_past_diff_le hLg hgLy K hx hirr hhalf hy'
    have hd2 : |1/2 - p.2| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [hy.2]; linarith [hy.1]]
    calc |hFn p.1 - g (natExtMap^[K] p)|
        = |g (natExtMap^[K] (p.1, 1/2)) - g (natExtMap^[K] (p.1, p.2))| := by rw [hhFndef]
      _ ≤ Lg * (2 * (1/2:ℝ) ^ K * |1/2 - p.2|) := hgd
      _ ≤ 2 * Lg * (1/2:ℝ) ^ K := by
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) K, hd2,
            mul_nonneg hLg (pow_pos (by norm_num : (0:ℝ) < 1/2) K).le]
  -- the mean of `f` lies in `[0,1]`
  have hcf : |∫ p, f p ∂hatNu| ≤ 1 := by
    rw [abs_of_nonneg (integral_nonneg (fun p => (hf01 p).1))]
    calc ∫ p, f p ∂hatNu ≤ ∫ _p, (1:ℝ) ∂hatNu := by
          refine integral_mono (integrable_of_ae_abs_le hf
            (Eventually.of_forall hf1)) (integrable_const 1) (fun p => (hf01 p).2)
      _ = 1 := by simp
  -- assemble
  have hchain : |(∫ p, f p * g (natExtMap^[m] p) ∂hatNu)
        - (∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu|
      ≤ 2 * Lg * (1/2:ℝ) ^ m + 2 * Lg * (1/2:ℝ) ^ K
        + (527/540 : ℝ) ^ q * (2 * Lf + 4) + 2 * Lg * (1/2:ℝ) ^ K := by
    have hlast : |(∫ x, wProj f x ∂gaussMarginal) * (∫ x, hFn x ∂gaussMarginal)
          - (∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu|
        ≤ 2 * Lg * (1/2:ℝ) ^ K := by
      rw [hE5a]
      have : (∫ p, f p ∂hatNu) * (∫ x, hFn x ∂gaussMarginal)
            - (∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu
          = (∫ p, f p ∂hatNu) * ((∫ x, hFn x ∂gaussMarginal) - ∫ p, g p ∂hatNu) := by
        ring
      rw [this, abs_mul]
      calc |∫ p, f p ∂hatNu| * |(∫ x, hFn x ∂gaussMarginal) - ∫ p, g p ∂hatNu|
          ≤ 1 * (2 * Lg * (1/2:ℝ) ^ K) :=
            mul_le_mul hcf hE5b (abs_nonneg _) one_pos.le
        _ = 2 * Lg * (1/2:ℝ) ^ K := one_mul _
    calc |(∫ p, f p * g (natExtMap^[m] p) ∂hatNu)
          - (∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu|
        ≤ |(∫ p, f p * g (natExtMap^[m] p) ∂hatNu) - ∫ p, Gm p.1 * f p ∂hatNu|
          + |(∫ p, Gm p.1 * f p ∂hatNu)
              - ∫ x, wProj f x * hFn (Erdos1002.gaussOrbit q x) ∂gaussMarginal|
          + |(∫ x, wProj f x * hFn (Erdos1002.gaussOrbit q x) ∂gaussMarginal)
              - (∫ x, wProj f x ∂gaussMarginal) * ∫ x, hFn x ∂gaussMarginal|
          + |(∫ x, wProj f x ∂gaussMarginal) * (∫ x, hFn x ∂gaussMarginal)
              - (∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu| := by
          exact abs_sub_le₄' _ _ _ _ _
      _ ≤ 2 * Lg * (1/2:ℝ) ^ m + 2 * Lg * (1/2:ℝ) ^ K
          + (527/540 : ℝ) ^ q * (2 * Lf + 4) + 2 * Lg * (1/2:ℝ) ^ K := by
          have hmid : |(∫ p, Gm p.1 * f p ∂hatNu)
              - ∫ x, wProj f x * hFn (Erdos1002.gaussOrbit q x) ∂gaussMarginal|
              ≤ 2 * Lg * (1/2:ℝ) ^ K := by
            rw [hE2]
            exact hE3
          have hE4' : |(∫ x, wProj f x * hFn (Erdos1002.gaussOrbit q x) ∂gaussMarginal)
              - (∫ x, wProj f x ∂gaussMarginal) * ∫ x, hFn x ∂gaussMarginal|
              ≤ (527/540 : ℝ) ^ q * (2 * Lf + 4) := by
            calc _ ≤ (527/540 : ℝ) ^ q * (2 * Lf + 4) * 1 := hE4
              _ = (527/540 : ℝ) ^ q * (2 * Lf + 4) := mul_one _
          exact add_le_add (add_le_add (add_le_add hE1 hmid) hE4') hlast
  refine hchain.trans ?_
  -- the four error terms are each dominated by `(527/540)^(m/2)`
  have hr01 : (0:ℝ) ≤ 527/540 := by norm_num
  have hr1 : (527/540 : ℝ) ≤ 1 := by norm_num
  have hhalfr : (1/2 : ℝ) ≤ 527/540 := by norm_num
  have hpm : (1/2:ℝ) ^ m ≤ (527/540 : ℝ) ^ K :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKlem).trans
      (pow_le_pow_left₀ (by norm_num) hhalfr K)
  have hpK : (1/2:ℝ) ^ K ≤ (527/540 : ℝ) ^ K := pow_le_pow_left₀ (by norm_num) hhalfr K
  have hpq : (527/540:ℝ) ^ q ≤ (527/540 : ℝ) ^ K := pow_le_pow_of_le_one hr01 hr1 hKleq
  have hRnn : (0:ℝ) ≤ (527/540 : ℝ) ^ K := by positivity
  calc 2 * Lg * (1/2:ℝ) ^ m + 2 * Lg * (1/2:ℝ) ^ K
        + (527/540 : ℝ) ^ q * (2 * Lf + 4) + 2 * Lg * (1/2:ℝ) ^ K
      ≤ 2 * Lg * (527/540 : ℝ) ^ K + 2 * Lg * (527/540 : ℝ) ^ K
        + (527/540 : ℝ) ^ K * (2 * Lf + 4) + 2 * Lg * (527/540 : ℝ) ^ K := by
        refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
        · exact mul_le_mul_of_nonneg_left hpm (by positivity)
        · exact mul_le_mul_of_nonneg_left hpK (by positivity)
        · exact mul_le_mul_of_nonneg_right hpq (by positivity)
        · exact mul_le_mul_of_nonneg_left hpK (by positivity)
    _ = (2 * Lf + 4 + 6 * Lg) * (527/540 : ℝ) ^ K := by ring

/-- **Mixing for coordinate-Lipschitz observables.** -/
theorem lipschitz_mixing
    {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf01 : ∀ p, f p ∈ Icc (0:ℝ) 1) (hg01 : ∀ p, g p ∈ Icc (0:ℝ) 1)
    {Lf : ℝ} (hLf : 0 ≤ Lf)
    (hfLx : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃x'⦄, x' ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 → |f (x, y) - f (x', y)| ≤ Lf * |x - x'|)
    {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hgLy : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y'⦄, y' ∈ Icc (0:ℝ) 1 → |g (x, y) - g (x, y')| ≤ Lg * |y - y'|) :
    Tendsto (fun m => ∫ p, f p * g (natExtMap^[m] p) ∂hatNu) atTop
      (𝓝 ((∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hb : ∀ m : ℕ, ‖(∫ p, f p * g (natExtMap^[m] p) ∂hatNu)
        - (∫ p, f p ∂hatNu) * ∫ p, g p ∂hatNu‖
      ≤ (2 * Lf + 4 + 6 * Lg) * (527/540 : ℝ) ^ (m / 2) := fun m => by
    rw [Real.norm_eq_abs]
    exact lipschitz_mixing_le hf hg hf01 hg01 hLf hfLx hLg hgLy m
  have h1 : Tendsto (fun n : ℕ => (527/540 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Tendsto (fun m : ℕ => m / 2) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr (fun b => ⟨2 * b, fun a ha => ?_⟩)
    omega
  have h4 := (h1.comp h2).const_mul (2 * Lf + 4 + 6 * Lg)
  rw [mul_zero] at h4
  exact squeeze_zero_norm hb h4

/-! ## 7. Lipschitz approximation of indicators

`ν̂` is a finite Borel measure on the metric space `ℝ²`, hence inner
regular by closed sets (`MeasurableSet.exists_isClosed_diff_lt`); a closed
`F` is approximated from outside by its `δ`-thickening
(`tendsto_measure_thickening_of_isClosed`), and
`p ↦ max 0 (1 - infDist(p,F)/δ)` is a `[0,1]`-valued `(1/δ)`-Lipschitz
function equal to `1` on `F` and `0` outside the thickening. -/

/-- `integral_indicator_one`, with the indicator's constant written as an
explicit lambda (the numeral-`1` function and the lambda are the same term
definitionally but not syntactically). -/
theorem integral_indicator_one_hatNu {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    ∫ p, S.indicator (fun _ => (1:ℝ)) p ∂hatNu = hatNu.real S := by
  rw [show (S.indicator (fun _ => (1:ℝ))) = S.indicator 1 from rfl]
  exact integral_indicator_one hS

theorem exists_lipschitz_approx {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ × ℝ → ℝ, ∃ L : ℝ, 0 ≤ L ∧ Measurable φ ∧ (∀ p, φ p ∈ Icc (0:ℝ) 1) ∧
      (∀ p q : ℝ × ℝ, |φ p - φ q| ≤ L * dist p q) ∧
      ∫ p, |A.indicator (fun _ => (1:ℝ)) p - φ p| ∂hatNu ≤ ε := by
  have hhalf : (0:ℝ) < ε / 2 := half_pos hε
  obtain ⟨F, hFA, hFc, hFd⟩ := hA.exists_isClosed_diff_lt (measure_ne_top hatNu A)
    (ε := ENNReal.ofReal (ε/2)) (by simp [ENNReal.ofReal_eq_zero]; linarith)
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · -- the closed set is empty: `A` itself has small measure, take `φ = 0`
    refine ⟨fun _ => 0, 0, le_refl 0, measurable_const,
      fun p => ⟨le_refl 0, zero_le_one⟩, fun p q => by simp, ?_⟩
    have hAsmall : hatNu A < ENNReal.ofReal (ε/2) := by simpa using hFd
    have hcalc : ∫ p, |A.indicator (fun _ => (1:ℝ)) p - 0| ∂hatNu = hatNu.real A := by
      rw [← integral_indicator_one_hatNu hA]
      refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
      by_cases h : p ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [hcalc, measureReal_def]
    have := ENNReal.toReal_le_of_le_ofReal hhalf.le hAsmall.le
    linarith
  · -- pick a thickening of `F` of nearly the same measure
    have htend := tendsto_measure_thickening_of_isClosed
      (μ := hatNu) ⟨1, one_pos, measure_ne_top _ _⟩ hFc
    have hlt : hatNu F < hatNu F + ENNReal.ofReal (ε/2) :=
      ENNReal.lt_add_right (measure_ne_top _ _)
        (by simp [ENNReal.ofReal_eq_zero]; linarith)
    have hev := htend.eventually_lt_const hlt
    obtain ⟨δ, hδsmall, hδpos⟩ := (hev.and eventually_mem_nhdsWithin).exists
    rw [Set.mem_Ioi] at hδpos
    have hthin : hatNu (thickening δ F \ F) < ENNReal.ofReal (ε/2) :=
      measure_diff_lt_of_lt_add hFc.nullMeasurableSet
        (self_subset_thickening hδpos F) (measure_ne_top _ _) hδsmall
    -- the wedge function
    set φ : ℝ × ℝ → ℝ := fun p => max 0 (1 - infDist p F / δ) with hφdef
    have hφmem : ∀ p, φ p ∈ Icc (0:ℝ) 1 := by
      intro p
      constructor
      · exact le_max_left _ _
      · refine max_le zero_le_one ?_
        have h1 : 0 ≤ infDist p F / δ := div_nonneg infDist_nonneg hδpos.le
        linarith
    have hφcont : Continuous φ := by
      refine continuous_const.max ?_
      exact continuous_const.sub ((continuous_infDist_pt F).div_const δ)
    have hφlip : ∀ p q : ℝ × ℝ, |φ p - φ q| ≤ (1/δ) * dist p q := by
      intro p q
      have h1 : |φ p - φ q|
          ≤ |(1 - infDist p F / δ) - (1 - infDist q F / δ)| := by
        rw [hφdef]
        simp only
        rw [max_comm 0 (1 - infDist p F / δ), max_comm 0 (1 - infDist q F / δ)]
        exact abs_max_sub_max_le_abs _ _ _
      have h2 : (1 - infDist p F / δ) - (1 - infDist q F / δ)
          = (infDist q F - infDist p F) / δ := by ring
      have h3 : |infDist q F - infDist p F| ≤ dist p q := by
        rw [abs_sub_le_iff]
        constructor
        · have := infDist_le_infDist_add_dist (x := q) (y := p) (s := F)
          rw [dist_comm q p] at this
          linarith
        · have := infDist_le_infDist_add_dist (x := p) (y := q) (s := F)
          linarith
      calc |φ p - φ q| ≤ |(infDist q F - infDist p F) / δ| := by rw [← h2]; exact h1
        _ = |infDist q F - infDist p F| / δ := by
            rw [abs_div, abs_of_pos hδpos]
        _ ≤ dist p q / δ := by gcongr
        _ = (1/δ) * dist p q := by ring
    -- `φ = 1` on `F`, `φ = 0` off the thickening
    have hφone : ∀ p ∈ F, φ p = 1 := by
      intro p hp
      rw [hφdef]
      simp only
      rw [infDist_zero_of_mem hp]
      norm_num
    have hφsupp : ∀ p, p ∉ thickening δ F → φ p = 0 := by
      intro p hp
      rw [hφdef]
      simp only
      have hd : δ ≤ infDist p F := by
        by_contra hcon
        push_neg at hcon
        exact hp ((mem_thickening_iff_infDist_lt hFne).mpr hcon)
      have h1 : (1:ℝ) ≤ infDist p F / δ := (one_le_div hδpos).mpr hd
      exact max_eq_left (by linarith)
    -- pointwise domination by the small exceptional set
    set U : Set (ℝ × ℝ) := (A \ F) ∪ (thickening δ F \ F) with hUdef
    have hUmeas : MeasurableSet U := (hA.diff hFc.measurableSet).union
      (isOpen_thickening.measurableSet.diff hFc.measurableSet)
    have hUnn : ∀ p, (0:ℝ) ≤ U.indicator (fun _ => (1:ℝ)) p :=
      fun p => Set.indicator_nonneg (fun _ _ => zero_le_one) p
    have hpt : ∀ p, |A.indicator (fun _ => (1:ℝ)) p - φ p| ≤ U.indicator (fun _ => (1:ℝ)) p := by
      intro p
      by_cases hpF : p ∈ F
      · have h0 : |A.indicator (fun _ => (1:ℝ)) p - φ p| = 0 := by
          rw [Set.indicator_of_mem (hFA hpF), hφone p hpF]
          simp
        rw [h0]
        exact hUnn p
      · by_cases hpA : p ∈ A
        · have hU : p ∈ U := Or.inl ⟨hpA, hpF⟩
          rw [Set.indicator_of_mem hU, Set.indicator_of_mem hpA]
          have hm := hφmem p
          rw [abs_le]
          constructor
          · linarith [hm.2]
          · linarith [hm.1]
        · by_cases hpT : p ∈ thickening δ F
          · have hU : p ∈ U := Or.inr ⟨hpT, hpF⟩
            rw [Set.indicator_of_mem hU, Set.indicator_of_notMem hpA]
            have hm := hφmem p
            rw [zero_sub, abs_neg, abs_of_nonneg hm.1]
            exact hm.2
          · have h0 : φ p = 0 := hφsupp p hpT
            rw [Set.indicator_of_notMem hpA, h0]
            simp only [sub_zero, abs_zero]
            exact hUnn p
    -- integrate the domination
    have hint1 : Integrable (fun p => |A.indicator (fun _ => (1:ℝ)) p - φ p|) hatNu := by
      refine integrable_of_ae_abs_le
        (((measurable_const.indicator hA).sub hφcont.measurable).abs) (C := 2)
        (Eventually.of_forall (fun p => ?_))
      rw [abs_abs]
      have hm := hφmem p
      have hi : A.indicator (fun _ => (1:ℝ)) p = 1 ∨ A.indicator (fun _ => (1:ℝ)) p = 0 := by
        by_cases h : p ∈ A
        · left; simp [Set.indicator_of_mem h]
        · right; simp [Set.indicator_of_notMem h]
      rcases hi with hi | hi <;> rw [hi, abs_le] <;> constructor <;>
        [linarith [hm.2]; linarith [hm.1]; linarith [hm.2]; linarith [hm.1]]
    have hint2 : Integrable (fun p => U.indicator (fun _ => (1:ℝ)) p) hatNu := by
      refine integrable_of_ae_abs_le (measurable_const.indicator hUmeas) (C := 1)
        (Eventually.of_forall (fun p => ?_))
      rw [abs_of_nonneg (hUnn p)]
      by_cases h : p ∈ U <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have hle : ∫ p, |A.indicator (fun _ => (1:ℝ)) p - φ p| ∂hatNu ≤ hatNu.real U := by
      rw [← integral_indicator_one_hatNu hUmeas]
      exact integral_mono hint1 hint2 hpt
    have hUsmall : hatNu U < ENNReal.ofReal ε := by
      calc hatNu U ≤ hatNu (A \ F) + hatNu (thickening δ F \ F) := measure_union_le _ _
        _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add hFd hthin
        _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
            norm_num
    refine ⟨φ, 1/δ, by positivity, hφcont.measurable, hφmem, hφlip, ?_⟩
    refine hle.trans ?_
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hUsmall.le

/-! ## 8. From Lipschitz observables to indicators: the zero-mode mixing -/

/-- Correlation of indicators is the measure of the intersection. -/
theorem hatNuReal_inter_eq (A B : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (m : ℕ) :
    hatNu.real (A ∩ natExtMap^[m] ⁻¹' B)
      = ∫ p, A.indicator (fun _ => (1:ℝ)) p
          * B.indicator (fun _ => (1:ℝ)) (natExtMap^[m] p) ∂hatNu := by
  rw [← integral_indicator_one_hatNu (hA.inter (measurable_natExtMap.iterate m hB))]
  refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
  by_cases h1 : p ∈ A <;> by_cases h2 : natExtMap^[m] p ∈ B <;>
    simp [Set.mem_inter_iff, Set.mem_preimage, h1, h2]

/-- Push-forward invariance of `ν̂`-integrals along the iterated map. -/
theorem integral_comp_iterate {h : ℝ × ℝ → ℝ} (hm : Measurable h) (K : ℕ) :
    ∫ p, h (natExtMap^[K] p) ∂hatNu = ∫ p, h p ∂hatNu := by
  have hmp : MeasurePreserving (natExtMap^[K]) hatNu hatNu :=
    NatExtInvariance.natExtMap_measurePreserving.iterate K
  calc ∫ p, h (natExtMap^[K] p) ∂hatNu
      = ∫ y, h y ∂(hatNu.map (natExtMap^[K])) :=
        (integral_map hmp.measurable.aemeasurable hm.aestronglyMeasurable).symm
    _ = ∫ p, h p ∂hatNu := by rw [hmp.map_eq]

theorem abs_integral_le_hatNu (h : ℝ × ℝ → ℝ) :
    |∫ p, h p ∂hatNu| ≤ ∫ p, |h p| ∂hatNu := by
  calc |∫ p, h p ∂hatNu| = ‖∫ p, h p ∂hatNu‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ p, ‖h p‖ ∂hatNu := norm_integral_le_integral_norm _
    _ = ∫ p, |h p| ∂hatNu := by simp only [Real.norm_eq_abs]

/-- Replacing the left factor of a `ν̂`-correlation costs at most the `L¹`
distance, as long as the right factor is bounded by `1`. -/
theorem corr_left_diff_le {u u' v : ℝ × ℝ → ℝ}
    (hu : Measurable u) (hu' : Measurable u') (hv : Measurable v)
    (hub : ∀ p, |u p| ≤ 1) (hub' : ∀ p, |u' p| ≤ 1) (hvb : ∀ p, |v p| ≤ 1) :
    |(∫ p, u p * v p ∂hatNu) - ∫ p, u' p * v p ∂hatNu|
      ≤ ∫ p, |u p - u' p| ∂hatNu := by
  have hi1 : Integrable (fun p => u p * v p) hatNu :=
    integrable_of_ae_abs_le (hu.mul hv) (Eventually.of_forall (fun p => by
      rw [abs_mul]
      exact mul_le_one₀ (hub p) (abs_nonneg _) (hvb p)))
  have hi2 : Integrable (fun p => u' p * v p) hatNu :=
    integrable_of_ae_abs_le (hu'.mul hv) (Eventually.of_forall (fun p => by
      rw [abs_mul]
      exact mul_le_one₀ (hub' p) (abs_nonneg _) (hvb p)))
  rw [← integral_sub hi1 hi2]
  refine (abs_integral_le_hatNu _).trans ?_
  refine integral_mono ((hi1.sub hi2).abs) ?_ (fun p => ?_)
  · exact integrable_of_ae_abs_le ((hu.sub hu').abs) (C := 2)
      (Eventually.of_forall (fun p => by
        rw [abs_abs]
        calc |u p - u' p| ≤ |u p| + |u' p| := abs_sub _ _
          _ ≤ 2 := by linarith [hub p, hub' p]))
  · calc |u p * v p - u' p * v p| = |(u p - u' p) * v p| := by ring_nf
      _ = |u p - u' p| * |v p| := abs_mul _ _
      _ ≤ |u p - u' p| := mul_le_of_le_one_right (abs_nonneg _) (hvb p)

/-- **The zero-mode mixing of the Gauss natural extension**: for all
measurable `A, B ⊆ ℝ²`, `ν̂(A ∩ σ⁻ᵐ B) → ν̂(A) ν̂(B)`.  This is the
statement `Kwon1002.Lemma62.natExt_zero_mode_mixing` delegates to. -/
theorem natExt_zero_mode_mixing (A B : Set (ℝ × ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun m : ℕ => hatNu.real (A ∩ natExtMap^[m] ⁻¹' B))
      atTop (𝓝 (hatNu.real A * hatNu.real B)) := by
  set IA : ℝ × ℝ → ℝ := A.indicator (fun _ => (1:ℝ)) with hIAdef
  set IB : ℝ × ℝ → ℝ := B.indicator (fun _ => (1:ℝ)) with hIBdef
  have hIAm : Measurable IA := measurable_const.indicator hA
  have hIBm : Measurable IB := measurable_const.indicator hB
  have hIA01 : ∀ p, IA p ∈ Icc (0:ℝ) 1 := by
    intro p
    rw [hIAdef]
    by_cases h : p ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hIB01 : ∀ p, IB p ∈ Icc (0:ℝ) 1 := by
    intro p
    rw [hIBdef]
    by_cases h : p ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hIA1 : ∀ p, |IA p| ≤ 1 := fun p =>
    abs_le.mpr ⟨by linarith [(hIA01 p).1], (hIA01 p).2⟩
  have hIB1 : ∀ p, |IB p| ≤ 1 := fun p =>
    abs_le.mpr ⟨by linarith [(hIB01 p).1], (hIB01 p).2⟩
  -- rewrite the sequence and the limit through indicator integrals
  have hfun : (fun m : ℕ => hatNu.real (A ∩ natExtMap^[m] ⁻¹' B))
      = fun m => ∫ p, IA p * IB (natExtMap^[m] p) ∂hatNu :=
    funext (fun m => hatNuReal_inter_eq A B hA hB m)
  have htA : hatNu.real A = ∫ p, IA p ∂hatNu := (integral_indicator_one_hatNu hA).symm
  have htB : hatNu.real B = ∫ p, IB p ∂hatNu := (integral_indicator_one_hatNu hB).symm
  rw [hfun, htA, htB]
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Lipschitz approximants at level `ε/8`
  obtain ⟨φ, Lφ, hLφ0, hφm, hφ01, hφlip, hφerr⟩ :=
    exists_lipschitz_approx hA (ε := ε/8) (by linarith)
  obtain ⟨ψ, Lψ, hLψ0, hψm, hψ01, hψlip, hψerr⟩ :=
    exists_lipschitz_approx hB (ε := ε/8) (by linarith)
  have hφ1 : ∀ p, |φ p| ≤ 1 := fun p =>
    abs_le.mpr ⟨by linarith [(hφ01 p).1], (hφ01 p).2⟩
  have hψ1 : ∀ p, |ψ p| ≤ 1 := fun p =>
    abs_le.mpr ⟨by linarith [(hψ01 p).1], (hψ01 p).2⟩
  -- coordinate Lipschitz bounds from the metric ones
  have hφLx : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃x'⦄, x' ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 → |φ (x, y) - φ (x', y)| ≤ Lφ * |x - x'| := by
    intro x _ x' _ y _
    have h := hφlip (x, y) (x', y)
    rwa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq] at h
  have hψLy : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → ∀ ⦃y⦄, y ∈ Icc (0:ℝ) 1 →
      ∀ ⦃y'⦄, y' ∈ Icc (0:ℝ) 1 → |ψ (x, y) - ψ (x, y')| ≤ Lψ * |y - y'| := by
    intro x _ y _ y' _
    have h := hψlip (x, y) (x, y')
    rwa [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq] at h
  -- mixing for the approximants
  have hmix := lipschitz_mixing hφm hψm hφ01 hψ01 hLφ0 hφLx hLψ0 hψLy
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmix) (ε/2) (by linarith)
  refine ⟨N, fun m hm => ?_⟩
  have hNm := hN m hm
  rw [Real.dist_eq] at hNm ⊢
  -- the error pieces
  have hσm : Measurable (natExtMap^[m]) := measurable_natExtMap.iterate m
  have heA : ∫ p, |IA p - φ p| ∂hatNu ≤ ε/8 := hφerr
  have heB : ∫ p, |IB p - ψ p| ∂hatNu ≤ ε/8 := hψerr
  -- (i) replace `IA` by `φ` against the shifted `IB`
  have h1 : |(∫ p, IA p * IB (natExtMap^[m] p) ∂hatNu)
        - ∫ p, φ p * IB (natExtMap^[m] p) ∂hatNu| ≤ ε/8 :=
    (corr_left_diff_le hIAm hφm (hIBm.comp hσm) hIA1 hφ1 (fun p => hIB1 _)).trans heA
  -- (ii) replace the shifted `IB` by the shifted `ψ` against `φ`
  have h2 : |(∫ p, φ p * IB (natExtMap^[m] p) ∂hatNu)
        - ∫ p, φ p * ψ (natExtMap^[m] p) ∂hatNu| ≤ ε/8 := by
    have hc1 : ∫ p, φ p * IB (natExtMap^[m] p) ∂hatNu
        = ∫ p, IB (natExtMap^[m] p) * φ p ∂hatNu :=
      integral_congr_ae (Eventually.of_forall (fun p => mul_comm _ _))
    have hc2 : ∫ p, φ p * ψ (natExtMap^[m] p) ∂hatNu
        = ∫ p, ψ (natExtMap^[m] p) * φ p ∂hatNu :=
      integral_congr_ae (Eventually.of_forall (fun p => mul_comm _ _))
    rw [hc1, hc2]
    refine (corr_left_diff_le (u := fun p => IB (natExtMap^[m] p))
      (u' := fun p => ψ (natExtMap^[m] p)) (v := φ)
      (hIBm.comp hσm) (hψm.comp hσm) hφm
      (fun p => hIB1 _) (fun p => hψ1 _) hφ1).trans ?_
    have hinv : ∫ p, |IB (natExtMap^[m] p) - ψ (natExtMap^[m] p)| ∂hatNu
        = ∫ p, |IB p - ψ p| ∂hatNu :=
      integral_comp_iterate ((hIBm.sub hψm).abs) m
    rw [hinv]
    exact heB
  -- (iii) the product of the means moves by at most `ε/8 + ε/8`
  have hIAint : Integrable IA hatNu :=
    integrable_of_ae_abs_le hIAm (Eventually.of_forall hIA1)
  have hIBint : Integrable IB hatNu :=
    integrable_of_ae_abs_le hIBm (Eventually.of_forall hIB1)
  have hφint : Integrable φ hatNu :=
    integrable_of_ae_abs_le hφm (Eventually.of_forall hφ1)
  have hψint : Integrable ψ hatNu :=
    integrable_of_ae_abs_le hψm (Eventually.of_forall hψ1)
  have hmeanA : |(∫ p, IA p ∂hatNu) - ∫ p, φ p ∂hatNu| ≤ ε/8 := by
    rw [← integral_sub hIAint hφint]
    exact (abs_integral_le_hatNu _).trans heA
  have hmeanB : |(∫ p, IB p ∂hatNu) - ∫ p, ψ p ∂hatNu| ≤ ε/8 := by
    rw [← integral_sub hIBint hψint]
    exact (abs_integral_le_hatNu _).trans heB
  have habs_mean : ∀ {h : ℝ × ℝ → ℝ}, Integrable h hatNu → (∀ p, |h p| ≤ 1) →
      |∫ p, h p ∂hatNu| ≤ 1 := by
    intro h hint hb
    refine (abs_integral_le_hatNu h).trans ?_
    calc ∫ p, |h p| ∂hatNu ≤ ∫ _p, (1:ℝ) ∂hatNu :=
          integral_mono hint.abs (integrable_const 1) hb
      _ = 1 := by simp
  have h3 : |(∫ p, IA p ∂hatNu) * (∫ p, IB p ∂hatNu)
        - (∫ p, φ p ∂hatNu) * ∫ p, ψ p ∂hatNu| ≤ ε/8 + ε/8 := by
    have hsplit : (∫ p, IA p ∂hatNu) * (∫ p, IB p ∂hatNu)
          - (∫ p, φ p ∂hatNu) * ∫ p, ψ p ∂hatNu
        = ((∫ p, IA p ∂hatNu) - ∫ p, φ p ∂hatNu) * (∫ p, IB p ∂hatNu)
          + (∫ p, φ p ∂hatNu) * ((∫ p, IB p ∂hatNu) - ∫ p, ψ p ∂hatNu) := by
      ring
    rw [hsplit]
    calc |((∫ p, IA p ∂hatNu) - ∫ p, φ p ∂hatNu) * (∫ p, IB p ∂hatNu)
          + (∫ p, φ p ∂hatNu) * ((∫ p, IB p ∂hatNu) - ∫ p, ψ p ∂hatNu)|
        ≤ |((∫ p, IA p ∂hatNu) - ∫ p, φ p ∂hatNu) * (∫ p, IB p ∂hatNu)|
          + |(∫ p, φ p ∂hatNu) * ((∫ p, IB p ∂hatNu) - ∫ p, ψ p ∂hatNu)| :=
          abs_add_le _ _
      _ = |(∫ p, IA p ∂hatNu) - ∫ p, φ p ∂hatNu| * |∫ p, IB p ∂hatNu|
          + |∫ p, φ p ∂hatNu| * |(∫ p, IB p ∂hatNu) - ∫ p, ψ p ∂hatNu| := by
          rw [abs_mul, abs_mul]
      _ ≤ (ε/8) * 1 + 1 * (ε/8) := by
          refine add_le_add (mul_le_mul hmeanA (habs_mean hIBint hIB1) (abs_nonneg _)
            (by linarith)) (mul_le_mul (habs_mean hφint hφ1) hmeanB (abs_nonneg _)
            zero_le_one)
      _ = ε/8 + ε/8 := by ring
  -- assemble
  calc |(∫ p, IA p * IB (natExtMap^[m] p) ∂hatNu)
        - (∫ p, IA p ∂hatNu) * ∫ p, IB p ∂hatNu|
      ≤ |(∫ p, IA p * IB (natExtMap^[m] p) ∂hatNu)
            - ∫ p, φ p * IB (natExtMap^[m] p) ∂hatNu|
        + |(∫ p, φ p * IB (natExtMap^[m] p) ∂hatNu)
            - ∫ p, φ p * ψ (natExtMap^[m] p) ∂hatNu|
        + |(∫ p, φ p * ψ (natExtMap^[m] p) ∂hatNu)
            - (∫ p, φ p ∂hatNu) * ∫ p, ψ p ∂hatNu|
        + |(∫ p, φ p ∂hatNu) * (∫ p, ψ p ∂hatNu)
            - (∫ p, IA p ∂hatNu) * ∫ p, IB p ∂hatNu| :=
        abs_sub_le₄' _ _ _ _ _
    _ < ε := by
        have h3' : |(∫ p, φ p ∂hatNu) * (∫ p, ψ p ∂hatNu)
              - (∫ p, IA p ∂hatNu) * ∫ p, IB p ∂hatNu| ≤ ε/8 + ε/8 := by
          rw [abs_sub_comm]
          exact h3
        linarith [h1, h2, hNm, h3']

end

end NatExtMixing

end Kwon1002
