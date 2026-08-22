import Kwon1002.WindowCovariance

/-!
# From tail quasi-independence to decorrelation, at a pair

`Kwon1002.MultiLevel.multiLevel_transfer` — proved, at every arity, with rate
`L^{-A}` for free `A` — is a statement about the `α`-average of a **product of
indicators**.  `Kwon1002.WindowCov.abs_far_sharp_of_det_pair_decay` needs a
statement about the covariance of two **bounded observables**.  This module
supplies the device that converts the first currency into the second.

The classical route is the layer-cake identity
`Cov(f,g) = ∫∫ [P(f>s, g>t) − P(f>s)P(g>t)] ds dt`, which costs a two-fold
Fubini over a triple product.  The route taken here is the discrete one: the
step approximation

  `S_N x = (M/N)·Σ_{i<N} 1{(i+1)M/N < x}`

is within `2M/N` of `x` uniformly on `[0,M]`, and a covariance of two such step
functions is a **finite** double sum of indicator covariances.  So the whole
argument is finite sums and linearity, with a single limit `N → ∞` at the end,
and no product measure appears anywhere.

`abs_cov_le_of_indicator_cov` is the result: if every pair of tail events at
levels `s, t` decorrelates to within `K`, then `|Cov(f,g)| ≤ M²·K`.  No
hypothesis is placed on the joint law beyond that.
-/

open Filter MeasureTheory Set

namespace Kwon1002

namespace PairLayerCake

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The tail indicator at level `s`. -/
def tailInd (f : Ω → ℝ) (s : ℝ) : Ω → ℝ := fun ω => if s < f ω then (1 : ℝ) else 0

lemma measurable_tailInd {f : Ω → ℝ} (hf : Measurable f) (s : ℝ) :
    Measurable (tailInd f s) := by
  unfold tailInd
  exact Measurable.ite (measurableSet_lt measurable_const hf) measurable_const measurable_const

lemma tailInd_nonneg (f : Ω → ℝ) (s : ℝ) (ω : Ω) : 0 ≤ tailInd f s ω := by
  unfold tailInd; split_ifs <;> norm_num

lemma tailInd_le_one (f : Ω → ℝ) (s : ℝ) (ω : Ω) : tailInd f s ω ≤ 1 := by
  unfold tailInd; split_ifs <;> norm_num

lemma abs_tailInd_le_one (f : Ω → ℝ) (s : ℝ) (ω : Ω) : |tailInd f s ω| ≤ 1 := by
  rw [abs_of_nonneg (tailInd_nonneg f s ω)]; exact tailInd_le_one f s ω

/-! ## The grid count

`#{i < N : (i+1)δ < x}` is within `2` of `x/δ` whenever `0 ≤ x ≤ Nδ`.  Both
bounds are inclusions of the filter between two initial segments. -/

lemma card_grid_le (δ x : ℝ) (hδ : 0 < δ) (hx0 : 0 ≤ x) (N : ℕ) :
    ((((Finset.range N).filter (fun i : ℕ => ((i : ℝ) + 1) * δ < x)).card : ℕ) : ℝ)
      ≤ x / δ := by
  classical
  have hxδ : (0 : ℝ) ≤ x / δ := by positivity
  have hsub : (Finset.range N).filter (fun i : ℕ => ((i : ℝ) + 1) * δ < x)
      ⊆ Finset.range ⌊x / δ⌋₊ := by
    intro i hi
    have hlt := (Finset.mem_filter.mp hi).2
    have h1 : ((i : ℝ) + 1) < x / δ := by rw [lt_div_iff₀ hδ]; linarith
    have h2 : ((i + 1 : ℕ) : ℝ) ≤ x / δ := by push_cast; linarith
    have h3 : i + 1 ≤ ⌊x / δ⌋₊ := Nat.le_floor h2
    exact Finset.mem_range.mpr (by omega)
  have h := Finset.card_le_card hsub
  rw [Finset.card_range] at h
  have hfl : ((⌊x / δ⌋₊ : ℕ) : ℝ) ≤ x / δ := Nat.floor_le hxδ
  have hcast := (Nat.cast_le (α := ℝ)).mpr h
  linarith

lemma le_card_grid (δ x : ℝ) (hδ : 0 < δ) (hx0 : 0 ≤ x) (N : ℕ) (hxN : x ≤ (N : ℝ) * δ) :
    x / δ - 2
      ≤ ((((Finset.range N).filter (fun i : ℕ => ((i : ℝ) + 1) * δ < x)).card : ℕ) : ℝ) := by
  classical
  have hxδ : (0 : ℝ) ≤ x / δ := by positivity
  set m : ℕ := ⌊x / δ⌋₊ with hm
  have hmN : m ≤ N := by
    have h1 : x / δ ≤ (N : ℝ) := by rw [div_le_iff₀ hδ]; linarith
    have h2 := Nat.floor_le_floor h1
    simpa [hm, Nat.floor_natCast] using h2
  have hsuper : Finset.range (m - 1)
      ⊆ (Finset.range N).filter (fun i : ℕ => ((i : ℝ) + 1) * δ < x) := by
    intro i hi
    have hilt : i < m - 1 := Finset.mem_range.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have hcast : ((i : ℝ) + 1) < (m : ℝ) := by
      have hii : i + 1 < m := by omega
      exact_mod_cast hii
    have hfl : (m : ℝ) ≤ x / δ := Nat.floor_le hxδ
    have hkey : ((i : ℝ) + 1) < x / δ := lt_of_lt_of_le hcast hfl
    rw [lt_div_iff₀ hδ] at hkey
    linarith
  have h := Finset.card_le_card hsuper
  rw [Finset.card_range] at h
  have hc : ((m - 1 : ℕ) : ℝ)
      ≤ ((((Finset.range N).filter (fun i : ℕ => ((i : ℝ) + 1) * δ < x)).card : ℕ) : ℝ) := by
    exact_mod_cast h
  have hfl1 : x / δ < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlow : x / δ - 2 ≤ ((m - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hfl1 ⊢
      norm_num at hfl1 ⊢
      linarith
    · have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have h1 : (1 : ℕ) ≤ m := h0
        push_cast [Nat.cast_sub h1]
        ring
      rw [hcast]
      linarith
  linarith

/-! ## The step approximation -/

/-- The `N`-step lower approximation of a `[0,M]`-valued observable. -/
def stepApprox (M : ℝ) (N : ℕ) (f : Ω → ℝ) : Ω → ℝ := fun ω =>
  (M / N) * ∑ i ∈ Finset.range N, tailInd f (((i : ℝ) + 1) * (M / N)) ω

lemma stepApprox_eq_card {M : ℝ} {N : ℕ} {f : Ω → ℝ} (ω : Ω) :
    stepApprox M N f ω = (M / N)
      * ((((Finset.range N).filter
            (fun i : ℕ => ((i : ℝ) + 1) * (M / N) < f ω)).card : ℕ) : ℝ) := by
  classical
  unfold stepApprox tailInd
  congr 1
  simpa using
    (Finset.sum_boole (s := Finset.range N)
      (p := fun i : ℕ => ((i : ℝ) + 1) * (M / (N : ℝ)) < f ω) (R := ℝ))

lemma stepApprox_le {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N) {f : Ω → ℝ} (ω : Ω)
    (hx0 : 0 ≤ f ω) : stepApprox M N f ω ≤ f ω := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hδ : (0 : ℝ) < M / (N : ℝ) := by positivity
  have hc := card_grid_le (M / (N : ℝ)) (f ω) hδ hx0 N
  rw [stepApprox_eq_card]
  calc (M / (N : ℝ)) * ((((Finset.range N).filter
        (fun i : ℕ => ((i : ℝ) + 1) * (M / (N : ℝ)) < f ω)).card : ℕ) : ℝ)
      ≤ (M / (N : ℝ)) * (f ω / (M / (N : ℝ))) := mul_le_mul_of_nonneg_left hc hδ.le
    _ = f ω := by field_simp

lemma sub_le_stepApprox {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N) {f : Ω → ℝ} (ω : Ω)
    (hx0 : 0 ≤ f ω) (hxM : f ω ≤ M) : f ω - 2 * M / N ≤ stepApprox M N f ω := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hδ : (0 : ℝ) < M / (N : ℝ) := by positivity
  have hxN : f ω ≤ (N : ℝ) * (M / (N : ℝ)) := by
    rw [mul_div_cancel₀ _ (ne_of_gt hN0)]
    exact hxM
  have hc := le_card_grid (M / (N : ℝ)) (f ω) hδ hx0 N hxN
  rw [stepApprox_eq_card]
  have hstep : (M / (N : ℝ)) * (f ω / (M / (N : ℝ)) - 2)
      ≤ (M / (N : ℝ)) * ((((Finset.range N).filter
        (fun i : ℕ => ((i : ℝ) + 1) * (M / (N : ℝ)) < f ω)).card : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hc hδ.le
  have heq : (M / (N : ℝ)) * (f ω / (M / (N : ℝ)) - 2) = f ω - 2 * M / (N : ℝ) := by
    field_simp
  linarith [hstep, heq.symm.le, heq.le]

lemma stepApprox_nonneg {M : ℝ} (hM : 0 < M) {N : ℕ} {f : Ω → ℝ} (ω : Ω) :
    0 ≤ stepApprox M N f ω := by
  unfold stepApprox
  have h1 : (0 : ℝ) ≤ M / (N : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ ∑ i ∈ Finset.range N, tailInd f (((i : ℝ) + 1) * (M / (N : ℝ))) ω :=
    Finset.sum_nonneg fun i _ => tailInd_nonneg f _ ω
  positivity

lemma abs_stepApprox_sub_le {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N) {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfM : ∀ ω, f ω ≤ M) (ω : Ω) :
    |f ω - stepApprox M N f ω| ≤ 2 * M / N := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 := stepApprox_le hM hN (f := f) ω (hf0 ω)
  have h2 := sub_le_stepApprox hM hN (f := f) ω (hf0 ω) (hfM ω)
  have hpos : (0 : ℝ) ≤ 2 * M / (N : ℝ) := by positivity
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

lemma abs_stepApprox_le {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N) {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfM : ∀ ω, f ω ≤ M) (ω : Ω) :
    |stepApprox M N f ω| ≤ M := by
  have h1 := stepApprox_le hM hN (f := f) ω (hf0 ω)
  rw [abs_of_nonneg (stepApprox_nonneg hM ω)]
  linarith [hfM ω]


/-! ## The covariance bound

A covariance of two step functions is a finite double sum of indicator
covariances, so tail decorrelation at every pair of levels bounds it outright;
the step error is then sent to zero. -/

lemma integrable_of_bdd {μ : Measure Ω} [IsFiniteMeasure μ] {h : Ω → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ ω, |h ω| ≤ C) : Integrable h μ :=
  memLp_one_iff_integrable.mp (MemLp.of_bound hh.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω))

lemma measurable_stepApprox {M : ℝ} {N : ℕ} {f : Ω → ℝ} (hf : Measurable f) :
    Measurable (stepApprox M N f) := by
  unfold stepApprox
  exact (Finset.measurable_sum _ (fun i _ => measurable_tailInd hf _)).const_mul _

lemma abs_integral_le_of_bdd {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ}
    {C : ℝ} (hC : ∀ ω, |h ω| ≤ C) : |∫ ω, h ω ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := C) (f := h)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  simpa [Real.norm_eq_abs] using this

/-- **The step covariance is a finite double sum of indicator covariances.** -/
lemma abs_cov_stepApprox_le {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) {M K : ℝ} (hM : 0 < M) (hK : 0 ≤ K)
    {N : ℕ} (hN : 0 < N)
    (hcov : ∀ s t : ℝ,
      |(∫ ω, tailInd f s ω * tailInd g t ω ∂μ)
        - (∫ ω, tailInd f s ω ∂μ) * (∫ ω, tailInd g t ω ∂μ)| ≤ K) :
    |(∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
        - (∫ ω, stepApprox M N f ω ∂μ) * (∫ ω, stepApprox M N g ω ∂μ)|
      ≤ M ^ 2 * K := by
  classical
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set δ : ℝ := M / (N : ℝ) with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  set u : ℕ → Ω → ℝ := fun i => tailInd f (((i : ℝ) + 1) * δ) with hu
  set v : ℕ → Ω → ℝ := fun j => tailInd g (((j : ℝ) + 1) * δ) with hv
  have huint : ∀ i, Integrable (u i) μ := fun i =>
    integrable_of_bdd (measurable_tailInd hf _) (fun ω => abs_tailInd_le_one f _ ω)
  have hvint : ∀ j, Integrable (v j) μ := fun j =>
    integrable_of_bdd (measurable_tailInd hg _) (fun ω => abs_tailInd_le_one g _ ω)
  have huvint : ∀ i j, Integrable (fun ω => u i ω * v j ω) μ := by
    intro i j
    refine integrable_of_bdd (((measurable_tailInd hf _)).mul (measurable_tailInd hg _))
      (C := 1) (fun ω => ?_)
    rw [abs_mul]
    nlinarith [abs_tailInd_le_one f (((i : ℝ) + 1) * δ) ω,
      abs_tailInd_le_one g (((j : ℝ) + 1) * δ) ω,
      abs_nonneg (tailInd f (((i : ℝ) + 1) * δ) ω),
      abs_nonneg (tailInd g (((j : ℝ) + 1) * δ) ω)]
  -- the product of the two step functions, expanded
  have hprod : ∀ ω, stepApprox M N f ω * stepApprox M N g ω
      = δ ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, u i ω * v j ω := by
    intro ω
    unfold stepApprox
    rw [← hδdef]
    rw [show (δ * ∑ i ∈ Finset.range N, u i ω) * (δ * ∑ j ∈ Finset.range N, v j ω)
        = δ ^ 2 * ((∑ i ∈ Finset.range N, u i ω) * ∑ j ∈ Finset.range N, v j ω) by ring]
    rw [Finset.sum_mul_sum]
  have hintprod : (∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
      = δ ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ∫ ω, u i ω * v j ω ∂μ := by
    simp only [hprod]
    rw [integral_const_mul]
    congr 1
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => huvint i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_finset_sum _ (fun j _ => huvint i j)
  have hintf : (∫ ω, stepApprox M N f ω ∂μ)
      = δ * ∑ i ∈ Finset.range N, ∫ ω, u i ω ∂μ := by
    unfold stepApprox
    rw [← hδdef, integral_const_mul,
      integral_finset_sum _ (fun i _ => huint i)]
  have hintg : (∫ ω, stepApprox M N g ω ∂μ)
      = δ * ∑ j ∈ Finset.range N, ∫ ω, v j ω ∂μ := by
    unfold stepApprox
    rw [← hδdef, integral_const_mul,
      integral_finset_sum _ (fun j _ => hvint j)]
  have hdiff : (∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
        - (∫ ω, stepApprox M N f ω ∂μ) * (∫ ω, stepApprox M N g ω ∂μ)
      = δ ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ((∫ ω, u i ω * v j ω ∂μ) - (∫ ω, u i ω ∂μ) * ∫ ω, v j ω ∂μ) := by
    rw [hintprod, hintf, hintg]
    rw [show (δ * ∑ i ∈ Finset.range N, ∫ ω, u i ω ∂μ)
        * (δ * ∑ j ∈ Finset.range N, ∫ ω, v j ω ∂μ)
        = δ ^ 2 * ((∑ i ∈ Finset.range N, ∫ ω, u i ω ∂μ)
            * ∑ j ∈ Finset.range N, ∫ ω, v j ω ∂μ) by ring]
    rw [Finset.sum_mul_sum, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_sub_distrib]
  rw [hdiff, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ δ ^ 2)]
  have hinner : |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ((∫ ω, u i ω * v j ω ∂μ) - (∫ ω, u i ω ∂μ) * ∫ ω, v j ω ∂μ)|
      ≤ (N : ℝ) * (N : ℝ) * K := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hrow : ∀ i ∈ Finset.range N,
        |∑ j ∈ Finset.range N,
          ((∫ ω, u i ω * v j ω ∂μ) - (∫ ω, u i ω ∂μ) * ∫ ω, v j ω ∂μ)|
          ≤ (N : ℝ) * K := by
      intro i _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ j ∈ Finset.range N,
            |(∫ ω, u i ω * v j ω ∂μ) - (∫ ω, u i ω ∂μ) * ∫ ω, v j ω ∂μ|
          ≤ ∑ _j ∈ Finset.range N, K :=
            Finset.sum_le_sum fun j _ => hcov _ _
        _ = (N : ℝ) * K := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ∑ i ∈ Finset.range N, |∑ j ∈ Finset.range N,
          ((∫ ω, u i ω * v j ω ∂μ) - (∫ ω, u i ω ∂μ) * ∫ ω, v j ω ∂μ)|
        ≤ ∑ _i ∈ Finset.range N, (N : ℝ) * K := Finset.sum_le_sum hrow
      _ = (N : ℝ) * ((N : ℝ) * K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (N : ℝ) * (N : ℝ) * K := by ring
  have hfinal : δ ^ 2 * ((N : ℝ) * (N : ℝ) * K) = M ^ 2 * K := by
    rw [hδdef]; field_simp
  calc δ ^ 2 * |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((∫ ω, u i ω * v j ω ∂μ) - (∫ ω, u i ω ∂μ) * ∫ ω, v j ω ∂μ)|
      ≤ δ ^ 2 * ((N : ℝ) * (N : ℝ) * K) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = M ^ 2 * K := hfinal


/-- **The device.**  If the tail events of two `[0,M]`-valued observables
decorrelate to within `K` at *every* pair of levels, then the observables
themselves decorrelate to within `M²·K`.

This is what converts the currency of `Kwon1002.MultiLevel.multiLevel_transfer`
— the `α`-average of a product of indicators against the product of the
stationary means — into the covariance currency of display (41). -/
theorem abs_cov_le_of_indicator_cov {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {M K : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfM : ∀ ω, f ω ≤ M)
    (hg0 : ∀ ω, 0 ≤ g ω) (hgM : ∀ ω, g ω ≤ M)
    (hcov : ∀ s t : ℝ,
      |(∫ ω, tailInd f s ω * tailInd g t ω ∂μ)
        - (∫ ω, tailInd f s ω ∂μ) * (∫ ω, tailInd g t ω ∂μ)| ≤ K) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)| ≤ M ^ 2 * K := by
  classical
  have hfa : ∀ ω, |f ω| ≤ M := fun ω => by rw [abs_of_nonneg (hf0 ω)]; exact hfM ω
  have hga : ∀ ω, |g ω| ≤ M := fun ω => by rw [abs_of_nonneg (hg0 ω)]; exact hgM ω
  have hfint : Integrable f μ := integrable_of_bdd hf hfa
  have hgint : Integrable g μ := integrable_of_bdd hg hga
  have hfgint : Integrable (fun ω => f ω * g ω) μ := by
    refine integrable_of_bdd (hf.mul hg) (C := M ^ 2) (fun ω => ?_)
    rw [abs_mul]
    nlinarith [hfa ω, hga ω, abs_nonneg (f ω), abs_nonneg (g ω)]
  have hkey : ∀ N : ℕ, 0 < N →
      |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
        ≤ M ^ 2 * K + 8 * M ^ 2 / N := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hSfa : ∀ ω, |stepApprox M N f ω| ≤ M := abs_stepApprox_le hM hN hf0 hfM
    have hSga : ∀ ω, |stepApprox M N g ω| ≤ M := abs_stepApprox_le hM hN hg0 hgM
    have hSfint : Integrable (stepApprox M N f) μ :=
      integrable_of_bdd (measurable_stepApprox hf) hSfa
    have hSgint : Integrable (stepApprox M N g) μ :=
      integrable_of_bdd (measurable_stepApprox hg) hSga
    have hSint : Integrable (fun ω => stepApprox M N f ω * stepApprox M N g ω) μ := by
      refine integrable_of_bdd
        ((measurable_stepApprox hf).mul (measurable_stepApprox hg)) (C := M ^ 2) (fun ω => ?_)
      rw [abs_mul]
      nlinarith [hSfa ω, hSga ω, abs_nonneg (stepApprox M N f ω),
        abs_nonneg (stepApprox M N g ω)]
    have hdf : ∀ ω, |f ω - stepApprox M N f ω| ≤ 2 * M / N :=
      abs_stepApprox_sub_le hM hN hf0 hfM
    have hdg : ∀ ω, |g ω - stepApprox M N g ω| ≤ 2 * M / N :=
      abs_stepApprox_sub_le hM hN hg0 hgM
    have h2 : |(∫ ω, f ω * g ω ∂μ) - ∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ|
        ≤ 4 * M ^ 2 / N := by
      rw [← integral_sub hfgint hSint]
      refine abs_integral_le_of_bdd (fun ω => ?_)
      have hrw : f ω * g ω - stepApprox M N f ω * stepApprox M N g ω
          = f ω * (g ω - stepApprox M N g ω)
            + stepApprox M N g ω * (f ω - stepApprox M N f ω) := by ring
      rw [hrw]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      have e1 : |f ω| * |g ω - stepApprox M N g ω| ≤ M * (2 * M / N) :=
        mul_le_mul (hfa ω) (hdg ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hfa ω))
      have e2 : |stepApprox M N g ω| * |f ω - stepApprox M N f ω| ≤ M * (2 * M / N) :=
        mul_le_mul (hSga ω) (hdf ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hSga ω))
      have : M * (2 * M / N) + M * (2 * M / N) = 4 * M ^ 2 / N := by field_simp; ring
      linarith
    have hIf : |(∫ ω, f ω ∂μ) - ∫ ω, stepApprox M N f ω ∂μ| ≤ 2 * M / N := by
      rw [← integral_sub hfint hSfint]
      exact abs_integral_le_of_bdd hdf
    have hIg : |(∫ ω, g ω ∂μ) - ∫ ω, stepApprox M N g ω ∂μ| ≤ 2 * M / N := by
      rw [← integral_sub hgint hSgint]
      exact abs_integral_le_of_bdd hdg
    have hIfa : |∫ ω, f ω ∂μ| ≤ M := abs_integral_le_of_bdd hfa
    have hISga : |∫ ω, stepApprox M N g ω ∂μ| ≤ M := abs_integral_le_of_bdd hSga
    have h3 : |(∫ ω, stepApprox M N f ω ∂μ) * (∫ ω, stepApprox M N g ω ∂μ)
        - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤ 4 * M ^ 2 / N := by
      have hrw : (∫ ω, stepApprox M N f ω ∂μ) * (∫ ω, stepApprox M N g ω ∂μ)
          - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ
          = (∫ ω, stepApprox M N g ω ∂μ)
              * ((∫ ω, stepApprox M N f ω ∂μ) - ∫ ω, f ω ∂μ)
            + (∫ ω, f ω ∂μ)
              * ((∫ ω, stepApprox M N g ω ∂μ) - ∫ ω, g ω ∂μ) := by ring
      rw [hrw]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      have hf' : |(∫ ω, stepApprox M N f ω ∂μ) - ∫ ω, f ω ∂μ| ≤ 2 * M / N := by
        rw [abs_sub_comm]; exact hIf
      have hg' : |(∫ ω, stepApprox M N g ω ∂μ) - ∫ ω, g ω ∂μ| ≤ 2 * M / N := by
        rw [abs_sub_comm]; exact hIg
      have e1 : |∫ ω, stepApprox M N g ω ∂μ|
          * |(∫ ω, stepApprox M N f ω ∂μ) - ∫ ω, f ω ∂μ| ≤ M * (2 * M / N) :=
        mul_le_mul hISga hf' (abs_nonneg _) (le_trans (abs_nonneg _) hISga)
      have e2 : |∫ ω, f ω ∂μ| * |(∫ ω, stepApprox M N g ω ∂μ) - ∫ ω, g ω ∂μ|
          ≤ M * (2 * M / N) :=
        mul_le_mul hIfa hg' (abs_nonneg _) (le_trans (abs_nonneg _) hIfa)
      have : M * (2 * M / N) + M * (2 * M / N) = 4 * M ^ 2 / N := by field_simp; ring
      linarith
    have h4 := abs_cov_stepApprox_le (μ := μ) hf hg hM hK hN hcov
    have hsplit : (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ
        = ((∫ ω, f ω * g ω ∂μ) - ∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
          + (((∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
                - (∫ ω, stepApprox M N f ω ∂μ) * ∫ ω, stepApprox M N g ω ∂μ)
            + ((∫ ω, stepApprox M N f ω ∂μ) * (∫ ω, stepApprox M N g ω ∂μ)
                - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ)) := by ring
    rw [hsplit]
    have hstep1 := abs_add_le
      ((∫ ω, f ω * g ω ∂μ) - ∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
      (((∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
          - (∫ ω, stepApprox M N f ω ∂μ) * ∫ ω, stepApprox M N g ω ∂μ)
        + ((∫ ω, stepApprox M N f ω ∂μ) * (∫ ω, stepApprox M N g ω ∂μ)
            - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ))
    have hstep2 := abs_add_le
      ((∫ ω, stepApprox M N f ω * stepApprox M N g ω ∂μ)
        - (∫ ω, stepApprox M N f ω ∂μ) * ∫ ω, stepApprox M N g ω ∂μ)
      ((∫ ω, stepApprox M N f ω ∂μ) * (∫ ω, stepApprox M N g ω ∂μ)
        - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ)
    have harith : 4 * M ^ 2 / (N : ℝ) + 4 * M ^ 2 / (N : ℝ) = 8 * M ^ 2 / (N : ℝ) := by
      field_simp; ring
    linarith
  refine le_of_forall_pos_le_add (fun η hη => ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * M ^ 2 / η)
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN
  have hNpos : 0 < N := by exact_mod_cast hN0
  have hsmall : 8 * M ^ 2 / (N : ℝ) ≤ η := by
    rw [div_le_iff₀ hN0]
    rw [div_lt_iff₀ hη] at hN
    nlinarith [hN, hη, hN0]
  linarith [hkey N hNpos]

end

end PairLayerCake

end Kwon1002
