import Kwon1002.StepQuasi

/-!
# The multilinear expansion of a step symbol

`Kwon1002.StepQuasi.exists_bulk_quasi_pattern` is quasi-independence on the
random bulk at a fixed cell pattern.  This module expands a `k`-fold product of
step symbols into patterns, so that the estimate applies, and pays the two
approximation errors — the mesh `η` inside the annulus and the truncation `R`
outside it — against the tuple masses.

The level factor of the expansion is `stepFactor`: the step symbol read at level
`j` on the random bulk, i.e. `1{j ∈ J_n}·(∑_i w_i 1_{E_i}(X_{n,j}))`.  Its
`k`-fold product over a tuple of levels expands, by `Finset.prod_univ_sum`, into
`M^k` pattern terms whose integrands are indicators of tuple events; that is the
only place where the multilinearity is used.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace QuasiIndep

noncomputable section

open LevyExponent TupleMeasure TupleFinal FactorialRoute PatternSum StepQuasi

/-! ## The level factor of a step symbol -/

/-- The step symbol read at level `j` on the random bulk. -/
def stepFactor (c : ℝ) {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ) (n j : ℕ) (α : ℝ) : ℂ :=
  ∑ i, w i * Set.indicator (bulkMarkEvent c n (E i) j) (fun _ => (1:ℂ)) α

/-- `stepFactor` is the level integrand of the step symbol. -/
lemma stepFactor_eq (c : ℝ) {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ) (n j : ℕ) (α : ℝ) :
    stepFactor c w E n j α
      = Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
          (fun β => ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) (signedMark β n j)) α := by
  classical
  by_cases hb : j ∈ bulkIndices c α n
  · rw [Set.indicator_of_mem (show α ∈ {β : ℝ | j ∈ bulkIndices c β n} from hb)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hs : signedMark α n j ∈ E i <;> simp [stepFactor, bulkMarkEvent, hb, hs]
  · rw [Set.indicator_of_notMem (show α ∉ {β : ℝ | j ∈ bulkIndices c β n} from hb)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Set.indicator_of_notMem (show α ∉ bulkMarkEvent c n (E i) j from fun h => hb h.1),
      mul_zero]

lemma measurable_stepFactor (c : ℝ) {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (n j : ℕ) : Measurable (stepFactor c w E n j) := by
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (measurable_const.indicator (measurableSet_bulkMarkEvent c n (hE i) j)).const_mul _

/-! ## The two pointwise error bounds -/

/-- Off the truncation set the step symbol vanishes, and on it it is bounded by
`5`: both follow from the approximation bound itself. -/
lemma norm_stepSymbol_le {t ε R η : ℝ} (hεR : ε ≤ R) (hη : η ≤ 1) {M : ℕ} (w : Fin M → ℂ)
    (E : Fin M → Set ℝ)
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x) (x : ℝ) :
    ‖∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
      ≤ 5 * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x := by
  classical
  have h := hpt x
  by_cases hx : x ∈ PoissonRoute.truncSet ε
  · rw [Set.indicator_of_mem hx]
    have h1 : ‖SymbolLimit.psi t ε x‖ ≤ 2 := SymbolLimit.norm_psi_le t ε x
    have h2 : Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x ≤ 1 := by
      rw [Set.indicator_apply]; split_ifs <;> norm_num
    have h3 : ‖∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ ‖SymbolLimit.psi t ε x‖
          + ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖ := by
      have := norm_sub_le (SymbolLimit.psi t ε x)
        (SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x)
      simpa using this
    rw [Set.indicator_of_mem hx] at h
    nlinarith
  · have hxR : x ∉ PoissonRoute.truncSet R := by
      intro hR
      exact hx (lt_of_le_of_lt hεR hR)
    have hpsi : SymbolLimit.psi t ε x = 0 := Set.indicator_of_notMem hx _
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxR, hpsi] at h
    simp only [zero_sub, norm_neg, mul_zero, add_zero] at h
    rw [Set.indicator_of_notMem hx]
    simp only [mul_zero]
    exact h

/-- The level factor of a step symbol is supported on the large-jump event and
bounded by `5` there. -/
lemma norm_stepFactor_le {t ε R η : ℝ} (hεR : ε ≤ R) (hη : η ≤ 1) {M : ℕ} (w : Fin M → ℂ)
    (E : Fin M → Set ℝ)
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x)
    (c : ℝ) (n j : ℕ) (α : ℝ) :
    ‖stepFactor c w E n j α‖
      ≤ 5 * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α := by
  rw [stepFactor_eq]
  by_cases hb : j ∈ bulkIndices c α n
  · rw [Set.indicator_of_mem (show α ∈ {β : ℝ | j ∈ bulkIndices c β n} from hb)]
    refine le_trans (norm_stepSymbol_le hεR hη w E hpt (signedMark α n j)) ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
    by_cases hs : signedMark α n j ∈ PoissonRoute.truncSet ε
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show α ∈ bigEvent c ε n j from ⟨hb, hs⟩)]
    · rw [Set.indicator_of_notMem hs,
        Set.indicator_of_notMem (show α ∉ bigEvent c ε n j from fun h => hs h.2)]
  · rw [Set.indicator_of_notMem (show α ∉ {β : ℝ | j ∈ bulkIndices c β n} from hb), norm_zero]
    refine mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => by norm_num) α)

/-- The approximation error at one level of the product. -/
lemma norm_jumpFactor_sub_stepFactor_le {t ε R η : ℝ} (hη0 : 0 ≤ η) {M : ℕ} (w : Fin M → ℂ)
    (E : Fin M → Set ℝ)
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x)
    (c : ℝ) (n j : ℕ) (α : ℝ) :
    ‖jumpFactor t c ε n j α - stepFactor c w E n j α‖
      ≤ η * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α
        + 2 * Set.indicator (bigEvent c R n j) (fun _ => (1:ℝ)) α := by
  rw [stepFactor_eq]
  by_cases hb : j ∈ bulkIndices c α n
  · rw [Set.indicator_of_mem (show α ∈ {β : ℝ | j ∈ bulkIndices c β n} from hb)]
    have hj : jumpFactor t c ε n j α = SymbolLimit.psi t ε (signedMark α n j) := by
      unfold jumpFactor SymbolLimit.psi
      by_cases hs : signedMark α n j ∈ PoissonRoute.truncSet ε
      · rw [Set.indicator_of_mem (show α ∈ bigEvent c ε n j from ⟨hb, hs⟩),
          Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem (show α ∉ bigEvent c ε n j from fun h => hs h.2),
          Set.indicator_of_notMem hs]
    rw [hj]
    refine le_trans (hpt (signedMark α n j)) (le_of_eq ?_)
    have h1 : Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) (signedMark α n j)
        = Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α := by
      by_cases hs : signedMark α n j ∈ PoissonRoute.truncSet ε
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show α ∈ bigEvent c ε n j from ⟨hb, hs⟩)]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (show α ∉ bigEvent c ε n j from fun h => hs h.2)]
    have h2 : Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) (signedMark α n j)
        = Set.indicator (bigEvent c R n j) (fun _ => (1:ℝ)) α := by
      by_cases hs : signedMark α n j ∈ PoissonRoute.truncSet R
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show α ∈ bigEvent c R n j from ⟨hb, hs⟩)]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (show α ∉ bigEvent c R n j from fun h => hs h.2)]
    rw [h1, h2]
  · rw [Set.indicator_of_notMem (show α ∉ {β : ℝ | j ∈ bulkIndices c β n} from hb),
      jumpFactor_of_notMem (fun h => hb h.1), sub_zero, norm_zero]
    have h1 : (0:ℝ) ≤ η * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α :=
      mul_nonneg hη0 (Set.indicator_nonneg (fun _ _ => by norm_num) α)
    have h2 : (0:ℝ) ≤ 2 * Set.indicator (bigEvent c R n j) (fun _ => (1:ℝ)) α :=
      mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => by norm_num) α)
    linarith

/-! ## The expansion -/

lemma prod_indicator_eq {k : ℕ} (A : Fin k → Set ℝ) (α : ℝ) :
    (∏ ℓ, Set.indicator (A ℓ) (fun _ => (1:ℂ)) α)
      = Set.indicator (⋂ ℓ, A ℓ) (fun _ => (1:ℂ)) α := by
  classical
  by_cases h : ∀ ℓ, α ∈ A ℓ
  · rw [Set.indicator_of_mem (Set.mem_iInter.mpr h)]
    refine Finset.prod_eq_one (fun ℓ _ => ?_)
    exact Set.indicator_of_mem (h ℓ) _
  · push_neg at h
    obtain ⟨ℓ₀, hℓ₀⟩ := h
    rw [Set.indicator_of_notMem (fun hh => hℓ₀ (Set.mem_iInter.mp hh ℓ₀))]
    exact Finset.prod_eq_zero (Finset.mem_univ ℓ₀) (Set.indicator_of_notMem hℓ₀ _)

/-- **The multilinear expansion, pointwise.** -/
lemma prod_stepFactor_eq {k : ℕ} (c : ℝ) {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ)
    (n : ℕ) (g : Fin k → ℕ) (α : ℝ) :
    (∏ ℓ, stepFactor c w E n (g ℓ) α)
      = ∑ u : Fin k → Fin M, (∏ ℓ, w (u ℓ))
          * Set.indicator (⋂ ℓ, bulkMarkEvent c n (E (u ℓ)) (g ℓ)) (fun _ => (1:ℂ)) α := by
  classical
  have h1 : (∏ ℓ, stepFactor c w E n (g ℓ) α)
      = ∑ u ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (Fin M))),
          ∏ ℓ, w (u ℓ) * Set.indicator (bulkMarkEvent c n (E (u ℓ)) (g ℓ)) (fun _ => (1:ℂ)) α :=
    Finset.prod_univ_sum _ _
  rw [h1, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.prod_mul_distrib, prod_indicator_eq]

/-! ## The integrated expansion -/

lemma integrableOn_indicator_complex {S : Set ℝ} (hS : MeasurableSet S) :
    IntegrableOn (fun α : ℝ => Set.indicator S (fun _ => (1:ℂ)) α) (Ioo (0:ℝ) 1) volume :=
  (integrable_const (1:ℂ)).indicator hS

lemma setIntegral_indicator_complex {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ α in Ioo (0:ℝ) 1, Set.indicator S (fun _ => (1:ℂ)) α) = ((unifIoo.real S : ℝ) : ℂ) := by
  rw [setIntegral_indicator hS, setIntegral_const, Complex.real_smul, mul_one]
  congr 1
  simp [Measure.real, unifIoo, Measure.restrict_apply hS, Set.inter_comm]

/-- **The multilinear expansion, integrated.** -/
lemma integral_prod_stepFactor {k : ℕ} (c : ℝ) {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (n : ℕ) (g : Fin k → ℕ) :
    (∫ α in Ioo (0:ℝ) 1, ∏ ℓ, stepFactor c w E n (g ℓ) α)
      = ∑ u : Fin k → Fin M, (∏ ℓ, w (u ℓ))
          * ((unifIoo.real (⋂ ℓ, bulkMarkEvent c n (E (u ℓ)) (g ℓ)) : ℝ) : ℂ) := by
  classical
  have hmeas : ∀ u : Fin k → Fin M,
      MeasurableSet (⋂ ℓ, bulkMarkEvent c n (E (u ℓ)) (g ℓ)) := fun u =>
    MeasurableSet.iInter (fun ℓ => measurableSet_bulkMarkEvent c n (hE (u ℓ)) (g ℓ))
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun α => prod_stepFactor_eq c w E n g α)),
    integral_finset_sum _ (fun u _ => (integrableOn_indicator_complex (hmeas u)).const_mul _)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [integral_const_mul, setIntegral_indicator_complex (hmeas u)]

lemma integral_stepFactor (c : ℝ) {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (n j : ℕ) :
    (∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α)
      = ∑ i, w i * ((unifIoo.real (bulkMarkEvent c n (E i) j) : ℝ) : ℂ) := by
  classical
  simp only [stepFactor]
  rw [integral_finset_sum _ (fun i _ =>
    (integrableOn_indicator_complex (measurableSet_bulkMarkEvent c n (hE i) j)).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul,
    setIntegral_indicator_complex (measurableSet_bulkMarkEvent c n (hE i) j)]

/-- The product of the one-level means, expanded over patterns. -/
lemma prod_integral_stepFactor {k : ℕ} (c : ℝ) {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (n : ℕ) (g : Fin k → ℕ) :
    (∏ ℓ, ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n (g ℓ) α)
      = ∑ u : Fin k → Fin M, (∏ ℓ, w (u ℓ))
          * ∏ ℓ, ((unifIoo.real (bulkMarkEvent c n (E (u ℓ)) (g ℓ)) : ℝ) : ℂ) := by
  classical
  have h1 : (∏ ℓ, ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n (g ℓ) α)
      = ∏ ℓ, ∑ i, w i * ((unifIoo.real (bulkMarkEvent c n (E i) (g ℓ)) : ℝ) : ℂ) :=
    Finset.prod_congr rfl (fun ℓ _ => integral_stepFactor c w hE n (g ℓ))
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.prod_mul_distrib]

/-- **The step-symbol quasi-independence defect at one tuple**, bounded by the
pattern defects. -/
lemma norm_stepDefect_le {k : ℕ} (c : ℝ) {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (n : ℕ) (g : Fin k → ℕ) :
    ‖(∫ α in Ioo (0:ℝ) 1, ∏ ℓ, stepFactor c w E n (g ℓ) α)
        - ∏ ℓ, ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n (g ℓ) α‖
      ≤ ∑ u : Fin k → Fin M, (∏ ℓ, ‖w (u ℓ)‖)
          * |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (E (u ℓ)) (g ℓ))
              - ∏ ℓ, unifIoo.real (bulkMarkEvent c n (E (u ℓ)) (g ℓ))| := by
  classical
  rw [integral_prod_stepFactor c w hE n g, prod_integral_stepFactor c w hE n g,
    ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun u _ => ?_))
  have hpush : ((unifIoo.real (⋂ ℓ, bulkMarkEvent c n (E (u ℓ)) (g ℓ)) : ℝ) : ℂ)
      - ∏ ℓ, ((unifIoo.real (bulkMarkEvent c n (E (u ℓ)) (g ℓ)) : ℝ) : ℂ)
      = (((unifIoo.real (⋂ ℓ, bulkMarkEvent c n (E (u ℓ)) (g ℓ))
          - ∏ ℓ, unifIoo.real (bulkMarkEvent c n (E (u ℓ)) (g ℓ)) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [← mul_sub, hpush, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]


/-! ## The tuple bound at per-level radii

`digit_tail_product` is stated with a *threshold per level*, and every call site
so far has instantiated it at a constant family.  The `R`-tail of a `k`-fold
product needs one level at the truncation radius `R` and the others at `ε`, so
the per-level form is recorded here.  Nothing in the proof changes but the
threshold family. -/

lemma prod_orderEmb {β : Type*} [CommMonoid β] {k : ℕ} {S : Finset ℕ} (h : S.card = k)
    (F : ℕ → β) : (∏ i : Fin k, F (S.orderEmbOfFin h i)) = ∏ j ∈ S, F j := by
  classical
  rw [← Finset.prod_image (f := F) (g := fun i : Fin k => (S.orderEmbOfFin h i))
      (fun x _ y _ hxy => (S.orderEmbOfFin h).injective hxy)]
  congr 1
  have hset : ((Finset.univ.image (fun i : Fin k => (S.orderEmbOfFin h i)) : Finset ℕ) : Set ℕ)
      = (S : Set ℕ) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact S.range_orderEmbOfFin h
  exact_mod_cast hset

/-- **The tuple bound with a radius per level.** -/
theorem exists_tuple_bound_radii (c : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ rad : ℕ → ℝ, (∀ j, ε ≤ rad j) → ∀ S : Finset ℕ,
        unifIoo.real (⋂ j ∈ S, bigEvent c (rad j) n j)
          ≤ ∏ j ∈ S, (C₀ / (8 * rad j) / Lnorm n) := by
  classical
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀, hC₀, ?_⟩
  intro ε hε
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * ε * Lnorm n := by
    have h : Tendsto (fun n : ℕ => 8 * ε * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) TupleMeasure.tendsto_Lnorm_atTop
    exact h.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 rad hrad S
  set k : ℕ := S.card with hk
  set js : Fin k → ℕ := fun i => S.orderEmbOfFin hk.symm i with hjs
  set A : Fin k → ℝ := fun i => 8 * rad (js i) * Lnorm n with hA
  have hinj : Function.Injective js := (S.orderEmbOfFin hk.symm).injective
  have hA1 : ∀ i, 1 ≤ A i := by
    intro i
    have h := hrad (js i)
    have hmul : 8 * ε * Lnorm n ≤ 8 * rad (js i) * Lnorm n := by nlinarith
    simp only [hA]
    linarith
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin k, A i ≤ (digit α (js i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ k * ∏ i, (A i)⁻¹ := hC k js A hinj hA1
  have hsub : (⋂ j ∈ S, bigEvent c (rad j) n j) ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    refine ⟨hαI, fun i => ?_⟩
    have hmem : α ∈ bigEvent c (rad (js i)) n (js i) :=
      Set.mem_iInter₂.mp hα (js i) (S.orderEmbOfFin_mem hk.symm i)
    have hB0 : ∀ x ∈ PoissonRoute.truncSet (rad (js i)), rad (js i) ≤ |x| :=
      fun _ hx => le_of_lt hx
    exact TupleMeasure.digit_ge_of_mem_bulkMarkEvent c (PoissonRoute.truncSet (rad (js i)))
      hB0 hn2 hmem
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (⋂ j ∈ S, bigEvent c (rad j) n j) ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound (le_of_eq ?_))
  have hstep : C₀ ^ k * ∏ i, (A i)⁻¹ = ∏ i : Fin k, (C₀ * (A i)⁻¹) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hstep]
  have hfin2 : (∏ i : Fin k, (C₀ * (8 * rad (js i) * Lnorm n)⁻¹))
      = ∏ j ∈ S, (C₀ * (8 * rad j * Lnorm n)⁻¹) :=
    prod_orderEmb hk.symm (fun j => C₀ * (8 * rad j * Lnorm n)⁻¹)
  simp only [hA]
  rw [hfin2]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [div_div, div_eq_mul_inv]

/-! ## Products of indicators over a `Finset` of levels -/

lemma prod_indicator_biInter (T : Finset ℕ) (A : ℕ → Set ℝ) (α : ℝ) :
    (∏ j ∈ T, Set.indicator (A j) (fun _ => (1:ℝ)) α)
      = Set.indicator (⋂ j ∈ T, A j) (fun _ => (1:ℝ)) α := by
  classical
  by_cases h : ∀ j ∈ T, α ∈ A j
  · rw [Set.indicator_of_mem (Set.mem_iInter₂.mpr h)]
    exact Finset.prod_eq_one (fun j hj => Set.indicator_of_mem (h j hj) _)
  · push_neg at h
    obtain ⟨j₀, hj₀T, hj₀⟩ := h
    rw [Set.indicator_of_notMem (fun hh => hj₀ (Set.mem_iInter₂.mp hh j₀ hj₀T))]
    exact Finset.prod_eq_zero hj₀T (Set.indicator_of_notMem hj₀ _)

/-! ## The sorted embedding attached to a level set -/

/-- The increasing enumeration of a `k`-element level set, as an embedding. -/
def sortEmb {n k : ℕ} {S : Finset ℕ} (hsub : S ⊆ Finset.range (n + 1)) (hcard : S.card = k) :
    Fin k ↪ (Finset.range (n + 1) : Finset ℕ) :=
  ⟨fun ℓ => ⟨S.orderEmbOfFin hcard ℓ, hsub (S.orderEmbOfFin_mem hcard ℓ)⟩,
    fun a b hab => (S.orderEmbOfFin hcard).injective (by
      simpa using congrArg Subtype.val hab)⟩

@[simp] lemma embTuple_sortEmb {n k : ℕ} {S : Finset ℕ} (hsub : S ⊆ Finset.range (n + 1))
    (hcard : S.card = k) (ℓ : Fin k) :
    embTuple (sortEmb hsub hcard) ℓ = S.orderEmbOfFin hcard ℓ := rfl

lemma image_embTuple_sortEmb {n k : ℕ} {S : Finset ℕ} (hsub : S ⊆ Finset.range (n + 1))
    (hcard : S.card = k) : Finset.univ.image (embTuple (sortEmb hsub hcard)) = S := by
  classical
  have hset : ((Finset.univ.image (embTuple (sortEmb hsub hcard)) : Finset ℕ) : Set ℕ)
      = (S : Set ℕ) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact S.range_orderEmbOfFin hcard
  exact_mod_cast hset

/-- Summing over `k`-element level sets is dominated by summing over embeddings:
each level set is the image of its own increasing enumeration. -/
lemma sum_powersetCard_le_sum_emb {n k : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range (n + 1))
    (G : Finset ℕ → ℝ) (F : (Fin k ↪ (Finset.range (n + 1) : Finset ℕ)) → ℝ)
    (hF : ∀ f, 0 ≤ F f)
    (hGF : ∀ S ∈ Finset.powersetCard k T, ∃ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
      Finset.univ.image (embTuple f) = S ∧ G S ≤ F f) :
    (∑ S ∈ Finset.powersetCard k T, G S) ≤ ∑ f, F f := by
  classical
  have hmaps : ∀ f ∈ (Finset.univ : Finset (Fin k ↪ (Finset.range (n + 1) : Finset ℕ))),
      Finset.univ.image (embTuple f) ∈ Finset.powersetCard k (Finset.range (n + 1)) := by
    intro f _
    rw [Finset.mem_powersetCard]
    refine ⟨?_, TupleFinal.card_image_embTuple f⟩
    intro x hx
    obtain ⟨ℓ, _, rfl⟩ := Finset.mem_image.mp hx
    exact (f ℓ).2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps F
  have hsubset : Finset.powersetCard k T ⊆ Finset.powersetCard k (Finset.range (n + 1)) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨fun x hx => hT (hS.1 hx), hS.2⟩
  calc (∑ S ∈ Finset.powersetCard k T, G S)
      ≤ ∑ S ∈ Finset.powersetCard k T,
          ∑ f ∈ Finset.univ.filter (fun f => Finset.univ.image (embTuple f) = S), F f := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        obtain ⟨f, hfS, hGf⟩ := hGF S hS
        refine le_trans hGf (Finset.single_le_sum (f := F) (fun g _ => hF g) ?_)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, hfS⟩
    _ ≤ ∑ S ∈ Finset.powersetCard k (Finset.range (n + 1)),
          ∑ f ∈ Finset.univ.filter (fun f => Finset.univ.image (embTuple f) = S), F f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun S _ _ => ?_)
        exact Finset.sum_nonneg (fun f _ => hF f)
    _ = ∑ f, F f := hfib

end

end QuasiIndep

end Kwon1002
