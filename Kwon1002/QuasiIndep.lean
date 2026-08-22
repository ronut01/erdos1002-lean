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


/-! ## The two approximation errors, at a level set

Both swaps — inside the integral and inside the product of means — are the same
telescoping, `PatternSum.norm_prod_sub_prod_le`, against the majorant
`5·1{large jump}` per level.  The point of keeping the indicator inside the
majorant is that the untouched factors then contribute the *tuple* mass, not the
constant `5`. -/

lemma indicator_mul_indicator (A B : Set ℝ) (α : ℝ) :
    Set.indicator A (fun _ => (1:ℝ)) α * Set.indicator B (fun _ => (1:ℝ)) α
      = Set.indicator (A ∩ B) (fun _ => (1:ℝ)) α := by
  classical
  by_cases hA : α ∈ A <;> by_cases hB : α ∈ B <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, hB, Set.mem_inter_iff]

lemma norm_jumpFactor_le_indicator (t c ε : ℝ) (n j : ℕ) (α : ℝ) :
    ‖jumpFactor t c ε n j α‖ ≤ 5 * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α := by
  classical
  by_cases h : α ∈ bigEvent c ε n j
  · rw [Set.indicator_of_mem h]
    have := norm_jumpFactor_le t c ε n j α
    linarith
  · rw [jumpFactor_of_notMem h, norm_zero, Set.indicator_of_notMem h]
    norm_num

/-- The mixed-radius event of the `R`-tail: all levels of `S` but one are large
at `ε`, and the remaining one is large at `R`. -/
def mixedEvent (c ε R : ℝ) (n : ℕ) (S : Finset ℕ) (i : ℕ) : Set ℝ :=
  (⋂ j ∈ S.erase i, bigEvent c ε n j) ∩ bigEvent c R n i

lemma measurableSet_mixedEvent (c ε R : ℝ) (n : ℕ) (S : Finset ℕ) (i : ℕ) :
    MeasurableSet (mixedEvent c ε R n S i) :=
  (MeasurableSet.biInter (S.erase i).countable_toSet
    (fun j _ => measurableSet_bigEvent c ε n j)).inter (measurableSet_bigEvent c R n i)

/-- The pointwise error of the symbol swap over a level set. -/
lemma norm_prod_jumpFactor_sub_prod_stepFactor_le {t ε R η : ℝ} (hη0 : 0 ≤ η) (hεR : ε ≤ R)
    (hη1 : η ≤ 1) {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ)
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x)
    (c : ℝ) (n : ℕ) (S : Finset ℕ) (α : ℝ) :
    ‖(∏ j ∈ S, jumpFactor t c ε n j α) - ∏ j ∈ S, stepFactor c w E n j α‖
      ≤ ∑ i ∈ S, (5:ℝ) ^ (S.card - 1) *
          (η * Set.indicator (tupleBigEvent c ε n S) (fun _ => (1:ℝ)) α
            + 2 * Set.indicator (mixedEvent c ε R n S i) (fun _ => (1:ℝ)) α) := by
  classical
  have htel := PatternSum.norm_prod_sub_prod_le (K := ℂ) S
    (fun j => jumpFactor t c ε n j α) (fun j => stepFactor c w E n j α)
    (fun j => 5 * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α)
    (fun j _ => norm_jumpFactor_le_indicator t c ε n j α)
    (fun j _ => norm_stepFactor_le hεR hη1 w E hpt c n j α)
  refine le_trans htel (Finset.sum_le_sum (fun i hi => ?_))
  have hcard : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
  have hprod : (∏ j ∈ S.erase i, 5 * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α)
      = (5:ℝ) ^ (S.card - 1)
        * Set.indicator (⋂ j ∈ S.erase i, bigEvent c ε n j) (fun _ => (1:ℝ)) α := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, prod_indicator_biInter]
  rw [hprod]
  have herr := norm_jumpFactor_sub_stepFactor_le hη0 w E hpt c n i α
  have hind0 : (0:ℝ) ≤ Set.indicator (⋂ j ∈ S.erase i, bigEvent c ε n j) (fun _ => (1:ℝ)) α :=
    Set.indicator_nonneg (fun _ _ => by norm_num) α
  have hmul : (5:ℝ) ^ (S.card - 1)
        * Set.indicator (⋂ j ∈ S.erase i, bigEvent c ε n j) (fun _ => (1:ℝ)) α
        * ‖jumpFactor t c ε n i α - stepFactor c w E n i α‖
      ≤ (5:ℝ) ^ (S.card - 1)
        * Set.indicator (⋂ j ∈ S.erase i, bigEvent c ε n j) (fun _ => (1:ℝ)) α
        * (η * Set.indicator (bigEvent c ε n i) (fun _ => (1:ℝ)) α
            + 2 * Set.indicator (bigEvent c R n i) (fun _ => (1:ℝ)) α) := by
    refine mul_le_mul_of_nonneg_left herr (by positivity)
  refine le_trans hmul (le_of_eq ?_)
  have hS : (⋂ j ∈ S.erase i, bigEvent c ε n j) ∩ bigEvent c ε n i = tupleBigEvent c ε n S := by
    rw [tupleBigEvent]
    ext β
    simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      by_cases hji : j = i
      · subst hji; exact h2
      · exact h1 j ⟨hji, hj⟩
    · intro h
      exact ⟨fun j hj => h j hj.2, h i hi⟩
  calc (5:ℝ) ^ (S.card - 1)
        * Set.indicator (⋂ j ∈ S.erase i, bigEvent c ε n j) (fun _ => (1:ℝ)) α
        * (η * Set.indicator (bigEvent c ε n i) (fun _ => (1:ℝ)) α
            + 2 * Set.indicator (bigEvent c R n i) (fun _ => (1:ℝ)) α)
      = (5:ℝ) ^ (S.card - 1) *
          (η * (Set.indicator (⋂ j ∈ S.erase i, bigEvent c ε n j) (fun _ => (1:ℝ)) α
                * Set.indicator (bigEvent c ε n i) (fun _ => (1:ℝ)) α)
            + 2 * (Set.indicator (⋂ j ∈ S.erase i, bigEvent c ε n j) (fun _ => (1:ℝ)) α
                * Set.indicator (bigEvent c R n i) (fun _ => (1:ℝ)) α)) := by ring
    _ = (5:ℝ) ^ (S.card - 1) *
          (η * Set.indicator (tupleBigEvent c ε n S) (fun _ => (1:ℝ)) α
            + 2 * Set.indicator (mixedEvent c ε R n S i) (fun _ => (1:ℝ)) α) := by
        rw [indicator_mul_indicator, indicator_mul_indicator, hS, mixedEvent]

/-! ## Integrating the two errors -/

lemma norm_stepFactor_le_crude (c : ℝ) {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ)
    (n j : ℕ) (α : ℝ) : ‖stepFactor c w E n j α‖ ≤ ∑ i, ‖w i‖ := by
  classical
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg (w i))) (le_of_eq (mul_one _))
  by_cases h : α ∈ bulkMarkEvent c n (E i) j
  · rw [Set.indicator_of_mem h, norm_one]
  · rw [Set.indicator_of_notMem h, norm_zero]; norm_num

lemma integrableOn_prod_stepFactor (c : ℝ) {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (n : ℕ) (S : Finset ℕ) :
    IntegrableOn (fun α : ℝ => ∏ j ∈ S, stepFactor c w E n j α) (Ioo (0:ℝ) 1) volume := by
  classical
  have hmeas : Measurable (fun α : ℝ => ∏ j ∈ S, stepFactor c w E n j α) :=
    Finset.measurable_prod _ (fun j _ => measurable_stepFactor c w hE n j)
  refine Measure.integrableOn_of_bounded (M := (∑ i, ‖w i‖) ^ S.card) (by simp [Real.volume_Ioo])
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun α => ?_)
  rw [norm_prod]
  refine le_trans (Finset.prod_le_prod (fun j _ => norm_nonneg _)
    (fun j _ => norm_stepFactor_le_crude c w E n j α)) ?_
  rw [Finset.prod_const]

lemma integrableOn_error_bound (c ε R η : ℝ) (n : ℕ) (S : Finset ℕ) :
    IntegrableOn (fun α : ℝ => ∑ i ∈ S, (5:ℝ) ^ (S.card - 1) *
      (η * Set.indicator (tupleBigEvent c ε n S) (fun _ => (1:ℝ)) α
        + 2 * Set.indicator (mixedEvent c ε R n S i) (fun _ => (1:ℝ)) α))
      (Ioo (0:ℝ) 1) volume := by
  classical
  refine integrable_finset_sum _ (fun i _ => ?_)
  refine Integrable.const_mul ?_ _
  refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
  · exact SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_tupleBigEvent c ε n S)
  · exact SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_mixedEvent c ε R n S i)

lemma integral_error_bound (c ε R η : ℝ) (n : ℕ) (S : Finset ℕ) :
    (∫ α in Ioo (0:ℝ) 1, ∑ i ∈ S, (5:ℝ) ^ (S.card - 1) *
      (η * Set.indicator (tupleBigEvent c ε n S) (fun _ => (1:ℝ)) α
        + 2 * Set.indicator (mixedEvent c ε R n S i) (fun _ => (1:ℝ)) α))
      = ∑ i ∈ S, (5:ℝ) ^ (S.card - 1) *
          (η * unifIoo.real (tupleBigEvent c ε n S)
            + 2 * unifIoo.real (mixedEvent c ε R n S i)) := by
  classical
  rw [integral_finset_sum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, integral_add (Integrable.const_mul
        (SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_tupleBigEvent c ε n S)) _)
      (Integrable.const_mul
        (SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_mixedEvent c ε R n S i)) _),
      integral_const_mul, integral_const_mul,
      SymbolLimit.setIntegral_indicator_unifIoo (measurableSet_tupleBigEvent c ε n S),
      SymbolLimit.setIntegral_indicator_unifIoo (measurableSet_mixedEvent c ε R n S i)]
  · refine Integrable.const_mul ?_ _
    refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
    · exact SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_tupleBigEvent c ε n S)
    · exact SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_mixedEvent c ε R n S i)

/-- **The symbol swap inside the integral.** -/
theorem norm_integral_swap_le {t ε R η : ℝ} (hη0 : 0 ≤ η) (hεR : ε ≤ R) (hη1 : η ≤ 1)
    {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ} (hEm : ∀ i, MeasurableSet (E i))
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x)
    (c : ℝ) (n : ℕ) (S : Finset ℕ) :
    ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
        - ∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w E n j α‖
      ≤ ∑ i ∈ S, (5:ℝ) ^ (S.card - 1) *
          (η * unifIoo.real (tupleBigEvent c ε n S)
            + 2 * unifIoo.real (mixedEvent c ε R n S i)) := by
  classical
  rw [← integral_sub (integrableOn_prod_jumpFactor t c ε n S)
    (integrableOn_prod_stepFactor c w hEm n S)]
  refine le_trans (norm_integral_le_of_norm_le (integrableOn_error_bound c ε R η n S)
    (Filter.Eventually.of_forall (fun α =>
      norm_prod_jumpFactor_sub_prod_stepFactor_le hη0 hεR hη1 w E hpt c n S α)))
    (le_of_eq (integral_error_bound c ε R η n S))


/-! ## The same swap inside the product of one-level means -/

lemma integrableOn_jumpFactor (t c ε : ℝ) (n j : ℕ) :
    IntegrableOn (fun α : ℝ => jumpFactor t c ε n j α) (Ioo (0:ℝ) 1) volume := by
  have h := integrableOn_prod_jumpFactor t c ε n ({j} : Finset ℕ)
  simpa using h

lemma integrableOn_stepFactor (c : ℝ) {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (n j : ℕ) :
    IntegrableOn (fun α : ℝ => stepFactor c w E n j α) (Ioo (0:ℝ) 1) volume := by
  have h := integrableOn_prod_stepFactor c w hE n ({j} : Finset ℕ)
  simpa using h

lemma norm_mu_le_mass (t c ε : ℝ) (n j : ℕ) :
    ‖LayerAssembly.mu t c ε n j‖ ≤ 5 * unifIoo.real (bigEvent c ε n j) := by
  have h := norm_integral_le_of_norm_le
    ((SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_bigEvent c ε n j)).const_mul 5)
    (Filter.Eventually.of_forall (fun α => norm_jumpFactor_le_indicator t c ε n j α))
  refine le_trans h (le_of_eq ?_)
  rw [integral_const_mul, SymbolLimit.setIntegral_indicator_unifIoo
    (measurableSet_bigEvent c ε n j)]

lemma norm_integral_stepFactor_le_mass {t ε R η : ℝ} (hεR : ε ≤ R) (hη1 : η ≤ 1)
    {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ)
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x)
    (c : ℝ) (n j : ℕ) :
    ‖∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α‖ ≤ 5 * unifIoo.real (bigEvent c ε n j) := by
  have h := norm_integral_le_of_norm_le
    ((SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_bigEvent c ε n j)).const_mul 5)
    (Filter.Eventually.of_forall (fun α => norm_stepFactor_le hεR hη1 w E hpt c n j α))
  refine le_trans h (le_of_eq ?_)
  rw [integral_const_mul, SymbolLimit.setIntegral_indicator_unifIoo
    (measurableSet_bigEvent c ε n j)]

lemma norm_mu_sub_integral_stepFactor_le {t ε R η : ℝ} (hη0 : 0 ≤ η)
    {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ} (hEm : ∀ i, MeasurableSet (E i))
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x)
    (c : ℝ) (n j : ℕ) :
    ‖LayerAssembly.mu t c ε n j - ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α‖
      ≤ η * unifIoo.real (bigEvent c ε n j) + 2 * unifIoo.real (bigEvent c R n j) := by
  rw [LayerAssembly.mu, ← integral_sub (integrableOn_jumpFactor t c ε n j)
    (integrableOn_stepFactor c w hEm n j)]
  have hint : IntegrableOn (fun α : ℝ =>
      η * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α
        + 2 * Set.indicator (bigEvent c R n j) (fun _ => (1:ℝ)) α) (Ioo (0:ℝ) 1) volume :=
    Integrable.add
      ((SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_bigEvent c ε n j)).const_mul η)
      ((SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_bigEvent c R n j)).const_mul 2)
  refine le_trans (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall
    (fun α => norm_jumpFactor_sub_stepFactor_le hη0 w E hpt c n j α))) (le_of_eq ?_)
  rw [integral_add
      ((SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_bigEvent c ε n j)).const_mul η)
      ((SymbolLimit.integrableOn_indicator_unifIoo (measurableSet_bigEvent c R n j)).const_mul 2),
    integral_const_mul, integral_const_mul,
    SymbolLimit.setIntegral_indicator_unifIoo (measurableSet_bigEvent c ε n j),
    SymbolLimit.setIntegral_indicator_unifIoo (measurableSet_bigEvent c R n j)]

/-- **The symbol swap inside the product of one-level means.** -/
theorem norm_prod_mean_swap_le {t ε R η : ℝ} (hη0 : 0 ≤ η) (hεR : ε ≤ R) (hη1 : η ≤ 1)
    {M : ℕ} (w : Fin M → ℂ) {E : Fin M → Set ℝ} (hEm : ∀ i, MeasurableSet (E i))
    (hpt : ∀ x : ℝ, ‖SymbolLimit.psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x)
    (c : ℝ) (n : ℕ) (S : Finset ℕ) :
    ‖(∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α)
        - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖
      ≤ ∑ i ∈ S, (5:ℝ) ^ (S.card - 1)
          * (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
          * (η * unifIoo.real (bigEvent c ε n i) + 2 * unifIoo.real (bigEvent c R n i)) := by
  classical
  have htel := PatternSum.norm_prod_sub_prod_le (K := ℂ) S
    (fun j => ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α)
    (fun j => LayerAssembly.mu t c ε n j)
    (fun j => 5 * unifIoo.real (bigEvent c ε n j))
    (fun j _ => norm_integral_stepFactor_le_mass hεR hη1 w E hpt c n j)
    (fun j _ => norm_mu_le_mass t c ε n j)
  refine le_trans htel (Finset.sum_le_sum (fun i hi => ?_))
  have hcard : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
  have hprod : (∏ j ∈ S.erase i, 5 * unifIoo.real (bigEvent c ε n j))
      = (5:ℝ) ^ (S.card - 1) * ∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have h5 : (0:ℝ) ≤ (5:ℝ) ^ (S.card - 1) := by positivity
  have hp0 : (0:ℝ) ≤ ∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j) :=
    Finset.prod_nonneg (fun j _ =>
      (measureReal_nonneg : (0:ℝ) ≤ unifIoo.real (bigEvent c ε n j)))
  have h := norm_mu_sub_integral_stepFactor_le hη0 w hEm hpt c n i
  rw [norm_sub_rev] at h
  rw [hprod]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg h5 hp0)

/-! ## The step-symbol defect at a level set, in the pattern currency -/

theorem norm_stepDefect_at_levelSet {n k : ℕ} (c : ℝ) {M : ℕ} (w : Fin M → ℂ)
    {E : Fin M → Set ℝ} (hEm : ∀ i, MeasurableSet (E i)) {S : Finset ℕ}
    (hsub : S ⊆ Finset.range (n + 1)) (hcard : S.card = k) :
    ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w E n j α)
        - ∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α‖
      ≤ ∑ u : Fin k → Fin M, (∏ ℓ, ‖w (u ℓ)‖)
          * |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (E (u ℓ))
                (embTuple (sortEmb hsub hcard) ℓ))
              - ∏ ℓ, unifIoo.real (bulkMarkEvent c n (E (u ℓ))
                  (embTuple (sortEmb hsub hcard) ℓ))| := by
  classical
  have h1 : (∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w E n j α)
      = ∫ α in Ioo (0:ℝ) 1, ∏ ℓ, stepFactor c w E n (embTuple (sortEmb hsub hcard) ℓ) α := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
    exact (prod_orderEmb hcard (fun j => stepFactor c w E n j α)).symm
  have h2 : (∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α)
      = ∏ ℓ, ∫ α in Ioo (0:ℝ) 1,
          stepFactor c w E n (embTuple (sortEmb hsub hcard) ℓ) α :=
    (prod_orderEmb hcard (fun j => ∫ α in Ioo (0:ℝ) 1, stepFactor c w E n j α)).symm
  rw [h1, h2]
  exact norm_stepDefect_le c w hEm n (embTuple (sortEmb hsub hcard))

end

end QuasiIndep

end Kwon1002
