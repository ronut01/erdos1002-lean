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


/-! ## Counting the level sets

All four counts run over the **capped** level range `min (n+1) (lameCap n)`,
which is `O(L)` deterministically; that is what makes a `k`-fold layer bounded
rather than growing with `n`. -/

/-- The capped level range. -/
def capRange (n : ℕ) : Finset ℕ := Finset.range (min (n + 1) (lameCap n))

lemma capRange_subset (n : ℕ) : capRange n ⊆ Finset.range (n + 1) := by
  intro x hx
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (min_le_left _ _))

lemma card_capRange_le {n : ℕ} (hL : 3 ≤ Lnorm n) : ((capRange n).card : ℝ) ≤ 4 * Lnorm n := by
  rw [capRange, Finset.card_range]
  refine le_trans ?_ (lameCap_le hL)
  exact_mod_cast Nat.cast_le.mpr (min_le_right (n + 1) (lameCap n))

/-- Count 1: the total tuple mass of a `k`-layer. -/
lemma count_tupleBig {c ε C₁ : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁) {n : ℕ} (k : ℕ)
    (hL : 3 ≤ Lnorm n)
    (hrad : ∀ rad : ℕ → ℝ, (∀ j, ε ≤ rad j) → ∀ S : Finset ℕ,
      unifIoo.real (⋂ j ∈ S, bigEvent c (rad j) n j) ≤ ∏ j ∈ S, (C₁ / (8 * rad j) / Lnorm n)) :
    (∑ S ∈ Finset.powersetCard k (capRange n), unifIoo.real (tupleBigEvent c ε n S))
      ≤ (4 * (C₁ / (8 * ε))) ^ k / (Nat.factorial k) := by
  classical
  have hL0 : (0:ℝ) < Lnorm n := by linarith
  have hCε : (0:ℝ) ≤ C₁ / (8 * ε) / Lnorm n := by positivity
  have hterm : ∀ S ∈ Finset.powersetCard k (capRange n),
      unifIoo.real (tupleBigEvent c ε n S) ≤ (C₁ / (8 * ε) / Lnorm n) ^ k := by
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have h := hrad (fun _ => ε) (fun _ => le_refl ε) S
    rw [Finset.prod_const, hcard] at h
    exact h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  have hchoose : (((capRange n).card.choose k : ℕ) : ℝ)
      ≤ ((capRange n).card : ℝ) ^ k / (Nat.factorial k) := Nat.choose_le_pow_div k _
  have hfac : (0:ℝ) < (Nat.factorial k) := by exact_mod_cast Nat.factorial_pos k
  refine le_trans (mul_le_mul_of_nonneg_right hchoose (by positivity)) ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hfac]
  have hkey : ((capRange n).card : ℝ) ^ k * (C₁ / (8 * ε) / Lnorm n) ^ k
      = (((capRange n).card : ℝ) * (C₁ / (8 * ε) / Lnorm n)) ^ k := by rw [mul_pow]
  rw [hkey]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have h8 : ((capRange n).card : ℝ) * (C₁ / (8 * ε) / Lnorm n)
      ≤ (4 * Lnorm n) * (C₁ / (8 * ε) / Lnorm n) :=
    mul_le_mul_of_nonneg_right (card_capRange_le hL) hCε
  refine le_trans h8 (le_of_eq ?_)
  field_simp

/-- Count 2: the total mixed-radius mass of a `k`-layer, with the `R`-tail
exhibited. -/
lemma count_mixed {c ε R C₁ : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hC₁ : 0 < C₁) {n : ℕ} (k' : ℕ)
    (hL : 3 ≤ Lnorm n)
    (hrad : ∀ rad : ℕ → ℝ, (∀ j, ε ≤ rad j) → ∀ S : Finset ℕ,
      unifIoo.real (⋂ j ∈ S, bigEvent c (rad j) n j) ≤ ∏ j ∈ S, (C₁ / (8 * rad j) / Lnorm n)) :
    (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
        ∑ i ∈ S, unifIoo.real (mixedEvent c ε R n S i))
      ≤ 4 ^ (k' + 1) * ((C₁ / (8 * ε)) ^ k' * (C₁ / (8 * R))) / (Nat.factorial k') := by
  classical
  have hL0 : (0:ℝ) < Lnorm n := by linarith
  have hR : (0:ℝ) < R := lt_of_lt_of_le hε hεR
  rw [← LayerAssembly.sum_powersetCard_sdiff_insert (capRange n) k'
    (fun S i => unifIoo.real (mixedEvent c ε R n S i))]
  have hterm : ∀ S ∈ Finset.powersetCard k' (capRange n), ∀ i ∈ capRange n \ S,
      unifIoo.real (mixedEvent c ε R n (insert i S) i)
        ≤ (C₁ / (8 * ε) / Lnorm n) ^ k' * (C₁ / (8 * R) / Lnorm n) := by
    intro S hS i hi
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
    have hcard : S.card = k' := (Finset.mem_powersetCard.mp hS).2
    set rad : ℕ → ℝ := fun j => if j = i then R else ε with hraddef
    have hrad0 : ∀ j, ε ≤ rad j := by
      intro j; simp only [hraddef]; split <;> [exact hεR; exact le_refl ε]
    have hset : mixedEvent c ε R n (insert i S) i
        = ⋂ j ∈ insert i S, bigEvent c (rad j) n j := by
      rw [mixedEvent, Finset.erase_insert hiS, Finset.set_biInter_insert]
      have hi' : rad i = R := by simp [hraddef]
      have hS' : (⋂ j ∈ S, bigEvent c (rad j) n j) = ⋂ j ∈ S, bigEvent c ε n j := by
        refine Set.iInter₂_congr (fun j hj => ?_)
        have : j ≠ i := fun h => hiS (h ▸ hj)
        simp [hraddef, this]
      rw [hi', hS', Set.inter_comm]
    rw [hset]
    refine le_trans (hrad rad hrad0 (insert i S)) (le_of_eq ?_)
    rw [Finset.prod_insert hiS]
    have hi' : rad i = R := by simp [hraddef]
    have hS' : (∏ j ∈ S, (C₁ / (8 * rad j) / Lnorm n))
        = ∏ j ∈ S, (C₁ / (8 * ε) / Lnorm n) := by
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have : j ≠ i := fun h => hiS (h ▸ hj)
      simp [hraddef, this]
    rw [hi', hS', Finset.prod_const, hcard]
    ring
  refine le_trans (Finset.sum_le_sum (fun S hS =>
    Finset.sum_le_sum (fun i hi => hterm S hS i hi))) ?_
  have hconst : ∀ S ∈ Finset.powersetCard k' (capRange n),
      (∑ _i ∈ capRange n \ S, (C₁ / (8 * ε) / Lnorm n) ^ k' * (C₁ / (8 * R) / Lnorm n))
        ≤ (4 * Lnorm n) * ((C₁ / (8 * ε) / Lnorm n) ^ k' * (C₁ / (8 * R) / Lnorm n)) := by
    intro S _
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine le_trans ?_ (card_capRange_le hL)
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (Finset.sdiff_subset))
  refine le_trans (Finset.sum_le_sum hconst) ?_
  rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  have hchoose : (((capRange n).card.choose k' : ℕ) : ℝ)
      ≤ ((capRange n).card : ℝ) ^ k' / (Nat.factorial k') := Nat.choose_le_pow_div k' _
  have hfac : (0:ℝ) < (Nat.factorial k') := by exact_mod_cast Nat.factorial_pos k'
  refine le_trans (mul_le_mul_of_nonneg_right hchoose (by positivity)) ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hfac]
  have hcap : ((capRange n).card : ℝ) ^ k' ≤ (4 * Lnorm n) ^ k' :=
    pow_le_pow_left₀ (by positivity) (card_capRange_le hL) k'
  have hnn : (0:ℝ) ≤ (4 * Lnorm n) * ((C₁ / (8 * ε) / Lnorm n) ^ k' * (C₁ / (8 * R) / Lnorm n)) := by
    positivity
  refine le_trans (mul_le_mul_of_nonneg_right hcap hnn) (le_of_eq ?_)
  have hLne : Lnorm n ≠ 0 := ne_of_gt hL0
  have hcancel : (Lnorm n) ^ k' * ((Lnorm n)⁻¹) ^ k' = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hLne, one_pow]
  field_simp
  linear_combination (C₁ ^ k' * (ε⁻¹) ^ k' * ((1:ℝ) / 8) ^ k' * 4 ^ k' * 4) * hcancel

/-- Count 3: the near part of the product of one-level means. -/
lemma count_prod_near {c ε Λ : ℝ} {n k : ℕ}
    (hmass : (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c ε n j)) ≤ Λ) :
    (∑ S ∈ Finset.powersetCard k (capRange n),
        ∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
          * unifIoo.real (bigEvent c ε n i))
      ≤ (k : ℝ) * Real.exp Λ := by
  classical
  have hstep : ∀ S ∈ Finset.powersetCard k (capRange n),
      (∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
          * unifIoo.real (bigEvent c ε n i))
        = (k : ℝ) * ∏ j ∈ S, unifIoo.real (bigEvent c ε n j) := by
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have h : ∀ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
        * unifIoo.real (bigEvent c ε n i) = ∏ j ∈ S, unifIoo.real (bigEvent c ε n j) :=
      fun i hi => Finset.prod_erase_mul S _ hi
    rw [Finset.sum_congr rfl h, Finset.sum_const, hcard, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg k)
  refine le_trans (LayerAssembly.esymm_le_exp (capRange n) k
    (fun j => unifIoo.real (bigEvent c ε n j)) (fun j => measureReal_nonneg)) ?_
  refine Real.exp_le_exp.mpr (le_trans ?_ hmass)
  exact Finset.sum_le_sum_of_subset_of_nonneg (capRange_subset n)
    (fun j _ _ => measureReal_nonneg)

/-- Count 4: the far part of the product of one-level means. -/
lemma count_prod_far {c ε R Λ ΛR : ℝ} {n k' : ℕ}
    (hmass : (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c ε n j)) ≤ Λ)
    (hmassR : (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c R n j)) ≤ ΛR)
    (hΛR : 0 ≤ ΛR) :
    (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
        ∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
          * unifIoo.real (bigEvent c R n i))
      ≤ Real.exp Λ * ΛR := by
  classical
  rw [← LayerAssembly.sum_powersetCard_sdiff_insert (capRange n) k'
    (fun S i => (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
      * unifIoo.real (bigEvent c R n i))]
  have hstep : ∀ S ∈ Finset.powersetCard k' (capRange n),
      (∑ i ∈ capRange n \ S, (∏ j ∈ (insert i S).erase i, unifIoo.real (bigEvent c ε n j))
          * unifIoo.real (bigEvent c R n i))
        ≤ (∏ j ∈ S, unifIoo.real (bigEvent c ε n j)) * ΛR := by
    intro S hS
    have h : ∀ i ∈ capRange n \ S,
        (∏ j ∈ (insert i S).erase i, unifIoo.real (bigEvent c ε n j))
          * unifIoo.real (bigEvent c R n i)
        = (∏ j ∈ S, unifIoo.real (bigEvent c ε n j)) * unifIoo.real (bigEvent c R n i) := by
      intro i hi
      rw [Finset.erase_insert (Finset.mem_sdiff.mp hi).2]
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_
      (Finset.prod_nonneg (fun j _ =>
        (measureReal_nonneg : (0:ℝ) ≤ unifIoo.real (bigEvent c ε n j))))
    refine le_trans ?_ hmassR
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => measureReal_nonneg)
    exact fun x hx => capRange_subset n (Finset.sdiff_subset hx)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hΛR
  refine le_trans (LayerAssembly.esymm_le_exp (capRange n) k'
    (fun j => unifIoo.real (bigEvent c ε n j)) (fun j => measureReal_nonneg)) ?_
  refine Real.exp_le_exp.mpr (le_trans ?_ hmass)
  exact Finset.sum_le_sum_of_subset_of_nonneg (capRange_subset n)
    (fun j _ _ => measureReal_nonneg)


/-! ## Padding the cell family, and a uniform interval count -/

lemma exists_uniform_interval_count {M : ℕ} (E : Fin M → Set ℝ)
    (h : ∀ i, IntervalClass.IsFiniteUnionOfIntervals (E i)) :
    ∃ m : ℕ, ∀ i, IntervalClass.IsUnionOfIntervals m (E i) := by
  classical
  choose mm hmm using h
  exact ⟨Finset.univ.sup mm, fun i => (hmm i).mono (Finset.le_sup (Finset.mem_univ i))⟩

lemma sum_cons_step {M : ℕ} (w : Fin M → ℂ) (E : Fin M → Set ℝ) (x : ℝ) :
    (∑ i : Fin (M + 1), (Fin.cons (0:ℂ) w : Fin (M + 1) → ℂ) i
        * Set.indicator ((Fin.cons (∅ : Set ℝ) E : Fin (M + 1) → Set ℝ) i) (fun _ => (1:ℂ)) x)
      = ∑ i : Fin M, w i * Set.indicator (E i) (fun _ => (1:ℂ)) x := by
  rw [Fin.sum_univ_succ]
  simp

/-! ## The subset quasi-independence of the complex symbol -/

/-- **`hqi` for the symbol `x ↦ (e^{itx} − 1)1{|x| > ε}`.**

For every `k`, the `k`-subset quasi-independence defect of the large-jump
factors tends to `0`.  The three errors are, in order: the mesh `η` and the
truncation `R` of the step approximation, both paid against the tuple masses of
`Kwon1002.QuasiIndep.exists_tuple_bound_radii`; and the quasi-independence of
the step symbol itself, paid by
`Kwon1002.StepQuasi.exists_bulk_quasi_pattern` once per cell pattern. -/
theorem hqi (c : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        ∑ S ∈ Finset.powersetCard k (Finset.range (n + 1)),
          ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
              - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖) atTop (𝓝 0) := by
  classical
  obtain _ | k' := k
  · -- the empty layer contributes nothing
    have hzero : ∀ n : ℕ, (∑ S ∈ Finset.powersetCard 0 (Finset.range (n + 1)),
        ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
            - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖) = 0 := by
      intro n
      rw [Finset.powersetCard_zero]
      simp only [Finset.sum_singleton, Finset.prod_empty]
      rw [setIntegral_const]
      simp
    simpa [hzero] using tendsto_const_nhds (α := ℕ) (x := (0:ℝ))
  obtain ⟨C₀, hC₀, hbnd⟩ := SymbolLimit.exists_tupleBigEvent_bound_uniform c
  obtain ⟨C₁, hC₁, hradAll⟩ := exists_tuple_bound_radii c
  set Λ : ℝ := C₀ / (2 * ε) with hΛ
  set Cε : ℝ := C₁ / (8 * ε) with hCε
  set P : ℝ := (5:ℝ) ^ k' with hP
  set K1 : ℝ := P * ((k' + 1 : ℝ) * ((4 * Cε) ^ (k' + 1) / (Nat.factorial (k' + 1))
    + Real.exp Λ)) with hK1def
  set K2 : ℝ := P * 2 * (4 ^ (k' + 1) * (Cε ^ k' * (C₁ / 8)) / (Nat.factorial k')
    + Real.exp Λ * (C₀ / 2)) with hK2def
  have hP0 : 0 < P := by rw [hP]; positivity
  have hCε0 : 0 < Cε := by rw [hCε]; positivity
  have hK10 : 0 < K1 := by
    rw [hK1def]
    have : (0:ℝ) < (4 * Cε) ^ (k' + 1) / (Nat.factorial (k' + 1)) := by
      have : (0:ℝ) < (Nat.factorial (k' + 1)) := by exact_mod_cast Nat.factorial_pos _
      positivity
    have hexp : (0:ℝ) < Real.exp Λ := Real.exp_pos _
    have hk1 : (0:ℝ) < (k' + 1 : ℝ) := by positivity
    positivity
  have hK20 : 0 ≤ K2 := by
    rw [hK2def]
    have hfac : (0:ℝ) < (Nat.factorial k') := by exact_mod_cast Nat.factorial_pos _
    have hexp : (0:ℝ) < Real.exp Λ := Real.exp_pos _
    positivity
  rw [Metric.tendsto_atTop]
  intro γ hγ
  -- the truncation radius
  obtain ⟨R, hR1, hR2⟩ : ∃ R : ℝ, ε < R ∧ K2 / R < γ / 3 := by
    refine ⟨max (ε + 1) (3 * K2 / γ + 1), ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · have hR0 : (0:ℝ) < max (ε + 1) (3 * K2 / γ + 1) :=
        lt_of_lt_of_le (by linarith) (le_max_left _ _)
      rw [div_lt_iff₀ hR0]
      have h1 : 3 * K2 / γ + 1 ≤ max (ε + 1) (3 * K2 / γ + 1) := le_max_right _ _
      have h2 : K2 = γ / 3 * (3 * K2 / γ) := by field_simp
      nlinarith [le_of_lt hγ, hK20]
  -- the mesh
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ K1 * η < γ / 3 := by
    refine ⟨min 1 (γ / (6 * K1)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
    have h1 : min 1 (γ / (6 * K1)) ≤ γ / (6 * K1) := min_le_right _ _
    have h2 : K1 * (γ / (6 * K1)) = γ / 6 := by field_simp
    nlinarith [le_of_lt hγ, le_of_lt hK10]
  -- the step approximation, padded to a nonempty cell family
  obtain ⟨M, w, E, hEm, hEsub, hEi, hpt⟩ := SymbolLimit.exists_step_approx t hε hR1 hη0
  set w' : Fin (M + 1) → ℂ := (Fin.cons (0:ℂ) w : Fin (M + 1) → ℂ) with hw'
  set E' : Fin (M + 1) → Set ℝ := (Fin.cons (∅ : Set ℝ) E : Fin (M + 1) → Set ℝ) with hE'
  have hpt' : ∀ x : ℝ,
      ‖SymbolLimit.psi t ε x - ∑ i, w' i * Set.indicator (E' i) (fun _ => (1:ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1:ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1:ℝ)) x := by
    intro x
    rw [hw', hE', sum_cons_step w E x]
    exact hpt x
  have hEm' : ∀ i, MeasurableSet (E' i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [hE'] using MeasurableSet.empty
    · intro j; simpa [hE'] using hEm j
  have hEi' : ∀ i, IntervalClass.IsFiniteUnionOfIntervals (E' i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [hE'] using (IntervalClass.isUnionOfIntervals_empty 0).finite
    · intro j; simpa [hE'] using hEi j
  have hEδ : ∀ i, ∀ y ∈ E' i, ε ≤ |y| := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [hE']
    · intro j y hy
      have := hEsub j (by simpa [hE'] using hy)
      exact le_of_lt this.1
  obtain ⟨m, hm⟩ := exists_uniform_interval_count E' hEi'
  set W : ℝ := ∑ i, ‖w' i‖ with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  obtain ⟨majB, hmajBlim, hmajB⟩ :=
    StepQuasi.exists_bulk_quasi_pattern c m (k' + 1) (M + 1) hε (Nat.succ_pos M)
  -- the eventual estimate
  have hmain : ∀ᶠ n : ℕ in atTop,
      (∑ S ∈ Finset.powersetCard (k' + 1) (Finset.range (n + 1)),
        ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
            - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖)
        ≤ K1 * η + K2 / R + W ^ (k' + 1) * majB n := by
    filter_upwards [eventually_ge_atTop 1,
      TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop (3:ℝ),
      hradAll ε hε, SymbolLimit.eventually_sum_bigEvent_mass c hbnd hC₀ hε,
      SymbolLimit.eventually_sum_bigEvent_mass c hbnd hC₀ (lt_trans hε hR1), hmajB]
      with n hn1 hLn hradn hmassε hmassR hmajBn
    -- only the capped level range contributes
    have hcapeq : (∑ S ∈ Finset.powersetCard (k' + 1) (Finset.range (n + 1)),
        ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
            - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖)
        = ∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
            ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
              - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖ := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro S hS
        rw [Finset.mem_powersetCard] at hS ⊢
        exact ⟨fun x hx => capRange_subset n (hS.1 hx), hS.2⟩
      · intro S hS hSnot
        rw [Finset.mem_powersetCard] at hS
        have hnsub : ¬ S ⊆ capRange n := fun hsub =>
          hSnot (Finset.mem_powersetCard.mpr ⟨hsub, hS.2⟩)
        obtain ⟨j, hjS, hj⟩ := Finset.not_subset.mp hnsub
        have hjn : j < n + 1 := Finset.mem_range.mp (hS.1 hjS)
        have hjc : lameCap n ≤ j := by
          rw [capRange, Finset.mem_range, not_lt] at hj
          omega
        rw [integral_prod_jumpFactor_eq_zero_of_lameCap t c ε hn1 S hjS hjc,
          Finset.prod_eq_zero hjS (LayerAssembly.mu_eq_zero_of_lameCap t c ε hn1 hjc)]
        simp
    rw [hcapeq]
    -- the three-term split at each level set
    have hsplit : ∀ S ∈ Finset.powersetCard (k' + 1) (capRange n),
        ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
            - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖
        ≤ (∑ i ∈ S, (5:ℝ) ^ (S.card - 1) * (η * unifIoo.real (tupleBigEvent c ε n S)
              + 2 * unifIoo.real (mixedEvent c ε R n S i)))
          + ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w' E' n j α)
              - ∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w' E' n j α‖
          + (∑ i ∈ S, (5:ℝ) ^ (S.card - 1)
              * (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
              * (η * unifIoo.real (bigEvent c ε n i)
                  + 2 * unifIoo.real (bigEvent c R n i))) := by
      intro S _
      have h1 := norm_integral_swap_le hη0.le (le_of_lt hR1) hη1 w' hEm' hpt' c n S
      have h3 := norm_prod_mean_swap_le hη0.le (le_of_lt hR1) hη1 w' hEm' hpt' c n S
      have hdec : (∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
            - ∏ j ∈ S, LayerAssembly.mu t c ε n j
          = ((∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
              - ∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w' E' n j α)
            + ((∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w' E' n j α)
              - ∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w' E' n j α)
            + ((∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w' E' n j α)
              - ∏ j ∈ S, LayerAssembly.mu t c ε n j) := by ring
      rw [hdec]
      refine le_trans (norm_add₃_le) ?_
      linarith
    refine le_trans (Finset.sum_le_sum hsplit) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- the three aggregate bounds
    have hAeq : (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
          ∑ i ∈ S, (5:ℝ) ^ (S.card - 1) * (η * unifIoo.real (tupleBigEvent c ε n S)
            + 2 * unifIoo.real (mixedEvent c ε R n S i)))
        = P * η * (k' + 1 : ℝ)
            * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
                unifIoo.real (tupleBigEvent c ε n S))
          + P * 2 * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
              ∑ i ∈ S, unifIoo.real (mixedEvent c ε R n S i)) := by
      have hterm : ∀ S ∈ Finset.powersetCard (k' + 1) (capRange n),
          (∑ i ∈ S, (5:ℝ) ^ (S.card - 1) * (η * unifIoo.real (tupleBigEvent c ε n S)
              + 2 * unifIoo.real (mixedEvent c ε R n S i)))
            = P * η * (k' + 1 : ℝ) * unifIoo.real (tupleBigEvent c ε n S)
              + P * 2 * ∑ i ∈ S, unifIoo.real (mixedEvent c ε R n S i) := by
        intro S hS
        have hcard : S.card = k' + 1 := (Finset.mem_powersetCard.mp hS).2
        have hpow : (5:ℝ) ^ (S.card - 1) = P := by rw [hcard, Nat.add_sub_cancel, hP]
        have hstep : ∀ i ∈ S, (5:ℝ) ^ (S.card - 1) * (η * unifIoo.real (tupleBigEvent c ε n S)
              + 2 * unifIoo.real (mixedEvent c ε R n S i))
            = P * η * unifIoo.real (tupleBigEvent c ε n S)
              + P * 2 * unifIoo.real (mixedEvent c ε R n S i) := by
          intro i _; rw [hpow]; ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const, hcard,
          nsmul_eq_mul, ← Finset.mul_sum]
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hCeq : (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
          ∑ i ∈ S, (5:ℝ) ^ (S.card - 1)
            * (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
            * (η * unifIoo.real (bigEvent c ε n i) + 2 * unifIoo.real (bigEvent c R n i)))
        = P * η * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
              ∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
                * unifIoo.real (bigEvent c ε n i))
          + P * 2 * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
              ∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
                * unifIoo.real (bigEvent c R n i)) := by
      have hterm : ∀ S ∈ Finset.powersetCard (k' + 1) (capRange n),
          (∑ i ∈ S, (5:ℝ) ^ (S.card - 1)
              * (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
              * (η * unifIoo.real (bigEvent c ε n i) + 2 * unifIoo.real (bigEvent c R n i)))
            = P * η * (∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
                * unifIoo.real (bigEvent c ε n i))
              + P * 2 * (∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
                * unifIoo.real (bigEvent c R n i)) := by
        intro S hS
        have hcard : S.card = k' + 1 := (Finset.mem_powersetCard.mp hS).2
        have hpow : (5:ℝ) ^ (S.card - 1) = P := by rw [hcard, Nat.add_sub_cancel, hP]
        have hstep : ∀ i ∈ S, (5:ℝ) ^ (S.card - 1)
              * (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
              * (η * unifIoo.real (bigEvent c ε n i) + 2 * unifIoo.real (bigEvent c R n i))
            = P * η * ((∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
                * unifIoo.real (bigEvent c ε n i))
              + P * 2 * ((∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
                * unifIoo.real (bigEvent c R n i)) := by
          intro i _; rw [hpow]; ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hAeq, hCeq]
    -- the four counts and the pattern bound
    have hcount1 := count_tupleBig (c := c) hε hC₁ (k' + 1) hLn hradn
    have hcount2 := count_mixed (c := c) hε (le_of_lt hR1) hC₁ k' hLn hradn
    have hcount3 := count_prod_near (c := c) (ε := ε) (Λ := Λ) (n := n) (k := k' + 1) hmassε
    have hcount4 := count_prod_far (c := c) (ε := ε) (R := R) (Λ := Λ) (ΛR := C₀ / (2 * R))
      (n := n) (k' := k') hmassε hmassR
      (div_nonneg hC₀.le (by linarith [lt_trans hε hR1]))
    have hB : (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
        ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w' E' n j α)
            - ∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w' E' n j α‖)
        ≤ W ^ (k' + 1) * majB n := by
      have hstep := sum_powersetCard_le_sum_emb (k := k' + 1) (capRange_subset n)
        (fun S => ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, stepFactor c w' E' n j α)
            - ∏ j ∈ S, ∫ α in Ioo (0:ℝ) 1, stepFactor c w' E' n j α‖)
        (fun f => ∑ u : Fin (k' + 1) → Fin (M + 1), (∏ ℓ, ‖w' (u ℓ)‖)
          * |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (E' (u ℓ)) (embTuple f ℓ))
              - ∏ ℓ, unifIoo.real (bulkMarkEvent c n (E' (u ℓ)) (embTuple f ℓ))|)
        (fun f => Finset.sum_nonneg (fun u _ =>
          mul_nonneg (Finset.prod_nonneg (fun ℓ _ => norm_nonneg _)) (abs_nonneg _)))
        (fun S hS => by
          refine ⟨sortEmb (fun x hx => capRange_subset n
              ((Finset.mem_powersetCard.mp hS).1 hx)) (Finset.mem_powersetCard.mp hS).2,
            image_embTuple_sortEmb _ _, ?_⟩
          exact norm_stepDefect_at_levelSet c w' hEm' _ _)
      refine le_trans hstep ?_
      rw [Finset.sum_comm]
      have hpat : ∀ u : Fin (k' + 1) → Fin (M + 1),
          (∑ f : Fin (k' + 1) ↪ (Finset.range (n + 1) : Finset ℕ), (∏ ℓ, ‖w' (u ℓ)‖)
            * |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (E' (u ℓ)) (embTuple f ℓ))
                - ∏ ℓ, unifIoo.real (bulkMarkEvent c n (E' (u ℓ)) (embTuple f ℓ))|)
            ≤ (∏ ℓ, ‖w' (u ℓ)‖) * majB n := by
        intro u
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg (fun ℓ _ => norm_nonneg _))
        exact hmajBn E' hEm' hm hEδ u
      refine le_trans (Finset.sum_le_sum (fun u _ => hpat u)) (le_of_eq ?_)
      rw [← Finset.sum_mul, hW, ← Fintype.piFinset_univ,
        ← Finset.prod_univ_sum (fun _ : Fin (k' + 1) => (Finset.univ : Finset (Fin (M + 1))))
          (fun _ i => ‖w' i‖),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- assembling
    have hΛR : C₀ / (2 * R) = (C₀ / 2) / R := by rw [div_div]
    have hCR : C₁ / (8 * R) = (C₁ / 8) / R := by rw [div_div]
    have hRpos : (0:ℝ) < R := lt_trans hε hR1
    have hid : P * η * (k' + 1 : ℝ) * ((4 * Cε) ^ (k' + 1) / (Nat.factorial (k' + 1)))
          + P * 2 * (4 ^ (k' + 1) * (Cε ^ k' * (C₁ / (8 * R))) / (Nat.factorial k'))
          + (P * η * ((k' + 1 : ℝ) * Real.exp Λ)
            + P * 2 * (Real.exp Λ * (C₀ / (2 * R))))
        = K1 * η + K2 / R := by
      rw [hK1def, hK2def, hΛR, hCR]
      field_simp
      ring
    have hn1' : (0:ℝ) ≤ P * η := by positivity
    have hn2' : (0:ℝ) ≤ P * 2 := by positivity
    have hmul1 : P * η * (k' + 1 : ℝ)
        * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
            unifIoo.real (tupleBigEvent c ε n S))
        ≤ P * η * (k' + 1 : ℝ) * ((4 * Cε) ^ (k' + 1) / (Nat.factorial (k' + 1))) := by
      refine mul_le_mul_of_nonneg_left hcount1 (by positivity)
    have hmul2 : P * 2 * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
          ∑ i ∈ S, unifIoo.real (mixedEvent c ε R n S i))
        ≤ P * 2 * (4 ^ (k' + 1) * (Cε ^ k' * (C₁ / (8 * R))) / (Nat.factorial k')) :=
      mul_le_mul_of_nonneg_left hcount2 hn2'
    have hmul3 : P * η * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
          ∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
            * unifIoo.real (bigEvent c ε n i))
        ≤ P * η * ((k' + 1 : ℝ) * Real.exp Λ) := by
      refine mul_le_mul_of_nonneg_left ?_ hn1'
      exact_mod_cast hcount3
    have hmul4 : P * 2 * (∑ S ∈ Finset.powersetCard (k' + 1) (capRange n),
          ∑ i ∈ S, (∏ j ∈ S.erase i, unifIoo.real (bigEvent c ε n j))
            * unifIoo.real (bigEvent c R n i))
        ≤ P * 2 * (Real.exp Λ * (C₀ / (2 * R))) :=
      mul_le_mul_of_nonneg_left hcount4 hn2'
    linarith
  -- and the conclusion
  have hlim : Tendsto (fun n : ℕ => K1 * η + K2 / R + W ^ (k' + 1) * majB n) atTop
      (𝓝 (K1 * η + K2 / R + W ^ (k' + 1) * 0)) :=
    tendsto_const_nhds.add ((hmajBlim.const_mul (W ^ (k' + 1))))
  rw [mul_zero, add_zero] at hlim
  have hev := (Metric.tendsto_atTop.mp hlim) (γ / 3) (by linarith)
  obtain ⟨N, hN⟩ := hev
  rw [Filter.eventually_atTop] at hmain
  obtain ⟨N', hN'⟩ := hmain
  refine ⟨max N N', fun n hn => ?_⟩
  have h1 := hN n (le_trans (le_max_left _ _) hn)
  have h2 := hN' n (le_trans (le_max_right _ _) hn)
  have hnn : (0:ℝ) ≤ ∑ S ∈ Finset.powersetCard (k' + 1) (Finset.range (n + 1)),
      ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
          - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖ :=
    Finset.sum_nonneg (fun S _ => norm_nonneg _)
  rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ _ - 0)]
  rw [Real.dist_eq] at h1
  have h3 : W ^ (k' + 1) * majB n < γ / 3 := by
    have habs := abs_lt.mp h1
    linarith [habs.2]
  linarith


/-! ## `CorFinal.largeSum_charFun_limit`, unconditionally

`SymbolLimit.largeSum_charFun_limit_of_hqi` carries the conclusion of
`Kwon1002.CorFinal.largeSum_charFun_limit` with `hqi` as its single hypothesis,
`hp1` having been discharged by `SymbolLimit.sum_mu_tendsto`.  With `hqi` proved
the statement is unconditional.

The `sorry` at `Kwon1002.CorFinal.largeSum_charFun_limit` itself cannot be shed:
`Kwon1002/FactorialRoute.lean` — and therefore the whole factorial route,
including this module — *imports* `Kwon1002/CorFinal.lean`, so the canonical
declaration sits strictly below its own proof.  The two anonymous `example`s
below are the guard: they carry one and the same statement text, and are closed
respectively by the canonical (sorried) declaration and by the theorem proved
here, so the two statements agree token for token. -/

/-- **DEBT 1, discharged.**  The fixed-`ε` large-jump characteristic-function
limit, with no hypotheses. -/
theorem largeSum_charFun_limit (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ α in Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Assembly5.largeSum c ε α n : ℂ) * Complex.I)) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) :=
  SymbolLimit.largeSum_charFun_limit_of_hqi c ε hε0 hε1 t (fun k => hqi c hε0 t k)

/-- Statement guard, half one: the text below is the statement of
`Kwon1002.CorFinal.largeSum_charFun_limit`.  The `example` mentions a sorried
declaration, so it is anonymous. -/
example : ∀ (c ε : ℝ), 0 < ε → ε < 1 → ∀ t : ℝ,
    Filter.Tendsto (fun n : ℕ => ∫ α in Set.Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Kwon1002.Assembly5.largeSum c ε α n : ℂ) * Complex.I)) Filter.atTop
      (nhds (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (Kwon1002.levyIntensityDensity x : ℂ)))) :=
  @Kwon1002.CorFinal.largeSum_charFun_limit

/-- Statement guard, half two: the same text, closed by the theorem proved in
this module. -/
example : ∀ (c ε : ℝ), 0 < ε → ε < 1 → ∀ t : ℝ,
    Filter.Tendsto (fun n : ℕ => ∫ α in Set.Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Kwon1002.Assembly5.largeSum c ε α n : ℂ) * Complex.I)) Filter.atTop
      (nhds (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (Kwon1002.levyIntensityDensity x : ℂ)))) :=
  @Kwon1002.QuasiIndep.largeSum_charFun_limit

end

end QuasiIndep

end Kwon1002
