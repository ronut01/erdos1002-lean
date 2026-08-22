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

end

end QuasiIndep

end Kwon1002
