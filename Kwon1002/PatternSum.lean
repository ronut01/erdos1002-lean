import Kwon1002.DetQuasiFamily

/-!
# Quasi-independence at a fixed **cell pattern**

`Kwon1002.WindowBridgeFamily.exists_window_bridge_family` and
`Kwon1002.DetQuasiFamily.exists_det_quasi_independence_family` bound their sums
over embeddings `f : Fin k ↪ {0,…,n}` uniformly over every **per-level** family
`E : ℕ → Set ℝ` of targets.  A multilinear expansion of a step symbol does not
produce a per-level family: expanding `∏_{ℓ} (∑_i w_i 1_{E_i})` assigns a cell
to each *position* `ℓ` of the tuple, and the assignment is the same for every
embedding.  The target at level `f ℓ` is then `C (u ℓ)`, which is a function of
the position, not of the level.

The gap is closed here by **averaging over level colourings**, not by redoing
either proof.  For a colouring `V` of the levels the per-level family
`j ↦ C (V j)` is admissible, so the family theorems bound
`∑_f a f (V ∘ f)`.  Summing that over all `M^{N}` colourings of the `N` levels
and counting, for each embedding, the `M^{N-k}` colourings that realise a
*prescribed* pattern `u` along `f`, gives

  `∑_f a f u ≤ M^k · maj n`

for every pattern `u` — `sum_emb_pattern_le` below, which is pure counting and
knows nothing about measures.  The price `M^k` is a constant: the number of
cells is fixed before `n → ∞`.

Nothing in this module weakens either family theorem; both are used as stated.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace PatternSum

noncomputable section

open LevyExponent TupleMeasure TupleFinal

/-! ## The counting device -/

open Classical in
/-- Splitting a colouring of a finite level type into its restriction along an
embedding and its restriction to the complement of the range. -/
noncomputable def splitEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] {k M : ℕ}
    (f : Fin k ↪ ι) :
    (ι → Fin M) ≃ ((Fin k → Fin M) × ({x : ι // x ∉ Set.range f} → Fin M)) where
  toFun V := (fun ℓ => V (f ℓ), fun x => V x.1)
  invFun p x := if h : ∃ ℓ, f ℓ = x then p.1 h.choose else p.2 ⟨x, fun hx => h hx⟩
  left_inv V := by
    funext x
    by_cases h : ∃ ℓ, f ℓ = x
    · simp only [dif_pos h]
      exact congrArg V h.choose_spec
    · simp only [dif_neg h]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext ℓ
      have h : ∃ ℓ', f ℓ' = f ℓ := ⟨ℓ, rfl⟩
      simp only [dif_pos h]
      exact congrArg p.1 (f.injective h.choose_spec)
    · funext x
      have h : ¬ ∃ ℓ, f ℓ = x := x.2
      simp only [dif_neg h]

/-- **From colourings to patterns.**  A bound on `∑_f a f (V ∘ f)` that holds
for *every* colouring `V` of the levels yields a bound on `∑_f a f u` for every
*fixed* pattern `u`, at the cost of the factor `M^k`.

This is a double count: summing the hypothesis over all `M^{card ι}` colourings
and using that each embedding realises the prescribed pattern under exactly
`M^{card ι - k}` of them. -/
theorem sum_emb_pattern_le {ι : Type*} [Fintype ι] [DecidableEq ι] {k M : ℕ} (hM : 0 < M)
    (a : (Fin k ↪ ι) → (Fin k → Fin M) → ℝ) (ha : ∀ f u, 0 ≤ a f u) {b : ℝ}
    (hb : ∀ V : ι → Fin M, (∑ f : Fin k ↪ ι, a f (fun ℓ => V (f ℓ))) ≤ b)
    (u : Fin k → Fin M) :
    (∑ f : Fin k ↪ ι, a f u) ≤ (M : ℝ) ^ k * b := by
  classical
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hb0 : 0 ≤ b := le_trans (Finset.sum_nonneg fun f _ => ha _ _) (hb (fun _ => ⟨0, hM⟩))
  rcases isEmpty_or_nonempty (Fin k ↪ ι) with hE | hE
  · rw [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  · obtain ⟨f₀⟩ := hE
    have hk : k ≤ Fintype.card ι := by
      simpa using Fintype.card_le_of_embedding f₀
    have key : ∀ f : Fin k ↪ ι,
        (∑ V : ι → Fin M, a f (fun ℓ => V (f ℓ)))
          = (M:ℝ) ^ (Fintype.card ι - k) * ∑ u' : Fin k → Fin M, a f u' := by
      intro f
      have h1 : (∑ V : ι → Fin M, a f (fun ℓ => V (f ℓ)))
          = ∑ p : (Fin k → Fin M) × ({x : ι // x ∉ Set.range f} → Fin M), a f p.1 :=
        Equiv.sum_comp (splitEquiv f) (fun p => a f p.1)
      have hcard : Fintype.card ({x : ι // x ∉ Set.range f} → Fin M)
          = M ^ (Fintype.card ι - k) := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
          Set.card_range_of_injective f.injective, Fintype.card_fin]
      rw [h1, Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      push_cast
      ring
    have hstep : ((M:ℝ) ^ (Fintype.card ι - k)) * (∑ f : Fin k ↪ ι, a f u)
        ≤ (M:ℝ) ^ (Fintype.card ι) * b := by
      calc ((M:ℝ) ^ (Fintype.card ι - k)) * (∑ f : Fin k ↪ ι, a f u)
          = ∑ f : Fin k ↪ ι, ((M:ℝ) ^ (Fintype.card ι - k)) * a f u := by
            rw [Finset.mul_sum]
        _ ≤ ∑ f : Fin k ↪ ι, ((M:ℝ) ^ (Fintype.card ι - k)) * ∑ u' : Fin k → Fin M, a f u' := by
            refine Finset.sum_le_sum (fun f _ => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.single_le_sum (f := fun u' => a f u') (fun i _ => ha f i)
              (Finset.mem_univ u)
        _ = ∑ f : Fin k ↪ ι, ∑ V : ι → Fin M, a f (fun ℓ => V (f ℓ)) :=
            Finset.sum_congr rfl (fun f _ => (key f).symm)
        _ = ∑ V : ι → Fin M, ∑ f : Fin k ↪ ι, a f (fun ℓ => V (f ℓ)) := Finset.sum_comm
        _ ≤ ∑ _V : ι → Fin M, b := Finset.sum_le_sum (fun V _ => hb V)
        _ = (M:ℝ) ^ (Fintype.card ι) * b := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              nsmul_eq_mul]
            push_cast
            ring
    have hpow : (M:ℝ) ^ (Fintype.card ι) = (M:ℝ) ^ (Fintype.card ι - k) * (M:ℝ) ^ k := by
      rw [← pow_add]
      congr 1
      omega
    refine le_of_mul_le_mul_left ?_
      (show (0:ℝ) < (M:ℝ) ^ (Fintype.card ι - k) by positivity)
    calc ((M:ℝ) ^ (Fintype.card ι - k)) * (∑ f : Fin k ↪ ι, a f u)
        ≤ (M:ℝ) ^ (Fintype.card ι) * b := hstep
      _ = (M:ℝ) ^ (Fintype.card ι - k) * ((M:ℝ) ^ k * b) := by rw [hpow]; ring

/-! ## Two elementary devices used with the counting

The first replaces a product by a telescoped sum **keeping the majorants of the
untouched factors**: a uniform `K^{k-1}` bound would be useless here, because
the other factors are what carry the smallness of a `k`-fold tuple. -/

/-- Telescoping a difference of products, with a per-factor majorant. -/
lemma norm_prod_sub_prod_le {K : Type*} [NormedField K] {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α → K) (cb : α → ℝ)
    (ha : ∀ x ∈ s, ‖a x‖ ≤ cb x) (hb : ∀ x ∈ s, ‖b x‖ ≤ cb x) :
    ‖(∏ x ∈ s, a x) - ∏ x ∈ s, b x‖
      ≤ ∑ x ∈ s, (∏ y ∈ s.erase x, cb y) * ‖a x - b x‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert z s hz ih =>
      have hcb0 : ∀ x ∈ s, 0 ≤ cb x := fun x hx =>
        le_trans (norm_nonneg _) (ha x (Finset.mem_insert_of_mem hx))
      have hprod : ‖∏ x ∈ s, a x‖ ≤ ∏ y ∈ s, cb y := by
        rw [norm_prod]
        exact Finset.prod_le_prod (fun x _ => norm_nonneg _)
          (fun x hx => ha x (Finset.mem_insert_of_mem hx))
      have hkey : (∏ x ∈ insert z s, a x) - ∏ x ∈ insert z s, b x
          = (a z - b z) * (∏ x ∈ s, a x) + b z * ((∏ x ∈ s, a x) - ∏ x ∈ s, b x) := by
        rw [Finset.prod_insert hz, Finset.prod_insert hz]; ring
      have hih := ih (fun x hx => ha x (Finset.mem_insert_of_mem hx))
        (fun x hx => hb x (Finset.mem_insert_of_mem hx))
      have hbz : ‖b z‖ ≤ cb z := hb z (Finset.mem_insert_self z s)
      have hstep : ‖(∏ x ∈ insert z s, a x) - ∏ x ∈ insert z s, b x‖
          ≤ (∏ y ∈ s, cb y) * ‖a z - b z‖
            + cb z * ∑ x ∈ s, (∏ y ∈ s.erase x, cb y) * ‖a x - b x‖ := by
        rw [hkey]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul]
        have h1 : ‖a z - b z‖ * ‖∏ x ∈ s, a x‖ ≤ ‖a z - b z‖ * ∏ y ∈ s, cb y :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        have h2 : ‖b z‖ * ‖(∏ x ∈ s, a x) - ∏ x ∈ s, b x‖
            ≤ cb z * ∑ x ∈ s, (∏ y ∈ s.erase x, cb y) * ‖a x - b x‖ := by
          refine mul_le_mul hbz hih (norm_nonneg _) (le_trans (norm_nonneg _) hbz)
        nlinarith [norm_nonneg (a z - b z), Finset.prod_nonneg hcb0]
      refine le_trans hstep (le_of_eq ?_)
      rw [Finset.sum_insert hz, Finset.erase_insert hz, Finset.mul_sum]
      refine congrArg (fun r => (∏ y ∈ s, cb y) * ‖a z - b z‖ + r) ?_
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' : x ≠ z := fun h => hz (h ▸ hx)
      rw [Finset.erase_insert_of_ne (Ne.symm hx'), Finset.prod_insert (fun h => hz (Finset.mem_of_mem_erase h))]
      ring

/-- Embeddings inject into all tuples, so a sum of products over embeddings is
dominated by the product of the level sums. -/
lemma sum_emb_prod_le_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (a : Fin k → ι → ℝ) (ha : ∀ ℓ x, 0 ≤ a ℓ x) :
    (∑ f : Fin k ↪ ι, ∏ ℓ, a ℓ (f ℓ)) ≤ ∏ ℓ, ∑ x : ι, a ℓ x := by
  classical
  have himg : (∑ f : Fin k ↪ ι, ∏ ℓ, a ℓ (f ℓ))
      = ∑ g ∈ (Finset.univ : Finset (Fin k ↪ ι)).image (fun f : Fin k ↪ ι => (f : Fin k → ι)),
          ∏ ℓ, a ℓ (g ℓ) := by
    rw [Finset.sum_image]
    intro f _ f' _ h
    exact DFunLike.coe_injective h
  rw [himg]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun g _ _ => Finset.prod_nonneg (fun ℓ _ => ha ℓ (g ℓ)))) ?_
  refine le_of_eq ?_
  rw [Finset.prod_univ_sum]
  exact (Finset.sum_congr (by simp) (fun g _ => rfl)).symm

/-! ## The colouring attached to a pattern -/

/-- A colouring of the levels `{0,…,n}` extended to all of `ℕ`. -/
def extendPattern {n M : ℕ} (hM : 0 < M)
    (V : (Finset.range (n + 1) : Finset ℕ) → Fin M) : ℕ → Fin M :=
  fun j => if h : j ∈ Finset.range (n + 1) then V ⟨j, h⟩ else ⟨0, hM⟩

@[simp] lemma extendPattern_coe {n M : ℕ} (hM : 0 < M)
    (V : (Finset.range (n + 1) : Finset ℕ) → Fin M)
    (x : (Finset.range (n + 1) : Finset ℕ)) : extendPattern hM V (x : ℕ) = V x := by
  simp only [extendPattern, dif_pos x.2]

/-! ## The two family theorems at a pattern -/

/-- **The §7/§4 index-set bridge at a fixed cell pattern.**  The cells are a
finite family `C : Fin M → Set ℝ` avoiding `(−δ, δ)`; the pattern `u` assigns a
cell to each *position* of the tuple.  The majorant is uniform over the cells
and over the pattern. -/
theorem exists_window_bridge_pattern (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (k M : ℕ) (hM : 0 < M) :
    ∃ maj : ℕ → ℝ, Tendsto maj atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ C : Fin M → Set ℝ, (∀ i : Fin M, ∀ y ∈ C i, δ ≤ |y|) → ∀ u : Fin k → Fin M,
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ))
              - unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))|)
          ≤ maj n := by
  classical
  obtain ⟨maj, hmaj, hev⟩ := WindowBridgeFamily.exists_window_bridge_family c hδ k
  refine ⟨fun n => (M : ℝ) ^ k * maj n, ?_, ?_⟩
  · simpa using hmaj.const_mul ((M : ℝ) ^ k)
  filter_upwards [hev] with n hn C hC u
  refine sum_emb_pattern_le (ι := (Finset.range (n + 1) : Finset ℕ)) hM
    (fun f u => |unifIoo.real (⋂ ℓ, bulkMarkEvent c n (C (u ℓ)) (embTuple f ℓ))
      - unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))|)
    (fun f u => abs_nonneg _) ?_ u
  intro V
  have hE : ∀ x : ℕ, ∀ y ∈ (fun j => C (extendPattern hM V j)) x, δ ≤ |y| :=
    fun x y hy => hC _ y hy
  refine le_trans (le_of_eq ?_) (hn (fun j => C (extendPattern hM V j)) hE)
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [Erdos1002.tupleEvent, embTuple, extendPattern_coe]

/-- **Displays (39)–(40) on the deterministic bulk at a fixed cell pattern.** -/
theorem exists_det_quasi_pattern (m k M : ℕ) {δ : ℝ} (hδ : 0 < δ) (hM : 0 < M) :
    ∃ maj : ℕ → ℝ, Tendsto maj atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ C : Fin M → Set ℝ, (∀ i : Fin M, MeasurableSet (C i)) →
        (∀ i : Fin M, IntervalClass.IsUnionOfIntervals m (C i)) →
        (∀ i : Fin M, ∀ y ∈ C i, δ ≤ |y|) → ∀ u : Fin k → Fin M,
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            |unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))
              - ∏ ℓ, unifIoo.real (detMarkEvent n (C (u ℓ)) (embTuple f ℓ))|)
          ≤ maj n := by
  classical
  obtain ⟨maj, hmaj, hev⟩ := DetQuasiFamily.exists_det_quasi_independence_family m k hδ
  refine ⟨fun n => (M : ℝ) ^ k * maj n, ?_, ?_⟩
  · simpa using hmaj.const_mul ((M : ℝ) ^ k)
  filter_upwards [hev] with n hn C hCm hCi hC u
  refine sum_emb_pattern_le (ι := (Finset.range (n + 1) : Finset ℕ)) hM
    (fun f u => |unifIoo.real (⋂ ℓ, detMarkEvent n (C (u ℓ)) (embTuple f ℓ))
      - ∏ ℓ, unifIoo.real (detMarkEvent n (C (u ℓ)) (embTuple f ℓ))|)
    (fun f u => abs_nonneg _) ?_ u
  intro V
  refine le_trans (le_of_eq ?_)
    (hn (fun j => C (extendPattern hM V j)) (fun x => hCm _) (fun x => hCi _)
      (fun x y hy => hC _ y hy))
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [Erdos1002.tupleEvent, embTuple, extendPattern_coe]

/-! ## The one-level bridge in the level currency -/

/-- The `k = 1` embedding sum, for an arbitrary summand. -/
lemma sum_emb_one_eq' (n : ℕ) (F : ℕ → ℝ) :
    (∑ f : Fin 1 ↪ (Finset.range (n + 1) : Finset ℕ), F (embTuple f 0))
      = ∑ j ∈ Finset.range (n + 1), F j := by
  rw [← Finset.sum_coe_sort (Finset.range (n + 1)) F]
  exact Fintype.sum_equiv (embOneEquiv (Finset.range (n + 1))) _ _ (fun f => rfl)

/-- **The one-level index-set bridge, summed over levels.**  This is
`exists_window_bridge_family` at `k = 1`, read in the level currency: it is the
input the telescoping of `∏ p − ∏ q` consumes. -/
theorem exists_oneLevel_bridge (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ maj : ℕ → ℝ, Tendsto maj atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ B : Set ℝ, (∀ y ∈ B, δ ≤ |y|) →
        (∑ j ∈ Finset.range (n + 1),
            |unifIoo.real (bulkMarkEvent c n B j) - unifIoo.real (detMarkEvent n B j)|)
          ≤ maj n := by
  classical
  obtain ⟨maj, hmaj, hev⟩ := WindowBridgeFamily.exists_window_bridge_family c hδ 1
  refine ⟨maj, hmaj, ?_⟩
  filter_upwards [hev] with n hn B hB
  have h1 : ∀ f : Fin 1 ↪ (Finset.range (n + 1) : Finset ℕ),
      Erdos1002.tupleEvent (fun j => bulkMarkEvent c n ((fun _ => B) j) j) f
        = bulkMarkEvent c n B (embTuple f 0) := by
    intro f
    ext α
    simp [Erdos1002.tupleEvent, Set.mem_iInter, Fin.forall_fin_one, embTuple]
  have h2 : ∀ f : Fin 1 ↪ (Finset.range (n + 1) : Finset ℕ),
      Erdos1002.tupleEvent (fun j => detMarkEvent n ((fun _ => B) j) j) f
        = detMarkEvent n B (embTuple f 0) := by
    intro f
    ext α
    simp [Erdos1002.tupleEvent, Set.mem_iInter, Fin.forall_fin_one, embTuple]
  have h := hn (fun _ => B) (fun _ y hy => hB y hy)
  simp only [h1, h2] at h
  refine le_trans (le_of_eq ?_) h
  exact (sum_emb_one_eq' n (fun j => |unifIoo.real (bulkMarkEvent c n B j)
    - unifIoo.real (detMarkEvent n B j)|)).symm

end

end PatternSum

end Kwon1002
