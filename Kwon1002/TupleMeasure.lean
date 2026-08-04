import Kwon1002.Discharge
import Kwon1002.DigitTail

/-!
# Scratch (agent `tuples`), displays (39)-(40): `LevyExponent.tuple_measure_convergence`

Target: `Kwon1002.LevyExponent.tuple_measure_convergence` (`Kwon1002/LevyExponent.lean`,
line ≈ 268), reproduced **token-identically** here as `tuple_measure_convergence`
(the target lives in `namespace Kwon1002.LevyExponent`; this file lives in
`namespace Kwon1002` with `open LevyExponent`, so every token of the statement
resolves to the same constant, diffed).

## What this pass delivers

The manuscript's route from (38) to (40) is

1. partition the ordered distinct `r`-tuples by their permutation type and
   parity vector, and count them, display (39);
2. remove the non-good tuples (`O_r(L^{r-1}H)` of them, each of probability
   `O(L^{-r})` by (15));
3. factor the expectation on good tuples by Proposition 4.1, the error
   surviving summation over `O(L^r)` tuples;
4. evaluate one level by (35).

Steps 1 and the *diagonal* bookkeeping implicit in "pairwise distinct" are
**pure combinatorics with no analysis in them**, and they are what this file
proves.  The analytic content (2)+(3) is isolated in exactly **one** named
sorried input, and (4) in one more; a third input that the manuscript uses
silently, the uniform one-level smallness, is **proved outright** here from
Lemma 3.1(ii) (`digit_tail_product`) and `W ≤ 1/8`.

### The reduction, precisely

Write `w_n(j) = P(j ∈ J_n and X_{n,j} ∈ B)` and
`T_n = ∑_{f : Fin k ↪ {0..n}} P(⋂_ℓ {f ℓ ∈ J_n, X_{n,f ℓ} ∈ B})`.

* `tendsto_emb_sum_of_inputs` (**proved**): if
  (I) `∑_{j ≤ n} w_n(j) → Λ`, (II) `T_n - ∑_f ∏_ℓ w_n(f ℓ) → 0`, and
  (III) `sup_{j ≤ n} w_n(j) → 0`, then `T_n → Λ^k`.
  The proof is the display-(39) combinatorics: `∑_f ∏_ℓ w_n(f ℓ)` differs from
  `(∑_j w_n(j))^k` by the non-injective tuples, and those are bounded by
  `k² · sup w · (∑ w)^{k-1}`, `sum_emb_prod_le` / `sum_emb_prod_ge`.
* `oneLevel_intensity_limit`, input (I), display (35) in indicator form
  (**sorried**).
* `tuple_quasi_independence`, input (II), Proposition 4.1 plus the
  bad-tuple/digit-cut/Jackson bookkeeping (**sorried**).
* `singleLevel_measure_le`, input (III) (**proved**, unconditional).

Then `tuple_measure_convergence` is derived (`tuple_measure_convergence`,
proof = `tendsto_emb_sum_of_inputs` fed with the three).

Two further ingredients of the manuscript's step 2 are **proved outright**, so
that whoever discharges input (II) does not have to redo them:

* `digit_ge_of_mem_bulkMarkEvent`, "if `φ_ℓ((-1)^j a W(θ)/L) ≠ 0` then
  `a ≥ 8cL`", from `W ≤ 1/8`;
* `tuple_measure_le`, the multi-level form of display (15): *every* ordered
  distinct `k`-tuple has probability at most `(C/L)^k`, uniformly.  Paired with
  the proved `Kwon1002.nonGood_tuple_count'` (`O_r(L^{r-1}H)` bad tuples) this
  is precisely the manuscript's `O(H/L) = o(1)` bad-tuple bound, modulo the
  index-set bridge recorded below.

### Honest accounting of what is *not* done

* The two sorried inputs are the whole analytic content.  Input (II) bundles
  the manuscript's steps 2 and 3; splitting it further needs a bridge between
  §4's deterministic `bulkJ n` (display (19)) and §7's random `bulkIndices c α n`
  (the stopping-time set that `bulkMarkEvent` uses), which no module in
  `Kwon1002/` states yet.  That bridge is flagged in the report, not papered
  over: it is a genuine gap in the manuscript's §5, which switches index sets
  between (19) and (38) without comment.
* Input (I) as stated is *setwise* convergence for an arbitrary measurable `B`
  bounded away from `0` and bounded, whereas the manuscript proves (35) only in
  the vague sense, against `φ ∈ C_c^1(ℝ∖{0})`.  Vague convergence gives
  `Λ`-continuity sets only.  The stronger indicator form is what
  `poisson_count_limit` consumes, and it is believable here (conditionally on
  the digit `a`, the law of `aW(Θ)/L` is absolutely continuous with a density
  that converges, so the limit is not a Riemann-sum limit), but it is *not* the
  statement the manuscript proves.  Recorded, not weakened.

No result in this file weakens its target; every sorried input is stated in the
strength the target consumes.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace Kwon1002

open LevyExponent

namespace TupleMeasure

noncomputable section

/-! ## Part A, the combinatorics of "pairwise distinct" (display (39))

Nothing in this section knows about measures, `α`, or `L`: it is the exact
statement that summing a product weight over *injective* tuples is the same as
summing over *all* tuples, up to the diagonal, which costs
`k² · (sup weight) · (total weight)^{k-1}`. -/

section Comb

variable {k : ℕ} {s : Finset ℕ}

/-- The underlying `k`-tuple of naturals of an embedding `Fin k ↪ s`.
Definitionally `fun ℓ => ↑(f ℓ)`. -/
def embTuple (f : Fin k ↪ (s : Finset ℕ)) : Fin k → ℕ := fun ℓ => (f ℓ : ℕ)

/-- The decidable form of injectivity used for `Finset.filter`. -/
def InjF (g : Fin k → ℕ) : Prop := ∀ a b : Fin k, g a = g b → a = b

instance : DecidablePred (@InjF k) := fun _ => inferInstanceAs (Decidable (∀ _ _, _ → _))

lemma injF_iff (g : Fin k → ℕ) : InjF g ↔ Function.Injective g :=
  ⟨fun h a b hab => h a b hab, fun h a b hab => h hab⟩

lemma embTuple_mem (f : Fin k ↪ (s : Finset ℕ)) (ℓ : Fin k) : embTuple f ℓ ∈ s := (f ℓ).2

lemma embTuple_injF (f : Fin k ↪ (s : Finset ℕ)) : InjF (embTuple f) := by
  intro a b h
  exact f.injective (Subtype.ext h)

lemma embTuple_injective :
    Function.Injective (fun f : Fin k ↪ (s : Finset ℕ) => embTuple f) := by
  intro f g h
  apply Function.Embedding.ext
  intro ℓ
  exact Subtype.ext (congrFun h ℓ)

/-- Embeddings `Fin k ↪ s` are exactly the injective `k`-tuples with entries in `s`. -/
lemma image_embTuple :
    (Finset.univ.image (fun f : Fin k ↪ (s : Finset ℕ) => embTuple f))
      = (Fintype.piFinset (fun _ : Fin k => s)).filter InjF := by
  ext g
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter,
    Fintype.mem_piFinset]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨fun ℓ => embTuple_mem f ℓ, embTuple_injF f⟩
  · rintro ⟨hmem, hinj⟩
    refine ⟨⟨fun ℓ => ⟨g ℓ, hmem ℓ⟩, ?_⟩, ?_⟩
    · intro a b h
      exact hinj a b (congrArg Subtype.val h)
    · rfl

lemma sum_emb_eq (w : ℕ → ℝ) :
    (∑ f : Fin k ↪ (s : Finset ℕ), ∏ ℓ, w (embTuple f ℓ))
      = ∑ g ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter InjF, ∏ ℓ, w (g ℓ) := by
  rw [← image_embTuple,
    Finset.sum_image (fun f _ f' _ h => embTuple_injective h)]

lemma sum_piFinset_prod (w : ℕ → ℝ) :
    (∑ g ∈ Fintype.piFinset (fun _ : Fin k => s), ∏ ℓ, w (g ℓ)) = (∑ j ∈ s, w j) ^ k := by
  rw [Finset.sum_prod_piFinset s (fun _ j => w j), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Half of display (39): the ordered distinct tuples never overshoot the full
`k`-th power of the total weight. -/
theorem sum_emb_prod_le (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (∑ f : Fin k ↪ (s : Finset ℕ), ∏ ℓ, w (embTuple f ℓ)) ≤ (∑ j ∈ s, w j) ^ k := by
  rw [sum_emb_eq, ← sum_piFinset_prod (s := s) w]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun g _ _ => Finset.prod_nonneg fun ℓ _ => hw _)

/-- A pointwise-modified tuple; a private stand-in for `Function.update`, kept
local so that the proofs below do not depend on `Function.update` API names. -/
def setAt (ℓ' : Fin k) (v : ℕ) (g : Fin k → ℕ) : Fin k → ℕ :=
  fun m => if m = ℓ' then v else g m

lemma setAt_self (ℓ' : Fin k) (v : ℕ) (g : Fin k → ℕ) : setAt ℓ' v g ℓ' = v := by
  simp [setAt]

lemma setAt_of_ne {ℓ' m : Fin k} (h : m ≠ ℓ') (v : ℕ) (g : Fin k → ℕ) :
    setAt ℓ' v g m = g m := by
  simp [setAt, h]

/-- The weight of the tuples with a prescribed coincidence `g ℓ = g ℓ'`
(`ℓ ≠ ℓ'`) is at most `(sup weight) · (total weight)^{k-1}`. -/
theorem sum_pair_le (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (M : ℝ) (hM : ∀ j ∈ s, w j ≤ M)
    {ℓ ℓ' : Fin k} (hne : ℓ ≠ ℓ') :
    (∑ g ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter (fun g => g ℓ = g ℓ'),
        ∏ m, w (g m)) ≤ M * (∑ j ∈ s, w j) ^ (k - 1) := by
  classical
  set A := (Fintype.piFinset (fun _ : Fin k => s)).filter (fun g => g ℓ = g ℓ') with hA
  set t : Fin k → Finset ℕ := fun m => if m = ℓ' then ({0} : Finset ℕ) else s with ht
  -- Step 1: pull out the `ℓ'` factor.
  have step1 : ∀ g ∈ A, ∏ m, w (g m) ≤ M * ∏ m ∈ Finset.univ.erase ℓ', w (g m) := by
    intro g hg
    have hmemA := Finset.mem_filter.mp hg
    have hmem : g ℓ' ∈ s := (Fintype.mem_piFinset.mp hmemA.1) ℓ'
    have hprod : ∏ m, w (g m) = w (g ℓ') * ∏ m ∈ Finset.univ.erase ℓ', w (g m) :=
      (Finset.mul_prod_erase Finset.univ (fun m => w (g m)) (Finset.mem_univ ℓ')).symm
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (hM _ hmem)
      (Finset.prod_nonneg fun m _ => hw _)
  -- Step 2: the coincidence constraint is a bijection onto a smaller `piFinset`.
  have hInjOn : Set.InjOn (setAt ℓ' 0) (A : Set (Fin k → ℕ)) := by
    intro g₁ hg₁ g₂ hg₂ h
    have h1 : g₁ ℓ = g₁ ℓ' := (Finset.mem_filter.mp hg₁).2
    have h2 : g₂ ℓ = g₂ ℓ' := (Finset.mem_filter.mp hg₂).2
    funext m
    by_cases hm : m = ℓ'
    · subst hm
      have := congrFun h ℓ
      rw [setAt_of_ne hne, setAt_of_ne hne] at this
      rw [← h1, ← h2, this]
    · have := congrFun h m
      rwa [setAt_of_ne hm, setAt_of_ne hm] at this
  have hImg : A.image (setAt ℓ' 0) = Fintype.piFinset t := by
    ext h
    simp only [Finset.mem_image, hA, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨g, ⟨hg1, _⟩, rfl⟩
      intro m
      by_cases hm : m = ℓ'
      · subst hm
        rw [setAt_self, ht]
        simp
      · rw [setAt_of_ne hm, ht]
        simpa [hm] using hg1 m
    · intro hh
      have hhℓ' : h ℓ' ∈ ({0} : Finset ℕ) := by simpa [ht] using hh ℓ'
      have hhℓ'0 : h ℓ' = 0 := Finset.mem_singleton.mp hhℓ'
      have hhℓ : h ℓ ∈ s := by simpa [ht, hne] using hh ℓ
      refine ⟨setAt ℓ' (h ℓ) h, ⟨?_, ?_⟩, ?_⟩
      · intro m
        by_cases hm : m = ℓ'
        · subst hm; rwa [setAt_self]
        · rw [setAt_of_ne hm]
          simpa [ht, hm] using hh m
      · rw [setAt_of_ne hne, setAt_self]
      · funext m
        by_cases hm : m = ℓ'
        · subst hm; rw [setAt_self, hhℓ'0]
        · rw [setAt_of_ne hm, setAt_of_ne hm]
  have step2 : (∑ g ∈ A, ∏ m ∈ Finset.univ.erase ℓ', w (g m))
      = (∑ j ∈ s, w j) ^ (k - 1) := by
    have h1 : (∑ h ∈ Fintype.piFinset t, ∏ m ∈ Finset.univ.erase ℓ', w (h m))
        = ∑ g ∈ A, ∏ m ∈ Finset.univ.erase ℓ', w (setAt ℓ' 0 g m) := by
      rw [← hImg, Finset.sum_image hInjOn]
    have h2 : ∀ g : Fin k → ℕ,
        (∏ m ∈ Finset.univ.erase ℓ', w (setAt ℓ' 0 g m))
          = ∏ m ∈ Finset.univ.erase ℓ', w (g m) := by
      intro g
      refine Finset.prod_congr rfl fun m hm => ?_
      rw [setAt_of_ne (Finset.ne_of_mem_erase hm)]
    simp only [h2] at h1
    rw [← h1]
    -- evaluate the smaller `piFinset` sum
    have key : ∀ h : Fin k → ℕ, (∏ m ∈ Finset.univ.erase ℓ', w (h m))
        = ∏ m : Fin k, (if m = ℓ' then (1 : ℝ) else w (h m)) := by
      intro h
      rw [← Finset.mul_prod_erase Finset.univ (fun m => if m = ℓ' then (1 : ℝ) else w (h m))
        (Finset.mem_univ ℓ'), if_pos rfl, one_mul]
      exact (Finset.prod_congr rfl fun m hm => by
        rw [if_neg (Finset.ne_of_mem_erase hm)]).symm
    simp only [key]
    rw [← Finset.prod_univ_sum t (fun m j => if m = ℓ' then (1 : ℝ) else w j)]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun m => ∑ j ∈ t m, (if m = ℓ' then (1 : ℝ) else w j)) (Finset.mem_univ ℓ')]
    have hℓ' : (∑ j ∈ t ℓ', (if ℓ' = ℓ' then (1 : ℝ) else w j)) = 1 := by
      simp [ht]
    rw [hℓ', one_mul]
    have hrest : ∀ m ∈ Finset.univ.erase ℓ',
        (∑ j ∈ t m, (if m = ℓ' then (1 : ℝ) else w j)) = ∑ j ∈ s, w j := by
      intro m hm
      have hm' : m ≠ ℓ' := Finset.ne_of_mem_erase hm
      simp [ht, hm']
    rw [Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ ℓ'), Finset.card_univ, Fintype.card_fin]
  calc (∑ g ∈ A, ∏ m, w (g m))
      ≤ ∑ g ∈ A, M * ∏ m ∈ Finset.univ.erase ℓ', w (g m) := Finset.sum_le_sum step1
    _ = M * ∑ g ∈ A, ∏ m ∈ Finset.univ.erase ℓ', w (g m) := by rw [Finset.mul_sum]
    _ = M * (∑ j ∈ s, w j) ^ (k - 1) := by rw [step2]

/-- A finite subadditivity step: a nonnegative sum over a set covered by a
family is at most the sum of the sums over the family. -/
theorem sum_le_sum_cover {ι κ : Type*} [DecidableEq ι] {N : Finset ι} {P : Finset κ}
    {A : κ → Finset ι} {F : ι → ℝ} (hF : ∀ x, 0 ≤ F x)
    (hcov : ∀ x ∈ N, ∃ p ∈ P, x ∈ A p) :
    (∑ x ∈ N, F x) ≤ ∑ p ∈ P, ∑ x ∈ A p, F x := by
  classical
  have hnn : ∀ (p : κ) (x : ι), 0 ≤ (if x ∈ A p then F x else 0) := by
    intro p x; split_ifs; exacts [hF x, le_refl 0]
  calc (∑ x ∈ N, F x)
      ≤ ∑ x ∈ N, ∑ p ∈ P, (if x ∈ A p then F x else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        obtain ⟨p, hp, hxp⟩ := hcov x hx
        calc F x = (if x ∈ A p then F x else 0) := by rw [if_pos hxp]
          _ ≤ ∑ p ∈ P, (if x ∈ A p then F x else 0) :=
              Finset.single_le_sum (fun q _ => hnn q x) hp
    _ = ∑ p ∈ P, ∑ x ∈ N, (if x ∈ A p then F x else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ P, ∑ x ∈ A p, F x := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => (Finset.mem_filter.mp hx).2) (fun x _ _ => hF x)

/-- **The diagonal estimate of display (39).**  Summing a product weight over
*ordered distinct* `k`-tuples loses at most `k² · M · (∑ w)^{k-1}` against the
full `k`-th power, where `M` bounds the individual weights. -/
theorem sum_emb_prod_ge (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ j ∈ s, w j ≤ M) :
    (∑ j ∈ s, w j) ^ k - (k : ℝ) ^ 2 * M * (∑ j ∈ s, w j) ^ (k - 1)
      ≤ ∑ f : Fin k ↪ (s : Finset ℕ), ∏ ℓ, w (embTuple f ℓ) := by
  classical
  set P := Fintype.piFinset (fun _ : Fin k => s) with hP
  set I := P.filter InjF with hI
  set F : (Fin k → ℕ) → ℝ := fun g => ∏ m, w (g m) with hF
  have hFnn : ∀ g, 0 ≤ F g := fun g => Finset.prod_nonneg fun m _ => hw _
  have hSnn : (0 : ℝ) ≤ ∑ j ∈ s, w j := Finset.sum_nonneg fun j _ => hw j
  have hsub : I ⊆ P := Finset.filter_subset _ _
  have hsplit : (∑ g ∈ P \ I, F g) + ∑ g ∈ I, F g = ∑ g ∈ P, F g := Finset.sum_sdiff hsub
  -- cover the non-injective tuples by the coincidence sets
  have hcov : ∀ g ∈ P \ I, ∃ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
      g ∈ P.filter (fun g => g p.1 = g p.2) := by
    intro g hg
    have hgP : g ∈ P := (Finset.mem_sdiff.mp hg).1
    have hgI : g ∉ I := (Finset.mem_sdiff.mp hg).2
    have hnot : ¬ InjF g := fun h => hgI (Finset.mem_filter.mpr ⟨hgP, h⟩)
    rw [injF_iff] at hnot
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hnot
    exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨Finset.mem_univ a, Finset.mem_univ b, hne⟩,
      Finset.mem_filter.mpr ⟨hgP, hab⟩⟩
  have hcover := sum_le_sum_cover (N := P \ I)
    (P := (Finset.univ : Finset (Fin k)).offDiag)
    (A := fun p => P.filter (fun g => g p.1 = g p.2)) (F := F) hFnn hcov
  have hpair : ∀ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
      (∑ g ∈ P.filter (fun g => g p.1 = g p.2), F g)
        ≤ M * (∑ j ∈ s, w j) ^ (k - 1) := by
    intro p hp
    exact sum_pair_le w hw M hM (Finset.mem_offDiag.mp hp).2.2
  have hsum : (∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
      ∑ g ∈ P.filter (fun g => g p.1 = g p.2), F g)
      ≤ (k : ℝ) ^ 2 * M * (∑ j ∈ s, w j) ^ (k - 1) := by
    calc (∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
            ∑ g ∈ P.filter (fun g => g p.1 = g p.2), F g)
        ≤ ∑ _p ∈ (Finset.univ : Finset (Fin k)).offDiag, M * (∑ j ∈ s, w j) ^ (k - 1) :=
          Finset.sum_le_sum hpair
      _ = ((Finset.univ : Finset (Fin k)).offDiag.card : ℝ) * (M * (∑ j ∈ s, w j) ^ (k - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) ^ 2 * (M * (∑ j ∈ s, w j) ^ (k - 1)) := by
          have hcard : ((Finset.univ : Finset (Fin k)).offDiag.card : ℝ) ≤ (k : ℝ) ^ 2 := by
            rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
            have : (k * k - k : ℕ) ≤ k ^ 2 := by
              calc k * k - k ≤ k * k := Nat.sub_le _ _
                _ = k ^ 2 := (sq k).symm
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hcard
            (mul_nonneg hM0 (pow_nonneg hSnn _))
      _ = (k : ℝ) ^ 2 * M * (∑ j ∈ s, w j) ^ (k - 1) := by ring
  have hPsum : (∑ g ∈ P, F g) = (∑ j ∈ s, w j) ^ k := sum_piFinset_prod w
  have hIsum : (∑ g ∈ I, F g) = ∑ f : Fin k ↪ (s : Finset ℕ), ∏ ℓ, w (embTuple f ℓ) :=
    (sum_emb_eq w).symm
  have hdiff : (∑ g ∈ P \ I, F g) ≤ (k : ℝ) ^ 2 * M * (∑ j ∈ s, w j) ^ (k - 1) :=
    le_trans hcover hsum
  rw [← hIsum, ← hPsum]
  linarith [hsplit, hdiff]

end Comb

/-! ## Part B, the reduction

Three inputs give display (40).  This is the only place the three are combined,
and it is proved. -/

/-- **The reduction, proved.**  Let `u n` be the level window, `w n j` the
one-level probabilities, `T n` the ordered-distinct-tuple sum.  If the one-level
sums converge to `Λ`, the individual levels are uniformly `o(1)`, and the tuple
sum factorizes up to `o(1)`, then `T n → Λ^k`.

The content is the diagonal bookkeeping of display (39): `∑_f ∏_ℓ w n (f ℓ)` is
squeezed between `(∑_j w n j)^k - k² M n (∑_j w n j)^{k-1}` and `(∑_j w n j)^k`. -/
theorem tendsto_emb_sum_of_inputs (k : ℕ) (u : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (T : ℕ → ℝ) (Λ : ℝ) (M : ℕ → ℝ)
    (hw0 : ∀ n j, 0 ≤ w n j)
    (hM0 : ∀ n, 0 ≤ M n)
    (hwM : ∀ᶠ n in atTop, ∀ j ∈ u n, w n j ≤ M n)
    (hMlim : Tendsto M atTop (𝓝 0))
    (hS : Tendsto (fun n => ∑ j ∈ u n, w n j) atTop (𝓝 Λ))
    (hT : Tendsto
      (fun n => T n - ∑ f : Fin k ↪ (u n : Finset ℕ), ∏ ℓ, w n (embTuple f ℓ))
      atTop (𝓝 0)) :
    Tendsto T atTop (𝓝 (Λ ^ k)) := by
  set S : ℕ → ℝ := fun n => ∑ j ∈ u n, w n j with hSdef
  set Pn : ℕ → ℝ := fun n => ∑ f : Fin k ↪ (u n : Finset ℕ), ∏ ℓ, w n (embTuple f ℓ) with hPdef
  have hupper : ∀ n, Pn n ≤ S n ^ k := fun n => sum_emb_prod_le (w n) (hw0 n)
  have hlower : ∀ᶠ n in atTop,
      S n ^ k - (k : ℝ) ^ 2 * M n * S n ^ (k - 1) ≤ Pn n := by
    filter_upwards [hwM] with n hn
    exact sum_emb_prod_ge (w n) (hw0 n) (M n) (hM0 n) hn
  have hglim : Tendsto (fun n => S n ^ k - (k : ℝ) ^ 2 * M n * S n ^ (k - 1)) atTop
      (𝓝 (Λ ^ k)) := by
    have h1 : Tendsto (fun n => S n ^ k) atTop (𝓝 (Λ ^ k)) := hS.pow k
    have h2 : Tendsto (fun n => (k : ℝ) ^ 2 * M n * S n ^ (k - 1)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := ((k : ℝ) ^ 2)) (f := atTop (α := ℕ))).mul hMlim).mul
        (hS.pow (k - 1))
      simpa using this
    simpa using h1.sub h2
  have hP : Tendsto Pn atTop (𝓝 (Λ ^ k)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hglim (hS.pow k) hlower
      (Eventually.of_forall hupper)
  have : Tendsto (fun n => (T n - Pn n) + Pn n) atTop (𝓝 (0 + Λ ^ k)) := hT.add hP
  simpa using this

/-! ## Part C, the three inputs

Input (III) is proved; inputs (I) and (II) are the analytic obstruction. -/

section Inputs

/-- `L = log n ≥ 0` for every natural `n` (Lean's `log 0 = 0`). -/
lemma Lnorm_nonneg (n : ℕ) : 0 ≤ Lnorm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Lnorm]
  · exact Real.log_nonneg (by exact_mod_cast hn)

lemma tendsto_Lnorm_atTop : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **The manuscript's "if `φ_ℓ((-1)^j a W(θ)/L) ≠ 0` then `a ≥ 8cL`".**  A level
whose normalized signed mark lands at distance at least `δ` from the origin has
digit at least `8 δ L`, because `W ≤ 1/8` (`Kwon1002.W_le_eighth`). -/
lemma digit_ge_of_mem_bulkMarkEvent (c : ℝ) (B : Set ℝ) {δ : ℝ}
    (hB0 : ∀ x ∈ B, δ ≤ |x|) {n : ℕ} (hn : 0 < Lnorm n) {j : ℕ} {α : ℝ}
    (hα : α ∈ bulkMarkEvent c n B j) : 8 * δ * Lnorm n ≤ (digit α j : ℝ) := by
  have hmark : signedMark α n j ∈ B := hα.2
  have hδle : δ ≤ |signedMark α n j| := hB0 _ hmark
  have hWnn : 0 ≤ W (theta α n j) := W_nonneg _
  have hprodnn : (0 : ℝ) ≤ (digit α j : ℝ) * W (theta α n j) :=
    mul_nonneg (Nat.cast_nonneg _) hWnn
  have habs : |signedMark α n j| = (digit α j : ℝ) * W (theta α n j) / Lnorm n := by
    rw [signedMark, mark, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hn.le, abs_of_nonneg hprodnn]
  rw [habs, le_div_iff₀ hn] at hδle
  have hW8 : W (theta α n j) ≤ 1 / 8 := W_le_eighth _
  have hbnd : (digit α j : ℝ) * W (theta α n j) ≤ (digit α j : ℝ) * (1 / 8) :=
    mul_le_mul_of_nonneg_left hW8 (Nat.cast_nonneg _)
  linarith

/-- The one-level form of the digit constraint, as a set inclusion in the exact
shape `digit_tail_product` consumes (`s = 1`). -/
lemma bulkMarkEvent_subset_digit (c : ℝ) (B : Set ℝ) {δ : ℝ}
    (hB0 : ∀ x ∈ B, δ ≤ |x|) (n : ℕ) (hn : 0 < Lnorm n) (j : ℕ) :
    bulkMarkEvent c n B j ∩ Ioo (0 : ℝ) 1
      ⊆ {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∀ _i : Fin 1, 8 * δ * Lnorm n ≤ (digit α j : ℝ)} := by
  rintro α ⟨hα, hαI⟩
  exact ⟨hαI, fun _ => digit_ge_of_mem_bulkMarkEvent c B hB0 hn hα⟩

/-- **Input (III), proved unconditionally.**  Uniformly in the level `j`, the
one-level probability is `O(1/L)`.  This is exactly the manuscript's remark
"if `φ_ℓ((-1)^j a W(θ)/L) ≠ 0` then `a ≥ 8cL`" combined with Lemma 3.1(ii)
(display (15)) at a single level.

Consumes: `Kwon1002.digit_tail_product` (proved in `Kwon1002/DigitTail.lean`)
and `Kwon1002.W_le_eighth`. -/
theorem singleLevel_measure_le (c : ℝ) (B : Set ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hB0 : ∀ x ∈ B, δ ≤ |x|) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      unifIoo.real (bulkMarkEvent c n B j) ≤ C / Lnorm n := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_Lnorm_atTop
    exact this.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 j
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin 1, (fun _ : Fin 1 => 8 * δ * Lnorm n) i ≤ (digit α ((fun _ : Fin 1 => j) i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ 1 * ∏ _i : Fin 1, (8 * δ * Lnorm n)⁻¹ :=
    hC 1 (fun _ => j) (fun _ => 8 * δ * Lnorm n)
      (fun a b _ => Subsingleton.elim a b) (fun _ => hn1)
  have hsub : bulkMarkEvent c n B j ∩ Ioo (0 : ℝ) 1 ⊆ big :=
    bulkMarkEvent_subset_digit c B hB0 n hn2 j
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (bulkMarkEvent c n B j) ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound ?_)
  rw [pow_one, Fin.prod_univ_one, div_div, ← div_eq_mul_inv]

/-- **The multi-level form of display (15), proved unconditionally.**  Every
ordered distinct `k`-tuple of levels has probability `O(L^{-k})`, uniformly in
the tuple.  This is the manuscript's "on each of them the probability that all
factors are nonzero is `O_r(L^{-r})` by (15)", the estimate its bad-tuple
removal multiplies against `nonGood_tuple_count'`.

Consumes: `Kwon1002.digit_tail_product` (proved) and `Kwon1002.W_le_eighth`. -/
theorem tuple_measure_le (c : ℝ) (B : Set ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hB0 : ∀ x ∈ B, δ ≤ |x|) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f) ≤ (C / Lnorm n) ^ k := by
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀ / (8 * δ), by positivity, ?_⟩
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * δ * Lnorm n := by
    have : Tendsto (fun n : ℕ => 8 * δ * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_Lnorm_atTop
    exact this.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    tendsto_Lnorm_atTop.eventually_gt_atTop 0
  filter_upwards [h1, h2] with n hn1 hn2 f
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin k, (fun _ : Fin k => 8 * δ * Lnorm n) i ≤ (digit α (embTuple f i) : ℝ)}
    with hbig
  have hbound : (volume big).toReal ≤ C₀ ^ k * ∏ _i : Fin k, (8 * δ * Lnorm n)⁻¹ :=
    hC k (embTuple f) (fun _ => 8 * δ * Lnorm n)
      ((injF_iff _).mp (embTuple_injF f)) (fun _ => hn1)
  have hsub : Erdos1002.tupleEvent (bulkMarkEvent c n B) f ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    refine ⟨hαI, fun i => ?_⟩
    exact digit_ge_of_mem_bulkMarkEvent c B hB0 hn2 (Set.mem_iInter.mp hα i)
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f)
      ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound (le_of_eq ?_))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, div_div,
    ← div_eq_mul_inv]

/-- **Input (I): display (35) in indicator form**, the one-level intensities
sum to the Lévy intensity of `B`.

This is the manuscript's `L·P(A W(Θ)/L ∈ dx) ⇒ c₀ x^{-2} dx` together with the
count `#J_n = (1+o(1)) L/λ` of (39), read against the indicator of `B` rather
than against `φ ∈ C_c^1`.  See the module docstring: the manuscript proves the
vague form only, and the indicator form is what `poisson_count_limit` consumes.

**Obstruction.** Not stated anywhere in `Kwon1002/` or in the substrate;
needs (35) plus the §7 level count for `bulkIndices`. -/
theorem oneLevel_intensity_limit (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        unifIoo.real (bulkMarkEvent c n B j)) atTop (𝓝 ((levyIntensity B).toReal)) := by
  sorry

/-- **Input (II): Proposition 4.1 in tuple form**, the ordered-distinct-tuple
probabilities factorize into the one-level probabilities, with total error
`o(1)` after summing over the `O(L^k)` tuples.

This is the manuscript's paragraph "Non-good time tuples are `O_r(L^{r-1}H)` in
number … On good tuples, Proposition 4.1 factors the expectation, and its error
remains `o(1)` after summing `O(L^r)` tuples", *plus* the `a ≤ L^D` digit cut
and the Jackson approximation that put the indicator of `B` into the symbol
class `P_D(L)` of (24).

**Obstruction (named).**  Discharging this needs
`Kwon1002.prop_4_1_marked_factorization` (sorried, `Kwon1002/Section4.lean`;
`Kwon1002.Prop41.prop_4_1_error_shape` is the remaining input there) together
with `Kwon1002.nonGood_tuple_count'` (**proved**, `Kwon1002/Discharge.lean`)
and `Kwon1002.digit_tail_product` (**proved**).  It also needs a bridge that
the manuscript never states: Proposition 4.1 quantifies over the deterministic
`bulkJ n` of display (19), while `bulkMarkEvent` uses the random
`bulkIndices c α n` built from the §7 stopping time.  That bridge is the honest
gap here, and it is a gap in §5 of the manuscript, not an artefact of the
formalization. -/
theorem tuple_quasi_independence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              ∏ ℓ, unifIoo.real (bulkMarkEvent c n B (f ℓ)))
      atTop (𝓝 0) := by
  sorry

end Inputs

/-! ## Part D, the target

`Kwon1002.LevyExponent.tuple_measure_convergence`, reproduced token-identically
and derived from Part B plus the inputs of Part C. -/

/-- **Displays (39)-(40)**, token-identical restatement of
`Kwon1002.LevyExponent.tuple_measure_convergence`, derived from
`tendsto_emb_sum_of_inputs` (proved), `singleLevel_measure_le` (proved),
`oneLevel_intensity_limit` (sorried input I) and `tuple_quasi_independence`
(sorried input II). -/
theorem tuple_measure_convergence (c : ℝ) (B : Set ℝ) (_hB : MeasurableSet B)
    (_hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (_hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ => ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
        unifIoo.real (Erdos1002.tupleEvent (bulkMarkEvent c n B) f))
      atTop (𝓝 ((levyIntensity B).toReal ^ k)) := by
  obtain ⟨δ, hδ, hBδ⟩ := _hB0
  obtain ⟨C, hC, hCle⟩ := singleLevel_measure_le c B hδ hBδ
  refine tendsto_emb_sum_of_inputs k (fun n => Finset.range (n + 1))
    (fun n j => unifIoo.real (bulkMarkEvent c n B j)) _
    ((levyIntensity B).toReal) (fun n => C / Lnorm n)
    (fun n j => measureReal_nonneg) (fun n => div_nonneg hC.le (Lnorm_nonneg n))
    ?_ ?_ ?_ ?_
  · filter_upwards [hCle] with n hn j _ using hn j
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_Lnorm_atTop
  · exact oneLevel_intensity_limit c B _hB ⟨δ, hδ, hBδ⟩ _hBbd
  · exact tuple_quasi_independence c B _hB ⟨δ, hδ, hBδ⟩ _hBbd k

end

end TupleMeasure

end Kwon1002


