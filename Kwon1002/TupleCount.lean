import Kwon1002.Section4

/-!
# §4 counting: the number of non-good `r`-tuples is `O_r(L^{r-1} H)`

Target: `Kwon1002.Section4.nonGood_tuple_count` (the sentence between (26) and
Proposition 4.1 of Kwon's manuscript).

The argument is pure counting.  A tuple in `J_n` fails to be good exactly when one
of the `O(r²)` constraints (25)/(26) is violated, and each violated constraint
confines one coordinate `j_q` to a window of length `O(H)` whose position is
determined by one *other* coordinate `j_p` (`p ≠ q`):

* (25) fails at `ℓ`  ⟹  `j_ℓ ≤ j_{ℓ+1} < j_ℓ + 200H`;
* (26) fails at `(i,ℓ)` ⟹ `j_ℓ` lies within `200H` of `(m_n + j_i)/2`.

So each constraint contributes at most `#J_n^{r-1} · O(H)` tuples, and
`#J_n ≤ m_n + 1 = O(L)`.

Everything below is proved outright; no `sorry`, and no sorried input is used.
-/

open Filter Set
open scoped BigOperators Topology

namespace Kwon1002
namespace TupleCount

/-! ## A generic confinement count -/

/-- **Confinement count.**  If on a finset `T` of `r`-tuples of naturals every
coordinate other than `ℓ₀` lies in `J`, and the `ℓ₀`-th coordinate is confined to a
window `[b f, b f + K)` whose base `b f` does not depend on the `ℓ₀`-th coordinate,
then `#T ≤ #J ^ (r-1) * K`. -/
theorem card_confined {r : ℕ} (J : Finset ℕ) (ℓ₀ : Fin r) (K : ℕ)
    (b : (Fin r → ℕ) → ℕ)
    (hb : ∀ f : Fin r → ℕ, b (Function.update f ℓ₀ 0) = b f)
    (T : Finset (Fin r → ℕ))
    (hT : ∀ f ∈ T, (∀ i, i ≠ ℓ₀ → f i ∈ J) ∧ b f ≤ f ℓ₀ ∧ f ℓ₀ < b f + K) :
    T.card ≤ J.card ^ (r - 1) * K := by
  classical
  have hPcard :
      (Fintype.piFinset (fun i : Fin r => if i = ℓ₀ then ({0} : Finset ℕ) else J)).card
        = J.card ^ (r - 1) := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ℓ₀)]
    have h2 : ∀ i ∈ Finset.univ.erase ℓ₀,
        (if i = ℓ₀ then ({0} : Finset ℕ) else J).card = J.card := by
      intro i hi
      rw [if_neg (Finset.ne_of_mem_erase hi)]
    rw [Finset.prod_congr rfl h2, if_pos rfl, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ ℓ₀), Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, one_mul]
  have key : T.card ≤
      ((Fintype.piFinset (fun i : Fin r => if i = ℓ₀ then ({0} : Finset ℕ) else J))
        ×ˢ Finset.range K).card := by
    apply Finset.card_le_card_of_injOn
      (fun f : Fin r → ℕ => (Function.update f ℓ₀ 0, f ℓ₀ - b f))
    · intro f hf
      obtain ⟨h1, h2, h3⟩ := hT f (by simpa using hf)
      show (Function.update f ℓ₀ 0, f ℓ₀ - b f) ∈
        ((Fintype.piFinset (fun i : Fin r => if i = ℓ₀ then ({0} : Finset ℕ) else J))
          ×ˢ Finset.range K : Finset _)
      refine Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 ?_, ?_⟩
      · intro i
        by_cases h : i = ℓ₀
        · subst h; simp
        · rw [if_neg h]
          show Function.update f ℓ₀ 0 i ∈ J
          rw [Function.update_of_ne h]
          exact h1 i h
      · exact Finset.mem_range.2 (by omega)
    · intro f hf g hg hfg
      obtain ⟨-, hf2, -⟩ := hT f (by simpa using hf)
      obtain ⟨-, hg2, -⟩ := hT g (by simpa using hg)
      simp only [Prod.mk.injEq] at hfg
      obtain ⟨he, hv⟩ := hfg
      have hbfg : b f = b g := by rw [← hb f, ← hb g, he]
      have hl0 : f ℓ₀ = g ℓ₀ := by omega
      funext i
      by_cases h : i = ℓ₀
      · subst h; exact hl0
      · have hi := congrFun he i
        rwa [Function.update_of_ne h, Function.update_of_ne h] at hi
  rwa [Finset.card_product, hPcard, Finset.card_range] at key

/-! ## The exceptional finsets -/

/-- All `r`-tuples with every coordinate in the bulk `J_n`. -/
noncomputable def AllJ (n r : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ : Fin r => bulkJ n)

/-- Tuples violating the gap constraint (25) between the coordinates `p` and `q`. -/
noncomputable def SgapF (n r W : ℕ) (p q : Fin r) : Finset (Fin r → ℕ) :=
  (AllJ n r).filter (fun f => f p ≤ f q ∧ f q < f p + W)

/-- Tuples violating the resonance constraint (26) for the pair `(p, q)`. -/
noncomputable def SresF (n r K W : ℕ) (p q : Fin r) : Finset (Fin r → ℕ) :=
  (AllJ n r).filter
    (fun f => (mIndex n + f p) / 2 - K ≤ f q ∧ f q < ((mIndex n + f p) / 2 - K) + W)

/-- The union of all `O(r²)` exceptional finsets. -/
noncomputable def BadF (n r K W : ℕ) : Finset (Fin r → ℕ) :=
  (Finset.univ.filter (fun c : Fin r × Fin r => c.1 ≠ c.2)).biUnion
    (fun c => SgapF n r W c.1 c.2 ∪ SresF n r K W c.1 c.2)

theorem card_BadF_le (n r K W : ℕ) :
    (BadF n r K W).card ≤ r * r * (2 * ((bulkJ n).card ^ (r - 1) * W)) := by
  classical
  refine le_trans (Finset.card_biUnion_le_card_mul _ _
    (2 * ((bulkJ n).card ^ (r - 1) * W)) ?_) ?_
  · intro c hc
    have hne : c.1 ≠ c.2 := (Finset.mem_filter.1 hc).2
    have h1 : (SgapF n r W c.1 c.2).card ≤ (bulkJ n).card ^ (r - 1) * W := by
      refine card_confined (bulkJ n) c.2 W (fun f => f c.1)
        (fun f => by
          show Function.update f c.2 0 c.1 = f c.1
          rw [Function.update_of_ne hne]) _ ?_
      intro f hf
      simp only [SgapF, AllJ, Finset.mem_filter, Fintype.mem_piFinset] at hf
      exact ⟨fun i _ => hf.1 i, hf.2.1, hf.2.2⟩
    have h2 : (SresF n r K W c.1 c.2).card ≤ (bulkJ n).card ^ (r - 1) * W := by
      refine card_confined (bulkJ n) c.2 W (fun f => (mIndex n + f c.1) / 2 - K)
        (fun f => by
          show (mIndex n + Function.update f c.2 0 c.1) / 2 - K = (mIndex n + f c.1) / 2 - K
          rw [Function.update_of_ne hne]) _ ?_
      intro f hf
      simp only [SresF, AllJ, Finset.mem_filter, Fintype.mem_piFinset] at hf
      exact ⟨fun i _ => hf.1 i, hf.2.1, hf.2.2⟩
    calc (SgapF n r W c.1 c.2 ∪ SresF n r K W c.1 c.2).card
        ≤ (SgapF n r W c.1 c.2).card + (SresF n r K W c.1 c.2).card :=
          Finset.card_union_le _ _
      _ ≤ (bulkJ n).card ^ (r - 1) * W + (bulkJ n).card ^ (r - 1) * W := Nat.add_le_add h1 h2
      _ = 2 * ((bulkJ n).card ^ (r - 1) * W) := by ring
  · have h : (Finset.univ.filter (fun c : Fin r × Fin r => c.1 ≠ c.2)).card ≤ r * r := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ h

/-! ## Every non-good admissible tuple lands in `BadF` -/

theorem restr_mem_BadF (n r K W : ℕ) (hK : 200 * Hscale n ≤ (K : ℝ)) (hW : 2 * K + 1 ≤ W)
    (j : ℕ → ℕ) (hadm : IsAdmissibleTuple n r j) (hbad : ¬ GoodTuple n r j) :
    (fun i : Fin r => j (i : ℕ)) ∈ BadF n r K W := by
  classical
  obtain ⟨hz, hmono, hmem⟩ := hadm
  have hallJ : (fun i : Fin r => j (i : ℕ)) ∈ AllJ n r :=
    Fintype.mem_piFinset.2 (fun i => hmem i i.isLt)
  by_cases hA : ∀ ℓ, ℓ + 1 < r → 200 * Hscale n ≤ (j (ℓ + 1) : ℝ) - (j ℓ : ℝ)
  · -- the gap constraint holds, so the resonance constraint must fail
    have hB : ¬ ∀ i ℓ, i < ℓ → ℓ < r →
        200 * Hscale n ≤ |(j ℓ : ℝ) - ((mIndex n : ℝ) + (j i : ℝ)) / 2| :=
      fun h => hbad ⟨⟨hz, hmono, hmem⟩, hA, h⟩
    push_neg at hB
    obtain ⟨i, ℓ, hiℓ, hℓr, hres⟩ := hB
    have hir : i < r := lt_trans hiℓ hℓr
    refine Finset.mem_biUnion.2 ⟨(⟨i, hir⟩, ⟨ℓ, hℓr⟩), ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [Fin.ext_iff]; omega⟩
    refine Finset.mem_union.2 (Or.inr ?_)
    -- the resonance window, in ℕ
    have habs := abs_lt.1 hres
    set M : ℕ := (mIndex n + j i) / 2 with hM
    have hMd : 2 * M ≤ mIndex n + j i ∧ mIndex n + j i < 2 * M + 2 := by omega
    have hMle : (M : ℝ) ≤ ((mIndex n : ℝ) + (j i : ℝ)) / 2 := by
      have : (2 * M : ℝ) ≤ ((mIndex n : ℝ) + (j i : ℝ)) := by exact_mod_cast hMd.1
      linarith
    have hMlt : ((mIndex n : ℝ) + (j i : ℝ)) / 2 < (M : ℝ) + 1 := by
      have : ((mIndex n : ℝ) + (j i : ℝ)) < (2 * M : ℝ) + 2 := by exact_mod_cast hMd.2
      linarith
    have hub : j ℓ < M + 1 + K := by
      have : ((j ℓ : ℕ) : ℝ) < ((M + 1 + K : ℕ) : ℝ) := by
        push_cast
        linarith [habs.2]
      exact_mod_cast this
    have hlb : M ≤ j ℓ + K := by
      have : ((M : ℕ) : ℝ) ≤ ((j ℓ + K : ℕ) : ℝ) := by
        push_cast
        linarith [habs.1]
      exact_mod_cast this
    simp only [SresF, Finset.mem_filter]
    exact ⟨hallJ, by simpa [hM] using (by omega : M - K ≤ j ℓ),
      by simpa [hM] using (by omega : j ℓ < (M - K) + W)⟩
  · push_neg at hA
    obtain ⟨ℓ, hℓr, hgap⟩ := hA
    have hℓr' : ℓ < r := by omega
    refine Finset.mem_biUnion.2 ⟨(⟨ℓ, hℓr'⟩, ⟨ℓ + 1, hℓr⟩), ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [Fin.ext_iff]⟩
    refine Finset.mem_union.2 (Or.inl ?_)
    have hlt : j ℓ < j (ℓ + 1) := hmono ℓ (ℓ + 1) (Nat.lt_succ_self ℓ) hℓr
    have hub : j (ℓ + 1) < j ℓ + K := by
      have : ((j (ℓ + 1) : ℕ) : ℝ) < ((j ℓ + K : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    simp only [SgapF, Finset.mem_filter]
    exact ⟨hallJ, by omega, by omega⟩

/-! ## The target -/

theorem nonGood_tuple_count (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j}).ncard : ℝ)
        ≤ C * (Lnorm n) ^ (r - 1) * Hscale n := by
  classical
  have hlam : (0 : ℝ) < lyapunov := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    show (0 : ℝ) < Real.pi ^ 2 / (12 * Real.log 2)
    positivity
  obtain ⟨A, hA0, hAdef⟩ : ∃ A : ℝ, 0 < A ∧ A = 1 / lyapunov + 1 :=
    ⟨1 / lyapunov + 1, by have := one_div_pos.2 hlam; linarith, rfl⟩
  refine ⟨806 * ((r : ℝ) ^ 2 + 1) * A ^ (r - 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 806 * ((r : ℝ) ^ 2 + 1) := by positivity
    exact mul_pos h1 (pow_pos hA0 _)
  have htend : Filter.Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop 1] with n hL1
  have hL0 : (0 : ℝ) ≤ Lnorm n := by linarith
  have hH1 : 1 ≤ Hscale n := by
    show (1 : ℝ) ≤ (Lnorm n) ^ (3 / 4 : ℝ)
    calc (1 : ℝ) = (1 : ℝ) ^ (3 / 4 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (Lnorm n) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hL1 (by norm_num)
  obtain ⟨K, hKge, hKlt⟩ : ∃ K : ℕ, 200 * Hscale n ≤ (K : ℝ) ∧ (K : ℝ) < 200 * Hscale n + 1 :=
    ⟨⌈200 * Hscale n⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  -- Step 1: the combinatorial bound
  have hinj : Set.InjOn (fun (j : ℕ → ℕ) (i : Fin r) => j (i : ℕ))
      ({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j}) := by
    rintro j1 ⟨⟨hz1, -, -⟩, -⟩ j2 ⟨⟨hz2, -, -⟩, -⟩ heq
    funext ℓ
    by_cases hlr : ℓ < r
    · exact congrFun heq ⟨ℓ, hlr⟩
    · rw [hz1 ℓ (not_lt.1 hlr), hz2 ℓ (not_lt.1 hlr)]
  have hsub : (fun (j : ℕ → ℕ) (i : Fin r) => j (i : ℕ)) ''
      ({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j})
      ⊆ ↑(BadF n r K (2 * K + 1)) := by
    rintro g ⟨j, hj, rfl⟩
    exact Finset.mem_coe.2
      (restr_mem_BadF n r K (2 * K + 1) hKge le_rfl j hj.1 hj.2)
  have hcard1 :
      ({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j}).ncard
        ≤ r * r * (2 * ((bulkJ n).card ^ (r - 1) * (2 * K + 1))) := by
    rw [← Set.ncard_image_of_injOn hinj]
    calc ((fun (j : ℕ → ℕ) (i : Fin r) => j (i : ℕ)) ''
            ({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j})).ncard
        ≤ ((BadF n r K (2 * K + 1) : Finset (Fin r → ℕ)) : Set (Fin r → ℕ)).ncard :=
          Set.ncard_le_ncard hsub (BadF n r K (2 * K + 1)).finite_toSet
      _ = (BadF n r K (2 * K + 1)).card := Set.ncard_coe_finset _
      _ ≤ _ := card_BadF_le n r K (2 * K + 1)
  -- Step 2: the scale bounds
  have hJ : ((bulkJ n).card : ℝ) ≤ A * Lnorm n := by
    have hsub2 : bulkJ n ⊆ Finset.range (mIndex n + 1) := Finset.filter_subset _ _
    have h1 : ((bulkJ n).card : ℝ) ≤ (mIndex n : ℝ) + 1 := by
      have h := Finset.card_le_card hsub2
      rw [Finset.card_range] at h
      have : ((bulkJ n).card : ℝ) ≤ ((mIndex n + 1 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
    have h2 : (mIndex n : ℝ) ≤ Lnorm n / lyapunov :=
      Nat.floor_le (div_nonneg hL0 hlam.le)
    have h3 : Lnorm n / lyapunov = (1 / lyapunov) * Lnorm n := by ring
    have h4 : A * Lnorm n = (1 / lyapunov) * Lnorm n + Lnorm n := by rw [hAdef]; ring
    rw [h3] at h2
    linarith
  have hY : 2 * (K : ℝ) + 1 ≤ 403 * Hscale n := by linarith
  have hJ0 : (0 : ℝ) ≤ ((bulkJ n).card : ℝ) := Nat.cast_nonneg _
  have hT : (0 : ℝ) ≤ A ^ (r - 1) * (Lnorm n) ^ (r - 1) * Hscale n :=
    mul_nonneg (mul_nonneg (pow_pos hA0 _).le (pow_nonneg hL0 _)) (by linarith)
  -- Step 3: assemble
  have hcast : ((r * r * (2 * ((bulkJ n).card ^ (r - 1) * (2 * K + 1))) : ℕ) : ℝ)
      = ((r : ℝ) * (r : ℝ) * 2) * (((bulkJ n).card : ℝ) ^ (r - 1) * (2 * (K : ℝ) + 1)) := by
    push_cast; ring
  have hXY : ((bulkJ n).card : ℝ) ^ (r - 1) * (2 * (K : ℝ) + 1)
      ≤ (A ^ (r - 1) * (Lnorm n) ^ (r - 1)) * (403 * Hscale n) := by
    refine mul_le_mul ?_ hY (by linarith) (by positivity)
    calc ((bulkJ n).card : ℝ) ^ (r - 1) ≤ (A * Lnorm n) ^ (r - 1) :=
          pow_le_pow_left₀ hJ0 hJ _
      _ = A ^ (r - 1) * (Lnorm n) ^ (r - 1) := mul_pow _ _ _
  have hrr : (0 : ℝ) ≤ (r : ℝ) * (r : ℝ) * 2 := by positivity
  have key := mul_le_mul_of_nonneg_left hXY hrr
  have hfinal : ((r * r * (2 * ((bulkJ n).card ^ (r - 1) * (2 * K + 1))) : ℕ) : ℝ)
      ≤ (806 * ((r : ℝ) ^ 2 + 1) * A ^ (r - 1)) * (Lnorm n) ^ (r - 1) * Hscale n := by
    rw [hcast]
    linarith
  refine le_trans ?_ hfinal
  exact_mod_cast hcard1

end TupleCount
end Kwon1002
