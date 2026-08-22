import Kwon1002.FactorialSeries
import Kwon1002.TupleFinal

/-!
# The layer assembly: elementary symmetric sums to `Λ̂^k/k!`

`Kwon1002/FactorialSeries.lean` reduces `CorFinal.largeSum_charFun_limit` to the
**layer limit**

  `layerSum t c ε n k = ∑_{S ⊆ {0,…,n}, |S| = k} ∫₀¹ ∏_{j∈S} h_j  →  Λ̂^k/k!`,

and names four things that separate that from what the tree has.  Two of the
four are in fact already proved elsewhere in the tree (see the record
correction below).  This module closes a third, item (iv), the passage

  `∑_{|S|=k} ∏_{j∈S} μ_j  →  (lim ∑_j μ_j)^k / k!`,

and reduces the layer limit to **two** analytic inputs, both about the symbol
`x ↦ (e^{itx}−1)1{|x|>ε}` and neither about counting:

* `hp1`, the one-level limit `∑_{j ≤ n} ∫₀¹ h_j → Λ̂`;
* `hqi`, the subset quasi-independence `∑_{|S|=k} |∫₀¹ ∏_{j∈S} h_j − ∏_{j∈S} ∫₀¹ h_j| → 0`.

The two side conditions that a symmetric-function argument also needs — that
`∑_j |∫ h_j|` stays bounded and that `∑_j |∫ h_j|²` vanishes — are **not**
assumed: they are *proved* here (`sum_norm_mu_le`, `tendsto_sum_norm_mu_sq`)
from the `k`-uniform tuple bound `FactorialRoute.exists_tupleBigEvent_bound`
and the deterministic Lamé cap `FactorialRoute.lameCap`, both already in the
tree.  That is what makes the reduction to exactly two inputs honest.

## Two records corrected (machine-checked)

`Kwon1002/FactorialSeries.lean` (§"What remains on this route", items 2 and 3)
and `Kwon1002/MultiLevel.lean` (§"What this does *not* close", items 2 and 3)
both record as open two statements that are in fact **proved and axiom-clean**:

* item 2, the non-good tuple count, is
  `Kwon1002.TupleCount.nonGood_tuple_count`, restated verbatim and cited as
  `Kwon1002.nonGood_tuple_count'` in `Kwon1002/Discharge.lean`.  Only the
  *below-declaration* copy `Kwon1002.Section4.nonGood_tuple_count` still carries
  a `sorry`, and it does so for the import-direction reason its own module
  documents, not for a mathematical one;
* item 3, the `k`-level index-set bridge, is
  `Kwon1002.TupleFinal.bulk_window_bridge_tuple`, whose proof was completed
  after those two headers were written.

The `example`s at the foot of this file check both claims inside Lean.

## The elementary-symmetric argument, and why no even/odd split is needed

The four named items include "the even/odd split the sign `(−1)^j` forces".
There is no such split on this route.  The comparison used here is the
**Newton-type recursion in the first power sum only**,

  `(∑_{j∈T} μ_j) · e_k = (k+1) · e_{k+1} + ∑_{|S|=k} ∑_{j∈S} μ_j ∏_{i∈S} μ_i`,

an identity with no alternating signs (`sum_mul_esymm`).  Its error term is
diagonal, hence bounded by `(∑_j |μ_j|²) · e_k(|μ|)`, and `e_k(|μ|) ≤ e^{∑|μ|}`
uniformly in `k` (`esymm_le_exp`), so a single induction on `k` gives
`e_k → a^k/k!` with no inclusion-exclusion and no alternating sum anywhere.
The full Newton identities, which do alternate, are not needed and are not used.

## Record correction: `hp1` is no longer an input

The reduction below leaves two analytic inputs, `hp1` and `hqi`.  `hp1` is now a
theorem: `Kwon1002.SymbolLimit.sum_mu_tendsto`, axiom-clean, and
`Kwon1002.SymbolLimit.largeSum_charFun_limit_of_hqi` is the conclusion of
`largeSum_charFun_limit_of_two_inputs` with `hqi` as its **only** hypothesis.

`hqi` is still open.  What it needs, and what is now available for it: expand the
step symbol of `SymbolLimit.exists_step_approx` multilinearly across the `k`
levels — this produces a *different* target at each level, so the per-level forms
are the currency — and feed
`Kwon1002.TupleTransfer.multiSet_mark_factorization` (proved, uniform over
per-level families), `Kwon1002.DetQuasiFamily.exists_det_quasi_independence_family`
(proved here as of this wave: displays (39)-(40) on the deterministic bulk at a
per-level family, with the absolute value *inside* the sum over embeddings) and
`Kwon1002.WindowBridgeFamily.exists_window_bridge_family` (proved here as of this
wave: the §7/§4 index-set bridge at a per-level family, again with the absolute
value inside).  What is **not** yet written is the passage from those two to the
random-bulk quasi-independence at a per-level family — it needs the product
telescoping `|∏ p − ∏ q| ≤ ∑_ℓ (∏_{ℓ'<ℓ} q)(|p − q|)(∏_{ℓ'>ℓ} p)` summed over
embeddings against `∑_f ∏_ℓ a_ℓ(f ℓ) ≤ ∏_ℓ ∑_j a_ℓ j` — and the multilinear
expansion itself, together with the `Finset`-to-embedding reindexing by `k!` and
the `η`/`R` error control for the `k`-fold products.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace LayerAssembly

noncomputable section

/-! ## The double count `(S, j ∉ S) ↔ (S ∪ {j}, j ∈ S ∪ {j})` -/

/-- **The double count.**  Pairs `(S, j)` with `|S| = k`, `S ⊆ T` and `j ∈ T \ S`
correspond bijectively to pairs `(S', j)` with `|S'| = k + 1`, `S' ⊆ T` and
`j ∈ S'`, via `S' = insert j S`.  Stated for an arbitrary summand so that both
the identity and the error bound below can spend it. -/
theorem sum_powersetCard_sdiff_insert {M : Type*} [AddCommMonoid M]
    (T : Finset ℕ) (k : ℕ) (F : Finset ℕ → ℕ → M) :
    (∑ S ∈ T.powersetCard k, ∑ j ∈ T \ S, F (insert j S) j)
      = ∑ S ∈ T.powersetCard (k + 1), ∑ j ∈ S, F S j := by
  classical
  rw [Finset.sum_sigma' (T.powersetCard k) (fun S => T \ S)
      (fun S j => F (insert j S) j),
    Finset.sum_sigma' (T.powersetCard (k + 1)) (fun S => S) (fun S j => F S j)]
  refine Finset.sum_nbij'
    (i := fun x : (_ : Finset ℕ) × ℕ => (⟨insert x.2 x.1, x.2⟩ : (_ : Finset ℕ) × ℕ))
    (j := fun y : (_ : Finset ℕ) × ℕ => (⟨y.1.erase y.2, y.2⟩ : (_ : Finset ℕ) × ℕ))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨S, j⟩ hx
    rw [Finset.mem_sigma] at hx ⊢
    obtain ⟨hS, hj⟩ := hx
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_sdiff] at hj
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset hj.1 hS.1
    · rw [Finset.card_insert_of_notMem hj.2, hS.2]
  · rintro ⟨S, j⟩ hy
    rw [Finset.mem_sigma] at hy ⊢
    obtain ⟨hS, hj⟩ := hy
    rw [Finset.mem_powersetCard] at hS
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (Finset.erase_subset _ _).trans hS.1
    · rw [Finset.card_erase_of_mem hj, hS.2]; rfl
    · exact Finset.mem_sdiff.mpr ⟨hS.1 hj, Finset.notMem_erase _ _⟩
  · rintro ⟨S, j⟩ hx
    rw [Finset.mem_sigma, Finset.mem_sdiff] at hx
    simp [Finset.erase_insert hx.2.2]
  · rintro ⟨S, j⟩ hy
    rw [Finset.mem_sigma] at hy
    simp [Finset.insert_erase hy.2]
  · rintro ⟨S, j⟩ _
    rfl

/-! ## The uniform bound on elementary symmetric sums -/

/-- `e_m(x) ≤ exp(∑ x)` for nonnegative `x`, uniformly in `m`.  This is the only
size input the induction needs, and it is uniform in the degree. -/
theorem esymm_le_exp (T : Finset ℕ) (m : ℕ) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ S ∈ T.powersetCard m, ∏ i ∈ S, x i) ≤ Real.exp (∑ i ∈ T, x i) := by
  classical
  have h1 : (∑ S ∈ T.powersetCard m, ∏ i ∈ S, x i)
      ≤ ∑ S ∈ T.powerset, ∏ i ∈ S, x i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro S hS
      exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1
    · intro S _ _
      exact Finset.prod_nonneg fun i _ => hx i
  have h2 : (∑ S ∈ T.powerset, ∏ i ∈ S, x i) = ∏ i ∈ T, (x i + 1) := by
    rw [Finset.prod_add]
    simp
  have h3 : (∏ i ∈ T, (x i + 1)) ≤ ∏ i ∈ T, Real.exp (x i) :=
    Finset.prod_le_prod (fun i _ => by have := hx i; positivity)
      (fun i _ => by linarith [Real.add_one_le_exp (x i)])
  have h4 : (∏ i ∈ T, Real.exp (x i)) = Real.exp (∑ i ∈ T, x i) :=
    (Real.exp_sum T x).symm
  calc (∑ S ∈ T.powersetCard m, ∏ i ∈ S, x i)
      ≤ ∑ S ∈ T.powerset, ∏ i ∈ S, x i := h1
    _ = ∏ i ∈ T, (x i + 1) := h2
    _ ≤ ∏ i ∈ T, Real.exp (x i) := h3
    _ = Real.exp (∑ i ∈ T, x i) := h4

/-! ## The Newton-type recursion in the first power sum -/

/-- The `k`-th elementary symmetric sum of `μ` over the `k`-subsets of `T`. -/
def esymm (T : Finset ℕ) (μ : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ S ∈ T.powersetCard k, ∏ i ∈ S, μ i

@[simp] theorem esymm_zero (T : Finset ℕ) (μ : ℕ → ℂ) : esymm T μ 0 = 1 := by
  simp [esymm]

/-- **The recursion.**  `p₁ · e_k = (k+1) · e_{k+1} + D_k`, where the error `D_k`
is supported on the diagonal `j ∈ S`.  No alternating signs occur. -/
theorem sum_mul_esymm (T : Finset ℕ) (μ : ℕ → ℂ) (k : ℕ) :
    (∑ j ∈ T, μ j) * esymm T μ k
      = ((k : ℂ) + 1) * esymm T μ (k + 1)
        + ∑ S ∈ T.powersetCard k, ∑ j ∈ S, μ j * ∏ i ∈ S, μ i := by
  classical
  have hsplit : ∀ S ∈ T.powersetCard k,
      (∑ j ∈ T, μ j) * ∏ i ∈ S, μ i
        = (∑ j ∈ T \ S, ∏ i ∈ insert j S, μ i) + ∑ j ∈ S, μ j * ∏ i ∈ S, μ i := by
    intro S hS
    have hsub : S ⊆ T := (Finset.mem_powersetCard.mp hS).1
    have hsd : (∑ j ∈ T \ S, μ j) + ∑ j ∈ S, μ j = ∑ j ∈ T, μ j :=
      Finset.sum_sdiff hsub
    have hins : ∀ j ∈ T \ S, (∏ i ∈ insert j S, μ i) = μ j * ∏ i ∈ S, μ i := by
      intro j hj
      exact Finset.prod_insert (Finset.mem_sdiff.mp hj).2
    rw [Finset.sum_congr rfl hins, ← hsd, add_mul, Finset.sum_mul, Finset.sum_mul]
  have hL : (∑ j ∈ T, μ j) * esymm T μ k
      = (∑ S ∈ T.powersetCard k, ∑ j ∈ T \ S, ∏ i ∈ insert j S, μ i)
        + ∑ S ∈ T.powersetCard k, ∑ j ∈ S, μ j * ∏ i ∈ S, μ i := by
    rw [esymm, Finset.mul_sum, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  rw [hL]
  congr 1
  rw [sum_powersetCard_sdiff_insert T k (fun S _ => ∏ i ∈ S, μ i)]
  rw [esymm, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hcard : S.card = k + 1 := (Finset.mem_powersetCard.mp hS).2
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  ring

/-! ## The diagonal error -/

/-- The diagonal error of the recursion is bounded by `(∑|μ|²) · e^{∑|μ|}`,
uniformly in `k`. -/
theorem norm_diagonal_le (T : Finset ℕ) (μ : ℕ → ℂ) (k : ℕ) :
    ‖∑ S ∈ T.powersetCard k, ∑ j ∈ S, μ j * ∏ i ∈ S, μ i‖
      ≤ (∑ j ∈ T, ‖μ j‖ ^ 2) * Real.exp (∑ j ∈ T, ‖μ j‖) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : (∑ S ∈ T.powersetCard 0, ∑ j ∈ S, μ j * ∏ i ∈ S, μ i) = 0 := by
      simp
    rw [this, norm_zero]
    have h1 : (0 : ℝ) ≤ ∑ j ∈ T, ‖μ j‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => by positivity
    positivity
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  -- the termwise bound
  have hterm : ‖∑ S ∈ T.powersetCard (m + 1), ∑ j ∈ S, μ j * ∏ i ∈ S, μ i‖
      ≤ ∑ S ∈ T.powersetCard (m + 1), ∑ j ∈ S, ‖μ j‖ ^ 2 * ∏ i ∈ S.erase j, ‖μ i‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro S _
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro j hj
    have hprod : (∏ i ∈ S, ‖μ i‖) = ‖μ j‖ * ∏ i ∈ S.erase j, ‖μ i‖ :=
      (Finset.mul_prod_erase _ _ hj).symm
    rw [norm_mul, norm_prod, hprod]
    exact le_of_eq (by ring)
  refine le_trans hterm ?_
  -- reindex the diagonal back down one level
  rw [← sum_powersetCard_sdiff_insert T m
    (fun S j => ‖μ j‖ ^ 2 * ∏ i ∈ S.erase j, ‖μ i‖)]
  have hrw : ∀ S ∈ T.powersetCard m, ∀ j ∈ T \ S,
      ‖μ j‖ ^ 2 * ∏ i ∈ (insert j S).erase j, ‖μ i‖
        = ‖μ j‖ ^ 2 * ∏ i ∈ S, ‖μ i‖ := by
    intro S _ j hj
    rw [Finset.erase_insert (Finset.mem_sdiff.mp hj).2]
  have hstep : (∑ S ∈ T.powersetCard m, ∑ j ∈ T \ S,
        ‖μ j‖ ^ 2 * ∏ i ∈ (insert j S).erase j, ‖μ i‖)
      ≤ ∑ S ∈ T.powersetCard m, (∑ j ∈ T, ‖μ j‖ ^ 2) * ∏ i ∈ S, ‖μ i‖ := by
    refine Finset.sum_le_sum ?_
    intro S hS
    rw [Finset.sum_congr rfl (hrw S hS), ← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun i _ _ => by positivity)
  refine le_trans hstep ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (esymm_le_exp T m (fun i => ‖μ i‖) (fun i => norm_nonneg _))
    (Finset.sum_nonneg fun j _ => by positivity)

/-! ## The layer limit for abstract weights -/

/-- **Item (iv), abstractly.**  If the weights sum to `a`, their squares sum to
`0`, and their absolute sums stay bounded, then the `k`-th elementary symmetric
sum tends to `a^k/k!`, for every fixed `k`. -/
theorem tendsto_esymm {T : ℕ → Finset ℕ} {μ : ℕ → ℕ → ℂ} {a : ℂ} {M : ℝ}
    (hM : ∀ᶠ n : ℕ in atTop, (∑ j ∈ T n, ‖μ n j‖) ≤ M)
    (hp1 : Tendsto (fun n : ℕ => ∑ j ∈ T n, μ n j) atTop (𝓝 a))
    (hQ : Tendsto (fun n : ℕ => ∑ j ∈ T n, ‖μ n j‖ ^ 2) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n : ℕ => esymm (T n) (μ n) k) atTop
      (𝓝 (a ^ k / (Nat.factorial k))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hDzero : Tendsto (fun n : ℕ =>
        ∑ S ∈ (T n).powersetCard k, ∑ j ∈ S, μ n j * ∏ i ∈ S, μ n i) atTop (𝓝 0) := by
      have hmaj : Tendsto (fun n : ℕ =>
          (∑ j ∈ T n, ‖μ n j‖ ^ 2) * Real.exp M) atTop (𝓝 0) := by
        simpa using hQ.mul_const (Real.exp M)
      refine squeeze_zero_norm' ?_ hmaj
      filter_upwards [hM] with n hn
      refine le_trans (norm_diagonal_le (T n) (μ n) k) ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hn)
        (Finset.sum_nonneg fun j _ => by positivity)
    have hcomb := (hp1.mul ih).sub hDzero
    rw [sub_zero] at hcomb
    have hkne : ((k : ℂ) + 1) ≠ 0 := by
      have h : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      simpa using h
    have heq : ∀ n : ℕ, esymm (T n) (μ n) (k + 1)
        = (((∑ j ∈ T n, μ n j) * esymm (T n) (μ n) k)
            - ∑ S ∈ (T n).powersetCard k, ∑ j ∈ S, μ n j * ∏ i ∈ S, μ n i)
          / ((k : ℂ) + 1) := by
      intro n
      rw [sum_mul_esymm (T n) (μ n) k]
      field_simp
      ring
    have hval : a ^ (k + 1) / (Nat.factorial (k + 1))
        = (a * (a ^ k / (Nat.factorial k))) / ((k : ℂ) + 1) := by
      have hfk : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [hval]
    exact Filter.Tendsto.congr (fun n => (heq n).symm) (hcomb.div_const ((k : ℂ) + 1))

/-! ## The one-level weights of the factorial route

`mu t c ε n j = ∫₀¹ h_j`, the mean of the jump factor at level `j`.  The two
size facts a symmetric-function argument needs about these weights are proved
outright below, so the layer limit is left resting on exactly two analytic
inputs. -/

open FactorialRoute

/-- The one-level weight `μ_{n,j} = ∫₀¹ h_j dα`. -/
def mu (t c ε : ℝ) (n j : ℕ) : ℂ :=
  ∫ α in Ioo (0:ℝ) 1, jumpFactor t c ε n j α

lemma mu_eq_integral_prod (t c ε : ℝ) (n j : ℕ) :
    mu t c ε n j = ∫ α in Ioo (0:ℝ) 1, ∏ i ∈ ({j} : Finset ℕ), jumpFactor t c ε n i α := by
  simp [mu]

/-- The pointwise one-level bound `‖μ_{n,j}‖ ≤ 2C/L`, from the `k`-uniform tuple
bound at `|S| = 1`. -/
lemma norm_mu_le (t c ε : ℝ) {C : ℝ} {n : ℕ}
    (hbnd : ∀ S : Finset ℕ, unifIoo.real (tupleBigEvent c ε n S) ≤ (C / Lnorm n) ^ S.card)
    (j : ℕ) : ‖mu t c ε n j‖ ≤ 2 * (C / Lnorm n) := by
  have h1 := norm_integral_prod_jumpFactor_le t c ε n ({j} : Finset ℕ)
  have h2 := hbnd ({j} : Finset ℕ)
  rw [Finset.card_singleton] at h1 h2
  rw [mu_eq_integral_prod]
  simpa using le_trans h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))

/-- Above the Lamé cap the weight vanishes, deterministically. -/
lemma mu_eq_zero_of_lameCap (t c ε : ℝ) {n : ℕ} (hn : 1 ≤ n) {j : ℕ}
    (hj : lameCap n ≤ j) : mu t c ε n j = 0 := by
  rw [mu_eq_integral_prod]
  exact integral_prod_jumpFactor_eq_zero_of_lameCap t c ε hn ({j} : Finset ℕ)
    (Finset.mem_singleton_self j) hj

/-- **The one-level weights are absolutely summable, uniformly in `n`.**  Not an
assumption: `O(L)` levels contribute by the deterministic cap, each of size
`O(1/L)` by the tuple bound. -/
theorem sum_norm_mu_le (t c ε : ℝ) {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n)
    (hL : 3 ≤ Lnorm n)
    (hbnd : ∀ S : Finset ℕ, unifIoo.real (tupleBigEvent c ε n S) ≤ (C / Lnorm n) ^ S.card) :
    (∑ j ∈ Finset.range (n + 1), ‖mu t c ε n j‖) ≤ 8 * C := by
  classical
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  set M : ℕ := min (n + 1) (lameCap n) with hM
  have hcap : (∑ j ∈ Finset.range (n + 1), ‖mu t c ε n j‖)
      = ∑ j ∈ Finset.range M, ‖mu t c ε n j‖ := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro j hj
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _))
    · intro j hjmem hjnot
      have hjn : j < n + 1 := Finset.mem_range.mp hjmem
      have hjc : lameCap n ≤ j := by
        simp only [hM, Finset.mem_range, not_lt] at hjnot
        omega
      rw [mu_eq_zero_of_lameCap t c ε hn hjc, norm_zero]
  rw [hcap]
  have hterm : ∀ j ∈ Finset.range M, ‖mu t c ε n j‖ ≤ 2 * (C / Lnorm n) :=
    fun j _ => norm_mu_le t c ε hbnd j
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hMle : (M : ℝ) ≤ 4 * Lnorm n :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (min_le_right (n + 1) (lameCap n)))
      (lameCap_le hL)
  have h1 : (M : ℝ) * (2 * (C / Lnorm n)) ≤ (4 * Lnorm n) * (2 * (C / Lnorm n)) :=
    mul_le_mul_of_nonneg_right hMle (by positivity)
  refine le_trans h1 (le_of_eq ?_)
  field_simp
  ring

/-- **The one-level weights are uniformly negligible in `L²`.**  Also not an
assumption. -/
theorem sum_norm_mu_sq_le (t c ε : ℝ) {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n)
    (hL : 3 ≤ Lnorm n)
    (hbnd : ∀ S : Finset ℕ, unifIoo.real (tupleBigEvent c ε n S) ≤ (C / Lnorm n) ^ S.card) :
    (∑ j ∈ Finset.range (n + 1), ‖mu t c ε n j‖ ^ 2) ≤ (2 * (C / Lnorm n)) * (8 * C) := by
  have hL0 : (0 : ℝ) < Lnorm n := by linarith
  have hstep : (∑ j ∈ Finset.range (n + 1), ‖mu t c ε n j‖ ^ 2)
      ≤ ∑ j ∈ Finset.range (n + 1), (2 * (C / Lnorm n)) * ‖mu t c ε n j‖ := by
    refine Finset.sum_le_sum ?_
    intro j _
    have h := norm_mu_le t c ε hbnd j
    have hnn : (0 : ℝ) ≤ ‖mu t c ε n j‖ := norm_nonneg _
    nlinarith
  refine le_trans hstep ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_norm_mu_le t c ε hC hn hL hbnd) (by positivity)

/-! ## The layer limit, reduced to two analytic inputs -/

/-- **The layer limit from the one-level limit and subset quasi-independence.**

`hp1` is the one-level limit for the complex symbol `x ↦ (e^{itx}−1)1{|x|>ε}`
and `hqi` is the `k`-subset quasi-independence for the same symbol.  Nothing
else is assumed: the two size conditions of the symmetric-function argument are
supplied by `sum_norm_mu_le` and `sum_norm_mu_sq_le`, which rest only on the
proved `FactorialRoute.exists_tupleBigEvent_bound` and the deterministic Lamé
cap.  This is item (iv) of the `FactorialSeries` list, discharged. -/
theorem layerSum_tendsto_of_inputs (c : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (a : ℂ) (k : ℕ)
    (hp1 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), mu t c ε n j) atTop (𝓝 a))
    (hqi : Tendsto (fun n : ℕ =>
        ∑ S ∈ Finset.powersetCard k (Finset.range (n + 1)),
          ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
              - ∏ j ∈ S, mu t c ε n j‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => layerSum t c ε n k) atTop (𝓝 (a ^ k / (Nat.factorial k))) := by
  classical
  obtain ⟨C, hC, hCn⟩ := exists_tupleBigEvent_bound c hε
  have hL3 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop 3
  have hM : ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (n + 1), ‖mu t c ε n j‖) ≤ 8 * C := by
    filter_upwards [hCn, hL3, eventually_ge_atTop 1] with n hn hL hn1
    exact sum_norm_mu_le t c ε hC hn1 hL hn
  have hQ : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range (n + 1), ‖mu t c ε n j‖ ^ 2) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun n : ℕ => (2 * (C / Lnorm n)) * (8 * C)) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => C / Lnorm n) atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds TupleMeasure.tendsto_Lnorm_atTop
      simpa using (h.const_mul (2 : ℝ)).mul_const (8 * C)
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards with n
      exact Finset.sum_nonneg fun j _ => by positivity
    · filter_upwards [hCn, hL3, eventually_ge_atTop 1] with n hn hL hn1
      exact sum_norm_mu_sq_le t c ε hC hn1 hL hn
  have hesymm : Tendsto (fun n : ℕ =>
      esymm (Finset.range (n + 1)) (mu t c ε n) k) atTop
      (𝓝 (a ^ k / (Nat.factorial k))) :=
    tendsto_esymm hM hp1 hQ k
  have hdiff : Tendsto (fun n : ℕ =>
      layerSum t c ε n k - esymm (Finset.range (n + 1)) (mu t c ε n) k) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hqi
    filter_upwards with n
    rw [layerSum, esymm, ← Finset.sum_sub_distrib]
    exact norm_sum_le _ _
  have h := hdiff.add hesymm
  rw [zero_add] at h
  exact Filter.Tendsto.congr (fun n => by ring) h

/-! ## `CorFinal.largeSum_charFun_limit`, reduced to two analytic inputs -/

/-- **The whole of DEBT 1, from the one-level limit and subset quasi-independence
for the complex symbol.**

The conclusion is the statement of `Kwon1002.CorFinal.largeSum_charFun_limit`
reproduced token for token (guarded by the anonymous `example` at the foot of
this file).  The hypotheses are exactly two, both about the symbol
`x ↦ (e^{itx} − 1)1{|x| > ε}` and both `k`-free in `hp1`'s case:

* `hp1` — the one-level limit `∑_{j ≤ n} ∫₀¹ h_j → Λ̂`;
* `hqi` — for each `k`, the `k`-subset quasi-independence
  `∑_{|S| = k} |∫₀¹ ∏_{j∈S} h_j − ∏_{j∈S} ∫₀¹ h_j| → 0`.

Everything else the route needed — the powerset expansion, the domination, the
Lamé cap, the `k`-uniform tuple bound, the series interchange, the
elementary-symmetric passage and the two weight-size conditions — is proved. -/
theorem largeSum_charFun_limit_of_two_inputs (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (t : ℝ)
    (hp1 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), mu t c ε n j) atTop
      (𝓝 (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ))))
    (hqi : ∀ k : ℕ, Tendsto (fun n : ℕ =>
        ∑ S ∈ Finset.powersetCard k (Finset.range (n + 1)),
          ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
              - ∏ j ∈ S, mu t c ε n j‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ α in Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Assembly5.largeSum c ε α n : ℂ) * Complex.I)) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) :=
  largeSum_charFun_limit_of_layer_limit c ε hε0 hε1 t
    (fun k => layerSum_tendsto_of_inputs c hε0 t _ k hp1 (hqi k))

/-! ## The two record corrections, checked in Lean

`FactorialSeries` items 2 and 3, and `MultiLevel` items 2 and 3, are proved and
axiom-clean where they live.  The `example`s below are the check. -/

example (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j}).ncard : ℝ))
        ≤ C * (Lnorm n) ^ (r - 1) * Hscale n :=
  Kwon1002.nonGood_tuple_count' r

example (c : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hB0 : ∃ δ > 0, ∀ x ∈ B, δ ≤ |x|) (hBbd : ∃ R : ℝ, ∀ x ∈ B, |x| ≤ R) (k : ℕ) :
    Tendsto (fun n : ℕ =>
        (∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
            unifIoo.real (Erdos1002.tupleEvent (LevyExponent.bulkMarkEvent c n B) f))
          - ∑ f : Fin k ↪ (Finset.range (n + 1) : Finset ℕ),
              unifIoo.real (Erdos1002.tupleEvent (TupleFinal.detMarkEvent n B) f))
      atTop (𝓝 0) :=
  TupleFinal.bulk_window_bridge_tuple c B hB hB0 hBbd k

end

end LayerAssembly

end Kwon1002

/- **Statement guard.**  The conclusion of
`Kwon1002.LayerAssembly.largeSum_charFun_limit_of_two_inputs` is the statement of
`Kwon1002.CorFinal.largeSum_charFun_limit`, token for token.  The `example`
mentions a sorried declaration, so it is anonymous and nothing proved above
depends on it. -/
example : ∀ (c ε : ℝ), 0 < ε → ε < 1 → ∀ t : ℝ,
    Filter.Tendsto (fun n : ℕ => ∫ α in Set.Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Kwon1002.Assembly5.largeSum c ε α n : ℂ) * Complex.I)) Filter.atTop
      (nhds (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (Kwon1002.levyIntensityDensity x : ℂ)))) :=
  @Kwon1002.CorFinal.largeSum_charFun_limit
