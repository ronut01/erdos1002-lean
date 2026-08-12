import Kwon1002.DigitTail
import Kwon1002.LDObservable

/-!
# Large deviations, stage A3: the excess-sum tail

At cap `u ≥ log(48(r+1))` the truncation excess
`E_r = Σ_{i<r} (flog(x_i) − u)⁺` has tail
`P(E_r > w) ≤ 3 exp(−w/(8(log(r+1) + 2)))` under Lebesgue measure.

Route (dyadic-rank union bound over `digit_tail_product`): with
`J := Nat.log2 r`, layers `τ_j := w/(2^j (2J+4))` for `j = 0, …, J+1`, if
`E_r > w` then either some excess exceeds `τ_0` or some layer `1 ≤ j ≤ J+1`
has `≥ 2^j` indices with excess `> τ_j` (layer-cake contradiction:
otherwise `E_r ≤ w(2J+3)/(2J+4) < w`).  Each layer event forces `2^j`
distinct digits `≥ e^{u+τ_j}`, so `digit_tail_product` and
`(r choose k) ≤ (r+1)^k` give the bound
`(24(r+1)e^{−u})^{2^j} e^{−2^j τ_j} ≤ 2^{−2^j} e^{−w/(2J+4)}`, and the
geometric sum closes at `3 e^{−w/(2J+4)}`.  Finally
`2J + 4 ≤ 8(log(r+1)+2)`.

The digit bridge: `flog(x_i) > t ⟹ digit α i ≥ e^t` for irrational
`α ∈ (0,1)` (since `a_{i+1} = 1/x_i − x_{i+1} ≥ e^{t+λ} − 1 ≥ e^t`,
using `λ > 1`).
-/

open Set MeasureTheory

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-- The dyadic geometric tail: `Σ_{j<n} (1/2)^{j+1} ≤ 1 − (1/2)^n`. -/
private lemma sum_half_pow_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1 : ℝ) / 2) ^ (j + 1) ≤ 1 - (1 / 2) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ((1 : ℝ) / 2) ^ (n + 1) = (1 / 2) ^ n * (1 / 2) := pow_succ _ _
    linarith

/-- Layer-cake pointwise bound: for a decreasing sequence of thresholds
`τ` and a value `v ≤ τ 0`, `v` is controlled by the deepest threshold plus
the telescoping increments over the crossed layers. -/
private lemma layer_pointwise (τ : ℕ → ℝ) (hmono : ∀ j, τ (j + 1) ≤ τ j)
    {v : ℝ} (hv : v ≤ τ 0) (n : ℕ) :
    v ≤ τ n + ∑ j ∈ Finset.range n,
      (τ j - τ (j + 1)) * (if τ (j + 1) < v then (1 : ℝ) else 0) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range n,
        (τ j - τ (j + 1)) * (if τ (j + 1) < v then (1 : ℝ) else 0) := by
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases hj : τ (j + 1) < v
      · rw [if_pos hj]
        have := hmono j
        linarith
      · rw [if_neg hj]
        simp
    by_cases hc : τ (n + 1) < v
    · rw [if_pos hc]
      linarith
    · rw [if_neg hc]
      push_neg at hc
      linarith

/-- The layer-cake count bound: if for every layer `j < J + 2` fewer than
`2^j` indices have excess above `w/(2^j B)`, then the total excess is at
most `(J+2)·(w/B)`. -/
private lemma excess_sum_le {r J : ℕ} (hr : r ≤ 2 ^ (J + 1)) {w B : ℝ}
    (hB : 0 < B) (hw : 0 ≤ w) (e : ℕ → ℝ)
    (hcount : ∀ j < J + 2,
      ((Finset.range r).filter (fun i => w / (2 ^ j * B) < e i)).card < 2 ^ j) :
    ∑ i ∈ Finset.range r, e i ≤ ((J : ℝ) + 2) * (w / B) := by
  have hτdiff : ∀ j : ℕ,
      w / (2 ^ j * B) - w / (2 ^ (j + 1) * B) = w / (2 ^ (j + 1) * B) := by
    intro j
    have h1 : ((2 : ℝ) ^ j) ≠ 0 := by positivity
    have h2 : B ≠ 0 := ne_of_gt hB
    field_simp
    ring
  have hτnn : ∀ j : ℕ, 0 ≤ w / (2 ^ j * B) := fun j => div_nonneg hw (by positivity)
  have hτmono : ∀ j : ℕ, w / (2 ^ (j + 1) * B) ≤ w / (2 ^ j * B) := by
    intro j
    have h1 := hτdiff j
    have h2 := hτnn (j + 1)
    linarith
  -- layer 0: no excess exceeds `τ 0`
  have h0 : ∀ i ∈ Finset.range r, e i ≤ w / (2 ^ 0 * B) := by
    intro i hi
    by_contra hlt
    push_neg at hlt
    have hmem : i ∈ (Finset.range r).filter (fun i => w / (2 ^ 0 * B) < e i) :=
      Finset.mem_filter.mpr ⟨hi, hlt⟩
    have hc := hcount 0 (by omega)
    rw [Nat.pow_zero] at hc
    rw [Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hc)] at hmem
    simp at hmem
  have hpoint : ∀ i ∈ Finset.range r,
      e i ≤ w / (2 ^ (J + 1) * B) + ∑ j ∈ Finset.range (J + 1),
        (w / (2 ^ j * B) - w / (2 ^ (j + 1) * B)) *
          (if w / (2 ^ (j + 1) * B) < e i then (1 : ℝ) else 0) :=
    fun i hi => layer_pointwise (fun j => w / (2 ^ j * B)) hτmono (h0 i hi) (J + 1)
  have hstep1 : (r : ℝ) * (w / (2 ^ (J + 1) * B)) ≤ w / B := by
    have hrle : (r : ℝ) ≤ (2 : ℝ) ^ (J + 1) := by exact_mod_cast hr
    calc (r : ℝ) * (w / (2 ^ (J + 1) * B))
        ≤ (2 : ℝ) ^ (J + 1) * (w / (2 ^ (J + 1) * B)) :=
          mul_le_mul_of_nonneg_right hrle (hτnn (J + 1))
      _ = w / B := by
          have h1 : ((2 : ℝ) ^ (J + 1)) ≠ 0 := by positivity
          have h2 : B ≠ 0 := ne_of_gt hB
          field_simp
  have hstep2 : ∀ j ∈ Finset.range (J + 1),
      (w / (2 ^ j * B) - w / (2 ^ (j + 1) * B)) *
        (((Finset.range r).filter (fun i => w / (2 ^ (j + 1) * B) < e i)).card : ℝ)
      ≤ w / B := by
    intro j hj
    rw [hτdiff j]
    have hcard : (((Finset.range r).filter
        (fun i => w / (2 ^ (j + 1) * B) < e i)).card : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      have h1 := (hcount (j + 1) (by rw [Finset.mem_range] at hj; omega)).le
      have h2 := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at h2
      exact h2
    calc w / (2 ^ (j + 1) * B) * (((Finset.range r).filter
          (fun i => w / (2 ^ (j + 1) * B) < e i)).card : ℝ)
        ≤ w / (2 ^ (j + 1) * B) * (2 : ℝ) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left hcard (hτnn (j + 1))
      _ = w / B := by
          have h1 : ((2 : ℝ) ^ (j + 1)) ≠ 0 := by positivity
          have h2 : B ≠ 0 := ne_of_gt hB
          field_simp
  calc ∑ i ∈ Finset.range r, e i
      ≤ ∑ i ∈ Finset.range r, (w / (2 ^ (J + 1) * B) + ∑ j ∈ Finset.range (J + 1),
          (w / (2 ^ j * B) - w / (2 ^ (j + 1) * B)) *
            (if w / (2 ^ (j + 1) * B) < e i then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum hpoint
    _ = (r : ℝ) * (w / (2 ^ (J + 1) * B)) + ∑ j ∈ Finset.range (J + 1),
          (w / (2 ^ j * B) - w / (2 ^ (j + 1) * B)) *
            (((Finset.range r).filter
              (fun i => w / (2 ^ (j + 1) * B) < e i)).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ w / B + ∑ j ∈ Finset.range (J + 1), w / B :=
        add_le_add hstep1 (Finset.sum_le_sum hstep2)
    _ = ((J : ℝ) + 2) * (w / B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Digit bridge: a large value of the observable forces a large digit. -/
lemma exp_le_digit_of_flog {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) {i : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (h : t < flog (gaussIter α i)) :
    Real.exp t ≤ (digit α i : ℝ) := by
  have hx : gaussIter α i ∈ Ioo (0 : ℝ) 1 := gaussIter_mem_Ioo hα hirr i
  have hx1 : gaussIter α (i + 1) ∈ Ioo (0 : ℝ) 1 := gaussIter_mem_Ioo hα hirr (i + 1)
  have hlog : Real.log (gaussIter α i) < -(t + lyapunov) := by
    simp only [flog] at h
    linarith
  have hxlt : gaussIter α i < Real.exp (-(t + lyapunov)) := by
    have h1 : Real.exp (Real.log (gaussIter α i)) < Real.exp (-(t + lyapunov)) :=
      Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log hx.1] at h1
  have hinv : Real.exp (t + lyapunov) < (gaussIter α i)⁻¹ := by
    rw [lt_inv_comm₀ (Real.exp_pos _) hx.1]
    rwa [← Real.exp_neg]
  have hdig : (gaussIter α i)⁻¹ = (digit α i : ℝ) + gaussIter α (i + 1) :=
    inv_gaussIter_eq hα hirr i
  have hexpt : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hexpl : 2 < Real.exp lyapunov := by
    have h1 := Real.add_one_le_exp lyapunov
    have h2 := one_lt_lyapunov
    linarith
  have hsplit : Real.exp (t + lyapunov) = Real.exp t * Real.exp lyapunov :=
    Real.exp_add t lyapunov
  have hmul : Real.exp t * 2 < Real.exp t * Real.exp lyapunov :=
    mul_lt_mul_of_pos_left hexpl (Real.exp_pos t)
  linarith [hx1.2]

/-- **The excess-sum tail.**  There is a threshold constant `C₀ ≥ 1`
(essentially twice the constant of `digit_tail_product`) such that for
`r ≥ 1`, `u ≥ log(C₀(r+1))` and `w > 0`, the Lebesgue measure of the set
where the truncation excess at cap `u` exceeds `w` is at most
`3 exp(−w/(8(log(r+1)+2)))`. -/
theorem excess_tail :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ r : ℕ, 1 ≤ r → ∀ u w : ℝ,
      Real.log (C₀ * (r + 1 : ℕ)) ≤ u → 0 < w →
      (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ Irrational α ∧
          w < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0}).toReal
        ≤ 3 * Real.exp (-w / (8 * (Real.log (r + 1 : ℕ) + 2))) := by
  obtain ⟨C, hCpos, hprod⟩ := digit_tail_product
  refine ⟨2 * max C 1, by linarith [le_max_right C 1], ?_⟩
  intro r hr u w hu hw
  -- basic positivity facts
  have hmax1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hC1 : C ≤ max C 1 := le_max_left _ _
  have hRpos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
  have hR2 : (2 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hr
  have hX1 : (1 : ℝ) < 2 * max C 1 * ((r + 1 : ℕ) : ℝ) := by
    have h4 : 2 * max C 1 * 2 ≤ 2 * max C 1 * ((r + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hR2 (by linarith)
    linarith
  have hXpos : (0 : ℝ) < 2 * max C 1 * ((r + 1 : ℕ) : ℝ) := lt_trans one_pos hX1
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le (Real.log_pos hX1) hu
  -- the dyadic scale
  set J := Nat.log 2 r with hJdef
  set B : ℝ := 2 * ((J : ℝ) + 2) with hBdef
  have hBpos : (0 : ℝ) < B := by rw [hBdef]; positivity
  have hτpos : ∀ j : ℕ, 0 < w / (2 ^ j * B) :=
    fun j => div_pos hw (mul_pos (pow_pos two_pos j) hBpos)
  have hrJ : r ≤ 2 ^ (J + 1) := (Nat.lt_pow_succ_log_self (by norm_num) r).le
  -- `e^{-u}` is dominated by `1/(2 max(C,1)(r+1))`
  have hexpu : Real.exp (-u) ≤ (2 * max C 1 * ((r + 1 : ℕ) : ℝ))⁻¹ := by
    have h1 : Real.exp (-u)
        ≤ Real.exp (Real.log ((2 * max C 1 * ((r + 1 : ℕ) : ℝ))⁻¹)) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_inv]
      exact neg_le_neg hu
    rwa [Real.exp_log (inv_pos.mpr hXpos)] at h1
  have hhalf : ((r + 1 : ℕ) : ℝ) * C * Real.exp (-u) ≤ 1 / 2 := by
    have hnn : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * C := mul_nonneg hRpos.le hCpos.le
    calc ((r + 1 : ℕ) : ℝ) * C * Real.exp (-u)
        ≤ ((r + 1 : ℕ) : ℝ) * C * (2 * max C 1 * ((r + 1 : ℕ) : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hexpu hnn
      _ ≤ 1 / 2 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hXpos]
          nlinarith [mul_nonneg (sub_nonneg.mpr hC1) hRpos.le]
  -- the layer events and the per-layer digit events
  set E : ℕ → Set ℝ := fun j => {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ Irrational α ∧
    2 ^ j ≤ ((Finset.range r).filter
      (fun i => w / (2 ^ j * B) < max (flog (gaussIter α i) - u) 0)).card} with hEdef
  set F : ℕ → Finset ℕ → Set ℝ := fun j S => {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
    ∀ i ∈ S, Real.exp (u + w / (2 ^ j * B)) ≤ (digit α i : ℝ)} with hFdef
  -- inclusion 1: the bad set is covered by the layer events
  have hsub1 : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ Irrational α ∧
      w < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0}
      ⊆ ⋃ j ∈ Finset.range (J + 2), E j := by
    intro α hα
    obtain ⟨h1, h2, h3⟩ := hα
    by_contra hnot
    rw [Set.mem_iUnion₂] at hnot
    push_neg at hnot
    have hcount : ∀ j < J + 2, ((Finset.range r).filter
        (fun i => w / (2 ^ j * B) < max (flog (gaussIter α i) - u) 0)).card < 2 ^ j := by
      intro j hj
      by_contra hge
      push_neg at hge
      exact hnot j (Finset.mem_range.mpr hj) ⟨h1, h2, hge⟩
    have hle : ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0
        ≤ ((J : ℝ) + 2) * (w / B) :=
      excess_sum_le hrJ hBpos hw.le _ hcount
    have hJ2 : ((J : ℝ) + 2) ≠ 0 := by positivity
    have hhalfw : ((J : ℝ) + 2) * (w / B) = w / 2 := by
      rw [hBdef]
      field_simp
    linarith
  -- inclusion 2: each layer event is covered by digit events over subsets
  have hsub2 : ∀ j : ℕ,
      E j ⊆ ⋃ S ∈ Finset.powersetCard (2 ^ j) (Finset.range r), F j S := by
    intro j α hα
    obtain ⟨h1, h2, hcard⟩ := hα
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    have hSsub' : S ⊆ Finset.range r := hSsub.trans (Finset.filter_subset _ _)
    rw [Set.mem_iUnion₂]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hSsub', hScard⟩, h1, ?_⟩
    intro i hi
    have hfilt := Finset.mem_filter.mp (hSsub hi)
    have hτlt : w / (2 ^ j * B) < flog (gaussIter α i) - u := by
      rcases lt_max_iff.mp hfilt.2 with hcase | hcase
      · exact hcase
      · exact absurd hcase (not_lt.mpr (hτpos j).le)
    exact exp_le_digit_of_flog h1 h2 (by linarith [hτpos j, hupos]) (by linarith)
  -- per-subset bound from `digit_tail_product`
  have hFbound : ∀ j : ℕ, ∀ S ∈ Finset.powersetCard (2 ^ j) (Finset.range r),
      volume (F j S) ≤ ENNReal.ofReal
        ((C * Real.exp (-(u + w / (2 ^ j * B)))) ^ 2 ^ j) := by
    intro j S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨hSsub, hScard⟩ := hS
    set js : Fin (2 ^ j) → ℕ := fun i => ((S.orderIsoOfFin hScard i : ℕ)) with hjs
    set A : Fin (2 ^ j) → ℝ := fun _ => Real.exp (u + w / (2 ^ j * B)) with hA
    have hinj : Function.Injective js := fun a b hab =>
      (S.orderIsoOfFin hScard).injective (Subtype.ext hab)
    have hA1 : ∀ i, 1 ≤ A i :=
      fun i => Real.one_le_exp (by linarith [hτpos j, hupos])
    have hbig := hprod (2 ^ j) js A hinj hA1
    have hPfin : volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ i, A i ≤ (digit α (js i) : ℝ)} ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.one_ne_top
      refine le_trans (measure_mono fun α hα => hα.1) ?_
      rw [Real.volume_Ioo]
      simp
    have hsub : F j S ⊆ {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ i, A i ≤ (digit α (js i) : ℝ)} := by
      intro α hα
      exact ⟨hα.1, fun i => hα.2 _ ((S.orderIsoOfFin hScard i).2)⟩
    calc volume (F j S)
        ≤ volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
            ∀ i, A i ≤ (digit α (js i) : ℝ)} := measure_mono hsub
      _ = ENNReal.ofReal ((volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
            ∀ i, A i ≤ (digit α (js i) : ℝ)}).toReal) :=
          (ENNReal.ofReal_toReal hPfin).symm
      _ ≤ ENNReal.ofReal ((C * Real.exp (-(u + w / (2 ^ j * B)))) ^ 2 ^ j) := by
          apply ENNReal.ofReal_le_ofReal
          refine le_trans hbig ?_
          have hAprod : ∏ i : Fin (2 ^ j), (A i)⁻¹
              = ((Real.exp (u + w / (2 ^ j * B)))⁻¹) ^ 2 ^ j := by
            simp only [hA]
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [hAprod, ← Real.exp_neg, ← mul_pow]
  -- the per-layer real bound
  have hperj : ∀ j : ℕ,
      ((r.choose (2 ^ j) : ℕ) : ℝ) * (C * Real.exp (-(u + w / (2 ^ j * B)))) ^ 2 ^ j
        ≤ (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-w / B) := by
    intro j
    have hfact : (1 : ℝ) ≤ ((2 ^ j).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hchoose : ((r.choose (2 ^ j) : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 ^ j := by
      calc ((r.choose (2 ^ j) : ℕ) : ℝ)
          ≤ (r : ℝ) ^ 2 ^ j / ((2 ^ j).factorial : ℝ) :=
            Nat.choose_le_pow_div (2 ^ j) r
        _ ≤ (r : ℝ) ^ 2 ^ j := div_le_self (by positivity) hfact
        _ ≤ ((r + 1 : ℕ) : ℝ) ^ 2 ^ j := by
            apply pow_le_pow_left₀ (Nat.cast_nonneg r)
            push_cast
            linarith
    have hsplit : (C * Real.exp (-(u + w / (2 ^ j * B)))) ^ 2 ^ j
        = (C * Real.exp (-u)) ^ 2 ^ j * Real.exp (-(w / (2 ^ j * B))) ^ 2 ^ j := by
      rw [show -(u + w / (2 ^ j * B)) = -u + -(w / (2 ^ j * B)) by ring, Real.exp_add,
        ← mul_assoc, mul_pow]
    have hτpow : Real.exp (-(w / (2 ^ j * B))) ^ 2 ^ j = Real.exp (-w / B) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have h2 : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
      rw [h2]
      have h1 : ((2 : ℝ) ^ j) ≠ 0 := by positivity
      have h2' : B ≠ 0 := ne_of_gt hBpos
      field_simp
    have hbase : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * C * Real.exp (-u) :=
      mul_nonneg (mul_nonneg hRpos.le hCpos.le) (Real.exp_pos _).le
    have hj1 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    calc ((r.choose (2 ^ j) : ℕ) : ℝ) * (C * Real.exp (-(u + w / (2 ^ j * B)))) ^ 2 ^ j
        = ((r.choose (2 ^ j) : ℕ) : ℝ) *
            ((C * Real.exp (-u)) ^ 2 ^ j * Real.exp (-w / B)) := by
          rw [hsplit, hτpow]
      _ ≤ ((r + 1 : ℕ) : ℝ) ^ 2 ^ j *
            ((C * Real.exp (-u)) ^ 2 ^ j * Real.exp (-w / B)) := by
          apply mul_le_mul_of_nonneg_right hchoose
          exact mul_nonneg
            (pow_nonneg (mul_nonneg hCpos.le (Real.exp_pos _).le) _) (Real.exp_pos _).le
      _ = (((r + 1 : ℕ) : ℝ) * C * Real.exp (-u)) ^ 2 ^ j * Real.exp (-w / B) := by
          ring
      _ ≤ (1 / 2 : ℝ) ^ 2 ^ j * Real.exp (-w / B) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase hhalf _) (Real.exp_pos _).le
      _ ≤ (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-w / B) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj1) (Real.exp_pos _).le
  -- per-layer measure bound
  have hEj : ∀ j : ℕ, volume (E j) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1) * Real.exp (-w / B)) := by
    intro j
    calc volume (E j)
        ≤ volume (⋃ S ∈ Finset.powersetCard (2 ^ j) (Finset.range r), F j S) :=
          measure_mono (hsub2 j)
      _ ≤ ∑ S ∈ Finset.powersetCard (2 ^ j) (Finset.range r), volume (F j S) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ S ∈ Finset.powersetCard (2 ^ j) (Finset.range r),
            ENNReal.ofReal ((C * Real.exp (-(u + w / (2 ^ j * B)))) ^ 2 ^ j) :=
          Finset.sum_le_sum (hFbound j)
      _ = ENNReal.ofReal (((r.choose (2 ^ j) : ℕ) : ℝ) *
            (C * Real.exp (-(u + w / (2 ^ j * B)))) ^ 2 ^ j) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1) * Real.exp (-w / B)) :=
          ENNReal.ofReal_le_ofReal (hperj j)
  -- `B` is dominated by the target rate denominator
  have hBle8 : B ≤ 8 * (Real.log ((r + 1 : ℕ) : ℝ) + 2) := by
    have hJr : 2 ^ J ≤ r := Nat.pow_log_le_self 2 (by omega)
    have h2J : ((2 : ℝ)) ^ J ≤ ((r + 1 : ℕ) : ℝ) := by
      have h1 := (Nat.cast_le (α := ℝ)).mpr hJr
      push_cast at h1 ⊢
      linarith
    have hlogJ : (J : ℝ) * Real.log 2 ≤ Real.log ((r + 1 : ℕ) : ℝ) := by
      have h1 : Real.log ((2 : ℝ) ^ J) ≤ Real.log ((r + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) h2J
      rwa [Real.log_pow] at h1
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hJnn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    rw [hBdef]
    linarith [mul_le_mul_of_nonneg_left hlog2.le hJnn]
  have hgeom : ∑ j ∈ Finset.range (J + 2), ((1 : ℝ) / 2) ^ (j + 1) ≤ 1 := by
    have h1 := sum_half_pow_le (J + 2)
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (J + 2) := by positivity
    linarith
  have hexpmono : Real.exp (-w / B) ≤
      Real.exp (-w / (8 * (Real.log ((r + 1 : ℕ) : ℝ) + 2))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left hw.le hBpos hBle8)
  -- assembly
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ Irrational α ∧
          w < ∑ i ∈ Finset.range r, max (flog (gaussIter α i) - u) 0}
      ≤ volume (⋃ j ∈ Finset.range (J + 2), E j) := measure_mono hsub1
    _ ≤ ∑ j ∈ Finset.range (J + 2), volume (E j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (J + 2),
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1) * Real.exp (-w / B)) :=
        Finset.sum_le_sum fun j _ => hEj j
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (J + 2),
          (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-w / B)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    _ ≤ ENNReal.ofReal (3 * Real.exp (-w / (8 * (Real.log ((r + 1 : ℕ) : ℝ) + 2)))) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∑ j ∈ Finset.range (J + 2), (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-w / B)
            = (∑ j ∈ Finset.range (J + 2), (1 / 2 : ℝ) ^ (j + 1)) * Real.exp (-w / B) :=
              (Finset.sum_mul _ _ _).symm
          _ ≤ 1 * Real.exp (-w / B) :=
              mul_le_mul_of_nonneg_right hgeom (Real.exp_pos _).le
          _ = Real.exp (-w / B) := one_mul _
          _ ≤ Real.exp (-w / (8 * (Real.log ((r + 1 : ℕ) : ℝ) + 2))) := hexpmono
          _ ≤ 3 * Real.exp (-w / (8 * (Real.log ((r + 1 : ℕ) : ℝ) + 2))) := by
              linarith [Real.exp_pos (-w / (8 * (Real.log ((r + 1 : ℕ) : ℝ) + 2)))]

end

end LargeDeviation

end Kwon1002
