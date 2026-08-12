import Kwon1002.LDObservable
import Kwon1002.LDPsi
import Kwon1002.LDVariance
import Kwon1002.LDLyapunov
import Kwon1002.DigitTail

/-!
# Large deviations, stage B: windowed blocks and the exponential-moment bound

The capped Birkhoff sum `Σ_{i<r} capLog u (x_i)` is approximated site-wise
by the *windowed* observable `hatSite u W`, which reads only the `W` digits
`a_{i+1}, …, a_{i+W}` (finite continued-fraction reconstruction clamped to
`[0,1]`); the approximation error per site is
`≤ e^{u+λ}·2·(1/2)^W` (cylinder contraction).  The windowed sum
`hatSum u W r` then splits into blocks of length `ℓ = 2W`; blocks of one
parity are separated digit-window functions with gap `W`, so
`LDPsi.separated_product_decouple` factorizes their exponential moments up
to `(1 + 24ρ₀^W)` per block, `LDVariance.exists_block_sq_bound` bounds each
block's second moment by `C₀ℓ`, and the elementary bound
`e^x ≤ 1 + x + 2x²` (valid for `x ≤ 1/2`) closes the per-block mgf.
Cauchy–Schwarz over the two parities is replaced by the pointwise
`fg ≤ (f² + g²)/2`, which suffices because both parities obey one bound.

Output: `exists_hatSum_mgf`, the two-sided exponential-moment bound
`E[e^{±σ hatSum}] ≤ exp(C₁(1 + σ²r [+ σr e^{−u/2}]))` in the regime
`σ·4W(u+3) ≤ 1/2`, with the mixing and windowing smallness supplied as
explicit hypotheses (the consumer chooses `W ≍ 170(log(r+1)+1)` and
`u ≍ 4 log(r+1)`, under which both hold with huge margin).
-/

open Set MeasureTheory

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-- Clamp to the unit interval. -/
def clampUnit (x : ℝ) : ℝ := max 0 (min x 1)

/-- The word of the first `W` digits of `y`. -/
def windowWord (W : ℕ) (y : ℝ) : List ℕ := List.ofFn (fun t : Fin W => digit y t)

/-- The windowed approximation to `y`: the value of the finite continued
fraction built from the first `W` digits, clamped to `[0,1]`. -/
def approxIter (W : ℕ) (y : ℝ) : ℝ :=
  clampUnit (Erdos1002.gaussInverseWord (windowWord W y) 0)

/-- The windowed capped observable at one site. -/
def hatSite (u : ℝ) (W : ℕ) (y : ℝ) : ℝ := capLog u (approxIter W y)

/-- The windowed capped Birkhoff sum. -/
def hatSum (u : ℝ) (W r : ℕ) (α : ℝ) : ℝ :=
  ∑ i ∈ Finset.range r, hatSite u W (Erdos1002.gaussOrbit i α)

/-! ### Elementary facts about the clamp -/

private lemma clampUnit_nonneg (x : ℝ) : 0 ≤ clampUnit x := le_max_left _ _

private lemma clampUnit_le_one (x : ℝ) : clampUnit x ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

private lemma clampUnit_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    clampUnit x = x := by
  unfold clampUnit
  rw [min_eq_left hx.2, max_eq_right hx.1]

private lemma abs_clampUnit_sub_le (x y : ℝ) :
    |clampUnit x - clampUnit y| ≤ |x - y| := by
  unfold clampUnit
  calc |max 0 (min x 1) - max 0 (min y 1)|
      = |max (min x 1) 0 - max (min y 1) 0| := by rw [max_comm 0, max_comm 0]
    _ ≤ |min x 1 - min y 1| := abs_max_sub_max_le_abs _ _ _
    _ ≤ max |x - y| |1 - 1| := abs_min_sub_min_le_max x 1 y 1
    _ = |x - y| := by simp

/-! ### Measurability of the windowed observable -/

private lemma measurable_digit_nat (t : ℕ) :
    Measurable (fun y : ℝ => digit y t) := by
  have h1 : Measurable (fun y : ℝ => gaussIter y t) :=
    Erdos1002.measurable_gaussMap.iterate t
  have h2 : Measurable (fun y : ℝ => ⌊(gaussIter y t)⁻¹⌋) := h1.inv.floor
  exact (measurable_of_countable Int.toNat).comp h2

private lemma measurable_approxIter (W : ℕ) : Measurable (approxIter W) := by
  have hD : Measurable (fun y : ℝ => (fun t : Fin W => digit y (t : ℕ))) :=
    measurable_pi_lambda _ (fun t => measurable_digit_nat (t : ℕ))
  have hg : Measurable (fun v : Fin W → ℕ =>
      clampUnit (Erdos1002.gaussInverseWord (List.ofFn v) 0)) :=
    measurable_of_countable _
  exact hg.comp hD

theorem measurable_hatSite (u : ℝ) (W : ℕ) : Measurable (hatSite u W) :=
  (measurable_capLog u).comp (measurable_approxIter W)

theorem measurable_hatSum (u : ℝ) (W r : ℕ) : Measurable (hatSum u W r) := by
  unfold hatSum
  exact Finset.measurable_sum _
    (fun i _ => (measurable_hatSite u W).comp (Erdos1002.measurable_gaussOrbit i))

theorem hatSite_le_cap (u : ℝ) (W : ℕ) (y : ℝ) : hatSite u W y ≤ u :=
  capLog_le_cap u _

theorem neg_lyapunov_le_hatSite {u : ℝ} (hu : 0 ≤ u) (W : ℕ) (y : ℝ) :
    -lyapunov ≤ hatSite u W y :=
  neg_lyapunov_le_capLog hu (clampUnit_le_one _)

/-! ### Reconstruction: the window word rebuilds the point -/

private lemma windowWord_zero (y : ℝ) : windowWord 0 y = [] := by
  simp [windowWord]

private lemma windowWord_succ (W : ℕ) (y : ℝ) :
    windowWord (W + 1) y = digit y 0 :: windowWord W (Erdos1002.gaussMap y) := by
  unfold windowWord
  rw [List.ofFn_succ]
  congr 1

private lemma gaussInverseWord_windowWord (W : ℕ) :
    ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 → Irrational y →
      Erdos1002.gaussInverseWord (windowWord W y) (gaussIter y W) = y := by
  induction W with
  | zero =>
      intro y _ _
      rw [windowWord_zero]
      rfl
  | succ W ih =>
      intro y hy hirr
      have hg : Erdos1002.gaussMap y ∈ Ioo (0 : ℝ) 1 := gaussMap_mem_Ioo hirr
      have hgi : Irrational (Erdos1002.gaussMap y) := gaussMap_irrational hirr
      have hiter : gaussIter y (W + 1) = gaussIter (Erdos1002.gaussMap y) W :=
        gaussIter_succ' y W
      rw [windowWord_succ, hiter]
      show Erdos1002.gaussInverseBranch (digit y 0)
          (Erdos1002.gaussInverseWord (windowWord W (Erdos1002.gaussMap y))
            (gaussIter (Erdos1002.gaussMap y) W)) = y
      rw [ih hg hgi]
      have hinv := inv_gaussIter_eq hy hirr 0
      rw [gaussIter_zero] at hinv
      have h1 : gaussIter y 1 = Erdos1002.gaussMap y := by
        rw [gaussIter_succ, gaussIter_zero]; rfl
      rw [h1] at hinv
      unfold Erdos1002.gaussInverseBranch
      rw [← hinv, one_div, inv_inv]

private lemma quarter_pow_le (W : ℕ) :
    (1 / 4 : ℝ) ^ (W / 2) ≤ 2 * (1 / 2 : ℝ) ^ W := by
  have h1 : (1 / 4 : ℝ) ^ (W / 2) = (1 / 2 : ℝ) ^ (2 * (W / 2)) := by
    rw [pow_mul]; norm_num
  have h2 : W ≤ 2 * (W / 2) + 1 := by omega
  have h4 : (1 / 2 : ℝ) ^ (2 * (W / 2)) = 2 * (1 / 2 : ℝ) ^ (2 * (W / 2) + 1) := by
    rw [pow_succ]; ring
  have h5 : (1 / 2 : ℝ) ^ (2 * (W / 2) + 1) ≤ (1 / 2 : ℝ) ^ W :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
  rw [h1, h4]
  linarith

private lemma abs_approxIter_sub_le {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational y) (W : ℕ) :
    |approxIter W y - y| ≤ 2 * (1 / 2 : ℝ) ^ W := by
  have hrec := gaussInverseWord_windowWord W hy hirr
  have h1 : |approxIter W y - y|
      ≤ |Erdos1002.gaussInverseWord (windowWord W y) 0 - y| := by
    have h := abs_clampUnit_sub_le (Erdos1002.gaussInverseWord (windowWord W y) 0) y
    rwa [clampUnit_eq_self ⟨hy.1.le, hy.2.le⟩] at h
  have hIoo : gaussIter y W ∈ Ioo (0 : ℝ) 1 := gaussIter_mem_Ioo hy hirr W
  have h2 : |Erdos1002.gaussInverseWord (windowWord W y) 0 - y|
      ≤ (1 / 4 : ℝ) ^ (W / 2) := by
    have hpos : ∀ q ∈ windowWord W y, 0 < q := by
      intro q hq
      rw [windowWord, List.mem_ofFn] at hq
      obtain ⟨t, ht⟩ := hq
      have := one_le_digit hy hirr t
      omega
    have hd := Erdos1002.dist_gaussInverseWord_le_length hpos
      (⟨le_refl (0 : ℝ), zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
      (Ioo_subset_Icc_self hIoo)
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hlen : (windowWord W y).length = W := by simp [windowWord]
    rw [hlen] at hd
    calc |Erdos1002.gaussInverseWord (windowWord W y) 0 - y|
        = |Erdos1002.gaussInverseWord (windowWord W y) 0
            - Erdos1002.gaussInverseWord (windowWord W y) (gaussIter y W)| := by
          rw [hrec]
      _ ≤ (1 / 4 : ℝ) ^ (W / 2) * |0 - gaussIter y W| := hd
      _ ≤ (1 / 4 : ℝ) ^ (W / 2) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [zero_sub, abs_neg, abs_of_nonneg hIoo.1.le]
          exact hIoo.2.le
      _ = (1 / 4 : ℝ) ^ (W / 2) := mul_one _
  have h3 := quarter_pow_le W
  linarith

/-- Site-wise windowing error, on irrationals of `(0,1)`. -/
theorem abs_hatSite_sub_capLog_le (u : ℝ) (W : ℕ) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) (hirr : Irrational y) :
    |hatSite u W y - capLog u y|
      ≤ Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W) := by
  calc |hatSite u W y - capLog u y|
      ≤ Real.exp (u + lyapunov) * |approxIter W y - y| :=
        abs_capLog_sub_capLog_le u (approxIter W y) y
    _ ≤ Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W) :=
        mul_le_mul_of_nonneg_left (abs_approxIter_sub_le hy hirr W)
          (Real.exp_nonneg _)

/-- Sum-wise windowing error, on irrationals of `(0,1)`. -/
theorem abs_hatSum_sub_capSum_le (u : ℝ) (W r : ℕ) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    |hatSum u W r α - ∑ i ∈ Finset.range r, capLog u (gaussIter α i)|
      ≤ (r : ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) := by
  have key : ∀ i ∈ Finset.range r,
      |hatSite u W (Erdos1002.gaussOrbit i α) - capLog u (gaussIter α i)|
        ≤ Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W) := by
    intro i _
    exact abs_hatSite_sub_capLog_le u W (gaussIter_mem_Ioo hα hirr i)
      (gaussIter_irrational hirr i)
  unfold hatSum
  rw [← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range r,
        (hatSite u W (Erdos1002.gaussOrbit i α) - capLog u (gaussIter α i))|
      ≤ ∑ i ∈ Finset.range r,
          |hatSite u W (Erdos1002.gaussOrbit i α) - capLog u (gaussIter α i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.range r).card •
          (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) :=
        Finset.sum_le_card_nsmul _ _ _ key
    _ = (r : ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) := by
        rw [Finset.card_range, nsmul_eq_mul]

/-! ### Elementary analytic helpers for the mgf bound -/

private lemma exp_taylor_le {x : ℝ} (hx : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + 2 * x ^ 2 := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x); linarith
  have h2 : (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg x)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have h3 : 0 < 1 - x + 2 * x ^ 2 - 2 * x ^ 3 := by
    nlinarith [sq_nonneg x, sq_nonneg (1 - x)]
  nlinarith [Real.exp_pos x, sq_nonneg x]

private lemma abs_hatSite_le {u : ℝ} (hu : 0 ≤ u) (W : ℕ) (y : ℝ) :
    |hatSite u W y| ≤ u + lyapunov :=
  abs_capLog_le hu (clampUnit_le_one _)

private lemma gaussOrbit_gaussOrbit (a b : ℕ) (x : ℝ) :
    Erdos1002.gaussOrbit a (Erdos1002.gaussOrbit b x)
      = Erdos1002.gaussOrbit (b + a) x := by
  rw [← gaussOrbit_add a b x, Nat.add_comm a b]

private lemma gaussIter_gaussOrbit (j t : ℕ) (x : ℝ) :
    gaussIter (Erdos1002.gaussOrbit j x) t = gaussIter x (j + t) := by
  show gaussMap^[t] (gaussMap^[j] x) = gaussMap^[j + t] x
  rw [Nat.add_comm j t, Function.iterate_add_apply]

private lemma digit_gaussOrbit (j t : ℕ) (x : ℝ) :
    digit (Erdos1002.gaussOrbit j x) t = digit x (j + t) := by
  unfold digit
  rw [gaussIter_gaussOrbit]

/-! ### Block observables -/

/-- The exponential of `s` times a windowed block of length `n` started at
the origin; blocks at position `t` are `blockObs … ∘ gaussOrbit t`. -/
private def blockObs (u : ℝ) (W : ℕ) (s : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun y => Real.exp (s * ∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y))

/-- The windowed block sum of the block at position `k` in blocks of
length `ℓ`, truncated at total length `r`. -/
private def blockSum (u : ℝ) (W ℓ r k : ℕ) (α : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (min ℓ (r - k * ℓ)),
    hatSite u W (Erdos1002.gaussOrbit (k * ℓ + j) α)

private lemma measurable_blockObs (u : ℝ) (W : ℕ) (s : ℝ) (n : ℕ) :
    Measurable (blockObs u W s n) := by
  apply Measurable.exp
  apply Measurable.const_mul
  exact Finset.measurable_sum _
    (fun j _ => (measurable_hatSite u W).comp (Erdos1002.measurable_gaussOrbit j))

private lemma blockObs_pos (u : ℝ) (W : ℕ) (s : ℝ) (n : ℕ) (y : ℝ) :
    0 < blockObs u W s n y := Real.exp_pos _

private lemma abs_hatBlock_le {u : ℝ} (hu : 0 ≤ u) (W n : ℕ) (y : ℝ) :
    |∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y)|
      ≤ (n : ℝ) * (u + lyapunov) := by
  calc |∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y)|
      ≤ ∑ j ∈ Finset.range n, |hatSite u W (Erdos1002.gaussOrbit j y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.range n).card • (u + lyapunov) :=
        Finset.sum_le_card_nsmul _ _ _ (fun j _ => abs_hatSite_le hu W _)
    _ = (n : ℝ) * (u + lyapunov) := by rw [Finset.card_range, nsmul_eq_mul]

private lemma blockObs_le {u : ℝ} (hu : 0 ≤ u) (W : ℕ) (s : ℝ) {n : ℕ}
    (hn : n ≤ 2 * W) (y : ℝ) :
    blockObs u W s n y ≤ Real.exp (|s| * (2 * (W : ℝ) * (u + 2))) := by
  unfold blockObs
  apply Real.exp_le_exp.mpr
  have hlam := lyapunov_lt_two
  have hlam0 := lyapunov_pos'
  have hn' : (n : ℝ) ≤ 2 * (W : ℝ) := by exact_mod_cast hn
  calc s * ∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y)
      ≤ |s * ∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y)| :=
        le_abs_self _
    _ = |s| * |∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y)| :=
        abs_mul _ _
    _ ≤ |s| * ((n : ℝ) * (u + lyapunov)) :=
        mul_le_mul_of_nonneg_left (abs_hatBlock_le hu W n y) (abs_nonneg s)
    _ ≤ |s| * (2 * (W : ℝ) * (u + 2)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg s)
        calc (n : ℝ) * (u + lyapunov) ≤ (n : ℝ) * (u + 2) :=
              mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
          _ ≤ 2 * (W : ℝ) * (u + 2) :=
              mul_le_mul_of_nonneg_right hn' (by linarith)

private lemma hatSite_window_eq (u : ℝ) (W : ℕ) {x y : ℝ} (j : ℕ)
    (hdig : ∀ i, i < j + W → digit x i = digit y i) :
    hatSite u W (Erdos1002.gaussOrbit j x) = hatSite u W (Erdos1002.gaussOrbit j y) := by
  have hww : windowWord W (Erdos1002.gaussOrbit j x)
      = windowWord W (Erdos1002.gaussOrbit j y) := by
    unfold windowWord
    congr 1
    funext t
    rw [digit_gaussOrbit, digit_gaussOrbit]
    exact hdig (j + t) (by have := t.isLt; omega)
  unfold hatSite approxIter
  rw [hww]

private lemma blockObs_digitDetermined (u : ℝ) (W : ℕ) (s : ℝ) {n : ℕ}
    (hn : n ≤ 2 * W) :
    DigitDetermined (3 * W) (blockObs u W s n) := by
  intro x y _ _ _ _ hdig
  unfold blockObs
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply hatSite_window_eq
  intro i hi
  apply hdig
  have := Finset.mem_range.mp hj
  omega

private lemma blockObs_orbit (u : ℝ) (W ℓ r : ℕ) (s : ℝ) (k : ℕ) (α : ℝ) :
    blockObs u W s (min ℓ (r - k * ℓ)) (Erdos1002.gaussOrbit (k * ℓ) α)
      = Real.exp (s * blockSum u W ℓ r k α) := by
  unfold blockObs blockSum
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussOrbit_gaussOrbit]

private lemma abs_blockSum_le {u : ℝ} (hu : 0 ≤ u) (W ℓ r k : ℕ) (α : ℝ) :
    |blockSum u W ℓ r k α|
      ≤ ((min ℓ (r - k * ℓ) : ℕ) : ℝ) * (u + lyapunov) := by
  unfold blockSum
  calc |∑ j ∈ Finset.range (min ℓ (r - k * ℓ)),
        hatSite u W (Erdos1002.gaussOrbit (k * ℓ + j) α)|
      ≤ ∑ j ∈ Finset.range (min ℓ (r - k * ℓ)),
          |hatSite u W (Erdos1002.gaussOrbit (k * ℓ + j) α)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.range (min ℓ (r - k * ℓ))).card • (u + lyapunov) :=
        Finset.sum_le_card_nsmul _ _ _ (fun j _ => abs_hatSite_le hu W _)
    _ = ((min ℓ (r - k * ℓ) : ℕ) : ℝ) * (u + lyapunov) := by
        rw [Finset.card_range, nsmul_eq_mul]

/-! ### Combinatorial helpers: block splitting and parity -/

private lemma list_range_map_prod (f : ℕ → ℝ) (c : ℕ) :
    ((List.range c).map f).prod = ∏ t ∈ Finset.range c, f t := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [List.range_succ, List.map_append, List.prod_append,
        Finset.prod_range_succ, ih]
      simp

private lemma sum_block_split {M : Type*} [AddCommMonoid M] (F : ℕ → M) (ℓ : ℕ) :
    ∀ B r : ℕ, r ≤ ℓ * B →
      ∑ i ∈ Finset.range r, F i
        = ∑ k ∈ Finset.range B,
            ∑ j ∈ Finset.range (min ℓ (r - k * ℓ)), F (k * ℓ + j) := by
  intro B
  induction B with
  | zero =>
      intro r hr
      rw [Nat.mul_zero] at hr
      have hr0 : r = 0 := Nat.le_zero.mp hr
      subst hr0
      simp
  | succ B ih =>
      intro r hr
      rw [Finset.sum_range_succ]
      by_cases hcase : r ≤ ℓ * B
      · rw [← ih r hcase]
        have h1 : r - B * ℓ = 0 :=
          Nat.sub_eq_zero_of_le (by rw [Nat.mul_comm]; exact hcase)
        rw [h1]
        simp
      · push_neg at hcase
        have hup : r ≤ ℓ * B + ℓ := by rw [Nat.mul_succ] at hr; exact hr
        have hsplit : ℓ * B + (r - ℓ * B) = r := Nat.add_sub_cancel' hcase.le
        have hLHS : ∑ i ∈ Finset.range r, F i
            = (∑ i ∈ Finset.range (ℓ * B), F i)
              + ∑ j ∈ Finset.range (r - ℓ * B), F (ℓ * B + j) := by
          conv_lhs => rw [← hsplit]
          exact Finset.sum_range_add F (ℓ * B) (r - ℓ * B)
        rw [hLHS, ih (ℓ * B) le_rfl]
        congr 1
        · apply Finset.sum_congr rfl
          intro k hk
          have hk' := Finset.mem_range.mp hk
          have hmul : ℓ * k + ℓ ≤ ℓ * B := by
            rw [← Nat.mul_succ]
            exact Nat.mul_le_mul_left ℓ hk'
          have hcomm : k * ℓ = ℓ * k := Nat.mul_comm k ℓ
          have hmin1 : min ℓ (ℓ * B - k * ℓ) = ℓ := by rw [hcomm]; omega
          have hmin2 : min ℓ (r - k * ℓ) = ℓ := by rw [hcomm]; omega
          rw [hmin1, hmin2]
        · have hmin3 : min ℓ (r - B * ℓ) = r - ℓ * B := by
            rw [Nat.mul_comm B ℓ]; omega
          rw [hmin3, Nat.mul_comm B ℓ]

private lemma sum_range_parity_split {M : Type*} [AddCommMonoid M] (G : ℕ → M)
    (B : ℕ) :
    ∑ k ∈ Finset.range B, G k
      = (∑ t ∈ Finset.range ((B + 1) / 2), G (2 * t))
        + ∑ t ∈ Finset.range (B / 2), G (2 * t + 1) := by
  induction B with
  | zero => simp
  | succ B ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd B with hev | hodd
      · obtain ⟨m, hm⟩ := hev
        subst hm
        have h1 : (m + m + 1) / 2 = m := by omega
        have h2 : (m + m) / 2 = m := by omega
        have h3 : (m + m + 1 + 1) / 2 = m + 1 := by omega
        rw [h1, h2, h3, Finset.sum_range_succ]
        have h4 : 2 * m = m + m := two_mul m
        rw [h4]
        abel
      · obtain ⟨m, hm⟩ := hodd
        subst hm
        have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
        have h2 : (2 * m + 1) / 2 = m := by omega
        have h3 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
        rw [h1, h2, h3, Finset.sum_range_succ (fun t => G (2 * t + 1)) m]
        abel

private lemma le_mul_blocks (r : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    r ≤ ℓ * ((r + ℓ - 1) / ℓ) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · simp [hr]
  · have h1 : r + ℓ - 1 = (r - 1) + ℓ := by omega
    rw [h1, Nat.add_div_right _ hℓ, Nat.mul_add, Nat.mul_one]
    have h2 := Nat.div_add_mod (r - 1) ℓ
    have h3 : (r - 1) % ℓ < ℓ := Nat.mod_lt _ hℓ
    generalize hA : ℓ * ((r - 1) / ℓ) = A at h2 ⊢
    generalize hM : (r - 1) % ℓ = M at h2 h3
    omega

private lemma blocks_le {r ℓ : ℕ} (hr : 1 ≤ r) (hℓ : 1 ≤ ℓ) :
    (r + ℓ - 1) / ℓ ≤ r := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  have hL : (1 + a) + (1 + b) - 1 = 1 + a + b := by omega
  have hexp : (1 + a) * (1 + b) = (1 + a + b) + a * b := by ring
  have h : (1 + a) + (1 + b) - 1 ≤ (1 + a) * (1 + b) := by
    rw [hL, hexp]; exact Nat.le_add_right _ _
  calc ((1 + a) + (1 + b) - 1) / (1 + b)
      ≤ ((1 + a) * (1 + b)) / (1 + b) := Nat.div_le_div_right h
    _ = 1 + a := Nat.mul_div_cancel (1 + a) (by omega)

/-! ### Integrability helper -/

private lemma integrable_exp_of_bound {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ᵐ y ∂Erdos1002.gaussMeasure, |f y| ≤ K) :
    Integrable (fun y => Real.exp (f y)) Erdos1002.gaussMeasure := by
  refine Integrable.of_bound hf.exp.aestronglyMeasurable (Real.exp K) ?_
  filter_upwards [hK] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hy)

/-! ### The per-block moment-generating bound -/

private lemma integral_blockObs_le
    {C₀ : ℝ}
    (hblk : ∀ u : ℝ, 0 ≤ u → ∀ t ℓ : ℕ,
      ∫ x, (∑ i ∈ Finset.range ℓ,
            (capLog u (Erdos1002.gaussOrbit (t + i) x)
              - ∫ y, capLog u y ∂Erdos1002.gaussMeasure)) ^ 2
          ∂Erdos1002.gaussMeasure ≤ C₀ * ℓ)
    {u : ℝ} (hu : 0 ≤ u) (W : ℕ) {s : ℝ} {n : ℕ}
    (hsmall : |s| * ((n : ℝ) * (u + 3)) ≤ 1 / 2) :
    ∫ y, blockObs u W s n y ∂Erdos1002.gaussMeasure
      ≤ Real.exp (s * ((n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
          + 2 * s ^ 2 * (C₀ * n)
          + |s| * ((n : ℝ)
              * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)))) := by
  have hm0 := integral_capLog_nonpos u hu
  have hm1 := neg_exp_le_integral_capLog u hu
  have hmabs : |∫ x, capLog u x ∂Erdos1002.gaussMeasure| ≤ 1 := by
    rw [abs_le]
    refine ⟨?_, by linarith⟩
    have hle1 : Real.exp (-u / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have haeorb : ∀ᵐ y ∂Erdos1002.gaussMeasure, ∀ j : ℕ,
      Erdos1002.gaussOrbit j y ∈ Ioo (0 : ℝ) 1
        ∧ Irrational (Erdos1002.gaussOrbit j y) := by
    filter_upwards [ae_gauss_unit_irrational] with y hy j
    exact ⟨gaussIter_mem_Ioo hy.1 hy.2 j, gaussIter_irrational hy.2 j⟩
  have hmeasCap : ∀ j : ℕ,
      Measurable (fun y => capLog u (Erdos1002.gaussOrbit j y)) :=
    fun j => (measurable_capLog u).comp (Erdos1002.measurable_gaussOrbit j)
  have hmeasCS : Measurable
      (fun y => ∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)) :=
    Finset.measurable_sum _ (fun j _ => hmeasCap j)
  have hintCap : ∀ j : ℕ,
      Integrable (fun y => capLog u (Erdos1002.gaussOrbit j y))
        Erdos1002.gaussMeasure := by
    intro j
    refine Integrable.of_bound (hmeasCap j).aestronglyMeasurable
      (u + lyapunov) ?_
    filter_upwards [haeorb] with y hy
    rw [Real.norm_eq_abs]
    exact abs_capLog_le hu (hy j).1.2.le
  have hintCS : ∫ y, (∑ j ∈ Finset.range n,
        capLog u (Erdos1002.gaussOrbit j y)) ∂Erdos1002.gaussMeasure
      = (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure := by
    rw [integral_finset_sum _ (fun j _ => hintCap j)]
    have hterm : ∀ j ∈ Finset.range n,
        ∫ y, capLog u (Erdos1002.gaussOrbit j y) ∂Erdos1002.gaussMeasure
          = ∫ x, capLog u x ∂Erdos1002.gaussMeasure := fun j _ =>
      integral_comp_gaussOrbit j (capLog u)
        (measurable_capLog u).aestronglyMeasurable
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  -- a.e. bound on the centered block sum
  have haeCSbd : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      |∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)|
        ≤ (n : ℝ) * (u + lyapunov) := by
    filter_upwards [haeorb] with y hy
    calc |∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)|
        ≤ ∑ j ∈ Finset.range n, |capLog u (Erdos1002.gaussOrbit j y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.range n).card • (u + lyapunov) :=
          Finset.sum_le_card_nsmul _ _ _
            (fun j _ => abs_capLog_le hu (hy j).1.2.le)
      _ = (n : ℝ) * (u + lyapunov) := by rw [Finset.card_range, nsmul_eq_mul]
  have haeGbd : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      |(∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure|
        ≤ (n : ℝ) * (u + 3) := by
    filter_upwards [haeCSbd] with y hy
    have hlam := lyapunov_lt_two
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc |(∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure|
        ≤ |∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)|
            + |(n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure| :=
          abs_sub _ _
      _ ≤ (n : ℝ) * (u + lyapunov) + (n : ℝ) * 1 := by
          have habs2 : |(n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure|
              = (n : ℝ) * |∫ x, capLog u x ∂Erdos1002.gaussMeasure| := by
            rw [abs_mul, abs_of_nonneg hn0]
          rw [habs2]
          have := mul_le_mul_of_nonneg_left hmabs hn0
          linarith
      _ ≤ (n : ℝ) * (u + 3) := by nlinarith
  -- pointwise: blockObs ≤ e^{|s| n δ} · e^{s · capSum}
  have hpt1 : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      blockObs u W s n y
        ≤ Real.exp (|s| * ((n : ℝ)
              * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))))
            * Real.exp (s * ∑ j ∈ Finset.range n,
                capLog u (Erdos1002.gaussOrbit j y)) := by
    filter_upwards [haeorb] with y hy
    have herr : |(∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y))
        - ∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)|
        ≤ (n : ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) := by
      rw [← Finset.sum_sub_distrib]
      calc |∑ j ∈ Finset.range n, (hatSite u W (Erdos1002.gaussOrbit j y)
            - capLog u (Erdos1002.gaussOrbit j y))|
          ≤ ∑ j ∈ Finset.range n, |hatSite u W (Erdos1002.gaussOrbit j y)
              - capLog u (Erdos1002.gaussOrbit j y)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ (Finset.range n).card
              • (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) :=
            Finset.sum_le_card_nsmul _ _ _
              (fun j _ => abs_hatSite_sub_capLog_le u W (hy j).1 (hy j).2)
        _ = (n : ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) := by
            rw [Finset.card_range, nsmul_eq_mul]
    unfold blockObs
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : s * (∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y))
        - s * ∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)
        ≤ |s| * ((n : ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))) := by
      calc s * (∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y))
            - s * ∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)
          = s * ((∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y))
              - ∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)) := by
            ring
        _ ≤ |s * ((∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y))
              - ∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))| :=
            le_abs_self _
        _ = |s| * |(∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y))
              - ∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y)| :=
            abs_mul _ _
        _ ≤ |s| * ((n : ℝ)
              * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))) :=
            mul_le_mul_of_nonneg_left herr (abs_nonneg s)
    linarith
  -- integrability of all players
  have hintBlock : Integrable (blockObs u W s n) Erdos1002.gaussMeasure := by
    have hmeasIn : Measurable (fun y : ℝ =>
        s * ∑ j ∈ Finset.range n, hatSite u W (Erdos1002.gaussOrbit j y)) :=
      (Finset.measurable_sum _ (fun j _ =>
        (measurable_hatSite u W).comp (Erdos1002.measurable_gaussOrbit j))).const_mul s
    exact integrable_exp_of_bound hmeasIn (ae_of_all _ (fun y => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_hatBlock_le hu W n y) (abs_nonneg s)))
  have hintExpCS : Integrable
      (fun y => Real.exp (s * ∑ j ∈ Finset.range n,
        capLog u (Erdos1002.gaussOrbit j y))) Erdos1002.gaussMeasure := by
    refine integrable_exp_of_bound (hmeasCS.const_mul s)
      (K := |s| * ((n : ℝ) * (u + lyapunov))) ?_
    filter_upwards [haeCSbd] with y hy
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg s)
  have hintG : Integrable (fun y =>
      (∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
      Erdos1002.gaussMeasure :=
    (integrable_finset_sum _ (fun j _ => hintCap j)).sub (integrable_const _)
  have hmeasG : Measurable (fun y =>
      (∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) :=
    hmeasCS.sub measurable_const
  have hintG2 : Integrable (fun y =>
      ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2)
      Erdos1002.gaussMeasure := by
    refine Integrable.of_bound (hmeasG.pow_const 2).aestronglyMeasurable
      (((n : ℝ) * (u + 3)) ^ 2) ?_
    filter_upwards [haeGbd] with y hy
    rw [Real.norm_eq_abs, abs_pow]
    have h0 : (0 : ℝ) ≤ |(∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure| := abs_nonneg _
    exact pow_le_pow_left₀ h0 hy 2
  have hintExpG : Integrable (fun y =>
      Real.exp (s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)))
      Erdos1002.gaussMeasure := by
    refine integrable_exp_of_bound (hmeasG.const_mul s) (K := 1 / 2) ?_
    filter_upwards [haeGbd] with y hy
    rw [abs_mul]
    calc |s| * |(∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure|
        ≤ |s| * ((n : ℝ) * (u + 3)) :=
          mul_le_mul_of_nonneg_left hy (abs_nonneg s)
      _ ≤ 1 / 2 := hsmall
  -- centering has mean zero
  have hEG : ∫ y, ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
      - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
      ∂Erdos1002.gaussMeasure = 0 := by
    rw [integral_sub (integrable_finset_sum _ (fun j _ => hintCap j))
      (integrable_const _), hintCS, integral_const]
    simp
  -- second moment
  have hEG2 : ∫ y, ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
      - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2
      ∂Erdos1002.gaussMeasure ≤ C₀ * n := by
    have h := hblk u hu 0 n
    simp only [zero_add] at h
    have hcong : ∀ y : ℝ,
        (∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure
        = ∑ i ∈ Finset.range n, (capLog u (Erdos1002.gaussOrbit i y)
            - ∫ x, capLog u x ∂Erdos1002.gaussMeasure) := by
      intro y
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    calc ∫ y, ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2
          ∂Erdos1002.gaussMeasure
        = ∫ y, (∑ i ∈ Finset.range n, (capLog u (Erdos1002.gaussOrbit i y)
            - ∫ x, capLog u x ∂Erdos1002.gaussMeasure)) ^ 2
            ∂Erdos1002.gaussMeasure := by
          apply integral_congr_ae
          exact ae_of_all _ (fun y => congrArg (· ^ 2) (hcong y))
      _ ≤ C₀ * n := h
  -- Taylor bound, pointwise then integrated
  have hptT : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      Real.exp (s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
      ≤ 1 + s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
        + 2 * s ^ 2 * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2 := by
    filter_upwards [haeGbd] with y hy
    have hx : s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ≤ 1 / 2 := by
      calc s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
            - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
          ≤ |s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
            - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)| := le_abs_self _
        _ = |s| * |(∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
            - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure| := abs_mul _ _
        _ ≤ |s| * ((n : ℝ) * (u + 3)) :=
            mul_le_mul_of_nonneg_left hy (abs_nonneg s)
        _ ≤ 1 / 2 := hsmall
    calc Real.exp (s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
        ≤ 1 + s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
            - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
          + 2 * (s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
            - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)) ^ 2 :=
          exp_taylor_le hx
      _ = 1 + s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
            - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
          + 2 * s ^ 2 * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
            - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2 := by ring
  have hintRHS : Integrable (fun y =>
      1 + s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
      + 2 * s ^ 2 * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2)
      Erdos1002.gaussMeasure :=
    (((integrable_const 1).add (hintG.const_mul s)).add (hintG2.const_mul (2 * s ^ 2)))
  have hint_a : Integrable (fun y =>
      1 + s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
      Erdos1002.gaussMeasure :=
    (integrable_const 1).add (hintG.const_mul s)
  have hint_b : Integrable (fun y =>
      2 * s ^ 2 * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2)
      Erdos1002.gaussMeasure :=
    hintG2.const_mul (2 * s ^ 2)
  have hint_s : Integrable (fun y =>
      s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
      Erdos1002.gaussMeasure :=
    hintG.const_mul s
  have hTaylorInt : ∫ y,
      Real.exp (s * ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
        - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
      ∂Erdos1002.gaussMeasure ≤ Real.exp (2 * s ^ 2 * (C₀ * n)) := by
    have step := integral_mono_ae hintExpG hintRHS hptT
    rw [integral_add hint_a hint_b,
      integral_add (integrable_const 1) hint_s,
      integral_const_mul, integral_const_mul, hEG, integral_const] at step
    simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at step
    have h2 : 2 * s ^ 2 * ∫ y,
        ((∑ j ∈ Finset.range n, capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure) ^ 2
        ∂Erdos1002.gaussMeasure ≤ 2 * s ^ 2 * (C₀ * n) :=
      mul_le_mul_of_nonneg_left hEG2 (by positivity)
    have h3 := Real.add_one_le_exp (2 * s ^ 2 * (C₀ * n))
    linarith
  -- assemble
  have step1 : ∫ y, blockObs u W s n y ∂Erdos1002.gaussMeasure
      ≤ Real.exp (|s| * ((n : ℝ)
            * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))))
          * ∫ y, Real.exp (s * ∑ j ∈ Finset.range n,
              capLog u (Erdos1002.gaussOrbit j y)) ∂Erdos1002.gaussMeasure := by
    have := integral_mono_ae hintBlock (hintExpCS.const_mul _) hpt1
    rwa [integral_const_mul] at this
  have hfactor : ∫ y, Real.exp (s * ∑ j ∈ Finset.range n,
        capLog u (Erdos1002.gaussOrbit j y)) ∂Erdos1002.gaussMeasure
      = Real.exp (s * ((n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
        * ∫ y, Real.exp (s * ((∑ j ∈ Finset.range n,
            capLog u (Erdos1002.gaussOrbit j y))
          - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
          ∂Erdos1002.gaussMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro y
    simp only []
    rw [← Real.exp_add]
    congr 1
    ring
  calc ∫ y, blockObs u W s n y ∂Erdos1002.gaussMeasure
      ≤ Real.exp (|s| * ((n : ℝ)
            * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))))
          * ∫ y, Real.exp (s * ∑ j ∈ Finset.range n,
              capLog u (Erdos1002.gaussOrbit j y)) ∂Erdos1002.gaussMeasure := step1
    _ = Real.exp (|s| * ((n : ℝ)
            * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))))
          * (Real.exp (s * ((n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
            * ∫ y, Real.exp (s * ((∑ j ∈ Finset.range n,
                capLog u (Erdos1002.gaussOrbit j y))
              - (n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
              ∂Erdos1002.gaussMeasure) := by rw [hfactor]
    _ ≤ Real.exp (|s| * ((n : ℝ)
            * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W))))
          * (Real.exp (s * ((n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure))
            * Real.exp (2 * s ^ 2 * (C₀ * n))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hTaylorInt (Real.exp_nonneg _)
    _ = Real.exp (s * ((n : ℝ) * ∫ x, capLog u x ∂Erdos1002.gaussMeasure)
          + 2 * s ^ 2 * (C₀ * n)
          + |s| * ((n : ℝ)
              * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-! ### The parity-class bound: decoupling plus the per-block mgf -/

private lemma integral_exp_class_le
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hblk : ∀ u : ℝ, 0 ≤ u → ∀ t ℓ : ℕ,
      ∫ x, (∑ i ∈ Finset.range ℓ,
            (capLog u (Erdos1002.gaussOrbit (t + i) x)
              - ∫ y, capLog u y ∂Erdos1002.gaussMeasure)) ^ 2
          ∂Erdos1002.gaussMeasure ≤ C₀ * ℓ)
    {u : ℝ} (hu : 0 ≤ u) {r W : ℕ} (hW : 1 ≤ W)
    (hmix : (r : ℝ) * (24 * (527 / 540 : ℝ) ^ W) ≤ 1)
    (hwin : (r : ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) ≤ 1)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσsmall : σ * (4 * W * (u + 3)) ≤ 1 / 2)
    {s : ℝ} (hs : |s| = 2 * σ)
    {Dr : ℝ}
    (hDr : ∀ L : ℝ, 0 ≤ L → L ≤ (r : ℝ) →
      s * ((∫ x, capLog u x ∂Erdos1002.gaussMeasure) * L) ≤ Dr)
    {c : ℕ} (hc : c ≤ r) {kf : ℕ → ℕ} (hkf : ∀ t, kf t + 2 ≤ kf (t + 1))
    (hL : (∑ t ∈ Finset.range c,
        ((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ)) ≤ (r : ℝ)) :
    ∫ α, Real.exp (s * ∑ t ∈ Finset.range c,
          blockSum u W (2 * W) r (kf t) α) ∂Erdos1002.gaussMeasure
      ≤ Real.exp (2 + 8 * C₀ * σ ^ 2 * r + Dr) := by
  have hWR : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  set bl : List (ℕ × (ℝ → ℝ)) := (List.range c).map
    (fun t => (kf t * (2 * W),
      blockObs u W s (min (2 * W) (r - kf t * (2 * W))))) with hbl
  have hmemf : ∀ p ∈ bl, ∃ t, p = (kf t * (2 * W),
      blockObs u W s (min (2 * W) (r - kf t * (2 * W)))) := by
    intro p hp
    rw [hbl, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    exact ⟨t, rfl⟩
  have hmeas : ∀ p ∈ bl, Measurable p.2 := by
    intro p hp
    obtain ⟨t, rfl⟩ := hmemf p hp
    exact measurable_blockObs _ _ _ _
  have h0 : ∀ p ∈ bl, ∀ x, 0 ≤ p.2 x := by
    intro p hp x
    obtain ⟨t, rfl⟩ := hmemf p hp
    exact (blockObs_pos _ _ _ _ _).le
  have hBd : (1 : ℝ) ≤ Real.exp (2 * σ * (2 * (W : ℝ) * (u + 2))) := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have h1 : (0 : ℝ) ≤ 2 * (W : ℝ) * (u + 2) := by nlinarith
    nlinarith
  have hbd : ∀ p ∈ bl, ∀ x,
      p.2 x ≤ Real.exp (2 * σ * (2 * (W : ℝ) * (u + 2))) := by
    intro p hp x
    obtain ⟨t, rfl⟩ := hmemf p hp
    have h := blockObs_le hu W s
      (n := min (2 * W) (r - kf t * (2 * W))) (Nat.min_le_left _ _) x
    rwa [hs] at h
  have hdet : ∀ p ∈ bl, DigitDetermined (3 * W) p.2 := by
    intro p hp
    obtain ⟨t, rfl⟩ := hmemf p hp
    exact blockObs_digitDetermined u W s (Nat.min_le_left _ _)
  have hsep : List.IsChain
      (fun p q : ℕ × (ℝ → ℝ) => p.1 + 3 * W + W ≤ q.1) bl := by
    rw [hbl, List.isChain_map, List.isChain_range]
    intro t _
    show kf t * (2 * W) + 3 * W + W ≤ kf (t + 1) * (2 * W)
    have h2 := hkf t
    have h3 : (kf t + 2) * (2 * W) ≤ kf (t + 1) * (2 * W) :=
      Nat.mul_le_mul_right (2 * W) h2
    have h4 : (kf t + 2) * (2 * W) = kf t * (2 * W) + 4 * W := by ring
    omega
  have hdec := separated_product_decouple (3 * W) W bl hmeas h0 hBd hbd hdet hsep
  have hpoint : ∀ α : ℝ,
      (bl.map (fun p => p.2 (Erdos1002.gaussOrbit p.1 α))).prod
        = Real.exp (s * ∑ t ∈ Finset.range c,
            blockSum u W (2 * W) r (kf t) α) := by
    intro α
    rw [hbl, List.map_map, list_range_map_prod, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro t _
    exact blockObs_orbit u W (2 * W) r s (kf t) α
  have hlenbl : bl.length = c := by rw [hbl]; simp
  have hRHS : (bl.map (fun p => ∫ x, p.2 x ∂Erdos1002.gaussMeasure)).prod
      = ∏ t ∈ Finset.range c, ∫ x, blockObs u W s
          (min (2 * W) (r - kf t * (2 * W))) x ∂Erdos1002.gaussMeasure := by
    rw [hbl, List.map_map, list_range_map_prod]
    rfl
  have hfac : ∀ t ∈ Finset.range c,
      ∫ x, blockObs u W s (min (2 * W) (r - kf t * (2 * W))) x
          ∂Erdos1002.gaussMeasure
        ≤ Real.exp ((s * ∫ x, capLog u x ∂Erdos1002.gaussMeasure
            + 2 * s ^ 2 * C₀
            + |s| * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)))
          * ((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ)) := by
    intro t _
    have hnle : ((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ) ≤ 2 * (W : ℝ) := by
      have h := Nat.min_le_left (2 * W) (r - kf t * (2 * W))
      exact_mod_cast h
    have hsm : |s| * (((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ) * (u + 3))
        ≤ 1 / 2 := by
      rw [hs]
      calc 2 * σ * (((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ) * (u + 3))
          ≤ 2 * σ * (2 * (W : ℝ) * (u + 3)) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact mul_le_mul_of_nonneg_right hnle (by linarith)
        _ = σ * (4 * (W : ℝ) * (u + 3)) := by ring
        _ ≤ 1 / 2 := hσsmall
    refine le_trans (integral_blockObs_le hblk hu W hsm) (le_of_eq ?_)
    congr 1
    ring
  have hprodle : (bl.map (fun p => ∫ x, p.2 x ∂Erdos1002.gaussMeasure)).prod
      ≤ Real.exp ((s * ∫ x, capLog u x ∂Erdos1002.gaussMeasure
          + 2 * s ^ 2 * C₀
          + |s| * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)))
        * ∑ t ∈ Finset.range c,
            ((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ)) := by
    rw [hRHS, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro t _
      exact integral_nonneg (fun x => (blockObs_pos _ _ _ _ _).le)
    · exact hfac
  have hL0 : 0 ≤ ∑ t ∈ Finset.range c,
      ((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun t _ => Nat.cast_nonneg _)
  have hδ0 : (0 : ℝ) ≤ Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W) := by
    positivity
  have hexpo : (s * ∫ x, capLog u x ∂Erdos1002.gaussMeasure
      + 2 * s ^ 2 * C₀
      + |s| * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)))
      * (∑ t ∈ Finset.range c, ((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ))
      ≤ Dr + 8 * C₀ * σ ^ 2 * r + 1 := by
    set L := ∑ t ∈ Finset.range c,
      ((min (2 * W) (r - kf t * (2 * W)) : ℕ) : ℝ) with hLdef
    have e1 : s * ((∫ x, capLog u x ∂Erdos1002.gaussMeasure) * L) ≤ Dr :=
      hDr L hL0 hL
    have hs2 : s ^ 2 = 4 * σ ^ 2 := by rw [← sq_abs, hs]; ring
    have e2 : 2 * s ^ 2 * C₀ * L ≤ 8 * C₀ * σ ^ 2 * r := by
      rw [hs2]
      have hco : (0 : ℝ) ≤ 8 * σ ^ 2 * C₀ :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg σ)) hC₀.le
      nlinarith [mul_le_mul_of_nonneg_left hL hco]
    have e3 : |s| * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) * L ≤ 1 := by
      rw [hs]
      have h12 : (12 : ℝ) ≤ 4 * (W : ℝ) * (u + 3) := by nlinarith
      have hσ12 : σ * 12 ≤ σ * (4 * (W : ℝ) * (u + 3)) :=
        mul_le_mul_of_nonneg_left h12 hσ
      have hσhalf : σ ≤ 1 / 2 := by
        have := hσsmall
        nlinarith
      have h5 : (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) * L
          ≤ (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) * r :=
        mul_le_mul_of_nonneg_left hL hδ0
      nlinarith [hwin]
    nlinarith [e1, e2, e3]
  have hclen : ((1 : ℝ) + 24 * (527 / 540 : ℝ) ^ W) ^ bl.length ≤ Real.exp 1 := by
    rw [hlenbl]
    have hε0 : (0 : ℝ) ≤ 24 * (527 / 540 : ℝ) ^ W := by positivity
    have h1 : (1 + 24 * (527 / 540 : ℝ) ^ W)
        ≤ Real.exp (24 * (527 / 540 : ℝ) ^ W) := by
      have := Real.add_one_le_exp (24 * (527 / 540 : ℝ) ^ W); linarith
    have h2 : ((1 : ℝ) + 24 * (527 / 540 : ℝ) ^ W) ^ c
        ≤ Real.exp (24 * (527 / 540 : ℝ) ^ W) ^ c :=
      pow_le_pow_left₀ (by linarith) h1 c
    rw [← Real.exp_nat_mul] at h2
    have h3 : (c : ℝ) * (24 * (527 / 540 : ℝ) ^ W)
        ≤ (r : ℝ) * (24 * (527 / 540 : ℝ) ^ W) := by
      apply mul_le_mul_of_nonneg_right _ hε0
      exact_mod_cast hc
    exact h2.trans (Real.exp_le_exp.mpr (by linarith [hmix]))
  calc ∫ α, Real.exp (s * ∑ t ∈ Finset.range c,
        blockSum u W (2 * W) r (kf t) α) ∂Erdos1002.gaussMeasure
      = ∫ α, (bl.map (fun p => p.2 (Erdos1002.gaussOrbit p.1 α))).prod
          ∂Erdos1002.gaussMeasure := by
        apply integral_congr_ae
        exact ae_of_all _ (fun α => (hpoint α).symm)
    _ ≤ (1 + 24 * (527 / 540 : ℝ) ^ W) ^ bl.length
          * (bl.map (fun p => ∫ x, p.2 x ∂Erdos1002.gaussMeasure)).prod := hdec
    _ ≤ Real.exp 1 * Real.exp (Dr + 8 * C₀ * σ ^ 2 * r + 1) := by
        apply mul_le_mul hclen (hprodle.trans (Real.exp_le_exp.mpr hexpo)) _
          (Real.exp_nonneg _)
        rw [hRHS]
        exact Finset.prod_nonneg
          (fun t _ => integral_nonneg (fun x => (blockObs_pos _ _ _ _ _).le))
    _ = Real.exp (2 + 8 * C₀ * σ ^ 2 * r + Dr) := by
        rw [← Real.exp_add]
        congr 1
        ring

set_option maxHeartbeats 1600000 in
/-- **The exponential-moment bound for the windowed capped sum**, both
signs.  In the regime `σ·4W(u+3) ≤ 1/2` (which forces `σ ≤ 1/24`), with the
mixing smallness `24ρ₀^W r ≤ 1` and the windowing smallness
`r·e^{u+λ}·2·(1/2)^W ≤ 1` as hypotheses:

`E[e^{σ·hatSum}] ≤ exp(C₁(1 + σ²r))` and
`E[e^{−σ·hatSum}] ≤ exp(C₁(1 + σ²r + σr e^{−u/2}))`. -/
theorem exists_hatSum_mgf :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ u : ℝ, 0 ≤ u → ∀ r W : ℕ, 1 ≤ r → 1 ≤ W →
      (r : ℝ) * (24 * (527 / 540 : ℝ) ^ W) ≤ 1 →
      (r : ℝ) * (Real.exp (u + lyapunov) * (2 * (1 / 2 : ℝ) ^ W)) ≤ 1 →
      ∀ σ : ℝ, 0 ≤ σ → σ * (4 * W * (u + 3)) ≤ 1 / 2 →
      (∫ α, Real.exp (σ * hatSum u W r α) ∂Erdos1002.gaussMeasure
          ≤ Real.exp (C₁ * (1 + σ ^ 2 * r)))
      ∧ (∫ α, Real.exp (-(σ * hatSum u W r α)) ∂Erdos1002.gaussMeasure
          ≤ Real.exp (C₁ * (1 + σ ^ 2 * r + σ * r * Real.exp (-u / 2)))) := by
  obtain ⟨C₀, hC₀pos, hblk⟩ := exists_block_sq_bound
  refine ⟨8 * C₀ + 2, by linarith, ?_⟩
  intro u hu r W hr hW hmix hwin σ hσ hσsmall
  have hm0 := integral_capLog_nonpos u hu
  have hm1 := neg_exp_le_integral_capLog u hu
  have hlam0 := lyapunov_pos'
  have hℓpos : 0 < 2 * W := by omega
  set B := (r + 2 * W - 1) / (2 * W) with hBdef
  have hrB : r ≤ 2 * W * B := le_mul_blocks r hℓpos
  have hBr : B ≤ r := blocks_le hr (by omega)
  -- pointwise block and parity decompositions
  have hsplit : ∀ α : ℝ, hatSum u W r α
      = ∑ k ∈ Finset.range B, blockSum u W (2 * W) r k α := by
    intro α
    unfold hatSum blockSum
    exact sum_block_split (fun i => hatSite u W (Erdos1002.gaussOrbit i α))
      (2 * W) B r hrB
  have hparity : ∀ α : ℝ,
      (∑ k ∈ Finset.range B, blockSum u W (2 * W) r k α)
        = (∑ t ∈ Finset.range ((B + 1) / 2), blockSum u W (2 * W) r (2 * t) α)
          + ∑ t ∈ Finset.range (B / 2), blockSum u W (2 * W) r (2 * t + 1) α :=
    fun α => sum_range_parity_split (fun k => blockSum u W (2 * W) r k α) B
  -- length bookkeeping
  have hlensum : (∑ k ∈ Finset.range B, min (2 * W) (r - k * (2 * W))) = r := by
    have h := sum_block_split (fun _ => (1 : ℕ)) (2 * W) B r hrB
    simpa using h.symm
  have hpar2 : (∑ k ∈ Finset.range B, min (2 * W) (r - k * (2 * W)))
      = (∑ t ∈ Finset.range ((B + 1) / 2), min (2 * W) (r - 2 * t * (2 * W)))
        + ∑ t ∈ Finset.range (B / 2), min (2 * W) (r - (2 * t + 1) * (2 * W)) :=
    sum_range_parity_split (fun k => min (2 * W) (r - k * (2 * W))) B
  rw [hlensum] at hpar2
  have hS0 : (∑ t ∈ Finset.range ((B + 1) / 2),
      min (2 * W) (r - 2 * t * (2 * W))) ≤ r := by omega
  have hS1 : (∑ t ∈ Finset.range (B / 2),
      min (2 * W) (r - (2 * t + 1) * (2 * W))) ≤ r := by omega
  have hL0R : (∑ t ∈ Finset.range ((B + 1) / 2),
      ((min (2 * W) (r - 2 * t * (2 * W)) : ℕ) : ℝ)) ≤ (r : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hS0
  have hL1R : (∑ t ∈ Finset.range (B / 2),
      ((min (2 * W) (r - (2 * t + 1) * (2 * W)) : ℕ) : ℝ)) ≤ (r : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hS1
  have hc0 : (B + 1) / 2 ≤ r := by omega
  have hc1 : B / 2 ≤ r := by omega
  -- global bounds and measurability
  have habsHS : ∀ α : ℝ, |hatSum u W r α| ≤ (r : ℝ) * (u + lyapunov) := by
    intro α
    unfold hatSum
    calc |∑ i ∈ Finset.range r, hatSite u W (Erdos1002.gaussOrbit i α)|
        ≤ ∑ i ∈ Finset.range r, |hatSite u W (Erdos1002.gaussOrbit i α)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.range r).card • (u + lyapunov) :=
          Finset.sum_le_card_nsmul _ _ _ (fun i _ => abs_hatSite_le hu W _)
      _ = (r : ℝ) * (u + lyapunov) := by rw [Finset.card_range, nsmul_eq_mul]
  have habsE : ∀ α : ℝ,
      |∑ t ∈ Finset.range ((B + 1) / 2), blockSum u W (2 * W) r (2 * t) α|
        ≤ (r : ℝ) * (u + lyapunov) := by
    intro α
    calc |∑ t ∈ Finset.range ((B + 1) / 2), blockSum u W (2 * W) r (2 * t) α|
        ≤ ∑ t ∈ Finset.range ((B + 1) / 2), |blockSum u W (2 * W) r (2 * t) α| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range ((B + 1) / 2),
            ((min (2 * W) (r - 2 * t * (2 * W)) : ℕ) : ℝ) * (u + lyapunov) :=
          Finset.sum_le_sum (fun t _ => abs_blockSum_le hu W (2 * W) r (2 * t) α)
      _ = (∑ t ∈ Finset.range ((B + 1) / 2),
            ((min (2 * W) (r - 2 * t * (2 * W)) : ℕ) : ℝ)) * (u + lyapunov) := by
          rw [← Finset.sum_mul]
      _ ≤ (r : ℝ) * (u + lyapunov) :=
          mul_le_mul_of_nonneg_right hL0R (by linarith)
  have habsO : ∀ α : ℝ,
      |∑ t ∈ Finset.range (B / 2), blockSum u W (2 * W) r (2 * t + 1) α|
        ≤ (r : ℝ) * (u + lyapunov) := by
    intro α
    calc |∑ t ∈ Finset.range (B / 2), blockSum u W (2 * W) r (2 * t + 1) α|
        ≤ ∑ t ∈ Finset.range (B / 2), |blockSum u W (2 * W) r (2 * t + 1) α| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range (B / 2),
            ((min (2 * W) (r - (2 * t + 1) * (2 * W)) : ℕ) : ℝ) * (u + lyapunov) :=
          Finset.sum_le_sum (fun t _ => abs_blockSum_le hu W (2 * W) r (2 * t + 1) α)
      _ = (∑ t ∈ Finset.range (B / 2),
            ((min (2 * W) (r - (2 * t + 1) * (2 * W)) : ℕ) : ℝ)) * (u + lyapunov) := by
          rw [← Finset.sum_mul]
      _ ≤ (r : ℝ) * (u + lyapunov) :=
          mul_le_mul_of_nonneg_right hL1R (by linarith)
  have hmeasBS : ∀ k : ℕ, Measurable (fun α => blockSum u W (2 * W) r k α) := by
    intro k
    unfold blockSum
    exact Finset.measurable_sum _ (fun j _ =>
      (measurable_hatSite u W).comp (Erdos1002.measurable_gaussOrbit _))
  have hmeasE : Measurable (fun α : ℝ => ∑ t ∈ Finset.range ((B + 1) / 2),
      blockSum u W (2 * W) r (2 * t) α) :=
    Finset.measurable_sum _ (fun t _ => hmeasBS (2 * t))
  have hmeasO : Measurable (fun α : ℝ => ∑ t ∈ Finset.range (B / 2),
      blockSum u W (2 * W) r (2 * t + 1) α) :=
    Finset.measurable_sum _ (fun t _ => hmeasBS (2 * t + 1))
  -- the one-signed master bound
  have main : ∀ s' : ℝ, |s'| = σ → ∀ Dr : ℝ,
      (∀ L : ℝ, 0 ≤ L → L ≤ (r : ℝ) →
        (2 * s') * ((∫ x, capLog u x ∂Erdos1002.gaussMeasure) * L) ≤ Dr) →
      ∫ α, Real.exp (s' * hatSum u W r α) ∂Erdos1002.gaussMeasure
        ≤ Real.exp (2 + 8 * C₀ * σ ^ 2 * r + Dr) := by
    intro s' hs' Dr hDr
    have habs2 : |2 * s'| = 2 * σ := by
      rw [abs_mul, hs', abs_two]
    have hev := integral_exp_class_le (kf := fun t => 2 * t) hC₀pos hblk hu hW
      hmix hwin hσ hσsmall habs2 hDr hc0
      (fun t => by show 2 * t + 2 ≤ 2 * (t + 1); omega) hL0R
    have hod := integral_exp_class_le (kf := fun t => 2 * t + 1) hC₀pos hblk hu hW
      hmix hwin hσ hσsmall habs2 hDr hc1
      (fun t => by show 2 * t + 1 + 2 ≤ 2 * (t + 1) + 1; omega) hL1R
    simp only [] at hev hod
    -- pointwise parity Cauchy–Schwarz
    have hpt : ∀ α : ℝ, Real.exp (s' * hatSum u W r α)
        ≤ (Real.exp (2 * s' * ∑ t ∈ Finset.range ((B + 1) / 2),
              blockSum u W (2 * W) r (2 * t) α)
            + Real.exp (2 * s' * ∑ t ∈ Finset.range (B / 2),
              blockSum u W (2 * W) r (2 * t + 1) α)) / 2 := by
      intro α
      rw [hsplit α, hparity α]
      set a := ∑ t ∈ Finset.range ((B + 1) / 2), blockSum u W (2 * W) r (2 * t) α
      set b := ∑ t ∈ Finset.range (B / 2), blockSum u W (2 * W) r (2 * t + 1) α
      have h1 : Real.exp (s' * (a + b)) = Real.exp (s' * a) * Real.exp (s' * b) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : Real.exp (s' * a) * Real.exp (s' * b)
          ≤ (Real.exp (s' * a) ^ 2 + Real.exp (s' * b) ^ 2) / 2 := by
        nlinarith [sq_nonneg (Real.exp (s' * a) - Real.exp (s' * b))]
      have h3 : Real.exp (s' * a) ^ 2 = Real.exp (2 * s' * a) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have h4 : Real.exp (s' * b) ^ 2 = Real.exp (2 * s' * b) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      rw [h1]
      rw [h3, h4] at h2
      exact h2
    -- integrability
    have hintHS : Integrable (fun α => Real.exp (s' * hatSum u W r α))
        Erdos1002.gaussMeasure := by
      refine integrable_exp_of_bound ((measurable_hatSum u W r).const_mul s')
        (K := |s'| * ((r : ℝ) * (u + lyapunov))) (ae_of_all _ (fun α => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (habsHS α) (abs_nonneg _)
    have hintE : Integrable (fun α => Real.exp (2 * s' *
        ∑ t ∈ Finset.range ((B + 1) / 2), blockSum u W (2 * W) r (2 * t) α))
        Erdos1002.gaussMeasure := by
      refine integrable_exp_of_bound (hmeasE.const_mul (2 * s'))
        (K := |2 * s'| * ((r : ℝ) * (u + lyapunov))) (ae_of_all _ (fun α => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (habsE α) (abs_nonneg _)
    have hintO : Integrable (fun α => Real.exp (2 * s' *
        ∑ t ∈ Finset.range (B / 2), blockSum u W (2 * W) r (2 * t + 1) α))
        Erdos1002.gaussMeasure := by
      refine integrable_exp_of_bound (hmeasO.const_mul (2 * s'))
        (K := |2 * s'| * ((r : ℝ) * (u + lyapunov))) (ae_of_all _ (fun α => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (habsO α) (abs_nonneg _)
    have hintEO : Integrable (fun α =>
        (Real.exp (2 * s' * ∑ t ∈ Finset.range ((B + 1) / 2),
            blockSum u W (2 * W) r (2 * t) α)
          + Real.exp (2 * s' * ∑ t ∈ Finset.range (B / 2),
            blockSum u W (2 * W) r (2 * t + 1) α)) / 2)
        Erdos1002.gaussMeasure := (hintE.add hintO).div_const 2
    have step := integral_mono_ae hintHS hintEO (ae_of_all _ hpt)
    rw [integral_div, integral_add hintE hintO] at step
    linarith [hev, hod, step]
  refine ⟨?_, ?_⟩
  · -- upper sign
    have hDr0 : ∀ L : ℝ, 0 ≤ L → L ≤ (r : ℝ) →
        (2 * σ) * ((∫ x, capLog u x ∂Erdos1002.gaussMeasure) * L) ≤ 0 := by
      intro L hL0 hLr
      have h1 : 0 ≤ (-(∫ x, capLog u x ∂Erdos1002.gaussMeasure)) * L :=
        mul_nonneg (by linarith) hL0
      nlinarith
    have h := main σ (abs_of_nonneg hσ) 0 hDr0
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith [mul_nonneg (sq_nonneg σ) hr0, hC₀pos.le,
      mul_nonneg (mul_nonneg hC₀pos.le (sq_nonneg σ)) hr0]
  · -- lower sign
    have hDrneg : ∀ L : ℝ, 0 ≤ L → L ≤ (r : ℝ) →
        (2 * (-σ)) * ((∫ x, capLog u x ∂Erdos1002.gaussMeasure) * L)
          ≤ 2 * σ * ((r : ℝ) * Real.exp (-u / 2)) := by
      intro L hL0 hLr
      have h1 : -(∫ x, capLog u x ∂Erdos1002.gaussMeasure) ≤ Real.exp (-u / 2) := by
        linarith
      have h2 : (-(∫ x, capLog u x ∂Erdos1002.gaussMeasure)) * L
          ≤ Real.exp (-u / 2) * L := mul_le_mul_of_nonneg_right h1 hL0
      have h3 : Real.exp (-u / 2) * L ≤ Real.exp (-u / 2) * r :=
        mul_le_mul_of_nonneg_left hLr (Real.exp_nonneg _)
      nlinarith [hσ]
    have habsneg : |(-σ)| = σ := by rw [abs_neg, abs_of_nonneg hσ]
    have h := main (-σ) habsneg _ hDrneg
    have hgoalrw : (fun α => Real.exp (-(σ * hatSum u W r α)))
        = fun α => Real.exp ((-σ) * hatSum u W r α) := by
      funext α; congr 1; ring
    rw [hgoalrw]
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith [mul_nonneg (sq_nonneg σ) hr0, hC₀pos.le,
      mul_nonneg (mul_nonneg hC₀pos.le (sq_nonneg σ)) hr0,
      mul_nonneg (mul_nonneg hσ hr0) (Real.exp_nonneg (-u / 2)),
      mul_nonneg (mul_nonneg hC₀pos.le (mul_nonneg hσ hr0)) (Real.exp_nonneg (-u / 2))]

end

end LargeDeviation

end Kwon1002
