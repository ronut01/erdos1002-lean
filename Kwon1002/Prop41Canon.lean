/-
Scratch file (agent `prop41`).

ASSIGNED TARGET: the canonical `Kwon1002.prop_4_1_marked_factorization`
(`Kwon1002/Section4.lean` lines 137-144, display (27)), currently sorried.

STATE FOUND.  The three-step `ErrorShape` decomposition of §4 is now 2/3
discharged by sibling agents:

* step 1 `integral_eq_sum_modeTerm`  -> `Prop4Final.integral_eq_sum_modeTerm'`
  (proved outright);
* step 2 `zero_mode_factorization`   -> `Prop41Final.zero_mode_factorization_f`
  (proved outright, on `Bridge.good_tuple_multiblock_mixing'`);
* step 3 `nonzero_mode_small`        -> still sorried.

So the canonical statement is already reachable, and §4 of the assembly is
`Prop41Final.prop_4_1_marked_factorization_f`.  Section 4 below reproduces
the canonical statement token-identically and derives it, so that the debt
is a single named sorried input and nothing else.

WHAT THIS FILE ADDS beyond the re-derivation: the first piece of the one
remaining branch.  `ErrorShape.nonzero_mode_small` names three obstructions;
the first of them is display **(28)**, the deterministic frequency bound

    (1/2) q_{j_s}  <=  |Q|  <=  2 L^D q_{j_s},      Q = sum_{l<=s} v_l (-1)^{j_l} q_{j_l},

which the manuscript deduces from "the continuants grow at least at the
Fibonacci rate" together with the separation condition (25) and |v_l| <= L^D.
Sections 1-3 prove that bound outright, in both a deterministic core form
and the `eventually`-in-`n` form the §4 branch consumes.

SORRIED RESULTS CONSUMED: exactly one,
`Kwon1002.ErrorShape.nonzero_mode_small`, and only in Section 4.
Sections 1-3 are unconditional.
-/
import Kwon1002.Prop41Final
import Kwon1002.AntiConcentration

open MeasureTheory Set Filter

open scoped BigOperators Topology

namespace Kwon1002

namespace Prop41Canon

open Prop41 ErrorShape

noncomputable section

/-! ## 1. Fibonacci growth of the continuants

The manuscript's "the continuants grow at least at the Fibonacci rate" is
used in exactly one way in the proof of (28): two indices `j < k` a distance
`2m` apart have `q_k >= 2^m q_j`.  That is what is proved here, straight from
the recursion `q_{j+2} = a_{j+2} q_{j+1} + q_j` of `Kwon1002.denom` and the
positivity of the digits (`GaussBasics.one_le_digit`). -/

variable {α : ℝ}

/-- `q_j ≤ q_{j+1}`. -/
theorem denom_le_succ (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (j : ℕ) :
    denom α j ≤ denom α (j + 1) := by
  cases j with
  | zero =>
      have h0 : denom α 0 = 1 := rfl
      have h1 : denom α 1 = digit α 0 := rfl
      rw [h0, h1]
      exact one_le_digit hα hirr 0
  | succ k =>
      have h : denom α (k + 1 + 1) = digit α (k + 1) * denom α (k + 1) + denom α k := rfl
      have h1 : 0 < digit α (k + 1) := one_le_digit hα hirr (k + 1)
      have h2 : denom α (k + 1) ≤ digit α (k + 1) * denom α (k + 1) :=
        Nat.le_mul_of_pos_left _ h1
      omega

/-- `q` is monotone along the orbit. -/
theorem denom_mono (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    Monotone (denom α) :=
  monotone_nat_of_le_succ (denom_le_succ hα hirr)

/-- The Fibonacci step: `2 q_j ≤ q_{j+2}`. -/
theorem two_mul_denom_le (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (j : ℕ) :
    2 * denom α j ≤ denom α (j + 2) := by
  have h : denom α (j + 2) = digit α (j + 1) * denom α (j + 1) + denom α j := rfl
  have h1 : 0 < digit α (j + 1) := one_le_digit hα hirr (j + 1)
  have h2 : denom α (j + 1) ≤ digit α (j + 1) * denom α (j + 1) :=
    Nat.le_mul_of_pos_left _ h1
  have h3 : denom α j ≤ denom α (j + 1) := denom_le_succ hα hirr j
  omega

/-- The Fibonacci rate, iterated: `2^m q_j ≤ q_{j+2m}`. -/
theorem pow_two_mul_denom_le (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (j m : ℕ) : 2 ^ m * denom α j ≤ denom α (j + 2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : 2 * (2 ^ m * denom α j) ≤ 2 * denom α (j + 2 * m) :=
        Nat.mul_le_mul le_rfl ih
      have h2 : 2 * denom α (j + 2 * m) ≤ denom α (j + 2 * m + 2) :=
        two_mul_denom_le hα hirr _
      have h3 : j + 2 * (m + 1) = j + 2 * m + 2 := by ring
      have h4 : 2 ^ (m + 1) * denom α j = 2 * (2 ^ m * denom α j) := by ring
      rw [h3, h4]
      omega

/-- The form used below: any two indices `2m` apart. -/
theorem pow_two_mul_denom_le_of_le (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    {j k m : ℕ} (h : j + 2 * m ≤ k) : 2 ^ m * denom α j ≤ denom α k :=
  le_trans (pow_two_mul_denom_le hα hirr j m) (denom_mono hα hirr h)

/-! ## 2. Geometric domination

The arithmetic core of (28), separated from the dynamics: a finite family
dominated by its last term at a ratio `ε ≤ 1/2` has total mass at most
`2ε` times that last term. -/

theorem sum_le_of_geom (q : ℕ → ℝ) (ε : ℝ) (hq : ∀ ℓ, 0 ≤ q ℓ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (s : ℕ)
    (hstep : ∀ ℓ, ℓ < s → q ℓ ≤ ε * q (ℓ + 1)) :
    ∑ ℓ ∈ Finset.range s, q ℓ ≤ 2 * ε * q s := by
  induction s with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      have : 0 ≤ 2 * ε := by linarith
      exact mul_nonneg this (hq 0)
  | succ s ih =>
      have hIH : ∑ ℓ ∈ Finset.range s, q ℓ ≤ 2 * ε * q s :=
        ih (fun ℓ hℓ => hstep ℓ (by omega))
      have hlast : q s ≤ ε * q (s + 1) := hstep s (by omega)
      rw [Finset.sum_range_succ]
      have hnn : 0 ≤ (1 - 2 * ε) * q s :=
        mul_nonneg (by linarith) (hq s)
      calc ∑ ℓ ∈ Finset.range s, q ℓ + q s ≤ 2 * ε * q s + q s := by linarith
        _ ≤ q s + q s := by nlinarith
        _ = 2 * q s := by ring
        _ ≤ 2 * (ε * q (s + 1)) := by linarith
        _ = 2 * ε * q (s + 1) := by ring

/-! ## 3. Display (28): the deterministic frequency bound

Manuscript, proof of Proposition 4.1: "By (8), the phase is `e^{2πinQα}`,
`Q = Σ_{ℓ≤s} v_ℓ (-1)^{j_ℓ} q_{j_ℓ}`. The continuants grow at least at the
Fibonacci rate.  The separation condition and `|v_ℓ| ≤ L^D` therefore give,
deterministically, `(1/2) q_{j_s} ≤ |Q| ≤ 2 L^D q_{j_s}` for all sufficiently
large `n`."

Indices follow §4: `v` runs over `ℓ ≤ s`, the manuscript's `v_ℓ = 0` for
`ℓ > s` being exactly the restriction of the sum to `Finset.range (s+1)`. -/

/-- `Q = Σ_{ℓ ≤ s} v_ℓ (-1)^{j_ℓ} q_{j_ℓ}`, the frequency of the mode `v`
truncated at its top nonzero index `s`. -/
def freqQ (α : ℝ) (j : ℕ → ℕ) (v : ℕ → ℤ) (s : ℕ) : ℤ :=
  ∑ ℓ ∈ Finset.range (s + 1), v ℓ * (-1) ^ (j ℓ) * (denom α (j ℓ) : ℤ)

/-- **Display (28), deterministic core.**  `m` is the half-gap (`m = ⌊100H⌋`
in the application, the separation being `⌊200H⌋`), `M` the coefficient cap
(`M = L^D`); `4M ≤ 2^m` is exactly "for all sufficiently large `n`". -/
theorem display_28_core (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (j : ℕ → ℕ) (v : ℕ → ℤ) (M : ℝ) (hM : 1 ≤ M) (s m : ℕ)
    (hv : ∀ ℓ, |(v ℓ : ℝ)| ≤ M) (hvs : v s ≠ 0)
    (hgap : ∀ ℓ, ℓ < s → j ℓ + 2 * m ≤ j (ℓ + 1))
    (hm : 4 * M ≤ (2 : ℝ) ^ m) :
    (denom α (j s) : ℝ) / 2 ≤ |((freqQ α j v s : ℤ) : ℝ)| ∧
      |((freqQ α j v s : ℤ) : ℝ)| ≤ 2 * M * (denom α (j s) : ℝ) := by
  have hq0 : ∀ ℓ : ℕ, (0 : ℝ) ≤ (denom α (j ℓ) : ℝ) := fun ℓ => Nat.cast_nonneg _
  have hPpos : (0 : ℝ) < 2 ^ m := by positivity
  set ε : ℝ := ((2 : ℝ) ^ m)⁻¹ with hεdef
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hεmul : ε * (2 : ℝ) ^ m = 1 := by
    rw [hεdef]; field_simp
  -- `4Mε ≤ 1`, hence `2Mε ≤ 1/2` and (since `M ≥ 1`) `ε ≤ 1/2`.
  have h4Mε : 4 * M * ε ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hm hε0
    calc 4 * M * ε ≤ (2:ℝ) ^ m * ε := h
      _ = ε * (2:ℝ) ^ m := by ring
      _ = 1 := hεmul
  have hεhalf : ε ≤ 1 / 2 := by nlinarith
  -- the geometric step, from the Fibonacci rate
  have hstep : ∀ ℓ, ℓ < s → (denom α (j ℓ) : ℝ) ≤ ε * (denom α (j (ℓ + 1)) : ℝ) := by
    intro ℓ hℓ
    have hnat : 2 ^ m * denom α (j ℓ) ≤ denom α (j (ℓ + 1)) :=
      pow_two_mul_denom_le_of_le hα hirr (hgap ℓ hℓ)
    have hreal : (2 : ℝ) ^ m * (denom α (j ℓ) : ℝ) ≤ (denom α (j (ℓ + 1)) : ℝ) := by
      exact_mod_cast hnat
    rw [hεdef, inv_mul_eq_div, le_div_iff₀ hPpos]
    linarith [hreal]
  have hsum : ∑ ℓ ∈ Finset.range s, (denom α (j ℓ) : ℝ) ≤ 2 * ε * (denom α (j s) : ℝ) :=
    sum_le_of_geom (fun ℓ => (denom α (j ℓ) : ℝ)) ε hq0 hε0 hεhalf s hstep
  -- split off the top term
  set T : ℝ := (v s : ℝ) * (-1) ^ (j s) * (denom α (j s) : ℝ) with hTdef
  set S : ℝ := ∑ ℓ ∈ Finset.range s, (v ℓ : ℝ) * (-1) ^ (j ℓ) * (denom α (j ℓ) : ℝ) with hSdef
  have hsplitZ : freqQ α j v s
      = (∑ ℓ ∈ Finset.range s, v ℓ * (-1) ^ (j ℓ) * (denom α (j ℓ) : ℤ))
        + v s * (-1) ^ (j s) * (denom α (j s) : ℤ) := Finset.sum_range_succ _ _
  have hsplit : ((freqQ α j v s : ℤ) : ℝ) = S + T := by
    rw [hsplitZ, hSdef, hTdef]
    push_cast
    ring
  -- the tail
  have htail : |S| ≤ M * (2 * ε * (denom α (j s) : ℝ)) := by
    have hterm : ∀ ℓ ∈ Finset.range s,
        |(v ℓ : ℝ) * (-1) ^ (j ℓ) * (denom α (j ℓ) : ℝ)| ≤ M * (denom α (j ℓ) : ℝ) := by
      intro ℓ _
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
        abs_of_nonneg (hq0 ℓ)]
      exact mul_le_mul_of_nonneg_right (hv ℓ) (hq0 ℓ)
    calc |S| ≤ ∑ ℓ ∈ Finset.range s, |(v ℓ : ℝ) * (-1) ^ (j ℓ) * (denom α (j ℓ) : ℝ)| := by
          rw [hSdef]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ℓ ∈ Finset.range s, M * (denom α (j ℓ) : ℝ) := Finset.sum_le_sum hterm
      _ = M * ∑ ℓ ∈ Finset.range s, (denom α (j ℓ) : ℝ) := by rw [Finset.mul_sum]
      _ ≤ M * (2 * ε * (denom α (j s) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by linarith)
  -- the top term
  have hvs1 : (1 : ℝ) ≤ |(v s : ℝ)| := by
    have hz : (1 : ℤ) ≤ |v s| := by
      have := abs_pos.mpr hvs
      omega
    have : ((1 : ℤ) : ℝ) ≤ ((|v s| : ℤ) : ℝ) := by exact_mod_cast hz
    rwa [Int.cast_abs, Int.cast_one] at this
  have hTabs : |T| = |(v s : ℝ)| * (denom α (j s) : ℝ) := by
    rw [hTdef, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_nonneg (hq0 s)]
  have hTlow : (denom α (j s) : ℝ) ≤ |T| := by
    rw [hTabs]
    nlinarith [hq0 s]
  have hTup : |T| ≤ M * (denom α (j s) : ℝ) := by
    rw [hTabs]
    exact mul_le_mul_of_nonneg_right (hv s) (hq0 s)
  -- `2Mε ≤ 1/2`
  have hMε : M * (2 * ε) ≤ 1 / 2 := by nlinarith
  have hMεq : M * (2 * ε * (denom α (j s) : ℝ)) ≤ (denom α (j s) : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_right hMε (hq0 s)
    calc M * (2 * ε * (denom α (j s) : ℝ)) = M * (2 * ε) * (denom α (j s) : ℝ) := by ring
      _ ≤ 1 / 2 * (denom α (j s) : ℝ) := h
      _ = (denom α (j s) : ℝ) / 2 := by ring
  constructor
  · -- lower bound
    have hkey : |T| - |S| ≤ |T + S| := by
      have h := abs_sub_abs_le_abs_sub T (-S)
      simpa [abs_neg, sub_neg_eq_add] using h
    have hcomm : ((freqQ α j v s : ℤ) : ℝ) = T + S := by rw [hsplit]; ring
    rw [hcomm]
    have h1 : M * (2 * ε * (denom α (j s) : ℝ)) ≤ (denom α (j s) : ℝ) / 2 := hMεq
    linarith [htail, hTlow, hkey]
  · -- upper bound
    rw [hsplit]
    have hle : |S + T| ≤ |S| + |T| := abs_add_le _ _
    have hq2 : (denom α (j s) : ℝ) / 2 ≤ M * (denom α (j s) : ℝ) := by
      nlinarith [hq0 s]
    linarith [htail, hTup, hMεq]

/-! ### The scale condition `4L^D ≤ 2^{⌊100H⌋}`

"for all sufficiently large `n`" of (28), proved.  `H = L^{3/4}` beats every
fixed power of `L`; the proof splits `L^{3/4} = L^{3/8} · L^{3/8}` and uses
`log x ≤ x - 1` at `x = L^{3/8}` to absorb `D log L`. -/

theorem eventually_four_rpow_le_two_pow (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, 4 * (Lnorm n) ^ D ≤ (2 : ℝ) ^ (⌊100 * Hscale n⌋₊) := by
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hXtend : Tendsto (fun L : ℝ => L ^ (3 / 8 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  set K : ℝ := (8 * D / 3 + Real.log 8) / (100 * Real.log 2) with hKdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have key : ∀ᶠ L : ℝ in atTop,
      4 * L ^ D ≤ (2 : ℝ) ^ (⌊100 * L ^ (3 / 4 : ℝ)⌋₊) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hXtend.eventually_ge_atTop K,
      hXtend.eventually_ge_atTop (1 : ℝ)] with L hL1 hLK hL1'
    have hL0 : (0 : ℝ) < L := by linarith
    set X : ℝ := L ^ (3 / 8 : ℝ) with hXdef
    have hXpos : 0 < X := by rw [hXdef]; positivity
    -- `L^{3/4} = X^2`
    have hsq : L ^ (3 / 4 : ℝ) = X * X := by
      rw [hXdef, ← Real.rpow_add hL0]
      norm_num
    -- `log L ≤ (8/3) X`
    have hlogL : Real.log L ≤ 8 / 3 * X := by
      have h1 : Real.log X = 3 / 8 * Real.log L := by
        rw [hXdef, Real.log_rpow hL0]
      have h2 : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos hXpos
      linarith
    -- the main inequality `log 8 + D log L ≤ 100 log 2 · L^{3/4}`
    have hmain : Real.log 8 + D * Real.log L ≤ 100 * Real.log 2 * L ^ (3 / 4 : ℝ) := by
      have hDlog : D * Real.log L ≤ 8 * D / 3 * X := by
        nlinarith [hlogL, hD.le]
      have hKX : 8 * D / 3 + Real.log 8 ≤ 100 * Real.log 2 * X := by
        have : K * (100 * Real.log 2) ≤ X * (100 * Real.log 2) := by
          apply mul_le_mul_of_nonneg_right hLK
          positivity
        rw [hKdef] at this
        have hne : (100 * Real.log 2) ≠ 0 := by positivity
        field_simp at this
        linarith
      have hXX : (8 * D / 3 + Real.log 8) * X ≤ (100 * Real.log 2 * X) * X :=
        mul_le_mul_of_nonneg_right hKX hXpos.le
      rw [hsq]
      have hlog8X : Real.log 8 ≤ Real.log 8 * X := by nlinarith
      nlinarith [hXX, hDlog, hL1', hlog8X]
    -- turn it into the exponential bound
    set m : ℕ := ⌊100 * L ^ (3 / 4 : ℝ)⌋₊ with hmdef
    have hmlow : 100 * L ^ (3 / 4 : ℝ) - 1 ≤ (m : ℝ) := by
      have := Nat.lt_floor_add_one (100 * L ^ (3 / 4 : ℝ))
      rw [← hmdef] at this
      linarith
    have hpow : (2 : ℝ) ^ m = Real.exp (Real.log 2 * (m : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) m, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    have hexp1 : Real.exp (Real.log 4 + D * Real.log L) ≤ Real.exp (Real.log 2 * (m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog84 : Real.log 8 = Real.log 4 + Real.log 2 := by
        rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      have hstep : Real.log 2 * (100 * L ^ (3 / 4 : ℝ) - 1) ≤ Real.log 2 * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hmlow hlog2.le
      nlinarith [hmain, hstep]
    have heq4 : 4 * L ^ D = Real.exp (Real.log 4 + D * Real.log L) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 4),
        Real.rpow_def_of_pos hL0, mul_comm D (Real.log L)]
    rw [heq4, hpow]
    exact hexp1
  have := hLtend.eventually key
  simpa [Hscale] using this

/-- **Display (28)**, in the form the `v_s ≠ 0` branch of §4 consumes:
uniformly over good tuples, over admissible mode caps, and over irrational
`α ∈ (0,1)`, for all large `n`. -/
theorem display_28 (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop,
      ∀ α : ℝ, α ∈ Ioo (0 : ℝ) 1 → Irrational α →
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ v : ℕ → ℤ, (∀ ℓ, |(v ℓ : ℝ)| ≤ (Lnorm n) ^ D) →
      ∀ s : ℕ, s < r → v s ≠ 0 →
        (denom α (j s) : ℝ) / 2 ≤ |((freqQ α j v s : ℤ) : ℝ)| ∧
          |((freqQ α j v s : ℤ) : ℝ)| ≤ 2 * (Lnorm n) ^ D * (denom α (j s) : ℝ) := by
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_four_rpow_le_two_pow D hD, hLtend.eventually_ge_atTop (1 : ℝ)]
    with n hscale hL1 α hα hirr j hj v hv s hs hvs
  have hM : (1 : ℝ) ≤ (Lnorm n) ^ D := Real.one_le_rpow hL1 hD.le
  have hH0 : (0 : ℝ) ≤ 100 * Hscale n := by
    have : (0 : ℝ) ≤ Hscale n := Real.rpow_nonneg (by linarith) _
    linarith
  -- the half-gap `m = ⌊100H⌋`, with `2m ≤ ⌊200H⌋`
  have hhalf : 2 * ⌊100 * Hscale n⌋₊ ≤ ⌊200 * Hscale n⌋₊ := by
    have h1 : ((⌊100 * Hscale n⌋₊ : ℕ) : ℝ) ≤ 100 * Hscale n := Nat.floor_le hH0
    refine Nat.le_floor ?_
    push_cast
    linarith
  have hgap : ∀ ℓ, ℓ < s → j ℓ + 2 * ⌊100 * Hscale n⌋₊ ≤ j (ℓ + 1) := by
    intro ℓ hℓ
    have hsep : j ℓ + ⌊200 * Hscale n⌋₊ ≤ j (ℓ + 1) :=
      goodTuple_sep n r j hj ℓ (by omega)
    omega
  exact display_28_core hα hirr j v ((Lnorm n) ^ D) hM s ⌊100 * Hscale n⌋₊ hv hvs hgap hscale

end

end Prop41Canon

/-! ## 4. The canonical Proposition 4.1

Reproduced token-identically from `Kwon1002/Section4.lean` lines 137-144
(mechanical line diff run against that block: empty apart from the `_c`
suffix on the name, which is forced because the canonical name is already
occupied by the sorried declaration in the imported `Section4`).  Placing it
in `namespace Kwon1002` makes every identifier, `GoodTuple`, `IsInPD`,
`Lnorm`, `digit`, `theta`, `stationaryMean`, resolve exactly as it does
there. -/

theorem prop_4_1_marked_factorization_c (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  -- Steps 1 and 2 of the `ErrorShape` decomposition are discharged
  -- (`Prop4Final.integral_eq_sum_modeTerm'`, `Prop41Final.zero_mode_factorization_f`);
  -- step 3, `ErrorShape.nonzero_mode_small`, is the single sorried input.
  obtain ⟨B, C, c, ρ, hC, hc, hρ0, hρ1, hbd⟩ := Prop41Final.prop_4_1_error_shape_f r D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbd, Prop41.eventually_rpow_mul_deltaScale_le A B c ρ hc hρ0 hρ1]
    with n hn harith j hj F hF
  calc ‖(∫ α in Ioo (0 : ℝ) 1,
            ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C * (Lnorm n) ^ B * Prop41.deltaScale c ρ n := hn j hj F hF
    _ = C * ((Lnorm n) ^ B * Prop41.deltaScale c ρ n) := by ring
    _ ≤ C * (Lnorm n) ^ (-A) := mul_le_mul_of_nonneg_left harith hC.le

end Kwon1002

