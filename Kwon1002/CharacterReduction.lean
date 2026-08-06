import Kwon1002.Section4

/-!
# §4, the exact-arithmetic heart: window characters and monomial frequencies

Scratch file for the `s4chars` pass.  Targets (both `sorry`-ed in
`Kwon1002.Section4`):

* `window_character_reduction` (display (31));
* `torusChar_monomial_frequency` (display (33)).

Everything is built from §2's coordinates (`betaProd`, `theta`, `thetaPred`)
and the continuant recursion (`denom`).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

noncomputable section

/-! ## The character `e(t)` is `1`-periodic -/

lemma torusChar_add_int (t : ℝ) (m : ℤ) : torusChar (t + (m : ℝ)) = torusChar t := by
  unfold torusChar
  have h : ((t + (m : ℝ) : ℝ) : ℂ) = (t : ℂ) + (m : ℂ) := by push_cast; ring
  rw [h, mul_add, Complex.exp_add]
  have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) = 1 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
        = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [h2, mul_one]

lemma torusChar_zero : torusChar 0 = 1 := by
  simp [torusChar]

lemma torusChar_half : torusChar (1 / 2) = -1 := by
  unfold torusChar
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (((1 : ℝ) / 2 : ℝ) : ℂ))
      = (Real.pi : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-! ## The `β`-recursion behind (9): `β_{k+1} = β_{k-1} - a_{k+1} β_k` -/

lemma betaProd_one_eq {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    betaProd α 1 = 1 - (digit α 0 : ℝ) * betaProd α 0 := by
  have h := inv_gaussIter_eq hα hirr 0
  have hx : gaussIter α 0 ≠ 0 := ne_of_gt (gaussIter_mem_Ioo hα hirr 0).1
  have h2 : gaussIter α 1 = (gaussIter α 0)⁻¹ - (digit α 0 : ℝ) := by rw [h]; ring
  rw [betaProd_succ α 0, betaProd_zero, h2, mul_sub, mul_inv_cancel₀ hx]
  ring

lemma betaProd_add_two {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (k : ℕ) :
    betaProd α (k + 2) = betaProd α k - (digit α (k + 1) : ℝ) * betaProd α (k + 1) := by
  have h := inv_gaussIter_eq hα hirr (k + 1)
  have hx : gaussIter α (k + 1) ≠ 0 := ne_of_gt (gaussIter_mem_Ioo hα hirr (k + 1)).1
  have h2 : gaussIter α (k + 2) = (gaussIter α (k + 1))⁻¹ - (digit α (k + 1) : ℝ) := by
    rw [h]; ring
  have hb : betaProd α (k + 2) = betaProd α (k + 1) * gaussIter α (k + 2) :=
    betaProd_succ α (k + 1)
  rw [hb, h2, betaProd_succ α k, mul_sub, mul_assoc, mul_inv_cancel₀ hx]
  ring

/-! ## (9) mod 1 : `θ_{k+1} ≡ θ_{k-1} - a_{k+1} θ_k` -/

/-- If `u = v - A w` with `A` an integer, the fractional parts obey the same
relation modulo `1`. -/
lemma fract_combo (A : ℤ) (u v w : ℝ) (h : u = v - (A : ℝ) * w) :
    ∃ m : ℤ, Int.fract u = Int.fract v - (A : ℝ) * Int.fract w + (m : ℝ) := by
  refine ⟨⌊v⌋ - A * ⌊w⌋ - ⌊u⌋, ?_⟩
  have hu : Int.fract u = u - (⌊u⌋ : ℝ) := rfl
  have hv : Int.fract v = v - (⌊v⌋ : ℝ) := rfl
  have hw : Int.fract w = w - (⌊w⌋ : ℝ) := rfl
  rw [hu, hv, hw, h]
  push_cast
  ring

/-- **(9) mod 1.**  `θ_{k+1} ≡ θ_{k-1} - a_{k+1} θ_k`, with the convention
`θ_{-1} = 0` of `thetaPred` (consistent because `β_{-1} = 1`, so
`n β_{-1} = n ∈ ℤ`). -/
lemma theta_succ_mod {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n k : ℕ) :
    ∃ m : ℤ, theta α n (k + 1)
      = thetaPred α n k - (digit α k : ℝ) * theta α n k + (m : ℝ) := by
  cases k with
  | zero =>
    have hβ : (n : ℝ) * betaProd α 1
        = (n : ℝ) - ((digit α 0 : ℤ) : ℝ) * ((n : ℝ) * betaProd α 0) := by
      rw [betaProd_one_eq hα hirr]; push_cast; ring
    obtain ⟨m, hm⟩ := fract_combo (digit α 0 : ℤ) ((n : ℝ) * betaProd α 1) (n : ℝ)
      ((n : ℝ) * betaProd α 0) hβ
    refine ⟨m, ?_⟩
    have h0 : Int.fract ((n : ℝ)) = 0 := by simp
    have hp : thetaPred α n 0 = 0 := rfl
    have hθ0 : theta α n 0 = Int.fract ((n : ℝ) * betaProd α 0) := rfl
    have hθ1 : theta α n 1 = Int.fract ((n : ℝ) * betaProd α 1) := rfl
    rw [show (0 : ℕ) + 1 = 1 from rfl, hθ1, hm, h0, hp, hθ0]
    push_cast
    ring
  | succ k =>
    have hβ : (n : ℝ) * betaProd α (k + 2)
        = (n : ℝ) * betaProd α k
          - ((digit α (k + 1) : ℤ) : ℝ) * ((n : ℝ) * betaProd α (k + 1)) := by
      rw [betaProd_add_two hα hirr k]; push_cast; ring
    obtain ⟨m, hm⟩ := fract_combo (digit α (k + 1) : ℤ) ((n : ℝ) * betaProd α (k + 2))
      ((n : ℝ) * betaProd α k) ((n : ℝ) * betaProd α (k + 1)) hβ
    refine ⟨m, ?_⟩
    have hp : thetaPred α n (k + 1) = theta α n k := rfl
    have hθa : theta α n k = Int.fract ((n : ℝ) * betaProd α k) := rfl
    have hθb : theta α n (k + 1) = Int.fract ((n : ℝ) * betaProd α (k + 1)) := rfl
    have hθc : theta α n (k + 2) = Int.fract ((n : ℝ) * betaProd α (k + 2)) := rfl
    rw [show k + 1 + 1 = k + 2 from rfl, hθc, hm, hp, hθa, hθb]
    push_cast
    ring

/-! ## The master identity `β_k = (-1)^k (q_k α - p_k)` -/

/-- Continuant numerators: `p_0 = 0`, `p_1 = 1`, `p_{j+1} = a_{j+1} p_j + p_{j-1}`. -/
def numer (α : ℝ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => digit α (j + 1) * numer α (j + 1) + numer α j

lemma betaProd_eq_convergent {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (k : ℕ) :
    betaProd α k = (-1 : ℝ) ^ k * ((denom α k : ℝ) * α - (numer α k : ℝ)) := by
  have key : ∀ k : ℕ,
      (betaProd α k = (-1 : ℝ) ^ k * ((denom α k : ℝ) * α - (numer α k : ℝ)))
      ∧ (betaProd α (k + 1)
          = (-1 : ℝ) ^ (k + 1) * ((denom α (k + 1) : ℝ) * α - (numer α (k + 1) : ℝ))) := by
    intro k
    induction k with
    | zero =>
      have hd0 : denom α 0 = 1 := rfl
      have hn0 : numer α 0 = 0 := rfl
      have hd1 : denom α 1 = digit α 0 := rfl
      have hn1 : numer α 1 = 1 := rfl
      refine ⟨?_, ?_⟩
      · have : betaProd α 0 = α := by rw [betaProd_zero]; rfl
        rw [this, hd0, hn0]
        push_cast
        ring
      · have hb : betaProd α 0 = α := by rw [betaProd_zero]; rfl
        rw [betaProd_one_eq hα hirr, hb, hd1, hn1]
        push_cast
        ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hd : denom α (k + 2) = digit α (k + 1) * denom α (k + 1) + denom α k := rfl
      have hn : numer α (k + 2) = digit α (k + 1) * numer α (k + 1) + numer α k := rfl
      rw [show k + 1 + 1 = k + 2 from rfl, betaProd_add_two hα hirr k, ih.1, ih.2, hd, hn]
      push_cast
      ring
  exact (key k).1

/-- **(8)** `θ_k ≡ (-1)^k q_k n α (mod 1)`. -/
lemma theta_eq_mod {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n k : ℕ) :
    ∃ m : ℤ, theta α n k = (-1 : ℝ) ^ k * (denom α k : ℝ) * (n : ℝ) * α + (m : ℝ) := by
  obtain ⟨F, hF⟩ : ∃ F : ℤ, theta α n k = (n : ℝ) * betaProd α k - (F : ℝ) :=
    ⟨⌊(n : ℝ) * betaProd α k⌋, rfl⟩
  refine ⟨-((-1) ^ k * (numer α k : ℤ) * (n : ℤ)) - F, ?_⟩
  rw [hF, betaProd_eq_convergent hα hirr k]
  push_cast
  ring

/-! ## (33): the frequency of a cylinder-torus monomial -/

/-- The statement of `Kwon1002.torusChar_monomial_frequency` (`Section4.lean`),
verbatim, packaged as a `Prop` so that it can be refuted. -/
def TorusCharMonomialFrequencyStatement : Prop :=
  ∀ (α : ℝ) (n j : ℕ), 1 ≤ j → ∀ (r s : ℤ),
    torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j)
      = torusChar ((-1 : ℝ) ^ j * (Qfreq α j r s : ℝ) * (n : ℝ) * α)

/-- **(33), with the standing §2 hypotheses restored.**  The torus part of a
monomial at time `j` is the pure phase `e((-1)^j Q_j(r,s) n α)`. -/
theorem torusChar_monomial_frequency' {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hj : 1 ≤ j) (r s : ℤ) :
    torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j)
      = torusChar ((-1 : ℝ) ^ j * (Qfreq α j r s : ℝ) * (n : ℝ) * α) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m1, h1⟩ := theta_eq_mod hα hirr n j
  obtain ⟨m2, h2⟩ := theta_eq_mod hα hirr n (j + 1)
  have hp : thetaPred α n (j + 1) = theta α n j := rfl
  have hQ : Qfreq α (j + 1) r s = s * (denom α (j + 1) : ℤ) - r * (denom α j : ℤ) := by
    simp [Qfreq]
  have hkey : (r : ℝ) * thetaPred α n (j + 1) + (s : ℝ) * theta α n (j + 1)
      = (-1 : ℝ) ^ (j + 1) * (Qfreq α (j + 1) r s : ℝ) * (n : ℝ) * α
        + ((r * m1 + s * m2 : ℤ) : ℝ) := by
    rw [hp, h1, h2, hQ]
    push_cast
    ring
  rw [hkey, torusChar_add_int]

/-! ### The statement without hypotheses on `α` is false -/

lemma gaussIter_half_one : gaussIter (1 / 2 : ℝ) 1 = 0 := by
  show Int.fract (((1 : ℝ) / 2)⁻¹) = 0
  norm_num [Int.fract]

lemma gaussIter_half_two : gaussIter (1 / 2 : ℝ) 2 = 0 := by
  show gaussMap (gaussMap (1 / 2 : ℝ)) = 0
  rw [show gaussMap (1 / 2 : ℝ) = 0 from gaussIter_half_one]
  show Int.fract ((0 : ℝ)⁻¹) = 0
  norm_num [Int.fract]

lemma betaProd_half_one : betaProd (1 / 2 : ℝ) 1 = 0 := by
  have h : betaProd (1 / 2 : ℝ) 1 = ∏ i ∈ Finset.range 2, gaussIter (1 / 2 : ℝ) i := rfl
  rw [h, Finset.prod_range_succ, Finset.prod_range_succ, gaussIter_half_one]
  ring

lemma betaProd_half_two : betaProd (1 / 2 : ℝ) 2 = 0 := by
  have h : betaProd (1 / 2 : ℝ) 2 = ∏ i ∈ Finset.range 3, gaussIter (1 / 2 : ℝ) i := rfl
  rw [h, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    gaussIter_half_one]
  ring

lemma theta_half_one (n : ℕ) : theta (1 / 2 : ℝ) n 1 = 0 := by
  show Int.fract ((n : ℝ) * betaProd (1 / 2 : ℝ) 1) = 0
  rw [betaProd_half_one]
  simp

lemma theta_half_two (n : ℕ) : theta (1 / 2 : ℝ) n 2 = 0 := by
  show Int.fract ((n : ℝ) * betaProd (1 / 2 : ℝ) 2) = 0
  rw [betaProd_half_two]
  simp

lemma digit_half_one : digit (1 / 2 : ℝ) 1 = 0 := by
  show ⌊(gaussIter (1 / 2 : ℝ) 1)⁻¹⌋.toNat = 0
  rw [gaussIter_half_one]
  norm_num

lemma denom_half_two : denom (1 / 2 : ℝ) 2 = 1 := by
  have h : denom (1 / 2 : ℝ) 2
      = digit (1 / 2 : ℝ) 1 * denom (1 / 2 : ℝ) 1 + denom (1 / 2 : ℝ) 0 := rfl
  rw [h, digit_half_one]
  show 0 * denom (1 / 2 : ℝ) 1 + 1 = 1
  ring

/-- Type-check guard.  The amended canonical statement in `Section4.lean`,
which now carries the standing §2 hypotheses, is discharged by the proof
here.  Its `sorry` there is plumbing forced by the import direction, not
mathematical debt: this `example` fails to elaborate if the two statements
ever drift apart. -/
example : ∀ {α : ℝ}, α ∈ Ioo (0 : ℝ) 1 → Irrational α → ∀ (n j : ℕ), 1 ≤ j →
    ∀ (r s : ℤ),
      torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j)
        = torusChar ((-1 : ℝ) ^ j * (Qfreq α j r s : ℝ) * (n : ℝ) * α) :=
  fun hα hirr n j hj r s => torusChar_monomial_frequency' hα hirr n j hj r s

/-- **Finding (manuscript-vs-formalisation).**  The hypothesis-free form of
`torusChar_monomial_frequency`, as `Section4.lean` stated it before the
amendment, is **false**.
Counterexample: `α = 1/2`, `n = 1`, `j = 2`, `(r,s) = (0,1)`; the left side is
`1`, the right side is `-1`.  The Gauss orbit of a rational reaches `0`, where
Lean's `0⁻¹ = 0` convention makes the digit `0` and breaks the `β`-recursion.
The identity holds with the standing §2 hypotheses `α ∈ Ioo 0 1` and
`Irrational α`, see `torusChar_monomial_frequency'`. -/
theorem torusChar_monomial_frequency_false : ¬ TorusCharMonomialFrequencyStatement := by
  intro h
  have h2 := h (1 / 2 : ℝ) 1 2 (by norm_num) 0 1
  have hQ : Qfreq (1 / 2 : ℝ) 2 0 1 = 1 := by
    have h : Qfreq (1 / 2 : ℝ) 2 0 1
        = (1 : ℤ) * (denom (1 / 2 : ℝ) 2 : ℤ) - (0 : ℤ) * (denom (1 / 2 : ℝ) (2 - 1) : ℤ) := rfl
    rw [h, denom_half_two]
    ring
  have hpred : thetaPred (1 / 2 : ℝ) 1 2 = 0 := theta_half_one 1
  have e1 : ((0 : ℤ) : ℝ) * thetaPred (1 / 2 : ℝ) 1 2
      + ((1 : ℤ) : ℝ) * theta (1 / 2 : ℝ) 1 2 = 0 := by
    rw [hpred, theta_half_two 1]; ring
  have e2 : (-1 : ℝ) ^ (2 : ℕ) * ((Qfreq (1 / 2 : ℝ) 2 0 1 : ℤ) : ℝ) * ((1 : ℕ) : ℝ)
      * (1 / 2 : ℝ) = 1 / 2 := by
    rw [hQ]; norm_num
  rw [e1, e2, torusChar_zero, torusChar_half] at h2
  norm_num at h2

/-! ## (31): reduction of a radius-`R` window character to the central pair

The integers `A_w`, `B_w` are produced by two recursions run on the digit word
alone.  Upward (`upC`) they encode `θ_{j+t} ≡ u_t θ_j + v_t θ_{j-1}` via
`θ_{i+1} = θ_{i-1} - a_{i+1} θ_i`; downward (`downC`) the same recursion read
backwards, `θ_{i-1} = θ_{i+1} + a_{i+1} θ_i`.
-/

/-- A radius-`R` word read as a total function `ℕ → ℕ` (zero off the window). -/
def wordFn (R : ℕ) (w : Fin (2 * R) → ℕ) (t : ℕ) : ℕ :=
  if h : t < 2 * R then w ⟨t, h⟩ else 0

/-- `upC R v t = (u_t, v_t)` with `θ_{j+t} ≡ u_t θ_j + v_t θ_{j-1} (mod 1)`,
the word `v` being read as `v t = a_{j+t-R+1}`. -/
def upC (R : ℕ) (v : ℕ → ℕ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (-(v R : ℤ), 1)
  | t + 2 =>
      ((upC R v t).1 - (v (R + t + 1) : ℤ) * (upC R v (t + 1)).1,
       (upC R v t).2 - (v (R + t + 1) : ℤ) * (upC R v (t + 1)).2)

/-- `downC R v d = (u_d, v_d)` with `θ_{j-d} ≡ u_d θ_j + v_d θ_{j-1} (mod 1)`. -/
def downC (R : ℕ) (v : ℕ → ℕ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | d + 2 =>
      ((downC R v d).1 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).1,
       (downC R v d).2 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).2)

/-- The coefficient pair attached to the window position `i ∈ {0,…,2R}`, i.e.
to the time `j + i - R`. -/
def winC (R : ℕ) (v : ℕ → ℕ) (i : ℕ) : ℤ × ℤ :=
  if R ≤ i then upC R v (i - R) else downC R v (R - i)

/-- `A_w` of (31). -/
def winA (R : ℕ) (c : Fin (2 * R + 1) → ℤ) (w : Fin (2 * R) → ℕ) : ℤ :=
  ∑ i : Fin (2 * R + 1), c i * (winC R (wordFn R w) (i : ℕ)).1

/-- `B_w` of (31). -/
def winB (R : ℕ) (c : Fin (2 * R + 1) → ℤ) (w : Fin (2 * R) → ℕ) : ℤ :=
  ∑ i : Fin (2 * R + 1), c i * (winC R (wordFn R w) (i : ℕ)).2

lemma wordFn_windowWord (R : ℕ) (α : ℝ) (j t : ℕ) (ht : t < 2 * R) :
    wordFn R (windowWord R α j) t = digit α (j + t - R) := by
  simp [wordFn, windowWord, ht]

lemma thetaPred_eq_theta_sub (α : ℝ) (n j : ℕ) (hj : 1 ≤ j) :
    thetaPred α n j = theta α n (j - 1) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rfl

/-- Upward half of (31). -/
lemma up_theta {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j R : ℕ) (v : ℕ → ℕ) (hv : ∀ t, t < 2 * R → v t = digit α (j + t - R)) :
    ∀ t, t ≤ R → ∃ m : ℤ, theta α n (j + t)
      = ((upC R v t).1 : ℝ) * theta α n j
        + ((upC R v t).2 : ℝ) * thetaPred α n j + (m : ℝ) := by
  have key : ∀ t : ℕ,
      (t ≤ R → ∃ m : ℤ, theta α n (j + t)
        = ((upC R v t).1 : ℝ) * theta α n j
          + ((upC R v t).2 : ℝ) * thetaPred α n j + (m : ℝ))
      ∧ (t + 1 ≤ R → ∃ m : ℤ, theta α n (j + (t + 1))
        = ((upC R v (t + 1)).1 : ℝ) * theta α n j
          + ((upC R v (t + 1)).2 : ℝ) * thetaPred α n j + (m : ℝ)) := by
    intro t
    induction t with
    | zero =>
      constructor
      · intro _
        refine ⟨0, ?_⟩
        have hc : upC R v 0 = ((1 : ℤ), (0 : ℤ)) := rfl
        rw [show j + 0 = j from rfl, hc]
        push_cast
        ring
      · intro hR
        obtain ⟨m, hm⟩ := theta_succ_mod hα hirr n j
        refine ⟨m, ?_⟩
        have hvR : v R = digit α j := by
          rw [hv R (by omega)]
          congr 1
          omega
        have hc : upC R v (0 + 1) = (-(v R : ℤ), (1 : ℤ)) := rfl
        rw [show j + (0 + 1) = j + 1 from rfl, hc, hvR, hm]
        push_cast
        ring
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      intro hR
      obtain ⟨m1, hm1⟩ := ih.1 (by omega)
      obtain ⟨m2, hm2⟩ := ih.2 (by omega)
      obtain ⟨m0, hm0⟩ := theta_succ_mod hα hirr n (j + t + 1)
      have hvidx : v (R + t + 1) = digit α (j + t + 1) := by
        rw [hv (R + t + 1) (by omega)]
        congr 1
        omega
      have hpred : thetaPred α n (j + t + 1) = theta α n (j + t) := rfl
      have hc : upC R v (t + 1 + 1)
          = ((upC R v t).1 - (v (R + t + 1) : ℤ) * (upC R v (t + 1)).1,
             (upC R v t).2 - (v (R + t + 1) : ℤ) * (upC R v (t + 1)).2) := rfl
      refine ⟨m1 - (v (R + t + 1) : ℤ) * m2 + m0, ?_⟩
      have hstep : theta α n (j + (t + 1 + 1))
          = theta α n (j + t) - (v (R + t + 1) : ℝ) * theta α n (j + (t + 1)) + (m0 : ℝ) := by
        rw [show j + (t + 1 + 1) = j + t + 1 + 1 from by omega,
          show j + (t + 1) = j + t + 1 from by omega, hm0, hpred, hvidx]
      rw [hstep, hm1, hm2, hc]
      push_cast
      ring
  exact fun t ht => (key t).1 ht

/-- Downward half of (31). -/
lemma down_theta {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j R : ℕ) (hRj : R ≤ j) (v : ℕ → ℕ)
    (hv : ∀ t, t < 2 * R → v t = digit α (j + t - R)) :
    ∀ d, d ≤ R → ∃ m : ℤ, theta α n (j - d)
      = ((downC R v d).1 : ℝ) * theta α n j
        + ((downC R v d).2 : ℝ) * thetaPred α n j + (m : ℝ) := by
  have key : ∀ d : ℕ,
      (d ≤ R → ∃ m : ℤ, theta α n (j - d)
        = ((downC R v d).1 : ℝ) * theta α n j
          + ((downC R v d).2 : ℝ) * thetaPred α n j + (m : ℝ))
      ∧ (d + 1 ≤ R → ∃ m : ℤ, theta α n (j - (d + 1))
        = ((downC R v (d + 1)).1 : ℝ) * theta α n j
          + ((downC R v (d + 1)).2 : ℝ) * thetaPred α n j + (m : ℝ)) := by
    intro d
    induction d with
    | zero =>
      constructor
      · intro _
        refine ⟨0, ?_⟩
        have hc : downC R v 0 = ((1 : ℤ), (0 : ℤ)) := rfl
        rw [show j - 0 = j from rfl, hc]
        push_cast
        ring
      · intro hR
        refine ⟨0, ?_⟩
        have hc : downC R v (0 + 1) = ((0 : ℤ), (1 : ℤ)) := rfl
        rw [hc, thetaPred_eq_theta_sub α n j (by omega), show j - (0 + 1) = j - 1 from rfl]
        push_cast
        ring
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      intro hR
      obtain ⟨m1, hm1⟩ := ih.1 (by omega)
      obtain ⟨m2, hm2⟩ := ih.2 (by omega)
      obtain ⟨k, hk⟩ : ∃ k, j - d - 2 = k := ⟨_, rfl⟩
      have ek0 : j - (d + 1 + 1) = k := by omega
      have ek1 : j - (d + 1) = k + 1 := by omega
      have ek2 : j - d = k + 2 := by omega
      obtain ⟨m0, hm0⟩ := theta_succ_mod hα hirr n (k + 1)
      have hvidx : v (R - d - 1) = digit α (k + 1) := by
        rw [hv (R - d - 1) (by omega)]
        congr 1
        omega
      have hpred : thetaPred α n (k + 1) = theta α n k := rfl
      have hm0' : theta α n (k + 2)
          = theta α n k - (v (R - d - 1) : ℝ) * theta α n (k + 1) + (m0 : ℝ) := by
        rw [hvidx, show k + 2 = k + 1 + 1 from rfl, hm0, hpred]
      rw [ek2] at hm1
      rw [ek1] at hm2
      have hc : downC R v (d + 1 + 1)
          = ((downC R v d).1 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).1,
             (downC R v d).2 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).2) := rfl
      refine ⟨m1 + (v (R - d - 1) : ℤ) * m2 - m0, ?_⟩
      have hstep : theta α n k
          = theta α n (k + 2) + (v (R - d - 1) : ℝ) * theta α n (k + 1) - (m0 : ℝ) := by
        rw [hm0']; ring
      rw [ek0, hstep, hm1, hm2, hc]
      push_cast
      ring
  exact fun d hd => (key d).1 hd

namespace S4chars

/-- **(31)**, statement token-identical to `Kwon1002.window_character_reduction`
of `Section4.lean` (only the enclosing namespace differs, so that the two
declarations can coexist in one environment), proved. -/
theorem window_character_reduction (R : ℕ) (c : Fin (2 * R + 1) → ℤ) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R ≤ j →
        ∃ m : ℤ,
          (∑ i : Fin (2 * R + 1), (c i : ℝ) * theta α n (j + (i : ℕ) - R))
            = (A (windowWord R α j) : ℝ) * theta α n j
              + (B (windowWord R α j) : ℝ) * thetaPred α n j + (m : ℝ) := by
  refine ⟨winA R c, winB R c, ?_⟩
  intro α hirr hα n j hRj
  have hv : ∀ t, t < 2 * R → wordFn R (windowWord R α j) t = digit α (j + t - R) :=
    fun t ht => wordFn_windowWord R α j t ht
  have key : ∀ i : Fin (2 * R + 1), ∃ m : ℤ, theta α n (j + (i : ℕ) - R)
      = ((winC R (wordFn R (windowWord R α j)) (i : ℕ)).1 : ℝ) * theta α n j
        + ((winC R (wordFn R (windowWord R α j)) (i : ℕ)).2 : ℝ) * thetaPred α n j
        + (m : ℝ) := by
    intro i
    have hi := i.isLt
    by_cases h : R ≤ (i : ℕ)
    · obtain ⟨m, hm⟩ := up_theta hα hirr n j R (wordFn R (windowWord R α j)) hv
        ((i : ℕ) - R) (by omega)
      refine ⟨m, ?_⟩
      rw [show j + (i : ℕ) - R = j + ((i : ℕ) - R) from by omega, hm, winC, if_pos h]
    · obtain ⟨m, hm⟩ := down_theta hα hirr n j R hRj (wordFn R (windowWord R α j)) hv
        (R - (i : ℕ)) (by omega)
      refine ⟨m, ?_⟩
      rw [show j + (i : ℕ) - R = j - (R - (i : ℕ)) from by omega, hm, winC, if_neg h]
  choose m hm using key
  refine ⟨∑ i : Fin (2 * R + 1), c i * m i, ?_⟩
  calc (∑ i : Fin (2 * R + 1), (c i : ℝ) * theta α n (j + (i : ℕ) - R))
      = ∑ i : Fin (2 * R + 1),
          ((c i : ℝ) * ((winC R (wordFn R (windowWord R α j)) (i : ℕ)).1 : ℝ) * theta α n j
            + (c i : ℝ) * ((winC R (wordFn R (windowWord R α j)) (i : ℕ)).2 : ℝ)
                * thetaPred α n j
            + (c i : ℝ) * (m i : ℝ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hm i]; ring
    _ = (winA R c (windowWord R α j) : ℝ) * theta α n j
          + (winB R c (windowWord R α j) : ℝ) * thetaPred α n j
          + ((∑ i : Fin (2 * R + 1), c i * m i : ℤ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        simp only [winA, winB]
        push_cast
        ring

end S4chars

end

end Kwon1002
