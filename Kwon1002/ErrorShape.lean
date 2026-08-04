import Kwon1002.Prop41

/-!
# Scratch (`errshape`): the body of §4, display (30)

Target: `Kwon1002.Prop41.prop_4_1_error_shape` (the single §4-body sorry of
`Kwon1002/Prop41.lean`), and then the canonical
`Kwon1002.prop_4_1_marked_factorization` of `Kwon1002/Section4.lean`.

Both targets are reproduced **token-identically** here as
`prop_4_1_error_shape'` and `prop_4_1_marked_factorization'` (diffed against
`Kwon1002/Prop41.lean` line 303-310 and `Kwon1002/Section4.lean` line
137-144; only the name carries a prime).  Nothing is weakened.

## What this file does

The manuscript's proof of Proposition 4.1 (lines ≈ 331-404) is

> Expand both in the digit values and in the Fourier modes `v_1,…,v_r` …
> If every `v_ℓ = 0` … Repeated use of Lemma 3.2 and (25) factors its mean
> with error `L^{O_{r,D}(1)} ρ^{200H}`.  Suppose now that `v_s ≠ 0` … [(28),
> (29), Lemma 3.4] … Restoring the discarded cylinder unions, and **summing
> all polynomially many Fourier terms**, gives the uniform bound (30).

That is a *three-part* argument, and this file separates it exactly:

1. `integral_eq_sum_modeTerm`, the digit-Fourier expansion (sorried).
2. `zero_mode_factorization`, the `v = 0` branch (sorried).
3. `nonzero_mode_small`, the `v_s ≠ 0` branch (sorried).

and then **proves outright** the step the manuscript names but does not do,
namely "summing all polynomially many Fourier terms": the mode count
`card (modeTuples r D L) ≤ 3^r L^{Dr}` (`card_modeTuples_le`), the triangle
inequality that splits off the zero mode, and the arithmetic that merges the
two branches' constants into a single `(C, c, ρ)` and puts the total in the
exact shape (30) asserts, with `B = 2Dr`.  Concretely the proved half is

  `‖∫∏F − ∏mean‖ ≤ ‖T(0) − ∏mean‖ + Σ_{v≠0} ‖T(v)‖ ≤ C·L^{2Dr}·δ_n`,

`δ_n` being `Prop41.deltaScale c ρ n`, and it is what fixes the exponent `B`
of (30), the manuscript writes only `L^{O_{r,D}(1)}`.

## Also proved: the mixing input, applied at the good tuple

`good_tuple_multiblock_mixing` **consumes** the named sorried input
`Prop41.lem_3_2_conditional_multiblock_mixing` and discharges its side
conditions from the good-tuple structure, which is the manuscript's
"Repeated use of Lemma 3.2 and (25)":

* the depth is `d = 0`, and `Prop41.cylinder 0 w = Ioo 0 1` (`cylinder_zero`),
  so the conditioning is vacuous and `ν(Ioo 0 1) > 0` (`gaussMeasure_Ioo_pos`);
* the start condition `d + M ≤ t_0` is `(19)`: `j_0 ∈ J_n` gives
  `200H ≤ j_0`, hence `⌊200H⌋₊ ≤ j_0`;
* the gaps `t_{i+1} − t_i ≥ M` are `(25)`, i.e. `Prop41.goodTuple_sep`.

This is the *only* place the mixing input is actually applied; the gap
between it and `zero_mode_factorization` is named in that lemma's docstring.

## Sorried inputs consumed

* `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing` (used by
  `good_tuple_multiblock_mixing`), the manuscript's Lemma 3.2, display (17).
* the three §4-body lemmas stated in this file (each sorried, each with its
  obstruction named in its docstring).

Everything else is proved outright.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace ErrorShape

open Prop41

noncomputable section

/-! ## 1. The digit-Fourier coefficient family of (24) -/

/-- A choice of coefficient families realizing `F ℓ ∈ P_D(L)` for every
`ℓ < r`.  The body is copied verbatim from `Kwon1002.IsInPD`. -/
def RepresentsPD (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ) : Prop :=
  ∀ ℓ, ℓ < r →
    (∀ a : ℕ, ∀ v : ℤ, L ^ D < (a : ℝ) → c ℓ a v = 0) ∧
    (∀ a : ℕ, ∀ v : ℤ, L ^ D < |(v : ℝ)| → c ℓ a v = 0) ∧
    (∑' p : ℕ × ℤ, ‖c ℓ p.1 p.2‖) ≤ L ^ D ∧
    (∀ a : ℕ, ∀ θ : ℝ, F ℓ a θ = ∑' v : ℤ, c ℓ a v * torusChar ((v : ℝ) * θ))

/-- The symbol class is an existential; this picks one witness per `ℓ < r`. -/
theorem exists_representsPD (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ)
    (hF : ∀ ℓ, ℓ < r → IsInPD D L (F ℓ)) :
    ∃ c : ℕ → ℕ → ℤ → ℂ, RepresentsPD r D L F c := by
  classical
  refine ⟨fun ℓ => if h : ℓ < r then (hF ℓ h).choose else fun _ _ => 0, ?_⟩
  intro ℓ hℓ
  simp only [dif_pos hℓ]
  exact (hF ℓ hℓ).choose_spec

/-! ## 2. The Fourier modes: the box `|v_ℓ| ≤ L^D`, and how many there are

`(24)` caps every Fourier mode at `|v| ≤ L^D`, so an `r`-tuple of modes runs
over a box with `(2⌊L^D⌋ + 1)^r` points.  This is the manuscript's
"polynomially many Fourier terms", made explicit. -/

/-- `{v : ℤ | |v| ≤ L^D}` as a `Finset`. -/
def modeBox (D L : ℝ) : Finset ℤ :=
  Finset.Icc (-(⌊L ^ D⌋₊ : ℤ)) (⌊L ^ D⌋₊ : ℤ)

/-- The `r`-fold mode box `(v_1,…,v_r)`. -/
def modeTuples (r : ℕ) (D L : ℝ) : Finset (Fin r → ℤ) :=
  Fintype.piFinset (fun _ => modeBox D L)

/-- The digit-Fourier term of mode `v`: the scalar coefficient product times
the pure phase `e(Σ_ℓ v_ℓ θ_{j_ℓ})`, integrated over `α`. -/
def modeTerm (n r : ℕ) (j : ℕ → ℕ) (c : ℕ → ℕ → ℤ → ℂ) (v : Fin r → ℤ) : ℂ :=
  ∫ α in Ioo (0 : ℝ) 1,
    (∏ ℓ : Fin r, c (ℓ : ℕ) (digit α (j ℓ)) (v ℓ)) *
      torusChar (∑ ℓ : Fin r, (v ℓ : ℝ) * theta α n (j ℓ))

theorem card_modeBox (D L : ℝ) :
    ((modeBox D L).card : ℤ) = 2 * (⌊L ^ D⌋₊ : ℤ) + 1 := by
  have hk : (0 : ℤ) ≤ (⌊L ^ D⌋₊ : ℤ) := Int.natCast_nonneg _
  have h := Int.card_Icc_of_le (a := -(⌊L ^ D⌋₊ : ℤ)) (b := (⌊L ^ D⌋₊ : ℤ)) (by omega)
  rw [modeBox, h]
  ring

theorem card_modeTuples (r : ℕ) (D L : ℝ) :
    (modeTuples r D L).card = (modeBox D L).card ^ r :=
  Fintype.card_piFinset_const _ _

/-- **"Polynomially many Fourier terms."**  For `L ≥ 1` the number of
`r`-tuples of admissible modes is at most `3^r L^{Dr}`. -/
theorem card_modeTuples_le (r : ℕ) (D L : ℝ) (hL : 1 ≤ L) (hD : 0 ≤ D) :
    ((modeTuples r D L).card : ℝ) ≤ 3 ^ r * L ^ (D * r) := by
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL
  have hLD : (1 : ℝ) ≤ L ^ D := Real.one_le_rpow hL hD
  have hbox : ((modeBox D L).card : ℝ) ≤ 3 * L ^ D := by
    have h1 : ((modeBox D L).card : ℤ) = 2 * (⌊L ^ D⌋₊ : ℤ) + 1 := card_modeBox D L
    have h2 : ((modeBox D L).card : ℝ) = 2 * ((⌊L ^ D⌋₊ : ℕ) : ℝ) + 1 := by
      exact_mod_cast h1
    have h3 : ((⌊L ^ D⌋₊ : ℕ) : ℝ) ≤ L ^ D := Nat.floor_le (by linarith)
    rw [h2]; linarith
  have hcast : ((modeTuples r D L).card : ℝ) = ((modeBox D L).card : ℝ) ^ r := by
    rw [card_modeTuples]; push_cast; ring
  rw [hcast]
  have hstep : ((modeBox D L).card : ℝ) ^ r ≤ (3 * L ^ D) ^ r := by
    gcongr
  refine le_trans hstep (le_of_eq ?_)
  rw [mul_pow, ← Real.rpow_natCast (L ^ D) r, ← Real.rpow_mul hL0]

/-- **The mode box loses nothing.**  `(24)` kills every coefficient with
`|v| > L^D`, and `v ∉ modeBox D L` forces `|v| ≥ ⌊L^D⌋ + 1 > L^D`.  This is
what makes the *finite* sum of `integral_eq_sum_modeTerm` below the whole
Fourier expansion rather than a truncation of it. -/
theorem coeff_eq_zero_of_notMem_modeBox (r : ℕ) (D L : ℝ) (F : ℕ → ℕ → ℝ → ℂ)
    (c : ℕ → ℕ → ℤ → ℂ) (hc : RepresentsPD r D L F c) (ℓ : ℕ) (hℓ : ℓ < r)
    (a : ℕ) (v : ℤ) (hv : v ∉ modeBox D L) : c ℓ a v = 0 := by
  refine (hc ℓ hℓ).2.1 a v ?_
  rw [modeBox, Finset.mem_Icc] at hv
  push_neg at hv
  have hint : ((⌊L ^ D⌋₊ : ℤ)) + 1 ≤ |v| := by
    rcases lt_or_ge v (-(⌊L ^ D⌋₊ : ℤ)) with h | h
    · rw [abs_of_nonpos (by omega)]; omega
    · have h2 := hv h
      rw [abs_of_nonneg (by omega)]; omega
  have hR : ((⌊L ^ D⌋₊ : ℕ) : ℝ) + 1 ≤ |(v : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hint
  have hfl : L ^ D < (⌊L ^ D⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one (L ^ D)
  linarith

/-! ## 3. The three §4-body inputs (sorried, one per manuscript step) -/

/-- **Step 1: the digit-Fourier expansion.**  Manuscript: "Expand both in the
digit values and in the Fourier modes `v_1,…,v_r`, and pull out the scalar
coefficient of each digit-Fourier term."

Since `(24)` makes every coefficient family finitely supported in `v`, the
expansion is a *finite* sum over `modeTuples r D L`.

**Obstruction.**  Interchanging the (absolutely convergent) Fourier `tsum`
with the integral over `α`, and expanding the `r`-fold product of `tsum`s.
Absolute convergence is exactly the `ℓ¹` mass `L^{Dr}` of `(24)`; the
interchange is dominated convergence plus `tsum_prod`.  Nothing here is
specific to §4, it is the analytic bookkeeping the manuscript compresses
into one sentence. -/
theorem integral_eq_sum_modeTerm (n r : ℕ) (D : ℝ) (j : ℕ → ℕ)
    (F : ℕ → ℕ → ℝ → ℂ) (c : ℕ → ℕ → ℤ → ℂ)
    (hc : RepresentsPD r D (Lnorm n) F c) :
    (∫ α in Ioo (0 : ℝ) 1,
        ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
      = ∑ v ∈ modeTuples r D (Lnorm n), modeTerm n r j c v := by
  sorry

/-- **Step 2: the zero mode.**  Manuscript: "If every `v_ℓ = 0`, the integrand
is a product of digit functions.  Repeated use of Lemma 3.2 and (25) factors
its mean with error `L^{O_{r,D}(1)} ρ^{200H}`."

**Obstruction** (three named gaps, all downstream of
`good_tuple_multiblock_mixing` below, which *does* apply Lemma 3.2 at the
good tuple's gap structure):

* Lebesgue `dα` on `(0,1)` versus Gauss `dν`: Kwon's (27) integrates `dα` but
  Lemma 3.2 is a `ν`-statement.  Since `j_1 ≥ 200H`, Gauss-Kuzmin transfers
  one to the other at cost `ρ^{200H}`, which is the same order as the mixing
  error and so does not change the shape.
* complex versus real observables: Lemma 3.2 is stated for real `g_i`; the
  zero-mode integrand is `∏_ℓ c_ℓ(a_{j_ℓ}, 0)`, so it must be split into real
  and imaginary parts (a factor `2^r` in `C`).
* the `BV` bound on the digit observable `x ↦ c_ℓ(a_1(x), 0)`: it is a step
  function with at most `L^D` jumps, so `‖·‖_BV ≤ 2 L^D`, but
  `eVariationOn` of a countably-supported step function is not in Mathlib. -/
theorem zero_mode_factorization (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
        ‖modeTerm n r j c 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (D * r) * ρ ^ (200 * Hscale n) := by
  sorry

/-- **Step 3: a nonzero mode.**  Manuscript: "Suppose now that `v_s ≠ 0` and
`v_ℓ = 0` for `ℓ > s`", then (28) pins the frequency between `q_{j_s}/2` and
`2L^D q_{j_s}`, the three local complete-cylinder cuts at depths `j_s`, `k_-`,
`k_+` discard `O(e^{-cL^{1/2}})` by (20), (29) holds on what is retained,
`good_avoids_resonance_window` places the post-resonance digit factors `100H`
clear of the window so Lemma 3.2 replaces them by their stationary means at
cost `L^{O(1)}(e^{-cH} + ρ^{cH})`, and Lemma 3.4
(`Kwon1002.descendant_phase_small`) kills each depth-`(j_s+1)` prefix at cost
`O(e^{-cH})`.

**Obstruction.**  This is the substantive half of §4 and needs, in addition
to Lemma 3.2: the Fibonacci lower bound on continuants feeding (28); the
large-deviation estimate (20) for `log q_j`; and display (22), the
oscillatory half of Lemma 3.4, which is *not yet stated* anywhere in
`Kwon1002/` (see the blind-audit finding). -/
theorem nonzero_mode_small (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ C c₀ ρ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, ∀ c : ℕ → ℕ → ℤ → ℂ,
        RepresentsPD r D (Lnorm n) F c →
      ∀ v ∈ modeTuples r D (Lnorm n), v ≠ 0 →
        ‖modeTerm n r j c v‖
          ≤ C * (Lnorm n) ^ (D * r) *
              (Real.exp (-c₀ * Real.sqrt (Lnorm n)) + Real.exp (-c₀ * Hscale n)
                + ρ ^ (c₀ * Hscale n)) := by
  sorry

/-! ## 4. Merging the two branches into the single bracket of (30)

The two branches come with independent mixing/deviation constants.  (30)
carries one `c` and one `ρ`; these two lemmas do the merge, with
`c = min c₃ 200` and `ρ = max ρ₂ ρ₃`.

**Finding (the implicit upper constraint on `c` in (30)).**  The zero-mode
branch of the manuscript produces the error `ρ^{200H}` (from (25)), while
(30) writes the bracket as `e^{-cL^{1/2}} + e^{-cH} + ρ^{cH}`.  For the
former to sit inside the latter one needs `c ≤ 200`, see the hypothesis
`hc200` of `zero_branch_le_deltaScale`.  The manuscript never says this;
`c` is introduced only as "the" mixing/deviation constant, and elsewhere
(Prop 4.2, referee cosmetic item 5) it carries a *different* upper
constraint (`c` with `3δ` below `80λ ≈ 94.9`).  Both constraints are upper
ones and are compatible, so the existential quantification over `c` in (30)
absorbs them; but the reader has to supply them. -/

theorem deltaScale_nonneg {c ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : 0 ≤ deltaScale c ρ n := by
  have h1 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have h2 : (0 : ℝ) < Real.exp (-c * Hscale n) := Real.exp_pos _
  have h3 : (0 : ℝ) < ρ ^ (c * Hscale n) := Real.rpow_pos_of_pos hρ _
  unfold deltaScale
  linarith

/-- The zero-mode error `ρ₂^{200H}` sits inside the bracket of (30), provided
`c ≤ 200` and `ρ₂ ≤ ρ`. -/
theorem zero_branch_le_deltaScale {c ρ ρ₂ : ℝ} (n : ℕ)
    (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (hρ : ρ₂ ≤ ρ)
    (hc0 : 0 < c) (hc200 : c ≤ 200) (hH : 0 ≤ Hscale n) :
    ρ₂ ^ (200 * Hscale n) ≤ deltaScale c ρ n := by
  have hexp : c * Hscale n ≤ 200 * Hscale n := by nlinarith
  have e1 : ρ₂ ^ (200 * Hscale n) ≤ ρ₂ ^ (c * Hscale n) :=
    Real.rpow_le_rpow_of_exponent_ge hρ₂0 hρ₂1.le hexp
  have e2 : ρ₂ ^ (c * Hscale n) ≤ ρ ^ (c * Hscale n) :=
    Real.rpow_le_rpow hρ₂0.le hρ (by nlinarith)
  have h1 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have h2 : (0 : ℝ) < Real.exp (-c * Hscale n) := Real.exp_pos _
  unfold deltaScale
  linarith

/-- The nonzero-mode bracket sits inside the bracket of (30), provided
`c ≤ c₃` and `ρ₃ ≤ ρ`. -/
theorem nonzero_branch_le_deltaScale {c ρ c₃ ρ₃ : ℝ} (n : ℕ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρ₃0 : 0 < ρ₃) (hρ₃ : ρ₃ ≤ ρ)
    (hc0 : 0 < c) (hcc : c ≤ c₃) (hH : 0 ≤ Hscale n) :
    Real.exp (-c₃ * Real.sqrt (Lnorm n)) + Real.exp (-c₃ * Hscale n)
        + ρ₃ ^ (c₃ * Hscale n)
      ≤ deltaScale c ρ n := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Lnorm n) := Real.sqrt_nonneg _
  have e1 : Real.exp (-c₃ * Real.sqrt (Lnorm n)) ≤ Real.exp (-c * Real.sqrt (Lnorm n)) := by
    apply Real.exp_le_exp.2; nlinarith
  have e2 : Real.exp (-c₃ * Hscale n) ≤ Real.exp (-c * Hscale n) := by
    apply Real.exp_le_exp.2; nlinarith
  have e3 : ρ₃ ^ (c₃ * Hscale n) ≤ ρ ^ (c * Hscale n) := by
    have h1 : ρ₃ ^ (c₃ * Hscale n) ≤ ρ ^ (c₃ * Hscale n) :=
      Real.rpow_le_rpow hρ₃0.le hρ₃ (by nlinarith)
    have h2 : ρ ^ (c₃ * Hscale n) ≤ ρ ^ (c * Hscale n) :=
      Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le (by nlinarith)
    linarith
  unfold deltaScale
  linarith

/-! ## 5. Display (30): the assembly

This is the manuscript's "summing all polynomially many Fourier terms", and
it is proved outright from the three inputs above. -/

/-- **Display (30).**  Statement reproduced token-identically from
`Kwon1002.Prop41.prop_4_1_error_shape`; the exponent `B` produced here is
`2Dr`, which the manuscript leaves as `O_{r,D}(1)`.

**On the value `2Dr`.**  The manuscript's own bookkeeping is sharper: it
factors the `ℓ¹` mass `L^{Dr}` out of the *whole* mode sum once, giving
`B = Dr`.  The split used here restates each single-mode bound with the full
`ℓ¹` mass `L^{Dr}` (rather than with that mode's own coefficient product)
and then multiplies by the mode count `3^r L^{Dr}`, so it pays `L^{Dr}`
twice.  That is a deliberate looseness: it keeps the two sorried branch
lemmas free of any per-mode coefficient bookkeeping, and (30) only ever
asks for *some* polynomial weight, which `prop_4_1_marked_factorization'`
then converts into `O_A(L^{-A})` regardless of `B`. -/
theorem prop_4_1_error_shape' (r : ℕ) (D : ℝ) (hD : 0 < D) :
    ∃ B C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ B * deltaScale c ρ n := by
  classical
  obtain ⟨C₂, ρ₂, hC₂, hρ₂0, hρ₂1, h2⟩ := zero_mode_factorization r D hD
  obtain ⟨C₃, c₃, ρ₃, hC₃, hc₃, hρ₃0, hρ₃1, h3⟩ := nonzero_mode_small r D hD
  have hc0 : (0 : ℝ) < min c₃ 200 := lt_min hc₃ (by norm_num)
  have hr0 : (0 : ℝ) < max ρ₂ ρ₃ := lt_of_lt_of_le hρ₂0 (le_max_left _ _)
  have hr1 : max ρ₂ ρ₃ < 1 := max_lt hρ₂1 hρ₃1
  refine ⟨2 * D * r, C₂ + 3 ^ r * C₃, min c₃ 200, max ρ₂ ρ₃,
    add_pos hC₂ (mul_pos (by positivity) hC₃), hc0, hr0, hr1, ?_⟩
  have hLtend : Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h2, h3, hLtend.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn2 hn3 hL1
  intro j hj F hF
  obtain ⟨cc, hcc⟩ := exists_representsPD r D (Lnorm n) F hF
  -- scale facts
  have hL0 : (0 : ℝ) < Lnorm n := lt_of_lt_of_le zero_lt_one hL1
  have hH1 : (1 : ℝ) ≤ Hscale n := by
    rw [Hscale]; exact Real.one_le_rpow hL1 (by norm_num)
  have hH0 : (0 : ℝ) ≤ Hscale n := le_trans zero_le_one hH1
  have hX1 : (1 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) :=
    Real.one_le_rpow hL1 (by positivity)
  have hX0 : (0 : ℝ) ≤ (Lnorm n) ^ (D * (r : ℝ)) := le_trans zero_le_one hX1
  have hY : (Lnorm n) ^ (2 * D * (r : ℝ))
      = (Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  have hδ0 : (0 : ℝ) ≤ deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := deltaScale_nonneg hr0 n
  -- the two branch bounds, both put in the bracket of (30)
  have hA : ‖modeTerm n r j cc 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C₂ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    refine le_trans (hn2 j hj F cc hcc) ?_
    have hbr := zero_branch_le_deltaScale (c := min c₃ 200) (ρ := max ρ₂ ρ₃) (ρ₂ := ρ₂)
      n hρ₂0 hρ₂1 (le_max_left _ _) hc0 (min_le_right _ _) hH0
    have hpos : (0 : ℝ) ≤ C₂ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hbr hpos
  have hBnd : ∀ v ∈ (modeTuples r D (Lnorm n)).erase 0,
      ‖modeTerm n r j cc v‖
        ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    intro v hv
    rcases Finset.mem_erase.1 hv with ⟨hv0, hvmem⟩
    refine le_trans (hn3 j hj F cc hcc v hvmem hv0) ?_
    have hbr := nonzero_branch_le_deltaScale (c := min c₃ 200) (ρ := max ρ₂ ρ₃)
      (c₃ := c₃) (ρ₃ := ρ₃) n hr0 hr1 hρ₃0 (le_max_right _ _) hc0 (min_le_left _ _) hH0
    have hpos : (0 : ℝ) ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hbr hpos
  -- the mode count
  have hcardS : (((modeTuples r D (Lnorm n)).erase 0).card : ℝ)
      ≤ 3 ^ r * (Lnorm n) ^ (D * (r : ℝ)) := by
    refine le_trans ?_ (card_modeTuples_le r D (Lnorm n) hL1 hD.le)
    exact_mod_cast Finset.card_erase_le
  have hsum : ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, ‖modeTerm n r j cc v‖
      ≤ (3 ^ r * (Lnorm n) ^ (D * (r : ℝ))) *
          (C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hBnd) ?_
    rw [nsmul_eq_mul]
    have hb0 : (0 : ℝ)
        ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
      have : (0 : ℝ) ≤ C₃ * (Lnorm n) ^ (D * (r : ℝ)) := by positivity
      exact mul_nonneg this hδ0
    exact mul_le_mul_of_nonneg_right hcardS hb0
  -- the split
  have h0mem : (0 : Fin r → ℤ) ∈ modeTuples r D (Lnorm n) := by
    rw [modeTuples, Fintype.mem_piFinset]
    intro i
    have hzero : (0 : Fin r → ℤ) i = 0 := rfl
    rw [hzero, modeBox, Finset.mem_Icc]
    exact ⟨neg_nonpos.2 (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  rw [integral_eq_sum_modeTerm n r D j F cc hcc,
    ← Finset.add_sum_erase _ (modeTerm n r j cc) h0mem]
  have hrw : (modeTerm n r j cc 0
        + ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, modeTerm n r j cc v)
      - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)
      = (modeTerm n r j cc 0 - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ))
        + ∑ v ∈ (modeTuples r D (Lnorm n)).erase 0, modeTerm n r j cc v := by
    ring
  rw [hrw]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add le_rfl (norm_sum_le _ _)) ?_
  refine le_trans (add_le_add hA hsum) ?_
  -- final arithmetic: `C₂ X Δ + 3^r X (C₃ X Δ) ≤ (C₂ + 3^r C₃) X² Δ`
  rw [hY]
  have hXX : (Lnorm n) ^ (D * (r : ℝ))
      ≤ (Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)) := by
    nlinarith
  have hstep : C₂ * (Lnorm n) ^ (D * (r : ℝ)) * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n
      ≤ C₂ * ((Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ)))
          * deltaScale (min c₃ 200) (max ρ₂ ρ₃) n := by
    have h1 : C₂ * (Lnorm n) ^ (D * (r : ℝ))
        ≤ C₂ * ((Lnorm n) ^ (D * (r : ℝ)) * (Lnorm n) ^ (D * (r : ℝ))) :=
      mul_le_mul_of_nonneg_left hXX hC₂.le
    exact mul_le_mul_of_nonneg_right h1 hδ0
  nlinarith [hδ0, hX0, hC₃.le]

/-! ## 6. Proposition 4.1 -/

/-- **Proposition 4.1** (Marked factorization), display (27).

Statement reproduced token-identically from
`Kwon1002/Section4.lean` (`Kwon1002.prop_4_1_marked_factorization`); proved
from `prop_4_1_error_shape'` and the fully proved `O_A(L^{-A})` reduction
`Prop41.eventually_rpow_mul_deltaScale_le`. -/
theorem prop_4_1_marked_factorization' (r : ℕ) (D A : ℝ) (hD : 0 < D) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ → ℕ, GoodTuple n r j →
      ∀ F : ℕ → ℕ → ℝ → ℂ, (∀ ℓ, ℓ < r → IsInPD D (Lnorm n) (F ℓ)) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
            - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
          ≤ C * (Lnorm n) ^ (-A) := by
  obtain ⟨B, C, c, ρ, hC, hc, hρ0, hρ1, hbd⟩ := prop_4_1_error_shape' r D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbd, eventually_rpow_mul_deltaScale_le A B c ρ hc hρ0 hρ1]
    with n hn harith j hj F hF
  calc ‖(∫ α in Ioo (0 : ℝ) 1,
            ∏ ℓ ∈ Finset.range r, F ℓ (digit α (j ℓ)) (theta α n (j ℓ)))
          - ∏ ℓ ∈ Finset.range r, stationaryMean (F ℓ)‖
      ≤ C * (Lnorm n) ^ B * deltaScale c ρ n := hn j hj F hF
    _ = C * ((Lnorm n) ^ B * deltaScale c ρ n) := by ring
    _ ≤ C * (Lnorm n) ^ (-A) := mul_le_mul_of_nonneg_left harith hC.le

/-! ## 7. The mixing input, applied at the good tuple's gap structure

This is the one place `Prop41.lem_3_2_conditional_multiblock_mixing` is
actually used.  It is the manuscript's "Repeated use of Lemma 3.2 and (25)",
with every side condition of (17) discharged from `GoodTuple`. -/

/-- The depth-`0` cylinder is all of `(0,1)`: the conditioning is vacuous. -/
theorem cylinder_zero (w : ℕ → ℕ) : cylinder 0 w = Ioo (0 : ℝ) 1 := by
  ext α
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- `ν(0,1) > 0`, which is the positivity side condition of (17) at `d = 0`. -/
theorem gaussMeasure_Ioo_pos : 0 < (Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1)).toReal := by
  have hsub : Ioc (0 : ℝ) (1 / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have h1 : Erdos1002.gaussMeasure.real (Ioc (0 : ℝ) (1 / 2))
      = (Real.log (1 + 1 / 2) - Real.log (1 + 0)) / Real.log 2 :=
    Erdos1002.gaussMeasure_real_Ioc le_rfl (by norm_num) (by norm_num)
  have h2 : 0 < Erdos1002.gaussMeasure.real (Ioc (0 : ℝ) (1 / 2)) := by
    rw [h1]
    have e : (1 : ℝ) + 0 = 1 := by norm_num
    rw [e, Real.log_one, sub_zero]
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have h3 : Erdos1002.gaussMeasure.real (Ioc (0 : ℝ) (1 / 2))
      ≤ Erdos1002.gaussMeasure.real (Ioo (0 : ℝ) 1) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have h4 : Erdos1002.gaussMeasure.real (Ioo (0 : ℝ) 1)
      = (Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1)).toReal := measureReal_def _ _
  linarith [h4 ▸ h3]

/-- **Lemma 3.2 applied at a good tuple.**  `d = 0`, `M = ⌊200H⌋₊`, `s = r`,
`t = j`.  The start condition of (17) is `(19)` (`j_1 ∈ J_n`, so `200H ≤ j_1`)
and the gap condition is `(25)` (`Prop41.goodTuple_sep`).

Consumes the sorried `Prop41.lem_3_2_conditional_multiblock_mixing`. -/
theorem good_tuple_multiblock_mixing (r : ℕ) (hr : 0 < r) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (j : ℕ → ℕ), GoodTuple n r j →
      ∀ (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K → (∀ i, i < r → BVBoundedBy K (g i)) →
        |(∫ α in Ioo (0 : ℝ) 1, ∏ i ∈ Finset.range r, g i (gaussIter α (j i))
              ∂Erdos1002.gaussMeasure)
              / (Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1)).toReal
            - ∏ i ∈ Finset.range r, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ C * ρ ^ (⌊200 * Hscale n⌋₊) * K ^ r := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, h⟩ := lem_3_2_conditional_multiblock_mixing r
  refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
  intro n j hj g K hK hg
  have hcyl : cylinder 0 (fun _ => 0) = Ioo (0 : ℝ) 1 := cylinder_zero _
  -- (19): `j_1 ∈ J_n` forces `200H ≤ j_1`, hence `⌊200H⌋₊ ≤ j_1`
  have hmemJ : j 0 ∈ bulkJ n := hj.1.2.2 0 hr
  have hge : 200 * Hscale n ≤ ((j 0 : ℕ) : ℝ) := ((Finset.mem_filter.1 hmemJ).2).1
  have hstart : 0 + ⌊200 * Hscale n⌋₊ ≤ j 0 := by
    have h1 : ⌊200 * Hscale n⌋₊ ≤ ⌊((j 0 : ℕ) : ℝ)⌋₊ := Nat.floor_mono hge
    rw [Nat.floor_natCast] at h1
    omega
  -- (25): the gaps
  have hgap : ∀ i, i + 1 < r → j i + ⌊200 * Hscale n⌋₊ ≤ j (i + 1) := fun i hi =>
    goodTuple_sep n r j hj i hi
  have hpos : 0 < (Erdos1002.gaussMeasure (cylinder 0 (fun _ => 0))).toReal := by
    rw [hcyl]; exact gaussMeasure_Ioo_pos
  have hmain := h 0 (⌊200 * Hscale n⌋₊) (fun _ => 0) j g K hK hg hstart hgap hpos
  rwa [hcyl] at hmain

end

end ErrorShape

end Kwon1002

