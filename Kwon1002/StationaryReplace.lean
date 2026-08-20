import Kwon1002.LDMain

/-!
# Step 2 of the nonzero-mode chain: the stationary-mean replacement

The three-step chain of `ZeroMode.nonzero_mode_three_step` reads, after the
retained-cylinder cut (step 1, unconditional since
`LargeDeviation.nonzero_mode_cut_unconditional`): on each retained
depth-`k₊` cylinder, replace the post-resonance digit factors by their
stationary Gauss means, at cost `L^{O_{r,D}(1)}(e^{-cH} + ρ^{cH})` per unit
of cylinder mass, plus the restoration of the discarded depth-`k₊`
cylinders at cost `L^{O_{r,D}(1)} e^{-cL^{1/2}}`.  This file builds the
machinery of that replacement:

* §1 **the phase is Lipschitz**: `‖e(a) - e(b)‖ ≤ 2π|a-b|`
  (`norm_torusChar_sub_le`), the quantitative form of the manuscript's
  "phase freezing" when combined with the cylinder-diameter bound
  `CylinderPhase.abs_sub_mul_denom_sq_le_one`;
* §2 **prefix continuants**: the word continuant of a prefix is the frozen
  continuant at the prefix depth (`wordDenom_take_of_mem_halfOpen`), and
  the word continuant is Wang's terminal continuant denominator
  (`wordDenom_eq_cfTerminalDenominator`), the currency of display (22);
* §3 **the three-cut retained family** (`retainedWords`): the manuscript's
  three local complete-cylinder cuts at depths `j_s`, `k₋`, `k₊`, realised
  as one family of depth-`k₊` words filtered on the three prefix
  continuants, with the display-(20) mass bound for the discard
  (`volume_discarded_retainedWords_le`) and the saturation property that
  drives the v8 restoration step (`mem_retainedWords_of_window`);
* §4 **the Lebesgue-conditional mean replacement on a cylinder**
  (`abs_setIntegral_prod_sub_le`, real form;
  `norm_setIntegral_future_sub_le`, complex form): for BV digit
  observables read at times `≥ M` past the cylinder depth,
  `∫_{I_w} ∏ g dλ = λ(I_w) ∏ ∫ g dν + O(ν(I_w)(ρ^M + diam(I_w)))`.
  The route is the one recorded in the reconciliation: Gauss-conditional
  mixing (`MixingBV.lem_3_2_conditional_multiblock_mixing'`) transported
  to Lebesgue *not* through a second transfer-operator argument but
  through the observation that the density `dλ/dν = log 2·(1+x)` is
  `log 2`-Lipschitz, hence constant to order `diam(I_w)` on the cylinder;
  the two `2^F` complex-to-real expansions are `ZeroMode.prod_complex_expand`.

Everything here is proved outright; no `sorry` and no new axioms.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace StationaryReplace

open Prop41 ErrorShape ZeroMode RetainedCut

noncomputable section

/-! ## 1. The phase is Lipschitz -/

/-- `‖e^{ix} - e^{iy}‖ ≤ |x - y|`, by the fundamental theorem of calculus
along the arc. -/
theorem norm_exp_I_sub_exp_I (x y : ℝ) :
    ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ ≤ |x - y| := by
  have key : ∀ u v : ℝ, u ≤ v →
      ‖Complex.exp (v * Complex.I) - Complex.exp (u * Complex.I)‖ ≤ |v - u| := by
    intro u v huv
    have hderiv : ∀ t ∈ Set.uIcc u v,
        HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
          (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ) * Complex.I)) Complex.I t := by
        have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
          simpa using Complex.ofRealCLM.hasDerivAt (x := t)
        simpa using h0.mul_const Complex.I
      simpa using h1.cexp
    have hcont : Continuous fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * Complex.I :=
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const
    have hint : IntervalIntegrable
        (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * Complex.I) volume u v :=
      hcont.intervalIntegrable u v
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hbd : ∀ t ∈ Set.Ioc (min u v) (max u v),
        ‖Complex.exp ((t : ℂ) * Complex.I) * Complex.I‖ ≤ 1 := by
      intro t _
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_exp_ofReal_mul_I]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) hbd
    rw [heq] at hnorm
    calc ‖Complex.exp ((v : ℂ) * Complex.I) - Complex.exp ((u : ℂ) * Complex.I)‖
        ≤ 1 * |v - u| := hnorm
      _ = |v - u| := one_mul _
  rcases le_total y x with h | h
  · exact key y x h
  · have := key x y h
    rwa [norm_sub_rev, abs_sub_comm] at this

/-- **The torus character is `2π`-Lipschitz**: `‖e(a) - e(b)‖ ≤ 2π|a - b|`. -/
theorem norm_torusChar_sub_le (a b : ℝ) :
    ‖torusChar a - torusChar b‖ ≤ 2 * Real.pi * |a - b| := by
  have hrw : ∀ t : ℝ, torusChar t
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    intro t
    unfold torusChar
    congr 1
    push_cast
    ring
  rw [hrw a, hrw b]
  have h := norm_exp_I_sub_exp_I (2 * Real.pi * a) (2 * Real.pi * b)
  calc ‖Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I)‖
      ≤ |2 * Real.pi * a - 2 * Real.pi * b| := h
    _ = 2 * Real.pi * |a - b| := by
        rw [show 2 * Real.pi * a - 2 * Real.pi * b = 2 * Real.pi * (a - b) by ring,
          abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

/-! ## 2. Prefix continuants of a retained word -/

/-- The first `m` digits of the depth-`d` digit word are the depth-`m`
digit word. -/
theorem digitWordOf_take (α : ℝ) {m d : ℕ} (h : m ≤ d) :
    (digitWordOf α d).take m = digitWordOf α m := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_take, digitWordOf_getElem, digitWordOf_getElem]

/-- On the cylinder of a positive word `w` of length `d`, the continuant at
any depth `m ≤ d` is frozen: it is the word continuant of the prefix
`w.take m`. -/
theorem denom_eq_wordDenom_take {w : List ℕ} {d : ℕ} (hlen : w.length = d)
    (hpos : ∀ a ∈ w, 0 < a) {α : ℝ}
    (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w) (hirr : Irrational α)
    (hd0 : 0 < d) {m : ℕ} (hm : m ≤ d) :
    (denom α m : ℝ) = (wordDenom (w.take m) : ℝ) := by
  have hwne : w ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
    omega
  have hαIoo : α ∈ Ioo (0 : ℝ) 1 := mem_Ioo_of_mem_halfOpen hwne hpos hα hirr
  have hdig := digit_eq_of_mem_halfOpen hαIoo hirr hα
  have hword : w = digitWordOf α d := eq_digitWordOf_of_digits hlen hdig
  rw [hword, digitWordOf_take α hm, wordDenom_digitWordOf]

/-- The fold continuant agrees with the Möbius matrix continuant pair. -/
theorem wordDenomPair_eq_quad (w : List ℕ) :
    ((wordDenomPair w).1 : ℤ) = qD w ∧ ((wordDenomPair w).2 : ℤ) = qC w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton w a ih =>
      obtain ⟨h1, h2⟩ := ih
      have hstep : wordDenomPair (w ++ [a]) = denomStep (wordDenomPair w) a := by
        unfold wordDenomPair
        rw [List.foldl_append]
        rfl
      obtain ⟨hqA, hqB, hqC, hqD⟩ := Kwon1002.quad_append w [a]
      have ha1 : qB ([a] : List ℕ) = 1 := by simp
      have ha2 : qD ([a] : List ℕ) = (a : ℤ) := by simp
      have ha3 : qA ([a] : List ℕ) = 0 := by simp
      have ha4 : qC ([a] : List ℕ) = 1 := by simp
      constructor
      · rw [hstep]
        show (((a * (wordDenomPair w).1 + (wordDenomPair w).2 : ℕ)) : ℤ) = qD (w ++ [a])
        rw [hqD, ha1, ha2]
        push_cast
        rw [h1, h2]
        ring
      · rw [hstep]
        show (((wordDenomPair w).1 : ℤ)) = qC (w ++ [a])
        rw [hqC, ha3, ha4, h1]
        ring

/-- **The fold continuant is Wang's terminal continuant denominator**, the
quantity display (22) reads on the descendants. -/
theorem wordDenom_eq_cfTerminalDenominator (w : List ℕ) :
    wordDenom w = Erdos1002.cfTerminalDenominator w := by
  have h1 : ((wordDenomPair w).1 : ℤ) = qD w := (wordDenomPair_eq_quad w).1
  have h2 : ((Erdos1002.cfTerminalDenominator w : ℕ) : ℤ) = qD w :=
    (Kwon1002.cfTerminal_eq_quad w).2
  have : ((wordDenom w : ℕ) : ℤ) = ((Erdos1002.cfTerminalDenominator w : ℕ) : ℤ) := by
    rw [wordDenom, h1, h2]
  exact_mod_cast this

/-! ## 3. The three-cut retained family

The manuscript makes three *local complete-cylinder cuts*, at depths `j_s`,
`k₋`, `k₊`: retain the window `e^{λj_s ± δH}` at `j_s`, the upper cut
`q_{k₋} ≤ e^{λk₋+δH}` at `k₋`, and the lower cut `q_{k₊} ≥ e^{λk₊-δH}` at
`k₊`.  Every cut is determined by the digits below `k₊`, so the retained
set is a union of complete depth-`k₊` cylinders; `retainedWords` is that
word family, obtained by filtering the digit box on the three *prefix*
word continuants.  (The upper window at `k₊` is also kept: it is what caps
the digits and makes the family finite.) -/

open scoped Classical in
/-- The three-cut retained family: depth-`d₃` positive words whose prefix
continuants obey the Lévy window at `d₁`, the upper cut at `d₂` and the
two-sided window at `d₃`. -/
def retainedWords (n d₁ d₂ d₃ : ℕ) (δ : ℝ) : Finset (List ℕ) :=
  ((Fintype.piFinset (fun _ : Fin d₃ =>
      Finset.Icc 1 ⌊Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n)⌋₊)).image
    (fun f => List.ofFn f)).filter
  (fun w =>
    (Real.exp (lyapunov * (d₁ : ℝ) - δ * Hscale n) ≤ (wordDenom (w.take d₁) : ℝ)
      ∧ (wordDenom (w.take d₁) : ℝ) ≤ Real.exp (lyapunov * (d₁ : ℝ) + δ * Hscale n))
    ∧ (wordDenom (w.take d₂) : ℝ) ≤ Real.exp (lyapunov * (d₂ : ℝ) + δ * Hscale n)
    ∧ (Real.exp (lyapunov * (d₃ : ℝ) - δ * Hscale n) ≤ (wordDenom w : ℝ)
      ∧ (wordDenom w : ℝ) ≤ Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n)))

/-- Membership in the digit box, characterised. -/
theorem mem_wordBox_iff {d M : ℕ} {w : List ℕ} :
    w ∈ (Fintype.piFinset (fun _ : Fin d => Finset.Icc 1 M)).image
        (fun f => List.ofFn f)
      ↔ w.length = d ∧ ∀ a ∈ w, 1 ≤ a ∧ a ≤ M := by
  constructor
  · intro hw
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hw
    rw [Fintype.mem_piFinset] at hf
    refine ⟨by simp, ?_⟩
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    have := Finset.mem_Icc.mp (hf i)
    omega
  · rintro ⟨hlen, hbox⟩
    rw [Finset.mem_image]
    refine ⟨fun i : Fin d => w[(i : ℕ)]'(by omega), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      exact hbox _ (List.getElem_mem _)
    · apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp

open scoped Classical in
/-- Membership in the retained family, characterised. -/
theorem mem_retainedWords_iff {n d₁ d₂ d₃ : ℕ} {δ : ℝ} {w : List ℕ} :
    w ∈ retainedWords n d₁ d₂ d₃ δ
      ↔ (w.length = d₃
          ∧ ∀ a ∈ w, 1 ≤ a ∧ a ≤ ⌊Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n)⌋₊)
        ∧ ((Real.exp (lyapunov * (d₁ : ℝ) - δ * Hscale n) ≤ (wordDenom (w.take d₁) : ℝ)
            ∧ (wordDenom (w.take d₁) : ℝ) ≤ Real.exp (lyapunov * (d₁ : ℝ) + δ * Hscale n))
          ∧ (wordDenom (w.take d₂) : ℝ) ≤ Real.exp (lyapunov * (d₂ : ℝ) + δ * Hscale n)
          ∧ (Real.exp (lyapunov * (d₃ : ℝ) - δ * Hscale n) ≤ (wordDenom w : ℝ)
            ∧ (wordDenom w : ℝ) ≤ Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n))) := by
  unfold retainedWords
  rw [Finset.mem_filter, mem_wordBox_iff]

/-- The retained words are positive words of length `d₃`. -/
theorem retainedWords_shape {n d₁ d₂ d₃ : ℕ} {δ : ℝ} :
    ∀ w ∈ retainedWords n d₁ d₂ d₃ δ, w.length = d₃ ∧ ∀ a ∈ w, 0 < a := by
  intro w hw
  obtain ⟨⟨hlen, hbox⟩, -⟩ := mem_retainedWords_iff.mp hw
  exact ⟨hlen, fun a ha => (hbox a ha).1⟩

/-- **The three frozen windows.**  On the cylinder of a retained word, the
continuants at all three cut depths obey their retained inequalities. -/
theorem retainedWords_windows {n d₁ d₂ d₃ : ℕ} {δ : ℝ} (hd : 0 < d₃)
    (h12 : d₁ ≤ d₂) (h23 : d₂ ≤ d₃) :
    ∀ w ∈ retainedWords n d₁ d₂ d₃ δ,
    ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational α →
      (Real.exp (lyapunov * (d₁ : ℝ) - δ * Hscale n) ≤ (denom α d₁ : ℝ)
        ∧ (denom α d₁ : ℝ) ≤ Real.exp (lyapunov * (d₁ : ℝ) + δ * Hscale n))
      ∧ (denom α d₂ : ℝ) ≤ Real.exp (lyapunov * (d₂ : ℝ) + δ * Hscale n)
      ∧ (Real.exp (lyapunov * (d₃ : ℝ) - δ * Hscale n) ≤ (denom α d₃ : ℝ)
        ∧ (denom α d₃ : ℝ) ≤ Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n)) := by
  intro w hw α hα hirr
  obtain ⟨⟨hlen, -⟩, hf1, hf2, hf3⟩ := mem_retainedWords_iff.mp hw
  have hpos := (retainedWords_shape w hw).2
  have h1 := denom_eq_wordDenom_take hlen hpos hα hirr hd (le_trans h12 h23)
  have h2 := denom_eq_wordDenom_take hlen hpos hα hirr hd h23
  have h3 := denom_eq_wordDenom_take hlen hpos hα hirr hd (le_refl d₃)
  rw [List.take_of_length_le (le_of_eq hlen)] at h3
  rw [h1, h2, h3]

  exact ⟨hf1, hf2, hf3⟩

/-- **The cover.**  An irrational point of `(0,1)` that satisfies all three
retained inequalities lies in a retained cylinder. -/
theorem mem_retainedWords_of_window {n d₁ d₂ d₃ : ℕ} {δ : ℝ}
    (h12 : d₁ ≤ d₂) (h23 : d₂ ≤ d₃) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (hw1 : Real.exp (lyapunov * (d₁ : ℝ) - δ * Hscale n) ≤ (denom α d₁ : ℝ)
      ∧ (denom α d₁ : ℝ) ≤ Real.exp (lyapunov * (d₁ : ℝ) + δ * Hscale n))
    (hw2 : (denom α d₂ : ℝ) ≤ Real.exp (lyapunov * (d₂ : ℝ) + δ * Hscale n))
    (hw3 : Real.exp (lyapunov * (d₃ : ℝ) - δ * Hscale n) ≤ (denom α d₃ : ℝ)
      ∧ (denom α d₃ : ℝ) ≤ Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n)) :
    digitWordOf α d₃ ∈ retainedWords n d₁ d₂ d₃ δ
      ∧ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder (digitWordOf α d₃) := by
  refine ⟨?_, mem_cylinder_digitWordOf hα hirr d₃⟩
  rw [mem_retainedWords_iff]
  have htake : ∀ m, m ≤ d₃ → (digitWordOf α d₃).take m = digitWordOf α m :=
    fun m hm => digitWordOf_take α hm
  refine ⟨⟨by simp, ?_⟩, ?_, ?_, ?_⟩
  · intro a ha
    rw [digitWordOf, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    refine ⟨one_le_digit hα hirr i, ?_⟩
    have h1 : digit α i ≤ denom α d₃ := digit_le_denom hα hirr i.isLt
    have h2 : denom α d₃ ≤ ⌊Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n)⌋₊ :=
      Nat.le_floor hw3.2
    omega
  · rw [htake d₁ (le_trans h12 h23), wordDenom_digitWordOf]
    exact hw1
  · rw [htake d₂ h23, wordDenom_digitWordOf]
    exact hw2
  · rw [wordDenom_digitWordOf]
    exact hw3

/-- **The discarded mass**, bounded by display (20) at the three cut
depths: at most `3 C₀ e^{-c₀√L}`. -/
theorem volume_discarded_retainedWords_le (n : ℕ) {C₀ δ c₀ : ℝ}
    (h20n : ∀ j : ℕ, j ≤ 2 * mIndex n →
      volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (j : ℝ) - δ * Hscale n) ≤ (denom α j : ℝ)
              ∧ (denom α j : ℝ) ≤ Real.exp (lyapunov * (j : ℝ) + δ * Hscale n))}
        ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
    {d₁ d₂ d₃ : ℕ} (h12 : d₁ ≤ d₂) (h23 : d₂ ≤ d₃) (h3 : d₃ ≤ 2 * mIndex n) :
    (volume (Ioo (0 : ℝ) 1 \
        ⋃ w ∈ retainedWords n d₁ d₂ d₃ δ,
          Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
  classical
  set Bad : ℕ → Set ℝ := fun j => {α ∈ Ioo (0 : ℝ) 1 |
      ¬ (Real.exp (lyapunov * (j : ℝ) - δ * Hscale n) ≤ (denom α j : ℝ)
          ∧ (denom α j : ℝ) ≤ Real.exp (lyapunov * (j : ℝ) + δ * Hscale n))}
    with hBadDef
  have hnull : volume {α : ℝ | ¬ Irrational α} = 0 := by
    have hset : {α : ℝ | ¬ Irrational α} = Set.range ((↑) : ℚ → ℝ) := by
      ext x
      simp [Irrational]
    rw [hset]
    exact (Set.countable_range _).measure_zero volume
  have hsub : Ioo (0 : ℝ) 1 \
      (⋃ w ∈ retainedWords n d₁ d₂ d₃ δ, Erdos1002.gaussHalfOpenPrefixCylinder w)
      ⊆ (Bad d₁ ∪ Bad d₂ ∪ Bad d₃) ∪ {α : ℝ | ¬ Irrational α} := by
    rintro α ⟨hα, hnu⟩
    by_cases hirr : Irrational α
    · left
      by_contra hgood
      simp only [Set.mem_union, not_or] at hgood
      obtain ⟨⟨hg1, hg2⟩, hg3⟩ := hgood
      have hb1 : Real.exp (lyapunov * (d₁ : ℝ) - δ * Hscale n) ≤ (denom α d₁ : ℝ)
          ∧ (denom α d₁ : ℝ) ≤ Real.exp (lyapunov * (d₁ : ℝ) + δ * Hscale n) := by
        by_contra hc
        exact hg1 ⟨hα, hc⟩
      have hb2 : Real.exp (lyapunov * (d₂ : ℝ) - δ * Hscale n) ≤ (denom α d₂ : ℝ)
          ∧ (denom α d₂ : ℝ) ≤ Real.exp (lyapunov * (d₂ : ℝ) + δ * Hscale n) := by
        by_contra hc
        exact hg2 ⟨hα, hc⟩
      have hb3 : Real.exp (lyapunov * (d₃ : ℝ) - δ * Hscale n) ≤ (denom α d₃ : ℝ)
          ∧ (denom α d₃ : ℝ) ≤ Real.exp (lyapunov * (d₃ : ℝ) + δ * Hscale n) := by
        by_contra hc
        exact hg3 ⟨hα, hc⟩
      obtain ⟨hmem, hcyl⟩ :=
        mem_retainedWords_of_window (n := n) h12 h23 hα hirr hb1 hb2.2 hb3
      exact hnu (Set.mem_biUnion hmem hcyl)
    · right
      exact hirr
  have hle : volume (Ioo (0 : ℝ) 1 \
      ⋃ w ∈ retainedWords n d₁ d₂ d₃ δ, Erdos1002.gaussHalfOpenPrefixCylinder w)
      ≤ volume (Bad d₁) + volume (Bad d₂) + volume (Bad d₃) := by
    calc volume (Ioo (0 : ℝ) 1 \
        ⋃ w ∈ retainedWords n d₁ d₂ d₃ δ, Erdos1002.gaussHalfOpenPrefixCylinder w)
        ≤ volume ((Bad d₁ ∪ Bad d₂ ∪ Bad d₃) ∪ {α : ℝ | ¬ Irrational α}) :=
          measure_mono hsub
      _ ≤ volume (Bad d₁ ∪ Bad d₂ ∪ Bad d₃) + volume {α : ℝ | ¬ Irrational α} :=
          measure_union_le _ _
      _ = volume (Bad d₁ ∪ Bad d₂ ∪ Bad d₃) := by rw [hnull, add_zero]
      _ ≤ volume (Bad d₁ ∪ Bad d₂) + volume (Bad d₃) := measure_union_le _ _
      _ ≤ volume (Bad d₁) + volume (Bad d₂) + volume (Bad d₃) :=
          add_le_add (measure_union_le _ _) le_rfl
  have hBadfin : ∀ j : ℕ, volume (Bad j) ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    simp
  have hfin : volume (Bad d₁) + volume (Bad d₂) + volume (Bad d₃) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hBadfin d₁, hBadfin d₂⟩, hBadfin d₃⟩
  refine le_trans (ENNReal.toReal_mono hfin hle) ?_
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hBadfin d₁, hBadfin d₂⟩)
      (hBadfin d₃),
    ENNReal.toReal_add (hBadfin d₁) (hBadfin d₂)]
  have hb1 := h20n d₁ (by omega)
  have hb2 := h20n d₂ (by omega)
  have hb3 := h20n d₃ h3
  simp only [Measure.real] at hb1 hb2 hb3
  have e1 : (volume (Bad d₁)).toReal ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := hb1
  have e2 : (volume (Bad d₂)).toReal ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := hb2
  have e3 : (volume (Bad d₃)).toReal ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := hb3
  linarith

/-! ## 4. The Lebesgue-conditional mean replacement on a cylinder

The mixing proved in the tree
(`MixingBV.lem_3_2_conditional_multiblock_mixing'`) conditions on
Gauss-measure cylinders, while the mode integrals of §4 are Lebesgue on
`(0,1)`.  The bridge costs no second transfer argument: the density
`dλ/dν = log 2 · (1+x)` (`Prop41Final.wGL`) is `log 2`-Lipschitz, hence
constant to order `diam(I_w)` on the cylinder, and the retained cylinders
of §3 have exponentially small diameter. -/

/-- A positive half-open cylinder has positive Lebesgue measure. -/
theorem volume_halfOpen_pos {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    0 < (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
  have hvol : volume (Erdos1002.gaussHalfOpenPrefixCylinder w)
      = volume (Erdos1002.closedGaussPrefixCylinder w) :=
    (Kwon1002.volume_closedCylinder_eq_halfOpen hpos).symm
  obtain ⟨-, -, hC, hD, -⟩ := Kwon1002.quad_bounds hpos
  have hCR : (0 : ℝ) ≤ (qC w : ℝ) := by exact_mod_cast hC
  have hDR : (0 : ℝ) < (qD w : ℝ) := by exact_mod_cast hD
  have hlen : |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0|
      = 1 / (((qC w : ℝ) + (qD w : ℝ)) * (qD w : ℝ)) :=
    Kwon1002.cylinder_length_eq hpos
  have hlenpos : 0 < |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0| := by
    rw [hlen]
    positivity
  have hmm : (Erdos1002.gaussInverseWord w 0 ⊔ Erdos1002.gaussInverseWord w 1)
      - (Erdos1002.gaussInverseWord w 0 ⊓ Erdos1002.gaussInverseWord w 1)
      = |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0| := by
    have h1 : Erdos1002.gaussInverseWord w 0 ⊔ Erdos1002.gaussInverseWord w 1
        = max (Erdos1002.gaussInverseWord w 0) (Erdos1002.gaussInverseWord w 1) := rfl
    have h2 : Erdos1002.gaussInverseWord w 0 ⊓ Erdos1002.gaussInverseWord w 1
        = min (Erdos1002.gaussInverseWord w 0) (Erdos1002.gaussInverseWord w 1) := rfl
    rw [h1, h2, max_sub_min_eq_abs, abs_sub_comm]
  rw [hvol, Kwon1002.closedCylinder_eq_uIcc hpos, Set.uIcc, Real.volume_Icc,
    ENNReal.toReal_ofReal (by rw [hmm]; exact hlenpos.le)]
  rw [hmm]
  exact hlenpos

/-- A positive half-open cylinder has positive Gauss measure. -/
theorem gaussMeasure_halfOpen_pos {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    0 < (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
  set S := Erdos1002.gaussHalfOpenPrefixCylinder w with hS
  have hmeas : MeasurableSet S := Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hfin : Erdos1002.gaussMeasure S ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ S))
  rw [ENNReal.toReal_pos_iff]
  refine ⟨?_, lt_top_iff_ne_top.mpr hfin⟩
  by_contra hzero
  push_neg at hzero
  have hzero' : Erdos1002.gaussMeasure S = 0 := le_antisymm hzero (zero_le _)
  have hsub : S ∩ Ioo (0 : ℝ) 1 ⊆ S := Set.inter_subset_left
  have hν0 : Erdos1002.gaussMeasure (S ∩ Ioo (0 : ℝ) 1) = 0 :=
    measure_mono_null hsub hzero'
  have hv2 := LargeDeviation.volume_le_two_gaussMeasure
    (hmeas.inter measurableSet_Ioo) Set.inter_subset_right
  rw [hν0, mul_zero, nonpos_iff_eq_zero] at hv2
  -- but `S` and `S ∩ Ioo 0 1` differ by at most the point `1`
  have hdiff : S \ Ioo (0 : ℝ) 1 ⊆ {(1 : ℝ)} ∪ {(0 : ℝ)} := by
    intro x hx
    rcases Nat.eq_zero_or_pos w.length with hlen | hlen
    · -- empty word: the cylinder is `Ico 0 1`
      have hwnil : w = [] := List.length_eq_zero_iff.mp hlen
      have hx1 : x ∈ Ico (0 : ℝ) 1 := by
        rw [hS, hwnil] at hx
        exact hx.1
      right
      have : ¬ (0 < x ∧ x < 1) := by
        intro hcon
        exact hx.2 ⟨hcon.1, hcon.2⟩
      rcases lt_or_eq_of_le hx1.1 with h0 | h0
      · exact absurd ⟨h0, hx1.2⟩ this
      · simp [← h0]
    · have hwne : w ≠ [] := by
        intro hnil
        rw [hnil] at hlen
        simp at hlen
      have hIoc := halfOpenCylinder_subset_Ioc hwne hpos (hS ▸ hx.1)
      left
      have : ¬ (0 < x ∧ x < 1) := by
        intro hcon
        exact hx.2 ⟨hcon.1, hcon.2⟩
      rcases lt_or_eq_of_le hIoc.2 with h1 | h1
      · exact absurd ⟨hIoc.1, h1⟩ this
      · simp [h1]
  have hvS : volume S = 0 := by
    have h1 : volume S ≤ volume (S ∩ Ioo (0 : ℝ) 1) + volume (S \ Ioo (0 : ℝ) 1) := by
      have := measure_union_le (μ := volume) (S ∩ Ioo (0 : ℝ) 1) (S \ Ioo (0 : ℝ) 1)
      rwa [Set.inter_union_diff] at this
    have h2 : volume (S \ Ioo (0 : ℝ) 1) = 0 := by
      refine measure_mono_null hdiff ?_
      refine measure_union_null (measure_singleton _) (measure_singleton _)
    rw [hv2, h2, add_zero] at h1
    exact le_antisymm h1 (zero_le _)
  have := volume_halfOpen_pos hpos
  rw [← hS, hvS] at this
  simp at this

/-- A positive half-open cylinder contains an irrational point. -/
theorem exists_irrational_mem_halfOpen {w : List ℕ} (hpos : ∀ a ∈ w, 0 < a) :
    ∃ β ∈ Erdos1002.gaussHalfOpenPrefixCylinder w, Irrational β := by
  by_contra hno
  push_neg at hno
  have hsub : Erdos1002.gaussHalfOpenPrefixCylinder w ⊆ Set.range ((↑) : ℚ → ℝ) := by
    intro x hx
    have := hno x hx
    simpa [Irrational] using this
  have h0 : volume (Erdos1002.gaussHalfOpenPrefixCylinder w) = 0 :=
    measure_mono_null hsub ((Set.countable_range _).measure_zero volume)
  have := volume_halfOpen_pos hpos
  rw [h0] at this
  simp at this

/-- **Change of measure on a cylinder**: `∫_{I_w} f dλ = ∫_{I_w} w_{GL}·f dν`,
for the Radon-Nikodym weight `w_{GL} = log 2·(1+x)` of `Prop41Final`. -/
theorem setIntegral_leb_eq_gauss_wGL {w : List ℕ} (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) (f : ℝ → ℝ) :
    (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w, f α)
      = ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
          Prop41Final.wGL α * f α ∂Erdos1002.gaussMeasure := by
  set S := Erdos1002.gaussHalfOpenPrefixCylinder w with hS
  have hmeas : MeasurableSet S := Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hsub : S ⊆ Ioc (0 : ℝ) 1 := halfOpenCylinder_subset_Ioc hw hpos
  have h1 : (∫ α in S, f α) = ∫ α in Ioc (0 : ℝ) 1, S.indicator f α := by
    rw [setIntegral_indicator hmeas, Set.inter_eq_self_of_subset_right hsub]
  have h2 := Prop41Final.integral_Ioc_eq_gauss_mul (S.indicator f)
  have h3 : (fun α => Prop41Final.wGL α * S.indicator f α)
      = S.indicator (fun α => Prop41Final.wGL α * f α) := by
    funext α
    by_cases hα : α ∈ S
    · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα]
    · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα, mul_zero]
  rw [h1, h2]
  calc (∫ α, Prop41Final.wGL α * S.indicator f α ∂Erdos1002.gaussMeasure)
      = ∫ α, S.indicator (fun β => Prop41Final.wGL β * f β) α
          ∂Erdos1002.gaussMeasure := by rw [h3]
    _ = ∫ α in S, Prop41Final.wGL α * f α ∂Erdos1002.gaussMeasure :=
        integral_indicator hmeas

/-- **The Gauss-conditional multiblock mixing, on half-open list cylinders.**
Bridge of `MixingBV.lem_3_2_conditional_multiblock_mixing'` from the
function-indexed digit cylinders to the substrate's word cylinders, with
the conditional mean cleared of its denominator. -/
theorem gauss_halfOpen_multiblock_mixing (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : List ℕ), w.length = d → (∀ a ∈ w, 0 < a) →
      ∀ (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → Prop41.BVBoundedBy K (g i)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        |(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              ∏ i ∈ Finset.range s, g i (gaussIter α (t i)) ∂Erdos1002.gaussMeasure)
            - (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
                * ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
              * (C * ρ ^ M * K ^ s) := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hmix⟩ :=
    MixingBV.lem_3_2_conditional_multiblock_mixing' s
  refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
  intro d M w hlen hpos t g K hK hbv h0 hstep
  classical
  set wf : ℕ → ℕ := fun i => w.getD i 1 with hwf
  have hword : MixingBV.digitWord d wf = w := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [MixingBV.digitWord, List.getElem_map, List.getElem_range, hwf]
      exact List.getD_eq_getElem w 1 h2
  have hae : (Prop41.cylinder d wf : Set ℝ) =ᵐ[Erdos1002.gaussMeasure]
      Erdos1002.gaussHalfOpenPrefixCylinder w := by
    have := MixingBV.cylinder_ae_eq_halfOpen d wf
    rwa [hword] at this
  have hμeq : Erdos1002.gaussMeasure (Prop41.cylinder d wf)
      = Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
    measure_congr hae
  have hIeq : (∫ α in Prop41.cylinder d wf,
        ∏ i ∈ Finset.range s, g i (gaussIter α (t i)) ∂Erdos1002.gaussMeasure)
      = ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
          ∏ i ∈ Finset.range s, g i (gaussIter α (t i)) ∂Erdos1002.gaussMeasure :=
    setIntegral_congr_set hae
  have hposμ : 0 < (Erdos1002.gaussMeasure (Prop41.cylinder d wf)).toReal := by
    rw [hμeq]
    exact gaussMeasure_halfOpen_pos hpos
  have h := hmix d M wf t g K hK hbv h0 hstep hposμ
  rw [hIeq, hμeq] at h
  set m : ℝ := (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
    with hm
  set A : ℝ := ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
      ∏ i ∈ Finset.range s, g i (gaussIter α (t i)) ∂Erdos1002.gaussMeasure with hA
  set P : ℝ := ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure with hP
  have hm0 : 0 < m := by
    rw [hm]
    exact gaussMeasure_halfOpen_pos hpos
  have hcancel : m * (A / m) = A := by
    field_simp
  have hkey : A - m * P = m * (A / m - P) := by
    rw [mul_sub, hcancel]
  rw [hkey, abs_mul, abs_of_pos hm0]
  exact mul_le_mul_of_nonneg_left h hm0.le

/-- The stationary mean of a `BV(0,1)` observable is bounded by its sup
norm. -/
theorem abs_integral_gauss_le {g : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ K) :
    |∫ x, g x ∂Erdos1002.gaussMeasure| ≤ K := by
  have hae : ∀ᵐ x ∂Erdos1002.gaussMeasure, ‖g x‖ ≤ K := by
    filter_upwards [LargeDeviation.ae_gauss_unit_irrational] with x hx
    rw [Real.norm_eq_abs]
    exact hbd x hx.1
  have h := norm_integral_le_of_norm_le_const (μ := Erdos1002.gaussMeasure) hae
  rw [Real.norm_eq_abs] at h
  simpa [measureReal_def] using h

/-- **The Lebesgue-conditional stationary-mean replacement, real form.**
For `BV(0,1)` observables read along the orbit at times `≥ M` past the
cylinder depth, the Lebesgue integral over the cylinder factorizes through
the product of the stationary Gauss means, at cost
`ν(I_w)·2log2·(Cρ^M + diam)·K^s`: the Gauss-conditional mixing of
Lemma 3.2 plus one `diam(I_w)` freeze of the density `dλ/dν`. -/
theorem leb_halfOpen_multiblock_mixing (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : List ℕ), w.length = d → (∀ a ∈ w, 0 < a) → 0 < d →
      ∀ Δ : ℝ,
      (∀ x ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
        ∀ y ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
          Irrational x → Irrational y → |x - y| ≤ Δ) →
      ∀ (t : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → Prop41.BVBoundedBy K (g i)) →
        (∀ i, i < s → Measurable (g i)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        |(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              ∏ i ∈ Finset.range s, g i (gaussIter α (t i)))
            - (volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
                * ∏ i ∈ Finset.range s, ∫ x, g i x ∂Erdos1002.gaussMeasure|
          ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
              * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hmix⟩ := gauss_halfOpen_multiblock_mixing s
  refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
  intro d M w hlen hpos hd0 Δ hΔ t g K hK hbv hgm h0 hstep
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set ν := Erdos1002.gaussMeasure with hν
  set S := Erdos1002.gaussHalfOpenPrefixCylinder w with hSdef
  have hSm : MeasurableSet S := Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hwne : w ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
    omega
  obtain ⟨β, hβS, hβirr⟩ := exists_irrational_mem_halfOpen hpos
  have hβIoo : β ∈ Ioo (0 : ℝ) 1 := mem_Ioo_of_mem_halfOpen hwne hpos hβS hβirr
  have hβIcc : β ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hβIoo
  set F : ℝ → ℝ := fun α => ∏ i ∈ Finset.range s, g i (gaussIter α (t i)) with hF
  have hFmeas : Measurable F :=
    Finset.measurable_prod _ (fun i hi =>
      (hgm i (Finset.mem_range.1 hi)).comp (measurable_gaussIter (t i)))
  have hKs : (0 : ℝ) ≤ K ^ s := by positivity
  have hFbound : ∀ α ∈ Ioo (0 : ℝ) 1, Irrational α → |F α| ≤ K ^ s := by
    intro α hα hirr
    rw [hF]
    calc |∏ i ∈ Finset.range s, g i (gaussIter α (t i))|
        = ∏ i ∈ Finset.range s, |g i (gaussIter α (t i))| := Finset.abs_prod _ _
      _ ≤ ∏ _i ∈ Finset.range s, K := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => ?_)
          exact (hbv i (Finset.mem_range.1 hi)).1 _ (gaussIter_mem_Ioo hα hirr (t i))
      _ = K ^ s := by rw [Finset.prod_const, Finset.card_range]
  -- integrability on the cylinder
  have hae_unit : ∀ᵐ α ∂(ν.restrict S), α ∈ Ioo (0 : ℝ) 1 ∧ Irrational α :=
    ae_restrict_of_ae LargeDeviation.ae_gauss_unit_irrational
  have haeS : ∀ᵐ α ∂(ν.restrict S), α ∈ S := ae_restrict_mem hSm
  have hFint : IntegrableOn F S ν := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable (K ^ s) ?_
    filter_upwards [hae_unit] with α hα
    rw [Real.norm_eq_abs]
    exact hFbound α hα.1 hα.2
  have hwGLFint : IntegrableOn (fun α => Prop41Final.wGL α * F α) S ν := by
    refine Integrable.of_bound
      ((Prop41Final.measurable_wGL.mul hFmeas).aestronglyMeasurable)
      (2 * Real.log 2 * K ^ s) ?_
    filter_upwards [hae_unit] with α hα
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Prop41Final.wGL α| ≤ 2 * Real.log 2 := by
      rw [abs_of_nonneg (Prop41Final.wGL_nonneg (Ioo_subset_Icc_self hα.1))]
      exact Prop41Final.wGL_le (Ioo_subset_Icc_self hα.1)
    have h2 := hFbound α hα.1 hα.2
    calc |Prop41Final.wGL α| * |F α| ≤ (2 * Real.log 2) * (K ^ s) := by
          exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 2 * Real.log 2 * K ^ s := by ring
  set m : ℝ := (ν S).toReal with hm
  set v : ℝ := (volume S).toReal with hv
  set P : ℝ := ∏ i ∈ Finset.range s, ∫ x, g i x ∂ν with hP
  have hm0 : 0 < m := gaussMeasure_halfOpen_pos hpos
  have hνSfin : ν S < ⊤ := measure_lt_top _ _
  -- change of measure and the two density freezes
  have hchange : (∫ α in S, F α) = ∫ α in S, Prop41Final.wGL α * F α ∂ν :=
    setIntegral_leb_eq_gauss_wGL hwne hpos F
  have hveq : v = ∫ α in S, Prop41Final.wGL α ∂ν := by
    have h1 := setIntegral_leb_eq_gauss_wGL hwne hpos (fun _ => (1 : ℝ))
    simp only [mul_one] at h1
    rw [hv, ← h1, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hfreezeS : |(∫ α in S, Prop41Final.wGL α * F α ∂ν)
      - Prop41Final.wGL β * ∫ α in S, F α ∂ν| ≤ Real.log 2 * Δ * K ^ s * m := by
    have hsplit : (∫ α in S, Prop41Final.wGL α * F α ∂ν)
        - Prop41Final.wGL β * ∫ α in S, F α ∂ν
        = ∫ α in S, (Prop41Final.wGL α - Prop41Final.wGL β) * F α ∂ν := by
      rw [← integral_const_mul, ← integral_sub hwGLFint (hFint.const_mul _)]
      congr 1
      funext α
      ring
    rw [hsplit]
    have hb := norm_setIntegral_le_of_norm_le_const_ae (μ := ν)
      (f := fun α => (Prop41Final.wGL α - Prop41Final.wGL β) * F α)
      (s := S) (C := Real.log 2 * Δ * K ^ s) hνSfin ?_
    · rw [Real.norm_eq_abs] at hb
      calc |∫ α in S, (Prop41Final.wGL α - Prop41Final.wGL β) * F α ∂ν|
          ≤ Real.log 2 * Δ * K ^ s * ν.real S := hb
        _ = Real.log 2 * Δ * K ^ s * m := by rw [measureReal_def]
    · filter_upwards [hae_unit, haeS] with α hα hαS
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Prop41Final.wGL α - Prop41Final.wGL β|
          ≤ Real.log 2 * |α - β| :=
        Prop41Final.wGL_lip (Ioo_subset_Icc_self hα.1) hβIcc
      have h2 : |α - β| ≤ Δ := hΔ α hαS β hβS hα.2 hβirr
      have h3 := hFbound α hα.1 hα.2
      have hΔ0 : (0 : ℝ) ≤ Δ := le_trans (abs_nonneg _) h2
      calc |Prop41Final.wGL α - Prop41Final.wGL β| * |F α|
          ≤ (Real.log 2 * Δ) * (K ^ s) := by
            refine mul_le_mul ?_ h3 (abs_nonneg _) (by positivity)
            calc |Prop41Final.wGL α - Prop41Final.wGL β|
                ≤ Real.log 2 * |α - β| := h1
              _ ≤ Real.log 2 * Δ := by
                  exact mul_le_mul_of_nonneg_left h2 hlog2.le
        _ = Real.log 2 * Δ * K ^ s := by ring
  have hfreeze1 : |v - Prop41Final.wGL β * m| ≤ Real.log 2 * Δ * m := by
    have hsplit : v - Prop41Final.wGL β * m
        = ∫ α in S, (Prop41Final.wGL α - Prop41Final.wGL β) ∂ν := by
      have hconst : (∫ _α in S, Prop41Final.wGL β ∂ν) = Prop41Final.wGL β * m := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, ← hm, mul_comm]
      have hint1 : IntegrableOn (fun α => Prop41Final.wGL α) S ν := by
        refine Integrable.of_bound
          Prop41Final.measurable_wGL.aestronglyMeasurable (2 * Real.log 2) ?_
        filter_upwards [hae_unit] with α hα
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Prop41Final.wGL_nonneg (Ioo_subset_Icc_self hα.1))]
        exact Prop41Final.wGL_le (Ioo_subset_Icc_self hα.1)
      rw [hveq, ← hconst, ← integral_sub hint1 (integrableOn_const ?_)]
      · exact hνSfin.ne
    rw [hsplit]
    have hb := norm_setIntegral_le_of_norm_le_const_ae (μ := ν)
      (f := fun α => Prop41Final.wGL α - Prop41Final.wGL β)
      (s := S) (C := Real.log 2 * Δ) hνSfin ?_
    · rw [Real.norm_eq_abs] at hb
      calc |∫ α in S, (Prop41Final.wGL α - Prop41Final.wGL β) ∂ν|
          ≤ Real.log 2 * Δ * ν.real S := hb
        _ = Real.log 2 * Δ * m := by rw [measureReal_def]
    · filter_upwards [hae_unit, haeS] with α hα hαS
      rw [Real.norm_eq_abs]
      have h1 : |Prop41Final.wGL α - Prop41Final.wGL β|
          ≤ Real.log 2 * |α - β| :=
        Prop41Final.wGL_lip (Ioo_subset_Icc_self hα.1) hβIcc
      have h2 : |α - β| ≤ Δ := hΔ α hαS β hβS hα.2 hβirr
      calc |Prop41Final.wGL α - Prop41Final.wGL β|
          ≤ Real.log 2 * |α - β| := h1
        _ ≤ Real.log 2 * Δ := mul_le_mul_of_nonneg_left h2 hlog2.le
  have hmixS : |(∫ α in S, F α ∂ν) - m * P| ≤ m * (C * ρ ^ M * K ^ s) :=
    hmix d M w hlen hpos t g K hK hbv h0 hstep
  have hPbd : |P| ≤ K ^ s := by
    rw [hP]
    calc |∏ i ∈ Finset.range s, ∫ x, g i x ∂ν|
        = ∏ i ∈ Finset.range s, |∫ x, g i x ∂ν| := Finset.abs_prod _ _
      _ ≤ ∏ _i ∈ Finset.range s, K := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => ?_)
          exact abs_integral_gauss_le hK (hbv i (Finset.mem_range.1 hi)).1
      _ = K ^ s := by rw [Finset.prod_const, Finset.card_range]
  have hwGLβ0 : 0 ≤ Prop41Final.wGL β := Prop41Final.wGL_nonneg hβIcc
  have hwGLβ2 : Prop41Final.wGL β ≤ 2 * Real.log 2 := Prop41Final.wGL_le hβIcc
  -- assemble
  rw [hchange]
  have hdec : (∫ α in S, Prop41Final.wGL α * F α ∂ν) - v * P
      = ((∫ α in S, Prop41Final.wGL α * F α ∂ν)
            - Prop41Final.wGL β * ∫ α in S, F α ∂ν)
        + Prop41Final.wGL β * ((∫ α in S, F α ∂ν) - m * P)
        - (v - Prop41Final.wGL β * m) * P := by
    ring
  rw [hdec]
  have hΔ0 : (0 : ℝ) ≤ Δ := le_trans (abs_nonneg _) (hΔ β hβS β hβS hβirr hβirr)
  have e2 : |Prop41Final.wGL β * ((∫ α in S, F α ∂ν) - m * P)|
      ≤ 2 * Real.log 2 * (m * (C * ρ ^ M * K ^ s)) := by
    rw [abs_mul, abs_of_nonneg hwGLβ0]
    refine mul_le_mul hwGLβ2 hmixS (abs_nonneg _) (by positivity)
  have e3 : |(v - Prop41Final.wGL β * m) * P| ≤ (Real.log 2 * Δ * m) * K ^ s := by
    rw [abs_mul]
    exact mul_le_mul hfreeze1 hPbd (abs_nonneg _) (by positivity)
  calc |((∫ α in S, Prop41Final.wGL α * F α ∂ν)
            - Prop41Final.wGL β * ∫ α in S, F α ∂ν)
        + Prop41Final.wGL β * ((∫ α in S, F α ∂ν) - m * P)
        - (v - Prop41Final.wGL β * m) * P|
      ≤ |((∫ α in S, Prop41Final.wGL α * F α ∂ν)
            - Prop41Final.wGL β * ∫ α in S, F α ∂ν)
          + Prop41Final.wGL β * ((∫ α in S, F α ∂ν) - m * P)|
        + |(v - Prop41Final.wGL β * m) * P| := abs_sub _ _
    _ ≤ |(∫ α in S, Prop41Final.wGL α * F α ∂ν)
            - Prop41Final.wGL β * ∫ α in S, F α ∂ν|
        + |Prop41Final.wGL β * ((∫ α in S, F α ∂ν) - m * P)|
        + |(v - Prop41Final.wGL β * m) * P| := by
          exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (Real.log 2 * Δ * K ^ s * m)
        + 2 * Real.log 2 * (m * (C * ρ ^ M * K ^ s))
        + (Real.log 2 * Δ * m) * K ^ s := by
          exact add_le_add (add_le_add hfreezeS e2) e3
    _ = m * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s := by ring

/-- **The Lebesgue-conditional stationary-mean replacement, complex form.**
The `2^s` expansion of `ZeroMode.prod_complex_expand` applied on both sides
of `leb_halfOpen_multiblock_mixing`: complex digit observables whose real
and imaginary parts are `BV(0,1)` factorize over a cylinder into the
product of their stationary Gauss means, under Lebesgue measure. -/
theorem leb_halfOpen_multiblock_mixing_complex (s : ℕ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (d M : ℕ) (w : List ℕ), w.length = d → (∀ a ∈ w, 0 < a) → 0 < d →
      ∀ Δ : ℝ,
      (∀ x ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
        ∀ y ∈ Erdos1002.gaussHalfOpenPrefixCylinder w,
          Irrational x → Irrational y → |x - y| ≤ Δ) →
      ∀ (t : ℕ → ℕ) (G : ℕ → ℝ → ℂ) (K : ℝ), 0 ≤ K →
        (∀ i, i < s → Measurable (G i)) →
        (∀ i, i < s → Prop41.BVBoundedBy K (fun x => (G i x).re)) →
        (∀ i, i < s → Prop41.BVBoundedBy K (fun x => (G i x).im)) →
        d + M ≤ t 0 → (∀ i, i + 1 < s → t i + M ≤ t (i + 1)) →
        ‖(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
              ∏ i ∈ Finset.range s, G i (gaussIter α (t i)))
            - ((volume (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal : ℂ)
                * ∏ i ∈ Finset.range s, ∫ x, G i x ∂Erdos1002.gaussMeasure‖
          ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
              * 2 ^ s * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hreal⟩ := leb_halfOpen_multiblock_mixing s
  refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
  intro d M w hlen hpos hd0 Δ hΔ t G K hK hGm hre him h0 hstep
  classical
  set ν := Erdos1002.gaussMeasure with hν
  set S := Erdos1002.gaussHalfOpenPrefixCylinder w with hSdef
  have hSm : MeasurableSet S := Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w
  have hwne : w ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
    omega
  have hvfin : volume S < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (halfOpenCylinder_subset_Ioc hwne hpos)) ?_
    rw [Real.volume_Ioc]
    simp
  haveI hfinS : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hKs : (0 : ℝ) ≤ K ^ s := by positivity
  -- the real selector families and their properties
  have hselbv : ∀ T : Finset ℕ, ∀ i, i < s →
      Prop41.BVBoundedBy K (fun x => if i ∈ T then (G i x).re else (G i x).im) := by
    intro T i hi
    by_cases h : i ∈ T
    · simpa [h] using hre i hi
    · simpa [h] using him i hi
  have hselm : ∀ T : Finset ℕ, ∀ i, i < s →
      Measurable (fun x => if i ∈ T then (G i x).re else (G i x).im) := by
    intro T i hi
    by_cases h : i ∈ T
    · simpa [h] using Complex.measurable_re.comp (hGm i hi)
    · simpa [h] using Complex.measurable_im.comp (hGm i hi)
  -- pointwise expansion of the integrand
  have hpt : ∀ α : ℝ, (∏ i ∈ Finset.range s, G i (gaussIter α (t i)))
      = ∑ T ∈ (Finset.range s).powerset,
          Complex.I ^ ((Finset.range s) \ T).card *
            ((∏ i ∈ Finset.range s,
                (if i ∈ T then (G i (gaussIter α (t i))).re
                  else (G i (gaussIter α (t i))).im) : ℝ) : ℂ) :=
    fun α => ZeroMode.prod_complex_expand s (fun i => G i (gaussIter α (t i)))
  -- the real block products, bounded and measurable
  have hSPm : ∀ T : Finset ℕ, Measurable (fun α : ℝ => (∏ i ∈ Finset.range s,
      (if i ∈ T then (G i (gaussIter α (t i))).re
        else (G i (gaussIter α (t i))).im) : ℝ)) := by
    intro T
    refine Finset.measurable_prod _ (fun i hi => ?_)
    exact (hselm T i (Finset.mem_range.1 hi)).comp (measurable_gaussIter (t i))
  have hSPbd : ∀ T : Finset ℕ, ∀ α ∈ Ioo (0 : ℝ) 1, Irrational α →
      |(∏ i ∈ Finset.range s,
          (if i ∈ T then (G i (gaussIter α (t i))).re
            else (G i (gaussIter α (t i))).im) : ℝ)| ≤ K ^ s := by
    intro T α hα hirr
    calc |(∏ i ∈ Finset.range s,
        (if i ∈ T then (G i (gaussIter α (t i))).re
          else (G i (gaussIter α (t i))).im) : ℝ)|
        = ∏ i ∈ Finset.range s, |(if i ∈ T then (G i (gaussIter α (t i))).re
            else (G i (gaussIter α (t i))).im : ℝ)| := Finset.abs_prod _ _
      _ ≤ ∏ _i ∈ Finset.range s, K := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => ?_)
          exact (hselbv T i (Finset.mem_range.1 hi)).1 _
            (gaussIter_mem_Ioo hα hirr (t i))
      _ = K ^ s := by rw [Finset.prod_const, Finset.card_range]
  -- integrability of every summand on the cylinder (Lebesgue)
  have hae_irr : ∀ᵐ α ∂(volume.restrict S), α ∈ S ∧ Irrational α := by
    filter_upwards [ae_restrict_mem hSm,
      ae_restrict_of_ae (LargeDeviation.ae_irrational_volume)] with α h1 h2
    exact ⟨h1, h2⟩
  have hint : ∀ T : Finset ℕ, IntegrableOn (fun α : ℝ =>
      Complex.I ^ ((Finset.range s) \ T).card *
        ((∏ i ∈ Finset.range s,
            (if i ∈ T then (G i (gaussIter α (t i))).re
              else (G i (gaussIter α (t i))).im) : ℝ) : ℂ)) S volume := by
    intro T
    refine Integrable.of_bound (C := K ^ s) ?_ ?_
    · exact ((measurable_const.mul
        (Complex.measurable_ofReal.comp (hSPm T))).aestronglyMeasurable)
    · filter_upwards [hae_irr] with α hα
      have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
        mem_Ioo_of_mem_halfOpen hwne hpos hα.1 hα.2
      rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      exact hSPbd T α hαIoo hα.2
  -- expansion of the integral
  have hIexp : (∫ α in S, ∏ i ∈ Finset.range s, G i (gaussIter α (t i)))
      = ∑ T ∈ (Finset.range s).powerset,
          Complex.I ^ ((Finset.range s) \ T).card *
            Complex.ofReal (∫ α in S, ∏ i ∈ Finset.range s,
                (if i ∈ T then (G i (gaussIter α (t i))).re
                  else (G i (gaussIter α (t i))).im)) := by
    rw [integral_congr_ae (Eventually.of_forall (fun α => hpt α))]
    rw [integral_finset_sum _ (fun T _ => hint T)]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [integral_const_mul]
    congr 1
    exact integral_complex_ofReal
  -- expansion of the product of the means
  have hGint : ∀ i, i < s → Integrable (G i) ν := by
    intro i hi
    refine Integrable.of_bound (C := K + K) (hGm i hi).aestronglyMeasurable ?_
    filter_upwards [LargeDeviation.ae_gauss_unit_irrational] with x hx
    calc ‖G i x‖ ≤ |(G i x).re| + |(G i x).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ K + K := add_le_add ((hre i hi).1 x hx.1) ((him i hi).1 x hx.1)
  have hPexp : (∏ i ∈ Finset.range s, ∫ x, G i x ∂ν)
      = ∑ T ∈ (Finset.range s).powerset,
          Complex.I ^ ((Finset.range s) \ T).card *
            Complex.ofReal (∏ i ∈ Finset.range s, ∫ x,
                (if i ∈ T then (G i x).re else (G i x).im) ∂ν) := by
    rw [ZeroMode.prod_complex_expand s (fun i => ∫ x, G i x ∂ν)]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    congr 1
    refine congrArg Complex.ofReal (Finset.prod_congr rfl (fun i hi => ?_))
    by_cases h : i ∈ T
    · simp only [if_pos h]
      simpa using (integral_re (𝕜 := ℂ) (hGint i (Finset.mem_range.1 hi))).symm
    · simp only [if_neg h]
      simpa using (integral_im (𝕜 := ℂ) (hGint i (Finset.mem_range.1 hi))).symm
  -- the difference is a sum of `2^s` real defects
  rw [hIexp, hPexp, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ T ∈ (Finset.range s).powerset,
      ‖Complex.I ^ ((Finset.range s) \ T).card *
            Complex.ofReal (∫ α in S, ∏ i ∈ Finset.range s,
                (if i ∈ T then (G i (gaussIter α (t i))).re
                  else (G i (gaussIter α (t i))).im))
          - ((volume S).toReal : ℂ) *
            (Complex.I ^ ((Finset.range s) \ T).card *
              Complex.ofReal (∏ i ∈ Finset.range s, ∫ x,
                  (if i ∈ T then (G i x).re else (G i x).im) ∂ν))‖
        ≤ (ν S).toReal * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s := by
    intro T _
    have hcollect : Complex.I ^ ((Finset.range s) \ T).card *
            Complex.ofReal (∫ α in S, ∏ i ∈ Finset.range s,
                (if i ∈ T then (G i (gaussIter α (t i))).re
                  else (G i (gaussIter α (t i))).im))
          - ((volume S).toReal : ℂ) *
            (Complex.I ^ ((Finset.range s) \ T).card *
              Complex.ofReal (∏ i ∈ Finset.range s, ∫ x,
                  (if i ∈ T then (G i x).re else (G i x).im) ∂ν))
        = Complex.I ^ ((Finset.range s) \ T).card *
            Complex.ofReal ((∫ α in S, ∏ i ∈ Finset.range s,
                (if i ∈ T then (G i (gaussIter α (t i))).re
                  else (G i (gaussIter α (t i))).im))
              - (volume S).toReal *
                ∏ i ∈ Finset.range s, ∫ x,
                  (if i ∈ T then (G i x).re else (G i x).im) ∂ν) := by
      push_cast
      ring
    rw [hcollect, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact hreal d M w hlen hpos hd0 Δ hΔ t
      (fun i x => if i ∈ T then (G i x).re else (G i x).im) K hK
      (fun i hi => hselbv T i hi) (fun i hi => hselm T i hi) h0 hstep
  calc ‖∑ T ∈ (Finset.range s).powerset,
        (Complex.I ^ ((Finset.range s) \ T).card *
            Complex.ofReal (∫ α in S, ∏ i ∈ Finset.range s,
                (if i ∈ T then (G i (gaussIter α (t i))).re
                  else (G i (gaussIter α (t i))).im))
          - ((volume S).toReal : ℂ) *
            (Complex.I ^ ((Finset.range s) \ T).card *
              Complex.ofReal (∏ i ∈ Finset.range s, ∫ x,
                  (if i ∈ T then (G i x).re else (G i x).im) ∂ν)))‖
      ≤ ∑ T ∈ (Finset.range s).powerset,
        ‖Complex.I ^ ((Finset.range s) \ T).card *
            Complex.ofReal (∫ α in S, ∏ i ∈ Finset.range s,
                (if i ∈ T then (G i (gaussIter α (t i))).re
                  else (G i (gaussIter α (t i))).im))
          - ((volume S).toReal : ℂ) *
            (Complex.I ^ ((Finset.range s) \ T).card *
              Complex.ofReal (∏ i ∈ Finset.range s, ∫ x,
                  (if i ∈ T then (G i x).re else (G i x).im) ∂ν))‖ :=
        norm_sum_le _ _
    _ ≤ ((Finset.range s).powerset.card : ℝ) *
          ((ν S).toReal * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s) := by
        have := Finset.sum_le_card_nsmul _ _
          ((ν S).toReal * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s) hterm
        rwa [nsmul_eq_mul] at this
    _ = (ν S).toReal * 2 ^ s * (2 * Real.log 2) * (C * ρ ^ M + Δ) * K ^ s := by
        rw [Finset.card_powerset, Finset.card_range]
        push_cast
        ring

end

end StationaryReplace

end Kwon1002