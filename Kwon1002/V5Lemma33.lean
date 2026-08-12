import Kwon1002.AntiConcentration

/-!
# Lemma 3.3 and display (21) in the version 5 formulation

Version 5 states the shrinking anti-concentration estimate as
`P(|s q_j - r q_{j-1}| < η q_j) ≤ 4 η + 4 F_{j+1}^{-2}`, uniformly for every
nonzero integer pair `(r,s)`, every `j ≥ 1` and every `η > 0`, and then
weakens it to `C (η + e^{-2 (log φ) j})`.

The earlier in-tree statement `Kwon1002.shrinking_anti_concentration` proves
the weaker `C (η + e^{-c j})` with `C = 64` and `c = log 2`, and carries the
hypothesis `η < 1/2`.  The version 5 bound is strictly sharper on both
counts: `4 η` instead of `32 η` after the reduction to the backward ratio,
and the decay rate `2 log φ = 0.9624…` instead of `log 2 = 0.6931…`.  It also
drops `η < 1/2`, which is genuinely unnecessary because the conclusion is
vacuous once `4 η ≥ 1`.

This file proves the version 5 form.  The method is unchanged: word reversal
plus continuant symmetry, that is `quad_reverse`.  What changes is that the
comparison of a cylinder with its mirror image is now carried out with the
exact cylinder length `|I_w| = 1/(q_j (q_j + q_{j-1}))` rather than through a
crude interior gap, which is what turns the previous factor `16` into the
sharp factor `2`, and that the diameter of a depth `j` cylinder is bounded by
`q_j^{-2} ≤ F_{j+1}^{-2}` rather than by the uniform contraction rate
`4^{-⌊j/2⌋}`.

Main results:

* `V5Lemma33.backward_ratio_anti_concentration_fib`, the estimate for the
  backward continuant ratio `Y_j = q_{j-1}/q_j`;
* `V5Lemma33.shrinking_anti_concentration_v5`, display (21) itself;
* `V5Lemma33.shrinking_anti_concentration_v5_exp`, the golden ratio
  exponential form.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Kwon1002

noncomputable section

namespace V5Lemma33

/-! ## Exact cylinder length -/

/-- The exact Lebesgue length of the depth `n` cylinder of a positive word `w`.
With `qD w = q_n` and `qC w = q_{n-1}` this is `1/(q_n (q_n + q_{n-1}))`. -/
def cylLen (w : List ℕ) : ℝ := 1 / ((qD w : ℝ) * ((qC w : ℝ) + (qD w : ℝ)))

/-- Real valued repackaging of `quad_bounds`. -/
lemma quad_bounds_real {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) :
    (0 : ℝ) ≤ (qA w : ℝ) ∧ (0 : ℝ) ≤ (qB w : ℝ) ∧ (0 : ℝ) ≤ (qC w : ℝ) ∧
      (0 : ℝ) < (qD w : ℝ) ∧ (qB w : ℝ) ≤ (qD w : ℝ) := by
  obtain ⟨hA, hB, hC, hD, hBD⟩ := quad_bounds hpos
  exact ⟨by exact_mod_cast hA, by exact_mod_cast hB, by exact_mod_cast hC,
    by exact_mod_cast hD, by exact_mod_cast hBD⟩

lemma cylLen_pos {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) : 0 < cylLen w := by
  obtain ⟨_, _, hC, hD, _⟩ := quad_bounds_real hpos
  have : (0 : ℝ) < (qD w : ℝ) * ((qC w : ℝ) + (qD w : ℝ)) := by nlinarith
  exact div_pos one_pos this

/-- The signed Moebius difference formula.  The determinant `(-1)^{|w|}` is
what makes the inverse word strictly monotone on `[0,1]`. -/
lemma gaussInverseWord_sub_eq {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Erdos1002.gaussInverseWord w x - Erdos1002.gaussInverseWord w y
      = ((-1 : ℝ) ^ w.length) * (x - y)
          / (((qC w : ℝ) * x + (qD w : ℝ)) * ((qC w : ℝ) * y + (qD w : ℝ))) := by
  obtain ⟨hA, hB, hC, hD, _⟩ := quad_bounds_real hpos
  have hdx : (0 : ℝ) < (qC w : ℝ) * x + (qD w : ℝ) := by nlinarith
  have hdy : (0 : ℝ) < (qC w : ℝ) * y + (qD w : ℝ) := by nlinarith
  have hdet : (qA w : ℝ) * (qD w : ℝ) - (qB w : ℝ) * (qC w : ℝ)
      = (-1 : ℝ) ^ w.length := by
    have h : ((qA w * qD w - qB w * qC w : ℤ) : ℝ) = (((-1 : ℤ) ^ w.length : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (quad_det w)
    push_cast at h
    linarith
  rw [gaussInverseWord_eq_quad hpos hx, gaussInverseWord_eq_quad hpos hy]
  have key : ((qA w : ℝ) * x + (qB w : ℝ)) / ((qC w : ℝ) * x + (qD w : ℝ))
      - ((qA w : ℝ) * y + (qB w : ℝ)) / ((qC w : ℝ) * y + (qD w : ℝ))
      = ((qA w : ℝ) * (qD w : ℝ) - (qB w : ℝ) * (qC w : ℝ)) * (x - y)
          / (((qC w : ℝ) * x + (qD w : ℝ)) * ((qC w : ℝ) * y + (qD w : ℝ))) := by
    field_simp; ring
  rw [key, hdet]

/-- The two endpoints of a depth `n` cylinder are `cylLen w` apart. -/
lemma abs_endpoint_gap {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) :
    |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0| = cylLen w := by
  obtain ⟨_, _, hC, hD, _⟩ := quad_bounds_real hpos
  rw [abs_gaussInverseWord_sub_quad hpos (by norm_num : (0 : ℝ) ≤ 1) (le_refl (0 : ℝ))]
  rw [cylLen]
  have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [h1]
  congr 1
  ring

/-- A depth `n` cylinder is contained in the closed interval spanned by its two
endpoints.  This is where strict monotonicity of the inverse word enters. -/
lemma closedCylinder_subset_uIcc {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) :
    Erdos1002.closedGaussPrefixCylinder w
      ⊆ uIcc (Erdos1002.gaussInverseWord w 0) (Erdos1002.gaussInverseWord w 1) := by
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨hA, hB, hC, hD, _⟩ := quad_bounds_real hpos
  have hdx : (0 : ℝ) < (qC w : ℝ) * x + (qD w : ℝ) := by nlinarith [hx.1]
  have hd0 : (0 : ℝ) < (qC w : ℝ) * 0 + (qD w : ℝ) := by nlinarith
  have hd1 : (0 : ℝ) < (qC w : ℝ) * 1 + (qD w : ℝ) := by nlinarith
  have e0 := gaussInverseWord_sub_eq hpos hx.1 (le_refl (0 : ℝ))
  have e1 := gaussInverseWord_sub_eq hpos (by norm_num : (0 : ℝ) ≤ 1) hx.1
  rcases Nat.even_or_odd w.length with hpar | hpar
  · have hs : ((-1 : ℝ)) ^ w.length = 1 := hpar.neg_one_pow
    rw [hs] at e0 e1
    have g0 : (0 : ℝ) ≤ 1 * (x - 0) / (((qC w : ℝ) * x + (qD w : ℝ))
        * ((qC w : ℝ) * 0 + (qD w : ℝ))) :=
      div_nonneg (by linarith [hx.1]) (le_of_lt (mul_pos hdx hd0))
    have g1 : (0 : ℝ) ≤ 1 * (1 - x) / (((qC w : ℝ) * 1 + (qD w : ℝ))
        * ((qC w : ℝ) * x + (qD w : ℝ))) :=
      div_nonneg (by linarith [hx.2]) (le_of_lt (mul_pos hd1 hdx))
    exact Set.mem_uIcc_of_le (by linarith) (by linarith)
  · have hs : ((-1 : ℝ)) ^ w.length = -1 := hpar.neg_one_pow
    rw [hs] at e0 e1
    have g0 : (0 : ℝ) ≤ 1 * (x - 0) / (((qC w : ℝ) * x + (qD w : ℝ))
        * ((qC w : ℝ) * 0 + (qD w : ℝ))) :=
      div_nonneg (by linarith [hx.1]) (le_of_lt (mul_pos hdx hd0))
    have g1 : (0 : ℝ) ≤ 1 * (1 - x) / (((qC w : ℝ) * 1 + (qD w : ℝ))
        * ((qC w : ℝ) * x + (qD w : ℝ))) :=
      div_nonneg (by linarith [hx.2]) (le_of_lt (mul_pos hd1 hdx))
    have e0' : Erdos1002.gaussInverseWord w x - Erdos1002.gaussInverseWord w 0
        = -(1 * (x - 0) / (((qC w : ℝ) * x + (qD w : ℝ))
            * ((qC w : ℝ) * 0 + (qD w : ℝ)))) := by
      rw [e0]; ring
    have e1' : Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w x
        = -(1 * (1 - x) / (((qC w : ℝ) * 1 + (qD w : ℝ))
            * ((qC w : ℝ) * x + (qD w : ℝ)))) := by
      rw [e1]; ring
    exact Set.mem_uIcc_of_ge (by linarith) (by linarith)

/-- Upper bound on the measure of a closed depth `n` cylinder by the exact
cylinder length. -/
lemma volume_closedCylinder_le_cylLen {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) :
    volume (Erdos1002.closedGaussPrefixCylinder w) ≤ ENNReal.ofReal (cylLen w) := by
  calc volume (Erdos1002.closedGaussPrefixCylinder w)
      ≤ volume (uIcc (Erdos1002.gaussInverseWord w 0) (Erdos1002.gaussInverseWord w 1)) :=
        measure_mono (closedCylinder_subset_uIcc hpos)
    _ = ENNReal.ofReal |Erdos1002.gaussInverseWord w 1 - Erdos1002.gaussInverseWord w 0| :=
        Real.volume_interval
    _ = ENNReal.ofReal (cylLen w) := by rw [abs_endpoint_gap hpos]

/-- Lower bound on the measure of a half open depth `n` cylinder by the exact
cylinder length.  The two endpoints form a null set, so the half open cylinder
already has the full length. -/
lemma cylLen_le_volume_halfOpen {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) :
    ENNReal.ofReal (cylLen w) ≤ volume (Erdos1002.gaussHalfOpenPrefixCylinder w) := by
  have hconn : IsPreconnected (Erdos1002.gaussInverseWord w '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image _ (continuousOn_gaussInverseWord hpos)
  have hsub1 : uIcc (Erdos1002.gaussInverseWord w 0) (Erdos1002.gaussInverseWord w 1)
      ⊆ Erdos1002.closedGaussPrefixCylinder w :=
    hconn.ordConnected.uIcc_subset ⟨0, by norm_num, rfl⟩ ⟨1, by norm_num, rfl⟩
  have hsub2 : Erdos1002.closedGaussPrefixCylinder w
      ⊆ (Erdos1002.gaussInverseWord w '' Ioo (0 : ℝ) 1)
        ∪ {Erdos1002.gaussInverseWord w 0, Erdos1002.gaussInverseWord w 1} := by
    rintro z ⟨x, hx, rfl⟩
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    rcases eq_or_lt_of_le hx.1 with h | h1
    · exact Or.inr (Or.inl (by rw [← h]))
    · rcases eq_or_lt_of_le hx.2 with h | h2
      · exact Or.inr (Or.inr (by rw [h]))
      · exact Or.inl ⟨x, ⟨h1, h2⟩, rfl⟩
  have hnull : volume ({Erdos1002.gaussInverseWord w 0,
      Erdos1002.gaussInverseWord w 1} : Set ℝ) = 0 :=
    (Set.toFinite _).countable.measure_zero volume
  calc ENNReal.ofReal (cylLen w)
      = volume (uIcc (Erdos1002.gaussInverseWord w 0) (Erdos1002.gaussInverseWord w 1)) := by
        rw [Real.volume_interval, abs_endpoint_gap hpos]
    _ ≤ volume (Erdos1002.closedGaussPrefixCylinder w) := measure_mono hsub1
    _ ≤ volume ((Erdos1002.gaussInverseWord w '' Ioo (0 : ℝ) 1)
          ∪ {Erdos1002.gaussInverseWord w 0, Erdos1002.gaussInverseWord w 1}) :=
        measure_mono hsub2
    _ ≤ volume (Erdos1002.gaussInverseWord w '' Ioo (0 : ℝ) 1)
          + volume ({Erdos1002.gaussInverseWord w 0,
            Erdos1002.gaussInverseWord w 1} : Set ℝ) := measure_union_le _ _
    _ = volume (Erdos1002.gaussInverseWord w '' Ioo (0 : ℝ) 1) := by rw [hnull, add_zero]
    _ ≤ volume (Erdos1002.gaussHalfOpenPrefixCylinder w) :=
        measure_mono (image_Ioo_subset_halfOpen hpos)

/-! ## The sharp mirror comparison -/

/-- **Mirror comparison with the sharp constant.**  Reversing a word transposes
the continuant matrix, so `q_n` is palindromic while `q_{n-1}` is replaced by
`p_n`.  Since `p_n ≤ q_n`, the ratio of the two cylinder lengths is
`(q_n + p_n)/(q_n + q_{n-1}) ≤ 2`. -/
theorem volume_closed_le_two_volume_halfOpen_reverse {w : List ℕ}
    (hpos : ∀ q ∈ w, 0 < q) :
    volume (Erdos1002.closedGaussPrefixCylinder w)
      ≤ 2 * volume (Erdos1002.gaussHalfOpenPrefixCylinder w.reverse) := by
  have hposr : ∀ q ∈ w.reverse, 0 < q := fun q hq => hpos q (List.mem_reverse.mp hq)
  obtain ⟨hA, hB, hC, hD, hBD⟩ := quad_bounds_real hpos
  obtain ⟨r1, r2, r3, r4⟩ := quad_reverse w
  have hcyl : cylLen w.reverse = 1 / ((qD w : ℝ) * ((qB w : ℝ) + (qD w : ℝ))) := by
    rw [cylLen, r3, r4]
  have hposA : (0 : ℝ) < (qD w : ℝ) * ((qC w : ℝ) + (qD w : ℝ)) := by nlinarith
  have hposB : (0 : ℝ) < (qD w : ℝ) * ((qB w : ℝ) + (qD w : ℝ)) := by nlinarith
  have hratio : cylLen w ≤ 2 * cylLen w.reverse := by
    rw [cylLen, hcyl,
      show (2 : ℝ) * (1 / ((qD w : ℝ) * ((qB w : ℝ) + (qD w : ℝ))))
        = 2 / ((qD w : ℝ) * ((qB w : ℝ) + (qD w : ℝ))) from by ring,
      div_le_div_iff₀ hposA hposB]
    nlinarith [mul_le_mul_of_nonneg_left hBD hD.le, mul_nonneg hD.le hC]
  calc volume (Erdos1002.closedGaussPrefixCylinder w)
      ≤ ENNReal.ofReal (cylLen w) := volume_closedCylinder_le_cylLen hpos
    _ ≤ ENNReal.ofReal (2 * cylLen w.reverse) := ENNReal.ofReal_le_ofReal hratio
    _ = 2 * ENNReal.ofReal (cylLen w.reverse) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    _ ≤ 2 * volume (Erdos1002.gaussHalfOpenPrefixCylinder w.reverse) :=
        mul_le_mul_left' (cylLen_le_volume_halfOpen hposr) 2

/-! ## The Fibonacci lower bound for continuants -/

/-- `q_n ≥ F_{n+1}` and `p_n ≥ F_n`, proved simultaneously.  This is the
in-word form of the classical `q_n ≥ F_{n+1}`. -/
lemma fib_le_quad {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) :
    (Nat.fib (w.length + 1) : ℤ) ≤ qD w ∧ (Nat.fib w.length : ℤ) ≤ qB w := by
  induction w with
  | nil => norm_num
  | cons q u ih =>
      have hq : 0 < q := hpos q (by simp)
      have htail : ∀ p ∈ u, 0 < p := fun p hp => hpos p (by simp [hp])
      obtain ⟨h1, h2⟩ := ih htail
      have hq1 : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
      obtain ⟨hA, hB, hC, hD, hBD⟩ := quad_bounds htail
      refine ⟨?_, ?_⟩
      · simp only [qD_cons, List.length_cons]
        have hfib : Nat.fib (u.length + 1 + 1)
            = Nat.fib u.length + Nat.fib (u.length + 1) := Nat.fib_add_two
        rw [hfib]
        push_cast
        nlinarith
      · simpa only [qB_cons, List.length_cons] using h1

/-- The reversed cylinder of a positive word of length `n` has length at most
`F_{n+1}^{-2}`. -/
lemma cylLen_reverse_le_fib {w : List ℕ} (hpos : ∀ q ∈ w, 0 < q) :
    cylLen w.reverse
      ≤ 1 / ((Nat.fib (w.length + 1) : ℝ) * (Nat.fib (w.length + 1) : ℝ)) := by
  obtain ⟨hA, hB, hC, hD, hBD⟩ := quad_bounds_real hpos
  obtain ⟨r1, r2, r3, r4⟩ := quad_reverse w
  have hfibZ : (Nat.fib (w.length + 1) : ℤ) ≤ qD w := (fib_le_quad hpos).1
  have hfibR : (Nat.fib (w.length + 1) : ℝ) ≤ (qD w : ℝ) := by exact_mod_cast hfibZ
  have hfpos : (0 : ℝ) < (Nat.fib (w.length + 1) : ℝ) := by
    have : 0 < Nat.fib (w.length + 1) := Nat.fib_pos.mpr (Nat.succ_pos _)
    exact_mod_cast this
  have hcyl : cylLen w.reverse = 1 / ((qD w : ℝ) * ((qB w : ℝ) + (qD w : ℝ))) := by
    rw [cylLen, r3, r4]
  rw [hcyl]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-! ## Anti-concentration for the backward ratio -/

/-- Depth `n` digit words whose reversed endpoint `[0;a_n,…,a_1]` lies in the
`δ` window around `t`.  A union of complete depth `n` cylinders. -/
def GoodW (t δ : ℝ) (n : ℕ) : Set (List ℕ) :=
  {w | w.length = n ∧ (∀ q ∈ w, 0 < q) ∧
    |Erdos1002.gaussInverseWord w.reverse 0 - t| < δ}

lemma volume_unit_slice_ne_top' (P : ℝ → Prop) :
    volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ P α} ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
  simp [Real.volume_Ioo]

lemma volume_unit_slice_toReal_le_one (P : ℝ → Prop) :
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ P α}).toReal ≤ 1 := by
  have h : (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ P α}).toReal
      ≤ (volume (Ioo (0 : ℝ) 1)).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono (fun x hx => hx.1))
    simp [Real.volume_Ioo]
  simpa [Real.volume_Ioo] using h

/-- Every reversed good cylinder sits in the `δ` window fattened by
`F_{n+1}^{-2}`.  Its left endpoint is exactly the backward ratio of the word. -/
lemma halfOpenRev_subset_window {t δ : ℝ} {n : ℕ} {w : List ℕ}
    (hw : w ∈ GoodW t δ n) :
    Erdos1002.gaussHalfOpenPrefixCylinder w.reverse
      ⊆ Icc (t - δ - 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 1) : ℝ)))
          (t + δ + 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 1) : ℝ))) := by
  obtain ⟨hlen, hpos, hnear⟩ := hw
  have hposr : ∀ q ∈ w.reverse, 0 < q := fun q hq => hpos q (List.mem_reverse.mp hq)
  have hrho : cylLen w.reverse
      ≤ 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 1) : ℝ)) := by
    have h := cylLen_reverse_le_fib hpos
    rwa [hlen] at h
  intro x hx
  have hxc : x ∈ Erdos1002.closedGaussPrefixCylinder w.reverse :=
    Erdos1002.gaussHalfOpenPrefixCylinder_subset_closed hposr hx
  have hxu : x ∈ uIcc (Erdos1002.gaussInverseWord w.reverse 0)
      (Erdos1002.gaussInverseWord w.reverse 1) := closedCylinder_subset_uIcc hposr hxc
  have hgap : |Erdos1002.gaussInverseWord w.reverse 1
      - Erdos1002.gaussInverseWord w.reverse 0| = cylLen w.reverse :=
    abs_endpoint_gap hposr
  obtain ⟨g1, g2⟩ := abs_le.mp (le_of_eq hgap)
  rcases Set.mem_uIcc.mp hxu with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;>
    obtain ⟨h3, h4⟩ := abs_lt.mp hnear <;>
      exact ⟨by linarith, by linarith⟩

/-- **Anti-concentration for the backward continuant ratio.**  This is the
inner estimate of Lemma 3.3: `P(|Y_j - t| < δ) ≤ 4 δ + 4 F_{j+1}^{-2}` with
`Y_j = q_{j-1}/q_j`, written multiplicatively so that no positivity side
condition on `q_j` is needed. -/
theorem backward_ratio_anti_concentration_fib (t : ℝ) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(denom α k : ℝ) - t * (denom α (k + 1) : ℝ)|
          < δ * (denom α (k + 1) : ℝ)}).toReal
      ≤ 4 * δ + 4 * (1 / ((Nat.fib (k + 2) : ℝ) * (Nat.fib (k + 2) : ℝ))) := by
  set ρ : ℝ := 1 / ((Nat.fib (k + 1 + 1) : ℝ) * (Nat.fib (k + 1 + 1) : ℝ)) with hρdef
  have hρpos : 0 < ρ := by
    have : 0 < Nat.fib (k + 1 + 1) := Nat.fib_pos.mpr (Nat.succ_pos _)
    have hR : (0 : ℝ) < (Nat.fib (k + 1 + 1) : ℝ) := by exact_mod_cast this
    rw [hρdef]; positivity
  have hAc : (GoodW t δ (k + 1)).Countable := Set.to_countable _
  have hQnull : volume {x : ℝ | ¬ Irrational x} = 0 := by
    have hset : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
      ext x; simp [Irrational]
    rw [hset]
    exact (Set.countable_range _).measure_zero _
  -- Step 1: the event is covered by complete depth `k+1` cylinders.
  have hcover : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      |(denom α k : ℝ) - t * (denom α (k + 1) : ℝ)| < δ * (denom α (k + 1) : ℝ)}
      ⊆ (⋃ w ∈ GoodW t δ (k + 1), Erdos1002.closedGaussPrefixCylinder w)
        ∪ {x : ℝ | ¬ Irrational x} := by
    rintro α ⟨hα, hineq⟩
    by_cases hirr : Irrational α
    · left
      have hQ : (0 : ℝ) < (denom α (k + 1) : ℝ) := by
        exact_mod_cast denom_pos_AC hα hirr (k + 1)
      have hY : |Yfun α (k + 1) - t| < δ := by
        have hYe : Yfun α (k + 1) = (denom α k : ℝ) / (denom α (k + 1) : ℝ) := rfl
        have key : (denom α k : ℝ) / (denom α (k + 1) : ℝ) - t
            = ((denom α k : ℝ) - t * (denom α (k + 1) : ℝ)) / (denom α (k + 1) : ℝ) := by
          field_simp
        rw [hYe, key, abs_div, abs_of_pos hQ, div_lt_iff₀ hQ]
        exact hineq
      refine Set.mem_biUnion
        (show (revWord α (k + 1)).reverse ∈ GoodW t δ (k + 1) from ?_)
        (mem_closedGaussPrefixCylinder hα hirr (k + 1))
      refine ⟨by rw [List.length_reverse, revWord_length], ?_, ?_⟩
      · intro q hq
        exact revWord_pos hα hirr (k + 1) q (List.mem_reverse.mp hq)
      · rw [List.reverse_reverse, ← Yfun_eq_gaussInverseWord hα hirr]
        exact hY
    · right; exact hirr
  -- Step 2: countable subadditivity.
  have hstep2 : volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      |(denom α k : ℝ) - t * (denom α (k + 1) : ℝ)| < δ * (denom α (k + 1) : ℝ)}
      ≤ ∑' w : GoodW t δ (k + 1),
          volume (Erdos1002.closedGaussPrefixCylinder (w : List ℕ)) := by
    calc volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
            |(denom α k : ℝ) - t * (denom α (k + 1) : ℝ)| < δ * (denom α (k + 1) : ℝ)}
        ≤ volume ((⋃ w ∈ GoodW t δ (k + 1), Erdos1002.closedGaussPrefixCylinder w)
            ∪ {x : ℝ | ¬ Irrational x}) := measure_mono hcover
      _ ≤ volume (⋃ w ∈ GoodW t δ (k + 1), Erdos1002.closedGaussPrefixCylinder w)
            + volume {x : ℝ | ¬ Irrational x} := measure_union_le _ _
      _ = volume (⋃ w ∈ GoodW t δ (k + 1), Erdos1002.closedGaussPrefixCylinder w) := by
            rw [hQnull, add_zero]
      _ ≤ ∑' w : GoodW t δ (k + 1),
            volume (Erdos1002.closedGaussPrefixCylinder (w : List ℕ)) :=
            measure_biUnion_le _ hAc _
  -- Step 3: sharp mirror comparison, term by term.
  have hstep3 : ∑' w : GoodW t δ (k + 1),
        volume (Erdos1002.closedGaussPrefixCylinder (w : List ℕ))
      ≤ ∑' w : GoodW t δ (k + 1),
        2 * volume (Erdos1002.gaussHalfOpenPrefixCylinder (w : List ℕ).reverse) :=
    ENNReal.tsum_le_tsum
      (fun w => volume_closed_le_two_volume_halfOpen_reverse w.2.2.1)
  -- Step 4: the mirrored cylinders are pairwise disjoint.
  have hdisj : (GoodW t δ (k + 1)).PairwiseDisjoint
      (fun w : List ℕ => Erdos1002.gaussHalfOpenPrefixCylinder w.reverse) := by
    intro w1 h1 w2 h2 hne
    refine Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength ?_ ?_ ?_ ?_
    · rw [List.length_reverse, List.length_reverse, h1.1, h2.1]
    · intro q hq; exact h1.2.1 q (List.mem_reverse.mp hq)
    · intro q hq; exact h2.2.1 q (List.mem_reverse.mp hq)
    · intro h
      exact hne (by simpa using congrArg List.reverse h)
  have hstep4 : ∑' w : GoodW t δ (k + 1),
        2 * volume (Erdos1002.gaussHalfOpenPrefixCylinder (w : List ℕ).reverse)
      = 2 * volume (⋃ w ∈ GoodW t δ (k + 1),
          Erdos1002.gaussHalfOpenPrefixCylinder (List.reverse w)) := by
    rw [ENNReal.tsum_mul_left]
    congr 1
    exact (measure_biUnion hAc hdisj
      (fun w _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder _)).symm
  -- Step 5: everything sits in one window.
  have hwin : (⋃ w ∈ GoodW t δ (k + 1),
      Erdos1002.gaussHalfOpenPrefixCylinder (List.reverse w))
      ⊆ Icc (t - δ - ρ) (t + δ + ρ) := by
    refine Set.iUnion₂_subset ?_
    intro w hw
    exact halfOpenRev_subset_window hw
  have hIcc : volume (Icc (t - δ - ρ) (t + δ + ρ))
      = ENNReal.ofReal (2 * δ + 2 * ρ) := by
    rw [Real.volume_Icc]; congr 1; ring
  have hchain : volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      |(denom α k : ℝ) - t * (denom α (k + 1) : ℝ)| < δ * (denom α (k + 1) : ℝ)}
      ≤ 2 * ENNReal.ofReal (2 * δ + 2 * ρ) := by
    refine hstep2.trans (hstep3.trans ?_)
    rw [hstep4, ← hIcc]
    exact mul_le_mul_left' (measure_mono hwin) 2
  have htoReal : (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      |(denom α k : ℝ) - t * (denom α (k + 1) : ℝ)| < δ * (denom α (k + 1) : ℝ)}).toReal
      ≤ 2 * (2 * δ + 2 * ρ) := by
    have hne : (2 : ℝ≥0∞) * ENNReal.ofReal (2 * δ + 2 * ρ) ≠ ⊤ := by
      simp [ENNReal.mul_eq_top]
    have h := ENNReal.toReal_mono hne hchain
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofNat] at h
  have hidx : (k + 1 + 1) = k + 2 := by omega
  rw [hρdef, hidx] at htoReal
  linarith

/-! ## Display (21) -/

/-- **Lemma 3.3, display (21)** in the version 5 form.  For every nonzero
integer pair `(r,s)`, every `j ≥ 1` and every `η > 0`,
`P(|s q_j - r q_{j-1}| < η q_j) ≤ 4 η + 4 F_{j+1}^{-2}`.
No upper restriction on `η` is imposed. -/
theorem shrinking_anti_concentration_v5 (r s : ℤ) (hrs : (r, s) ≠ (0, 0))
    (j : ℕ) (hj : 1 ≤ j) (η : ℝ) (hη : 0 < η) :
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(s : ℝ) * denom α j - (r : ℝ) * denom α (j - 1)| < η * denom α j}).toReal
      ≤ 4 * η + 4 * (1 / ((Nat.fib (j + 1) : ℝ) * (Nat.fib (j + 1) : ℝ))) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hfpos : (0 : ℝ) < (Nat.fib (k + 1 + 1) : ℝ) := by
    have : 0 < Nat.fib (k + 1 + 1) := Nat.fib_pos.mpr (Nat.succ_pos _)
    exact_mod_cast this
  have hρnn : (0 : ℝ)
      ≤ 4 * (1 / ((Nat.fib (k + 1 + 1) : ℝ) * (Nat.fib (k + 1 + 1) : ℝ))) := by positivity
  by_cases hr : r = 0
  · subst hr
    have hs : s ≠ 0 := fun h => hrs (by simp [h])
    by_cases hbig : 1 ≤ η
    · refine le_trans (volume_unit_slice_toReal_le_one
        (fun α => |(s : ℝ) * denom α (k + 1) - ((0 : ℤ) : ℝ) * denom α k|
          < η * denom α (k + 1))) ?_
      linarith
    · push_neg at hbig
      have hempty : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          |(s : ℝ) * denom α (k + 1) - ((0 : ℤ) : ℝ) * denom α k|
            < η * denom α (k + 1)} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro α ⟨-, h⟩
        rw [Int.cast_zero, zero_mul, sub_zero, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (denom α (k + 1) : ℝ))] at h
        have hs1 : (1 : ℝ) ≤ |(s : ℝ)| := by
          have hz : (1 : ℤ) ≤ |s| := Int.one_le_abs (by omega)
          calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
            _ ≤ ((|s| : ℤ) : ℝ) := by exact_mod_cast hz
            _ = |(s : ℝ)| := by push_cast; ring
        have hQ : (0 : ℝ) ≤ (denom α (k + 1) : ℝ) := by positivity
        nlinarith
      rw [hempty]
      simp only [measure_empty, ENNReal.toReal_zero]
      linarith
  · have hrR : ((r : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hr
    have hR1 : (1 : ℝ) ≤ |(r : ℝ)| := by
      have hz : (1 : ℤ) ≤ |r| := Int.one_le_abs (by omega)
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|r| : ℤ) : ℝ) := by exact_mod_cast hz
        _ = |(r : ℝ)| := by push_cast; ring
    have hsub : {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(s : ℝ) * denom α (k + 1) - (r : ℝ) * denom α k| < η * denom α (k + 1)}
        ⊆ {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
          |(denom α k : ℝ) - ((s : ℝ) / (r : ℝ)) * (denom α (k + 1) : ℝ)|
            < η * (denom α (k + 1) : ℝ)} := by
      rintro α ⟨hα, h⟩
      refine ⟨hα, ?_⟩
      set Q : ℝ := (denom α (k + 1) : ℝ) with hQdef
      set P : ℝ := (denom α k : ℝ) with hPdef
      have hQ : (0 : ℝ) ≤ Q := by rw [hQdef]; positivity
      have hkey : (s : ℝ) * Q - (r : ℝ) * P
          = -((r : ℝ) * (P - ((s : ℝ) / (r : ℝ)) * Q)) := by
        field_simp; ring
      rw [hkey, abs_neg, abs_mul] at h
      have hX : (0 : ℝ) ≤ |P - ((s : ℝ) / (r : ℝ)) * Q| := abs_nonneg _
      nlinarith
    calc (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
            |(s : ℝ) * denom α (k + 1) - (r : ℝ) * denom α k|
              < η * denom α (k + 1)}).toReal
        ≤ (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
            |(denom α k : ℝ) - ((s : ℝ) / (r : ℝ)) * (denom α (k + 1) : ℝ)|
              < η * (denom α (k + 1) : ℝ)}).toReal :=
          ENNReal.toReal_mono (volume_unit_slice_ne_top' _) (measure_mono hsub)
      _ ≤ 4 * η + 4 * (1 / ((Nat.fib (k + 2) : ℝ) * (Nat.fib (k + 2) : ℝ))) :=
          backward_ratio_anti_concentration_fib _ _ _ hη
      _ = 4 * η + 4 * (1 / ((Nat.fib (k + 1 + 1) : ℝ) * (Nat.fib (k + 1 + 1) : ℝ))) := by
          norm_num

/-! ## The golden ratio exponential form -/

/-- `φ = (1+√5)/2`. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have h : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  rw [phi]; linarith

lemma one_lt_phi : 1 < phi := by
  have h : (2 : ℝ) ≤ Real.sqrt 5 := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h4, this.symm ▸ h4]
  rw [phi]; linarith

lemma phi_sq : phi ^ 2 = phi + 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [phi]
  field_simp
  nlinarith [h5]

/-- `φ^n ≤ F_{n+2}`, the classical exponential lower bound for Fibonacci. -/
lemma phi_pow_le_fib (n : ℕ) : phi ^ n ≤ (Nat.fib (n + 2) : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        have h : Nat.fib 2 = 1 := rfl
        norm_num [h]
    | 1 =>
        have h : Nat.fib 3 = 2 := rfl
        have h5 : Real.sqrt 5 ≤ 3 := by
          have := Real.sqrt_le_sqrt (show (5 : ℝ) ≤ 9 by norm_num)
          have h9 : Real.sqrt 9 = 3 := by
            rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          linarith [h9 ▸ this]
        rw [h]
        simp only [pow_one, phi]
        push_cast
        linarith
    | (m + 2) =>
        have h1 := ih m (by omega)
        have h2 := ih (m + 1) (by omega)
        have hfib : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 1 + 2) := by
          have := Nat.fib_add_two (n := m + 2)
          simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using this
        have hexp : phi ^ (m + 2) = phi ^ m * phi ^ 2 := by ring
        rw [hfib, hexp, phi_sq]
        push_cast
        have hsplit : phi ^ m * (phi + 1) = phi ^ (m + 1) + phi ^ m := by ring
        rw [hsplit]
        linarith

/-- **Display (21), exponential form.**  With `φ = (1+√5)/2`, the bound of
Lemma 3.3 is at most `C (η + e^{-2 (log φ) j})` with `C = 11`. -/
theorem shrinking_anti_concentration_v5_exp (r s : ℤ) (hrs : (r, s) ≠ (0, 0))
    (j : ℕ) (hj : 1 ≤ j) (η : ℝ) (hη : 0 < η) :
    (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(s : ℝ) * denom α j - (r : ℝ) * denom α (j - 1)| < η * denom α j}).toReal
      ≤ 11 * (η + Real.exp (-(2 * Real.log phi) * j)) := by
  have hmain := shrinking_anti_concentration_v5 r s hrs j hj η hη
  have hphi1 : 1 < phi := one_lt_phi
  have hphi0 : 0 < phi := phi_pos
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  -- `φ^m ≤ F_{m+2} = F_{j+1}`.
  have hfib : phi ^ m ≤ (Nat.fib (m + 1 + 1) : ℝ) := phi_pow_le_fib m
  have hpm : (0 : ℝ) < phi ^ m := pow_pos hphi0 m
  have hkey : 1 / ((Nat.fib (m + 1 + 1) : ℝ) * (Nat.fib (m + 1 + 1) : ℝ))
      ≤ 1 / (phi ^ m * phi ^ m) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  -- `exp (-(2 log φ) (m+1)) = φ^{-2(m+1)}`, so `1/(φ^m)^2 = φ^2 exp(...)`.
  have hexp : Real.exp (-(2 * Real.log phi) * ((m : ℝ) + 1))
      = 1 / (phi ^ (2 * (m + 1))) := by
    rw [eq_div_iff (by positivity)]
    rw [← Real.rpow_natCast phi (2 * (m + 1))]
    rw [Real.rpow_def_of_pos hphi0, ← Real.exp_add]
    rw [show -(2 * Real.log phi) * ((m : ℝ) + 1)
        + Real.log phi * ((2 * (m + 1) : ℕ) : ℝ) = 0 by push_cast; ring]
    simp
  have hpmne : (phi ^ m : ℝ) ≠ 0 := ne_of_gt hpm
  have hp2ne : (phi ^ 2 : ℝ) ≠ 0 := by positivity
  have hrewrite : 1 / (phi ^ m * phi ^ m)
      = phi ^ 2 * (1 / (phi ^ (2 * (m + 1)))) := by
    rw [show 2 * (m + 1) = m + m + 2 from by ring, pow_add, pow_add]
    field_simp
  have hsqrt5 : Real.sqrt 5 ≤ 2.25 := by
    have h := Real.sqrt_le_sqrt (show (5 : ℝ) ≤ 2.25 ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.25)] at h
  have hphisq : phi ^ 2 ≤ 2.625 := by
    rw [phi_sq, phi]; linarith
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.log phi) * ((m : ℝ) + 1)) := Real.exp_pos _
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hstep : 4 * (1 / ((Nat.fib (m + 1 + 1) : ℝ) * (Nat.fib (m + 1 + 1) : ℝ)))
      ≤ 4 * (phi ^ 2 * Real.exp (-(2 * Real.log phi) * ((m : ℝ) + 1))) := by
    have h1 : 1 / ((Nat.fib (m + 1 + 1) : ℝ) * (Nat.fib (m + 1 + 1) : ℝ))
        ≤ phi ^ 2 * Real.exp (-(2 * Real.log phi) * ((m : ℝ) + 1)) := by
      calc 1 / ((Nat.fib (m + 1 + 1) : ℝ) * (Nat.fib (m + 1 + 1) : ℝ))
          ≤ 1 / (phi ^ m * phi ^ m) := hkey
        _ = phi ^ 2 * (1 / (phi ^ (2 * (m + 1)))) := hrewrite
        _ = phi ^ 2 * Real.exp (-(2 * Real.log phi) * ((m : ℝ) + 1)) := by rw [hexp]
    linarith
  have hfin : 4 * (phi ^ 2 * Real.exp (-(2 * Real.log phi) * ((m : ℝ) + 1)))
      ≤ 11 * Real.exp (-(2 * Real.log phi) * ((m : ℝ) + 1)) := by nlinarith [hE, hphisq]
  linarith

/-- Drop-in strengthening of `Kwon1002.shrinking_anti_concentration`.  Same
shape, but with `C = 11` in place of `64`, decay rate `2 log φ = 0.9624…` in
place of `log 2 = 0.6931…`, and no hypothesis `η < 1/2`. -/
theorem shrinking_anti_concentration_v5_exists :
    ∃ C c : ℝ, 0 < c ∧ ∀ r s : ℤ, (r, s) ≠ (0, 0) → ∀ j : ℕ, 1 ≤ j → ∀ η : ℝ,
      0 < η →
      (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(s : ℝ) * denom α j - (r : ℝ) * denom α (j - 1)| < η * denom α j}).toReal
        ≤ C * (η + Real.exp (-c * j)) := by
  refine ⟨11, 2 * Real.log phi, ?_, ?_⟩
  · have h : 0 < Real.log phi := Real.log_pos one_lt_phi
    linarith
  · intro r s hrs j hj η hη
    exact shrinking_anti_concentration_v5_exp r s hrs j hj η hη

end V5Lemma33

end

end Kwon1002
