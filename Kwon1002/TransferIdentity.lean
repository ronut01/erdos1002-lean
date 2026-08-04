/-
Scratch file (identity agent): Kwon §3, display (14).

Target: `Kwon1002.Transfer.cylinder_transfer_eq_kwonDensity`, the single
sorry of `Kwon1002/TransferMixing.lean`.
-/
import Kwon1002.TransferMixing
import Mathlib.Analysis.BoundedVariation

open MeasureTheory Set
open scoped ENNReal

namespace Kwon1002.TransferIdentity

open Erdos1002 Kwon1002.Transfer

noncomputable section

/-! ## 1. `Ioo 0 1` is invariant under every positive inverse branch -/

theorem gaussInverseBranch_mem_Ioo' {q : ℕ} (hq : 0 < q) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) : gaussInverseBranch q y ∈ Ioo (0 : ℝ) 1 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < (q : ℝ) + y := by linarith [hy.1]
  constructor
  · exact one_div_pos.mpr hden
  · rw [gaussInverseBranch, div_lt_one hden]; linarith [hy.1]

/-! ## 2. Congruence: the transfer iterate only sees `Ioo 0 1` -/

theorem gaussTransfer_congr_Ioo {F G : ℝ → ℝ}
    (h : ∀ z ∈ Ioo (0 : ℝ) 1, F z = G z) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    gaussTransfer F y = gaussTransfer G y := by
  unfold gaussTransfer
  refine tsum_congr fun n => ?_
  rw [h _ (gaussInverseBranch_mem_Ioo' (q := n + 1) (by omega) hy)]

theorem gaussTransfer_iterate_congr_Ioo {F G : ℝ → ℝ}
    (h : ∀ z ∈ Ioo (0 : ℝ) 1, F z = G z) (d : ℕ) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    (gaussTransfer^[d]) F y = (gaussTransfer^[d]) G y := by
  induction d generalizing F G with
  | zero => exact h y hy
  | succ d ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (fun z hz => gaussTransfer_congr_Ioo h hz)

/-! ## 3. Disjointness of the first-digit cylinders -/

theorem firstDigitCylinder_eq_of_mem {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {x : ℝ} (hxq : x ∈ firstDigitCylinder q) (hxr : x ∈ firstDigitCylinder r) :
    q = r := by
  have hu := firstDigitCylinder_subset_unit q hq hxq
  have h1 := (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hu q hq).2 hxq
  have h2 := (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hu r hr).2 hxr
  have : (q : ℤ) = (r : ℤ) := h1.symm.trans h2
  exact_mod_cast this

/-! ## 4. One transfer step strips the head digit -/

theorem gaussTransfer_indicator_cons (q : ℕ) (hq : 0 < q) (v : List ℕ)
    (g : ℝ → ℝ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    gaussTransfer (fun x =>
        (gaussHalfOpenPrefixCylinder (q :: v)).indicator (fun _ => (1 : ℝ)) x * g x) y
      = gaussBranchRatio q y *
          ((gaussHalfOpenPrefixCylinder v).indicator (fun _ => (1 : ℝ)) y *
            g (gaussInverseBranch q y)) := by
  have hyIco : y ∈ Ico (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
  have hkey : ∀ n : ℕ, n ≠ q - 1 →
      gaussBranchRatio (n + 1) y *
        ((gaussHalfOpenPrefixCylinder (q :: v)).indicator (fun _ => (1 : ℝ))
            (gaussInverseBranch (n + 1) y) *
          g (gaussInverseBranch (n + 1) y)) = 0 := by
    intro n hn
    have hnot : gaussInverseBranch (n + 1) y ∉ gaussHalfOpenPrefixCylinder (q :: v) := by
      intro hmem
      have h1 : gaussInverseBranch (n + 1) y ∈ firstDigitCylinder (n + 1) :=
        gaussInverseBranch_mem_firstDigitCylinder hyIco (n + 1) (by omega)
      have h2 : gaussInverseBranch (n + 1) y ∈ firstDigitCylinder q := hmem.1
      have := firstDigitCylinder_eq_of_mem (by omega : 0 < n + 1) hq h1 h2
      omega
    rw [Set.indicator_of_notMem hnot]
    ring
  unfold gaussTransfer
  rw [tsum_eq_single (q - 1) hkey]
  have hq1 : q - 1 + 1 = q := by omega
  rw [hq1]
  have hmem1 : gaussInverseBranch q y ∈ firstDigitCylinder q :=
    gaussInverseBranch_mem_firstDigitCylinder hyIco q hq
  have hmap : gaussMap (gaussInverseBranch q y) = y :=
    gaussMap_gaussInverseBranch hyIco q hq
  by_cases hv : y ∈ gaussHalfOpenPrefixCylinder v
  · have hmem : gaussInverseBranch q y ∈ gaussHalfOpenPrefixCylinder (q :: v) := by
      refine ⟨hmem1, ?_⟩
      show gaussMap (gaussInverseBranch q y) ∈ gaussHalfOpenPrefixCylinder v
      rw [hmap]; exact hv
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hv]
  · have hnot : gaussInverseBranch q y ∉ gaussHalfOpenPrefixCylinder (q :: v) := by
      intro hmem
      apply hv
      have : gaussMap (gaussInverseBranch q y) ∈ gaussHalfOpenPrefixCylinder v := hmem.2
      rwa [hmap] at this
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hv]

/-! ## 5. The depth-`d` transfer of a cylinder indicator

`branchJac w` is the Jacobian factor `∏_j ρ_{a_j}` picked up along the
inverse word; it is the (unnormalized) `ν`-density Kwon writes as `ρ_w`. -/

def branchJac : List ℕ → ℝ → ℝ
  | [], _ => 1
  | q :: v, y => gaussBranchRatio q (gaussInverseWord v y) * branchJac v y

@[simp] theorem branchJac_nil (y : ℝ) : branchJac [] y = 1 := rfl

@[simp] theorem branchJac_cons (q : ℕ) (v : List ℕ) (y : ℝ) :
    branchJac (q :: v) y =
      gaussBranchRatio q (gaussInverseWord v y) * branchJac v y := rfl

theorem transfer_iterate_indicator_mul (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (g : ℝ → ℝ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (gaussTransfer^[w.length]) (fun x =>
        (gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ)) x * g x) y
      = branchJac w y * g (gaussInverseWord w y) := by
  induction w generalizing g y with
  | nil =>
      have hmem : y ∈ gaussHalfOpenPrefixCylinder ([] : List ℕ) := ⟨hy.1.le, hy.2⟩
      simp [Set.indicator_of_mem hmem, gaussInverseWord]
  | cons q v ih =>
      have hq : 0 < q := hw q (by simp)
      have hv : ∀ r ∈ v, 0 < r := fun r hr => hw r (by simp [hr])
      have hlen : (q :: v).length = v.length + 1 := rfl
      rw [hlen, Function.iterate_succ_apply]
      have hstep : ∀ z ∈ Ioo (0 : ℝ) 1,
          gaussTransfer (fun x =>
              (gaussHalfOpenPrefixCylinder (q :: v)).indicator (fun _ => (1 : ℝ)) x * g x) z
            = (gaussHalfOpenPrefixCylinder v).indicator (fun _ => (1 : ℝ)) z *
                (gaussBranchRatio q z * g (gaussInverseBranch q z)) := by
        intro z hz
        rw [gaussTransfer_indicator_cons q hq v g hz]
        ring
      rw [gaussTransfer_iterate_congr_Ioo hstep v.length hy,
        ih hv (fun z => gaussBranchRatio q z * g (gaussInverseBranch q z)) hy]
      show branchJac v y * _ = gaussBranchRatio q (gaussInverseWord v y) * branchJac v y *
        g (gaussInverseBranch q (gaussInverseWord v y))
      ring

theorem transfer_iterate_indicator (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (gaussTransfer^[w.length])
        ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) y
      = branchJac w y := by
  have h := transfer_iterate_indicator_mul w hw (fun _ => (1 : ℝ)) hy
  simpa using h

/-! ## 6. The Möbius data of a digit word (continuants) -/

structure Mob where
  P : ℝ
  P' : ℝ
  Q : ℝ
  Q' : ℝ

def mob : List ℕ → Mob
  | [] => ⟨0, 1, 1, 0⟩
  | q :: v => ⟨(mob v).Q, (mob v).Q', (q : ℝ) * (mob v).Q + (mob v).P,
      (q : ℝ) * (mob v).Q' + (mob v).P'⟩

@[simp] theorem mob_nil_P : (mob []).P = 0 := rfl
@[simp] theorem mob_nil_P' : (mob []).P' = 1 := rfl
@[simp] theorem mob_nil_Q : (mob []).Q = 1 := rfl
@[simp] theorem mob_nil_Q' : (mob []).Q' = 0 := rfl

@[simp] theorem mob_cons_P (q : ℕ) (v : List ℕ) : (mob (q :: v)).P = (mob v).Q := rfl
@[simp] theorem mob_cons_P' (q : ℕ) (v : List ℕ) : (mob (q :: v)).P' = (mob v).Q' := rfl
@[simp] theorem mob_cons_Q (q : ℕ) (v : List ℕ) :
    (mob (q :: v)).Q = (q : ℝ) * (mob v).Q + (mob v).P := rfl
@[simp] theorem mob_cons_Q' (q : ℕ) (v : List ℕ) :
    (mob (q :: v)).Q' = (q : ℝ) * (mob v).Q' + (mob v).P' := rfl

theorem mob_ok (w : List ℕ) (hw : ∀ q ∈ w, 0 < q) :
    0 ≤ (mob w).P ∧ 0 ≤ (mob w).P' ∧ 0 < (mob w).Q ∧ 0 ≤ (mob w).Q' ∧
      (mob w).Q' ≤ (mob w).Q ∧ (mob w).Q' + (mob w).P' ≤ (mob w).Q + (mob w).P := by
  induction w with
  | nil => norm_num
  | cons q v ih =>
      have hq : 0 < q := hw q (by simp)
      have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      obtain ⟨hP, hP', hQ, hQ', hQQ, hsum⟩ := ih (fun r hr => hw r (by simp [hr]))
      have hkey : (q : ℝ) * (mob v).Q' + (mob v).P'
          ≤ (q : ℝ) * (mob v).Q + (mob v).P := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hqR) (sub_nonneg.mpr hQQ)]
      simp only [mob_cons_P, mob_cons_P', mob_cons_Q, mob_cons_Q']
      exact ⟨hQ.le, hQ', by nlinarith, by nlinarith, hkey, by linarith⟩

theorem mob_denomP {w : List ℕ} (hw : ∀ q ∈ w, 0 < q) {y : ℝ} (hy : 0 ≤ y) :
    0 < (mob w).Q + (mob w).Q' * y := by
  obtain ⟨_, _, hQ, hQ', _, _⟩ := mob_ok w hw
  nlinarith

theorem mob_denomM {w : List ℕ} (hw : ∀ q ∈ w, 0 < q) {y : ℝ} (hy : 0 ≤ y) :
    0 < ((mob w).Q + (mob w).P) + ((mob w).Q' + (mob w).P') * y := by
  obtain ⟨hP, hP', hQ, hQ', _, _⟩ := mob_ok w hw
  nlinarith

theorem add_div_eq {t X N : ℝ} (hN : N ≠ 0) : t + X / N = (t * N + X) / N := by
  rw [add_div, mul_div_assoc, div_self hN, mul_one]

theorem gaussInverseWord_eq_mob (w : List ℕ) (hw : ∀ q ∈ w, 0 < q) {y : ℝ}
    (hy : 0 ≤ y) :
    gaussInverseWord w y
      = ((mob w).P + (mob w).P' * y) / ((mob w).Q + (mob w).Q' * y) := by
  induction w with
  | nil => simp [gaussInverseWord]
  | cons q v ih =>
      have hv : ∀ r ∈ v, 0 < r := fun r hr => hw r (by simp [hr])
      have hN : (0 : ℝ) < (mob v).Q + (mob v).Q' * y := mob_denomP hv hy
      have hN1 : (0 : ℝ) < (mob (q :: v)).Q + (mob (q :: v)).Q' * y :=
        mob_denomP hw hy
      have hN0 : (mob v).Q + (mob v).Q' * y ≠ 0 := ne_of_gt hN
      have hden : (q : ℝ) + ((mob v).P + (mob v).P' * y) / ((mob v).Q + (mob v).Q' * y)
          = ((q : ℝ) * (mob v).Q + (mob v).P
              + ((q : ℝ) * (mob v).Q' + (mob v).P') * y)
            / ((mob v).Q + (mob v).Q' * y) := by
        rw [add_div_eq hN0]
        congr 1
        ring
      show gaussInverseBranch q (gaussInverseWord v y) = _
      rw [gaussInverseBranch, ih hv, hden, one_div_div]
      simp only [mob_cons_P, mob_cons_P', mob_cons_Q, mob_cons_Q']

/-! ## 7. The algebraic core of the change of variables -/

theorem mobius_step {N M N₁ M₁ u qr z : ℝ} (hN : N ≠ 0) (hM : M ≠ 0)
    (hN₁ : N₁ ≠ 0) (hM₁ : M₁ ≠ 0) (h1 : 1 + u = M / N) (h2 : qr + u = N₁ / N)
    (h3 : qr + u + 1 = M₁ / N) :
    (1 + u) / ((qr + u) * (qr + u + 1)) * (z / (M * N)) = z / (M₁ * N₁) := by
  rw [h3, h2, h1]
  field_simp

theorem branchJac_eq_mob (w : List ℕ) (hw : ∀ q ∈ w, 0 < q) {y : ℝ} (hy : 0 ≤ y) :
    branchJac w y = (1 + y) /
      ((((mob w).Q + (mob w).P) + ((mob w).Q' + (mob w).P') * y) *
        ((mob w).Q + (mob w).Q' * y)) := by
  induction w with
  | nil =>
      have h : ((1 : ℝ) + y) ≠ 0 := by linarith
      show (1 : ℝ) = _
      simp only [mob_nil_P, mob_nil_P', mob_nil_Q, mob_nil_Q']
      rw [show ((1 : ℝ) + 0 + (0 + 1) * y) * (1 + 0 * y) = 1 + y by ring, div_self h]
  | cons q v ih =>
      have hq : 0 < q := hw q (by simp)
      have hv : ∀ r ∈ v, 0 < r := fun r hr => hw r (by simp [hr])
      set m := mob v with hm
      have hN : (0 : ℝ) < m.Q + m.Q' * y := mob_denomP hv hy
      have hM : (0 : ℝ) < (m.Q + m.P) + (m.Q' + m.P') * y := mob_denomM hv hy
      have hN1 : (0 : ℝ) < ((q : ℝ) * m.Q + m.P) + ((q : ℝ) * m.Q' + m.P') * y := by
        have := mob_denomP hw hy
        simpa using this
      have hM1 : (0 : ℝ) <
          (((q : ℝ) * m.Q + m.P) + m.Q) + (((q : ℝ) * m.Q' + m.P') + m.Q') * y := by
        have := mob_denomM hw hy
        simpa using this
      have hN0 : m.Q + m.Q' * y ≠ 0 := ne_of_gt hN
      have hu : gaussInverseWord v y = (m.P + m.P' * y) / (m.Q + m.Q' * y) :=
        gaussInverseWord_eq_mob v hv hy
      have h1 : 1 + gaussInverseWord v y
          = ((m.Q + m.P) + (m.Q' + m.P') * y) / (m.Q + m.Q' * y) := by
        rw [hu, add_div_eq hN0]; congr 1; ring
      have h2 : (q : ℝ) + gaussInverseWord v y
          = (((q : ℝ) * m.Q + m.P) + ((q : ℝ) * m.Q' + m.P') * y) / (m.Q + m.Q' * y) := by
        rw [hu, add_div_eq hN0]; congr 1; ring
      have h3 : (q : ℝ) + gaussInverseWord v y + 1
          = ((((q : ℝ) * m.Q + m.P) + m.Q) + (((q : ℝ) * m.Q' + m.P') + m.Q') * y)
              / (m.Q + m.Q' * y) := by
        have hre : (q : ℝ) + gaussInverseWord v y + 1
            = ((q : ℝ) + 1) + gaussInverseWord v y := by ring
        rw [hre, hu, add_div_eq hN0]; congr 1; ring
      rw [branchJac_cons, ih hv, gaussBranchRatio]
      simp only [mob_cons_P, mob_cons_P', mob_cons_Q, mob_cons_Q']
      exact mobius_step (ne_of_gt hN) (ne_of_gt hM) (ne_of_gt hN1) (ne_of_gt hM1)
        h1 h2 h3

/-! ## 8. `branchJac w` is a Kwon weight -/

theorem kwon_shape {Q R N M z : ℝ} (hQ : Q ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hM : M ≠ 0) :
    z / (M * N) = 1 / (Q * R) * (z / (N / Q * (M / R))) := by
  field_simp

theorem branchJac_eq_kwonWeight (w : List ℕ) (hw : ∀ q ∈ w, 0 < q) :
    ∃ a b c : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ 0 < c ∧
      ∀ y : ℝ, 0 ≤ y → branchJac w y = c * kwonWeight a b y := by
  obtain ⟨hP, hP', hQ, hQ', hQQ, hsum⟩ := mob_ok w hw
  have hQP : (0 : ℝ) < (mob w).Q + (mob w).P := by linarith
  refine ⟨(mob w).Q' / (mob w).Q,
    ((mob w).Q' + (mob w).P') / ((mob w).Q + (mob w).P),
    1 / ((mob w).Q * ((mob w).Q + (mob w).P)),
    ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩, by positivity, ?_⟩
  · rw [div_le_one hQ]; exact hQQ
  · rw [div_le_one hQP]; exact hsum
  · intro y hy
    have hN : (0 : ℝ) < (mob w).Q + (mob w).Q' * y := mob_denomP hw hy
    have hM : (0 : ℝ) < (mob w).Q + (mob w).P + ((mob w).Q' + (mob w).P') * y :=
      mob_denomM hw hy
    have e1 : 1 + (mob w).Q' / (mob w).Q * y
        = ((mob w).Q + (mob w).Q' * y) / (mob w).Q := by
      rw [div_mul_eq_mul_div, add_div_eq (ne_of_gt hQ)]
      congr 1; ring
    have e2 : 1 + ((mob w).Q' + (mob w).P') / ((mob w).Q + (mob w).P) * y
        = ((mob w).Q + (mob w).P + ((mob w).Q' + (mob w).P') * y)
            / ((mob w).Q + (mob w).P) := by
      rw [div_mul_eq_mul_div, add_div_eq (ne_of_gt hQP)]
      congr 1; ring
    rw [branchJac_eq_mob w hw hy, kwonWeight, e1, e2]
    exact kwon_shape (ne_of_gt hQ) (ne_of_gt hQP) (ne_of_gt hN) (ne_of_gt hM)

/-! ## 9. `ν`-almost every point is interior -/

theorem gaussMeasure_ae_Ioo : ∀ᵐ y ∂gaussMeasure, y ∈ Ioo (0 : ℝ) 1 := by
  have h1 : gaussMeasure {(1 : ℝ)} = 0 := by
    rw [gaussMeasure_eq_volume_withDensity]
    exact withDensity_absolutelyContinuous volume gaussDensity (by simp)
  have h2 : ∀ᵐ y ∂gaussMeasure, y ≠ (1 : ℝ) := by
    rw [ae_iff]; simpa using h1
  filter_upwards [gaussMeasure_unit_ae, h2] with y hy hy1
  exact ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩

/-! ## 10. Kwon's display (14), on the interior

This is `Kwon1002.Transfer.cylinder_transfer_eq_kwonDensity` with `Icc`
replaced by `Ioo`, see §12 below: the `Icc` form is false at `y = 1`. -/

theorem cylinder_transfer_eq_kwonDensity_Ioo (w : List ℕ) (hw : ∀ q ∈ w, 0 < q) :
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧
      ∀ y ∈ Ioo (0 : ℝ) 1,
        (gaussTransfer^[w.length])
            ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) y
          = (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal *
              kwonDensity a b y := by
  obtain ⟨a, b, c, ha, hb, hc, hid⟩ := branchJac_eq_kwonWeight w hw
  refine ⟨a, b, ha, hb, ?_⟩
  have hSm : MeasurableSet (gaussHalfOpenPrefixCylinder w) :=
    measurableSet_gaussHalfOpenPrefixCylinder w
  have hfM : Measurable
      ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hSm
  have hf0 : GaussUnitNonnegative
      ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) := fun x _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hf1 : GaussUnitUpperBound 1
      ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) := by
    intro x _
    by_cases hx : x ∈ gaussHalfOpenPrefixCylinder w
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- the transfer operator preserves total mass
  have hmass : (∫ y, (gaussTransfer^[w.length])
        ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) y ∂gaussMeasure)
      = (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal := by
    have h := integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate hfM
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))) hf0 hf1 w.length
    simp only [mul_one] at h
    rw [← h, integral_indicator_const (1 : ℝ) hSm]
    simp [measureReal_def]
  -- and it computes the normalizing constant
  have hZ := kwonNorm_bounds ha hb
  have hZ0 : (0 : ℝ) < kwonNorm a b := by linarith [hZ.1]
  have hint : (∫ y, (gaussTransfer^[w.length])
        ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) y ∂gaussMeasure)
      = c * kwonNorm a b := by
    rw [kwonNorm, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [gaussMeasure_ae_Ioo] with y hy
    rw [transfer_iterate_indicator w hw hy, hid y hy.1.le]
  have hcz : c * kwonNorm a b
      = (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal := by
    rw [← hint, hmass]
  intro y hy
  rw [transfer_iterate_indicator w hw hy, hid y hy.1.le, ← hcz, kwonDensity]
  field_simp

/-! ## 11. Downstream: `IsCondDensity` and Lemma 3.2, unconditionally

`Kwon1002.Transfer.isCondDensity_of_transfer_eq` asks for the identity on
all of `Icc 0 1`; it only ever uses it `ν`-almost everywhere, so the `Ioo`
form below suffices.  Everything from here on is the TransferMixing proof
verbatim, with `gaussMeasure_ae_Ioo` in place of `gaussMeasure_unit_ae`. -/

theorem isCondDensity_of_transfer_eq_Ioo {S : Set ℝ} (hS : MeasurableSet S) {d : ℕ}
    (hSpos : 0 < (gaussMeasure S).toReal) {a b : ℝ}
    (hid : ∀ y ∈ Ioo (0 : ℝ) 1,
      (gaussTransfer^[d]) (S.indicator (fun _ => (1 : ℝ))) y
        = (gaussMeasure S).toReal * kwonDensity a b y) :
    IsCondDensity S d (kwonDensity a b) := by
  intro F hF
  set f : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ)) with hf
  have hfM : Measurable f := measurable_const.indicator hS
  have hf0 : GaussUnitNonnegative f := fun x _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hf1 : GaussUnitUpperBound 1 f := by
    intro x _
    by_cases hx : x ∈ S
    · simp [hf, Set.indicator_of_mem hx]
    · simp [hf, Set.indicator_of_notMem hx]
  have hind : ∀ x : ℝ,
      f x * F (gaussOrbit d x) = S.indicator (fun z => F (gaussOrbit d z)) x := by
    intro x
    by_cases hx : x ∈ S
    · simp [hf, Set.indicator_of_mem hx]
    · simp [hf, Set.indicator_of_notMem hx]
  have h1 : (∫ x in S, F (gaussOrbit d x) ∂gaussMeasure)
      = ∫ x, f x * F (gaussOrbit d x) ∂gaussMeasure := by
    simp_rw [hind]
    exact (integral_indicator hS).symm
  have h2 : (∫ x, f x * F (gaussOrbit d x) ∂gaussMeasure)
      = ∫ y, ((gaussTransfer^[d]) f y) * F y ∂gaussMeasure :=
    integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate hfM hF hf0 hf1 d
  have h3 : (∫ y, ((gaussTransfer^[d]) f y) * F y ∂gaussMeasure)
      = (gaussMeasure S).toReal * ∫ y, kwonDensity a b y * F y ∂gaussMeasure := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [gaussMeasure_ae_Ioo] with y hy
    rw [hid y hy]
    ring
  rw [condMean, h1, h2, h3, mul_comm, mul_div_assoc, div_self (ne_of_gt hSpos),
    mul_one]

theorem exists_cylinder_condDensity' (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal) :
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧
      IsCondDensity (gaussHalfOpenPrefixCylinder w) w.length (kwonDensity a b) := by
  obtain ⟨a, b, ha, hb, hid⟩ := cylinder_transfer_eq_kwonDensity_Ioo w hw
  exact ⟨a, b, ha, hb, isCondDensity_of_transfer_eq_Ioo
    (measurableSet_gaussHalfOpenPrefixCylinder w) hpos hid⟩

/-- **Lemma 3.2**, now unconditional.  The statement is reproduced
token-identically from `Kwon1002.Transfer.lemma_3_2` (only the name is
primed); its proof there consumes the sorried `exists_cylinder_condDensity`,
this one consumes nothing. -/
theorem lemma_3_2' (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal)
    (A K : ℝ) (hAA : 8 ≤ A) (hKK : 24 ≤ K) (M : ℕ)
    (blocks : List (ℕ × (ℝ → ℝ)))
    (hM : ∀ p ∈ blocks, Measurable p.2)
    (h0 : ∀ p ∈ blocks, GaussUnitNonnegative p.2)
    (hAb : ∀ p ∈ blocks, GaussUnitUpperBound A p.2)
    (hKb : ∀ p ∈ blocks, GaussUnitLipschitzBound K p.2)
    (hgap : ∀ p ∈ blocks, M ≤ p.1) :
    |condMean (gaussHalfOpenPrefixCylinder w)
        (fun α => blockProduct blocks (gaussOrbit w.length α)) - blockMean blocks|
      ≤ (blocks.length : ℝ) *
          ((527 / 540 : ℝ) ^ M * K * A ^ blocks.length) := by
  obtain ⟨a, b, ha, hb, hrep⟩ := exists_cylinder_condDensity' w hw hpos
  exact conditional_multiblock_mixing (by linarith) M
    (measurable_kwonDensity a b) (kwonDensity_nonneg ha hb)
    (gaussUnitUpperBound_mono (kwonDensity_le ha hb) hAA)
    (gaussUnitLipschitzBound_mono (kwonDensity_lipschitz ha hb) hKK)
    (kwonDensity_integral_eq_one ha hb) hrep blocks hM h0 hAb hKb hgap

/-! ## 12. The `Icc` form of the target is false at `y = 1` -/

theorem cylinder_one_eq : gaussHalfOpenPrefixCylinder [1] = firstDigitCylinder 1 := by
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem transfer_cylinder_one_at_one :
    (gaussTransfer^[([1] : List ℕ).length])
        ((gaussHalfOpenPrefixCylinder [1]).indicator (fun _ => (1 : ℝ))) 1 = 0 := by
  have hlen : ([1] : List ℕ).length = 1 := rfl
  rw [hlen, Function.iterate_one]
  have hz : ∀ n : ℕ,
      gaussBranchRatio (n + 1) 1 *
        (gaussHalfOpenPrefixCylinder [1]).indicator (fun _ => (1 : ℝ))
          (gaussInverseBranch (n + 1) 1) = 0 := by
    intro n
    have hnot : gaussInverseBranch (n + 1) 1 ∉ gaussHalfOpenPrefixCylinder [1] := by
      rw [cylinder_one_eq]
      intro hmem
      have h : (1 : ℝ) / ((1 + 1 : ℕ) : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) + 1) := hmem.1
      have hc1 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
      have hc2 : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
      rw [hc1, hc2] at h
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hle : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    rw [Set.indicator_of_notMem hnot, mul_zero]
  simp [gaussTransfer, hz]

theorem gaussMeasure_cylinder_one_pos :
    0 < (gaussMeasure (gaussHalfOpenPrefixCylinder [1])).toReal := by
  have h := gaussMeasure_real_firstDigitCylinder 1 one_pos
  rw [cylinder_one_eq, ← measureReal_def, h]
  refine div_pos (Real.log_pos ?_) (Real.log_pos (by norm_num))
  norm_num

/-- **Finding.**  The `Icc 0 1` form of
`Kwon1002.Transfer.cylinder_transfer_eq_kwonDensity` is false: at `y = 1`
every inverse branch `y ↦ 1/(n+1+y)` lands on the *right endpoint* of the
first-digit cylinder of `n+2`, so the depth-`1` transfer of `1_{I_[1]}`
vanishes at `y = 1`, while the right-hand side is `≥ ν(I_[1])/8 > 0`. -/
theorem cylinder_transfer_eq_kwonDensity_Icc_false :
    ¬ (∀ (w : List ℕ), (∀ q ∈ w, 0 < q) →
        ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧
          ∀ y ∈ Icc (0 : ℝ) 1,
            (gaussTransfer^[w.length])
                ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) y
              = (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal *
                  kwonDensity a b y) := by
  intro h
  obtain ⟨a, b, ha, hb, hid⟩ := h [1] (by intro q hq; simp at hq; omega)
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hlhs := transfer_cylinder_one_at_one
  have hkey := hid 1 h1
  rw [hlhs] at hkey
  have hW := (kwonWeight_bounds ha hb h1).1
  have hZ := kwonNorm_bounds ha hb
  have hZ0 : (0 : ℝ) < kwonNorm a b := by linarith [hZ.1]
  have hD : (0 : ℝ) < kwonDensity a b 1 := by
    rw [kwonDensity]
    exact div_pos (by linarith) hZ0
  have hM := gaussMeasure_cylinder_one_pos
  nlinarith [hkey, hD, hM]

/-! ## 13. The bridge to `Kwon1002.Prop41.lem_3_2_conditional_multiblock_mixing`

`Prop41` states its mixing input over the class

  `BVBoundedBy K g := (∀ x ∈ Ioo 0 1, |g x| ≤ K) ∧
     eVariationOn g (Ioo 0 1) ≤ ENNReal.ofReal K`

(reproduced token-identically as `BVBoundedBy'` below; `Kwon1002.Prop41` is
deliberately *not* imported, because it is in namespace `Kwon1002` and
`Kwon1002.gaussMap` would make every bare `gaussMap` above ambiguous).

`lemma_3_2'` above is stated over `GaussUnitUpperBound A` +
`GaussUnitLipschitzBound K`.  The two do **not** align, and the mismatch is
not bookkeeping: the second is strictly smaller than the first, and §4's
actual observables live in the difference.  The two theorems below make
that precise, on the very function §4 feeds in (a first-digit indicator,
manuscript lines ≈ 334 and 369). -/

def BVBoundedBy' (K : ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ K) ∧
    eVariationOn g (Ioo (0 : ℝ) 1) ≤ ENNReal.ofReal K

theorem firstDigitCylinder_one_eq : firstDigitCylinder 1 = Ioc (1 / 2 : ℝ) 1 := by
  rw [firstDigitCylinder]
  norm_num

/-- The first-digit indicator lies in Kwon's class `BV(0,1)`, with norm `1`. -/
theorem firstDigitIndicator_bv :
    BVBoundedBy' 1 ((firstDigitCylinder 1).indicator (fun _ => (1 : ℝ))) := by
  rw [firstDigitCylinder_one_eq]
  constructor
  · intro x _
    by_cases hx : x ∈ Ioc (1 / 2 : ℝ) 1
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  · have hmono : MonotoneOn ((Ioc (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)))
        (Icc (0 : ℝ) 1) := by
      intro x _ y hy hxy
      by_cases hx1 : x ∈ Ioc (1 / 2 : ℝ) 1
      · have hy1 : y ∈ Ioc (1 / 2 : ℝ) 1 := ⟨lt_of_lt_of_le hx1.1 hxy, hy.2⟩
        rw [Set.indicator_of_mem hx1, Set.indicator_of_mem hy1]
      · rw [Set.indicator_of_notMem hx1]
        by_cases hy1 : y ∈ Ioc (1 / 2 : ℝ) 1
        · rw [Set.indicator_of_mem hy1]; norm_num
        · rw [Set.indicator_of_notMem hy1]
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hle := hmono.eVariationOn_le h0 h1
    rw [Set.inter_self] at hle
    have hv0 : (Ioc (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) 0 = 0 := by
      rw [Set.indicator_of_notMem]; norm_num
    have hv1 : (Ioc (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) 1 = 1 := by
      rw [Set.indicator_of_mem]; constructor <;> norm_num
    rw [hv0, hv1] at hle
    refine le_trans (eVariationOn.mono _ ?_) (le_trans hle (by norm_num))
    exact Ioo_subset_Icc_self

/-- …but it is **not** Lipschitz on `[0,1]` for any constant, so it is
outside the class `lemma_3_2'` (and hence Wang's Lasota-Yorke contraction,
which is proved for the Lipschitz seminorm) can accept. -/
theorem firstDigitIndicator_not_lipschitz :
    ¬ ∃ K : ℝ, GaussUnitLipschitzBound K
        ((firstDigitCylinder 1).indicator (fun _ => (1 : ℝ))) := by
  rintro ⟨K, hK⟩
  rw [firstDigitCylinder_one_eq] at hK
  have hK0 : (0 : ℝ) < |K| + 1 := by positivity
  set ε : ℝ := 1 / (2 * (|K| + 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεhalf : ε ≤ 1 / 2 := by
    rw [hε]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [abs_nonneg K])
  have hy : (1 / 2 + ε) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hz : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hmem : (1 / 2 + ε) ∈ Ioc (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hnot : (1 / 2 : ℝ) ∉ Ioc (1 / 2 : ℝ) 1 := by
    intro h; exact absurd h.1 (lt_irrefl _)
  have h := hK hy hz
  rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot] at h
  have habs2 : |(1 / 2 + ε) - (1 / 2 : ℝ)| = ε := by
    rw [show (1 / 2 + ε) - (1 / 2 : ℝ) = ε by ring, abs_of_pos hε0]
  rw [habs2] at h
  have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [h1] at h
  have hKe : K * ε ≤ |K| * ε := mul_le_mul_of_nonneg_right (le_abs_self K) hε0.le
  have hlt : |K| * ε < 1 := by
    have : |K| * ε = |K| / (2 * (|K| + 1)) := by rw [hε]; ring
    rw [this, div_lt_one (by positivity)]
    linarith [abs_nonneg K]
  linarith

end

end Kwon1002.TransferIdentity
