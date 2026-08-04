import Kwon1002.Statement

/-!
# Gauss-map foundations for §2

The facts every §2 proof needs: the Gauss map keeps irrationals of
`(0,1)` in `(0,1)`, iterates inherit both properties, digits are ≥ 1,
and the defining identity `1/x_j = a_{j+1} + x_{j+1}` holds.
-/

open Set

namespace Kwon1002

noncomputable section

/-- The Gauss map `T x = {1/x}`. -/
def gaussMap (x : ℝ) : ℝ := Int.fract x⁻¹

/-- `x_j = T^j α`. -/
def gaussIter (α : ℝ) (j : ℕ) : ℝ := gaussMap^[j] α

/-- The continued-fraction digit `a_{j+1} = ⌊1/x_j⌋`. -/
def digit (α : ℝ) (j : ℕ) : ℕ := ⌊(gaussIter α j)⁻¹⌋.toNat

@[simp] lemma gaussIter_zero (α : ℝ) : gaussIter α 0 = α := rfl

lemma gaussIter_succ (α : ℝ) (j : ℕ) :
    gaussIter α (j + 1) = gaussMap (gaussIter α j) := by
  simp [gaussIter, Function.iterate_succ_apply']

/-- Irrationality is preserved by the Gauss map. -/
lemma gaussMap_irrational {x : ℝ} (hirr : Irrational x) :
    Irrational (gaussMap x) := by
  have h : gaussMap x = x⁻¹ - (⌊x⁻¹⌋ : ℝ) := rfl
  rw [h]
  exact Irrational.sub_intCast (Irrational.inv hirr) ⌊x⁻¹⌋

/-- Iterates of an irrational are irrational. -/
lemma gaussIter_irrational {α : ℝ} (hirr : Irrational α) (j : ℕ) :
    Irrational (gaussIter α j) := by
  induction j with
  | zero => simpa using hirr
  | succ j ih => rw [gaussIter_succ]; exact gaussMap_irrational ih

/-- The Gauss map of an irrational is in `(0,1)`. -/
lemma gaussMap_mem_Ioo {x : ℝ} (hirr : Irrational x) :
    gaussMap x ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨(Int.fract_nonneg _).lt_of_ne' ?_, Int.fract_lt_one _⟩
  intro h0
  have hd : x⁻¹ - (⌊x⁻¹⌋ : ℝ) = 0 := h0
  exact (hirr.inv.ne_int ⌊x⁻¹⌋) (by linarith)

/-- Iterates of an irrational in `(0,1)` remain in `(0,1)`. -/
lemma gaussIter_mem_Ioo {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (j : ℕ) : gaussIter α j ∈ Ioo (0 : ℝ) 1 := by
  cases j with
  | zero => simpa using hα
  | succ j =>
    rw [gaussIter_succ]
    exact gaussMap_mem_Ioo (gaussIter_irrational hirr j)

/-- For `x_j ∈ (0,1)` the digit is ≥ 1. -/
lemma one_le_digit {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (j : ℕ) : 1 ≤ digit α j := by
  have hj := gaussIter_mem_Ioo hα hirr j
  have h1 : (1 : ℝ) ≤ (gaussIter α j)⁻¹ := by
    rw [le_inv_comm₀ one_pos hj.1]
    simpa using hj.2.le
  have hfl : (1 : ℤ) ≤ ⌊(gaussIter α j)⁻¹⌋ := by
    exact_mod_cast Int.le_floor.mpr (by exact_mod_cast h1)
  simpa [digit] using Int.toNat_le_toNat hfl

/-- The defining split `1/x_j = a_{j+1} + x_{j+1}`. -/
lemma inv_gaussIter_eq {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (j : ℕ) :
    (gaussIter α j)⁻¹ = (digit α j : ℝ) + gaussIter α (j + 1) := by
  have hj := gaussIter_mem_Ioo hα hirr j
  have hfl : (0 : ℤ) ≤ ⌊(gaussIter α j)⁻¹⌋ :=
    Int.floor_nonneg.mpr (inv_nonneg.mpr hj.1.le)
  have hcast : ((⌊(gaussIter α j)⁻¹⌋.toNat : ℕ) : ℝ)
      = ((⌊(gaussIter α j)⁻¹⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfl
  rw [gaussIter_succ]
  unfold gaussMap digit
  rw [hcast]
  unfold Int.fract
  ring

end

end Kwon1002
