/-
Copyright (c) 2026 Shouqiao Wang. All rights reserved.
Released under the MIT License.
Author: Shouqiao Wang.

Vendored VERBATIM (this header excepted) from
  https://github.com/ShouqiaoW/erdos  @ d28713ac8245ca86a686b8c67370a8d19d81b242
  original path: 1002/lean/Erdos1002/GaussPrefixApproximation.lean
for use as shared infrastructure in the Kwon Erdős-1002 formalization.
Not our work; see wang_substrate/PROVENANCE.md.
-/
import Erdos1002.GaussLebesgueTransfer

/-!
# Oscillation of the Lebesgue-to-Gauss transfer weight

The transfer density `g(x) = log 2 * (1+x)` is affine.  Hence on every
continued-fraction cylinder its representative-point approximation has an
explicit error equal to `log 2` times the cylinder diameter.  The actual
cylinder diameter estimate can be supplied independently.
-/

open Set

namespace Erdos1002

noncomputable section

/-- Exact oscillation identity for the transfer weight. -/
theorem abs_gaussLebesguePrefixWeight_sub
    (x y : ℝ) :
    |gaussLebesguePrefixWeight x - gaussLebesguePrefixWeight y| =
      Real.log 2 * |x - y| := by
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  unfold gaussLebesguePrefixWeight lebesgueOverGaussDensityReal
  rw [show Real.log 2 * (1 + x) - Real.log 2 * (1 + y) =
      Real.log 2 * (x - y) by ring,
    abs_mul, abs_of_nonneg hlog]

/-- Diameter form used on one cylinder. -/
theorem abs_gaussLebesguePrefixWeight_sub_le_of_dist
    {x y d : ℝ} (hxy : dist x y ≤ d) :
    |gaussLebesguePrefixWeight x - gaussLebesguePrefixWeight y| ≤
      Real.log 2 * d := by
  rw [abs_gaussLebesguePrefixWeight_sub]
  rw [Real.dist_eq] at hxy
  exact mul_le_mul_of_nonneg_left hxy (Real.log_pos (by norm_num)).le

/-- Uniform representative-point approximation on any family of sets with
a common diameter bound. -/
theorem abs_gaussLebesguePrefixWeight_sub_representative_le
    {ι : Type*} (C : ι → Set ℝ) (c : ι → ℝ) {d : ℝ}
    (hdiam : ∀ i x, x ∈ C i → dist x (c i) ≤ d) :
    ∀ i x, x ∈ C i →
      |gaussLebesguePrefixWeight x - gaussLebesguePrefixWeight (c i)| ≤
        Real.log 2 * d := by
  intro i x hx
  exact abs_gaussLebesguePrefixWeight_sub_le_of_dist (hdiam i x hx)

end

end Erdos1002
