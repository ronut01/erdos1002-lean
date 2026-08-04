import Kwon1002.Marks

/-!
# §5, the Poisson limit and the principal Cauchy law

Skeleton of §5. Three results:

* **Prop 5.1** (Poisson point process): `Ξ_n ⇒ PRM(Λ)` with
  `dΛ(x) = |x|^{-2} dx / (2π²)`, in the vague topology on Radon point
  measures on `ℝ \ {0}`. Stating this needs a point-process type; the
  substrate's `CompoundPoisson` / `PoissonFactorialConvergence` supply
  the factorial-moment route the manuscript actually uses, and the
  statement is written against them at M5 rather than invented here.
  What is stated now is the *consequence* the rest of the proof consumes.

* **Lem 5.2** (small jumps): the truncated marks contribute variance
  `O(ε)` after normalization, stated below.

* **Cor 5.3** (principal Cauchy law): the normalized bulk sum, after a
  deterministic centering, converges to `Cauchy(0, 1/(2π))`, stated
  below, and this is the form §7 consumes. Note the limit CDF is exactly
  `cauchyLimitCDF` from `Statement.lean`: the same law the whole problem
  is about, which is why Cor 5.3 is the mathematical heart of the paper.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Kwon1002

noncomputable section

/-- The `ε`-truncated mark: the part of `Z_{n,j}` below the cutoff, whose
aggregate variance Lem 5.2 controls. -/
def truncatedMark (ε : ℝ) (α : ℝ) (n j : ℕ) : ℝ :=
  if mark α n j ≤ ε * Lnorm n then mark α n j else 0


/-- **Corollary 5.3** (Principal Cauchy law). There are deterministic
centerings `b n` such that the centered bulk sum converges in
distribution to the centered Cauchy law of scale `1/(2π)`, i.e. its
distribution functions converge to `cauchyLimitCDF`.

This is the principal-part statement; §6's bounded-remainder weak law and
§7's end-term control turn it into Theorem 1.1. -/
theorem principal_cauchy_law (c : ℝ) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  sorry

end

end Kwon1002
