import Kwon1002.SubstrateBridge

/-!
# The marks and index sets of §§5-7

`L = log n`; the level mark `Z_{n,j} = a_{j+1} W(θ_j)` (§5, around (38));
the normalized signed mark `X_{n,j} = (-1)^j Z_{n,j} / L`; and the bulk
index set `J_n`, which the manuscript trims by `O(H)` at both ends with
`H = L^{3/4}` (§7, Lem 7.1).

The trimming constant in `bulkIndices` is written as a parameter rather
than baked in: the manuscript fixes it in the §7 stopping-time argument,
which is one of the passages being revised, and a parameterized index set
lets §5 be stated and proved now without committing to a number we would
have to change later.
-/

open Filter Set

namespace Kwon1002

noncomputable section

/-- `L = log n`, the normalization of the problem. -/
def Lnorm (n : ℕ) : ℝ := Real.log (n : ℝ)

/-- `H = L^{3/4}`, the boundary scale of Lem 7.1. -/
def Hscale (n : ℕ) : ℝ := (Lnorm n) ^ (3 / 4 : ℝ)

/-- The level mark `Z_{n,j} = a_{j+1} W(θ_j)`: the digit weighted by the
sawtooth-average `W` at the torus coordinate. -/
def mark (α : ℝ) (n j : ℕ) : ℝ := (digit α j : ℝ) * W (theta α n j)

/-- The normalized signed mark `X_{n,j} = (-1)^j Z_{n,j} / L`. -/
def signedMark (α : ℝ) (n j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * mark α n j / Lnorm n

/-- The bulk index set: levels below the stopping time, trimmed by
`c·H` at the bottom (`c` fixed in §7). -/
def bulkIndices (c : ℝ) (α : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (stoppingTime α n)).filter (fun j => c * Hscale n ≤ (j : ℝ))

/-- The normalized bulk sum, whose limit law is the content of §5. -/
def bulkSum (c : ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ bulkIndices c α n, signedMark α n j

end

end Kwon1002
