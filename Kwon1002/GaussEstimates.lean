import Kwon1002.Reciprocity

/-!
# §3, shared vocabulary (the continuant recursion)

The §3 estimates themselves now live in their own modules, each proved:
`DigitTail` (Lem 3.1(ii)), `AntiConcentration` (Lem 3.3), `CylinderPhase`
(Lem 3.4 converse). Lems 3.1(i) and 3.2 (spectral gap / multi-block
mixing) remain to be stated against the substrate's transfer operator.

Shared §3 vocabulary: the continuant recursion. The §3 estimates
themselves are proved in their own modules, `DigitTail` (Lem 3.1(ii)),
`AntiConcentration` (Lem 3.3), `CylinderPhase` (Lem 3.4 converse).

Still to state: Lems 3.1(i) and 3.2 (BV spectral gap and conditional
multi-block mixing), which need the substrate's transfer-operator and
cylinder-conditioning vocabulary.
-/

namespace Kwon1002

noncomputable section

/-- Continuant denominators: `q_0 = 1`, `q_1 = a_1`,
`q_{j+1} = a_{j+1} q_j + q_{j-1}`, the standard recursion, indexed so
that `denom α j` is `q_j` along the orbit of `α`. -/
def denom (α : ℝ) : ℕ → ℕ
  | 0 => 1
  | 1 => digit α 0
  | j + 2 => digit α (j + 1) * denom α (j + 1) + denom α j

end

end Kwon1002
