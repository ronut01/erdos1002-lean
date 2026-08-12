import Kwon1002.Reciprocity
import Erdos1002.GaussDynamics
import Erdos1002.GaussMeasure

/-!
# Bridge: our §2 objects ↔ the vendored substrate

The vendored substrate (Shouqiao Wang, MIT, see `wang_substrate/`)
defines the Gauss map and its first digit exactly as §2 of Kwon's
manuscript does, so our objects and his coincide **definitionally**.
Recording that here means every mixing, transfer-operator and
digit-statistics result in the substrate applies verbatim to the
coordinates §2 builds on, with no translation layer.
-/

namespace Kwon1002

/-- Our Gauss map is the substrate's Gauss map. -/
theorem gaussMap_eq_substrate : gaussMap = Erdos1002.gaussMap := rfl

/-- Our digit is the substrate's first digit (as a natural number). -/
theorem digit_eq_substrate (α : ℝ) (j : ℕ) :
    (digit α j : ℤ) = max (Erdos1002.gaussFirstDigit (gaussIter α j)) 0 := by
  simp [digit, Erdos1002.gaussFirstDigit]

/-- Iterating our map is iterating the substrate's map. -/
theorem gaussIter_eq_substrate (α : ℝ) (j : ℕ) :
    gaussIter α j = Erdos1002.gaussMap^[j] α := rfl

end Kwon1002
