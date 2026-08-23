import Kwon1002.Prop64Final
import Kwon1002.TailTransferCauchy
import Mathlib.Util.AssertNoSorry

/-!
# Completion of Kwon's Theorem 1.1

The existing endgame already proves Corollary 5.3 and Section 7.  Feeding it
the axiom-clean Proposition 6.4 from `Prop64Final` closes the last remaining
manuscript input.
-/

namespace Kwon1002.ProofComplete

/-- Kwon's Theorem 1.1 with Proposition 6.4 discharged. -/
theorem erdos1002Conclusion : Erdos1002Conclusion :=
  TailTransferCauchy.erdos1002Conclusion_of_prop64_T
    Prop64Final.prop_6_4_bounded_remainder_weak_law

/-- The official existential form, with Proposition 6.4 discharged. -/
theorem erdos1002Official : Erdos1002Official :=
  TailTransferCauchy.erdos1002Official_of_prop64_T
    Prop64Final.prop_6_4_bounded_remainder_weak_law

assert_no_sorry erdos1002Conclusion
assert_no_sorry erdos1002Official

end Kwon1002.ProofComplete
