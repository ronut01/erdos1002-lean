import Kwon1002
open Lean Elab Meta

/-- Names whose *own* value carries a `sorry`, in the transitive closure. -/
def sorryLeaves (root : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    let n :: rest := stack | break
    stack := rest
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut cs : NameSet := {}
    if let some v := ci.value? then
      cs := v.getUsedConstants.foldl (·.insert ·) cs
    cs := ci.type.getUsedConstants.foldl (·.insert ·) cs
    -- does this declaration's own value mention sorryAx directly?
    if let some v := ci.value? then
      if v.getUsedConstants.contains ``sorryAx then
        out := out.push n
    for c in cs.toList do
      if !seen.contains c then stack := c :: stack
  return out

def report (root : Name) : MetaM Unit := do
  let ls ← sorryLeaves root
  logInfo m!"{root} sorry-leaves: {ls.qsort Name.lt}"

run_meta report ``Kwon1002.CorFinal.principal_cauchy_law_F
run_meta report ``Kwon1002.Master.erdos1002Conclusion_of_section7
run_meta report ``Kwon1002.CauchyJoin.principal_cauchy_law_J
run_meta report ``Kwon1002.CauchyJoin.erdos1002Conclusion_of_section7_J
run_meta report ``Kwon1002.CauchyJoin.erdos1002Conclusion_final
run_meta report ``Kwon1002.TailTransferCauchy.principal_cauchy_law_T
run_meta report ``Kwon1002.TailTransferCauchy.erdos1002Conclusion_of_prop64_T
run_meta report ``Kwon1002.TailTransferCauchy.erdos1002Conclusion_final_T
run_meta report ``Kwon1002.TailTransferCauchy.erdos1002Official_final_T
