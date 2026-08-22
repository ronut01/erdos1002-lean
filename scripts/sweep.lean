import Kwon1002
/-  Canonical axiom sweep for the Kwon1002 development.
    Counts named, non-internal theorems in the `Kwon1002` namespace.
    Run: lake env lean scripts/sweep.lean                              -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total := 0; let mut clean := 0; let mut bad := 0
  let mut tainted := 0; let mut direct := 0
  for (n, ci) in env.constants.toList do
    unless (`Kwon1002).isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternalDetail then continue
    total := total + 1
    let axs ← collectAxioms n
    if axs.contains ``sorryAx then
      tainted := tainted + 1
      if let some (.thmInfo ti) := env.find? n then
        if ti.value.hasSorry then direct := direct + 1
    else if axs.all (fun a => allowed.contains a) then clean := clean + 1
    else bad := bad + 1
  logInfo m!"TOTAL={total} CLEAN={clean} SORRY_TAINTED={tainted} DIRECT_SORRY={direct} NONSTANDARD={bad}"
