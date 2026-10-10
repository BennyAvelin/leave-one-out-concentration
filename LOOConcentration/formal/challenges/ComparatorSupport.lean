import Lean

set_option autoImplicit false

open Lean Elab Command Meta

private def frozenSolutionPairs : Array (Name × Name) := #[
  (`LOOConcentration.Revision.Challenges.simplifiedConcentration, `LOOConcentration.Revision.simplifiedConcentration),
  (`LOOConcentration.Revision.Challenges.mainConcentration, `LOOConcentration.Revision.mainConcentration),
  (`LOOConcentration.Revision.Challenges.looMoments, `LOOConcentration.Revision.looMoments),
  (`LOOConcentration.Revision.Challenges.dataDependentConcentration, `LOOConcentration.Revision.dataDependentConcentration)
]

private def acceptedSolutionAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def checkFrozenChallengeTypes (checkAxioms : Bool) : CommandElabM Unit := do
  for (benchmarkName, frozenName) in frozenSolutionPairs do
    let benchmarkInfo ← getConstInfo benchmarkName
    unless benchmarkInfo.isTheorem do
      throwError "{benchmarkName} is missing or is not a theorem"
    let frozenInfo ← getConstInfo frozenName
    unless frozenInfo.isTheorem do
      throwError "{frozenName} is missing or is not a theorem"
    let matchingTypes ← liftTermElabM do
      withTransparency .all <| isDefEq benchmarkInfo.type frozenInfo.type
    unless matchingTypes do
      throwError "Type mismatch: {benchmarkName} does not match {frozenName}"
    logInfo m!"#check_frozen_types: PASS {benchmarkName} == {frozenName}"
    if checkAxioms then
      let axioms ← Lean.collectAxioms benchmarkName
      let unexpected := axioms.filter fun axName =>
        !(acceptedSolutionAxioms.contains axName)
      unless unexpected.isEmpty do
        throwError "{benchmarkName} uses disallowed axioms: {unexpected}"
      logInfo m!"#check_frozen_solution axioms: PASS {benchmarkName} {axioms}"
  if checkAxioms then
    let env ← getEnv
    let benchmarkAxioms ← env.constants.foldM (init := #[]) fun acc name info => do
      if (`LOOConcentration.Revision.Challenges).isPrefixOf name && info.isAxiom then
        return acc.push name
      return acc
    unless benchmarkAxioms.isEmpty do
      throwError "Axiom declarations in benchmark namespace: {benchmarkAxioms}"
    logInfo "#check_frozen_solution environment axiom declarations: PASS"
  logInfo m!"#check_frozen_{if checkAxioms then "solution" else "types"}: PASS (4 declarations)"

elab "#check_frozen_types" : command => do
  checkFrozenChallengeTypes false

elab "#check_frozen_solution" : command => do
  checkFrozenChallengeTypes true
