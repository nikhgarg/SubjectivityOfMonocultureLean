import JGR26SubjectivityMonoculture
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! The public import must expose every advertised theorem at its exact
specification, with only Lean's standard logical axioms. -/

run_cmd do
  let pairs : Array (Name × Name) := #[
    (`JGR26SubjectivityMonoculture.ProofInterface.theorem1,
     `JGR26SubjectivityMonoculture.PaperInterface.theorem1Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.proposition2,
     `JGR26SubjectivityMonoculture.PaperInterface.proposition2Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.theorem3,
     `JGR26SubjectivityMonoculture.PaperInterface.theorem3Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.proposition4,
     `JGR26SubjectivityMonoculture.PaperInterface.proposition4Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.theorem5,
     `JGR26SubjectivityMonoculture.PaperInterface.theorem5Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.lemma6,
     `JGR26SubjectivityMonoculture.PaperInterface.lemma6Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.proposition7,
     `JGR26SubjectivityMonoculture.PaperInterface.proposition7Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.remark1,
     `JGR26SubjectivityMonoculture.PaperInterface.remark1Spec),
    (`JGR26SubjectivityMonoculture.ProofInterface.lemma8,
     `JGR26SubjectivityMonoculture.PaperInterface.lemma8Spec)]
  let permitted : Array Name := #[`Classical.choice, `Quot.sound, `propext]
  for (proof, spec) in pairs do
    let proofInfo ← getConstInfo proof
    match proofInfo with
    | .thmInfo _ => pure ()
    | _ => throwError "{proof} is not a kernel-checked theorem"
    let specInfo ← getConstInfo spec
    match specInfo with
    | .defnInfo _ => pure ()
    | _ => throwError "{spec} is not a transparent definition"
    unless proofInfo.type.getForallBody.getAppFn.isConstOf spec do
      throwError "{proof} does not expose its advertised specification {spec}"
    let axioms ← collectAxioms proof
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "{proof} depends on an unapproved axiom: {axiomName}"
    logInfo m!"Checked {proof}: exact specification and standard axioms"
