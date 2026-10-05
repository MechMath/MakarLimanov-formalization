import MakarLimanov
import Lean.Util.CollectAxioms

/-! Audit all declarations in the verified library, including private helpers. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants do
    let publicName := privateToUserName name
    if (`MakarLimanov).isPrefixOf publicName then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unapproved axiom {ax} in {name}"
      count := count + 1
  logInfo m!"AXIOM_AUDIT_OK: {count} declarations; only standard axioms"
