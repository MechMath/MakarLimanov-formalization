import MakarLimanov
import MakarLimanov.Main
import Lean.Util.CollectAxioms

/-!
# Whole-project standard-axiom verification

The historical conditional gate now rejects every additional axiom, including
in private and generated project helpers. `VerifyComplete.lean` also checks the
main theorem directly.
-/

open Lean Elab Command in
run_cmd do
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if (`MakarLimanov).isPrefixOf (privateToUserName name) then
      let axioms ← collectAxioms name
      for ax in axioms do
        if ax == `sorryAx then
          throwError "Unfinished proof in {name}: sorryAx"
        unless standard.contains ax do
          throwError "Unlisted axiom {ax} in {name}"
      count := count + 1
  logInfo m!"COMPLETE_PROJECT_AUDIT_OK: {count} declarations; only standard axioms"
