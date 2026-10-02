import MakarLimanov
import MakarLimanov.Main
import Lean.Util.CollectAxioms

/-! A strict completion gate: a successful build with sorry warnings is insufficient. -/

open Lean Elab Command in
run_cmd do
  let axioms ← collectAxioms ``MakarLimanov.makarLimanov
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Original theorem is incomplete: unapproved axiom {ax}"
  logInfo "Original theorem verified with standard axioms only"
