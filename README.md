# Makar–Limanov Conjecture in Lean

A Lean 4 formalization of the proof in [proof.tex](proof.tex). The main theorem,
[`MakarLimanov.makarLimanov`](MakarLimanov/Main.lean), uses only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or custom axioms.

For every nonconstant free polynomial over an algebraically closed field of
characteristic zero, the infimum of its minimum normalized matrix ranks is zero.
The precise statement is in [Statement.lean](MakarLimanov/Statement.lean).

## Proof structure

- **Differential separation:** [StarOperatorRepresentation.lean](MakarLimanov/StarOperatorRepresentation.lean).
- **Finite Newton approximation:** [InitialSlopeData.lean](MakarLimanov/InitialSlopeData.lean),
  [NewtonSlopeData.lean](MakarLimanov/NewtonSlopeData.lean), and
  [FiniteNewtonTheorem.lean](MakarLimanov/FiniteNewtonTheorem.lean).
- **Matrix realization and reduction:** [SymbolRealization.lean](MakarLimanov/SymbolRealization.lean),
  [ConditionalMain.lean](MakarLimanov/ConditionalMain.lean), and
  [TwoGenerator.lean](MakarLimanov/TwoGenerator.lean).

The uniform support bound is chosen before the target precision; the proof does
not need the paper's stronger explicit initial bound. The historical
`AuditedAssumptions` interface now contains proved theorems.

## Build and verify

Uses Lean `v4.30.0-rc1` and mathlib commit
`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`.
The current [lakefile.toml](lakefile.toml) points to a local mathlib checkout;
update that dependency path before building on another machine.

```sh
lake build
lake env lean FullAxiomAudit.lean
lake env lean MainAxiomAudit.lean
lake env lean VerifyComplete.lean
lake env lean VerifyConditional.lean
```

These checks build the library and main theorem, report the main theorem's axioms,
and reject additional axioms in project declarations, including private helpers.
[verification.json](verification.json) records the previous verification run and
source hashes. Older notes in [review/](review/) describe historical work.
