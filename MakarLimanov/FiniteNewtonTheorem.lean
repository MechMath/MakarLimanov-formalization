import MakarLimanov.InitialSeparationApproximation
import MakarLimanov.StarOperatorRepresentation

/-!
# Finite Newton approximation from a concrete separating model

The polynomial differential model supplies a nonzero initial symbol value.
The generic initial slope and the multiplicity-controlled Newton iteration
then give all finite precisions with a uniform support bound.
-/

noncomputable section

namespace MakarLimanov.FiniteNewtonTheorem

open SymbolSeries SymbolSeries.StarSeries TwoVariableDifferentialField

universe u

/-- The finite approximation statement, proved without additional axioms. -/
theorem finite_newton_approximation (K : Type u) [Field K] [CharZero K]
    (g : FreeAlgebra K Bool) (hg : g ≠ 0) (hab : binaryAbelianize K g = 0) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ T : ℕ, 0 < T →
      Nonempty (AuditedAssumptions.SymbolApproximation K g A T) := by
  obtain ⟨a, hoperator⟩ :=
    DifferentialSeparation.exists_generic_operator_evaluation_ne_zero g hg
  let C := DifferentialSeparation.CoefficientField (k := K) a
  let values : Fin (a + 1) → C := DifferentialSeparation.genericValues (k := K) a
  have hvalue := StarOperatorRepresentation.diagonal_evaluateAt_ne_zero_of_operator_ne_zero
    (k := K) (C := C) a values g hoperator
  exact InitialSeparationApproximation.finite_newton_approximation_of_value
    g hg hab (delta (k := K) (C := C)) (eta (k := K) (C := C))
    (commute (k := K) (C := C)) _ hvalue

end MakarLimanov.FiniteNewtonTheorem
