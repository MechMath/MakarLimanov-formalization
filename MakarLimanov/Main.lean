import MakarLimanov.TwoGenerator
import MakarLimanov.Assembly
import MakarLimanov.ConditionalMain

/-!
# The original target

The original statement follows from the proved finite Newton approximation,
filtered symbol realization, matrix descent, and two-generator reduction.
-/

namespace MakarLimanov

/-- The exact original conjecture. -/
theorem makarLimanov (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (d : ℕ) :
    OriginalConjecture K d := by
  exact originalConjecture_of_normalizedBinary K
    (normalizedBinaryClaim_of_audited_assumptions K) d

end MakarLimanov
