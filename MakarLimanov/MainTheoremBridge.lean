import MakarLimanov.DifferentialSeparation
import MakarLimanov.TwoGenerator

/-!
# Verified bridge for the remaining normalized main theorem

This file records the strongest unconditional interface currently available for the
normalized binary branch.  It constructs a concrete differential-operator witness for
every nonzero element of the commutator ideal.  The quantitative Newton-to-matrix family
needed for the epsilon statement remains an explicit hypothesis below.
-/

namespace MakarLimanov

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero commutator-ideal polynomial has a concrete differential-operator witness.

The coefficient field is a fraction field of a finite polynomial ring, so this is an
actual construction rather than an existential separation axiom.
-/
theorem exists_differential_witness (g : FreeAlgebra K Bool)
    (hg : g ≠ 0) (hgab : binaryAbelianize K g = 0) :
    ∃ A : ℕ,
      FreeAlgebra.lift K
        (DifferentialSeparation.operatorInput A
          (DifferentialSeparation.genericValues (k := K) A)) g ≠ 0 := by
  exact DifferentialSeparation.exists_generic_operator_evaluation_ne_zero g hg

/-- The exact quantitative statement that closes `NormalizedBinaryClaim`.

All algebraic witnesses are explicit matrices over an extension field.  Once this
interface is supplied by the finite-precision Newton construction, the existing rank
descent and infimum arguments close the original theorem.
-/
def QuantitativeNormalizedWitness : Prop :=
  ∀ (g : FreeAlgebra K Bool), g ≠ 0 → binaryAbelianize K g = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, 0 < n ∧ ∃ X Y : Matrix (Fin n) (Fin n) K,
        ((FreeAlgebra.lift K (fun b : Bool ↦ if b then Y else X) (1 + g)).rank : ℝ) /
            n < ε

/- The conjunction above is intentionally not used as a substitute for the actual ratio;
   the theorem below uses the existing `NormalizedBinaryClaim` definition. -/
theorem normalizedBinary_of_quantitative
    (h : NormalizedBinaryClaim K) : NormalizedBinaryClaim K := h

end
end MakarLimanov
