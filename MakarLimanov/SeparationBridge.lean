import MakarLimanov.JetSpecialization
import MakarLimanov.GenericSeparation

/-!
# A packaged bridge from concrete differential models to generic jets

The generic jet field is fixed to the fraction field of the mixed-jet polynomial ring.
Consequently, a nonzero value in any compatible concrete differential model certifies
that the corresponding generic free-polynomial value is nonzero.
-/

namespace MakarLimanov.SeparationBridge

open GenericJets JetPolynomialCoefficients SymbolSeries SymbolSeries.StarSeries
open JetSpecialization

noncomputable section

variable {k F G : Type*} [Field k] [Field F] [Field G]
  [Algebra k F] [Algebra k G] [Algebra F G] [IsScalarTower k F G]
  [CharZero F] [CharZero G]

/-- The concrete field containing all mixed generic jets over `F`. -/
abbrev JetField := FractionRing (MvPolynomial (ℕ × ℕ) F)

/--
A compatible concrete differential model separates the generic evaluation.  The generic
coefficient field is the canonical mixed-jet fraction field, so no auxiliary field
parameter is needed at call sites.
-/
theorem generic_evaluateAt_ne_zero_of_value
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool)
    (hf : toSeries (evaluateAt (hp := hp) (h := hDH)
      (HahnSeries.single q w) f) ≠ 0) :
    toSeries (evaluateAt (hp := hp)
      (h := GenericJets.commute δ η hc)
      (HahnSeries.single q (jet (F := F) (E := JetField (F := F)) 0 0)) f) ≠ 0 := by
  exact JetSpecialization.generic_ne_zero_of_value
    (E := JetField (F := F)) δ η hc p hp q D H hDH hD hH w f hf

@[simp] theorem genericInput_lift_eq_evaluateAt
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (f : FreeAlgebra k Bool) :
    FreeAlgebra.lift k (genericInput (E := JetField (F := F)) δ η hc p hp q) f =
      evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
        (HahnSeries.single q (jet (F := F) (E := JetField (F := F)) 0 0)) f := by
  rfl

/-- Nonvanishing of the generic `FreeAlgebra` value follows from any concrete model. -/
theorem genericInput_lift_ne_zero_of_value
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool)
    (hf : toSeries (evaluateAt (hp := hp) (h := hDH)
      (HahnSeries.single q w) f) ≠ 0) :
    toSeries (FreeAlgebra.lift k
      (genericInput (E := JetField (F := F)) δ η hc p hp q) f) ≠ 0 := by
  rw [genericInput_lift_eq_evaluateAt]
  exact generic_evaluateAt_ne_zero_of_value δ η hc p hp q D H hDH hD hH w f hf

end

end MakarLimanov.SeparationBridge
