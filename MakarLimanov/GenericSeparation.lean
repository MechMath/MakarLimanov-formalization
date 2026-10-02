import MakarLimanov.GenericJets

/-!
# Separation by the concrete generic differential field

The fraction field of the mixed-jet polynomial ring gives a completely explicit
model of a differential indeterminate.  This file records the separation facts
used when passing from formal differential polynomials to concrete values.
-/

namespace MakarLimanov.GenericSeparation

open GenericJets

noncomputable section

variable {k F : Type*} [CommRing k] [Field F]
  [Algebra k F]
  {δ η : Derivation k F F}

/-- The concrete generic field attached to a coefficient field `F`. -/
abbrev GenericField := FractionRing (MvPolynomial (ℕ × ℕ) F)

/-- The mixed-jet evaluation map on differential polynomials. -/
def mixedEvaluation (δ η : Derivation k F F) (P : MvPolynomial (ℕ × ℕ) F) :
    GenericField (F := F) :=
  MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
    (delta (E := GenericField (F := F)) δ)^[ij.1]
      ((eta (E := GenericField (F := F)) η)^[ij.2]
        (jet (F := F) (E := GenericField (F := F)) 0 0))) P

/-- Mixed evaluation is exactly the canonical embedding into the fraction field. -/
theorem mixedEvaluation_eq_algebraMap (P : MvPolynomial (ℕ × ℕ) F) :
    mixedEvaluation δ η P =
      algebraMap (MvPolynomial (ℕ × ℕ) F) (GenericField (F := F)) P := by
  exact eval_mixed δ η P

/-- A nonzero differential polynomial remains nonzero in the generic model. -/
theorem mixedEvaluation_ne_zero {P : MvPolynomial (ℕ × ℕ) F} (hP : P ≠ 0) :
    mixedEvaluation δ η P ≠ 0 := by
  exact eval_mixed_ne_zero δ η P hP

/-- The mixed-jet substitution is injective. -/
theorem mixedEvaluation_injective : Function.Injective (mixedEvaluation δ η) := by
  intro P Q h
  apply IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) (GenericField (F := F))
  rw [← mixedEvaluation_eq_algebraMap (δ := δ) (η := η) P,
    ← mixedEvaluation_eq_algebraMap (δ := δ) (η := η) Q, h]

end

end MakarLimanov.GenericSeparation
