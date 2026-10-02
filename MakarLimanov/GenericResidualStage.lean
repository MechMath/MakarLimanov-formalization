import MakarLimanov.ResidualPolynomial
import MakarLimanov.FiniteNewtonInduction
import MakarLimanov.GenericResidualLeading

/-!
# A Newton stage from an active positive variation

The residual coefficient used by the root theorem is the full coefficient of
the translated residual.  This file connects the homogeneous decomposition of
that coefficient to the certified one-step Newton construction.
-/

namespace MakarLimanov.GenericResidualStage

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open VariationCoefficients NewtonResidual
open FiniteNewtonInduction

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [CharZero k] [CharZero F] [CharZero E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/-- An active positive variation supplies the actual residual representative
needed by `corrected_stage`, rather than only a representative of one summand.
-/
theorem corrected_stage_of_active_variation
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (hactive : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0) :
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G) (_ : Algebra F G)
      (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  obtain ⟨P, hP0, hPnu, hP⟩ :=
    ResidualPolynomial.exists_nonunit_residual_coefficient_representative
      (E := E) δ η hc p hp q z f r hactive
  exact corrected_stage δ η hc p hp q z f b r hz hb hq hr P hP hP0 hPnu

/-- The order-zero variation vanishes, so any nonzero residual coefficient
automatically has an active positive-degree component and hence admits a
certified Newton correction. -/
theorem corrected_stage_of_nonzero_residual
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (hcoef : (genericResidual (E := E) δ η hc p hp q z f).coeff r ≠ 0)
    (hzero : (SymbolVariations.variation (hp := hp)
      (h := GenericJets.commute δ η hc) f
      (mapField (IsScalarTower.toAlgHom k F E) z)
      (HahnSeries.single q (jet (F := F) (E := E) 0 0)) 0).coeff r = 0) :
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G) (_ : Algebra F G)
      (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  obtain ⟨j, hj, _, P, hP, hP0, hPmap, _⟩ :=
    GenericResidualLeading.exists_positive_nonunit_component
      (E := E) δ η hc p hp q z f r hcoef hzero
  have hactive : (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 := by
    intro hzero'
    apply hP0
    apply IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E
    rw [hPmap, hzero', map_zero]
  exact corrected_stage_of_active_variation δ η hc p hp q z f b r hz hb hq hr
    ⟨j, hj, hactive⟩

end

end MakarLimanov.GenericResidualStage
