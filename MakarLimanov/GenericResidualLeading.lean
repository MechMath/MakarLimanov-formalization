import MakarLimanov.GenericResidualHomogeneous
import MakarLimanov.VariationSlope

/-!
# A positive homogeneous component of a generic residual

The residual decomposition separates the order-zero term from the genuinely
positive variations.  Once the order-zero coefficient vanishes, a nonzero
residual coefficient therefore supplies a nonunit homogeneous jet polynomial.
-/

namespace MakarLimanov.GenericResidualLeading

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open GenericResidualHomogeneous VariationCoefficients VariationSlope
open NewtonResidual

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

theorem exists_positive_nonunit_component
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (n : ℤ)
    (hcoef : (genericResidual (E := E) δ η hc p hp q z f).coeff n ≠ 0)
    (hzero :
      (SymbolVariations.variation (hp := hp)
        (h := GenericJets.commute δ η hc) f
        (mapField (IsScalarTower.toAlgHom k F E) z)
        (HahnSeries.single q (jet (F := F) (E := E) 0 0)) 0).coeff n = 0) :
    ∃ j, 0 < j ∧ j ≤ ControlledMatrix.wordDegree f ∧
      ∃ P : MvPolynomial (ℕ × ℕ) F,
        P.IsHomogeneous j ∧ P ≠ 0 ∧
        algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
          (genericVariation (E := E) δ η hc p hp q z f j).coeff n ∧
        ¬ IsUnit P := by
  obtain ⟨j, hjbound, hjcoef⟩ := exists_genericResidual_component_bounded
    (E := E) δ η hc p hp q z f n hcoef
  have hjpos : 0 < j := by
    by_contra hj
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj
    subst j
    exact hjcoef (by simpa [genericVariation] using hzero)
  obtain ⟨P, hhom, hP, hmap, hunit⟩ :=
    exists_nonzero_homogeneous_variation_coefficient
      (E := E) δ η hc p hp q z f j n hjpos (by simpa [genericVariation] using hjcoef)
  exact ⟨j, hjpos, hjbound, P, hhom, hP, hmap, hunit⟩

end

end MakarLimanov.GenericResidualLeading
