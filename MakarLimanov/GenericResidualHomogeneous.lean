import MakarLimanov.NewtonResidual
import MakarLimanov.ResidualHomogeneous

/-!
# Homogeneous decomposition of the generic Newton residual

The universal residual is the translated evaluation at the generic monomial
correction.  The coefficient decomposition from `ResidualHomogeneous` therefore
applies directly, giving a finite sum of variation coefficients indexed by the
number of correction letters.
-/

namespace MakarLimanov.GenericResidualHomogeneous

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization VariationCoefficients
open NewtonResidual

noncomputable section

variable {k F E : Type*} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

theorem genericResidual_coeff_sum
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (n : ℤ) :
    (genericResidual (E := E) δ η hc p hp q z f).coeff n =
      ∑ j ∈ (Variations.expansion
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (mapField (IsScalarTower.toAlgHom k F E) z))
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (HahnSeries.single q (jet (F := F) 0 0))) f).support,
        (SymbolVariations.variation (hp := hp)
          (h := GenericJets.commute δ η hc) f
          (mapField (IsScalarTower.toAlgHom k F E) z)
          (HahnSeries.single q (jet (F := F) 0 0)) j).coeff n := by
  exact ResidualHomogeneous.translated_residual_coeff_sum
    (p := p) (hp := hp) (δ := GenericJets.delta δ) (η := GenericJets.eta η)
    (h := GenericJets.commute δ η hc) f
    (mapField (IsScalarTower.toAlgHom k F E) z)
    (HahnSeries.single q (jet (F := F) 0 0)) n

theorem exists_genericResidual_component_bounded
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (n : ℤ)
    (hn : (genericResidual (E := E) δ η hc p hp q z f).coeff n ≠ 0) :
    ∃ j, j ≤ ControlledMatrix.wordDegree f ∧
      (SymbolVariations.variation (hp := hp)
        (h := GenericJets.commute δ η hc) f
        (mapField (IsScalarTower.toAlgHom k F E) z)
        (HahnSeries.single q (jet (F := F) 0 0)) j).coeff n ≠ 0 := by
  exact ResidualHomogeneous.exists_nonzero_variation_component_bounded
    (p := p) (hp := hp) (δ := GenericJets.delta δ) (η := GenericJets.eta η)
    (h := GenericJets.commute δ η hc) f
    (mapField (IsScalarTower.toAlgHom k F E) z)
    (HahnSeries.single q (jet (F := F) 0 0)) n hn

theorem genericResidual_variation_degree_bound
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ)
    (hj : ControlledMatrix.wordDegree f < j) :
    SymbolVariations.variation (hp := hp)
      (h := GenericJets.commute δ η hc) f
      (mapField (IsScalarTower.toAlgHom k F E) z)
      (HahnSeries.single q (jet (F := F) 0 0)) j = 0 := by
  exact ResidualHomogeneous.variation_eq_zero_of_wordDegree_lt
    (p := p) (hp := hp) (δ := GenericJets.delta δ)
    (η := GenericJets.eta η) (h := GenericJets.commute δ η hc)
    f (mapField (IsScalarTower.toAlgHom k F E) z)
    (HahnSeries.single q (jet (F := F) 0 0)) j hj

end

end MakarLimanov.GenericResidualHomogeneous
