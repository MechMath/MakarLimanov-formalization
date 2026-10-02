import MakarLimanov.ResidualPolynomial
import MakarLimanov.ResidualConstantTerm

/-!
# The leading Newton polynomial

This packages the two pieces of Lemma 8 that are independent of factorization:
the coefficient polynomial is nonunit because a positive homogeneous component is
active, while its constant term is the old residual coefficient.
-/

namespace MakarLimanov.GenericNewtonPolynomial

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients VariationCoefficients
open NewtonResidual ResidualPolynomial ResidualConstantTerm

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero k] [CharZero F] [CharZero E]

theorem exists_leading_polynomial
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (hres : (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0)
    (hactive : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      P ≠ 0 ∧ ¬ IsUnit P ∧
      MvPolynomial.constantCoeff P ≠ 0 ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (genericResidual (E := E) δ η hc p hp q z f).coeff r := by
  obtain ⟨P, hP0, hPnu, hPmap⟩ :=
    ResidualPolynomial.exists_nonunit_residual_coefficient_representative
      (E := E) δ η hc p hp q z f r hactive
  have hconst := ResidualConstantTerm.residual_coefficient_constantCoeff
    (E := E) δ η hc p hp q z f r P hPmap
  exact ⟨P, hP0, hPnu, by simpa [hconst] using hres, hPmap⟩

end

end MakarLimanov.GenericNewtonPolynomial
