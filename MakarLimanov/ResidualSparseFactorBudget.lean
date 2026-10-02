import MakarLimanov.ResidualPolynomial
import MakarLimanov.ResidualConstantTerm
import MakarLimanov.SparseFactorBudget

/-!
# The sparse factor budget for a Newton residual coefficient

This is the direct formal counterpart of the factor-selection part of
Lemma 8.  The residual coefficient is represented by a sum of homogeneous
variation representatives; divisibility of the active variation degrees gives
the sparse support hypothesis needed by the root-of-unity budget.
-/

noncomputable section

namespace MakarLimanov.ResidualSparseFactorBudget

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients NewtonResidual
open ResidualPolynomial ResidualConstantTerm SparseFactorBudget
open FiniteJets

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero k] [CharZero F] [CharZero E]

/-- A nonzero uncorrected residual coefficient and an active positive
variation give the exact sparse factor budget for its Newton polynomial. -/
theorem exists_residual_factorisation_with_sparse_budget
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (e : ℕ)
    (he : 0 < e)
    (hres : (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0)
    (hactive : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0)
    (hdiv : ∀ j, (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      e ∣ j) :
    ∃ (Ψ P Q : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      Ψ ≠ 0 ∧ ¬ IsUnit Ψ ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E Ψ =
        (genericResidual (E := E) δ η hc p hp q z f).coeff r ∧
      Irreducible P ∧ 0 < m ∧ Ψ = P ^ m * Q ∧ ¬ P ∣ Q ∧
      differentialOrder P = differentialOrder Ψ ∧
      differentialOrder Q ≤ differentialOrder P ∧
      e * m ≤ Ψ.totalDegree := by
  obtain ⟨Ψ, hΨ0, hΨnu, hΨmap, hsparse⟩ :=
    ResidualPolynomial.exists_nonunit_residual_coefficient_representative_sparse
      (E := E) δ η hc p hp q z f r e hactive hdiv
  have hconst : MvPolynomial.constantCoeff Ψ ≠ 0 :=
    ResidualConstantTerm.residual_coefficient_constantCoeff_ne_zero
      (E := E) δ η hc p hp q z f r Ψ hΨmap hres
  obtain ⟨P, Q, m, hP, hm, hfactor, hPnotdvd, horderP, horderQ, hbudget⟩ :=
    SparseFactorBudget.exists_factorisation_with_sparse_budget
      Ψ e he hconst hsparse hΨnu
  exact ⟨Ψ, P, Q, m, hΨ0, hΨnu, hΨmap, hP, hm, hfactor, hPnotdvd,
    horderP, horderQ, hbudget⟩

end MakarLimanov.ResidualSparseFactorBudget
