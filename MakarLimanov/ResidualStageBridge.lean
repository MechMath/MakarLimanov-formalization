import MakarLimanov.FiniteNewtonInduction

/-!
# A representative-level Newton dichotomy

The finite Newton induction works with the coefficient of the current residual
at one lattice index.  This file removes an unnecessary homogeneity
assumption from that interface: once a polynomial representative of the
coefficient is known to be nonunit, the checked differential-factor step
already gives the correction.  The homogeneous argument is only needed when
proving that the representative is nonunit.
-/

noncomputable section

namespace MakarLimanov.ResidualStageBridge

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open NewtonResidual FiniteNewtonInduction

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [CharZero k] [CharZero F] [CharZero E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/-- Every nonzero generic residual coefficient has a nonzero polynomial
representative in the finite jet ring. -/
theorem exists_nonzero_residual_representative
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (hcoef : (genericResidual (E := E) δ η hc p hp q z f).coeff r ≠ 0) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      P ≠ 0 ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (genericResidual (E := E) δ η hc p hp q z f).coeff r := by
  obtain ⟨P, hP, _hsp⟩ := exists_universal_residual_coefficient
    (E := E) (G := E) δ η hc p hp q z f r
  refine ⟨P, ?_, hP⟩
  intro hzero
  apply hcoef
  rw [← hP, hzero, map_zero]

/-- A residual coefficient representative has the two checked outcomes.  In
the zero branch its coefficient vanishes and the lower bound advances.  In the
nonzero branch, a nonunit representative produces a commuting differential
extension and a corrected symbol with the improved residual bound. -/
theorem residual_dichotomy_of_representative
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hPnu : ¬ IsUnit P) :
    LowerBound (r + 1) (genericResidual (E := E) δ η hc p hp q z f) ∨
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
  by_cases hzero : P = 0
  · left
    exact zero_coefficient_progress δ η hc p hp q z f r hr P hP hzero
  · right
    exact corrected_stage δ η hc p hp q z f b r hz hb hq hr P hP hzero hPnu

end MakarLimanov.ResidualStageBridge
