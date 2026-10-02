import MakarLimanov.FiniteNewtonDichotomy

/-! A stage interface which records the precision gain in the zero branch. -/

noncomputable section

namespace MakarLimanov.FiniteNewtonInduction

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open NewtonResidual

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [CharZero k] [CharZero F] [CharZero E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/-- The zero branch records the one-unit lower-bound improvement explicitly. -/
theorem stage_progress
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ) (j : ℕ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hhom : P.IsHomogeneous j) (hj : 0 < j) :
    (P = 0 ∧ LowerBound (r + 1) (genericResidual (E := E) δ η hc p hp q z f)) ∨
      (P ≠ 0 ∧
        ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G) (_ : Algebra F G)
          (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (w : G),
          ∃ hDH : Function.Commute D H,
          (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
          (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
          LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
          LowerBound (r + 1)
            (toSeries (evaluateAt (hp := hp) (h := hDH)
              (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f))) := by
  by_cases hzero : P = 0
  · left
    exact ⟨hzero, zero_coefficient_progress δ η hc p hp q z f r hr P hP hzero⟩
  · right
    refine ⟨hzero, ?_⟩
    exact corrected_stage δ η hc p hp q z f b r hz hb hq hr P hP hzero
      (homogeneous_nonunit hj hhom hzero)

end MakarLimanov.FiniteNewtonInduction
