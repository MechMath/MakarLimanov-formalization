import MakarLimanov.FiniteNewtonInduction

/-! The two checked branches of one finite Newton stage. -/

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

/-- A homogeneous residual coefficient has exactly the two checked outcomes:
zero advances the lower bound directly, while a nonzero positive-degree
coefficient admits the explicit commuting-derivation correction. -/
theorem corrected_or_zero
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ) (j : ℕ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hhom : P.IsHomogeneous j) (hj : 0 < j) :
    P = 0 ∨
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
  · exact Or.inl hzero
  · right
    exact corrected_stage δ η hc p hp q z f b r hz hb hq hr P hP hzero
      (homogeneous_nonunit hj hhom hzero)

/- The same split with the zero branch converted into an actual residual
progress statement, ready for an induction on the integer precision index. -/
theorem progress_or_corrected
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ) (j : ℕ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hhom : P.IsHomogeneous j) (hj : 0 < j) :
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
  obtain hzero | hcorr := corrected_or_zero δ η hc p hp q z f b r j hz hb hq hr P hP hhom hj
  · left
    exact zero_coefficient_progress δ η hc p hp q z f r hr P hP hzero
  · exact Or.inr hcorr

end MakarLimanov.FiniteNewtonInduction
