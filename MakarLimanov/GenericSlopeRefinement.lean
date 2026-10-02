import MakarLimanov.SymbolReindex
import MakarLimanov.VariationCoefficients
import MakarLimanov.NewtonResidual

/-!
# Generic variations under a lattice refinement

Passing from denominator `p` to `p*e` embeds every Laurent exponent by the
factor `e`.  The variation identity is preserved by this embedding, including
the generic jet correction; consequently vanishing is reflected and the
Laurent order is multiplied by `e`.
-/

namespace MakarLimanov.GenericSlopeRefinement

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

/-- Refinement transports a universal generic variation to the refined
denominator and multiplies its perturbation exponent by `e`. -/
theorem refineLattice_genericVariation
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (j : ℕ) :
    refineLattice e he
        (genericVariation (E := E) δ η hc p hp q z f j) =
      genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        ((e : ℤ) * q) (refineLattice e he z) f j := by
  unfold genericVariation
  rw [refineLattice_variation p e hp he (GenericJets.delta δ)
    (GenericJets.eta η) (GenericJets.commute δ η hc)]
  rw [mapField_refineLattice (IsScalarTower.toAlgHom k F E) e he z,
    refineLattice_single]

/-- The zero/nonzero status of a generic variation is unchanged by lattice
refinement. -/
theorem refineLattice_genericVariation_eq_zero_iff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (j : ℕ) :
    genericVariation (E := E) δ η hc p hp q z f j = 0 ↔
      genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        ((e : ℤ) * q) (refineLattice e he z) f j = 0 := by
  have htransport := refineLattice_genericVariation
    (E := E) δ η hc p e hp he q z f j
  constructor
  · intro hz
    rw [← htransport, hz, refineLattice_zero]
  · intro hz
    apply (refineLattice_injective e he)
    rw [htransport, hz, refineLattice_zero]

/-- Refinement multiplies the exact Laurent order of a nonzero generic
variation by the refinement factor. -/
theorem refineLattice_genericVariation_order
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (j : ℕ)
    (hV : genericVariation (E := E) δ η hc p hp q z f j ≠ 0) :
    (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      ((e : ℤ) * q) (refineLattice e he z) f j).order =
      (e : ℤ) * (genericVariation (E := E) δ η hc p hp q z f j).order := by
  rw [← refineLattice_genericVariation (E := E) δ η hc p e hp he q z f j,
    order_refineLattice]

/-- The frequently used zero-slope instance. -/
theorem refineLattice_genericVariation_zero_order
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (j : ℕ)
    (hV : genericVariation (E := E) δ η hc p hp 0 z f j ≠ 0) :
    (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      0 (refineLattice e he z) f j).order =
      (e : ℤ) * (genericVariation (E := E) δ η hc p hp 0 z f j).order := by
  simpa using refineLattice_genericVariation_order
    (E := E) δ η hc p e hp he 0 z f j hV

/-- The complete generic residual is transported by the same refinement. -/
theorem refineLattice_genericResidual
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) :
    refineLattice e he
        (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f) =
      NewtonResidual.genericResidual (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        ((e : ℤ) * q) (refineLattice e he z) f := by
  unfold NewtonResidual.genericResidual
  rw [refineLattice_evaluateAt]
  congr 2
  simp [NewtonResidual.genericCorrectedSymbol, mapField_refineLattice]

/-- Lower-bound information for the generic residual is equivalent before and
after refinement, with the bound scaled by the refinement factor. -/
theorem refineLattice_genericResidual_lowerBound_iff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (b : ℤ) :
    LowerBound ((e : ℤ) * b)
        (NewtonResidual.genericResidual (E := E) δ η hc (p * e)
          (Nat.mul_pos hp he) ((e : ℤ) * q) (refineLattice e he z) f) ↔
      LowerBound b (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f) := by
  rw [← refineLattice_genericResidual (E := E) δ η hc p e hp he q z f,
    lowerBound_refineLattice_iff]

/-- Coefficients on the inherited lattice are unchanged by refinement. -/
theorem refineLattice_genericResidual_coeff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (r : ℤ) :
    (NewtonResidual.genericResidual (E := E) δ η hc (p * e)
      (Nat.mul_pos hp he) ((e : ℤ) * q) (refineLattice e he z) f).coeff
        ((e : ℤ) * r) =
      (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f).coeff r := by
  rw [← refineLattice_genericResidual (E := E) δ η hc p e hp he q z f,
    refineLattice_coeff]

end

end MakarLimanov.GenericSlopeRefinement
