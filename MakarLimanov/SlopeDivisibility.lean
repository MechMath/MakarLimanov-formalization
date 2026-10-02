import MakarLimanov.ExactGenericSlope
import MakarLimanov.GenericSlopeRefinement
import MakarLimanov.LatticeDenominator

/-!
# The active-degree divisibility at a Newton slope

An active coefficient at an old-lattice residual order has exact order there.
Exact slope covariance then makes its slope contribution integral on the old
lattice.  The reduced slope denominator therefore gives precisely the sparse
homogeneous-degree condition needed by the ramification budget.
-/

namespace MakarLimanov.SlopeDivisibility

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

/-- On a fixed lattice, a nonzero coefficient at the residual order gives
the divisibility required by the reduced denominator of the selected slope. -/
theorem refinement_factor_dvd_of_active_coefficient_same_lattice
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q r : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (s : ℚ)
    (hs : s = (q : ℚ) / p) (j : ℕ)
    (horder : r ≤
      (genericVariation (E := E) δ η hc p hp q z f j).order)
    (hcoeff : (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0) :
    s.den / Nat.gcd p s.den ∣ j := by
  have hVq := HahnSeries.ne_zero_of_coeff_ne_zero hcoeff
  have hslope := ExactGenericSlope.genericVariation_slope (E := E)
    δ η hc p hp q z f j
  have hV0 : genericVariation (E := E) δ η hc p hp 0 z f j ≠ 0 := by
    intro hz
    exact hVq (hslope.1.mpr hz)
  have hexact := le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcoeff) horder
  have horder_eq : (j : ℤ) * q +
      (genericVariation (E := E) δ η hc p hp 0 z f j).order = r := by
    rw [← hslope.2 hV0]
    exact hexact
  apply LatticeDenominator.refinement_factor_dvd_of_order_equality s p j hp
    (genericVariation (E := E) δ η hc p hp 0 z f j).order r
  rw [hs]
  field_simp
  exact_mod_cast horder_eq

/-- All coefficient-active degrees share the reduced denominator factor. -/
theorem refinement_factor_dvd_of_active_coefficients_same_lattice
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q r : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (s : ℚ)
    (hs : s = (q : ℚ) / p)
    (horders : ∀ j : ℕ,
      genericVariation (E := E) δ η hc p hp q z f j = 0 ∨
        r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order) :
    ∀ j : ℕ,
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      s.den / Nat.gcd p s.den ∣ j := by
  intro j hj
  apply refinement_factor_dvd_of_active_coefficient_same_lattice
    (E := E) δ η hc p hp q r z f s hs j _ hj
  rcases horders j with hz | horder
  · exact (hj (by rw [hz, coeff_zero])).elim
  · exact horder

/-- A nonzero coefficient at the old residual order forces divisibility of its
homogeneous degree by the reduced denominator refinement factor.  Only that
coefficient must be active; variations beginning above the residual order play
no role in the assertion. -/
theorem refinement_factor_dvd_of_active_coefficient
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q r : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (s : ℚ)
    (hs : s = (q : ℚ) / (p * e : ℕ)) (j : ℕ)
    (horder : (e : ℤ) * r ≤
      (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        q (refineLattice e he z) f j).order)
    (hcoeff : (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q (refineLattice e he z) f j).coeff ((e : ℤ) * r) ≠ 0) :
    s.den / Nat.gcd p s.den ∣ j := by
  have hVq := HahnSeries.ne_zero_of_coeff_ne_zero hcoeff
  have hslope := ExactGenericSlope.genericVariation_slope (E := E)
    δ η hc (p * e) (Nat.mul_pos hp he) q (refineLattice e he z) f j
  have hVref : genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      0 (refineLattice e he z) f j ≠ 0 := by
    intro hz
    exact hVq (hslope.1.mpr hz)
  have hV0 : genericVariation (E := E) δ η hc p hp 0 z f j ≠ 0 := by
    intro hz
    apply hVref
    simpa using (GenericSlopeRefinement.refineLattice_genericVariation_eq_zero_iff
      (E := E) δ η hc p e hp he 0 z f j).mp hz
  have href := GenericSlopeRefinement.refineLattice_genericVariation_zero_order
    (E := E) δ η hc p e hp he z f j hV0
  have hexact := le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcoeff) horder
  have horders : (j : ℤ) * q +
      (e : ℤ) * (genericVariation (E := E) δ η hc p hp 0 z f j).order =
      (e : ℤ) * r := by
    rw [← href, ← hslope.2 hVref]
    exact hexact
  apply LatticeDenominator.refinement_factor_dvd_of_order_equality s p j hp
    (genericVariation (E := E) δ η hc p hp 0 z f j).order r
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have heQ : (e : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
  have hordersQ : (j : ℚ) * q +
      (e : ℚ) * (genericVariation (E := E) δ η hc p hp 0 z f j).order =
      (e : ℚ) * r := by exact_mod_cast horders
  rw [hs]
  push_cast
  field_simp
  nlinarith

/-- The coefficient-active sparse-support hypothesis for the residual
polynomial follows uniformly from the supporting-slope lower order bounds. -/
theorem refinement_factor_dvd_active_coefficients
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q r : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (s : ℚ)
    (hs : s = (q : ℚ) / (p * e : ℕ))
    (horders : ∀ j : ℕ,
      genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        q (refineLattice e he z) f j = 0 ∨
      (e : ℤ) * r ≤
        (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
          q (refineLattice e he z) f j).order) :
    ∀ j : ℕ,
      (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        q (refineLattice e he z) f j).coeff ((e : ℤ) * r) ≠ 0 →
      s.den / Nat.gcd p s.den ∣ j := by
  intro j hj
  apply refinement_factor_dvd_of_active_coefficient
    (E := E) δ η hc p e hp he q r z f s hs j _ hj
  rcases horders j with hz | horder
  · exact (hj (by rw [hz, coeff_zero])).elim
  · exact horder

end

end MakarLimanov.SlopeDivisibility
