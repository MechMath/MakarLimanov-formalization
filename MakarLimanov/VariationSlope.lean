import MakarLimanov.SymbolVariations
import MakarLimanov.VariationHomogeneity
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Slope covariance and leading variation interfaces

The Newton argument uses two exact identities repeatedly: translating a symbol by a
monomial perturbation is a finite binomial transform of the old variations, and
twisting the perturbation by a differential eigen-monomial shifts the order of its
`n`-th variation by `n*q`.  The underlying identities are proved in
`Variations` and `SymbolVariations`; this file packages them for the generic
variation construction and records the nonzero homogeneous coefficient interface.
-/

namespace MakarLimanov.VariationSlope

open HahnSeries SymbolSeries SymbolSeries.StarSeries SymbolVariations
open VariationCoefficients VariationHomogeneity

noncomputable section

variable {k F E G : Type*} [Field k] [Field F] [Field E] [Field G]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E] [Algebra k G] [Algebra F G]
  [IsScalarTower k F G] [CharZero G]

open GenericJets JetSpecialization

/- The translated coefficient identity, with all coefficients in the generic
   differential field.  No support or nonvanishing assumption is needed. -/
theorem genericVariation_shift
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (z v : LaurentSeries E)
    (f : FreeAlgebra k Bool) (n : ℕ) :
    SymbolVariations.variation (hp := hp)
        (h := GenericJets.commute δ η hc) f (z + v) v n =
      ∑ j ∈ (Variations.expansion (ofSeries (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc) z)
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc) v) f).support,
        (j.choose n) •
          SymbolVariations.variation (hp := hp)
            (h := GenericJets.commute δ η hc) f z v j := by
  exact SymbolVariations.variation_shift f z v n

/- Exact slope covariance for a differential eigen-monomial.  The condition on
   `a` is precisely the one making `single q a` central for the star product. -/
theorem variation_slope_covariance
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (z v : LaurentSeries E)
    (f : FreeAlgebra k Bool) (a : E) (q : ℤ)
    (ha : a ≠ 0)
    (haδ : (GenericJets.delta δ) a = 0)
    (haη : (GenericJets.eta η) a = (p : E)⁻¹ * (q : E) * a)
    (n : ℕ)
    (hv : SymbolVariations.variation (hp := hp)
      (h := GenericJets.commute δ η hc) f z v n ≠ 0) :
    (SymbolVariations.variation (hp := hp)
      (h := GenericJets.commute δ η hc) f z ((single q a) * v) n).order =
      (n : ℤ) * q +
        (SymbolVariations.variation (hp := hp)
          (h := GenericJets.commute δ η hc) f z v n).order := by
  exact SymbolVariations.monomial_order f z v a ha q haδ haη n hv

/- A nonzero universal leading coefficient has a nonzero homogeneous jet
   representative.  This is the exact algebraic interface consumed by the
   Newton factor step; specialization remains available through the final field
   equality in the conclusion. -/
theorem exists_nonzero_homogeneous_variation_coefficient
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ) (hj : 0 < j)
    (hcoef : (VariationCoefficients.genericVariation (E := E)
      δ η hc p hp q z f j).coeff n ≠ 0) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      P.IsHomogeneous j ∧ P ≠ 0 ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (VariationCoefficients.genericVariation (E := E)
          δ η hc p hp q z f j).coeff n ∧
      ¬ IsUnit P := by
  obtain ⟨P, hhom, hmap, _hspecial⟩ :=
    exists_homogeneous_universal_variation_coefficient
      (E := E) (G := E) δ η hc p hp q z f j n
  have hP : P.IsHomogeneous j := hhom
  have hP0 : P ≠ 0 := by
    intro hzero
    apply hcoef
    rw [← hmap, hzero, map_zero]
  have hunit : ¬ IsUnit P := by
    intro hu
    have hdeg : P.totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have hhomdeg : P.totalDegree = j := hhom.totalDegree hP0
    omega
  exact ⟨P, hhom, hP0, hmap, hunit⟩

end

end MakarLimanov.VariationSlope
