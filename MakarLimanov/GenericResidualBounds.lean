import MakarLimanov.ResidualPolynomial

/-!
# Homogeneous separation for generic residual coefficients

The coefficient of the generic residual is a sum of coefficients of distinct
homogeneous degrees.  We record the resulting coefficientwise and lower-bound
equivalences.  These are the formal version of the uniqueness argument used in
the proof of Lemma 8 in the paper.
-/

noncomputable section

namespace MakarLimanov.GenericResidualBounds

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open VariationCoefficients VariationHomogeneity GenericResidualHomogeneous
open NewtonResidual ResidualPolynomial

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

private def residualSupport (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) : Finset ℕ :=
  (Variations.expansion
    (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
      (distinguishedSymbol p))
    (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
      (mapField (IsScalarTower.toAlgHom k F E) z))
    (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
      (HahnSeries.single q (jet (F := F) 0 0))) f).support

private theorem finite_sum_nonzero_of_component
    (S : Finset ℕ) (Q : ℕ → MvPolynomial (ℕ × ℕ) F)
    (hhom : ∀ j ∈ S, (Q j).IsHomogeneous j)
    {j : ℕ} (hjS : j ∈ S) (hjQ : Q j ≠ 0) :
    (∑ l ∈ S, Q l) ≠ 0 := by
  have hjcoeff : (Q j).coeff ≠ 0 := by
    intro h
    apply hjQ
    apply AddMonoidAlgebra.coeff_injective
    simpa using h
  obtain ⟨d, hd⟩ := Finsupp.support_nonempty_iff.mpr hjcoeff
  have hdcoef : (Q j).coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
  have hother : ∀ l ∈ S, l ≠ j → (Q l).coeff d = 0 := by
    intro l hl hlj
    by_contra hne
    have hld : d.degree = l := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hhom l hl hne
    have hjd : d.degree = j := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hhom j hjS hdcoef
    omega
  have hsumcoef : (∑ l ∈ S, Q l).coeff d ≠ 0 := by
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j]
    · simpa using hdcoef
    · intro l hl hlj
      exact hother l hl hlj
    · intro hnot
      exact (hnot hjS).elim
  intro hzero
  exact hsumcoef (by simpa [hzero])

private theorem variation_coeff_zero_of_not_mem_support
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (r : ℤ)
    (hj : j ∉ (Variations.expansion
      (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
        (distinguishedSymbol p))
      (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
        (mapField (IsScalarTower.toAlgHom k F E) z))
      (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
        (HahnSeries.single q (jet (F := F) 0 0))) f).support) :
    (genericVariation (E := E) δ η hc p hp q z f j).coeff r = 0 := by
  have hcoeff :
      (Variations.expansion
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (mapField (IsScalarTower.toAlgHom k F E) z))
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (HahnSeries.single q (jet (F := F) 0 0))) f).coeff j = 0 := by
    by_contra hne
    exact hj (Polynomial.mem_support_iff.mpr hne)
  change
    ((Variations.expansion
      (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
        (distinguishedSymbol p))
      (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
        (mapField (IsScalarTower.toAlgHom k F E) z))
      (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
        (HahnSeries.single q (jet (F := F) 0 0))) f).coeff j).toSeries.coeff r = 0
  rw [hcoeff]
  rfl

/-- Vanishing of one generic residual coefficient is equivalent to vanishing of
all homogeneous variation coefficients contributing to it. -/
theorem genericResidual_coeff_zero_iff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) :
    (genericResidual (E := E) δ η hc p hp q z f).coeff r = 0 ↔
      ∀ j : ℕ, (genericVariation (E := E) δ η hc p hp q z f j).coeff r = 0 := by
  let S := residualSupport (E := E) δ η hc p hp q z f
  constructor
  · intro hres j
    obtain ⟨P, hPmap, Q, hQhom, hQmap, hPsum⟩ :=
      exists_residual_coefficient_representative (E := E) δ η hc p hp q z f r
    have hPsum' : P = ∑ l ∈ S, Q l := by
      simpa [S, residualSupport, ResidualPolynomial.residualVariationSupport] using hPsum
    have hQhom' : ∀ l ∈ S, (Q l).IsHomogeneous l := by
      intro l hl
      apply hQhom l
      apply Polynomial.mem_support_iff.mpr
      simpa [S, residualSupport, ResidualPolynomial.residualVariationSupport] using hl
    have hQmap' : ∀ l ∈ S,
        algebraMap (MvPolynomial (ℕ × ℕ) F) E (Q l) =
          (genericVariation (E := E) δ η hc p hp q z f l).coeff r := by
      intro l hl
      apply hQmap l
      apply Polynomial.mem_support_iff.mpr
      simpa [S, residualSupport, ResidualPolynomial.residualVariationSupport] using hl
    have hPzero : P = 0 := by
      apply (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
      rw [hPmap, hres]
      exact (map_zero (algebraMap (MvPolynomial (ℕ × ℕ) F) E)).symm
    by_cases hjS : j ∈ S
    · have hQzero : Q j = 0 := by
        by_contra hQ
        have hsum := finite_sum_nonzero_of_component S Q hQhom' hjS hQ
        apply hsum
        rw [← hPsum', hPzero]
      rw [← hQmap' j hjS, hQzero, map_zero]
    · exact variation_coeff_zero_of_not_mem_support
        (E := E) δ η hc p hp q z f j r hjS
  · intro hzero
    rw [genericResidual_coeff_sum]
    let S := residualSupport (E := E) δ η hc p hp q z f
    apply Finset.sum_eq_zero
    intro j hjS
    exact hzero j

/-- Lower bounds of the residual are equivalent to lower bounds of all its
homogeneous variation components. -/
theorem genericResidual_lowerBound_iff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b : ℤ) :
    LowerBound b (genericResidual (E := E) δ η hc p hp q z f) ↔
      ∀ j : ℕ, LowerBound b (genericVariation (E := E) δ η hc p hp q z f j) := by
  constructor
  · intro hr j n hn
    exact (genericResidual_coeff_zero_iff (E := E) δ η hc p hp q z f n).mp
      (hr n hn) j
  · intro hv n hn
    apply (genericResidual_coeff_zero_iff (E := E) δ η hc p hp q z f n).mpr
    intro j
    exact hv j n hn

/-- The same coefficient criterion with the finite word-degree range made
explicit.  Variations above the word degree vanish identically. -/
theorem genericResidual_coeff_zero_iff_bounded
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) :
    (genericResidual (E := E) δ η hc p hp q z f).coeff r = 0 ↔
      ∀ j : ℕ, j ≤ ControlledMatrix.wordDegree f →
        (genericVariation (E := E) δ η hc p hp q z f j).coeff r = 0 := by
  constructor
  · intro hres j hj
    exact (genericResidual_coeff_zero_iff (E := E) δ η hc p hp q z f r).mp hres j
  · intro hfinite
    apply (genericResidual_coeff_zero_iff (E := E) δ η hc p hp q z f r).mpr
    intro j
    by_cases hj : j ≤ ControlledMatrix.wordDegree f
    · exact hfinite j hj
    · have hvan : genericVariation (E := E) δ η hc p hp q z f j = 0 := by
        apply genericResidual_variation_degree_bound (E := E) δ η hc p hp q z f j
        exact Nat.lt_of_not_ge hj
      rw [hvan]
      rfl

/-- If the order-zero term vanishes while the residual coefficient does not,
some positive-degree variation at that coefficient is nonzero. -/
theorem exists_positive_variation_coeff_of_nonzero_residual
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (hcoef : (genericResidual (E := E) δ η hc p hp q z f).coeff r ≠ 0)
    (hzero : (genericVariation (E := E) δ η hc p hp q z f 0).coeff r = 0) :
    ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 := by
  by_contra hnone
  apply hcoef
  apply (genericResidual_coeff_zero_iff (E := E) δ η hc p hp q z f r).mpr
  intro j
  by_cases hj : j = 0
  · simpa [hj] using hzero
  · by_contra hne
    exact hnone ⟨j, Nat.pos_of_ne_zero hj, hne⟩

end MakarLimanov.GenericResidualBounds
