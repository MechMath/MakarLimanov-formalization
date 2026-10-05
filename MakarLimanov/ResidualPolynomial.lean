import MakarLimanov.GenericResidualHomogeneous
import MakarLimanov.HomogeneousSum

/-!
# Polynomial representatives of generic residual coefficients

The residual coefficient is the finite sum of its homogeneous variation
coefficients.  Choosing the canonical polynomial representatives of those
coefficients gives a representative for the residual itself.  Any nonzero
positive-degree contribution makes this representative nonzero and nonunit.
-/

noncomputable section

namespace MakarLimanov.ResidualPolynomial

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open VariationCoefficients VariationHomogeneity GenericResidualHomogeneous

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

def residualVariationSupport (E : Type u) [Field E]
    [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    [Algebra (MvPolynomial (ℕ × ℕ) F) E]
    [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
    [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
    [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E] [CharZero E]
    (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) : Finset ℕ :=
  (Variations.expansion
    (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
      (distinguishedSymbol p))
    (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
      (mapField (IsScalarTower.toAlgHom k F E) z))
    (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
      (HahnSeries.single q (jet (F := F) 0 0))) f).support

/-- Pick, for every variation index, its homogeneous universal coefficient
representative. -/
private def variationRepresentative (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (r : ℤ) (j : ℕ) :
    MvPolynomial (ℕ × ℕ) F :=
  Classical.choose (exists_homogeneous_universal_variation_coefficient
    (E := E) (G := E) δ η hc p hp q z f j r)

private theorem variationRepresentative_spec (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (r : ℤ) (j : ℕ) :
    (variationRepresentative (E := E) δ η hc p hp q z f r j).IsHomogeneous j ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E
        (variationRepresentative (E := E) δ η hc p hp q z f r j) =
        (genericVariation (E := E) δ η hc p hp q z f j).coeff r := by
  rcases Classical.choose_spec (exists_homogeneous_universal_variation_coefficient
    (E := E) (G := E) δ η hc p hp q z f j r) with ⟨hh, hm, _⟩
  exact ⟨hh, hm⟩

private theorem finite_sum_nonzero_of_positive_component
    (S : Finset ℕ) (Q : ℕ → MvPolynomial (ℕ × ℕ) F)
    (hhom : ∀ j ∈ S, (Q j).IsHomogeneous j)
    (hpos : ∃ j ∈ S, 0 < j ∧ Q j ≠ 0) :
    (∑ j ∈ S, Q j) ≠ 0 := by
  obtain ⟨j, hjS, hjpos, hjQ⟩ := hpos
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

/-- The actual coefficient of a generic residual has a polynomial representative
which is the sum of the homogeneous representatives of all its variations. -/
theorem exists_residual_coefficient_representative
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r ∧
      ∃ Q : ℕ → MvPolynomial (ℕ × ℕ) F,
        (∀ j ∈ residualVariationSupport E δ η hc p hp q z f,
          (Q j).IsHomogeneous j) ∧
        (∀ j ∈ residualVariationSupport E δ η hc p hp q z f,
          algebraMap (MvPolynomial (ℕ × ℕ) F) E (Q j) =
            (genericVariation (E := E) δ η hc p hp q z f j).coeff r) ∧
        P = ∑ j ∈ residualVariationSupport E δ η hc p hp q z f, Q j := by
  let S := residualVariationSupport E δ η hc p hp q z f
  let Q := variationRepresentative (E := E) δ η hc p hp q z f r
  let P : MvPolynomial (ℕ × ℕ) F := ∑ j ∈ S, Q j
  have hhom : ∀ j ∈ S, (Q j).IsHomogeneous j := by
    intro j hj
    exact (variationRepresentative_spec (E := E) δ η hc p hp q z f r j).1
  have hmap : ∀ j ∈ S,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E (Q j) =
        (genericVariation (E := E) δ η hc p hp q z f j).coeff r := by
    intro j hj
    simpa [genericVariation, SymbolVariations.variation] using
      (variationRepresentative_spec (E := E) δ η hc p hp q z f r j).2
  have hsum : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r := by
    change algebraMap (MvPolynomial (ℕ × ℕ) F) E (∑ j ∈ S, Q j) = _
    rw [map_sum, GenericResidualHomogeneous.genericResidual_coeff_sum]
    dsimp [S, residualVariationSupport]
    apply Finset.sum_congr rfl
    intro j hj
    simpa [genericVariation, SymbolVariations.variation] using (hmap j hj)
  exact ⟨P, hsum, Q, hhom, hmap, rfl⟩

/-- A positive-degree nonzero variation contribution makes the actual residual
coefficient representative nonzero and nonunit.  In particular, no separate
nonvanishing hypothesis on the full residual coefficient is needed. -/
theorem exists_nonunit_residual_coefficient_representative
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (hactive : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      P ≠ 0 ∧ ¬ IsUnit P ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r := by
  obtain ⟨P, hPmap, Q, hQhom, hQmap, rfl⟩ :=
    exists_residual_coefficient_representative (E := E) δ η hc p hp q z f r
  let S := residualVariationSupport E δ η hc p hp q z f
  have hpos : ∃ j ∈ S, 0 < j ∧ Q j ≠ 0 := by
    obtain ⟨j, hjpos, hjcoef⟩ := hactive
    have hjS : j ∈ S := by
      dsimp [S, residualVariationSupport]
      apply Polynomial.mem_support_iff.mpr
      intro hcoeff
      apply hjcoef
      simp [genericVariation, SymbolVariations.variation, Variations.variation,
        hcoeff]
    have hQj : Q j ≠ 0 := by
      intro hzero
      apply hjcoef
      rw [← hQmap j hjS, hzero, map_zero]
    exact ⟨j, hjS, hjpos, hQj⟩
  have hnonzero : (∑ j ∈ S, Q j) ≠ 0 :=
    finite_sum_nonzero_of_positive_component S Q hQhom hpos
  have hnonunit : ¬ IsUnit (∑ j ∈ S, Q j) :=
    HomogeneousSum.nonunit_of_nonzero_positive_component S Q hQhom hpos
  exact ⟨∑ j ∈ S, Q j, hnonzero, hnonunit, hPmap⟩

/- The finite sum representative inherits divisibility of all active
   homogeneous degrees.  This is the sparse-support form needed by the
   root-of-unity degree budget in Lemma 9. -/
theorem exists_residual_coefficient_representative_sparse
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (e : ℕ)
    (hdiv : ∀ j, (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      e ∣ j) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r ∧
      ∀ d ∈ P.support, e ∣ d.degree := by
  obtain ⟨P, hPmap, Q, hQhom, hQmap, hPsum⟩ :=
    exists_residual_coefficient_representative (E := E) δ η hc p hp q z f r
  refine ⟨P, hPmap, ?_⟩
  intro d hd
  have hdcoef : P.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
  rw [hPsum, MvPolynomial.coeff_sum] at hdcoef
  by_contra hnot
  apply hdcoef
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hq : (Q j).coeff d = 0
  · exact hq
  · have hdj : d.degree = j := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hQhom j hj hq
    have hactive : (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 := by
      intro hz
      have hQzero : Q j = 0 :=
        (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
          (by rw [hQmap j hj, hz, map_zero])
      exact hq (by simp [hQzero])
    exact False.elim (hnot (hdj ▸ hdiv j hactive))

/- The sparse representative can be chosen together with the nonunit
   certificate supplied by a positive active variation. -/
theorem exists_nonunit_residual_coefficient_representative_sparse
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (e : ℕ)
    (hactive : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0)
    (hdiv : ∀ j, (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      e ∣ j) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      P ≠ 0 ∧ ¬ IsUnit P ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r ∧
      ∀ d ∈ P.support, e ∣ d.degree := by
  obtain ⟨P, hPmap, Q, hQhom, hQmap, hPsum⟩ :=
    exists_residual_coefficient_representative (E := E) δ η hc p hp q z f r
  let S := residualVariationSupport E δ η hc p hp q z f
  have hpos : ∃ j ∈ S, 0 < j ∧ Q j ≠ 0 := by
    obtain ⟨j, hjpos, hjcoef⟩ := hactive
    have hjS : j ∈ S := by
      dsimp [S, residualVariationSupport]
      apply Polynomial.mem_support_iff.mpr
      intro hcoeff
      apply hjcoef
      simp [genericVariation, SymbolVariations.variation, Variations.variation,
        hcoeff]
    have hQj : Q j ≠ 0 := by
      intro hzero
      apply hjcoef
      rw [← hQmap j hjS, hzero, map_zero]
    exact ⟨j, hjS, hjpos, hQj⟩
  have hnonzero : P ≠ 0 := by
    rw [hPsum]
    exact finite_sum_nonzero_of_positive_component S Q hQhom hpos
  have hnonunit : ¬ IsUnit P := by
    rw [hPsum]
    exact HomogeneousSum.nonunit_of_nonzero_positive_component S Q hQhom hpos
  refine ⟨P, hnonzero, hnonunit, hPmap, ?_⟩
  intro d hd
  have hdcoef : P.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
  rw [hPsum, MvPolynomial.coeff_sum] at hdcoef
  by_contra hnot
  apply hdcoef
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hq : (Q j).coeff d = 0
  · exact hq
  · have hdj : d.degree = j := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hQhom j hj hq
    have hjactive : (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 := by
      intro hz
      have hQzero : Q j = 0 :=
        (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
          (by rw [hQmap j hj, hz, map_zero])
      exact hq (by simp [hQzero])
    exact False.elim (hnot (hdj ▸ hdiv j hjactive))

/-- Each monomial in a residual coefficient comes from a nonzero variation
coefficient of exactly that monomial's total degree. -/
theorem support_degree_active
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r)
    (d : (ℕ × ℕ) →₀ ℕ) (hd : d ∈ P.support) :
    (genericVariation (E := E) δ η hc p hp q z f d.degree).coeff r ≠ 0 := by
  obtain ⟨R, hRmap, Q, hQhom, hQmap, hRsum⟩ :=
    exists_residual_coefficient_representative (E := E) δ η hc p hp q z f r
  have hPR : P = R := (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
    (hP.trans hRmap.symm)
  have hdcoef : P.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
  rw [hPR, hRsum, MvPolynomial.coeff_sum] at hdcoef
  obtain ⟨j, hj, hjcoef⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdcoef
  have hdj : d.degree = j := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hQhom j hj hjcoef
  rw [hdj]
  intro hz
  have hQzero : Q j = 0 :=
    (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
      (by rw [hQmap j hj, hz, map_zero])
  exact hjcoef (by simp [hQzero])

/-- The degree budget only concerns variations active at the selected Laurent
coefficient. It bounds every representative of that coefficient. -/
theorem totalDegree_le_of_active_bound
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (b : ℕ)
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r)
    (hb : ∀ j, (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      j ≤ b) :
    P.totalDegree ≤ b := by
  apply Finset.sup_le
  intro d hd
  exact hb d.degree (support_degree_active (E := E) δ η hc p hp q z f r P hP d hd)

/-- Homogeneous projection of the actual residual representative recovers
exactly the corresponding variation coefficient. This identifies the
translated polynomial's multiplicity with actual variation coefficients. -/
theorem homogeneousComponent_map
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (NewtonResidual.genericResidual δ η hc p hp q z f).coeff r)
    (j : ℕ) :
    algebraMap (MvPolynomial (ℕ × ℕ) F) E (MvPolynomial.homogeneousComponent j P) =
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r := by
  classical
  obtain ⟨R, hRmap, Q, hQhom, hQmap, hRsum⟩ :=
    exists_residual_coefficient_representative (E := E) δ η hc p hp q z f r
  have hPR : P = R := (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
    (hP.trans hRmap.symm)
  rw [hPR, hRsum, map_sum, map_sum]
  by_cases hj : j ∈ residualVariationSupport E δ η hc p hp q z f
  · rw [Finset.sum_eq_single j]
    · rw [MvPolynomial.homogeneousComponent_of_mem (hQhom j hj), if_pos rfl]
      exact hQmap j hj
    · intro l hl hlj
      rw [MvPolynomial.homogeneousComponent_of_mem (hQhom l hl), if_neg hlj.symm, map_zero]
    · exact fun hnot ↦ (hnot hj).elim
  · have hsum : ∑ l ∈ residualVariationSupport E δ η hc p hp q z f,
        algebraMap (MvPolynomial (ℕ × ℕ) F) E (MvPolynomial.homogeneousComponent j (Q l)) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have hjl : j ≠ l := fun h ↦ hj (h ▸ hl)
      rw [MvPolynomial.homogeneousComponent_of_mem (hQhom l hl), if_neg hjl, map_zero]
    rw [hsum]
    have hv : (Variations.expansion
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc) (distinguishedSymbol p))
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (mapField (IsScalarTower.toAlgHom k F E) z))
        (ofSeries (hp := hp) (h := GenericJets.commute δ η hc)
          (HahnSeries.single q (jet (F := F) 0 0))) f).coeff j = 0 := by
      exact Polynomial.notMem_support_iff.mp hj
    simp [genericVariation, SymbolVariations.variation, Variations.variation, hv]

end MakarLimanov.ResidualPolynomial
