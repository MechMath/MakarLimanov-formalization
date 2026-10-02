import MakarLimanov.ResidualConstantTerm
import MakarLimanov.FiniteJets
import MakarLimanov.HomogeneousRamification

/-!
# Factor budgets for a homogeneous residual representative

The constant term of a universal residual coefficient is inherited from the
uncorrected residual.  Once a representative is known to be homogeneous, the
finite-jet factorisation and the homogeneous ramification estimate therefore
give the multiplicity budget used in the Newton descent.
-/

noncomputable section

namespace MakarLimanov.ResidualFactorBudget

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open NewtonResidual
open MakarLimanov.ResidualConstantTerm
open MakarLimanov.FiniteJets
open MakarLimanov.HomogeneousRamification
open MakarLimanov.FiniteNewtonInduction
open MakarLimanov.JetRamificationBudget

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

/-- A homogeneous polynomial representative of a nonzero residual coefficient
has a finite factorisation whose multiplicity satisfies the ramification
budget.  The constant term is supplied by the uncorrected residual through
`residual_coefficient_constantCoeff_ne_zero`.
-/
theorem exists_factorisation_with_budget
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (Ψ : MvPolynomial (ℕ × ℕ) F)
    (hΨ : algebraMap (MvPolynomial (ℕ × ℕ) F) E Ψ =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (huncorrected :
      (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0)
    (hΨ0 : Ψ ≠ 0) (hΨnu : ¬ IsUnit Ψ)
    (j e : ℕ) (hhom : Ψ.IsHomogeneous j) (he : 0 < e) (hej : e ∣ j) :
    ∃ (P Q : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      Irreducible P ∧ 0 < m ∧ Ψ = P ^ m * Q ∧ ¬ P ∣ Q ∧
      differentialOrder P = differentialOrder Ψ ∧
      differentialOrder Q ≤ differentialOrder P ∧ e * m ≤ j := by
  have hconst : MvPolynomial.constantCoeff Ψ ≠ 0 :=
    residual_coefficient_constantCoeff_ne_zero
      (E := E) δ η hc p hp q z f r Ψ hΨ huncorrected
  obtain ⟨P, Q, m, hP, hm, hfactor, hPnotdvd, horderP, horderQ⟩ :=
    exists_exact_factorization Ψ hΨnu hΨ0
  let N := differentialOrder Ψ
  obtain ⟨P', hP'⟩ := exists_triangle P N horderP.le
  obtain ⟨Q', hQ'⟩ := exists_triangle Q N (horderQ.trans horderP.le)
  have hinc : includeTriangle N (trianglePolynomial Ψ) = Ψ := by
    simpa [N] using (include_trianglePolynomial Ψ)
  have hconst' : MvPolynomial.constantCoeff (trianglePolynomial Ψ) ≠ 0 := by
    have hcc : MvPolynomial.constantCoeff (includeTriangle N (trianglePolynomial Ψ)) =
        MvPolynomial.constantCoeff (trianglePolynomial Ψ) := by
      simp [includeTriangle, MvPolynomial.constantCoeff_rename]
    rw [hinc] at hcc
    rw [← hcc]
    exact hconst
  have hhom' : (trianglePolynomial Ψ).IsHomogeneous j := by
    intro d hd
    have hd' : d ∈ (trianglePolynomial Ψ).support :=
      MvPolynomial.mem_support_iff.mpr hd
    have hsupport : Finsupp.mapDomain Subtype.val d ∈
        (includeTriangle N (trianglePolynomial Ψ)).support := by
      rw [includeTriangle, MvPolynomial.support_rename_of_injective Subtype.val_injective]
      exact Finset.mem_image.mpr ⟨d, hd', rfl⟩
    rw [hinc] at hsupport
    have hdeg := hhom (MvPolynomial.mem_support_iff.mp hsupport)
    simpa [Finsupp.weight,
      Finsupp.sum_mapDomain_index_inj Subtype.val_injective] using hdeg
  have hΨ'0 : trianglePolynomial Ψ ≠ 0 := by
    intro hz
    apply hΨ0
    rw [← hinc, hz, map_zero]
  have hdeg' : (trianglePolynomial Ψ).totalDegree = j :=
    hhom'.totalDegree hΨ'0
  have htri_eq : trianglePolynomial Ψ = P' ^ m * Q' := by
    apply includeTriangle_injective N
    rw [hinc, map_mul, map_pow, hP', hQ', hfactor]
  have hP'nu : ¬ IsUnit P' := by
    intro hu
    apply hP.not_isUnit
    rw [← hP']
    exact hu.map (includeTriangle N).toRingHom
  have hdiv' : P' ^ m ∣ trianglePolynomial Ψ := ⟨Q', htri_eq⟩
  have hs' : ∀ s ∈ (trianglePolynomial Ψ).support,
      e ∣ s.sum (fun _ n ↦ n) := by
    intro s hs
    have hinc_support : Finsupp.mapDomain Subtype.val s ∈
        (includeTriangle N (trianglePolynomial Ψ)).support := by
      rw [includeTriangle, MvPolynomial.support_rename_of_injective Subtype.val_injective]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    rw [hinc] at hinc_support
    have hfull := hinc_support
    have hdeg := homogeneous_support_divisible hhom hej _ hfull
    simpa only [Finsupp.sum_mapDomain_index_inj Subtype.val_injective] using hdeg
  have hbudget' := factor_degree_budget_triangle
    (Ψ := trianglePolynomial Ψ) (P := P') e m he hconst' hs' hP'nu hdiv'
  have hbudget : e * m ≤ j := by simpa [hdeg'] using hbudget'
  exact ⟨P, Q, m, hP, hm, hfactor, hPnotdvd, horderP, horderQ, hbudget⟩

/-- Variant exposing the constant-term hypothesis directly.  The residual
constant-term identity is used backwards to obtain the uncorrected residual
coefficient needed by `exists_factorisation_with_budget`. -/
theorem exists_factorisation_with_budget_of_constantCoeff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (Ψ : MvPolynomial (ℕ × ℕ) F)
    (hΨ : algebraMap (MvPolynomial (ℕ × ℕ) F) E Ψ =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hconst : MvPolynomial.constantCoeff Ψ ≠ 0)
    (hΨ0 : Ψ ≠ 0) (hΨnu : ¬ IsUnit Ψ)
    (j e : ℕ) (hhom : Ψ.IsHomogeneous j) (he : 0 < e) (hej : e ∣ j) :
    ∃ (P Q : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      Irreducible P ∧ 0 < m ∧ Ψ = P ^ m * Q ∧ ¬ P ∣ Q ∧
      differentialOrder P = differentialOrder Ψ ∧
      differentialOrder Q ≤ differentialOrder P ∧ e * m ≤ j := by
  have huncorrected :
      (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0 := by
    intro hz
    apply hconst
    rw [residual_coefficient_constantCoeff (E := E) δ η hc p hp q z f r Ψ hΨ]
    exact hz
  exact exists_factorisation_with_budget δ η hc p hp q z f r Ψ hΨ
    huncorrected hΨ0 hΨnu j e hhom he hej

end MakarLimanov.ResidualFactorBudget
