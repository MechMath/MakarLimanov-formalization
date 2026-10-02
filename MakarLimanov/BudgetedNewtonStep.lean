import MakarLimanov.SparseNewtonRoot
import MakarLimanov.ResidualPolynomial
import MakarLimanov.ResidualConstantTerm

/-!
# A residual correction retaining its multiplicity budget

The residual representative, its sparse factor, the differential root, and
the improved Laurent bound are constructed together. The multiplicity in the
ramification bound is also the first nonzero translated homogeneous degree.
-/

noncomputable section

namespace MakarLimanov.BudgetedNewtonStep

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients NewtonResidual

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero k] [CharZero F] [CharZero E]

/-- A genuine Newton correction with the degree and ramification budget of
the same selected factor, using only variation coefficients active at `r`. -/
theorem corrected_stage_with_budget
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ) (e B : ℕ) (he : 0 < e)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (hres : (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0)
    (hactive : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0)
    (hdiv : ∀ j, (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      e ∣ j)
    (hdegree : ∀ j, (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      j ≤ B) :
    ∃ (Ψ : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      algebraMap (MvPolynomial (ℕ × ℕ) F) E Ψ =
        (genericResidual (E := E) δ η hc p hp q z f).coeff r ∧
      0 < m ∧ e * m ≤ B ∧
      ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G)
        (_ : Algebra F G) (_ : IsScalarTower k F G),
        ∃ (D H : Derivation k G G) (w : G), ∃ hDH : Function.Commute D H,
        (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
        (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
        (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
        LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
        LowerBound (r + 1)
          (toSeries (evaluateAt (hp := hp) (h := hDH)
            (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) ∧
        (let jets : ℕ × ℕ → G := fun ij ↦ D^[ij.1] (H^[ij.2] w)
        let translated := NewtonTranslation.translate jets (MvPolynomial.map (algebraMap F G) Ψ)
        (∀ j < m, MvPolynomial.homogeneousComponent j translated = 0) ∧
        MvPolynomial.homogeneousComponent m translated ≠ 0) := by
  obtain ⟨Ψ, _hΨ0, hΨnu, hΨmap, hsparse⟩ :=
    ResidualPolynomial.exists_nonunit_residual_coefficient_representative_sparse
      (E := E) δ η hc p hp q z f r e hactive hdiv
  have hconst : MvPolynomial.constantCoeff Ψ ≠ 0 :=
    ResidualConstantTerm.residual_coefficient_constantCoeff_ne_zero
      (E := E) δ η hc p hp q z f r Ψ hΨmap hres
  have hdeg : Ψ.totalDegree ≤ B :=
    ResidualPolynomial.totalDegree_le_of_active_bound
      (E := E) δ η hc p hp q z f r B Ψ hΨmap hdegree
  obtain ⟨m, hm, hbudget, G, hG, hkG, hFG, hkFG, D, H, w, hDH, hD, hH,
      hroot, hlow, htop⟩ :=
    SparseNewtonRoot.exists_polynomial_step_with_budget Ψ e he hconst hsparse hΨnu δ η hc
  letI : CharZero G := charZero_of_injective_algebraMap (algebraMap F G).injective
  obtain ⟨hfinite, hbound, hprogress⟩ :=
    NewtonResidual.corrected_symbol_of_root
      (E := E) (G := G) δ η hc p hp q z D H hDH hD hH w f b r
      hz hb hq hr Ψ hΨmap hroot
  exact ⟨Ψ, m, hΨmap, hm, hbudget.trans hdeg, G, hG, inferInstance, hkG, hFG, hkFG,
    D, H, w, hDH, hD, hH, hfinite, hbound, hprogress, hlow, htop⟩

end MakarLimanov.BudgetedNewtonStep
