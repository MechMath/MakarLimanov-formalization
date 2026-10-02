import MakarLimanov.GenericNewtonPolynomial
import MakarLimanov.GenericNewtonSupport
import MakarLimanov.HomogeneousSum
import MakarLimanov.SparseFactorBudget
import MakarLimanov.ResidualSparseFactorBudget

/-!
# A certified single Newton stage

This module records the data which occur at one stage of the Newton argument
in `proof.pdf`.  The residual order, a finite set of active variation orders,
the rational slope and its refinement factor are kept as explicit data.  The
leading polynomial is represented as a finite sum of homogeneous components.

The point of the interface is that the algebraic conditions on this polynomial
are enough to call the checked one-step construction.  No factorisation or
choice of an extension is hidden in this interface.
-/

namespace MakarLimanov.NewtonStageSpec

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients VariationCoefficients
open NewtonResidual
open GenericNewtonSupport
open FiniteNewtonInduction
open ResidualSparseFactorBudget
open FiniteJets

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [CharZero k] [CharZero F] [CharZero E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/-- Data and invariants at one Newton stage.

`Ψ` is given as a finite sum of homogeneous pieces.  The `active_component`
field is the formal version of the nonzero positive-degree part in Lemma 8;
`constantCoeff_ne_zero` is the nonvanishing constant term used in Lemma 9.
The fields `slope`, `slope_den`, and `refinement_factor` retain the lattice
bookkeeping, while `factor_budget` is the chosen inequality `e*m ≤ deg Ψ`.
-/
structure Stage
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ) where
  finite_support : z.support.Finite
  symbol_lower_bound : LowerBound b z
  target_above_symbol : b ≤ q
  variation_lower_orders : ∀ j : ℕ,
    genericVariation (E := E) δ η hc p hp q z f j = 0 ∨
      r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order
  active_orders : Finset ℕ
  active_variation : ∃ j ∈ active_orders, 0 < j ∧
    genericVariation (E := E) δ η hc p hp q z f j ≠ 0 ∧
    (genericVariation (E := E) δ η hc p hp q z f j).order = r
  slope : ℚ
  slope_num : ℤ
  slope_den : ℕ
  slope_den_pos : 0 < slope_den
  slope_as_fraction : slope = (slope_num : ℚ) / (slope_den : ℚ)
  refinement_factor : ℕ
  refinement_factor_pos : 0 < refinement_factor
  slope_den_dvd_refinement : slope_den ∣ refinement_factor
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  Ψ : MvPolynomial (ℕ × ℕ) F
  components : Finset ℕ
  component : ℕ → MvPolynomial (ℕ × ℕ) F
  Ψ_decomposition : Ψ = ∑ j ∈ components, component j
  component_homogeneous : ∀ j ∈ components, (component j).IsHomogeneous j
  active_component : ∃ j ∈ components, 0 < j ∧ component j ≠ 0
  constantCoeff_ne_zero : MvPolynomial.constantCoeff Ψ ≠ 0
  factor_budget : refinement_factor * multiplicity ≤ Ψ.totalDegree
  residual_coefficient :
    algebraMap (MvPolynomial (ℕ × ℕ) F) E Ψ =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r

namespace Stage

variable {δ η : Derivation k F F} {hc : Function.Commute δ η}
  {p : ℕ} {hp : 0 < p} {q : ℤ} {z : LaurentSeries F}
  {f : FreeAlgebra k Bool} {b r : ℤ}

/-- A positive homogeneous component makes the stage polynomial nonunit. -/
theorem leading_polynomial_nonunit
    (S : Stage (E := E) δ η hc p hp q z f b r) : ¬ IsUnit S.Ψ := by
  rw [S.Ψ_decomposition]
  exact HomogeneousSum.nonunit_of_nonzero_positive_component S.components S.component
    S.component_homogeneous S.active_component

/-- The polynomial is nonzero because its constant coefficient is nonzero. -/
theorem leading_polynomial_ne_zero
    (S : Stage (E := E) δ η hc p hp q z f b r) : S.Ψ ≠ 0 := by
  intro hzero
  apply S.constantCoeff_ne_zero
  simp [hzero]

/-- The numerical part of the Lemma 9 budget is available at the stage. -/
theorem chosen_factor_budget
    (S : Stage (E := E) δ η hc p hp q z f b r) :
    S.refinement_factor * S.multiplicity ≤ S.Ψ.totalDegree := S.factor_budget

/-- The factor budget can alternatively be reconstructed from sparse support.

This is the checked Lemma 9 interface.  It is useful when the stage data do
not yet contain a selected factor: the maximal differential-order factorisation
and its multiplicity are produced together with `e*m ≤ deg Ψ`.
-/
theorem exists_factorisation_with_budget
    (S : Stage (E := E) δ η hc p hp q z f b r)
    (hs : ∀ d ∈ S.Ψ.support,
      S.refinement_factor ∣ d.sum (fun _ n ↦ n)) :
    ∃ (P Q : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      Irreducible P ∧ 0 < m ∧ S.Ψ = P ^ m * Q ∧ ¬ P ∣ Q ∧
      differentialOrder P = differentialOrder S.Ψ ∧
      differentialOrder Q ≤ differentialOrder P ∧
      S.refinement_factor * m ≤ S.Ψ.totalDegree := by
  exact SparseFactorBudget.exists_factorisation_with_sparse_budget S.Ψ
    S.refinement_factor S.refinement_factor_pos S.constantCoeff_ne_zero hs
    (leading_polynomial_nonunit S)

/- The canonical residual representative has the same budget once the
   uncorrected leading coefficient is known to be nonzero. -/
theorem exists_residual_factorisation_with_budget
    (S : Stage (E := E) δ η hc p hp q z f b r)
    (hres : (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0)
    (hs : ∀ j, (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 →
      S.refinement_factor ∣ j) :
    ∃ (Ψ P Q : MvPolynomial (ℕ × ℕ) F) (m : ℕ),
      Ψ ≠ 0 ∧ ¬ IsUnit Ψ ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E Ψ =
        (genericResidual (E := E) δ η hc p hp q z f).coeff r ∧
      Irreducible P ∧ 0 < m ∧ Ψ = P ^ m * Q ∧ ¬ P ∣ Q ∧
      differentialOrder P = differentialOrder Ψ ∧
      differentialOrder Q ≤ differentialOrder P ∧
      S.refinement_factor * m ≤ Ψ.totalDegree := by
  have hact : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 := by
    obtain ⟨j, _hjA, hj, hV, horder⟩ := S.active_variation
    exact ⟨j, hj,
      GenericNewtonSupport.active_coefficient_of_exact_order
        (E := E) δ η hc p hp q z f r j hj hV horder⟩
  exact ResidualSparseFactorBudget.exists_residual_factorisation_with_sparse_budget
    (E := E) δ η hc p hp q z f r S.refinement_factor
    S.refinement_factor_pos hres hact hs

/-- The active exact-order component supplies the coefficient required by the
generic leading-polynomial theorem. -/
theorem active_coefficient
    (S : Stage (E := E) δ η hc p hp q z f b r) :
    ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 := by
  obtain ⟨j, hjA, hj, hV, horder⟩ := S.active_variation
  exact ⟨j, hj,
    GenericNewtonSupport.active_coefficient_of_exact_order
      (E := E) δ η hc p hp q z f r j hj hV horder⟩

/-- `GenericNewtonPolynomial.exists_leading_polynomial` applied to a stage.

The old residual coefficient is the constant term of the leading polynomial,
so its nonvanishing is supplied by the untranslated evaluation hypothesis.
-/
theorem exists_certified_leading_polynomial
    (S : Stage (E := E) δ η hc p hp q z f b r)
    (hres : (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0) :
    ∃ P : MvPolynomial (ℕ × ℕ) F,
      P ≠ 0 ∧ ¬ IsUnit P ∧ MvPolynomial.constantCoeff P ≠ 0 ∧
      algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
        (genericResidual (E := E) δ η hc p hp q z f).coeff r := by
  exact GenericNewtonPolynomial.exists_leading_polynomial
    (E := E) δ η hc p hp q z f r hres S.active_coefficient

/-- The supporting-variation route to a one-step Newton correction.

This is exactly the interface used by the proof of Lemma 8: all variations
are above the selected residual order, and one positive-degree variation reaches
that order.  The result is the extension field, commuting derivations, and the
corrected symbol with the next Laurent lower bound.
-/
theorem corrected_stage_of_supporting_variation
    (S : Stage (E := E) δ η hc p hp q z f b r) :
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G)
      (_ : Algebra F G) (_ : IsScalarTower k F G),
      ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  obtain ⟨j, hjA, hj, hV, horder⟩ := S.active_variation
  exact MakarLimanov.GenericNewtonSupport.corrected_stage_of_supporting_variation
    (E := E) δ η hc p hp q z f b r S.finite_support S.symbol_lower_bound
    S.target_above_symbol S.variation_lower_orders j hj hV horder

/-- The leading polynomial `Ψ` itself can be fed to the checked Newton root.

The lower bound is obtained from the finite active-order inequalities, while
nonzeroness and nonunitness follow from the constant term and the positive
homogeneous component.  The factor budget is retained as an explicit premise
of the stage certificate and is available through `chosen_factor_budget`.
-/
theorem corrected_stage_from_leading_polynomial
    (S : Stage (E := E) δ η hc p hp q z f b r) :
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G)
      (_ : Algebra F G) (_ : IsScalarTower k F G),
      ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  have hr : LowerBound r
      (genericResidual (E := E) δ η hc p hp q z f) :=
    by
      apply MakarLimanov.GenericResidualBounds.genericResidual_lowerBound_iff
        (E := E) δ η hc p hp q z f r |>.mpr
      intro j
      exact NewtonOrderBridge.lowerBound_of_order_or_zero _ r
        (S.variation_lower_orders j)
  exact FiniteNewtonInduction.corrected_stage
    (E := E) δ η hc p hp q z f b r S.finite_support S.symbol_lower_bound
    S.target_above_symbol hr S.Ψ S.residual_coefficient
    (leading_polynomial_ne_zero S) (leading_polynomial_nonunit S)

end Stage

end

end MakarLimanov.NewtonStageSpec
