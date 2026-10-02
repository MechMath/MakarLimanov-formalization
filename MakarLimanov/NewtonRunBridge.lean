import MakarLimanov.GenericNewtonSupport
import MakarLimanov.GenericResidualHomogeneous

/-!
# Finite active-set bridge for Newton stages

The variation expansion has finite support.  Once a finite active set records
which homogeneous degrees are nonzero, order inequalities on that set extend
to all degrees because all other variations vanish.  This is the exact
interface needed by a dependent `RunSpec` step.
-/

namespace MakarLimanov.NewtonRunBridge

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients GenericNewtonSupport GenericResidualHomogeneous
open NewtonResidual

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero k] [CharZero F] [CharZero E]

/-- A finite active set with an order lower bound controls every variation. -/
theorem all_variation_orders_of_finite_active
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (active : Finset ℕ)
    (hzero : ∀ j, j ∉ active →
      genericVariation (E := E) δ η hc p hp q z f j = 0)
    (horder : ∀ j, j ∈ active →
      r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order) :
    ∀ j : ℕ,
      genericVariation (E := E) δ η hc p hp q z f j = 0 ∨
        r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order := by
  intro j
  by_cases hj : j ∈ active
  · exact Or.inr (horder j hj)
  · exact Or.inl (hzero j hj)

/-- The finite active-set order data imply the full generic residual lower
bound. -/
theorem genericResidual_lowerBound_of_finite_active
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (active : Finset ℕ)
    (hzero : ∀ j, j ∉ active →
      genericVariation (E := E) δ η hc p hp q z f j = 0)
    (horder : ∀ j, j ∈ active →
      r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order) :
    LowerBound r (genericResidual (E := E) δ η hc p hp q z f) := by
  apply genericResidual_lowerBound_of_variation_orders
    (E := E) δ η hc p hp q z f r
  exact all_variation_orders_of_finite_active
    (E := E) δ η hc p hp q z f r active hzero horder

/-- The canonical finite active universe is `range (wordDegree f + 1)`;
variations outside it vanish by the word-degree bound. -/
theorem wordDegree_active_orders
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (horder : ∀ j ≤ ControlledMatrix.wordDegree f,
      r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order) :
    ∀ j : ℕ,
      genericVariation (E := E) δ η hc p hp q z f j = 0 ∨
        r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order := by
  intro j
  by_cases hj : j ≤ ControlledMatrix.wordDegree f
  · exact Or.inr (horder j hj)
  · left
    apply GenericResidualHomogeneous.genericResidual_variation_degree_bound
      (E := E) δ η hc p hp q z f j
    exact Nat.lt_of_not_ge hj

/-- Word-degree bounded order data directly imply the full residual lower
bound, without naming an active finite set. -/
theorem genericResidual_lowerBound_of_wordDegree_orders
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (horder : ∀ j ≤ ControlledMatrix.wordDegree f,
      r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order) :
    LowerBound r (genericResidual (E := E) δ η hc p hp q z f) := by
  apply genericResidual_lowerBound_of_variation_orders
    (E := E) δ η hc p hp q z f r
  exact wordDegree_active_orders (E := E) δ η hc p hp q z f r horder

/-- A selected positive variation at the residual order, together with the
word-degree order bounds, is sufficient for one certified correction. -/
theorem corrected_stage_of_wordDegree_orders
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (horder : ∀ j ≤ ControlledMatrix.wordDegree f,
      r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order)
    (j : ℕ) (hj : 0 < j)
    (hjnonzero : genericVariation (E := E) δ η hc p hp q z f j ≠ 0)
    (hjorder : (genericVariation (E := E) δ η hc p hp q z f j).order = r)
    (hjbound : j ≤ ControlledMatrix.wordDegree f) :
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G)
      (_ : Algebra F G) (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  exact corrected_stage_of_supporting_variation
    (E := E) δ η hc p hp q z f b r hz hb hq
    (wordDegree_active_orders (E := E) δ η hc p hp q z f r horder)
    j hj hjnonzero hjorder

/-- A selected active degree at the residual order feeds the certified one-step
Newton construction once the finite active-set lower bound is available. -/
theorem corrected_stage_of_finite_active
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (active : Finset ℕ)
    (hzero : ∀ j, j ∉ active →
      genericVariation (E := E) δ η hc p hp q z f j = 0)
    (horder : ∀ j, j ∈ active →
      r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order)
    (j : ℕ) (hjmem : j ∈ active) (hjpos : 0 < j)
    (hjnonzero : genericVariation (E := E) δ η hc p hp q z f j ≠ 0)
    (hjorder : (genericVariation (E := E) δ η hc p hp q z f j).order = r) :
    ∃ (G : Type u) (_ : Field G) (_ : CharZero G) (_ : Algebra k G)
      (_ : Algebra F G) (_ : IsScalarTower k F G), ∃ (D H : Derivation k G G) (w : G),
      ∃ hDH : Function.Commute D H,
      (∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a)) ∧
      (∀ a : F, H (algebraMap F G a) = algebraMap F G (η a)) ∧
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w).support.Finite ∧
      LowerBound b (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) ∧
      LowerBound (r + 1)
        (toSeries (evaluateAt (hp := hp) (h := hDH)
          (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f)) := by
  have hr := genericResidual_lowerBound_of_finite_active
    (E := E) δ η hc p hp q z f r active hzero horder
  exact corrected_stage_of_supporting_variation
    (E := E) δ η hc p hp q z f b r hz hb hq
    (all_variation_orders_of_finite_active
      (E := E) δ η hc p hp q z f r active hzero horder)
    j hjpos hjnonzero hjorder

end

end MakarLimanov.NewtonRunBridge
