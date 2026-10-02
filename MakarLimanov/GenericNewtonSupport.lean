import MakarLimanov.GenericResidualStage
import MakarLimanov.GenericResidualBounds
import MakarLimanov.NewtonOrderBridge

/-!
# Leading support at a chosen Newton slope

The order identities from the generic slope calculation are converted here into
the `LowerBound` predicates used by the certified Newton root.  This is the
coefficient-level part of Lemma 8: once a supporting variation is selected,
the full residual has the required lower bound and its leading coefficient has
a nonzero positive-degree component.
-/

namespace MakarLimanov.GenericNewtonSupport

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients GenericResidualBounds
open NewtonOrderBridge GenericResidualStage

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero k] [CharZero F] [CharZero E]

theorem lowerBound_of_variation_order
    (r : ℤ) (V : LaurentSeries E)
    (hV : V = 0 ∨ r ≤ V.order) : LowerBound r V := by
  exact lowerBound_of_order_or_zero V r hV

theorem genericResidual_lowerBound_of_variation_orders
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (horders : ∀ j : ℕ,
      genericVariation (E := E) δ η hc p hp q z f j = 0 ∨
        r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order) :
    LowerBound r
      (MakarLimanov.NewtonResidual.genericResidual (E := E) δ η hc p hp q z f) := by
  apply MakarLimanov.GenericResidualBounds.genericResidual_lowerBound_iff
    (E := E) δ η hc p hp q z f r |>.mpr
  intro j
  exact lowerBound_of_variation_order r _ (horders j)

theorem active_coefficient_of_exact_order
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (j : ℕ)
    (hj : 0 < j)
    (hV : genericVariation (E := E) δ η hc p hp q z f j ≠ 0)
    (horder : (genericVariation (E := E) δ η hc p hp q z f j).order = r) :
    (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0 := by
  rw [← horder]
  exact (HahnSeries.coeff_order_eq_zero.not).mpr hV

theorem corrected_stage_of_supporting_variation
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (horders : ∀ j : ℕ,
      genericVariation (E := E) δ η hc p hp q z f j = 0 ∨
        r ≤ (genericVariation (E := E) δ η hc p hp q z f j).order)
    (j : ℕ) (hj : 0 < j)
    (hV : genericVariation (E := E) δ η hc p hp q z f j ≠ 0)
    (horder : (genericVariation (E := E) δ η hc p hp q z f j).order = r) :
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
  have hr := MakarLimanov.GenericNewtonSupport.genericResidual_lowerBound_of_variation_orders
    (E := E) δ η hc p hp q z f r horders
  have hcoeff := active_coefficient_of_exact_order
    (E := E) δ η hc p hp q z f r j hj hV horder
  exact corrected_stage_of_active_variation δ η hc p hp q z f b r hz hb hq hr
    ⟨j, hj, hcoeff⟩

end

end MakarLimanov.GenericNewtonSupport
