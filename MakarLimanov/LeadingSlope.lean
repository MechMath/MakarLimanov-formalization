import MakarLimanov.GenericResidualHomogeneous
import MakarLimanov.InitialResidual
import MakarLimanov.InitialNewton
import MakarLimanov.SeparationBridge

/-!
# A positive active variation at the initial symbol

The generic residual at the zero symbol has no order-zero variation in the
binary commutator branch.  Consequently any nonzero compatible evaluation of
the free polynomial produces a genuinely positive variation coefficient.  This
is the algebraic starting point for the first Newton slope.
-/

namespace MakarLimanov.LeadingSlope

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetSpecialization GenericResidualHomogeneous
open SymbolVariations

noncomputable section

universe u

variable {k F G : Type u} [Field k] [Field F] [Field G]
  [Algebra k F] [Algebra k G] [Algebra F G] [IsScalarTower k F G]
  [CharZero F] [CharZero G]

private theorem variation_zero_at_zero
    {p : ℕ} (hp : 0 < p) (δ η : Derivation k F F)
    (hc : Function.Commute δ η) (f : FreeAlgebra k Bool)
    (q : ℤ) :
    SymbolVariations.variation (hp := hp)
      (h := GenericJets.commute δ η hc) f
      (0 : LaurentSeries (FractionRing (MvPolynomial (ℕ × ℕ) F)))
      (HahnSeries.single q (jet (F := F) (E := FractionRing (MvPolynomial (ℕ × ℕ) F)) 0 0)) 0 =
      toSeries (evaluateAt (hp := hp)
        (h := GenericJets.commute δ η hc)
        (0 : LaurentSeries (FractionRing (MvPolynomial (ℕ × ℕ) F))) f) := by
  unfold SymbolVariations.variation
  rw [Variations.variation_zero]
  rfl

/-- The initial residual of `1 + g` has order zero.  This discharges the
order hypothesis used by the first positive-variation step. -/
theorem initial_generic_order_zero
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] [CharZero F]
    (g : FreeAlgebra k Bool) (hg : binaryAbelianize k g = 0)
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hc : Function.Commute δ η) :
    (toSeries (evaluateAt (hp := hp) (h := hc)
      (0 : LaurentSeries F) (1 + g))).order = 0 := by
  rw [InitialNewton.initial_residual g hg p hp δ η hc]
  exact HahnSeries.order_one

theorem initial_one_add_negative_coeff
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] [CharZero F]
    (g : FreeAlgebra k Bool) (hg : binaryAbelianize k g = 0)
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (hc : Function.Commute δ η) {n : ℤ} (hn : n < 0) :
    (toSeries (evaluateAt (hp := hp) (h := hc)
      (0 : LaurentSeries F) (1 + g))).coeff n = 0 := by
  have heq := InitialNewton.initial_residual g hg p hp δ η hc
  rw [heq]
  simp [HahnSeries.coeff_one, hn.ne]

/-! A nonzero compatible differential value yields a positive generic
variation coefficient at the initial symbol.  The index is bounded by the
word degree, and the selected Laurent coefficient is nonzero. -/
set_option maxHeartbeats 800000 in
theorem exists_positive_generic_variation
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (f : FreeAlgebra k Bool)
    (hzero : (toSeries (evaluateAt (hp := hp)
      (h := GenericJets.commute δ η hc)
      (0 : LaurentSeries (FractionRing (MvPolynomial (ℕ × ℕ) F))) f)).coeff
        (toSeries (evaluateAt (hp := hp)
          (h := GenericJets.commute δ η hc)
          (HahnSeries.single q
            (jet (F := F) (E := FractionRing (MvPolynomial (ℕ × ℕ) F)) 0 0)) f)).order = 0)
    (hvalue : toSeries (evaluateAt (hp := hp) (h := hDH)
      (HahnSeries.single q w) f) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ j ≤ ControlledMatrix.wordDegree f ∧
      (SymbolVariations.variation (hp := hp)
        (h := GenericJets.commute δ η hc) f
        (0 : LaurentSeries (FractionRing (MvPolynomial (ℕ × ℕ) F)))
        (HahnSeries.single q
          (jet (F := F) (E := FractionRing (MvPolynomial (ℕ × ℕ) F)) 0 0)) j).coeff
          ((toSeries (evaluateAt (hp := hp)
            (h := GenericJets.commute δ η hc)
            (HahnSeries.single q
              (jet (F := F) (E := FractionRing (MvPolynomial (ℕ × ℕ) F)) 0 0)) f)).order) ≠ 0 := by
  let E := FractionRing (MvPolynomial (ℕ × ℕ) F)
  let U : LaurentSeries E :=
    toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
      (HahnSeries.single q (jet (F := F) (E := E) 0 0)) f)
  have hU : U ≠ 0 := by
    dsimp [U]
    exact SeparationBridge.generic_evaluateAt_ne_zero_of_value
      δ η hc p hp q D H hDH hD hH w f hvalue
  have hcoeff : U.coeff U.order ≠ 0 :=
    (HahnSeries.coeff_order_eq_zero.not).mpr hU
  have hcoeff' :
      (toSeries (evaluateAt (hp := hp) (h := GenericJets.commute δ η hc)
        ((0 : LaurentSeries E) + HahnSeries.single q
          (jet (F := F) (E := E) 0 0)) f)).coeff U.order ≠ 0 := by
    simpa [U] using hcoeff
  obtain ⟨j, hjbound, hjcoeff⟩ :=
    ResidualHomogeneous.exists_nonzero_variation_component_bounded
      (p := p) (hp := hp)
      (δ := GenericJets.delta δ) (η := GenericJets.eta η)
      (h := GenericJets.commute δ η hc) f
      (0 : LaurentSeries E)
      (HahnSeries.single q (jet (F := F) (E := E) 0 0)) U.order hcoeff'
  have hvar0 :
      (SymbolVariations.variation (hp := hp)
        (h := GenericJets.commute δ η hc) f
        (0 : LaurentSeries E)
        (HahnSeries.single q (jet (F := F) (E := E) 0 0)) 0).coeff U.order = 0 := by
    rw [variation_zero_at_zero (p := p) hp δ η hc f q]
    exact hzero
  have hjpos : 0 < j := by
    by_contra hjnot
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos hjnot
    subst j
    rw [hvar0] at hjcoeff
    exact hjcoeff rfl
  exact ⟨j, hjpos, hjbound, hjcoeff⟩


end

end MakarLimanov.LeadingSlope
