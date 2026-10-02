import MakarLimanov.VariationFaithful

/-!
# Exact slope covariance for generic variations

This theorem isolates the exact algebraic bridge used by the Newton slope
argument. A compatible generic differential specialization preserves the order
of the universal variation, and an eigenvector monomial shifts that order by
precisely `j*q`.
-/

namespace MakarLimanov.GenericVariationSlope

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetSpecialization VariationCoefficients
open VariationFaithful

noncomputable section

universe u

abbrev JetField (F : Type u) [Field F] := FractionRing (MvPolynomial (ℕ × ℕ) F)

variable {k F G : Type u} [Field k] [Field F] [Field G]
  [Algebra k F] [Algebra k G] [Algebra F G] [IsScalarTower k F G]
  [CharZero F] [CharZero G]

set_option maxHeartbeats 800000 in
theorem generic_variation_order_of_twist
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (j : ℕ)
    (D H : Derivation k G G) (e w : G)
    (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (he : e ≠ 0)
    (heδ : D e = 0)
    (heη : H e = (p : G)⁻¹ * (q : G) * e)
    (hGeneric : ∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0)
    (hV : genericVariation (E := JetField F) δ η hc p hp 0 z f j ≠ 0) :
    (SymbolVariations.variation (δ := D) (η := H) (hp := hp) (h := hDH)
      f (mapField (IsScalarTower.toAlgHom k F G) z)
      (HahnSeries.single q e * HahnSeries.single 0 w) j).order =
      (j : ℤ) * q +
        (genericVariation (E := JetField F) δ η hc p hp 0 z f j).order := by
  have horder := VariationFaithful.specialized_variation_order_eq_of_generic
    (E := JetField F) (G := G) δ η hc p hp 0 z f j D H hDH hD hH w
    hGeneric hV
  have hEval : Function.Injective (fun P : MvPolynomial (ℕ × ℕ) F ↦
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P) := by
    intro P Q hPQ
    change MvPolynomial.aeval
      (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P =
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) Q at hPQ
    by_contra hne
    have hdiff : P - Q ≠ 0 := by
      intro hz
      apply hne
      exact sub_eq_zero.mp hz
    have hv := hGeneric (P - Q) hdiff
    apply hv
    rw [map_sub, hPQ, sub_self]
  have hbase :
      SymbolVariations.variation (δ := D) (η := H) (hp := hp) (h := hDH)
        f (mapField (IsScalarTower.toAlgHom k F G) z)
        (HahnSeries.single 0 w) j ≠ 0 := by
    let r := (genericVariation (E := JetField F) δ η hc p hp 0 z f j).order
    have hr : (genericVariation (E := JetField F) δ η hc p hp 0 z f j).coeff r ≠ 0 := by
      dsimp [r]
      exact (HahnSeries.coeff_order_eq_zero.not).mpr hV
    have hcoeff := VariationFaithful.specialized_variation_coeff_ne_zero_of_injective
      (E := JetField F) (G := G) δ η hc p hp 0 z f j r D H hDH hD hH w hEval hr
    intro hz
    apply hcoeff
    rw [hz, coeff_zero]
  have hshift := SymbolVariations.monomial_order
    (δ := D) (η := H) (p := p) (hp := hp) (h := hDH) f
    (mapField (IsScalarTower.toAlgHom k F G) z)
    (HahnSeries.single 0 w) e he q heδ heη j ?_
  · rw [hshift, horder]
  · exact hbase

set_option maxHeartbeats 800000 in
theorem rational_twist_generic_variation_order
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (j : ℕ)
    (hV : genericVariation (E := JetField F) δ η hc p hp 0 z f j ≠ 0) :
    ∃ (D H : Derivation k (VariationFaithful.TwistField F)
        (VariationFaithful.TwistField F))
      (e : VariationFaithful.TwistBase F) (w : VariationFaithful.TwistField F),
      ∃ hDH : Function.Commute D H,
      e ≠ 0 ∧
      (∀ a : F, D (algebraMap F (VariationFaithful.TwistField F) a) =
        algebraMap F (VariationFaithful.TwistField F) (δ a)) ∧
      (∀ a : F, H (algebraMap F (VariationFaithful.TwistField F) a) =
        algebraMap F (VariationFaithful.TwistField F) (η a)) ∧
      (SymbolVariations.variation (δ := D) (η := H) (hp := hp) (h := hDH)
        f (mapField (IsScalarTower.toAlgHom k F (VariationFaithful.TwistField F)) z)
        (HahnSeries.single q
          (algebraMap (VariationFaithful.TwistBase F)
            (VariationFaithful.TwistField F) e) *
          HahnSeries.single 0 w) j).order =
        (j : ℤ) * q +
          (genericVariation (E := JetField F) δ η hc p hp 0 z f j).order := by
  obtain ⟨D, H, e, w, he, hDH, hD, hH, heδ, heη, hw, _hew⟩ :=
    GenericTwist.rational_twist_generic_extension δ η hc p q
  let L := VariationFaithful.TwistBase F
  let E := VariationFaithful.TwistField F
  have hGeneric : ∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0 := by
    intro P hP
    let PL : MvPolynomial (ℕ × ℕ) L := MvPolynomial.map (algebraMap F L) P
    have hPL : PL ≠ 0 := by
      intro hz
      apply hP
      exact (MvPolynomial.map_injective (algebraMap F L)
        (algebraMap F L).injective) hz
    have hPLval := hw PL hPL
    intro hz
    apply hPLval
    change MvPolynomial.aeval
      (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) PL = 0
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    rw [← IsScalarTower.algebraMap_eq F L E]
    exact hz
  have hresult := generic_variation_order_of_twist
    (G := E) δ η hc p hp q z f j D H
    (algebraMap L E e) w hDH hD hH
    (by
      intro hz
      apply he
      exact (algebraMap L E).injective (by simpa using hz))
    heδ heη hGeneric hV
  refine ⟨D, H, e, w, hDH, he, hD, hH, ?_⟩
  exact hresult

end

end MakarLimanov.GenericVariationSlope
