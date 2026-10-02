import MakarLimanov.VariationCoefficients
import MakarLimanov.GenericTwist

/-!
# Faithfulness of generic variation coefficients

The generic variation lives in the fraction field of the finite jet
polynomial ring.  A compatible differential specialization can therefore
preserve a nonzero coefficient whenever its jet evaluation is injective.  The
same observation, together with the lower-bound preservation theorem, gives
exact preservation of the Laurent order.
-/

namespace MakarLimanov.VariationFaithful

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open VariationCoefficients

noncomputable section

universe u

variable {k F E G : Type u} [Field k] [Field F] [Field E] [Field G]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [Algebra k G] [Algebra F G] [IsScalarTower k F G]
  [CharZero F] [CharZero E] [CharZero G]

abbrev TwistBase (F : Type u) [Field F] := FractionRing (MvPolynomial Unit F)

abbrev TwistField (F : Type u) [Field F] :=
  FractionRing (MvPolynomial (ℕ × ℕ) (TwistBase F))

/-- A nonzero generic variation coefficient remains nonzero after any
compatible specialization whose mixed-jet evaluation is injective. -/
theorem specialized_variation_coeff_ne_zero_of_injective
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) (n : ℤ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G)
    (hEval : Function.Injective (fun P : MvPolynomial (ℕ × ℕ) F ↦
      MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P))
    (hcoef : (genericVariation (E := E) δ η hc p hp q z f j).coeff n ≠ 0) :
    (SymbolVariations.variation (hp := hp) (h := hDH) f
      (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w) j).coeff n ≠ 0 := by
  obtain ⟨P, hP, hspecial⟩ := exists_universal_variation_coefficient
    (E := E) (G := G) δ η hc p hp q z f j n
  have hP0 : P ≠ 0 := by
    intro hzero
    apply hcoef
    rw [← hP, hzero, map_zero]
  have hjet : MvPolynomial.aeval
      (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0 := by
    intro hz
    apply hP0
    apply hEval
    change MvPolynomial.aeval
      (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P =
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) 0
    simpa [hz]
  rw [← hspecial D H hDH hD hH w]
  exact hjet

/-- Compatible injective specialization preserves the exact Laurent order of
a nonzero generic variation. -/
theorem specialized_variation_order_eq_of_injective
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G)
    (hEval : Function.Injective (fun P : MvPolynomial (ℕ × ℕ) F ↦
      MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P))
    (hV : genericVariation (E := E) δ η hc p hp q z f j ≠ 0) :
    (SymbolVariations.variation (hp := hp) (h := hDH) f
      (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w) j).order =
      (genericVariation (E := E) δ η hc p hp q z f j).order := by
  let V := genericVariation (E := E) δ η hc p hp q z f j
  let SV := SymbolVariations.variation (hp := hp) (h := hDH) f
    (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w) j
  let r : ℤ := V.order
  have hVcoeff : V.coeff r ≠ 0 := by
    dsimp [r]
    exact (HahnSeries.coeff_order_eq_zero.not).mpr hV
  have hScoeff : SV.coeff r ≠ 0 := by
    dsimp [SV, V] at hVcoeff ⊢
    exact specialized_variation_coeff_ne_zero_of_injective
      δ η hc p hp q z f j r D H hDH hD hH w hEval hVcoeff
  have hSV : SV ≠ 0 := by
    intro hzero
    apply hScoeff
    rw [hzero, coeff_zero]
  have hSVle : SV.order ≤ r := HahnSeries.order_le_of_coeff_ne_zero hScoeff
  have hlowV : LowerBound r V := by
    dsimp [r]
    exact lowerBound_order V
  have hlowSV : LowerBound r SV := by
    dsimp [SV, V] at hlowV ⊢
    rw [← specialize_genericVariation (E := E) (G := G) δ η hc p hp q z
      D H hDH hD hH w f j]
    exact SymbolSpecialization.lowerBound _ _ _ hlowV
  have hleSV : r ≤ SV.order := by
    exact (HahnSeries.le_order_iff_forall hSV).mpr hlowSV
  simpa [SV, V] using le_antisymm hSVle hleSV

/-- The generic-twist form of the preceding theorem: it is enough to know
that every nonzero jet polynomial has nonzero value at the chosen generic
element. -/
theorem specialized_variation_order_eq_of_generic
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G)
    (hGeneric : ∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0)
    (hV : genericVariation (E := E) δ η hc p hp q z f j ≠ 0) :
    (SymbolVariations.variation (hp := hp) (h := hDH) f
      (mapField (IsScalarTower.toAlgHom k F G) z) (HahnSeries.single q w) j).order =
      (genericVariation (E := E) δ η hc p hp q z f j).order := by
  apply specialized_variation_order_eq_of_injective
    δ η hc p hp q z f j D H hDH hD hH w ?_ hV
  intro P Q hPQ
  change MvPolynomial.aeval
      (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P =
    MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) Q at hPQ
  by_contra hne
  have hdiff : P - Q ≠ 0 := by
    intro hz
    apply hne
    exact sub_eq_zero.mp hz
  have hv := hGeneric (P - Q) hdiff
  apply hv
  rw [map_sub, hPQ, sub_self]

/-- The rational generic twist gives a concrete exact order-covariance
interface on its final differential field. -/
theorem rational_twist_variation_order
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (f : FreeAlgebra k Bool) :
    ∃ (D H : Derivation k (TwistField F) (TwistField F))
      (e : TwistBase F) (w : TwistField F),
      ∃ hDH : Function.Commute D H,
      e ≠ 0 ∧
      D (algebraMap (TwistBase F) (TwistField F) e) = 0 ∧
      H (algebraMap (TwistBase F) (TwistField F) e) =
        (p : TwistField F)⁻¹ * (q : TwistField F) *
          algebraMap (TwistBase F) (TwistField F) e ∧
      ∀ (z v : LaurentSeries (TwistField F)) (n : ℕ),
        SymbolVariations.variation (δ := D) (η := H) (hp := hp) (h := hDH)
            f z v n ≠ 0 →
          (SymbolVariations.variation (δ := D) (η := H) (hp := hp) (h := hDH)
            f z (HahnSeries.single q
              (algebraMap (TwistBase F) (TwistField F) e) * v) n).order =
            (n : ℤ) * q +
              (SymbolVariations.variation (δ := D) (η := H) (hp := hp) (h := hDH)
                f z v n).order := by
  obtain ⟨D, H, e, w, he, hDH, hD, hH, hroot, hw, hew⟩ :=
    GenericTwist.rational_twist_generic_extension δ η hc p q
  refine ⟨D, H, e, w, hDH, he, hroot, hw, ?_⟩
  have he' : algebraMap (TwistBase F) (TwistField F) e ≠ 0 := by
    intro hz
    apply he
    apply (algebraMap (TwistBase F) (TwistField F)).injective
    simpa using hz
  intro z v n hvar
  exact SymbolVariations.monomial_order f z v
    (algebraMap (TwistBase F) (TwistField F) e) he' q hroot hw n hvar


end

end MakarLimanov.VariationFaithful
