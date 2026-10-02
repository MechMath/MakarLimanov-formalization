import MakarLimanov.NewtonResidual
import MakarLimanov.NewtonTranslation
import MakarLimanov.ResidualPolynomial

/-!
# Translation of a generic residual after a Newton correction

Adding an actual correction and then a new generic correction at the same
slope translates the old residual coefficient polynomial by the mixed jets
of the actual correction.
-/

noncomputable section

namespace MakarLimanov.GenericResidualTranslation

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets NewtonResidual

universe u

private theorem iterate_add {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (n : ℕ) (x y : R) :
    D^[n] (x + y) = D^[n] x + D^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

variable {k F E G K : Type u} [Field k] [Field F] [Field E] [Field G] [Field K]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [Algebra k G] [Algebra F G] [IsScalarTower k F G]
  [Algebra k K] [Algebra F K] [Algebra G K]
  [IsScalarTower k G K] [IsScalarTower F G K] [IsScalarTower k F K]
  [Algebra (MvPolynomial (ℕ × ℕ) G) K]
  [IsScalarTower G (MvPolynomial (ℕ × ℕ) G) K]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) G) K]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) G) K]
  [CharZero F] [CharZero E] [CharZero G] [CharZero K]

private theorem iterate_base_delta (D : Derivation k G G) (n : ℕ) (a : G) :
    (GenericJets.delta (E := K) D)^[n] (algebraMap G K a) =
      algebraMap G K (D^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, delta_base]

private theorem iterate_base_eta (H : Derivation k G G) (n : ℕ) (a : G) :
    (GenericJets.eta (E := K) H)^[n] (algebraMap G K a) =
      algebraMap G K (H^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, eta_base]

private theorem mixed_translate (D H : Derivation k G G) (w : G) (i j : ℕ) :
    (GenericJets.delta (E := K) D)^[i]
        ((GenericJets.eta (E := K) H)^[j]
          (algebraMap G K w + jet (F := G) 0 0)) =
      algebraMap G K (D^[i] (H^[j] w)) + jet (F := G) i j := by
  rw [iterate_add, iterate_add, iterate_base_eta, iterate_base_delta, mixed_jet]

private theorem map_translated_polynomial (v : ℕ × ℕ → G)
    (P : MvPolynomial (ℕ × ℕ) F) :
    algebraMap (MvPolynomial (ℕ × ℕ) G) K
        (NewtonTranslation.translate v (MvPolynomial.map (algebraMap F G) P)) =
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ algebraMap G K (v ij) + jet (F := G) ij.1 ij.2) P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, NewtonTranslation.translate_C, MvPolynomial.aeval_C]
    change algebraMap (MvPolynomial (ℕ × ℕ) G) K
      (algebraMap G (MvPolynomial (ℕ × ℕ) G) (algebraMap F G a)) = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P ij hP =>
    simp only [map_mul, MvPolynomial.map_X, NewtonTranslation.translate_X, map_add,
      MvPolynomial.aeval_X, hP]
    congr 2
    change algebraMap (MvPolynomial (ℕ × ℕ) G) K
      (algebraMap G (MvPolynomial (ℕ × ℕ) G) (v ij)) = algebraMap G K (v ij)
    exact (IsScalarTower.algebraMap_apply G (MvPolynomial (ℕ × ℕ) G) K _).symm

/-- The translated old coefficient polynomial represents the residual after
an actual correction and a fresh generic correction at the same slope. -/
theorem translated_residual_coefficient
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r) :
    algebraMap (MvPolynomial (ℕ × ℕ) G) K
      (NewtonTranslation.translate (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
        (MvPolynomial.map (algebraMap F G) P)) =
      (genericResidual (E := K) D H hDH p hp q
        (mapField (IsScalarTower.toAlgHom k F G) z + single q w) f).coeff r := by
  obtain ⟨Q, hQ, hspec⟩ := exists_universal_residual_coefficient (E := E) (G := K)
    δ η hc p hp q z f r
  have hPQ : P = Q := (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
    (hP.trans hQ.symm)
  have hD' : ∀ a : F, GenericJets.delta (E := K) D (algebraMap F K a) =
      algebraMap F K (δ a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply F G K, delta_base, hD,
      ← IsScalarTower.algebraMap_apply]
  have hH' : ∀ a : F, GenericJets.eta (E := K) H (algebraMap F K a) =
      algebraMap F K (η a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply F G K, eta_base, hH,
      ← IsScalarTower.algebraMap_apply]
  have hvalue := hspec (GenericJets.delta (E := K) D) (GenericJets.eta (E := K) H)
    (GenericJets.commute D H hDH) hD' hH'
    (algebraMap G K w + jet (F := G) 0 0)
  rw [← hPQ] at hvalue
  simp only [mixed_translate] at hvalue
  rw [map_translated_polynomial]
  rw [hvalue]
  have hmaps : mapField (IsScalarTower.toAlgHom k G K)
      (mapField (IsScalarTower.toAlgHom k F G) z) =
      mapField (IsScalarTower.toAlgHom k F K) z := by
    ext n
    simp only [mapField_coeff, IsScalarTower.toAlgHom_apply]
    rw [← IsScalarTower.algebraMap_apply]
  have hsymbols : mapField (IsScalarTower.toAlgHom k F K) z +
      single q (algebraMap G K w + jet (F := G) 0 0) =
      genericCorrectedSymbol (k := k) (E := K)
        (mapField (IsScalarTower.toAlgHom k F G) z + single q w) q := by
    rw [genericCorrectedSymbol, mapField_add, mapField_single, hmaps, single_add]
    simp only [IsScalarTower.toAlgHom_apply, add_assoc]
  rw [hsymbols]
  rfl

/-- A lower support bound for the old generic residual is preserved after
translating its coefficients by an actual differential correction. This is
the all-coefficients form needed to choose the next supporting slope. -/
theorem translated_residual_lowerBound
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) :
    LowerBound r (genericResidual (E := K) D H hDH p hp q
      (mapField (IsScalarTower.toAlgHom k F G) z + single q w) f) := by
  intro n hn
  obtain ⟨P, hP, _⟩ := ResidualPolynomial.exists_residual_coefficient_representative
    (E := E) δ η hc p hp q z f n
  have hPzero : P = 0 := by
    apply (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E)
    rw [hP, hr n hn, map_zero]
  have htranslated := translated_residual_coefficient (E := E) (K := K)
    δ η hc p hp q z f n D H hDH hD hH w P hP
  have htranslated0 : (algebraMap (MvPolynomial (ℕ × ℕ) G) K)
      (NewtonTranslation.translate (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
        (MvPolynomial.map (algebraMap F G) P)) =
      (genericResidual (E := K) D H hDH p hp q
        (mapField (IsScalarTower.toAlgHom k F G) z + single q w) f).coeff n := by
    simpa [hPzero, NewtonTranslation.translate] using htranslated
  rw [hPzero, map_zero, NewtonTranslation.translate, map_zero] at htranslated0
  simpa only [map_zero] using htranslated0.symm

/-- Homogeneous components of the translated polynomial are exactly the
variation coefficients around the corrected symbol. -/
theorem translated_homogeneousComponent_map
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r) (j : ℕ) :
    algebraMap (MvPolynomial (ℕ × ℕ) G) K
      (MvPolynomial.homogeneousComponent j
        (NewtonTranslation.translate (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
          (MvPolynomial.map (algebraMap F G) P))) =
      (VariationCoefficients.genericVariation (E := K) D H hDH p hp q
        (mapField (IsScalarTower.toAlgHom k F G) z + single q w) f j).coeff r := by
  exact ResidualPolynomial.homogeneousComponent_map D H hDH p hp q _ f r _
    (translated_residual_coefficient (E := E) (K := K)
      δ η hc p hp q z f r D H hDH hD hH w P hP) j

/-- The multiplicity of the selected factor becomes the first nonzero
variation coefficient at the old residual order after correction. -/
theorem corrected_variation_coefficients_of_translation
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r) (m : ℕ)
    (hlow : ∀ j < m, MvPolynomial.homogeneousComponent j
      (NewtonTranslation.translate (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
        (MvPolynomial.map (algebraMap F G) P)) = 0)
    (htop : MvPolynomial.homogeneousComponent m
      (NewtonTranslation.translate (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
        (MvPolynomial.map (algebraMap F G) P)) ≠ 0) :
    (∀ j < m, (VariationCoefficients.genericVariation (E := K) D H hDH p hp q
      (mapField (IsScalarTower.toAlgHom k F G) z + single q w) f j).coeff r = 0) ∧
    (VariationCoefficients.genericVariation (E := K) D H hDH p hp q
      (mapField (IsScalarTower.toAlgHom k F G) z + single q w) f m).coeff r ≠ 0 := by
  constructor
  · intro j hj
    rw [← translated_homogeneousComponent_map (E := E) (K := K)
      δ η hc p hp q z f r D H hDH hD hH w P hP j, hlow j hj, map_zero]
  · rw [← translated_homogeneousComponent_map (E := E) (K := K)
      δ η hc p hp q z f r D H hDH hD hH w P hP m]
    exact fun hz ↦ htop ((IsFractionRing.injective (MvPolynomial (ℕ × ℕ) G) K)
      (hz.trans (map_zero _).symm))

end MakarLimanov.GenericResidualTranslation
