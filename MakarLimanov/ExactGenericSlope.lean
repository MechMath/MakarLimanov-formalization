import MakarLimanov.GenericVariationSlope

/-!
# Exact slope covariance of the universal variations

This is the same-lattice part of equation (3.5) in Lemma 6 of `proof.pdf`.
Faithfulness at both the generic element and its eigenvector twist transfers
the central-monomial identity back to the two universal jet evaluations.
-/

namespace MakarLimanov.ExactGenericSlope

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetSpecialization VariationCoefficients

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

/-- A differentially generic specialization reflects vanishing of each
universal variation. -/
theorem specialized_variation_eq_zero_iff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ)
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G)
    (hGeneric : ∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
      MvPolynomial.aeval
        (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0) :
    SymbolVariations.variation (hp := hp) (h := hDH) f
        (mapField (IsScalarTower.toAlgHom k F G) z) (single q w) j = 0 ↔
      genericVariation (E := E) δ η hc p hp q z f j = 0 := by
  constructor
  · intro hzero
    ext n
    obtain ⟨P, hP, hs⟩ := exists_universal_variation_coefficient
      (E := E) (G := G) δ η hc p hp q z f j n
    have hPzero : P = 0 := by
      by_contra hPne
      apply hGeneric P hPne
      rw [hs D H hDH hD hH w, hzero, coeff_zero]
    rw [← hP, hPzero, map_zero, coeff_zero]
  · intro hzero
    have hs := specialize_genericVariation (E := E) (G := G)
      δ η hc p hp q z D H hDH hD hH w f j
    simpa only [hzero, SymbolSpecialization.specialize_zero] using hs.symm

private theorem generic_over_subfield
    {L G : Type u} [Field L] [Field G] [Algebra F L] [Algebra L G]
    [Algebra F G] [IsScalarTower F L G]
    (v : ℕ × ℕ → G)
    (hv : ∀ P : MvPolynomial (ℕ × ℕ) L, P ≠ 0 → MvPolynomial.aeval v P ≠ 0) :
    ∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 → MvPolynomial.aeval v P ≠ 0 := by
  intro P hP
  let PL : MvPolynomial (ℕ × ℕ) L := MvPolynomial.map (algebraMap F L) P
  have hPL : PL ≠ 0 := by
    intro hz
    apply hP
    exact (MvPolynomial.map_injective (algebraMap F L)
      (algebraMap F L).injective) (by simpa [PL] using hz)
  have hval := hv PL hPL
  intro hz
  apply hval
  change MvPolynomial.aeval v PL = 0
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [← IsScalarTower.algebraMap_eq F L G]
  exact hz

set_option maxHeartbeats 1000000 in
/-- Changing the integer numerator of a slope preserves the active variations
and changes their lower Laurent index by exactly `j*q`. -/
theorem genericVariation_slope
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (j : ℕ) :
    (genericVariation (E := E) δ η hc p hp q z f j = 0 ↔
      genericVariation (E := E) δ η hc p hp 0 z f j = 0) ∧
    (genericVariation (E := E) δ η hc p hp 0 z f j ≠ 0 →
      (genericVariation (E := E) δ η hc p hp q z f j).order =
        (j : ℤ) * q + (genericVariation (E := E) δ η hc p hp 0 z f j).order) := by
  let L := VariationFaithful.TwistBase F
  let K := VariationFaithful.TwistField F
  obtain ⟨D, H, e, w, he, hDH, hD, hH, heδ, heη, hw, hew⟩ :=
    GenericTwist.rational_twist_generic_extension δ η hc p q
  have hwF := generic_over_subfield (F := F)
    (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) hw
  have hewF := generic_over_subfield (F := F)
    (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] (algebraMap L K e * w))) hew
  have heK : algebraMap L K e ≠ 0 := by
    intro hz
    apply he
    exact (algebraMap L K).injective (by simpa using hz)
  have hz0 := specialized_variation_eq_zero_iff (E := E) (G := K)
    δ η hc p hp 0 z f j D H hDH hD hH w hwF
  have hzq := specialized_variation_eq_zero_iff (E := E) (G := K)
    δ η hc p hp q z f j D H hDH hD hH (algebraMap L K e * w) hewF
  have hmul := SymbolVariations.monomial_mul
    (δ := D) (η := H) (p := p) (hp := hp) (h := hDH)
    f (mapField (IsScalarTower.toAlgHom k F K) z)
    (single 0 w) (algebraMap L K e) q heδ heη j
  simp only [single_mul_single, add_zero] at hmul
  have hzero : genericVariation (E := E) δ η hc p hp q z f j = 0 ↔
      genericVariation (E := E) δ η hc p hp 0 z f j = 0 := by
    rw [← hzq, hmul, mul_eq_zero,
      or_iff_right (single_ne_zero (pow_ne_zero j heK)), hz0]
  refine ⟨hzero, ?_⟩
  intro hV0
  have hVq : genericVariation (E := E) δ η hc p hp q z f j ≠ 0 :=
    fun hz ↦ hV0 (hzero.mp hz)
  have horder0 := VariationFaithful.specialized_variation_order_eq_of_generic
    (E := E) (G := K) δ η hc p hp 0 z f j D H hDH hD hH w hwF hV0
  have horderq := VariationFaithful.specialized_variation_order_eq_of_generic
    (E := E) (G := K) δ η hc p hp q z f j D H hDH hD hH
    (algebraMap L K e * w) hewF hVq
  rw [← horderq, hmul]
  rw [order_single_mul_of_isRegular
    (IsRegular.of_ne_zero (pow_ne_zero j heK)) (fun hz ↦ hV0 (hz0.mp hz))]
  rw [horder0]

end

end MakarLimanov.ExactGenericSlope
