import MakarLimanov.InitialSlopeData
import MakarLimanov.LeadingSlope

/-!
# From a concrete separating symbol to finite Newton approximations

A single nonzero evaluation of the commutator polynomial supplies the positive
generic variation needed to initialize the fully proved Newton iteration.
-/

noncomputable section

namespace MakarLimanov.InitialSeparationApproximation

open SymbolSeries SymbolSeries.StarSeries

universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  [CharZero K] [CharZero F]

/-- A nonzero concrete value at an integral coefficient symbol initializes
the generic positive-degree variation of `1 + g`. -/
theorem positive_variation_of_value
    (g : FreeAlgebra K Bool) (hab : binaryAbelianize K g = 0)
    (D H : Derivation K F F) (hDH : Function.Commute D H) (w : F)
    (hvalue : toSeries (evaluateAt (hp := (by decide : 0 < 1))
      (h := hDH) (HahnSeries.single 0 w) g) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧
      VariationCoefficients.genericVariation
        (E := FractionRing (MvPolynomial (ℕ × ℕ) K))
        (0 : Derivation K K K) 0 (fun _ ↦ rfl) 1 (by decide) 0 0 (1 + g) j ≠ 0 := by
  obtain ⟨j, hj, _, hcoeff⟩ := LeadingSlope.exists_positive_generic_variation
    (0 : Derivation K K K) 0 (fun _ ↦ rfl) 1 (by decide) 0
    D H hDH
    (fun a ↦ by simp) (fun a ↦ by simp) w g (by
      rw [InitialNewton.lift_zero_true_of_binaryAbelianize_zero g hab]
      exact HahnSeries.coeff_zero) hvalue
  refine ⟨j, hj, ?_⟩
  have hV := HahnSeries.ne_zero_of_coeff_ne_zero hcoeff
  have heq : VariationCoefficients.genericVariation
      (E := FractionRing (MvPolynomial (ℕ × ℕ) K))
      (0 : Derivation K K K) 0 (fun _ ↦ rfl) 1 (by decide) 0 0 (1 + g) j =
      SymbolVariations.variation (hp := (by decide : 0 < 1))
        (h := GenericJets.commute (0 : Derivation K K K) 0 (fun _ ↦ rfl)) g
        (0 : LaurentSeries (FractionRing (MvPolynomial (ℕ × ℕ) K)))
        (HahnSeries.single 0 (GenericJets.jet (F := K)
          (E := FractionRing (MvPolynomial (ℕ × ℕ) K)) 0 0)) j := by
    simp [VariationCoefficients.genericVariation, SymbolVariations.variation,
      Variations.variation, Polynomial.coeff_one, hj.ne', StarSeries.toSeries]
  rw [heq]
  exact hV

/-- Concrete separation is sufficient for the original finite Newton output;
the support bound is chosen once and works for every target precision. -/
theorem finite_newton_approximation_of_value
    (g : FreeAlgebra K Bool) (hg : g ≠ 0) (hab : binaryAbelianize K g = 0)
    (D H : Derivation K F F) (hDH : Function.Commute D H) (w : F)
    (hvalue : toSeries (evaluateAt (hp := (by decide : 0 < 1))
      (h := hDH) (HahnSeries.single 0 w) g) ≠ 0) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ T : ℕ, 0 < T →
      Nonempty (AuditedAssumptions.SymbolApproximation K g A T) :=
  InitialSlopeData.finite_newton_approximation_of_generic_variation g hg hab
    (positive_variation_of_value g hab D H hDH w hvalue)

end MakarLimanov.InitialSeparationApproximation
