import MakarLimanov.InitialNewton
import MakarLimanov.FiniteNewtonInduction
import MakarLimanov.FiniteNewtonApproximation
import MakarLimanov.ResidualPolynomial

/-!
# Axiom-free interfaces for finite Newton stages

This file records the two pieces of a finite Newton run which can be assembled
without any global approximation axiom: the initial zero stage, and one genuine
correction whenever a positive variation coefficient is active.  The latter
uses the homogeneous decomposition of the residual coefficient to construct
the nonzero nonunit polynomial required by the certified Newton step.
-/

noncomputable section

namespace MakarLimanov.FiniteNewtonRun

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets JetPolynomialCoefficients JetSpecialization
open VariationCoefficients

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [CharZero k] [CharZero F] [CharZero E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]

/-- The initial stage of a Newton run is constructive.  In particular, the
zero Laurent series has finite support and the initial residual has no negative
coefficient when the binary abelianization of `g` vanishes. -/
theorem initial_newton_stage
    (g : FreeAlgebra k Bool) (hg : binaryAbelianize k g = 0)
    (p : ℕ) (hp : 0 < p)
    (δ η : Derivation k F F) (hc : Function.Commute δ η) :
    (0 : LaurentSeries F).support.Finite ∧
      LowerBound 0 (0 : LaurentSeries F) ∧
      LowerBound 0
        (toSeries (evaluateAt (hp := hp) (h := hc)
          (0 : LaurentSeries F) (1 + g))) :=
  InitialNewton.initial_stage_data g hg p hp δ η hc

/-- A single certified Newton correction, with no use of the finite Newton
approximation axiom.  An active positive-degree generic variation supplies a
polynomial representative of the residual coefficient; its homogeneous
decomposition proves that representative is nonzero and nonunit, so the
kernel-checked `corrected_stage` theorem applies. -/
theorem one_step_from_active_variation
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (b r : ℤ)
    (hz : z.support.Finite) (hb : LowerBound b z) (hq : b ≤ q)
    (hr : LowerBound r
      (NewtonResidual.genericResidual (E := E) δ η hc p hp q z f))
    (hactive : ∃ j : ℕ, 0 < j ∧
      (genericVariation (E := E) δ η hc p hp q z f j).coeff r ≠ 0) :
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
  obtain ⟨P, hP0, hPnu, hP⟩ :=
    ResidualPolynomial.exists_nonunit_residual_coefficient_representative
      (E := E) δ η hc p hp q z f r hactive
  exact FiniteNewtonInduction.corrected_stage
    (E := E) δ η hc p hp q z f b r hz hb hq hr P hP hP0 hPnu

/-- Once the stage relation has been assembled, its endpoint theorem gives the
finite approximation uniformly in the requested precision.  This is the
axiom-free replacement interface for the former global approximation axiom:
the remaining obligation is exactly the construction of the `AssembledApproximation`
data, whose `run.step` can use `one_step_from_active_variation`. -/
theorem finite_approximation_of_assembled_runs
    {K : Type u} [Field K] (g : FreeAlgebra K Bool) (A : ℕ)
    (hRuns : ∀ T : ℕ,
      FiniteNewtonApproximation.AssembledApproximation g A T) :
    ∀ T : ℕ, 0 < T →
      Nonempty (AuditedAssumptions.SymbolApproximation K g A T) := by
  intro T hT
  exact (hRuns T).endpoint

end MakarLimanov.FiniteNewtonRun
