import MakarLimanov.NewtonSymbolState
import MakarLimanov.NextSlopeRefinedResidual
import MakarLimanov.RefinedSlopeActive
import MakarLimanov.SlopeDivisibility

/-!
# Admissible slope data for a concrete Newton state

The slope certificate records exactly the hypotheses of a ramified correction.
It keeps the coefficient and degree bounds together so that a supporting-line
construction can be fed to the finite iteration without selecting a new root.
-/

noncomputable section

namespace MakarLimanov.NewtonSymbolState.State

open SymbolSeries SymbolSeries.StarSeries

universe u

variable {K : Type u} [Field K] {g : FreeAlgebra K Bool} {A : ℕ}

/-- A correction exponent and its complete residual and multiplicity bounds. -/
structure SlopeData (S : State g A) where
  e : ℕ
  positive_factor : 0 < e
  q : ℤ
  correction_bound : -((S.p * e) * A : ℤ) ≤ q
  generic_bound : LowerBound ((e : ℤ) * S.r)
    (NewtonResidual.genericResidual
      (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
      S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p positive_factor)
      q (refineLattice e positive_factor S.Z) (1 + g))
  active : ∃ j : ℕ, 0 < j ∧
    (VariationCoefficients.genericVariation
      (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
      S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p positive_factor)
      q (refineLattice e positive_factor S.Z) (1 + g) j).coeff ((e : ℤ) * S.r) ≠ 0
  divisible : ∀ j, (VariationCoefficients.genericVariation
      (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
      S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p positive_factor)
      q (refineLattice e positive_factor S.Z) (1 + g) j).coeff ((e : ℤ) * S.r) ≠ 0 →
    e ∣ j
  degree_bound : ∀ j, (VariationCoefficients.genericVariation
      (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
      S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p positive_factor)
      q (refineLattice e positive_factor S.Z) (1 + g) j).coeff ((e : ℤ) * S.r) ≠ 0 →
    j ≤ S.b

/-- The admissible slope certificate produces the actual root extension and
the correction certificate needed by the following supporting-line step. -/
theorem SlopeData.exists_correction [CharZero K] {S : State g A} (d : SlopeData S)
    (hres : (toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
      S.Z (1 + g))).coeff S.r ≠ 0) :
    ∃ S' : State g A, Nonempty (RefinedCorrection S S' d.e d.q) :=
  exists_refined_correction S d.e d.positive_factor d.q d.correction_bound
    d.generic_bound hres d.active d.divisible d.degree_bound

/-- A correction with nonzero residual supplies all slope data for its next
exact-order state, preserving the fixed support bound and the degree budget. -/
theorem RefinedCorrection.nextSlopeData [CharZero K]
    {S S' : State g A} {e : ℕ} {q : ℤ} (C : RefinedCorrection S S' e q)
    (hq : -(S'.p * A : ℤ) ≤ q)
    (hr : LowerBound ((e : ℤ) * S.r)
      (NewtonResidual.genericResidual
        (E := FractionRing (MvPolynomial (ℕ × ℕ) S.F))
        S.δ S.η S.commute (S.p * e) (Nat.mul_pos S.positive_p C.positive_factor)
        q (refineLattice e C.positive_factor S.Z) (1 + g)))
    (hnew : toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute)
      S'.Z (1 + g)) ≠ 0) : Nonempty (SlopeData S'.exactOrder) := by
  classical
  let E := FractionRing (MvPolynomial (ℕ × ℕ) S'.F)
  let rho : ℤ := S'.exactOrder.r
  obtain ⟨active, s, j, hactive, hj, hjpos, _, hqs, heq, hline, htie⟩ :=
    C.nextSupportingSlope hr hnew
  obtain ⟨d, q', hfactor, hd, hq', hquot⟩ :=
    NextSlopeRefinedResidual.exists_refined_slope_exponent S'.p S'.positive_p s
  have hqbound : -((S'.p * d) * A : ℤ) ≤ q' := by
    have hqQ : -((S'.p : ℚ) * A) ≤ (q : ℚ) := by exact_mod_cast hq
    have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
    have hscaled := mul_le_mul_of_nonneg_left (hqQ.trans hqs.le) hdQ.le
    rw [← hq'] at hscaled
    have hfinal : -((S'.p : ℚ) * d * A) ≤ (q' : ℚ) := by nlinarith
    exact_mod_cast hfinal
  have hbound := NextSlopeRefinedResidual.lowerBound_after_refined_slope
    (E := E) S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g)
    rho s active hactive hline rfl d hd q' hq'
  have hactiveq : ∀ i, i ∈ active ↔ i ≤ ControlledMatrix.wordDegree (1 + g) ∧
      0 < i ∧ VariationCoefficients.genericVariation (E := E)
        S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g) i ≠ 0 := by
    intro i
    have hslope := (ExactGenericSlope.genericVariation_slope
      (E := E) S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g) i).1
    constructor
    · intro hi
      obtain ⟨hdegree, hpos, hnonzero⟩ := (hactive i).mp hi
      exact ⟨hdegree, hpos, fun hz ↦ hnonzero (hslope.mp hz)⟩
    · rintro ⟨hdegree, hpos, hnonzero⟩
      exact (hactive i).mpr ⟨hdegree, hpos, fun hz ↦ hnonzero (hslope.mpr hz)⟩
  have hcoeff := RefinedSlopeActive.coefficient_ne_zero_of_supporting_equality
    (E := E) S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g)
    rho s j ((hactiveq j).mp hj).2.2 heq d hd q' hq'
  have hdegrees := RefinedSlopeActive.active_coefficient_degree_bound
    (E := E) S'.δ S'.η S'.commute S'.p S'.positive_p q S'.Z (1 + g)
    rho s active hactiveq hline S'.b htie d hd q' hq'
  refine ⟨{
    e := d
    positive_factor := hd
    q := q'
    correction_bound := hqbound
    generic_bound := hbound
    active := ⟨j, hjpos, hcoeff⟩
    divisible := ?_
    degree_bound := hdegrees }⟩
  intro i hi
  have hV := HahnSeries.ne_zero_of_coeff_ne_zero hi
  have hVbound := (GenericResidualBounds.genericResidual_lowerBound_iff
    (E := E) S'.δ S'.η S'.commute (S'.p * d) (Nat.mul_pos S'.positive_p hd)
    q' (refineLattice d hd S'.Z) (1 + g) ((d : ℤ) * rho)).mp hbound i
  have horder := (HahnSeries.le_order_iff_forall hV).mpr hVbound
  have hdiv := SlopeDivisibility.refinement_factor_dvd_of_active_coefficient
    (E := E) S'.δ S'.η S'.commute S'.p d S'.positive_p hd q' rho S'.Z
    (1 + g) (s / S'.p) hquot.symm i horder hi
  simpa only [hfactor, RationalSlopeRefinement.refinementFactor] using hdiv

/-- Once one admissible slope has been found, the concrete Newton corrections
reach every finite precision while keeping the same support bound. -/
theorem SlopeData.approximation [CharZero K] {S₀ : State g A} (d₀ : SlopeData S₀)
    (hres₀ : (toSeries (evaluateAt (hp := S₀.positive_p) (h := S₀.commute)
      S₀.Z (1 + g))).coeff S₀.r ≠ 0)
    (hprecision₀ : 0 ≤ S₀.precision) (T : ℕ) :
    Nonempty (AuditedAssumptions.SymbolApproximation K g A T) := by
  classical
  let Inv : State g A → Prop := fun S ↦
    toSeries (evaluateAt (hp := S.positive_p) (h := S.commute) S.Z (1 + g)) = 0 ∨
      Nonempty (SlopeData S) ∧
        (toSeries (evaluateAt (hp := S.positive_p) (h := S.commute)
          S.Z (1 + g))).coeff S.r ≠ 0
  apply approximation_of_nonzero_steps Inv S₀ (Or.inr ⟨⟨d₀⟩, hres₀⟩) hprecision₀ T
  intro S hInv _ hres
  obtain ⟨⟨d⟩, hcoeff⟩ := hInv.resolve_left hres
  obtain ⟨S', ⟨C⟩⟩ := d.exists_correction hcoeff
  by_cases hnew : toSeries (evaluateAt (hp := S'.positive_p) (h := S'.commute)
      S'.Z (1 + g)) = 0
  · exact ⟨S', Or.inl hnew, C.step⟩
  have hq : -(S'.p * A : ℤ) ≤ d.q := by
    simpa only [C.denominator_eq, Nat.cast_mul] using d.correction_bound
  have hnext := C.nextSlopeData hq d.generic_bound hnew
  refine ⟨S'.exactOrder, Or.inr ⟨hnext, ?_⟩, C.step.exactOrder hnew⟩
  exact S'.exactOrder_coefficient_ne_zero hnew

end MakarLimanov.NewtonSymbolState.State
