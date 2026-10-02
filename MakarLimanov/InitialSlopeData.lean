import MakarLimanov.NewtonSlopeData

/-!
# The first Newton slope certificate

A nonzero positive generic variation at the zero symbol gives a finite
supporting line.  Its rational slope determines an integral correction on a
refined lattice.  Choosing the pole bound after this finite construction is
enough for the iteration.
-/

noncomputable section

namespace MakarLimanov.InitialSlopeData

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients NewtonResidual ControlledMatrix
open NewtonSymbolState NewtonSymbolState.State

universe u

theorem exists_supporting_line (a : ℕ → ℚ) (active : Finset ℕ)
    (hne : active.Nonempty) (hpos : ∀ i ∈ active, 0 < i) :
    ∃ (s : ℚ) (j : ℕ), j ∈ active ∧ 0 < j ∧
      a j + (j : ℚ) * s = 0 ∧
      ∀ i ∈ active, 0 ≤ a i + (i : ℚ) * s := by
  obtain ⟨j, hj, hmax⟩ := active.exists_max_image
    (fun i ↦ -(a i) / (i : ℚ)) hne
  have hjpos := hpos j hj
  have hjQ : (0 : ℚ) < j := by exact_mod_cast hjpos
  refine ⟨-(a j) / j, j, hj, hjpos, ?_, ?_⟩
  · field_simp
    ring
  · intro i hi
    have hiQ : (0 : ℚ) < i := by exact_mod_cast hpos i hi
    have hratio := hmax i hi
    have hprod := (div_le_iff₀ hiQ).mp hratio
    linarith

variable {K : Type u} [Field K] [CharZero K]

omit [CharZero K] in
theorem wordDegree_one_add_le (g : FreeAlgebra K Bool) :
    wordDegree (1 + g) ≤ wordDegree g := by
  classical
  unfold wordDegree
  apply Finset.sup_le
  intro w hw
  have hmap : wordCoefficients (1 + g) = 1 + wordCoefficients g := by
    simp [wordCoefficients]
  rw [hmap] at hw
  rcases Finset.mem_union.mp (Finsupp.support_add hw) with hw | hw
  · have hw1 : w = 1 := by
      by_contra hwne
      have hcoeff : (1 : MonoidAlgebra K (FreeMonoid Bool)) w ≠ 0 :=
        Finsupp.mem_support_iff.mp hw
      exact hcoeff (by simp [MonoidAlgebra.one_def, hwne])
    simp [hw1]
  · exact Finset.le_sup hw

/-- Initial separation supplies every item of the first slope certificate.
The positive pole bound is selected after the supporting slope. -/
theorem exists_initial_slopeData
    (g : FreeAlgebra K Bool) (hg : g ≠ 0) (hab : binaryAbelianize K g = 0)
    (hseparate : ∃ j : ℕ, 0 < j ∧
      genericVariation (E := FractionRing (MvPolynomial (ℕ × ℕ) K))
        (0 : Derivation K K K) 0 (fun _ ↦ rfl) 1 (by decide) 0 0 (1 + g) j ≠ 0) :
    ∃ A : ℕ, 1 ≤ A ∧ Nonempty (SlopeData (State.initial g hg hab A)) := by
  classical
  let E := FractionRing (MvPolynomial (ℕ × ℕ) K)
  let hc : Function.Commute (0 : Derivation K K K) 0 := fun _ ↦ rfl
  let V : ℕ → LaurentSeries E := fun i ↦
    genericVariation (E := E) (0 : Derivation K K K) 0 hc
      1 (by decide) 0 0 (1 + g) i
  let active : Finset ℕ :=
    (Finset.range (wordDegree (1 + g) + 1)).filter
      (fun i ↦ 0 < i ∧ V i ≠ 0)
  have hactive : ∀ i, i ∈ active ↔
      i ≤ wordDegree (1 + g) ∧ 0 < i ∧ V i ≠ 0 := by
    intro i
    simp only [active, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hpos, hV⟩
      exact ⟨by omega, hpos, hV⟩
    · rintro ⟨hi, hpos, hV⟩
      exact ⟨by omega, hpos, hV⟩
  have hnonempty : active.Nonempty := by
    obtain ⟨j, hj, hV⟩ := hseparate
    have hdeg : j ≤ wordDegree (1 + g) := by
      by_contra hnot
      exact hV (GenericResidualHomogeneous.genericResidual_variation_degree_bound
        (E := E) (0 : Derivation K K K) 0 hc 1 (by decide) 0 0 (1 + g) j
        (Nat.lt_of_not_ge hnot))
    exact ⟨j, (hactive j).mpr ⟨hdeg, hj, hV⟩⟩
  obtain ⟨s, j, hj, hjpos, htie, hline⟩ := exists_supporting_line
    (fun i ↦ ((V i).order : ℚ)) active hnonempty
    (fun i hi ↦ ((hactive i).mp hi).2.1)
  obtain ⟨e, q, hfactor, he, hq, hquot⟩ :=
    NextSlopeRefinedResidual.exists_refined_slope_exponent 1 (by decide) s
  have hline' : ∀ i ∈ active,
      (0 : ℚ) ≤ ((V i).order : ℚ) + (i : ℚ) * (s - (0 : ℤ)) := by
    simpa using hline
  have hrho : (0 : ℤ) =
      (toSeries (evaluateAt (hp := (by decide : 0 < 1))
        (δ := (0 : Derivation K K K)) (η := 0) (h := hc)
        (0 : LaurentSeries K) (1 + g))).order := by
    rw [InitialNewton.initial_residual g hab 1 (by decide) 0 0 hc]
    simp
  have hbound := NextSlopeRefinedResidual.lowerBound_after_refined_slope
    (E := E) (0 : Derivation K K K) 0 hc 1 (by decide) 0 0 (1 + g)
    0 s active hactive hline' hrho e he q hq
  have hcoeff := RefinedSlopeActive.coefficient_ne_zero_of_supporting_equality
    (E := E) (0 : Derivation K K K) 0 hc 1 (by decide) 0 0 (1 + g)
    0 s j ((hactive j).mp hj).2.2 (by simpa using htie) e he q hq
  obtain ⟨N, hN⟩ := exists_nat_gt (-s)
  let A : ℕ := N + 1
  have hA : 1 ≤ A := by simp [A]
  have hqbound : -((1 * e) * A : ℤ) ≤ q := by
    have hsA : -(A : ℚ) ≤ s := by
      dsimp [A]
      push_cast
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hsA
      (show (0 : ℚ) ≤ e by positivity)
    rw [← hq] at hscaled
    have hfinal : -((1 : ℚ) * e * A) ≤ (q : ℚ) := by nlinarith
    exact_mod_cast hfinal
  refine ⟨A, hA, ⟨{
    e := e
    positive_factor := he
    q := q
    correction_bound := hqbound
    generic_bound := hbound
    active := ⟨j, hjpos, hcoeff⟩
    divisible := ?_
    degree_bound := ?_ }⟩⟩
  · intro i hi
    have hV := HahnSeries.ne_zero_of_coeff_ne_zero hi
    have hVbound := (GenericResidualBounds.genericResidual_lowerBound_iff
      (E := E) (0 : Derivation K K K) 0 hc (1 * e) (Nat.mul_pos (by decide) he)
      q (refineLattice e he 0) (1 + g) ((e : ℤ) * 0)).mp hbound i
    have horder := (HahnSeries.le_order_iff_forall hV).mpr hVbound
    have hdiv := SlopeDivisibility.refinement_factor_dvd_of_active_coefficient
      (E := E) (0 : Derivation K K K) 0 hc 1 e (by decide) he q 0 0
      (1 + g) (s / 1) hquot.symm i horder hi
    simpa only [hfactor, RationalSlopeRefinement.refinementFactor] using hdiv
  · intro i hi
    have hideg : i ≤ wordDegree (1 + g) := by
      by_contra hnot
      have hzero := GenericResidualHomogeneous.genericResidual_variation_degree_bound
        (E := E) (0 : Derivation K K K) 0 hc (1 * e)
        (Nat.mul_pos (by decide) he) q (refineLattice e he 0) (1 + g) i
        (Nat.lt_of_not_ge hnot)
      have hzero' : genericVariation (E := E) (0 : Derivation K K K) 0 hc
          (1 * e) (Nat.mul_pos (by decide) he) q (refineLattice e he 0) (1 + g) i = 0 :=
        hzero
      exact hi (by change (genericVariation (E := E) (0 : Derivation K K K) 0 hc
          (1 * e) (Nat.mul_pos (by decide) he) q (refineLattice e he 0)
          (1 + g) i).coeff ((e : ℤ) * 0) = 0
                   rw [hzero', coeff_zero])
    exact hideg.trans (wordDegree_one_add_le g)

/-- Initial generic separation completes the finite Newton approximation at
every requested precision, with one support bound fixed before the precision.
All corrections and the finite termination argument are kernel checked. -/
theorem finite_newton_approximation_of_generic_variation
    (g : FreeAlgebra K Bool) (hg : g ≠ 0) (hab : binaryAbelianize K g = 0)
    (hseparate : ∃ j : ℕ, 0 < j ∧
      genericVariation (E := FractionRing (MvPolynomial (ℕ × ℕ) K))
        (0 : Derivation K K K) 0 (fun _ ↦ rfl) 1 (by decide) 0 0 (1 + g) j ≠ 0) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ T : ℕ, 0 < T →
      Nonempty (AuditedAssumptions.SymbolApproximation K g A T) := by
  obtain ⟨A, hA, ⟨d⟩⟩ := exists_initial_slopeData g hg hab hseparate
  refine ⟨A, hA, fun T _ ↦ d.approximation ?_ ?_ T⟩
  · change (toSeries (evaluateAt (hp := (by decide : 0 < 1))
      (δ := (0 : Derivation K K K)) (η := 0) (h := fun _ ↦ rfl)
      (0 : LaurentSeries K) (1 + g))).coeff 0 ≠ 0
    rw [InitialNewton.initial_residual g hab 1 (by decide) 0 0 (fun _ ↦ rfl)]
    simp
  · rw [State.initial_precision]


end MakarLimanov.InitialSlopeData

end
