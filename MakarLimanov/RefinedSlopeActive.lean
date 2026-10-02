import MakarLimanov.ExactGenericSlope
import MakarLimanov.GenericSlopeRefinement
import MakarLimanov.GenericResidualHomogeneous

/-!
# Active variation coefficients after refining a supporting slope

Exact order covariance transports a supporting-line equality to a nonzero
coefficient on the refined lattice. Conversely, a nonzero coefficient at the
supporting order must come from an old nonzero variation attaining the line.
-/

noncomputable section

namespace MakarLimanov.RefinedSlopeActive

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

/-- Refinement and a change of slope preserve the nonzero variation degrees. -/
theorem refined_variation_eq_zero_iff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q q' : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (i : ℕ) :
    genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        q' (refineLattice e he z) f i = 0 ↔
      genericVariation (E := E) δ η hc p hp q z f i = 0 := by
  have hnew := (ExactGenericSlope.genericVariation_slope (E := E)
    δ η hc (p * e) (Nat.mul_pos hp he) q' (refineLattice e he z) f i).1
  have href := GenericSlopeRefinement.refineLattice_genericVariation_eq_zero_iff
    (E := E) δ η hc p e hp he 0 z f i
  have hold := (ExactGenericSlope.genericVariation_slope (E := E)
    δ η hc p hp q z f i).1
  simpa only [mul_zero] using hnew.trans (href.symm.trans hold.symm)

/-- The exact refined order is the old order plus the slope increment,
multiplied by the refinement factor. -/
theorem refined_variation_order
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p e : ℕ) (hp : 0 < p) (he : 0 < e) (q q' : ℤ)
    (z : LaurentSeries F) (f : FreeAlgebra k Bool) (s : ℚ)
    (hq' : (q' : ℚ) = (e : ℚ) * s) (i : ℕ)
    (hV : genericVariation (E := E) δ η hc p hp q z f i ≠ 0) :
    ((genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q' (refineLattice e he z) f i).order : ℚ) =
      (e : ℚ) *
        (((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
          (i : ℚ) * (s - (q : ℚ))) := by
  have hold := ExactGenericSlope.genericVariation_slope (E := E)
    δ η hc p hp q z f i
  have hV0 : genericVariation (E := E) δ η hc p hp 0 z f i ≠ 0 :=
    fun hz ↦ hV (hold.1.mpr hz)
  have hVref0 : genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      0 (refineLattice e he z) f i ≠ 0 := by
    intro hz
    apply hV0
    exact (GenericSlopeRefinement.refineLattice_genericVariation_eq_zero_iff
      (E := E) δ η hc p e hp he 0 z f i).mpr (by simpa using hz)
  have hnew := ExactGenericSlope.genericVariation_slope (E := E)
    δ η hc (p * e) (Nat.mul_pos hp he) q' (refineLattice e he z) f i
  rw [hnew.2 hVref0,
    GenericSlopeRefinement.refineLattice_genericVariation_zero_order
      (E := E) δ η hc p e hp he z f i hV0, hold.2 hV0]
  push_cast
  rw [hq']
  ring

/-- A variation attaining the supporting line gives a nonzero coefficient at
the scaled residual order. -/
theorem coefficient_ne_zero_of_supporting_equality
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (rho : ℤ) (s : ℚ) (i : ℕ)
    (hV : genericVariation (E := E) δ η hc p hp q z f i ≠ 0)
    (htie : ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
      (i : ℚ) * (s - (q : ℚ)) = (rho : ℚ))
    (e : ℕ) (he : 0 < e) (q' : ℤ)
    (hq' : (q' : ℚ) = (e : ℚ) * s) :
    (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q' (refineLattice e he z) f i).coeff ((e : ℤ) * rho) ≠ 0 := by
  have hVnew : genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q' (refineLattice e he z) f i ≠ 0 := by
    intro hz
    exact hV ((refined_variation_eq_zero_iff
      (E := E) δ η hc p e hp he q q' z f i).mp hz)
  have horder := refined_variation_order (E := E)
    δ η hc p e hp he q q' z f s hq' i hV
  rw [htie] at horder
  have horderZ : (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q' (refineLattice e he z) f i).order = (e : ℤ) * rho := by
    exact_mod_cast horder
  rw [← horderZ]
  exact HahnSeries.coeff_order_eq_zero.not.mpr hVnew

/-- If the supporting-line lower bound holds, a nonzero coefficient at its
height forces the old variation to be nonzero and to attain the line. -/
theorem supporting_equality_of_coefficient_ne_zero
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (rho : ℤ) (s : ℚ) (i : ℕ)
    (hline : genericVariation (E := E) δ η hc p hp q z f i ≠ 0 →
      (rho : ℚ) ≤ ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
        (i : ℚ) * (s - (q : ℚ)))
    (e : ℕ) (he : 0 < e) (q' : ℤ)
    (hq' : (q' : ℚ) = (e : ℚ) * s)
    (hcoeff : (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q' (refineLattice e he z) f i).coeff ((e : ℤ) * rho) ≠ 0) :
    genericVariation (E := E) δ η hc p hp q z f i ≠ 0 ∧
      ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
        (i : ℚ) * (s - (q : ℚ)) = (rho : ℚ) := by
  have hVnew := HahnSeries.ne_zero_of_coeff_ne_zero hcoeff
  have hV : genericVariation (E := E) δ η hc p hp q z f i ≠ 0 := by
    intro hz
    exact hVnew ((refined_variation_eq_zero_iff
      (E := E) δ η hc p e hp he q q' z f i).mpr hz)
  refine ⟨hV, le_antisymm ?_ (hline hV)⟩
  have horder := refined_variation_order (E := E)
    δ η hc p e hp he q q' z f s hq' i hV
  have hle := HahnSeries.order_le_of_coeff_ne_zero hcoeff
  have hleQ : ((genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q' (refineLattice e he z) f i).order : ℚ) ≤ (e : ℚ) * rho := by
    exact_mod_cast hle
  rw [horder] at hleQ
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast he : (0 : ℚ) < e)).mp hleQ

/-- Positive refined active degrees belong to the old finite active set and
attain its supporting line. -/
theorem mem_active_and_tie_of_coefficient_ne_zero
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (rho : ℤ) (s : ℚ)
    (active : Finset ℕ)
    (hactive : ∀ i, i ∈ active ↔
      i ≤ ControlledMatrix.wordDegree f ∧ 0 < i ∧
        genericVariation (E := E) δ η hc p hp q z f i ≠ 0)
    (hline : ∀ i ∈ active,
      (rho : ℚ) ≤ ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
        (i : ℚ) * (s - (q : ℚ)))
    (e : ℕ) (he : 0 < e) (q' : ℤ)
    (hq' : (q' : ℚ) = (e : ℚ) * s) (i : ℕ) (hi : 0 < i)
    (hcoeff : (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
      q' (refineLattice e he z) f i).coeff ((e : ℤ) * rho) ≠ 0) :
    i ∈ active ∧
      ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
        (i : ℚ) * (s - (q : ℚ)) = (rho : ℚ) := by
  have hmem : genericVariation (E := E) δ η hc p hp q z f i ≠ 0 →
      i ∈ active := by
    intro hV
    apply (hactive i).mpr
    refine ⟨?_, hi, hV⟩
    by_contra hnot
    exact hV (GenericResidualHomogeneous.genericResidual_variation_degree_bound
      (E := E) δ η hc p hp q z f i (Nat.lt_of_not_ge hnot))
  obtain ⟨hV, htie⟩ := supporting_equality_of_coefficient_ne_zero
    (E := E) δ η hc p hp q z f rho s i (fun hV ↦ hline i (hmem hV))
    e he q' hq' hcoeff
  exact ⟨hmem hV, htie⟩

/-- A bound on the old indices attaining the line bounds every nonzero
homogeneous coefficient of the refined leading residual polynomial. -/
theorem active_coefficient_degree_bound
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (rho : ℤ) (s : ℚ)
    (active : Finset ℕ)
    (hactive : ∀ i, i ∈ active ↔
      i ≤ ControlledMatrix.wordDegree f ∧ 0 < i ∧
        genericVariation (E := E) δ η hc p hp q z f i ≠ 0)
    (hline : ∀ i ∈ active,
      (rho : ℚ) ≤ ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
        (i : ℚ) * (s - (q : ℚ)))
    (m : ℕ)
    (htie : ∀ i ∈ active,
      ((genericVariation (E := E) δ η hc p hp q z f i).order : ℚ) +
        (i : ℚ) * (s - (q : ℚ)) = (rho : ℚ) → i ≤ m)
    (e : ℕ) (he : 0 < e) (q' : ℤ)
    (hq' : (q' : ℚ) = (e : ℚ) * s) :
    ∀ i : ℕ,
      (genericVariation (E := E) δ η hc (p * e) (Nat.mul_pos hp he)
        q' (refineLattice e he z) f i).coeff ((e : ℤ) * rho) ≠ 0 → i ≤ m := by
  intro i hcoeff
  by_cases hi : i = 0
  · simp [hi]
  obtain ⟨hmem, heq⟩ := mem_active_and_tie_of_coefficient_ne_zero
    (E := E) δ η hc p hp q z f rho s active hactive hline e he q' hq' i
    (Nat.pos_of_ne_zero hi) hcoeff
  exact htie i hmem heq

end MakarLimanov.RefinedSlopeActive
