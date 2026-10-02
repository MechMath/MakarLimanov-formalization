import MakarLimanov.GenericResidualTranslation
import MakarLimanov.GenericResidualBounds
import MakarLimanov.ExactGenericSlope
import MakarLimanov.SupportingSlope

/-!
# The next supporting slope after a Newton correction

The translated residual bound and the first surviving homogeneous correction
component provide the finite order data needed by the next supporting-line
argument.
-/

noncomputable section

namespace MakarLimanov.CorrectedNextSlope

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets NewtonResidual VariationCoefficients

universe u

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

/-- After an actual correction, the old residual bound and the first nonzero
translated homogeneous component produce the finite support inequalities for
the next slope. `newResidual` is the actual residual at the corrected symbol;
its order is the `ρ'` in the supporting-line statement. -/
theorem exists_next_supporting_slope
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ)
    (hr : LowerBound r (genericResidual (E := E) δ η hc p hp q z f))
    (D H : Derivation k G G) (hDH : Function.Commute D H)
    (hD : ∀ a : F, D (algebraMap F G a) = algebraMap F G (δ a))
    (hH : ∀ a : F, H (algebraMap F G a) = algebraMap F G (η a))
    (w : G) (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (m : ℕ) (hm : 0 < m)
    (hlow : ∀ j < m,
      MvPolynomial.homogeneousComponent j
        (NewtonTranslation.translate
          (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
          (MvPolynomial.map (algebraMap F G) P)) = 0)
    (htop : MvPolynomial.homogeneousComponent m
      (NewtonTranslation.translate (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
        (MvPolynomial.map (algebraMap F G) P)) ≠ 0)
    (newResidual : LaurentSeries G)
    (hnewEq : newResidual = toSeries (evaluateAt (hp := hp) (h := hDH)
      (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f))
    (hnew : newResidual ≠ 0)
    (horder : r < newResidual.order) :
    let z' := mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w
    newResidual.coeff newResidual.order ≠ 0 ∧
      ∃ active : Finset ℕ,
        (∀ j, j ∈ active ↔ j ≤ ControlledMatrix.wordDegree f ∧ 0 < j ∧
          genericVariation (E := K) D H hDH p hp 0 z' f j ≠ 0) ∧
        ∃ (s' : ℚ) (j : ℕ), j ∈ active ∧ 0 < j ∧ j ≤ m ∧
          (q : ℚ) < s' ∧
          ((genericVariation (E := K) D H hDH p hp q z' f j).order : ℚ) +
              (j : ℚ) * (s' - (q : ℚ)) = (newResidual.order : ℚ) ∧
          (∀ i ∈ active,
            (newResidual.order : ℚ) ≤
              ((genericVariation (E := K) D H hDH p hp q z' f i).order : ℚ) +
                (i : ℚ) * (s' - (q : ℚ))) ∧
          (∀ i ∈ active,
            ((genericVariation (E := K) D H hDH p hp q z' f i).order : ℚ) +
                (i : ℚ) * (s' - (q : ℚ)) = (newResidual.order : ℚ) → i ≤ m) := by
  classical
  dsimp
  let z' : LaurentSeries G :=
    mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w
  let active : Finset ℕ :=
    (Finset.range (ControlledMatrix.wordDegree f + 1)).filter
      (fun j ↦ 0 < j ∧
        genericVariation (E := K) D H hDH p hp 0 z' f j ≠ 0)
  let a : ℕ → ℚ :=
    fun j ↦ ((genericVariation (E := K) D H hDH p hp q z' f j).order : ℚ)
  have hnewBound := GenericResidualTranslation.translated_residual_lowerBound
    (E := E) (K := K) δ η hc p hp q z f r hr D H hDH hD hH w
  have hvariationBound :=
    (GenericResidualBounds.genericResidual_lowerBound_iff
      (E := K) D H hDH p hp q z' f r).mp hnewBound
  have htranslatedTop :=
    GenericResidualTranslation.corrected_variation_coefficients_of_translation
      (E := E) (K := K) δ η hc p hp q z f r D H hDH hD hH w P hP m hlow htop
  have hmcoef :
      (genericVariation (E := K) D H hDH p hp q z' f m).coeff r ≠ 0 :=
    htranslatedTop.2
  have hmnonzero : genericVariation (E := K) D H hDH p hp q z' f m ≠ 0 := by
    intro hz
    exact hmcoef (by simp [hz])
  have hmslope := ExactGenericSlope.genericVariation_slope
    (E := K) D H hDH p hp q z' f m
  have hmzeroSlope : genericVariation (E := K) D H hDH p hp 0 z' f m ≠ 0 := by
    intro hz
    exact hmnonzero (hmslope.1.mpr hz)
  have hmdegree : m ≤ ControlledMatrix.wordDegree f := by
    by_contra hnot
    have hvan := GenericResidualHomogeneous.genericResidual_variation_degree_bound
      (E := K) D H hDH p hp 0 z' f m (Nat.lt_of_not_ge hnot)
    exact hmzeroSlope (by simpa [genericVariation] using hvan)
  have hmem : m ∈ active := by
    simp only [active, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hm, hmzeroSlope⟩
  have hlowerOrder : ∀ j ∈ active, (r : ℚ) ≤ a j := by
    intro j hj
    have hjpos : 0 < j := (Finset.mem_filter.mp hj).2.1
    have hjzero : genericVariation (E := K) D H hDH p hp 0 z' f j ≠ 0 :=
      (Finset.mem_filter.mp hj).2.2
    have hjslope := ExactGenericSlope.genericVariation_slope
      (E := K) D H hDH p hp q z' f j
    have hjnonzero : genericVariation (E := K) D H hDH p hp q z' f j ≠ 0 := by
      intro hz
      exact hjzero (hjslope.1.mp hz)
    have hjorder : r ≤ (genericVariation (E := K) D H hDH p hp q z' f j).order := by
      by_contra hn
      have hlt : (genericVariation (E := K) D H hDH p hp q z' f j).order < r :=
        lt_of_not_ge hn
      have hcoeffzero := hvariationBound j
        (genericVariation (E := K) D H hDH p hp q z' f j).order hlt
      exact (HahnSeries.coeff_order_eq_zero.not.mpr hjnonzero) hcoeffzero
    change (r : ℚ) ≤
      ((genericVariation (E := K) D H hDH p hp q z' f j).order : ℚ)
    exact_mod_cast hjorder
  have ham : a m = (r : ℚ) := by
    have hmlower : r ≤ (genericVariation (E := K) D H hDH p hp q z' f m).order := by
      by_contra hn
      have hlt :
          (genericVariation (E := K) D H hDH p hp q z' f m).order < r :=
        lt_of_not_ge hn
      have hcoeffzero := hvariationBound m
        (genericVariation (E := K) D H hDH p hp q z' f m).order hlt
      exact (HahnSeries.coeff_order_eq_zero.not.mpr hmnonzero) hcoeffzero
    have hmupper := HahnSeries.order_le_of_coeff_ne_zero hmcoef
    change ((genericVariation (E := K) D H hDH p hp q z' f m).order : ℚ) = (r : ℚ)
    exact_mod_cast le_antisymm hmupper hmlower
  have hstrict : (r : ℚ) < (newResidual.order : ℚ) := by
    exact_mod_cast horder
  have hpositive : ∀ j ∈ active, 0 < j := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2.1
  have hline := SupportingSlope.exists_supporting_line
    (r : ℚ) (newResidual.order : ℚ) (q : ℚ) a active hm hmem hstrict
    hlowerOrder ham hpositive
  have hactual :
      toSeries (evaluateAt (hp := hp) (h := hDH)
        (mapField (IsScalarTower.toAlgHom k F G) z + HahnSeries.single q w) f) ≠ 0 := by
    rw [← hnewEq]
    exact hnew
  have hnewCoeff : newResidual.coeff newResidual.order ≠ 0 := by
    rw [hnewEq]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hactual)
  refine ⟨hnewCoeff, active, ?_, ?_⟩
  · intro j
    simp only [active, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hjrange, hjpos, hjzero⟩
      exact ⟨by omega, hjpos, hjzero⟩
    · rintro ⟨hjdegree, hjpos, hjzero⟩
      exact ⟨by omega, hjpos, hjzero⟩
  · simpa [a] using hline

end MakarLimanov.CorrectedNextSlope

end
