import MakarLimanov.ExactGenericSlope
import MakarLimanov.Numerics

/-!
# Finite slope selection

The Newton argument chooses a supporting slope from the finite set of active
homogeneous degrees. This module packages that finite maximum together with
the exact order covariance of the universal variations.
-/

namespace MakarLimanov.SlopeSelection

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open GenericJets VariationCoefficients

noncomputable section

universe u

variable {k F E : Type u} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

/-- Select a degree whose rational slope is maximal. -/
theorem exists_supporting_active_degree
    (ρ ρ' s : ℚ) (a : ℕ → ℚ) (active : Finset ℕ)
    {m : ℕ} (hm : 0 < m) (hmem : m ∈ active)
    (hρ : ρ < ρ') (ha : ∀ j ∈ active, ρ ≤ a j) (ham : a m = ρ) :
    ∃ k ∈ active, 0 < k ∧ k ≤ m ∧
      s < s + (ρ' - a k) / (k : ℚ) ∧
      ∀ j ∈ active, s + (ρ' - a j) / (j : ℚ) ≤
        s + (ρ' - a k) / (k : ℚ) := by
  exact MakarLimanov.exists_next_slope ρ ρ' s a active hm hmem hρ ha ham

/-- Select a supporting degree and retain its exact order formula at every
integer numerator. -/
theorem exists_supporting_generic_variation
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (active : Finset ℕ)
    {m : ℕ} (hm : 0 < m) (hmem : m ∈ active)
    (ρ ρ' s : ℚ) (hρ : ρ < ρ')
    (ha : ∀ j ∈ active,
      ρ ≤ ((genericVariation (E := E) δ η hc p hp 0 z f j).order : ℚ))
    (ham : ((genericVariation (E := E) δ η hc p hp 0 z f m).order : ℚ) = ρ)
    (hactive : ∀ j ∈ active,
      genericVariation (E := E) δ η hc p hp 0 z f j ≠ 0) :
    ∃ k ∈ active, 0 < k ∧ k ≤ m ∧
      s < s + (ρ' -
        ((genericVariation (E := E) δ η hc p hp 0 z f k).order : ℚ)) /
        (k : ℚ) ∧
      (∀ j ∈ active, s + (ρ' -
        ((genericVariation (E := E) δ η hc p hp 0 z f j).order : ℚ)) /
        (j : ℚ) ≤ s + (ρ' -
        ((genericVariation (E := E) δ η hc p hp 0 z f k).order : ℚ)) /
        (k : ℚ)) ∧
      (∀ q : ℤ,
        genericVariation (E := E) δ η hc p hp q z f k ≠ 0 ∧
          (genericVariation (E := E) δ η hc p hp q z f k).order =
            (k : ℤ) * q +
              (genericVariation (E := E) δ η hc p hp 0 z f k).order) := by
  let a : ℕ → ℚ := fun j ↦
    (genericVariation (E := E) δ η hc p hp 0 z f j).order
  obtain ⟨k, hk, hkpos, hkm, hks, hmax⟩ :=
    exists_supporting_active_degree ρ ρ' s a active hm hmem hρ
      (by
        intro j hj
        simpa [a] using ha j hj)
      (by simpa [a] using ham)
  refine ⟨k, hk, hkpos, hkm, ?_, ?_, ?_⟩
  · simpa [a] using hks
  · intro j hj
    simpa [a] using hmax j hj
  · intro q
    have hq := ExactGenericSlope.genericVariation_slope
      (E := E) δ η hc p hp q z f k
    have hV0 := hactive k hk
    exact ⟨fun hzero ↦ hV0 (hq.1.mp hzero), hq.2 hV0⟩

end

end MakarLimanov.SlopeSelection
