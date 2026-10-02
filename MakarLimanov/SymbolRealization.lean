import MakarLimanov.InfiniteRealization

/-!
# The filtered symbol-realization ring homomorphism

Double Taylor expansion followed by the infinite normal-order construction
gives the constant-preserving realization, with its exact matrix jump bound.
-/

namespace MakarLimanov.SymbolRealization

open SymbolSeries TaylorCoordinates MatrixRealization ControlledMatrix Lattice HahnSeries

universe u v

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [CharZero F]
    (p : ℕ) (hp : 0 < p) (δ η : Derivation K F F) (h : Function.Commute δ η)

/-- The actual symbol-realization map, defined without any realization assumption. -/
noncomputable def realization : StarSeries p hp δ η h →+* Controlled (InLattice p) F where
  toFun U := realize p (taylorLaurent δ η U.toSeries)
  map_zero' := by
    have hz : taylorLaurent δ η (0 : LaurentSeries F) = 0 := by
      apply HahnSeries.ext
      funext n
      simp
    simp only [StarSeries.toSeries_zero, hz, realize_zero]
  map_one' := by
    have ho : taylorLaurent δ η (1 : LaurentSeries F) = 1 := by
      apply HahnSeries.ext
      funext n
      by_cases hn : n = 0 <;> simp [taylorLaurent_coeff, coeff_one, hn]
    simp only [StarSeries.toSeries_one, ho, realize_one]
  map_add' U V := by
    have ha : taylorLaurent δ η (U.toSeries + V.toSeries) =
        taylorLaurent δ η U.toSeries + taylorLaurent δ η V.toSeries := by
      apply HahnSeries.ext
      funext n
      simp
    rw [StarSeries.toSeries_add, ha, realize_add p hp]
  map_mul' U V := by
    rw [StarSeries.toSeries_mul, ← diamond_taylorLaurent δ η h p hp, realize_diamond p hp]

/-- Original base-field constants are sent to scalar matrices. -/
theorem realization_constants (c : K) :
    realization p hp δ η h (algebraMap K (StarSeries p hp δ η h) c) =
      algebraMap F (Controlled (InLattice p) F) (algebraMap K F c) := by
  change realize p (taylorLaurent δ η
    (StarSeries.toSeries (algebraMap K (StarSeries p hp δ η h) c))) = _
  rw [StarSeries.toSeries_algebraMap, taylorLaurent_single,
    doubleTaylor_of_constant δ η (algebraMap K F c) (by simp) (by simp), realize_constant]

/-- The realization keeps the exact lower-Laurent-to-matrix bound, with no
additional scaling by the denominator. -/
theorem realization_bound (U : StarSeries p hp δ η h) (b : ℤ)
    (hU : LowerBound b U.toSeries) : HasBound (realization p hp δ η h U).entries (-b) := by
  apply realize_bound
  intro n hn
  rw [taylorLaurent_coeff, hU n hn, map_zero]

/-- The complete realization existence statement, proved from the concrete construction. -/
theorem exists_realization :
    ∃ ρ : StarSeries p hp δ η h →+* Controlled (InLattice p) F,
      (∀ c : K, ρ (algebraMap K (StarSeries p hp δ η h) c) =
        algebraMap F (Controlled (InLattice p) F) (algebraMap K F c)) ∧
      ∀ (U : StarSeries p hp δ η h) (b : ℤ), LowerBound b U.toSeries →
        HasBound (ρ U).entries (-b) := by
  exact ⟨realization p hp δ η h, realization_constants p hp δ η h,
    realization_bound p hp δ η h⟩

end MakarLimanov.SymbolRealization
