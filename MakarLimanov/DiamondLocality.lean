import MakarLimanov.CoordinateLocality

/-!
# Uniform finite source windows for the infinite coordinate product

The lower Laurent bounds give a finite derivative range for each coefficient.
Combining the summand windows proves locality of the full diamond product.
-/

namespace MakarLimanov.TaylorCoordinates

open HahnSeries Finset

variable {F : Type*} [Field F] [CharZero F]

/-- A uniform derivative cutoff determined by lower bounds, rather than the
possibly changed orders of individual truncated inputs. -/
lemma diamond_coeff_finite_of_bounds (p : ℕ) (hp : 0 < p)
    {b c : ℤ} {x y : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (hy : CoordinateBound c y) (m : ℤ) :
    (diamond p hp x y).coeff m =
      ∑ n ∈ Finset.range ((m - (b + c)).toNat + 1), (diamondTerm p x y n).coeff m := by
  apply SummableFamily.coeff_hsum_eq_sum_of_subset
  intro n hn
  change (diamondTerm p x y n).coeff m ≠ 0 at hn
  have hbound : b + c + (p : ℤ) * n ≤ m := by
    by_contra! h
    exact hn (diamondTerm_bound p hx hy n m h)
  have hp' : (1 : ℤ) ≤ p := by omega
  have hn' : (0 : ℤ) ≤ n := by omega
  have : (n : ℤ) ≤ m - (b + c) := by nlinarith
  change n ∈ Finset.range ((m - (b + c)).toNat + 1)
  rw [Finset.mem_range]
  omega

end MakarLimanov.TaylorCoordinates

namespace MakarLimanov.TaylorCoordinates

open HahnSeries

variable {F : Type*} [Field F] [CharZero F]

/-- The infinite diamond product preserves the sum of the input Laurent lower bounds. -/
lemma CoordinateBound.diamond {b c : ℤ} {x y : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (hy : CoordinateBound c y) (p : ℕ) (hp : 0 < p) :
    CoordinateBound (b + c) (TaylorCoordinates.diamond p hp x y) := by
  intro m hm
  change (∑ᶠ n, (diamondTerm p x y n).coeff m) = 0
  have hz : ∀ n, (diamondTerm p x y n).coeff m = 0 := by
    intro n
    apply diamondTerm_bound p hx hy n
    have : (0 : ℤ) ≤ (p : ℤ) * n := mul_nonneg (by omega) (by omega)
    omega
  simp [hz]

end MakarLimanov.TaylorCoordinates

namespace MakarLimanov.MatrixRealization

open TaylorCoordinates HahnSeries Finset

variable {F : Type*} [Field F] [CharZero F]

/-- A diamond source coefficient uses a uniform finite derivative range. -/
lemma sourceCoeff_diamond_finite_of_bounds (p : ℕ) (hp : 0 < p)
    {b c : ℤ} {x y : LaurentSeries (BiSeries F)}
    (hx : CoordinateBound b x) (hy : CoordinateBound c y) (q : Source) :
    sourceCoeff (diamond p hp x y) q =
      ∑ n ∈ Finset.range ((-q.2 - (b + c)).toNat + 1),
        sourceCoeff (diamondTerm p x y n) q := by
  simp only [sourceCoeff, diamond_coeff_finite_of_bounds p hp hx hy, map_sum]

/-- Each coefficient of the infinite diamond product depends on finite source
windows of the inputs, uniformly under their lower Laurent bounds. -/
theorem exists_diamond_coefficient_window (p : ℕ) (hp : 0 < p) (b c : ℤ) (q : Source) :
    ∃ s t : Finset Source, ∀ x y x' y' : LaurentSeries (BiSeries F),
      CoordinateBound b x → CoordinateBound c y →
      CoordinateBound b x' → CoordinateBound c y' →
      (∀ u ∈ s, sourceCoeff x u = sourceCoeff x' u) →
      (∀ u ∈ t, sourceCoeff y u = sourceCoeff y' u) →
      sourceCoeff (diamond p hp x y) q = sourceCoeff (diamond p hp x' y') q := by
  classical
  choose s t hw using fun n : ℕ ↦
    exists_diamondTerm_coefficient_window (F := F) p n b c q
  let N := Finset.range ((-q.2 - (b + c)).toNat + 1)
  refine ⟨N.biUnion s, N.biUnion t, ?_⟩
  intro x y x' y' hx hy hx' hy' hs ht
  rw [sourceCoeff_diamond_finite_of_bounds p hp hx hy,
    sourceCoeff_diamond_finite_of_bounds p hp hx' hy']
  apply Finset.sum_congr rfl
  intro n hn
  exact hw n x y x' y' hx hy hx' hy'
    (fun u hu ↦ hs u (Finset.mem_biUnion.mpr ⟨n, hn, hu⟩))
    (fun u hu ↦ ht u (Finset.mem_biUnion.mpr ⟨n, hn, hu⟩))

end MakarLimanov.MatrixRealization
