import MakarLimanov.DiamondLocality

/-!
# Multiplicativity of the infinite normal-order realization

Uniform finite source windows reduce each entry of the infinite product to
the already proved finite coordinate realization theorem.
-/

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice TaylorCoordinates HahnSeries

variable {F : Type*} [Field F] [CharZero F] (p : ℕ)

/-- Matching all bounded source monomials that reach an entry matches that entry. -/
theorem entry_eq_of_source_window (hp : 0 < p) (b : ℤ)
    {x y : LaurentSeries (BiSeries F)} (hx : CoordinateBound b x) (hy : CoordinateBound b y)
    (a d : Index (InLattice p))
    (h : ∀ q : Source, q.2 ≤ -b →
      normalMonomialMatrix (F := F) p q.1.1 q.1.2 q.2 a d ≠ 0 →
        sourceCoeff x q = sourceCoeff y q) :
    realize p x a d = realize p y a d := by
  simp only [realize_apply, entries]
  apply finsum_congr
  intro q
  by_cases hm : normalMonomialMatrix (F := F) p q.1.1 q.1.2 q.2 a d = 0
  · simp [hm]
  · by_cases hq : q.2 ≤ -b
    · rw [h q hq hm]
    · have hq' : -b < q.2 := by omega
      rw [sourceCoeff_eq_zero_of_lt x b hx q hq',
        sourceCoeff_eq_zero_of_lt y b hy q hq']

/-- A realized diamond entry has uniform finite source windows in both inputs. -/
theorem exists_diamond_entry_window (hp : 0 < p) (b c : ℤ)
    (a d : Index (InLattice p)) :
    ∃ s t : Finset Source, ∀ x y x' y' : LaurentSeries (BiSeries F),
      CoordinateBound b x → CoordinateBound c y →
      CoordinateBound b x' → CoordinateBound c y' →
      (∀ u ∈ s, sourceCoeff x u = sourceCoeff x' u) →
      (∀ u ∈ t, sourceCoeff y u = sourceCoeff y' u) →
      realize p (diamond p hp x y) a d = realize p (diamond p hp x' y') a d := by
  classical
  let M := (finite_normalMonomial_sources (F := F) p hp (-(b + c)) a d).toFinset
  choose s t hw using fun q : Source ↦ exists_diamond_coefficient_window (F := F) p hp b c q
  refine ⟨M.biUnion s, M.biUnion t, ?_⟩
  intro x y x' y' hx hy hx' hy' hs ht
  apply entry_eq_of_source_window p hp (b + c) (hx.diamond hy p hp) (hx'.diamond hy' p hp)
  intro q hq hm
  have hM : q ∈ M :=
    (finite_normalMonomial_sources (F := F) p hp (-(b + c)) a d).mem_toFinset.mpr ⟨hq, hm⟩
  exact hw q x y x' y' hx hy hx' hy'
    (fun u hu ↦ hs u (Finset.mem_biUnion.mpr ⟨q, hM, hu⟩))
    (fun u hu ↦ ht u (Finset.mem_biUnion.mpr ⟨q, hM, hu⟩))

/-- The concrete normal-order matrix construction preserves the full infinite
coordinate product. Every rearrangement is reduced to a finite source window. -/
theorem realize_diamond (hp : 0 < p) (x y : LaurentSeries (BiSeries F)) :
    realize p (diamond p hp x y) = realize p x * realize p y := by
  classical
  apply Controlled.ext
  intro a d
  obtain ⟨s₀, t₀, hprod⟩ := exists_truncation_product_entry_stable p hp x y a d
  obtain ⟨s₁, t₁, hdiamond⟩ := exists_diamond_entry_window (F := F) p hp x.order y.order a d
  let s := s₀ ∪ s₁
  let t := t₀ ∪ t₁
  have hx := coordinateBound_order x
  have hy := coordinateBound_order y
  have hdx := truncateSource_bound s x x.order hx
  have hdy := truncateSource_bound t y y.order hy
  have hd := hdiamond x y (truncateSource s x) (truncateSource t y) hx hy hdx hdy
    (fun u hu ↦ by rw [sourceCoeff_truncateSource, if_pos (Finset.mem_union_right _ hu)])
    (fun u hu ↦ by rw [sourceCoeff_truncateSource, if_pos (Finset.mem_union_right _ hu)])
  calc
    (realize p (diamond p hp x y)).entries a d =
        realize p (diamond p hp (truncateSource s x) (truncateSource t y)) a d := hd
    _ = (realize p (truncateSource s x) * realize p (truncateSource t y)) a d := by
      rw [realize_diamond_finite p hp (finiteCoordinate_truncateSource s x)
        (finiteCoordinate_truncateSource t y)]
    _ = (realize p x * realize p y).entries a d :=
      hprod s t Finset.subset_union_left Finset.subset_union_left

end MakarLimanov.MatrixRealization
