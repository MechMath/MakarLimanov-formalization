import MakarLimanov.FiniteDiamond

/-!
# Entrywise finite coordinate truncations

Every fixed finite collection of realized matrix entries is unchanged by a
finite source truncation. The truncation preserves the Laurent support bound.
-/

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice TaylorCoordinates HahnSeries

variable {F : Type*} [Field F] (p : ℕ)

/-- Extracting a source coefficient is an additive map. -/
noncomputable def sourceCoeffAddHom (q : Source) :
    LaurentSeries (BiSeries F) →+ F where
  toFun x := sourceCoeff x q
  map_zero' := sourceCoeff_zero q
  map_add' x y := sourceCoeff_add x y q

@[simp] lemma sourceCoeff_coordinateMonomial (i j : ℕ) (r : ℤ) (c : F) (q : Source) :
    sourceCoeff (coordinateMonomial i j r c) q = if q = ((i, j), r) then c else 0 := by
  rcases q with ⟨⟨u, v⟩, s⟩
  by_cases hu : u = i <;> by_cases hv : v = j <;> by_cases hs : s = r <;>
    simp [sourceCoeff, coordinateMonomial, PowerSeries.coeff_monomial, hu, hv, hs]

/-- Retain only the selected Taylor--Laurent source monomials. -/
noncomputable def truncateSource (s : Finset Source) (x : LaurentSeries (BiSeries F)) :
    LaurentSeries (BiSeries F) :=
  ∑ q ∈ s, coordinateMonomial q.1.1 q.1.2 q.2 (sourceCoeff x q)

@[simp] lemma sourceCoeff_truncateSource (s : Finset Source)
    (x : LaurentSeries (BiSeries F)) (q : Source) :
    sourceCoeff (truncateSource s x) q = if q ∈ s then sourceCoeff x q else 0 := by
  classical
  change (sourceCoeffAddHom q) (∑ t ∈ s,
    coordinateMonomial t.1.1 t.1.2 t.2 (sourceCoeff x t)) = _
  rw [map_sum]
  change (∑ t ∈ s, sourceCoeff (coordinateMonomial t.1.1 t.1.2 t.2
    (sourceCoeff x t)) q) = _
  simp [eq_comm]

/-- A source truncation is an actual finite coordinate expression. -/
theorem finiteCoordinate_truncateSource (s : Finset Source)
    (x : LaurentSeries (BiSeries F)) : FiniteCoordinate (truncateSource s x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [truncateSource] using (FiniteCoordinate.zero (F := F))
  | @insert q s hq ih =>
    rw [truncateSource, Finset.sum_insert hq]
    exact .add (.monomial _ _ _ _) ih

/-- Truncating source coefficients never weakens the lower Laurent bound. -/
theorem truncateSource_bound (s : Finset Source) (x : LaurentSeries (BiSeries F))
    (b : ℤ) (hx : CoordinateBound b x) : CoordinateBound b (truncateSource s x) := by
  intro n hn
  ext i j
  have h := sourceCoeff_truncateSource s x ((i, j), -n)
  simp only [sourceCoeff, neg_neg] at h
  rw [h]
  simp [hx n hn]

/-- A finite truncation that contains all contributing sources preserves a matrix entry. -/
theorem truncateSource_entry_eq (s : Finset Source) (x : LaurentSeries (BiSeries F))
    (a b : Index (InLattice p))
    (hs : ∀ q : Source, sourceCoeff x q *
      normalMonomialMatrix p q.1.1 q.1.2 q.2 a b ≠ 0 → q ∈ s) :
    realize p (truncateSource s x) a b = realize p x a b := by
  classical
  simp only [realize_apply, entries]
  apply finsum_congr
  intro q
  rw [sourceCoeff_truncateSource]
  by_cases hq : q ∈ s
  · simp [hq]
  · have hz : sourceCoeff x q * normalMonomialMatrix p q.1.1 q.1.2 q.2 a b = 0 := by
      by_contra h
      exact hq (hs q h)
    simp [hq, hz]

/-- Any finite collection of entries is exactly reproduced by one finite coordinate expression. -/
theorem exists_truncation_entries (hp : 0 < p) (x : LaurentSeries (BiSeries F))
    (e : Finset (Index (InLattice p) × Index (InLattice p))) :
    ∃ s : Finset Source, ∀ ab ∈ e,
      realize p (truncateSource s x) ab.1 ab.2 = realize p x ab.1 ab.2 := by
  classical
  have hs := e.finite_toSet.biUnion (fun ab _ ↦ finite_entry_support p hp x ab.1 ab.2)
  refine ⟨hs.toFinset, ?_⟩
  intro ab hab
  apply truncateSource_entry_eq
  intro q hq
  apply hs.mem_toFinset.mpr
  exact Set.mem_iUnion₂.mpr ⟨ab, hab, hq⟩

/-- A fixed product entry is reproduced exactly by finite truncations of both
inputs. This uses the joint source support, rather than an unjustified action
of the infinite matrices on a direct-sum vector space. -/
theorem exists_truncation_product_entry (hp : 0 < p)
    (x y : LaurentSeries (BiSeries F)) (a b : Index (InLattice p)) :
    ∃ s t : Finset Source,
      (realize p (truncateSource s x) * realize p (truncateSource t y)) a b =
        (realize p x * realize p y) a b := by
  classical
  let f : Index (InLattice p) × (Source × Source) → F := fun q ↦
    (sourceCoeff x q.2.1 *
      normalMonomialMatrix p q.2.1.1.1 q.2.1.1.2 q.2.1.2 a q.1) *
    (sourceCoeff y q.2.2 *
      normalMonomialMatrix p q.2.2.1.1 q.2.2.1.2 q.2.2.2 q.1 b)
  have hf : (Function.support f).Finite := finite_product_entry_support p hp x y a b
  let s := (hf.image (fun q ↦ q.2.1)).toFinset
  let t := (hf.image (fun q ↦ q.2.2)).toFinset
  refine ⟨s, t, ?_⟩
  rw [product_entry_expansion p hp, product_entry_expansion p hp]
  apply finsum_congr
  intro q
  by_cases hz : f q = 0
  · dsimp [f] at hz
    simp only [sourceCoeff_truncateSource]
    split_ifs <;> simp [hz]
  · have hs : q.2.1 ∈ s := by
      exact (hf.image (fun q ↦ q.2.1)).mem_toFinset.mpr (Set.mem_image_of_mem _ hz)
    have ht : q.2.2 ∈ t := by
      exact (hf.image (fun q ↦ q.2.2)).mem_toFinset.mpr (Set.mem_image_of_mem _ hz)
    simp [sourceCoeff_truncateSource, hs, ht]

/-- Enlarging the truncation windows also preserves the fixed product entry. -/
theorem exists_truncation_product_entry_stable (hp : 0 < p)
    (x y : LaurentSeries (BiSeries F)) (a b : Index (InLattice p)) :
    ∃ s₀ t₀ : Finset Source, ∀ s t : Finset Source, s₀ ⊆ s → t₀ ⊆ t →
      (realize p (truncateSource s x) * realize p (truncateSource t y)) a b =
        (realize p x * realize p y) a b := by
  classical
  let f : Index (InLattice p) × (Source × Source) → F := fun q ↦
    (sourceCoeff x q.2.1 *
      normalMonomialMatrix p q.2.1.1.1 q.2.1.1.2 q.2.1.2 a q.1) *
    (sourceCoeff y q.2.2 *
      normalMonomialMatrix p q.2.2.1.1 q.2.2.1.2 q.2.2.2 q.1 b)
  have hf : (Function.support f).Finite := finite_product_entry_support p hp x y a b
  let s₀ := (hf.image (fun q ↦ q.2.1)).toFinset
  let t₀ := (hf.image (fun q ↦ q.2.2)).toFinset
  refine ⟨s₀, t₀, ?_⟩
  intro s t hs₀ ht₀
  rw [product_entry_expansion p hp, product_entry_expansion p hp]
  apply finsum_congr
  intro q
  by_cases hz : f q = 0
  · dsimp [f] at hz
    simp only [sourceCoeff_truncateSource]
    split_ifs <;> simp [hz]
  · have hs : q.2.1 ∈ s := by
      exact hs₀ ((hf.image (fun q ↦ q.2.1)).mem_toFinset.mpr (Set.mem_image_of_mem _ hz))
    have ht : q.2.2 ∈ t := by
      exact ht₀ ((hf.image (fun q ↦ q.2.2)).mem_toFinset.mpr (Set.mem_image_of_mem _ hz))
    simp [sourceCoeff_truncateSource, hs, ht]

end MakarLimanov.MatrixRealization
