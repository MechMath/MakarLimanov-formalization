import MakarLimanov.MatrixRealizationSupport
import MakarLimanov.TaylorSeries
import Mathlib.RingTheory.LaurentSeries

/-!
# The entrywise normal-order realization

This constructs the actual controlled matrix of an arbitrary Laurent series
with double power-series coefficients. Each matrix entry is a finite sum even
though a column or row need not have finite support.
-/

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice HahnSeries

variable {F : Type*} [Field F] (p : ℕ)

/-- The source indices are the two Taylor exponents and the scaled Laurent exponent. -/
abbrev Source := (ℕ × ℕ) × ℤ

/-- Expand the lower-bounded Laurent convention as upper-bounded powers of `z^(1/p)`. -/
noncomputable def sourceCoeff (x : LaurentSeries (PowerSeries (PowerSeries F))) (q : Source) : F :=
  PowerSeries.coeff q.1.2 (PowerSeries.coeff q.1.1 (x.coeff (-q.2)))

lemma sourceCoeff_eq_zero_of_lt (x : LaurentSeries (PowerSeries (PowerSeries F)))
    (b : ℤ) (hx : ∀ n < b, x.coeff n = 0) (q : Source) (hq : -b < q.2) :
    sourceCoeff x q = 0 := by
  simp [sourceCoeff, hx (-q.2) (by omega)]

/-- The entry obtained by summing all normal-ordered source monomials. -/
noncomputable def entries (x : LaurentSeries (PowerSeries (PowerSeries F))) :
    Matrix (Index (InLattice p)) (Index (InLattice p)) F :=
  fun a b ↦ ∑ᶠ q : Source,
    sourceCoeff x q * normalMonomialMatrix p q.1.1 q.1.2 q.2 a b

/-- Every entry of the source expansion has finite support. -/
theorem finite_entry_support (hp : 0 < p)
    (x : LaurentSeries (PowerSeries (PowerSeries F))) (a b : Index (InLattice p)) :
    (Function.support (fun q : Source ↦
      sourceCoeff x q * normalMonomialMatrix p q.1.1 q.1.2 q.2 a b)).Finite := by
  apply (finite_normalMonomial_sources (F := F) p hp (-x.order) a b).subset
  intro q hq
  have hx : sourceCoeff x q ≠ 0 := left_ne_zero_of_mul hq
  refine ⟨?_, right_ne_zero_of_mul hq⟩
  by_contra! h
  exact hx (sourceCoeff_eq_zero_of_lt x x.order (fun _ h ↦ coeff_eq_zero_of_lt_order h) q h)

/-- A lower Laurent bound becomes the opposite coordinate bound of the realized matrix. -/
theorem entries_bound (x : LaurentSeries (PowerSeries (PowerSeries F)))
    (b : ℤ) (hx : ∀ n < b, x.coeff n = 0) : HasBound (entries p x) (-b) := by
  intro i j hij
  have hex : ∃ q : Source, sourceCoeff x q *
      normalMonomialMatrix p q.1.1 q.1.2 q.2 i j ≠ 0 := by
    by_contra! h
    exact hij (by simp [entries, h])
  obtain ⟨q, hq⟩ := hex
  have hb : q.2 ≤ -b := by
    by_contra! h
    exact left_ne_zero_of_mul hq (sourceCoeff_eq_zero_of_lt x b hx q h)
  obtain ⟨ha, hc⟩ := normalMonomialMatrix_bound (F := F) p q.1.1 q.1.2 q.2 i j
    (right_ne_zero_of_mul hq)
  constructor <;> omega

/-- The actual normal-order map, with its controlled support proof. -/
noncomputable def realize (x : LaurentSeries (PowerSeries (PowerSeries F))) :
    Controlled (InLattice p) F :=
  ⟨entries p x, -x.order,
    entries_bound p x x.order (fun _ h ↦ coeff_eq_zero_of_lt_order h)⟩

@[simp] lemma realize_apply (x : LaurentSeries (PowerSeries (PowerSeries F)))
    (a b : Index (InLattice p)) : realize p x a b = entries p x a b := rfl

lemma realize_bound (x : LaurentSeries (PowerSeries (PowerSeries F)))
    (b : ℤ) (hx : ∀ n < b, x.coeff n = 0) :
    HasBound (realize p x).entries (-b) := entries_bound p x b hx

@[simp] lemma sourceCoeff_add (x y : LaurentSeries (PowerSeries (PowerSeries F))) (q : Source) :
    sourceCoeff (x+y) q = sourceCoeff x q + sourceCoeff y q := by
  simp [sourceCoeff]

@[simp] lemma sourceCoeff_zero (q : Source) : sourceCoeff (0 :
    LaurentSeries (PowerSeries (PowerSeries F))) q = 0 := by
  simp [sourceCoeff]

@[simp] lemma realize_zero : realize (F := F) p 0 = 0 := by
  apply Controlled.ext
  intro a b
  simp [entries]

/-- The infinite normal-order map is additive because every entry uses finite sums. -/
lemma realize_add (hp : 0 < p) (x y : LaurentSeries (PowerSeries (PowerSeries F))) :
    realize p (x+y) = realize p x + realize p y := by
  apply Controlled.ext
  intro a b
  change entries p (x+y) a b = entries p x a b + entries p y a b
  simp only [entries, sourceCoeff_add, add_mul]
  exact finsum_add_distrib (finite_entry_support p hp x a b) (finite_entry_support p hp y a b)

/-- The normal-order map fixes the identity. -/
@[simp] lemma realize_one : realize (F := F) p 1 = 1 := by
  apply Controlled.ext
  intro a b
  change (∑ᶠ q : Source, sourceCoeff (1 : LaurentSeries (PowerSeries (PowerSeries F))) q *
    normalMonomialMatrix p q.1.1 q.1.2 q.2 a b) = (1 : Controlled (InLattice p) F) a b
  rw [finsum_eq_single _ ((0,0),0)]
  · simp [sourceCoeff]
  · rintro ⟨⟨i,j⟩,r⟩ hq
    have h : r ≠ 0 ∨ i ≠ 0 ∨ j ≠ 0 := by
      by_contra! h
      simp [h.1, h.2.1, h.2.2] at hq
    rcases h with hr | hi | hj
    · simp [sourceCoeff, coeff_one, hr]
    · by_cases hr : r = 0
      · subst r; simp [sourceCoeff, coeff_one, PowerSeries.coeff_one, hi]
      · simp [sourceCoeff, coeff_one, hr]
    · by_cases hr : r = 0
      · subst r
        by_cases hi : i = 0
        · subst i; simp [sourceCoeff, PowerSeries.coeff_one, hj]
        · simp [sourceCoeff, PowerSeries.coeff_one, hi]
      · simp [sourceCoeff, coeff_one, hr]

/-- A constant coordinate expression realizes as a scalar matrix. -/
lemma realize_constant (c : F) :
    realize p (single 0 (PowerSeries.C (PowerSeries.C c))) =
      algebraMap F (Controlled (InLattice p) F) c := by
  apply Controlled.ext
  intro a b
  change (∑ᶠ q : Source, sourceCoeff (single 0 (PowerSeries.C (PowerSeries.C c))) q *
    normalMonomialMatrix p q.1.1 q.1.2 q.2 a b) = scalarMatrix c a b
  rw [finsum_eq_single _ ((0,0),0)]
  · simp [sourceCoeff]
    change c * scalarMatrix 1 a b = scalarMatrix c a b
    by_cases h : a = b <;> simp [scalarMatrix, h]
  · rintro ⟨⟨i,j⟩,r⟩ hq
    have h : r ≠ 0 ∨ i ≠ 0 ∨ j ≠ 0 := by
      by_contra! h
      simp [h.1, h.2.1, h.2.2] at hq
    rcases h with hr | hi | hj
    · have hz : sourceCoeff (single 0 (PowerSeries.C (PowerSeries.C c))) ((i,j),r) = 0 := by
        simp [sourceCoeff, HahnSeries.coeff_single, hr]
      rw [hz, zero_mul]
    · by_cases hr : r = 0
      · subst r
        have hz : sourceCoeff (single 0 (PowerSeries.C (PowerSeries.C c))) ((i,j),0) = 0 := by
          simp [sourceCoeff, PowerSeries.coeff_C, hi]
        rw [hz, zero_mul]
      · have hz : sourceCoeff (single 0 (PowerSeries.C (PowerSeries.C c))) ((i,j),r) = 0 := by
          simp [sourceCoeff, HahnSeries.coeff_single, hr]
        rw [hz, zero_mul]
    · by_cases hr : r = 0
      · subst r
        have hz : sourceCoeff (single 0 (PowerSeries.C (PowerSeries.C c))) ((i,j),0) = 0 := by
          by_cases hi : i = 0
          · subst i
            simp [sourceCoeff, HahnSeries.coeff_single, PowerSeries.coeff_C, hj]
          · simp [sourceCoeff, HahnSeries.coeff_single, PowerSeries.coeff_C, hi]
        rw [hz, zero_mul]
      · have hz : sourceCoeff (single 0 (PowerSeries.C (PowerSeries.C c))) ((i,j),r) = 0 := by
          simp [sourceCoeff, HahnSeries.coeff_single, hr]
        rw [hz, zero_mul]


/-- The entrywise realization as an additive group homomorphism. -/
noncomputable def realizeAddHom (hp : 0 < p) :
    LaurentSeries (PowerSeries (PowerSeries F)) →+ Controlled (InLattice p) F where
  toFun := realize p
  map_zero' := realize_zero p
  map_add' := realize_add p hp

/-- A single Taylor--Laurent monomial realizes as its normal-ordered matrix,
scaled by its coefficient. This identifies the infinite construction with the
concrete monomial operators used in the multiplication calculation. -/
lemma realize_monomial (i j : ℕ) (r : ℤ) (c : F) :
    realize p (single (-r) (PowerSeries.monomial i (PowerSeries.monomial j c))) =
      algebraMap F (Controlled (InLattice p) F) c * normalMonomialMatrix p i j r := by
  classical
  apply Controlled.ext
  intro a b
  change (∑ᶠ q : Source,
    sourceCoeff (single (-r) (PowerSeries.monomial i (PowerSeries.monomial j c))) q *
      normalMonomialMatrix p q.1.1 q.1.2 q.2 a b) = _
  rw [finsum_eq_single _ ((i, j), r)]
  · simp only [sourceCoeff, coeff_single_same, PowerSeries.coeff_monomial_same]
    change c * normalMonomialMatrix p i j r a b =
      product (scalarMatrix c) (normalMonomialMatrix p i j r).entries a b
    rw [scalar_product]
  · rintro ⟨⟨u, v⟩, s⟩ hq
    by_cases hs : s = r
    · subst s
      by_cases hu : u = i
      · subst u
        have hv : v ≠ j := by
          intro hv
          subst v
          exact hq rfl
        simp [sourceCoeff, PowerSeries.coeff_monomial, hv]
      · simp [sourceCoeff, PowerSeries.coeff_monomial, hu]
    · simp [sourceCoeff, hs]

/-- Scalar multiplication commutes with extracting a Taylor--Laurent coefficient. -/
@[simp] lemma sourceCoeff_smul (c : F)
    (x : LaurentSeries (PowerSeries (PowerSeries F))) (q : Source) :
    sourceCoeff (c • x) q = c * sourceCoeff x q := by
  simp [sourceCoeff]

/-- The entrywise realization is linear over the coordinate coefficient field. -/
lemma realize_smul (c : F) (x : LaurentSeries (PowerSeries (PowerSeries F))) :
    realize p (c • x) = c • realize p x := by
  rw [Algebra.smul_def]
  apply Controlled.ext
  intro a b
  change entries p (c • x) a b =
    product (scalarMatrix c) (realize p x).entries a b
  rw [scalar_product]
  change (∑ᶠ q : Source, sourceCoeff (c • x) q *
    normalMonomialMatrix p q.1.1 q.1.2 q.2 a b) = c * entries p x a b
  simp only [sourceCoeff_smul, mul_assoc, entries]
  rw [mul_finsum]

/-- The normal-order construction bundled as a linear map. Multiplicativity is
the additional obligation needed for the symbol-realization ring homomorphism. -/
noncomputable def realizeLinearMap (hp : 0 < p) :
    LaurentSeries (PowerSeries (PowerSeries F)) →ₗ[F] Controlled (InLattice p) F where
  toFun := realize p
  map_add' := realize_add p hp
  map_smul' := realize_smul p

/-- The full coefficient-weighted expansion of a product entry has finite
support. Thus reordering both source sums and the intermediate-index sum
requires no convergence assumption. -/
theorem finite_product_entry_support (hp : 0 < p)
    (x y : LaurentSeries (PowerSeries (PowerSeries F))) (a b : Index (InLattice p)) :
    (Function.support (fun q : Index (InLattice p) × (Source × Source) ↦
      (sourceCoeff x q.2.1 *
        normalMonomialMatrix p q.2.1.1.1 q.2.1.1.2 q.2.1.2 a q.1) *
      (sourceCoeff y q.2.2 *
        normalMonomialMatrix p q.2.2.1.1 q.2.2.1.2 q.2.2.2 q.1 b))).Finite := by
  apply (finite_normalMonomial_product_sources (F := F) p hp
    (-x.order) (-y.order) a b).subset
  intro q hq
  have hleft := left_ne_zero_of_mul hq
  have hright := right_ne_zero_of_mul hq
  refine ⟨?_, ?_, right_ne_zero_of_mul hleft, right_ne_zero_of_mul hright⟩
  · by_contra! h
    exact left_ne_zero_of_mul hleft
      (sourceCoeff_eq_zero_of_lt x x.order
        (fun _ hn ↦ coeff_eq_zero_of_lt_order hn) q.2.1 h)
  · by_contra! h
    exact left_ne_zero_of_mul hright
      (sourceCoeff_eq_zero_of_lt y y.order
        (fun _ hn ↦ coeff_eq_zero_of_lt_order hn) q.2.2 h)

end MakarLimanov.MatrixRealization
