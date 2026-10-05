import MakarLimanov.MatrixRealization
import MakarLimanov.NormalOrdering
import MakarLimanov.TaylorCoordinates
import MakarLimanov.CoordinateMonomials

/-!
# Finite rearrangements for the normal-order realization product

Although a realized matrix need not have finite rows or columns, its product
entries admit a finite expansion in pairs of source monomials.
-/

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice HahnSeries

variable {F : Type*} [Field F] (p : ℕ)

/-- Expanding a matrix product into its intermediate index and two source indices. -/
theorem product_entry_expansion (hp : 0 < p)
    (x y : LaurentSeries (PowerSeries (PowerSeries F))) (a b : Index (InLattice p)) :
    (realize p x * realize p y) a b =
      ∑ᶠ q : Index (InLattice p) × (Source × Source),
        (sourceCoeff x q.2.1 *
          normalMonomialMatrix p q.2.1.1.1 q.2.1.1.2 q.2.1.2 a q.1) *
        (sourceCoeff y q.2.2 *
          normalMonomialMatrix p q.2.2.1.1 q.2.2.1.2 q.2.2.2 q.1 b) := by
  rw [Controlled.mul_apply]
  simp only [realize_apply, entries]
  simp_rw [finsum_mul, mul_finsum]
  exact (finsum_curry₃ _ (finite_product_entry_support p hp x y a b)).symm

/-- A product entry is the finite sum of products of the normal-ordered
monomial matrices, weighted by the two source coefficients. -/
theorem product_entry_source_pairs (hp : 0 < p)
    (x y : LaurentSeries (PowerSeries (PowerSeries F))) (a b : Index (InLattice p)) :
    (realize p x * realize p y) a b =
      ∑ᶠ q : Source × Source, (sourceCoeff x q.1 * sourceCoeff y q.2) *
        (normalMonomialMatrix (F := F) p q.1.1.1 q.1.1.2 q.1.2 *
          normalMonomialMatrix p q.2.1.1 q.2.1.2 q.2.2 :
            Controlled (InLattice p) F) a b := by
  let f : Index (InLattice p) × (Source × Source) → F := fun q ↦
    (sourceCoeff x q.2.1 *
      normalMonomialMatrix p q.2.1.1.1 q.2.1.1.2 q.2.1.2 a q.1) *
    (sourceCoeff y q.2.2 *
      normalMonomialMatrix p q.2.2.1.1 q.2.2.1.2 q.2.2.2 q.1 b)
  have hf : (Function.support f).Finite := finite_product_entry_support p hp x y a b
  have hs : (Function.support (fun q : (Source × Source) × Index (InLattice p) ↦
      f q.swap)).Finite :=
    hf.preimage (f := Prod.swap) (Equiv.prodComm _ _).injective.injOn
  rw [product_entry_expansion p hp x y a b]
  change (∑ᶠ q, f q) = _
  rw [← finsum_eq_of_bijective Prod.swap (Equiv.prodComm _ _).bijective
    (fun _ ↦ rfl), finsum_curry _ hs]
  apply finsum_congr
  intro q
  rw [Controlled.mul_apply, mul_finsum]
  apply finsum_congr
  intro k
  dsimp [f]
  ring

end MakarLimanov.MatrixRealization

namespace MakarLimanov.Lattice

open ControlledMatrix

variable {F : Type*} [Field F] (p : ℕ)

/-- Normal ordering a power of the polynomial coordinate against `T`. -/
theorem wMatrix_pow_tMatrix (hp : 0 < p) (j : ℕ) :
    (wMatrix (K := F) p) ^ j * tMatrix p =
      tMatrix p * (wMatrix p) ^ j +
        j • ((wMatrix p) ^ (j - 1) * zMatrix p (-(p : ℤ))) := by
  cases j with
  | zero => simp
  | succ j =>
    have hcomm : wMatrix (K := F) p * tMatrix p =
        tMatrix p * wMatrix p + zMatrix p (-(p : ℤ)) := by
      simpa only [add_comm] using
        (sub_eq_iff_eq_add.mp (wMatrix_tMatrix_commutator (F := F) p hp))
    simpa using NormalOrdering.pow_commutator (wMatrix (K := F) p) (tMatrix p)
      (zMatrix p (-(p : ℤ))) hcomm (zMatrix_commute_wMatrix p (-(p : ℤ))).symm j

/-- The Laurent coordinate has the required additive normal-order identity. -/
theorem zMatrix_tMatrix_normal_order (r : ℤ) :
    zMatrix (K := F) p r * tMatrix p = tMatrix p * zMatrix p r +
      algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F)) *
        zMatrix p (r - p) := by
  simpa only [add_comm] using
    (sub_eq_iff_eq_add.mp (zMatrix_tMatrix_commutator_general (F := F) p r))

/-- The matrix commutator reproduces the two terms of the coordinate `Δ`
derivative of every source monomial. -/
theorem normalMonomialMatrix_tMatrix (hp : 0 < p) (i j : ℕ) (r : ℤ) :
    normalMonomialMatrix (F := F) p i j r * tMatrix p =
      tMatrix p * normalMonomialMatrix p i j r +
        j • normalMonomialMatrix p i (j - 1) (r - p) +
        algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F)) *
          normalMonomialMatrix p i j (r - p) := by
  let T := tMatrix (F := F) p
  let W := wMatrix (K := F) p
  let C := algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F))
  have ht : T ^ i * T = T * T ^ i := (Commute.refl T).pow_left i |>.eq
  have hcW : W ^ j * C = C * W ^ j :=
    (Algebra.commutes ((r : F) / (p : F)) (W ^ j)).symm
  have hcT : T ^ i * C = C * T ^ i :=
    (Algebra.commutes ((r : F) / (p : F)) (T ^ i)).symm
  change (T ^ i * W ^ j * zMatrix p r) * T =
    T * (T ^ i * W ^ j * zMatrix p r) +
      j • (T ^ i * W ^ (j - 1) * zMatrix p (r - p)) +
      C * (T ^ i * W ^ j * zMatrix p (r - p))
  calc
    _ = T ^ i * ((W ^ j * T) * zMatrix p r) +
        T ^ i * (W ^ j * (C * zMatrix p (r - p))) := by
      have hz := zMatrix_tMatrix_normal_order (F := F) p r
      change zMatrix p r * T = T * zMatrix p r + C * zMatrix p (r - p) at hz
      rw [mul_assoc, hz]
      noncomm_ring
    _ = T ^ i * ((T * W ^ j + j • (W ^ (j - 1) *
        zMatrix p (-(p : ℤ)))) * zMatrix p r) +
        T ^ i * (W ^ j * (C * zMatrix p (r - p))) := by
      rw [wMatrix_pow_tMatrix p hp]
    _ = _ := by
      simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, mul_assoc,
        zMatrix_mul]
      rw [show -(p : ℤ) + r = r - p by omega]
      rw [← mul_assoc (W ^ j) C, hcW, mul_assoc C,
        ← mul_assoc (T ^ i) C, hcT]
      rw [← mul_assoc (T ^ i) T, ht]
      simp only [mul_assoc]

end MakarLimanov.Lattice

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice TaylorCoordinates

variable {F : Type*} [Field F] (p : ℕ)

/-- On a source monomial the coordinate derivative is exactly the matrix
commutator, including its coefficient. -/
theorem realize_coordinateDelta_monomial (hp : 0 < p)
    (i j : ℕ) (r : ℤ) (c : F) :
    realize p (coordinateMonomial i j r c) * tMatrix p =
      tMatrix p * realize p (coordinateMonomial i j r c) +
        realize p (coordinateDelta p (coordinateMonomial i j r c)) := by
  rw [coordinateDelta_monomial, realize_add p hp]
  simp only [realize_coordinateMonomial, map_mul, map_natCast]
  rw [mul_assoc, normalMonomialMatrix_tMatrix p hp]
  have hc := Algebra.commutes (A := Controlled (InLattice p) F) c (tMatrix p)
  simp only [mul_add, mul_smul_comm, nsmul_eq_mul]
  rw [← mul_assoc (tMatrix p), ← hc]
  rw [← mul_assoc (algebraMap F (Controlled (InLattice p) F) c)
    (algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F))),
    Algebra.commutes c
      (algebraMap F (Controlled (InLattice p) F) ((r : F) / (p : F))), mul_assoc]
  noncomm_ring

/-- The commutator identity extends to every finite coordinate expression. -/
theorem realize_coordinateDelta_finite (hp : 0 < p)
    {x : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x) :
    realize p x * tMatrix p = tMatrix p * realize p x +
      realize p (coordinateDelta p x) := by
  induction hx with
  | zero => simp
  | monomial i j r c => exact realize_coordinateDelta_monomial p hp i j r c
  | add hx hy ihx ihy =>
    rw [realize_add p hp, coordinateDelta_add, realize_add p hp]
    rw [add_mul, mul_add, ihx, ihy]
    abel

/-- The concrete matrix normal-order formula for finite coordinate symbols. -/
theorem realize_normal_order_finite (hp : 0 < p)
    {x : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x) (n : ℕ) :
    realize p x * (tMatrix p) ^ n = ∑ ac ∈ Finset.HasAntidiagonal.antidiagonal n,
      n.choose ac.1 • ((tMatrix p) ^ ac.1 *
        realize p ((coordinateDelta p)^[ac.2] x)) := by
  apply NormalOrdering.normal_order_sequence
    (fun j ↦ realize p ((coordinateDelta p)^[j] x)) (tMatrix p)
  intro j
  simpa only [Function.iterate_succ_apply'] using
    realize_coordinateDelta_finite p hp (hx.coordinateDelta_iterate p j)

end MakarLimanov.MatrixRealization
