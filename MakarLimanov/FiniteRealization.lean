import MakarLimanov.MatrixRealizationProduct

/-!
# Finite coordinate realization

Left multiplication by powers of `t` and right multiplication by coefficient
monomials have exact normal-order matrix interpretations.
-/

namespace MakarLimanov.Lattice

open ControlledMatrix

variable {F : Type*} [Field F] (p : ℕ)

/-- Right coefficient multiplication does not require a normal-order correction. -/
lemma normalMonomialMatrix_mul_coefficient (i j v : ℕ) (r s : ℤ) :
    normalMonomialMatrix (F := F) p i j r * normalMonomialMatrix p 0 v s =
      normalMonomialMatrix p i (j + v) (r + s) := by
  simp only [normalMonomialMatrix, pow_zero, one_mul, pow_add, mul_assoc]
  rw [← mul_assoc (zMatrix p r) ((wMatrix p) ^ v),
    (zMatrix_commute_wMatrix p r).pow_right v |>.eq, mul_assoc, zMatrix_mul]

end MakarLimanov.Lattice

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice TaylorCoordinates

variable {F : Type*} [Field F] (p : ℕ)

/-- Multiplying a finite expression on the left by `t^u` prefixes its matrix by `T^u`. -/
theorem realize_left_tPower_finite (hp : 0 < p) (u : ℕ)
    {x : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x) :
    realize p (coordinateMonomial u 0 0 1 * x) = (tMatrix p) ^ u * realize p x := by
  induction hx with
  | zero => simp
  | monomial i j r c =>
    rw [coordinateMonomial_mul]
    simp only [zero_add, add_zero, one_mul, realize_coordinateMonomial]
    rw [← mul_assoc, ← Algebra.commutes c ((tMatrix p) ^ u)]
    simp only [normalMonomialMatrix, pow_add, mul_assoc]
  | add hx hy ihx ihy =>
    rw [mul_add, realize_add p hp, realize_add p hp, mul_add, ihx, ihy]

/-- Right multiplication by a `t`-independent monomial is preserved exactly. -/
theorem realize_right_coefficient_finite (hp : 0 < p) (v : ℕ) (s : ℤ) (d : F)
    {x : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x) :
    realize p (x * coordinateMonomial 0 v s d) =
      realize p x * realize p (coordinateMonomial 0 v s d) := by
  induction hx with
  | zero => simp
  | monomial i j r c =>
    rw [coordinateMonomial_mul]
    simp only [add_zero, realize_coordinateMonomial, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (normalMonomialMatrix p i j r),
      ← Algebra.commutes d (normalMonomialMatrix p i j r)]
    simp only [mul_assoc, normalMonomialMatrix_mul_coefficient]
  | add hx hy ihx ihy =>
    rw [add_mul, realize_add p hp, realize_add p hp, add_mul, ihx, ihy]

end MakarLimanov.MatrixRealization

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice TaylorCoordinates

variable {F : Type*} [Field F] (p : ℕ)

/-- Ordinary multiplication by a source monomial has its `t` power on the
left and its coefficient-coordinate matrix on the right after realization. -/
theorem realize_mul_monomial_finite (hp : 0 < p) (u v : ℕ) (s : ℤ) (d : F)
    {x : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x) :
    realize p (x * coordinateMonomial u v s d) =
      (tMatrix p) ^ u * realize p x * realize p (coordinateMonomial 0 v s d) := by
  have hm : coordinateMonomial u v s d =
      coordinateMonomial u 0 0 1 * coordinateMonomial 0 v s d := by
    rw [coordinateMonomial_mul]
    simp
  rw [hm, ← mul_assoc, mul_comm x (coordinateMonomial u 0 0 1),
    realize_right_coefficient_finite p hp v s d
      ((FiniteCoordinate.monomial u 0 0 1).mul hx),
    realize_left_tPower_finite p hp u hx]

end MakarLimanov.MatrixRealization
