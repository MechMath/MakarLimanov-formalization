import MakarLimanov.TaylorCoordinates
import MakarLimanov.MatrixRealization

/-!
# Coordinate monomials and their derivatives

These formulas identify the coordinate differential operators with the
commutators used in the concrete normal-order matrix construction.
-/

namespace MakarLimanov.TaylorCoordinates

open HahnSeries

variable {F : Type*} [Field F]

/-- A finite source monomial, with `r` the scaled upper Laurent exponent. -/
noncomputable def coordinateMonomial (i j : ℕ) (r : ℤ) (c : F) :
    LaurentSeries (BiSeries F) :=
  single (-r) (PowerSeries.monomial i (PowerSeries.monomial j c))

@[simp] lemma realize_coordinateMonomial (p : ℕ) (i j : ℕ) (r : ℤ) (c : F) :
    MatrixRealization.realize p (coordinateMonomial i j r c) =
      algebraMap F (ControlledMatrix.Controlled (Lattice.InLattice p) F) c *
        Lattice.normalMonomialMatrix p i j r :=
  MatrixRealization.realize_monomial p i j r c

/-- Ordinary coordinate multiplication simply adds all three exponents. -/
lemma coordinateMonomial_mul (i j u v : ℕ) (r s : ℤ) (c d : F) :
    coordinateMonomial i j r c * coordinateMonomial u v s d =
      coordinateMonomial (i + u) (j + v) (r + s) (c * d) := by
  simp [coordinateMonomial, single_mul_single, PowerSeries.monomial_mul_monomial, add_comm]

/-- Coefficients of a source monomial scale over the coordinate coefficient field. -/
lemma coordinateMonomial_smul (i j : ℕ) (r : ℤ) (a c : F) :
    a • coordinateMonomial i j r c = coordinateMonomial i j r (a * c) := by
  ext n u v
  by_cases hn : n = -r <;> by_cases hu : u = i <;> by_cases hv : v = j <;>
    simp [coordinateMonomial, hn, hu, hv, PowerSeries.coeff_monomial]

/-- A constant Laurent coefficient is the scalar action from the coefficient field. -/
lemma coordinateConstant_mul (c : F) (x : LaurentSeries (BiSeries F)) :
    single 0 (PowerSeries.C (PowerSeries.C c)) * x = c • x := by
  ext n u v
  simp only [coeff_single_mul, zero_add, sub_zero, PowerSeries.coeff_C_mul]
  simp

/-- Coefficient-field scalars commute with coordinate multiplication. -/
lemma coordinate_mul_smul (x y : LaurentSeries (BiSeries F)) (c : F) :
    x * (c • y) = c • (x * y) := by
  rw [← coordinateConstant_mul c y, ← coordinateConstant_mul c (x * y)]
  ring

lemma derivative_monomial_succ (n : ℕ) (c : F) :
    PowerSeries.derivative F (PowerSeries.monomial (n + 1) c) =
      PowerSeries.monomial n (c * (n + 1)) := by
  ext m
  rw [PowerSeries.coeff_derivative]
  by_cases hm : m = n
  · subst m
    simp
  · have hs : m + 1 ≠ n + 1 := by omega
    simp [PowerSeries.coeff_monomial, hm, hs]

lemma partialW_monomial (i : ℕ) (x : PowerSeries F) :
    partialW (PowerSeries.monomial i x) =
      PowerSeries.monomial i (PowerSeries.derivative F x) := by
  ext n
  by_cases hn : n = i <;> simp [PowerSeries.coeff_monomial, hn]

lemma partialT_monomial_succ (i : ℕ) (x : PowerSeries F) :
    partialT (PowerSeries.monomial (i + 1) x) =
      PowerSeries.monomial i (x * (i + 1)) := by
  ext n
  rw [coeff_partialT]
  by_cases hn : n = i
  · subst n
    simp
  · have hs : n + 1 ≠ i + 1 := by omega
    simp [PowerSeries.coeff_monomial, hn, hs]

@[simp] lemma partialT_monomial_zero (x : PowerSeries F) :
    partialT (PowerSeries.monomial 0 x) = 0 := by
  ext n
  simp [PowerSeries.coeff_monomial]

lemma coordinateT_monomial_succ (i j : ℕ) (r : ℤ) (c : F) :
    coordinateT (coordinateMonomial (i + 1) j r c) =
      coordinateMonomial i j r (c * (i + 1)) := by
  ext n u v
  by_cases hn : n = -r
  · subst n
    simp only [coordinateT_coeff, coordinateMonomial, coeff_single_same,
      partialT_monomial_succ]
    by_cases hu : u = i
    · subst u
      rw [PowerSeries.coeff_monomial_same, PowerSeries.coeff_monomial_same]
      rw [← Nat.cast_add_one, mul_comm, ← nsmul_eq_mul]
      rw [map_nsmul]
      simp [PowerSeries.coeff_monomial, nsmul_eq_mul, mul_comm]
    · simp [PowerSeries.coeff_monomial, hu]
  · simp [coordinateMonomial, hn]

@[simp] lemma coordinateT_monomial_zero (j : ℕ) (r : ℤ) (c : F) :
    coordinateT (coordinateMonomial 0 j r c) = 0 := by
  ext n
  by_cases hn : n = -r <;> simp [coordinateMonomial, hn]

@[simp] lemma coordinateMonomial_zero (i j : ℕ) (r : ℤ) :
    coordinateMonomial (F := F) i j r 0 = 0 := by
  simp [coordinateMonomial]

/-- Iterated `t` differentiation has the falling-factorial coefficient. -/
lemma coordinateT_iterate_monomial (k j : ℕ) (r : ℤ) (c : F) (n : ℕ) :
    coordinateT^[n] (coordinateMonomial k j r c) =
      coordinateMonomial (k - n) j r (c * (k.descFactorial n : F)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Nat.descFactorial_succ, Nat.cast_mul]
    by_cases hn : n < k
    · have he : k - n = (k - (n + 1)) + 1 := by omega
      rw [he, coordinateT_monomial_succ]
      congr 1
      rw [← Nat.cast_add_one, ← he]
      ring
    · have he : k - n = 0 := by omega
      have he' : k - (n + 1) = 0 := by omega
      simp [he, he']

/-- A monomial's higher `t` derivatives vanish past its `t` degree. -/
lemma coordinateT_iterate_monomial_of_lt (k j : ℕ) (r : ℤ) (c : F)
    {n : ℕ} (hn : k < n) :
    coordinateT^[n] (coordinateMonomial k j r c) = 0 := by
  rw [coordinateT_iterate_monomial, Nat.descFactorial_of_lt hn]
  simp

lemma derivative_monomial (n : ℕ) (c : F) :
    PowerSeries.derivative F (PowerSeries.monomial n c) =
      PowerSeries.monomial (n - 1) (c * n) := by
  cases n with
  | zero => simp [PowerSeries.monomial_zero_eq_C_apply]
  | succ n => simpa using derivative_monomial_succ n c

lemma coordinateDelta_monomial (p i j : ℕ) (r : ℤ) (c : F) :
    coordinateDelta p (coordinateMonomial i j r c) =
      coordinateMonomial i (j - 1) (r - p) (c * j) +
        coordinateMonomial i j (r - p) ((r : F) / (p : F) * c) := by
  ext n u v
  by_cases hn : n = -(r - p)
  · subst n
    have he : -(r - (p : ℤ)) - p = -r := by ring
    simp only [coordinateDelta_coeff, he, coordinateMonomial, coeff_single_same,
      partialW_monomial, derivative_monomial, coeff_add]
    have hr : (r : BiSeries F) = PowerSeries.C (PowerSeries.C (r : F)) := by simp
    rw [Int.cast_neg, hr, mul_neg, neg_mul, sub_neg_eq_add, ← map_mul]
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_monomial]
    by_cases hu : u = i
    · subst u
      simp only [ite_true, ← map_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_monomial]
      split_ifs <;>
        simp only [div_eq_mul_inv, mul_zero, zero_mul, add_zero, zero_add] <;> ring
    · simp [hu]
  · have he : n - (p : ℤ) ≠ -r := by omega
    have hn' : n ≠ (p : ℤ) - r := by omega
    simp [coordinateDelta_coeff, coordinateMonomial, hn', he]

end MakarLimanov.TaylorCoordinates

namespace MakarLimanov.TaylorCoordinates

open HahnSeries

variable {F : Type*} [Field F]

@[simp] lemma coordinateDelta_zero (p : ℕ) :
    coordinateDelta p (0 : LaurentSeries (BiSeries F)) = 0 := by
  ext n
  simp [coordinateDelta_coeff]

lemma coordinateDelta_add (p : ℕ) (x y : LaurentSeries (BiSeries F)) :
    coordinateDelta p (x + y) = coordinateDelta p x + coordinateDelta p y := by
  apply HahnSeries.ext
  funext n
  simp only [coordinateDelta_coeff, coeff_add, map_add]
  ring

/-- The coordinate derivative bundled additively, for finite source expansions. -/
noncomputable def coordinateDeltaAddHom (p : ℕ) :
    LaurentSeries (BiSeries F) →+ LaurentSeries (BiSeries F) where
  toFun := coordinateDelta p
  map_zero' := coordinateDelta_zero p
  map_add' := coordinateDelta_add p

/-- Finite coordinate expressions are finite sums of Taylor--Laurent monomials. -/
inductive FiniteCoordinate : LaurentSeries (BiSeries F) → Prop
  | zero : FiniteCoordinate 0
  | monomial (i j : ℕ) (r : ℤ) (c : F) :
      FiniteCoordinate (coordinateMonomial i j r c)
  | add {x y : LaurentSeries (BiSeries F)} :
      FiniteCoordinate x → FiniteCoordinate y → FiniteCoordinate (x + y)

/-- Multiplication by a monomial preserves finite coordinate expressions. -/
theorem FiniteCoordinate.mul_monomial {x : LaurentSeries (BiSeries F)}
    (hx : FiniteCoordinate x) (i j : ℕ) (r : ℤ) (c : F) :
    FiniteCoordinate (x * coordinateMonomial i j r c) := by
  induction hx with
  | zero => simpa using (FiniteCoordinate.zero (F := F))
  | monomial u v s d =>
    rw [coordinateMonomial_mul]
    exact .monomial _ _ _ _
  | add hx hy ihx ihy =>
    rw [add_mul]
    exact .add ihx ihy

/-- The product of two finite coordinate expressions is finite. -/
theorem FiniteCoordinate.mul {x y : LaurentSeries (BiSeries F)}
    (hx : FiniteCoordinate x) (hy : FiniteCoordinate y) : FiniteCoordinate (x * y) := by
  induction hy with
  | zero => simpa using (FiniteCoordinate.zero (F := F))
  | monomial i j r c => exact hx.mul_monomial i j r c
  | add hy hz ihy ihz =>
    rw [mul_add]
    exact .add ihy ihz

/-- Coordinate differentiation keeps a finite expression finite. -/
theorem FiniteCoordinate.coordinateDelta {x : LaurentSeries (BiSeries F)}
    (hx : FiniteCoordinate x) (p : ℕ) : FiniteCoordinate (coordinateDelta p x) := by
  induction hx with
  | zero => simpa using (FiniteCoordinate.zero (F := F))
  | monomial i j r c =>
    rw [coordinateDelta_monomial]
    exact .add (.monomial _ _ _ _) (.monomial _ _ _ _)
  | add hx hy ihx ihy =>
    rw [coordinateDelta_add]
    exact .add ihx ihy

/-- Every iterate used in normal ordering has a finite coordinate expansion. -/
theorem FiniteCoordinate.coordinateDelta_iterate {x : LaurentSeries (BiSeries F)}
    (hx : FiniteCoordinate x) (p n : ℕ) :
    FiniteCoordinate ((TaylorCoordinates.coordinateDelta p)^[n] x) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using ih.coordinateDelta p

end MakarLimanov.TaylorCoordinates
