import MakarLimanov.FiniteRealization

/-!
# The finite normal-order product

When the right input is a coordinate monomial, the infinite diamond product
reduces to the finite binomial normal-order formula.
-/

namespace MakarLimanov.TaylorCoordinates

open HahnSeries Finset

variable {F : Type*} [Field F] [CharZero F]

lemma factorial_inv_mul_descFactorial (k n : ℕ) :
    (n.factorial : F)⁻¹ * (k.descFactorial n : F) = (k.choose n : F) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_mul]

/-- Each nonzero diamond summand has precisely the normal-order binomial coefficient. -/
lemma diamondTerm_right_monomial (p k j : ℕ) (r : ℤ) (c : F)
    (x : LaurentSeries (BiSeries F)) (n : ℕ) :
    diamondTerm p x (coordinateMonomial k j r c) n =
      k.choose n • ((coordinateDelta p)^[n] x *
        coordinateMonomial (k - n) j r c) := by
  rw [diamondTerm, coordinateConstant_mul, coordinateT_iterate_monomial]
  rw [mul_comm c (k.descFactorial n : F), ← coordinateMonomial_smul,
    coordinate_mul_smul, smul_smul, factorial_inv_mul_descFactorial]
  exact Nat.cast_smul_eq_nsmul F (k.choose n) _

/-- No right-monomial summand survives past its outer Taylor degree. -/
lemma diamondTerm_right_monomial_of_lt (p k j : ℕ) (r : ℤ) (c : F)
    (x : LaurentSeries (BiSeries F)) {n : ℕ} (hn : k < n) :
    diamondTerm p x (coordinateMonomial k j r c) n = 0 := by
  rw [diamondTerm_right_monomial, Nat.choose_eq_zero_of_lt hn, zero_nsmul]

/-- The infinite coordinate product is a finite sum when its right input is a monomial. -/
theorem diamond_right_monomial (p : ℕ) (hp : 0 < p) (k j : ℕ) (r : ℤ) (c : F)
    (x : LaurentSeries (BiSeries F)) :
    diamond p hp x (coordinateMonomial k j r c) =
      ∑ n ∈ Finset.range (k + 1), k.choose n •
        ((coordinateDelta p)^[n] x * coordinateMonomial (k - n) j r c) := by
  apply HahnSeries.ext
  funext m
  change (∑ᶠ n, (diamondTerm p x (coordinateMonomial k j r c) n).coeff m) = _
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (k + 1)) _]
  · simp only [coeff_sum, diamondTerm_right_monomial]
  · intro n hn
    by_contra! h
    have hkn : k < n := by simpa using h
    apply hn
    change (diamondTerm p x (coordinateMonomial k j r c) n).coeff m = 0
    rw [diamondTerm_right_monomial_of_lt p k j r c x hkn]
    simp

end MakarLimanov.TaylorCoordinates

namespace MakarLimanov.TaylorCoordinates

open HahnSeries

variable {F : Type*} [Field F] [CharZero F]

lemma coordinateT_add (x y : LaurentSeries (BiSeries F)) :
    coordinateT (x + y) = coordinateT x + coordinateT y := by
  apply HahnSeries.ext
  funext n
  simp

lemma coordinateT_iterate_add (x y : LaurentSeries (BiSeries F)) (n : ℕ) :
    coordinateT^[n] (x + y) = coordinateT^[n] x + coordinateT^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, coordinateT_add]

@[simp] lemma coordinateT_iterate_zero (n : ℕ) :
    coordinateT^[n] (0 : LaurentSeries (BiSeries F)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    apply HahnSeries.ext
    funext m
    simp

lemma diamondTerm_add_right (p : ℕ) (x y z : LaurentSeries (BiSeries F)) (n : ℕ) :
    diamondTerm p x (y + z) n = diamondTerm p x y n + diamondTerm p x z n := by
  simp only [diamondTerm, coordinateT_iterate_add, mul_add]

/-- Additivity of the infinite coordinate product in its right input. -/
lemma diamond_add_right (p : ℕ) (hp : 0 < p) (x y z : LaurentSeries (BiSeries F)) :
    diamond p hp x (y + z) = diamond p hp x y + diamond p hp x z := by
  apply HahnSeries.ext
  funext m
  change (∑ᶠ n, (diamondTerm p x (y + z) n).coeff m) =
    (∑ᶠ n, (diamondTerm p x y n).coeff m) +
      (∑ᶠ n, (diamondTerm p x z n).coeff m)
  simp only [diamondTerm_add_right, coeff_add]
  exact finsum_add_distrib ((diamondFamily p hp x y).finite_co_support m)
    ((diamondFamily p hp x z).finite_co_support m)

@[simp] lemma diamond_zero_right (p : ℕ) (hp : 0 < p) (x : LaurentSeries (BiSeries F)) :
    diamond p hp x 0 = 0 := by
  apply HahnSeries.ext
  funext m
  change (∑ᶠ n, (diamondTerm p x 0 n).coeff m) = 0
  simp [diamondTerm]

end MakarLimanov.TaylorCoordinates

namespace MakarLimanov.MatrixRealization

open ControlledMatrix Lattice TaylorCoordinates Finset

variable {F : Type*} [Field F] [CharZero F] (p : ℕ)

/-- The finite matrix normal-order sum, indexed by the number of derivatives. -/
theorem realize_normal_order_range (hp : 0 < p)
    {x : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x) (k : ℕ) :
    realize p x * (tMatrix p) ^ k = ∑ n ∈ Finset.range (k + 1),
      k.choose n • ((tMatrix p) ^ (k - n) *
        realize p ((coordinateDelta p)^[n] x)) := by
  rw [realize_normal_order_finite p hp hx, Finset.Nat.antidiagonal_eq_map', Finset.sum_map]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ k := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  simp only [Function.Embedding.coeFn_mk]
  rw [← Nat.choose_symm hn']

/-- Realization preserves diamond multiplication when the left expression is
finite and the right input is a source monomial. -/
theorem realize_diamond_right_monomial (hp : 0 < p)
    {x : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x)
    (k j : ℕ) (r : ℤ) (c : F) :
    realize p (diamond p hp x (coordinateMonomial k j r c)) =
      realize p x * realize p (coordinateMonomial k j r c) := by
  have hm : realize p (coordinateMonomial k j r c) =
      (tMatrix p) ^ k * realize p (coordinateMonomial 0 j r c) := by
    rw [← realize_left_tPower_finite p hp k (FiniteCoordinate.monomial 0 j r c),
      coordinateMonomial_mul]
    simp
  rw [diamond_right_monomial]
  change (realizeAddHom p hp) (∑ n ∈ Finset.range (k + 1),
    k.choose n • ((coordinateDelta p)^[n] x *
      coordinateMonomial (k - n) j r c)) = _
  rw [map_sum, hm, ← mul_assoc, realize_normal_order_range p hp hx, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  simp only [map_nsmul, smul_mul_assoc]
  congr 1
  exact realize_mul_monomial_finite p hp (k - n) j r c
    (hx.coordinateDelta_iterate p n)

/-- The actual coordinate product is preserved on all finite expressions;
this is the finite-symbol part of the realization lemma. -/
theorem realize_diamond_finite (hp : 0 < p)
    {x y : LaurentSeries (BiSeries F)} (hx : FiniteCoordinate x) (hy : FiniteCoordinate y) :
    realize p (diamond p hp x y) = realize p x * realize p y := by
  induction hy with
  | zero => simp
  | monomial k j r c => exact realize_diamond_right_monomial p hp hx k j r c
  | add hy hz ihy ihz =>
    rw [diamond_add_right, realize_add p hp, realize_add p hp, mul_add, ihy, ihz]

end MakarLimanov.MatrixRealization
