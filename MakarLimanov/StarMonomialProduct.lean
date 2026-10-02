import MakarLimanov.SymbolSeries
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Finite star products of monomials with an Euler eigen-coefficient

At denominator one, an `η`-eigenvector of eigenvalue `Q` placed at Laurent
index `Q-d` has a nilpotent `Δ` orbit of length `d+1`.  Its star product with
a second monomial is therefore a finite binomial sum.
-/

namespace MakarLimanov.StarMonomialProduct

open HahnSeries SymbolSeries

attribute [local instance 2000] HahnSeries.instAlgebra

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

omit [CharZero F] in
/-- Coefficient derivations iterate without changing the Laurent index. -/
theorem coefficientDerivation_iterate_single
    (δ : Derivation k F F) (n : ℤ) (a : F) (i : ℕ) :
    (coefficientDerivation δ)^[i] (single n a) = single n (δ^[i] a) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, coefficientDerivation_single,
      Function.iterate_succ_apply']

/-- The falling factorial formula for `Δ` on an Euler eigen-coefficient. -/
theorem deltaOperator_iterate_single_eigen
    (η : Derivation k F F) (Q : ℤ) (d : ℕ) (a : F)
    (ha : η a = (Q : F) * a) (i : ℕ) :
    (deltaOperator 1 η)^[i] (single (Q - (d : ℤ)) a) =
      single (Q - (d : ℤ) + (i : ℤ)) ((d.descFactorial i : F) * a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, deltaOperator_single]
    simp only [Nat.cast_one, inv_one, one_mul]
    have hind : Q - (d : ℤ) + (i : ℤ) + 1 = Q - (d : ℤ) + (i + 1 : ℕ) := by
      push_cast
      ring
    rw [hind]
    congr 1
    by_cases hid : i ≤ d
    · simp only [Derivation.leibniz, Derivation.map_natCast, smul_eq_mul, mul_zero,
        add_zero, ha, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hid,
        Int.cast_add, Int.cast_sub, Int.cast_natCast]
      ring
    · have hz : d.descFactorial i = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hid)
      simp [hz]

/-- Every `Δ` iterate above the nonnegative differential degree vanishes. -/
theorem deltaOperator_iterate_single_eigen_eq_zero
    (η : Derivation k F F) (Q : ℤ) (d : ℕ) (a : F)
    (ha : η a = (Q : F) * a) (i : ℕ) (hi : d < i) :
    (deltaOperator 1 η)^[i] (single (Q - (d : ℤ)) a) = 0 := by
  rw [deltaOperator_iterate_single_eigen η Q d a ha i,
    Nat.descFactorial_eq_zero_iff_lt.mpr hi]
  simp

private theorem iterate_derivation_zero
    {R : Type*} [CommRing R] [Algebra k R]
    (D : Derivation k R R) (i : ℕ) : D^[i] 0 = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Function.iterate_succ_apply', ih, map_zero]

private theorem iterate_derivation_eq_zero_of_le
    {R : Type*} [CommRing R] [Algebra k R]
    (D : Derivation k R R) (a : R) (m i : ℕ)
    (hm : D^[m] a = 0) (hi : m ≤ i) : D^[i] a = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_comm, Function.iterate_add_apply, hm, iterate_derivation_zero]

omit [CharZero F] in
/-- A nilpotent left `Δ` orbit truncates the star product at its nilpotence
degree, independently of the right series. -/
theorem starProduct_eq_sum_of_delta_nilpotent
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y : LaurentSeries F) (m : ℕ)
    (hm : (deltaOperator p η)^[m + 1] x = 0) :
    starProduct p hp δ η x y = ∑ i ∈ Finset.range (m + 1), starTerm p δ η x y i := by
  ext n
  rw [starProduct_coeff, coeff_sum]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  have hz := iterate_derivation_eq_zero_of_le (deltaOperator p η) x (m + 1) i hm
    (Nat.le_of_not_gt hn)
  exact hi (by simp [starTerm, hz])

omit [CharZero F] in
/-- A nilpotent right coefficient-derivation orbit also gives an exact finite
star-product sum. -/
theorem starProduct_eq_sum_of_coefficient_nilpotent
    (p : ℕ) (hp : 0 < p) (δ η : Derivation k F F)
    (x y : LaurentSeries F) (m : ℕ)
    (hm : (coefficientDerivation δ)^[m + 1] y = 0) :
    starProduct p hp δ η x y = ∑ i ∈ Finset.range (m + 1), starTerm p δ η x y i := by
  ext n
  rw [starProduct_coeff, coeff_sum]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  have hz := iterate_derivation_eq_zero_of_le (coefficientDerivation δ) y (m + 1) i hm
    (Nat.le_of_not_gt hn)
  exact hi (by simp [starTerm, hz])

/-- The individual star summands have binomial coefficients when the left
monomial has a nonnegative differential degree. -/
theorem starTerm_single_eigen
    (δ η : Derivation k F F) (Q : ℤ) (d : ℕ) (a b : F)
    (ha : η a = (Q : F) * a) (n : ℤ) (i : ℕ) :
    starTerm 1 δ η (single (Q - (d : ℤ)) a) (single n b) i =
      single (Q - (d : ℤ) + n + (i : ℤ))
        ((d.choose i : F) * a * δ^[i] b) := by
  rw [starTerm, deltaOperator_iterate_single_eigen η Q d a ha i,
    coefficientDerivation_iterate_single, single_mul_single]
  have hindex : Q - (d : ℤ) + (i : ℤ) + n = Q - (d : ℤ) + n + (i : ℤ) := by
    ring
  rw [hindex]
  have hf : (i.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  ext j
  by_cases hj : j = Q - (d : ℤ) + n + (i : ℤ)
  · simp [coeff_smul, hj, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul, smul_eq_mul, hf, mul_assoc]
  · simp [coeff_smul, hj]

/-- Formula (3.3) in an abstract Euler eigen-coefficient form; the left
nilpotence alone makes the product a finite sum. -/
theorem starProduct_single_eigen
    (δ η : Derivation k F F) (Q : ℤ) (d : ℕ) (a b : F)
    (ha : η a = (Q : F) * a) (n : ℤ) :
    starProduct 1 (by decide) δ η (single (Q - (d : ℤ)) a) (single n b) =
      ∑ i ∈ Finset.range (d + 1),
        single (Q - (d : ℤ) + n + (i : ℤ))
          ((d.choose i : F) * a * δ^[i] b) := by
  rw [starProduct_eq_sum_of_delta_nilpotent 1 (by decide) δ η _ _ d
    (deltaOperator_iterate_single_eigen_eq_zero η Q d a ha (d + 1) (by omega))]
  apply Finset.sum_congr rfl
  intro i hi
  exact starTerm_single_eigen δ η Q d a b ha n i

/-- Right coefficient nilpotence can give a shorter finite monomial sum. -/
theorem starProduct_single_eigen_of_right_nilpotent
    (δ η : Derivation k F F) (Q : ℤ) (d : ℕ) (a b : F)
    (ha : η a = (Q : F) * a) (n : ℤ) (m : ℕ)
    (hm : δ^[m + 1] b = 0) :
    starProduct 1 (by decide) δ η (single (Q - (d : ℤ)) a) (single n b) =
      ∑ i ∈ Finset.range (m + 1),
        single (Q - (d : ℤ) + n + (i : ℤ))
          ((d.choose i : F) * a * δ^[i] b) := by
  have hright : (coefficientDerivation δ)^[m + 1] (single n b) = 0 := by
    rw [coefficientDerivation_iterate_single, hm, map_zero]
  rw [starProduct_eq_sum_of_coefficient_nilpotent 1 (by decide) δ η _ _ m hright]
  apply Finset.sum_congr rfl
  intro i hi
  exact starTerm_single_eigen δ η Q d a b ha n i

/-- Both nilpotence bounds may be used simultaneously. -/
theorem starProduct_single_eigen_sum_min
    (δ η : Derivation k F F) (Q : ℤ) (d : ℕ) (a b : F)
    (ha : η a = (Q : F) * a) (n : ℤ) (m : ℕ)
    (hm : δ^[m + 1] b = 0) :
    starProduct 1 (by decide) δ η (single (Q - (d : ℤ)) a) (single n b) =
      ∑ i ∈ Finset.range (min d m + 1),
        single (Q - (d : ℤ) + n + (i : ℤ))
          ((d.choose i : F) * a * δ^[i] b) := by
  rw [starProduct_single_eigen δ η Q d a b ha n]
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono (by omega)
  · intro i hi hnot
    have hid : i < d + 1 := Finset.mem_range.mp hi
    have hmi : m + 1 ≤ i := by
      have hmin : ¬ i < min d m + 1 := by simpa only [Finset.mem_range] using hnot
      omega
    have hz := iterate_derivation_eq_zero_of_le δ b (m + 1) i hm hmi
    simp [hz]

end

end MakarLimanov.StarMonomialProduct
