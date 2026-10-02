import MakarLimanov.TwoVariableDifferentialField
import MakarLimanov.StarMonomialProduct

/-!
# Concrete finite star monomials

The rational variables carry the partial derivative in `tau` and the Euler derivative in
`upsilon`. Placing `tau^l * upsilon^Q` at Laurent index `Q-d` gives a finite star product
with the usual binomial and falling-factorial coefficients.
-/

noncomputable section

namespace MakarLimanov.ConcreteStarMonomials

open HahnSeries SymbolSeries TwoVariableDifferentialField StarMonomialProduct

attribute [local instance 2000] HahnSeries.instAlgebra

variable {k C : Type*} [Field k] [Field C] [Algebra k C]

/-- The coefficient of a concrete star monomial. -/
def coefficient (l Q : ℕ) : RationalField C := tau ^ l * upsilon ^ Q

/-- The ordinary Laurent series underlying a concrete star monomial. -/
def monomial (l Q d : ℕ) : LaurentSeries (RationalField C) :=
  single ((Q : ℤ) - (d : ℤ)) (coefficient (C := C) l Q)

/-- The Euler derivation reads the second coefficient degree. -/
theorem eta_coefficient (l Q : ℕ) :
    eta (k := k) (C := C) (coefficient l Q) =
      (Q : RationalField C) * coefficient l Q := by
  cases Q with
  | zero => simp [coefficient, Derivation.leibniz_pow]
  | succ Q =>
    simp only [coefficient, Derivation.leibniz, Derivation.leibniz_pow,
      eta_tau, eta_upsilon, smul_eq_mul, mul_zero, Nat.add_sub_cancel]
    rw [pow_succ]
    push_cast
    ring

/-- Differentiating in the first variable lowers the first coefficient degree. -/
theorem delta_coefficient (l Q : ℕ) :
    delta (k := k) (C := C) (coefficient l Q) =
      (l : RationalField C) * coefficient (l - 1) Q := by
  simp only [coefficient, Derivation.leibniz, Derivation.leibniz_pow,
    delta_tau, delta_upsilon, smul_eq_mul, mul_zero, mul_one]
  ring

/-- Iterated partial derivatives are given by a falling factorial. -/
theorem delta_iterate_coefficient (l Q i : ℕ) :
    (delta (k := k) (C := C))^[i] (coefficient l Q) =
      (l.descFactorial i : RationalField C) * coefficient (l - i) Q := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [Derivation.leibniz, Derivation.map_natCast, smul_eq_mul,
      mul_zero, add_zero, delta_coefficient, Nat.descFactorial_succ,
      Nat.cast_mul, Nat.sub_sub]
    ring

/-- Every partial derivative above the first coefficient degree vanishes. -/
theorem delta_iterate_coefficient_eq_zero (l Q i : ℕ) (hi : l < i) :
    (delta (k := k) (C := C))^[i] (coefficient l Q) = 0 := by
  rw [delta_iterate_coefficient, Nat.descFactorial_eq_zero_iff_lt.mpr hi]
  simp

variable [CharZero C]

/-- The Laurent derivation lowers the differential degree by each iteration. -/
theorem deltaOperator_iterate_monomial (l Q d i : ℕ) :
    (deltaOperator 1 (eta (k := k) (C := C)))^[i] (monomial l Q d) =
      single ((Q : ℤ) - (d : ℤ) + (i : ℤ))
        ((d.descFactorial i : RationalField C) * coefficient l Q) := by
  apply deltaOperator_iterate_single_eigen
  simpa only [Int.cast_natCast] using eta_coefficient (k := k) (C := C) l Q

/-- The left monomial's differential degree bounds the Laurent derivation orbit. -/
theorem deltaOperator_iterate_monomial_eq_zero (l Q d i : ℕ) (hi : d < i) :
    (deltaOperator 1 (eta (k := k) (C := C)))^[i] (monomial l Q d) = 0 := by
  rw [deltaOperator_iterate_monomial, Nat.descFactorial_eq_zero_iff_lt.mpr hi]
  simp

omit [CharZero C] in
/-- Multiplication of the coefficient monomials adds their two degrees. -/
theorem coefficient_mul (l Q m N : ℕ) :
    coefficient (C := C) l Q * coefficient m N = coefficient (l + m) (Q + N) := by
  simp only [coefficient, pow_add]
  ring

/-- The precise finite multiplication law for the concrete Laurent monomials. -/
theorem monomial_starProduct (l Q d m N h : ℕ) :
    starProduct 1 (by decide) (delta (k := k) (C := C)) (eta (k := k) (C := C))
      (monomial l Q d) (monomial m N h) =
      ∑ i ∈ Finset.range (min d m + 1),
        (d.choose i * m.descFactorial i : C) •
          monomial (l + m - i) (Q + N) (d + h - i) := by
  have heigen : eta (k := k) (C := C) (coefficient l Q) =
      ((Q : ℤ) : RationalField C) * coefficient l Q := by
    simpa only [Int.cast_natCast] using eta_coefficient (k := k) (C := C) l Q
  rw [monomial, monomial, starProduct_single_eigen_sum_min _ _ (Q : ℤ) d _ _ heigen
    ((N : ℤ) - (h : ℤ)) m
    (delta_iterate_coefficient_eq_zero (k := k) (C := C) m N (m + 1) (by omega))]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
  have hidh : i ≤ d + h := by have := Finset.mem_range.mp hi; omega
  have hindex : (Q : ℤ) - (d : ℤ) + ((N : ℤ) - (h : ℤ)) + (i : ℤ) =
      ((Q + N : ℕ) : ℤ) - ((d + h - i : ℕ) : ℤ) := by
    rw [Nat.cast_sub hidh]
    push_cast
    ring
  rw [delta_iterate_coefficient, hindex]
  ext j
  by_cases hj : j = ((Q + N : ℕ) : ℤ) - ((d + h - i : ℕ) : ℤ)
  · simp only [monomial, coeff_smul, hj, coeff_single_same, Algebra.smul_def,
      map_mul, map_natCast]
    rw [Nat.add_sub_assoc him]
    simp only [coefficient, pow_add]
    ring
  · simp only [monomial, coeff_smul, coeff_single, if_neg hj, smul_zero]

/-- The same monomial as an element of the associative star algebra. -/
def starMonomial (l Q d : ℕ) :
    StarSeries 1 (by decide) (delta (k := k) (C := C)) (eta (k := k) (C := C))
      (TwoVariableDifferentialField.commute (k := k) (C := C)) :=
  StarSeries.ofSeries (monomial l Q d)

omit [CharZero C] in
@[simp] theorem toSeries_starMonomial (l Q d : ℕ) :
    StarSeries.toSeries (starMonomial (k := k) (C := C) l Q d) = monomial l Q d := rfl

end MakarLimanov.ConcreteStarMonomials
