import MakarLimanov.FallingFactorialSeparation
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Falling-basis coefficients for the separating symbol

The polynomial `P` defining the diagonal differential operator is expanded in
falling factorials before its coefficients are used in the symbol
`Σ cⱼ τʲ uʲ`.  Evaluating this expansion at the Euler operator recovers the
original diagonal operator.
-/

noncomputable section

namespace MakarLimanov.FallingBasisSymbol

open Polynomial DifferentialSeparation FallingFactorialSeparation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The monic falling factorials form a polynomial sequence. -/
def fallingSequence : Polynomial.Sequence K where
  elems' := fallingPolynomial
  degree_eq' j := by
    rw [Polynomial.degree_eq_natDegree (fallingPolynomial_monic j).ne_zero,
      fallingPolynomial_natDegree]

/-- The falling factorial basis of the polynomial ring. -/
def fallingBasis : Module.Basis ℕ K (Polynomial K) :=
  fallingSequence.basis (fun j ↦ by
    change IsUnit (fallingPolynomial (K := K) j).leadingCoeff
    rw [(fallingPolynomial_monic j).leadingCoeff]
    exact isUnit_one)

@[simp] theorem fallingBasis_apply (j : ℕ) :
    fallingBasis (K := K) j = fallingPolynomial j := by
  exact Polynomial.Sequence.basis_eq_self _ _ j

/-- Finite coordinates of a polynomial in the falling factorial basis. -/
def coefficients (P : Polynomial K) : ℕ →₀ K := fallingBasis.repr P

/-- Every polynomial is its finite sum of falling factorial components. -/
theorem sum_coefficients (P : Polynomial K) :
    (coefficients P).sum (fun j c ↦ c • fallingPolynomial j) = P := by
  simpa only [coefficients, Finsupp.linearCombination_apply, fallingBasis_apply] using
    (fallingBasis (K := K)).linearCombination_repr P

/-- A finite coefficient family realizing the falling factorial expansion. -/
theorem exists_falling_expansion (P : Polynomial K) :
    ∃ c : ℕ →₀ K, P = c.sum (fun j a ↦ a • fallingPolynomial j) :=
  ⟨coefficients P, (sum_coefficients P).symm⟩

/-- The corrected coefficient polynomial `Σ cⱼ τʲ uʲ`. -/
def coefficientPolynomial (P : Polynomial K) : MvPolynomial (Fin 2) K :=
  (coefficients P).sum (fun j c ↦
    MvPolynomial.C c * MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ j)

/-- Evaluation of the coefficient polynomial at any two elements. -/
theorem aeval_coefficientPolynomial {R : Type*} [CommRing R] [Algebra K R]
    (P : Polynomial K) (τ u : R) :
    MvPolynomial.aeval ![τ, u] (coefficientPolynomial P) =
      (coefficients P).sum (fun j c ↦ algebraMap K R c * τ ^ j * u ^ j) := by
  simp [coefficientPolynomial, Finsupp.sum]

/-- The coefficient polynomial associated with the interpolated diagonal values. -/
def diagonalCoefficient (A : ℕ) (values : Fin (A + 1) → K) : MvPolynomial (Fin 2) K :=
  coefficientPolynomial (interpolatingPolynomial A values)

/-- The separating coefficient uses falling-basis coordinates of the
interpolating polynomial. -/
theorem diagonalCoefficient_eq_sum (A : ℕ) (values : Fin (A + 1) → K) :
    diagonalCoefficient A values =
      (coefficients (interpolatingPolynomial A values)).sum
        (fun j c ↦ MvPolynomial.C c * MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ j) := rfl

/-- Applying the falling expansion to the Euler operator preserves its value. -/
theorem sum_fallingOperator (P : Polynomial K) :
    (coefficients P).sum (fun j c ↦ c • fallingOperator j) =
      Polynomial.aeval (DifferentialSeparation.euler (K := K)) P := by
  have h := congrArg (Polynomial.aeval (DifferentialSeparation.euler (K := K)))
    (sum_coefficients P)
  simpa only [Finsupp.sum, map_sum, map_smul, fallingOperator] using h

/-- The falling coefficients of the interpolation polynomial recover the
same diagonal differential operator as the original construction. -/
theorem diagonalOperator_eq_sum (A : ℕ) (values : Fin (A + 1) → K) :
    diagonalOperator A values =
      (coefficients (interpolatingPolynomial A values)).sum
        (fun j c ↦ c • fallingOperator j) :=
  (sum_fallingOperator (interpolatingPolynomial A values)).symm

/-- The falling Euler operator is the normal-ordered operator `τʲ ∂τʲ`. -/
theorem fallingOperator_eq_mulLeft_derivative_pow (j : ℕ) :
    fallingOperator (K := K) j =
      LinearMap.mulLeft K (Polynomial.X ^ j) * Polynomial.derivative ^ j := by
  have hpower (n : ℕ) :
      fallingOperator (K := K) j (Polynomial.X ^ n) =
        (LinearMap.mulLeft K (Polynomial.X ^ j) * Polynomial.derivative ^ j :
          Module.End K (Polynomial K))
          (Polynomial.X ^ n) := by
    have hdp : (Polynomial.X ^ n : Polynomial K) =
        (n.factorial : K) • dividedPower n := by
      simp [dividedPower, smul_monomial, smul_eq_mul, n.factorial_ne_zero,
        Polynomial.monomial_one_right_eq_X_pow]
    have hfall : fallingOperator (K := K) j (Polynomial.X ^ n) =
        (fallingPolynomial (K := K) j).eval (n : K) • Polynomial.X ^ n := by
      rw [hdp, map_smul, fallingOperator_dividedPower, smul_comm]
    change fallingOperator (K := K) j (Polynomial.X ^ n) =
      Polynomial.X ^ j * (Polynomial.derivative ^ j) (Polynomial.X ^ n)
    rw [hfall, Module.End.pow_apply, Polynomial.iterate_derivative_X_pow_eq_smul]
    by_cases hj : j ≤ n
    · rw [eval_fallingPolynomial_of_le hj, mul_smul_comm, ← pow_add]
      have hindex : j + (n - j) = n := by omega
      rw [hindex]
    · have hnj : n < j := Nat.lt_of_not_ge hj
      rw [eval_fallingPolynomial_of_lt hnj, Nat.descFactorial_of_lt hnj]
      simp
  apply LinearMap.ext
  intro P
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [← Polynomial.smul_X_eq_monomial, map_smul, map_smul, hpower]

/-- The diagonal operator has the finite normal-ordered expansion used by
the separating symbol. -/
theorem diagonalOperator_eq_normalOrdered_sum (A : ℕ) (values : Fin (A + 1) → K) :
    diagonalOperator A values =
      (coefficients (interpolatingPolynomial A values)).sum
        (fun j c ↦ c • (LinearMap.mulLeft K (Polynomial.X ^ j) *
          Polynomial.derivative ^ j)) := by
  rw [diagonalOperator_eq_sum]
  simp only [fallingOperator_eq_mulLeft_derivative_pow]

end MakarLimanov.FallingBasisSymbol

end
