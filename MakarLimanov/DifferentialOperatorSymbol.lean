import MakarLimanov.TwoVariableDifferentialField
import MakarLimanov.FallingBasisSymbol

/-!
# Compatibility interface for the concrete separating symbol

The diagonal values lie in `Coeff A`. The two polynomial variables are `tau` and `upsilon`,
with commuting derivations `∂tau` and `upsilon ∂upsilon`. The field derivations use the
proved rational model from `TwoVariableDifferentialField`.

The diagonal interpolation polynomial is expanded in the falling factorial basis. Its
coordinates, rather than its ordinary power coefficients, form the separating symbol
`Σ cⱼ tauʲ upsilonʲ`, as in the differential-operator construction of proof.tex, §3.
-/

namespace MakarLimanov.DifferentialOperatorSymbol

open MvPolynomial Polynomial DifferentialSeparation PolynomialDerivations

noncomputable section

universe u

variable {K : Type u} [Field K]

abbrev Coefficients (A : ℕ) := DifferentialSeparation.CoefficientField (k := K) A
abbrev Coeff (A : ℕ) := Coefficients (K := K) A
abbrev PolynomialRing (A : ℕ) := MvPolynomial (Fin 2) (Coeff (K := K) A)
abbrev DifferentialField (A : ℕ) :=
  TwoVariableDifferentialField.RationalField (Coeff (K := K) A)

/-- The first polynomial variable in the compatibility interface. -/
def tau (A : ℕ) : PolynomialRing (K := K) A := X 0

/-- The second polynomial variable in the compatibility interface. -/
def upsilon (A : ℕ) : PolynomialRing (K := K) A := X 1

/-- Partial differentiation in the first polynomial variable. -/
def tauDerivationPolynomial (A : ℕ) :
    Derivation K (PolynomialRing (K := K) A) (PolynomialRing (K := K) A) :=
  mvDerivation (0 : Derivation K (Coeff (K := K) A) (PolynomialRing (K := K) A))
    (fun i : Fin 2 ↦ if i = 0 then 1 else 0)

/-- Euler differentiation in the second polynomial variable. -/
def eulerDerivationPolynomial (A : ℕ) :
    Derivation K (PolynomialRing (K := K) A) (PolynomialRing (K := K) A) :=
  mvDerivation (0 : Derivation K (Coeff (K := K) A) (PolynomialRing (K := K) A))
    (fun i : Fin 2 ↦ if i = 1 then X 1 else 0)

/-- The partial derivation on the rational function field. -/
def tauDerivation (A : ℕ) : Derivation K (DifferentialField (K := K) A)
    (DifferentialField (K := K) A) :=
  TwoVariableDifferentialField.delta (k := K) (C := Coeff (K := K) A)

/-- The Euler derivation on the rational function field. -/
def eulerDerivation (A : ℕ) : Derivation K (DifferentialField (K := K) A)
    (DifferentialField (K := K) A) :=
  TwoVariableDifferentialField.eta (k := K) (C := Coeff (K := K) A)

@[simp] theorem tauDerivation_tau (A : ℕ) :
    (tauDerivation (K := K) A) (algebraMap (PolynomialRing (K := K) A)
      (DifferentialField (K := K) A) (tau A)) = 1 :=
  TwoVariableDifferentialField.delta_tau

@[simp] theorem tauDerivation_upsilon (A : ℕ) :
    (tauDerivation (K := K) A) (algebraMap (PolynomialRing (K := K) A)
      (DifferentialField (K := K) A) (upsilon A)) = 0 :=
  TwoVariableDifferentialField.delta_upsilon

@[simp] theorem eulerDerivation_tau (A : ℕ) :
    (eulerDerivation (K := K) A) (algebraMap (PolynomialRing (K := K) A)
      (DifferentialField (K := K) A) (tau A)) = 0 :=
  TwoVariableDifferentialField.eta_tau

@[simp] theorem eulerDerivation_upsilon (A : ℕ) :
    (eulerDerivation (K := K) A) (algebraMap (PolynomialRing (K := K) A)
      (DifferentialField (K := K) A) (upsilon A)) =
      algebraMap (PolynomialRing (K := K) A) (DifferentialField (K := K) A) (upsilon A) :=
  TwoVariableDifferentialField.eta_upsilon

/-- The polynomial derivations commute as endomorphisms of the polynomial ring. -/
theorem polynomial_derivations_commute (A : ℕ) :
    Function.Commute (tauDerivationPolynomial (K := K) A)
      (eulerDerivationPolynomial (K := K) A) := by
  have hz : ⁅tauDerivationPolynomial (K := K) A,
      eulerDerivationPolynomial (K := K) A⁆ = 0 := by
    apply CKStrip.derivation_ext_mv
    · intro a
      simp [Derivation.commutator_apply, tauDerivationPolynomial,
        eulerDerivationPolynomial, mvDerivation_C]
    · intro i
      fin_cases i <;>
        simp [Derivation.commutator_apply, tauDerivationPolynomial,
          eulerDerivationPolynomial, mvDerivation_X]
  intro x
  have hx := DFunLike.congr_fun hz x
  simpa [Derivation.commutator_apply, sub_eq_zero] using hx

/-- The field derivations are the commuting pair of the rational model. -/
theorem derivations_commute (A : ℕ) :
    Function.Commute (tauDerivation (K := K) A) (eulerDerivation (K := K) A) :=
  TwoVariableDifferentialField.commute

variable [CharZero K]

/-- The interpolating coefficient polynomial from the separation construction. -/
def diagonalPolynomial (A : ℕ) : Polynomial (Coeff (K := K) A) :=
  interpolatingPolynomial A (genericValues (k := K) A)

/-- The symbol `Σ cⱼ tauʲ upsilonʲ`, using falling-basis coordinates `cⱼ`. -/
def symbolCoefficient (A : ℕ) : PolynomialRing (K := K) A :=
  FallingBasisSymbol.coefficientPolynomial (diagonalPolynomial (K := K) A)

/-- This compatibility entry is exactly the falling-basis separating coefficient. -/
theorem symbolCoefficient_eq_diagonalCoefficient (A : ℕ) :
    symbolCoefficient (K := K) A =
      FallingBasisSymbol.diagonalCoefficient A (genericValues (k := K) A) := rfl

/-- Explicit finite coefficients of the corrected separating symbol. -/
theorem symbolCoefficient_eq_sum (A : ℕ) :
    symbolCoefficient (K := K) A =
      (FallingBasisSymbol.coefficients (diagonalPolynomial (K := K) A)).sum
        (fun j c ↦ MvPolynomial.C c * tau A ^ j * upsilon A ^ j) := rfl

/-- The same falling coordinates recover the original diagonal operator. -/
theorem diagonalOperator_eq_normalOrdered_sum (A : ℕ) :
    diagonalOperator A (genericValues (k := K) A) =
      (FallingBasisSymbol.coefficients (diagonalPolynomial (K := K) A)).sum
        (fun j c ↦ c • (LinearMap.mulLeft (Coeff (K := K) A) (Polynomial.X ^ j) *
          Polynomial.derivative ^ j)) :=
  FallingBasisSymbol.diagonalOperator_eq_normalOrdered_sum A (genericValues (k := K) A)

end

end MakarLimanov.DifferentialOperatorSymbol
