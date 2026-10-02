import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Multiplication of normal-ordered differential operators

The finite Leibniz formula for `Xˡ ∂ᵈ` has the same coefficients and indices
as the corresponding concrete symbol product.
-/

noncomputable section

namespace MakarLimanov.NormalOrderedOperatorProduct

open Polynomial

universe u

variable {C : Type u} [CommRing C]

/-- A differential operator with multiplication placed before differentiation. -/
def operatorMonomial (l d : ℕ) : Module.End C (Polynomial C) :=
  LinearMap.mulLeft C (Polynomial.X ^ l) * Polynomial.derivative ^ d

@[simp] theorem operatorMonomial_apply (l d : ℕ) (P : Polynomial C) :
    operatorMonomial l d P = Polynomial.X ^ l * Polynomial.derivative^[d] P := by
  simp only [operatorMonomial, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Module.End.pow_apply]

/-- The exact finite multiplication formula for normal-ordered operators. -/
theorem operatorMonomial_mul (l d m h : ℕ) :
    operatorMonomial (C := C) l d * operatorMonomial m h =
      ∑ i ∈ Finset.range (min d m + 1),
        ((d.choose i * m.descFactorial i : ℕ) : C) •
          operatorMonomial (l + m - i) (d + h - i) := by
  apply LinearMap.ext
  intro P
  simp only [Module.End.mul_apply, operatorMonomial_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  rw [mul_comm (Polynomial.X ^ m) (Polynomial.derivative^[h] P),
    Polynomial.iterate_derivative_mul_X_pow, Nat.min_comm m d, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ min d m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hid : i ≤ d := le_trans hi' (Nat.min_le_left d m)
  have him : i ≤ m := le_trans hi' (Nat.min_le_right d m)
  have hdegree : l + (m - i) = l + m - i := by omega
  have horder : d - i + h = d + h - i := by omega
  rw [← Nat.cast_smul_eq_nsmul C, mul_smul_comm, ← Function.iterate_add_apply,
    horder, mul_comm (Polynomial.derivative^[d + h - i] P) (Polynomial.X ^ (m - i)),
    ← mul_assoc, ← pow_add, hdegree]

end MakarLimanov.NormalOrderedOperatorProduct

end
