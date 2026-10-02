import MakarLimanov.NewtonCKRoot

/-!
# Positive degree at a nonzero leader partial

The triangular-to-strip encoding is injective. Thus a nonzero leader partial
becomes a nonzero ordinary derivative, which forces positive univariate degree.
This argument also applies to the order-zero triangle.
-/

namespace MakarLimanov.NewtonCKRoot

open MvPolynomial

noncomputable section

variable {F : Type*} [Field F] {N : ℕ}

/-- Splitting the pure leader from the remaining strip variables is injective. -/
theorem stripPolynomial_injective :
    Function.Injective (stripPolynomial (F := F) (N := N)) :=
  (optionEquivLeft F (Fin N × ℕ)).injective.comp
    (MvPolynomial.rename_injective _ stripIndex_injective)

/-- A nonzero leader partial ensures positive degree in the strip's algebraic variable. -/
theorem stripPolynomial_natDegree_ne_zero_of_pderiv (P : MvPolynomial (Triangle N) F)
    (hP : pderiv (leader N) P ≠ 0) : (stripPolynomial P).natDegree ≠ 0 := by
  intro hdeg
  apply hP
  apply stripPolynomial_injective
  rw [stripPolynomial_leader_pderiv]
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  rw [hconstant, Polynomial.derivative_C]
  simp [stripPolynomial]

end

end MakarLimanov.NewtonCKRoot
