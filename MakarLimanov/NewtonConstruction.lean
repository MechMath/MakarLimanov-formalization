import MakarLimanov.Numerics
import MakarLimanov.Ramification

/-!
# Interfaces for the finite Newton construction

This file records the bookkeeping interface used by the finite Newton argument in
`proof.tex`, Section 5.  The algebraic production of a correction is deliberately
left as data: once a construction supplies the fields below, the termination and
budget conclusions are proved here without any infinitary argument.
-/

namespace MakarLimanov

/-- Data supplied by one Newton stage.

`rho j` is the precision reached after stage `j`; `p j` is the denominator of the
current lattice and `b j` is the remaining degree budget.  The fields are exactly
the numerical invariants maintained in (5.5) of the paper.
-/
structure NewtonData (M T : ℕ) where
  rho : ℕ → ℚ
  p : ℕ → ℕ
  b : ℕ → ℕ
  rho_nonneg : 0 ≤ rho 0
  budget : ∀ j, p j * b j ≤ M
  progress : ∀ j < M * T, rho j + 1 / (M : ℚ) ≤ rho (j + 1)

namespace NewtonData

variable {M T : ℕ} (N : NewtonData M T)

theorem precision_at_budget (hM : 0 < M) :
    (T : ℚ) ≤ N.rho (M * T) := by
  exact finite_progress hM N.rho N.rho_nonneg N.progress

theorem positive_budget_bound {j m : ℕ} (hm : 0 < m)
    (hstep : N.p j * m ≤ M) : N.p j ≤ M := by
  exact denominator_bound hm hstep

theorem denominator_multiplicity_bound {j e m q : ℕ}
    (horbit : e * m ≤ q) (hq : q ≤ N.b j) :
    (N.p j * e) * m ≤ M := by
  exact newton_budget horbit hq (N.budget j)

end NewtonData

/-- A stage with a nonzero residual improves precision by at least one lattice unit. -/
theorem newton_strict_progress {ρ ρ' : ℚ} {p : ℕ}
    (hp : 0 < p) (hstep : ρ + 1 / (p : ℚ) ≤ ρ') : ρ < ρ' := by
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hfrac : (0 : ℚ) < 1 / (p : ℚ) := by positivity
  linarith

/-- The finite Newton schedule reaches precision `T` within `M*T` stages. -/
theorem newton_termination {M T : ℕ} (hM : 0 < M)
    (N : NewtonData M T) : (T : ℚ) ≤ N.rho (M * T) :=
  N.precision_at_budget hM

/-- Termination from the actual integer indices of successively refined lattices. -/
theorem newton_termination_of_lattice {M T : ℕ} (hM : 0 < M)
    (r : ℕ → ℤ) (p e : ℕ → ℕ)
    (hzero : 0 ≤ r 0) (hp : ∀ j, 0 < p j) (he : ∀ j, 0 < e j)
    (hbudget : ∀ j, p j ≤ M)
    (hnext : ∀ j < M * T, p (j + 1) = p j * e j)
    (hr : ∀ j < M * T, r j * (e j : ℤ) < r (j + 1)) :
    (T : ℚ) ≤ (r (M * T) : ℚ) / p (M * T) := by
  apply finite_progress hM (fun j ↦ (r j : ℚ) / p j)
  · apply div_nonneg
    · exact_mod_cast hzero
    · exact_mod_cast (hp 0).le
  · intro j hj
    rw [hnext j hj]
    apply newton_lattice_progress (hp j) (he j) _ (hr j hj)
    rw [← hnext j hj]
    exact hbudget (j + 1)

end MakarLimanov
