import MakarLimanov.Numerics
import MakarLimanov.LatticeDenominator

/-!
# Numerical Newton invariants

This module isolates the arithmetic part of Proposition 10. It records the
finite-stage invariant used by a dependent Newton run, its endpoint precision,
and the denominator and multiplicity budget preserved by one refinement.
-/

namespace MakarLimanov.NewtonInvariant

noncomputable section

/-! A schedule stores only the numerical data of a Newton stage. -/
structure Schedule (M T : ℕ) where
  rho : ℕ → ℚ
  p : ℕ → ℕ
  b : ℕ → ℕ
  rho_nonneg : 0 ≤ rho 0
  positive_p : ∀ j, 0 < p j
  budget : ∀ j, p j * b j ≤ M
  progress : ∀ j < M * T, rho j + 1 / (M : ℚ) ≤ rho (j + 1)

/-- The finite schedule reaches precision `T` at its budget endpoint. -/
theorem endpoint_precision {M T : ℕ} (hM : 0 < M) (R : Schedule M T) :
    (T : ℚ) ≤ R.rho (M * T) := by
  exact MakarLimanov.finite_progress hM R.rho R.rho_nonneg R.progress

/-- The endpoint statement in the form used by Proposition 10. -/
theorem exists_precision_stage {M T : ℕ} (hM : 0 < M) (R : Schedule M T) :
    ∃ J ≤ M * T, (T : ℚ) ≤ R.rho J := by
  exact ⟨M * T, le_rfl, endpoint_precision hM R⟩

/-- The multiplicity and denominator estimate is preserved by one Newton
refinement. -/
theorem refined_budget
    {p e m q b M : ℕ}
    (horbit : e * m ≤ q) (hq : q ≤ b) (hbudget : p * b ≤ M) :
    (p * e) * m ≤ M := by
  exact MakarLimanov.newton_budget horbit hq hbudget

/-- The same estimate with the product normalized in the form used by the
dependent stage invariant. -/
theorem refined_budget_assoc
    {p e m q b M : ℕ}
    (horbit : e * m ≤ q) (hq : q ≤ b) (hbudget : p * b ≤ M) :
    p * (e * m) ≤ M := by
  simpa [Nat.mul_assoc] using refined_budget horbit hq hbudget

/-- If the reduced denominator of a new slope divides `p*k`, its lattice
refinement factor divides the active degree `k`. -/
theorem refinement_factor_of_active_degree
    (p b k : ℕ) (hp : 0 < p) (hb : 0 < b)
    (h_integral : b ∣ p * k) :
    b / Nat.gcd p b ∣ k := by
  exact LatticeDenominator.refinement_factor_dvd_of_dvd_mul p b k hp hb h_integral

/-- The lattice refinement factor divides every member of a finite active set
whose slope contribution is integral on the old lattice.

This is the finite-support form of the denominator calculation used in the
Newton step.  The analytic construction of the active set is deliberately
separate: once it supplies `b ∣ p * k` for each active order `k`, the common
refinement factor is obtained uniformly by this lemma.
-/
theorem refinement_factor_dvd_active_orders
    (p b : ℕ) (hp : 0 < p) (hb : 0 < b)
    (active : Finset ℕ)
    (h_integral : ∀ k ∈ active, b ∣ p * k) :
    ∀ k ∈ active, b / Nat.gcd p b ∣ k := by
  intro k hk
  exact refinement_factor_of_active_degree p b k hp hb (h_integral k hk)

/-- A support-indexed variant convenient for residual variation supports. -/
theorem refinement_factor_dvd_support
    (p b : ℕ) (hp : 0 < p) (hb : 0 < b)
    {S : Finset ℕ}
    (h_integral : ∀ k ∈ S, b ∣ p * k) :
    ∀ k ∈ S, b / Nat.gcd p b ∣ k := by
  exact refinement_factor_dvd_active_orders p b hp hb S h_integral

/-- A stage denominator remains within the global budget after choosing an
active factor whose orbit degree is bounded by the current budget. -/
theorem positive_refined_denominator_bound
    {p e m M : ℕ} (hp : 0 < p) (he : 0 < e) (hm : 0 < m)
    (hbudget : p * e * m ≤ M) : p * e ≤ M := by
  exact denominator_bound (p := p * e) (m := m) (M := M) hm
    (by simpa [Nat.mul_assoc] using hbudget)

end

end MakarLimanov.NewtonInvariant
