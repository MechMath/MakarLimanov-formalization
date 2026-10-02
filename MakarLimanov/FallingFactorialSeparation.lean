import MakarLimanov.DifferentialSeparation
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Falling-factorial operators in the finite differential model

The interpolation polynomial is naturally expressed in the falling-factorial
basis.  This file proves the basic basis identities used in that expansion and
records the resulting diagonal action on divided powers.  No separation or
approximation axiom is used here.
-/

namespace MakarLimanov.FallingFactorialSeparation

noncomputable section

open Polynomial DifferentialSeparation

universe u

variable {K : Type u} [Field K] [CharZero K]

def fallingPolynomial (j : ℕ) : Polynomial K :=
  ∏ i ∈ Finset.range j, (X - C (i : K))

theorem fallingPolynomial_monic (j : ℕ) :
    (fallingPolynomial (K := K) j).Monic := by
  unfold fallingPolynomial
  exact monic_prod_of_monic _ _ (by
    intro i hi
    exact monic_X_sub_C _)

theorem fallingPolynomial_natDegree (j : ℕ) :
    (fallingPolynomial (K := K) j).natDegree = j := by
  unfold fallingPolynomial
  rw [natDegree_prod_of_monic]
  · simp only [natDegree_X_sub_C]
    simp
  · intro i hi
    exact monic_X_sub_C _

theorem eval_fallingPolynomial (j n : ℕ) :
    (fallingPolynomial (K := K) j).eval (n : K) =
      ∏ i ∈ Finset.range j, ((n : K) - (i : K)) := by
  unfold fallingPolynomial
  simp only [eval_prod, eval_sub, eval_X, eval_C]

theorem eval_fallingPolynomial_of_le {j n : ℕ} (hjn : j ≤ n) :
    (fallingPolynomial (K := K) j).eval (n : K) =
      (n.descFactorial j : K) := by
  rw [eval_fallingPolynomial]
  rw [Nat.descFactorial_eq_prod_range]
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hil : i ≤ n :=
    le_trans (Nat.le_of_lt (Finset.mem_range.mp (by simpa using hi))) hjn
  rw [Nat.cast_sub hil]

theorem eval_fallingPolynomial_of_lt {j n : ℕ} (hnj : n < j) :
    (fallingPolynomial (K := K) j).eval (n : K) = 0 := by
  rw [eval_fallingPolynomial]
  obtain ⟨hmem, hcast⟩ : n ∈ Finset.range j ∧ n ≤ j :=
    ⟨Finset.mem_range.mpr hnj, Nat.le_of_lt hnj⟩
  rw [Finset.prod_eq_zero (i := n) (by simp [hmem])]
  simp

theorem interpolatingPolynomial_degree_lt (A : ℕ) (values : Fin (A + 1) → K) :
    (DifferentialSeparation.interpolatingPolynomial A values).degree < A + 1 := by
  unfold DifferentialSeparation.interpolatingPolynomial
  have h := Lagrange.degree_interpolate_lt (s := Finset.univ)
    (v := fun i : Fin (A + 1) ↦ ((A - i.val : ℕ) : K)) values
    (DifferentialSeparation.interpolation_nodes_injective (K := K) A).injOn
  simpa using h

theorem interpolatingPolynomial_natDegree_le (A : ℕ) (values : Fin (A + 1) → K) :
    (DifferentialSeparation.interpolatingPolynomial A values).natDegree ≤ A := by
  have h := interpolatingPolynomial_degree_lt (K := K) A values
  rw [natDegree_le_iff_degree_le]
  have h' : (DifferentialSeparation.interpolatingPolynomial A values).degree <
      ((A + 1 : ℕ) : WithBot ℕ) := by
    simpa using h
  by_cases hd : (DifferentialSeparation.interpolatingPolynomial A values).degree = ⊥
  · simp [hd]
  · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hd
    rw [← hd] at h'
    have h'' : (↑d : WithBot ℕ) < ↑(A + 1) := h'
    have hnat : d < A + 1 := WithBot.coe_lt_coe.mp h''
    rw [← hd]
    exact WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ hnat)

def fallingOperator (j : ℕ) : Module.End K (Polynomial K) :=
  aeval DifferentialSeparation.euler (fallingPolynomial (K := K) j)

theorem fallingOperator_dividedPower (j n : ℕ) :
    fallingOperator (K := K) j (dividedPower (K := K) n) =
      (fallingPolynomial (K := K) j).eval (n : K) • dividedPower n := by
  unfold fallingOperator
  rw [Module.End.aeval_apply_of_hasEigenvector
    ⟨(Module.End.mem_eigenspace_iff.mpr (euler_dividedPower n)),
      dividedPower_ne_zero n⟩]

theorem fallingOperator_dividedPower_of_le {j n : ℕ} (hjn : j ≤ n) :
    fallingOperator (K := K) j (dividedPower (K := K) n) =
      (n.descFactorial j : K) • dividedPower n := by
  rw [fallingOperator_dividedPower, eval_fallingPolynomial_of_le hjn]

theorem fallingOperator_dividedPower_of_lt {j n : ℕ} (hnj : n < j) :
    fallingOperator (K := K) j (dividedPower (K := K) n) = 0 := by
  rw [fallingOperator_dividedPower, eval_fallingPolynomial_of_lt hnj, zero_smul]

end
end MakarLimanov.FallingFactorialSeparation
