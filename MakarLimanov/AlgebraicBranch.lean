import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Derivation.Basic
open Polynomial
namespace MakarLimanov.AlgebraicBranch
universe u
variable {K : Type u} [Field K] [CharZero K] (P : K[X]) [Fact (Irreducible P)]
lemma separable : Algebra.IsSeparable K (AdjoinRoot P) := by
  letI : FiniteDimensional K (AdjoinRoot P) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis (Fact.out : Irreducible P).ne_zero).basis
  infer_instance
omit [CharZero K] in
lemma root_equation : aeval (AdjoinRoot.root P) P = 0 := by
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
omit [CharZero K] in
lemma kernel_iff (Q : K[X]) : aeval (AdjoinRoot.root P) Q = 0 ↔ P ∣ Q := by
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
omit [CharZero K] in
lemma inequation (Q : K[X]) (hQ : ¬ P ∣ Q) : aeval (AdjoinRoot.root P) Q ≠ 0 := by
  exact mt (kernel_iff P Q).mp hQ
lemma separant_nonzero : aeval (AdjoinRoot.root P) P.derivative ≠ 0 := by
  apply inequation
  have hdeg := Irreducible.natDegree_pos (Fact.out : Irreducible P)
  apply Polynomial.not_dvd_of_natDegree_lt
  · intro h
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
    omega
  · exact Polynomial.natDegree_derivative_lt (ne_of_gt hdeg)
lemma exists_separable_root :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E),
      Algebra.IsSeparable K E ∧ ∃ u : E,
        aeval u P = 0 ∧
        (∀ Q : K[X], aeval u Q = 0 ↔ P ∣ Q) ∧
        (∀ Q : K[X], ¬ P ∣ Q → aeval u Q ≠ 0) ∧
        aeval u P.derivative ≠ 0 := by
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, separable P, AdjoinRoot.root P,
    root_equation P, kernel_iff P, inequation P, separant_nonzero P⟩
end MakarLimanov.AlgebraicBranch
