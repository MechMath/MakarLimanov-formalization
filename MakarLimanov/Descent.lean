import Mathlib.RingTheory.Nullstellensatz

/-!
# Polynomial-system descent

The algebraic-geometric descent step is verified here for arbitrary systems of polynomials
in finitely many variables. Connecting the matrix-rank condition to such a system remains
a separate obligation; this file does not claim the matrix descent lemma of the paper.
-/

namespace MakarLimanov

variable {K L σ : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L] [Finite σ]

/-- A polynomial system over an algebraically closed field with an extension-field solution
already has a solution in the base field. The set of equations need not be finite. -/
theorem polynomial_system_descent (S : Set (MvPolynomial σ K))
    (z : σ → L) (hz : ∀ p ∈ S, MvPolynomial.aeval z p = 0) :
    ∃ a : σ → K, ∀ p ∈ S, MvPolynomial.aeval a p = 0 := by
  let I : Ideal (MvPolynomial σ K) := Ideal.span S
  have hker : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    exact hz p hp
  have hproper : I ≠ ⊤ := by
    intro htop
    have hmem : (1 : MvPolynomial σ K) ∈ I := by rw [htop]; trivial
    have hzero : MvPolynomial.aeval z 1 = 0 := hker hmem
    simp at hzero
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I hproper
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine ⟨a, fun p hp ↦ ?_⟩
  apply (MvPolynomial.mem_vanishingIdeal_singleton_iff a p).mp
  rw [← ha]
  exact hIJ (Ideal.subset_span hp)

end MakarLimanov
