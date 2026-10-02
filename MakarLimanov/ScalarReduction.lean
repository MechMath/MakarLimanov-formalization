import MakarLimanov.Statement
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# The scalar-zero versus constant-abelianization dichotomy

This is the first part of Lemma 2.1. The injective two-generator substitution and its degree
bounds are separate obligations, not supplied by the results in this file.
-/

namespace MakarLimanov

variable {K : Type*} [Field K] {d : ℕ}

/-- Abelianization of the free algebra, retaining the original number of variables. -/
noncomputable def abelianize : FreePoly K d →ₐ[K] MvPolynomial (Fin d) K :=
  FreeAlgebra.lift K MvPolynomial.X

theorem eval_abelianize (f : FreePoly K d) (a : Fin d → K) :
    MvPolynomial.aeval a (abelianize f) = FreeAlgebra.lift K a f := by
  have h : (MvPolynomial.aeval a).comp abelianize = FreeAlgebra.lift K a := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [abelianize]
  exact DFunLike.congr_fun h f

/-- A nonunit polynomial in finitely many variables has a zero over an algebraically closed field. -/
theorem polynomial_zero_of_nonunit [IsAlgClosed K] (p : MvPolynomial (Fin d) K)
    (hp : ¬IsUnit p) : ∃ a : Fin d → K, MvPolynomial.aeval a p = 0 := by
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal (Ideal.span {p})
    (Ideal.span_singleton_ne_top hp)
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine ⟨a, (MvPolynomial.mem_vanishingIdeal_singleton_iff a p).mp ?_⟩
  rw [← ha]
  exact hle (Ideal.subset_span (Set.mem_singleton p))

/-- The first dichotomy of the source proof, fully quantified over the original scalar field. -/
theorem scalar_zero_or_constant_abelianization [IsAlgClosed K] (f : FreePoly K d) :
    (∃ a : Fin d → K, FreeAlgebra.lift K a f = 0) ∨
      ∃ c : K, c ≠ 0 ∧ abelianize f = MvPolynomial.C c := by
  by_cases h : IsUnit (abelianize f)
  · obtain ⟨c, hc, heq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
    exact Or.inr ⟨c, isUnit_iff_ne_zero.mp hc, heq⟩
  · obtain ⟨a, ha⟩ := polynomial_zero_of_nonunit (abelianize f) h
    exact Or.inl ⟨a, by simpa [eval_abelianize] using ha⟩

/-- Only the constant-abelianization branch remains after the verified scalar reduction. -/
theorem originalConjecture_of_constant_abelianization [IsAlgClosed K] [CharZero K]
    (remaining : ∀ f : FreePoly K d, Nonconstant f →
      (∃ c : K, c ≠ 0 ∧ abelianize f = MvPolynomial.C c) → RankInfimumZero f) :
    OriginalConjecture K d := by
  intro f hf
  rcases scalar_zero_or_constant_abelianization f with ⟨a, ha⟩ | hc
  · exact rankInfimumZero_of_scalar_zero f a ha
  · exact remaining f hf hc

end MakarLimanov
