import MakarLimanov.FiniteJets
import Mathlib.Algebra.Polynomial.Roots

/-!
# Choosing a noncharacteristic constant direction

A polynomial which uses a jet of maximal differential order has a nonzero
partial derivative at that order in characteristic zero. The corresponding
polynomial in a direction parameter is nonzero, and hence takes a nonzero
value at a constant from any infinite base field.
-/

namespace MakarLimanov.JetLeaderDirection

open MvPolynomial NewtonCKRoot FiniteJets

noncomputable section

/-- Multiplication by the differentiated variable restores each monomial exponent. -/
theorem coeff_X_mul_pderiv {R σ : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (i : σ) (d : σ →₀ ℕ) :
    (X i * pderiv i P).coeff d = (d i : R) * P.coeff d := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [X_mul_pderiv_monomial]
    rw [show (e i • monomial e a).coeff d = e i • (monomial e a).coeff d from
      (coeffAddMonoidHom d).map_nsmul _ _]
    simp only [coeff_monomial, nsmul_eq_mul]
    split_ifs with h
    · subst e; rfl
    · simp
  | add P Q hP hQ =>
    simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]

/-- In characteristic zero every variable which occurs has nonzero partial derivative. -/
theorem pderiv_ne_zero_of_mem_vars {R σ : Type*} [CommRing R] [IsDomain R]
    [CharZero R] (P : MvPolynomial σ R) {i : σ} (hi : i ∈ P.vars) :
    pderiv i P ≠ 0 := by
  classical
  obtain ⟨d, hd, hi⟩ := (MvPolynomial.mem_vars i).mp hi
  intro h
  have heq := coeff_X_mul_pderiv P i d
  simp only [h, mul_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at heq
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    (MvPolynomial.mem_support_iff.mp hd) heq.symm

/-- A nonzero polynomial has a nonzero value on every infinite embedded base field. -/
theorem exists_eval_algebraMap_ne_zero {k R : Type*} [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] (P : Polynomial R) (hP : P ≠ 0) :
    ∃ c : k, P.eval (algebraMap k R c) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective (FaithfulSMul.algebraMap_injective k R)).mono
  rintro _ ⟨c, rfl⟩
  exact h c

/-- The jets on the top edge of the order-`N` triangle. -/
def topJet (N : ℕ) (j : Fin (N + 1)) : Triangle N :=
  ⟨(N - j.val, j.val), by have := j.isLt; omega⟩

variable {F : Type*} [Field F] {N : ℕ}

/-- The polynomial in the direction parameter whose coefficients are top-order partials. -/
def directionPolynomial (P : MvPolynomial (Triangle N) F) :
    Polynomial (MvPolynomial (Triangle N) F) :=
  ∑ j : Fin (N + 1), Polynomial.monomial j.val (pderiv (topJet N j) P)

@[simp] theorem directionPolynomial_coeff (P : MvPolynomial (Triangle N) F)
    (j : Fin (N + 1)) :
    (directionPolynomial P).coeff j.val = pderiv (topJet N j) P := by
  classical
  simp [directionPolynomial, Polynomial.coeff_monomial, Fin.val_inj]

/-- A positive maximal differential order is attained by a top-edge variable. -/
theorem exists_topJet_mem_vars (P : MvPolynomial (Triangle N) F)
    (horder : differentialOrder (includeTriangle N P) = N) (hN : 0 < N) :
    ∃ j : Fin (N + 1), topJet N j ∈ P.vars := by
  classical
  have hvars : (includeTriangle N P).vars.Nonempty := by
    by_contra h
    have he : (includeTriangle N P).vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [differentialOrder, he] at horder
    omega
  obtain ⟨ij, hij, he⟩ := Finset.exists_mem_eq_sup (includeTriangle N P).vars hvars
    (fun ij : ℕ × ℕ ↦ ij.1 + ij.2)
  change differentialOrder (includeTriangle N P) = ij.1 + ij.2 at he
  rw [horder] at he
  obtain ⟨ab, hab, habij⟩ := MvPolynomial.mem_vars_rename Subtype.val P hij
  let j : Fin (N + 1) := ⟨ij.2, by omega⟩
  refine ⟨j, ?_⟩
  have htop : topJet N j = ab := by
    apply Subtype.ext
    rw [habij]
    apply Prod.ext
    · dsimp [topJet, j]
      omega
    · rfl
  rwa [htop]

/-- A polynomial of positive differential order has a nonzero top-order partial. -/
theorem exists_top_pderiv_ne_zero [CharZero F] (P : MvPolynomial (Triangle N) F)
    (horder : differentialOrder (includeTriangle N P) = N) (hN : 0 < N) :
    ∃ j : Fin (N + 1), pderiv (topJet N j) P ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_topJet_mem_vars P horder hN
  exact ⟨j, pderiv_ne_zero_of_mem_vars P hj⟩

theorem directionPolynomial_ne_zero_of_top_pderiv (P : MvPolynomial (Triangle N) F)
    (hP : ∃ j : Fin (N + 1), pderiv (topJet N j) P ≠ 0) :
    directionPolynomial P ≠ 0 := by
  obtain ⟨j, hj⟩ := hP
  intro h
  apply hj
  simpa using congrArg (fun Q : Polynomial (MvPolynomial (Triangle N) F) ↦ Q.coeff j.val) h

/-- Evaluation of the direction polynomial is the weighted sum of top partials. -/
theorem directionPolynomial_eval (P : MvPolynomial (Triangle N) F) (c : F) :
    (directionPolynomial P).eval (C c) =
      ∑ j : Fin (N + 1), C c ^ j.val * pderiv (topJet N j) P := by
  simp [directionPolynomial, Polynomial.eval_finset_sum, mul_comm]

/-- Choose a base-field direction on which the top-order differential symbol is nonzero. -/
theorem exists_top_direction {k : Type*} [Field k] [Infinite k] [Algebra k F]
    (P : MvPolynomial (Triangle N) F)
    (hP : ∃ j : Fin (N + 1), pderiv (topJet N j) P ≠ 0) :
    ∃ c : k, (∑ j : Fin (N + 1),
      C (algebraMap k F c) ^ j.val * pderiv (topJet N j) P) ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_eval_algebraMap_ne_zero (k := k)
    (directionPolynomial P) (directionPolynomial_ne_zero_of_top_pderiv P hP)
  refine ⟨c, ?_⟩
  change (directionPolynomial P).eval (C (algebraMap k F c)) ≠ 0 at hc
  rwa [directionPolynomial_eval] at hc

theorem exists_top_direction_of_order {k : Type*} [Field k] [Infinite k]
    [Algebra k F] [CharZero F] (P : MvPolynomial (Triangle N) F)
    (horder : differentialOrder (includeTriangle N P) = N) (hN : 0 < N) :
    ∃ c : k, (∑ j : Fin (N + 1),
      C (algebraMap k F c) ^ j.val * pderiv (topJet N j) P) ≠ 0 :=
  exists_top_direction P (exists_top_pderiv_ne_zero P horder hN)

end

end MakarLimanov.JetLeaderDirection
