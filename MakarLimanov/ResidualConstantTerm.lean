import MakarLimanov.NewtonResidual
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Constant terms of generic residual coefficients

The constant term of a universal residual coefficient is its value when all
perturbation jets vanish.  Specializing the generic correction to zero recovers
the uncorrected residual.  This is the identity `Ψ(0) = c` in Lemma 8 of the paper.
-/

noncomputable section

namespace MakarLimanov.ResidualConstantTerm

open HahnSeries SymbolSeries SymbolSeries.StarSeries
open NewtonResidual

variable {k F E : Type*} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [Algebra (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower F (MvPolynomial (ℕ × ℕ) F) E]
  [IsScalarTower k (MvPolynomial (ℕ × ℕ) F) E]
  [IsFractionRing (MvPolynomial (ℕ × ℕ) F) E]
  [CharZero F] [CharZero E]

/- A positive-degree homogeneous polynomial has no constant term. -/
omit [CharZero F] in
theorem constantCoeff_eq_zero_of_isHomogeneous
    {j : ℕ} {P : MvPolynomial (ℕ × ℕ) F}
    (hP : P.IsHomogeneous j) (hj : 0 < j) :
    MvPolynomial.constantCoeff P = 0 := by
  rw [MvPolynomial.constantCoeff_eq]
  exact hP.coeff_eq_zero (by simpa using (Nat.ne_of_gt hj).symm)

omit [CharZero F] in
private theorem derivation_iterate_zero (D : Derivation k F F) (n : ℕ) :
    D^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

/-- Evaluating all generic jets at zero recovers the coefficient of the
uncorrected residual. -/
theorem residual_coefficient_constantCoeff
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r) :
    MvPolynomial.constantCoeff P =
      (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r := by
  obtain ⟨Q, hQ, hspecial⟩ :=
    exists_universal_residual_coefficient (E := E) (G := F) δ η hc p hp q z f r
  have hPQ : P = Q :=
    (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) F) E) (hP.trans hQ.symm)
  have hzero := hspecial δ η hc (fun a ↦ by simp) (fun a ↦ by simp) 0
  have hz : mapField (IsScalarTower.toAlgHom k F F) z = z := by
    ext n
    simp
  have hjets : (fun ij : ℕ × ℕ ↦ δ^[ij.1] (η^[ij.2] (0 : F))) =
      (fun _ : ℕ × ℕ ↦ (0 : F)) := by
    funext ij
    rw [derivation_iterate_zero, derivation_iterate_zero]
  rw [hjets, MvPolynomial.aeval_zero', hz, map_zero, add_zero] at hzero
  simpa [hPQ] using hzero

/-- A nonzero coefficient of the uncorrected residual forces a nonzero
constant term in its universal coefficient polynomial. -/
theorem residual_coefficient_constantCoeff_ne_zero
    (δ η : Derivation k F F) (hc : Function.Commute δ η)
    (p : ℕ) (hp : 0 < p) (q : ℤ) (z : LaurentSeries F)
    (f : FreeAlgebra k Bool) (r : ℤ) (P : MvPolynomial (ℕ × ℕ) F)
    (hP : algebraMap (MvPolynomial (ℕ × ℕ) F) E P =
      (genericResidual (E := E) δ η hc p hp q z f).coeff r)
    (hres : (toSeries (evaluateAt (hp := hp) (h := hc) z f)).coeff r ≠ 0) :
    MvPolynomial.constantCoeff P ≠ 0 := by
  rw [residual_coefficient_constantCoeff (E := E) δ η hc p hp q z f r P hP]
  exact hres

end MakarLimanov.ResidualConstantTerm
