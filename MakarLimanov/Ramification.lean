import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic
import MakarLimanov.ScalarReduction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.Degrees
open Polynomial
namespace MakarLimanov.Ramification
variable {F : Type*} [Field F] [CharZero F]
lemma multiplicity_pow (Q : F[X]) (hQ : Q ≠ 0) (a : F) (m : ℕ) :
    (Q ^ m).rootMultiplicity a = m * Q.rootMultiplicity a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hQ) hQ), ih]
    ring
lemma multiplicity_expand_one (e : ℕ) (he : 0 < e) (Q : F[X]) :
    (expand F e Q).rootMultiplicity 1 = Q.rootMultiplicity 1 := by
  by_cases hQ : Q = 0
  · simp [hQ]
  obtain ⟨R, hR, hnd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ 1
  have hR0 : R ≠ 0 := by intro h; simp [h] at hR; exact hQ hR
  have heF : (e : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)
  have hsep := separable_X_pow_sub_C (1 : F) heF one_ne_zero
  have hpoly : (X ^ e - C (1 : F)) ≠ 0 := hsep.ne_zero
  have hmult : (X ^ e - C (1 : F)).rootMultiplicity 1 = 1 := by
    have hlo : 0 < (X ^ e - C (1 : F)).rootMultiplicity 1 :=
      (rootMultiplicity_pos hpoly).mpr (by simp [IsRoot])
    have hhi := rootMultiplicity_le_one_of_separable hsep 1
    omega
  have hRroot : ¬ IsRoot (expand F e R) 1 := by
    rw [dvd_iff_isRoot] at hnd
    simpa only [IsRoot, expand_eval, one_pow] using hnd
  calc
    _ = ((X ^ e - C (1 : F)) ^ Q.rootMultiplicity 1 * expand F e R).rootMultiplicity 1 := by
      congr 1
      conv_lhs => rw [hR]
      simp
    _ = Q.rootMultiplicity 1 := by
      rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hpoly) ((expand_ne_zero he).mpr hR0)),
        multiplicity_pow _ hpoly, hmult, rootMultiplicity_eq_zero hRroot]
      omega
omit [CharZero F] in
lemma expand_contract_sparse (e : ℕ) (he : 0 < e) (Q : F[X])
    (hs : ∀ n, ¬ e ∣ n → Q.coeff n = 0) : expand F e (contract e Q) = Q := by
  ext n
  rw [coeff_expand he, coeff_contract (Nat.ne_of_gt he)]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · exact (hs n h).symm
lemma sparse_degree_bound (e m : ℕ) (he : 0 < e) (Q : F[X]) (hQ : Q ≠ 0)
    (hs : ∀ n, ¬ e ∣ n → Q.coeff n = 0) (hm : (X - C (1 : F)) ^ m ∣ Q) :
    e * m ≤ Q.natDegree := by
  let R := contract e Q
  have hQR : expand F e R = Q := expand_contract_sparse e he Q hs
  have hR : R ≠ 0 := by intro h; simp [h] at hQR; exact hQ hQR.symm
  have hmult : m ≤ R.rootMultiplicity 1 := by
    rw [← multiplicity_expand_one e he R, hQR]
    exact (le_rootMultiplicity_iff hQ).mpr hm
  have hdeg : R.rootMultiplicity 1 ≤ R.natDegree := by
    have h := natDegree_le_of_dvd (pow_rootMultiplicity_dvd R 1) hR
    simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using h
  rw [← hQR, natDegree_expand]
  nlinarith
section Radial
omit [CharZero F]
variable {σ : Type*}
noncomputable def radial (v : σ → F) : MvPolynomial σ F →+* F[X] :=
  MvPolynomial.eval₂Hom C (fun i ↦ C (v i) * X)
lemma radial_monomial (v : σ → F) (d : σ →₀ ℕ) (c : F) :
    radial v (MvPolynomial.monomial d c) =
      C (c * d.prod (fun i n ↦ v i ^ n)) * X ^ (d.sum fun _ n ↦ n) := by
  classical
  simp only [radial, MvPolynomial.eval₂Hom_monomial, Finsupp.prod, Finsupp.sum,
    mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, map_mul]
  ring
lemma radial_eval (v : σ → F) (P : MvPolynomial σ F) (t : F) :
    (radial v P).eval t = MvPolynomial.eval (fun i ↦ v i * t) P := by
  have h : (Polynomial.evalRingHom t).comp (radial v) =
      MvPolynomial.eval₂Hom (RingHom.id F) (fun i ↦ v i * t) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [radial]
  exact DFunLike.congr_fun h P
lemma radial_degree (v : σ → F) (P : MvPolynomial σ F) :
    (radial v P).natDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply natDegree_sum_le_of_forall_le
  intro d hd
  rw [radial_monomial]
  exact (natDegree_C_mul_X_pow_le _ _).trans (MvPolynomial.le_totalDegree hd)
lemma radial_sparse (v : σ → F) (P : MvPolynomial σ F) (e : ℕ)
    (hs : ∀ d ∈ P.support, e ∣ d.sum (fun _ n ↦ n)) :
    ∀ n, ¬ e ∣ n → (radial v P).coeff n = 0 := by
  classical
  intro n hn
  rw [P.as_sum, map_sum, finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro d hd
  rw [radial_monomial, coeff_C_mul_X_pow]
  split_ifs with heq
  · exact False.elim (hn (heq ▸ hs d hd))
  · rfl
end Radial

/-- Sparse homogeneous degrees force the ramification budget for any nonunit factor. -/
theorem factor_degree_budget [IsAlgClosed F] {d : ℕ} (Ψ P : MvPolynomial (Fin d) F)
    (e m : ℕ) (he : 0 < e) (h0 : MvPolynomial.constantCoeff Ψ ≠ 0)
    (hs : ∀ s ∈ Ψ.support, e ∣ s.sum (fun _ n ↦ n))
    (hP : ¬ IsUnit P) (hm : P ^ m ∣ Ψ) : e * m ≤ Ψ.totalDegree := by
  obtain ⟨v, hv⟩ := polynomial_zero_of_nonunit P hP
  have hrad : radial v Ψ ≠ 0 := by
    intro h
    have hz := congrArg (Polynomial.eval 0) h
    rw [radial_eval] at hz
    simp only [mul_zero, MvPolynomial.eval_zero', Polynomial.eval_zero] at hz
    exact h0 hz
  have hroot : (X - C (1 : F)) ∣ radial v P := by
    rw [dvd_iff_isRoot, IsRoot, radial_eval]
    simpa using hv
  have hdiv : (X - C (1 : F)) ^ m ∣ radial v Ψ :=
    (pow_dvd_pow_of_dvd hroot m).trans (by obtain ⟨R, hR⟩ := hm; exact ⟨radial v R, by rw [hR, map_mul, map_pow]⟩)
  exact (sparse_degree_bound e m he _ hrad (radial_sparse v Ψ e hs) hdiv).trans
    (radial_degree v Ψ)
/-- The same budget over any characteristic-zero field, by extending coefficients. -/
theorem factor_degree_budget_general {d : ℕ} (Ψ P : MvPolynomial (Fin d) F)
    (e m : ℕ) (he : 0 < e) (h0 : MvPolynomial.constantCoeff Ψ ≠ 0)
    (hs : ∀ s ∈ Ψ.support, e ∣ s.sum (fun _ n ↦ n))
    (hP : ¬ IsUnit P) (hm : P ^ m ∣ Ψ) : e * m ≤ Ψ.totalDegree := by
  let f := algebraMap F (AlgebraicClosure F)
  have hf : Function.Injective f := (algebraMap F (AlgebraicClosure F)).injective
  have hdeg (Q : MvPolynomial (Fin d) F) : (MvPolynomial.map f Q).totalDegree = Q.totalDegree := by
    simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective Q hf]
  have hmapP : ¬ IsUnit (MvPolynomial.map f P) := by
    intro h
    rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced] at h
    apply hP
    rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
    refine ⟨?_, (hdeg P) ▸ h.2⟩
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hc : (MvPolynomial.map f P).coeff 0 = 0 := by simp [MvPolynomial.coeff_map, hz]
    exact (isUnit_iff_ne_zero.mp h.1) hc
  have hmap0 : MvPolynomial.constantCoeff (MvPolynomial.map f Ψ) ≠ 0 := by
    rw [MvPolynomial.constantCoeff_map]
    exact fun h ↦ h0 (hf (by simpa using h))
  have hmaps : ∀ s ∈ (MvPolynomial.map f Ψ).support, e ∣ s.sum (fun _ n ↦ n) := by
    simpa only [MvPolynomial.support_map_of_injective Ψ hf] using hs
  have hmapm : (MvPolynomial.map f P) ^ m ∣ MvPolynomial.map f Ψ := by
    obtain ⟨Q, hQ⟩ := hm
    exact ⟨MvPolynomial.map f Q, by rw [hQ, map_mul, map_pow]⟩
  exact (factor_degree_budget _ _ e m he hmap0 hmaps hmapP hmapm).trans_eq (hdeg Ψ)
end MakarLimanov.Ramification
