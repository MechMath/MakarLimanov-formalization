import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic

/-!
# The lowest homogeneous term after a Newton correction

This file proves the polynomial calculation in equation (5.2) of `proof.tex`.
If `P(v) = 0`, a partial derivative of `P` is nonzero at `v`, and `Q(v) ≠ 0`,
then the first nonzero homogeneous term of `(P ^ m * Q)(v + w)` has degree `m`.
It equals `Q(v)` times the `m`th power of the linearization of `P` at `v`.
The variables may be an infinite set of mixed jets: every polynomial still has
finite support.
-/

namespace MakarLimanov.NewtonTranslation

open MvPolynomial

noncomputable section

variable {R σ : Type*} [CommSemiring R]

/-- No monomial of total degree below `n` occurs. -/
def DegreeLowerBound (n : ℕ) (P : MvPolynomial σ R) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < n → P.coeff d = 0

theorem degreeLowerBound_zero (P : MvPolynomial σ R) : DegreeLowerBound 0 P := by
  intro d hd
  omega

theorem degreeLowerBound_one_iff (P : MvPolynomial σ R) :
    DegreeLowerBound 1 P ↔ P.coeff 0 = 0 := by
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have hd' : d.degree = 0 := by omega
    have hd0 : d = 0 := by
      ext i
      have hi : d i ≤ d.degree := Finsupp.le_degree i d
      simp only [Finsupp.zero_apply]
      omega
    simpa [hd0] using h

theorem DegreeLowerBound.mul {m n : ℕ} {P Q : MvPolynomial σ R}
    (hP : DegreeLowerBound m P) (hQ : DegreeLowerBound n Q) :
    DegreeLowerBound (m + n) (P * Q) := by
  classical
  intro d hd
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have heq : a.degree + b.degree = d.degree := by
    rw [← map_add, Finset.mem_antidiagonal.mp hab]
  by_cases ha : a.degree < m
  · simp [hP a ha]
  · have hb : b.degree < n := by omega
    simp [hQ b hb]

theorem DegreeLowerBound.pow {n : ℕ} {P : MvPolynomial σ R}
    (hP : DegreeLowerBound n P) (m : ℕ) : DegreeLowerBound (n * m) (P ^ m) := by
  induction m with
  | zero => simpa using degreeLowerBound_zero (1 : MvPolynomial σ R)
  | succ m ih => simpa [pow_succ, Nat.mul_succ] using ih.mul hP

/-- Below a support degree bound, the homogeneous component is zero. -/
theorem DegreeLowerBound.homogeneousComponent_eq_zero {n k : ℕ} {P : MvPolynomial σ R}
    (hP : DegreeLowerBound n P) (hk : k < n) : homogeneousComponent k P = 0 := by
  ext d
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with hd
  · exact hP d (hd ▸ hk)
  · rfl

/-- At the sum of two lower degree bounds, only the two lowest components contribute. -/
theorem homogeneousComponent_mul_of_lowerBound {m n : ℕ} {P Q : MvPolynomial σ R}
    (hP : DegreeLowerBound m P) (hQ : DegreeLowerBound n Q) :
    homogeneousComponent (m + n) (P * Q) =
      homogeneousComponent m P * homogeneousComponent n Q := by
  classical
  ext d
  by_cases hd : d.degree = m + n
  · rw [coeff_homogeneousComponent, if_pos hd, MvPolynomial.coeff_mul,
      MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ hab
    have heq : a.degree + b.degree = m + n := by
      rw [← map_add, Finset.mem_antidiagonal.mp hab, hd]
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases ha : a.degree = m
    · have hb : b.degree = n := by omega
      simp [ha, hb]
    · by_cases hal : a.degree < m
      · simp [ha, hP a hal]
      · have hb : b.degree < n := by omega
        simp [ha, hQ b hb]
  · rw [coeff_homogeneousComponent, if_neg hd]
    exact ((homogeneousComponent_isHomogeneous m P).mul
      (homogeneousComponent_isHomogeneous n Q)).coeff_eq_zero hd |>.symm

theorem homogeneousComponent_pow_of_lowerBound {n : ℕ} {P : MvPolynomial σ R}
    (hP : DegreeLowerBound n P) (m : ℕ) :
    homogeneousComponent (n * m) (P ^ m) = homogeneousComponent n P ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.mul_succ, homogeneousComponent_mul_of_lowerBound (hP.pow m) hP,
      ih, pow_succ]

/-- Substitute `vᵢ + wᵢ` into a polynomial. -/
def translate (v : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun i ↦ C (v i) + X i)

@[simp] theorem translate_C (v : σ → R) (a : R) : translate v (C a) = C a := by
  simp [translate]

@[simp] theorem translate_X (v : σ → R) (i : σ) : translate v (X i) = C (v i) + X i := by
  simp [translate]

/-- The constant coefficient after translation is evaluation at the translation point. -/
theorem constantCoeff_translate (v : σ → R) (P : MvPolynomial σ R) :
    constantCoeff (translate v P) = MvPolynomial.eval v P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP]

/-- Translation commutes with formal partial differentiation. -/
theorem pderiv_translate (v : σ → R) (P : MvPolynomial σ R) (i : σ) :
    pderiv i (translate v P) = translate v (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, translate_X, pderiv_mul, map_add, pderiv_C, zero_add, hP,
      pderiv_X, Pi.single_apply]
    split_ifs <;> simp

/-- A partial derivative evaluated at zero reads the corresponding linear coefficient. -/
theorem constantCoeff_pderiv (P : MvPolynomial σ R) (i : σ) :
    constantCoeff (pderiv i P) = P.coeff (Finsupp.single i 1) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hi : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h
      have := congrArg (fun d : σ →₀ ℕ ↦ d i) h
      simp at this
    simp [hi]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
    by_cases hij : j = i
    · subst j
      simp only [Derivation.leibniz, smul_eq_mul, pderiv_X_self, mul_one, map_add,
        map_mul, constantCoeff_X, zero_mul, add_zero, coeff_mul_X',
        Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton, ↓reduceIte,
        tsub_self]
      rfl
    · simp [coeff_mul_X', hP, hij]

/-- The linear part of `P(v + w)` is the formal linearization at `v`. -/
def linearization (v : σ → R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  homogeneousComponent 1 (translate v P)

/-- Each linear coefficient is exactly the corresponding partial derivative at `v`. -/
theorem coeff_linearization (v : σ → R) (P : MvPolynomial σ R) (i : σ) :
    (linearization v P).coeff (Finsupp.single i 1) = MvPolynomial.eval v (pderiv i P) := by
  rw [linearization, coeff_homogeneousComponent]
  simp only [Finsupp.degree_single, ↓reduceIte]
  rw [← constantCoeff_pderiv, pderiv_translate, constantCoeff_translate]

theorem linearization_ne_zero (v : σ → R) (P : MvPolynomial σ R) (i : σ)
    (hi : MvPolynomial.eval v (pderiv i P) ≠ 0) : linearization v P ≠ 0 := by
  intro h
  apply hi
  rw [← coeff_linearization, h, coeff_zero]

theorem linearization_isHomogeneous (v : σ → R) (P : MvPolynomial σ R) :
    (linearization v P).IsHomogeneous 1 :=
  homogeneousComponent_isHomogeneous _ _

/-- The exact leading homogeneous component in the translated Newton equation. -/
theorem translated_factor_component (v : σ → R) (P Q : MvPolynomial σ R) (m : ℕ)
    (hP : MvPolynomial.eval v P = 0) :
    homogeneousComponent m (translate v (P ^ m * Q)) =
      C (MvPolynomial.eval v Q) * linearization v P ^ m := by
  have hP' : DegreeLowerBound 1 (translate v P) := by
    rw [degreeLowerBound_one_iff]
    exact (constantCoeff_translate v P).trans hP
  rw [map_mul, map_pow]
  have heq := homogeneousComponent_mul_of_lowerBound (hP'.pow m)
    (degreeLowerBound_zero (translate v Q))
  simp only [one_mul, add_zero] at heq
  rw [heq]
  have hpow := homogeneousComponent_pow_of_lowerBound hP' m
  simp only [one_mul] at hpow
  rw [hpow, homogeneousComponent_zero]
  change linearization v P ^ m * C (constantCoeff (translate v Q)) = _
  rw [constantCoeff_translate, mul_comm]

theorem translated_factor_components_below (v : σ → R) (P Q : MvPolynomial σ R)
    (m : ℕ) (hP : MvPolynomial.eval v P = 0) {j : ℕ} (hj : j < m) :
    homogeneousComponent j (translate v (P ^ m * Q)) = 0 := by
  have hP' : DegreeLowerBound 1 (translate v P) := by
    rw [degreeLowerBound_one_iff]
    exact (constantCoeff_translate v P).trans hP
  have hb := (hP'.pow m).mul (degreeLowerBound_zero (translate v Q))
  simp only [one_mul, add_zero] at hb
  rw [map_mul, map_pow]
  exact hb.homogeneousComponent_eq_zero hj

variable [NoZeroDivisors R]

/-- A nonsingular factor root makes the degree-`m` component genuinely nonzero. -/
theorem translated_factor_component_ne_zero (v : σ → R) (P Q : MvPolynomial σ R)
    (m : ℕ) (i : σ) (hP : MvPolynomial.eval v P = 0)
    (hQ : MvPolynomial.eval v Q ≠ 0) (hi : MvPolynomial.eval v (pderiv i P) ≠ 0) :
    homogeneousComponent m (translate v (P ^ m * Q)) ≠ 0 := by
  rw [translated_factor_component v P Q m hP]
  exact mul_ne_zero (by simpa using hQ)
    (pow_ne_zero m (linearization_ne_zero v P i hi))

/-- Equation (5.2): the first nonzero translated homogeneous term has exactly degree `m`. -/
theorem translated_factor_lowest_term (v : σ → R) (P Q : MvPolynomial σ R)
    (m : ℕ) (i : σ) (hP : MvPolynomial.eval v P = 0)
    (hQ : MvPolynomial.eval v Q ≠ 0) (hi : MvPolynomial.eval v (pderiv i P) ≠ 0) :
    (∀ j < m, homogeneousComponent j (translate v (P ^ m * Q)) = 0) ∧
      homogeneousComponent m (translate v (P ^ m * Q)) =
        C (MvPolynomial.eval v Q) * linearization v P ^ m ∧
      homogeneousComponent m (translate v (P ^ m * Q)) ≠ 0 := by
  exact ⟨fun j hj ↦ translated_factor_components_below v P Q m hP hj,
    translated_factor_component v P Q m hP,
    translated_factor_component_ne_zero v P Q m i hP hQ hi⟩

end

end MakarLimanov.NewtonTranslation
