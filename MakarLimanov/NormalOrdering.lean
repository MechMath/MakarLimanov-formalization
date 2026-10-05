import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
namespace MakarLimanov.NormalOrdering
open Finset
variable {k B A : Type*} [CommRing k] [CommRing B] [Ring A] [Algebra k B]
/-- Binomial normal ordering from the single commutator identity. -/
theorem normal_order (φ : B →+* A) (D : Derivation k B B) (T : A)
    (hcomm : ∀ b, φ b * T = T * φ b + φ (D b)) (b : B) (n : ℕ) :
    φ b * T^n = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      n.choose ab.1 • (T^ab.1 * φ (D^[ab.2] b)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, Finset.sum_mul,
      sum_antidiagonal_choose_succ_nsmul (fun a c ↦ T^a * φ (D^[c] b)) n]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    rintro ⟨a,c⟩ hac
    have hn := Finset.HasAntidiagonal.mem_antidiagonal.mp hac
    rw [n.choose_symm_of_eq_add hn.symm]
    simp only [smul_mul_assoc, mul_assoc, hcomm, mul_add, pow_succ,
      Function.iterate_succ_apply']
    simp only [← mul_assoc, smul_add]
    abel
/-- Multiplication by elements of a commutative algebra, as linear endomorphisms. -/
def multiplicationHom : B →+* Module.End k B where
  toFun := LinearMap.mulLeft k
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp [add_mul]
  map_mul' a b := by ext x; simp [mul_assoc]

lemma negative_derivation_commutator (D : Derivation k B B) (b : B) :
    multiplicationHom b * (-D.toLinearMap) =
      (-D.toLinearMap) * multiplicationHom b + multiplicationHom (D b) := by
  ext x
  simp [multiplicationHom, Derivation.leibniz, Module.End.mul_apply]
  ring

/-- Normal ordering for the actual differential operator T = -D. -/
theorem derivative_normal_order (D : Derivation k B B) (b : B) (n : ℕ) :
    multiplicationHom b * (-D.toLinearMap)^n = ∑ ac ∈ Finset.HasAntidiagonal.antidiagonal n,
      n.choose ac.1 • ((-D.toLinearMap)^ac.1 * multiplicationHom (D^[ac.2] b)) :=
  normal_order multiplicationHom D (-D.toLinearMap) (negative_derivation_commutator D) b n
end MakarLimanov.NormalOrdering

namespace MakarLimanov.NormalOrdering

variable {A : Type*} [Ring A]

/-- Binomial normal ordering along a specified sequence of iterated
commutators; no extension of that sequence to all ring elements is needed. -/
theorem normal_order_sequence (b : ℕ → A) (T : A)
    (hcomm : ∀ j, b j * T = T * b j + b (j + 1)) (n : ℕ) :
    b 0 * T ^ n = ∑ ac ∈ Finset.HasAntidiagonal.antidiagonal n,
      n.choose ac.1 • (T ^ ac.1 * b ac.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, Finset.sum_mul,
      Finset.sum_antidiagonal_choose_succ_nsmul (fun a c ↦ T ^ a * b c) n]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    rintro ⟨a, c⟩ hac
    rw [n.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hac).symm]
    rw [smul_mul_assoc, mul_assoc, hcomm c, mul_add]
    simp only [pow_succ, ← mul_assoc, smul_add]
    abel

end MakarLimanov.NormalOrdering

namespace MakarLimanov.NormalOrdering

variable {A : Type*} [Ring A]

/-- Normal ordering needs only the iterated commutator identity; the ambient
ring may itself be noncommutative. -/
theorem normal_order_iterates (d : A → A) (T : A)
    (hcomm : ∀ b, b * T = T * b + d b) (b : A) (n : ℕ) :
    b * T ^ n = ∑ ac ∈ Finset.HasAntidiagonal.antidiagonal n,
      n.choose ac.1 • (T ^ ac.1 * d^[ac.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, Finset.sum_mul,
      Finset.sum_antidiagonal_choose_succ_nsmul (fun a c ↦ T ^ a * d^[c] b) n]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    rintro ⟨a, c⟩ hac
    rw [n.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hac).symm]
    rw [smul_mul_assoc, mul_assoc, hcomm (d^[c] b), mul_add]
    simp only [pow_succ, Function.iterate_succ_apply']
    simp only [← mul_assoc, smul_add]
    abel

/-- A commuting first commutator gives the derivative formula for every
positive power, without division or characteristic assumptions. -/
theorem pow_commutator (W T C : A) (hcomm : W * T = T * W + C)
    (hc : Commute W C) (n : ℕ) :
    W ^ (n + 1) * T = T * W ^ (n + 1) + (n + 1) • (W ^ n * C) := by
  induction n with
  | zero => simpa using hcomm
  | succ n ih =>
    rw [pow_succ, mul_assoc, hcomm, mul_add, ← mul_assoc, ih, add_mul]
    rw [mul_assoc T, ← pow_succ, smul_mul_assoc]
    rw [mul_assoc (W ^ n), hc.symm.eq, ← mul_assoc, ← pow_succ]
    simp only [Nat.succ_eq_add_one, add_nsmul, one_nsmul]
    abel

end MakarLimanov.NormalOrdering
