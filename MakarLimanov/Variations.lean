import MakarLimanov.Compression
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Variations of a free polynomial

The auxiliary polynomial variable is central, although its coefficient algebra need not be
commutative. Its coefficients are the actual variations in the second free generator.
-/

-- Preserve definition unfolding used by these proofs across Lean versions.
set_option backward.isDefEq.respectTransparency false

namespace MakarLimanov.Variations

open Polynomial

noncomputable section

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- Substitute `x` and `z + v t`, with a central auxiliary variable `t`. -/
def expansion (x z v : A) : FreeAlgebra k Bool →ₐ[k] Polynomial A :=
  FreeAlgebra.lift k (fun b ↦ if b then C z + C v * X else C x)

/-- The coefficient of degree `n` in the perturbation of the second generator. -/
def variation (f : FreeAlgebra k Bool) (x z v : A) (n : ℕ) : A :=
  (expansion x z v f).coeff n

@[simp] theorem expansion_false (x z v : A) :
    expansion (k := k) x z v (FreeAlgebra.ι k false) = C x := by simp [expansion]

@[simp] theorem expansion_true (x z v : A) :
    expansion (k := k) x z v (FreeAlgebra.ι k true) = C z + C v * X := by
  simp [expansion]

/-- Evaluation at a central parameter recovers the original ordered substitution. -/
theorem eval_expansion (f : FreeAlgebra k Bool) (x z v t : A)
    (ht : ∀ a : A, Commute a t) :
    (expansion x z v f).eval₂ (RingHom.id A) t =
      FreeAlgebra.lift k (fun b ↦ if b then z + v * t else x) f := by
  have hh : (eval₂AlgHom (AlgHom.id k A) t ht).comp (expansion x z v) =
      FreeAlgebra.lift k (fun b ↦ if b then z + v * t else x) := by
    apply FreeAlgebra.hom_ext
    funext b
    cases b <;> simp [expansion, eval₂AlgHom]
  exact DFunLike.congr_fun hh f

@[simp] theorem variation_zero (f : FreeAlgebra k Bool) (x z v : A) :
    variation f x z v 0 = FreeAlgebra.lift k (fun b ↦ if b then z else x) f := by
  simpa [variation] using eval_expansion f x z v 0 (fun a ↦ Commute.zero_right a)

@[simp] theorem variation_add (f g : FreeAlgebra k Bool) (x z v : A) (n : ℕ) :
    variation (f + g) x z v n = variation f x z v n + variation g x z v n := by
  simp [variation]

/-- Ordered convolution, with no commutativity assumption on the coefficient algebra. -/
theorem variation_mul (f g : FreeAlgebra k Bool) (x z v : A) (n : ℕ) :
    variation (f * g) x z v n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      variation f x z v ij.1 * variation g x z v ij.2 := by
  simp [variation, coeff_mul]

private theorem coeff_rescale (c : A) (hc : ∀ a : A, Commute a c)
    (q : Polynomial A) (n : ℕ) :
    (q.eval₂ C (C c * X)).coeff n = c ^ n * q.coeff n := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp [eval₂_add, hq, hr, mul_add]
  | monomial m a =>
    rw [eval₂_monomial, (commute_X (C c)).symm.mul_pow, ← map_pow,
      ← mul_assoc, ← map_mul]
    simp only [coeff_C_mul_X_pow, coeff_monomial, eq_comm (a := m) (b := n)]
    by_cases h : n = m
    · subst n
      simpa only [ite_true] using ((hc a).pow_right m).eq
    · simp only [h, ↓reduceIte, mul_zero]

/-- Moving a central multiplier out of each chosen perturbation position gives its nth power. -/
theorem variation_central_mul (f : FreeAlgebra k Bool) (x z v c : A)
    (hc : ∀ a : A, Commute a c) (n : ℕ) :
    variation f x z (c * v) n = c ^ n * variation f x z v n := by
  let ρ : Polynomial A →ₐ[k] Polynomial A :=
    eval₂AlgHom CAlgHom (C c * X) (fun a ↦
      ((hc a).map C).mul_right (commute_X (C a)).symm)
  have hh : ρ.comp (expansion x z v) = expansion (k := k) x z (c * v) := by
    apply FreeAlgebra.hom_ext
    funext b
    cases b <;> simp [ρ, expansion, eval₂AlgHom, ← mul_assoc, ← map_mul, (hc v).eq]
  have heq := DFunLike.congr_fun hh f
  change (expansion x z (c * v) f).coeff n = c ^ n * (expansion x z v f).coeff n
  rw [← heq]
  exact coeff_rescale c hc _ n

/-- The variations reconstruct evaluation at any central parameter. -/
theorem sum_variation (f : FreeAlgebra k Bool) (x z v t : A)
    (ht : ∀ a : A, Commute a t) :
    ∑ n ∈ (expansion x z v f).support, variation f x z v n * t ^ n =
      FreeAlgebra.lift k (fun b ↦ if b then z + v * t else x) f := by
  simpa only [eval₂_eq_sum, Polynomial.sum, RingHom.id_apply, variation]
    using eval_expansion f x z v t ht

/-- Algebra homomorphisms preserve every variation, including its coefficient order. -/
theorem map_variation {B : Type*} [Ring B] [Algebra k B] (φ : A →ₐ[k] B)
    (f : FreeAlgebra k Bool) (x z v : A) (n : ℕ) :
    φ (variation f x z v n) = variation f (φ x) (φ z) (φ v) n := by
  have hh : (mapAlgHom φ).comp (expansion x z v) =
      expansion (k := k) (φ x) (φ z) (φ v) := by
    apply FreeAlgebra.hom_ext
    funext b
    cases b <;> simp [expansion]
  have heq := congrArg (fun q : Polynomial B ↦ q.coeff n) (DFunLike.congr_fun hh f)
  simpa [variation] using heq

private theorem word_expansion_degree (w : List Bool) (x z v : A) :
    ((w.map (fun b : Bool ↦ if b then C z + C v * X else C x)).prod).natDegree ≤
      w.count true := by
  induction w with
  | nil => simp
  | cons b w ih =>
    simp only [List.map_cons, List.prod_cons]
    apply natDegree_mul_le.trans
    cases b
    · simpa using ih
    · have hlin : (C z + C v * X).natDegree ≤ 1 := by
        apply natDegree_add_le_of_degree_le (by simp)
        exact (natDegree_C_mul_le v X).trans natDegree_X_le
      simpa [Nat.add_comm] using Nat.add_le_add hlin ih

/-- A bound on the number of second-generator letters bounds the number of variations. -/
theorem expansion_degree_le (f : FreeAlgebra k Bool) (x z v : A) (M : ℕ)
    (hM : ∀ w ∈ (ControlledMatrix.wordCoefficients f).coeff.support, w.toList.count true ≤ M) :
    (expansion x z v f).natDegree ≤ M := by
  classical
  rw [expansion, ControlledMatrix.lift_eq_word_sum]
  apply natDegree_sum_le_of_forall_le
  intro w hw
  exact (natDegree_smul_le _ _).trans ((word_expansion_degree _ x z v).trans (hM w hw))

/-- No formal coefficient beyond the actual word-count bound can survive evaluation. -/
theorem variation_eq_zero_of_count_lt (f : FreeAlgebra k Bool) (x z v : A) (M n : ℕ)
    (hM : ∀ w ∈ (ControlledMatrix.wordCoefficients f).coeff.support, w.toList.count true ≤ M)
    (hn : M < n) : variation f x z v n = 0 :=
  coeff_eq_zero_of_natDegree_lt ((expansion_degree_le f x z v M hM).trans_lt hn)

/- The change of base point used by each Newton correction is exact even in a
noncommutative coefficient algebra. -/
theorem expansion_shift (f : FreeAlgebra k Bool) (x z v : A) :
    expansion x (z + v) v f = (expansion x z v f).eval₂ C (1 + X) := by
  let τ : Polynomial A →ₐ[k] Polynomial A :=
    eval₂AlgHom CAlgHom (1 + X) (fun a ↦
      (Commute.one_right (C a)).add_right (commute_X (C a)).symm)
  have hh : τ.comp (expansion x z v) = expansion (k := k) x (z + v) v := by
    apply FreeAlgebra.hom_ext
    funext b
    cases b <;> simp [τ, expansion, eval₂AlgHom, mul_add, add_assoc]
  exact (DFunLike.congr_fun hh f).symm

/-- All variations after a correction are finite binomial transforms of the old ones. -/
theorem variation_shift (f : FreeAlgebra k Bool) (x z v : A) (n : ℕ) :
    variation f x (z + v) v n =
      ∑ j ∈ (expansion x z v f).support,
        variation f x z v j * (j.choose n : A) := by
  classical
  unfold variation
  rw [expansion_shift, eval₂_eq_sum]
  simp [Polynomial.sum, coeff_C_mul, coeff_one_add_X_pow]

end

end MakarLimanov.Variations
