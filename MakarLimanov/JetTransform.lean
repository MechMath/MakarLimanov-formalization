import MakarLimanov.TaylorSeries
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! The invertible binomial jet substitution used to compare different symbol slopes. -/

namespace MakarLimanov.JetTransform

noncomputable section

section Transform

variable {R : Type*} [CommRing R]

/-- The binomial transform, recursively organized by the Pascal recurrence. -/
def transform (s : R) (a : ℕ → R) : ℕ → R
  | 0 => a 0
  | n + 1 => s * transform s a n + transform s (fun j ↦ a (j + 1)) n

@[simp] theorem transform_zero_index (s : R) (a : ℕ → R) : transform s a 0 = a 0 := rfl

theorem transform_add (s : R) (a b : ℕ → R) (n : ℕ) :
    transform s (fun j ↦ a j + b j) n = transform s a n + transform s b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [transform, ih]; ring

theorem transform_mul (s c : R) (a : ℕ → R) (n : ℕ) :
    transform s (fun j ↦ c * a j) n = c * transform s a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [transform, ih]; ring

@[simp] theorem transform_zero (a : ℕ → R) (n : ℕ) : transform 0 a n = a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [transform, ih]

/-- Composing binomial transforms adds their parameters. -/
theorem transform_comp (s t : R) (a : ℕ → R) (n : ℕ) :
    transform s (transform t a) n = transform (s + t) a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [transform]
    have hs : (fun j ↦ transform t a (j + 1)) =
        (fun j ↦ t * transform t a j + transform t (fun l ↦ a (l + 1)) j) := rfl
    rw [hs, transform_add, transform_mul, ih, ih, transform]
    ring

theorem map_transform {S : Type*} [CommRing S] (φ : R →+* S)
    (s : R) (a : ℕ → R) (n : ℕ) :
    φ (transform s a n) = transform (φ s) (fun j ↦ φ (a j)) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [transform, map_add, map_mul, ih]

/-- The recurrence equals the binomial sum appearing in the jet substitution formula. -/
theorem transform_eq_sum (s : R) (a : ℕ → R) (n : ℕ) :
    transform s a n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • (s ^ ij.2 * a ij.1) := by
  induction n generalizing a with
  | zero => simp [transform]
  | succ n ih =>
    rw [transform, ih, ih,
      Finset.sum_antidiagonal_choose_succ_nsmul (fun i j ↦ s ^ j * a i) n]
    rw [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro ij hij
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
    · apply Finset.sum_congr rfl
      rintro ⟨i,j⟩ hij
      rw [Nat.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hij).symm]

end Transform

section Differentiation

variable {k F : Type*} [CommRing k] [Field F] [Algebra k F]

theorem derivation_transform (D : Derivation k F F) (s : F) (hs : D s = 0)
    (a : ℕ → F) (n : ℕ) :
    D (transform s a n) = transform s (fun j ↦ D (a j)) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [transform, Derivation.leibniz, hs, ih, mul_comm]

theorem iterate_transform (D : Derivation k F F) (s : F) (hs : D s = 0)
    (a : ℕ → F) (n i : ℕ) :
    D^[i] (transform s a n) = transform s (fun j ↦ D^[i] (a j)) n := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, derivation_transform D s hs]
    simp only [Function.iterate_succ_apply']

/-- Iterating a derivation on an eigenvector times an arbitrary element gives the binomial twist. -/
theorem iterate_eigenvector_mul (H : Derivation k F F) (e s w : F)
    (he : H e = s * e) (hs : H s = 0) (j : ℕ) :
    H^[j] (e * w) = e * transform s (fun l ↦ H^[l] w) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz,
      derivation_transform H s hs, he, transform]
    simp only [Function.iterate_succ_apply', smul_eq_mul]
    ring

/-- The exact mixed-jet substitution formula (3.8), including the nonzero scaling factor. -/
theorem mixed_eigenvector_mul (D H : Derivation k F F) (e s w : F)
    (heD : D e = 0) (heH : H e = s * e) (hsD : D s = 0) (hsH : H s = 0)
    (i j : ℕ) :
    D^[i] (H^[j] (e * w)) = e * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
      j.choose ab.1 • (s ^ ab.2 * D^[i] (H^[ab.1] w)) := by
  rw [iterate_eigenvector_mul H e s w heH hsH,
    TaylorSeries.iterate_mul_constant D e heD, iterate_transform D s hsD,
    transform_eq_sum]

end Differentiation

section Jets

variable {F : Type*} [Field F]

/-- The unscaled triangular substitution on the infinite polynomial jet ring. -/
def shear (s : F) : MvPolynomial (ℕ × ℕ) F →ₐ[F] MvPolynomial (ℕ × ℕ) F :=
  MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
    transform (MvPolynomial.C s) (fun j ↦ MvPolynomial.X (ij.1, j)) ij.2)

@[simp] theorem shear_X (s : F) (i j : ℕ) :
    shear s (MvPolynomial.X (i,j)) =
      transform (MvPolynomial.C s) (fun l ↦ MvPolynomial.X (i,l)) j := by
  simp [shear]

@[simp] theorem shear_C (s a : F) : shear s (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [shear]

/-- The inverse triangular substitution has the negative parameter. -/
theorem shear_comp (s t : F) : (shear s).comp (shear t) = shear (s + t) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i,j⟩
  simp only [AlgHom.comp_apply, shear_X]
  have hm := map_transform (shear s).toRingHom (MvPolynomial.C t)
    (fun l ↦ MvPolynomial.X (i,l)) j
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, shear_C, shear_X] at hm
  rw [hm]
  rw [transform_comp, ← map_add, add_comm t s]

@[simp] theorem shear_zero : shear (0 : F) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i,j⟩
  simp

/-- Algebraic independence survives the triangular change of all mixed jets. -/
def shearEquiv (s : F) : MvPolynomial (ℕ × ℕ) F ≃ₐ[F] MvPolynomial (ℕ × ℕ) F :=
  AlgEquiv.ofAlgHom (shear s) (shear (-s))
    (by rw [shear_comp, add_neg_cancel, shear_zero])
    (by rw [shear_comp, neg_add_cancel, shear_zero])

/-- Uniformly multiply all jet variables by a field element. -/
def scale (e : F) : MvPolynomial (ℕ × ℕ) F →ₐ[F] MvPolynomial (ℕ × ℕ) F :=
  MvPolynomial.aeval (fun ij ↦ MvPolynomial.C e * MvPolynomial.X ij)

@[simp] theorem scale_X (e : F) (ij : ℕ × ℕ) :
    scale e (MvPolynomial.X ij) = MvPolynomial.C e * MvPolynomial.X ij := by
  simp [scale]

@[simp] theorem scale_C (e a : F) : scale e (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [scale]

theorem scale_comp (e f : F) : (scale e).comp (scale f) = scale (e * f) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp [mul_left_comm, mul_comm]

@[simp] theorem scale_one : scale (1 : F) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp

/-- Nonzero scaling is an automorphism of the jet ring. -/
def scaleEquiv (e : F) (he : e ≠ 0) :
    MvPolynomial (ℕ × ℕ) F ≃ₐ[F] MvPolynomial (ℕ × ℕ) F :=
  AlgEquiv.ofAlgHom (scale e) (scale e⁻¹)
    (by rw [scale_comp, mul_inv_cancel₀ he, scale_one])
    (by rw [scale_comp, inv_mul_cancel₀ he, scale_one])

/-- The precise invertible substitution `v = e w` in the mixed-jet coordinates. -/
def twistEquiv (e : F) (he : e ≠ 0) (s : F) :
    MvPolynomial (ℕ × ℕ) F ≃ₐ[F] MvPolynomial (ℕ × ℕ) F :=
  (shearEquiv s).trans (scaleEquiv e he)

theorem twistEquiv_X (e : F) (he : e ≠ 0) (s : F) (i j : ℕ) :
    twistEquiv e he s (MvPolynomial.X (i,j)) =
      MvPolynomial.C e * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        j.choose ab.1 • (MvPolynomial.C s ^ ab.2 * MvPolynomial.X (i,ab.1)) := by
  change scale e (shear s (MvPolynomial.X (i,j))) = _
  rw [shear_X]
  have hm := map_transform (scale e).toRingHom (MvPolynomial.C s)
    (fun l ↦ MvPolynomial.X (i,l)) j
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, scale_C, scale_X] at hm
  rw [hm]
  rw [transform_mul, transform_eq_sum]

/-- In particular, a nonzero leading-coefficient polynomial cannot disappear under the twist. -/
theorem twist_ne_zero_iff (e : F) (he : e ≠ 0) (s : F) (P : MvPolynomial (ℕ × ℕ) F) :
    twistEquiv e he s P ≠ 0 ↔ P ≠ 0 :=
  map_ne_zero_iff (twistEquiv e he s) (twistEquiv e he s).injective

/-- Evaluating after the jet automorphism is the actual mixed differentiation of `e*w`. -/
theorem eval_twist {k E : Type*} [CommRing k] [Field E] [Algebra k E] [Algebra F E]
    (D H : Derivation k E E) (e : F) (he : e ≠ 0) (s : F) (w : E)
    (heD : D (algebraMap F E e) = 0)
    (heH : H (algebraMap F E e) = algebraMap F E s * algebraMap F E e)
    (hsD : D (algebraMap F E s) = 0) (hsH : H (algebraMap F E s) = 0)
    (P : MvPolynomial (ℕ × ℕ) F) :
    MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))
        (twistEquiv e he s P) =
      MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
        D^[ij.1] (H^[ij.2] (algebraMap F E e * w))) P := by
  have hh : (MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w))).comp
        (twistEquiv e he s).toAlgHom =
      MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
        D^[ij.1] (H^[ij.2] (algebraMap F E e * w))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i,j⟩
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, twistEquiv_X, map_mul,
      map_sum, map_nsmul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    exact (mixed_eigenvector_mul D H _ _ w heD heH hsD hsH i j).symm
  exact DFunLike.congr_fun hh P

/-- Multiplication by a nonzero eigenvector preserves differential algebraic independence. -/
theorem twisted_generic {k E : Type*} [CommRing k] [Field E] [Algebra k E] [Algebra F E]
    (D H : Derivation k E E) (e : F) (he : e ≠ 0) (s : F) (w : E)
    (heD : D (algebraMap F E e) = 0)
    (heH : H (algebraMap F E e) = algebraMap F E s * algebraMap F E e)
    (hsD : D (algebraMap F E s) = 0) (hsH : H (algebraMap F E s) = 0)
    (hw : ∀ P : MvPolynomial (ℕ × ℕ) F, P ≠ 0 →
      MvPolynomial.aeval (fun ij : ℕ × ℕ ↦ D^[ij.1] (H^[ij.2] w)) P ≠ 0)
    (P : MvPolynomial (ℕ × ℕ) F) (hP : P ≠ 0) :
    MvPolynomial.aeval (fun ij : ℕ × ℕ ↦
      D^[ij.1] (H^[ij.2] (algebraMap F E e * w))) P ≠ 0 := by
  rw [← eval_twist D H e he s w heD heH hsD hsH]
  exact hw _ ((twist_ne_zero_iff e he s P).mpr hP)

end Jets

end

end MakarLimanov.JetTransform
