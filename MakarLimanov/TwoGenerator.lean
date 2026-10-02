import MakarLimanov.ScalarReduction
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The two-generator encoding

The code sends the i-th source letter to x y^(i+1). A parser proves that distinct words
remain distinct. The resulting map of free algebras is therefore injective.
-/

namespace MakarLimanov

private def parseWord : List Bool → ℕ × List ℕ
  | [] => (0, [])
  | true :: w => ((parseWord w).1 + 1, (parseWord w).2)
  | false :: w => (0, (parseWord w).1 :: (parseWord w).2)

private def encodeWord {d : ℕ} : List (Fin d) → List Bool
  | [] => []
  | i :: w => false :: (List.replicate (i.val + 1) true ++ encodeWord w)

private theorem parse_replicate (n : ℕ) (w : List Bool) :
    parseWord (List.replicate n true ++ w) = ((parseWord w).1 + n, (parseWord w).2) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, parseWord, ih, Nat.add_assoc]

private theorem parse_encode {d : ℕ} (w : List (Fin d)) :
    parseWord (encodeWord w) = (0, w.map (fun i ↦ i.val + 1)) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [encodeWord, parseWord, parse_replicate, ih]

private theorem encodeWord_injective {d : ℕ} : Function.Injective (@encodeWord d) := by
  intro u v h
  have h' := congrArg (fun w ↦ (parseWord w).2) h
  simp only [parse_encode] at h'
  exact List.map_injective_iff.mpr (fun i j h ↦ Fin.ext (Nat.add_right_cancel h)) h'

private theorem encodeWord_append {d : ℕ} (u v : List (Fin d)) :
    encodeWord (u ++ v) = encodeWord u ++ encodeWord v := by
  induction u with
  | nil => rfl
  | cons i u ih => simp [encodeWord, ih, List.append_assoc]

/-- The word-level code underlying xᵢ ↦ x y^(i+1). -/
def binaryWordCode (d : ℕ) : FreeMonoid (Fin d) →* FreeMonoid Bool where
  toFun w := FreeMonoid.ofList (encodeWord w.toList)
  map_one' := rfl
  map_mul' u v := congrArg FreeMonoid.ofList (encodeWord_append u.toList v.toList)

theorem binaryWordCode_injective (d : ℕ) : Function.Injective (binaryWordCode d) := by
  intro u v h
  apply FreeMonoid.toList.injective
  apply encodeWord_injective
  exact congrArg FreeMonoid.toList h

variable (K : Type*) [Field K]

/-- The induced injective algebra map, constructed through word coefficients. -/
noncomputable def binarySubstitution (d : ℕ) :
    FreePoly K d →ₐ[K] FreeAlgebra K Bool :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.comp
    ((MonoidAlgebra.mapDomainAlgHom K K (binaryWordCode d)).comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom)

theorem binarySubstitution_injective (d : ℕ) :
    Function.Injective (binarySubstitution K d) := by
  intro f g h
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  apply MonoidAlgebra.mapDomain_injective (binaryWordCode_injective d)
  exact FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.injective h

theorem binarySubstitution_generator {d : ℕ} (i : Fin d) :
    binarySubstitution K d (FreeAlgebra.ι K i) =
      FreeAlgebra.ι K false * FreeAlgebra.ι K true ^ (i.val + 1) := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  simp [binarySubstitution, FreeAlgebra.equivMonoidAlgebraFreeMonoid,
    MonoidAlgebra.mapDomainAlgHom, binaryWordCode, encodeWord]

/-- The binary substitution preserves the nonconstant hypothesis. -/
theorem binarySubstitution_nonconstant {d : ℕ} (f : FreePoly K d) (hf : Nonconstant f)
    (c : K) : binarySubstitution K d f ≠ algebraMap K (FreeAlgebra K Bool) c := by
  intro h
  apply hf c
  apply binarySubstitution_injective K d
  simpa using h

/-- Evaluation of the binary code gives the original tuple X Y, X Y², … . -/
theorem eval_binarySubstitution {d n : ℕ} (f : FreePoly K d) (X Y : Mat K n) :
    FreeAlgebra.lift (A := Mat K n) K (fun b ↦ if b then Y else X)
        (binarySubstitution K d f) =
      eval f (fun i ↦ X * Y ^ (i.val + 1)) := by
  have h : (FreeAlgebra.lift (A := Mat K n) K (fun b ↦ if b then Y else X)).comp
      (binarySubstitution K d) = FreeAlgebra.lift K (fun i ↦ X * Y ^ (i.val + 1)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [binarySubstitution_generator]
  exact DFunLike.congr_fun h f

/-- Commutative image of a two-letter free polynomial. -/
noncomputable def binaryAbelianize : FreeAlgebra K Bool →ₐ[K] MvPolynomial Bool K :=
  FreeAlgebra.lift K MvPolynomial.X

theorem binaryAbelianize_substitution {d : ℕ} (f : FreePoly K d) :
    binaryAbelianize K (binarySubstitution K d f) =
      MvPolynomial.aeval (fun i : Fin d ↦ MvPolynomial.X false *
        MvPolynomial.X true ^ (i.val + 1)) (abelianize f) := by
  have h : (binaryAbelianize K).comp (binarySubstitution K d) =
      (MvPolynomial.aeval (fun i : Fin d ↦ MvPolynomial.X false *
        MvPolynomial.X true ^ (i.val + 1))).comp abelianize := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [binaryAbelianize, binarySubstitution_generator, abelianize]
  exact DFunLike.congr_fun h f

/-- Normalization produces a nonzero commutator-ideal part in the binary algebra. -/
theorem binary_normalization {d : ℕ} (f : FreePoly K d) (hf : Nonconstant f)
    (c : K) (hc : c ≠ 0) (hab : abelianize f = MvPolynomial.C c) :
    ∃ g : FreeAlgebra K Bool, g ≠ 0 ∧ binaryAbelianize K g = 0 ∧
      1 + g = c⁻¹ • binarySubstitution K d f := by
  let h := c⁻¹ • binarySubstitution K d f
  have hne : h ≠ 1 := by
    intro heq
    have hmul := congrArg (fun z : FreeAlgebra K Bool ↦ c • z) heq
    have : binarySubstitution K d f = algebraMap K (FreeAlgebra K Bool) c := by
      simpa [h, smul_smul, hc, Algebra.algebraMap_eq_smul_one] using hmul
    exact binarySubstitution_nonconstant K f hf c this
  have habh : binaryAbelianize K h = 1 := by
    change binaryAbelianize K (c⁻¹ • binarySubstitution K d f) = 1
    rw [map_smul, binaryAbelianize_substitution, hab, MvPolynomial.aeval_C]
    simp [Algebra.smul_def, ← map_mul, hc]
  refine ⟨h - 1, sub_ne_zero.mpr hne, ?_, by simp [h]⟩
  simp [map_sub, habh]

/-- Nonzero scalar multiplication preserves matrix rank. -/
theorem matrix_rank_smul {n : ℕ} (c : K) (hc : c ≠ 0) (M : Mat K n) :
    (c • M).rank = M.rank := by
  unfold Matrix.rank
  have hlin : (c • M).mulVecLin = c • M.mulVecLin := by
    ext x i
    simp [Matrix.mulVecLin]
  rw [hlin, LinearMap.range_smul _ _ hc]

/-- The normalized binary conclusion still to be established by the symbol construction. -/
def NormalizedBinaryClaim : Prop :=
  ∀ g : FreeAlgebra K Bool, g ≠ 0 → binaryAbelianize K g = 0 →
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∃ X Y : Mat K n,
      ((FreeAlgebra.lift (A := Mat K n) K (fun b ↦ if b then Y else X) (1 + g)).rank : ℝ)
        / n < ε

/-- Exact reduction from the original theorem to the normalized binary construction. -/
theorem originalConjecture_of_normalizedBinary [IsAlgClosed K] [CharZero K]
    (normalized : NormalizedBinaryClaim K) (d : ℕ) : OriginalConjecture K d := by
  apply originalConjecture_of_constant_abelianization
  intro f hf hc
  obtain ⟨c, hc, hab⟩ := hc
  obtain ⟨g, hg, hgab, hgeq⟩ := binary_normalization K f hf c hc hab
  rw [rankInfimumZero_iff]
  intro ε hε
  obtain ⟨n, hn, X, Y, hXY⟩ := normalized g hg hgab ε hε
  refine ⟨n, hn, fun i ↦ X * Y ^ (i.val + 1), ?_⟩
  rw [hgeq, map_smul, matrix_rank_smul K c⁻¹ (inv_ne_zero hc),
    eval_binarySubstitution] at hXY
  exact hXY

end MakarLimanov
