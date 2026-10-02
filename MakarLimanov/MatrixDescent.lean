import MakarLimanov.Statement
import MakarLimanov.Descent
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Descent of a free-polynomial matrix rank bound

We use a rank factorization instead of minors to encode the rank bound by polynomial equations.
This is an alternative formal proof of the paper's descent lemma.
-/

namespace MakarLimanov

variable {K : Type*} [Field K]

set_option backward.isDefEq.respectTransparency false in
/-- A square matrix factors through a coordinate space of dimension exactly its rank. -/
theorem matrix_rank_factorization {n : ℕ} (M : Mat K n) :
    ∃ A : Matrix (Fin n) (Fin M.rank) K,
      ∃ B : Matrix (Fin M.rank) (Fin n) K, A * B = M := by
  let b := Module.finBasis K (LinearMap.range M.mulVecLin)
  let e := Pi.basisFun K (Fin n)
  refine ⟨LinearMap.toMatrix b e (LinearMap.range M.mulVecLin).subtype,
    LinearMap.toMatrix e b M.mulVecLin.rangeRestrict, ?_⟩
  rw [← LinearMap.toMatrix_comp e b e
    (LinearMap.range M.mulVecLin).subtype M.mulVecLin.rangeRestrict]
  change LinearMap.toMatrix e e M.mulVecLin = M
  change LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n))
    (Matrix.toLin' M) = M
  simp

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

/-- Entrywise coefficient specialization commutes with free-polynomial evaluation. -/
theorem map_free_eval {d n : ℕ} (f : FreePoly K d) (Z : Fin d → Mat R n)
    (φ : R →ₐ[K] S) :
    (FreeAlgebra.lift K Z f).map φ = FreeAlgebra.lift K (fun i ↦ (Z i).map φ) f := by
  have h : φ.mapMatrix.comp (FreeAlgebra.lift K Z) =
      FreeAlgebra.lift K (fun i ↦ (Z i).map φ) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp
  exact DFunLike.congr_fun h f

private abbrev RankCoords (d n r : ℕ) :=
  (Fin d × Fin n × Fin n) ⊕ (Fin n × Fin r) ⊕ (Fin r × Fin n)

private noncomputable def genericTuple (K : Type*) [Field K] (d n r : ℕ) :
    Fin d → Mat (MvPolynomial (RankCoords d n r) K) n :=
  fun l i j ↦ MvPolynomial.X (Sum.inl (l, i, j))

private noncomputable def genericLeft (K : Type*) [Field K] (d n r : ℕ) :
    Matrix (Fin n) (Fin r) (MvPolynomial (RankCoords d n r) K) :=
  fun i j ↦ MvPolynomial.X (Sum.inr (Sum.inl (i, j)))

private noncomputable def genericRight (K : Type*) [Field K] (d n r : ℕ) :
    Matrix (Fin r) (Fin n) (MvPolynomial (RankCoords d n r) K) :=
  fun i j ↦ MvPolynomial.X (Sum.inr (Sum.inr (i, j)))

private noncomputable def rankEquations {d n r : ℕ} (f : FreePoly K d) :
    Mat (MvPolynomial (RankCoords d n r) K) n :=
  FreeAlgebra.lift K (genericTuple K d n r) f - genericLeft K d n r * genericRight K d n r

private theorem specialize_rankEquations {d n r : ℕ} (f : FreePoly K d)
    (a : RankCoords d n r → R) (i j : Fin n) :
    MvPolynomial.aeval a (rankEquations f i j) =
      FreeAlgebra.lift (A := Mat R n) K (fun l i j ↦ a (Sum.inl (l, i, j))) f i j -
        ∑ t : Fin r, a (Sum.inr (Sum.inl (i, t))) * a (Sum.inr (Sum.inr (t, j))) := by
  have h := congrArg (fun M : Mat R n ↦ M i j)
    (map_free_eval f (genericTuple K d n r) (MvPolynomial.aeval a))
  have htuple : (fun l ↦ (genericTuple K d n r l).map (MvPolynomial.aeval a)) =
      (fun l i j ↦ a (Sum.inl (l, i, j))) := by
    funext l i j
    simp [genericTuple]
  simp only [Matrix.map_apply, htuple] at h
  simp [rankEquations, Matrix.sub_apply, Matrix.mul_apply, genericLeft, genericRight,
    map_sum, map_mul, map_sub, h]

variable {L : Type*} [Field L] [Algebra K L]

/-- Polynomial equations for a rank factorization descend to the algebraically closed base. -/
theorem factorization_descent [IsAlgClosed K] {d n r : ℕ} (f : FreePoly K d)
    (Z : Fin d → Mat L n) (A : Matrix (Fin n) (Fin r) L)
    (B : Matrix (Fin r) (Fin n) L) (h : FreeAlgebra.lift K Z f = A * B) :
    ∃ X : Fin d → Mat K n, ∃ U : Matrix (Fin n) (Fin r) K,
      ∃ V : Matrix (Fin r) (Fin n) K, eval f X = U * V := by
  let z : RankCoords d n r → L :=
    Sum.elim (fun ⟨l, i, j⟩ ↦ Z l i j)
      (Sum.elim (fun ⟨i, j⟩ ↦ A i j) (fun ⟨i, j⟩ ↦ B i j))
  let equations : Set (MvPolynomial (RankCoords d n r) K) :=
    Set.range (fun ij : Fin n × Fin n ↦ rankEquations f ij.1 ij.2)
  have hz : ∀ p ∈ equations, MvPolynomial.aeval z p = 0 := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rw [specialize_rankEquations]
    change FreeAlgebra.lift K Z f i j - (A * B) i j = 0
    rw [h, sub_self]
  obtain ⟨a, ha⟩ := polynomial_system_descent equations z hz
  refine ⟨fun l i j ↦ a (Sum.inl (l, i, j)),
    fun i j ↦ a (Sum.inr (Sum.inl (i, j))),
    fun i j ↦ a (Sum.inr (Sum.inr (i, j))), ?_⟩
  ext i j
  have heq := ha (rankEquations f i j) ⟨(i, j), rfl⟩
  rw [specialize_rankEquations] at heq
  exact sub_eq_zero.mp heq

/-- The full rank-descent lemma: no algebraicity or finiteness assumption on the extension. -/
theorem matrix_rank_descent [IsAlgClosed K] {d n r : ℕ} (f : FreePoly K d)
    (Z : Fin d → Mat L n) (h : (FreeAlgebra.lift K Z f).rank ≤ r) :
    ∃ X : Fin d → Mat K n, (eval f X).rank ≤ r := by
  obtain ⟨A, B, hAB⟩ := matrix_rank_factorization (FreeAlgebra.lift K Z f)
  obtain ⟨X, U, V, hUV⟩ := factorization_descent f Z A B hAB.symm
  refine ⟨X, ?_⟩
  rw [hUV]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_width U).trans h)

end MakarLimanov
