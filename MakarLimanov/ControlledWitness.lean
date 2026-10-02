import MakarLimanov.Lattice
import MakarLimanov.Assembly
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual finite matrix witnesses obtained from controlled infinite residuals. -/

namespace MakarLimanov
open ControlledMatrix Lattice
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {d : ℕ}

noncomputable def changeCoefficients (f : FreePoly K d) : FreePoly L d :=
  FreeAlgebra.lift K (FreeAlgebra.ι L) f

lemma eval_changeCoefficients {n : ℕ} (f : FreePoly K d) (Z : Fin d → Mat L n) :
    FreeAlgebra.lift L Z (changeCoefficients f) = FreeAlgebra.lift K Z f := by
  have h : ((FreeAlgebra.lift L Z).restrictScalars K).comp
      (FreeAlgebra.lift K (FreeAlgebra.ι L)) = FreeAlgebra.lift K Z := by
    apply FreeAlgebra.hom_ext
    funext i
    simp
  exact DFunLike.congr_fun h f

/-- Reindexing a matrix tuple commutes with ordered free-polynomial evaluation. -/
lemma eval_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : FreePoly L d) (Z : Fin d → Matrix ι ι L) (e : ι ≃ κ) :
    FreeAlgebra.lift L (fun i ↦ Matrix.reindex e e (Z i)) f =
      Matrix.reindex e e (FreeAlgebra.lift L Z f) := by
  have h : (Matrix.reindexAlgEquiv L L e).toAlgHom.comp (FreeAlgebra.lift L Z) =
      FreeAlgebra.lift L (fun i ↦ Matrix.reindex e e (Z i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp
  exact (DFunLike.congr_fun h f).symm

/-- A controlled approximation constructs matrices of exactly the required size. -/
theorem matrix_witness_of_controlled {p T A D : ℕ} (hp : 0 < p)
    (f : FreePoly K d) (hD : DegreeBound (changeCoefficients (L := L) f) D)
    (X : Fin d → Controlled (InLattice p) L)
    (hX : ∀ i, HasBound (X i).entries (p * A))
    (hres : HasBound (FreeAlgebra.lift L X (changeCoefficients f)).entries (-(p*T : ℤ))) :
    ∃ Z : Fin d → Mat L (p * T^2), (FreeAlgebra.lift K Z f).rank ≤ 4 * D * A * p * T := by
  classical
  let e : Square p T ≃ Fin (p*T^2) :=
    (Fintype.equivFin (Square p T)).trans (finCongr (square_card p T))
  let Z₀ : Fin d → Matrix (Square p T) (Square p T) L :=
    fun i ↦ compress (embedding hp) (X i).entries
  refine ⟨fun i ↦ Matrix.reindex e e (Z₀ i), ?_⟩
  rw [← eval_changeCoefficients, eval_reindex, Matrix.rank_reindex]
  exact compression_rank hp le_rfl (changeCoefficients f) hD X hX hres

/-- Completing the controlled approximation construction is sufficient for the original target. -/
theorem rankInfimumZero_of_controlled [IsAlgClosed K] (f : FreePoly K d) (D A : ℕ)
    (approx : ∀ T : ℕ, 0 < T → ∃ (p : ℕ), 0 < p ∧
      ∃ X : Fin d → Controlled (InLattice p) L,
        DegreeBound (changeCoefficients (L := L) f) D ∧
        (∀ i, HasBound (X i).entries (p*A)) ∧
        HasBound (FreeAlgebra.lift L X (changeCoefficients f)).entries (-(p*T : ℤ))) :
    RankInfimumZero f := by
  apply rankInfimumZero_of_quantitative_witnesses f (4*D*A) (by positivity)
  intro T hT
  obtain ⟨p, hp, X, hD, hX, hres⟩ := approx T hT
  obtain ⟨Z, hZ⟩ := matrix_witness_of_controlled hp f hD X hX hres
  obtain ⟨W, hW⟩ := matrix_rank_descent f Z hZ
  refine ⟨p*T^2, Nat.mul_pos hp (pow_pos hT _), W, ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_pow] using compressed_ratio_bound hp hT hW

/-- Completing the controlled approximation construction is sufficient for the original target. -/
theorem rankInfimumZero_of_controlled_family [IsAlgClosed K] (f : FreePoly K d) (D A : ℕ)
    (E : ℕ → Type*) [∀ T, Field (E T)] [∀ T, Algebra K (E T)]
    (approx : ∀ T : ℕ, 0 < T → ∃ (p : ℕ), 0 < p ∧
      ∃ X : Fin d → Controlled (InLattice p) (E T),
        DegreeBound (changeCoefficients (L := E T) f) D ∧
        (∀ i, HasBound (X i).entries (p*A)) ∧
        HasBound (FreeAlgebra.lift (E T) X (changeCoefficients f)).entries (-(p*T : ℤ))) :
    RankInfimumZero f := by
  apply rankInfimumZero_of_quantitative_witnesses f (4*D*A) (by positivity)
  intro T hT
  obtain ⟨p, hp, X, hD, hX, hres⟩ := approx T hT
  obtain ⟨Z, hZ⟩ := matrix_witness_of_controlled hp f hD X hX hres
  obtain ⟨W, hW⟩ := matrix_rank_descent f Z hZ
  refine ⟨p*T^2, Nat.mul_pos hp (pow_pos hT _), W, ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_pow] using compressed_ratio_bound hp hT hW

end MakarLimanov
