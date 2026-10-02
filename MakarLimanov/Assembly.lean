import MakarLimanov.MatrixDescent
import MakarLimanov.Numerics

/-!
# Conditional final assembly

This theorem isolates the missing construction in `hZ`. It proves the infimum conclusion
from an explicit family of extension-field matrix witnesses. No such family is constructed
in this project yet. In particular, this is NOT a proof of `OriginalConjecture`.
-/

namespace MakarLimanov

universe u v
variable {K : Type u} [Field K] [IsAlgClosed K] {d : ℕ}

/-- Verified assembly of descent and the normalized-rank estimate, conditional on witnesses. -/
theorem rankInfimumZero_of_extension_witnesses (f : FreePoly K d) (D A : ℕ)
    (p : ℕ → ℕ) (hp : ∀ T, 0 < T → 0 < p T)
    (L : ℕ → Type v) [∀ T, Field (L T)] [∀ T, Algebra K (L T)]
    (Z : (T : ℕ) → Fin d → Mat (L T) (p T * T ^ 2))
    (hZ : ∀ T, 0 < T → (FreeAlgebra.lift K (Z T) f).rank ≤ 4 * D * A * p T * T) :
    RankInfimumZero f := by
  apply rankInfimumZero_of_quantitative_witnesses f (4 * D * A) (by positivity)
  intro T hT
  obtain ⟨X, hX⟩ := matrix_rank_descent f (Z T) (hZ T hT)
  refine ⟨p T * T ^ 2, Nat.mul_pos (hp T hT) (pow_pos hT _), X, ?_⟩
  have hratio := compressed_ratio_bound (hp T hT) hT hX
  simpa only [Nat.cast_mul, Nat.cast_pow] using hratio

end MakarLimanov
