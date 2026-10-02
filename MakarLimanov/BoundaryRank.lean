import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Common boundary rank bound

This proves the last linear-algebra step of Proposition 6.2: a matrix supported on prescribed
rows or columns has rank at most the sum of the sizes of those sets. It does not assume
that the paper's infinite-matrix realization or its compression has been constructed.
-/

namespace MakarLimanov

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem matrix_rank_add_le (A B : Matrix ι ι K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Coordinate projection onto a finite set. -/
noncomputable def coordinateProjection (s : Finset ι) : Matrix ι ι K :=
  Matrix.diagonal (fun i ↦ if i ∈ s then 1 else 0)

theorem rank_coordinateProjection (s : Finset ι) :
    (coordinateProjection (K := K) s).rank = s.card := by
  classical
  rw [coordinateProjection, Matrix.rank_diagonal]
  simp

/-- Common row/column support gives an additive, rather than word-count-dependent, bound. -/
theorem rank_le_boundary (Q : Matrix ι ι K) (rows cols : Finset ι)
    (hsupport : ∀ i j, i ∉ rows → j ∉ cols → Q i j = 0) :
    Q.rank ≤ rows.card + cols.card := by
  classical
  let P : Matrix ι ι K := coordinateProjection rows
  let C : Matrix ι ι K := coordinateProjection cols
  have decomp : Q = P * Q + ((1 - P) * Q) * C := by
    ext i j
    simp only [P, C, sub_mul, one_mul, Matrix.add_apply, Matrix.mul_diagonal,
      coordinateProjection, Matrix.sub_apply, Matrix.diagonal_mul]
    by_cases hi : i ∈ rows <;> by_cases hj : j ∈ cols <;>
      simp_all
  calc
    Q.rank = (P * Q + ((1 - P) * Q) * C).rank := congrArg Matrix.rank decomp
    _ ≤ (P * Q).rank + (((1 - P) * Q) * C).rank := matrix_rank_add_le _ _
    _ ≤ P.rank + C.rank := Nat.add_le_add
      (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
    _ = rows.card + cols.card := by simp [P, C, rank_coordinateProjection]

end MakarLimanov
