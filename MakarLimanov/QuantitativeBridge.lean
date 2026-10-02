import MakarLimanov.ControlledWitness
import MakarLimanov.MainTheoremBridge

namespace MakarLimanov

noncomputable section

open ControlledMatrix Lattice

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- The exact finite-precision output required from the Newton construction. -/
structure ControlledApproximation (f : FreePoly K 2) where
  D : ℕ
  A : ℕ
  bound : ControlledMatrix.DegreeBound (σ := Fin 2) (changeCoefficients (L := K) f) D
  approx : ∀ T : ℕ, 0 < T → ∃ p : ℕ, 0 < p ∧
    ∃ X : Fin 2 → Controlled (InLattice p) K,
      (∀ i, HasBound (X i).entries (p * A)) ∧
      HasBound (FreeAlgebra.lift K X (changeCoefficients (L := K) f)).entries
        (-(p * T : ℤ))

/-- Once the explicit controlled Newton family is supplied, compression and descent
prove the rank-infimum conclusion without any further analytic assumptions. -/
theorem rankInfimumZero_of_controlled_approximation
    (f : FreePoly K 2) (h : ControlledApproximation f) :
    RankInfimumZero f := by
  apply rankInfimumZero_of_controlled (L := K) f h.D h.A
  intro T hT
  obtain ⟨p, hp, X, hX, hres⟩ := h.approx T hT
  obtain ⟨Z, hZ⟩ := matrix_witness_of_controlled hp f h.bound X hX hres
  obtain ⟨W, hW⟩ := matrix_rank_descent f Z hZ
  exact ⟨p, hp, X, h.bound, hX, hres⟩

end
end MakarLimanov
