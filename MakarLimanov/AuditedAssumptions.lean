import MakarLimanov.SymbolSeries
import MakarLimanov.BinarySupport
import MakarLimanov.Lattice
import MakarLimanov.SymbolRealization
import MakarLimanov.SymbolApproximation
import MakarLimanov.FiniteNewtonTheorem

/-!
# Proved interfaces for finite approximation and symbol realization

Both historical assumptions are now kernel-checked theorems. The namespace and
signatures are retained for callers of the original main-theorem assembly.
-/

noncomputable section

namespace MakarLimanov.AuditedAssumptions

open SymbolSeries ControlledMatrix Lattice

universe u v

/-- Finite Newton approximation, the output needed from the proposition in proof.tex §5.
The uniform bound `A` is chosen before the precision. All operations in the residual
are the already constructed star-algebra operations. No matrix rank conclusion is assumed.
-/
theorem finite_newton_approximation (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (g : FreeAlgebra K Bool) (hg : g ≠ 0) (hab : binaryAbelianize K g = 0) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ T : ℕ, 0 < T → Nonempty (SymbolApproximation K g A T) :=
  FiniteNewtonTheorem.finite_newton_approximation K g hg hab

/-- The proved unital, constant-preserving, filtered realization lemma in proof.tex §6.
The ring homomorphism formulation avoids treating the coefficient field `F` as central
in the star algebra. Only constants from `K` must map to scalar matrices. A Laurent
lower bound `b` becomes the matrix jump bound `-b`, with no extra factor of `p`.
-/
-- The historical assumption below is now discharged by the concrete realization.
theorem symbol_realization (K : Type u) (F : Type v)
    [Field K] [Field F] [Algebra K F] [CharZero F]
    (p : ℕ) (hp : 0 < p) (δ η : Derivation K F F) (h : Function.Commute δ η) :
    ∃ ρ : StarSeries p hp δ η h →+* Controlled (InLattice p) F,
      (∀ c : K, ρ (algebraMap K (StarSeries p hp δ η h) c) =
        algebraMap F (Controlled (InLattice p) F) (algebraMap K F c)) ∧
      ∀ (U : StarSeries p hp δ η h) (b : ℤ), LowerBound b U.toSeries →
        HasBound (ρ U).entries (-b) :=
  SymbolRealization.exists_realization p hp δ η h

end MakarLimanov.AuditedAssumptions
