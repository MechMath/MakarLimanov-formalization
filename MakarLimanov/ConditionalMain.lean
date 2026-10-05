import MakarLimanov.AuditedAssumptions
import MakarLimanov.CoefficientSupport
import MakarLimanov.TwoGenerator

/-!
# Main-theorem assembly using finite Newton approximation

The finite Newton construction and filtered realization are proved through the
historical `AuditedAssumptions` interface. Matrix compression, descent to the
algebraically closed base, and passage to arbitrarily small normalized rank are
proved here using the previously verified library.
-/

namespace MakarLimanov

open ControlledMatrix Lattice SymbolSeries SymbolSeries.StarSeries

noncomputable section

universe u

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- The normalized binary claim follows from finite Newton approximation and
the proved filtered symbol realization. -/
theorem normalizedBinaryClaim_of_audited_assumptions : NormalizedBinaryClaim K := by
  classical
  intro g hg hab
  obtain ⟨A, hA, happ⟩ := AuditedAssumptions.finite_newton_approximation K g hg hab
  let f : FreePoly K 2 := binaryToFinTwo (1 + g)
  let D : ℕ := wordDegree f
  have hf : RankInfimumZero f := by
    apply rankInfimumZero_of_quantitative_witnesses f (4 * D * A) (by positivity)
    intro T hT
    obtain ⟨S⟩ := happ T hT
    obtain ⟨ρ, hρc, hρb⟩ := AuditedAssumptions.symbol_realization
      K S.F S.p S.hp S.δ S.η S.commute
    let C := Controlled (InLattice S.p) S.F
    letI : Algebra K C := Algebra.compHom C (algebraMap K S.F)
    letI : IsScalarTower K S.F C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    let ρa : StarSeries S.p S.hp S.δ S.η S.commute →ₐ[K] C :=
      { ρ with commutes' := hρc }
    let U : Bool → StarSeries S.p S.hp S.δ S.η S.commute :=
      fun b ↦ ofSeries (if b then S.Z else distinguishedSymbol S.p)
    let X : Fin 2 → C := fun i ↦ ρa (U (finTwoEquiv i))
    have hUb : ∀ b, LowerBound (-(S.p * A : ℤ)) (toSeries (U b)) := by
      intro b
      cases b
      · change LowerBound (-(S.p * A : ℤ)) (distinguishedSymbol S.p)
        intro n hn
        apply HahnSeries.coeff_single_of_ne
        have hprod : (S.p : ℤ) ≤ (S.p : ℤ) * A := by
          have hAz : (1 : ℤ) ≤ A := by exact_mod_cast hA
          nlinarith [Nat.cast_nonneg (α := ℤ) S.p]
        omega
      · exact S.symbol_bound
    have hX : ∀ i, HasBound (X i).entries (S.p * A : ℤ) := by
      intro i
      change HasBound (ρ (U (finTwoEquiv i))).entries (S.p * A : ℤ)
      simpa only [neg_neg] using hρb (U (finTwoEquiv i)) _ (hUb (finTwoEquiv i))
    have heval : FreeAlgebra.lift S.F X (changeCoefficients (L := S.F) f) =
        ρ (evaluateAt (hp := S.hp) (h := S.commute) S.Z (1 + g)) := by
      have hmap : ((FreeAlgebra.lift S.F X).restrictScalars K).comp
          ((FreeAlgebra.lift K (FreeAlgebra.ι S.F)).comp
            (binaryToFinTwo (K := K))) =
          ρa.comp (evaluateAt (hp := S.hp) (h := S.commute) S.Z) := by
        apply FreeAlgebra.hom_ext
        funext b
        simp [binaryToFinTwo, X, U, evaluateAt, evaluatePair, evaluate]
      exact DFunLike.congr_fun hmap (1 + g)
    have hres : HasBound
        (FreeAlgebra.lift S.F X (changeCoefficients (L := S.F) f)).entries
        (-(S.p * T : ℤ)) := by
      rw [heval]
      exact hρb _ _ S.residual_bound
    have hD : DegreeBound (changeCoefficients (L := S.F) f) D :=
      degreeBound_changeCoefficients f (degreeBound_wordDegree f)
    obtain ⟨Z, hZ⟩ := matrix_witness_of_controlled S.hp f hD X hX hres
    obtain ⟨W, hW⟩ := matrix_rank_descent f Z hZ
    refine ⟨S.p * T ^ 2, Nat.mul_pos S.hp (pow_pos hT _), W, ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using compressed_ratio_bound S.hp hT hW
  intro ε hε
  obtain ⟨n, hn, W, hW⟩ := (rankInfimumZero_iff f).mp hf ε hε
  refine ⟨n, hn, W (finTwoEquiv.symm false), W (finTwoEquiv.symm true), ?_⟩
  have heval := lift_binaryToFinTwo (1 + g) W
  have htuple : (fun b ↦ W (finTwoEquiv.symm b)) =
      (fun b ↦ if b then W (finTwoEquiv.symm true) else W (finTwoEquiv.symm false)) := by
    funext b
    cases b <;> rfl
  rw [htuple] at heval
  change ((FreeAlgebra.lift K W (binaryToFinTwo (1 + g))).rank : ℝ) / n < ε at hW
  rw [heval] at hW
  exact hW

end

end MakarLimanov
