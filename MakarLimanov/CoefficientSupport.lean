import MakarLimanov.ControlledWitness

/-! Coefficient extension preserves the word support and degree of a free polynomial. -/

namespace MakarLimanov

open ControlledMatrix

variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]

/-- Extending scalars in a free polynomial maps each word coefficient separately. -/
theorem wordCoefficients_lift_coefficients (f : FreeAlgebra K σ) :
    wordCoefficients (FreeAlgebra.lift K (FreeAlgebra.ι L) f) =
      MonoidAlgebra.mapAlgHom (FreeMonoid σ) (Algebra.ofId K L) (wordCoefficients f) := by
  have h :
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.restrictScalars K).comp
          (FreeAlgebra.lift K (FreeAlgebra.ι L)) =
        (MonoidAlgebra.mapAlgHom (FreeMonoid σ) (Algebra.ofId K L)).comp
          FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply]
  exact DFunLike.congr_fun h f

/-- A word coefficient is unchanged except for the field embedding. -/
theorem wordCoefficients_lift_coefficients_apply (f : FreeAlgebra K σ)
    (w : FreeMonoid σ) :
    wordCoefficients (FreeAlgebra.lift K (FreeAlgebra.ι L) f) w =
      algebraMap K L (wordCoefficients f w) := by
  rw [wordCoefficients_lift_coefficients]
  simp

/-- An injective field extension preserves the exact word support. -/
theorem support_lift_coefficients (f : FreeAlgebra K σ) :
    (wordCoefficients (FreeAlgebra.lift K (FreeAlgebra.ι L) f)).support =
      (wordCoefficients f).support := by
  classical
  ext w
  simp only [Finsupp.mem_support_iff, wordCoefficients_lift_coefficients_apply]
  exact not_congr (map_eq_zero_iff (algebraMap K L) (RingHom.injective _))

/-- Extending the coefficient field preserves every bound on occurring word lengths. -/
theorem degreeBound_changeCoefficients {d D : ℕ} (f : FreePoly K d)
    (hD : DegreeBound f D) : DegreeBound (changeCoefficients (L := L) f) D := by
  intro w hw
  apply hD w
  simpa only [changeCoefficients, support_lift_coefficients] using hw

/-- The maximum word length is unchanged under extension of the coefficient field. -/
theorem wordDegree_changeCoefficients {d : ℕ} (f : FreePoly K d) :
    wordDegree (changeCoefficients (L := L) f) = wordDegree f := by
  simp only [wordDegree, changeCoefficients, support_lift_coefficients]

/-- Rename the two binary letters as the generators indexed by `Fin 2`. -/
noncomputable def binaryToFinTwo : FreeAlgebra K Bool →ₐ[K] FreePoly K 2 :=
  FreeAlgebra.lift K (fun b ↦ FreeAlgebra.ι K (finTwoEquiv.symm b))

/-- Renaming binary generators is compatible with evaluation in every algebra. -/
theorem lift_binaryToFinTwo {A : Type*} [Semiring A] [Algebra K A]
    (f : FreeAlgebra K Bool) (X : Fin 2 → A) :
    FreeAlgebra.lift K X (binaryToFinTwo f) =
      FreeAlgebra.lift K (fun b ↦ X (finTwoEquiv.symm b)) f := by
  have h : (FreeAlgebra.lift K X).comp binaryToFinTwo =
      FreeAlgebra.lift K (fun b ↦ X (finTwoEquiv.symm b)) := by
    apply FreeAlgebra.hom_ext
    funext b
    simp [binaryToFinTwo]
  exact DFunLike.congr_fun h f

/-- Evaluating the renamed polynomial on the corresponding binary tuple restores its value. -/
theorem lift_binaryToFinTwo_binary {A : Type*} [Semiring A] [Algebra K A]
    (f : FreeAlgebra K Bool) (X : Bool → A) :
    FreeAlgebra.lift K (fun i ↦ X (finTwoEquiv i)) (binaryToFinTwo f) =
      FreeAlgebra.lift K X f := by
  rw [lift_binaryToFinTwo]
  simp

end MakarLimanov
