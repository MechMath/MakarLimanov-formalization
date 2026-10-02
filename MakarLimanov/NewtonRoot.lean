import MakarLimanov.GenericKernel
import MakarLimanov.NewtonTranslation

/-!
# A generic factor root for the translated Newton equation

An irreducible jet polynomial with a chosen positive-degree leader has a root in an
explicit fraction-field/AdjoinRoot extension. Its cofactor and leader separant stay
nonzero. Combined with `NewtonTranslation`, this constructs the nonzero degree-`m`
term in equation (5.2) after extension of the coefficient field.
-/

namespace MakarLimanov.NewtonRoot

open MvPolynomial

noncomputable section

universe u v w

variable {F : Type u} {σ : Type v} [Field F]

/-- Differentiating with respect to the selected leader is univariate differentiation. -/
theorem optionEquivLeft_pderiv_none (P : MvPolynomial (Option σ) F) :
    optionEquivLeft F σ (pderiv none P) = (optionEquivLeft F σ P).derivative := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    cases i <;> simp [Derivation.leibniz, smul_eq_mul, hP, Polynomial.derivative_mul,
      mul_comm]

variable {L : Type w} {E : Type*} [Field L] [Field E]
  [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
  [Algebra (MvPolynomial σ F) L] [IsScalarTower F (MvPolynomial σ F) L]

/-- Use the generic coefficient variables together with the selected algebraic root. -/
def rootPoint (z : E) : Option σ → E
  | none => z
  | some i => algebraMap L E (algebraMap (MvPolynomial σ F) L (X i))

/-- Evaluation at the generic point is the univariate root evaluation used by Gauss's lemma. -/
theorem aeval_rootPoint (z : E) (P : MvPolynomial (Option σ) F) :
    MvPolynomial.aeval (rootPoint (F := F) (L := L) z) P =
      Polynomial.aeval z ((optionEquivLeft F σ P).map (algebraMap (MvPolynomial σ F) L)) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, optionEquivLeft_C, Polynomial.map_C,
      Polynomial.aeval_C]
    change algebraMap F E a = algebraMap L E
      (algebraMap (MvPolynomial σ F) L (algebraMap F (MvPolynomial σ F) a))
    rw [← IsScalarTower.algebraMap_apply F (MvPolynomial σ F) L,
      ← IsScalarTower.algebraMap_apply F L E]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => cases i <;> simp [hP, rootPoint]

end

noncomputable section

universe u

variable {F σ : Type u} [Field F] [CharZero F]

/--
An explicit fraction-field/root-quotient construction realizes an irreducible factor,
preserves every inequation outside its principal ideal, and has nonzero leader separant.
-/
theorem exists_factor_root (P : MvPolynomial (Option σ) F) (hP : Irreducible P)
    (hdeg : P.degreeOf none ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E), ∃ v : Option σ → E,
      MvPolynomial.aeval v P = 0 ∧
      (∀ Q : MvPolynomial (Option σ) F, MvPolynomial.aeval v Q = 0 ↔ P ∣ Q) ∧
      MvPolynomial.aeval v (pderiv none P) ≠ 0 := by
  let R := MvPolynomial σ F
  let L := FractionRing R
  let P₀ := optionEquivLeft F σ P
  have hP₀ : Irreducible P₀ := hP.map (optionEquivLeft F σ)
  have hd₀ : P₀.natDegree ≠ 0 := by
    simpa only [P₀, natDegree_optionEquivLeft] using hdeg
  let p := P₀.map (algebraMap R L)
  have hp : Irreducible p := GenericKernel.irreducible_fraction_map hP₀ hd₀
  letI : Fact (Irreducible p) := ⟨hp⟩
  let E := AdjoinRoot p
  let z : E := AdjoinRoot.root p
  let v : Option σ → E := rootPoint (F := F) (L := L) z
  have : CharZero R := charZero_of_injective_ringHom (MvPolynomial.C_injective σ F)
  have : CharZero L := IsFractionRing.charZero_of_isFractionRing R
  refine ⟨E, inferInstance, inferInstance, v, ?_, ?_, ?_⟩
  · rw [aeval_rootPoint]
    exact AlgebraicBranch.root_equation p
  · intro Q
    rw [aeval_rootPoint, GenericKernel.generic_root_kernel P₀ hP₀ hd₀]
    exact map_dvd_iff (optionEquivLeft F σ)
  · rw [aeval_rootPoint, optionEquivLeft_pderiv_none, ← Polynomial.derivative_map]
    exact AlgebraicBranch.separant_nonzero p

open NewtonTranslation

/--
The algebraic part of one correction: construct a factor root and prove the exact
nonzero lowest term of the translated residual, with no root or separant supplied
as an assumption.
-/
theorem exists_translated_factor_lowest_term (P Q : MvPolynomial (Option σ) F)
    (hP : Irreducible P) (hdeg : P.degreeOf none ≠ 0) (hQ : ¬ P ∣ Q) (m : ℕ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E), ∃ v : Option σ → E,
      MvPolynomial.aeval v P = 0 ∧ MvPolynomial.aeval v Q ≠ 0 ∧
      MvPolynomial.aeval v (pderiv none P) ≠ 0 ∧
      (∀ j < m, homogeneousComponent j
        (translate v (MvPolynomial.map (algebraMap F E) (P ^ m * Q))) = 0) ∧
      homogeneousComponent m (translate v (MvPolynomial.map (algebraMap F E) (P ^ m * Q))) =
        C (MvPolynomial.aeval v Q) * linearization v (MvPolynomial.map (algebraMap F E) P) ^ m ∧
      homogeneousComponent m (translate v (MvPolynomial.map (algebraMap F E) (P ^ m * Q))) ≠ 0 := by
  obtain ⟨E, hE, hFE, v, hvP, hker, hsep⟩ := exists_factor_root P hP hdeg
  have hvQ : MvPolynomial.aeval v Q ≠ 0 := fun h ↦ hQ ((hker Q).mp h)
  have hmap (A : MvPolynomial (Option σ) F) :
      MvPolynomial.eval v (MvPolynomial.map (algebraMap F E) A) =
        MvPolynomial.aeval v A := by
    rw [MvPolynomial.eval_map]
    rfl
  have hroot : MvPolynomial.eval v (MvPolynomial.map (algebraMap F E) P) = 0 := by
    rw [hmap, hvP]
  have hcofactor : MvPolynomial.eval v (MvPolynomial.map (algebraMap F E) Q) ≠ 0 := by
    rw [hmap]
    exact hvQ
  have hderiv : MvPolynomial.eval v
      (pderiv none (MvPolynomial.map (algebraMap F E) P)) ≠ 0 := by
    rw [MvPolynomial.pderiv_map, hmap]
    exact hsep
  refine ⟨E, hE, hFE, v, hvP, hvQ, hsep, ?_⟩
  have hlowest := translated_factor_lowest_term v
    (MvPolynomial.map (algebraMap F E) P) (MvPolynomial.map (algebraMap F E) Q)
    m none hroot hcofactor hderiv
  simpa only [map_mul, map_pow, hmap] using hlowest

end

end MakarLimanov.NewtonRoot
